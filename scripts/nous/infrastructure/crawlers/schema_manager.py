"""
Schema Manager for Extraction Strategies

Handles caching, generation, and lifecycle of CSS/XPath extraction schemas.
Key insight from Crawl4AI tutorial: Use LLM ONCE to generate schema,
then reuse for fast, LLM-free extractions.
"""

import json
from dataclasses import dataclass
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Protocol


@dataclass
class SchemaConfig:
    """Configuration for a single extraction schema."""

    name: str
    target_json_example: dict[str, Any]
    query: str
    sample_html: str | None = None  # Optional sample for generation


@dataclass
class CachedSchema:
    """A cached extraction schema with metadata."""

    name: str
    schema: dict[str, Any]
    generated_at: datetime
    expires_at: datetime | None = None
    version: int = 1

    def is_expired(self) -> bool:
        if self.expires_at is None:
            return False
        return datetime.utcnow() > self.expires_at

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "schema": self.schema,
            "generated_at": self.generated_at.isoformat(),
            "expires_at": self.expires_at.isoformat() if self.expires_at else None,
            "version": self.version,
        }

    @classmethod
    def from_dict(cls, data: dict) -> "CachedSchema":
        return cls(
            name=data["name"],
            schema=data["schema"],
            generated_at=datetime.fromisoformat(data["generated_at"]),
            expires_at=datetime.fromisoformat(data["expires_at"])
            if data.get("expires_at")
            else None,
            version=data.get("version", 1),
        )


class SchemaGenerator(Protocol):
    """Protocol for schema generation (LLM-based)."""

    async def generate(
        self,
        html: str,
        config: SchemaConfig,
    ) -> dict[str, Any]:
        """Generate extraction schema from HTML sample."""
        ...


class SchemaStore(Protocol):
    """Protocol for schema persistence."""

    async def get(self, name: str) -> CachedSchema | None: ...

    async def save(self, schema: CachedSchema) -> None: ...

    async def delete(self, name: str) -> None: ...

    async def list_all(self) -> list[CachedSchema]: ...


class FileSchemaStore:
    """File-based schema store for development/exploration."""

    def __init__(self, base_path: Path):
        self.base_path = base_path
        self.base_path.mkdir(parents=True, exist_ok=True)

    def _path_for(self, name: str) -> Path:
        safe_name = name.replace("/", "_").replace(" ", "_").lower()
        return self.base_path / f"{safe_name}.json"

    async def get(self, name: str) -> CachedSchema | None:
        path = self._path_for(name)
        if not path.exists():
            return None
        with open(path) as f:
            return CachedSchema.from_dict(json.load(f))

    async def save(self, schema: CachedSchema) -> None:
        path = self._path_for(schema.name)
        with open(path, "w") as f:
            json.dump(schema.to_dict(), f, indent=2)

    async def delete(self, name: str) -> None:
        path = self._path_for(name)
        if path.exists():
            path.unlink()

    async def list_all(self) -> list[CachedSchema]:
        schemas = []
        for path in self.base_path.glob("*.json"):
            with open(path) as f:
                schemas.append(CachedSchema.from_dict(json.load(f)))
        return schemas


class SchemaManager:
    """
    Manages extraction schemas with caching and lazy regeneration.

    Key pattern from tutorial:
    1. Check cache first
    2. If expired/missing, regenerate with LLM (one-time cost)
    3. Use cached schema for fast, LLM-free extractions
    """

    def __init__(
        self,
        store: SchemaStore,
        generator: SchemaGenerator | None = None,
        default_ttl: timedelta = timedelta(hours=24),
    ):
        self.store = store
        self.generator = generator
        self.default_ttl = default_ttl

    async def get_or_generate(
        self,
        config: SchemaConfig,
        html: str,
        force_regenerate: bool = False,
    ) -> dict[str, Any]:
        """
        Get schema from cache or generate if missing/expired.

        Args:
            config: Schema configuration
            html: Sample HTML for generation
            force_regenerate: Force regeneration even if cached

        Returns:
            The extraction schema dict
        """
        if not force_regenerate:
            cached = await self.store.get(config.name)
            if cached and not cached.is_expired():
                return cached.schema

        if self.generator is None:
            raise ValueError(f"No generator configured and schema '{config.name}' not in cache")

        schema = await self.generator.generate(html, config)

        cached_schema = CachedSchema(
            name=config.name,
            schema=schema,
            generated_at=datetime.utcnow(),
            expires_at=datetime.utcnow() + self.default_ttl,
        )
        await self.store.save(cached_schema)

        return schema

    async def get(self, name: str) -> dict[str, Any] | None:
        """Get schema by name, returns None if not found."""
        cached = await self.store.get(name)
        if cached and not cached.is_expired():
            return cached.schema
        return None
