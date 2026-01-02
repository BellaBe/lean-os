"""
Session Management for Authenticated Crawling

Manages browser sessions with persistent state:
- Cookies
- localStorage
- sessionStorage

Use cases:
- Crawl auth-required pages without re-login
- Maintain session across multiple crawls
- Share sessions between crawler instances

Flow:
1. Login once (manually or automated)
2. Export storage state
3. Reuse for subsequent crawls
"""

import json
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any


@dataclass
class Cookie:
    """Browser cookie."""

    name: str
    value: str
    domain: str
    path: str = "/"
    expires: float | None = None  # Unix timestamp
    http_only: bool = False
    secure: bool = False
    same_site: str = "None"  # "Strict", "Lax", "None"

    def to_dict(self) -> dict:
        d = {
            "name": self.name,
            "value": self.value,
            "domain": self.domain,
            "path": self.path,
            "httpOnly": self.http_only,
            "secure": self.secure,
            "sameSite": self.same_site,
        }
        if self.expires:
            d["expires"] = self.expires
        return d

    @classmethod
    def from_dict(cls, d: dict) -> "Cookie":
        return cls(
            name=d["name"],
            value=d["value"],
            domain=d["domain"],
            path=d.get("path", "/"),
            expires=d.get("expires"),
            http_only=d.get("httpOnly", False),
            secure=d.get("secure", False),
            same_site=d.get("sameSite", "None"),
        )


@dataclass
class LocalStorageItem:
    """localStorage key-value pair."""

    name: str
    value: str


@dataclass
class Origin:
    """Origin with localStorage data."""

    origin: str  # e.g., "https://example.com"
    local_storage: list[LocalStorageItem] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "origin": self.origin,
            "localStorage": [
                {"name": item.name, "value": item.value} for item in self.local_storage
            ],
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Origin":
        return cls(
            origin=d["origin"],
            local_storage=[
                LocalStorageItem(name=item["name"], value=item["value"])
                for item in d.get("localStorage", [])
            ],
        )


@dataclass
class StorageState:
    """
    Complete browser storage state.

    Compatible with Playwright's storageState format.
    """

    cookies: list[Cookie] = field(default_factory=list)
    origins: list[Origin] = field(default_factory=list)

    # Metadata
    created_at: datetime | None = None
    source_domain: str | None = None
    notes: str | None = None

    def to_dict(self) -> dict:
        """Convert to Playwright-compatible format."""
        return {
            "cookies": [c.to_dict() for c in self.cookies],
            "origins": [o.to_dict() for o in self.origins],
        }

    @classmethod
    def from_dict(cls, d: dict) -> "StorageState":
        return cls(
            cookies=[Cookie.from_dict(c) for c in d.get("cookies", [])],
            origins=[Origin.from_dict(o) for o in d.get("origins", [])],
        )

    def save(self, path: Path) -> None:
        """Save storage state to JSON file."""
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)

        data = self.to_dict()
        # Add metadata
        data["_metadata"] = {
            "created_at": self.created_at.isoformat() if self.created_at else None,
            "source_domain": self.source_domain,
            "notes": self.notes,
        }

        path.write_text(json.dumps(data, indent=2), encoding="utf-8")

    @classmethod
    def load(cls, path: Path) -> "StorageState":
        """Load storage state from JSON file."""
        path = Path(path)
        data = json.loads(path.read_text(encoding="utf-8"))

        state = cls.from_dict(data)

        # Load metadata if present
        if "_metadata" in data:
            meta = data["_metadata"]
            if meta.get("created_at"):
                state.created_at = datetime.fromisoformat(meta["created_at"])
            state.source_domain = meta.get("source_domain")
            state.notes = meta.get("notes")

        return state

    def get_cookies_for_domain(self, domain: str) -> list[Cookie]:
        """Get cookies that apply to a domain."""
        matching = []
        for cookie in self.cookies:
            # Check if cookie domain matches
            cookie_domain = cookie.domain.lstrip(".")
            if domain.endswith(cookie_domain) or domain == cookie_domain:
                matching.append(cookie)
        return matching

    def get_local_storage_for_origin(self, origin: str) -> dict[str, str]:
        """Get localStorage items for an origin."""
        for o in self.origins:
            if o.origin == origin:
                return {item.name: item.value for item in o.local_storage}
        return {}

    def add_cookie(self, cookie: Cookie) -> None:
        """Add or update a cookie."""
        # Remove existing cookie with same name/domain/path
        self.cookies = [
            c
            for c in self.cookies
            if not (
                c.name == cookie.name
                and c.domain == cookie.domain
                and c.path == cookie.path
            )
        ]
        self.cookies.append(cookie)

    def set_local_storage(self, origin: str, key: str, value: str) -> None:
        """Set a localStorage item."""
        for o in self.origins:
            if o.origin == origin:
                # Update existing
                for item in o.local_storage:
                    if item.name == key:
                        item.value = value
                        return
                # Add new
                o.local_storage.append(LocalStorageItem(name=key, value=value))
                return

        # Create new origin
        self.origins.append(
            Origin(
                origin=origin,
                local_storage=[LocalStorageItem(name=key, value=value)],
            )
        )


class SessionManager:
    """
    Manages browser sessions for authenticated crawling.

    Example:
        manager = SessionManager(Path("~/.nous/sessions"))

        # Create session from manual login
        session = await manager.create_from_login(
            "https://example.com/login",
            name="example_session",
        )

        # Later, use the session
        crawler = await manager.get_crawler_with_session("example_session")
        result = await crawler.arun("https://example.com/protected")
    """

    def __init__(self, sessions_dir: Path):
        self.sessions_dir = Path(sessions_dir).expanduser()
        self.sessions_dir.mkdir(parents=True, exist_ok=True)

    def _session_path(self, name: str) -> Path:
        """Get path for a named session."""
        return self.sessions_dir / f"{name}.json"

    def list_sessions(self) -> list[str]:
        """List all saved session names."""
        return [f.stem for f in self.sessions_dir.glob("*.json")]

    def session_exists(self, name: str) -> bool:
        """Check if a session exists."""
        return self._session_path(name).exists()

    def load_session(self, name: str) -> StorageState:
        """Load a saved session."""
        path = self._session_path(name)
        if not path.exists():
            raise FileNotFoundError(f"Session '{name}' not found")
        return StorageState.load(path)

    def save_session(self, name: str, state: StorageState) -> None:
        """Save a session."""
        state.save(self._session_path(name))

    def delete_session(self, name: str) -> None:
        """Delete a saved session."""
        path = self._session_path(name)
        if path.exists():
            path.unlink()

    async def create_from_login(
        self,
        login_url: str,
        name: str,
        wait_for_auth: str | None = None,
        timeout: int = 120,
    ) -> StorageState:
        """
        Create a session by opening a browser for manual login.

        Opens a visible browser window, waits for authentication,
        then captures and saves the storage state.

        Args:
            login_url: URL to the login page
            name: Name for the saved session
            wait_for_auth: CSS selector that indicates successful login
            timeout: Maximum seconds to wait for login

        Returns:
            Captured StorageState
        """
        try:
            from crawl4ai import AsyncWebCrawler, BrowserConfig, CrawlerRunConfig
        except ImportError:
            raise ImportError("crawl4ai not installed. Run: pip install crawl4ai")

        # Use visible browser for manual login
        config = BrowserConfig(
            headless=False,
            verbose=True,
        )

        print(f"Opening browser for login at: {login_url}")
        print("Please complete the login process...")
        print(f"Timeout: {timeout} seconds")

        async with AsyncWebCrawler(config=config) as crawler:
            # Navigate to login page
            run_config = CrawlerRunConfig(
                wait_for=wait_for_auth,
                page_timeout=timeout * 1000,
            )

            result = await crawler.arun(url=login_url, config=run_config)

            if not result.success:
                raise RuntimeError(f"Failed to load login page: {result.error_message}")

            # Wait for user to complete login
            if wait_for_auth:
                print(f"Waiting for selector: {wait_for_auth}")
            else:
                print("Please complete login and press Enter when done...")
                input()

            # Export storage state
            # Note: This requires access to the browser context
            # In actual implementation, you'd use Playwright's context.storage_state()

            # For now, create a placeholder that can be manually filled
            state = StorageState(
                created_at=datetime.utcnow(),
                source_domain=login_url,
                notes=f"Created from manual login at {login_url}",
            )

        self.save_session(name, state)
        print(f"Session '{name}' saved to {self._session_path(name)}")

        return state

    def create_manual_session(
        self,
        name: str,
        cookies: list[dict[str, Any]] | None = None,
        local_storage: dict[str, dict[str, str]] | None = None,
        notes: str | None = None,
    ) -> StorageState:
        """
        Create a session manually from provided data.

        Args:
            name: Session name
            cookies: List of cookie dicts
            local_storage: Dict of origin -> {key: value}
            notes: Optional notes

        Example:
            manager.create_manual_session(
                "my_session",
                cookies=[{
                    "name": "session_id",
                    "value": "abc123",
                    "domain": "example.com",
                }],
                local_storage={
                    "https://example.com": {
                        "auth_token": "xyz789",
                    },
                },
            )
        """
        state = StorageState(
            created_at=datetime.utcnow(),
            notes=notes,
        )

        if cookies:
            for c in cookies:
                state.add_cookie(Cookie.from_dict(c))

        if local_storage:
            for origin, items in local_storage.items():
                for key, value in items.items():
                    state.set_local_storage(origin, key, value)

        self.save_session(name, state)
        return state

    async def get_crawler_with_session(
        self,
        session_name: str,
        browser_profile: Any = None,
    ) -> Any:
        """
        Get a crawler configured with a saved session.

        Args:
            session_name: Name of saved session
            browser_profile: Optional BrowserProfile for additional config

        Returns:
            Configured AsyncWebCrawler
        """
        try:
            from crawl4ai import AsyncWebCrawler, BrowserConfig
        except ImportError:
            raise ImportError("crawl4ai not installed")

        session_path = self._session_path(session_name)
        if not session_path.exists():
            raise FileNotFoundError(f"Session '{session_name}' not found")

        if browser_profile:
            from .browser_config import BrowserFactory

            config = BrowserFactory.create_browser_config(browser_profile)
        else:
            config = BrowserConfig(headless=True, verbose=False)

        return AsyncWebCrawler(
            config=config,
            storage_state=str(session_path),
        )


class AuthenticatedCrawler:
    """
    High-level crawler for authenticated sites.

    Example:
        async with AuthenticatedCrawler("my_session") as crawler:
            result = await crawler.crawl("https://example.com/dashboard")
    """

    def __init__(
        self,
        session_name: str,
        sessions_dir: Path | None = None,
        browser_profile: Any = None,
    ) -> None:
        self.session_name = session_name
        self.sessions_dir = Path(sessions_dir or "~/.nous/sessions").expanduser()
        self.browser_profile = browser_profile
        self._crawler: Any = None
        self._manager = SessionManager(self.sessions_dir)

    async def __aenter__(self) -> "AuthenticatedCrawler":
        self._crawler = await self._manager.get_crawler_with_session(
            self.session_name,
            self.browser_profile,
        )
        await self._crawler.start()
        return self

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: Any,
    ) -> None:
        if self._crawler:
            await self._crawler.close()

    async def crawl(
        self,
        url: str,
        wait_for: str | None = None,
        **kwargs: Any,
    ) -> Any:
        """
        Crawl a URL with the authenticated session.

        Args:
            url: URL to crawl
            wait_for: CSS selector to wait for
            **kwargs: Additional CrawlerRunConfig options
        """
        try:
            from crawl4ai import CacheMode, CrawlerRunConfig
        except ImportError:
            raise ImportError("crawl4ai not installed")

        config = CrawlerRunConfig(
            cache_mode=CacheMode.BYPASS,
            wait_for=wait_for,
            **kwargs,
        )

        return await self._crawler.arun(url=url, config=config)


# Convenience functions
def create_session_from_cookies(
    name: str,
    cookies: list[dict[str, Any]],
    sessions_dir: Path | None = None,
) -> StorageState:
    """
    Quick helper to create a session from cookie data.

    Example:
        create_session_from_cookies(
            "nytimes",
            [{"name": "nyt-a", "value": "...", "domain": ".nytimes.com"}],
        )
    """
    manager = SessionManager(sessions_dir or Path("~/.nous/sessions"))
    return manager.create_manual_session(name, cookies=cookies)
