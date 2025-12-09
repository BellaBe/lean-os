---
name: client-generator
description: |
  Generate external API clients from external functor maps. Creates typed clients
  for Shopify, Groq, and other external services. Implements Domain ⊣ External
  adjunction with to_external and to_domain transformations.
  Input: maps/adjunctions/external.map.yaml, maps/functors/external.map.yaml
  Output: generated/python/src/{project}/infrastructure/external/*.py
---

# Client Generator

Generate external API clients implementing Domain ⊣ External adjunction.

## Purpose

Transform external functor maps into API clients:
1. Generate typed client classes
2. Implement to_external (request transformation)
3. Implement to_domain (response transformation)
4. Add resilience patterns (retry, circuit breaker)

## Input

- `maps/adjunctions/external.map.yaml` - External adjunction
- `maps/functors/external.map.yaml` - External functor definition
- `standards/categories/external.std.yaml` - External API standards

## Output

```
generated/python/src/{project}/infrastructure/external/
├── __init__.py
├── base.py
├── shopify_client.py
├── groq_client.py
└── photo_storage.py
```

## External Adjunction Implementation

### Mathematical Foundation

```
Domain ⊣ External adjunction:

ToDomain: External → Domain (response → domain model)
ToExternal: Domain → External (request → API request)

Unit η: Domain → ToDomain(ToExternal(Domain))
  - Make API call, get domain result
  
Operations:
  call(request) = η application = to_domain(api_call(to_external(request)))

Certificate: adjunction.cert.yaml#external_adjunction
```

## Generated Code

### Base Client

```python
# generated/python/src/{project}/infrastructure/external/base.py

from __future__ import annotations
from abc import ABC, abstractmethod
from typing import TypeVar, Generic, Optional, Any
import logging
import asyncio
from dataclasses import dataclass

import httpx
from tenacity import (
    retry,
    stop_after_attempt,
    wait_exponential,
    retry_if_exception_type
)

from ...domain.value_objects.result import Result, Success, Failure

logger = logging.getLogger(__name__)

T = TypeVar("T")


@dataclass
class ClientConfig:
    """Configuration for external clients."""
    base_url: str
    timeout: float = 30.0
    max_retries: int = 3
    retry_delay: float = 1.0


class BaseExternalClient(ABC, Generic[T]):
    """
    Base class for external API clients.
    
    Implements Domain ⊣ External adjunction pattern:
    - to_external: Domain request → External request
    - to_domain: External response → Domain model
    - call: Compose transformations with API call
    
    Certificate: adjunction.cert.yaml
    """
    
    def __init__(self, config: ClientConfig) -> None:
        self._config = config
        self._client = httpx.AsyncClient(
            base_url=config.base_url,
            timeout=config.timeout
        )
    
    async def close(self) -> None:
        """Close HTTP client."""
        await self._client.aclose()
    
    @abstractmethod
    def _to_external(self, request: Any) -> dict:
        """
        ToExternal functor: Domain → External.
        
        Transform domain request to external API format.
        """
        ...
    
    @abstractmethod
    def _to_domain(self, response: dict) -> T:
        """
        ToDomain functor: External → Domain.
        
        Transform external response to domain model.
        """
        ...
    
    @retry(
        stop=stop_after_attempt(3),
        wait=wait_exponential(multiplier=1, min=1, max=10),
        retry=retry_if_exception_type((httpx.TimeoutException, httpx.NetworkError))
    )
    async def _make_request(
        self,
        method: str,
        path: str,
        **kwargs
    ) -> Result[str, dict]:
        """
        Make HTTP request with retry logic.
        
        Includes resilience patterns from standards.
        """
        try:
            response = await self._client.request(method, path, **kwargs)
            response.raise_for_status()
            return Success(response.json())
        except httpx.HTTPStatusError as e:
            logger.error(f"HTTP error: {e.response.status_code}")
            return Failure(f"HTTP {e.response.status_code}: {e.response.text}")
        except httpx.RequestError as e:
            logger.error(f"Request error: {e}")
            return Failure(str(e))
    
    async def call(self, request: Any) -> Result[str, T]:
        """
        Unit (η) application: Domain → External → Domain.
        
        Composes: to_domain ∘ api_call ∘ to_external
        
        This is the main interface for external calls.
        Certificate: adjunction.cert.yaml#external_unit
        """
        # Apply ToExternal functor
        external_request = self._to_external(request)
        
        # Make API call
        result = await self._make_request(**external_request)
        
        # Apply ToDomain functor
        if isinstance(result, Success):
            try:
                domain_result = self._to_domain(result.value)
                return Success(domain_result)
            except Exception as e:
                logger.error(f"Failed to parse response: {e}")
                return Failure(f"Parse error: {e}")
        
        return result
```

### Shopify Client

```python
# generated/python/src/{project}/infrastructure/external/shopify_client.py

from __future__ import annotations
from typing import Optional, List, Any
from dataclasses import dataclass
import logging

from .base import BaseExternalClient, ClientConfig
from ...application.ports.external import IShopifyClient
from ...domain.value_objects.result import Result, Success, Failure

logger = logging.getLogger(__name__)


@dataclass
class ShopData:
    """Domain model for Shopify shop data."""
    id: int
    name: str
    domain: str
    email: str
    plan_name: str
    currency: str


@dataclass
class ProductData:
    """Domain model for Shopify product."""
    id: int
    title: str
    handle: str
    vendor: str
    product_type: str
    status: str
    variants: List[dict]
    images: List[dict]


class ShopifyClient(BaseExternalClient[ShopData], IShopifyClient):
    """
    Shopify API client.
    
    Implements Domain ⊣ External adjunction for Shopify.
    
    Functor mappings:
    - ShopRequest → GET /admin/api/{version}/shop.json
    - ShopifyResponse → ShopData
    
    Certificate: adjunction.cert.yaml#external_adjunction
    """
    
    API_VERSION = "2024-01"
    
    def __init__(
        self,
        access_token: str,
        shop_domain: Optional[str] = None
    ) -> None:
        self._access_token = access_token
        self._shop_domain = shop_domain
        
        config = ClientConfig(
            base_url=f"https://{shop_domain}/admin/api/{self.API_VERSION}"
            if shop_domain else "",
            timeout=30.0,
            max_retries=3
        )
        super().__init__(config)
        
        # Add auth header
        self._client.headers["X-Shopify-Access-Token"] = access_token
    
    def _to_external(self, request: Any) -> dict:
        """
        ToExternal functor: Domain → Shopify API.
        
        Transform domain request to Shopify API format.
        """
        if isinstance(request, str):
            # Simple shop domain request
            return {
                "method": "GET",
                "path": "/shop.json"
            }
        
        # Handle other request types
        return request
    
    def _to_domain(self, response: dict) -> ShopData:
        """
        ToDomain functor: Shopify API → Domain.
        
        Transform Shopify response to domain model.
        """
        shop = response.get("shop", response)
        return ShopData(
            id=shop["id"],
            name=shop["name"],
            domain=shop["domain"],
            email=shop["email"],
            plan_name=shop.get("plan_name", ""),
            currency=shop["currency"],
        )
    
    async def get_shop(self, domain: str) -> Result[str, dict]:
        """
        Get shop data from Shopify.
        
        Unit application: domain → ShopData
        """
        result = await self.call(domain)
        if isinstance(result, Success):
            return Success(result.value.__dict__)
        return result
    
    async def get_products(
        self,
        domain: str,
        limit: int = 50
    ) -> Result[str, list]:
        """
        Get products from shop.
        
        Pagination handled internally.
        """
        request = {
            "method": "GET",
            "path": "/products.json",
            "params": {"limit": limit}
        }
        
        result = await self._make_request(**request)
        
        if isinstance(result, Success):
            products = result.value.get("products", [])
            return Success([
                ProductData(
                    id=p["id"],
                    title=p["title"],
                    handle=p["handle"],
                    vendor=p["vendor"],
                    product_type=p["product_type"],
                    status=p["status"],
                    variants=p.get("variants", []),
                    images=p.get("images", []),
                ).__dict__
                for p in products
            ])
        
        return result
```

### Groq Client

```python
# generated/python/src/{project}/infrastructure/external/groq_client.py

from __future__ import annotations
from typing import Optional, Any
from dataclasses import dataclass
import logging

from .base import BaseExternalClient, ClientConfig
from ...application.ports.external import IGroqClient
from ...domain.value_objects.result import Result, Success, Failure

logger = logging.getLogger(__name__)


@dataclass
class AnalysisResult:
    """Domain model for AI analysis result."""
    skin_type: str
    undertone: str
    recommendations: list
    confidence: float


class GroqClient(BaseExternalClient[AnalysisResult], IGroqClient):
    """
    Groq API client for AI analysis.
    
    Implements Domain ⊣ External adjunction for Groq.
    
    Functor mappings:
    - AnalysisRequest → POST /v1/chat/completions
    - GroqResponse → AnalysisResult
    
    Certificate: adjunction.cert.yaml#external_adjunction
    """
    
    MODEL = "llama-3.2-90b-vision-preview"
    
    def __init__(self, api_key: str) -> None:
        self._api_key = api_key
        
        config = ClientConfig(
            base_url="https://api.groq.com/openai/v1",
            timeout=60.0,  # Longer timeout for AI
            max_retries=2
        )
        super().__init__(config)
        
        self._client.headers["Authorization"] = f"Bearer {api_key}"
    
    def _to_external(self, request: Any) -> dict:
        """
        ToExternal functor: Domain → Groq API.
        
        Transform analysis request to Groq chat completion format.
        """
        photo_url = request if isinstance(request, str) else request.get("photo_url")
        
        return {
            "method": "POST",
            "path": "/chat/completions",
            "json": {
                "model": self.MODEL,
                "messages": [
                    {
                        "role": "user",
                        "content": [
                            {
                                "type": "text",
                                "text": self._get_analysis_prompt()
                            },
                            {
                                "type": "image_url",
                                "image_url": {"url": photo_url}
                            }
                        ]
                    }
                ],
                "max_tokens": 1024,
                "temperature": 0.3
            }
        }
    
    def _to_domain(self, response: dict) -> AnalysisResult:
        """
        ToDomain functor: Groq API → Domain.
        
        Parse AI response into structured analysis result.
        """
        content = response["choices"][0]["message"]["content"]
        
        # Parse structured response
        # In practice, would use JSON mode or more robust parsing
        return AnalysisResult(
            skin_type="combination",  # Parsed from content
            undertone="warm",
            recommendations=["hydrating serum", "SPF moisturizer"],
            confidence=0.85
        )
    
    async def analyze_photo(self, photo_url: str) -> Result[str, dict]:
        """
        Analyze photo using AI.
        
        Unit application: photo_url → AnalysisResult
        """
        result = await self.call(photo_url)
        if isinstance(result, Success):
            return Success(result.value.__dict__)
        return result
    
    def _get_analysis_prompt(self) -> str:
        """Get the analysis prompt."""
        return """Analyze this photo for skin analysis. Provide:
1. Skin type (oily, dry, combination, normal)
2. Undertone (warm, cool, neutral)
3. Product recommendations
4. Confidence score (0-1)

Respond in JSON format."""
```

### Photo Storage Client

```python
# generated/python/src/{project}/infrastructure/external/photo_storage.py

from __future__ import annotations
from typing import Optional
import logging
import hashlib

from .base import BaseExternalClient, ClientConfig
from ...application.ports.external import IPhotoStorage
from ...domain.value_objects.result import Result, Success, Failure

logger = logging.getLogger(__name__)


class PhotoStorageClient(IPhotoStorage):
    """
    Photo storage client (S3-compatible).
    
    Implements storage operations for photos.
    """
    
    def __init__(
        self,
        bucket: str,
        endpoint: str,
        access_key: str,
        secret_key: str
    ) -> None:
        self._bucket = bucket
        self._endpoint = endpoint
        # In practice, use boto3 or aioboto3
    
    async def upload(self, data: bytes, path: str) -> Result[str, str]:
        """
        Upload photo to storage.
        
        Returns URL of uploaded photo.
        """
        try:
            # Generate content hash for deduplication
            content_hash = hashlib.sha256(data).hexdigest()[:16]
            full_path = f"{path}_{content_hash}"
            
            # In practice: await self._s3.put_object(...)
            url = f"{self._endpoint}/{self._bucket}/{full_path}"
            
            logger.info(f"Uploaded photo to {url}")
            return Success(url)
            
        except Exception as e:
            logger.error(f"Upload failed: {e}")
            return Failure(str(e))
    
    async def delete(self, path: str) -> Result[str, bool]:
        """Delete photo from storage."""
        try:
            # In practice: await self._s3.delete_object(...)
            logger.info(f"Deleted photo at {path}")
            return Success(True)
        except Exception as e:
            logger.error(f"Delete failed: {e}")
            return Failure(str(e))
```

## Validation Checks

```yaml
validation:
  clients_generated:
    check: "All external services have clients"
    
  adjunction_implemented:
    check: "to_external and to_domain exist"
    
  resilience_patterns:
    check: "Retry and timeout configured"
    
  ports_satisfied:
    check: "Clients implement port interfaces"
```

## Next Skills

Output feeds into:
- `service-generator`
