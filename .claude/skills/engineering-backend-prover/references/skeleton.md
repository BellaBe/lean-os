Core Principle
Rule: If it belongs to standardization layer → goes in shared/
Rule: If it's business logic → generated per service from maps

Complete Service Skeleton
Directory Structure
service-name/
├── alembic/                           # ✅ Skeleton (migrations)
│   ├── versions/
│   ├── env.py
│   └── script.py.mako
│
├── src/
│   ├── api/v1/                       # ⚠️ Generated (endpoints from maps)
│   │   ├── __init__.py
│   │   └── {domain}.py
│   │
│   ├── db/
│   │   ├── models.py                 # ⚠️ Generated (from ADT)
│   │   └── session.py                # ✅ Skeleton (SQLAlchemy setup)
│   │
│   ├── events/                       # ⚠️ Generated (from maps)
│   │   ├── __init__.py
│   │   ├── listeners.py              # Business event handlers
│   │   └── publishers.py             # Business event publishers
│   │
│   ├── repositories/                 # ⚠️ Generated (from maps)
│   │   ├── __init__.py
│   │   └── {domain}_repository.py
│   │
│   ├── schemas/                      # ⚠️ Generated (from ADT)
│   │   ├── __init__.py
│   │   └── {domain}.py
│   │
│   ├── services/                     # ⚠️ Generated (from maps)
│   │   ├── __init__.py
│   │   └── {domain}_service.py
│   │
│   ├── observability/                # ⚠️ Generated (from maps)
│   │   ├── __init__.py
│   │   ├── metrics.py                # Service-specific metrics
│   │   └── traces.py                 # Service-specific tracing
│   │
│   ├── config.py                     # ✅ Skeleton (service config)
│   ├── dependencies.py               # ⚠️ Generated (DI wiring)
│   ├── exceptions.py                 # ⚠️ Generated (domain exceptions)
│   ├── lifecycle.py                  # ⚠️ Generated (startup/shutdown)
│   └── main.py                       # ✅ Skeleton (FastAPI app)
│
├── tests/                            # ⚠️ Generated (from maps)
│   ├── unit/
│   ├── integration/
│   └── properties/
│
├── .python-version                   # ✅ Skeleton
├── alembic.ini                       # ✅ Skeleton
├── pyproject.toml                    # ✅ Skeleton
└── poetry.lock

Shared Layer (Standardization)
Everything cross-cutting goes here:
shared/
├── api/                              # ✅ Standardization
│   ├── __init__.py
│   ├── responses.py                  # success_response(), error_response()
│   ├── middleware.py                 # Auth, CORS, correlation, logging
│   ├── dependencies.py               # RequestContextDep, ClientAuthDep
│   ├── handlers.py                   # Exception → HTTP response mapping
│   └── health.py                     # Health check router
│
├── messaging/                        # ✅ Standardization
│   ├── __init__.py
│   ├── jetstream_client.py          # NATS JetStream client
│   ├── publisher.py                  # Base publisher (correlation, retries)
│   ├── listener.py                   # Base listener (DLQ, backoff)
│   ├── subjects.py                   # Subject patterns (evt.*, cmd.*)
│   └── events/
│       └── base.py                   # BaseIdentifiers, BasePayload
│
├── observability/                    # ✅ Standardization
│   ├── __init__.py
│   ├── metrics.py                    # Prometheus metrics helpers
│   ├── tracing.py                    # OpenTelemetry tracing helpers
│   ├── logging.py                    # Structured logging setup
│   └── monitors/
│       ├── composition.py            # Composition law monitors
│       ├── database.py               # DB query monitors
│       └── http.py                   # HTTP call monitors
│
├── database/                         # ✅ Standardization
│   ├── __init__.py
│   ├── base.py                       # Base, metadata (naming conventions)
│   ├── mixins.py                     # TimestampMixin, SoftDeleteMixin
│   └── types.py                      # Custom SQLAlchemy types (UUID, JSON)
│
├── utils/                            # ✅ Standardization
│   ├── __init__.py
│   ├── exceptions.py                 # Base exception hierarchy
│   ├── logger.py                     # ServiceLogger class
│   ├── idempotency.py               # Idempotency key handling
│   ├── retry.py                      # Retry decorators
│   └── validation.py                 # Common validators
│
└── testing/                          # ✅ Standardization
    ├── __init__.py
    ├── fixtures.py                   # Common test fixtures
    ├── factories.py                  # Model factories
    └── mocks.py                      # Mock clients (NATS, DB)

Complete Skeleton Definition
1. Service Layer Skeleton
python# src/services/{domain}_service.py (GENERATED from map)

from sqlalchemy.ext.asyncio import async_sessionmaker, AsyncSession
from shared.observability import ServiceTracer, ServiceMetrics  # ⬅️ From shared
from shared.utils.logger import ServiceLogger                   # ⬅️ From shared

from ..repositories.{domain}_repository import {Domain}Repository
from ..schemas.{domain} import {Domain}CreateIn, {Domain}Out
from ..events.publishers import {Domain}EventPublisher
from ..exceptions import {Domain}NotFoundError

class {Domain}Service:
    """
    Generated from: maps/backend/services/{domain}_service.map.yaml
    Composition verified: true
    """
    
    def __init__(
        self,
        session_factory: async_sessionmaker[AsyncSession],
        publisher: {Domain}EventPublisher,
        logger: ServiceLogger,                    # ⬅️ From shared
        tracer: ServiceTracer,                    # ⬅️ From shared
        metrics: ServiceMetrics                   # ⬅️ From shared
    ):
        self.session_factory = session_factory
        self.publisher = publisher
        self.logger = logger
        self.tracer = tracer
        self.metrics = metrics
    
    async def create_{domain}(
        self, 
        data: {Domain}CreateIn, 
        ctx                                       # ⬅️ RequestContext from shared
    ) -> {Domain}Out:
        """
        Morphism: ({Domain}CreateIn, Context) → IO[Either[Error, {Domain}Out]]
        
        Composition (from map):
          1. repo.create: {Domain}CreateIn → IO[Either[Error, {Domain}]]
          2. validate: {Domain} → {Domain}Out
          3. publisher.created: {Domain}Out → IO[String]
        """
        with self.tracer.start_span("create_{domain}"):         # ⬅️ From shared
            self.metrics.increment("create_{domain}_called")    # ⬅️ From shared
            
            async with self.session_factory() as session:
                repo = {Domain}Repository(session)
                
                # Step 1: repo.create (from map)
                entity = await repo.create(data)
                await session.commit()
                
                # Step 2: validate (from map)
                dto = {Domain}Out.model_validate(entity)
                
                # Step 3: publisher.created (from map)
                await self.publisher.{domain}_created(dto, ctx)
                
                self.metrics.increment("create_{domain}_success")
                return dto

2. Events Skeleton
Publishers (Business-Specific)
python# src/events/publishers.py (GENERATED from map)

from uuid import UUID
from shared.messaging.publisher import Publisher              # ⬅️ Base from shared
from shared.messaging.events.base import BaseIdentifiers     # ⬅️ From shared
from shared.messaging.subjects import Subjects               # ⬅️ From shared

from ..schemas.{domain} import {Domain}Out

class {Domain}EventPublisher(Publisher):
    """
    Generated from: maps/backend/events/{domain}_publisher.map.yaml
    """
    
    @property
    def service_name(self) -> str:
        return "{domain}-service"
    
    async def {domain}_created(
        self, 
        entity: {Domain}Out, 
        ctx
    ) -> str:
        """
        Event: {domain}.created.v1
        Payload: {domain} identifiers + data
        """
        identifiers = BaseIdentifiers(id=UUID(str(entity.id)))
        
        payload = {
            "identifiers": identifiers.model_dump(),
            "field1": entity.field1,
            "field2": entity.field2,
            "status": entity.status,
        }
        
        return await self.publish_event(
            subject=Subjects.{DOMAIN}_CREATED,     # ⬅️ From shared
            payload=payload,
            correlation_id=ctx.correlation_id
        )
    
    async def {domain}_updated(
        self,
        entity: {Domain}Out,
        ctx
    ) -> str:
        """Event: {domain}.updated.v1"""
        identifiers = BaseIdentifiers(id=UUID(str(entity.id)))
        
        payload = {
            "identifiers": identifiers.model_dump(),
            "field1": entity.field1,
            "field2": entity.field2,
            "status": entity.status,
        }
        
        return await self.publish_event(
            subject=Subjects.{DOMAIN}_UPDATED,
            payload=payload,
            correlation_id=ctx.correlation_id
        )
Listeners (Business-Specific)
python# src/events/listeners.py (GENERATED from map)

from shared.messaging.jetstream_client import JetStreamClient  # ⬅️ From shared
from shared.messaging.listener import Listener                 # ⬅️ Base from shared
from shared.utils.logger import ServiceLogger                  # ⬅️ From shared
from shared.utils.exceptions import ValidationError            # ⬅️ From shared

from ..services.{domain}_service import {Domain}Service

class {Event}Listener(Listener):
    """
    Generated from: maps/backend/events/{event}_listener.map.yaml
    
    Subject: evt.{subject}.{event}.v1
    Queue: {domain}-{event}
    DLQ: dlq.{domain}-service.{domain}-{event}.failed
    """
    
    @property
    def subject(self) -> str:
        return "evt.{subject}.{event}.v1"
    
    @property
    def queue_group(self) -> str:
        return "{domain}-{event}"
    
    @property
    def service_name(self) -> str:
        return "{domain}-service"
    
    def __init__(
        self,
        js_client: JetStreamClient,
        service: {Domain}Service,
        logger: ServiceLogger
    ):
        super().__init__(js_client, logger)        # ⬅️ Base initialization
        self.service = service
    
    async def on_message(self, data: dict) -> None:
        """
        Handle incoming event
        
        Validation errors → ACK (don't retry)
        Business errors → NACK (retry with backoff)
        """
        try:
            # Validate payload
            field1 = data.get("field1")
            if not field1:
                raise ValidationError(
                    message="Missing field1",
                    field="field1"
                )
            
            # Process event
            await self.service.handle_event(field1)
            
        except ValidationError:
            # ACK invalid messages (don't retry)
            self.logger.error(
                "Invalid event payload",
                extra={"data": data}
            )
            return
            
        except Exception:
            # NACK for retry
            self.logger.exception(
                "Listener processing failed",
                exc_info=True,
                extra={"data": data}
            )
            raise
    
    async def on_error(self, error: Exception, data: dict) -> bool:
        """
        Handle error after max retries
        
        Returns:
            True: ACK message (stop retries)
            False: NACK message (retry)
        """
        # Validation errors → ACK immediately
        if isinstance(error, ValidationError):
            return True
        
        # Max retries reached → send to DLQ, then ACK
        if self.delivery_count >= self.max_deliver:
            await self.publish_event(
                subject=f"dlq.{self.service_name}.{self.queue_group}.failed",
                payload={
                    "original_data": data,
                    "error": str(error),
                    "delivery_count": self.delivery_count
                }
            )
            return True  # ACK to prevent further retries
        
        return False  # NACK for retry

3. Observability Skeleton
Service-Specific Metrics
python# src/observability/metrics.py (GENERATED from map)

from shared.observability.metrics import MetricsCollector      # ⬅️ Base from shared

class {Domain}Metrics(MetricsCollector):
    """
    Generated from: maps/backend/observability/{domain}_metrics.map.yaml
    
    Service-specific metrics for {domain}-service
    """
    
    def __init__(self):
        super().__init__(service_name="{domain}-service")
        
        # Business metrics (from map)
        self.create_counter = self.counter(
            name="{domain}_created_total",
            description="Total {domain}s created"
        )
        
        self.update_counter = self.counter(
            name="{domain}_updated_total",
            description="Total {domain}s updated"
        )
        
        self.operation_duration = self.histogram(
            name="{domain}_operation_duration_seconds",
            description="{Domain} operation duration",
            buckets=[0.01, 0.05, 0.1, 0.5, 1.0, 5.0]
        )
        
        # Composition metrics (from map)
        self.composition_valid = self.counter(
            name="{domain}_composition_valid_total",
            description="Composition laws verified"
        )
        
        self.composition_invalid = self.counter(
            name="{domain}_composition_invalid_total",
            description="Composition law violations"
        )
Service-Specific Tracing
python# src/observability/traces.py (GENERATED from map)

from shared.observability.tracing import TracingProvider       # ⬅️ Base from shared

class {Domain}Tracer(TracingProvider):
    """
    Generated from: maps/backend/observability/{domain}_tracer.map.yaml
    
    Service-specific tracing for {domain}-service
    """
    
    def __init__(self):
        super().__init__(service_name="{domain}-service")
    
    def trace_create(self, data):
        """Trace create operation"""
        return self.start_span(
            name="create_{domain}",
            attributes={
                "operation": "create",
                "domain": "{domain}",
                "field1": data.field1
            }
        )
    
    def trace_composition(self, step: str):
        """Trace composition step"""
        return self.start_span(
            name=f"composition.{step}",
            attributes={
                "composition_step": step,
                "category_theory": "morphism"
            }
        )

4. Lifecycle Skeleton (with Events + Observability)
python# src/lifecycle.py (GENERATED from map)

import asyncio
from shared.messaging.jetstream_client import JetStreamClient  # ⬅️ From shared
from shared.utils.logger import ServiceLogger                  # ⬅️ From shared

from .config import ServiceConfig
from .db.session import make_engine, make_session_factory
from .events.listeners import {Event}Listener
from .events.publishers import {Domain}EventPublisher
from .services.{domain}_service import {Domain}Service
from .observability.metrics import {Domain}Metrics
from .observability.traces import {Domain}Tracer

class ServiceLifecycle:
    """
    Generated from: maps/backend/lifecycle.map.yaml
    
    Manages service lifecycle:
    - Messaging (NATS)
    - Database (PostgreSQL)
    - Services
    - Event listeners
    - Observability
    """
    
    def __init__(self, config: ServiceConfig, logger: ServiceLogger):
        self.config = config
        self.logger = logger
        
        # Infrastructure
        self.messaging_client: JetStreamClient | None = None
        self.engine = None
        self.session_factory = None
        
        # Business components
        self.event_publisher: {Domain}EventPublisher | None = None
        self.{domain}_service: {Domain}Service | None = None
        
        # Observability
        self.metrics: {Domain}Metrics | None = None
        self.tracer: {Domain}Tracer | None = None
        
        # Event listeners
        self._listeners: list = []
        self._tasks: list[asyncio.Task] = []
    
    async def startup(self) -> None:
        """Start all components in correct order"""
        try:
            self.logger.info("Starting service components...")
            
            # 1. Observability (first, so we can track everything)
            await self._init_observability()
            
            # 2. Infrastructure
            await self._init_messaging()
            await self._init_database()
            
            # 3. Business logic
            self._init_services()
            
            # 4. Event listeners (last, so services are ready)
            await self._init_listeners()
            
            self.logger.info(f"{self.config.service_name} started successfully")
            
        except Exception:
            self.logger.critical("Service failed to start", exc_info=True)
            await self.shutdown()
            raise
    
    async def shutdown(self) -> None:
        """Graceful shutdown in reverse order"""
        self.logger.info("Shutting down service...")
        
        # 1. Stop accepting new work (listeners)
        for task in self._tasks:
            task.cancel()
        if self._tasks:
            await asyncio.gather(*self._tasks, return_exceptions=True)
        
        for listener in self._listeners:
            try:
                await listener.stop()
            except Exception:
                self.logger.exception("Listener stop failed", exc_info=True)
        
        # 2. Close messaging
        if self.messaging_client:
            try:
                await self.messaging_client.close()
            except Exception:
                self.logger.exception("Messaging close failed", exc_info=True)
        
        # 3. Close database
        if self.engine:
            try:
                await self.engine.dispose()
            except Exception:
                self.logger.exception("Engine dispose failed", exc_info=True)
        
        # 4. Flush observability
        if self.metrics:
            try:
                await self.metrics.shutdown()
            except Exception:
                self.logger.exception("Metrics shutdown failed", exc_info=True)
        
        if self.tracer:
            try:
                await self.tracer.shutdown()
            except Exception:
                self.logger.exception("Tracer shutdown failed", exc_info=True)
        
        self.logger.info("Service shutdown complete")
    
    async def _init_observability(self) -> None:
        """Initialize metrics and tracing"""
        self.metrics = {Domain}Metrics()
        self.tracer = {Domain}Tracer()
        
        self.logger.info("Observability initialized")
    
    async def _init_messaging(self) -> None:
        """Initialize NATS JetStream"""
        self.messaging_client = JetStreamClient(self.logger)
        await self.messaging_client.connect([self.config.nats_url])
        
        # Ensure stream exists
        await self.messaging_client.ensure_stream(
            "GLAM_EVENTS",
            ["evt.*", "cmd.*"]
        )
        
        self.event_publisher = {Domain}EventPublisher(
            self.messaging_client,
            self.logger
        )
        
        self.logger.info("Messaging initialized")
    
    async def _init_database(self) -> None:
        """Initialize database connection"""
        if not self.config.database_enabled:
            self.logger.info("Database disabled; skipping")
            return
        
        self.engine = make_engine(self.config.database_url)
        self.session_factory = make_session_factory(self.engine)
        
        self.logger.info("Database initialized")
    
    def _init_services(self) -> None:
        """Initialize business services"""
        if not self.session_factory or not self.event_publisher:
            raise RuntimeError("Dependencies not ready for service initialization")
        
        if not self.metrics or not self.tracer:
            raise RuntimeError("Observability not ready for service initialization")
        
        self.{domain}_service = {Domain}Service(
            session_factory=self.session_factory,
            publisher=self.event_publisher,
            logger=self.logger,
            tracer=self.tracer,              
            metrics=self.metrics             
        )
        
        self.logger.info("Services initialized")
    
    async def _init_listeners(self) -> None:
        """Initialize event listeners"""
        if not self.messaging_client or not self.{domain}_service:
            raise RuntimeError("Dependencies not ready for listeners")
        
        # Create listener (from map)
        listener = {Event}Listener(
            js_client=self.messaging_client,
            service=self.{domain}_service,
            logger=self.logger
        )
        
        # Start listener
        await listener.start()
        self._listeners.append(listener)
        
        self.logger.info(f"Listeners initialized: {len(self._listeners)}")