# standard_generator.py
from standard_spec import StandardizationSpec, AuthMethod


def generate_standard_block(spec: StandardizationSpec) -> str:
    a = spec.auth
    v = spec.validation
    r = spec.response
    e = spec.errors
    o = spec.observability
    rl = spec.rate_limit

    block = f"""
import os, time, uuid, json
from datetime import datetime
from fastapi import Request
from fastapi.responses import JSONResponse

STD_VERSION = "{spec.version}"
JWT_SECRET = os.getenv("JWT_SECRET", "change-me")
JWT_ALGO = "{a.jwt_algorithm}"
API_KEY_VALUE = os.getenv("API_KEY_VALUE", "change-me")
API_KEY_HEADER = "{a.api_key_header}"
OAUTH_SCOPE = "{a.oauth_scope}"
TRACE_HEADER = "{o.trace_header}"
MAX_REQUEST_SIZE = int(os.getenv("MAX_REQUEST_SIZE", {v.max_request_size}))
REQS_PER_MINUTE = int(os.getenv("REQS_PER_MINUTE", {rl.requests_per_minute}))
""".rstrip()

    # 1) error handling (outermost)
    if e.enabled:
        block += f"""
@app.middleware("http")
async def error_handling_mw(request: Request, call_next):
    try:
        return await call_next(request)
    except Exception as ex:
        # retry/circuit-breaker hooks would go here
        return JSONResponse(
            status_code=500,
            content={{
                "status": 500,
                "error": "Internal Server Error",
                "detail": str(ex),
                "meta": {{"trace_id": getattr(getattr(request, "state", None), "trace_id", None)}},
            }},
        )
""".rstrip()

    # 2) observability
    if o.enabled:
        block += """
@app.middleware("http")
async def observability_mw(request: Request, call_next):
    start = time.time()
    trace_id = request.headers.get(TRACE_HEADER, str(uuid.uuid4()))
    request.state.trace_id = trace_id
    response = await call_next(request)
    latency_ms = (time.time() - start) * 1000
    if True:  # simple metrics/logging
        print({"path": request.url.path, "latency_ms": latency_ms, "trace_id": trace_id})
    return response
""".rstrip()

    # 3) validation (size + standardized pydantic base)
    if v.enabled:
        block += """
@app.middleware("http")
async def validation_mw(request: Request, call_next):
    body = await request.body()
    if len(body) > MAX_REQUEST_SIZE:
        return JSONResponse(status_code=413, content={"status": 413, "error": "Payload too large"})
    request._body = body
    return await call_next(request)

from pydantic import BaseModel, validator
class StandardizedModel(BaseModel):
    @validator("*", pre=True)
    def _validate(cls, v, field):
        if isinstance(v, str) and len(v) > """ + str(v.max_string_length) + """:
            raise ValueError(f"String too long: {field.name}")
        return v
"""

    # 4) auth
    if a.required and a.method != AuthMethod.NONE:
        if a.method == AuthMethod.JWT:
            block += """
@app.middleware("http")
async def auth_mw(request: Request, call_next):
    if request.url.path == "/health":
        return await call_next(request)
    auth_header = request.headers.get("Authorization")
    if not auth_header or not auth_header.startswith("Bearer "):
        return JSONResponse(status_code=401, content={"status": 401, "error": "Unauthorized"})
    token = auth_header.split(" ")[1]
    import jwt
    try:
        payload = jwt.decode(token, JWT_SECRET, algorithms=[JWT_ALGO])
        request.state.user = payload
    except jwt.InvalidTokenError:
        return JSONResponse(status_code=401, content={"status": 401, "error": "Invalid token"})
    return await call_next(request)
"""
        elif a.method == AuthMethod.API_KEY:
            block += """
@app.middleware("http")
async def auth_mw(request: Request, call_next):
    if request.url.path == "/health":
        return await call_next(request)
    api_key = request.headers.get(API_KEY_HEADER)
    if not api_key or api_key != API_KEY_VALUE:
        return JSONResponse(status_code=401, content={"status": 401, "error": "Invalid API key"})
    request.state.user = {"api_key": api_key}
    return await call_next(request)
"""
        elif a.method == AuthMethod.OAUTH:
            block += """
@app.middleware("http")
async def auth_mw(request: Request, call_next):
    # placeholder: real OAuth2/JWT introspection goes here
    if request.url.path == "/health":
        return await call_next(request)
    auth_header = request.headers.get("Authorization")
    if not auth_header or not auth_header.startswith("Bearer "):
        return JSONResponse(status_code=401, content={"status": 401, "error": "Unauthorized"})
    # accept any token but attach scope
    request.state.user = {"scope": OAUTH_SCOPE}
    return await call_next(request)
"""

    # 5) rate limiting (simple, in-memory)
    if rl.enabled:
        block += f"""
_rate_limit_store = {{}}
@app.middleware("http")
async def rate_limit_mw(request: Request, call_next):
    # key order: user > api key > ip
    key = None
    user = getattr(getattr(request, "state", None), "user", None)
    if {rl.per_user} and user and ("user_id" in user):
        key = "user:" + str(user["user_id"])
    elif {rl.per_api_key} and user and ("api_key" in user):
        key = "api:" + str(user["api_key"])
    if key is None:
        key = "ip:" + request.client.host

    now_bucket = int(time.time() // 60)
    user_buckets = _rate_limit_store.setdefault(key, {{}})
    count = user_buckets.get(now_bucket, 0)
    if count >= REQS_PER_MINUTE:
        return JSONResponse(status_code=429, content={{"status": 429, "error": "Rate limit exceeded"}})
    user_buckets[now_bucket] = count + 1
    return await call_next(request)
"""

    # 6) response formatter
    if r.enabled:
        block += f"""
def standard_response(data=None, status: int = 200, error: str = None, request: Request = None):
    meta = {{}}
    if {r.include_request_id} and request is not None:
        meta["request_id"] = request.headers.get("X-Request-Id")
    if {r.include_trace_id} and request is not None:
        meta["trace_id"] = getattr(getattr(request, "state", None), "trace_id", None)
    if {r.include_timestamp}:
        meta["timestamp"] = datetime.utcnow().isoformat()
    meta["version"] = "{r.version}"
    return JSONResponse(
        status_code=status,
        content={{
            "status": status,
            "data": data,
            "error": error,
            "meta": meta,
        }},
    )
"""

    return block + "\n"
