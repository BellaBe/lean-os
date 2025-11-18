# merchant_app.py
from fastapi import FastAPI, Request

app = FastAPI(title="MerchantService")


@app.get("/merchants/{merchant_id}")
async def get_merchant(merchant_id: str, request: Request):
    # after injection you can call standard_response(...)
    return {"merchant_id": merchant_id, "name": "Acme Co"}


@app.get("/health")
async def health():
    return {"status": "ok"}

# <<< STANDARDIZATION:BEGIN >>>
# will be filled by standard_injector.py
# <<< STANDARDIZATION:END >>>
