# billing_app.py
from fastapi import FastAPI, Request

app = FastAPI(title="BillingService")


@app.post("/billing/invoice")
async def create_invoice(payload: dict, request: Request):
    return {"status": "created", "amount": payload.get("amount", 0)}


@app.get("/health")
async def health():
    return {"status": "ok"}

# <<< STANDARDIZATION:BEGIN >>>
# will be filled by standard_injector.py
# <<< STANDARDIZATION:END >>>
