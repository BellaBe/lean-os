from typing import Union
from dataclasses import dataclass

@dataclass
class Active:
    activated_at: datetime

@dataclass
class Deactivated:
    reason: str

@dataclass
class Trial:
    credits_remaining: int

MerchantState = Union[Active, Deactivated, Trial]
