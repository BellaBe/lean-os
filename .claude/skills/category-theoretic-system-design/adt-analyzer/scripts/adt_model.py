# adt_model.py
from dataclasses import dataclass
from typing import List, Union
from enum import Enum


class ADTType(Enum):
    PRODUCT = "×"
    COPRODUCT = "+"
    ATOM = "atom"
    UNIT = "1"
    VOID = "0"


@dataclass
class ADT:
    """Algebraic Data Type representation"""
    type: ADTType
    children: List['ADT'] = None
    name: str = None

    def __post_init__(self):
        if self.children is None:
            self.children = []

    def __str__(self):
        if self.type == ADTType.ATOM:
            return self.name
        elif self.type == ADTType.UNIT:
            return "1"
        elif self.type == ADTType.VOID:
            return "0"
        elif self.type == ADTType.PRODUCT:
            return " × ".join(str(c) for c in self.children)
        elif self.type == ADTType.COPRODUCT:
            return f"({' + '.join(str(c) for c in self.children)})"
        return "Unknown"


def atom(name: str) -> ADT:
    """Create atomic type"""
    return ADT(ADTType.ATOM, [], name)


def product(*types: ADT) -> ADT:
    """Create product type"""
    return ADT(ADTType.PRODUCT, list(types))


def coproduct(*types: ADT) -> ADT:
    """Create coproduct type"""
    return ADT(ADTType.COPRODUCT, list(types))


def unit() -> ADT:
    """Create unit type (1)"""
    return ADT(ADTType.UNIT, [])


def void() -> ADT:
    """Create void type (0)"""
    return ADT(ADTType.VOID, [])
