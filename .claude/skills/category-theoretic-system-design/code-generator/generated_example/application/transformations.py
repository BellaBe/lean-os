from typing import Optional, List, TypeVar

A = TypeVar('A')

def maybe_to_list(maybe_value: Optional[A]) -> List[A]:
    """
    Natural transformation: Maybe ⇒ List

    Transforms optional value to list (0 or 1 element).
    Naturality: list.fmap(f) ∘ maybe_to_list = maybe_to_list ∘ maybe.fmap(f)
    """
    return [maybe_value] if maybe_value is not None else []

