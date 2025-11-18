import pytest
from hypothesis import given, strategies as st

def test_merchantstate_creation():
    """Test MerchantState type creation"""
    # Add specific tests for your types
    pass

def test_reader_identity_law():
    """Verify F(id) = id for Reader"""
    def identity(x):
        return x

    @given(st.integers())
    def check(value):
        f = Reader.pure(value)
        assert f.fmap(identity).run(None) == identity(f.run(None))

    check()

def test_reader_composition_law():
    """Verify F(g ∘ f) = F(g) ∘ F(f) for Reader"""
    def f(x): return x + 1
    def g(x): return x * 2

    @given(st.integers())
    def check(value):
        functor = Reader.pure(value)
        composed = lambda x: g(f(x))
        # F(g ∘ f)
        result1 = functor.fmap(composed).run(None)
        # F(g) ∘ F(f)
        result2 = functor.fmap(f).fmap(g).run(None)
        assert result1 == result2

    check()
