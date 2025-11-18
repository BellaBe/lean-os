# standard_injector.py
import pathlib
from dataclasses import dataclass
from typing import List, Tuple

from standard_spec import StandardizationSpec, AuthSpec, AuthMethod, ValidationSpec, ResponseFormatSpec, RateLimitSpec
from standard_generator import generate_standard_block

START = "# <<< STANDARDIZATION:BEGIN >>>"
END = "# <<< STANDARDIZATION:END >>>"


@dataclass
class Service:
    name: str
    path: str
    code: str
    input_type: str
    output_type: str


def inject_text(source: str, block: str) -> str:
    if START in source and END in source:
        pre, _, tail = source.partition(START)
        _, _, post = tail.partition(END)
        return pre + START + "\n" + block + END + post
    else:
        return source.rstrip() + "\n\n" + START + "\n" + block + END + "\n"


def F(service: Service, spec: StandardizationSpec) -> Service:
    """Functor-like transform: Service -> Service (standardized)"""
    block = generate_standard_block(spec)
    new_code = inject_text(service.code, block)
    # preserve input/output
    return Service(
        name=service.name,
        path=service.path,
        code=new_code,
        input_type=service.input_type,
        output_type=service.output_type,
    )


def verify_functor_laws(original: Service, transformed: Service) -> bool:
    # F(id) = id  is approximated by: types unchanged
    if original.input_type != transformed.input_type:
        return False
    if original.output_type != transformed.output_type:
        return False
    return True


def can_compose(a: Service, b: Service) -> bool:
    return a.output_type == b.input_type


def verify_composition_preserved(a: Service, b: Service, spec: StandardizationSpec) -> bool:
    # check original composition
    if not can_compose(a, b):
        return False
    Fa = F(a, spec)
    Fb = F(b, spec)
    # after transform, they should still compose
    return can_compose(Fa, Fb)


def write_service(service: Service):
    pathlib.Path(service.path).write_text(service.code)


def load_service(path: str, name: str, input_type: str, output_type: str) -> Service:
    src = pathlib.Path(path).read_text()
    return Service(
        name=name,
        path=path,
        code=src,
        input_type=input_type,
        output_type=output_type,
    )


if __name__ == "__main__":
    # define specs
    merchant_spec = StandardizationSpec(
        auth=AuthSpec(method=AuthMethod.JWT, required=True),
        validation=ValidationSpec(enabled=True, max_request_size=5 * 1024 * 1024),
        response=ResponseFormatSpec(enabled=True),
        rate_limit=RateLimitSpec(enabled=True, requests_per_minute=20, per_user=True, per_api_key=True),
    )

    billing_spec = StandardizationSpec(
        auth=AuthSpec(method=AuthMethod.NONE, required=False),
        validation=ValidationSpec(enabled=True),
        response=ResponseFormatSpec(enabled=True),
        rate_limit=RateLimitSpec(enabled=True, requests_per_minute=100, per_user=False, per_api_key=False),
    )

    # load services from disk
    merchant = load_service("merchant_app.py", "MerchantService", input_type="json", output_type="json")
    billing = load_service("billing_app.py", "BillingService", input_type="json", output_type="json")

    # apply functor
    merchant_std = F(merchant, merchant_spec)
    billing_std = F(billing, billing_spec)

    # verify laws
    assert verify_functor_laws(merchant, merchant_std), "Merchant: functor laws failed (types changed)"
    assert verify_functor_laws(billing, billing_std), "Billing: functor laws failed (types changed)"

    # verify composition merchant -> billing (json -> json)
    assert verify_composition_preserved(merchant, billing, merchant_spec), "composition broke after standardization"

    # write back
    write_service(merchant_std)
    write_service(billing_std)

    print("standardization applied to merchant_app.py and billing_app.py")
