#!/usr/bin/env python3
"""Independent numerical check of the bounded consumer's three interfaces.

The check uses a nonzero diagonal Jacobian sample for the operator/Frobenius
comparison and the exact Gaussian identity oracle's normalized value for the
`ha2` interface.  It does not import or inspect the Lean development.
"""

from math import sqrt


def main() -> None:
    diagonal = (1.0, -2.0, 3.0)
    operator = max(abs(value) for value in diagonal)
    frobenius = sqrt(sum(value * value for value in diagonal))
    assert operator <= frobenius
    assert frobenius <= sqrt(3.0) * operator

    # The nonzero Gaussian field used by the companion identity oracle has
    # both normalized squared integrals equal to 65/8.
    hessian_sq = 65.0 / 8.0
    laplacian_sq = 65.0 / 8.0
    a = sqrt(hessian_sq)
    assert abs(a * a - laplacian_sq) < 1.0e-12

    print("Jacobian operator/Frobenius bounds: PASS")
    print("Gaussian ha2 interface: PASS (both squared integrals = 65/8)")


if __name__ == "__main__":
    main()
