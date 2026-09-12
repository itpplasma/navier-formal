#!/usr/bin/env python3
"""Independent exact oracle for the Hessian--Laplacian L2 identity.

For the rapidly decaying vector field

    u(x) = (exp(-|x|^2/2), 0, 0),

the script derives both sides from Gaussian moments.  It does not import or
inspect the Lean development: the equality is checked from the explicit
derivative formulas and the moments of exp(-|x|^2) on R^3.
"""

from fractions import Fraction
from math import prod


def gaussian_even_moment(power: int) -> Fraction:
    """E[x**power] for the normalized one-dimensional exp(-x^2) measure."""
    if power % 2:
        return Fraction(0)
    # The unnormalized moments satisfy I_(2n) / I_0 = (2n-1)!! / 2^n.
    n = power // 2
    return Fraction(prod(range(1, 2 * n, 2)), 2**n)


def gaussian_moment(exponents: tuple[int, int, int]) -> Fraction:
    """Normalized R^3 moment under the product density exp(-|x|^2)."""
    return prod(gaussian_even_moment(p) for p in exponents)


def main() -> None:
    # Hessian entries of exp(-|x|^2/2) are (x_i*x_j - delta_ij) exp(-|x|^2/2).
    hessian_sq = Fraction(0)
    for i in range(3):
        for j in range(3):
            if i == j:
                # E[(x_i^2 - 1)^2].
                entry = (gaussian_moment(tuple(4 if k == i else 0 for k in range(3)))
                         - 2 * gaussian_moment(tuple(2 if k == i else 0 for k in range(3)))
                         + gaussian_moment((0, 0, 0)))
            else:
                # E[x_i^2*x_j^2].
                entry = gaussian_moment(tuple(2 if k in (i, j) else 0 for k in range(3)))
            hessian_sq += entry

    # Δ exp(-|x|^2/2) = (|x|^2 - 3) exp(-|x|^2/2).
    r2 = sum(gaussian_moment(tuple(2 if k == i else 0 for k in range(3))) for i in range(3))
    r4 = sum(
        gaussian_moment(tuple(4 if k == i else 0 for k in range(3))) for i in range(3)
    ) + 2 * sum(
        gaussian_moment(tuple(2 if k in (i, j) else 0 for k in range(3)))
        for i in range(3) for j in range(i + 1, 3)
    )
    laplacian_sq = r4 - 6 * r2 + 9 * gaussian_moment((0, 0, 0))

    assert hessian_sq == Fraction(15, 4), hessian_sq
    assert laplacian_sq == Fraction(15, 4), laplacian_sq
    print("Gaussian model: both normalized integrals = 15/4")
    print("Common unnormalized value: (15/4) * pi^(3/2)")


if __name__ == "__main__":
    main()
