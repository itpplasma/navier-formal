#!/usr/bin/env python3
"""Independent oracle for the consumer-facing Hessian ``ha2`` bookkeeping.

For the nonzero vector Gaussian

    u(x) = (exp(-|x|^2/2), x_1 exp(-|x|^2/2), 0),

the Hessian and Laplacian squared integrals are evaluated from Gaussian
moments.  The oracle then checks the exact consumer choice
``a = sqrt(integral |D^2 u|_F^2)`` and verifies ``a^2 = integral |Delta u|^2``.
It does not import or inspect the Lean development.
"""

from fractions import Fraction
from math import prod, sqrt


def gaussian_even_moment(power: int) -> Fraction:
    if power % 2:
        return Fraction(0)
    n = power // 2
    return Fraction(prod(range(1, 2 * n, 2)), 2**n)


def gaussian_moment(exponents: tuple[int, int, int]) -> Fraction:
    return prod(gaussian_even_moment(p) for p in exponents)


def add_monomial(target: dict[tuple[int, int, int], Fraction],
                 exponents: tuple[int, int, int], coefficient: Fraction) -> None:
    target[exponents] = target.get(exponents, Fraction(0)) + coefficient


def gaussian_square_integral(polynomial: dict[tuple[int, int, int], Fraction]) -> Fraction:
    result = Fraction(0)
    for left_exp, left_coeff in polynomial.items():
        for right_exp, right_coeff in polynomial.items():
            exponents = tuple(a + b for a, b in zip(left_exp, right_exp))
            result += left_coeff * right_coeff * gaussian_moment(exponents)
    return result


def main() -> None:
    # Each derivative entry is a polynomial times exp(-|x|^2/2); squaring
    # contributes exp(-|x|^2), so Gaussian moments suffice.
    hessian_sq = Fraction(0)
    laplacian_sq = Fraction(0)
    for component in range(2):
        for i in range(3):
            for j in range(3):
                polynomial: dict[tuple[int, int, int], Fraction] = {}
                if component == 0:
                    if i == j:
                        add_monomial(polynomial, (0, 0, 0), Fraction(-1))
                    exponents = tuple((k == i) + (k == j) for k in range(3))
                    add_monomial(polynomial, exponents, Fraction(1))
                else:
                    # u_1 = x_1 exp(-|x|^2/2), with the product rule applied
                    # twice: d_i d_j u_1 = (x1 xi xj - δij x1
                    # - δi1 xj - δj1 xi) exp(-|x|^2/2).
                    add_monomial(polynomial, tuple((k == 0) + (k == i) + (k == j)
                                                    for k in range(3)), Fraction(1))
                    if i == j:
                        add_monomial(polynomial, (1, 0, 0), Fraction(-1))
                    if i == 0:
                        add_monomial(polynomial, tuple(1 if k == j else 0 for k in range(3)), Fraction(-1))
                    if j == 0:
                        add_monomial(polynomial, tuple(1 if k == i else 0 for k in range(3)), Fraction(-1))
                hessian_sq += gaussian_square_integral(polynomial)

        laplacian: dict[tuple[int, int, int], Fraction] = {}
        if component == 0:
            add_monomial(laplacian, (0, 0, 0), Fraction(-3))
            for i in range(3):
                add_monomial(laplacian, tuple(2 if k == i else 0 for k in range(3)), Fraction(1))
        else:
            add_monomial(laplacian, (1, 0, 0), Fraction(-5))
            for i in range(3):
                add_monomial(laplacian, tuple((k == 0) + (2 if k == i else 0)
                                                for k in range(3)), Fraction(1))
        laplacian_sq += gaussian_square_integral(laplacian)

    assert hessian_sq == laplacian_sq, (hessian_sq, laplacian_sq)
    a = sqrt(float(hessian_sq))
    assert abs(a * a - float(laplacian_sq)) < 1.0e-12
    print(f"nonzero vector Gaussian: both normalized integrals = {hessian_sq}")
    print(f"consumer a = sqrt({hessian_sq}); a^2 = {laplacian_sq}")
    print("PASS")


if __name__ == "__main__":
    main()
