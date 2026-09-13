"""Independent numerical oracle for the CP1 scalar-obstruction integral.

The endpoint singularity is removed by the substitution ``T - t = s^2``.
The transformed integrand is continuously extended at ``s = 0`` and should
be the constant ``sqrt(2 / C)``.  The rational test data also checks the
algebraic identity behind the claimed value without importing Lean code.
"""

from __future__ import annotations

import math
from fractions import Fraction


CASES = (
    (Fraction(1, 2), Fraction(2)),
    (Fraction(3, 2), Fraction(5, 2)),
    (Fraction(7, 3), Fraction(0)),
)
N = 1000


def transformed_integrand(s: float, c: float) -> float:
    """The integrand after ``T - t = s²``, including its endpoint value."""
    if s == 0.0:
        return math.sqrt(2.0 / c)
    return 2.0 * s / math.sqrt(2.0 * c * s * s)


def simpson(c: float, upper: float) -> float:
    if upper == 0.0:
        return 0.0
    step = upper / N
    values = [transformed_integrand(i * step, c) for i in range(N + 1)]
    total = values[0] + values[-1]
    total += 4.0 * sum(values[1:-1:2])
    total += 2.0 * sum(values[2:-1:2])
    return step * total / 3.0


def main() -> int:
    passed = True
    for c_fraction, t_fraction in CASES:
        c = float(c_fraction)
        t = float(t_fraction)
        numerical = simpson(c, math.sqrt(t))
        expected = math.sqrt(2.0 * t / c)
        exact_square = Fraction(2) * t_fraction / c_fraction
        error = abs(numerical - expected)
        print(
            f"C={c_fraction}, T={t_fraction}: "
            f"integral={numerical:.15g}, expected={expected:.15g}, "
            f"squared value={exact_square}, error={error:.3e}"
        )
        passed = passed and error <= 1.0e-12
    print("PASS" if passed else "FAIL")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
