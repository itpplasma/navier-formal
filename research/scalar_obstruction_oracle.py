"""Independent numerical oracle for the CP1 scalar ODE witness.

The witness is ``y(t) = (2*C*(T-t))**(-1/2)`` on ``0 <= t < T``.
The checks below use only the explicit formula: a finite-difference check
tests the differential equation, the substitution ``T-t=s^2`` tests the
finite integral, and shrinking positive gaps to ``T`` tests blow-up.
"""

from __future__ import annotations

import math
from fractions import Fraction


CASES = (
    (Fraction(1, 2), Fraction(2)),
    (Fraction(3, 2), Fraction(5, 2)),
    (Fraction(7, 3), Fraction(4, 5)),
)
STEPS = 2000


def witness(c: float, t: float, terminal: float) -> float:
    return (2.0 * c * (terminal - t)) ** -0.5


def simpson_after_substitution(c: float, terminal: float) -> float:
    """Integrate after ``T-t=s^2``; the transformed integrand is constant."""
    upper = math.sqrt(terminal)
    if upper == 0.0:
        return 0.0

    def transformed(s: float) -> float:
        if s == 0.0:
            return math.sqrt(2.0 / c)
        return 2.0 * s * witness(c, terminal - s * s, terminal)

    step = upper / STEPS
    values = [transformed(i * step) for i in range(STEPS + 1)]
    total = values[0] + values[-1]
    total += 4.0 * sum(values[1:-1:2])
    total += 2.0 * sum(values[2:-1:2])
    return step * total / 3.0


def main() -> int:
    passed = True
    for c_fraction, t_fraction in CASES:
        c = float(c_fraction)
        terminal = float(t_fraction)
        interior = 0.37 * terminal
        h = 1.0e-6 * terminal
        numerical_derivative = (
            witness(c, interior + h, terminal)
            - witness(c, interior - h, terminal)
        ) / (2.0 * h)
        rhs = c * witness(c, interior, terminal) ** 3
        ode_error = abs(numerical_derivative - rhs)

        numerical_integral = simpson_after_substitution(c, terminal)
        expected_integral = math.sqrt(2.0 * terminal / c)
        integral_error = abs(numerical_integral - expected_integral)

        tail_values = [witness(c, terminal - terminal / (10**k), terminal)
                       for k in (1, 2, 3, 4)]
        blows_up = all(a < b for a, b in zip(tail_values, tail_values[1:]))

        exact_squared_value = Fraction(2) * t_fraction / c_fraction
        print(
            f"C={c_fraction}, T={t_fraction}: "
            f"ODE error={ode_error:.3e}, integral error={integral_error:.3e}, "
            f"integral²={exact_squared_value}, increasing tail={blows_up}"
        )
        passed = passed and ode_error <= 1.0e-8
        passed = passed and integral_error <= 1.0e-12
        passed = passed and blows_up

    print("PASS" if passed else "FAIL")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
