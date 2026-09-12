"""Independent numerical oracle for the compact-support IBP adapter.

The profile is the standard C-infinity bump exp(-1/(1-x^2)) on (-1, 1),
multiplied by a nonconstant polynomial.  Product quadrature checks both
the one-dimensional whole-line Green identity and the three-dimensional
separable identity

    integral |D^2 U|_F^2 = integral |Delta U|^2.

This file deliberately has no Lean-source or project import.
"""

from __future__ import annotations

import math
import sys


N = 1200  # deterministic even mesh for composite Simpson quadrature
LEFT = -1.0
RIGHT = 1.0


def profile(x: float) -> tuple[float, float, float]:
    """Return u, u', u'' for a compactly supported smooth surrogate."""
    if not (-1.0 < x < 1.0):
        return 0.0, 0.0, 0.0
    q = 1.0 - x * x
    bump = math.exp(-1.0 / q)
    g1 = -2.0 * x / (q * q)
    g2 = -2.0 / (q * q) - 8.0 * x * x / (q * q * q)
    bump1 = bump * g1
    bump2 = bump * (g2 + g1 * g1)
    poly = 1.0 + 0.3 * x + 0.2 * x * x
    poly1 = 0.3 + 0.4 * x
    poly2 = 0.4
    return (
        bump * poly,
        bump1 * poly + bump * poly1,
        bump2 * poly + 2.0 * bump1 * poly1 + bump * poly2,
    )


def simpson(values: list[float], step: float) -> float:
    if len(values) != N + 1 or N % 2:
        raise ValueError("invalid deterministic Simpson mesh")
    total = values[0] + values[-1]
    total += 4.0 * sum(values[1:-1:2])
    total += 2.0 * sum(values[2:-1:2])
    return step * total / 3.0


def main() -> int:
    step = (RIGHT - LEFT) / N
    samples = [profile(LEFT + i * step) for i in range(N + 1)]
    u = [row[0] for row in samples]
    du = [row[1] for row in samples]
    ddu = [row[2] for row in samples]

    mass = simpson([value * value for value in u], step)
    grad_sq = simpson([value * value for value in du], step)
    hess_sq_1d = simpson([value * value for value in ddu], step)
    green_rhs = -simpson([u[i] * ddu[i] for i in range(N + 1)], step)
    boundary = u[-1] * du[-1] - u[0] * du[0]

    # For U(x,y,z) = u(x)u(y)u(z), separability gives these exact reductions.
    hessian_sq_3d = 3.0 * hess_sq_1d * mass * mass + 6.0 * grad_sq * grad_sq * mass
    cross = simpson([u[i] * ddu[i] for i in range(N + 1)], step)
    laplacian_sq_3d = 3.0 * hess_sq_1d * mass * mass + 6.0 * cross * cross * mass

    checks = {
        "1D Green identity": abs(grad_sq - green_rhs),
        "vanishing boundary term": abs(boundary),
        "3D Hessian/Laplacian identity": abs(hessian_sq_3d - laplacian_sq_3d),
    }
    tolerance = 2.0e-9
    for name, error in checks.items():
        print(f"{name}: error={error:.3e}")
    passed = all(error <= tolerance for error in checks.values())
    print("PASS" if passed else "FAIL")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
