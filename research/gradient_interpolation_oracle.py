"""Independent numerical oracle for the bounded gradient-interpolation route.

For a compactly supported smooth separable field U(x,y,z) =
(f(x)f(y)f(z), 0, 0), this checks the manuscript's interpolation inequality

    ||grad U||_3 <= ||grad U||_2**(1/2) ||grad U||_6**(1/2)

and independently checks the Hessian/Laplacian L2 identity used by the next
Sobolev step.  The script does not import Lean or inspect the formalization.
The Sobolev constant is intentionally not numerically identified: it is an
opaque Mathlib constant in the formal theorem, so this oracle tests the
computable interpolation behavior and the exact derivative-side bridge.
"""

from __future__ import annotations

import math
import sys


N = 240
LEFT = -1.0
RIGHT = 1.0


def profile(x: float) -> tuple[float, float, float]:
    """Return a smooth compactly supported profile and its first two derivatives."""
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
    mass = simpson([row[0] ** 2 for row in samples], step)
    grad_sq_1d = simpson([row[1] ** 2 for row in samples], step)
    hess_sq_1d = simpson([row[2] ** 2 for row in samples], step)
    cross_1d = simpson([row[0] * row[2] for row in samples], step)

    # Exact separable reductions for the L2 quantities.
    grad_l2_sq = 3.0 * grad_sq_1d * mass * mass
    hess_l2_sq = (
        3.0 * hess_sq_1d * mass * mass
        + 6.0 * grad_sq_1d * grad_sq_1d * mass
    )
    lap_l2_sq = 3.0 * hess_sq_1d * mass * mass + 6.0 * cross_1d * cross_1d * mass

    # The L3/L6 gradient norms are evaluated directly on a tensor Simpson mesh.
    grad_cube = []
    grad_sixth = []
    for fx, dfx, _ in samples:
        for fy, dfy, _ in samples:
            for fz, dfz, _ in samples:
                g2 = (dfx * fy * fz) ** 2 + (fx * dfy * fz) ** 2 + (fx * fy * dfz) ** 2
                grad_cube.append(g2 ** 1.5)
                grad_sixth.append(g2 ** 3.0)

    # Product Simpson weights, kept explicit so the oracle has no quadrature package.
    weights = [1.0 if i in (0, N) else (4.0 if i % 2 else 2.0) for i in range(N + 1)]
    weighted_cube = 0.0
    weighted_sixth = 0.0
    index = 0
    for i in range(N + 1):
        for j in range(N + 1):
            for k in range(N + 1):
                weight = weights[i] * weights[j] * weights[k]
                weighted_cube += weight * grad_cube[index]
                weighted_sixth += weight * grad_sixth[index]
                index += 1
    volume_factor = (step / 3.0) ** 3
    grad_l3 = (volume_factor * weighted_cube) ** (1.0 / 3.0)
    grad_l6 = (volume_factor * weighted_sixth) ** (1.0 / 6.0)
    grad_l2 = math.sqrt(grad_l2_sq)
    interpolation_rhs = math.sqrt(grad_l2) * math.sqrt(grad_l6)

    interpolation_gap = grad_l3 - interpolation_rhs
    identity_gap = abs(hess_l2_sq - lap_l2_sq)
    print(f"gradient interpolation gap: {interpolation_gap:.3e}")
    print(f"Hessian/Laplacian squared gap: {identity_gap:.3e}")
    print(f"empirical Jacobian Sobolev factor: {grad_l6 / math.sqrt(hess_l2_sq):.6g}")
    # The identity check is a three-dimensional Simpson approximation; the
    # tolerance is deliberately looser than the interpolation check while
    # remaining far below the displayed scale of either integral.
    passed = interpolation_gap <= 5.0e-10 and identity_gap <= 5.0e-9
    print("PASS" if passed else "FAIL")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
