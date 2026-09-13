#!/usr/bin/env python3
"""Independent exact oracle for the 3-by-3 norm-comparison bridge.

The selected matrices have an explicitly known spectral/operator norm, so the
check uses only integer arithmetic.  It tests the squared form used by the
Lean development:

    ||A||_op^2 <= ||A||_F^2 <= 3 ||A||_op^2.

This script does not import Lean or inspect the formalization.
"""

from __future__ import annotations


def frobenius_sq(matrix: tuple[tuple[int, ...], ...]) -> int:
    return sum(entry * entry for row in matrix for entry in row)


def main() -> int:
    # (matrix, exact operator-norm squared).  These are diagonal, rank-one,
    # or orthogonal-row examples, so the stated operator norms are immediate.
    examples = [
        (((0, 0, 0), (0, 0, 0), (0, 0, 0)), 0),
        (((1, 0, 0), (0, 1, 0), (0, 0, 1)), 1),
        (((1, 0, 0), (0, 2, 0), (0, 0, 2)), 4),
        (((-3, 0, 0), (0, 0, 0), (0, 0, 0)), 9),
        (((1, 1, 0), (0, 0, 0), (0, 0, 0)), 2),
    ]
    for matrix, operator_sq in examples:
        hilbert_schmidt_sq = frobenius_sq(matrix)
        assert operator_sq <= hilbert_schmidt_sq
        assert hilbert_schmidt_sq <= 3 * operator_sq
    print(f"checked {len(examples)} exact 3x3 examples")
    print("PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
