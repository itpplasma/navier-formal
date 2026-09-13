"""Independent arithmetic oracle for the CP1 L4/L3 supercriticality claim."""

from __future__ import annotations

from fractions import Fraction


def main() -> int:
    spacetime_sum = Fraction(2, 4) + Fraction(3, 3)
    critical_value = Fraction(3, 2)
    is_supercritical = Fraction(1, 1) < critical_value

    print(f"2/4 + 3/3 = {spacetime_sum}")
    print(f"1 < 3/2: {is_supercritical}")
    passed = spacetime_sum == critical_value and is_supercritical
    print("PASS" if passed else "FAIL")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
