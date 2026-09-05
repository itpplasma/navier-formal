# navier-formal

Lean 4 formalization of checkpoint CP1 of a private research programme on the
three-dimensional incompressible Navier–Stokes Cauchy problem. CP1 is the
manuscript's conditional route: energy identity, critical scaling, cubic
enstrophy inequality, signed critical pressure balance, low-frequency pressure
bound, cubic gradient-quotient functional, and the theorem that a finite-horizon
a priori `L³` bound implies Clay alternative A. The arbitrary-data critical
bound is an explicit hypothesis. No solution of the Millennium problem is
claimed here or in the companion repositories.

Companion repositories: `itpplasma/navier` (research dossier, live status in
`PLAN.md`) and `itpplasma/navier-paper` (manuscript). Layout follows the
Palomar template: `Challenge.lean` states the advertised results with
Mathlib-only imports, `Solution.lean` proves them, `comparator.json` names the
compared declarations, `formalization.yaml` records metadata.

Build with `lake build` (Lean `v4.33.1`, Mathlib `v4.33.1`). Status and axiom
reports are in `docs/verification-status.md`; literature inputs in
`docs/literature-assumptions.yaml`; the paper-to-Lean correspondence in
`docs/paper-lean-specification.md`. The repository is private.
