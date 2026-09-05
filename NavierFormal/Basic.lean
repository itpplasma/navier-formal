import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Navier–Stokes checkpoint CP1: basic definitions

This module will carry the Mathlib-only definitions of the CP1 statement
surface: the three-dimensional state space, divergence-free Schwartz data,
classical solutions of the unforced Navier–Stokes equations on `ℝ³ × [0,T)`,
kinetic energy, and the critical `L³` quantity. Definitions land after the
CP01 statement-design audit recorded in
`itpplasma/navier:research/evidence/cp01-lean-statement-design.md`.

Nothing here is a theorem about the Millennium problem.
-/

namespace NavierFormal

/-- Three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

end NavierFormal
