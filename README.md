# navier-formal

Lean 4 formalization of checkpoint CP1 of a research programme on the
three-dimensional incompressible Navier–Stokes Cauchy problem. CP1 is an
internal manuscript route: energy identity, critical scaling, cubic enstrophy
inequality, signed critical pressure balance, low-frequency pressure bound,
cubic gradient-quotient functional, and the theorem that a finite-horizon a
priori `L³` bound implies Clay alternative A. The arbitrary-data critical bound
is an explicit hypothesis. No solution of the Millennium problem is claimed
here or in the companion repositories.

Companion repository: [itpplasma/navier](https://github.com/itpplasma/navier)
contains the research dossier, live `PLAN.md`, and public manuscript sources
in [paper/](https://github.com/itpplasma/navier/tree/main/paper). The former
`navier-paper` repository was archived on 2026-09-09.
The manuscript, research dossier, and Lean development are records of the same
ongoing project, not separate prior publications or presentations. Their dated
chronology is retained for provenance and review. Layout follows the Palomar
template: `Challenge.lean` states the advertised results with Mathlib-only
imports, `Solution.lean` proves them, `comparator.json` names the compared
declarations, `formalization.yaml` records metadata.

Build with `lake build` (Lean `v4.34.0-rc2`, Mathlib `v4.34.0-rc2`, commit
`85e3a25e`; pinned to match the Solution-only external dependency
`openai/NavierStokesAndEuler@8937a8f4`, Apache-2.0, which only modules under
`NavierFormal/External/` may import; see `docs/external-openai-audit.md`). Status and axiom
reports are in `docs/verification-status.md`; literature inputs in
`docs/literature-assumptions.yaml`; the internal-proof-to-Lean correspondence
in `docs/paper-lean-specification.md`. The repository was made public on
2026-09-08 under Apache-2.0 as a documented record of the work before and
after OpenAI's forced-blowup release of the same day.

## Public status and disclaimer (2026-09-08)

No solution of the Millennium problem, no priority claim, and no dependence
of any unforced statement on the forced OpenAI result is asserted. Advertised
Palomar surface: nine CP1 statements are advertised. `Solution.lean` proves
all nine from Mathlib, while `Challenge.lean` intentionally retains six
interface placeholders. The
conditional theorem `NavierFormal.conditional_clay_A_of_tao`
(`CriticalHypothesis → ClayAlternativeA_all`) is Phase I over exactly two
named literature axioms, `NavierFormal.Literature.taoLocalTheory` and
`NavierFormal.Literature.endpointContinuation`, kept in the separate library
`NavierFormalConditional`. The research context, status and allocation are in
the companion repository `itpplasma/navier` (`PLAN.md`). The manuscript
sources are public in that repository's `paper/` directory; `navier-paper` is
historical.

## Proof map

The current route is: CP1 statement surface in `Challenge.lean` → Mathlib-only
solutions in `Solution.lean` → conditional literature bridge
`NavierFormalConditional` → the paper's critical `L³` producer. The first two
surfaces contain checked pieces. Estimate `eq:L4L3`, the pressure integral
closure, the finite-horizon critical bound, and remaining endpoint hypotheses
remain open as recorded
in `docs/verification-status.md` and the live plan in `../navier/PLAN.md`.

## Blockers for anyone continuing this work

Formal, in order of value:

1. `‖D²u‖₂ = ‖Δu‖₂` for compactly supported smooth `u` on `ℝ³` (Hilbert–Schmidt
   square of the Hessian). `NavierFormal/HessianLaplacianL2.lean` now proves
   the exact integrated identity under an explicit whole-space
   integration-by-parts package, with an independent Gaussian oracle. The
   `NavierFormal/CompactSupportIBP/Adapter.lean` now derives all seven explicit
   IBP integrability fields from compact support and pointwise `C³`; its
   independent bump-function oracle passes. The remaining bridge is deriving
   the required pointwise `C³`/IBP data from the manuscript's compact-support/
   `H²` hypotheses. Under the explicit `CompactSupportC3Hypotheses` package,
   `CompactSupportIBP/GradientInterpolation.lean` now proves the bounded
   operator-norm Jacobian Sobolev/interpolation step and has an independent
   bump-function oracle. `CompactSupportIBP/FiniteDimensionalNormBridge.lean`
   now lifts the operator/Frobenius comparison to the relevant eLpNorms and
   specializes it to Jacobian fields, with an independent exact oracle. The
   manuscript-level H²-to-C³/IBP bridge and critical `L³` producer remain open.
   `HessianLaplacianEnstrophy.lean` now derives the exact `ha2` input for the
   enstrophy consumer from explicit IBP data, with a trust-zero consumer check
   and independent Gaussian oracle. The pinned target build replays the
   bounded route only. The disjoint
   `CompactSupportIBP/BoundedEnstrophyConsumer.lean` packages `ha2`, the
   bounded Jacobian interpolation estimate, and the verified Jacobian norm
   interfaces under the same explicit hypotheses.
2. Discharge the four explicit hypotheses of `endpointContinuation_of_ess`
   (uniform `L²` bound, identification of the abstract enstrophy with the
   gradient norm, `SerrinHypotheses`, interval-integral monotonicity) from
   `taoLocalTheory`, so that `conditional_clay_A` depends on `taoLocalTheory`
   and `essL3ToL5` only.
3. `lem:R-consequences`(a): the `L²` difference-quotient limit of `u` in time
   from the regularity package alone (needs a Bochner Taylor remainder with
   Minkowski's integral inequality); currently a clause of `taoLocalTheory`.
4. Formalize the Leray–Hopf weak-solution class so that `essL3ToL5` can be
   split into ESS Theorem 1.3 verbatim plus a proved `lem:leray-hopf`.
5. Phase II of `taoLocalTheory` (local classical theory for Schwartz data):
   standard PDE, absent from Mathlib, large.
6. Statement surface: `IsClassicalSolution` has no integrability class, so
   `CriticalBound` quantifies over a wider family than the manuscript's
   `hyp:critical`; the direction `hyp:critical → CriticalBound` needs
   uniqueness in the class.

Mathematical: the only open input of the positive route is the finite-horizon
critical `L³` bound `hyp:critical`; nothing in either repository produces it.
