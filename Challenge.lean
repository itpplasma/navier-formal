import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Advertised statements (Navier–Stokes checkpoint CP1)

This is the small trusted surface a mathematical reader audits.  It imports
Mathlib only: every object below is a Mathlib definition, so reading this file
requires no knowledge of the `NavierFormal` development, and the file
introduces no definition of its own.  Each statement is proved in
`Solution.lean`, which re-declares it with an identical type.

The advertised block is the scaling/obstruction material of the manuscript
`../navier-paper/main.tex` that is proved from Mathlib today:

* Proposition `prop:scaling`(ii), the critical-dilation norm identity
  `‖λ v(λ ·)‖_q = λ^{1-3/q}‖v‖_q` for `0 < q < ∞`, its fixed-time form for
  `u_λ(x,t) = λ u(λ x, λ² t)`, and the two consequences the manuscript draws
  from it (`L³` invariant, `‖·‖₂²` scaling by `λ⁻¹`);
* Remark `rem:mismatch`, both halves of the interpolation mismatch inside the
  proof of `prop:scaling`;
* Proposition `prop:ode`, the scalar obstruction, together with the integral
  value `√(2T/C)` computed in its proof.

Nothing here is a theorem about the Millennium problem, and nothing here
asserts a solution, a blowup, or a global regularity statement for the
Navier–Stokes equations.  Deliberately **not** advertised: the PDE half of
`prop:scaling`(i), the estimate `eq:L4L3`, the endpoint `q = ∞` of
`eq:scaling-norm`, and every other labelled manuscript result
(`prop:energy`, `prop:enstrophy`, `prop:pressure`, `prop:lowpressure`,
`thm:continuation`, `thm:conditional`, `sec:quotient`).
-/

open MeasureTheory

open scoped ENNReal NNReal

namespace NavierFormal.CP1

/-- **Manuscript Proposition `prop:scaling`(ii), identity `eq:scaling-norm`,
for `0 < q < ∞`.**  Under the critical spatial dilation `v ↦ λ v(λ ·)` on `ℝ³`
the Lebesgue norms scale by `λ^{1-3/q}`:
`‖λ v(λ ·)‖_q = λ^{1-3/q} ‖v‖_q`.
Both sides are allowed to be `+∞`, and no measurability of `v` is assumed.
The endpoint `q = ∞` of the manuscript statement is **not** advertised. -/
theorem eLpNorm_dilation
    (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {q : ℝ≥0∞}
    (hq0 : q ≠ 0) (hq : q ≠ ∞) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (fun x => lam • v (lam • x)) q volume
      = ENNReal.ofReal (lam ^ (1 - 3 / q.toReal)) * eLpNorm v q volume := by
  sorry

/-- **Manuscript Proposition `prop:scaling`(ii), consequence for the rescaled
field `u_λ(x,t) = λ u(λ x, λ² t)`, for `0 < q < ∞`.**  At each fixed time `t`,
`‖u_λ(t)‖_q = λ^{1-3/q} ‖u(λ² t)‖_q`.
This is the norm identity applied to the time slice; it makes no claim that
`u_λ` solves the Navier–Stokes system, which is the PDE half of
`prop:scaling`(i) and is **not** advertised. -/
theorem eLpNorm_dilation_slice
    (u : ℝ × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (t : ℝ) {q : ℝ≥0∞}
    (hq0 : q ≠ 0) (hq : q ≠ ∞) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (fun x => lam • u (lam ^ 2 * t, lam • x)) q volume
      = ENNReal.ofReal (lam ^ (1 - 3 / q.toReal))
        * eLpNorm (fun x => u (lam ^ 2 * t, x)) q volume := by
  sorry

/-- **Manuscript Proposition `prop:scaling`(ii), first consequence: `L³` is
invariant under the critical dilation.**  `‖λ v(λ ·)‖₃ = ‖v‖₃`. -/
theorem eLpNorm_dilation_three
    (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (fun x => lam • v (lam • x)) 3 volume = eLpNorm v 3 volume := by
  sorry

/-- **Manuscript Proposition `prop:scaling`(ii), second consequence: the
kinetic-energy norm is not invariant.**  `‖λ v(λ ·)‖₂² = λ⁻¹ ‖v‖₂²`, which is
the manuscript's `‖u_λ(t)‖₂² = λ⁻¹ ‖u(λ² t)‖₂²`. -/
theorem eLpNorm_dilation_two_sq
    (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (fun x => lam • v (lam • x)) 2 volume ^ 2
      = ENNReal.ofReal lam⁻¹ * eLpNorm v 2 volume ^ 2 := by
  sorry

/-- **Manuscript Remark `rem:mismatch`(a) (the interpolation mismatch).**  For
every `T > 0` there is a scalar function on `(0,T)` that lies in `L⁴(0,T)` but
not in `L^∞(0,T)`; hence the `L⁴_t L³_x` bound `eq:L4L3` cannot yield a bound on
`sup_{t<T} ‖u(t)‖₃`.  The manuscript's witness is `g(t) = t^{-1/5}`. -/
theorem exists_memLp_four_not_memLp_top {T : ℝ} (hT : 0 < T) :
    ∃ g : ℝ → ℝ, MemLp g 4 (volume.restrict (Set.Ioo 0 T)) ∧
      ¬ MemLp g ⊤ (volume.restrict (Set.Ioo 0 T)) := by
  sorry

/-- **Manuscript Remark `rem:mismatch`(a), essential-supremum form.**  The same
witness has infinite `L^∞(0,T)` seminorm while lying in `L⁴(0,T)`, which is the
manuscript's `ess sup_{(0,T)} g = ∞`. -/
theorem exists_memLp_four_eLpNorm_top_eq_top {T : ℝ} (hT : 0 < T) :
    ∃ g : ℝ → ℝ, MemLp g 4 (volume.restrict (Set.Ioo 0 T)) ∧
      eLpNorm g ⊤ (volume.restrict (Set.Ioo 0 T)) = ⊤ := by
  sorry

/-- **Manuscript Remark `rem:mismatch`(b) (supercriticality).**  The
Ladyzhenskaya–Prodi–Serrin sum of the spacetime norm of `eq:L4L3`, with
`(r,q) = (4,3)`, is `2/4 + 3/3 = 3/2`, which exceeds the critical value `1`. -/
theorem L4L3_supercritical : (2 : ℝ) / 4 + (3 : ℝ) / 3 = 3 / 2 ∧ (1 : ℝ) < 3 / 2 := by
  sorry

/-- **Manuscript Proposition `prop:ode` (Scalar obstruction).**  For every
`C > 0` and `T > 0` there is a positive function `y` on `[0,T)`, differentiable
there with `y' = C y³`, integrable on `[0,T)`, and with `y t → ∞` as `t ↑ T`.

This is a statement about a scalar ODE only.  It is not a Navier–Stokes blowup
solution and no such solution is claimed; the proposition records the logical
point that `∫_0^{T} Y < ∞` together with `Y' ≤ C Y³` does not rule out
`Y → ∞`. -/
theorem scalar_obstruction_exists {C T : ℝ} (hC : 0 < C) (hT : 0 < T) :
    ∃ y : ℝ → ℝ,
      (∀ t ∈ Set.Ico (0 : ℝ) T, 0 < y t) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (C * (y t) ^ 3) t) ∧
      MeasureTheory.IntegrableOn y (Set.Ico 0 T) ∧
      Filter.Tendsto y (nhdsWithin T (Set.Iio T)) Filter.atTop := by
  sorry

/-- **Manuscript Proposition `prop:ode`, proof value.**  The witness
`y(t) = (2C(T-t))^{-1/2}` of `prop:ode` has `∫_0^T y(t) dt = √(2T/C)`, the
value computed in the manuscript's proof. -/
theorem integral_scalar_obstruction {C T : ℝ} (hC : 0 < C) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (2 * C * (T - t)) ^ (-(1 / 2) : ℝ) = Real.sqrt (2 * T / C) := by
  sorry

end NavierFormal.CP1
