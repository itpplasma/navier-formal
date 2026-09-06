import NavierFormal.Ode
import NavierFormal.Scaling
import NavierFormal.InterpolationMismatch

/-!
# Proofs of the advertised statements (Navier–Stokes checkpoint CP1)

Every declaration of `Challenge.lean` is re-declared here with an identical
type and proved.  This file deliberately does **not** import `Challenge`: the
comparator checks that the two modules declare the same names with the same
types, and that the proofs here use only the permitted axioms
`propext`, `Quot.sound`, `Classical.choice`.

The statement text below is byte-identical to `Challenge.lean`; only the
proofs differ.  Each proof discharges the statement from the corresponding
declaration of the `NavierFormal` development:

| advertised | development |
| --- | --- |
| `eLpNorm_dilation` | `NavierFormal.eLpNorm_dilate` |
| `eLpNorm_dilation_slice` | `NavierFormal.eLpNorm_dilateSpaceTime` |
| `eLpNorm_dilation_three` | `NavierFormal.eLpNorm_dilate_three` |
| `eLpNorm_dilation_two_sq` | `NavierFormal.eLpNorm_dilate_two_sq` |
| `exists_memLp_four_not_memLp_top` | `NavierFormal.exists_memLp_four_not_memLp_top` |
| `exists_memLp_four_eLpNorm_top_eq_top` | `NavierFormal.exists_memLp_four_eLpNorm_top_eq_top` |
| `L4L3_supercritical` | `NavierFormal.L4L3_supercritical` |
| `scalar_obstruction_exists` | `NavierFormal.scalar_obstruction_exists` |
| `integral_scalar_obstruction` | `NavierFormal.integral_scalarObstruction` |

Only `NavierFormal/Ode.lean`, `NavierFormal/Scaling.lean` and
`NavierFormal/InterpolationMismatch.lean` are imported, so the advertised
surface depends on no other module of the development.
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
  exact NavierFormal.eLpNorm_dilate v hq0 hq hlam

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
  exact NavierFormal.eLpNorm_dilateSpaceTime u t hq0 hq hlam

/-- **Manuscript Proposition `prop:scaling`(ii), first consequence: `L³` is
invariant under the critical dilation.**  `‖λ v(λ ·)‖₃ = ‖v‖₃`. -/
theorem eLpNorm_dilation_three
    (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (fun x => lam • v (lam • x)) 3 volume = eLpNorm v 3 volume := by
  exact NavierFormal.eLpNorm_dilate_three v hlam

/-- **Manuscript Proposition `prop:scaling`(ii), second consequence: the
kinetic-energy norm is not invariant.**  `‖λ v(λ ·)‖₂² = λ⁻¹ ‖v‖₂²`, which is
the manuscript's `‖u_λ(t)‖₂² = λ⁻¹ ‖u(λ² t)‖₂²`. -/
theorem eLpNorm_dilation_two_sq
    (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (fun x => lam • v (lam • x)) 2 volume ^ 2
      = ENNReal.ofReal lam⁻¹ * eLpNorm v 2 volume ^ 2 := by
  exact NavierFormal.eLpNorm_dilate_two_sq v hlam

/-- **Manuscript Remark `rem:mismatch`(a) (the interpolation mismatch).**  For
every `T > 0` there is a scalar function on `(0,T)` that lies in `L⁴(0,T)` but
not in `L^∞(0,T)`; hence the `L⁴_t L³_x` bound `eq:L4L3` cannot yield a bound on
`sup_{t<T} ‖u(t)‖₃`.  The manuscript's witness is `g(t) = t^{-1/5}`. -/
theorem exists_memLp_four_not_memLp_top {T : ℝ} (hT : 0 < T) :
    ∃ g : ℝ → ℝ, MemLp g 4 (volume.restrict (Set.Ioo 0 T)) ∧
      ¬ MemLp g ⊤ (volume.restrict (Set.Ioo 0 T)) := by
  exact NavierFormal.exists_memLp_four_not_memLp_top hT

/-- **Manuscript Remark `rem:mismatch`(a), essential-supremum form.**  The same
witness has infinite `L^∞(0,T)` seminorm while lying in `L⁴(0,T)`, which is the
manuscript's `ess sup_{(0,T)} g = ∞`. -/
theorem exists_memLp_four_eLpNorm_top_eq_top {T : ℝ} (hT : 0 < T) :
    ∃ g : ℝ → ℝ, MemLp g 4 (volume.restrict (Set.Ioo 0 T)) ∧
      eLpNorm g ⊤ (volume.restrict (Set.Ioo 0 T)) = ⊤ := by
  exact NavierFormal.exists_memLp_four_eLpNorm_top_eq_top hT

/-- **Manuscript Remark `rem:mismatch`(b) (supercriticality).**  The
Ladyzhenskaya–Prodi–Serrin sum of the spacetime norm of `eq:L4L3`, with
`(r,q) = (4,3)`, is `2/4 + 3/3 = 3/2`, which exceeds the critical value `1`. -/
theorem L4L3_supercritical : (2 : ℝ) / 4 + (3 : ℝ) / 3 = 3 / 2 ∧ (1 : ℝ) < 3 / 2 := by
  exact NavierFormal.L4L3_supercritical

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
  exact NavierFormal.scalar_obstruction_exists hC hT

/-- **Manuscript Proposition `prop:ode`, proof value.**  The witness
`y(t) = (2C(T-t))^{-1/2}` of `prop:ode` has `∫_0^T y(t) dt = √(2T/C)`, the
value computed in the manuscript's proof. -/
theorem integral_scalar_obstruction {C T : ℝ} (hC : 0 < C) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (2 * C * (T - t)) ^ (-(1 / 2) : ℝ) = Real.sqrt (2 * T / C) := by
  exact NavierFormal.integral_scalarObstruction hC hT

end NavierFormal.CP1
