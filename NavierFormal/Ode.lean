import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The scalar obstruction of `prop:ode`

This module formalizes Proposition `prop:ode` (Scalar obstruction) of the
manuscript `../navier-paper/main.tex`: for every `C > 0` and `T > 0` there is a
positive differentiable `y : [0, T) → (0, ∞)` with `y' = C y ^ 3`,
`∫_0^T y < ∞`, and `y t → ∞` as `t ↑ T`.  The witness is the manuscript's,
`y t = (2 C (T - t)) ^ (-1/2)`, with a real exponent as in the paper.

The exact value `∫_0^T y = √(2T/C)` computed in the manuscript's proof is
recorded as `NavierFormal.integral_scalarObstruction`.

**Remark.**  As the manuscript states immediately after `prop:ode`, this is not
a model of a Navier–Stokes singularity and nothing here is a blowup solution of
the Navier–Stokes equations.  The proposition proves only the logical point that
the two scalar consequences `∫_0^{T_*} Y < ∞` and `Y' ≤ C_ν Y ^ 3` do not by
themselves rule out `Y → ∞`.
-/

namespace NavierFormal

open MeasureTheory Set Filter Topology

variable {C T : ℝ}

/-- The witness of Proposition `prop:ode` (Scalar obstruction) of the
manuscript: `y t = (2 C (T - t)) ^ (-1/2)`, with the real exponent `-1/2` of the
paper.  This is a scalar comparison profile, not a Navier–Stokes solution. -/
noncomputable def scalarObstruction (C T : ℝ) : ℝ → ℝ :=
  fun t => (2 * C * (T - t)) ^ (-(1 / 2) : ℝ)

/-- Auxiliary positivity of the base `2 C (T - t)` used throughout
Proposition `prop:ode`. -/
theorem scalarObstruction_base_pos (hC : 0 < C) {t : ℝ} (ht : t < T) :
    0 < 2 * C * (T - t) :=
  mul_pos (by linarith) (sub_pos.mpr ht)

/-- Positivity in Proposition `prop:ode`: the profile maps `[0, T)` into
`(0, ∞)`. -/
theorem scalarObstruction_pos (hC : 0 < C) {t : ℝ} (ht : t < T) :
    0 < scalarObstruction C T t :=
  Real.rpow_pos_of_pos (scalarObstruction_base_pos hC ht) _

/-- The differential equation `y' = C y ^ 3` of Proposition `prop:ode`, in the
form of a genuine (two-sided) derivative at every `t ∈ [0, T)`. -/
theorem hasDerivAt_scalarObstruction (hC : 0 < C) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt (scalarObstruction C T) (C * (scalarObstruction C T t) ^ 3) t := by
  intro t ht
  have hx : 0 < 2 * C * (T - t) := scalarObstruction_base_pos hC ht.2
  have hu : HasDerivAt (fun s : ℝ => 2 * C * (T - s)) (2 * C * (-1)) t :=
    ((hasDerivAt_id t).const_sub T).const_mul (2 * C)
  have hcomp :
      HasDerivAt (fun s : ℝ => (2 * C * (T - s)) ^ (-(1 / 2) : ℝ))
        ((2 * C * (-1)) * (-(1 / 2) : ℝ) * (2 * C * (T - t)) ^ ((-(1 / 2) : ℝ) - 1)) t :=
    hu.rpow_const (Or.inl hx.ne')
  have hcube : (scalarObstruction C T t) ^ 3 = (2 * C * (T - t)) ^ (-(3 / 2) : ℝ) := by
    rw [scalarObstruction, ← Real.rpow_natCast ((2 * C * (T - t)) ^ (-(1 / 2) : ℝ)) 3,
      ← Real.rpow_mul hx.le]
    norm_num
  have hexp : (-(1 / 2) : ℝ) - 1 = (-(3 / 2) : ℝ) := by norm_num
  rw [hexp] at hcomp
  rw [hcube, show C * (2 * C * (T - t)) ^ (-(3 / 2) : ℝ)
      = 2 * C * (-1) * (-(1 / 2) : ℝ) * (2 * C * (T - t)) ^ (-(3 / 2) : ℝ) by ring]
  exact hcomp

/-- Interval integrability of the profile of Proposition `prop:ode` on
`[0, T]`; this is the finiteness `∫_0^T y < ∞` of the proposition. -/
theorem intervalIntegrable_scalarObstruction (hC : 0 < C) :
    IntervalIntegrable (scalarObstruction C T) volume 0 T := by
  have hc : (2 * C) ≠ 0 := by positivity
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) volume 0 (2 * C * T) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 :
      IntervalIntegrable (fun x : ℝ => (2 * C * x) ^ (-(1 / 2) : ℝ)) volume
        (0 / (2 * C)) (2 * C * T / (2 * C)) := h1.comp_mul_left
  rw [zero_div, mul_div_cancel_left₀ _ hc] at h2
  have h3 := h2.comp_sub_left T
  rw [sub_zero, sub_self] at h3
  exact h3.symm

/-- Integrability of the profile of Proposition `prop:ode` on the half-open
interval `[0, T)`: the manuscript's `∫_0^T y(t) dt < ∞`. -/
theorem integrableOn_scalarObstruction (hC : 0 < C) (hT : 0 < T) :
    MeasureTheory.IntegrableOn (scalarObstruction C T) (Set.Ico 0 T) := by
  rw [← intervalIntegrable_iff_integrableOn_Ico_of_le hT.le]
  exact intervalIntegrable_scalarObstruction hC

/-- Blowup in Proposition `prop:ode`: `y t → ∞` as `t ↑ T`. -/
theorem tendsto_scalarObstruction (hC : 0 < C) :
    Filter.Tendsto (scalarObstruction C T) (nhdsWithin T (Set.Iio T)) Filter.atTop := by
  have hbase :
      Tendsto (fun t : ℝ => 2 * C * (T - t)) (nhdsWithin T (Set.Iio T))
        (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous fun t : ℝ => 2 * C * (T - t) := by fun_prop
      exact (hcont.tendsto' T 0 (by ring)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact scalarObstruction_base_pos hC ht
  exact (tendsto_rpow_neg_nhdsGT_zero (by norm_num)).comp hbase

/-- The exact value of the integral in the proof of Proposition `prop:ode`:
`∫_0^T y(t) dt = √(2T/C)`. -/
theorem integral_scalarObstruction (hC : 0 < C) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, scalarObstruction C T t = Real.sqrt (2 * T / C) := by
  have hc : (2 * C) ≠ 0 := by positivity
  have hint : ∫ t in (0 : ℝ)..T, scalarObstruction C T t
      = ∫ t in (0 : ℝ)..T, (2 * C * T - 2 * C * t) ^ (-(1 / 2) : ℝ) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [scalarObstruction]
    congr 1
    ring
  rw [hint, intervalIntegral.integral_comp_sub_mul (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) hc (2 * C * T),
    sub_self, mul_zero, sub_zero, integral_rpow (Or.inl (by norm_num))]
  have hzero : (0 : ℝ) ^ ((-(1 / 2) : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
  have hhalf : (-(1 / 2) : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hzero, hhalf, ← Real.sqrt_eq_rpow]
  have hsplit : 2 * T / C = 2 * C * T / C ^ 2 := by
    field_simp
  rw [hsplit, Real.sqrt_div (by positivity), Real.sqrt_sq hC.le, sub_zero, smul_eq_mul]
  field_simp

/-- Proposition `prop:ode` (Scalar obstruction) of the manuscript: for every
`C > 0` and `T > 0` there is a positive function `y` on `[0, T)`, differentiable
with `y' = C y ^ 3` there, integrable on `[0, T)`, and with `y t → ∞` as
`t ↑ T`.

This is not a Navier–Stokes blowup solution; see the module docstring. -/
theorem scalar_obstruction_exists (hC : 0 < C) (hT : 0 < T) :
    ∃ y : ℝ → ℝ,
      (∀ t ∈ Set.Ico (0 : ℝ) T, 0 < y t) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (C * (y t) ^ 3) t) ∧
      MeasureTheory.IntegrableOn y (Set.Ico 0 T) ∧
      Filter.Tendsto y (nhdsWithin T (Set.Iio T)) Filter.atTop :=
  ⟨scalarObstruction C T, fun _ ht => scalarObstruction_pos hC ht.2,
    hasDerivAt_scalarObstruction hC, integrableOn_scalarObstruction hC hT,
    tendsto_scalarObstruction hC⟩

end NavierFormal
