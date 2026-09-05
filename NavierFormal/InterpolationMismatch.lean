import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The interpolation mismatch recorded in `prop:scaling`

This module formalizes the two side remarks made inside the proof of
`prop:scaling` of `../navier-paper/main.tex`.

* The scalar counterexample: "There can be no deduction of a time supremum
  from these two energy norms: even for scalar functions, membership in
  `L⁴(0,T)` does not imply membership in `L^∞(0,T)`."  The witness used here
  is the manuscript's `t ↦ t^{-1/5}`, whose fourth power `t^{-4/5}` is
  integrable on `(0,T)` while the function itself is unbounded near `0`.
* The exponent bookkeeping under `eq:L4L3`: "The spacetime norm in
  \eqref{eq:L4L3} is also supercritical, since `2/4 + 3/3 = 3/2 > 1`."

Nothing here is a statement about the Navier–Stokes equations themselves; it
is the scalar obstruction that blocks the implication
`L⁴(0,T;L³) ⇒ L^∞(0,T;L³)`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NavierFormal

/-- The scalar witness `g(t) = t^{-1/5}` used in the proof of `prop:scaling`
to show that `L⁴(0,T)` membership does not imply `L^∞(0,T)` membership. -/
noncomputable def scalingWitness (t : ℝ) : ℝ := t ^ (-(1 : ℝ) / 5)

/-- The witness of `prop:scaling` is measurable, hence almost everywhere
strongly measurable for every measure on `ℝ`. -/
theorem aestronglyMeasurable_scalingWitness (μ : Measure ℝ) :
    AEStronglyMeasurable scalingWitness μ :=
  (measurable_id.pow_const (-(1 : ℝ) / 5)).aestronglyMeasurable

/-- On the time interval `(0,T)` the fourth power of the witness of
`prop:scaling` is the integrable power `t^{-4/5}`. -/
theorem integrable_scalingWitness_rpow_four {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => ‖scalingWitness t‖ ^ (4 : ℝ))
      (volume.restrict (Ioo 0 T)) := by
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-(4 : ℝ) / 5)) (Ioo 0 T) volume := by
    refine (intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 ?_
    norm_num
  refine hpow.congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  have hg : scalingWitness t = t ^ (-(1 : ℝ) / 5) := rfl
  rw [hg, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), ← Real.rpow_mul ht0.le]
  norm_num

/-- **Manuscript `prop:scaling`, first remark (positive half).**  The witness
`t ↦ t^{-1/5}` belongs to `L⁴(0,T)` for every `T > 0`. -/
theorem memLp_scalingWitness_four {T : ℝ} (hT : 0 < T) :
    MemLp scalingWitness 4 (volume.restrict (Ioo 0 T)) := by
  have h := integrable_scalingWitness_rpow_four hT
  have hp : ((4 : ℝ≥0∞)).toReal = (4 : ℝ) := by norm_num
  rw [← hp] at h
  exact (integrable_norm_rpow_iff (aestronglyMeasurable_scalingWitness _)
    (by norm_num) (by norm_num)).1 h

/-- The witness of `prop:scaling` exceeds any given level on a subinterval of
`(0,T)` of positive length: for `C ≥ 0` and `0 < t < (C+1)^{-5}` one has
`C < t^{-1/5}`. -/
theorem lt_scalingWitness {C t : ℝ} (hC : 0 ≤ C) (ht0 : 0 < t)
    (ht : t < (C + 1) ^ (-(5 : ℝ))) : C < scalingWitness t := by
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hlt : ((C + 1) ^ (-(5 : ℝ))) ^ (-(1 : ℝ) / 5) < t ^ (-(1 : ℝ) / 5) :=
    Real.rpow_lt_rpow_of_neg ht0 ht (by norm_num)
  have hval : ((C + 1) ^ (-(5 : ℝ))) ^ (-(1 : ℝ) / 5) = C + 1 := by
    rw [← Real.rpow_mul hC1.le]
    norm_num
  rw [hval] at hlt
  exact lt_of_lt_of_le (by linarith) hlt.le

/-- **Manuscript `prop:scaling`, first remark (negative half).**  The witness
`t ↦ t^{-1/5}` is not essentially bounded on `(0,T)`: its essential supremum
is infinite. -/
theorem eLpNormEssSup_scalingWitness {T : ℝ} (hT : 0 < T) :
    eLpNormEssSup scalingWitness (volume.restrict (Ioo 0 T)) = ⊤ := by
  by_contra hne
  obtain ⟨C, hC⟩ :=
    eLpNormEssSup_lt_top_iff_isBoundedUnder.1 (lt_top_iff_ne_top.2 hne)
  have hC' : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ‖scalingWitness t‖₊ ≤ C := hC
  set r : ℝ := min T (((C : ℝ) + 1) ^ (-(5 : ℝ))) with hr_def
  have hrpos : 0 < r := lt_min hT (Real.rpow_pos_of_pos (by positivity) _)
  have hsub : Ioo (0 : ℝ) r ⊆ {t : ℝ | ¬ ‖scalingWitness t‖₊ ≤ C} := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have htlt : t < ((C : ℝ) + 1) ^ (-(5 : ℝ)) := lt_of_lt_of_le ht.2 (min_le_right _ _)
    have hgt : (C : ℝ) < scalingWitness t := lt_scalingWitness C.coe_nonneg ht0 htlt
    have hnorm : ‖scalingWitness t‖ = scalingWitness t :=
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)
    have hnn : ¬ ‖scalingWitness t‖₊ ≤ C := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, hnorm]
      exact not_le.2 hgt
    exact hnn
  have hzero : volume.restrict (Ioo 0 T) {t : ℝ | ¬ ‖scalingWitness t‖₊ ≤ C} = 0 :=
    ae_iff.1 hC'
  have hle : volume.restrict (Ioo 0 T) (Ioo (0 : ℝ) r) = 0 :=
    le_antisymm (hzero ▸ measure_mono hsub) (zero_le)
  rw [Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.2 (Ioo_subset_Ioo le_rfl (min_le_left _ _)), Real.volume_Ioo] at hle
  simp only [sub_zero, ENNReal.ofReal_eq_zero] at hle
  exact absurd hle (not_le.2 hrpos)

/-- **Manuscript `prop:scaling`, first remark.**  For every `T > 0` there is a
scalar function on `(0,T)` that lies in `L⁴(0,T)` but not in `L^∞(0,T)`; hence
the energy bounds `eq:L4L3` cannot yield a time supremum.  The witness is the
manuscript's `g(t) = t^{-1/5}`. -/
theorem exists_memLp_four_not_memLp_top {T : ℝ} (hT : 0 < T) :
    ∃ g : ℝ → ℝ, MemLp g 4 (volume.restrict (Ioo 0 T)) ∧
      ¬ MemLp g ⊤ (volume.restrict (Ioo 0 T)) := by
  refine ⟨scalingWitness, memLp_scalingWitness_four hT, ?_⟩
  intro h
  have := h.2
  rw [eLpNorm_exponent_top, eLpNormEssSup_scalingWitness hT] at this
  exact absurd rfl this.ne

/-- **Manuscript `prop:scaling`, first remark, `eLpNorm` form.**  Restated with
the `L^∞` seminorm: the witness has infinite `L^∞(0,T)` seminorm while lying in
`L⁴(0,T)`. -/
theorem exists_memLp_four_eLpNorm_top_eq_top {T : ℝ} (hT : 0 < T) :
    ∃ g : ℝ → ℝ, MemLp g 4 (volume.restrict (Ioo 0 T)) ∧
      eLpNorm g ⊤ (volume.restrict (Ioo 0 T)) = ⊤ :=
  ⟨scalingWitness, memLp_scalingWitness_four hT, by
    rw [eLpNorm_exponent_top]; exact eLpNormEssSup_scalingWitness hT⟩

/-- **Manuscript `prop:scaling`, second remark.**  The exponent bookkeeping for
the spacetime norm of `eq:L4L3`: the Ladyzhenskaya–Prodi–Serrin sum for
`L⁴_t L³_x` is `2/4 + 3/3 = 3/2`, which exceeds the critical value `1`, so the
norm controlled by the energy estimate is supercritical. -/
theorem L4L3_supercritical : (2 : ℝ) / 4 + (3 : ℝ) / 3 = 3 / 2 ∧ (1 : ℝ) < 3 / 2 := by
  norm_num

end NavierFormal
