import NavierFormal.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Critical scaling of Lebesgue norms (manuscript Proposition `prop:scaling`)

This module formalizes the purely metric half of the manuscript's Proposition
`prop:scaling`: the behaviour of the spatial Lebesgue norms under the critical
Navier–Stokes dilation
`u_λ(x,t) = λ u(λ x, λ² t)`.

No claim about the Navier–Stokes equations is made here.  Only the change of
variables `y = λ x` on `ℝ³`, which is the step the manuscript's proof invokes
for the identity
`‖u_λ(t)‖_q = λ^{1-3/q} ‖u(λ² t)‖_q`,
is formalized, together with the two consequences the manuscript records:
`L³` is invariant, and `‖·‖₂²` scales by `λ⁻¹`.
-/

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

namespace NavierFormal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The critical spatial dilation of Proposition `prop:scaling`:
`(dilate λ f) x = λ • f (λ • x)`, the fixed-time profile of the rescaled
velocity field `u_λ(x,t) = λ u(λ x, λ² t)`. -/
def dilate (lam : ℝ) (f : Space → E) : Space → E := fun x => lam • f (lam • x)

/-- The space-time rescaling of Proposition `prop:scaling`:
`(dilateSpaceTime λ u) (t, x) = λ • u (λ² t, λ • x)`, i.e. the manuscript's
`u_λ(x,t) = λ u(λ x, λ² t)` with the time variable written first.  This is a
definition only; no assertion that it maps solutions to solutions is made. -/
def dilateSpaceTime (lam : ℝ) (u : ℝ × Space → E) : ℝ × Space → E :=
  fun tx => lam • u (lam ^ 2 * tx.1, lam • tx.2)

/-- Change of variables `y = λ x` on `ℝ³` at the level of measures: the
push-forward of Lebesgue measure under `x ↦ λ • x` is `λ^{-3}` times Lebesgue
measure.  This is the Jacobian step in the proof of Proposition
`prop:scaling`. -/
lemma map_smul_volume {lam : ℝ} (hlam : 0 < lam) :
    Measure.map (fun x : Space => lam • x) volume
      = ENNReal.ofReal (lam ^ (-(3 : ℝ))) • (volume : Measure Space) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure Space) hlam.ne'
  rw [finrank_euclideanSpace_fin] at hmap
  rw [show (fun x : Space => lam • x) = (lam • ·) from rfl, hmap]
  congr 2
  rw [abs_of_pos (by positivity), ← Real.rpow_natCast lam 3, ← Real.rpow_neg hlam.le]
  norm_num

/-- The exponent bookkeeping of Proposition `prop:scaling`: for `λ > 0` and a
real exponent `r`, `λ · (λ^{-3})^{1/r} = λ^{1-3/r}`. -/
lemma rpow_dilate_factor {lam r : ℝ} (hlam : 0 < lam) :
    lam * (lam ^ (-(3 : ℝ))) ^ r⁻¹ = lam ^ (1 - 3 / r) := by
  have hexp : (1 : ℝ) - 3 / r = 1 + -3 * r⁻¹ := by ring
  rw [← Real.rpow_mul hlam.le, hexp, Real.rpow_add hlam, Real.rpow_one]

omit [NormedSpace ℝ E] in
/-- Change of variables `y = λ x` at the level of `eLpNorm`: for `λ > 0` and a
finite exponent `p`, `‖f(λ ·)‖_p = (λ^{-3})^{1/p} ‖f‖_p`.  This is the
manuscript's step "changing variables `y = λ x`" in the proof of Proposition
`prop:scaling`, before the amplitude factor `λ` is taken into account. -/
lemma eLpNorm_comp_smul (f : Space → E) {p : ℝ≥0∞} (hp : p ≠ ∞) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (fun x => f (lam • x)) p volume
      = ENNReal.ofReal (lam ^ (-(3 : ℝ))) ^ p.toReal⁻¹ * eLpNorm f p volume := by
  have hemb : MeasurableEmbedding (fun x : Space => lam • x) :=
    measurableEmbedding_const_smul₀ hlam.ne'
  have hmap := hemb.eLpNorm_map_measure (g := f) (p := p) (μ := (volume : Measure Space))
  rw [map_smul_volume hlam, eLpNorm_smul_measure_of_ne_top hp, smul_eq_mul, one_div,
    ENNReal.toReal_inv] at hmap
  exact hmap.symm

/-- Proposition `prop:scaling`, norm identity:
`‖u_λ(t)‖_q = λ^{1-3/q} ‖u(λ² t)‖_q`, in the form that needs no PDE.  For
`λ > 0` and a finite nonzero exponent `p`,
`‖dilate λ f‖_p = λ^{1-3/p} ‖f‖_p` on `ℝ³`. -/
theorem eLpNorm_dilate (f : Space → E) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {lam : ℝ}
    (hlam : 0 < lam) :
    eLpNorm (dilate lam f) p volume
      = ENNReal.ofReal (lam ^ (1 - 3 / p.toReal)) * eLpNorm f p volume := by
  have _hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hfun : dilate lam f = lam • fun x : Space => f (lam • x) := rfl
  rw [hfun, eLpNorm_const_smul, eLpNorm_comp_smul f hp hlam, ← mul_assoc,
    Real.enorm_eq_ofReal hlam.le,
    ENNReal.ofReal_rpow_of_pos (by positivity : (0:ℝ) < lam ^ (-(3 : ℝ))),
    ← ENNReal.ofReal_mul hlam.le, rpow_dilate_factor hlam]

/-- Proposition `prop:scaling`, first consequence: `L³` is invariant under the
critical dilation, `‖dilate λ f‖₃ = ‖f‖₃`. -/
theorem eLpNorm_dilate_three (f : Space → E) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (dilate lam f) 3 volume = eLpNorm f 3 volume := by
  rw [eLpNorm_dilate f (by norm_num) (by norm_num) hlam]
  norm_num

/-- Proposition `prop:scaling`, second consequence (norm form): the `L²` norm
scales by `λ^{-1/2}`, `‖dilate λ f‖₂ = λ^{-1/2} ‖f‖₂`. -/
theorem eLpNorm_dilate_two (f : Space → E) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (dilate lam f) 2 volume
      = ENNReal.ofReal (lam ^ (-(1 : ℝ) / 2)) * eLpNorm f 2 volume := by
  rw [eLpNorm_dilate f (by norm_num) (by norm_num) hlam]
  norm_num

/-- Proposition `prop:scaling`, second consequence as the manuscript states it:
`‖u‖₂²` scales by `λ^{-1}`, `‖dilate λ f‖₂² = λ^{-1} ‖f‖₂²`. -/
theorem eLpNorm_dilate_two_sq (f : Space → E) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (dilate lam f) 2 volume ^ 2
      = ENNReal.ofReal lam⁻¹ * eLpNorm f 2 volume ^ 2 := by
  rw [eLpNorm_dilate_two f hlam, mul_pow, ← ENNReal.ofReal_pow (by positivity)]
  congr 2
  rw [← Real.rpow_natCast (lam ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hlam.le,
    ← Real.rpow_neg_one lam]
  norm_num

/-- Proposition `prop:scaling`, fixed-time form for the space-time rescaling:
at each fixed time `t`, the spatial profile of `dilateSpaceTime λ u` is the
spatial dilation of the profile of `u` at time `λ² t`, so
`‖u_λ(t)‖_q = λ^{1-3/q} ‖u(λ² t)‖_q`.  No PDE claim is involved. -/
theorem eLpNorm_dilateSpaceTime (u : ℝ × Space → E) (t : ℝ) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {lam : ℝ} (hlam : 0 < lam) :
    eLpNorm (fun x => dilateSpaceTime lam u (t, x)) p volume
      = ENNReal.ofReal (lam ^ (1 - 3 / p.toReal))
        * eLpNorm (fun x => u (lam ^ 2 * t, x)) p volume :=
  eLpNorm_dilate (fun x => u (lam ^ 2 * t, x)) hp0 hp hlam

end NavierFormal

end
