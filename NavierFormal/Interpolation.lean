import NavierFormal.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Interpolation, Sobolev, and Young inequalities (CP1 module `Calculus/Interpolation`)

This module supplies the three elementary inequalities that the manuscript
`../navier-paper/main.tex` uses inside Proposition `prop:scaling`
(the interpolation mismatch) and Proposition `prop:enstrophy`
(the cubic differential inequality):

* the Lyapunov (Hölder) interpolation of Lebesgue seminorms
  `‖f‖_r ≤ ‖f‖_p^θ ‖f‖_q^{1-θ}` for `1/r = θ/p + (1-θ)/q`, together with the
  two instances the manuscript displays or needs,
  `‖f‖₃ ≤ ‖f‖₂^{1/2} ‖f‖₆^{1/2}` and `‖f‖_{10/3} ≤ ‖f‖₂^{2/5} ‖f‖₆^{3/5}`;
* the Sobolev inequality `‖u‖₆ ≤ C ‖∇u‖₂` on `ℝ³`, first for compactly
  supported `C¹` fields by wrapping Mathlib's Gagliardo–Nirenberg–Sobolev
  theorem `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, and then — this is
  the form the manuscript uses — for `C¹` fields with `u, ∇u ∈ L²` and no
  support hypothesis, by a cutoff argument;
* Young's inequality for products in the two conjugate pairs the manuscript
  uses, `(4/3, 4)` in the proof of `prop:enstrophy` and `(5/4, 5)`.

Nothing here is a statement about the Navier–Stokes equations.

## Conventions

All Lebesgue quantities are `MeasureTheory.eLpNorm` valued in `ℝ≥0∞`, so a
non-`L^p` field gives `⊤` rather than the junk real value `0` (design record
`cp01-lean-statement-design.md`, risk `R-JUNK`).  Powers are `ENNReal.rpow`
with real exponents, and `Real.rpow` on the real side; on `ℝ≥0∞` the
convention `0 ^ (0:ℝ) = 1` is Mathlib's and is used only through the
degenerate endpoints `θ = 0`, `θ = 1`, where the inequality is an identity.

The Sobolev inequality is stated with the **operator** norm of `fderiv ℝ u`,
which is the norm Mathlib's `eLpNorm (fderiv ℝ u) 2` uses; it differs from the
manuscript's Frobenius `‖∇u‖₂` by a dimensional constant (design record risk
`R-NORM`).  Since the constant here is existential/opaque this is harmless for
an inequality, but the two norms must never be mixed inside an identity.

## The cutoff extension

The Sobolev inequality is proved twice.
`eLpNorm_six_le_eLpNorm_fderiv_two_of_hasCompactSupport` is the direct wrapper
of Mathlib's theorem and needs `HasCompactSupport u`;
`eLpNorm_six_le_eLpNorm_fderiv_two` removes that hypothesis at the price of
`u ∈ L²` and `∇u ∈ L²` (both of which the manuscript's solution class supplies)
and keeps the *same* constant `sobolevSixConst`.  Its proof multiplies `u` by
the cutoffs `χ_R(x) = φ(x/R)` of a fixed reference bump `φ`
(`sobolevBump`, equal to `1` on `‖x‖ ≤ 1` and supported in `‖x‖ ≤ 2`), applies
the compactly supported inequality to `χ_R u`, controls the commutator by
`‖u ⊗ ∇χ_R‖₂ ≤ (K/R)‖u‖₂` with `K = sup‖∇φ‖`, and passes to the limit
`R = n+1 → ∞` through Fatou's lemma
(`MeasureTheory.lintegral_liminf_le'`), the left-hand side being recovered
because `χ_R = 1` on `‖x‖ ≤ R`.  Nothing in this module is a `sorry` and no
axiom beyond Mathlib's stands behind it.

The two `L²` hypotheses are not a weakening of the manuscript's use of the
inequality: it is applied to `u(t)` inside the class `L^∞_tH¹ ∩ L²_tH²`, where
both hold.  Neither can simply be dropped in this formulation.  `u ∈ L²` is
necessary: a nonzero constant field is `C¹` with `∇u = 0`, so the right-hand
side is `0` while `‖u‖₆ = ⊤`.  For `∇u ∉ L²` the right-hand side is `⊤` — hence
the inequality is trivially true — but only if `sobolevSixConst ≠ 0`, which is
not proved here (Mathlib's constant is not unfolded), so that case is excluded
by hypothesis rather than argued.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace NavierFormal

/-! ## 1. Lyapunov interpolation of Lebesgue seminorms -/

section Interpolation

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]

/-- **Lyapunov interpolation**, real-exponent form.  For `0 < p, q, r`, `0 ≤ θ ≤ 1` and
`1/r = θ/p + (1-θ)/q`,
`(∫‖f‖^r)^{1/r} ≤ (∫‖f‖^p)^{θ/p} (∫‖f‖^q)^{(1-θ)/q}`.

This is the inequality the manuscript invokes as "interpolation" in the proof of
Proposition `prop:scaling` (`‖u‖₃ ≤ ‖u‖₂^{1/2}‖u‖₆^{1/2}`) and inside the Hölder
step of Proposition `prop:enstrophy`.  Mathlib `v4.33.1` has no such lemma
(`Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean` carries only the
finite-measure comparison and the bilinear Hölder inequalities), so it is proved
here from Hölder's inequality for the Lebesgue integral
`ENNReal.lintegral_mul_norm_pow_le`, applied to the splitting
`‖f‖^r = (‖f‖^p)^{θr/p} · (‖f‖^q)^{(1-θ)r/q}` whose exponents sum to `1`.

Stated on the auxiliary seminorm `eLpNorm'`; see `eLpNorm_interpolate` for the
`eLpNorm` version with `ℝ≥0∞` exponents. -/
theorem eLpNorm'_interpolate {f : α → F} (hf : AEStronglyMeasurable f μ)
    {p q r θ : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hint : 1 / r = θ / p + (1 - θ) / q) :
    eLpNorm' f r μ ≤ eLpNorm' f p μ ^ θ * eLpNorm' f q μ ^ (1 - θ) := by
  have hθ1' : 0 ≤ 1 - θ := by linarith
  have ha : (0 : ℝ) ≤ θ * r / p := by positivity
  have hb : (0 : ℝ) ≤ (1 - θ) * r / q := by positivity
  have hs : θ * r / p + (1 - θ) * r / q = 1 := by
    have h1 : θ * r / p + (1 - θ) * r / q = r * (θ / p + (1 - θ) / q) := by ring
    rw [h1, ← hint]
    field_simp
  set A := ∫⁻ x, ‖f x‖ₑ ^ p ∂μ with hA
  set B := ∫⁻ x, ‖f x‖ₑ ^ q ∂μ with hB
  have key : ∫⁻ x, ‖f x‖ₑ ^ r ∂μ ≤ A ^ (θ * r / p) * B ^ ((1 - θ) * r / q) := by
    have h := ENNReal.lintegral_mul_norm_pow_le (μ := μ)
      (f := fun x => ‖f x‖ₑ ^ p) (g := fun x => ‖f x‖ₑ ^ q)
      (hf.enorm.pow_const p) (hf.enorm.pow_const q) ha hb hs
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have hr0 : (0 : ℝ) ≤ 1 / r := by positivity
  calc eLpNorm' f r μ = (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (1 / r) := rfl
    _ ≤ (A ^ (θ * r / p) * B ^ ((1 - θ) * r / q)) ^ (1 / r) := ENNReal.rpow_le_rpow key hr0
    _ = A ^ (θ / p) * B ^ ((1 - θ) / q) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr0, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1 <;> · field_simp; try ring
    _ = eLpNorm' f p μ ^ θ * eLpNorm' f q μ ^ (1 - θ) := by
        rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm, ← hA, ← hB,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1 <;> · field_simp

/-- **Lyapunov interpolation** for `eLpNorm` with finite `ℝ≥0∞` exponents:
if `1/r = θ/p + (1-θ)/q` with `0 ≤ θ ≤ 1` and `p, q, r ∈ (0,∞)`, then
`‖f‖_r ≤ ‖f‖_p^θ ‖f‖_q^{1-θ}`.

The manuscript's ordering hypothesis `p ≤ r ≤ q` is not needed: it is implied by
the exponent relation whenever `θ ∈ [0,1]`.  See `eLpNorm_interpolate_top` for
the endpoint `q = ∞` (which additionally assumes `f ∈ L^∞`). -/
theorem eLpNorm_interpolate {f : α → F} (hf : AEStronglyMeasurable f μ)
    {p q r : ℝ≥0∞} {θ : ℝ} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : r ≠ 0) (hrt : r ≠ ∞) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hint : 1 / r.toReal = θ / p.toReal + (1 - θ) / q.toReal) :
    eLpNorm f r μ ≤ eLpNorm f p μ ^ θ * eLpNorm f q μ ^ (1 - θ) := by
  rw [eLpNorm_eq_eLpNorm' hp0 hpt, eLpNorm_eq_eLpNorm' hq0 hqt, eLpNorm_eq_eLpNorm' hr0 hrt]
  exact eLpNorm'_interpolate hf (ENNReal.toReal_pos hp0 hpt) (ENNReal.toReal_pos hq0 hqt)
    (ENNReal.toReal_pos hr0 hrt) hθ0 hθ1 hint

/-- **Lyapunov interpolation** at the endpoint `q = ∞`:
`‖f‖_r ≤ ‖f‖_p^{p/r} ‖f‖_∞^{1-p/r}` for `0 < p ≤ r < ∞`.  With `θ := p/r` this is
`1/r = θ/p + (1-θ)/∞`, i.e. the `q = ∞` case of `eLpNorm_interpolate`.

The hypothesis `f ∈ L^∞` (`eLpNorm f ∞ μ ≠ ∞`) is assumed: it is the only case in
which the statement is used, and it removes the `⊤ · 0` degeneracies of the
extended-real product on the right. -/
theorem eLpNorm_interpolate_top {f : α → F} (hf : eLpNorm f ∞ μ ≠ ∞)
    {p r : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (hr0 : r ≠ 0) (hrt : r ≠ ∞)
    (hpr : p ≤ r) :
    eLpNorm f r μ
      ≤ eLpNorm f p μ ^ (p.toReal / r.toReal) * eLpNorm f ∞ μ ^ (1 - p.toReal / r.toReal) := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hr' : 0 < r.toReal := ENNReal.toReal_pos hr0 hrt
  have hle : p.toReal ≤ r.toReal := ENNReal.toReal_mono hrt hpr
  set M := eLpNormEssSup f μ with hM
  have hMne : M ≠ ∞ := by rwa [hM, ← eLpNorm_exponent_top]
  have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M := ae_le_essSup (f := fun x => ‖f x‖ₑ)
  have hpt' : (0 : ℝ) ≤ r.toReal - p.toReal := by linarith
  have key : ∫⁻ x, ‖f x‖ₑ ^ r.toReal ∂μ
      ≤ M ^ (r.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
    rw [← lintegral_const_mul' _ _ (by finiteness)]
    refine lintegral_mono_ae (hae.mono fun x hx => ?_)
    have : ‖f x‖ₑ ^ r.toReal = ‖f x‖ₑ ^ p.toReal * ‖f x‖ₑ ^ (r.toReal - p.toReal) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hp'.le hpt']
      ring_nf
    rw [this, mul_comm]
    gcongr
  have h1r : (0 : ℝ) ≤ 1 / r.toReal := by positivity
  calc eLpNorm f r μ = (∫⁻ x, ‖f x‖ₑ ^ r.toReal ∂μ) ^ (1 / r.toReal) :=
        eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt
    _ ≤ (M ^ (r.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / r.toReal) :=
        ENNReal.rpow_le_rpow key h1r
    _ = eLpNorm f p μ ^ (p.toReal / r.toReal) * M ^ (1 - p.toReal / r.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1r, mul_comm,
          eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1 <;> · field_simp; try ring
    _ = eLpNorm f p μ ^ (p.toReal / r.toReal) * eLpNorm f ∞ μ ^ (1 - p.toReal / r.toReal) := by
        rw [hM, eLpNorm_exponent_top]

/-- The instance of Lyapunov interpolation displayed in the proof of Proposition
`prop:scaling`: `‖f‖₃ ≤ ‖f‖₂^{1/2} ‖f‖₆^{1/2}` (here `1/3 = (1/2)/2 + (1/2)/6`). -/
theorem eLpNorm_three_le {f : α → F} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 3 μ ≤ eLpNorm f 2 μ ^ (1 / 2 : ℝ) * eLpNorm f 6 μ ^ (1 / 2 : ℝ) := by
  have h := eLpNorm_interpolate (μ := μ) (f := f) (p := 2) (q := 6) (r := 3) (θ := 1 / 2)
    hf (by norm_num) (by finiteness) (by norm_num) (by finiteness) (by norm_num)
    (by finiteness) (by norm_num) (by norm_num) (by norm_num)
  have hθ : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rwa [hθ] at h

/-- The instance of Lyapunov interpolation available for the Hölder step of Proposition
`prop:enstrophy`: `‖g‖_{10/3} ≤ ‖g‖₂^{2/5} ‖g‖₆^{3/5}` (here
`3/10 = (2/5)/2 + (3/5)/6`).  The manuscript's displayed proof uses the `L³`
instance `eLpNorm_three_le` applied to `∇u`; this is the equivalent `10/3`
form of the same interpolation. -/
theorem eLpNorm_tenThirds_le {g : α → F} (hg : AEStronglyMeasurable g μ) :
    eLpNorm g (10 / 3) μ ≤ eLpNorm g 2 μ ^ (2 / 5 : ℝ) * eLpNorm g 6 μ ^ (3 / 5 : ℝ) := by
  have h := eLpNorm_interpolate (μ := μ) (f := g) (p := 2) (q := 6) (r := 10 / 3) (θ := 2 / 5)
    hg (by norm_num) (by finiteness) (by norm_num) (by finiteness) (by norm_num)
    (by finiteness) (by norm_num) (by norm_num) (by norm_num)
  have hθ : (1 : ℝ) - 2 / 5 = 3 / 5 := by norm_num
  rwa [hθ] at h

end Interpolation

/-! ## 2. The Sobolev inequality `‖u‖₆ ≤ C‖∇u‖₂` on `ℝ³` -/

/-- The constant of the Sobolev inequality `‖u‖₆ ≤ C‖∇u‖₂` on `ℝ³`, i.e. Mathlib's
Gagliardo–Nirenberg–Sobolev constant `SNormLESNormFDerivOfEqConst` at `p = 2` for
`Space`-valued fields on `Space` with Lebesgue measure.  It is the manuscript's
absolute constant `C` in `‖u‖₆ ≤ C‖∇u‖₂` (proofs of Propositions `prop:scaling`
and `prop:enstrophy`); its numerical value is irrelevant and never unfolded. -/
def sobolevSixConst : ℝ≥0 :=
  SNormLESNormFDerivOfEqConst Space (volume : Measure Space) 2

/-- **Sobolev inequality on `ℝ³`, compactly supported case.**
For a `C¹` vector field `u : ℝ³ → ℝ³` with compact support,
`‖u‖₆ ≤ C ‖∇u‖₂`.  This is the manuscript's `‖u‖₆ ≤ C‖∇u‖₂` (used in
Propositions `prop:scaling` and `prop:enstrophy`), restricted to compactly
supported fields; `eLpNorm_six_le_eLpNorm_fderiv_two` removes the restriction.

Wrapper of `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` at `n = 3`, `p = 2`,
`p' = 6`, using `(1/6) = (1/2) - (1/3)`.  The gradient norm on the right is the
operator norm of `fderiv ℝ u` (see the module docstring, risk `R-NORM`). -/
theorem eLpNorm_six_le_eLpNorm_fderiv_two_of_hasCompactSupport {u : Space → Space}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    eLpNorm u 6 volume ≤ sobolevSixConst * eLpNorm (fderiv ℝ u) 2 volume := by
  have hn : Module.finrank ℝ Space = 3 := by simp
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq (F := Space) (E := Space)
    (μ := (volume : Measure Space)) (p := 2) (p' := 6) hu h2u (by norm_num)
    (by rw [hn]; norm_num) (by rw [hn]; norm_num)
  simpa [sobolevSixConst] using h

/-! ### The cutoff family used to remove the compact-support hypothesis

`sobolevBump` is the fixed reference profile `φ` and `sobolevCutoff R` is
`χ_R(x) = φ(x/R)`.  These have no counterpart in the manuscript: they implement
the sentence "cut off and pass to the limit" in the manuscript's use of the
Sobolev inequality (proof of Proposition `prop:scaling`). -/

/-- The fixed reference cutoff profile `φ` of the Sobolev cutoff argument:
Mathlib's smooth bump on `ℝ³` that equals `1` on the closed unit ball and is
supported in the ball of radius `2`. -/
def sobolevBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff at scale `R` of the Sobolev cutoff argument, `χ_R(x) = φ(x/R)`
with `φ = sobolevBump`.  For `R > 0` it is smooth, takes values in `[0,1]`,
equals `1` on `‖x‖ ≤ R`, and is supported in `‖x‖ ≤ 2R`. -/
def sobolevCutoff (R : ℝ) (x : Space) : ℝ := sobolevBump ((R⁻¹ : ℝ) • x)

/-- `χ_R` is continuously differentiable (indeed smooth): `sobolevCutoff` is the
composition of the smooth profile `sobolevBump` with a linear map. -/
theorem sobolevCutoff_contDiff (R : ℝ) : ContDiff ℝ 1 (sobolevCutoff R) :=
  (sobolevBump.contDiff (n := 1)).comp (contDiff_const_smul _)

/-- `0 ≤ χ_R`. -/
theorem sobolevCutoff_nonneg (R : ℝ) (x : Space) : 0 ≤ sobolevCutoff R x := sobolevBump.nonneg

/-- `χ_R ≤ 1`. -/
theorem sobolevCutoff_le_one (R : ℝ) (x : Space) : sobolevCutoff R x ≤ 1 := sobolevBump.le_one

/-- `χ_R = 1` on the closed ball of radius `R`; this is what recovers the full
left-hand side `‖u‖₆` in the limit `R → ∞`. -/
theorem sobolevCutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) :
    sobolevCutoff R x = 1 := by
  refine sobolevBump.one_of_mem_closedBall ?_
  simp only [Metric.mem_closedBall, dist_zero_right, sobolevBump]
  rw [norm_smul]
  simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  rw [inv_mul_le_iff₀ hR]
  simpa using hx

/-- `χ_R` has compact support (it vanishes outside the ball of radius `2R`);
this is what makes `χ_R u` admissible in
`eLpNorm_six_le_eLpNorm_fderiv_two_of_hasCompactSupport`. -/
theorem sobolevCutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (sobolevCutoff R) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * R))
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  refine sobolevBump.zero_of_le_dist ?_
  simp only [dist_zero_right, sobolevBump]
  rw [norm_smul]
  simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  rw [le_inv_mul_iff₀ hR]
  linarith

/-- The gradient of the reference profile is bounded: `K = sup‖∇φ‖ < ∞`, because
`∇φ` is continuous with compact support.  `K` is the constant in the commutator
estimate `‖u ⊗ ∇χ_R‖₂ ≤ (K/R)‖u‖₂`. -/
theorem exists_bound_norm_fderiv_sobolevBump :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Space, ‖fderiv ℝ (sobolevBump : Space → ℝ) y‖ ≤ K := by
  obtain ⟨K, hK⟩ := (HasCompactSupport.fderiv (𝕜 := ℝ)
      sobolevBump.hasCompactSupport).exists_bound_of_continuous
    ((sobolevBump.contDiff (n := 2)).continuous_fderiv (by norm_num))
  exact ⟨K, le_trans (norm_nonneg _) (hK 0), hK⟩

/-- The scaling estimate for the cutoff gradient, `‖∇χ_R‖_∞ ≤ K/R`: this is the
whole point of using a *scaled* fixed profile, and it is what makes the
commutator error vanish as `R → ∞`. -/
theorem norm_fderiv_sobolevCutoff_le {K R : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y : Space, ‖fderiv ℝ (sobolevBump : Space → ℝ) y‖ ≤ K) (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (sobolevCutoff R) x‖ ≤ K / R := by
  have hL : ‖(R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ Space‖ ≤ R⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    exact le_rfl
  have h1 : HasFDerivAt (fun x : Space => (R⁻¹ : ℝ) • x)
      ((R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ Space) x :=
    (hasFDerivAt_id x).const_smul (R⁻¹ : ℝ)
  have h2 : HasFDerivAt (sobolevBump : Space → ℝ)
      (fderiv ℝ (sobolevBump : Space → ℝ) ((R⁻¹ : ℝ) • x)) ((R⁻¹ : ℝ) • x) :=
    ((sobolevBump.contDiff (n := 1)).differentiable (by norm_num) _).hasFDerivAt
  have hd : HasFDerivAt (sobolevCutoff R)
      ((fderiv ℝ (sobolevBump : Space → ℝ) ((R⁻¹ : ℝ) • x)).comp
        ((R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ Space)) x := h2.comp x h1
  rw [hd.fderiv]
  calc ‖(fderiv ℝ (sobolevBump : Space → ℝ) ((R⁻¹ : ℝ) • x)).comp
          ((R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ Space)‖
      ≤ ‖fderiv ℝ (sobolevBump : Space → ℝ) ((R⁻¹ : ℝ) • x)‖ *
          ‖(R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ Space‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K * R⁻¹ := mul_le_mul (hK _) hL (by positivity) hK0
    _ = K / R := by rw [div_eq_mul_inv]

set_option maxHeartbeats 1000000 in
/-- **The cutoff step.**  For `C¹` fields `u` and every `R > 0`,
`‖χ_R u‖₆ ≤ C (‖∇u‖₂ + (K/R)‖u‖₂)`: apply the compactly supported Sobolev
inequality to `χ_R u` and split its gradient by the product rule
`∇(χ_R u) = χ_R ∇u + u ⊗ ∇χ_R`, using `0 ≤ χ_R ≤ 1` and `‖∇χ_R‖_∞ ≤ K/R`. -/
theorem eLpNorm_six_sobolevCutoff_smul_le {u : Space → Space} (hu : ContDiff ℝ 1 u) {K R : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ y : Space, ‖fderiv ℝ (sobolevBump : Space → ℝ) y‖ ≤ K) (hR : 0 < R) :
    eLpNorm (fun x => sobolevCutoff R x • u x) 6 volume
      ≤ sobolevSixConst * (eLpNorm (fderiv ℝ u) 2 volume
        + ENNReal.ofReal (K / R) * eLpNorm u 2 volume) := by
  have hv : ContDiff ℝ 1 fun x => sobolevCutoff R x • u x := (sobolevCutoff_contDiff R).smul hu
  have h2v : HasCompactSupport fun x => sobolevCutoff R x • u x :=
    HasCompactSupport.smul_right (sobolevCutoff_hasCompactSupport hR)
  have hpt : ∀ x, ‖fderiv ℝ (fun y => sobolevCutoff R y • u y) x‖
      ≤ ‖‖fderiv ℝ u x‖ + (K / R) * ‖u x‖‖ := by
    intro x
    have hcx : HasFDerivAt (sobolevCutoff R) (fderiv ℝ (sobolevCutoff R) x) x :=
      ((sobolevCutoff_contDiff R).differentiable (by norm_num) _).hasFDerivAt
    have hux : HasFDerivAt u (fderiv ℝ u x) x :=
      (hu.differentiable (by norm_num) _).hasFDerivAt
    have hd : HasFDerivAt (fun y => sobolevCutoff R y • u y)
        (sobolevCutoff R x • fderiv ℝ u x + (fderiv ℝ (sobolevCutoff R) x).smulRight (u x)) x :=
      hcx.smul hux
    rw [hd.fderiv]
    have h1 : ‖sobolevCutoff R x • fderiv ℝ u x
        + (fderiv ℝ (sobolevCutoff R) x).smulRight (u x)‖
        ≤ ‖sobolevCutoff R x • fderiv ℝ u x‖
          + ‖(fderiv ℝ (sobolevCutoff R) x).smulRight (u x)‖ := norm_add_le _ _
    have h2 : ‖sobolevCutoff R x • fderiv ℝ u x‖ ≤ ‖fderiv ℝ u x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sobolevCutoff_nonneg R x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (sobolevCutoff_le_one R x)
    have h3 : ‖(fderiv ℝ (sobolevCutoff R) x).smulRight (u x)‖ ≤ (K / R) * ‖u x‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (norm_fderiv_sobolevCutoff_le hK0 hK hR x) (norm_nonneg _)
    have hnn : (0 : ℝ) ≤ ‖fderiv ℝ u x‖ + (K / R) * ‖u x‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith
  have hmeas1 : AEStronglyMeasurable (fun x => ‖fderiv ℝ u x‖) (volume : Measure Space) :=
    (hu.continuous_fderiv (by norm_num)).norm.aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun x => (K / R) * ‖u x‖) (volume : Measure Space) :=
    (continuous_const.mul hu.continuous.norm).aestronglyMeasurable
  calc eLpNorm (fun x => sobolevCutoff R x • u x) 6 volume
      ≤ sobolevSixConst * eLpNorm (fderiv ℝ fun x => sobolevCutoff R x • u x) 2 volume :=
        eLpNorm_six_le_eLpNorm_fderiv_two_of_hasCompactSupport hv h2v
    _ ≤ sobolevSixConst * (eLpNorm (fderiv ℝ u) 2 volume
        + ENNReal.ofReal (K / R) * eLpNorm u 2 volume) := by
        gcongr
        calc eLpNorm (fderiv ℝ fun x => sobolevCutoff R x • u x) 2 volume
            ≤ eLpNorm (fun x => ‖fderiv ℝ u x‖ + (K / R) * ‖u x‖) 2 volume :=
              eLpNorm_mono hpt
          _ ≤ eLpNorm (fun x => ‖fderiv ℝ u x‖) 2 volume
              + eLpNorm (fun x => (K / R) * ‖u x‖) 2 volume :=
              eLpNorm_add_le hmeas1 hmeas2 (by norm_num)
          _ = eLpNorm (fderiv ℝ u) 2 volume
              + ENNReal.ofReal (K / R) * eLpNorm u 2 volume := by
              rw [eLpNorm_norm]
              congr 1
              have hsm : (fun x => (K / R) * ‖u x‖) = (K / R) • fun x => ‖u x‖ := by
                funext x; simp [Pi.smul_apply, smul_eq_mul]
              rw [hsm, eLpNorm_const_smul, eLpNorm_norm]
              congr 1
              rw [Real.enorm_eq_ofReal (by positivity)]

/-- The `L⁶` seminorm as a Lebesgue integral: `∫ ‖f‖^6 = ‖f‖₆^6`.  Used to move the
cutoff estimate under Fatou's lemma. -/
theorem lintegral_enorm_rpow_six_eq (f : Space → Space) :
    ∫⁻ x, ‖f x‖ₑ ^ (6 : ℝ) ∂(volume : Measure Space) = eLpNorm f 6 volume ^ (6 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by finiteness), ← ENNReal.rpow_mul]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **Sobolev inequality on `ℝ³` without a support hypothesis**, in exactly the form
the manuscript uses inside Propositions `prop:scaling` and `prop:enstrophy`: for
every `C¹` vector field `u : ℝ³ → ℝ³` with `u ∈ L²` and `∇u ∈ L²`,
`‖u‖₆ ≤ C‖∇u‖₂` with the *same* constant `sobolevSixConst` as in the compactly
supported case.

Proof: multiply by the cutoffs `χ_{n+1}`, apply
`eLpNorm_six_sobolevCutoff_smul_le`, and let `n → ∞`.  The left-hand side is
recovered by Fatou's lemma (`MeasureTheory.lintegral_liminf_le'`) because
`χ_{n+1}(x) = 1` as soon as `n + 1 ≥ ‖x‖`, so the integrands converge pointwise
to `‖u‖⁶`; the right-hand side converges to `C‖∇u‖₂` because the commutator
error `(K/(n+1))‖u‖₂` vanishes, which is where the finiteness of `‖u‖₂` and
`‖∇u‖₂` is used. -/
theorem eLpNorm_six_le_eLpNorm_fderiv_two {u : Space → Space} (hu : ContDiff ℝ 1 u)
    (hu2 : MemLp u 2 volume) (hdu2 : MemLp (fderiv ℝ u) 2 volume) :
    eLpNorm u 6 volume ≤ sobolevSixConst * eLpNorm (fderiv ℝ u) 2 volume := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_norm_fderiv_sobolevBump
  set a : ℝ := (eLpNorm (fderiv ℝ u) 2 volume).toReal with ha
  set e : ℝ := (eLpNorm u 2 volume).toReal with he
  set cc : ℝ := (sobolevSixConst : ℝ) with hcc
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  have hcc0 : 0 ≤ cc := (sobolevSixConst : ℝ≥0).coe_nonneg
  have hA : eLpNorm (fderiv ℝ u) 2 volume = ENNReal.ofReal a :=
    (ENNReal.ofReal_toReal hdu2.eLpNorm_ne_top).symm
  have hE : eLpNorm u 2 volume = ENNReal.ofReal e :=
    (ENNReal.ofReal_toReal hu2.eLpNorm_ne_top).symm
  -- the cutoff estimate at scale `R = n+1`, in real form
  have key : ∀ n : ℕ, ∫⁻ x, ‖sobolevCutoff ((n : ℝ) + 1) x • u x‖ₑ ^ (6 : ℝ)
        ∂(volume : Measure Space)
      ≤ ENNReal.ofReal ((cc * (a + K / ((n : ℝ) + 1) * e)) ^ (6 : ℝ)) := by
    intro n
    have hRpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 := eLpNorm_six_sobolevCutoff_smul_le hu hK0 hK hRpos
    rw [lintegral_enorm_rpow_six_eq]
    have hKR : (0 : ℝ) ≤ K / ((n : ℝ) + 1) := by positivity
    have hrw : ENNReal.ofReal (cc * (a + K / ((n : ℝ) + 1) * e))
        = (sobolevSixConst : ℝ≥0∞) * (ENNReal.ofReal a
            + ENNReal.ofReal (K / ((n : ℝ) + 1)) * ENNReal.ofReal e) := by
      rw [ENNReal.ofReal_mul hcc0, ENNReal.ofReal_add ha0 (by positivity),
        ENNReal.ofReal_mul hKR, hcc, ENNReal.ofReal_coe_nnreal]
    have h2 : eLpNorm (fun x => sobolevCutoff ((n : ℝ) + 1) x • u x) 6 volume
        ≤ ENNReal.ofReal (cc * (a + K / ((n : ℝ) + 1) * e)) := by
      rw [hrw, ← hA, ← hE]
      exact h1
    refine le_trans (ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 6)) ?_
    exact le_of_eq (ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num))
  -- Fatou's lemma recovers the full left-hand side
  have hfatou : ∫⁻ x, ‖u x‖ₑ ^ (6 : ℝ) ∂(volume : Measure Space)
      ≤ liminf (fun n : ℕ => ∫⁻ x, ‖sobolevCutoff ((n : ℝ) + 1) x • u x‖ₑ ^ (6 : ℝ)
          ∂(volume : Measure Space)) atTop := by
    have hmeas : ∀ n : ℕ, AEMeasurable
        (fun x => ‖sobolevCutoff ((n : ℝ) + 1) x • u x‖ₑ ^ (6 : ℝ)) (volume : Measure Space) := by
      intro n
      have hm : Measurable (fun x => ‖sobolevCutoff ((n : ℝ) + 1) x • u x‖ₑ ^ (6 : ℝ)) :=
        (((sobolevCutoff_contDiff ((n : ℝ) + 1)).continuous.smul
          hu.continuous).measurable.enorm).pow_const _
      exact hm.aemeasurable
    have hlim : ∀ x : Space,
        liminf (fun n : ℕ => ‖sobolevCutoff ((n : ℝ) + 1) x • u x‖ₑ ^ (6 : ℝ)) atTop
          = ‖u x‖ₑ ^ (6 : ℝ) := by
      intro x
      have hev : ∀ᶠ n : ℕ in atTop,
          ‖sobolevCutoff ((n : ℝ) + 1) x • u x‖ₑ ^ (6 : ℝ) = ‖u x‖ₑ ^ (6 : ℝ) := by
        filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
        have hRpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hxn : ‖x‖ ≤ (n : ℝ) + 1 := by
          have := Nat.ceil_le.mp hn
          linarith
        rw [sobolevCutoff_eq_one hRpos hxn, one_smul]
      rw [liminf_congr hev, liminf_const]
    calc ∫⁻ x, ‖u x‖ₑ ^ (6 : ℝ) ∂(volume : Measure Space)
        = ∫⁻ x, liminf (fun n : ℕ => ‖sobolevCutoff ((n : ℝ) + 1) x • u x‖ₑ ^ (6 : ℝ)) atTop
            ∂(volume : Measure Space) := by
          simp_rw [hlim]
      _ ≤ _ := lintegral_liminf_le' hmeas
  -- the commutator error vanishes
  have htendR : Tendsto (fun n : ℕ => (cc * (a + K / ((n : ℝ) + 1) * e)) ^ (6 : ℝ)) atTop
      (𝓝 ((cc * a) ^ (6 : ℝ))) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hnat
    have h1 : Tendsto (fun n : ℕ => cc * (a + K / ((n : ℝ) + 1) * e)) atTop (𝓝 (cc * a)) := by
      have h2 : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1) * e) atTop (𝓝 (0 * e)) :=
        h0.mul tendsto_const_nhds
      have h3 : Tendsto (fun n : ℕ => a + K / ((n : ℝ) + 1) * e) atTop (𝓝 (a + 0 * e)) :=
        tendsto_const_nhds.add h2
      have h4 : Tendsto (fun n : ℕ => cc * (a + K / ((n : ℝ) + 1) * e)) atTop
          (𝓝 (cc * (a + 0 * e))) := tendsto_const_nhds.mul h3
      simpa using h4
    exact ((Real.continuousAt_rpow_const (cc * a) 6 (Or.inr (by norm_num))).tendsto).comp h1
  have htend : Tendsto
      (fun n : ℕ => ENNReal.ofReal ((cc * (a + K / ((n : ℝ) + 1) * e)) ^ (6 : ℝ))) atTop
      (𝓝 (ENNReal.ofReal ((cc * a) ^ (6 : ℝ)))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp htendR
  have hbound : ∫⁻ x, ‖u x‖ₑ ^ (6 : ℝ) ∂(volume : Measure Space)
      ≤ ENNReal.ofReal ((cc * a) ^ (6 : ℝ)) := by
    refine hfatou.trans ?_
    refine le_trans (liminf_le_liminf (Eventually.of_forall key)) ?_
    exact le_of_eq htend.liminf_eq
  have hfinal : eLpNorm u 6 volume ≤ ENNReal.ofReal (cc * a) := by
    have h6 := lintegral_enorm_rpow_six_eq u
    have hle : eLpNorm u 6 volume ^ (6 : ℝ) ≤ ENNReal.ofReal ((cc * a) ^ (6 : ℝ)) := by
      rw [← h6]; exact hbound
    have hmono := ENNReal.rpow_le_rpow hle (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [← ENNReal.rpow_mul] at hmono
    norm_num at hmono
    refine hmono.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [← Real.rpow_natCast (cc * a) 6, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hA]
  refine hfinal.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hcc0, hcc, ENNReal.ofReal_coe_nnreal]

/-- The Sobolev inequality without compact support, packaged as the `Prop` that the
design record `cp01-lean-statement-design.md` lists as obligation `F #12`; it is
now a theorem (`sobolevSixWithoutCompactSupport`), not an assumption. -/
def SobolevSixWithoutCompactSupport : Prop :=
  ∀ u : Space → Space, ContDiff ℝ 1 u → MemLp u 2 volume →
    MemLp (fderiv ℝ u) 2 volume →
    eLpNorm u 6 volume ≤ sobolevSixConst * eLpNorm (fderiv ℝ u) 2 volume

/-- Obligation `F #12` of the design record is discharged: the packaged statement
`SobolevSixWithoutCompactSupport` holds, with no `sorry` and no axiom beyond
Mathlib's. -/
theorem sobolevSixWithoutCompactSupport : SobolevSixWithoutCompactSupport :=
  fun _u hu hu2 hdu2 => eLpNorm_six_le_eLpNorm_fderiv_two hu hu2 hdu2

/-! ## 3. Young's inequality in the exponent pairs `(4/3, 4)` and `(5/4, 5)` -/

/-- `4/3` and `4` are Hölder conjugate: `3/4 + 1/4 = 1`.  These are the exponents
named in the proof of Proposition `prop:enstrophy`. -/
theorem holderConjugate_four_thirds_four : Real.HolderConjugate (4 / 3) 4 :=
  Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

/-- `5/4` and `5` are Hölder conjugate: `4/5 + 1/5 = 1`. -/
theorem holderConjugate_five_fourths_five : Real.HolderConjugate (5 / 4) 5 :=
  Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

/-- **Young's inequality with conjugate exponents `4/3` and `4`**:
`ab ≤ (3/4) a^{4/3} + (1/4) b^4` for `a, b ≥ 0`.  This is the inequality the
manuscript invokes verbatim in the proof of Proposition `prop:enstrophy`
("Young's inequality with conjugate exponents `4/3` and `4`") to absorb
`C Y^{3/4}‖Δu‖₂^{3/2}` into `(ν/2)‖Δu‖₂² + Cν^{-3}Y³`.  Powers are `Real.rpow`. -/
theorem young_four_thirds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ (3 / 4) * a ^ (4 / 3 : ℝ) + (1 / 4) * b ^ (4 : ℝ) := by
  have h := Real.young_inequality_of_nonneg ha hb holderConjugate_four_thirds_four
  linarith [h]

/-- **Young's inequality with conjugate exponents `5/4` and `5`**:
`ab ≤ (4/5) a^{5/4} + (1/5) b^5` for `a, b ≥ 0`.  The `(5/4, 5)` companion of
`young_four_thirds`. -/
theorem young_five_fourths {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ (4 / 5) * a ^ (5 / 4 : ℝ) + (1 / 5) * b ^ (5 : ℝ) := by
  have h := Real.young_inequality_of_nonneg ha hb holderConjugate_five_fourths_five
  linarith [h]

/-- **Young's inequality with a free small parameter.**  For Hölder conjugate `p, q`
and every `ε > 0` there is `C > 0` with `ab ≤ ε a^p + C b^q` for all `a, b ≥ 0`.
This is the absorbing form actually used in the manuscript's proofs: the first term
is made small enough to be swallowed by the dissipation, at the cost of an
`ε`-dependent constant in front of the second. -/
theorem young_holderConjugate_eps {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * b ≤ ε * a ^ p + C * b ^ q := by
  have hp : 1 < p := (Real.holderConjugate_iff.mp hpq).1
  have hq : 1 < q := (Real.holderConjugate_iff.mp hpq.symm).1
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  set l : ℝ := (ε * p) ^ (1 / p) with hl
  have hlpos : 0 < l := Real.rpow_pos_of_pos (by positivity) _
  have hlp : l ^ p = ε * p := by
    rw [hl, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  refine ⟨l ^ (-q) / q, by positivity, fun a b ha hb => ?_⟩
  have hsplit : a * b = l * a * (b / l) := by field_simp
  have h := Real.young_inequality_of_nonneg (by positivity : (0 : ℝ) ≤ l * a)
    (by positivity : (0 : ℝ) ≤ b / l) hpq
  rw [← hsplit] at h
  refine h.trans (le_of_eq ?_)
  rw [Real.mul_rpow hlpos.le ha, Real.div_rpow hb hlpos.le, hlp, Real.rpow_neg hlpos.le]
  field_simp

/-- The `(4/3, 4)` case of `young_holderConjugate_eps`: for every `ε > 0` there is
`C > 0` with `ab ≤ ε a^{4/3} + C b^4`.  This is the shape used in
Proposition `prop:enstrophy`, where `ε` is chosen so that the `b^4 = ‖Δu‖₂²`
term is absorbed by `(ν/2)‖Δu‖₂²`. -/
theorem young_four_thirds_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a * b ≤ ε * a ^ (4 / 3 : ℝ) + C * b ^ (4 : ℝ) :=
  young_holderConjugate_eps holderConjugate_four_thirds_four hε

/-- The `(5/4, 5)` case of `young_holderConjugate_eps`: for every `ε > 0` there is
`C > 0` with `ab ≤ ε a^{5/4} + C b^5`. -/
theorem young_five_fourths_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a * b ≤ ε * a ^ (5 / 4 : ℝ) + C * b ^ (5 : ℝ) :=
  young_holderConjugate_eps holderConjugate_five_fourths_five hε

end NavierFormal

end

