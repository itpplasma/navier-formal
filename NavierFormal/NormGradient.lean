import NavierFormal.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Almost-everywhere calculus for `|u|` (manuscript Proposition `prop:pressure`)

The proof of the manuscript's Proposition `prop:pressure` (the exact pressure
balance `⅓X' + ν D₃ = P₃`) uses three pointwise facts about the scalar field
`|u|` attached to a vector field `u`:

* the chain rule `∇|u| = ⟪u, ∇u⟫ / |u|` away from the zero set of `u`;
* the Kato-type domination `|∇|u|| ≤ |∇u|`, which is the hypothesis that makes
  the dominated-convergence step `ε ↓ 0` in the manuscript's proof legitimate;
* `∇|u| = 0` almost everywhere on the zero set of `u`, which is how the
  manuscript reads the integrand `|u| |∇|u||²` of `D₃` "as zero at `u = 0`".

This module proves exactly these facts, in the generality of a map
`u : E → F` between real normed spaces (`F` an inner product space where the
chain rule is stated), specialized to `NavierFormal.Space = EuclideanSpace ℝ (Fin 3)`
only at the very end.  Nothing here is a statement about the Navier–Stokes
equations.

## Remark on the hypotheses used by the manuscript

Rademacher's theorem in Mathlib (`LipschitzWith.ae_differentiableAt`,
`LipschitzWith.ae_differentiableAt_of_real`) is stated for maps that are
Lipschitz on the *whole* finite-dimensional domain, so that is the hypothesis
used below.  For the manuscript this is not a restriction: the solutions
considered there are smooth with Schwartz-class data, hence on each compact
time interval `[0, τ] ⊂ [0, T_*)` the field `u(t)` is `C¹` with
`∇u(t)` bounded on `ℝ³` uniformly in `t ∈ [0, τ]`, and a `C¹` map with globally
bounded derivative on `ℝ³` is globally Lipschitz
(`lipschitzWith_of_nnnorm_fderiv_le`).  So the Lipschitz hypothesis of
`NavierFormal.ae_norm_fderiv_norm_le` holds for `u(t)`, `t` in a compact time
interval, which is where the manuscript applies `|∇|u|| ≤ |∇u||`.
-/

open MeasureTheory Filter
open scoped NNReal RealInnerProductSpace Topology

noncomputable section

namespace NavierFormal

section Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The chain rule away from the zero set -/

section Inner

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] {u : E → F} {u' : E →L[ℝ] F} {x : E}

/-- Manuscript Proposition `prop:pressure`, chain rule for `|u|`: where `u` is
differentiable and `u x ≠ 0`, the scalar field `y ↦ ‖u y‖` is differentiable with
Fréchet derivative `h ↦ ⟪u x, u' h⟫ / ‖u x‖`.  This is the identity behind the
manuscript's `∇|u|` and behind `div (r_ε u) = (|u| / r_ε) u · ∇|u|`. -/
theorem hasFDerivAt_norm_of_ne_zero (hu : HasFDerivAt u u' x) (hx : u x ≠ 0) :
    HasFDerivAt (fun y => ‖u y‖) (‖u x‖⁻¹ • (innerSL ℝ (u x)).comp u') x := by
  have hn : ‖u x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hne : (fun y => ‖u y‖ ^ 2) x ≠ 0 := by
    simpa using pow_ne_zero 2 hn
  have h := (hu.norm_sq).sqrt hne
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert h using 1
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, one_div]
  field_simp

/-- Manuscript Proposition `prop:pressure`, chain rule for `|u|` in applied form:
`∇|u| · h = ⟪u, ∇u · h⟫ / |u|` where `u ≠ 0`. -/
theorem fderiv_norm_apply_of_ne_zero (hu : DifferentiableAt ℝ u x) (hx : u x ≠ 0) (h : E) :
    fderiv ℝ (fun y => ‖u y‖) x h = ⟪u x, fderiv ℝ u x h⟫ / ‖u x‖ := by
  rw [(hasFDerivAt_norm_of_ne_zero hu.hasFDerivAt hx).fderiv]
  simp [div_eq_inv_mul]

end Inner

/-! ### The Kato domination `|∇|u|| ≤ |∇u|` -/

variable [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F} {u' : E →L[ℝ] F}
  {D : E →L[ℝ] ℝ} {x : E}

/-- Manuscript Proposition `prop:pressure`, directional form of `|∇|u|| ≤ |∇u|`:
wherever both `u` and `y ↦ ‖u y‖` are Fréchet differentiable, the derivative of the
norm dominates nothing more than the derivative of `u` in every direction. -/
theorem norm_apply_le_of_hasFDerivAt_norm (hu : HasFDerivAt u u' x)
    (hD : HasFDerivAt (fun y => ‖u y‖) D x) (h : E) : ‖D h‖ ≤ ‖u' h‖ := by
  have hline : HasDerivAt (fun t : ℝ => x + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  have hφ : HasDerivAt (fun t : ℝ => ‖u (x + t • h)‖) (D h) 0 := by
    have := HasFDerivAt.comp_hasDerivAt_of_eq (x := 0) (f := fun t : ℝ => x + t • h)
      hD hline (by simp)
    simpa [Function.comp_def] using this
  have hψ : HasDerivAt (fun t : ℝ => u (x + t • h)) (u' h) 0 := by
    have := HasFDerivAt.comp_hasDerivAt_of_eq (x := 0) (f := fun t : ℝ => x + t • h)
      hu hline (by simp)
    simpa [Function.comp_def] using this
  rw [hasDerivAt_iff_tendsto_slope] at hφ hψ
  refine le_of_tendsto_of_tendsto' hφ.norm hψ.norm ?_
  intro t
  simp only [slope_def_module, zero_smul, add_zero, norm_smul, sub_zero]
  gcongr
  exact abs_norm_sub_norm_le _ _

/-- Manuscript Proposition `prop:pressure`, operator-norm form of `|∇|u|| ≤ |∇u|`. -/
theorem opNorm_le_of_hasFDerivAt_norm (hu : HasFDerivAt u u' x)
    (hD : HasFDerivAt (fun y => ‖u y‖) D x) : ‖D‖ ≤ ‖u'‖ :=
  D.opNorm_le_bound (norm_nonneg _) fun h =>
    (norm_apply_le_of_hasFDerivAt_norm hu hD h).trans (u'.le_opNorm h)

/-- Manuscript Proposition `prop:pressure`, `|∇|u|| ≤ |∇u|` in terms of `fderiv`. -/
theorem norm_fderiv_norm_le (hu : DifferentiableAt ℝ u x)
    (hD : DifferentiableAt ℝ (fun y => ‖u y‖) x) :
    ‖fderiv ℝ (fun y => ‖u y‖) x‖ ≤ ‖fderiv ℝ u x‖ :=
  opNorm_le_of_hasFDerivAt_norm hu.hasFDerivAt hD.hasFDerivAt

/-! ### Vanishing of `∇|u|` on the zero set -/

omit [NormedSpace ℝ F] in
/-- Manuscript Proposition `prop:pressure`, the statement `∇|u| = 0` on the zero set:
if `u x = 0` and `y ↦ ‖u y‖` has a Fréchet derivative at `x`, that derivative is `0`,
because `x` is a global minimum of `y ↦ ‖u y‖`. -/
theorem hasFDerivAt_norm_eq_zero_of_eq_zero (hD : HasFDerivAt (fun y => ‖u y‖) D x)
    (hx : u x = 0) : D = 0 := by
  have hmin : IsLocalMin (fun y => ‖u y‖) x :=
    Filter.Eventually.of_forall fun y => by simp [hx]
  exact hmin.hasFDerivAt_eq_zero hD

omit [NormedSpace ℝ F] in
/-- Manuscript Proposition `prop:pressure`, `∇|u| = 0` on the zero set, `fderiv` form. -/
theorem fderiv_norm_eq_zero_of_eq_zero (hx : u x = 0) :
    fderiv ℝ (fun y => ‖u y‖) x = 0 := by
  by_cases hD : DifferentiableAt ℝ (fun y => ‖u y‖) x
  · exact hasFDerivAt_norm_eq_zero_of_eq_zero hD.hasFDerivAt hx
  · exact fderiv_zero_of_not_differentiableAt hD

end Pointwise

/-! ### Rademacher consequences -/

section AlmostEverywhere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {u : E → F} {C : ℝ≥0} {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ F] in
/-- Manuscript Proposition `prop:pressure`: a globally Lipschitz vector field has an
almost everywhere differentiable modulus.  This is Rademacher's theorem
(`LipschitzWith.ae_differentiableAt_of_real`) applied to `y ↦ ‖u y‖`, which is
Lipschitz with the same constant.  Only the domain needs to be finite dimensional. -/
theorem ae_differentiableAt_norm (hu : LipschitzWith C u) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun y => ‖u y‖) x := by
  have h : LipschitzWith C (fun y => ‖u y‖) := by
    simpa [Function.comp_def] using lipschitzWith_one_norm.comp hu
  exact h.ae_differentiableAt_of_real

/-- Manuscript Proposition `prop:pressure`, the almost everywhere Kato bound
`|∇|u|| ≤ |∇u|` used to dominate the `ε`-regularized integrands. -/
theorem ae_norm_fderiv_norm_le [FiniteDimensional ℝ F] (hu : LipschitzWith C u) :
    ∀ᵐ x ∂μ, ‖fderiv ℝ (fun y => ‖u y‖) x‖ ≤ ‖fderiv ℝ u x‖ := by
  filter_upwards [hu.ae_differentiableAt (μ := μ), ae_differentiableAt_norm (μ := μ) hu]
    with x hx hnx using norm_fderiv_norm_le hx hnx

/-- Manuscript Proposition `prop:pressure`, the almost everywhere Kato bound for a
`C¹` field with a global Lipschitz bound — the form in which the manuscript uses it
for a smooth solution restricted to a compact time interval. -/
theorem ae_norm_fderiv_norm_le_of_contDiff [FiniteDimensional ℝ F]
    (hsmooth : ContDiff ℝ 1 u) (hu : LipschitzWith C u) :
    ∀ᵐ x ∂μ, ‖fderiv ℝ (fun y => ‖u y‖) x‖ ≤ ‖fderiv ℝ u x‖ := by
  filter_upwards [ae_differentiableAt_norm (μ := μ) hu] with x hnx
  exact norm_fderiv_norm_le (hsmooth.differentiable one_ne_zero x) hnx

end AlmostEverywhere

section AlmostEverywhereInner

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {u : E → F} {C : ℝ≥0} {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Manuscript Proposition `prop:pressure`, the combined almost everywhere description of
`∇|u|` for a globally Lipschitz field: for almost every `x`, either `u x ≠ 0` and the
chain rule `∇|u| = ⟪u, ∇u⟫ / |u|` holds, or `u x = 0` and `∇|u| x = 0`.  The second
alternative is the manuscript's "`∇|u| = 0` almost everywhere on the zero set of its
Sobolev representative", and the first is the derivative used in `D₃` and `P₃`. -/
theorem ae_hasFDerivAt_norm (hu : LipschitzWith C u) :
    ∀ᵐ x ∂μ,
      (u x ≠ 0 ∧ HasFDerivAt (fun y => ‖u y‖)
          (‖u x‖⁻¹ • (innerSL ℝ (u x)).comp (fderiv ℝ u x)) x) ∨
      (u x = 0 ∧ fderiv ℝ (fun y => ‖u y‖) x = 0) := by
  filter_upwards [hu.ae_differentiableAt (μ := μ)] with x hx
  by_cases h0 : u x = 0
  · exact Or.inr ⟨h0, fderiv_norm_eq_zero_of_eq_zero h0⟩
  · exact Or.inl ⟨h0, hasFDerivAt_norm_of_ne_zero hx.hasFDerivAt h0⟩

end AlmostEverywhereInner

/-! ### Specialization to the physical space `ℝ³` -/

section Space

variable {u : Space → Space} {C : ℝ≥0}

/-- Manuscript Proposition `prop:pressure` on `ℝ³`: for a globally Lipschitz velocity
field, `|∇|u|| ≤ |∇u|` Lebesgue-almost everywhere. -/
theorem ae_norm_fderiv_norm_le_space (hu : LipschitzWith C u) :
    ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (fun y => ‖u y‖) x‖ ≤ ‖fderiv ℝ u x‖ :=
  ae_norm_fderiv_norm_le hu

/-- Manuscript Proposition `prop:pressure` on `ℝ³`: the combined almost everywhere
description of `∇|u|`, chain rule off the zero set and vanishing on it. -/
theorem ae_hasFDerivAt_norm_space (hu : LipschitzWith C u) :
    ∀ᵐ x ∂(volume : Measure Space),
      (u x ≠ 0 ∧ HasFDerivAt (fun y => ‖u y‖)
          (‖u x‖⁻¹ • (innerSL ℝ (u x)).comp (fderiv ℝ u x)) x) ∨
      (u x = 0 ∧ fderiv ℝ (fun y => ‖u y‖) x = 0) :=
  ae_hasFDerivAt_norm hu

end Space

end NavierFormal
