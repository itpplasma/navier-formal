import NavierFormal.CompactSupportIBP.Adapter
import NavierFormal.Interpolation

/-!
# Compact-support gradient interpolation

This module formalizes the next bounded step after the compact-support
integration-by-parts adapter in the proof of manuscript `lem:GN`, used in
`prop:enstrophy`.

The proof is the manuscript's interpolation--Sobolev chain applied to the
Jacobian field `fderiv ℝ u`: first interpolate its `L²` and `L⁶` norms, then
apply the compact-support Sobolev inequality to that Jacobian field.  The
result is deliberately stated in Lean's operator-norm `eLpNorm` convention.
The manuscript's Frobenius `L²` norms and the final replacement of the
Hessian norm by the Laplacian norm are not identified by coercion here; the
existing exact identity in `HessianLaplacianL2` remains the explicit bridge
for that latter step.

Nothing in this file asserts or produces the critical `L³` bound from the
manuscript's `hyp:critical`.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace NavierFormal

/-- The Sobolev constant for the Jacobian field, whose values lie in the
finite-dimensional space of continuous linear maps `ℝ³ → ℝ³`.  This is the
constant in the bounded operator-norm version of manuscript `lem:GN`. -/
def jacobianSobolevSixConst : ℝ≥0 :=
  SNormLESNormFDerivOfEqConst (Space →L[ℝ] Space) (volume : Measure Space) 2

/-- Sobolev applied to the Jacobian of a compactly supported `C³` field.  This
is the `ℝ⁹`-valued Sobolev step in manuscript `lem:GN`, before the
finite-dimensional Frobenius norm bookkeeping. -/
theorem eLpNorm_six_fderiv_le_of_compactSupportC3
    {u : Space → Space} (h : CompactSupportC3Hypotheses u) :
    eLpNorm (fderiv ℝ u) 6 volume ≤
      jacobianSobolevSixConst * eLpNorm (fderiv ℝ (fderiv ℝ u)) 2 volume := by
  have hv : ContDiff ℝ 1 (fderiv ℝ u) :=
    h.smooth.fderiv_right (m := 1) (by norm_num)
  have hcompact : HasCompactSupport (fderiv ℝ u) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) h.compact
  have hdim : Module.finrank ℝ Space = 3 := by
    simp
  have hs := eLpNorm_le_eLpNorm_fderiv_of_eq
    (F := Space →L[ℝ] Space) (E := Space)
    (μ := (volume : Measure Space)) (p := 2) (p' := 6) hv hcompact
    (by norm_num) (by rw [hdim]; norm_num) (by rw [hdim]; norm_num)
  simpa [jacobianSobolevSixConst] using hs

/-- **Bounded gradient interpolation**, the interpolation--Sobolev half of
manuscript `lem:GN` used in `prop:enstrophy`.

For compactly supported pointwise `C³` fields,

`‖∇u‖₃ ≤ C_J^{1/2} ‖∇u‖₂^{1/2} ‖D²u‖₂^{1/2}`.

Here the Jacobian and Hessian norms are the operator norms appearing in
Mathlib's `eLpNorm`; this theorem makes no claim that they are already the
manuscript's Frobenius norms. -/
theorem gradient_interpolation_of_compactSupportC3
    {u : Space → Space} (h : CompactSupportC3Hypotheses u) :
    eLpNorm (fderiv ℝ u) 3 volume ≤
      eLpNorm (fderiv ℝ u) 2 volume ^ (1 / 2 : ℝ) *
        (jacobianSobolevSixConst *
          eLpNorm (fderiv ℝ (fderiv ℝ u)) 2 volume) ^ (1 / 2 : ℝ) := by
  have hdu : ContDiff ℝ 1 (fderiv ℝ u) :=
    h.smooth.fderiv_right (m := 1) (by norm_num)
  have hinterp := eLpNorm_three_le
    (μ := (volume : Measure Space)) (f := fderiv ℝ u)
    hdu.continuous.aestronglyMeasurable
  have hsob := eLpNorm_six_fderiv_le_of_compactSupportC3 h
  calc
    eLpNorm (fderiv ℝ u) 3 volume ≤
        eLpNorm (fderiv ℝ u) 2 volume ^ (1 / 2 : ℝ) *
          eLpNorm (fderiv ℝ u) 6 volume ^ (1 / 2 : ℝ) := hinterp
    _ ≤ eLpNorm (fderiv ℝ u) 2 volume ^ (1 / 2 : ℝ) *
        (jacobianSobolevSixConst *
          eLpNorm (fderiv ℝ (fderiv ℝ u)) 2 volume) ^ (1 / 2 : ℝ) := by
      gcongr

end NavierFormal

end
