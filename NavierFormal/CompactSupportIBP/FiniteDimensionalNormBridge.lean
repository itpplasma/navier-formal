import NavierFormal.Calculus
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# The finite-dimensional norm bridge for the interpolation route

`NavierFormal.Calculus` already proves the pointwise comparison between the
operator norm and the Frobenius/Hilbert--Schmidt norm on `Space →L[ℝ] Space`.
The compact-support interpolation theorem, however, uses `eLpNorm` of a field
of continuous linear maps, so the pointwise comparison must be lifted through
the `eLpNorm` seminorm before the manuscript's Frobenius quantities can be
inserted into that route.

This file contains only that bounded lift.  It does not infer measurability,
integrability, compact support, an `H²`--`C³` representative, or any PDE
statement.  The measure, measurable-space structure, exponent, and field are
all explicit in the two generic theorems below.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace NavierFormal

variable {α : Type*} [MeasurableSpace α]

/-- The nonnegative real constant `√3`, used as an `eLpNorm` multiplier. -/
def sqrtThreeNNReal : ℝ≥0 :=
  ⟨Real.sqrt 3, Real.sqrt_nonneg _⟩

@[simp]
theorem coe_sqrtThreeNNReal : (sqrtThreeNNReal : ℝ) = Real.sqrt 3 :=
  rfl

/-- The operator-norm `eLpNorm` is bounded by the Frobenius `eLpNorm`, with no
measurability or finiteness assumption hidden in the statement. -/
theorem eLpNorm_operator_le_frobenius
    (L : α → Space →L[ℝ] Space) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm L p μ ≤
      eLpNorm (fun x => frobeniusNorm (L x)) p μ := by
  apply eLpNorm_mono
  intro x
  simpa [Real.norm_eq_abs, abs_of_nonneg (frobeniusNorm_nonneg (L x))] using
    (opNorm_le_frobeniusNorm (L x))

/-- The Frobenius `eLpNorm` is bounded by `√3` times the operator-norm
`eLpNorm` in dimension three.  This is the `eLpNorm` interface consumed by
the operator-norm version of `GradientInterpolation`. -/
theorem eLpNorm_frobenius_le_sqrt_three_operator
    (L : α → Space →L[ℝ] Space) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (fun x => frobeniusNorm (L x)) p μ ≤
      sqrtThreeNNReal • eLpNorm L p μ := by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (p := p)
  filter_upwards [] with x
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm]
  simpa [Real.norm_eq_abs, abs_of_nonneg (frobeniusNorm_nonneg (L x)),
    coe_sqrtThreeNNReal] using
    (frobeniusNorm_le_sqrt_three_mul (L x))

/-- The same upper comparison specialized to a Jacobian field.  No
differentiability hypothesis is needed: `fderiv` is a total function, and
regularity belongs to the analytic theorem that consumes this bound. -/
theorem eLpNorm_frobenius_fderiv_le_sqrt_three_operator
    (u : Space → Space) (p : ℝ≥0∞) (μ : Measure Space) :
    eLpNorm (fun x => frobeniusNorm (fderiv ℝ u x)) p μ ≤
      sqrtThreeNNReal • eLpNorm (fderiv ℝ u) p μ := by
  exact eLpNorm_frobenius_le_sqrt_three_operator (fun x => fderiv ℝ u x) p μ

end NavierFormal
