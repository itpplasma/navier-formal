import NavierFormal.HessianLaplacianEnstrophy
import NavierFormal.CompactSupportIBP.FiniteDimensionalNormBridge
import NavierFormal.CompactSupportIBP.GradientInterpolation

/-!
# Bounded enstrophy consumer under explicit compact-support data

This file is the smallest checked composition of the current bounded route for
manuscript `prop:enstrophy`.  It packages the exact squared-Laplacian input
(`ha2`), the operator-norm Jacobian interpolation estimate, and the verified
operator/Frobenius comparisons for the Jacobian field.

The result is intentionally a consumer package, not the manuscript theorem:
`CompactSupportC3Hypotheses` is not obtained from generic `H²` data, and the
second-derivative operator norm in the interpolation theorem is not silently
identified with `hessianFrobeniusSq`.  The critical `L³` producer is absent.
-/

open MeasureTheory Laplacian
open scoped ENNReal NNReal

noncomputable section

namespace NavierFormal

/-- The currently supported bounded composition for manuscript
`prop:enstrophy`: exact `ha2` bookkeeping, operator-norm interpolation, and
the Jacobian norm-convention bridges.  All fields are under the explicit
compact-support pointwise-`C³` package; no manuscript `H²` representative or
critical `L³` producer is inferred. -/
structure BoundedEnstrophyConsumer (u : Space → Space) : Prop where
  /-- The squared dissipation input used by `enstrophy_inequality`. -/
  ha2 :
    (Real.sqrt (∫ x, hessianFrobeniusSq u x)) ^ 2 =
      ∫ x, ‖Δ u x‖ ^ 2
  /-- The bounded Jacobian interpolation estimate from the compact-support
  Sobolev route, in Mathlib's operator-norm `eLpNorm` convention. -/
  gradientInterpolation :
    eLpNorm (fderiv ℝ u) 3 volume ≤
      eLpNorm (fderiv ℝ u) 2 volume ^ (1 / 2 : ℝ) *
        (jacobianSobolevSixConst *
          eLpNorm (fderiv ℝ (fderiv ℝ u)) 2 volume) ^ (1 / 2 : ℝ)
  /-- Operator-norm Jacobian `eLpNorm` is bounded by its Frobenius version. -/
  operatorLeFrobenius :
    eLpNorm (fderiv ℝ u) 2 volume ≤
      eLpNorm (fun x => frobeniusNorm (fderiv ℝ u x)) 2 volume
  /-- Frobenius Jacobian `eLpNorm` is bounded by `√3` times the operator
  version. -/
  frobeniusLeSqrtThreeOperator :
    eLpNorm (fun x => frobeniusNorm (fderiv ℝ u x)) 2 volume ≤
      sqrtThreeNNReal • eLpNorm (fderiv ℝ u) 2 volume

/-- Construct the bounded enstrophy consumer from the already checked compact
support adapter, Hessian/Laplacian bookkeeping, interpolation theorem, and
finite-dimensional norm bridge.  This theorem formalizes only the bounded
composition supported by those explicit hypotheses. -/
theorem boundedEnstrophyConsumer_of_compactSupportC3
    {u : Space → Space} (h : CompactSupportC3Hypotheses u) :
    BoundedEnstrophyConsumer u := by
  refine
    { ha2 := ?_
      gradientInterpolation := gradient_interpolation_of_compactSupportC3 h
      operatorLeFrobenius := ?_
      frobeniusLeSqrtThreeOperator := ?_ }
  · exact hessian_laplacian_ha2_of_IBPData h.smooth
      (CompactSupportC3Hypotheses.toHessianLaplacianIBPData h)
  · exact eLpNorm_operator_le_frobenius (fun x => fderiv ℝ u x) 2 volume
  · exact eLpNorm_frobenius_fderiv_le_sqrt_three_operator u 2 volume

end NavierFormal

end
