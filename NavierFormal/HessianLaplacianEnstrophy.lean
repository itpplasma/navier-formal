import NavierFormal.HessianLaplacianL2

/-!
# Hessian--Laplacian bookkeeping for the enstrophy consumer

This module supplies the exact `ha2` input expected by
`NavierFormal.enstrophy_inequality` from the explicit
`HessianLaplacianIBPData` package.  It composes the checked integrated
Hessian--Laplacian identity only; it does not infer that package from an
`H²` hypothesis, compact support, or a pointwise representative.
-/

open MeasureTheory Laplacian

noncomputable section

namespace NavierFormal

/-- The exact squared-dissipation bookkeeping used as `ha2` by
`NavierFormal.enstrophy_inequality`: when `a` is the Frobenius Hessian
`L²` square root, its square is the Laplacian `L²` integral under the explicit
whole-space integration-by-parts package.  This is the consumer-facing form
of manuscript `prop:enstrophy`, `lem:plancherel`(ii). -/
theorem hessian_laplacian_ha2_of_IBPData
    {u : Space → Space} (hu : ContDiff ℝ 3 u)
    (h : HessianLaplacianIBPData u) :
    (Real.sqrt (∫ x, hessianFrobeniusSq u x)) ^ 2 =
      ∫ x, ‖Δ u x‖ ^ 2 := by
  have hnonneg : 0 ≤ ∫ x, hessianFrobeniusSq u x := by
    apply integral_nonneg
    intro x
    exact Finset.sum_nonneg fun j _ => enstrophyDensity_nonneg
      (firstDirectionalDerivative u j) x
  rw [Real.sq_sqrt hnonneg]
  exact hessian_laplacian_L2_identity hu h

end NavierFormal
