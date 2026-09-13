import NavierFormal.HessianLaplacianEnstrophy
import NavierFormal.EnstrophyInequality
import NavierFormal.CompactSupportIBP.GradientInterpolation

/-! Targeted trust-disabled checks for the consumer-facing `ha2` producer. -/

open MeasureTheory Laplacian

namespace NavierFormal

example {u : Space → Space} (hu : ContDiff ℝ 3 u)
    (h : HessianLaplacianIBPData u) :
    (Real.sqrt (∫ x, hessianFrobeniusSq u x)) ^ 2 =
      ∫ x, ‖Δ u x‖ ^ 2 :=
  hessian_laplacian_ha2_of_IBPData hu h

/- Keep the existing consumers in the targeted import closure. -/
#check @enstrophy_inequality
#check @gradient_interpolation_of_compactSupportC3

#print axioms NavierFormal.hessian_laplacian_ha2_of_IBPData
#print axioms NavierFormal.hessian_laplacian_L2_identity
#print axioms NavierFormal.enstrophy_inequality
#print axioms NavierFormal.gradient_interpolation_of_compactSupportC3

end NavierFormal
