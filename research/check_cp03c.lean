import NavierFormal

/-!
Axiom check for the CP03c integration (statement surface of the CP1 checkpoint:
pointwise calculus, integration by parts, interpolation/Sobolev/Young, quotient
objects, and the classical solution class).  Run with
`lake env lean research/check_cp03c.lean`.
-/

-- NavierFormal/Calculus.lean
#print axioms NavierFormal.e
#print axioms NavierFormal.e_eq_basisFun
#print axioms NavierFormal.norm_e
#print axioms NavierFormal.sum_smul_e
#print axioms NavierFormal.inner_e
#print axioms NavierFormal.frobeniusNormSq
#print axioms NavierFormal.frobeniusNorm
#print axioms NavierFormal.frobeniusNormSq_nonneg
#print axioms NavierFormal.frobeniusNorm_nonneg
#print axioms NavierFormal.frobeniusNorm_sq
#print axioms NavierFormal.opNorm_le_frobeniusNorm
#print axioms NavierFormal.frobeniusNormSq_le_three_mul
#print axioms NavierFormal.frobeniusNorm_le_sqrt_three_mul
#print axioms NavierFormal.opNorm_sq_le_frobeniusNormSq
#print axioms NavierFormal.norm_apply_le_frobeniusNorm_mul
#print axioms NavierFormal.divergence
#print axioms NavierFormal.divergence_eq_sum_component
#print axioms NavierFormal.laplacian_eq_sum_iteratedFDeriv
#print axioms NavierFormal.inner_gradient_apply
#print axioms NavierFormal.gradient_component
#print axioms NavierFormal.enstrophyDensity
#print axioms NavierFormal.enstrophyDensity_nonneg
#print axioms NavierFormal.convection
#print axioms NavierFormal.gradTranspose
#print axioms NavierFormal.inner_gradTranspose_left
#print axioms NavierFormal.gradTranspose_component
#print axioms NavierFormal.inner_self_gradTranspose
#print axioms NavierFormal.norm_gradTranspose_le
#print axioms NavierFormal.kineticEnergy
#print axioms NavierFormal.kineticEnergyLintegral
#print axioms NavierFormal.X3
#print axioms NavierFormal.X3Real
#print axioms NavierFormal.kineticEnergy_nonneg
#print axioms NavierFormal.X3Real_nonneg
#print axioms NavierFormal.kineticEnergyLintegral_eq
#print axioms NavierFormal.X3_eq_lintegral_ofReal
#print axioms NavierFormal.measurable_norm_pow_three
#print axioms NavierFormal.measurable_norm_sq
#print axioms NavierFormal.D3density
#print axioms NavierFormal.D3
#print axioms NavierFormal.P3density
#print axioms NavierFormal.P3
#print axioms NavierFormal.norm_gradTranspose_sq_div_le
#print axioms NavierFormal.D3density_nonneg
#print axioms NavierFormal.D3density_le_two_mul
#print axioms NavierFormal.D3density_eq_zero_of_eq_zero
#print axioms NavierFormal.P3density_eq_mul_div
#print axioms NavierFormal.P3density_eq_zero_of_eq_zero
#print axioms NavierFormal.abs_P3density_le
#print axioms NavierFormal.hasFDerivAt_rEps_gradTranspose
#print axioms NavierFormal.fderiv_rEps_apply
#print axioms NavierFormal.fderiv_rEps_apply_self
#print axioms NavierFormal.P3density_eq_convection

-- NavierFormal/IBP.lean
#print axioms NavierFormal.IBP.coord
#print axioms NavierFormal.IBP.coord_apply
#print axioms NavierFormal.IBP.abs_coord_le
#print axioms NavierFormal.IBP.abs_divergence_le
#print axioms NavierFormal.IBP.fderiv_coord
#print axioms NavierFormal.IBP.continuous_divergence
#print axioms NavierFormal.IBP.continuous_enstrophyDensity
#print axioms NavierFormal.IBP.integral_fderiv_apply_eq_zero
#print axioms NavierFormal.IBP.integral_divergence_eq_zero
#print axioms NavierFormal.IBP.divergence_smul
#print axioms NavierFormal.IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence
#print axioms NavierFormal.IBP.laplacian_eq_sum
#print axioms NavierFormal.IBP.norm_laplacian_le
#print axioms NavierFormal.IBP.continuous_laplacian
#print axioms NavierFormal.IBP.sq_le_enstrophyDensity
#print axioms NavierFormal.IBP.differentiable_inner_dir
#print axioms NavierFormal.IBP.fderiv_inner_dir_self
#print axioms NavierFormal.IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity
#print axioms NavierFormal.IBP.integral_inner_convection_eq_zero

-- NavierFormal/Interpolation.lean
#print axioms NavierFormal.eLpNorm'_interpolate
#print axioms NavierFormal.eLpNorm_interpolate
#print axioms NavierFormal.eLpNorm_interpolate_top
#print axioms NavierFormal.eLpNorm_three_le
#print axioms NavierFormal.eLpNorm_tenThirds_le
#print axioms NavierFormal.sobolevSixConst
#print axioms NavierFormal.eLpNorm_six_le_eLpNorm_fderiv_two_of_hasCompactSupport
#print axioms NavierFormal.sobolevBump
#print axioms NavierFormal.sobolevCutoff
#print axioms NavierFormal.sobolevCutoff_contDiff
#print axioms NavierFormal.sobolevCutoff_nonneg
#print axioms NavierFormal.sobolevCutoff_le_one
#print axioms NavierFormal.sobolevCutoff_eq_one
#print axioms NavierFormal.sobolevCutoff_hasCompactSupport
#print axioms NavierFormal.exists_bound_norm_fderiv_sobolevBump
#print axioms NavierFormal.norm_fderiv_sobolevCutoff_le
#print axioms NavierFormal.eLpNorm_six_sobolevCutoff_smul_le
#print axioms NavierFormal.lintegral_enorm_rpow_six_eq
#print axioms NavierFormal.eLpNorm_six_le_eLpNorm_fderiv_two
#print axioms NavierFormal.SobolevSixWithoutCompactSupport
#print axioms NavierFormal.sobolevSixWithoutCompactSupport
#print axioms NavierFormal.holderConjugate_four_thirds_four
#print axioms NavierFormal.holderConjugate_five_fourths_five
#print axioms NavierFormal.young_four_thirds
#print axioms NavierFormal.young_five_fourths
#print axioms NavierFormal.young_holderConjugate_eps
#print axioms NavierFormal.young_four_thirds_eps
#print axioms NavierFormal.young_five_fourths_eps

-- NavierFormal/QuotientObjects.lean
#print axioms NavierFormal.L3
#print axioms NavierFormal.IsTestPotential
#print axioms NavierFormal.gradientGenerators
#print axioms NavierFormal.gradientSubspace
#print axioms NavierFormal.isClosed_gradientSubspace
#print axioms NavierFormal.gradientGenerators_subset
#print axioms NavierFormal.memLp_gradient_toLp_mem_gradientSubspace
#print axioms NavierFormal.quotientFunctional
#print axioms NavierFormal.quotientFunctional_bddBelow
#print axioms NavierFormal.quotientFunctional_nonneg
#print axioms NavierFormal.quotientFunctional_le
#print axioms NavierFormal.quotientFunctional_le_cube
#print axioms NavierFormal.quotientFunctional_zero
#print axioms NavierFormal.quotientFunctional_smul
#print axioms NavierFormal.IsQuotientMinimizer
#print axioms NavierFormal.IsQuotientMinimizer.quotientFunctional_eq
#print axioms NavierFormal.IsQuotientMinimizer.cube_norm_eq
#print axioms NavierFormal.cubicMap
#print axioms NavierFormal.cubicMap_apply
#print axioms NavierFormal.norm_cubicMap
#print axioms NavierFormal.aestronglyMeasurable_cubicMap
#print axioms NavierFormal.cubicMap_congr
#print axioms NavierFormal.IsSolenoidalL3
#print axioms NavierFormal.isSolenoidalL3_zero
#print axioms NavierFormal.quotientDissipation
#print axioms NavierFormal.strainFlux
#print axioms NavierFormal.strainFlux_zero
#print axioms NavierFormal.quotientDissipation_zero

-- NavierFormal/SolutionClass.lean
#print axioms NavierFormal.timeDeriv
#print axioms NavierFormal.timeDerivIter
#print axioms NavierFormal.timeDerivIter_zero
#print axioms NavierFormal.timeDerivIter_succ
#print axioms NavierFormal.timeDeriv_eq_deriv
#print axioms NavierFormal.convection_const_smul
#print axioms NavierFormal.divergence_const_smul
#print axioms NavierFormal.gradient_const_smul
#print axioms NavierFormal.SchwartzDivFree
#print axioms NavierFormal.SchwartzDivFree.contDiff
#print axioms NavierFormal.SchwartzDivFree.continuous
#print axioms NavierFormal.SchwartzDivFree.differentiable
#print axioms NavierFormal.IsClassicalSolution
#print axioms NavierFormal.RegularityPackage
#print axioms NavierFormal.RegularityPackage.mono
#print axioms NavierFormal.ClayAlternativeA
#print axioms NavierFormal.ClayAlternativeA_all
#print axioms NavierFormal.CriticalBound
#print axioms NavierFormal.CriticalHypothesis
#print axioms NavierFormal.IsClassicalSolution.two_le_infty
#print axioms NavierFormal.IsClassicalSolution.infty_ne_zero
#print axioms NavierFormal.IsClassicalSolution.contDiffAt_space_of_smooth
#print axioms NavierFormal.IsClassicalSolution.contDiffAt_time_of_smooth
#print axioms NavierFormal.IsClassicalSolution.contDiffAt_velocity
#print axioms NavierFormal.IsClassicalSolution.contDiffAt_pressure
#print axioms NavierFormal.IsClassicalSolution.differentiableAt_velocity
#print axioms NavierFormal.IsClassicalSolution.differentiableAt_pressure
#print axioms NavierFormal.IsClassicalSolution.differentiableAt_time
#print axioms NavierFormal.IsClassicalSolution.continuous_velocity
#print axioms NavierFormal.IsClassicalSolution.aestronglyMeasurable_velocity
#print axioms NavierFormal.IsClassicalSolution.mono
#print axioms NavierFormal.contDiffOn_timeScale
#print axioms NavierFormal.continuousOn_timeScale
#print axioms NavierFormal.IsClassicalSolution.nuNormalization
#print axioms NavierFormal.eLpNorm_three_nuNormalization
