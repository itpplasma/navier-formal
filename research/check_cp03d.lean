import NavierFormal

/-!
Axiom check for the CP03d integration (the `∇|u|` form of the `D₃`/`P₃`
densities and the divergence identity of `prop:pressure`; critical-scaling
invariance of the cubic gradient quotient of `sec:quotient`).  Run with
`lake env lean research/check_cp03d.lean`.
-/

-- NavierFormal/DensityBridge.lean
#print axioms NavierFormal.fderiv_norm_apply_eq_inner_gradTranspose_div
#print axioms NavierFormal.gradient_norm_eq_smul_gradTranspose
#print axioms NavierFormal.gradTranspose_eq_smul_gradient_norm
#print axioms NavierFormal.norm_gradient_norm_eq
#print axioms NavierFormal.norm_gradTranspose_sq_div_eq
#print axioms NavierFormal.D3density_eq_gradient_norm
#print axioms NavierFormal.D3density_eq_enstrophy_add_gradient_norm
#print axioms NavierFormal.inner_self_gradient_norm
#print axioms NavierFormal.P3density_eq_gradient_norm
#print axioms NavierFormal.gradient_norm_of_zero
#print axioms NavierFormal.D3density_of_zero
#print axioms NavierFormal.D3density_gradient_norm_of_zero
#print axioms NavierFormal.P3density_of_zero
#print axioms NavierFormal.P3density_gradient_norm_of_zero
#print axioms NavierFormal.fderiv_rEps_apply_inner_gradTranspose
#print axioms NavierFormal.gradient_rEps_eq_smul_gradTranspose
#print axioms NavierFormal.sum_component_inner_fderiv
#print axioms NavierFormal.divergence_rEps_smul_add
#print axioms NavierFormal.divergence_rEps_smul
#print axioms NavierFormal.inner_gradTranspose_self_div_rEps_eq
#print axioms NavierFormal.divergence_rEps_smul_eq_gradient_norm
#print axioms NavierFormal.divergence_rEps_smul_of_zero

-- NavierFormal/QuotientScaling.lean
#print axioms NavierFormal.dilate_add
#print axioms NavierFormal.dilate_const_smul
#print axioms NavierFormal.dilate_dilate
#print axioms NavierFormal.dilate_one
#print axioms NavierFormal.dilate_inv_dilate
#print axioms NavierFormal.dilate_dilate_inv
#print axioms NavierFormal.quasiMeasurePreserving_smul_space
#print axioms NavierFormal.dilate_congr_ae
#print axioms NavierFormal.memLp_dilate
#print axioms NavierFormal.dilateL3Fun
#print axioms NavierFormal.coeFn_dilateL3Fun
#print axioms NavierFormal.norm_dilateL3Fun
#print axioms NavierFormal.dilateL3Fun_add
#print axioms NavierFormal.dilateL3Fun_smul
#print axioms NavierFormal.dilateL3Fun_inv_left
#print axioms NavierFormal.dilateL3Fun_inv_right
#print axioms NavierFormal.dilateL3
#print axioms NavierFormal.dilateL3_apply
#print axioms NavierFormal.dilateL3_symm_apply
#print axioms NavierFormal.space_eq_of_inner_eq
#print axioms NavierFormal.gradient_comp_smul
#print axioms NavierFormal.dilate_gradient
#print axioms NavierFormal.IsTestPotential.comp_smul
#print axioms NavierFormal.dilateL3_mem_gradientGenerators
#print axioms NavierFormal.dilateL3_image_gradientGenerators
#print axioms NavierFormal.dilateL3_map_span
#print axioms NavierFormal.dilateL3_image_span
#print axioms NavierFormal.dilateL3_mem_gradientSubspace
#print axioms NavierFormal.dilateL3_mem_gradientSubspace_iff
#print axioms NavierFormal.dilateL3_symm_mem_gradientSubspace
#print axioms NavierFormal.dilateL3_gradientSubspace
#print axioms NavierFormal.quotientFunctional_dilateL3
#print axioms NavierFormal.quotientFunctional_smul_dilateL3
#print axioms NavierFormal.isQuotientMinimizer_dilateL3
