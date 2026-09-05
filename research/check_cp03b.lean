import NavierFormal

/-!
Axiom check for the CP03b integration (supporting lemmas for the proof of
prop:pressure: the regularized speed `r_ε`, its time primitive `H_ε`, and the
almost-everywhere calculus of `|u|`).  Run with
`lake env lean research/check_cp03b.lean`.
-/

-- NavierFormal/Regularization.lean
#print axioms NavierFormal.rEps
#print axioms NavierFormal.HEps
#print axioms NavierFormal.HEpsConst
#print axioms NavierFormal.sqrt_cube_eq_rpow
#print axioms NavierFormal.rEps_sq
#print axioms NavierFormal.rEps_pos
#print axioms NavierFormal.norm_le_rEps
#print axioms NavierFormal.rEps_le_norm_add_sqrt
#print axioms NavierFormal.rEps_mono
#print axioms NavierFormal.norm_sq_div_rEps_le
#print axioms NavierFormal.norm_div_rEps_le_one
#print axioms NavierFormal.rEps_cube
#print axioms NavierFormal.HEps_eq_cube
#print axioms NavierFormal.HEps_nonneg
#print axioms NavierFormal.HEps_le_norm_sq_mul_rEps
#print axioms NavierFormal.HEps_le
#print axioms NavierFormal.abs_HEps_le
#print axioms NavierFormal.abs_HEps_le_two
#print axioms NavierFormal.tendsto_rEps
#print axioms NavierFormal.tendsto_HEps
#print axioms NavierFormal.rEps_fderiv_apply
#print axioms NavierFormal.hasFDerivAt_rEps
#print axioms NavierFormal.hasFDerivAt_HEps
#print axioms NavierFormal.opNorm_rEps_fderiv_le
#print axioms NavierFormal.rEps_smul_fderiv_apply
#print axioms NavierFormal.hasFDerivAt_rEps_smul
#print axioms NavierFormal.hasFDerivAt_rEps_space
#print axioms NavierFormal.hasFDerivAt_HEps_space
#print axioms NavierFormal.hasFDerivAt_rEps_smul_space

-- NavierFormal/NormGradient.lean
#print axioms NavierFormal.hasFDerivAt_norm_of_ne_zero
#print axioms NavierFormal.fderiv_norm_apply_of_ne_zero
#print axioms NavierFormal.norm_apply_le_of_hasFDerivAt_norm
#print axioms NavierFormal.opNorm_le_of_hasFDerivAt_norm
#print axioms NavierFormal.norm_fderiv_norm_le
#print axioms NavierFormal.hasFDerivAt_norm_eq_zero_of_eq_zero
#print axioms NavierFormal.fderiv_norm_eq_zero_of_eq_zero
#print axioms NavierFormal.ae_differentiableAt_norm
#print axioms NavierFormal.ae_norm_fderiv_norm_le
#print axioms NavierFormal.ae_norm_fderiv_norm_le_of_contDiff
#print axioms NavierFormal.ae_hasFDerivAt_norm
#print axioms NavierFormal.ae_norm_fderiv_norm_le_space
#print axioms NavierFormal.ae_hasFDerivAt_norm_space
