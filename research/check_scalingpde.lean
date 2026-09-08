import NavierFormal.ScalingPDE

/-!
Axiom check for the `scalingpde` lane (PLAN task FC4 / manuscript `prop:scaling`(i)).
Run with `lake env lean research/check_scalingpde.lean`.
-/

-- NavierFormal/ScalingPDE.lean
#print axioms NavierFormal.hasFDerivAt_comp_dilate
#print axioms NavierFormal.differentiableAt_comp_dilate
#print axioms NavierFormal.fderiv_comp_dilate_apply
#print axioms NavierFormal.convection_dilate
#print axioms NavierFormal.divergence_dilate
#print axioms NavierFormal.divergence_dilate_full
#print axioms NavierFormal.gradient_const_smul_dilate
#print axioms NavierFormal.laplacian_dilate
#print axioms NavierFormal.laplacian_const_smul_dilate
#print axioms NavierFormal.contDiffOn_spaceTimeDilate
#print axioms NavierFormal.continuousOn_spaceTimeDilate
#print axioms NavierFormal.IsClassicalSolution.dilate
#print axioms NavierFormal.dilateSpaceTime_uncurry
