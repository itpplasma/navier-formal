import NavierFormal

/-!
Axiom check for the CP03a integration (prop:ode and the scaling / interpolation
half of prop:scaling).  Run with `lake env lean research/check_cp03a.lean`.
-/

-- NavierFormal/Ode.lean
#print axioms NavierFormal.scalarObstruction
#print axioms NavierFormal.scalarObstruction_base_pos
#print axioms NavierFormal.scalarObstruction_pos
#print axioms NavierFormal.hasDerivAt_scalarObstruction
#print axioms NavierFormal.intervalIntegrable_scalarObstruction
#print axioms NavierFormal.integrableOn_scalarObstruction
#print axioms NavierFormal.tendsto_scalarObstruction
#print axioms NavierFormal.integral_scalarObstruction
#print axioms NavierFormal.scalar_obstruction_exists

-- NavierFormal/Scaling.lean
#print axioms NavierFormal.dilate
#print axioms NavierFormal.dilateSpaceTime
#print axioms NavierFormal.map_smul_volume
#print axioms NavierFormal.rpow_dilate_factor
#print axioms NavierFormal.eLpNorm_comp_smul
#print axioms NavierFormal.eLpNorm_dilate
#print axioms NavierFormal.eLpNorm_dilate_three
#print axioms NavierFormal.eLpNorm_dilate_two
#print axioms NavierFormal.eLpNorm_dilate_two_sq
#print axioms NavierFormal.eLpNorm_dilateSpaceTime

-- NavierFormal/InterpolationMismatch.lean
#print axioms NavierFormal.scalingWitness
#print axioms NavierFormal.aestronglyMeasurable_scalingWitness
#print axioms NavierFormal.integrable_scalingWitness_rpow_four
#print axioms NavierFormal.memLp_scalingWitness_four
#print axioms NavierFormal.lt_scalingWitness
#print axioms NavierFormal.eLpNormEssSup_scalingWitness
#print axioms NavierFormal.exists_memLp_four_not_memLp_top
#print axioms NavierFormal.exists_memLp_four_eLpNorm_top_eq_top
#print axioms NavierFormal.L4L3_supercritical
