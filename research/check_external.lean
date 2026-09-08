import NavierFormal.External.OpenAIUniqueness

/-!
Axiom check for the `external` lane (PLAN task FC6): the adapter to OpenAI's
`NavierStokesAndEuler` whole-space uniqueness theorem, and the first local
`#print axioms` evidence for the imported statements themselves.
Run with `lake env lean research/check_external.lean`.
-/

-- NavierFormal/External/OpenAIUniqueness.lean
#print axioms NavierFormal.External.ofSpacetime_toSpacetime
#print axioms NavierFormal.External.toSpacetime_ofSpacetime
#print axioms NavierFormal.External.coordinateVector_eq_e
#print axioms NavierFormal.External.spatialDerivative_toSpacetime
#print axioms NavierFormal.External.advection_toSpacetime
#print axioms NavierFormal.External.spatialDivergence_toSpacetime
#print axioms NavierFormal.External.pressureGradient_toSpacetime
#print axioms NavierFormal.External.temporalDerivative_toSpacetime
#print axioms NavierFormal.External.spatialLaplacian_toSpacetime
#print axioms NavierFormal.External.navierStokesResidual_toSpacetime_eq_zero
#print axioms NavierFormal.External.uniformFiniteEnergy_toSpacetime_of_bound
#print axioms NavierFormal.External.classical_uniqueness_of_compact_support
#print axioms NavierFormal.External.classical_uniqueness_of_compact_support_nu

-- The imported external statements themselves (first local axiom evidence,
-- audit §2 documents this had not previously been independently checked).
#print axioms NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc
#print axioms NavierStokesR3.WholeSpaceUniqueness.candidate_unique_on_Icc
#print axioms NavierStokesR3.WholeSpaceUniqueness.candidate_global_agrees_before_one
#print axioms NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_le
#print axioms NavierStokesR3.PressureRecovery.pressure_gradient_recovery
