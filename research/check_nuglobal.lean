import NavierFormal.NuRescaling

/-!
Axiom check for the `nuglobal` lane (PLAN task `8.2a`, "global viscosity
rescaling in Blowup"). Run with `lake env lean research/check_nuglobal.lean`.
-/

-- NavierFormal/NuRescaling.lean
#print axioms NavierFormal.IsGlobalSmoothSolution.rescale
#print axioms NavierFormal.UniformFiniteEnergyOn.rescale_ici
#print axioms NavierFormal.UniformFiniteEnergyOn.rescale
#print axioms NavierFormal.SpeedUnboundedAt.rescale
#print axioms NavierFormal.IsClassicalSolution.rescale
#print axioms NavierFormal.IsGlobalSmoothSolution.rescale_iff
#print axioms NavierFormal.UnforcedCounterexample.rescale
#print axioms NavierFormal.UnforcedCounterexample.nuNormalization
#print axioms NavierFormal.UnforcedCounterexample.of_nuNormalization
#print axioms NavierFormal.unforcedCounterexampleSome_iff
#print axioms NavierFormal.unforcedCounterexampleAll_iff
