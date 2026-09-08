import NavierFormal.Blowup

/-!
Axiom check for the `blowup` lane (PLAN task FC7 / UE4 statement surface).
Run with `lake env lean research/check_blowup.lean`.
-/

-- NavierFormal/Blowup.lean
#print axioms NavierFormal.SpeedUnboundedAt
#print axioms NavierFormal.L3UnboundedAt
#print axioms NavierFormal.EnstrophyUnboundedAt
#print axioms NavierFormal.UniformFiniteEnergyOn
#print axioms NavierFormal.UniformFiniteEnergyOn.mono
#print axioms NavierFormal.IsGlobalSmoothSolution
#print axioms NavierFormal.clayAlternativeA_iff
#print axioms NavierFormal.IsGlobalSmoothSolution.restrict
#print axioms NavierFormal.IsGlobalSmoothSolution.uniformFiniteEnergyOn
#print axioms NavierFormal.UnforcedCounterexample
#print axioms NavierFormal.UnforcedCounterexampleSome
#print axioms NavierFormal.UnforcedCounterexampleAll
#print axioms NavierFormal.UnforcedCounterexample.not_clayAlternativeA_all
#print axioms NavierFormal.not_clayAlternativeA_all_of_some
#print axioms NavierFormal.SpeedUnboundedAt.not_bounded
#print axioms NavierFormal.SchwartzDivFree.smul
#print axioms NavierFormal.SchwartzDivFree.coe_smul
#print axioms NavierFormal.SchwartzDivFree.smul_ne_zero
#print axioms NavierFormal.UniformFiniteEnergyOn.nuNormalization
#print axioms NavierFormal.UnforcedCounterexample.nuNormalization_energy
