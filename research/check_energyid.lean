import NavierFormal.EnergyIdentity

/-!
Axiom check for lane `energyid` (manuscript `prop:energy`, the energy identity
assembled from a single hypothesis bundle).  Run with
`lake env lean research/check_energyid.lean`.
-/

-- NavierFormal/EnergyIdentity.lean
#print axioms NavierFormal.EnergyIdentity.hasL2DerivWithinAt_mono
#print axioms NavierFormal.EnergyIdentity.energy_hasDerivAt
#print axioms NavierFormal.EnergyIdentity.energy_identity
#print axioms NavierFormal.EnergyIdentity.energy_nonincreasing
