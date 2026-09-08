import NavierFormal.ClayReference

/-!
Axiom check for the ClayReference lane (task FC0, statement alignment).  Run with
`lake env lean research/check_clayref.lean`.
-/

-- NavierFormal/ClayReference.lean
#print axioms NavierFormal.ClayReference.divergence_eq
#print axioms NavierFormal.ClayReference.contDiffOn_prod_swap_iff
#print axioms NavierFormal.ClayReference.navierStokesExistenceAndSmoothness_iff
#print axioms NavierFormal.ClayReference.energy_bound_iff
#print axioms NavierFormal.ClayReference.navierStokesExistenceAndSmoothnessRn_iff
#print axioms NavierFormal.ClayReference.clayAlternativeA_iff
#print axioms NavierFormal.ClayReference.clayAlternativeA_all_implies_reference
