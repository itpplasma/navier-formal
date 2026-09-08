import NavierFormal.Literature.ESS
import NavierFormal.SerrinEnstrophy
import NavierFormal.EndpointBridge

/-!
Axiom check for the `esssplit` lane (PLAN task 8.2a residual queue, FC2).
Run with `lake env lean research/check_esssplit.lean`.
-/

-- NavierFormal/Literature/ESS.lean
#print axioms NavierFormal.Literature.essL3ToL5

-- NavierFormal/SerrinEnstrophy.lean
#print axioms NavierFormal.enstrophy_differential_inequality
#print axioms NavierFormal.serrin_enstrophy_bound_sq
#print axioms NavierFormal.serrin_enstrophy_bound

-- NavierFormal/EndpointBridge.lean
#print axioms NavierFormal.endpointContinuation_of_ess
