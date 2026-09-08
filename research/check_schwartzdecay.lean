import NavierFormal.SchwartzDecay

/-!
Axiom check for the schwartzdecay lane (`thm:conditional` Step 0, "the data
class"; Fefferman condition (4) versus `u₀ ∈ 𝒮(ℝ³)³`; `premise:local`).  Run
with `lake env lean research/check_schwartzdecay.lean`.
-/

-- NavierFormal/SchwartzDecay.lean
#print axioms NavierFormal.SchwartzMap.decay_fefferman
#print axioms NavierFormal.SchwartzMap.ofDecay
#print axioms NavierFormal.SchwartzMap.coe_ofDecay
#print axioms NavierFormal.SchwartzDivFree.decay_fefferman
#print axioms NavierFormal.SchwartzDivFree.ofFefferman
