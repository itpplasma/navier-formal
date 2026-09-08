import NavierFormal.LocalTheoryBridge

-- Axiom checks for the `taosplit` lane (PLAN 8.2a residual queue, FC1): the pure literature
-- axiom `taoLocalTheory`, the proved bridge `localTheory_of_tao` (and its two convenience
-- consequences), and `thm:conditional` reproved through this route.

#print axioms NavierFormal.Literature.taoLocalTheory
#print axioms NavierFormal.localTheory_of_tao
#print axioms NavierFormal.isClassicalSolution_of_lt_of_tao
#print axioms NavierFormal.clayAlternativeA_of_Tstar_top_of_tao
#print axioms NavierFormal.conditional_clay_A_of_bound_of_tao
#print axioms NavierFormal.conditional_clay_A_of_tao
