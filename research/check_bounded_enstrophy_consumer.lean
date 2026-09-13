import NavierFormal.CompactSupportIBP.BoundedEnstrophyConsumer

/-! Targeted trust-disabled check for the bounded enstrophy composition. -/

open MeasureTheory

namespace NavierFormal

example {u : Space → Space} (h : CompactSupportC3Hypotheses u) :
    BoundedEnstrophyConsumer u :=
  boundedEnstrophyConsumer_of_compactSupportC3 h

#print axioms NavierFormal.boundedEnstrophyConsumer_of_compactSupportC3
#print axioms NavierFormal.BoundedEnstrophyConsumer

end NavierFormal
