import NavierFormal.Literature.LocalTheory
import NavierFormal.Literature.Endpoint

/-!
# The conditional Clay alternative A (manuscript `thm:conditional`, Phase I)

This module proves the manuscript's Theorem `thm:conditional`
("If Hypothesis `hyp:critical` holds, then Theorem `def:target` holds") from
the two literature axioms `NavierFormal.Literature.localTheory` and
`NavierFormal.Literature.endpointContinuation`, following manuscript Steps
0–2 of the proof of `thm:conditional` (Step 0, the data-class identification,
is already built into `NavierFormal.SchwartzDivFree`; Steps 1–2 are
`conditional_clay_A_of_bound` below).

`#print axioms conditional_clay_A` shows exactly `propext, Classical.choice,
Quot.sound, NavierFormal.Literature.localTheory,
NavierFormal.Literature.endpointContinuation` (`research/check_conditional.lean`).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace NavierFormal

/-- **Manuscript `thm:conditional`, fixed `(ν,u₀)` form.**  If the
finite-horizon critical `L³` bound `NavierFormal.CriticalBound` holds for
one viscosity `ν > 0` and one divergence-free Schwartz datum `u₀`, then the
Clay alternative (A) holds for that pair.

Proof (manuscript Steps 1–2 of `thm:conditional`).  Take the maximal branch
`(Tstar,u,p)` of `Literature.localTheory`.  If `Tstar` were finite, put
`H := Tstar.toReal + 1`; `CriticalBound` at this horizon gives a finite `M`
bounding `‖u(t)‖₃` for every classical solution on every `[0,T')`,
`T' ≤ H` — in particular for `(u,p)` itself, restricted to a suitable
`T' < Tstar` — contradicting the unboundedness given by
`Literature.endpointContinuation`.  Hence `Tstar = ∞`
(manuscript's `thm:continuation` argument, "this contradicts (R4)"), and
`Literature.clayAlternativeA_of_Tstar_top` assembles the global-smoothness
and energy clauses of `localTheory` into `ClayAlternativeA`
(manuscript Steps 2–5, `lem:global-smooth` and `prop:energy`). -/
theorem conditional_clay_A_of_bound {ν : ℝ} (hν : 0 < ν) {u₀ : SchwartzDivFree}
    (hcb : CriticalBound ν u₀) : ClayAlternativeA ν u₀ := by
  obtain ⟨Tstar, u, p, -, hsol, hblow, hglob, -⟩ := Literature.localTheory ν hν u₀
  have hTstarTop : Tstar = ⊤ := by
    by_contra hne
    have hlt : Tstar < ⊤ := lt_top_iff_ne_top.mpr hne
    -- Step 1: `H := T_* + 1` (manuscript notation `S_* = ν T_*`, real time here).
    obtain ⟨M, -, hM⟩ := hcb (Tstar.toReal + 1) (by positivity)
    -- `Literature.endpointContinuation` at this `M` gives an unbounded time `t`.
    obtain ⟨t, ht0, htlt, htgt⟩ :=
      Literature.endpointContinuation ν hν u₀ Tstar u p hsol hblow hlt M
    have htTstar : t < Tstar.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal ht0.le hlt.ne).1 htlt
    -- restrict the branch to a time strictly between `t` and `Tstar`.
    set T' : ℝ := (t + Tstar.toReal) / 2 with hT'_def
    have hT't : t < T' := by rw [hT'_def]; linarith
    have hT'Tstar : T' < Tstar.toReal := by rw [hT'_def]; linarith
    have hT'pos : 0 < T' := ht0.trans hT't
    have hT'H : T' ≤ Tstar.toReal + 1 := by linarith
    have hT'lt : ENNReal.ofReal T' < Tstar :=
      (ENNReal.ofReal_lt_iff_lt_toReal hT'pos.le hlt.ne).2 hT'Tstar
    have hsolT' : IsClassicalSolution ν (⇑u₀) T' u p := (hsol T' hT'pos hT'lt).1
    have hle : eLpNorm (u t) 3 volume ≤ ENNReal.ofReal M := hM T' u p hT'H hsolT' t ht0 hT't
    exact absurd hle (not_le.2 htgt)
  refine Literature.clayAlternativeA_of_Tstar_top hν ?_ (hglob hTstarTop)
  intro T hT0 _
  exact hsol T hT0 (hTstarTop ▸ ENNReal.ofReal_lt_top)

/-- **Manuscript `thm:conditional`.**  If the finite-horizon critical
estimate `NavierFormal.CriticalHypothesis` (manuscript `hyp:critical`)
holds, then the Clay alternative (A) holds for every viscosity and every
divergence-free Schwartz datum (manuscript `def:target`, Fefferman's
alternative (A)).  Immediate from `conditional_clay_A_of_bound`,
specialised at each `(ν,u₀)` (manuscript Step 0: the data class
identification, `CriticalHypothesis` unfolds to `CriticalBound ν u₀` at
each pair). -/
theorem conditional_clay_A (hcrit : CriticalHypothesis) : ClayAlternativeA_all :=
  fun ν hν u₀ => conditional_clay_A_of_bound hν (hcrit ν hν u₀)

end NavierFormal
