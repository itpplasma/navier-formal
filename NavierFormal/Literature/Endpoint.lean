import NavierFormal.Literature.LocalTheory

/-!
# Literature axiom: the endpoint continuation theorem (manuscript `thm:continuation`)

This module states, as a single Lean `axiom`, the manuscript's endpoint
continuation criterion for the maximal classical branch of
`NavierFormal.Literature.localTheory`: if the branch's maximal time is
finite, its `L³` norm is unbounded.

**Source record.** Escauriaza–Seregin–Šverák, "`L_{3,∞}`-solutions of
Navier–Stokes equations and backward uniqueness", *Russian Math. Surveys*
58 (2003), Theorem 1.3 (the manuscript's `thm:ess`, quoted verbatim there
with the mixed-norm convention of `rem:ess-norm`: the hypothesis is
`v ∈ L^∞_tL^3_x(Q_T)`, i.e. `L_{3,∞}(Q_T)` in the cited paper's own
notation), combined with three manuscript-owned bridges from the classical
branch of `prop:localtheory` to the hypotheses of that theorem:
`lem:leray-hopf` (the `ν`-normalised branch, restricted to a finite
sub-interval, is a Leray–Hopf weak solution of the Cauchy problem in the
sense of `\cite{ESS2003}`), `lem:l3-to-l5` (a uniform `L³` bound on the
branch turns the `L^5(Q_T)` conclusion of Theorem 1.3 back into a bound on
`u`), and `lem:serrin-enstrophy` (a Serrin-type Grönwall estimate turning
finite `L^5` space-time integrability into a uniform `H¹` bound), together
with the manuscript's own conclusion in `thm:continuation`
("`sup‖u(t)‖₃<∞` … contradicts (R4)" [the blow-up alternative
`prop:localtheory`(v)]).  **Phase I axiom, and it is coarser than the pure
literature input**: the three bridges above are manuscript-owned real
analysis (weak-solution identification, Tonelli/Hölder bookkeeping between
`L³`, `L⁵`, `H¹`, and a nonlinear Grönwall argument), not statements of
`\cite{ESS2003}`, and this axiom folds them into the literature package
rather than formalizing the Leray–Hopf weak-solution class in Lean and
proving them, which the lane's brief marks out of scope.  Recorded here
explicitly, as instructed, rather than silently: an eventual Phase II
discharge of this axiom must supply the Leray–Hopf class and all three
bridges, not merely Theorem 1.3 itself. (`docs/literature-assumptions.yaml`
does not yet carry an ESS-2003 entry; the nearest existing entry,
`gkp-2013-theorem-4`, cites a different paper for a related endpoint
statement and is not used here.)

**Statement shape.**  The hypotheses reproduce exactly the two data clauses
of a `Literature.localTheory` branch that the manuscript's proof of
`thm:continuation` uses — clause `sol` (classical solution with regularity
package on every `[0,T)`, `T < Tstar`) and clause `blowup` (the `H¹`
blow-up alternative at finite `Tstar`) — so that
`NavierFormal.Conditional` can feed a `localTheory` branch to this axiom
directly.  The conclusion is the pointwise unboundedness form
`∀ M, ∃ t < Tstar, ‖u(t)‖₃ > M`, equivalent for an extended-real quantity to
`⨆_{0<t<Tstar} ‖u(t)‖₃ = ⊤` (the manuscript's `sup_{0<t<T_*}‖u(t)‖_{L^3}
= ∞`); the pointwise form is used because it is exactly what discharges the
contradiction against `CriticalBound` in `Conditional.lean`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace NavierFormal.Literature

/-- **Literature axiom** (Escauriaza–Seregin–Šverák, *Russian Math. Surveys*
58 (2003), Theorem 1.3, combined with the manuscript-owned bridges
`lem:leray-hopf`, `lem:l3-to-l5`, `lem:serrin-enstrophy`): for a branch
`(Tstar, u, p)` satisfying the solution/regularity clause `hsol` and the
`H¹` blow-up clause `hblowup` of `localTheory`, if `Tstar` is finite then
`‖u(t)‖₃` is unbounded as `t` ranges over `(0,Tstar)` — the manuscript's
`thm:continuation`, `sup_{0<t<T_*}‖u(t)‖_{L^3(\R^3)} = ∞`.  See the module
docstring for the exact fidelity discussion, in particular that this axiom
is coarser than Theorem 1.3 alone: it also packages three manuscript-owned
bridges (`lem:leray-hopf`, `lem:l3-to-l5`, `lem:serrin-enstrophy`). -/
axiom endpointContinuation (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzDivFree)
    (Tstar : ℝ≥0∞) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ)
    (hsol : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tstar →
      IsClassicalSolution ν (⇑u₀) T u p ∧ RegularityPackage T u p)
    (hblowup : Tstar < ⊤ → ∀ M : ℝ, ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < Tstar ∧
      ENNReal.ofReal M <
        eLpNorm (u t) 2 volume + eLpNorm (iteratedFDeriv ℝ 1 (u t)) 2 volume)
    (hfin : Tstar < ⊤) (M : ℝ) :
    ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < Tstar ∧
      ENNReal.ofReal M < eLpNorm (u t) 3 volume

end NavierFormal.Literature
