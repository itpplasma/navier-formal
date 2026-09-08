import NavierFormal.SolutionClass

/-!
# Literature axiom: `L³` control gives `L⁵` space–time integrability (ESS 2003, thm:ess)

This module states, as a single Lean `axiom`, the manuscript's Lemma `lem:l3-to-l5`
("`L³` control gives `L⁵` integrability") applied directly to the classical branch of
`NavierFormal.Literature.localTheory`: a uniform `L³` bound on `u` over a finite horizon
`(0,Tstar)` forces `∫₀^{Tstar}‖u(t)‖₅⁵dt < ∞`.

**Source record.** Escauriaza–Seregin–Šverák, "`L_{3,∞}`-solutions of Navier–Stokes
equations and backward uniqueness", *Russian Math. Surveys* 58 (2003), Theorem 1.3
(the manuscript's `thm:ess`, quoted verbatim there with the mixed-norm convention of
`rem:ess-norm`: the hypothesis is `v ∈ L_{3,∞}(Q_T) = L^∞_tL^3_x(Q_T)`, *not* the weak
Lorentz space `L^{3,∞}_x`), combined with the manuscript-owned Lemma
`lem:leray-hopf` (the `ν`-normalised classical branch, restricted to any finite
sub-interval, is a Leray–Hopf weak solution of the Cauchy problem in the sense of
`\cite{ESS2003}`) and the Tonelli/normalisation bookkeeping of the proof of
`lem:l3-to-l5` itself (`../navier-paper/main.tex`, ~4512–4534).

**This axiom is the pure-literature half of the coarse axiom
`NavierFormal.Literature.endpointContinuation`** (see `NavierFormal/Literature/Endpoint.lean`,
which this module does not edit): the module docstring there names three manuscript-owned
bridges folded into that axiom, `lem:leray-hopf`, `lem:l3-to-l5`, `lem:serrin-enstrophy`.
This axiom packages exactly the first two (`lem:leray-hopf` supplies the hypotheses of
`thm:ess`, and `lem:l3-to-l5` is the theorem itself specialised to the classical branch);
`lem:serrin-enstrophy` is proved separately in `NavierFormal/SerrinEnstrophy.lean` and is
*not* folded in here.  `NavierFormal/EndpointBridge.lean` recombines this axiom with the
proved Serrin bound into the old axiom's exact statement.

**Statement shape.**  `Tstar : ℝ` (not `ℝ≥0∞`) because `lem:l3-to-l5`'s hypothesis is
literally `T_* < ∞`; the caller who has a `ℝ≥0∞`-valued maximal time converts via
`ENNReal.toReal` once `Tstar < ⊤` is known (done in `EndpointBridge.lean`).  The solution
clause `hsol` reproduces `localTheory`'s clause `sol` verbatim (classical solution with
regularity package on every finite sub-horizon), which is exactly what
`lem:leray-hopf`'s proof of the Leray–Hopf identification uses (joint smoothness,
continuity up to the initial time, the momentum and incompressibility equations, and the
`H^k` regularity package `R` — see `lem:nu-normalisation`,
Lemma~\ref{lem:leray-hopf} Steps 0–6 of the manuscript).  The `L³` hypothesis `hbound` is
the manuscript's `sup_{0≤t<T_*}‖u(t)‖₃<∞`, written with `≤ ENNReal.ofReal M` (never
`.toReal`) so that the bound is not vacuously true for a state outside `L³`.  The
conclusion is `eq:l3-to-l5`'s `∫₀^{T_*}‖u(t)‖₅⁵dt<∞`, written as the extended-real Lebesgue
integral `∫⁻ t in Set.Ioo 0 Tstar, eLpNorm (u t) 5 volume ^ 5 < ⊤` (the Tonelli identification
`∫_{Q_{T_*}}|u|⁵ = ∫₀^{T_*}‖u(t)‖₅⁵dt` of the manuscript's proof, using continuity of `u` on
`ℝ³×[0,T_*)`, is absorbed into the choice of writing the conclusion directly as a
time-integral rather than a space–time one). -/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace NavierFormal.Literature

/-- **Literature axiom** (Escauriaza–Seregin–Šverák, *Russian Math. Surveys* 58 (2003),
Theorem 1.3, combined with the manuscript-owned Lemma `lem:leray-hopf`): for a classical
branch `(u,p)` out of `(ν,u₀)` on every finite sub-horizon of `(0,Tstar)` with `Tstar > 0`
finite, a uniform `L³` bound on `u(t)` for `t ∈ (0,Tstar)` forces
`∫₀^{Tstar}‖u(t)‖₅⁵dt < ∞`.  This is the manuscript's Lemma `lem:l3-to-l5`
(`../navier-paper/main.tex`, ~4512), whose proof invokes Lemma `lem:leray-hopf`
(the normalised branch is a Leray–Hopf weak solution) to verify the hypotheses of
Theorem `thm:ess` (`ESS2003`, Theorem 1.3) and then applies that theorem.  See the module
docstring for the exact fidelity discussion, in particular that this axiom is the
pure-literature-plus-`lem:leray-hopf` half of the old coarse axiom
`NavierFormal.Literature.endpointContinuation`; `lem:serrin-enstrophy` is proved
separately and is not folded in here. -/
axiom essL3ToL5 (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzDivFree) (Tstar : ℝ)
    (hTstar : 0 < Tstar) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ)
    (hsol : ∀ T : ℝ, 0 < T → T < Tstar →
      IsClassicalSolution ν (⇑u₀) T u p ∧ RegularityPackage T u p)
    (hbound : ∃ M : ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) Tstar, eLpNorm (u t) 3 volume ≤ ENNReal.ofReal M) :
    ∫⁻ t in Set.Ioo (0 : ℝ) Tstar, eLpNorm (u t) 5 volume ^ (5 : ℕ) < ⊤

end NavierFormal.Literature
