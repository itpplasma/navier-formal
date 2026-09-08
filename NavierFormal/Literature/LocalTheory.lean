import NavierFormal.SolutionClass

/-!
# Literature axiom: the local classical branch (manuscript `prop:localtheory`)

This module states, as a single Lean `axiom`, the manuscript's local theory
for the unforced Navier–Stokes system: existence of a unique maximal
classical branch out of every divergence-free Schwartz datum, together with
its regularity, its blow-up alternative, and (when the branch is global) its
smoothness up to `t = 0` and its energy bound.

**Source record.** Tao, "Localisation and compactness properties of the
Navier–Stokes global regularity problem", *Anal. PDE* 6 (2013), Theorem 5.4,
together with Corollaries 4.3 and 5.8, via the manuscript's
`prop:localtheory` (existence, uniqueness, regularity, blow-up alternative)
and `lem:nu-scaling` (the viscosity normalisation used to reduce
`prop:localtheory` to Tao's `ν = 1` statement).  This is a manuscript-owned
bridge from Tao's theorem to the class `IsClassicalSolution` of
`NavierFormal.SolutionClass`, not a verbatim transcription of Tao's
statement, because Tao's theorem is phrased for `H¹` mild solutions and the
Schwartz/pointwise reduction (`prop:localtheory` Steps 5–9) is the
manuscript's own work.  Phase I axiom (`docs/literature-assumptions.yaml`,
`tao-2013-theorem-5-4`); Phase II disposal class F (standard PDE local
theory, currently absent from Mathlib).

**Encoding of `T_*`.**  The maximal time `T_* ∈ (0,∞]` of the manuscript is
`Tstar : ℝ≥0∞`, compared against real times `T` via `ENNReal.ofReal T`
(monotone for `T ≥ 0` and insensitive to sign, so no separate positivity
side-condition is needed at comparison sites).  `Tstar = ⊤` is the
manuscript's `T_* = ∞`.

**What the axiom packages, and how it deviates from `prop:localtheory`.**

* Clause `pos`: `0 < Tstar`, i.e. `T_* ∈ (0,∞]` (`prop:localtheory`,
  preamble).
* Clause `sol`: for every `0 < T` with `T < T_*`, `(u,p)` is a classical
  solution *and* carries the regularity package `R` on `[0,T)`
  (`prop:localtheory`\,(i) existence, on the class `IsClassicalSolution` /
  `RegularityPackage` rather than Tao's `H¹` mild-solution class; the
  identification of the two classes is exactly the content of Tao's theorem
  applied through the manuscript's bridge, so it is folded into this
  axiom rather than re-derived).  Maximality (`T_*` is the *supremum* of
  existence times, the second half of (i)) is not separately asserted: it
  is not used anywhere downstream, and asserting it would require comparing
  against Tao's mild-solution class, which this module does not introduce.
* Clause `blowup`: the enstrophy blow-up alternative (v), `T_* < ∞ ⇒
  \lim_{t\uparrow T_*}\|u(t)\|_{H^1} = ∞`, encoded as `H¹ := L² of u(t)`
  plus `L²` of the first derivative (matching the norm bookkeeping of
  `RegularityPackage`), and the limit is weakened to unboundedness: "for
  every `M` there is `t < T_*` with `H¹`-quantity `> M`".  This is
  implied by, and strictly weaker than, the manuscript's genuine limit
  statement; the weaker form is all `Literature.endpointContinuation`
  needs downstream, and it is what its own proof (Theorem
  `thm:continuation`) actually consumes ("contradicts (R4)"), so recording
  the stronger limit here would be recording unused content.
* Clause `global`: when `T_* = ∞`, `(u,p)` satisfies exactly the
  post-datum conjuncts of `NavierFormal.ClayAlternativeA`: joint smoothness
  on the *closed* half-space `[0,∞) × ℝ³` (manuscript `lem:global-smooth`,
  which is strictly more than smoothness on every open slab `(0,T) × ℝ³`:
  it is smoothness up to and including the initial time, and does not
  follow from clause `sol` alone inside this development), the momentum
  equation and incompressibility *at every* `t ≥ 0` including `t = 0`
  (`lem:global-smooth`'s own conclusion states the equations "pointwise on
  `ℝ³×[0,∞)`"; this is strictly more than clause `sol` gives, because
  `IsClassicalSolution.momentum`/`.incompressible` are asserted only on the
  *open* interval `0 < t < T`, by the design of `NavierFormal.SolutionClass`
  — a boundary gap belonging to that module, not to this axiom), and the
  bounded-energy consequence of `prop:energy`, `sup_{t≥0}\|u(t)\|_2^2 < ∞`
  (in fact `≤ \|u_0\|_2^2`, but only finiteness of a single bound is
  recorded, since that is exactly the shape `ClayAlternativeA` asks for).
  `prop:energy` itself has a *proved* Lean statement in `NavierFormal.Energy`
  (`kineticEnergy_le` and neighbours), but only under an explicit `L²`
  membership and dissipation-integrability hypothesis package that
  `IsClassicalSolution`/`RegularityPackage` do not, by design (`A5`/`A7` in
  `docs/paper-lean-specification.md`), expose without a further bridge;
  supplying that bridge is exactly the kind of manuscript-owned derivation
  this lane is instructed not to undertake, so the energy bound is folded
  into this literature axiom instead, flagged here for Phase II.  The
  initial datum `u(0) = u₀` *is* recoverable from clause `sol` (any
  `IsClassicalSolution` gives it), and is assembled that way in
  `NavierFormal.Literature.clayAlternativeA_of_Tstar_top` below, so it is
  not restated in this clause.
* Clause `uniq`: uniqueness (ii).  The manuscript states this for `T ≤ ∞`
  with no relation to `T_*` assumed and concludes `T < T_*`; here the
  conclusion is weakened to `T ≤ T_*` (a classical solution could a priori
  coincide with the maximal branch exactly at `T = T_*` inside this
  half-open-interval bookkeeping, whereas the manuscript's closed-interval
  `[0,T]` convention forces strictness) and the pressure clause of (ii) is
  dropped (`ũ = v` a.e./everywhere is retained; `p̃ - p` constant is not
  formalized, since nothing downstream uses it).  This clause is not used
  by `NavierFormal.Conditional`; it is included only for fidelity to
  `prop:localtheory`.
-/

open MeasureTheory
open scoped ENNReal ContDiff Gradient Laplacian

noncomputable section

namespace NavierFormal.Literature

/-- **Literature axiom** (Tao, *Anal. PDE* 6 (2013), Theorem 5.4 with
Corollaries 4.3 and 5.8, via the manuscript's `prop:localtheory` and
`lem:nu-scaling`): every viscosity `ν > 0` and divergence-free Schwartz
datum `u₀` has a maximal classical branch `(Tstar, u, p)`, `Tstar ∈ (0,∞]`,
solving `eq:NS` with the regularity package `R` on every `[0,T)`,
`T < Tstar`; if `Tstar` is finite the branch's `H¹`-type norm is unbounded
as `t ↑ Tstar` (the blow-up alternative `prop:localtheory`(v)); if
`Tstar = ∞` the branch is jointly smooth up to `t = 0` on the closed
half-space and has bounded energy (`lem:global-smooth`, `prop:energy`); and
the branch is the essentially unique classical solution with the
regularity package on any interval (`prop:localtheory`(ii)).  See the
module docstring for the exact clause-by-clause fidelity discussion. -/
axiom localTheory (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzDivFree) :
    ∃ (Tstar : ℝ≥0∞) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
      0 < Tstar ∧
      (∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tstar →
        IsClassicalSolution ν (⇑u₀) T u p ∧ RegularityPackage T u p) ∧
      (Tstar < ⊤ → ∀ M : ℝ, ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < Tstar ∧
        ENNReal.ofReal M <
          eLpNorm (u t) 2 volume + eLpNorm (iteratedFDeriv ℝ 1 (u t)) 2 volume) ∧
      (Tstar = ⊤ →
        ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2)
          (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2)
          (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ∧
        (∀ t x, 0 ≤ t →
          timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x) ∧
        (∀ t x, 0 ≤ t → divergence (u t) x = 0) ∧
        ∃ C : ℝ, ∀ t, 0 ≤ t → ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ENNReal.ofReal C) ∧
      (∀ (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ),
        IsClassicalSolution ν (⇑u₀) T v q → RegularityPackage T v q →
        ENNReal.ofReal T ≤ Tstar ∧ ∀ t x, 0 ≤ t → t < T → v t x = u t x)

/-- Convenience consequence of `localTheory`: at every finite `T < Tstar`
(including `T ≤ 0`, vacuously) the branch is a classical solution with the
regularity package.  Restates clause `sol` with the hypotheses split so it
composes directly with `IsClassicalSolution.mono`. -/
theorem isClassicalSolution_of_lt {ν : ℝ} (_hν : 0 < ν) {u₀ : SchwartzDivFree}
    {Tstar : ℝ≥0∞} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hsol : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tstar →
      IsClassicalSolution ν (⇑u₀) T u p ∧ RegularityPackage T u p)
    {T : ℝ} (hT0 : 0 < T) (hTlt : ENNReal.ofReal T < Tstar) :
    IsClassicalSolution ν (⇑u₀) T u p :=
  (hsol T hT0 hTlt).1

/-- **Assembly lemma.**  When the maximal branch of `localTheory` is global
(`Tstar = ⊤`), its global-smoothness/energy clause `global` together with
clause `sol` (applied at every finite time, for the equations,
incompressibility, and the initial datum) assemble exactly into
`NavierFormal.ClayAlternativeA`.  This is the manuscript's
`lem:global-smooth` plus `prop:energy`, repackaged; it is the bridge used by
`NavierFormal.Conditional.conditional_clay_A`. -/
theorem clayAlternativeA_of_Tstar_top {ν : ℝ} (_hν : 0 < ν) {u₀ : SchwartzDivFree}
    {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hsol : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < (⊤ : ℝ≥0∞) →
      IsClassicalSolution ν (⇑u₀) T u p ∧ RegularityPackage T u p)
    (hglob :
      ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2)
        (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2)
        (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ∧
      (∀ t x, 0 ≤ t →
        timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x) ∧
      (∀ t x, 0 ≤ t → divergence (u t) x = 0) ∧
      ∃ C : ℝ, ∀ t, 0 ≤ t → ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ENNReal.ofReal C) :
    ClayAlternativeA ν u₀ := by
  obtain ⟨hsu, hsp, hmom, hdiv, C, hC⟩ := hglob
  have h1 : IsClassicalSolution ν (⇑u₀) 1 u p :=
    (hsol 1 one_pos (by simp)).1
  exact ⟨u, p, hsu, hsp, h1.initial, hmom, hdiv, C, hC⟩

end NavierFormal.Literature
