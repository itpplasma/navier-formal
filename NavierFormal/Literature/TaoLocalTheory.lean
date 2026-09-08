import NavierFormal.ClassBridges
import NavierFormal.Energy

/-!
# Literature axiom: Tao's local theory, split from the manuscript's bridge (FC1)

This module states, as a single Lean `axiom`, **only** the content that the manuscript
attributes to Tao, "Localisation and compactness properties of the Navier–Stokes global
regularity problem", *Anal. PDE* 6 (2013), Theorem 5.4, together with Corollaries 4.3 and
5.8, via the manuscript's `prop:localtheory` (`../navier-paper/main.tex`, `\label{prop:localtheory}`
at line 1195) and the regularity package `R` recorded there after `premise:local`.  It is the
`taosplit` lane's pure literature half of the residual queue item FC1: the old coarse axiom
`NavierFormal.Literature.localTheory` (`NavierFormal/Literature/LocalTheory.lean`, not edited by
this lane) additionally folds in two results the manuscript proves for itself —
`lem:global-smooth` (joint smoothness up to `t = 0` on the *closed* half-space, the equations at
every `t ≥ 0`, when `T_* = ∞`) and the boundedness half of `prop:energy` (a finite energy bound)
— which `NavierFormal/LocalTheoryBridge.lean` now *proves* as theorems from this axiom instead
of assuming them.

**Source record.** Tao (2013), Theorem 5.4 and Corollaries 4.3, 5.8, via `prop:localtheory`
clauses (i)–(vi) (`main.tex` lines 1195–1234) and the regularity package `R`
(`docs/literature-assumptions.yaml`, `tao-2013-theorem-5-4`); Phase II disposal class F
(standard PDE local theory, currently absent from Mathlib), as in the old axiom.

## Clause-by-clause provenance

Reusing the encoding of `NavierFormal.Literature.localTheory` (`Tstar : ℝ≥0∞`, compared to real
times via `ENNReal.ofReal`), this axiom asserts:

* `pos` : `0 < Tstar` — `prop:localtheory`, preamble, `T_* ∈ (0,∞]`.
* For every finite horizon `0 < T < T_*` (all of the following are `prop:localtheory`(iii)'s
  regularity package `R`, together with (i)/(iv) restricted to `[0,T)`, and are packaged
  together here exactly as clause `sol` of the old axiom packaged `IsClassicalSolution ∧
  RegularityPackage`):
  * `hsol` : `IsClassicalSolution ν u₀ T u p` (existence, (i)) and `RegularityPackage T u p`
    (the `H^k` half of `R`).
  * `hbd` : `BoundedDerivatives T u p` (the pointwise-boundedness half of `R`, `prop:localtheory`
    (iii), "all derivatives … are bounded on `[0,T]×ℝ³`" — the clause
    `NavierFormal.ClassBridges.BoundedDerivatives` already isolates from `RegularityPackage`).
  * `hsmooth_bdry` : joint smoothness of `u`, `p` up to `t = 0` on the *half-open* slab
    `Ico 0 T ×ˢ ℝ³` — Tao's own class is `C^j([0,T];H^k)` for `j,k`, i.e. joint smoothness with
    all one-sided derivatives existing and continuous *up to and including* `t = 0`
    (`def:nu-mild`'s "almost smooth" clause, "smooth on `(0,T]×ℝ³`" after the `ν`-rescaling
    convention that also reaches `t=0` through Corollary 5.8/Theorem 5.4's Duhamel
    representation).  `IsClassicalSolution.smooth_u`/`smooth_p` only assert this on the *open*
    slab `Ioo 0 T`, so this clause is genuinely extra content, legitimately Tao's (it is *not*
    the manuscript's `lem:global-smooth`, which needs the *closed half-space* `[0,∞)`, a
    statement about *all* `T < T_*` simultaneously that only the manuscript's own gluing
    argument, `LocalTheoryBridge.lean`, can produce).
  * `heqn0` : the momentum equation and incompressibility *at* `t = 0`, with `timeDeriv` (the
    one-sided derivative), matching Tao's equation holding on the closed-at-0 class of
    `hsmooth_bdry`.  (Restated once, not per-`T`, since it is a single fact about `t = 0`.)
  * `hL2deriv` : for every interior time `σ`, `u` is `L²`-differentiable at `σ` on `Ioo 0 T`
    with derivative `timeDeriv u σ`, and that derivative lies in `L²` — Tao's `u ∈
    C¹([0,T];L²)`, the exact input `NavierFormal.EnergyIdentity.EnergyHypotheses.hasL2Deriv`/
    `.mem_L2_timeDeriv` need and `RegularityPackage`/`BoundedDerivatives` do not supply (those
    are `H^k`/pointwise bounds, not differentiability of the `L²`-valued curve).
  * `hdiss_cont` : `τ ↦ ∫‖∇u(τ)‖²` is continuous on `Ico 0 T` — Tao's `u ∈ C([0,T];H¹)`
    (the norm-continuity consequence of `C^0([0,T];H^k)` at `k=1`), the additional Tao-type
    clause flagged as possibly necessary by the lane brief: `NavierFormal.EnergyIdentity.
    EnergyHypotheses.dissipation_intervalIntegrable` needs interval-integrability of the
    dissipation, and `LocalTheoryBridge.lean` derives it from this continuity together with a
    Schwartz-datum truncation (see that file's docstring) rather than from `RegularityPackage`
    alone, which only bounds `L²` norms, not their continuity in time.
* `hcont0` : `L²`-continuity of `u` at the initial time,
  `∫⁻‖u(t)-u₀‖ₑ² → 0` as `t ↓ 0` — Tao's `u ∈ C([0,T];H^k)` at `k = 0`, `t = 0`, phrased in
  `ℝ≥0∞` so that it is not vacuous for a non-`L²` field.  Used by `LocalTheoryBridge.lean` to
  get the energy bound *at* `t = 0` (together with `energy_nonincreasing` on `(0,t)`) without
  reproving `prop:energy`'s Step 1 exactly at the boundary point.
* `hblowup` : the enstrophy blow-up alternative (v), verbatim as in the old axiom's `blowup`
  clause (weakened to pointwise unboundedness, for the same reason recorded there: it is all
  `Literature.endpointContinuation` consumes).
* `huniq` : uniqueness (ii), verbatim as in the old axiom's `uniq` clause (same weakenings:
  `T ≤ Tstar` in place of `T < Tstar`, pressure clause dropped).

Not included (this is the whole point of the split): the `Tstar = ⊤` global-smoothness/energy
clause `global` of the old axiom.  `NavierFormal.LocalTheoryBridge.localTheory_of_tao` derives it
as a theorem from `hsmooth_bdry`/`heqn0` (glued across all `T < T_*`) and from `hL2deriv`/
`hdiss_cont`/`hcont0` via `NavierFormal.EnergyIdentity.energy_identity`.
-/

open MeasureTheory
open scoped ENNReal ContDiff Gradient Laplacian

noncomputable section

namespace NavierFormal.Literature

/-- **Literature axiom** (Tao, *Anal. PDE* 6 (2013), Theorem 5.4 with Corollaries 4.3 and 5.8,
via the manuscript's `prop:localtheory` and the regularity package `R`): every viscosity
`ν > 0` and divergence-free Schwartz datum `u₀` has a maximal classical branch
`(Tstar, u, p)`, `Tstar ∈ (0,∞]`, solving `eq:NS` with the regularity package `R`
(`RegularityPackage` and `BoundedDerivatives`) on every `[0,T)`, `T < Tstar`, jointly smooth up
to `t = 0` there with the equations holding at `t = 0`, `L²`-differentiable in time with
continuous dissipation, and `L²`-continuous at the initial time; if `Tstar` is finite the
branch's `H¹`-type norm is unbounded as `t ↑ Tstar`; and the branch is the essentially unique
classical solution with the regularity package on any interval.  See the module docstring for
the exact clause-by-clause Tao provenance; unlike `NavierFormal.Literature.localTheory` this
axiom does **not** assert the `Tstar = ⊤` global-smoothness/energy clause, which is
manuscript-owned content proved from this axiom in `NavierFormal.LocalTheoryBridge`. -/
axiom taoLocalTheory (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzDivFree) :
    ∃ (Tstar : ℝ≥0∞) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
      0 < Tstar ∧
      (∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tstar →
        IsClassicalSolution ν (⇑u₀) T u p ∧
        RegularityPackage T u p ∧
        BoundedDerivatives T u p ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2)
          (Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set Space)) ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2)
          (Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set Space)) ∧
        (∀ σ ∈ Set.Ioo (0 : ℝ) T,
          Energy.HasL2DerivWithinAt u (timeDeriv u σ) (Set.Ioo (0 : ℝ) T) σ ∧
          MemLp (timeDeriv u σ) 2 volume) ∧
        ContinuousOn (fun τ => ∫ x, enstrophyDensity (u τ) x) (Set.Ico (0 : ℝ) T)) ∧
      (∀ x, timeDeriv u 0 x + convection (u 0) x + ∇ (p 0) x = ν • Δ (u 0) x) ∧
      (∀ x, divergence (u 0) x = 0) ∧
      Filter.Tendsto (fun t => ∫⁻ x, ‖u t x - (⇑u₀ : Space → Space) x‖ₑ ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      (Tstar < ⊤ → ∀ M : ℝ, ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < Tstar ∧
        ENNReal.ofReal M <
          eLpNorm (u t) 2 volume + eLpNorm (iteratedFDeriv ℝ 1 (u t)) 2 volume) ∧
      (∀ (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ),
        IsClassicalSolution ν (⇑u₀) T v q → RegularityPackage T v q →
        ENNReal.ofReal T ≤ Tstar ∧ ∀ t x, 0 ≤ t → t < T → v t x = u t x)

end NavierFormal.Literature
