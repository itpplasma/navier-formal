/-
Copyright 2026 The Formal Conjectures Authors.

This file has been modified from its original form in the Formal Conjectures
project.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import NavierFormal.Basic
import NavierFormal.Calculus
import NavierFormal.SolutionClass
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The community Clay-problem reference statement, and its bridge to `NavierFormal.ClayAlternativeA`

Community reference copied and specialised from:
https://github.com/google-deepmind/formal-conjectures/blob/8bf45ed70d48b2b2a501de9c00b26bfa38c573ee/FormalConjectures/Millenium/NavierStokes.lean
(Apache-2.0), the definitions OpenAI's Lean certificate uses for alternatives (C)/(D)
(`/home/ert/proj/openai-NavierStokesAndEuler/ComparatorChallenges/NavierStokes.lean`).

This is task **FC0** (statement alignment): it does **not** import the reference file, it
re-states, verbatim in mathematical content, exactly the definitions needed for alternative
(A) on `ℝ³`, specialised to `n = 3` (i.e. to `NavierFormal.Space`), and proves that this
project's `NavierFormal.ClayAlternativeA` / `ClayAlternativeA_all`
(`NavierFormal/SolutionClass.lean`) is the same mathematical statement as the community's
`∃ v p, NavierStokesExistenceAndSmoothnessRn ν u₀ (f := 0) v p`.

## Variable conventions (kept from the reference, only the ambient space is fixed)

The reference writes the velocity `v : Space → ℝ → Space` and pressure `p : Space → ℝ → ℝ`
curried **position first**, `v x t`, `p x t`; this project's solution class curries
**time first**, `u : ℝ → Space → Space`, `u t x`.  The bridge theorems below convert between
the two by `v x t := u t x`, an operation which is `rfl` in both directions (function
extensionality/eta), so the existential quantifiers over solutions transfer without loss.

## Main declarations

* `NavierFormal.ClayReference.divergence`, `divergence_eq` — the reference's divergence
  (trace of the Fréchet derivative) equals `NavierFormal.divergence` (sum of `⟪eᵢ, ∂ᵢv⟫`)
  pointwise.
* `NavierFormal.ClayReference.InitialVelocityCondition`,
  `InitialVelocityConditionDecay`, `ForceCondition`, `ForceConditionDecay`,
  `NavierStokesExistenceAndSmoothness`, `NavierStokesExistenceAndSmoothnessRn` — the
  reference structures, specialised to `Space`.
* `NavierFormal.ClayReference.navierStokesExistenceAndSmoothness_iff` — the bridge for the
  solution structure without the energy clause.
* `NavierFormal.ClayReference.navierStokesExistenceAndSmoothnessRn_iff` — the bridge
  including the energy clause.
* `NavierFormal.ClayReference.clayAlternativeA_iff` — `NavierFormal.ClayAlternativeA ν u₀ ↔
  ∃ v p, NavierStokesExistenceAndSmoothnessRn ν (⇑u₀) (f := 0) v p`, for `u₀` a divergence-free
  Schwartz datum.
* `NavierFormal.ClayReference.clayAlternativeA_all_implies_reference` — the manuscript's target
  `ClayAlternativeA_all` implies the community reference statement (A), for every Schwartz
  divergence-free datum, given the datum's polynomial-decay clause as an explicit hypothesis
  (proved separately in lane `SchwartzDecay`, not here).

Nothing here is a theorem about the Millennium problem; no existence is claimed for any
particular `(ν, u₀)`.
-/

open MeasureTheory
open scoped ENNReal ContDiff Gradient Laplacian

noncomputable section

namespace NavierFormal.ClayReference

/-! ## The reference definitions, specialised to `Space = ℝ³` -/

/-- The reference's divergence `∇·v` of a vector field, computed as the trace of the Fréchet
derivative (rather than as `∑ᵢ ⟪eᵢ, ∂ᵢv⟫`, `NavierFormal.divergence`'s definition).  Equal to
`NavierFormal.divergence` pointwise by `divergence_eq`.  Junk value `0` where `v` is not
differentiable, as for `fderiv`. -/
def divergence (v : Space → Space) (x : Space) : ℝ := (fderiv ℝ v x).trace ℝ Space

/-- The reference's divergence (trace of the Fréchet derivative) agrees pointwise with
`NavierFormal.divergence` (`∑ᵢ ⟪eᵢ, ∂ᵢv⟫`, `NavierFormal/Calculus.lean`): both are the trace of
the same linear map, computed against the same orthonormal basis `NavierFormal.e`. -/
theorem divergence_eq (v : Space → Space) (x : Space) :
    divergence v x = NavierFormal.divergence v x := by
  classical
  rw [ClayReference.divergence, NavierFormal.divergence,
    LinearMap.trace_eq_sum_inner (fderiv ℝ v x : Space →ₗ[ℝ] Space)
      (EuclideanSpace.basisFun (Fin 3) ℝ)]
  exact Fintype.sum_congr _ _ (fun i => by rw [← NavierFormal.e_eq_basisFun]; rfl)

/-- The reference's basic condition on an initial velocity field: divergence-free and smooth.
Specialised to `Space = ℝ³`; the reference states this for arbitrary dimension `n`. -/
structure InitialVelocityCondition (u₀ : Space → Space) : Prop where
  /-- Incompressibility, equation (2) of the reference. -/
  div_free : ∀ x, divergence u₀ x = 0
  /-- Smoothness of the datum. -/
  smooth : ContDiff ℝ ∞ u₀

/-- The reference's initial velocity condition on all of `ℝ³` (condition 4 of Fefferman's
paper): in addition to `InitialVelocityCondition`, every derivative decays faster than any
polynomial. -/
structure InitialVelocityConditionDecay (u₀ : Space → Space) : Prop extends
    InitialVelocityCondition u₀ where
  /-- Polynomial decay of every derivative, condition 4. -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/-- The reference's basic smoothness condition on the external forcing term: smooth on
`ℝ³ × [0,∞)`. -/
structure ForceCondition (f : Space → ℝ → Space) : Prop where
  /-- Joint smoothness of the force on the closed half-space. -/
  smooth : ContDiffOn ℝ ∞ (Function.uncurry f) (Set.univ ×ˢ Set.Ici (0 : ℝ))

/-- The reference's force condition on all of `ℝ³` (condition 5): in addition to
`ForceCondition`, every derivative decays faster than any polynomial in space and time. -/
structure ForceConditionDecay (f : Space → ℝ → Space) : Prop extends ForceCondition f where
  /-- Polynomial decay of every space-time derivative, condition 5. -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (Function.uncurry f) (Set.univ ×ˢ Set.Ici (0 : ℝ)) (x, t)‖ ≤
      C / (1 + ‖x‖ + t) ^ K

/-- The reference's solution structure: `(v,p)` solves the Navier–Stokes system with
viscosity `nu`, datum `u₀`, and force `f`, jointly smooth on `ℝ³ × [0,∞)` (equations 1, 2, 3,
6, 11 of the reference).  Position-first curry `v x t`, `p x t`, matching the reference. -/
structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : Space → Space) (f : Space → ℝ → Space)
    (v : Space → ℝ → Space) (p : Space → ℝ → ℝ) : Prop where
  /-- The Navier–Stokes equation (equation 1):
  `∂v/∂t + (v·∇)v = νΔv - ∇p + f`. -/
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  /-- Incompressibility (equation 2). -/
  div_free : ∀ x, ∀ t ≥ 0, divergence (v · t) x = 0
  /-- The initial condition (equation 3). -/
  initial_condition : ∀ x, v x 0 = u₀ x
  /-- Joint smoothness of the velocity on `ℝ³ × [0,∞)` (conditions 6, 11). -/
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici (0 : ℝ))
  /-- Joint smoothness of the pressure on `ℝ³ × [0,∞)` (conditions 6, 11). -/
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici (0 : ℝ))

/-- The reference's solution structure on all of `ℝ³` (condition 7): in addition to
`NavierStokesExistenceAndSmoothness`, the velocity is square-integrable at every time with a
time-uniform bound on the Bochner integral `∫‖v(·,t)‖²`.  This is the community's shape of
alternative (A). -/
structure NavierStokesExistenceAndSmoothnessRn
    (nu : ℝ) (u₀ : Space → Space) (f : Space → ℝ → Space)
    (v : Space → ℝ → Space) (p : Space → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  /-- The velocity is square-integrable at every time `t ≥ 0`. -/
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  /-- The kinetic energy is uniformly bounded for all time, as a real Bochner integral. -/
  globally_bounded_energy : ∃ E, ∀ t ≥ 0, (∫ x : Space, ‖v x t‖ ^ 2) < E

/-! ## The curry-order bridge -/

/-- Precomposing a jointly-smooth field with `Prod.swap` swaps which factor is required to lie
in `Set.Ici 0`: this is exactly the translation between this project's time-first joint
smoothness `ContDiffOn … (Set.Ici 0 ×ˢ Set.univ)` (`NavierFormal.ClayAlternativeA`) and the
reference's position-first joint smoothness `ContDiffOn … (Set.univ ×ˢ Set.Ici 0)`
(`NavierStokesExistenceAndSmoothness.velocity_smooth` / `.pressure_smooth`, unfolding
`Function.uncurry`). -/
theorem contDiffOn_prod_swap_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : ℝ → Space → F) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ↔
    ContDiffOn ℝ ∞ (fun q : Space × ℝ => U q.2 q.1) ((Set.univ : Set Space) ×ˢ Set.Ici (0 : ℝ)) := by
  have hswap1 : ContDiff ℝ ∞ (Prod.swap : Space × ℝ → ℝ × Space) :=
    contDiff_snd.prodMk contDiff_fst
  have hswap2 : ContDiff ℝ ∞ (Prod.swap : ℝ × Space → Space × ℝ) :=
    contDiff_snd.prodMk contDiff_fst
  constructor
  · intro h
    have hmaps : Set.MapsTo (Prod.swap : Space × ℝ → ℝ × Space)
        ((Set.univ : Set Space) ×ˢ Set.Ici (0 : ℝ)) (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) :=
      fun q hq => ⟨hq.2, Set.mem_univ _⟩
    exact h.comp hswap1.contDiffOn hmaps
  · intro h
    have hmaps : Set.MapsTo (Prod.swap : ℝ × Space → Space × ℝ)
        (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ((Set.univ : Set Space) ×ˢ Set.Ici (0 : ℝ)) :=
      fun q hq => ⟨Set.mem_univ _, hq.1⟩
    exact h.comp hswap2.contDiffOn hmaps

/-- Bridge (statement alignment, task FC0): for one curried triple `(u,p)` of this project's
convention, the reference's `NavierStokesExistenceAndSmoothness` for the unforced system
(`f = 0`) and the position-first pair `v x t := u t x`, `p x t := p t x`, holds iff the five
manuscript conditions of `NavierFormal.ClayAlternativeA` (everything but the energy bound) hold
for `(u,p)`.

Fidelity: the momentum equation matches exactly, term for term, once `f = 0` is substituted and
the pressure-gradient term is moved across the equality (`eq_sub_iff_add_eq`); no sign or
normalization discrepancy exists between the two conventions. -/
theorem navierStokesExistenceAndSmoothness_iff (ν : ℝ) (u₀ : Space → Space)
    (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) :
    NavierStokesExistenceAndSmoothness ν u₀ (0 : Space → ℝ → Space)
      (fun x t => u t x) (fun x t => p t x) ↔
      ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2)
        (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2)
        (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ∧
      (∀ x, u 0 x = u₀ x) ∧
      (∀ t x, 0 ≤ t →
        timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x) ∧
      (∀ t x, 0 ≤ t → NavierFormal.divergence (u t) x = 0) := by
  constructor
  · rintro ⟨hns, hdiv, hinit, hvel, hpres⟩
    refine ⟨(contDiffOn_prod_swap_iff u).2 hvel, (contDiffOn_prod_swap_iff p).2 hpres, hinit, ?_,
      ?_⟩
    · intro t x ht
      have h := hns x t ht
      simp only [Pi.zero_apply, add_zero] at h
      rw [eq_sub_iff_add_eq] at h
      exact h
    · intro t x ht
      have h := hdiv x t ht
      rwa [divergence_eq] at h
  · rintro ⟨hvel, hpres, hinit, hmom, hdiv⟩
    refine ⟨?_, ?_, hinit, (contDiffOn_prod_swap_iff u).1 hvel, (contDiffOn_prod_swap_iff p).1
      hpres⟩
    · intro x t ht
      have h := hmom t x ht
      simp only [Pi.zero_apply, add_zero]
      rw [eq_sub_iff_add_eq]
      exact h
    · intro x t ht
      rw [divergence_eq]
      exact hdiv t x ht

/-- Bridge for the energy clauses alone: given a family `u` continuous at every time `t ≥ 0`,
the manuscript's `L²` bound `∫⁻‖u(t)‖ₑ² ≤ ofReal C` uniform in `t` is equivalent to the
reference's pair `MemLp (‖u(t)‖) 2` for every `t` together with a uniform real Bochner-integral
bound `∫‖u(t)‖² < E`.

Fidelity: the manuscript states `≤` on an extended-real (`ℝ≥0∞`) quantity with no sign
constraint on `C`; the reference states `<` on a real Bochner integral.  Both directions hold
without any extra hypothesis: continuity gives `AEStronglyMeasurable`, which is exactly the
missing ingredient making `eLpNorm² = ∫⁻‖·‖ₑ²` finite iff `MemLp`, and
`ofReal_integral_eq_lintegral_ofReal` converts between the Bochner and Lebesgue integrals of the
(integrable, nonnegative) integrand `‖·‖²` in both directions; the strict/non-strict and
sign mismatches are absorbed by `max C 0 + 1` (forward) and by reusing `E` itself as the bound
constant (backward). -/
theorem energy_bound_iff (u : ℝ → Space → Space) (hcont : ∀ t, 0 ≤ t → Continuous (u t)) :
    (∃ C : ℝ, ∀ t, 0 ≤ t → ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ENNReal.ofReal C) ↔
    ((∀ t, 0 ≤ t → MemLp (fun x => ‖u t x‖) 2 volume) ∧
      ∃ E : ℝ, ∀ t, 0 ≤ t → ∫ x, ‖u t x‖ ^ 2 < E) := by
  constructor
  · rintro ⟨C, hC⟩
    have hstep : ∀ t, 0 ≤ t →
        MemLp (fun x => ‖u t x‖) 2 volume ∧ ∫ x, ‖u t x‖ ^ 2 ≤ max C 0 := by
      intro t ht
      have hb := hC t ht
      have hcontt := hcont t ht
      have hmeas : AEStronglyMeasurable (u t) volume := hcontt.aestronglyMeasurable
      have heLp : eLpNorm (u t) 2 volume < ⊤ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (two_ne_zero) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
        have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
        rw [h2]
        have hcast : ∀ x : Space, ‖u t x‖ₑ ^ (2 : ℝ) = ‖u t x‖ₑ ^ (2 : ℕ) := by
          intro x
          rw [← ENNReal.rpow_natCast (‖u t x‖ₑ) 2]
          norm_num
        simp_rw [hcast]
        calc (∫⁻ x, ‖u t x‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal C) ^ (1 / (2 : ℝ)) := by
              gcongr
          _ < ⊤ := by
              apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
              exact ENNReal.ofReal_ne_top
      have hmemLp : MemLp (u t) 2 volume := ⟨hmeas, heLp⟩
      refine ⟨hmemLp.norm, ?_⟩
      have hint : Integrable (fun x => ‖u t x‖ ^ (2 : ℝ)) volume := by
        have := hmemLp.integrable_norm_rpow (two_ne_zero) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        simpa using this
      have hint' : Integrable (fun x => ‖u t x‖ ^ (2 : ℕ)) volume := by
        have heq : (fun x => ‖u t x‖ ^ (2 : ℝ)) = (fun x => ‖u t x‖ ^ (2 : ℕ)) := by
          funext x; rw [← Real.rpow_natCast]; norm_num
        rwa [heq] at hint
      have hnn : 0 ≤ᵐ[volume] (fun x => ‖u t x‖ ^ (2 : ℕ)) := ae_of_all _ (fun x => by positivity)
      have key : ENNReal.ofReal (∫ x, ‖u t x‖ ^ (2 : ℕ)) =
          ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ (2 : ℕ)) :=
        ofReal_integral_eq_lintegral_ofReal hint' hnn
      have hofReal_eq : ∀ x : Space, ENNReal.ofReal (‖u t x‖ ^ (2 : ℕ)) = ‖u t x‖ₑ ^ (2 : ℕ) := by
        intro x
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      simp_rw [hofReal_eq] at key
      have hle : ENNReal.ofReal (∫ x, ‖u t x‖ ^ (2 : ℕ)) ≤ ENNReal.ofReal C := key ▸ hb
      have hle' : ENNReal.ofReal (∫ x, ‖u t x‖ ^ (2 : ℕ)) ≤ ENNReal.ofReal (max C 0) :=
        hle.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))
      exact (ENNReal.ofReal_le_ofReal_iff (le_max_right C 0)).1 hle'
    exact ⟨fun t ht => (hstep t ht).1, max C 0 + 1,
      fun t ht => lt_of_le_of_lt (hstep t ht).2 (lt_add_one _)⟩
  · rintro ⟨hmemLp, E, hE⟩
    refine ⟨E, fun t ht => ?_⟩
    have hmemLpt := hmemLp t ht
    have hEt := hE t ht
    have hint' : Integrable (fun x => ‖u t x‖ ^ (2 : ℕ)) volume := by
      have hint : Integrable (fun x => (‖u t x‖ : ℝ) ^ (2 : ℝ)) volume := by
        have := hmemLpt.integrable_norm_rpow (two_ne_zero) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        simpa using this
      have heq : (fun x => (‖u t x‖ : ℝ) ^ (2 : ℝ)) = (fun x => ‖u t x‖ ^ (2 : ℕ)) := by
        funext x; rw [← Real.rpow_natCast]; norm_num
      rwa [heq] at hint
    have hnn : 0 ≤ᵐ[volume] (fun x => ‖u t x‖ ^ (2 : ℕ)) := ae_of_all _ (fun x => by positivity)
    have key : ENNReal.ofReal (∫ x, ‖u t x‖ ^ (2 : ℕ)) =
        ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ (2 : ℕ)) :=
      ofReal_integral_eq_lintegral_ofReal hint' hnn
    have hofReal_eq : ∀ x : Space, ENNReal.ofReal (‖u t x‖ ^ (2 : ℕ)) = ‖u t x‖ₑ ^ (2 : ℕ) := by
      intro x
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [hofReal_eq] at key
    rw [← key]
    exact ENNReal.ofReal_le_ofReal hEt.le

/-- Bridge (statement alignment, task FC0), full `Rn` structure: adjoining the energy bridge
`energy_bound_iff` to `navierStokesExistenceAndSmoothness_iff` via the continuity that the
smoothness clause already supplies. -/
theorem navierStokesExistenceAndSmoothnessRn_iff (ν : ℝ) (u₀ : Space → Space)
    (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) :
    NavierStokesExistenceAndSmoothnessRn ν u₀ (0 : Space → ℝ → Space)
      (fun x t => u t x) (fun x t => p t x) ↔
      (ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2)
        (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2)
        (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) ∧
      (∀ x, u 0 x = u₀ x) ∧
      (∀ t x, 0 ≤ t →
        timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x) ∧
      (∀ t x, 0 ≤ t → NavierFormal.divergence (u t) x = 0)) ∧
      (∃ C : ℝ, ∀ t, 0 ≤ t → ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ENNReal.ofReal C) := by
  constructor
  · rintro ⟨hcore, hint, C, hC⟩
    refine ⟨(navierStokesExistenceAndSmoothness_iff ν u₀ u p).1 hcore, ?_⟩
    have hsmooth := ((navierStokesExistenceAndSmoothness_iff ν u₀ u p).1 hcore).1
    have hcont : ∀ t, 0 ≤ t → Continuous (u t) := fun t ht =>
      hsmooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨ht, trivial⟩)
    exact (energy_bound_iff u hcont).2 ⟨hint, C, hC⟩
  · rintro ⟨hcore, C, hC⟩
    have hstruct := (navierStokesExistenceAndSmoothness_iff ν u₀ u p).2 hcore
    have hsmooth := hcore.1
    have hcont : ∀ t, 0 ≤ t → Continuous (u t) := fun t ht =>
      hsmooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨ht, trivial⟩)
    obtain ⟨hint, hE⟩ := (energy_bound_iff u hcont).1 ⟨C, hC⟩
    exact ⟨hstruct, hint, hE⟩

/-! ## The full statement bridge -/

/-- The main statement-alignment theorem (task FC0(ii)): for one viscosity `ν` and one
divergence-free Schwartz datum `u₀`, `NavierFormal.ClayAlternativeA` is the reference's
alternative (A), `∃ v p, NavierStokesExistenceAndSmoothnessRn ν (⇑u₀) (f := 0) v p`.  The
existential quantifiers transfer along the curry-order reindexing `v x t := u t x`, `p x t :=
p t x`, which is definitional (function eta) in both directions, so no direction of the iff
needs an extra hypothesis. -/
theorem clayAlternativeA_iff (ν : ℝ) (u₀ : SchwartzDivFree) :
    ClayAlternativeA ν u₀ ↔
      ∃ v p, NavierStokesExistenceAndSmoothnessRn ν (⇑u₀) (f := (0 : Space → ℝ → Space)) v p := by
  constructor
  · rintro ⟨u, p, hu, hp, hinit, hmom, hdiv, C, hC⟩
    exact ⟨fun x t => u t x, fun x t => p t x,
      (navierStokesExistenceAndSmoothnessRn_iff ν (⇑u₀) u p).2 ⟨⟨hu, hp, hinit, hmom, hdiv⟩, C,
        hC⟩⟩
  · rintro ⟨v, p, hRn⟩
    have hveq : v = fun x t => (fun t x => v x t) t x := rfl
    have hpeq : p = fun x t => (fun t x => p x t) t x := rfl
    rw [hveq, hpeq] at hRn
    obtain ⟨⟨hu, hp, hinit, hmom, hdiv⟩, C, hC⟩ :=
      (navierStokesExistenceAndSmoothnessRn_iff ν (⇑u₀) (fun t x => v x t)
        (fun t x => p x t)).1 hRn
    exact ⟨fun t x => v x t, fun t x => p x t, hu, hp, hinit, hmom, hdiv, C, hC⟩

/-- Task FC0(iii): `NavierFormal.ClayAlternativeA_all` implies the community reference statement
(A) for every viscosity `ν > 0` and every divergence-free Schwartz datum `u₀`, given the
datum's decay clause `InitialVelocityConditionDecay` as an explicit hypothesis.

Deviation from the reference's `navier_stokes_existence_and_smoothness_R3`: that theorem takes
`hu₀ : InitialVelocityConditionDecay u₀` as a hypothesis but never uses it in its statement's
conclusion (only `u₀` itself, via `InitialVelocityCondition.smooth`/`.div_free`, appears through
`NavierStokesExistenceAndSmoothnessRn`).  The same is true here: `hdecay` is carried only to
match the reference's exact hypothesis shape.  Proving `hdecay` for a `SchwartzMap` (i.e. that a
Schwartz function satisfies the reference's polynomial-decay clause) is the separate lane
`SchwartzDecay`; it is *not* proved in this file. -/
theorem clayAlternativeA_all_implies_reference (h : ClayAlternativeA_all) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SchwartzDivFree) (_hdecay : InitialVelocityConditionDecay (⇑u₀)) :
    ∃ v p, NavierStokesExistenceAndSmoothnessRn ν (⇑u₀) (f := (0 : Space → ℝ → Space)) v p :=
  (clayAlternativeA_iff ν u₀).1 (h ν hν u₀)

end NavierFormal.ClayReference
