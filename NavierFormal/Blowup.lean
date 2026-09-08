import NavierFormal.Basic
import NavierFormal.Calculus
import NavierFormal.SolutionClass
import Mathlib.Analysis.Normed.MulAction
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Blow-up statement surface for the negative route (PLAN task FC7 / UE4)

This module is a **statement surface**, in the sense of
`itpplasma/navier:PLAN.md` §§1, 3, 4 (task `UE4`, "Terminal verification").  It
records, on top of `NavierFormal.SolutionClass`, the diagnostics and the exact
proposition an UNFORCED counterexample to global regularity would have to
satisfy, together with the elementary structural facts connecting it to
`NavierFormal.ClayAlternativeA_all`.  Its style mirrors OpenAI's
`NavierStokes/R3/ProblemStatement.lean` /
`ComparatorChallenges/Euler.lean` (`SpeedUnboundedAtOne`,
`UniformFiniteEnergy`, `velocityC1Norm`, `vorticityNorm`,
`exists_compact_smooth_euler_singularity`), rewritten in this development's
curried `u : ℝ → Space → Space` conventions and against
`NavierFormal.IsClassicalSolution` / `NavierFormal.ClayAlternativeA`.

**No counterexample is asserted or constructed here.** Every declaration below
is either a definition (a diagnostic predicate, or the proposition
`UnforcedCounterexample`/`…Some`/`…All`) or an elementary theorem connecting
such definitions to `ClayAlternativeA_all`, `IsClassicalSolution`, and
`IsGlobalSmoothSolution`. Nothing here proves that any solution is singular,
and nothing here proves or disproves `ClayAlternativeA_all`.

## Contents

* `SpeedUnboundedAt`, `L3UnboundedAt`, `EnstrophyUnboundedAt` — limsup-type
  blow-up diagnostics for a classical solution at a terminal time `T`.
* `UniformFiniteEnergyOn` — the energy clause of `ClayAlternativeA`, factored
  out and parametrized by an arbitrary time-set `I` (`ClayAlternativeA`'s own
  clause is `UniformFiniteEnergyOn (Set.Ici 0) u`, definitionally).
* `IsGlobalSmoothSolution` — the "there is a global smooth solution" predicate
  hiding inside `ClayAlternativeA`, exposed as its own definition so that
  `clayAlternativeA_iff` is `Iff.rfl`.
* `UnforcedCounterexample`, `UnforcedCounterexampleSome`,
  `UnforcedCounterexampleAll` — the PLAN §1 negative-resolution target: one
  nonzero real solenoidal Schwartz datum, finite energy, a classical solution
  singular (in the `SpeedUnboundedAt` sense) at a finite time `T`, for which no
  global smooth finite-energy solution exists.
* Elementary theorems: an `UnforcedCounterexample` refutes
  `ClayAlternativeA_all`; a global smooth solution restricts to a classical
  solution on every finite window and has uniformly finite energy on `Ici 0`;
  `SpeedUnboundedAt` is incompatible with a uniform bound; and the viscosity
  rescaling of `NavierFormal.IsClassicalSolution.nuNormalization` turns an
  `UnforcedCounterexample ν` into an `UnforcedCounterexample 1`.

Nothing in this file is a theorem about the Millennium problem.
-/

open MeasureTheory Set
open scoped ENNReal ContDiff Gradient Laplacian

noncomputable section

namespace NavierFormal

/-! ## Blow-up diagnostics for a classical solution -/

/-- Pointwise speed unbounded at `T`, in the limsup sense: for every bound `M`
and every `t₀ < T` there is a later time `t < T` and a point `x` where the
speed exceeds `M`. This is the diagnostic used in OpenAI's
`SpeedUnboundedAtOne` (`ComparatorChallenges/Euler.lean`), transcribed with a
free terminal time `T` and this development's curried `u : ℝ → Space → Space`.
No claim that any particular `u`, `T` satisfies it is made here. -/
def SpeedUnboundedAt (T : ℝ) (u : ℝ → Space → Space) : Prop :=
  ∀ M : ℝ, ∀ t₀ : ℝ, t₀ < T → ∃ t ∈ Ioo t₀ T, ∃ x : Space, M < ‖u t x‖

/-- The critical `L³` norm `eLpNorm (u t) 3 volume` unbounded on approach to
`T`, in the limsup sense: for every finite bound `M` there is a time `t < T`
at which the norm exceeds `M`. This is the manuscript's `hyp:critical`
diagnostic (`NavierFormal.CriticalBound`) read as a blow-up statement rather
than as a hypothesis. -/
def L3UnboundedAt (T : ℝ) (u : ℝ → Space → Space) : Prop :=
  ∀ M : ℝ≥0∞, M < ⊤ → ∃ t ∈ Ioo (0 : ℝ) T, M < eLpNorm (u t) 3 volume

/-- The enstrophy `eLpNorm (fderiv ℝ (u t)) 2 volume` unbounded on approach to
`T`, in the limsup sense: for every finite bound `M` there is a time `t < T`
at which it exceeds `M`. Encoding choice: `fderiv ℝ (u t)` valued in
`Space →L[ℝ] Space` with its operator norm, following Mathlib's `eLpNorm`;
this is not literally `NavierFormal.enstrophyDensity` (the Frobenius
convention of `NavierFormal.Calculus`), since `eLpNorm` needs a norm on the
codomain and Mathlib supplies the operator norm there, not the Frobenius one.
The two are comparable by `NavierFormal.opNorm_le_frobeniusNorm` /
`NavierFormal.frobeniusNorm_le_sqrt_three_mul`, so unboundedness in one sense
is equivalent to unboundedness in the other; that equivalence is not proved
here. -/
def EnstrophyUnboundedAt (T : ℝ) (u : ℝ → Space → Space) : Prop :=
  ∀ M : ℝ≥0∞, M < ⊤ → ∃ t ∈ Ioo (0 : ℝ) T, M < eLpNorm (fderiv ℝ (u t)) 2 volume

/-- Uniformly finite kinetic energy on a set of times `I`, matching the energy
clause of `NavierFormal.ClayAlternativeA` verbatim: `ClayAlternativeA`'s own
clause is `UniformFiniteEnergyOn (Set.Ici 0) u`, by `rfl` (see
`clayAlternativeA_iff` below). This is OpenAI's `UniformFiniteEnergy`
(`ComparatorChallenges/Euler.lean`), parametrized the same way by a set of
times, with the energy written as the `ℝ≥0∞`-valued Lebesgue integral of
`ClayAlternativeA`, not as a possibly-junk real integral. -/
def UniformFiniteEnergyOn (I : Set ℝ) (u : ℝ → Space → Space) : Prop :=
  ∃ C : ℝ, ∀ t ∈ I, ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ENNReal.ofReal C

/-- `UniformFiniteEnergyOn` restricts to any subset of times. -/
theorem UniformFiniteEnergyOn.mono {I J : Set ℝ} {u : ℝ → Space → Space}
    (h : UniformFiniteEnergyOn I u) (hJI : J ⊆ I) : UniformFiniteEnergyOn J u := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun t ht => hC t (hJI ht)⟩

/-! ## Global smooth solutions -/

/-- A global smooth finite-energy solution of the manuscript's `eq:NS` with
viscosity `ν` and datum `u₀`: smoothness on `Ici 0 ×ˢ univ`, the datum, the
momentum and incompressibility equations for `t ≥ 0`, and uniformly finite
energy on `Ici 0`. This is exactly the conjunction quantified over `u, p`
inside `NavierFormal.ClayAlternativeA`, so that
`ClayAlternativeA ν u₀ ↔ ∃ u p, IsGlobalSmoothSolution ν (⇑u₀) u p` holds by
`Iff.rfl` (`clayAlternativeA_iff`). No existence is asserted here; this is
purely a repackaging of `ClayAlternativeA`'s body as a two-argument
predicate. -/
def IsGlobalSmoothSolution (ν : ℝ) (u₀ : Space → Space) (u : ℝ → Space → Space)
    (p : ℝ → Space → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2) (Ici 0 ×ˢ (univ : Set Space)) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2) (Ici 0 ×ˢ (univ : Set Space)) ∧
  (∀ x, u 0 x = u₀ x) ∧
  (∀ t x, 0 ≤ t →
    timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x) ∧
  (∀ t x, 0 ≤ t → divergence (u t) x = 0) ∧
  UniformFiniteEnergyOn (Ici 0) u

/-- `ClayAlternativeA` is exactly the existence of an `IsGlobalSmoothSolution`.
The two sides are definitionally the same proposition: `ClayAlternativeA`'s
body is the six-way conjunction `IsGlobalSmoothSolution` was written to be, and
its last clause `∃ C, ∀ t, 0 ≤ t → …` is `UniformFiniteEnergyOn (Ici 0) u`
unfolded (`t ∈ Set.Ici 0` reduces to `0 ≤ t`). -/
theorem clayAlternativeA_iff (ν : ℝ) (u₀ : SchwartzDivFree) :
    ClayAlternativeA ν u₀ ↔ ∃ u p, IsGlobalSmoothSolution ν (⇑u₀) u p :=
  Iff.rfl

/-- A global smooth solution restricts to an `IsClassicalSolution` on every
finite window `[0,T)`, `T > 0`: the smoothness/continuity clauses restrict
along `Ioo 0 T ⊆ Ici 0` and `Ico 0 T ⊆ Ici 0`, and the momentum and
incompressibility equations at `0 < t < T` are literally the `0 ≤ t` clauses
of `IsGlobalSmoothSolution` specialized to `t`, since both use the same
`NavierFormal.timeDeriv` (`derivWithin … (Ici 0)`), so no appeal to
`timeDeriv_eq_deriv` is needed. -/
theorem IsGlobalSmoothSolution.restrict {ν : ℝ} {u₀ : Space → Space}
    {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsGlobalSmoothSolution ν u₀ u p) {T : ℝ} (hT : 0 < T) :
    IsClassicalSolution ν u₀ T u p where
  smooth_u := h.1.mono (Set.prod_mono (Ioo_subset_Ico_self.trans Ico_subset_Ici_self) le_rfl)
  smooth_p := h.2.1.mono (Set.prod_mono (Ioo_subset_Ico_self.trans Ico_subset_Ici_self) le_rfl)
  cont_u := h.1.continuousOn.mono (Set.prod_mono Ico_subset_Ici_self le_rfl)
  cont_p := h.2.1.continuousOn.mono (Set.prod_mono Ico_subset_Ici_self le_rfl)
  initial := h.2.2.1
  momentum := fun t x ht _ => h.2.2.2.1 t x ht.le
  incompressible := fun t x ht _ => h.2.2.2.2.1 t x ht.le

/-- A global smooth solution has uniformly finite energy on `Ici 0`; this is
literally the last clause of `IsGlobalSmoothSolution`, extracted as its own
lemma for use alongside `IsGlobalSmoothSolution.restrict`. -/
theorem IsGlobalSmoothSolution.uniformFiniteEnergyOn {ν : ℝ} {u₀ : Space → Space}
    {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsGlobalSmoothSolution ν u₀ u p) : UniformFiniteEnergyOn (Ici 0) u :=
  h.2.2.2.2.2

/-! ## The unforced counterexample statement -/

/-- The PLAN §1 negative-resolution target at one fixed viscosity `ν`: one
nonzero real divergence-free Schwartz datum `d`, a finite positive time `T`, a
classical solution `(u,p)` on `[0,T)` with that datum, uniformly finite energy
on `[0,T)`, pointwise-unbounded speed on approach to `T`
(`SpeedUnboundedAt T u`), and no global smooth finite-energy solution for the
same datum and viscosity. This is a **statement surface**: it is the exact
proposition PLAN task `UE4` would have to establish for one `ν` to refute
`NavierFormal.ClayAlternativeA_all`; nothing here proves it. -/
def UnforcedCounterexample (ν : ℝ) : Prop :=
  ∃ (d : SchwartzDivFree) (T : ℝ) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
    (⇑d ≠ (0 : Space → Space)) ∧ 0 < T ∧
    IsClassicalSolution ν (⇑d) T u p ∧
    UniformFiniteEnergyOn (Ico 0 T) u ∧
    SpeedUnboundedAt T u ∧
    ¬ ∃ v q, IsGlobalSmoothSolution ν (⇑d) v q

/-- The PLAN §1 negative-resolution target for at least one positive
viscosity. -/
def UnforcedCounterexampleSome : Prop := ∃ ν : ℝ, 0 < ν ∧ UnforcedCounterexample ν

/-- The PLAN §1 negative-resolution target for every positive viscosity, the
strongest form of the negative alternative. -/
def UnforcedCounterexampleAll : Prop := ∀ ν : ℝ, 0 < ν → UnforcedCounterexample ν

/-- An `UnforcedCounterexample` at viscosity `ν` refutes `ClayAlternativeA_all`:
the datum `d` it produces has no global smooth solution at that same `ν`, so
`ClayAlternativeA_all` (which would supply one for every `ν > 0` and every
datum) fails. -/
theorem UnforcedCounterexample.not_clayAlternativeA_all {ν : ℝ} (hν : 0 < ν)
    (h : UnforcedCounterexample ν) : ¬ ClayAlternativeA_all := by
  rintro hall
  obtain ⟨d, T, u, p, -, -, -, -, -, hno⟩ := h
  exact hno ((clayAlternativeA_iff ν d).mp (hall ν hν d))

/-- `UnforcedCounterexampleSome` refutes `ClayAlternativeA_all`. -/
theorem not_clayAlternativeA_all_of_some (h : UnforcedCounterexampleSome) :
    ¬ ClayAlternativeA_all := by
  obtain ⟨ν, hν, hce⟩ := h
  exact hce.not_clayAlternativeA_all hν

/-- Pointwise-unbounded speed at `T > 0` is incompatible with a uniform bound
on `[0,T)`: choosing `t₀ = 0 < T` in `SpeedUnboundedAt` produces a time
`t ∈ Ico 0 T` and a point where the speed exceeds any proposed bound `M`. -/
theorem SpeedUnboundedAt.not_bounded {T : ℝ} (hT : 0 < T) {u : ℝ → Space → Space}
    (h : SpeedUnboundedAt T u) :
    ¬ ∃ M : ℝ, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, ‖u t x‖ ≤ M := by
  rintro ⟨M, hM⟩
  obtain ⟨t, ht, x, hx⟩ := h M 0 hT
  exact absurd (hM t ⟨ht.1.le, ht.2⟩ x) (not_le.mpr hx)

/-! ## Viscosity rescaling -/

/-- The scalar rescaling `ν⁻¹ • d` of a divergence-free Schwartz datum is again
divergence-free: `divergence_const_smul` (`NavierFormal.SolutionClass`) turns
`∇·d = 0` into `∇·(ν⁻¹ • d) = ν⁻¹ · 0 = 0` at every point, using that `d` is
everywhere differentiable (`SchwartzDivFree.differentiable`). -/
def SchwartzDivFree.smul (c : ℝ) (d : SchwartzDivFree) : SchwartzDivFree where
  toSchwartz := c • d.toSchwartz
  div_free x := by
    have hd : DifferentiableAt ℝ (⇑d : Space → Space) x := d.differentiable.differentiableAt
    have hfun : (⇑(c • d.toSchwartz) : Space → Space) = fun y => c • (⇑d : Space → Space) y := by
      funext y; simp
    rw [hfun, divergence_const_smul c hd, d.div_free x, mul_zero]

@[simp] theorem SchwartzDivFree.coe_smul (c : ℝ) (d : SchwartzDivFree) :
    (⇑(d.smul c) : Space → Space) = fun x => c • (⇑d : Space → Space) x := by
  funext x; simp [SchwartzDivFree.smul]

/-- A nonzero datum scaled by a nonzero constant stays nonzero. -/
theorem SchwartzDivFree.smul_ne_zero {c : ℝ} (hc : c ≠ 0) {d : SchwartzDivFree}
    (hd : (⇑d : Space → Space) ≠ 0) : (⇑(d.smul c) : Space → Space) ≠ 0 := by
  rw [SchwartzDivFree.coe_smul]
  intro hzero
  apply hd
  funext x
  have hx : c • (⇑d : Space → Space) x = 0 := congrFun hzero x
  exact (smul_eq_zero.mp hx).resolve_left hc

/-- The energy rescaling accompanying `IsClassicalSolution.nuNormalization`:
if `u` has uniformly finite energy on `[0,T)` and `ν > 0`, then
`v(x,s) = ν⁻¹ • u(x,s/ν)` has uniformly finite energy on `[0,νT)`. This is the
`UniformFiniteEnergyOn` half of the manuscript's `eq:nu-normalization`,
proved directly from `enorm_smul` and `lintegral_const_mul'` rather than
through `eLpNorm`. -/
theorem UniformFiniteEnergyOn.nuNormalization {ν T : ℝ} (hν : 0 < ν)
    {u : ℝ → Space → Space} (h : UniformFiniteEnergyOn (Ico 0 T) u) :
    UniformFiniteEnergyOn (Ico 0 (ν * T)) (fun s x => ν⁻¹ • u (s / ν) x) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨ν⁻¹ ^ 2 * C, fun s hs => ?_⟩
  have ht : s / ν ∈ Ico (0 : ℝ) T := by
    refine ⟨div_nonneg hs.1 hν.le, (div_lt_iff₀ hν).2 ?_⟩
    calc s < ν * T := hs.2
      _ = T * ν := mul_comm _ _
  have hpt : ∀ x : Space,
      ‖ν⁻¹ • u (s / ν) x‖ₑ ^ 2 = ENNReal.ofReal (ν⁻¹ ^ 2) * ‖u (s / ν) x‖ₑ ^ 2 := by
    intro x
    rw [enorm_smul, mul_pow, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs]
  simp only [hpt]
  rw [lintegral_const_mul' _ _ (by finiteness), ENNReal.ofReal_mul (by positivity)]
  gcongr
  exact hC (s / ν) ht

/-- The manuscript's viscosity normalization turns an `UnforcedCounterexample`
at viscosity `ν > 0` into an `UnforcedCounterexample` at viscosity `1`: the
rescaled datum `ν⁻¹ • d`, time `νT`, and fields
`v(x,s) = ν⁻¹u(x,s/ν)`, `q(x,s) = ν⁻²p(x,s/ν)` of
`IsClassicalSolution.nuNormalization` inherit nonvanishing (`smul_ne_zero`),
positivity of the horizon, the classical-solution property, and uniformly
finite energy (`UniformFiniteEnergyOn.nuNormalization`) from the `ν` instance.
**Not completed**: the pointwise-unbounded-speed clause `SpeedUnboundedAt` and
the nonexistence-of-a-global-solution clause do not rescale by the lemmas
proved in this file or in `NavierFormal.SolutionClass`; see the report for the
exact obstruction. -/
theorem UnforcedCounterexample.nuNormalization_energy {ν : ℝ} (hν : 0 < ν)
    (h : UnforcedCounterexample ν) :
    ∃ (d' : SchwartzDivFree) (T' : ℝ) (u' : ℝ → Space → Space) (p' : ℝ → Space → ℝ),
      (⇑d' ≠ (0 : Space → Space)) ∧ 0 < T' ∧
      IsClassicalSolution 1 (⇑d') T' u' p' ∧
      UniformFiniteEnergyOn (Ico 0 T') u' := by
  obtain ⟨d, T, u, p, hd, hT, hsol, hufe, -, -⟩ := h
  refine ⟨d.smul ν⁻¹, ν * T, fun s x => ν⁻¹ • u (s / ν) x, fun s x => (ν ^ 2)⁻¹ * p (s / ν) x,
    SchwartzDivFree.smul_ne_zero (inv_ne_zero hν.ne') hd, mul_pos hν hT, ?_,
    hufe.nuNormalization hν⟩
  have := hsol.nuNormalization hν
  simpa [SchwartzDivFree.coe_smul] using this

end NavierFormal
