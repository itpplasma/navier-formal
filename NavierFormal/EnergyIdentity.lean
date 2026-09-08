import NavierFormal.Energy

/-!
# The energy identity, assembled from a single hypothesis bundle (manuscript `prop:energy`)

`NavierFormal.Energy` already carries every ingredient of the manuscript's proof of
`prop:energy`: the `L²`-differentiation of the kinetic energy
(`Energy.hasDerivWithinAt_kineticEnergy`, manuscript `eq:energy-derivative`), the
spatial assembly of the three integration-by-parts terms
(`Energy.integral_inner_timeDeriv_eq`), the resulting derivative of the energy
(`Energy.hasDerivWithinAt_energy`), and the fundamental-theorem-of-calculus step
producing the identity itself (`Energy.energy_identity`, manuscript `eq:energy`).

This module does not duplicate any of that; it only packages the hypotheses those
theorems take on a *closed* subinterval `Icc a b` into a single bundle
`EnergyHypotheses` stated once and for all on the open slab `Ioo 0 T` (the natural
domain of the manuscript's regularity package `R`, `lem:R-consequences`), and
restates the two headline theorems, `energy_hasDerivAt` and `energy_identity`, at a
single interior time / over a single subinterval `[s,t] ⊆ (0,T)` drawn from that
bundle.  The only new proof content is the restriction lemma
`hasL2DerivWithinAt_mono`, needed because `Energy.HasL2DerivWithinAt u ut s t` is
tied to a specific set `s` and `EnergyHypotheses` only supplies it on `Ioo 0 T`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace NavierFormal
namespace EnergyIdentity

/-! ## A restriction lemma for `Energy.HasL2DerivWithinAt` -/

/-- `Energy.HasL2DerivWithinAt` is monotone under shrinking the set: an
`L²`-difference-quotient limit taken over `s \ {t}` is in particular a limit
taken over any smaller `s' \ {t}`, since `nhdsWithin` only gets finer.  This is
the private device that lets `EnergyHypotheses` state its `L²`-differentiability
field once, on the open slab `Ioo 0 T`, while `NavierFormal.Energy`'s theorems
ask for it on a caller-chosen closed subinterval `Icc a b`. -/
theorem hasL2DerivWithinAt_mono {u : ℝ → Space → Space} {ut : Space → Space}
    {s s' : Set ℝ} {t : ℝ} (h : Energy.HasL2DerivWithinAt u ut s t) (hs : s' ⊆ s) :
    Energy.HasL2DerivWithinAt u ut s' t := by
  unfold Energy.HasL2DerivWithinAt at h ⊢
  exact h.mono_left (nhdsWithin_mono t (Set.sdiff_subset_sdiff_left hs))

/-! ## The hypothesis bundle -/

/-- The manuscript's regularity input for `prop:energy`, bundled once on the open
slab `Ioo 0 T` (manuscript `lem:R-consequences`, obtained there from the
regularity package `R` of `premise:local`).

* `mem_L2`, `mem_L2_timeDeriv`: `u(σ), u_t(σ) ∈ L²(ℝ³)³` for every interior time
  (`lem:R-consequences`(a), the ambient space of Step 1).
* `hasL2Deriv`: the `L²`-differentiability of `u` in time with derivative `u_t`
  (manuscript's `u ∈ C¹([0,T);L²)`, `lem:R-consequences`(a)), the sole input of
  Step 1 of the proof of `prop:energy`.
* `spatialIntegrability`: at each interior time, the eight `L¹` products
  `NavierFormal.Energy.SpatialIntegrability` needs to run the three
  boundary-free integrations by parts of `NavierFormal.IBP` (Steps 2–4),
  obtained in the manuscript from `u(σ), p(σ) ∈ H^k` for all `k` together with
  `u(σ) ∈ L^q`, `2 ≤ q ≤ ∞` (`lem:R-consequences`(c)).
* `dissipation_intervalIntegrable`: interval-integrability in time of
  `τ ↦ ‖∇u(τ)‖₂²` on every finite subinterval, the input the fundamental
  theorem of calculus needs at Step 5 to integrate the derivative found in
  Steps 1–4. -/
structure EnergyHypotheses (ν T : ℝ) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) :
    Prop where
  /-- `u(σ) ∈ L²(ℝ³)³` for every interior time `σ`. -/
  mem_L2 : ∀ σ ∈ Set.Ioo (0 : ℝ) T, MemLp (u σ) 2 volume
  /-- `u_t(σ) ∈ L²(ℝ³)³` for every interior time `σ`. -/
  mem_L2_timeDeriv : ∀ σ ∈ Set.Ioo (0 : ℝ) T, MemLp (timeDeriv u σ) 2 volume
  /-- `u` is `L²`-differentiable in time at every interior time `σ`, with
  derivative `u_t(σ)`, on the open slab `Ioo 0 T`. -/
  hasL2Deriv : ∀ σ ∈ Set.Ioo (0 : ℝ) T,
    Energy.HasL2DerivWithinAt u (timeDeriv u σ) (Set.Ioo (0 : ℝ) T) σ
  /-- The eight `L¹` products of `NavierFormal.Energy.SpatialIntegrability` at
  every interior time `σ`. -/
  spatialIntegrability : ∀ σ ∈ Set.Ioo (0 : ℝ) T, Energy.SpatialIntegrability (u σ) (p σ)
  /-- `τ ↦ ‖∇u(τ)‖₂²` is interval-integrable on every subinterval `[s,t]` of the
  open slab. -/
  dissipation_intervalIntegrable : ∀ {s t : ℝ}, 0 < s → t < T →
    IntervalIntegrable (fun σ => Energy.dissipation (u σ)) volume s t

/-! ## The headline theorems -/

variable {ν T : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}

/-- **The energy derivative, manuscript `prop:energy`, `eq:energy-derivative`.**

For a classical solution of `eq:NS` on `ℝ³ × [0,T)` carrying the regularity
bundle `EnergyHypotheses`, at every interior time `t`,

`d/dt (½‖u(t)‖₂²) = -ν‖∇u(t)‖₂²`.

This is `NavierFormal.Energy.hasDerivWithinAt_energy` (Steps 1–4 of the
manuscript's proof) upgraded from `HasDerivWithinAt` on a closed subinterval
`Icc a b` (chosen here as `[t/2, (t+T)/2] ⊆ (0,T)`, an explicit neighbourhood of
`t` inside the slab) to `HasDerivAt`, and rewritten from `NavierFormal.Energy`'s
`kineticEnergy _ / 2` / `NavierFormal.Energy.dissipation` bookkeeping to the
manuscript's `½∫‖u‖²` / `∫‖∇u‖²` display. -/
theorem energy_hasDerivAt (h : IsClassicalSolution ν u₀ T u p) (hE : EnergyHypotheses ν T u p)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => (1 / 2) * ∫ x, ‖u s x‖ ^ 2)
      (-(ν * ∫ x, enstrophyDensity (u t) x)) t := by
  set a : ℝ := t / 2 with ha_def
  set b : ℝ := (t + T) / 2 with hb_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hat : a < t := by rw [ha_def]; linarith
  have htb : t < b := by rw [hb_def]; linarith
  have hbT : b < T := by rw [hb_def]; linarith
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T :=
    fun x hx => ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hbT⟩
  have hmem : ∀ σ ∈ Set.Icc a b, MemLp (u σ) 2 volume :=
    fun σ hσ => hE.mem_L2 σ (hsub hσ)
  have hut : ∀ σ ∈ Set.Icc a b, MemLp (timeDeriv u σ) 2 volume :=
    fun σ hσ => hE.mem_L2_timeDeriv σ (hsub hσ)
  have hL2 : ∀ σ ∈ Set.Icc a b,
      Energy.HasL2DerivWithinAt u (timeDeriv u σ) (Set.Icc a b) σ :=
    fun σ hσ => hasL2DerivWithinAt_mono (hE.hasL2Deriv σ (hsub hσ)) hsub
  have hτ : t ∈ Set.Icc a b := ⟨hat.le, htb.le⟩
  have hint : Energy.SpatialIntegrability (u t) (p t) := hE.spatialIntegrability t ⟨ht0, htT⟩
  have hderivWithin := Energy.hasDerivWithinAt_energy h hmem hut hL2 hτ ht0 htT hint
  have hnhds : Set.Icc a b ∈ nhds t := Icc_mem_nhds hat htb
  have hderivAt := hderivWithin.hasDerivAt hnhds
  have heq : (fun σ => kineticEnergy (u σ) / 2) = fun σ => (1 / 2) * ∫ x, ‖u σ x‖ ^ 2 := by
    funext σ; unfold kineticEnergy; ring
  rw [heq] at hderivAt
  have hval : -(ν * Energy.dissipation (u t)) = -(ν * ∫ x, enstrophyDensity (u t) x) := rfl
  rwa [hval] at hderivAt

/-- **The energy identity, manuscript `prop:energy`, `eq:energy`.**

For a classical solution of `eq:NS` on `ℝ³ × [0,T)` carrying the regularity
bundle `EnergyHypotheses`, for every `0 < s ≤ t < T`,

`½‖u(t)‖₂² + ν ∫ₛᵗ ‖∇u(τ)‖₂² dτ = ½‖u(s)‖₂²`.

This is `NavierFormal.Energy.energy_identity` (the manuscript's Step 5,
continuity of the energy plus the fundamental theorem of calculus applied to
`energy_hasDerivAt`) specialized to `a := s`, `b := t`, and rewritten from
`kineticEnergy _ / 2` / `NavierFormal.Energy.dissipation` to the manuscript's
`½∫‖u‖²` / `∫‖∇u‖²` display. -/
theorem energy_identity (h : IsClassicalSolution ν u₀ T u p) (hE : EnergyHypotheses ν T u p)
    {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (htT : t < T) :
    (1 / 2) * (∫ x, ‖u t x‖ ^ 2) + ν * (∫ τ in s..t, ∫ x, enstrophyDensity (u τ) x)
      = (1 / 2) * ∫ x, ‖u s x‖ ^ 2 := by
  have hsub : Set.Icc s t ⊆ Set.Ioo (0 : ℝ) T :=
    fun x hx => ⟨lt_of_lt_of_le hs0 hx.1, lt_of_le_of_lt hx.2 htT⟩
  have hsub' : Set.Ioo s t ⊆ Set.Ioo (0 : ℝ) T := fun x hx => hsub ⟨hx.1.le, hx.2.le⟩
  have hmem : ∀ σ ∈ Set.Icc s t, MemLp (u σ) 2 volume := fun σ hσ => hE.mem_L2 σ (hsub hσ)
  have hut : ∀ σ ∈ Set.Icc s t, MemLp (timeDeriv u σ) 2 volume :=
    fun σ hσ => hE.mem_L2_timeDeriv σ (hsub hσ)
  have hL2 : ∀ σ ∈ Set.Icc s t,
      Energy.HasL2DerivWithinAt u (timeDeriv u σ) (Set.Icc s t) σ :=
    fun σ hσ => hasL2DerivWithinAt_mono (hE.hasL2Deriv σ (hsub hσ)) hsub
  have hint : ∀ σ ∈ Set.Ioo s t, Energy.SpatialIntegrability (u σ) (p σ) :=
    fun σ hσ => hE.spatialIntegrability σ (hsub' hσ)
  have hdiss : IntervalIntegrable (fun σ => Energy.dissipation (u σ)) volume s t :=
    hE.dissipation_intervalIntegrable hs0 htT
  have key := Energy.energy_identity h hst hs0.le htT hmem hut hL2 hint hdiss
  have heq1 : kineticEnergy (u t) / 2 = (1 / 2) * ∫ x, ‖u t x‖ ^ 2 := by
    unfold kineticEnergy; ring
  have heq2 : kineticEnergy (u s) / 2 = (1 / 2) * ∫ x, ‖u s x‖ ^ 2 := by
    unfold kineticEnergy; ring
  have heq3 : (∫ σ in s..t, Energy.dissipation (u σ))
      = ∫ τ in s..t, ∫ x, enstrophyDensity (u τ) x := by
    unfold Energy.dissipation; rfl
  rw [heq1, heq2, heq3] at key
  exact key

/-- **Energy non-increase for `ν ≥ 0`, corollary of `prop:energy`.**

A nonnegative-viscosity classical solution carrying the regularity bundle
`EnergyHypotheses` loses no energy backwards in time: for `0 < s ≤ t < T`,
`½‖u(t)‖₂² ≤ ½‖u(s)‖₂²`, since the dissipation term `ν ∫ₛᵗ‖∇u(τ)‖₂²dτ`
subtracted in `energy_identity` is nonnegative. -/
theorem energy_nonincreasing (h : IsClassicalSolution ν u₀ T u p) (hE : EnergyHypotheses ν T u p)
    (hν : 0 ≤ ν) {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (htT : t < T) :
    (1 / 2) * ∫ x, ‖u t x‖ ^ 2 ≤ (1 / 2) * ∫ x, ‖u s x‖ ^ 2 := by
  have hid := energy_identity h hE hs0 hst htT
  have hnonneg : 0 ≤ ν * ∫ τ in s..t, ∫ x, enstrophyDensity (u τ) x := by
    refine mul_nonneg hν (intervalIntegral.integral_nonneg hst fun τ _ => ?_)
    exact integral_nonneg fun x => enstrophyDensity_nonneg (u τ) x
  calc (1 / 2) * ∫ x, ‖u t x‖ ^ 2
      ≤ (1 / 2) * (∫ x, ‖u t x‖ ^ 2) + ν * (∫ τ in s..t, ∫ x, enstrophyDensity (u τ) x) := by
        linarith
    _ = (1 / 2) * ∫ x, ‖u s x‖ ^ 2 := hid

end EnergyIdentity
end NavierFormal

end
