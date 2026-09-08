import NavierFormal.Literature.TaoLocalTheory
import NavierFormal.Literature.Endpoint
import NavierFormal.EnergyIdentity

/-!
# The manuscript's local-theory bridge, proved from Tao's axiom (`taosplit` lane, FC1)

This module proves, as **theorems** from `NavierFormal.Literature.taoLocalTheory`
(`NavierFormal/Literature/TaoLocalTheory.lean`), exactly the statement of the old coarse
literature axiom `NavierFormal.Literature.localTheory` (`NavierFormal/Literature/LocalTheory.lean`,
not imported here) and its two convenience consequences, together with the manuscript's
`thm:conditional` reproved through this route.  The two pieces of manuscript-owned content that
the old axiom assumed are now genuinely *proved*:

* `lem:global-smooth` (`../navier-paper/main.tex`, `\label{lem:global-smooth}`): when `T_* = ∞`,
  joint one-sided smoothness of `(u,p)` on the *closed* half-space `Ici 0 ×ˢ ℝ³`, and the
  momentum/incompressibility equations at *every* `t ≥ 0`.  Proved by `contDiffOn_of_locally_
  contDiffOn` gluing Tao's per-horizon smoothness (`taoLocalTheory`'s `hsmooth_bdry`, on the
  half-open slab `Ico 0 T`) across all `T < T_* = ∞`, and by evaluating the `t = 0` equations
  (`taoLocalTheory`'s `heqn0`) together with the interior equations at each `t > 0`.
* The finite energy bound `∃ C, ∀ t ≥ 0, ∫⁻‖u(t)‖ₑ² ≤ ofReal C`, a consequence of
  `prop:energy` (`NavierFormal.EnergyIdentity.energy_identity`/`energy_nonincreasing`).  Proved
  by combining `energy_nonincreasing` on `[s,t]` with the `L²`-continuity of `u` at `t = 0`
  (`taoLocalTheory`'s `hcont0`) to let `s ↓ 0`, giving `‖u(t)‖₂ ≤ ‖u₀‖₂` for every `t > 0`
  (`t = 0` itself is the datum, `‖u(0)‖₂ = ‖u₀‖₂` exactly).

## The `EnergyHypotheses` bundle and the truncation device

`NavierFormal.EnergyIdentity.EnergyHypotheses`'s field `dissipation_intervalIntegrable` asks for
`IntervalIntegrable (fun σ => Energy.dissipation (u σ)) volume s t` for **every** real `s > 0`
and `t < T`, with no upper bound on `s` and no lower bound on `t`: literally, for `u` outside the
horizon `[0,T)`, where `taoLocalTheory` says nothing at all about `u`.  This field cannot be
proved for the literal branch `u`.  The fix used throughout this file is a truncation:
`uTrunc T u u₀ := fun t => if t ∈ Ico 0 T then u t else u₀` (similarly `pTrunc`, junk value `0`).
Since `IsClassicalSolution`/`RegularityPackage`/`EnergyHypotheses`'s every field only examines
`u`/`p` at times inside `Ico 0 T` (or, for the `L²`-derivative field, at times inside the open
sub-interval `Ioo 0 T`, using only *local* behaviour of `u` near each such time, which is exactly
where `uTrunc` still agrees with `u`), every hypothesis needed transfers from `(u,p)` to
`(uTrunc T u u₀, pTrunc T p)` by plain function-equality rewriting (`timeDeriv_uTrunc_eq` is the
one place a genuine local-derivative congruence lemma, `Filter.EventuallyEq.derivWithin_eq`, is
needed).  Outside `Ico 0 T`, `uTrunc`/`pTrunc` are the *constant* fields `u₀`/`0`, so
`dissipation ∘ uTrunc` is bounded and piecewise-continuous on the whole real line, hence
interval-integrable everywhere — discharging the field honestly, without asserting anything
about the literal `u` outside its known domain.  Because `uTrunc T u u₀ = u` pointwise on
`Ico 0 T`, every conclusion drawn about `uTrunc T u u₀` at a time `< T` is literally a conclusion
about `u` there, so the substitution costs nothing at the point of use.
-/

open MeasureTheory
open scoped ENNReal ContDiff Gradient Laplacian

noncomputable section

namespace NavierFormal

/-! ## The truncation device -/

/-- The datum-truncated velocity: agrees with `u` on `Ico 0 T`, and is the constant datum `u₀`
outside it.  Used only to discharge `NavierFormal.EnergyIdentity.EnergyHypotheses`'s
`dissipation_intervalIntegrable` field, which quantifies over times outside `Ico 0 T` where
`taoLocalTheory` gives no information about the literal branch `u`. -/
def uTrunc (T : ℝ) (u : ℝ → Space → Space) (u₀ : Space → Space) : ℝ → Space → Space :=
  fun t => if t ∈ Set.Ico (0 : ℝ) T then u t else u₀

/-- The pressure-truncated field, junk value `0` outside `Ico 0 T`, alongside `uTrunc`. -/
def pTrunc (T : ℝ) (p : ℝ → Space → ℝ) : ℝ → Space → ℝ :=
  fun t => if t ∈ Set.Ico (0 : ℝ) T then p t else 0

theorem uTrunc_eq_of_mem {T t : ℝ} (u : ℝ → Space → Space) (u₀ : Space → Space)
    (ht : t ∈ Set.Ico (0 : ℝ) T) : uTrunc T u u₀ t = u t :=
  if_pos ht

theorem pTrunc_eq_of_mem {T t : ℝ} (p : ℝ → Space → ℝ) (ht : t ∈ Set.Ico (0 : ℝ) T) :
    pTrunc T p t = p t :=
  if_pos ht

theorem uTrunc_eq_of_notMem {T t : ℝ} (u : ℝ → Space → Space) (u₀ : Space → Space)
    (ht : t ∉ Set.Ico (0 : ℝ) T) : uTrunc T u u₀ t = u₀ :=
  if_neg ht

/-- The one genuine local-congruence lemma the truncation device needs: at an interior time
`σ < T`, the time derivative of `uTrunc T u u₀` at `σ` agrees with that of `u`, because
`timeDeriv` at `σ` only examines `u` on a neighbourhood of `σ` within `Ici 0`, and `Ico 0 T` is
such a neighbourhood whenever `σ < T`. -/
theorem timeDeriv_uTrunc_eq {T σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) T) (u : ℝ → Space → Space)
    (u₀ : Space → Space) : timeDeriv (uTrunc T u u₀) σ = timeDeriv u σ := by
  funext x
  have hmem : Set.Ico (0 : ℝ) T ∈ nhdsWithin σ (Set.Ici (0 : ℝ)) := by
    have h1 : Set.Iio T ∈ nhdsWithin σ (Set.Ici (0 : ℝ)) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hσ.2)
    have h2 : Set.Ici (0 : ℝ) ∈ nhdsWithin σ (Set.Ici (0 : ℝ)) := self_mem_nhdsWithin
    have hinter := Filter.inter_mem h2 h1
    have hset : Set.Ici (0 : ℝ) ∩ Set.Iio T = Set.Ico (0 : ℝ) T := by
      ext y; simp [Set.mem_Ico, Set.mem_Ici, Set.mem_Iio]
    rwa [hset] at hinter
  have heq : (fun s => uTrunc T u u₀ s x) =ᶠ[nhdsWithin σ (Set.Ici (0 : ℝ))] (fun s => u s x) :=
    Filter.eventuallyEq_of_mem hmem fun s hs => congrFun (uTrunc_eq_of_mem u u₀ hs) x
  show derivWithin (fun s => uTrunc T u u₀ s x) (Set.Ici 0) σ
      = derivWithin (fun s => u s x) (Set.Ici 0) σ
  exact heq.derivWithin_eq (congrFun (uTrunc_eq_of_mem u u₀ ⟨hσ.1.le, hσ.2⟩) x)

/-- `IsClassicalSolution` transfers from `(u,p)` to the truncated pair, since every field only
examines `u`/`p` on `Ioo 0 T ⊆ Ico 0 T` or `Ico 0 T` itself (`smooth_u`/`smooth_p`/momentum/
incompressible/initial) — direct function equality — using `timeDeriv_uTrunc_eq` for the momentum
equation's time derivative. -/
theorem isClassicalSolution_uTrunc {ν T : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space}
    {p : ℝ → Space → ℝ} (hT0 : 0 < T) (h : IsClassicalSolution ν u₀ T u p) :
    IsClassicalSolution ν u₀ T (uTrunc T u u₀) (pTrunc T p) where
  smooth_u := h.smooth_u.congr fun q hq => by
    obtain ⟨hq1, -⟩ := hq
    exact congrFun (uTrunc_eq_of_mem u u₀ ⟨hq1.1.le, hq1.2⟩) q.2
  smooth_p := h.smooth_p.congr fun q hq => by
    obtain ⟨hq1, -⟩ := hq
    exact congrFun (pTrunc_eq_of_mem p ⟨hq1.1.le, hq1.2⟩) q.2
  cont_u := h.cont_u.congr fun q hq => by
    obtain ⟨hq1, -⟩ := hq
    exact congrFun (uTrunc_eq_of_mem u u₀ hq1) q.2
  cont_p := h.cont_p.congr fun q hq => by
    obtain ⟨hq1, -⟩ := hq
    exact congrFun (pTrunc_eq_of_mem p hq1) q.2
  initial := fun x => by
    rw [congrFun (uTrunc_eq_of_mem u u₀ ⟨le_refl 0, hT0⟩) x]; exact h.initial x
  momentum := fun t x ht htT => by
    have hmem : t ∈ Set.Ico (0 : ℝ) T := ⟨ht.le, htT⟩
    rw [timeDeriv_uTrunc_eq ⟨ht, htT⟩ u u₀, uTrunc_eq_of_mem u u₀ hmem, pTrunc_eq_of_mem p hmem]
    exact h.momentum t x ht htT
  incompressible := fun t x ht htT => by
    have hmem : t ∈ Set.Ico (0 : ℝ) T := ⟨ht.le, htT⟩
    rw [uTrunc_eq_of_mem u u₀ hmem]
    exact h.incompressible t x ht htT

/-- `Energy.HasL2DerivWithinAt` transfers along the truncation: the predicate at an interior
time `σ < T` only examines `u`/`uTrunc T u u₀` at times inside `Ioo 0 T ⊆ Ico 0 T`, where the
two agree, so the two `Tendsto` statements defining it are literally eventually equal along the
relevant filter. -/
theorem hasL2DerivWithinAt_uTrunc {T σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) T)
    (u : ℝ → Space → Space) (u₀ : Space → Space) (ut : Space → Space) :
    Energy.HasL2DerivWithinAt (uTrunc T u u₀) ut (Set.Ioo (0 : ℝ) T) σ
      ↔ Energy.HasL2DerivWithinAt u ut (Set.Ioo (0 : ℝ) T) σ := by
  have heq :
      (fun τ => eLpNorm
          (fun x => (τ - σ)⁻¹ • (uTrunc T u u₀ τ x - uTrunc T u u₀ σ x) - ut x) 2 volume)
        =ᶠ[nhdsWithin σ (Set.Ioo (0 : ℝ) T \ {σ})]
      (fun τ => eLpNorm (fun x => (τ - σ)⁻¹ • (u τ x - u σ x) - ut x) 2 volume) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : τ ∈ Set.Ico (0 : ℝ) T := ⟨hτ.1.1.le, hτ.1.2⟩
    have hσ' : σ ∈ Set.Ico (0 : ℝ) T := ⟨hσ.1.le, hσ.2⟩
    rw [uTrunc_eq_of_mem u u₀ hτ', uTrunc_eq_of_mem u u₀ hσ']
  unfold Energy.HasL2DerivWithinAt
  exact Filter.tendsto_congr' heq

/-- **The truncation discharges `dissipation_intervalIntegrable`.**  Given continuity of
`τ ↦ ∫ enstrophyDensity(u τ)` on the *closed, compact* interval `Icc 0 T` (obtained by the
caller from Tao's continuity clause at a horizon strictly beyond `T`), `dissipation ∘ uTrunc`
is bounded (by the sup on the compact piece, or by `dissipation u₀` on the constant piece) and
measurable (continuous on `Ico 0 T`, constant elsewhere) on the whole real line, hence
interval-integrable between any two reals whatsoever — discharging the field's unrestricted
quantifier honestly. -/
theorem intervalIntegrable_dissipation_uTrunc {T : ℝ}
    (u : ℝ → Space → Space) (u₀ : Space → Space)
    (hdiss_cont_cl : ContinuousOn (fun τ => ∫ x, enstrophyDensity (u τ) x) (Set.Icc (0 : ℝ) T))
    (a b : ℝ) :
    IntervalIntegrable (fun σ => Energy.dissipation (uTrunc T u u₀ σ)) volume a b := by
  set s : Set ℝ := Set.Ico (0 : ℝ) T with hs_def
  have hsmeas : MeasurableSet s := measurableSet_Ico
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (f := fun τ => ‖(fun τ => ∫ x, enstrophyDensity (u τ) x) τ‖) hdiss_cont_cl.norm
  set M : ℝ := max C ‖Energy.dissipation u₀‖ with hM_def
  have hbound : ∀ τ : ℝ, ‖Energy.dissipation (uTrunc T u u₀ τ)‖ ≤ M := by
    intro τ
    by_cases hτ : τ ∈ s
    · rw [uTrunc_eq_of_mem u u₀ hτ]
      have hτ' : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.le⟩
      have hCτ := hC ⟨τ, hτ', rfl⟩
      exact le_trans hCτ (le_max_left _ _)
    · rw [uTrunc_eq_of_notMem u u₀ hτ]
      exact le_max_right _ _
  have hmeas : AEStronglyMeasurable (fun τ => Energy.dissipation (uTrunc T u u₀ τ)) volume := by
    have heqfun : (fun τ => Energy.dissipation (uTrunc T u u₀ τ))
        = s.piecewise (fun τ => Energy.dissipation (u τ)) (fun _ => Energy.dissipation u₀) := by
      funext τ
      by_cases hτ : τ ∈ s
      · rw [Set.piecewise_eq_of_mem _ _ _ hτ, uTrunc_eq_of_mem u u₀ hτ]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hτ, uTrunc_eq_of_notMem u u₀ hτ]
    rw [heqfun]
    refine AEStronglyMeasurable.piecewise hsmeas ?_ aestronglyMeasurable_const
    exact (hdiss_cont_cl.mono Set.Ico_subset_Icc_self).aestronglyMeasurable hsmeas
  have hfin : volume (Set.uIcc a b) ≠ ⊤ := isCompact_uIcc.measure_lt_top.ne
  exact (Measure.integrableOn_of_bounded hfin hmeas
    (Filter.Eventually.of_forall hbound)).intervalIntegrable

/-- **The `EnergyHypotheses` bundle for the truncated pair.**  Assembles
`mem_L2`/`mem_L2_timeDeriv`/`hasL2Deriv`/`spatialIntegrability` from `IsClassicalSolution`,
`RegularityPackage`, `BoundedDerivatives`, and Tao's `L²`-derivative clause (all pointwise-in-`σ`
facts about the literal `u`, transported to `uTrunc T u u₀` by plain rewriting since the two
agree on `Ioo 0 T`), and `dissipation_intervalIntegrable` from the truncation lemma above. -/
theorem energyHypotheses_uTrunc {ν T : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space}
    {p : ℝ → Space → ℝ} (h : IsClassicalSolution ν u₀ T u p) (hreg : RegularityPackage T u p)
    (hbd : BoundedDerivatives T u p)
    (hL2deriv : ∀ σ ∈ Set.Ioo (0 : ℝ) T,
      Energy.HasL2DerivWithinAt u (timeDeriv u σ) (Set.Ioo (0 : ℝ) T) σ ∧
        MemLp (timeDeriv u σ) 2 volume)
    (hdiss_cont_cl : ContinuousOn (fun τ => ∫ x, enstrophyDensity (u τ) x) (Set.Icc (0 : ℝ) T)) :
    EnergyIdentity.EnergyHypotheses ν T (uTrunc T u u₀) (pTrunc T p) where
  mem_L2 := fun σ hσ => by
    rw [uTrunc_eq_of_mem u u₀ ⟨hσ.1.le, hσ.2⟩]
    exact h.memLp_two_velocity hreg hσ.1 hσ.2
  mem_L2_timeDeriv := fun σ hσ => by
    rw [timeDeriv_uTrunc_eq hσ u u₀]
    exact (hL2deriv σ hσ).2
  hasL2Deriv := fun σ hσ => by
    rw [timeDeriv_uTrunc_eq hσ u u₀]
    exact (hasL2DerivWithinAt_uTrunc hσ u u₀ (timeDeriv u σ)).2 (hL2deriv σ hσ).1
  spatialIntegrability := fun σ hσ => by
    rw [uTrunc_eq_of_mem u u₀ ⟨hσ.1.le, hσ.2⟩, pTrunc_eq_of_mem p ⟨hσ.1.le, hσ.2⟩]
    exact
      { norm_mul_fderiv := h.integrable_norm_velocity_mul_norm_fderiv hreg hσ.1 hσ.2
        enstrophy := h.integrable_enstrophyDensity_velocity hreg hσ.1 hσ.2
        norm_mul_fderiv2 := h.integrable_norm_velocity_mul_norm_fderiv_fderiv hreg hσ.1 hσ.2
        norm_cube := h.integrable_norm_velocity_pow_three hreg hbd hσ.1 hσ.2
        norm_sq_mul_fderiv := h.integrable_norm_velocity_sq_mul_norm_fderiv hreg hbd hσ.1 hσ.2
        pressure_mul := h.integrable_norm_pressure_mul_norm_velocity hreg hσ.1 hσ.2
        pressure_mul_fderiv := h.integrable_norm_pressure_mul_norm_fderiv_velocity hreg hσ.1 hσ.2
        fderiv_pressure_mul := by
          refine (h.integrable_norm_gradient_pressure_mul_norm_velocity hreg hσ.1 hσ.2).congr
            (Filter.Eventually.of_forall fun x => ?_)
          show ‖∇ (p σ) x‖ * ‖u σ x‖ = ‖fderiv ℝ (p σ) x‖ * ‖u σ x‖
          rw [norm_gradient_eq_norm_fderiv] }
  dissipation_intervalIntegrable := fun {s t} _ _ =>
    intervalIntegrable_dissipation_uTrunc u u₀ hdiss_cont_cl s t

/-- Order density of `ENNReal.ofReal` against `Tstar`: from `ofReal T < Tstar` there is a real
`T₂ > T` with `ofReal T₂ < Tstar` still.  Used to reach up to (but not including) a horizon `T`
using the regularity/continuity clauses of `taoLocalTheory`, which are only supplied strictly
below each horizon. -/
theorem exists_between_horizon {Tstar : ℝ≥0∞} {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ENNReal.ofReal T < Tstar) : ∃ T₂ : ℝ, T < T₂ ∧ ENNReal.ofReal T₂ < Tstar := by
  rcases eq_or_ne Tstar ⊤ with hTop | hTop
  · exact ⟨T + 1, by linarith, hTop ▸ ENNReal.ofReal_lt_top⟩
  · have hTlt : T < Tstar.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hT0 hTop).1 hT
    refine ⟨(T + Tstar.toReal) / 2, by linarith, ?_⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hTop).2 (by linarith)

/-- **The energy is non-increasing all the way down to the datum.**  For a Tao branch and an
interior time `0 < t` with `ofReal t < Tstar`, `kineticEnergy (u t) ≤ kineticEnergy u₀`.  Proved
by applying `EnergyIdentity.energy_nonincreasing` (via the truncation device) on `[s,t]` for
every `0 < s ≤ t`, then letting `s ↓ 0` using the `L²`-continuity clause `hcont0` of
`taoLocalTheory` to identify the limit of `kineticEnergy (u s)` as `kineticEnergy u₀`. -/
theorem kineticEnergy_le_datum {ν : ℝ} (hν : 0 < ν) {u₀ : SchwartzDivFree} {Tstar : ℝ≥0∞}
    {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hclause : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tstar →
      IsClassicalSolution ν (⇑u₀) T u p ∧ RegularityPackage T u p ∧ BoundedDerivatives T u p ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2)
          (Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set Space)) ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2)
          (Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set Space)) ∧
        (∀ σ ∈ Set.Ioo (0 : ℝ) T, Energy.HasL2DerivWithinAt u (timeDeriv u σ)
              (Set.Ioo (0 : ℝ) T) σ ∧ MemLp (timeDeriv u σ) 2 volume) ∧
        ContinuousOn (fun τ => ∫ x, enstrophyDensity (u τ) x) (Set.Ico (0 : ℝ) T))
    (hcont0 : Filter.Tendsto (fun t => ∫⁻ x, ‖u t x - (⇑u₀ : Space → Space) x‖ₑ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    {t : ℝ} (ht : 0 < t) (hTt : ENNReal.ofReal t < Tstar) :
    kineticEnergy (u t) ≤ kineticEnergy (⇑u₀ : Space → Space) := by
  obtain ⟨T, htT, hTlt⟩ := exists_between_horizon ht.le hTt
  have hT0 : 0 < T := ht.trans htT
  obtain ⟨h, hreg, hbd, -, -, hL2deriv, hdiss_cont⟩ := hclause T hT0 hTlt
  obtain ⟨T₂, hTT₂, hT₂lt⟩ := exists_between_horizon hT0.le hTlt
  obtain ⟨-, -, -, -, -, -, hdiss_cont₂⟩ := hclause T₂ (hT0.trans hTT₂) hT₂lt
  have hdiss_cont_cl : ContinuousOn (fun τ => ∫ x, enstrophyDensity (u τ) x) (Set.Icc (0 : ℝ) T) :=
    hdiss_cont₂.mono fun x hx => ⟨hx.1, hx.2.trans_lt hTT₂⟩
  have hIso : IsClassicalSolution ν (⇑u₀ : Space → Space) T (uTrunc T u (⇑u₀)) (pTrunc T p) :=
    isClassicalSolution_uTrunc hT0 h
  have hE := energyHypotheses_uTrunc h hreg hbd hL2deriv hdiss_cont_cl
  have hmono : ∀ s : ℝ, 0 < s → s ≤ t → kineticEnergy (u t) ≤ kineticEnergy (u s) := by
    intro s hs0 hst
    have hstT : t < T := htT
    have hnon := EnergyIdentity.energy_nonincreasing hIso hE hν.le hs0 hst hstT
    have hut : uTrunc T u (⇑u₀ : Space → Space) t = u t :=
      uTrunc_eq_of_mem u (⇑u₀ : Space → Space) ⟨(hs0.trans_le hst).le, hstT⟩
    have hus : uTrunc T u (⇑u₀ : Space → Space) s = u s :=
      uTrunc_eq_of_mem u (⇑u₀ : Space → Space) ⟨hs0.le, hst.trans_lt hstT⟩
    rw [hut, hus] at hnon
    have hhalf : (1 / 2 : ℝ) * kineticEnergy (u t) ≤ (1 / 2 : ℝ) * kineticEnergy (u s) := hnon
    linarith
  have hu₀mem : MemLp (⇑u₀ : Space → Space) 2 volume := u₀.toSchwartz.memLp 2 volume
  have hmemLp_near : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), MemLp (u s) 2 volume := by
    filter_upwards [Ioo_mem_nhdsGT hT0] with s hs
    exact h.memLp_two_velocity hreg hs.1 hs.2
  have htendsto : Filter.Tendsto (fun s => kineticEnergy (u s)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (kineticEnergy (⇑u₀ : Space → Space))) := by
    have hrpow : Filter.Tendsto
        (fun s => (∫⁻ x, ‖u s x - (⇑u₀ : Space → Space) x‖ₑ ^ 2) ^ (1 / 2 : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp hcont0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hrpow
    have htoreal : Filter.Tendsto
        (fun s => ((∫⁻ x, ‖u s x - (⇑u₀ : Space → Space) x‖ₑ ^ 2) ^ (1 / 2 : ℝ)).toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
      have hto := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp hrpow
      simpa [Function.comp_def] using hto
    have heLp : ∀ s : ℝ, MemLp (u s) 2 volume →
        (eLpNorm (fun x => u s x - (⇑u₀ : Space → Space) x) 2 volume).toReal
          = ((∫⁻ x, ‖u s x - (⇑u₀ : Space → Space) x‖ₑ ^ 2) ^ (1 / 2 : ℝ)).toReal := by
      intro s hs
      congr 1
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (two_ne_zero) (by simp)]
      norm_num
    have hnormeq : ∀ s : ℝ, MemLp (u s) 2 volume →
        ‖Energy.toL2 (u s) - Energy.toL2 (⇑u₀ : Space → Space)‖
          = (eLpNorm (fun x => u s x - (⇑u₀ : Space → Space) x) 2 volume).toReal := by
      intro s hs
      rw [Lp.norm_def]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (Energy.toL2 (u s)) (Energy.toL2 (⇑u₀ : Space → Space)),
        Energy.coeFn_toL2 hs, Energy.coeFn_toL2 hu₀mem] with x h1 h2 h3
      rw [h1]
      simp only [Pi.sub_apply]
      rw [h2, h3]
    have hkey : Filter.Tendsto
        (fun s => ‖Energy.toL2 (u s) - Energy.toL2 (⇑u₀ : Space → Space)‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      refine htoreal.congr' ?_
      filter_upwards [hmemLp_near] with s hs
      rw [hnormeq s hs, heLp s hs]
    have htoL2tendsto : Filter.Tendsto (fun s => Energy.toL2 (u s))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Energy.toL2 (⇑u₀ : Space → Space))) :=
      tendsto_iff_norm_sub_tendsto_zero.2 hkey
    have hnormtendsto : Filter.Tendsto (fun s => ‖Energy.toL2 (u s)‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ‖Energy.toL2 (⇑u₀ : Space → Space)‖) :=
      (continuous_norm.tendsto _).comp htoL2tendsto
    rw [← Energy.norm_toL2_sq hu₀mem]
    refine (Filter.Tendsto.congr' ?_ ((continuous_pow 2).tendsto _ |>.comp hnormtendsto))
    filter_upwards [hmemLp_near] with s hs
    exact Energy.norm_toL2_sq hs
  have hstend : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), kineticEnergy (u t) ≤ kineticEnergy (u s) := by
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    exact hmono s hs.1 hs.2.le
  exact ge_of_tendsto htendsto hstend

/-- The `ℝ≥0∞` kinetic-energy integral equals `ofReal (kineticEnergy v)` once `v ∈ L²`, so that
a real bound on `kineticEnergy` transfers to the `ℝ≥0∞` bound `ClayAlternativeA` asks for. -/
theorem lintegral_norm_sq_eq_ofReal_kineticEnergy {v : Space → Space} (hv : MemLp v 2 volume) :
    (∫⁻ x, ‖v x‖ₑ ^ 2) = ENNReal.ofReal (kineticEnergy v) := by
  show kineticEnergyLintegral v = ENNReal.ofReal (kineticEnergy v)
  rw [kineticEnergyLintegral_eq, kineticEnergy,
    ofReal_integral_eq_lintegral_ofReal hv.norm.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]

/-- **The manuscript's `prop:localtheory`, proved from `taoLocalTheory`.**  This is exactly the
statement of the old coarse axiom `NavierFormal.Literature.localTheory`
(`NavierFormal/Literature/LocalTheory.lean`, not imported here), now a theorem: the `Tstar = ⊤`
clause (`lem:global-smooth` and the energy half of `prop:energy`) is derived rather than assumed,
by gluing Tao's per-horizon smoothness (`contDiffOn_of_locally_contDiffOn`), evaluating the
equations at every `t ≥ 0` (Tao's `t = 0` clause plus the interior equations at each `t > 0`), and
`kineticEnergy_le_datum` for the energy bound. -/
theorem localTheory_of_tao (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzDivFree) :
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
        ENNReal.ofReal T ≤ Tstar ∧ ∀ t x, 0 ≤ t → t < T → v t x = u t x) := by
  obtain ⟨Tstar, u, p, hpos, hclause, heqn0, hdiv0, hcont0, hblow, huniq⟩ :=
    Literature.taoLocalTheory ν hν u₀
  refine ⟨Tstar, u, p, hpos,
    fun T hT0 hTlt => ⟨(hclause T hT0 hTlt).1, (hclause T hT0 hTlt).2.1⟩, hblow, ?_, huniq⟩
  intro hTstarTop
  have hlt_top : ∀ T : ℝ, 0 ≤ T → ENNReal.ofReal T < Tstar := fun T _ =>
    hTstarTop ▸ ENNReal.ofReal_lt_top
  have hsmooth_u : ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2)
      (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) := by
    refine contDiffOn_of_locally_contDiffOn ?_
    rintro ⟨t₀, x₀⟩ hmemx
    have ht₀ : 0 ≤ t₀ := hmemx.1
    have hmem_u : (t₀, x₀) ∈ Set.Iio (t₀ + 1) ×ˢ (Set.univ : Set Space) :=
      ⟨lt_add_one t₀, Set.mem_univ x₀⟩
    refine ⟨Set.Iio (t₀ + 1) ×ˢ (Set.univ : Set Space), isOpen_Iio.prod isOpen_univ,
      hmem_u, ?_⟩
    have hset : (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space))
          ∩ (Set.Iio (t₀ + 1) ×ˢ (Set.univ : Set Space))
        = Set.Ico (0 : ℝ) (t₀ + 1) ×ˢ (Set.univ : Set Space) := by
      rw [Set.prod_inter_prod, Set.univ_inter, Set.Ici_inter_Iio]
    rw [hset]
    exact (hclause (t₀ + 1) (by linarith) (hlt_top _ (by linarith))).2.2.2.1
  have hsmooth_p : ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2)
      (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)) := by
    refine contDiffOn_of_locally_contDiffOn ?_
    rintro ⟨t₀, x₀⟩ hmemx
    have ht₀ : 0 ≤ t₀ := hmemx.1
    have hmem_u : (t₀, x₀) ∈ Set.Iio (t₀ + 1) ×ˢ (Set.univ : Set Space) :=
      ⟨lt_add_one t₀, Set.mem_univ x₀⟩
    refine ⟨Set.Iio (t₀ + 1) ×ˢ (Set.univ : Set Space), isOpen_Iio.prod isOpen_univ,
      hmem_u, ?_⟩
    have hset : (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space))
          ∩ (Set.Iio (t₀ + 1) ×ˢ (Set.univ : Set Space))
        = Set.Ico (0 : ℝ) (t₀ + 1) ×ˢ (Set.univ : Set Space) := by
      rw [Set.prod_inter_prod, Set.univ_inter, Set.Ici_inter_Iio]
    rw [hset]
    exact (hclause (t₀ + 1) (by linarith) (hlt_top _ (by linarith))).2.2.2.2.1
  have hmom_all : ∀ t x, 0 ≤ t →
      timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x := by
    intro t x ht
    rcases ht.eq_or_lt with h0 | hpos'
    · exact h0 ▸ heqn0 x
    · exact (hclause (t + 1) (by linarith) (hlt_top _ (by linarith))).1.momentum t x hpos'
        (by linarith)
  have hdiv_all : ∀ t x, 0 ≤ t → divergence (u t) x = 0 := by
    intro t x ht
    rcases ht.eq_or_lt with h0 | hpos'
    · exact h0 ▸ hdiv0 x
    · exact (hclause (t + 1) (by linarith) (hlt_top _ (by linarith))).1.incompressible t x hpos'
        (by linarith)
  have henergy : ∃ C : ℝ, ∀ t, 0 ≤ t → ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ENNReal.ofReal C := by
    refine ⟨kineticEnergy (⇑u₀ : Space → Space), fun t ht => ?_⟩
    rcases ht.eq_or_lt with h0 | hpos'
    · have h1 : IsClassicalSolution ν (⇑u₀ : Space → Space) 1 u p :=
        (hclause 1 one_pos (hlt_top 1 zero_le_one)).1
      have hu0 : u t = (⇑u₀ : Space → Space) := by rw [← h0]; exact funext h1.initial
      rw [hu0, lintegral_norm_sq_eq_ofReal_kineticEnergy (u₀.toSchwartz.memLp 2 volume)]
    · obtain ⟨T, htT, hTlt⟩ := exists_between_horizon hpos'.le (hlt_top t hpos'.le)
      have hmemLp := (hclause T (hpos'.trans htT) hTlt).1.memLp_two_velocity
        (hclause T (hpos'.trans htT) hTlt).2.1 hpos' htT
      rw [lintegral_norm_sq_eq_ofReal_kineticEnergy hmemLp]
      exact ENNReal.ofReal_le_ofReal
        (kineticEnergy_le_datum hν hclause hcont0 hpos' (hlt_top t hpos'.le))
  exact ⟨hsmooth_u, hsmooth_p, hmom_all, hdiv_all, henergy⟩

/-- Convenience consequence of `localTheory_of_tao`, alongside the old file's
`isClassicalSolution_of_lt`: at every finite `T < Tstar` the branch is a classical solution with
the regularity package. -/
theorem isClassicalSolution_of_lt_of_tao {ν : ℝ} (_hν : 0 < ν) {u₀ : SchwartzDivFree}
    {Tstar : ℝ≥0∞} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hsol : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tstar →
      IsClassicalSolution ν (⇑u₀) T u p ∧ RegularityPackage T u p)
    {T : ℝ} (hT0 : 0 < T) (hTlt : ENNReal.ofReal T < Tstar) :
    IsClassicalSolution ν (⇑u₀) T u p :=
  (hsol T hT0 hTlt).1

/-- **Assembly lemma**, alongside the old file's `clayAlternativeA_of_Tstar_top`: when the
maximal branch produced by `localTheory_of_tao` is global (`Tstar = ⊤`), its global-smoothness/
energy clause together with clause `sol` assemble into `NavierFormal.ClayAlternativeA`. -/
theorem clayAlternativeA_of_Tstar_top_of_tao {ν : ℝ} (_hν : 0 < ν) {u₀ : SchwartzDivFree}
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
  have h1 : IsClassicalSolution ν (⇑u₀) 1 u p := (hsol 1 one_pos (by simp)).1
  exact ⟨u, p, hsu, hsp, h1.initial, hmom, hdiv, C, hC⟩

/-- **Manuscript `thm:conditional`, fixed `(ν,u₀)` form, reproved through `localTheory_of_tao`
and `Literature.endpointContinuation`.**  Copies the proof structure of
`NavierFormal.Conditional.conditional_clay_A_of_bound`, with `localTheory_of_tao` in place of
the coarse axiom `NavierFormal.Literature.localTheory`. -/
theorem conditional_clay_A_of_bound_of_tao {ν : ℝ} (hν : 0 < ν) {u₀ : SchwartzDivFree}
    (hcb : CriticalBound ν u₀) : ClayAlternativeA ν u₀ := by
  obtain ⟨Tstar, u, p, -, hsol, hblow, hglob, -⟩ := localTheory_of_tao ν hν u₀
  have hTstarTop : Tstar = ⊤ := by
    by_contra hne
    have hlt : Tstar < ⊤ := lt_top_iff_ne_top.mpr hne
    obtain ⟨M, -, hM⟩ := hcb (Tstar.toReal + 1) (by positivity)
    obtain ⟨t, ht0, htlt, htgt⟩ :=
      Literature.endpointContinuation ν hν u₀ Tstar u p hsol hblow hlt M
    have htTstar : t < Tstar.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal ht0.le hlt.ne).1 htlt
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
  refine clayAlternativeA_of_Tstar_top_of_tao hν ?_ (hglob hTstarTop)
  intro T hT0 _
  exact hsol T hT0 (hTstarTop ▸ ENNReal.ofReal_lt_top)

/-- **Manuscript `thm:conditional`, reproved through `localTheory_of_tao`.**  Immediate from
`conditional_clay_A_of_bound_of_tao`, specialised at each `(ν,u₀)`. -/
theorem conditional_clay_A_of_tao (hcrit : CriticalHypothesis) : ClayAlternativeA_all :=
  fun ν hν u₀ => conditional_clay_A_of_bound_of_tao hν (hcrit ν hν u₀)

end NavierFormal

end
