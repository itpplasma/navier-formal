import NavierFormal.EnergyIdentity
import NavierFormal.ClassBridges

/-!
# The energy hypotheses, derived from the regularity package (PLAN 8.2a)

This module discharges the PLAN 8.2a residual: it derives the hypothesis bundle
`NavierFormal.EnergyIdentity.EnergyHypotheses` (manuscript `prop:energy` Step 1,
`lem:R-consequences`, obtained after `premise:local`) from `IsClassicalSolution`
together with the regularity package `NavierFormal.RegularityPackage` and the
boundedness package `NavierFormal.BoundedDerivatives` of `NavierFormal.ClassBridges`.

Three of the four fields of `EnergyHypotheses` are assembled here without any
further hypothesis:

* `mem_L2` and `mem_L2_timeDeriv` (`lem:R-consequences`(a), the ambient-space half):
  `u(σ), ∂ₜu(σ) ∈ L²(ℝ³)³` at every interior time.  The velocity case is
  `ClassBridges.IsClassicalSolution.memLp_two_velocity`; the time-derivative case
  is new here (`mem_L2_timeDeriv_of_bridges`) and needs one auxiliary fact not
  present elsewhere in the development: that `∂ₜu(σ) = NavierFormal.timeDeriv u σ`
  is *continuous* in space, hence measurable, at an interior time.  This is
  proved from the joint smoothness `IsClassicalSolution.smooth_u` alone
  (`continuous_timeDeriv_of_smooth` below), by identifying `∂ₜu(σ,x)` with the
  directional derivative of the jointly smooth field `(t,x) ↦ u(t,x)` in the
  time direction, which stays jointly smooth after one differentiation.
* `spatialIntegrability` (`lem:R-consequences`(c)): the eight `L¹` products of
  `Energy.SpatialIntegrability`, assembled verbatim from the `ClassBridges`
  `integrable_*`/`memLp_*` lemmas (`spatialIntegrability_of_bridges`); the one
  field with no exact counterpart, `fderiv_pressure_mul`, is obtained from
  `ClassBridges.IsClassicalSolution.integrable_norm_gradient_pressure_mul_norm_velocity`
  by the norm identity `norm_gradient_eq_norm_fderiv`.

The remaining field, `hasL2Deriv` (manuscript `lem:R-consequences`(a), the
`L²`-differentiability half — Step 1 itself of `prop:energy`), and the
interval-integrability field `dissipation_intervalIntegrable`, are **not**
derived here from `RegularityPackage`/`BoundedDerivatives`; see the "What is
NOT done" discussion below `EnergyHypotheses.of_regularity` for the precise
reason. They are carried as explicit hypotheses of `EnergyHypotheses.of_regularity`
and `energy_identity_of_regularity`, in the form requested by the task
statement: "if this is too hard, state the domination as an explicit
hypothesis in a structure and prove everything else."

Nothing in this file is a theorem about the Millennium problem.
-/

open MeasureTheory
open scoped ENNReal ContDiff

noncomputable section

namespace NavierFormal

/-! ## The time derivative of a jointly smooth field is jointly smooth

These two lemmas are the generic fact behind `mem_L2_timeDeriv_of_bridges`: on
the open slab where a time-dependent field is jointly `C^∞`, its time
derivative `NavierFormal.timeDeriv` is *also* jointly smooth, in particular
continuous in space at each interior time.  Nothing here is specific to the
velocity or the pressure; it is stated for a general jointly smooth field so
that it applies to `u` unchanged. -/

section TimeDerivSmoothness

variable {T : ℝ} {U : ℝ → Space → Space}

/-- The pointwise identification of `NavierFormal.timeDeriv` with the joint
Fréchet derivative of a jointly smooth field, evaluated in the time direction
`(1,0)`: for `t` interior, `∂ₜU(t,x) = D(t,x)U · (1,0)`, where `D(t,x)U` is the
Fréchet derivative of `(t,x) ↦ U(t,x)` at `(t,x)`.  Proof: `timeDeriv` agrees
with the ordinary one-sided-free derivative at `t > 0`
(`NavierFormal.timeDeriv_eq_deriv`), and that ordinary derivative is the
composition of the joint derivative with the affine map `s ↦ (s,x)`, whose own
derivative is `(1,0)` (`HasFDerivAt.comp_hasDerivAt`). -/
theorem timeDeriv_eq_fderiv_apply_of_smooth
    (hU : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2)
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space)))
    {t : ℝ} (ht : 0 < t) (htT : t < T) (x : Space) :
    timeDeriv U t x
      = fderiv ℝ (fun q : ℝ × Space => U q.1 q.2) (t, x) ((1 : ℝ), (0 : Space)) := by
  rw [timeDeriv_eq_deriv ht x]
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Space)) :=
    isOpen_Ioo.prod isOpen_univ
  have hmem : ((t, x) : ℝ × Space) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Space) :=
    ⟨⟨ht, htT⟩, Set.mem_univ x⟩
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × Space => U q.1 q.2) (t, x) :=
    (hU.contDiffAt (hopen.mem_nhds hmem)).differentiableAt IsClassicalSolution.infty_ne_zero
  have hF : HasFDerivAt (fun q : ℝ × Space => U q.1 q.2)
      (fderiv ℝ (fun q : ℝ × Space => U q.1 q.2) (t, x)) (t, x) := hdiff.hasFDerivAt
  have hg : HasDerivAt (fun s : ℝ => ((s, x) : ℝ × Space)) ((1 : ℝ), (0 : Space)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hcomp := HasFDerivAt.comp_hasDerivAt t hF hg
  exact hcomp.deriv

/-- **The time derivative of a jointly smooth field is continuous in space at
each interior time.**  Consequence of `timeDeriv_eq_fderiv_apply_of_smooth`:
the joint Fréchet derivative of a `C^∞` field is itself `C^∞` (one order is
absorbed since `∞ + 1 = ∞`), and postcomposing with the fixed evaluation
functional `L ↦ L(1,0)` and precomposing with `x ↦ (t,x)` preserves smoothness,
hence in particular continuity. -/
theorem continuous_timeDeriv_of_smooth
    (hU : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2)
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space)))
    {t : ℝ} (ht : 0 < t) (htT : t < T) : Continuous (timeDeriv U t) := by
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Space)) :=
    isOpen_Ioo.prod isOpen_univ
  have hFderiv : ContDiffOn ℝ ∞ (fderiv ℝ (fun q : ℝ × Space => U q.1 q.2))
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space)) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hopen).1 hU).2
  have hEval : ContDiffOn ℝ ∞
      (fun q : ℝ × Space => fderiv ℝ (fun q' : ℝ × Space => U q'.1 q'.2) q
        ((1 : ℝ), (0 : Space)))
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space)) :=
    (ContinuousLinearMap.apply ℝ Space ((1 : ℝ), (0 : Space))).contDiff.fun_comp_contDiffOn
      hFderiv
  have hsub : Set.MapsTo (fun x : Space => ((t, x) : ℝ × Space)) Set.univ
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space)) :=
    fun x _ => ⟨⟨ht, htT⟩, Set.mem_univ x⟩
  have hcomp : ContDiffOn ℝ ∞
      (fun x : Space => fderiv ℝ (fun q' : ℝ × Space => U q'.1 q'.2) (t, x)
        ((1 : ℝ), (0 : Space)))
      Set.univ :=
    hEval.comp (contDiff_const.prodMk contDiff_id).contDiffOn hsub
  have hcont : Continuous
      (fun x : Space => fderiv ℝ (fun q' : ℝ × Space => U q'.1 q'.2) (t, x)
        ((1 : ℝ), (0 : Space))) :=
    continuousOn_univ.mp hcomp.continuousOn
  have hfun : timeDeriv U t
      = fun x => fderiv ℝ (fun q' : ℝ × Space => U q'.1 q'.2) (t, x) ((1 : ℝ), (0 : Space)) :=
    funext fun x => timeDeriv_eq_fderiv_apply_of_smooth hU ht htT x
  rw [hfun]
  exact hcont

end TimeDerivSmoothness

namespace EnergyIdentity
namespace EnergyHypotheses

variable {ν T : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}

/-! ## `mem_L2` and `mem_L2_timeDeriv`, from the regularity package -/

/-- **`EnergyHypotheses.mem_L2` from the regularity package.**  `u(σ) ∈ L²(ℝ³)³`
at an interior time `σ`, manuscript `lem:R-consequences`(a).  This is exactly
`ClassBridges.IsClassicalSolution.memLp_two_velocity`, the `j = k = 0` instance
of `RegularityPackage`. -/
theorem mem_L2_of_bridges (h : IsClassicalSolution ν u₀ T u p) (hR : RegularityPackage T u p)
    {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) T) : MemLp (u σ) 2 volume :=
  h.memLp_two_velocity hR hσ.1 hσ.2

/-- **`EnergyHypotheses.mem_L2_timeDeriv` from the regularity package.**
`∂ₜu(σ) ∈ L²(ℝ³)³` at an interior time `σ`, manuscript `lem:R-consequences`(a).
`RegularityPackage`'s `j = 1, k = 0` instance bounds
`eLpNorm (iteratedFDeriv ℝ 0 (timeDerivIter 1 u σ)) 2`; since
`timeDerivIter 1 u = timeDeriv u` (`timeDerivIter_succ`/`timeDerivIter_zero`) and
`iteratedFDeriv ℝ 0` agrees with the identity in `eLpNorm`
(`ClassBridges.eLpNorm_iteratedFDeriv_zero`), this is exactly the finiteness half
of `MemLp`; the measurability half is `continuous_timeDeriv_of_smooth`, applied
to `h.smooth_u`. -/
theorem mem_L2_timeDeriv_of_bridges (h : IsClassicalSolution ν u₀ T u p)
    (hR : RegularityPackage T u p) {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) T) :
    MemLp (timeDeriv u σ) 2 volume := by
  refine ⟨(continuous_timeDeriv_of_smooth h.smooth_u hσ.1 hσ.2).aestronglyMeasurable, ?_⟩
  have hlt := hR.eLpNorm_two_lt_top_u 1 0 hσ.1.le hσ.2
  have hiter : timeDerivIter 1 u = timeDeriv u := by
    rw [timeDerivIter_succ, timeDerivIter_zero]
  rwa [hiter, eLpNorm_iteratedFDeriv_zero] at hlt

/-! ## `spatialIntegrability`, from the regularity and boundedness packages -/

/-- **`EnergyHypotheses.spatialIntegrability` from the regularity and boundedness
packages.**  The eight `L¹` products of `Energy.SpatialIntegrability` at an
interior time `σ`, manuscript `lem:R-consequences`(c).  Each field is exactly
one `ClassBridges` bridge lemma; the one field with no verbatim counterpart,
`fderiv_pressure_mul` (`‖∇p(σ)‖‖u(σ)‖ ∈ L¹`), is obtained from
`ClassBridges.IsClassicalSolution.integrable_norm_gradient_pressure_mul_norm_velocity`
(stated through `gradient`) via the norm identity
`ClassBridges.norm_gradient_eq_norm_fderiv`. -/
theorem spatialIntegrability_of_bridges (h : IsClassicalSolution ν u₀ T u p)
    (hR : RegularityPackage T u p) (hB : BoundedDerivatives T u p) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) T) : Energy.SpatialIntegrability (u σ) (p σ) where
  norm_mul_fderiv := h.integrable_norm_velocity_mul_norm_fderiv hR hσ.1 hσ.2
  enstrophy := h.integrable_enstrophyDensity_velocity hR hσ.1 hσ.2
  norm_mul_fderiv2 := h.integrable_norm_velocity_mul_norm_fderiv_fderiv hR hσ.1 hσ.2
  norm_cube := h.integrable_norm_velocity_pow_three hR hB hσ.1 hσ.2
  norm_sq_mul_fderiv := h.integrable_norm_velocity_sq_mul_norm_fderiv hR hB hσ.1 hσ.2
  pressure_mul := h.integrable_norm_pressure_mul_norm_velocity hR hσ.1 hσ.2
  pressure_mul_fderiv := h.integrable_norm_pressure_mul_norm_fderiv_velocity hR hσ.1 hσ.2
  fderiv_pressure_mul := by
    refine (h.integrable_norm_gradient_pressure_mul_norm_velocity hR hσ.1 hσ.2).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_gradient_eq_norm_fderiv]

/-! ## Assembly

The two remaining fields of `EnergyHypotheses`, `hasL2Deriv` and
`dissipation_intervalIntegrable`, are **not** derived from `RegularityPackage`
and `BoundedDerivatives` in this file.

* `hasL2Deriv` is the manuscript's `lem:R-consequences`(a), Step 1 of
  `prop:energy` itself: `∂ₜ` of the difference quotient of `u` converges **in
  `L²`**.  `RegularityPackage` does supply, via its `j = 2, k = 0` instance, a
  uniform-in-time bound `eLpNorm (∂ₜ²u(r)) 2 ≤ C` on every compact time
  subinterval, which is the manuscript's domination hypothesis for the Taylor
  remainder `‖(u(τ)-u(σ))/(τ-σ) - ∂ₜu(σ)‖₂ ≤ (|τ-σ|/2) · sup_{r} ‖∂ₜ²u(r)‖₂`.
  Turning that bound into the stated `L²` limit needs a Taylor formula for
  `Space →₂[volume] Space`-valued curves together with Minkowski's integral
  inequality for the Bochner integral defining the Taylor remainder (to avoid a
  pointwise-in-`x`, "measurable sup over `r`" argument, which does not fit the
  `RegularityPackage` bound, itself only an `L²`-in-`x` bound at each fixed
  `r`, not a bound on a single dominating function of `x`).  Building that
  Taylor-remainder infrastructure for Hilbert-space-valued curves is out of
  reach of this lane's budget: it is not a rearrangement of an existing
  Mathlib/`NavierFormal` lemma, and would need its own file.  `hasL2Deriv` is
  therefore taken here as the explicit hypothesis `hL2Deriv`, in the exact
  shape `EnergyHypotheses.hasL2Deriv` already asks for it.
* `dissipation_intervalIntegrable` needs continuity of
  `τ ↦ ∫ enstrophyDensity (u τ)` on the relevant closed interval.  The joint
  smoothness of `u` makes the integrand jointly continuous, but continuity of
  the parametric integral needs a *τ-independent, `x`-integrable* dominating
  function; `BoundedDerivatives` only supplies a pointwise bound uniform in `x`
  (a non-integrable constant), and `RegularityPackage`/`ClassBridges` only
  supply the fixed-time integrability `SpatialIntegrability.enstrophy`, not a
  bound uniform over a neighbourhood of `τ`. Producing the needed local
  domination is a genuine uniform-integrability argument not present anywhere
  in the development, so `dissipation_intervalIntegrable` is likewise taken as
  the explicit hypothesis `hDissInt`. -/

/-- **`EnergyHypotheses.of_regularity`.**  Assembles the manuscript's regularity
input for `prop:energy` (`lem:R-consequences`) from a classical solution
together with `RegularityPackage` and `BoundedDerivatives`
(`premise:local`), and the two explicit hypotheses `hL2Deriv`
(`lem:R-consequences`(a), Step 1 of `prop:energy`) and `hDissInt` that this file
does not reduce further (see the discussion above). -/
theorem of_regularity (h : IsClassicalSolution ν u₀ T u p) (hR : RegularityPackage T u p)
    (hB : BoundedDerivatives T u p)
    (hL2Deriv : ∀ σ ∈ Set.Ioo (0 : ℝ) T,
      Energy.HasL2DerivWithinAt u (timeDeriv u σ) (Set.Ioo (0 : ℝ) T) σ)
    (hDissInt : ∀ {s t : ℝ}, 0 < s → t < T →
      IntervalIntegrable (fun σ => Energy.dissipation (u σ)) volume s t) :
    EnergyHypotheses ν T u p where
  mem_L2 := fun _σ hσ => mem_L2_of_bridges h hR hσ
  mem_L2_timeDeriv := fun _σ hσ => mem_L2_timeDeriv_of_bridges h hR hσ
  hasL2Deriv := hL2Deriv
  spatialIntegrability := fun _σ hσ => spatialIntegrability_of_bridges h hR hB hσ
  dissipation_intervalIntegrable := hDissInt

end EnergyHypotheses

/-- **The energy identity, assembled from the regularity package.**  Corollary of
`EnergyHypotheses.of_regularity` and `EnergyIdentity.energy_identity`: for a
classical solution of `eq:NS` carrying `RegularityPackage`, `BoundedDerivatives`,
and the two explicit hypotheses `hL2Deriv`/`hDissInt` of `of_regularity`, the
manuscript's `prop:energy` identity `eq:energy` holds on `[s,t] ⊆ (0,T)`. -/
theorem energy_identity_of_regularity {ν T : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space}
    {p : ℝ → Space → ℝ} (h : IsClassicalSolution ν u₀ T u p) (hR : RegularityPackage T u p)
    (hB : BoundedDerivatives T u p)
    (hL2Deriv : ∀ σ ∈ Set.Ioo (0 : ℝ) T,
      Energy.HasL2DerivWithinAt u (timeDeriv u σ) (Set.Ioo (0 : ℝ) T) σ)
    (hDissInt : ∀ {s t : ℝ}, 0 < s → t < T →
      IntervalIntegrable (fun σ => Energy.dissipation (u σ)) volume s t)
    {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (htT : t < T) :
    (1 / 2) * (∫ x, ‖u t x‖ ^ 2) + ν * (∫ τ in s..t, ∫ x, enstrophyDensity (u τ) x)
      = (1 / 2) * ∫ x, ‖u s x‖ ^ 2 :=
  energy_identity h (EnergyHypotheses.of_regularity h hR hB hL2Deriv hDissInt) hs0 hst htT

end EnergyIdentity
end NavierFormal

end
