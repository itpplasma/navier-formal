import NavierFormal.Basic
import NavierFormal.Calculus
import NavierFormal.SolutionClass
import NavierFormal.IBP
import NavierFormal.Interpolation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Class bridges: boundedness, the Lipschitz bridge, and the `IBP` integrability hypotheses

This module discharges PLAN task FC5 ("class bridges").  It supplies the second half of
the manuscript's regularity package `R` (recorded after `premise:local`,
`../navier-paper/main.tex`), which `NavierFormal.RegularityPackage` (`SolutionClass.lean`)
does **not** carry:

* `premise:local` states that `u(t), p(t) ∈ H^k` for all `k`, uniformly on compact time
  intervals (this half **is** `RegularityPackage`), *and* that all derivatives
  `∂ₜʲ∂ₓᵅu, ∂ₜʲ∂ₓᵅp` are bounded on `[0,T]×ℝ³` (this half is **missing** from the existing
  statement surface and is supplied here as `NavierFormal.BoundedDerivatives`).

From `IsClassicalSolution`, `RegularityPackage`, and `BoundedDerivatives` together, this
module derives:

1. `NavierFormal.lipschitzWith_of_bounded_fderiv` and
   `NavierFormal.IsClassicalSolution.lipschitzWith_velocity` — the bridge
   "classical solution on `[0,T)` ⇒ `u(t)` globally Lipschitz" requested by
   `docs/verification-status.md`'s solution-class gap, using `prop:localtheory`(iii)
   (the `k = 1, j = 0` instance of the boundedness clause of `R`).
2. The `L¹` integrability hypotheses of `NavierFormal.IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence`,
   `NavierFormal.IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity`, and
   `NavierFormal.IBP.integral_inner_convection_eq_zero`, derived from `RegularityPackage`'s
   `L²` bounds via Cauchy–Schwarz/Hölder, and from `BoundedDerivatives`'s uniform bounds via
   "bounded times `L¹`", at one fixed interior time `t`.

## Conventions

* `IBP`'s hypotheses are stated through the **operator** norm `‖fderiv ℝ v x‖` (and, for the
  second derivative, `‖fderiv ℝ (fderiv ℝ v) x‖`), while `RegularityPackage`/`BoundedDerivatives`
  are stated through `iteratedFDeriv`.  The exact bridges
  `NavierFormal.norm_gradient_eq_norm_fderiv`, Mathlib's `norm_iteratedFDeriv_one`, and
  `NavierFormal.norm_iteratedFDeriv_two_eq_norm_fderiv_fderiv` convert between the two without
  loss, so every integrability bridge below is provided in the exact hypothesis shape `IBP`
  needs; the `enstrophyDensity` term is the Frobenius density already used by `IBP`, related
  to the operator norm through `NavierFormal.frobeniusNormSq_le_three_mul`
  (`NavierFormal.Calculus`).
* All integrability bridges are stated at one fixed interior time `0 < t < T`; no claim is
  made about integrability uniform in `t`, matching how `IBP`'s hypotheses are used pointwise
  in time by the manuscript's `prop:energy` and `prop:pressure`.

Nothing in this file is a theorem about the Millennium problem.
-/

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff Gradient Laplacian

noncomputable section

namespace NavierFormal

/-! ## `BoundedDerivatives`: the missing half of the regularity package `R` -/

/-- The boundedness half of the manuscript's regularity package `R`, recorded after
`premise:local` alongside `RegularityPackage`'s `H^k` bounds: on every compact time slab
`[0,T'] × ℝ³` with `T' < T`, every mixed derivative `∂ₜʲ∂ₓᵏu` and `∂ₜʲ∂ₓᵏp` is (uniformly)
bounded.  `RegularityPackage` alone (the `L²` half) does not imply this: `H^k` membership
is an integral bound, not a pointwise one.  This is exactly the clause of `premise:local`
that `docs/verification-status.md`'s solution-class gap identifies as missing from the
Lean statement surface, and the hypothesis used by `prop:localtheory`(iii). -/
structure BoundedDerivatives (T : ℝ) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) : Prop where
  /-- Every mixed derivative of the velocity is uniformly bounded on every compact
  time subinterval. -/
  bound_u : ∀ (j k : ℕ) (T' : ℝ), 0 ≤ T' → T' < T → ∃ C : ℝ, 0 ≤ C ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ x : Space,
      ‖iteratedFDeriv ℝ k (timeDerivIter j u t) x‖ ≤ C
  /-- Every mixed derivative of the pressure is uniformly bounded on every compact
  time subinterval. -/
  bound_p : ∀ (j k : ℕ) (T' : ℝ), 0 ≤ T' → T' < T → ∃ C : ℝ, 0 ≤ C ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ x : Space,
      ‖iteratedFDeriv ℝ k (timeDerivIter j p t) x‖ ≤ C

/-- `BoundedDerivatives` restricts to shorter intervals, alongside `RegularityPackage.mono`
and `IsClassicalSolution.mono`. -/
theorem BoundedDerivatives.mono {T T' : ℝ} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : BoundedDerivatives T u p) (hT : T' ≤ T) : BoundedDerivatives T' u p where
  bound_u := fun j k S hS hST => h.bound_u j k S hS (lt_of_lt_of_le hST hT)
  bound_p := fun j k S hS hST => h.bound_p j k S hS (lt_of_lt_of_le hST hT)

/-- Specialization of `BoundedDerivatives.bound_u` to the compact interval `[0,t]`, extracting
the pointwise bound at `t` itself. -/
theorem BoundedDerivatives.bound_u_at {T : ℝ} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hbd : BoundedDerivatives T u p) (j k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space, ‖iteratedFDeriv ℝ k (timeDerivIter j u t) x‖ ≤ C := by
  obtain ⟨C, hC0, hbound⟩ := hbd.bound_u j k t ht0 htT
  exact ⟨C, hC0, fun x => hbound t ⟨ht0, le_rfl⟩ x⟩

/-- Specialization of `BoundedDerivatives.bound_p` to the compact interval `[0,t]`, extracting
the pointwise bound at `t` itself. -/
theorem BoundedDerivatives.bound_p_at {T : ℝ} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hbd : BoundedDerivatives T u p) (j k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space, ‖iteratedFDeriv ℝ k (timeDerivIter j p t) x‖ ≤ C := by
  obtain ⟨C, hC0, hbound⟩ := hbd.bound_p j k t ht0 htT
  exact ⟨C, hC0, fun x => hbound t ⟨ht0, le_rfl⟩ x⟩

/-- Specialization of `RegularityPackage` to the compact interval `[0,t]`, extracting
the `L²` bound at `t` itself for the velocity. -/
theorem RegularityPackage.eLpNorm_two_lt_top_u {T : ℝ} {u : ℝ → Space → Space}
    {p : ℝ → Space → ℝ} (hreg : RegularityPackage T u p) (j k : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t < T) :
    eLpNorm (iteratedFDeriv ℝ k (timeDerivIter j u t)) 2 volume < ⊤ := by
  obtain ⟨C, hCtop, hbound⟩ := hreg j k t ht0 htT
  exact (hbound t ⟨ht0, le_rfl⟩).1.trans_lt hCtop

/-- Specialization of `RegularityPackage` to the compact interval `[0,t]`, extracting
the `L²` bound at `t` itself for the pressure. -/
theorem RegularityPackage.eLpNorm_two_lt_top_p {T : ℝ} {u : ℝ → Space → Space}
    {p : ℝ → Space → ℝ} (hreg : RegularityPackage T u p) (j k : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t < T) :
    eLpNorm (iteratedFDeriv ℝ k (timeDerivIter j p t)) 2 volume < ⊤ := by
  obtain ⟨C, hCtop, hbound⟩ := hreg j k t ht0 htT
  exact (hbound t ⟨ht0, le_rfl⟩).2.trans_lt hCtop

/-- `1 ≤ ∞` in the smoothness-order lattice `WithTop ℕ∞`, alongside
`IsClassicalSolution.two_le_infty` (`SolutionClass.lean`). -/
theorem one_le_infty : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.2 le_top

/-! ## Elementary norm bridges: `iteratedFDeriv`, `fderiv`, and `gradient` -/

/-- The second iterated Fréchet derivative agrees in norm with the double `fderiv`, exactly
what `IBP.norm_laplacian_le` and `IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity`
are stated through.  Proof: `norm_iteratedFDeriv_fderiv` at `n = 1` composed with
`norm_iteratedFDeriv_one`. -/
theorem norm_iteratedFDeriv_two_eq_norm_fderiv_fderiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Space → F) (x : Space) :
    ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

/-- The gradient of a scalar field agrees in norm with its Fréchet derivative: `∇` is the
Riesz representative of `fderiv ℝ`, and `y ↦ ⟪y, ·⟫` (`innerSL`) is a linear isometry. -/
theorem norm_gradient_eq_norm_fderiv (q : Space → ℝ) (x : Space) :
    ‖gradient q x‖ = ‖fderiv ℝ q x‖ := by
  have heq : fderiv ℝ q x = innerSL ℝ (gradient q x) := by
    apply ContinuousLinearMap.ext
    intro h
    rw [innerSL_apply_apply]
    exact (inner_gradient_apply q x h).symm
  rw [heq, innerSL_apply_norm]

/-- `eLpNorm` transfers along the `iteratedFDeriv 0`/identity norm equality. -/
theorem eLpNorm_iteratedFDeriv_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) : eLpNorm (iteratedFDeriv ℝ 0 f) 2 volume = eLpNorm f 2 volume :=
  eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero)

/-- `eLpNorm` transfers along the `iteratedFDeriv 1`/`fderiv` norm equality
(Mathlib's `norm_iteratedFDeriv_one`). -/
theorem eLpNorm_iteratedFDeriv_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) :
    eLpNorm (iteratedFDeriv ℝ 1 f) 2 volume = eLpNorm (fderiv ℝ f) 2 volume :=
  eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_one f)

/-- `eLpNorm` transfers along the `iteratedFDeriv 1`/`gradient` norm equality, for scalar
fields. -/
theorem eLpNorm_iteratedFDeriv_one_gradient (q : Space → ℝ) :
    eLpNorm (iteratedFDeriv ℝ 1 q) 2 volume = eLpNorm (gradient q) 2 volume :=
  eLpNorm_congr_norm_ae
    (Filter.Eventually.of_forall fun x => (norm_iteratedFDeriv_one q).trans
      (norm_gradient_eq_norm_fderiv q x).symm)

/-! ## The Lipschitz bridge -/

/-- **The Lipschitz bridge from a bounded derivative.**  If `f : ℝ³ → F` is differentiable
everywhere with `‖fderiv ℝ f x‖ ≤ C` for every `x`, then `f` is `C`-Lipschitz.  This is
Mathlib's mean value inequality `lipschitzWith_of_nnnorm_fderiv_le`, restated with a real (not
`ℝ≥0`) bound and junk value `C.toNNReal` when `C < 0` (vacuous, since `‖fderiv ℝ f x‖ ≥ 0`
already forces `0 ≤ C` whenever `F` is nontrivial; no such hypothesis is imposed here). -/
theorem lipschitzWith_of_bounded_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} {C : ℝ} (hC : 0 ≤ C) (hf : Differentiable ℝ f)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) : LipschitzWith C.toNNReal f :=
  lipschitzWith_of_nnnorm_fderiv_le hf fun x => by
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC]
    exact hb x

/-- **The solution-class gap of `docs/verification-status.md`, closed**: a classical solution's
velocity is globally Lipschitz at every interior time, from the boundedness clause of the
regularity package `R` (`prop:localtheory`(iii), here `BoundedDerivatives`).  This is the
`j = 0, k = 1` instance of `BoundedDerivatives.bound_u`, transported from `iteratedFDeriv ℝ 1`
to `fderiv ℝ` by `norm_iteratedFDeriv_one` and fed to `lipschitzWith_of_bounded_fderiv`. -/
theorem IsClassicalSolution.lipschitzWith_velocity {ν T : ℝ} {u₀ : Space → Space}
    {u : ℝ → Space → Space} {p : ℝ → Space → ℝ} (h : IsClassicalSolution ν u₀ T u p)
    (hb : BoundedDerivatives T u p) {t : ℝ} (ht : 0 < t) (ht' : t < T) :
    ∃ C, LipschitzWith C (u t) := by
  obtain ⟨C, hC0, hbound⟩ := hb.bound_u_at 0 1 ht.le ht'
  refine ⟨C.toNNReal, lipschitzWith_of_bounded_fderiv hC0 (fun x => h.differentiableAt_velocity ht ht' x)
    fun x => ?_⟩
  have := hbound x
  simpa only [timeDerivIter_zero, norm_iteratedFDeriv_one] using this

/-! ## `IBP` integrability bridges at a fixed interior time -/

section Integrability

/-- Hölder's inequality at the exponents `(2,2,1)`, as an `ENNReal.HolderTriple` instance:
`2⁻¹ + 2⁻¹ = 1⁻¹`. -/
instance holderTriple_two_two_one : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
  ⟨by simp [ENNReal.inv_two_add_inv_two]⟩

/-- Cauchy–Schwarz for two real-valued `L²` functions: their pointwise product is `L¹`. -/
theorem integrable_mul_of_memLp_two {f g : Space → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : Integrable (fun x => f x * g x) volume := by
  have h : MemLp (fun x => g x * f x) 1 volume := hf.mul' hg
  rw [← memLp_one_iff_integrable]
  simpa [mul_comm] using h

variable {ν T : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ} {t : ℝ}
variable (h : IsClassicalSolution ν u₀ T u p) (hreg : RegularityPackage T u p)
variable (hbd : BoundedDerivatives T u p) (ht : 0 < t) (htT : t < T)

include h ht htT in
/-- The velocity of a classical solution is jointly `C^∞` (in particular of every finite
order) in space at a fixed interior time. -/
theorem IsClassicalSolution.contDiff_velocity : ContDiff ℝ ∞ (u t) :=
  contDiff_iff_contDiffAt.2 fun x => h.contDiffAt_velocity ht htT x

include h ht htT in
/-- The pressure of a classical solution is jointly `C^∞` (in particular of every finite
order) in space at a fixed interior time. -/
theorem IsClassicalSolution.contDiff_pressure : ContDiff ℝ ∞ (p t) :=
  contDiff_iff_contDiffAt.2 fun x => h.contDiffAt_pressure ht htT x

include h ht htT in
/-- The pressure of a classical solution is continuous in space at each interior time
(the pressure counterpart of `IsClassicalSolution.continuous_velocity`, absent from
`SolutionClass.lean`). -/
theorem IsClassicalSolution.continuous_pressure : Continuous (p t) :=
  continuous_iff_continuousAt.2 fun x => (h.differentiableAt_pressure ht htT x).continuousAt

include h hreg ht htT in
/-- The regularity package's `H^0 = L^2` bound: `u(t) ∈ L²(ℝ³)`. -/
theorem IsClassicalSolution.memLp_two_velocity : MemLp (u t) 2 volume := by
  refine ⟨(h.continuous_velocity ht htT).aestronglyMeasurable, ?_⟩
  have := hreg.eLpNorm_two_lt_top_u 0 0 ht.le htT
  rwa [timeDerivIter_zero, eLpNorm_iteratedFDeriv_zero] at this

include h hreg ht htT in
/-- The regularity package's `H^1` bound, in `fderiv` form: `∇u(t) ∈ L²(ℝ³)`. -/
theorem IsClassicalSolution.memLp_two_fderiv_velocity : MemLp (fderiv ℝ (u t)) 2 volume := by
  have hcd : ContDiff ℝ 1 (u t) := (h.contDiff_velocity ht htT).of_le one_le_infty
  refine ⟨(hcd.continuous_fderiv one_ne_zero).aestronglyMeasurable, ?_⟩
  have := hreg.eLpNorm_two_lt_top_u 0 1 ht.le htT
  rwa [timeDerivIter_zero, eLpNorm_iteratedFDeriv_one] at this

include h hreg ht htT in
/-- The regularity package's `H^2` bound, in `iteratedFDeriv` form: `D²u(t) ∈ L²(ℝ³)`. -/
theorem IsClassicalSolution.memLp_two_iteratedFDeriv_two_velocity :
    MemLp (fun x => iteratedFDeriv ℝ 2 (u t) x) 2 volume := by
  have hcd : ContDiff ℝ 2 (u t) := (h.contDiff_velocity ht htT).of_le IsClassicalSolution.two_le_infty
  refine ⟨(hcd.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable, ?_⟩
  have := hreg.eLpNorm_two_lt_top_u 0 2 ht.le htT
  rwa [timeDerivIter_zero] at this

include h hreg ht htT in
/-- The regularity package's `H^0 = L^2` bound for the pressure: `p(t) ∈ L²(ℝ³)`. -/
theorem IsClassicalSolution.memLp_two_pressure : MemLp (p t) 2 volume := by
  refine ⟨(h.continuous_pressure ht htT).aestronglyMeasurable, ?_⟩
  have := hreg.eLpNorm_two_lt_top_p 0 0 ht.le htT
  rwa [timeDerivIter_zero, eLpNorm_iteratedFDeriv_zero] at this

include h hreg ht htT in
/-- The regularity package's `H^1` bound for the pressure, in `gradient` form:
`∇p(t) ∈ L²(ℝ³)`. -/
theorem IsClassicalSolution.memLp_two_gradient_pressure : MemLp (gradient (p t)) 2 volume := by
  have hcd : ContDiff ℝ 1 (p t) := (h.contDiff_pressure ht htT).of_le one_le_infty
  have hfd : Continuous (fderiv ℝ (p t)) := hcd.continuous_fderiv one_ne_zero
  have hcont : Continuous (gradient (p t)) := by
    have heq : gradient (p t) = fun x => ∑ i : Fin 3, fderiv ℝ (p t) x (e i) • e i := by
      funext x
      rw [← sum_smul_e (gradient (p t) x)]
      exact Finset.sum_congr rfl fun i _ => by rw [gradient_component]
    rw [heq]
    exact continuous_finsetSum _ fun i _ =>
      ((ContinuousLinearMap.apply ℝ ℝ (e i)).continuous.comp hfd).smul continuous_const
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have := hreg.eLpNorm_two_lt_top_p 0 1 ht.le htT
  rwa [timeDerivIter_zero, eLpNorm_iteratedFDeriv_one_gradient] at this

include h hreg ht htT in
/-- **`IBP` integrability hypothesis, primitive form**: `‖u(t)‖‖∇u(t)‖ ∈ L¹(ℝ³)`.  This is
`IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity`'s first hypothesis and, at
`p = |u|²`, the first hypothesis of `IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence`
used by `IBP.integral_inner_convection_eq_zero`. -/
theorem IsClassicalSolution.integrable_norm_velocity_mul_norm_fderiv :
    Integrable (fun x => ‖u t x‖ * ‖fderiv ℝ (u t) x‖) volume :=
  integrable_mul_of_memLp_two (h.memLp_two_velocity hreg ht htT).norm
    (h.memLp_two_fderiv_velocity hreg ht htT).norm

include h hreg ht htT in
/-- **`IBP` integrability hypothesis**: the enstrophy density `‖∇u(t)‖²_F ∈ L¹(ℝ³)`.  This is
`IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity`'s second hypothesis, from
`u(t) ∈ H¹` via `frobeniusNormSq_le_three_mul` (Cauchy–Schwarz on the Frobenius density). -/
theorem IsClassicalSolution.integrable_enstrophyDensity_velocity :
    Integrable (enstrophyDensity (u t)) volume := by
  have hcd : ContDiff ℝ 1 (u t) := (h.contDiff_velocity ht htT).of_le one_le_infty
  have hmeas : AEStronglyMeasurable (enstrophyDensity (u t)) volume :=
    (IBP.continuous_enstrophyDensity hcd).aestronglyMeasurable
  have hsq : Integrable (fun x => ‖fderiv ℝ (u t) x‖ ^ 2) volume :=
    (h.memLp_two_fderiv_velocity hreg ht htT).norm.integrable_sq
  refine (hsq.const_mul 3).mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (enstrophyDensity_nonneg _ _)]
  exact frobeniusNormSq_le_three_mul _

include h hreg ht htT in
/-- **`IBP` integrability hypothesis, second-derivative form (Frobenius/`iteratedFDeriv`
side)**: `‖u(t)‖‖D²u(t)‖ ∈ L¹(ℝ³)`, the `iteratedFDeriv` form of
`IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity`'s third hypothesis. -/
theorem IsClassicalSolution.integrable_norm_velocity_mul_norm_iteratedFDeriv_two :
    Integrable (fun x => ‖u t x‖ * ‖iteratedFDeriv ℝ 2 (u t) x‖) volume :=
  integrable_mul_of_memLp_two (h.memLp_two_velocity hreg ht htT).norm
    (h.memLp_two_iteratedFDeriv_two_velocity hreg ht htT).norm

include h hreg ht htT in
/-- **`IBP` integrability hypothesis, second-derivative form (operator-norm side)**:
`‖u(t)‖‖fderiv ℝ (fderiv ℝ u(t))‖ ∈ L¹(ℝ³)`, exactly
`IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity`'s third hypothesis, related to
`integrable_norm_velocity_mul_norm_iteratedFDeriv_two` by
`norm_iteratedFDeriv_two_eq_norm_fderiv_fderiv`. -/
theorem IsClassicalSolution.integrable_norm_velocity_mul_norm_fderiv_fderiv :
    Integrable (fun x => ‖u t x‖ * ‖fderiv ℝ (fderiv ℝ (u t)) x‖) volume := by
  refine (h.integrable_norm_velocity_mul_norm_iteratedFDeriv_two hreg ht htT).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_iteratedFDeriv_two_eq_norm_fderiv_fderiv]

include h hreg ht htT in
/-- **`IBP` integrability hypothesis**: `‖p(t)‖‖u(t)‖ ∈ L¹(ℝ³)`, the first hypothesis of
`IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence`. -/
theorem IsClassicalSolution.integrable_norm_pressure_mul_norm_velocity :
    Integrable (fun x => ‖p t x‖ * ‖u t x‖) volume :=
  integrable_mul_of_memLp_two (h.memLp_two_pressure hreg ht htT).norm
    (h.memLp_two_velocity hreg ht htT).norm

include h hreg ht htT in
/-- **`IBP` integrability hypothesis**: `‖p(t)‖‖∇u(t)‖ ∈ L¹(ℝ³)`, the second hypothesis of
`IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence`. -/
theorem IsClassicalSolution.integrable_norm_pressure_mul_norm_fderiv_velocity :
    Integrable (fun x => ‖p t x‖ * ‖fderiv ℝ (u t) x‖) volume :=
  integrable_mul_of_memLp_two (h.memLp_two_pressure hreg ht htT).norm
    (h.memLp_two_fderiv_velocity hreg ht htT).norm

include h hreg ht htT in
/-- **`IBP` integrability hypothesis**: `‖∇p(t)‖‖u(t)‖ ∈ L¹(ℝ³)`, the third hypothesis of
`IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence`. -/
theorem IsClassicalSolution.integrable_norm_gradient_pressure_mul_norm_velocity :
    Integrable (fun x => ‖gradient (p t) x‖ * ‖u t x‖) volume :=
  integrable_mul_of_memLp_two (h.memLp_two_gradient_pressure hreg ht htT).norm
    (h.memLp_two_velocity hreg ht htT).norm

include h hbd ht htT in
/-- The velocity of a classical solution is bounded (pointwise) at a fixed interior time, the
`j = 0, k = 0` instance of the boundedness clause of `R`.  `h` is not used in the proof (the
bound is a property of `BoundedDerivatives` alone); it is kept as a hypothesis so that this
lemma is available through `h.exists_bound_velocity`, matching the dot-notation style of the
other bridges in this section. -/
theorem IsClassicalSolution.exists_bound_velocity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖u t x‖ ≤ C := by
  obtain ⟨C, hC0, hbound⟩ := hbd.bound_u_at 0 0 ht.le htT
  refine ⟨C, hC0, fun x => ?_⟩
  simpa only [timeDerivIter_zero, norm_iteratedFDeriv_zero] using hbound x

include h hreg hbd ht htT in
/-- **`IBP` integrability hypothesis, "bounded times `L¹`" form**: `‖u(t)‖³ ∈ L¹(ℝ³)`, the
first hypothesis of `IBP.integral_inner_convection_eq_zero`. -/
theorem IsClassicalSolution.integrable_norm_velocity_pow_three :
    Integrable (fun x => ‖u t x‖ ^ 3) volume := by
  obtain ⟨C, hC0, hbound⟩ := h.exists_bound_velocity hbd ht htT
  have hmeas : AEStronglyMeasurable (fun x => ‖u t x‖ ^ 3) volume :=
    ((h.continuous_velocity ht htT).norm.pow 3).aestronglyMeasurable
  have hsq : Integrable (fun x => ‖u t x‖ ^ 2) volume :=
    (h.memLp_two_velocity hreg ht htT).norm.integrable_sq
  refine (hsq.const_mul C).mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖u t x‖ ^ 3 = ‖u t x‖ * ‖u t x‖ ^ 2 := by ring
    _ ≤ C * ‖u t x‖ ^ 2 := by gcongr; exact hbound x

include h hreg hbd ht htT in
/-- **`IBP` integrability hypothesis, "bounded times `L¹`" form**: `‖u(t)‖²‖∇u(t)‖ ∈ L¹(ℝ³)`,
the second hypothesis of `IBP.integral_inner_convection_eq_zero`. -/
theorem IsClassicalSolution.integrable_norm_velocity_sq_mul_norm_fderiv :
    Integrable (fun x => ‖u t x‖ ^ 2 * ‖fderiv ℝ (u t) x‖) volume := by
  obtain ⟨C, hC0, hbound⟩ := h.exists_bound_velocity hbd ht htT
  have hmeas : AEStronglyMeasurable (fun x => ‖u t x‖ ^ 2 * ‖fderiv ℝ (u t) x‖) volume := by
    have hcd : ContDiff ℝ 1 (u t) := (h.contDiff_velocity ht htT).of_le one_le_infty
    exact ((h.continuous_velocity ht htT).norm.pow 2).mul
      (hcd.continuous_fderiv one_ne_zero).norm |>.aestronglyMeasurable
  have hL1 : Integrable (fun x => ‖u t x‖ * ‖fderiv ℝ (u t) x‖) volume :=
    h.integrable_norm_velocity_mul_norm_fderiv hreg ht htT
  refine (hL1.const_mul C).mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖u t x‖ ^ 2 * ‖fderiv ℝ (u t) x‖)]
  calc ‖u t x‖ ^ 2 * ‖fderiv ℝ (u t) x‖ = ‖u t x‖ * (‖u t x‖ * ‖fderiv ℝ (u t) x‖) := by ring
    _ ≤ C * (‖u t x‖ * ‖fderiv ℝ (u t) x‖) := by gcongr; exact hbound x

include h hreg hbd ht htT in
/-- **`MemLp (u t) 3`, from `L² ∩ L^∞` interpolation.**  Used wherever the manuscript needs the
critical `L³` norm of a classical solution at an interior time, e.g. `CriticalBound`. -/
theorem IsClassicalSolution.memLp_three_velocity : MemLp (u t) 3 volume := by
  obtain ⟨C, hC0, hbound⟩ := h.exists_bound_velocity hbd ht htT
  have hmeasu : AEStronglyMeasurable (u t) volume :=
    (h.continuous_velocity ht htT).aestronglyMeasurable
  have htop : MemLp (u t) ⊤ volume :=
    memLp_top_of_bound hmeasu C (Filter.Eventually.of_forall hbound)
  have h2 : MemLp (u t) 2 volume := h.memLp_two_velocity hreg ht htT
  refine ⟨hmeasu, ?_⟩
  have hle := eLpNorm_interpolate_top (μ := (volume : Measure Space)) (f := u t)
    htop.eLpNorm_lt_top.ne (p := 2) (r := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine hle.trans_lt ?_
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_lt_top.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) htop.eLpNorm_lt_top.ne)

include h hreg ht htT in
/-- **`IBP` integrability hypothesis, viscous form**: `‖Δu(t)‖² ∈ L¹(ℝ³)`.  Used wherever the
manuscript's enstrophy balance needs the viscous dissipation term in `L¹` directly (rather
than through `‖u‖‖D²u‖`), via `IBP.norm_laplacian_le` and
`norm_iteratedFDeriv_two_eq_norm_fderiv_fderiv`. -/
theorem IsClassicalSolution.integrable_norm_laplacian_velocity_sq :
    Integrable (fun x => ‖Δ (u t) x‖ ^ 2) volume := by
  have hcd : ContDiff ℝ 2 (u t) := (h.contDiff_velocity ht htT).of_le IsClassicalSolution.two_le_infty
  have hmeas : AEStronglyMeasurable (fun x => ‖Δ (u t) x‖ ^ 2) volume :=
    ((IBP.continuous_laplacian hcd).norm.pow 2).aestronglyMeasurable
  have hD2 : Integrable (fun x => ‖iteratedFDeriv ℝ 2 (u t) x‖ ^ 2) volume :=
    (h.memLp_two_iteratedFDeriv_two_velocity hreg ht htT).norm.integrable_sq
  refine (hD2.const_mul 9).mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb : ‖Δ (u t) x‖ ≤ 3 * ‖fderiv ℝ (fderiv ℝ (u t)) x‖ := IBP.norm_laplacian_le (u t) x
  have heq : ‖fderiv ℝ (fderiv ℝ (u t)) x‖ = ‖iteratedFDeriv ℝ 2 (u t) x‖ :=
    (norm_iteratedFDeriv_two_eq_norm_fderiv_fderiv (u t) x).symm
  calc ‖Δ (u t) x‖ ^ 2 ≤ (3 * ‖fderiv ℝ (fderiv ℝ (u t)) x‖) ^ 2 := by gcongr
    _ = 9 * ‖iteratedFDeriv ℝ 2 (u t) x‖ ^ 2 := by rw [heq]; ring

end Integrability

end NavierFormal

end
