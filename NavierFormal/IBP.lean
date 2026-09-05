import NavierFormal.Basic
import NavierFormal.Calculus
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Integration by parts on `ℝ³` (manuscript `prop:energy`, `prop:enstrophy`)

This module is the design record's module `Calculus/IBP`
(`itpplasma/navier:research/evidence/cp01-lean-statement-design.md` §5, order 1).
It wraps Mathlib's integration-by-parts theorem for Fréchet derivatives on a
finite-dimensional real vector space with an additive Haar measure
(`integral_bilinear_fderiv_right_eq_neg_left_of_integrable` and its relatives in
`Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`) into the four
identities the manuscript's energy and enstrophy computations use on
`NavierFormal.Space = EuclideanSpace ℝ (Fin 3)`:

1. `integral_divergence_eq_zero` — `∫ ∇·F = 0`;
2. `integral_fderiv_apply_eq_neg_integral_mul_divergence` —
   `∫ ⟪u, ∇p⟫ = -∫ p (∇·u)`, the step that removes the pressure from the energy
   balance of `prop:energy` and produces the pressure term `P₃` of
   `prop:pressure`;
3. `integral_inner_laplacian_eq_neg_integral_enstrophyDensity` —
   `∫ ⟪u, Δu⟫ = -∫ |∇u|²`, the viscous term of `prop:energy` (and, applied to
   `∇u`, of `prop:enstrophy`);
4. `integral_inner_convection_eq_zero` — `∫ ⟪u, (u·∇)u⟫ = 0` for a
   divergence-free field, the cancellation of the transport term in
   `prop:energy`.

## Conventions

* `‖∇u‖²` is the **Frobenius** (Hilbert–Schmidt) square
  `NavierFormal.enstrophyDensity u x = ∑ⱼ ‖∂ⱼ u(x)‖² = ∑ᵢⱼ (∂ⱼ uᵢ(x))²`
  (`NavierFormal.Calculus`), *not* the operator norm of `fderiv ℝ u x`
  (design decision D7, fidelity risk R-NORM): identity (3) is false with the
  operator norm.
* `⟪·,·⟫` is the real inner product of `Space`, `Δ` is Mathlib's
  `InnerProductSpace.laplacian`, which on an orthonormal basis is
  `∑ᵢ ∂ᵢ² u` (no sign, no factor `1/2`).
* `∇·u = NavierFormal.divergence u x = ∑ᵢ ∂ᵢ uᵢ(x)` (`NavierFormal.Calculus`),
  written through the Fréchet derivative as `∑ᵢ ⟪eᵢ, fderiv ℝ u x eᵢ⟫`, with
  `fderiv`'s junk value `0` where `u` is not differentiable.

## Integrability

Mathlib's integration by parts is the "integrable function with integrable
derivative" version, **not** the "vanishing at infinity" version; it has no
boundary term and needs the products appearing on both sides to be integrable.
Every such requirement is carried as an explicit hypothesis below and none is
hidden: the classical solution class of the manuscript does not by itself
supply them, and the callers (`Energy.lean`, `Pressure.lean`) must discharge
them from the regularity package.  Concretely, the four identities ask for

1. `Integrable F` and `Integrable (fderiv ℝ F)`;
2. `‖p‖‖u‖`, `‖p‖‖∇u‖`, `‖∇p‖‖u‖` in `L¹`;
3. `u` of class `C²` with `‖u‖‖∇u‖`, `‖∇u‖²_F` and `‖u‖‖D²u‖` in `L¹`;
4. `u` of class `C¹` with `‖u‖³` and `‖u‖²‖∇u‖` in `L¹`.

## Namespace note

The basis `e`, the divergence, and the Frobenius density are the definitions of
`NavierFormal.Calculus` (`NavierFormal.e`, `NavierFormal.divergence`,
`NavierFormal.enstrophyDensity`); this module only adds the integration-by-parts
wrappers, in the nested namespace `NavierFormal.IBP`.

Nothing here is a theorem about the Millennium problem.
-/

open MeasureTheory InnerProductSpace Laplacian
open scoped RealInnerProductSpace

noncomputable section

namespace NavierFormal
namespace IBP

/-! ## Coordinates on `ℝ³` -/

/-- The `i`-th coordinate functional on `ℝ³` as a continuous linear map,
`coord i y = ⟪eᵢ, y⟫ = yᵢ`.  It is only a bookkeeping device for extracting
components of vector fields inside integrals. -/
def coord (i : Fin 3) : Space →L[ℝ] ℝ := innerSL ℝ (e i)

@[simp] theorem coord_apply (i : Fin 3) (y : Space) : coord i y = y i := by
  simp [coord, inner_e]

/-- Every coordinate is dominated by the Euclidean norm, `|yᵢ| ≤ ‖y‖`. -/
theorem abs_coord_le (i : Fin 3) (y : Space) : |y i| ≤ ‖y‖ := by
  have h : |⟪e i, y⟫| ≤ ‖e i‖ * ‖y‖ := abs_real_inner_le_norm (e i) y
  simpa [inner_e] using h

/-! ## Elementary bounds on the divergence -/

/-- The divergence is dominated by three times the operator norm of the
Jacobian, `|∇·F| ≤ 3 ‖fderiv ℝ F x‖`.  This is the crude bound used to turn the
callers' `L¹` hypotheses on `‖p‖ ‖∇u‖` into integrability of `p (∇·u)`. -/
theorem abs_divergence_le (F : Space → Space) (x : Space) :
    |divergence F x| ≤ 3 * ‖fderiv ℝ F x‖ := by
  have h : ∀ j : Fin 3, |(fderiv ℝ F x (e j)) j| ≤ ‖fderiv ℝ F x‖ := by
    intro j
    refine (abs_coord_le j _).trans ?_
    simpa using (fderiv ℝ F x).le_opNorm (e j)
  rw [divergence_eq_sum_component]
  calc |∑ j : Fin 3, (fderiv ℝ F x (e j)) j| ≤ ∑ j : Fin 3, |(fderiv ℝ F x (e j)) j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, ‖fderiv ℝ F x‖ := Finset.sum_le_sum fun j _ => h j
    _ = 3 * ‖fderiv ℝ F x‖ := by simp [Finset.sum_const]

/-- Differentiating a component: `∂ᵥ(Fᵢ) = (∂ᵥF)ᵢ`. -/
theorem fderiv_coord {F : Space → Space} (hF : Differentiable ℝ F) (i : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => (F y) i) x v = (fderiv ℝ F x v) i := by
  have h := ((coord i).hasFDerivAt.comp x (hF x).hasFDerivAt).fderiv
  simp only [Function.comp_def, coord_apply] at h
  rw [h]
  simp

/-- Continuity of the divergence for a `C¹` field. -/
theorem continuous_divergence {F : Space → Space} (hF : ContDiff ℝ 1 F) :
    Continuous (divergence F) := by
  rw [show divergence F = fun x => ∑ i : Fin 3, (fderiv ℝ F x (e i)) i from
    funext (divergence_eq_sum_component F)]
  refine continuous_finsetSum _ fun i _ => ?_
  have h : Continuous fun x => coord i (fderiv ℝ F x (e i)) :=
    (coord i).continuous.comp
      ((ContinuousLinearMap.apply ℝ Space (e i)).continuous.comp
        (hF.continuous_fderiv one_ne_zero))
  simpa using h

/-- Continuity of the Frobenius density for a `C¹` field. -/
theorem continuous_enstrophyDensity {F : Space → Space} (hF : ContDiff ℝ 1 F) :
    Continuous (enstrophyDensity F) := by
  unfold enstrophyDensity frobeniusNormSq
  refine continuous_finsetSum _ fun j _ => ?_
  exact (((ContinuousLinearMap.apply ℝ Space (e j)).continuous.comp
    (hF.continuous_fderiv one_ne_zero)).norm).pow 2

/-! ## The basic vanishing-integral lemma -/

/-- **Integration by parts without boundary term, primitive form.**  If a
differentiable map `f : ℝ³ → F` is integrable and its derivative in the fixed
direction `v` is integrable, then `∫ ∂ᵥ f = 0`.

This is Mathlib's `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`
tested against the constant function `1`; the integrability hypotheses are
exactly the ones Mathlib requires (`f` itself integrable, `∂ᵥ f` integrable),
and are *not* the "vanishing at infinity" hypotheses.  Every divergence
identity below is a finite sum of instances of this lemma. -/
theorem integral_fderiv_apply_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (v : Space) (hf : Differentiable ℝ f)
    (hfi : Integrable f volume) (hdf : Integrable (fun x => fderiv ℝ f x v) volume) :
    ∫ x, fderiv ℝ f x v = 0 := by
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := (volume : Measure Space)) (f := fun _ : Space => (1 : ℝ)) (g := f) (v := v)
    (by simp)
    (by simpa using hdf) (by simpa using hfi)
    (fun x _ => differentiableAt_const (1 : ℝ)) (fun x _ => hf x)
  simp at h
  exact h

/-! ## `∫ ∇·F = 0` -/

/-- **The divergence theorem on `ℝ³` without boundary term** (manuscript
`prop:energy`, first step of every integration by parts there).

`∫_{ℝ³} ∇·F = 0` for a differentiable vector field `F : ℝ³ → ℝ³` such that `F`
itself and its Fréchet derivative `x ↦ fderiv ℝ F x` are Bochner integrable.

The exact integrability Mathlib needs is stated, not hidden: `Integrable F`
(the field) and `Integrable (fun x => fderiv ℝ F x)` (the `ℝ³ →L[ℝ] ℝ³`-valued
Jacobian, i.e. all first partial derivatives in `L¹`).  This is Mathlib's
"integrable with integrable derivative" hypothesis set, which is *not*
comparable with "tends to zero at infinity with integrable derivative". -/
theorem integral_divergence_eq_zero {F : Space → Space} (hF : Differentiable ℝ F)
    (hFi : Integrable F volume) (hdF : Integrable (fun x => fderiv ℝ F x) volume) :
    ∫ x, divergence F x = 0 := by
  have hcomp : ∀ i : Fin 3, Integrable (fun x => (fderiv ℝ F x (e i)) i) volume := by
    intro i
    have := ((coord i).comp (ContinuousLinearMap.apply ℝ Space (e i))).integrable_comp hdF
    simpa using this
  have hFcomp : ∀ i : Fin 3, Integrable (fun x => (F x) i) volume := by
    intro i
    have := (coord i).integrable_comp hFi
    simpa using this
  have hsplit : ∫ x, divergence F x
      = ∑ i : Fin 3, ∫ x, (fderiv ℝ F x (e i)) i := by
    simp_rw [divergence_eq_sum_component]
    exact integral_finsetSum (μ := (volume : Measure Space)) (s := Finset.univ)
      (f := fun (i : Fin 3) (x : Space) => (fderiv ℝ F x (e i)) i)
      (fun i _ => hcomp i)
  rw [hsplit]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hzero : ∫ x, fderiv ℝ (fun y => (F y) i) x (e i) = 0 :=
    integral_fderiv_apply_eq_zero (e i)
      (fun x => by
        have h := (coord i).differentiableAt.comp x (hF x)
        simpa [Function.comp_def] using h)
      (hFcomp i)
      (by
        refine (hcomp i).congr (Filter.Eventually.of_forall fun x => ?_)
        exact (fderiv_coord hF i x (e i)).symm)
  rw [← hzero]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (fderiv_coord hF i x (e i)).symm)

/-! ## `∫ ⟪u, ∇p⟫ = -∫ p (∇·u)` -/

/-- Product rule for the divergence, `∇·(p u) = ⟪u, ∇p⟫ + p (∇·u)`, with
`⟪u, ∇p⟫` written as the derivative of `p` in the direction `u` (design
decision D3). -/
theorem divergence_smul {u : Space → Space} {p : Space → ℝ} {x : Space}
    (hu : DifferentiableAt ℝ u x) (hp : DifferentiableAt ℝ p x) :
    divergence (fun y => p y • u y) x = fderiv ℝ p x (u x) + p x * divergence u x := by
  have hd : fderiv ℝ (fun y => p y • u y) x
      = p x • fderiv ℝ u x + (fderiv ℝ p x).smulRight (u x) :=
    (hp.hasFDerivAt.smul hu.hasFDerivAt).fderiv
  have hsum : fderiv ℝ p x (u x) = ∑ i : Fin 3, fderiv ℝ p x (e i) * (u x) i := by
    conv_lhs => rw [← sum_smul_e (u x)]
    rw [map_sum]
    simp [mul_comm]
  simp only [divergence_eq_sum_component, hd, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Integration by parts against the pressure gradient** (manuscript
`prop:energy`: the step `∫ ⟪u, ∇p⟫ = 0` for divergence-free `u`; manuscript
`prop:pressure`: the same identity with the weight `r_ε u` producing `P₃`).

`∫ ⟪u, ∇p⟫ = -∫ p (∇·u)`, where `⟪u, ∇p⟫` is written as `fderiv ℝ p x (u x)`
(design decision D3) and `∇·u` is `divergence u`.

The three integrability hypotheses are exactly what Mathlib's boundary-free
integration by parts requires, expressed through pointwise norm products so
that a caller can discharge them from `Lᵖ` information:
`‖p‖‖u‖`, `‖p‖‖∇u‖` and `‖∇p‖‖u‖` must all be in `L¹(ℝ³)`.  The classical
solution class of the manuscript does not supply them by itself. -/
theorem integral_fderiv_apply_eq_neg_integral_mul_divergence
    {u : Space → Space} {p : Space → ℝ} (hu : ContDiff ℝ 1 u) (hp : ContDiff ℝ 1 p)
    (hpu : Integrable (fun x => ‖p x‖ * ‖u x‖) volume)
    (hpdu : Integrable (fun x => ‖p x‖ * ‖fderiv ℝ u x‖) volume)
    (hdpu : Integrable (fun x => ‖fderiv ℝ p x‖ * ‖u x‖) volume) :
    ∫ x, fderiv ℝ p x (u x) = - ∫ x, p x * divergence u x := by
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hpd : Differentiable ℝ p := hp.differentiable one_ne_zero
  have hducont : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hpdcont : Continuous (fderiv ℝ p) := hp.continuous_fderiv one_ne_zero
  -- the vector field `F = p u`
  set F : Space → Space := fun y => p y • u y with hFdef
  have hFcd : ContDiff ℝ 1 F := hp.smul hu
  have hFd : Differentiable ℝ F := hFcd.differentiable one_ne_zero
  have hFderiv : ∀ x, fderiv ℝ F x = p x • fderiv ℝ u x + (fderiv ℝ p x).smulRight (u x) :=
    fun x => ((hpd x).hasFDerivAt.smul (hud x).hasFDerivAt).fderiv
  have hFi : Integrable F volume := by
    refine hpu.mono' (hFcd.continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    simp [hFdef, norm_smul]
  have hdFi : Integrable (fun x => fderiv ℝ F x) volume := by
    refine (hpdu.add hdpu).mono'
      ((hFcd.continuous_fderiv one_ne_zero).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [hFderiv x]
    simp only [Pi.add_apply]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
  -- integrability of the two terms of the product rule
  have hgrad : Integrable (fun x => fderiv ℝ p x (u x)) volume := by
    refine hdpu.mono' (hpdcont.clm_apply hu.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simpa using (fderiv ℝ p x).le_opNorm (u x)
  have hpdiv : Integrable (fun x => p x * divergence u x) volume := by
    refine (hpdu.const_mul 3).mono'
      (hp.continuous.mul (continuous_divergence hu)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |p x| * |divergence u x| ≤ |p x| * (3 * ‖fderiv ℝ u x‖) := by
          gcongr
          exact abs_divergence_le u x
      _ = 3 * (‖p x‖ * ‖fderiv ℝ u x‖) := by rw [Real.norm_eq_abs]; ring
  -- the divergence theorem applied to `p u`
  have h0 : ∫ x, divergence F x = 0 := integral_divergence_eq_zero hFd hFi hdFi
  have hpt : ∀ x, divergence F x = fderiv ℝ p x (u x) + p x * divergence u x :=
    fun x => divergence_smul (hud x) (hpd x)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hgrad hpdiv] at h0
  linarith

/-! ## The Laplacian in coordinates -/

/-- Mathlib's `InnerProductSpace.laplacian` on `ℝ³` in coordinates,
`Δ F x = ∑ᵢ ∂ᵢ∂ᵢ F(x)`, written through the iterated Fréchet derivative.  This
records the sign and normalization convention of the manuscript's viscous term
`ν Δu` (manuscript `prop:energy`): no minus sign and no factor `1/2`. -/
theorem laplacian_eq_sum (F : Space → Space) (x : Space) :
    Δ F x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ F) x (e i) (e i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis F
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply, e]

/-- Crude bound `‖Δ F x‖ ≤ 3 ‖D²F(x)‖`.  It is the device that turns a caller's
`L¹` hypothesis on `‖u‖ ‖D²u‖` into integrability of the viscous integrand
`⟪u, Δu⟫` of `prop:energy`. -/
theorem norm_laplacian_le (F : Space → Space) (x : Space) :
    ‖Δ F x‖ ≤ 3 * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
  rw [laplacian_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin 3, ‖fderiv ℝ (fderiv ℝ F) x (e i) (e i)‖
      ≤ ∑ _i : Fin 3, ‖fderiv ℝ (fderiv ℝ F) x‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := (fderiv ℝ (fderiv ℝ F) x (e i)).le_opNorm (e i)
        have h2 := (fderiv ℝ (fderiv ℝ F) x).le_opNorm (e i)
        simp only [norm_e, mul_one] at h1 h2
        exact h1.trans h2
    _ = 3 * ‖fderiv ℝ (fderiv ℝ F) x‖ := by simp [Finset.sum_const]

/-- Continuity of `Δ F` for a `C²` field; used only to supply strong
measurability inside the integrability arguments. -/
theorem continuous_laplacian {F : Space → Space} (hF : ContDiff ℝ 2 F) :
    Continuous (Δ F) := by
  have h2 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hc : Continuous fun x => ∑ i : Fin 3, fderiv ℝ (fderiv ℝ F) x (e i) (e i) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (ContinuousLinearMap.apply ℝ Space (e i)).continuous.comp
      ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (e i)).continuous.comp
        (h2.continuous_fderiv one_ne_zero))
  simpa [funext (laplacian_eq_sum F)] using hc

/-- A single squared directional derivative is dominated by the Frobenius
density, `‖∂ᵢF(x)‖² ≤ enstrophyDensity F x`. -/
theorem sq_le_enstrophyDensity (F : Space → Space) (x : Space) (i : Fin 3) :
    ‖fderiv ℝ F x (e i)‖ ^ 2 ≤ enstrophyDensity F x :=
  Finset.single_le_sum (f := fun j : Fin 3 => ‖fderiv ℝ F x (e j)‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-! ## `∫ ⟪u, Δu⟫ = -∫ ‖∇u‖²` -/

/-- The scalar field `y ↦ ⟪u(y), ∂ᵢu(y)⟫` is differentiable when `u` is `C²`.
It is the primitive of the manuscript's viscous integration by parts
(`prop:energy`). -/
theorem differentiable_inner_dir {u : Space → Space} (hu : ContDiff ℝ 2 u) (i : Fin 3) :
    Differentiable ℝ fun y => ⟪u y, fderiv ℝ u y (e i)⟫ := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have h2d : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  intro x
  have hi : DifferentiableAt ℝ (fun y => fderiv ℝ u y (e i)) x := by
    have := (ContinuousLinearMap.apply ℝ Space (e i)).differentiableAt.comp x (h2d x)
    simpa [Function.comp_def] using this
  exact (hud x).inner ℝ hi

/-- Pointwise product rule `∂ᵢ⟪u, ∂ᵢu⟫ = ‖∂ᵢu‖² + ⟪u, ∂ᵢ∂ᵢu⟫`, the identity that
the manuscript's viscous integration by parts (`prop:energy`) integrates. -/
theorem fderiv_inner_dir_self {u : Space → Space} (hu : ContDiff ℝ 2 u) (i : Fin 3) (x : Space) :
    fderiv ℝ (fun y => ⟪u y, fderiv ℝ u y (e i)⟫) x (e i)
      = ‖fderiv ℝ u x (e i)‖ ^ 2 + ⟪u x, fderiv ℝ (fderiv ℝ u) x (e i) (e i)⟫ := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have h2d : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hi : HasFDerivAt (fun y => fderiv ℝ u y (e i))
      ((ContinuousLinearMap.apply ℝ Space (e i)).comp (fderiv ℝ (fderiv ℝ u) x)) x := by
    have := (ContinuousLinearMap.apply ℝ Space (e i)).hasFDerivAt.comp x (h2d x).hasFDerivAt
    simpa [Function.comp_def] using this
  rw [((hud x).hasFDerivAt.inner ℝ hi).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.apply_apply, real_inner_self_eq_norm_sq]
  ring

/-- **The viscous integration by parts** (manuscript `prop:energy`; applied to
`∇u` it is also the viscous term of `prop:enstrophy`).

`∫ ⟪u, Δu⟫ = -∫ ‖∇u‖²_F`, with `‖∇u‖²_F = enstrophyDensity u` the Frobenius density
(design decision D7; the identity is **false** with the operator norm).

The proof is componentwise: it applies `integral_fderiv_apply_eq_zero` in the
direction `eᵢ` to the scalar field `y ↦ ⟪u(y), ∂ᵢu(y)⟫` and sums over `i`, which
is the coordinate form of identity (2) of this module.

The three integrability hypotheses are exactly what Mathlib's boundary-free
integration by parts requires, and none of them is supplied by the manuscript's
classical solution class on its own:
`‖u‖‖∇u‖ ∈ L¹` (the primitive), `‖∇u‖²_F ∈ L¹` (the right-hand side), and
`‖u‖‖D²u‖ ∈ L¹` (the left-hand side, through `norm_laplacian_le`). -/
theorem integral_inner_laplacian_eq_neg_integral_enstrophyDensity
    {u : Space → Space} (hu : ContDiff ℝ 2 u)
    (hu1 : Integrable (fun x => ‖u x‖ * ‖fderiv ℝ u x‖) volume)
    (hjac : Integrable (enstrophyDensity u) volume)
    (hu2 : Integrable (fun x => ‖u x‖ * ‖fderiv ℝ (fderiv ℝ u) x‖) volume) :
    ∫ x, ⟪u x, Δ u x⟫ = - ∫ x, enstrophyDensity u x := by
  have hucont : Continuous u := hu.continuous
  have h2 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hu'cont : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hu''cont : Continuous (fderiv ℝ (fderiv ℝ u)) := h2.continuous_fderiv one_ne_zero
  have hdir : ∀ i : Fin 3, Continuous fun x => fderiv ℝ u x (e i) := fun i =>
    (ContinuousLinearMap.apply ℝ Space (e i)).continuous.comp hu'cont
  have hdir2 : ∀ i : Fin 3, Continuous fun x => fderiv ℝ (fderiv ℝ u) x (e i) (e i) := fun i =>
    (ContinuousLinearMap.apply ℝ Space (e i)).continuous.comp
      ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (e i)).continuous.comp hu''cont)
  have hop2 : ∀ (i : Fin 3) (x : Space),
      ‖fderiv ℝ (fderiv ℝ u) x (e i) (e i)‖ ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ := by
    intro i x
    have h1 := (fderiv ℝ (fderiv ℝ u) x (e i)).le_opNorm (e i)
    have h2 := (fderiv ℝ (fderiv ℝ u) x).le_opNorm (e i)
    simp only [norm_e, mul_one] at h1 h2
    exact h1.trans h2
  -- the primitive `⟪u, ∂ᵢu⟫` is integrable
  have hgi : ∀ i : Fin 3, Integrable (fun x => ⟪u x, fderiv ℝ u x (e i)⟫) volume := by
    intro i
    refine hu1.mono' (hucont.inner (hdir i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    simpa using (fderiv ℝ u x).le_opNorm (e i)
  -- its `∂ᵢ` derivative is integrable
  have hHi : ∀ i : Fin 3, Integrable (fun x => ‖fderiv ℝ u x (e i)‖ ^ 2
      + ⟪u x, fderiv ℝ (fderiv ℝ u) x (e i) (e i)⟫) volume := by
    intro i
    have hcont : Continuous fun x => ‖fderiv ℝ u x (e i)‖ ^ 2
        + ⟪u x, fderiv ℝ (fderiv ℝ u) x (e i) (e i)⟫ :=
      ((hdir i).norm.pow 2).add (hucont.inner (hdir2 i))
    refine (hjac.add hu2).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_enstrophyDensity u x i
    · rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      gcongr
      exact hop2 i x
  -- the left-hand side is integrable
  have hlap : Integrable (fun x => ⟪u x, Δ u x⟫) volume := by
    refine (hu2.const_mul 3).mono'
      (hucont.inner (continuous_laplacian hu)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖u x‖ * ‖Δ u x‖ ≤ ‖u x‖ * (3 * ‖fderiv ℝ (fderiv ℝ u) x‖) := by
          gcongr
          exact norm_laplacian_le u x
      _ = 3 * (‖u x‖ * ‖fderiv ℝ (fderiv ℝ u) x‖) := by ring
  -- componentwise integration by parts
  have key : ∀ i : Fin 3, ∫ x, (‖fderiv ℝ u x (e i)‖ ^ 2
      + ⟪u x, fderiv ℝ (fderiv ℝ u) x (e i) (e i)⟫) = 0 := by
    intro i
    have hdgi : Integrable
        (fun x => fderiv ℝ (fun y => ⟪u y, fderiv ℝ u y (e i)⟫) x (e i)) volume :=
      (hHi i).congr (Filter.Eventually.of_forall fun x => (fderiv_inner_dir_self hu i x).symm)
    have hz := integral_fderiv_apply_eq_zero (e i) (differentiable_inner_dir hu i) (hgi i) hdgi
    rw [← hz]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => (fderiv_inner_dir_self hu i x).symm)
  have hsum : ∑ i : Fin 3, ∫ x, (‖fderiv ℝ u x (e i)‖ ^ 2
      + ⟪u x, fderiv ℝ (fderiv ℝ u) x (e i) (e i)⟫) = 0 :=
    Finset.sum_eq_zero fun i _ => key i
  rw [← integral_finsetSum (μ := (volume : Measure Space)) (s := Finset.univ)
      (f := fun (i : Fin 3) (x : Space) => ‖fderiv ℝ u x (e i)‖ ^ 2
        + ⟪u x, fderiv ℝ (fderiv ℝ u) x (e i) (e i)⟫) (fun i _ => hHi i)] at hsum
  have hpt : ∀ x : Space, ∑ i : Fin 3, (‖fderiv ℝ u x (e i)‖ ^ 2
      + ⟪u x, fderiv ℝ (fderiv ℝ u) x (e i) (e i)⟫)
      = enstrophyDensity u x + ⟪u x, Δ u x⟫ := by
    intro x
    rw [Finset.sum_add_distrib, laplacian_eq_sum u x, inner_sum]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hjac hlap] at hsum
  linarith

/-! ## `∫ ⟪u, (u·∇)u⟫ = 0` for a divergence-free field -/

/-- **Cancellation of the transport term** (manuscript `prop:energy`).

`∫ ⟪u, (u·∇)u⟫ = 0` for a divergence-free `C¹` field, where `(u·∇)u` is
`fderiv ℝ u x (u x)`.  This is the manuscript's `∫ ∇·(|u|²u) / 2 = 0`: the proof
is identity (2) of this module applied to the weight `p = |u|²`, whose gradient
contracted with `u` is `2⟪u, (u·∇)u⟫`, together with `∇·u = 0`.

The two integrability hypotheses are exactly the specialization of identity (2)'s
hypotheses to `p = |u|²`: `‖u‖³ ∈ L¹` and `‖u‖²‖∇u‖ ∈ L¹`.  Neither follows from
the manuscript's classical solution class alone. -/
theorem integral_inner_convection_eq_zero
    {u : Space → Space} (hu : ContDiff ℝ 1 u)
    (hdiv : ∀ x, divergence u x = 0)
    (hu3 : Integrable (fun x => ‖u x‖ ^ 3) volume)
    (hu2d : Integrable (fun x => ‖u x‖ ^ 2 * ‖fderiv ℝ u x‖) volume) :
    ∫ x, ⟪u x, fderiv ℝ u x (u x)⟫ = 0 := by
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hp : ContDiff ℝ 1 fun y => ‖u y‖ ^ 2 := hu.norm_sq ℝ
  have hpapp : ∀ x v : Space,
      fderiv ℝ (fun y => ‖u y‖ ^ 2) x v = 2 * ⟪u x, fderiv ℝ u x v⟫ := by
    intro x v
    rw [(hud x).hasFDerivAt.norm_sq.fderiv]
    simp
  -- the three integrability hypotheses of identity (2) for `p = |u|²`
  have hpu : Integrable (fun x => ‖‖u x‖ ^ 2‖ * ‖u x‖) volume := by
    refine hu3.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖u x‖ ^ 3 = ‖‖u x‖ ^ 2‖ * ‖u x‖
    rw [Real.norm_of_nonneg (by positivity)]
    ring
  have hpdu : Integrable (fun x => ‖‖u x‖ ^ 2‖ * ‖fderiv ℝ u x‖) volume := by
    refine hu2d.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖u x‖ ^ 2 * ‖fderiv ℝ u x‖ = ‖‖u x‖ ^ 2‖ * ‖fderiv ℝ u x‖
    rw [Real.norm_of_nonneg (by positivity)]
  have hdpu : Integrable
      (fun x => ‖fderiv ℝ (fun y => ‖u y‖ ^ 2) x‖ * ‖u x‖) volume := by
    refine (hu2d.const_mul 2).mono'
      (((hp.continuous_fderiv one_ne_zero).norm).mul hu.continuous.norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have hbound : ‖fderiv ℝ (fun y => ‖u y‖ ^ 2) x‖ ≤ 2 * (‖u x‖ * ‖fderiv ℝ u x‖) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      have h1 : ‖⟪u x, fderiv ℝ u x v⟫‖ ≤ ‖u x‖ * ‖fderiv ℝ u x v‖ := by
        rw [Real.norm_eq_abs]
        exact abs_real_inner_le_norm _ _
      have h2 : ‖u x‖ * ‖fderiv ℝ u x v‖ ≤ ‖u x‖ * (‖fderiv ℝ u x‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((fderiv ℝ u x).le_opNorm v) (norm_nonneg _)
      rw [hpapp x v, norm_mul, show ‖(2 : ℝ)‖ = 2 from by norm_num]
      calc 2 * ‖⟪u x, fderiv ℝ u x v⟫‖ ≤ 2 * (‖u x‖ * (‖fderiv ℝ u x‖ * ‖v‖)) := by
            linarith
        _ = 2 * (‖u x‖ * ‖fderiv ℝ u x‖) * ‖v‖ := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖fderiv ℝ (fun y => ‖u y‖ ^ 2) x‖ * ‖u x‖
        ≤ 2 * (‖u x‖ * ‖fderiv ℝ u x‖) * ‖u x‖ := by
          gcongr
      _ = 2 * (‖u x‖ ^ 2 * ‖fderiv ℝ u x‖) := by ring
  have hmain := integral_fderiv_apply_eq_neg_integral_mul_divergence hu hp hpu hpdu hdpu
  have hzero : ∫ x, ‖u x‖ ^ 2 * divergence u x = 0 := by
    simp [hdiv]
  rw [hzero, neg_zero] at hmain
  have hL : ∫ x, fderiv ℝ (fun y => ‖u y‖ ^ 2) x (u x)
      = 2 * ∫ x, ⟪u x, fderiv ℝ u x (u x)⟫ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hpapp x (u x))
  rw [hL] at hmain
  linarith

end IBP
end NavierFormal

end
