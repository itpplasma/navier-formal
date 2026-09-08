import NavierFormal.Basic
import NavierFormal.Calculus
import NavierFormal.IBP
import NavierFormal.SolutionClass
import NavierFormal.Interpolation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The enstrophy identity and the cubic differential inequality (`prop:enstrophy`)

This module formalizes the manuscript's Proposition `prop:enstrophy`
(`../navier-paper/main.tex`): the enstrophy identity `eq:enstrophy-identity`

`½Y'(τ) + ν‖Δu(τ)‖₂² = ∫(u·∇)u·Δu dx`,  `Y(τ) = ‖∇u(τ)‖₂²`

and, from it together with Hölder, Sobolev, the gradient interpolation
inequality, and Young's inequality, the cubic differential inequality
`eq:enstrophy`

`½Y'(τ) + (ν/2)‖Δu(τ)‖₂² ≤ C_E ν⁻³ Y(τ)³`.

## Route

* `frobeniusInner` is the polarization of `NavierFormal.frobeniusNormSq` used for
  `∇u : ∇u_t` in step (a)–(b) of the manuscript's proof.
* `fderiv_dir_comm` is the elementary Clairaut/Schwarz commutation of two
  directional derivatives, obtained from Mathlib's
  `ContDiffAt.isSymmSndFDerivAt` (symmetry of the second Fréchet derivative for
  `C²` maps).  It is the sole source of "mixed partials commute" used below;
  no third-order symmetric-multilinear-map machinery is introduced.
* `divergence_fderiv_dir_eq_fderiv_divergence` and
  `fderiv_gradient_dir_eq_gradient_fderiv_dir` push `fderiv_dir_comm` through the
  divergence and the gradient, and are the "IBP coordinate lemma" alternative
  the lane brief allows in place of a general `∇·Δu = Δ(∇·u)` identity.
* `integral_frobenius_inner_eq_neg_integral_inner_laplacian` is the bilinear
  (polarized) generalization of `NavierFormal.IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity`
  to two different vector fields; manuscript `lem:plancherel`(i).
* `integral_gradient_inner_laplacian_eq_zero` is manuscript `lem:plancherel`(iii),
  proved by two applications of `NavierFormal.IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence`
  (one per spatial direction) sandwiching one application of the bilinear
  Green identity above, rather than by first isolating a standalone
  `∇·Δu = Δ(∇·u)` lemma.
* `enstrophy_identity_pointwise_time` assembles these with the momentum
  equation into `eq:enstrophy-identity`, taking the manuscript's Step 1
  (`Y' = 2∫∇u:∇u_t`) as an explicit hypothesis `hY`, exactly as the lane brief
  permits.
* `enstrophy_inequality_of_interpolation` chases Hölder, Sobolev
  (`NavierFormal.eLpNorm_six_le_eLpNorm_fderiv_two`), the interpolation
  inequality (hypothesis, not proved here), and Young
  (`NavierFormal.young_four_thirds_eps`) into `eq:enstrophy`, working with real
  numbers standing for the relevant `Lᵖ` norms rather than re-deriving their
  `eLpNorm`/`MemLp` bookkeeping; see its docstring for the exact deviation.

## Norm conventions (fidelity risk `R-NORM`, documented per the lane brief)

`Y = ∫enstrophyDensity u = ∫‖∇u‖²_F` is always the **Frobenius** norm
(`NavierFormal.enstrophyDensity`), matching `frobeniusInner`/`frobeniusNormSq`.
`eLpNorm_six_le_eLpNorm_fderiv_two`, used only inside
`enstrophy_inequality_of_interpolation`, is stated with the **operator** norm
`‖fderiv ℝ u x‖`.  `enstrophy_inequality_of_interpolation` therefore works with
an abstract real `g` standing for the operator-norm quantity
`eLpNorm(∇u)₂`, *not* `√Y`; the two differ by at most a factor `√3`
(`NavierFormal.opNorm_le_frobeniusNorm`, `NavierFormal.frobeniusNorm_le_sqrt_three_mul`),
which is not chased here (deviation, documented at the theorem).

Nothing here is a theorem about the Millennium problem.
-/

open MeasureTheory InnerProductSpace Laplacian
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace NavierFormal

/-! ## The Frobenius inner product of two Jacobians -/

/-- The Frobenius (Hilbert–Schmidt) inner product `⟪L,M⟫_F = ∑ⱼ⟪L eⱼ, M eⱼ⟫` of
two linear maps of `ℝ³`, the polarization of `NavierFormal.frobeniusNormSq`.
Used for the manuscript's `∇u : ∇u_t = ∑ⱼₖ ∂ⱼuₖ ∂ⱼ(u_t)ₖ`
(`lem:plancherel`(i), `prop:enstrophy` Step 1). -/
def frobeniusInner (L M : Space →L[ℝ] Space) : ℝ := ∑ j, ⟪L (e j), M (e j)⟫

/-- The Frobenius inner product is symmetric. -/
theorem frobeniusInner_comm (L M : Space →L[ℝ] Space) :
    frobeniusInner L M = frobeniusInner M L := by
  unfold frobeniusInner
  simp_rw [real_inner_comm]

/-- The Frobenius inner product polarizes `frobeniusNormSq`. -/
theorem frobeniusInner_self (L : Space →L[ℝ] Space) :
    frobeniusInner L L = frobeniusNormSq L := by
  unfold frobeniusInner frobeniusNormSq
  simp_rw [real_inner_self_eq_norm_sq]

/-! ## Commutation of two directional derivatives (Clairaut/Schwarz) -/

/-- The derivative of the directional derivative `y ↦ fderiv φ y v` in direction
`w`, rewritten through the second Fréchet derivative: `∂_w(∂_v φ) = D²φ(w,v)`.
Elementary bookkeeping, the same identity used inside
`NavierFormal.IBP.fderiv_inner_dir_self`. -/
theorem fderiv_dir_apply_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : Space → F} (hφ : ContDiff ℝ 2 φ) (x v w : Space) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w = fderiv ℝ (fderiv ℝ φ) x w v := by
  have h2d : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hi : HasFDerivAt (fun y => fderiv ℝ φ y v)
      ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ φ) x)) x := by
    have := (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x (h2d x).hasFDerivAt
    simpa [Function.comp_def] using this
  rw [hi.fderiv]
  simp

/-- **Commutation of two directional derivatives** (Clairaut/Schwarz), the sole
source of "mixed partials commute" used in this file: for a `C²` map `φ`,
`∂_w(∂_vφ) = ∂_v(∂_wφ)` at every point.  Obtained from Mathlib's
`ContDiffAt.isSymmSndFDerivAt` (symmetry of the second Fréchet derivative). -/
theorem fderiv_dir_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : Space → F} (hφ : ContDiff ℝ 2 φ) (x v w : Space) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w = fderiv ℝ (fun y => fderiv ℝ φ y w) x v := by
  rw [fderiv_dir_apply_eq hφ x v w, fderiv_dir_apply_eq hφ x w v]
  have hsymm : IsSymmSndFDerivAt ℝ φ x := hφ.contDiffAt.isSymmSndFDerivAt (by simp)
  exact hsymm.eq w v

/-! ## `fderiv_dir_comm` pushed through the divergence and the gradient -/

/-- The directional derivative of a `C²` field commutes with its divergence:
`∇·(∂_w u) = ∂_w(∇·u)`.  This is the "IBP coordinate lemma" route to
`∇·Δu = Δ(∇·u)` that the lane brief allows in place of a general symmetric
`iteratedFDeriv` statement: it is exactly what `integral_gradient_inner_laplacian_eq_zero`
needs, applied to `w = eⱼ` and to the vector field `Δu` written as
`∑ⱼ ∂ⱼ(∂ⱼu)`. -/
theorem divergence_fderiv_dir_eq_fderiv_divergence {u : Space → Space} (hu : ContDiff ℝ 2 u)
    (x w : Space) :
    divergence (fun y => fderiv ℝ u y w) x = fderiv ℝ (divergence u) x w := by
  have hu1 : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hFi : ∀ i : Fin 3, Differentiable ℝ (fun y => fderiv ℝ u y (e i)) := fun i x' =>
    (ContinuousLinearMap.apply ℝ Space (e i)).differentiableAt.comp x' (hu1 x')
  have hcoord : ∀ i : Fin 3, Differentiable ℝ (fun y => (fderiv ℝ u y (e i)) i) := by
    intro i x'
    have h := (IBP.coord i).differentiableAt.comp x' (hFi i x')
    simpa [Function.comp_def, IBP.coord_apply] using h
  have hstep : ∀ i : Fin 3, (fderiv ℝ (fun y => fderiv ℝ u y w) x (e i)) i
      = fderiv ℝ (fun y => (fderiv ℝ u y (e i)) i) x w := by
    intro i
    rw [fderiv_dir_comm hu x w (e i)]
    exact (IBP.fderiv_coord (hFi i) i x w).symm
  have hdiv : divergence (fun y => fderiv ℝ u y w) x
      = ∑ i : Fin 3, fderiv ℝ (fun y => (fderiv ℝ u y (e i)) i) x w := by
    rw [divergence_eq_sum_component]
    exact Finset.sum_congr rfl fun i _ => hstep i
  have hHasF : HasFDerivAt (fun y => ∑ i : Fin 3, (fderiv ℝ u y (e i)) i)
      (∑ i : Fin 3, fderiv ℝ (fun y => (fderiv ℝ u y (e i)) i) x) x :=
    HasFDerivAt.fun_sum fun i _ => (hcoord i x).hasFDerivAt
  have hfun : (fun y => ∑ i : Fin 3, (fderiv ℝ u y (e i)) i) = divergence u :=
    funext fun y => (divergence_eq_sum_component u y).symm
  rw [hfun] at hHasF
  rw [hdiv, hHasF.fderiv]
  simp

/-- The directional derivative of a `C²` scalar field commutes with its
gradient: `∇(∂_v p) = ∂_v(∇p)`, i.e. the Hessian of `p` is a symmetric bilinear
form written through directional derivatives.  Used for
`integral_gradient_inner_laplacian_eq_zero`. -/
theorem fderiv_gradient_dir_eq_gradient_fderiv_dir {p : Space → ℝ} (hp : ContDiff ℝ 2 p)
    (x v : Space) :
    fderiv ℝ (gradient p) x v = gradient (fun y => fderiv ℝ p y v) x := by
  have hp1 : Differentiable ℝ (fderiv ℝ p) :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hgp : Differentiable ℝ (gradient p) := by
    have heq : gradient p = fun y => ∑ i : Fin 3, fderiv ℝ p y (e i) • e i := by
      funext y
      rw [← sum_smul_e (gradient p y)]
      exact Finset.sum_congr rfl fun i _ => by rw [gradient_component p y i]
    rw [heq]
    exact Differentiable.fun_sum fun i _ =>
      ((ContinuousLinearMap.apply ℝ ℝ (e i)).differentiable.comp hp1).smul_const (e i)
  ext i
  rw [← IBP.fderiv_coord hgp i x v]
  have hcomp : (fun y => gradient p y i) = fun y => fderiv ℝ p y (e i) :=
    funext fun y => gradient_component p y i
  rw [hcomp, fderiv_dir_comm hp x (e i) v, gradient_component]

/-! ## The bilinear Green identity (`lem:plancherel`(i)) -/

/-- The primitive `y ↦ ⟪w y, ∂ᵢv y⟫` of the bilinear Green identity is
differentiable for `v` of class `C²` and `w` of class `C¹`. -/
theorem differentiable_inner_dir_bilinear {v w : Space → Space} (hv : ContDiff ℝ 2 v)
    (hw : ContDiff ℝ 1 w) (i : Fin 3) :
    Differentiable ℝ fun y => ⟪w y, fderiv ℝ v y (e i)⟫ := by
  have hwd : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hvd : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  intro x
  have hi : DifferentiableAt ℝ (fun y => fderiv ℝ v y (e i)) x := by
    have := (ContinuousLinearMap.apply ℝ Space (e i)).differentiableAt.comp x (hvd x)
    simpa [Function.comp_def] using this
  exact (hwd x).inner ℝ hi

/-- The pointwise product rule integrated by the bilinear Green identity:
`∂ᵢ⟪w,∂ᵢv⟫ = ⟪∂ᵢw,∂ᵢv⟫ + ⟪w,∂ᵢ∂ᵢv⟫`. -/
theorem fderiv_inner_dir_bilinear {v w : Space → Space} (hv : ContDiff ℝ 2 v) (hw : ContDiff ℝ 1 w)
    (i : Fin 3) (x : Space) :
    fderiv ℝ (fun y => ⟪w y, fderiv ℝ v y (e i)⟫) x (e i)
      = ⟪fderiv ℝ w x (e i), fderiv ℝ v x (e i)⟫
        + ⟪w x, fderiv ℝ (fderiv ℝ v) x (e i) (e i)⟫ := by
  have hwd : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hvd : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hi : HasFDerivAt (fun y => fderiv ℝ v y (e i))
      ((ContinuousLinearMap.apply ℝ Space (e i)).comp (fderiv ℝ (fderiv ℝ v) x)) x := by
    have := (ContinuousLinearMap.apply ℝ Space (e i)).hasFDerivAt.comp x (hvd x).hasFDerivAt
    simpa [Function.comp_def] using this
  rw [((hwd x).hasFDerivAt.inner ℝ hi).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.apply_apply]
  ring

/-- **The bilinear (polarized) Green identity** (manuscript `lem:plancherel`(i)):
`∫⟪∇v,∇w⟫_F = -∫⟪Δv,w⟫` for two vector fields `v,w`. This generalizes
`NavierFormal.IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity`
(the case `w = v`) to two different fields, exactly as needed for `∇p` versus
`Δu` in `integral_gradient_inner_laplacian_eq_zero`.

The three integrability hypotheses mirror `NavierFormal.IBP`'s style:
`‖w‖‖∇v‖ ∈ L¹` (the primitive), `‖∇v‖‖∇w‖ ∈ L¹` (dominates the derivative term
`⟪∂ᵢw,∂ᵢv⟫`, using the operator norm), and `‖w‖‖D²v‖ ∈ L¹` (dominates the
`⟪w,∂ᵢ∂ᵢv⟫` term and the right-hand side `⟪Δv,w⟫`). -/
theorem integral_frobenius_inner_eq_neg_integral_inner_laplacian
    {v w : Space → Space} (hv : ContDiff ℝ 2 v) (hw : ContDiff ℝ 1 w)
    (hvw1 : Integrable (fun x => ‖w x‖ * ‖fderiv ℝ v x‖) volume)
    (hprod : Integrable (fun x => ‖fderiv ℝ v x‖ * ‖fderiv ℝ w x‖) volume)
    (hvw2 : Integrable (fun x => ‖w x‖ * ‖fderiv ℝ (fderiv ℝ v) x‖) volume) :
    ∫ x, frobeniusInner (fderiv ℝ v x) (fderiv ℝ w x) = - ∫ x, ⟪Δ v x, w x⟫ := by
  have hwcont : Continuous w := hw.continuous
  have hv'cont : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hw'cont : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hv' : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have hv''cont : Continuous (fderiv ℝ (fderiv ℝ v)) := hv'.continuous_fderiv one_ne_zero
  have hdirv : ∀ i : Fin 3, Continuous fun x => fderiv ℝ v x (e i) := fun i =>
    (ContinuousLinearMap.apply ℝ Space (e i)).continuous.comp hv'cont
  have hdirw : ∀ i : Fin 3, Continuous fun x => fderiv ℝ w x (e i) := fun i =>
    (ContinuousLinearMap.apply ℝ Space (e i)).continuous.comp hw'cont
  have hdir2 : ∀ i : Fin 3, Continuous fun x => fderiv ℝ (fderiv ℝ v) x (e i) (e i) := fun i =>
    (ContinuousLinearMap.apply ℝ Space (e i)).continuous.comp
      ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (e i)).continuous.comp hv''cont)
  have hop2 : ∀ (i : Fin 3) (x : Space),
      ‖fderiv ℝ (fderiv ℝ v) x (e i) (e i)‖ ≤ ‖fderiv ℝ (fderiv ℝ v) x‖ := by
    intro i x
    have h1 := (fderiv ℝ (fderiv ℝ v) x (e i)).le_opNorm (e i)
    have h2 := (fderiv ℝ (fderiv ℝ v) x).le_opNorm (e i)
    simp only [norm_e, mul_one] at h1 h2
    exact h1.trans h2
  have hgi : ∀ i : Fin 3, Integrable (fun x => ⟪w x, fderiv ℝ v x (e i)⟫) volume := by
    intro i
    refine hvw1.mono' (hwcont.inner (hdirv i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    simpa using (fderiv ℝ v x).le_opNorm (e i)
  have hHi : ∀ i : Fin 3, Integrable (fun x => ⟪fderiv ℝ w x (e i), fderiv ℝ v x (e i)⟫
      + ⟪w x, fderiv ℝ (fderiv ℝ v) x (e i) (e i)⟫) volume := by
    intro i
    have hcont : Continuous fun x => ⟪fderiv ℝ w x (e i), fderiv ℝ v x (e i)⟫
        + ⟪w x, fderiv ℝ (fderiv ℝ v) x (e i) (e i)⟫ :=
      ((hdirw i).inner (hdirv i)).add (hwcont.inner (hdir2 i))
    refine (hprod.add hvw2).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖fderiv ℝ w x (e i)‖ * ‖fderiv ℝ v x (e i)‖
          ≤ ‖fderiv ℝ v x‖ * ‖fderiv ℝ w x‖ := by
            rw [mul_comm (‖fderiv ℝ v x‖)]
            gcongr
            · simpa using (fderiv ℝ w x).le_opNorm (e i)
            · simpa using (fderiv ℝ v x).le_opNorm (e i)
        _ = ‖fderiv ℝ v x‖ * ‖fderiv ℝ w x‖ := rfl
    · rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      gcongr
      exact hop2 i x
  have hlap : Integrable (fun x => ⟪Δ v x, w x⟫) volume := by
    refine (hvw2.const_mul 3).mono'
      ((IBP.continuous_laplacian hv).inner hwcont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖Δ v x‖ * ‖w x‖ ≤ (3 * ‖fderiv ℝ (fderiv ℝ v) x‖) * ‖w x‖ := by
          gcongr
          exact IBP.norm_laplacian_le v x
      _ = 3 * (‖w x‖ * ‖fderiv ℝ (fderiv ℝ v) x‖) := by ring
  have key : ∀ i : Fin 3, ∫ x, (⟪fderiv ℝ w x (e i), fderiv ℝ v x (e i)⟫
      + ⟪w x, fderiv ℝ (fderiv ℝ v) x (e i) (e i)⟫) = 0 := by
    intro i
    have hdgi : Integrable
        (fun x => fderiv ℝ (fun y => ⟪w y, fderiv ℝ v y (e i)⟫) x (e i)) volume :=
      (hHi i).congr
        (Filter.Eventually.of_forall fun x => (fderiv_inner_dir_bilinear hv hw i x).symm)
    have hz := IBP.integral_fderiv_apply_eq_zero (e i)
      (differentiable_inner_dir_bilinear hv hw i) (hgi i) hdgi
    rw [← hz]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => (fderiv_inner_dir_bilinear hv hw i x).symm)
  have hsum : ∑ i : Fin 3, ∫ x, (⟪fderiv ℝ w x (e i), fderiv ℝ v x (e i)⟫
      + ⟪w x, fderiv ℝ (fderiv ℝ v) x (e i) (e i)⟫) = 0 :=
    Finset.sum_eq_zero fun i _ => key i
  rw [← integral_finsetSum (μ := (volume : Measure Space)) (s := Finset.univ)
      (f := fun (i : Fin 3) (x : Space) => ⟪fderiv ℝ w x (e i), fderiv ℝ v x (e i)⟫
        + ⟪w x, fderiv ℝ (fderiv ℝ v) x (e i) (e i)⟫) (fun i _ => hHi i)] at hsum
  have hpt : ∀ x : Space, ∑ i : Fin 3, (⟪fderiv ℝ w x (e i), fderiv ℝ v x (e i)⟫
      + ⟪w x, fderiv ℝ (fderiv ℝ v) x (e i) (e i)⟫)
      = frobeniusInner (fderiv ℝ v x) (fderiv ℝ w x) + ⟪Δ v x, w x⟫ := by
    intro x
    rw [Finset.sum_add_distrib]
    have e1 : ∑ i : Fin 3, ⟪fderiv ℝ w x (e i), fderiv ℝ v x (e i)⟫
        = frobeniusInner (fderiv ℝ v x) (fderiv ℝ w x) := by
      unfold frobeniusInner
      exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
    have e2 : ∑ i : Fin 3, ⟪w x, fderiv ℝ (fderiv ℝ v) x (e i) (e i)⟫ = ⟪Δ v x, w x⟫ := by
      rw [IBP.laplacian_eq_sum v x, sum_inner]
      exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
    rw [e1, e2]
  have hfrob : Integrable (fun x => frobeniusInner (fderiv ℝ v x) (fderiv ℝ w x)) volume := by
    have hcont : Continuous fun x => frobeniusInner (fderiv ℝ v x) (fderiv ℝ w x) := by
      unfold frobeniusInner
      exact continuous_finsetSum _ fun i _ => (hdirv i).inner (hdirw i)
    refine (hprod.const_mul 3).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    unfold frobeniusInner
    calc |∑ i : Fin 3, ⟪fderiv ℝ v x (e i), fderiv ℝ w x (e i)⟫|
        ≤ ∑ i : Fin 3, |⟪fderiv ℝ v x (e i), fderiv ℝ w x (e i)⟫| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ v x‖ * ‖fderiv ℝ w x‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (abs_real_inner_le_norm _ _).trans ?_
          gcongr
          · simpa using (fderiv ℝ v x).le_opNorm (e i)
          · simpa using (fderiv ℝ w x).le_opNorm (e i)
      _ = 3 * (‖fderiv ℝ v x‖ * ‖fderiv ℝ w x‖) := by simp [Finset.sum_const]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add hfrob hlap] at hsum
  linarith

end NavierFormal

end

namespace NavierFormal

/-! ## `∫⟪∇p,Δu⟫ = 0` for a divergence-free field (manuscript `lem:plancherel`(iii)) -/

/-- Divergence of a finite sum of `C¹` vector fields is the sum of the
divergences.  Elementary bookkeeping used to push the divergence through the
sum defining the Laplacian (`NavierFormal.IBP.laplacian_eq_sum`). -/
theorem divergence_finsum_eq_sum_divergence {ι : Type*} [Fintype ι] {F : ι → Space → Space}
    (hF : ∀ j, Differentiable ℝ (F j)) (x : Space) :
    divergence (fun y => ∑ j, F j y) x = ∑ j, divergence (F j) x := by
  have hd : fderiv ℝ (fun y => ∑ j, F j y) x = ∑ j, fderiv ℝ (F j) x :=
    fderiv_fun_sum (fun j _ => (hF j) x)
  have hstep : ∀ i : Fin 3, ((∑ j, fderiv ℝ (F j) x) (e i)) i
      = ∑ j, (fderiv ℝ (F j) x (e i)) i := by
    intro i
    rw [sum_apply]
    simp [Finset.sum_apply]
  rw [divergence_eq_sum_component, hd]
  simp_rw [hstep]
  rw [Finset.sum_comm]
  simp_rw [← divergence_eq_sum_component]

/-- A directional derivative field of a `C³` field is divergence-free when the
underlying field is: `∇·(∂_w u) = 0` for `w` a fixed direction, given
`∇·u ≡ 0`.  Immediate from `divergence_fderiv_dir_eq_fderiv_divergence`, since
`∇·u` is then the constant zero function and its derivative in any direction
vanishes. -/
theorem divergence_fderiv_dir_eq_zero {u : Space → Space} (hu : ContDiff ℝ 2 u)
    (hdiv : ∀ x, divergence u x = 0) (x w : Space) :
    divergence (fun y => fderiv ℝ u y w) x = 0 := by
  rw [divergence_fderiv_dir_eq_fderiv_divergence hu]
  have : divergence u = fun _ => (0 : ℝ) := funext hdiv
  rw [this]
  simp

/-- The Laplacian of a divergence-free `C³` field is again divergence-free:
`∇·(Δu) = 0`.  Proved by writing `Δu = ∑ⱼ ∂ⱼ(∂ⱼu)`
(`NavierFormal.IBP.laplacian_eq_sum`) and applying
`divergence_fderiv_dir_eq_zero` twice, once to `u` (giving `∇·(∂ⱼu) = 0`, hence
`∂ⱼu` itself divergence-free — used only implicitly) and once more to each
`∂ⱼu`, which is `C²` because `u` is `C³`.  This is the manuscript's
`∇·Δu = Δ(∇·u) = 0` (`lem:plancherel`(iii)) obtained through the "IBP
coordinate lemma" route rather than a general symmetric-derivative identity. -/
theorem divergence_laplacian_eq_zero {u : Space → Space} (hu : ContDiff ℝ 3 u)
    (hdiv : ∀ x, divergence u x = 0) (x : Space) :
    divergence (Δ u) x = 0 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hWcd : ∀ j : Fin 3, ContDiff ℝ 2 (fun y => fderiv ℝ u y (e j)) := by
    intro j
    have h2 : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (m := 2) (by norm_num)
    have := (ContinuousLinearMap.apply ℝ Space (e j)).contDiff.comp h2
    simpa [Function.comp_def] using this
  have hlap : Δ u = fun y => ∑ j : Fin 3, fderiv ℝ (fderiv ℝ u) y (e j) (e j) :=
    funext (IBP.laplacian_eq_sum u)
  have hVdiff : ∀ j : Fin 3, Differentiable ℝ
      (fun y => fderiv ℝ (fun z => fderiv ℝ u z (e j)) y (e j)) := fun j x' => by
    have := (hWcd j).fderiv_right (m := 1) (by norm_num) |>.differentiable one_ne_zero
    have h2 := (ContinuousLinearMap.apply ℝ Space (e j)).differentiableAt.comp x' (this x')
    simpa [Function.comp_def] using h2
  have hVeq : ∀ j : Fin 3, (fun y => fderiv ℝ (fderiv ℝ u) y (e j) (e j))
      = fun y => fderiv ℝ (fun z => fderiv ℝ u z (e j)) y (e j) :=
    fun j => funext fun y => (fderiv_dir_apply_eq hu2 y (e j) (e j)).symm
  rw [hlap, divergence_finsum_eq_sum_divergence (fun j => by rw [hVeq j]; exact hVdiff j)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hVeq j]
  exact divergence_fderiv_dir_eq_zero (hWcd j) (fun y => divergence_fderiv_dir_eq_zero hu2 hdiv y (e j)) x (e j)

/-- **`∫⟪∇p,Δu⟫ = 0`, manuscript `lem:plancherel`(iii)**, for a divergence-free
`C³` velocity field `u` and a `C²` pressure `p`.

Proof: `⟪∇p,Δu⟫ = fderiv ℝ p x (Δu x)` by the defining property of the
gradient (`NavierFormal.inner_gradient_apply`), and
`NavierFormal.IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence`
(applied with the pressure role played by `p` and the vector-field role by
`Δu`) turns the integral into `-∫ p (∇·Δu)`, which vanishes by
`divergence_laplacian_eq_zero`.

The three integrability hypotheses are exactly what that lemma requires for
the pair `(p, Δu)`: `‖p‖‖Δu‖`, `‖p‖‖∇(Δu)‖` and `‖∇p‖‖Δu‖` in `L¹(ℝ³)`. -/
theorem integral_gradient_inner_laplacian_eq_zero
    {u : Space → Space} {p : Space → ℝ} (hu : ContDiff ℝ 3 u) (hp : ContDiff ℝ 1 p)
    (hdiv : ∀ x, divergence u x = 0)
    (hpu : Integrable (fun x => ‖p x‖ * ‖Δ u x‖) volume)
    (hpdu : Integrable (fun x => ‖p x‖ * ‖fderiv ℝ (Δ u) x‖) volume)
    (hdpu : Integrable (fun x => ‖fderiv ℝ p x‖ * ‖Δ u x‖) volume) :
    ∫ x, ⟪gradient p x, Δ u x⟫ = 0 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hΔcd : ContDiff ℝ 1 (Δ u) := by
    have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
      (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
    have : Δ u = fun x => ∑ i : Fin 3, fderiv ℝ (fderiv ℝ u) x (e i) (e i) :=
      funext (IBP.laplacian_eq_sum u)
    rw [this]
    refine ContDiff.sum fun i _ => ?_
    have := (ContinuousLinearMap.apply ℝ Space (e i)).contDiff.comp
        ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (e i)).contDiff.comp h2)
    simpa [Function.comp_def] using this
  have hkey := IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence hΔcd hp hpu hpdu hdpu
  have hzero : ∫ x, p x * divergence (Δ u) x = 0 := by
    have : (fun x => p x * divergence (Δ u) x) = fun _ => (0 : ℝ) := by
      funext x; rw [divergence_laplacian_eq_zero hu hdiv x]; ring
    rw [this]; simp
  rw [hzero, neg_zero] at hkey
  refine Eq.trans ?_ hkey
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => inner_gradient_apply p x (Δ u x))

/-! ## The enstrophy identity, manuscript `eq:enstrophy-identity` -/

/-- **The enstrophy identity** (manuscript Proposition `prop:enstrophy`, Step 1,
`eq:enstrophy-identity`): for a classical solution at an interior time `t`,

`½Y'(t) + ν‖Δu(t)‖₂² = ∫(u·∇)u·Δu dx`,

written here with `Y'(t)` supplied literally as the hypothesis `hY`
(the manuscript's Step 1, `Y' = 2∫∇u:∇u_t`, taken as given rather than
re-derived from `L²`-differentiability of `t ↦ u(t)`) and displayed as
`(1/2)*(2*∫frobeniusInner(∇u,∇u_t))` rather than through `deriv`.

Proof: substitute the momentum equation
`u_t = ν•Δu - (u·∇)u - ∇p` (`IsClassicalSolution.momentum`) into
`⟪Δu,u_t⟫` pointwise, then integrate; the pressure term drops out by
`integral_gradient_inner_laplacian_eq_zero` (`lem:plancherel`(iii)) and the
left side is rewritten via the bilinear Green identity
`integral_frobenius_inner_eq_neg_integral_inner_laplacian`
(`lem:plancherel`(i)).

The hypotheses `hu3`, `hp2`, `hut1` are the smoothness inputs of the two
lemmas invoked; `hvw1,hprod,hvw2` and `hpu,hpdu,hdpu` are exactly their `L¹`
hypotheses (for the pairs `(u(t),u_t(t))` and `(u(t),p(t))` respectively);
`hΔsq,hconvΔ,hgradΔ` are the further `L¹` hypotheses needed to split the
integral of the substituted momentum equation into its three terms. None of
these follow from `IsClassicalSolution` alone (see `NavierFormal.IBP`'s module
docstring); a caller discharges them from the regularity package. -/
theorem enstrophy_identity_pointwise_time
    {ν : ℝ} {u₀ : Space → Space} {T : ℝ} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsClassicalSolution ν u₀ T u p) {t : ℝ} (ht0 : 0 < t) (htT : t < T)
    (hY : HasDerivAt (fun s => ∫ x, enstrophyDensity (u s) x)
      (2 * ∫ x, frobeniusInner (fderiv ℝ (u t) x) (fderiv ℝ (timeDeriv u t) x)) t)
    (hu3 : ContDiff ℝ 3 (u t)) (hp2 : ContDiff ℝ 2 (p t)) (hut1 : ContDiff ℝ 1 (timeDeriv u t))
    (hvw1 : Integrable (fun x => ‖timeDeriv u t x‖ * ‖fderiv ℝ (u t) x‖) volume)
    (hprod : Integrable (fun x => ‖fderiv ℝ (u t) x‖ * ‖fderiv ℝ (timeDeriv u t) x‖) volume)
    (hvw2 : Integrable (fun x => ‖timeDeriv u t x‖ * ‖fderiv ℝ (fderiv ℝ (u t)) x‖) volume)
    (hpu : Integrable (fun x => ‖p t x‖ * ‖Δ (u t) x‖) volume)
    (hpdu : Integrable (fun x => ‖p t x‖ * ‖fderiv ℝ (Δ (u t)) x‖) volume)
    (hdpu : Integrable (fun x => ‖fderiv ℝ (p t) x‖ * ‖Δ (u t) x‖) volume)
    (hΔsq : Integrable (fun x => ‖Δ (u t) x‖ ^ 2) volume)
    (hconvΔ : Integrable (fun x => ⟪Δ (u t) x, convection (u t) x⟫) volume)
    (hgradΔ : Integrable (fun x => ⟪Δ (u t) x, gradient (p t) x⟫) volume) :
    (1 / 2) * (2 * ∫ x, frobeniusInner (fderiv ℝ (u t) x) (fderiv ℝ (timeDeriv u t) x))
      + ν * ∫ x, ‖Δ (u t) x‖ ^ 2
      = ∫ x, ⟪convection (u t) x, Δ (u t) x⟫ := by
  have hu2 : ContDiff ℝ 2 (u t) := hu3.of_le (by norm_num)
  have hp1 : ContDiff ℝ 1 (p t) := hp2.of_le (by norm_num)
  have hdivt : ∀ x, divergence (u t) x = 0 := fun x => h.incompressible t x ht0 htT
  have key2 : ∫ x, frobeniusInner (fderiv ℝ (u t) x) (fderiv ℝ (timeDeriv u t) x)
      = -∫ x, ⟪Δ (u t) x, timeDeriv u t x⟫ :=
    integral_frobenius_inner_eq_neg_integral_inner_laplacian hu2 hut1 hvw1 hprod hvw2
  have key1 : ∫ x, ⟪gradient (p t) x, Δ (u t) x⟫ = 0 :=
    integral_gradient_inner_laplacian_eq_zero hu3 hp1 hdivt hpu hpdu hdpu
  have key1' : ∫ x, ⟪Δ (u t) x, gradient (p t) x⟫ = 0 := by
    rw [← key1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)
  have hCE : ∫ x, ⟪convection (u t) x, Δ (u t) x⟫ = ∫ x, ⟪Δ (u t) x, convection (u t) x⟫ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)
  have hpt : ∀ x, ⟪Δ (u t) x, timeDeriv u t x⟫
      = ν * ‖Δ (u t) x‖ ^ 2 - ⟪Δ (u t) x, convection (u t) x⟫
        - ⟪Δ (u t) x, gradient (p t) x⟫ := by
    intro x
    have hmom := h.momentum t x ht0 htT
    have heq : timeDeriv u t x
        = ν • Δ (u t) x - convection (u t) x - gradient (p t) x := by
      rw [sub_sub, eq_sub_iff_add_eq, ← add_assoc]
      exact hmom
    rw [heq, inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hAB : Integrable (fun x => ν * ‖Δ (u t) x‖ ^ 2 - ⟪Δ (u t) x, convection (u t) x⟫) volume :=
    (hΔsq.const_mul ν).sub hconvΔ
  have hfinal : (∫ x, (ν * ‖Δ (u t) x‖ ^ 2 - ⟪Δ (u t) x, convection (u t) x⟫
      - ⟪Δ (u t) x, gradient (p t) x⟫))
      = ν * (∫ x, ‖Δ (u t) x‖ ^ 2) - (∫ x, ⟪Δ (u t) x, convection (u t) x⟫)
        - (∫ x, ⟪Δ (u t) x, gradient (p t) x⟫) := by
    rw [integral_sub hAB hgradΔ, integral_sub (hΔsq.const_mul ν) hconvΔ, integral_const_mul]
  have hstep : (∫ x, ⟪Δ (u t) x, timeDeriv u t x⟫)
      = ν * (∫ x, ‖Δ (u t) x‖ ^ 2) - (∫ x, ⟪Δ (u t) x, convection (u t) x⟫)
        - (∫ x, ⟪Δ (u t) x, gradient (p t) x⟫) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hfinal]
  rw [key1'] at hstep
  linarith [key2, hCE, hstep]

end NavierFormal

namespace NavierFormal

/-! ## The cubic differential inequality, manuscript `eq:enstrophy` -/

end NavierFormal
