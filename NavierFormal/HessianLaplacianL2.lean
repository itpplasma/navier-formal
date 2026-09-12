import NavierFormal.HessianLaplacian
import NavierFormal.EnstrophyIdentity

/-!
# The integrated Hessian--Laplacian identity

This module formalizes the next analytic bridge after the pointwise
Hessian/Laplacian commutation in `NavierFormal.HessianLaplacian`: the
Frobenius/Hilbert--Schmidt `L²` identity used by manuscript `prop:enstrophy`,
`lem:plancherel`(ii),

`∫ ‖D²u‖_F² = ∫ ‖Δu‖²`.

The route is the whole-space integration-by-parts route.  For each coordinate
direction `e j`, apply the existing Green identity to `∂ⱼu`; then commute
`Δ` past `∂ⱼ` using the pointwise `C³` theorem.  A second Green identity,
applied to `u` and `Δu`, identifies the resulting sum with `‖Δu‖₂²`.

The theorem below carries every integrability condition needed by those two
Green identities and by the finite-sum integral rearrangements in an explicit
structure.  Thus the result has no hidden boundary or decay assumption.  It
does not prove that compact support, or the manuscript's `H²` hypotheses, imply
this package; that separate representative/integrability bridge remains open.
The conclusion is nevertheless the exact squared identity, with the
Frobenius norm convention rather than the operator norm.
-/

open MeasureTheory InnerProductSpace Laplacian
open scoped RealInnerProductSpace

noncomputable section

namespace NavierFormal

/-! ## Directional derivatives and the Frobenius Hessian density -/

/-- The `j`-th spatial directional derivative of a vector field.  This is the
coordinate field used in the proof of manuscript `prop:enstrophy`,
`lem:plancherel`(ii). -/
def firstDirectionalDerivative (u : Space → Space) (j : Fin 3) : Space → Space :=
  fun x => fderiv ℝ u x (e j)

/-- The pointwise squared Frobenius/Hilbert--Schmidt Hessian density
`‖D²u(x)‖_F² = ∑ⱼ ‖∇(∂ⱼu)(x)‖_F²` used in manuscript `prop:enstrophy`,
`lem:plancherel`(ii).  It sums all spatial and vector-component second
derivatives; it is not the square of the operator norm of a second derivative.
-/
def hessianFrobeniusSq (u : Space → Space) (x : Space) : ℝ :=
  ∑ j : Fin 3, enstrophyDensity (firstDirectionalDerivative u j) x

/-! ## Explicit boundary-free integrability hypotheses -/

/-- The exact `L¹` package used by the whole-space integration-by-parts proof
of manuscript `prop:enstrophy`, `lem:plancherel`(ii), for a field `u`.

For every `j`, the first three fields are the hypotheses for the existing
identity applied to `∂ⱼu`: its primitive, its Frobenius gradient square, and
the primitive's second-derivative bound.  The last three fields are the
corresponding hypotheses for the identity applied to `u` with `Δu` as the
second field.  `directional_laplacian_inner` is the additional exact
integrability needed to exchange the finite sum with the integral.  No field
asserts compact support, and no integrability claim is inferred from
smoothness alone.
-/
structure HessianLaplacianIBPData (u : Space → Space) : Prop where
  directional_primitive : ∀ j : Fin 3,
    Integrable (fun x =>
      ‖firstDirectionalDerivative u j x‖ *
        ‖fderiv ℝ (firstDirectionalDerivative u j) x‖) volume
  directional_hessian : ∀ j : Fin 3,
    Integrable (enstrophyDensity (firstDirectionalDerivative u j)) volume
  directional_second : ∀ j : Fin 3,
    Integrable (fun x =>
      ‖firstDirectionalDerivative u j x‖ *
        ‖fderiv ℝ (fderiv ℝ (firstDirectionalDerivative u j)) x‖) volume
  directional_laplacian_inner : ∀ j : Fin 3,
    Integrable (fun x =>
      ⟪firstDirectionalDerivative u j x,
        Δ (firstDirectionalDerivative u j) x⟫) volume
  base_primitive :
    Integrable (fun x => ‖Δ u x‖ * ‖fderiv ℝ u x‖) volume
  base_gradient_product :
    Integrable (fun x => ‖fderiv ℝ u x‖ * ‖fderiv ℝ (Δ u) x‖) volume
  base_second :
    Integrable (fun x => ‖Δ u x‖ * ‖fderiv ℝ (fderiv ℝ u) x‖) volume

/-! ## The integrated identity -/

/-- **The integrated Hessian--Laplacian identity** (manuscript
`prop:enstrophy`, `lem:plancherel`(ii)).

If `u : ℝ³ → ℝ³` is `C³` and satisfies the explicit whole-space
integration-by-parts package `h`, then

`∫ ‖D²u‖_F² = ∫ ‖Δu‖²`.

Here `hessianFrobeniusSq u` is the sum of the squares of all nine vector-valued
first-directional derivatives, hence exactly the squared Frobenius/Hilbert--
Schmidt Hessian norm.  The hypotheses are sufficient boundary-free `L¹`
conditions, not a claim that the manuscript's `H²` class or compact support
has already been connected to Lean's Bochner integrals.  This theorem proves
the identity itself, not the downstream `‖∇u‖₃` interpolation inequality.
-/
theorem hessian_laplacian_L2_identity
    {u : Space → Space} (hu : ContDiff ℝ 3 u)
    (h : HessianLaplacianIBPData u) :
    ∫ x, hessianFrobeniusSq u x = ∫ x, ‖Δ u x‖ ^ 2 := by
  have hdir_cd : ∀ j : Fin 3,
      ContDiff ℝ 2 (firstDirectionalDerivative u j) := by
    intro j
    have huf : ContDiff ℝ 2 (fderiv ℝ u) :=
      hu.fderiv_right (m := 2) (by norm_num)
    have hcomp := (ContinuousLinearMap.apply ℝ Space (e j)).contDiff.comp huf
    simpa [firstDirectionalDerivative, Function.comp_def] using hcomp

  have hdelta_cd : ContDiff ℝ 1 (Δ u) := by
    have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
      (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
    have hsum : Δ u = fun x =>
        ∑ i : Fin 3, fderiv ℝ (fderiv ℝ u) x (e i) (e i) :=
      funext (IBP.laplacian_eq_sum u)
    rw [hsum]
    refine ContDiff.sum fun i _ => ?_
    have hcomp := (ContinuousLinearMap.apply ℝ Space (e i)).contDiff.comp
      ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (e i)).contDiff.comp h2)
    simpa [Function.comp_def] using hcomp

  have hdirectional_green : ∀ j : Fin 3,
      ∫ x, ⟪firstDirectionalDerivative u j x,
          Δ (firstDirectionalDerivative u j) x⟫ =
        - ∫ x, enstrophyDensity (firstDirectionalDerivative u j) x := by
    intro j
    exact IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity
      (hdir_cd j) (h.directional_primitive j) (h.directional_hessian j)
      (h.directional_second j)

  have hdirectional_green_sum :
      ∑ j : Fin 3, ∫ x, enstrophyDensity (firstDirectionalDerivative u j) x =
        - ∫ x, ∑ j : Fin 3, ⟪firstDirectionalDerivative u j x,
          Δ (firstDirectionalDerivative u j) x⟫ := by
    calc
      ∑ j : Fin 3, ∫ x, enstrophyDensity (firstDirectionalDerivative u j) x =
          ∑ j : Fin 3, (- ∫ x, ⟪firstDirectionalDerivative u j x,
            Δ (firstDirectionalDerivative u j) x⟫) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              linarith [hdirectional_green j]
      _ = - ∑ j : Fin 3, ∫ x, ⟪firstDirectionalDerivative u j x,
          Δ (firstDirectionalDerivative u j) x⟫ := by
            rw [Finset.sum_neg_distrib]
      _ = - ∫ x, ∑ j : Fin 3, ⟪firstDirectionalDerivative u j x,
          Δ (firstDirectionalDerivative u j) x⟫ := by
            rw [integral_finsetSum (μ := (volume : Measure Space))
              (s := Finset.univ)
              (f := fun (j : Fin 3) (x : Space) =>
                ⟪firstDirectionalDerivative u j x,
                  Δ (firstDirectionalDerivative u j) x⟫)
              (fun j _ => h.directional_laplacian_inner j)]

  have hhessian_integral :
      ∫ x, hessianFrobeniusSq u x =
        ∑ j : Fin 3, ∫ x, enstrophyDensity (firstDirectionalDerivative u j) x := by
    unfold hessianFrobeniusSq
    exact integral_finsetSum (μ := (volume : Measure Space)) (s := Finset.univ)
      (f := fun (j : Fin 3) (x : Space) =>
        enstrophyDensity (firstDirectionalDerivative u j) x)
      (fun j _ => h.directional_hessian j)

  have hcomm_pointwise : ∀ x : Space,
      (∑ j : Fin 3, ⟪firstDirectionalDerivative u j x,
          Δ (firstDirectionalDerivative u j) x⟫) =
        frobeniusInner (fderiv ℝ u x) (fderiv ℝ (Δ u) x) := by
    intro x
    calc
      ∑ j : Fin 3, ⟪firstDirectionalDerivative u j x,
          Δ (firstDirectionalDerivative u j) x⟫ =
          ∑ j : Fin 3, ⟪fderiv ℝ u x (e j),
            fderiv ℝ (Δ u) x (e j)⟫ := by
              refine Finset.sum_congr rfl fun j _ => ?_
              simp only [firstDirectionalDerivative]
              rw [← laplacian_fderiv_dir_comm_euclidean hu x (e j)]
      _ = frobeniusInner (fderiv ℝ u x) (fderiv ℝ (Δ u) x) := by
            rfl

  have hcomm_integral :
      ∫ x, ∑ j : Fin 3, ⟪firstDirectionalDerivative u j x,
          Δ (firstDirectionalDerivative u j) x⟫ =
        ∫ x, frobeniusInner (fderiv ℝ u x) (fderiv ℝ (Δ u) x) :=
    integral_congr_ae (Filter.Eventually.of_forall hcomm_pointwise)

  have hbase := integral_frobenius_inner_eq_neg_integral_inner_laplacian hu
    hdelta_cd h.base_primitive h.base_gradient_product h.base_second
  have hbase_norm :
      ∫ x, ⟪Δ u x, Δ u x⟫ = ∫ x, ‖Δ u x‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_self_eq_norm_sq _)

  calc
    ∫ x, hessianFrobeniusSq u x =
        ∑ j : Fin 3, ∫ x, enstrophyDensity (firstDirectionalDerivative u j) x :=
      hhessian_integral
    _ = - ∫ x, ∑ j : Fin 3, ⟪firstDirectionalDerivative u j x,
        Δ (firstDirectionalDerivative u j) x⟫ :=
      hdirectional_green_sum
    _ = - ∫ x, frobeniusInner (fderiv ℝ u x) (fderiv ℝ (Δ u) x) := by
      rw [hcomm_integral]
    _ = - (- ∫ x, ⟪Δ u x, Δ u x⟫) := by rw [hbase]
    _ = ∫ x, ‖Δ u x‖ ^ 2 := by rw [hbase_norm]; ring

/-- **The norm form of the integrated Hessian--Laplacian identity** (manuscript
`prop:enstrophy`, `lem:plancherel`(ii)).  Under the same explicit assumptions
as `hessian_laplacian_L2_identity`, taking the nonnegative square-root of both
sides gives the paper's `‖D²u‖₂ = ‖Δu‖₂`, with the left `L²` norm defined from
the Frobenius/Hilbert--Schmidt density `hessianFrobeniusSq`.
-/
theorem hessian_laplacian_L2_norm_identity
    {u : Space → Space} (hu : ContDiff ℝ 3 u)
    (h : HessianLaplacianIBPData u) :
    Real.sqrt (∫ x, hessianFrobeniusSq u x) =
      Real.sqrt (∫ x, ‖Δ u x‖ ^ 2) := by
  rw [hessian_laplacian_L2_identity hu h]

end NavierFormal
