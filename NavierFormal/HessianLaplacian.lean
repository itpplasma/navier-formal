import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Generic Hessian and Laplacian commutation

This file isolates the application-independent part of the open Hessian--Laplacian
bridge in manuscript `prop:enstrophy`.  It uses only Mathlib's symmetry theorem
for the second Fréchet derivative and its orthonormal-basis formula for the
Laplacian.

The trace lemma is deliberately stated for an arbitrary finite family of
directions.  When that family is an orthonormal basis of a finite-dimensional
Euclidean space, the final theorem identifies the trace with Mathlib's `Δ`.
No integrability, PDE, or dimension-three hypothesis is used here.

This file does not prove the analytic estimate
`‖D²u‖₂ = ‖Δu‖₂`; that remains the first downstream bridge needed by the
manuscript's `prop:enstrophy` interpolation step.
-/

open Laplacian

noncomputable section

namespace NavierFormal

/-! ## Generic Hessian bookkeeping -/

/-- The derivative of a directional derivative is the second Fréchet derivative.
This is the generic bookkeeping lemma used below for the open Hessian--Laplacian
bridge of manuscript `prop:enstrophy`. -/
theorem fderiv_dir_apply_eq_generic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E → F} (hφ : ContDiff ℝ 2 φ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fderiv ℝ φ) x w v := by
  have h2d : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hi : HasFDerivAt (fun y => fderiv ℝ φ y v)
      ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ φ) x)) x := by
    have h := (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x
      (h2d x).hasFDerivAt
    simpa [Function.comp_def] using h
  rw [hi.fderiv]
  simp

/-- For a `C²` map between arbitrary normed spaces, directional derivatives
commute:
`∂_w(∂_v φ) = ∂_v(∂_w φ)`.  This is the generic Hessian symmetry supplied by
Mathlib's `ContDiffAt.isSymmSndFDerivAt`, recorded here for the open
Hessian--Laplacian bridge of manuscript `prop:enstrophy`. -/
theorem fderiv_dir_comm_generic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E → F} (hφ : ContDiff ℝ 2 φ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ φ y w) x v := by
  rw [fderiv_dir_apply_eq_generic hφ x v w,
    fderiv_dir_apply_eq_generic hφ x w v]
  have hsymm : IsSymmSndFDerivAt ℝ φ x :=
    hφ.contDiffAt.isSymmSndFDerivAt (by simp)
  exact hsymm.eq w v

/-! ## A generic finite directional trace -/

/-- The trace of the second Fréchet derivative over a finite family of
directions.  For an orthonormal basis this is Mathlib's Laplacian, by
`InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`; the definition
is kept independent of inner-product and dimension assumptions so that the
commutation lemma itself is genuinely generic.  This supports the open
Hessian--Laplacian bridge of manuscript `prop:enstrophy`. -/
def secondDerivativeTrace
    {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : ι → E) (φ : E → F) (x : E) : F :=
  ∑ i, fderiv ℝ (fderiv ℝ φ) x (b i) (b i)

/-- A `C³` map commutes with a directional derivative after taking the finite
second-derivative trace:
`∂_v tr(D²φ) = tr(D²(∂_vφ))`.  The directions and the domain/codomain are
arbitrary; choosing an orthonormal basis turns this into the Laplacian theorem
below.  This is the smallest generic trace-level lemma supporting the open
Hessian--Laplacian bridge of manuscript `prop:enstrophy`. -/
theorem fderiv_secondDerivativeTrace_comm
    {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {b : ι → E} {φ : E → F} (hφ : ContDiff ℝ 3 φ) (x v : E) :
    fderiv ℝ (secondDerivativeTrace b φ) x v =
      secondDerivativeTrace b (fun y => fderiv ℝ φ y v) x := by
  classical
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hφf : ContDiff ℝ 2 (fderiv ℝ φ) :=
    hφ.fderiv_right (m := 2) (by norm_num)
  have hφff : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ φ)) :=
    hφf.fderiv_right (m := 1) (by norm_num)
  have hterm : ∀ i : ι, Differentiable ℝ
      (fun y => fderiv ℝ (fderiv ℝ φ) y (b i) (b i)) := by
    intro i
    have hfirst : ContDiff ℝ 1
        (fun y => fderiv ℝ (fderiv ℝ φ) y (b i)) := by
      have h := (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) (b i)).contDiff.comp hφff
      simpa [Function.comp_def] using h
    have hsecond : ContDiff ℝ 1
        (fun y => fderiv ℝ (fderiv ℝ φ) y (b i) (b i)) := by
      have h := (ContinuousLinearMap.apply ℝ F (b i)).contDiff.comp hfirst
      simpa [Function.comp_def] using h
    exact hsecond.differentiable one_ne_zero
  change fderiv ℝ
      (fun y => ∑ i, fderiv ℝ (fderiv ℝ φ) y (b i) (b i)) x v =
    ∑ i, fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ φ y v)) x (b i) (b i)
  have hsum : fderiv ℝ
      (fun y => ∑ i, fderiv ℝ (fderiv ℝ φ) y (b i) (b i)) x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ φ) y (b i) (b i)) x :=
    fderiv_fun_sum (fun i _ => (hterm i) x)
  rw [hsum]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hφbi : ContDiff ℝ 2 (fun y => fderiv ℝ φ y (b i)) := by
    have h := (ContinuousLinearMap.apply ℝ F (b i)).contDiff.comp hφf
    simpa [Function.comp_def] using h
  have hφv : ContDiff ℝ 2 (fun y => fderiv ℝ φ y v) := by
    have h := (ContinuousLinearMap.apply ℝ F v).contDiff.comp hφf
    simpa [Function.comp_def] using h
  have hpoint₁ :
      (fun y => fderiv ℝ (fderiv ℝ φ) y (b i) (b i)) =
        (fun y => fderiv ℝ (fun z => fderiv ℝ φ z (b i)) y (b i)) := by
    funext y
    exact (fderiv_dir_apply_eq_generic hφ2 y (b i) (b i)).symm
  have hpoint₂ :
      (fun y => fderiv ℝ (fun z => fderiv ℝ φ z (b i)) y v) =
        (fun y => fderiv ℝ (fun z => fderiv ℝ φ z v) y (b i)) := by
    funext y
    exact fderiv_dir_comm_generic hφ2 y (b i) v
  calc
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ φ) y (b i) (b i)) x v =
        fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ φ z (b i)) y v) x (b i) := by
          rw [hpoint₁, fderiv_dir_comm_generic hφbi x (b i) v]
    _ = fderiv ℝ
        (fun y => fderiv ℝ (fun z => fderiv ℝ φ z v) y (b i)) x (b i) := by
          rw [hpoint₂]
    _ = fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ φ y v)) x (b i) (b i) :=
      fderiv_dir_apply_eq_generic hφv x (b i) (b i)

/-- On `EuclideanSpace ℝ ι`, a `C³` map commutes with a directional derivative
and Mathlib's Laplacian:
`∂_v(Δφ) = Δ(∂_vφ)`.  The finite index type `ι` is arbitrary (not fixed to
dimension three), and the theorem supports the open Hessian--Laplacian bridge
of manuscript `prop:enstrophy`.  It proves only pointwise commutation; no
integrability or `L²` identity is claimed. -/
theorem laplacian_fderiv_dir_comm_euclidean
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : EuclideanSpace ℝ ι → F} (hφ : ContDiff ℝ 3 φ)
    (x v : EuclideanSpace ℝ ι) :
    fderiv ℝ (Δ φ) x v = Δ (fun y => fderiv ℝ φ y v) x := by
  classical
  let b : ι → EuclideanSpace ℝ ι := EuclideanSpace.basisFun ι ℝ
  have htrace (ψ : EuclideanSpace ℝ ι → F) :
      Δ ψ = secondDerivativeTrace b ψ := by
    funext y
    have h := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ψ
      (EuclideanSpace.basisFun ι ℝ)
    simpa [b, secondDerivativeTrace, iteratedFDeriv_two_apply] using congrFun h y
  rw [htrace φ, htrace (fun y => fderiv ℝ φ y v)]
  exact fderiv_secondDerivativeTrace_comm hφ x v

end NavierFormal
