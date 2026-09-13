import NavierFormal.HessianLaplacian

/-! Independent targeted checks for the generic Hessian--Laplacian lane
(`prop:enstrophy`, open Hessian--Laplacian bridge). -/

open Laplacian

namespace NavierFormal

/-! A concrete zero-field oracle, proved independently of the exported
commutation theorem: the finite second-derivative trace of a constant field is
constant with zero derivative. -/
example (x v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ
        (secondDerivativeTrace (fun _ : Fin 2 => (0 : EuclideanSpace ℝ (Fin 2)))
          (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))) x v =
      secondDerivativeTrace (fun _ : Fin 2 => (0 : EuclideanSpace ℝ (Fin 2)))
        (fun y => fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) y v) x := by
  have htrace : secondDerivativeTrace
      (fun _ : Fin 2 => (0 : EuclideanSpace ℝ (Fin 2)))
      (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) =
      (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) := by
    funext y
    simp [secondDerivativeTrace]
  rw [htrace]
  simp [secondDerivativeTrace]

/-! The exported theorem separately specializes to the same non-dependent
scalar field and Mathlib's Laplacian notation. -/
example (x v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (Δ (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))) x v =
      Δ (fun y => fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) y v) x := by
  have hzero : ContDiff ℝ 3
      (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) :=
    contDiff_const
  exact laplacian_fderiv_dir_comm_euclidean hzero x v

/-! The generic trace theorem is also exercised independently of the
Laplacian notation, with an arbitrary finite family of directions. -/
example {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {b : ι → E} {φ : E → F} (hφ : ContDiff ℝ 3 φ) (x v : E) :
    fderiv ℝ (secondDerivativeTrace b φ) x v =
      secondDerivativeTrace b (fun y => fderiv ℝ φ y v) x :=
  fderiv_secondDerivativeTrace_comm hφ x v

#print axioms fderiv_dir_apply_eq_generic
#print axioms fderiv_dir_comm_generic
#print axioms fderiv_secondDerivativeTrace_comm
#print axioms laplacian_fderiv_dir_comm_euclidean

end NavierFormal
