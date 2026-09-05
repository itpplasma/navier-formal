import NavierFormal.Calculus
import NavierFormal.NormGradient

/-!
# The `∇|u|` form of the pressure-route densities (manuscript `prop:pressure`)

`NavierFormal/Calculus.lean` writes the pressure-route densities `D₃` and `P₃`
of the manuscript `../navier-paper/main.tex` through the transposed Jacobian
`(∇u)ᵀu` (`NavierFormal.gradTranspose`, amendment A2 / obligation P-0), while
the manuscript states them through `∇|u|`:

```
D₃ = ∫ (|u| |∇u|² + |u| |∇|u||²),      P₃ = ∫ p u·∇|u|.
```

This module proves the pointwise dictionary between the two forms at a point
where `u` is differentiable, together with the zero-set convention and the
`ε`-regularized statements that the manuscript's proof of `prop:pressure`
actually uses.  The steps of the manuscript that are formalized here:

* the chain rule of `prop:pressure`, in the two forms
  `d|u|(x)h = ⟪(∇u)ᵀu, h⟫ / |u|` and `∇|u|(x) = |u|⁻¹ (∇u)ᵀu`
  (`fderiv_norm_apply_eq_inner_gradTranspose_div`,
  `gradient_norm_eq_smul_gradTranspose`);
* the identification of the second `D₃` integrand,
  `|(∇u)ᵀu|²/|u| = |u| |∇|u||²`, hence
  `D₃ density = |u| ‖∇u‖_F² + |u| |∇|u||²`
  (`norm_gradTranspose_sq_div_eq`, `D3density_eq_gradient_norm`);
* the identification of the `P₃` integrand, `P₃ density = p (u·∇|u|)`
  (`P3density_eq_gradient_norm`);
* the manuscript's convention "the integrand is zero at `u = 0`", where both
  densities and `∇|u|` itself vanish (`gradient_norm_of_zero`,
  `D3density_of_zero`, `P3density_of_zero`);
* the regularized chain rule `d r_ε(u)(x)h = ⟪(∇u)ᵀu, h⟫ / r_ε(u(x))` and
  `∇ r_ε(u) = r_ε(u)⁻¹ (∇u)ᵀu` (`fderiv_rEps_apply_inner_gradTranspose`,
  `gradient_rEps_eq_smul_gradTranspose`);
* the divergence identity quoted in the proof of `prop:pressure`,
  `div(r_ε u) = (|u|/r_ε) u·∇|u|` for a solenoidal field
  (`divergence_rEps_smul`, `divergence_rEps_smul_eq_gradient_norm`), with the
  zero-set case recorded separately (`divergence_rEps_smul_of_zero`).

Nothing in this file is a theorem about the Millennium problem.
-/

namespace NavierFormal

open scoped RealInnerProductSpace

noncomputable section

variable {u : Space → Space} {p : Space → ℝ} {x : Space} {ε : ℝ}

/-! ## The chain rule for `|u|` in transposed-Jacobian form -/

/-- Manuscript `prop:pressure`, chain rule for `|u|` in the `(∇u)ᵀu` form of
obligation P-0: where `u` is differentiable and `u x ≠ 0`,
`d|u|(x)h = ⟪(∇u)ᵀu, h⟫ / |u|`.  This is
`NavierFormal.fderiv_norm_apply_of_ne_zero` with the inner product moved onto the
adjoint via `NavierFormal.inner_gradTranspose_left`. -/
theorem fderiv_norm_apply_eq_inner_gradTranspose_div (hu : DifferentiableAt ℝ u x)
    (hx : u x ≠ 0) (h : Space) :
    fderiv ℝ (fun y => ‖u y‖) x h = ⟪gradTranspose u x, h⟫ / ‖u x‖ := by
  rw [fderiv_norm_apply_of_ne_zero hu hx, inner_gradTranspose_left]

/-- Manuscript `prop:pressure`, chain rule for `|u|` in gradient form:
`∇|u|(x) = |u(x)|⁻¹ (∇u)ᵀu(x)` where `u` is differentiable and `u x ≠ 0`.  This
is the pointwise bridge between the manuscript's `∇|u|` and the
transposed-Jacobian vector of `NavierFormal.Calculus`. -/
theorem gradient_norm_eq_smul_gradTranspose (hu : DifferentiableAt ℝ u x) (hx : u x ≠ 0) :
    gradient (fun y => ‖u y‖) x = (‖u x‖)⁻¹ • gradTranspose u x := by
  refine ext_inner_right ℝ fun h => ?_
  rw [inner_gradient_apply, fderiv_norm_apply_eq_inner_gradTranspose_div hu hx,
    real_inner_smul_left, div_eq_inv_mul]

/-- The transposed Jacobian recovered from the manuscript's `∇|u|`:
`(∇u)ᵀu = |u| ∇|u|` where `u` is differentiable and `u x ≠ 0`. -/
theorem gradTranspose_eq_smul_gradient_norm (hu : DifferentiableAt ℝ u x) (hx : u x ≠ 0) :
    gradTranspose u x = ‖u x‖ • gradient (fun y => ‖u y‖) x := by
  rw [gradient_norm_eq_smul_gradTranspose hu hx, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

/-- Manuscript `prop:pressure`: the length of `∇|u|` is `|(∇u)ᵀu| / |u|`. -/
theorem norm_gradient_norm_eq (hu : DifferentiableAt ℝ u x) (hx : u x ≠ 0) :
    ‖gradient (fun y => ‖u y‖) x‖ = ‖gradTranspose u x‖ / ‖u x‖ := by
  rw [gradient_norm_eq_smul_gradTranspose hu hx, norm_smul, norm_inv, norm_norm,
    div_eq_inv_mul]

/-! ## The `D₃` density in the manuscript's `∇|u|` form -/

/-- Manuscript `prop:pressure`, second `D₃` integrand: `|(∇u)ᵀu|²/|u| = |u| |∇|u||²`
where `u` is differentiable and `u x ≠ 0`.  This is the identity that turns the
`(∇u)ᵀu`-form density of `NavierFormal.D3density` into the manuscript's
`|u| |∇u|² + |u| |∇|u||²`. -/
theorem norm_gradTranspose_sq_div_eq (hu : DifferentiableAt ℝ u x) (hx : u x ≠ 0) :
    ‖gradTranspose u x‖ ^ 2 / ‖u x‖ = ‖u x‖ * ‖gradient (fun y => ‖u y‖) x‖ ^ 2 := by
  have hn : ‖u x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [norm_gradient_norm_eq hu hx, div_pow]
  field_simp

/-- Manuscript `prop:pressure`, the `D₃` density in the form printed in the
manuscript: at a point of differentiability with `u x ≠ 0`,
`D₃ density = |u| ‖∇u‖_F² + |u| |∇|u||²`.  The Frobenius convention for
`‖∇u‖_F²` is the one of `NavierFormal.frobeniusNormSq` (design risk R-NORM). -/
theorem D3density_eq_gradient_norm (hu : DifferentiableAt ℝ u x) (hx : u x ≠ 0) :
    D3density u x
      = ‖u x‖ * frobeniusNormSq (fderiv ℝ u x)
        + ‖u x‖ * ‖gradient (fun y => ‖u y‖) x‖ ^ 2 := by
  rw [D3density, norm_gradTranspose_sq_div_eq hu hx]

/-- Manuscript `prop:pressure`, the `D₃` density with the enstrophy density
abbreviated: `D₃ density = |u| ‖∇u‖_F² + |u| |∇|u||²`. -/
theorem D3density_eq_enstrophy_add_gradient_norm (hu : DifferentiableAt ℝ u x)
    (hx : u x ≠ 0) :
    D3density u x
      = ‖u x‖ * enstrophyDensity u x + ‖u x‖ * ‖gradient (fun y => ‖u y‖) x‖ ^ 2 :=
  D3density_eq_gradient_norm hu hx

/-! ## The `P₃` density in the manuscript's `p u·∇|u|` form -/

/-- Manuscript `prop:pressure`: the contraction of `u` with `∇|u|` is
`⟪u, (∇u)ᵀu⟫ / |u|`, i.e. the manuscript's `u·∇|u|`. -/
theorem inner_self_gradient_norm (hu : DifferentiableAt ℝ u x) (hx : u x ≠ 0) :
    ⟪u x, gradient (fun y => ‖u y‖) x⟫ = ⟪u x, gradTranspose u x⟫ / ‖u x‖ := by
  rw [gradient_norm_eq_smul_gradTranspose hu hx, real_inner_smul_right, div_eq_inv_mul]

/-- Manuscript `prop:pressure`, the `P₃` density in the form printed in the
manuscript: at a point of differentiability with `u x ≠ 0`,
`P₃ density = p (u·∇|u|)`. -/
theorem P3density_eq_gradient_norm (hu : DifferentiableAt ℝ u x) (hx : u x ≠ 0) :
    P3density p u x = p x * ⟪u x, gradient (fun y => ‖u y‖) x⟫ := by
  rw [P3density_eq_mul_div, inner_self_gradient_norm hu hx]

/-! ## The zero set: the manuscript's convention `integrand = 0` at `u = 0` -/

/-- Manuscript `prop:pressure`, `∇|u| = 0` on the zero set of `u`: at a point
where `u x = 0` the gradient of the speed vanishes, because `x` is a global
minimum of `y ↦ ‖u y‖` (`NavierFormal.fderiv_norm_eq_zero_of_eq_zero`).  No
differentiability of `u` is needed. -/
@[simp]
theorem gradient_norm_of_zero (hx : u x = 0) : gradient (fun y => ‖u y‖) x = 0 := by
  rw [gradient, fderiv_norm_eq_zero_of_eq_zero hx, map_zero]

/-- Manuscript `prop:pressure`, the `D₃` integrand "is zero at `u = 0`": both the
`(∇u)ᵀu` form of `NavierFormal.D3density` and the manuscript's
`|u| |∇u|² + |u| |∇|u||²` vanish there. -/
@[simp]
theorem D3density_of_zero (hx : u x = 0) : D3density u x = 0 :=
  D3density_eq_zero_of_eq_zero hx

/-- Manuscript `prop:pressure`, the manuscript's `D₃` integrand at `u = 0`. -/
theorem D3density_gradient_norm_of_zero (hx : u x = 0) :
    ‖u x‖ * frobeniusNormSq (fderiv ℝ u x)
        + ‖u x‖ * ‖gradient (fun y => ‖u y‖) x‖ ^ 2 = 0 := by
  simp [hx]

/-- Manuscript `prop:pressure`, the `P₃` integrand is zero at `u = 0`. -/
@[simp]
theorem P3density_of_zero (hx : u x = 0) : P3density p u x = 0 :=
  P3density_eq_zero_of_eq_zero hx

/-- Manuscript `prop:pressure`, the manuscript's `P₃` integrand at `u = 0`. -/
theorem P3density_gradient_norm_of_zero (hx : u x = 0) :
    p x * ⟪u x, gradient (fun y => ‖u y‖) x⟫ = 0 := by
  simp [hx]

/-! ## The regularized speed `r_ε` -/

/-- Manuscript `prop:pressure`, regularized chain rule in the `(∇u)ᵀu` form: for
`ε > 0` and `u` differentiable at `x`,
`d r_ε(u)(x) h = ⟪(∇u)ᵀu, h⟫ / r_ε(u(x))`.  Proved from
`NavierFormal.hasFDerivAt_rEps`; as `ε ↓ 0` at a point with `u x ≠ 0` the
right-hand side becomes `d|u|(x)h`. -/
theorem fderiv_rEps_apply_inner_gradTranspose (hε : 0 < ε) (hu : DifferentiableAt ℝ u x)
    (h : Space) :
    fderiv ℝ (fun y => rEps ε (u y)) x h = ⟪gradTranspose u x, h⟫ / rEps ε (u x) := by
  rw [(hasFDerivAt_rEps hε hu.hasFDerivAt).fderiv, rEps_fderiv_apply,
    inner_gradTranspose_left]

/-- Manuscript `prop:pressure`, regularized chain rule in gradient form:
`∇ r_ε(u)(x) = r_ε(u(x))⁻¹ (∇u)ᵀu(x)`, the `ε`-regularization of
`∇|u| = |u|⁻¹ (∇u)ᵀu`. -/
theorem gradient_rEps_eq_smul_gradTranspose (hε : 0 < ε) (hu : DifferentiableAt ℝ u x) :
    gradient (fun y => rEps ε (u y)) x = (rEps ε (u x))⁻¹ • gradTranspose u x := by
  refine ext_inner_right ℝ fun h => ?_
  rw [inner_gradient_apply, fderiv_rEps_apply_inner_gradTranspose hε hu,
    real_inner_smul_left, div_eq_inv_mul]

/-! ## The divergence of the tested field `r_ε u` -/

/-- The contraction of the transposed Jacobian with the field itself, summed in
the standard basis: `∑ᵢ uᵢ ⟪u, ∂ᵢu⟫ = ⟪u, (∇u)u⟫ = ⟪(∇u)ᵀu, u⟫`. -/
theorem sum_component_inner_fderiv (u : Space → Space) (x : Space) :
    ∑ i, (u x) i * ⟪u x, fderiv ℝ u x (e i)⟫ = ⟪gradTranspose u x, u x⟫ := by
  have hsum : fderiv ℝ u x (u x) = ∑ i, (u x) i • fderiv ℝ u x (e i) := by
    conv_lhs => rw [← sum_smul_e (u x)]
    simp
  rw [inner_gradTranspose_left, hsum, inner_sum]
  simp [real_inner_smul_right]

/-- Manuscript `prop:pressure`, product rule for the tested field `r_ε u`:
`div(r_ε u) = ⟪(∇u)ᵀu, u⟫ / r_ε + r_ε (∇·u)`.  The first term is the
manuscript's `(|u|/r_ε) u·∇|u|`, the second vanishes by incompressibility. -/
theorem divergence_rEps_smul_add (hε : 0 < ε) (hu : DifferentiableAt ℝ u x) :
    divergence (fun y => rEps ε (u y) • u y) x
      = ⟪gradTranspose u x, u x⟫ / rEps ε (u x) + rEps ε (u x) * divergence u x := by
  have hfd := (hasFDerivAt_rEps_smul hε hu.hasFDerivAt).fderiv
  have hterm : ∀ i : Fin 3,
      ⟪e i, fderiv ℝ (fun y => rEps ε (u y) • u y) x (e i)⟫
        = (u x) i * ⟪u x, fderiv ℝ u x (e i)⟫ / rEps ε (u x)
          + rEps ε (u x) * ⟪e i, fderiv ℝ u x (e i)⟫ := by
    intro i
    rw [hfd, rEps_smul_fderiv_apply, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, inner_e]
    ring
  rw [divergence, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    ← Finset.sum_div, sum_component_inner_fderiv, ← Finset.mul_sum, divergence]

/-- Manuscript `prop:pressure`, the divergence identity for the tested field of a
solenoidal velocity: if `∇·u(x) = 0` then
`div(r_ε u)(x) = ⟪(∇u)ᵀu, u⟫ / r_ε(u(x))`. -/
theorem divergence_rEps_smul (hε : 0 < ε) (hu : DifferentiableAt ℝ u x)
    (hdiv : divergence u x = 0) :
    divergence (fun y => rEps ε (u y) • u y) x
      = ⟪gradTranspose u x, u x⟫ / rEps ε (u x) := by
  rw [divergence_rEps_smul_add hε hu, hdiv, mul_zero, add_zero]

/-- Manuscript `prop:pressure`, the `∇|u|` reading of the divergence identity's
right-hand side: `⟪(∇u)ᵀu, u⟫ / r_ε = (|u|/r_ε) u·∇|u|`.  The identity holds at
every point of differentiability: where `u x = 0` both sides are `0`, since
`(∇u)ᵀu` and `∇|u|` vanish there. -/
theorem inner_gradTranspose_self_div_rEps_eq (hε : 0 < ε) (hu : DifferentiableAt ℝ u x) :
    ⟪gradTranspose u x, u x⟫ / rEps ε (u x)
      = (‖u x‖ / rEps ε (u x)) * ⟪u x, gradient (fun y => ‖u y‖) x⟫ := by
  by_cases hx : u x = 0
  · have hg : gradTranspose u x = 0 := by simp [gradTranspose, hx]
    simp [hg, hx]
  · have hn : ‖u x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hr : rEps ε (u x) ≠ 0 := (rEps_pos hε (u x)).ne'
    rw [inner_self_gradient_norm hu hx, real_inner_comm]
    field_simp

/-- Manuscript `prop:pressure`, the divergence identity as printed in the
manuscript: for `ε > 0`, `u` differentiable at `x` and `∇·u(x) = 0`,
`div(r_ε u) = (|u|/r_ε) u·∇|u|`. -/
theorem divergence_rEps_smul_eq_gradient_norm (hε : 0 < ε) (hu : DifferentiableAt ℝ u x)
    (hdiv : divergence u x = 0) :
    divergence (fun y => rEps ε (u y) • u y) x
      = (‖u x‖ / rEps ε (u x)) * ⟪u x, gradient (fun y => ‖u y‖) x⟫ := by
  rw [divergence_rEps_smul hε hu hdiv, inner_gradTranspose_self_div_rEps_eq hε hu]

/-- Manuscript `prop:pressure`, the divergence identity on the zero set of `u`,
where the manuscript's convention makes both sides vanish: at a point with
`u x = 0` and `∇·u(x) = 0` one has `div(r_ε u)(x) = 0` and
`(|u|/r_ε) u·∇|u| = 0`. -/
theorem divergence_rEps_smul_of_zero (hε : 0 < ε) (hu : DifferentiableAt ℝ u x)
    (hdiv : divergence u x = 0) (hx : u x = 0) :
    divergence (fun y => rEps ε (u y) • u y) x = 0
      ∧ (‖u x‖ / rEps ε (u x)) * ⟪u x, gradient (fun y => ‖u y‖) x⟫ = 0 := by
  have hg : gradTranspose u x = 0 := by simp [gradTranspose, hx]
  refine ⟨?_, by simp [hx]⟩
  rw [divergence_rEps_smul hε hu hdiv, hg]
  simp

end

end NavierFormal
