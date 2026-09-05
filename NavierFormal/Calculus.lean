import NavierFormal.Basic
import NavierFormal.Regularization
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Pointwise vector calculus on `ℝ³` for the CP1 statement surface

This module realizes §2.1 of the CP01 statement-surface design
(`itpplasma/navier:research/evidence/cp01-lean-statement-design.md`) with the
controller amendments A1–A3: the state space is `NavierFormal.Space`, and the
pressure-route densities `D₃` and `P₃` of the manuscript
`../navier-paper/main.tex` are written through the transposed Jacobian
`(∇u)ᵀu` (obligation P-0), never through `∇|u|`.

Objects defined here:

* `NavierFormal.e i` — the standard basis of `Space = ℝ³`;
* `NavierFormal.divergence v` — `∇·v`, the trace of the Fréchet derivative;
* `NavierFormal.frobeniusNormSq L`, `NavierFormal.frobeniusNorm L` — the
  Hilbert–Schmidt (Frobenius) norm `‖L‖_F² = ∑_{ij} L_{ij}²` of a linear map,
  with the two-sided comparison `‖L‖ ≤ ‖L‖_F ≤ √3 ‖L‖` to the operator norm;
* `NavierFormal.enstrophyDensity v x = ‖∇v(x)‖_F²` — the manuscript's
  pointwise enstrophy density (norm convention R-NORM);
* `NavierFormal.convection v x = (v·∇)v (x)`;
* `NavierFormal.gradTranspose v x = (∇v(x))ᵀ v(x)`, written with
  `ContinuousLinearMap.adjoint` on `Space`;
* `NavierFormal.kineticEnergy`, `NavierFormal.kineticEnergyLintegral`,
  `NavierFormal.X3`, `NavierFormal.X3Real` — `∫|v|²` and `∫|v|³`;
* `NavierFormal.D3density`, `NavierFormal.D3`, `NavierFormal.P3density`,
  `NavierFormal.P3` — the pressure-route dissipation and pressure work of
  Proposition `prop:pressure`.

Conventions.

* The **Frobenius** (Hilbert–Schmidt) norm of `L : Space →L[ℝ] Space` is
  `‖L‖_F² = ∑_j ‖L eⱼ‖²`, i.e. the sum of the squares of all nine matrix
  entries in the standard basis.  It is *not* the operator norm `‖L‖` that
  Mathlib's `NormedAddCommGroup` instance on `Space →L[ℝ] Space` carries; the
  two differ by a factor of at most `√3`, and the manuscript's identities are
  false with the operator norm (design risk R-NORM).
* The **Euclidean** norm and inner product on `Space` are Mathlib's
  `EuclideanSpace ℝ (Fin 3)` instances; `⟪x, y⟫` is `inner ℝ x y`.
* The **Laplacian** of a vector field is Mathlib's `Δ`
  (`InnerProductSpace.instLaplacian`, `Mathlib/Analysis/InnerProductSpace/Laplacian.lean`),
  i.e. the trace of the second derivative; no separate definition is
  introduced here.  `laplacian_eq_sum_iteratedFDeriv` exhibits it as
  `∑ᵢ ∂ᵢ²`.
* The **gradient** of a scalar field is Mathlib's `gradient`
  (`Mathlib/Analysis/Calculus/Gradient/Basic.lean`), the Riesz representative
  of the Fréchet derivative; `inner_gradient_eq_fderiv` is the defining
  relation used in the manuscript's integrations by parts.
* Division by `‖v x‖` uses Lean's `a / 0 = 0`, which is exactly the
  manuscript's convention "the integrand vanishes where `u = 0`"
  (obligation P-0, design risk R-P0).
* No viscosity appears in this file; every definition is `ν`-free, so the free
  parameter `ν > 0` of amendment A3 is carried by the modules that state the
  equation.

Nothing in this file is a theorem about the Millennium problem.
-/

namespace NavierFormal

open MeasureTheory Laplacian
open scoped RealInnerProductSpace ENNReal

noncomputable section

/-! ## The standard basis of `ℝ³` -/

/-- The `i`-th standard basis vector of `Space = ℝ³`.  This is the `i`-th
vector of Mathlib's orthonormal basis `EuclideanSpace.basisFun`. -/
def e (i : Fin 3) : Space := EuclideanSpace.single i (1 : ℝ)

/-- `e i` is the `i`-th vector of the standard orthonormal basis of `ℝ³`. -/
theorem e_eq_basisFun (i : Fin 3) : e i = EuclideanSpace.basisFun (Fin 3) ℝ i :=
  (EuclideanSpace.basisFun_apply (Fin 3) ℝ i).symm

/-- The standard basis of `ℝ³` is normalized. -/
@[simp]
theorem norm_e (i : Fin 3) : ‖e i‖ = 1 := by
  rw [e_eq_basisFun]
  exact (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one i

/-- Expansion of a vector of `ℝ³` in the standard basis. -/
theorem sum_smul_e (x : Space) : ∑ i, x i • e i = x := by
  simpa [e_eq_basisFun] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x

/-- The `i`-th component of a vector of `ℝ³` is its inner product with `e i`. -/
theorem inner_e (x : Space) (i : Fin 3) : ⟪e i, x⟫ = x i := by
  rw [e_eq_basisFun]
  exact EuclideanSpace.basisFun_inner (Fin 3) ℝ x i

/-! ## The Frobenius norm of a Jacobian, and its comparison with the operator norm -/

/-- The Frobenius (Hilbert–Schmidt) squared norm `‖L‖_F² = ∑ⱼ ‖L eⱼ‖² = ∑ᵢⱼ L_{ij}²`
of a linear map of `ℝ³`.  This is the pointwise density used by the manuscript's
`‖∇u‖₂²`; it is **not** the operator norm `‖L‖` (design risk R-NORM). -/
def frobeniusNormSq (L : Space →L[ℝ] Space) : ℝ := ∑ j, ‖L (e j)‖ ^ 2

/-- The Frobenius (Hilbert–Schmidt) norm `‖L‖_F = (∑ᵢⱼ L_{ij}²)^{1/2}` of a linear
map of `ℝ³`. -/
def frobeniusNorm (L : Space →L[ℝ] Space) : ℝ := Real.sqrt (frobeniusNormSq L)

theorem frobeniusNormSq_nonneg (L : Space →L[ℝ] Space) : 0 ≤ frobeniusNormSq L :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem frobeniusNorm_nonneg (L : Space →L[ℝ] Space) : 0 ≤ frobeniusNorm L :=
  Real.sqrt_nonneg _

@[simp]
theorem frobeniusNorm_sq (L : Space →L[ℝ] Space) :
    frobeniusNorm L ^ 2 = frobeniusNormSq L :=
  Real.sq_sqrt (frobeniusNormSq_nonneg L)

/-- One half of the comparison `‖L‖ ≤ ‖L‖_F ≤ √3 ‖L‖`: the operator norm is
dominated by the Frobenius norm.  Proof: expand in the standard basis and apply
the Cauchy–Schwarz inequality. -/
theorem opNorm_le_frobeniusNorm (L : Space →L[ℝ] Space) : ‖L‖ ≤ frobeniusNorm L := by
  refine L.opNorm_le_bound (frobeniusNorm_nonneg L) fun x => ?_
  have hx : L x = ∑ i, x i • L (e i) := by
    conv_lhs => rw [← sum_smul_e x]
    simp
  calc ‖L x‖ = ‖∑ i, x i • L (e i)‖ := by rw [hx]
    _ ≤ ∑ i, ‖x i • L (e i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖L (e i)‖ := by simp [norm_smul]
    _ ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ i, ‖L (e i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = frobeniusNorm L * ‖x‖ := by
        rw [← EuclideanSpace.norm_eq x, frobeniusNorm, frobeniusNormSq, mul_comm]

/-- The squared form of the other half of `‖L‖ ≤ ‖L‖_F ≤ √3 ‖L‖`: in dimension
three, `‖L‖_F² ≤ 3‖L‖²`. -/
theorem frobeniusNormSq_le_three_mul (L : Space →L[ℝ] Space) :
    frobeniusNormSq L ≤ 3 * ‖L‖ ^ 2 := by
  have h : ∀ j : Fin 3, ‖L (e j)‖ ^ 2 ≤ ‖L‖ ^ 2 := by
    intro j
    have h1 : ‖L (e j)‖ ≤ ‖L‖ := by
      simpa [norm_e] using L.le_opNorm (e j)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc frobeniusNormSq L ≤ ∑ _j : Fin 3, ‖L‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => h j
    _ = 3 * ‖L‖ ^ 2 := by simp

/-- The comparison `‖L‖_F ≤ √3 ‖L‖` of the Frobenius norm with the operator norm
in dimension three. -/
theorem frobeniusNorm_le_sqrt_three_mul (L : Space →L[ℝ] Space) :
    frobeniusNorm L ≤ Real.sqrt 3 * ‖L‖ := by
  have h : frobeniusNorm L ≤ Real.sqrt (3 * ‖L‖ ^ 2) :=
    Real.sqrt_le_sqrt (frobeniusNormSq_le_three_mul L)
  calc frobeniusNorm L ≤ Real.sqrt (3 * ‖L‖ ^ 2) := h
    _ = Real.sqrt 3 * ‖L‖ := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg L)]

/-- The squared form of `‖L‖ ≤ ‖L‖_F`. -/
theorem opNorm_sq_le_frobeniusNormSq (L : Space →L[ℝ] Space) :
    ‖L‖ ^ 2 ≤ frobeniusNormSq L := by
  have := opNorm_le_frobeniusNorm L
  calc ‖L‖ ^ 2 ≤ frobeniusNorm L ^ 2 := pow_le_pow_left₀ (norm_nonneg L) this 2
    _ = frobeniusNormSq L := frobeniusNorm_sq L

/-- The bound `‖L y‖ ≤ ‖L‖_F ‖y‖` used pointwise in the pressure route. -/
theorem norm_apply_le_frobeniusNorm_mul (L : Space →L[ℝ] Space) (y : Space) :
    ‖L y‖ ≤ frobeniusNorm L * ‖y‖ :=
  (L.le_opNorm y).trans (mul_le_mul_of_nonneg_right (opNorm_le_frobeniusNorm L) (norm_nonneg y))

/-! ## Differential operators on `ℝ³` -/

/-- The divergence `∇·v = ∑ᵢ ∂ᵢvᵢ` of a vector field, defined as the trace
`∑ᵢ ⟪eᵢ, ∂ᵢ v⟫` of its Fréchet derivative.  Junk value `0` where `v` fails to be
differentiable, as for `fderiv`.  This is the manuscript's incompressibility
operator in `∇·u = 0`. -/
def divergence (v : Space → Space) (x : Space) : ℝ :=
  ∑ i, ⟪e i, fderiv ℝ v x (e i)⟫

/-- The divergence written in components: `∇·v = ∑ᵢ (∂ᵢv)ᵢ`. -/
theorem divergence_eq_sum_component (v : Space → Space) (x : Space) :
    divergence v x = ∑ i, (fderiv ℝ v x (e i)) i := by
  simp [divergence, inner_e]

/-- The manuscript's Laplacian `Δv = ∑ᵢ ∂ᵢ²v` of a vector field is Mathlib's `Δ`
(`InnerProductSpace.instLaplacian`): the trace of the second derivative, computed
in the standard orthonormal basis of `ℝ³`.  No separate definition of the
Laplacian is introduced in this development. -/
theorem laplacian_eq_sum_iteratedFDeriv (v : Space → Space) (x : Space) :
    Δ v x = ∑ i, iteratedFDeriv ℝ 2 v x ![e i, e i] := by
  have h := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis v
    (EuclideanSpace.basisFun (Fin 3) ℝ)
  simp only [e_eq_basisFun]
  exact congrFun h x

/-- The manuscript's `∇p` for a scalar field is Mathlib's `gradient`, the Riesz
representative of the Fréchet derivative: `⟪∇p(x), h⟫ = dp(x)h`.  This is the
relation used in every integration by parts against the pressure. -/
theorem inner_gradient_apply (q : Space → ℝ) (x h : Space) :
    ⟪gradient q x, h⟫ = fderiv ℝ q x h :=
  inner_gradient_left

/-- The gradient of a scalar field in components: `(∇q)ᵢ = ∂ᵢq`. -/
theorem gradient_component (q : Space → ℝ) (x : Space) (i : Fin 3) :
    gradient q x i = fderiv ℝ q x (e i) := by
  rw [← inner_e (gradient q x) i, real_inner_comm, inner_gradient_apply]

/-- The pointwise enstrophy density `‖∇v(x)‖_F² = ∑ᵢⱼ (∂ⱼvᵢ)²` of the manuscript's
enstrophy `Y = ∫ ‖∇u‖²`.  The Frobenius convention is essential: with the operator
norm the manuscript's identities are false (design risk R-NORM). -/
def enstrophyDensity (v : Space → Space) (x : Space) : ℝ :=
  frobeniusNormSq (fderiv ℝ v x)

theorem enstrophyDensity_nonneg (v : Space → Space) (x : Space) :
    0 ≤ enstrophyDensity v x :=
  frobeniusNormSq_nonneg _

/-- The convection term `(v·∇)v (x) = ∑ⱼ vⱼ ∂ⱼ v (x)`, i.e. the Fréchet derivative
of `v` at `x` evaluated in the direction `v x`. -/
def convection (v : Space → Space) (x : Space) : Space := fderiv ℝ v x (v x)

/-- The transposed-Jacobian field `(∇v)ᵀv` of the manuscript's pressure route,
written with the adjoint of the Fréchet derivative on `Space`.  Its components are
`((∇v)ᵀv)ⱼ = ⟪v, ∂ⱼv⟫ = ½ ∂ⱼ|v|²`, so that on `{v ≠ 0}` one has
`(∇v)ᵀv = |v| ∇|v|`.  Amendment A2 (obligation P-0): the whole pressure route is
written through this vector, never through `∇|v|`. -/
def gradTranspose (v : Space → Space) (x : Space) : Space :=
  ContinuousLinearMap.adjoint (fderiv ℝ v x) (v x)

/-- The defining property of `(∇v)ᵀv`: `⟪(∇v)ᵀv, h⟫ = ⟪v, (∇v)h⟫` for every
direction `h`. -/
theorem inner_gradTranspose_left (v : Space → Space) (x h : Space) :
    ⟪gradTranspose v x, h⟫ = ⟪v x, fderiv ℝ v x h⟫ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

/-- Components of `(∇v)ᵀv`: `((∇v)ᵀv)ⱼ = ⟪v, ∂ⱼv⟫`, half the `j`-th partial
derivative of `|v|²`. -/
theorem gradTranspose_component (v : Space → Space) (x : Space) (j : Fin 3) :
    gradTranspose v x j = ⟪v x, fderiv ℝ v x (e j)⟫ := by
  rw [← inner_e (gradTranspose v x) j, real_inner_comm, inner_gradTranspose_left]

/-- Contraction of `(∇v)ᵀv` with `v` is the convection term tested against `v`:
`⟪v, (∇v)ᵀv⟫ = ⟪(v·∇)v, v⟫`.  Divided by `|v|`, this is the manuscript's
`v·∇|v|`. -/
theorem inner_self_gradTranspose (v : Space → Space) (x : Space) :
    ⟪v x, gradTranspose v x⟫ = ⟪convection v x, v x⟫ :=
  ContinuousLinearMap.adjoint_inner_right _ _ _

/-- The pointwise bound `|(∇v)ᵀv| ≤ ‖∇v‖_F |v|`, the elementary ingredient of the
Cauchy–Schwarz step in the manuscript's pressure route. -/
theorem norm_gradTranspose_le (v : Space → Space) (x : Space) :
    ‖gradTranspose v x‖ ≤ frobeniusNorm (fderiv ℝ v x) * ‖v x‖ := by
  have hadj : ‖ContinuousLinearMap.adjoint (fderiv ℝ v x)‖ = ‖fderiv ℝ v x‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  calc ‖gradTranspose v x‖
      ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ v x)‖ * ‖v x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ v x‖ * ‖v x‖ := by rw [hadj]
    _ ≤ frobeniusNorm (fderiv ℝ v x) * ‖v x‖ :=
        mul_le_mul_of_nonneg_right (opNorm_le_frobeniusNorm _) (norm_nonneg _)

/-! ## Integral quantities -/

/-- The kinetic energy `∫ |v|²` of the manuscript's energy identity, as a Bochner
integral.  Junk value `0` when `|v|²` is not integrable; the extended-real
`kineticEnergyLintegral` is the junk-free version used where finiteness is a
conclusion rather than a hypothesis (design risk R-JUNK). -/
def kineticEnergy (v : Space → Space) : ℝ := ∫ x, ‖v x‖ ^ 2

/-- The kinetic energy `∫ |v|²` as a Lebesgue integral in `ℝ≥0∞`; equals `⊤`
exactly when `v ∉ L²`. -/
def kineticEnergyLintegral (v : Space → Space) : ℝ≥0∞ := ∫⁻ x, ‖v x‖ₑ ^ 2

/-- The manuscript's critical quantity `X = ‖v‖₃³ = ∫ |v|³`, as a Lebesgue integral
in `ℝ≥0∞`; equals `⊤` exactly when `v ∉ L³`. -/
def X3 (v : Space → Space) : ℝ≥0∞ := ∫⁻ x, ‖v x‖ₑ ^ 3

/-- The manuscript's critical quantity `X = ‖v‖₃³ = ∫ |v|³` as a real number.
Junk value `0` when `|v|³` is not integrable; use it only under an integrability
hypothesis (design risk R-JUNK). -/
def X3Real (v : Space → Space) : ℝ := ∫ x, ‖v x‖ ^ 3

theorem kineticEnergy_nonneg (v : Space → Space) : 0 ≤ kineticEnergy v :=
  integral_nonneg fun _ => sq_nonneg _

theorem X3Real_nonneg (v : Space → Space) : 0 ≤ X3Real v :=
  integral_nonneg fun _ => by positivity

/-- The `ℝ≥0∞`-valued kinetic energy written with `ENNReal.ofReal`. -/
theorem kineticEnergyLintegral_eq (v : Space → Space) :
    kineticEnergyLintegral v = ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2) := by
  simp [kineticEnergyLintegral, ENNReal.ofReal_pow (norm_nonneg _)]

/-- The `ℝ≥0∞`-valued `L³` quantity written with `ENNReal.ofReal`. -/
theorem X3_eq_lintegral_ofReal (v : Space → Space) :
    X3 v = ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 3) := by
  simp [X3, ENNReal.ofReal_pow (norm_nonneg _)]

/-- Measurability of the `L³` integrand for a continuous field. -/
theorem measurable_norm_pow_three {v : Space → Space} (hv : Continuous v) :
    Measurable fun x => ‖v x‖ ^ 3 :=
  (hv.norm.pow 3).measurable

/-- Measurability of the energy integrand for a continuous field. -/
theorem measurable_norm_sq {v : Space → Space} (hv : Continuous v) :
    Measurable fun x => ‖v x‖ ^ 2 :=
  (hv.norm.pow 2).measurable

/-! ## The pressure-route densities `D₃` and `P₃` (amendment A2, obligation P-0) -/

/-- The density of the manuscript's pressure-route dissipation,
`|v| ‖∇v‖_F² + |(∇v)ᵀv|² / |v|`.  Amendment A2: the second term is written with
the transposed Jacobian rather than with `∇|v|`, and Lean's `a / 0 = 0` supplies
the manuscript's convention that the integrand vanishes where `v = 0`
(design risk R-P0). -/
def D3density (v : Space → Space) (x : Space) : ℝ :=
  ‖v x‖ * frobeniusNormSq (fderiv ℝ v x) + ‖gradTranspose v x‖ ^ 2 / ‖v x‖

/-- The manuscript's `D₃(v) = ∫ (|v| ‖∇v‖_F² + |(∇v)ᵀv|²/|v|)`, a Bochner integral
of a nonnegative density. -/
def D3 (v : Space → Space) : ℝ := ∫ x, D3density v x

/-- The density of the manuscript's pressure work `P₃ = ∫ q (v·∇|v|)`, written as
`q ⟪v, (∇v)ᵀv⟫ / |v|` (amendment A2, obligation P-0), with the value `0` where
`v = 0`. -/
def P3density (q : Space → ℝ) (v : Space → Space) (x : Space) : ℝ :=
  q x * ⟪v x, gradTranspose v x⟫ / ‖v x‖

/-- The manuscript's pressure work `P₃(q, v) = ∫ q (v·∇|v|)`. -/
def P3 (q : Space → ℝ) (v : Space → Space) : ℝ := ∫ x, P3density q v x

/-- The pointwise Cauchy–Schwarz bound `|(∇v)ᵀv|²/|v| ≤ |v| ‖∇v‖_F²`: the second
term of the `D₃` density is dominated by the first.  At `v x = 0` both sides are
`0` by the `a / 0 = 0` convention. -/
theorem norm_gradTranspose_sq_div_le (v : Space → Space) (x : Space) :
    ‖gradTranspose v x‖ ^ 2 / ‖v x‖ ≤ ‖v x‖ * frobeniusNormSq (fderiv ℝ v x) := by
  rcases eq_or_lt_of_le (norm_nonneg (v x)) with h | h
  · have hx : ‖v x‖ = 0 := h.symm
    have hz : v x = 0 := by simpa using hx
    have hg : gradTranspose v x = 0 := by simp [gradTranspose, hz]
    simp [hx, hg]
  · rw [div_le_iff₀ h]
    have hb : ‖gradTranspose v x‖ ≤ frobeniusNorm (fderiv ℝ v x) * ‖v x‖ :=
      norm_gradTranspose_le v x
    have hsq : ‖gradTranspose v x‖ ^ 2
        ≤ (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    calc ‖gradTranspose v x‖ ^ 2
        ≤ (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) ^ 2 := hsq
      _ = ‖v x‖ * frobeniusNormSq (fderiv ℝ v x) * ‖v x‖ := by
          rw [mul_pow, frobeniusNorm_sq]; ring

/-- The `D₃` density is nonnegative pointwise, so `D₃` is an integral of a
nonnegative function. -/
theorem D3density_nonneg (v : Space → Space) (x : Space) : 0 ≤ D3density v x := by
  have h1 : 0 ≤ ‖v x‖ * frobeniusNormSq (fderiv ℝ v x) :=
    mul_nonneg (norm_nonneg _) (frobeniusNormSq_nonneg _)
  have h2 : 0 ≤ ‖gradTranspose v x‖ ^ 2 / ‖v x‖ :=
    div_nonneg (sq_nonneg _) (norm_nonneg _)
  exact add_nonneg h1 h2

/-- Both terms of the `D₃` density are controlled by the first:
`D₃ density ≤ 2 |v| ‖∇v‖_F²`. -/
theorem D3density_le_two_mul (v : Space → Space) (x : Space) :
    D3density v x ≤ 2 * (‖v x‖ * enstrophyDensity v x) := by
  have h := norm_gradTranspose_sq_div_le v x
  simp only [D3density, enstrophyDensity]
  linarith

/-- The `D₃` density vanishes where the field vanishes (the manuscript's
convention at `u = 0`). -/
theorem D3density_eq_zero_of_eq_zero {v : Space → Space} {x : Space} (hx : v x = 0) :
    D3density v x = 0 := by
  have hg : gradTranspose v x = 0 := by simp [gradTranspose, hx]
  simp [D3density, hx, hg]

/-- The `P₃` density with the division applied to the inner product only; the two
readings agree because `a * b / 0 = 0 = a * (b / 0)`. -/
theorem P3density_eq_mul_div (q : Space → ℝ) (v : Space → Space) (x : Space) :
    P3density q v x = q x * (⟪v x, gradTranspose v x⟫ / ‖v x‖) := by
  rw [P3density, mul_div_assoc]

/-- The `P₃` density vanishes where the field vanishes. -/
theorem P3density_eq_zero_of_eq_zero {q : Space → ℝ} {v : Space → Space} {x : Space}
    (hx : v x = 0) : P3density q v x = 0 := by
  have hg : gradTranspose v x = 0 := by simp [gradTranspose, hx]
  simp [P3density, hx, hg]

/-- The pointwise bound `|q (v·∇|v|)| ≤ |q| ‖∇v‖_F |v|` on the `P₃` density. -/
theorem abs_P3density_le (q : Space → ℝ) (v : Space → Space) (x : Space) :
    |P3density q v x| ≤ |q x| * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) := by
  rcases eq_or_lt_of_le (norm_nonneg (v x)) with h | h
  · have hx : ‖v x‖ = 0 := h.symm
    have hz : v x = 0 := by simpa using hx
    simp [P3density_eq_zero_of_eq_zero hz, hx]
  · rw [P3density_eq_mul_div, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_div, abs_of_pos h, div_le_iff₀ h]
    calc |⟪v x, gradTranspose v x⟫| ≤ ‖v x‖ * ‖gradTranspose v x‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖v x‖ * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) :=
          mul_le_mul_of_nonneg_left (norm_gradTranspose_le v x) (norm_nonneg _)
      _ = frobeniusNorm (fderiv ℝ v x) * ‖v x‖ * ‖v x‖ := by ring

/-! ## The regularized speed and the `P₃` integrand

The manuscript's pressure route tests the equation against the regularized speed
`r_ε(u) = (|u|² + ε)^{1/2}` (`NavierFormal.rEps`, `NavierFormal/Regularization.lean`)
precisely because its spatial gradient is the transposed Jacobian divided by
`r_ε`, which converges to the `P₃` integrand as `ε ↓ 0`.  The following lemmas
record that chain rule in the `(∇u)ᵀu` form of amendment A2. -/

/-- Chain rule for the regularized speed in the transposed-Jacobian form: if `v`
has derivative `v'` at `x`, then `r_ε ∘ v` has derivative
`h ↦ ⟪(v')ᵀ v(x), h⟫ / r_ε(v(x))` at `x`.  This is
`NavierFormal.hasFDerivAt_rEps` with the inner product moved onto the adjoint. -/
theorem hasFDerivAt_rEps_gradTranspose {ε : ℝ} (hε : 0 < ε) {v : Space → Space}
    {v' : Space →L[ℝ] Space} {x : Space} (hv : HasFDerivAt v v' x) :
    HasFDerivAt (fun y => rEps ε (v y))
      ((rEps ε (v x))⁻¹ • innerSL ℝ (ContinuousLinearMap.adjoint v' (v x))) x := by
  refine (hasFDerivAt_rEps hε hv).congr_fderiv ?_
  ext h
  simp [ContinuousLinearMap.adjoint_inner_left]

/-- The pointwise chain rule connecting the `P₃` integrand to the derivative of the
regularized speed: for `v` differentiable at `x`,
`d(r_ε ∘ v)(x) h = ⟪(∇v)ᵀv, h⟫ / r_ε(v(x))`.
As `ε ↓ 0` the right-hand side is the manuscript's `∇|v|`, written through
`(∇v)ᵀv` as required by amendment A2 (obligation P-0). -/
theorem fderiv_rEps_apply {ε : ℝ} (hε : 0 < ε) {v : Space → Space} {x : Space}
    (hv : DifferentiableAt ℝ v x) (h : Space) :
    fderiv ℝ (fun y => rEps ε (v y)) x h = ⟪gradTranspose v x, h⟫ / rEps ε (v x) := by
  have hd := hasFDerivAt_rEps_gradTranspose hε hv.hasFDerivAt
  rw [hd.fderiv]
  simp [gradTranspose, div_eq_inv_mul]

/-- The `ε`-regularization of the `P₃` integrand: testing the derivative of
`r_ε ∘ v` in the direction `v(x)` gives `⟪v, (∇v)ᵀv⟫ / r_ε(v(x))`, which is the
manuscript's `v·∇|v|` with `|v|` replaced by `r_ε(v)` in the denominator.  Letting
`ε ↓ 0` at a point where `v(x) ≠ 0` returns `P3density`'s inner factor. -/
theorem fderiv_rEps_apply_self {ε : ℝ} (hε : 0 < ε) {v : Space → Space} {x : Space}
    (hv : DifferentiableAt ℝ v x) :
    fderiv ℝ (fun y => rEps ε (v y)) x (v x)
      = ⟪v x, gradTranspose v x⟫ / rEps ε (v x) := by
  rw [fderiv_rEps_apply hε hv, real_inner_comm]

/-- The `P₃` integrand in convection form: `q ⟪v, (∇v)ᵀv⟫ / |v| = q ⟪(v·∇)v, v⟫ / |v|`,
which at a point where `v ≠ 0` is the manuscript's `q (v·∇|v|)`.  The identity holds
at every point, the zero convention `a / 0 = 0` covering `v(x) = 0`. -/
theorem P3density_eq_convection (q : Space → ℝ) (v : Space → Space) (x : Space) :
    P3density q v x = q x * (⟪convection v x, v x⟫ / ‖v x‖) := by
  rw [P3density_eq_mul_div, inner_self_gradTranspose]

end

end NavierFormal
