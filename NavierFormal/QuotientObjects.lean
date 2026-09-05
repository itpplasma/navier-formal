import NavierFormal.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Data.Real.Pointwise

/-!
# Objects of the quotient functional (manuscript `sec:quotient`)

This module carries the Mathlib-only *objects* of the manuscript's quotient
section: the critical Lebesgue space `L³(ℝ³;ℝ³)`, the closed subspace `𝒢₃` of
gradients, the quotient functional `𝒬`, its minimizers, the cubic map
`A = |w| w`, distributional solenoidality, and the two integral functionals
`D_𝒬` and the strain flux that appear in the manuscript's quotient evolution
identity.

Only definitions and their cheap API are proved here.  Existence and
uniqueness of minimizers, coercivity, differentiability, heat monotonicity and
the evolution identity are *not* claimed anywhere in this file, and nothing
here is a statement about the Millennium problem.

## Conventions

* `Space` is `EuclideanSpace ℝ (Fin 3)` from `NavierFormal.Basic`, carrying its
  Euclidean inner product and Lebesgue (Haar) `volume`.
* `⟪x, y⟫` is the real inner product `inner ℝ x y`
  (scope `RealInnerProductSpace`).
* `Δ` is Mathlib's `InnerProductSpace` Laplacian, the trace of the second
  Fréchet derivative, with the sign convention `Δ = ∑ᵢ ∂ᵢ²` (scope
  `Laplacian`).  It takes junk value `0` where the field is not twice
  differentiable.
* Elements of `Lp` are equivalence classes; they are related to genuine
  functions only through `⇑` and almost-everywhere equalities.
-/

open MeasureTheory
open scoped ENNReal ContDiff RealInnerProductSpace Laplacian

noncomputable section

namespace NavierFormal

/-- `1 ≤ 3` as an exponent fact, so that `Lp Space 3 volume` is a normed space. -/
instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

/-- The critical Lebesgue space `L³(ℝ³; ℝ³)` of the manuscript's `sec:quotient`:
Mathlib's `Lp` of `Space`-valued functions with exponent `3` for Lebesgue
measure on `ℝ³`.  Its elements are almost-everywhere equivalence classes. -/
abbrev L3 : Type := Lp Space 3 (volume : Measure Space)

/-! ### The gradient subspace `𝒢₃` -/

/-- A test potential: a smooth, compactly supported scalar field `φ : ℝ³ → ℝ`.
These are the manuscript's `φ ∈ C_c^∞(ℝ³)` whose gradients generate `𝒢₃`. -/
def IsTestPotential (φ : Space → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

/-- The generating set of the manuscript's gradient space `𝒢₃`: those `L³`
classes that are almost everywhere equal to the gradient `∇φ` of a smooth
compactly supported potential `φ`.  Almost-everywhere equality is the only
sensible relation between an `Lp` class and a genuine function. -/
def gradientGenerators : Set L3 :=
  {g | ∃ φ : Space → ℝ, IsTestPotential φ ∧ ⇑g =ᵐ[volume] gradient φ}

/-- The manuscript's `𝒢₃ ⊂ L³`: the closure in `L³` of the linear span of
`{∇φ : φ ∈ C_c^∞(ℝ³)}`.  It is a closed linear subspace by construction. -/
def gradientSubspace : Submodule ℝ L3 :=
  (Submodule.span ℝ gradientGenerators).topologicalClosure

/-- `𝒢₃` is closed in `L³`, as the manuscript requires when it takes the
infimum over `𝒢₃`. -/
lemma isClosed_gradientSubspace :
    IsClosed (gradientSubspace : Set L3) :=
  Submodule.isClosed_topologicalClosure _

/-- Every generator of the manuscript's `𝒢₃` lies in `𝒢₃`. -/
lemma gradientGenerators_subset : gradientGenerators ⊆ (gradientSubspace : Set L3) :=
  (Submodule.subset_span).trans (Submodule.le_topologicalClosure _)

/-- The manuscript's statement that `∇φ ∈ 𝒢₃` for every test potential `φ`
whose gradient is in `L³`. -/
lemma memLp_gradient_toLp_mem_gradientSubspace {φ : Space → ℝ} (hφ : IsTestPotential φ)
    (hg : MemLp (gradient φ) 3 (volume : Measure Space)) :
    hg.toLp (gradient φ) ∈ gradientSubspace :=
  gradientGenerators_subset ⟨φ, hφ, hg.coeFn_toLp⟩

/-- `𝒢₃` is nonempty as a type: it contains `0`. -/
instance : Nonempty (gradientSubspace) := ⟨0⟩

/-! ### The quotient functional `𝒬` -/

/-- The manuscript's quotient functional
`𝒬(u) = inf_{q ∈ 𝒢₃} ⅓‖u + q‖₃³`, as an infimum over the subtype `𝒢₃`.
The family is nonempty (`q = 0`) and bounded below by `0`
(`quotientFunctional_bddBelow`), so this `Real.iInf` is the genuine
infimum. -/
def quotientFunctional (u : L3) : ℝ :=
  ⨅ q : gradientSubspace, (1 / 3 : ℝ) * ‖u + (q : L3)‖ ^ 3

/-- The family whose infimum defines `𝒬(u)` is bounded below by `0`; this is
what makes `Real.iInf` the true infimum of the manuscript. -/
lemma quotientFunctional_bddBelow (u : L3) :
    BddBelow (Set.range fun q : gradientSubspace => (1 / 3 : ℝ) * ‖u + (q : L3)‖ ^ 3) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨q, rfl⟩
  positivity

/-- Nonnegativity of the manuscript's quotient functional, `𝒬(u) ≥ 0`. -/
lemma quotientFunctional_nonneg (u : L3) : 0 ≤ quotientFunctional u :=
  le_ciInf fun _ => by positivity

/-- Every competitor bounds the manuscript's infimum:
`𝒬(u) ≤ ⅓‖u + q‖₃³` for `q ∈ 𝒢₃`. -/
lemma quotientFunctional_le (u q : L3) (hq : q ∈ gradientSubspace) :
    quotientFunctional u ≤ (1 / 3 : ℝ) * ‖u + q‖ ^ 3 :=
  ciInf_le (quotientFunctional_bddBelow u) (⟨q, hq⟩ : gradientSubspace)

/-- The manuscript's upper bound `𝒬(u) ≤ ⅓‖u‖₃³`, obtained from the competitor
`q = 0`.  Together with coercivity (not proved here) this is the two-sided
comparison of `sec:quotient`. -/
lemma quotientFunctional_le_cube (u : L3) :
    quotientFunctional u ≤ (1 / 3 : ℝ) * ‖u‖ ^ 3 := by
  simpa using quotientFunctional_le u 0 (zero_mem _)

/-- `𝒬(0) = 0`. -/
@[simp] lemma quotientFunctional_zero : quotientFunctional (0 : L3) = 0 :=
  le_antisymm (by simpa using quotientFunctional_le_cube (0 : L3))
    (quotientFunctional_nonneg _)

/-- Cubic homogeneity of the manuscript's quotient functional,
`𝒬(a u) = |a|³ 𝒬(u)`.  It holds because `𝒢₃` is a linear subspace, so
`q ↦ a q` permutes the competitors when `a ≠ 0`. -/
lemma quotientFunctional_smul (a : ℝ) (u : L3) :
    quotientFunctional (a • u) = |a| ^ 3 * quotientFunctional u := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have habs : (0 : ℝ) ≤ |a| ^ 3 := by positivity
  rw [quotientFunctional, quotientFunctional, Real.mul_iInf_of_nonneg habs]
  have hbdd : BddBelow
      (Set.range fun q : gradientSubspace =>
        |a| ^ 3 * ((1 / 3 : ℝ) * ‖u + (q : L3)‖ ^ 3)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    positivity
  refine le_antisymm (le_ciInf fun q => ?_) (le_ciInf fun r => ?_)
  · have hmem : a • (q : L3) ∈ gradientSubspace := Submodule.smul_mem _ a q.2
    have hnorm : ‖a • u + a • (q : L3)‖ = |a| * ‖u + (q : L3)‖ := by
      rw [← smul_add, norm_smul, Real.norm_eq_abs]
    calc (⨅ q : gradientSubspace, (1 / 3 : ℝ) * ‖a • u + (q : L3)‖ ^ 3)
        ≤ (1 / 3 : ℝ) * ‖a • u + a • (q : L3)‖ ^ 3 :=
          quotientFunctional_le (a • u) _ hmem
      _ = |a| ^ 3 * ((1 / 3 : ℝ) * ‖u + (q : L3)‖ ^ 3) := by rw [hnorm, mul_pow]; ring
  · have hmem : a⁻¹ • (r : L3) ∈ gradientSubspace := Submodule.smul_mem _ _ r.2
    have hnorm : ‖a • u + (r : L3)‖ = |a| * ‖u + a⁻¹ • (r : L3)‖ := by
      rw [show a • u + (r : L3) = a • (u + a⁻¹ • (r : L3)) by
        rw [smul_add, smul_inv_smul₀ ha], norm_smul, Real.norm_eq_abs]
    calc (⨅ q : gradientSubspace, |a| ^ 3 * ((1 / 3 : ℝ) * ‖u + (q : L3)‖ ^ 3))
        ≤ |a| ^ 3 * ((1 / 3 : ℝ) * ‖u + a⁻¹ • (r : L3)‖ ^ 3) :=
          ciInf_le hbdd (⟨a⁻¹ • (r : L3), hmem⟩ : gradientSubspace)
      _ = (1 / 3 : ℝ) * ‖a • u + (r : L3)‖ ^ 3 := by rw [hnorm, mul_pow]; ring

/-! ### Minimizers -/

/-- `w` is a minimizing representative of `u` in the manuscript's sense: it lies
in the affine class `u + 𝒢₃` and its `L³` norm is minimal there.  The
manuscript writes `w = u + q` with `q` the minimizer; minimizers are quantified
rather than chosen, so that no definition depends on an unproved existence
statement. -/
def IsQuotientMinimizer (u w : L3) : Prop :=
  w - u ∈ gradientSubspace ∧ ∀ q ∈ gradientSubspace, ‖w‖ ≤ ‖u + q‖

/-- A minimizer attains the manuscript's infimum: `𝒬(u) = ⅓‖w‖₃³`. -/
lemma IsQuotientMinimizer.quotientFunctional_eq {u w : L3} (h : IsQuotientMinimizer u w) :
    quotientFunctional u = (1 / 3 : ℝ) * ‖w‖ ^ 3 := by
  refine le_antisymm ?_ (le_ciInf fun q => ?_)
  · have := quotientFunctional_le u (w - u) h.1
    simpa using this
  · have hle : ‖w‖ ≤ ‖u + (q : L3)‖ := h.2 _ q.2
    have hw : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
    gcongr

/-- The minimal value is the cube of the minimal norm: `⅓‖w‖₃³ = 𝒬(u)`, the
form in which the manuscript uses it. -/
lemma IsQuotientMinimizer.cube_norm_eq {u w : L3} (h : IsQuotientMinimizer u w) :
    (1 / 3 : ℝ) * ‖w‖ ^ 3 = quotientFunctional u :=
  h.quotientFunctional_eq.symm

/-! ### The cubic map `A = |w| w` -/

/-- The manuscript's `A = |w| w`, the pointwise cubic map attached to a
representative `w ∈ L³`.  It is defined on the function representative `⇑w`, so
it is determined almost everywhere by the `L³` class. -/
def cubicMap (w : L3) (x : Space) : Space := ‖(⇑w) x‖ • (⇑w) x

@[simp] lemma cubicMap_apply (w : L3) (x : Space) :
    cubicMap w x = ‖(⇑w) x‖ • (⇑w) x := rfl

/-- Pointwise size of the manuscript's `A = |w| w`: `|A| = |w|²`, which is why
`A ∈ L^{3/2}` when `w ∈ L³`. -/
lemma norm_cubicMap (w : L3) (x : Space) : ‖cubicMap w x‖ = ‖(⇑w) x‖ ^ 2 := by
  simp [cubicMap, norm_smul, sq]

/-- The manuscript's `A = |w| w` is almost everywhere strongly measurable. -/
lemma aestronglyMeasurable_cubicMap (w : L3) :
    AEStronglyMeasurable (cubicMap w) (volume : Measure Space) :=
  (Lp.aestronglyMeasurable w).norm.smul (Lp.aestronglyMeasurable w)

/-- Almost everywhere, the manuscript's `A` only depends on the `L³` class: two
representatives that agree almost everywhere give the same `A`. -/
lemma cubicMap_congr {w : L3} {v : Space → Space} (h : ⇑w =ᵐ[volume] v) :
    cubicMap w =ᵐ[volume] fun x => ‖v x‖ • v x := by
  filter_upwards [h] with x hx
  simp [cubicMap, hx]

/-! ### Distributional solenoidality -/

/-- The manuscript's solenoidality condition for an `L³` field, in the
distributional form `∫ ⟪u, ∇φ⟫ = 0` for every smooth compactly supported
scalar potential `φ`.  This is exactly the orthogonality to `𝒢₃` used in
`sec:quotient`. -/
def IsSolenoidalL3 (u : L3) : Prop :=
  ∀ φ : Space → ℝ, IsTestPotential φ → ∫ x, ⟪(⇑u) x, gradient φ x⟫ = 0

/-- The zero field is solenoidal. -/
lemma isSolenoidalL3_zero : IsSolenoidalL3 (0 : L3) := by
  intro φ _
  have h : ∫ x, ⟪(⇑(0 : L3)) x, gradient φ x⟫ = ∫ _x : Space, (0 : ℝ) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero Space 3 (volume : Measure Space)] with x _
    simp
  rw [h, integral_zero]

/-! ### The quotient dissipation and the strain flux -/

/-- The manuscript's quotient heat dissipation `D_𝒬 = -∫ ⟪A, Δu⟫` for the
minimizing representative `w` (through `A = |w| w`) and a velocity field `v`.
`Δ` is Mathlib's Laplacian, i.e. the trace of the second Fréchet derivative,
with junk value `0` where `v` fails to be twice differentiable. -/
def quotientDissipation (w : L3) (v : Space → Space) : ℝ :=
  -∫ x, ⟪cubicMap w x, Δ v x⟫

/-- The manuscript's strain flux `∫ ⟪q, (A·∇)v⟫`, where `q = w - u` is the
gradient part of the minimizing representative and `(A·∇)v x` is the Fréchet
derivative of `v` at `x` in the direction `A x = |w(x)| w(x)`. -/
def strainFlux (w : L3) (q : Space → Space) (v : Space → Space) : ℝ :=
  ∫ x, ⟪q x, fderiv ℝ v x (cubicMap w x)⟫

/-- Linearity of the manuscript's strain flux in the transported field `q`. -/
lemma strainFlux_zero (w : L3) (v : Space → Space) : strainFlux w 0 v = 0 := by
  simp [strainFlux]

/-- The manuscript's quotient dissipation vanishes on fields with vanishing
Laplacian; in particular `D_𝒬(w, 0) = 0`. -/
lemma quotientDissipation_zero (w : L3) : quotientDissipation w 0 = 0 := by
  have h0 : Δ (0 : Space → Space) = 0 := by
    rw [show (0 : Space → Space) = fun _ : Space => (0 : Space) from rfl]
    exact InnerProductSpace.laplacian_const
  simp [quotientDissipation, h0]

end NavierFormal

end
