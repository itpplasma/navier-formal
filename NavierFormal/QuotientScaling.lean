import NavierFormal.Scaling
import NavierFormal.QuotientObjects
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Critical-scaling invariance of the cubic gradient quotient (manuscript `sec:quotient`)

The manuscript sentence formalized here is the one in `sec:quotient`:

> The functional is cubic in amplitude and invariant under the critical
> spatial scaling.

The cubic amplitude homogeneity `𝒬(a u) = |a|³ 𝒬(u)` is already
`NavierFormal.quotientFunctional_smul` in `NavierFormal/QuotientObjects.lean`.
This module supplies the second half, the invariance under the critical
dilation `u ↦ dilate λ u`, `(dilate λ u)(x) = λ u(λ x)`, of Proposition
`prop:scaling`.

The chain of steps is the manuscript's own:

1. `NavierFormal.memLp_dilate`, `NavierFormal.dilateL3`: for `λ > 0` the
   critical dilation preserves `L³` and induces a *linear isometry* of
   `L³(ℝ³;ℝ³)` onto itself, with inverse the dilation by `λ⁻¹`.  The norm
   identity is `Scaling.eLpNorm_dilate_three`, the `L³` case `1 - 3/3 = 0` of
   `prop:scaling`.
2. `NavierFormal.dilate_gradient`: the dilation sends gradients of test
   potentials to gradients of test potentials,
   `dilate λ (∇φ) = ∇(φ ∘ (λ • ·))`; the chain-rule factor `λ` is exactly the
   amplitude factor carried by `dilate`.  Hence the generating set of the
   manuscript's `𝒢₃` is mapped onto itself
   (`NavierFormal.dilateL3_image_gradientGenerators`), and by continuity of the
   isometry together with closedness of `𝒢₃`, so is `𝒢₃` itself
   (`NavierFormal.dilateL3_gradientSubspace`).
3. `NavierFormal.quotientFunctional_dilateL3`: the infimum defining `𝒬` is
   transported by the isometry, so `𝒬(dilate λ u) = 𝒬(u)`.
4. `NavierFormal.isQuotientMinimizer_dilateL3`: minimizing representatives are
   transported as well.

Nothing here is a statement about the Navier–Stokes equations or the
Millennium problem; only the change of variables `y = λ x` is used.
-/

open MeasureTheory Set

open scoped ENNReal ContDiff RealInnerProductSpace

noncomputable section

namespace NavierFormal

/-! ### Pointwise algebra of the critical dilation -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The critical dilation of Proposition `prop:scaling` is additive:
`dilate λ (f + g) = dilate λ f + dilate λ g`. -/
lemma dilate_add (lam : ℝ) (f g : Space → E) :
    dilate lam (f + g) = dilate lam f + dilate lam g := by
  funext x
  simp [dilate, smul_add]

/-- The critical dilation commutes with scalar multiples of the field:
`dilate λ (c • f) = c • dilate λ f`.  Together with `dilate_add` this is the
linearity used to promote `dilate λ` to a linear map on `L³`. -/
lemma dilate_const_smul (lam c : ℝ) (f : Space → E) :
    dilate lam (c • f) = c • dilate lam f := by
  funext x
  show lam • (c • f (lam • x)) = c • (lam • f (lam • x))
  rw [smul_comm]

/-- The critical dilations compose as a multiplicative one-parameter family:
`dilate a (dilate b f) = dilate (a b) f`.  Both the amplitude factor and the
spatial factor multiply. -/
lemma dilate_dilate (a b : ℝ) (f : Space → E) :
    dilate a (dilate b f) = dilate (a * b) f := by
  funext x
  simp [dilate, smul_smul, mul_comm a b]

/-- `dilate 1` is the identity. -/
@[simp] lemma dilate_one (f : Space → E) : dilate 1 f = f := by
  funext x
  simp [dilate]

/-- The dilation by `λ⁻¹` inverts the dilation by `λ`. -/
lemma dilate_inv_dilate {lam : ℝ} (hlam : lam ≠ 0) (f : Space → E) :
    dilate lam⁻¹ (dilate lam f) = f := by
  rw [dilate_dilate, inv_mul_cancel₀ hlam, dilate_one]

/-- The dilation by `λ` inverts the dilation by `λ⁻¹`. -/
lemma dilate_dilate_inv {lam : ℝ} (hlam : lam ≠ 0) (f : Space → E) :
    dilate lam (dilate lam⁻¹ f) = f := by
  rw [dilate_dilate, mul_inv_cancel₀ hlam, dilate_one]

/-! ### Measure-theoretic prerequisites for the `L³` dilation -/

/-- The change of variables `y = λ x` of Proposition `prop:scaling` is
quasi-measure-preserving for Lebesgue measure on `ℝ³`: it rescales the measure
by the nonzero finite constant `λ⁻³`.  This is what lets almost-everywhere
statements be pulled back along the dilation. -/
lemma quasiMeasurePreserving_smul_space {lam : ℝ} (hlam : lam ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : Space => lam • x) volume volume :=
  Measure.quasiMeasurePreserving_smul (volume : Measure Space) hlam

/-- Almost-everywhere equal fields have almost-everywhere equal dilations, so
`dilate λ` is well defined on `L³` classes. -/
lemma dilate_congr_ae {lam : ℝ} (hlam : lam ≠ 0) {f g : Space → E}
    (h : f =ᵐ[volume] g) : dilate lam f =ᵐ[volume] dilate lam g := by
  have h' := (quasiMeasurePreserving_smul_space hlam).ae_eq h
  filter_upwards [h'] with x hx
  simp only [Function.comp_apply] at hx
  simp [dilate, hx]

/-- Step 1 of the invariance, membership: for `λ > 0` the critical dilation
preserves `L³(ℝ³;ℝ³)`.  Measurability is the composition with the linear
homeomorphism `x ↦ λ x`; the norm is unchanged by
`Scaling.eLpNorm_dilate_three`. -/
lemma memLp_dilate {f : Space → E} (hf : MemLp f 3 (volume : Measure Space)) {lam : ℝ}
    (hlam : 0 < lam) : MemLp (dilate lam f) 3 (volume : Measure Space) := by
  refine ⟨?_, ?_⟩
  · exact (hf.1.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_smul_space hlam.ne')).const_smul lam
  · rw [show eLpNorm (dilate lam f) 3 (volume : Measure Space)
        = eLpNorm f 3 (volume : Measure Space) from eLpNorm_dilate_three f hlam]
    exact hf.2

/-! ### The dilation as a linear isometry of `L³` -/

/-- The critical dilation on `L³` classes: the class of `dilate λ u` for any
representative of `u`.  Well defined by `dilate_congr_ae`. -/
def dilateL3Fun (lam : ℝ) (hlam : 0 < lam) (u : L3) : L3 :=
  (memLp_dilate (Lp.memLp u) hlam).toLp _

/-- The representative of `dilateL3Fun λ u` is `dilate λ` of the
representative of `u`. -/
lemma coeFn_dilateL3Fun (lam : ℝ) (hlam : 0 < lam) (u : L3) :
    ⇑(dilateL3Fun lam hlam u) =ᵐ[volume] dilate lam ⇑u :=
  MemLp.coeFn_toLp _

/-- Step 1 of the invariance, norm: the critical dilation is an `L³` isometry,
the case `1 - 3/3 = 0` of Proposition `prop:scaling`. -/
lemma norm_dilateL3Fun (lam : ℝ) (hlam : 0 < lam) (u : L3) :
    ‖dilateL3Fun lam hlam u‖ = ‖u‖ := by
  rw [dilateL3Fun, Lp.norm_toLp, eLpNorm_dilate_three _ hlam, Lp.norm_def]

/-- Additivity of the `L³` dilation. -/
lemma dilateL3Fun_add (lam : ℝ) (hlam : 0 < lam) (u v : L3) :
    dilateL3Fun lam hlam (u + v) = dilateL3Fun lam hlam u + dilateL3Fun lam hlam v := by
  refine Lp.ext ?_
  refine (coeFn_dilateL3Fun lam hlam (u + v)).trans ?_
  refine ((dilate_congr_ae hlam.ne' (Lp.coeFn_add u v)).trans ?_).trans
    ((Lp.coeFn_add (dilateL3Fun lam hlam u) (dilateL3Fun lam hlam v)).trans
      ((coeFn_dilateL3Fun lam hlam u).add (coeFn_dilateL3Fun lam hlam v))).symm
  rw [dilate_add]

/-- Homogeneity of the `L³` dilation in the field. -/
lemma dilateL3Fun_smul (lam : ℝ) (hlam : 0 < lam) (c : ℝ) (u : L3) :
    dilateL3Fun lam hlam (c • u) = c • dilateL3Fun lam hlam u := by
  refine Lp.ext ?_
  refine (coeFn_dilateL3Fun lam hlam (c • u)).trans ?_
  refine ((dilate_congr_ae hlam.ne' (Lp.coeFn_smul c u)).trans ?_).trans
    ((Lp.coeFn_smul c (dilateL3Fun lam hlam u)).trans
      ((coeFn_dilateL3Fun lam hlam u).const_smul c)).symm
  rw [dilate_const_smul]

/-- The dilation by `λ⁻¹` undoes the dilation by `λ` on `L³`. -/
lemma dilateL3Fun_inv_left (lam : ℝ) (hlam : 0 < lam) (u : L3) :
    dilateL3Fun lam⁻¹ (inv_pos.mpr hlam) (dilateL3Fun lam hlam u) = u := by
  refine Lp.ext ?_
  refine (coeFn_dilateL3Fun lam⁻¹ (inv_pos.mpr hlam) (dilateL3Fun lam hlam u)).trans ?_
  refine (dilate_congr_ae (inv_pos.mpr hlam).ne' (coeFn_dilateL3Fun lam hlam u)).trans ?_
  rw [dilate_inv_dilate hlam.ne']

/-- The dilation by `λ` undoes the dilation by `λ⁻¹` on `L³`. -/
lemma dilateL3Fun_inv_right (lam : ℝ) (hlam : 0 < lam) (u : L3) :
    dilateL3Fun lam hlam (dilateL3Fun lam⁻¹ (inv_pos.mpr hlam) u) = u := by
  refine Lp.ext ?_
  refine (coeFn_dilateL3Fun lam hlam (dilateL3Fun lam⁻¹ (inv_pos.mpr hlam) u)).trans ?_
  refine (dilate_congr_ae hlam.ne'
    (coeFn_dilateL3Fun lam⁻¹ (inv_pos.mpr hlam) u)).trans ?_
  rw [dilate_dilate_inv hlam.ne']

/-- Step 1 of the manuscript's invariance claim: for `λ > 0` the critical
spatial dilation `u ↦ λ u(λ ·)` is a linear isometry of
`L³(ℝ³;ℝ³) = NavierFormal.L3` onto itself, with inverse the dilation by
`λ⁻¹`. -/
def dilateL3 (lam : ℝ) (hlam : 0 < lam) : L3 ≃ₗᵢ[ℝ] L3 where
  toFun := dilateL3Fun lam hlam
  map_add' := dilateL3Fun_add lam hlam
  map_smul' c u := dilateL3Fun_smul lam hlam c u
  invFun := dilateL3Fun lam⁻¹ (inv_pos.mpr hlam)
  left_inv := dilateL3Fun_inv_left lam hlam
  right_inv := dilateL3Fun_inv_right lam hlam
  norm_map' := norm_dilateL3Fun lam hlam

@[simp] lemma dilateL3_apply (lam : ℝ) (hlam : 0 < lam) (u : L3) :
    dilateL3 lam hlam u = dilateL3Fun lam hlam u := rfl

/-- The inverse of the critical `L³` dilation is the dilation by `λ⁻¹`. -/
lemma dilateL3_symm_apply (lam : ℝ) (hlam : 0 < lam) (u : L3) :
    (dilateL3 lam hlam).symm u = dilateL3Fun lam⁻¹ (inv_pos.mpr hlam) u := rfl


/-! ### Step 2: the dilation of a gradient is a gradient -/

/-- Two vectors of `ℝ³` agreeing against every test vector in the inner
product are equal; the elementary form of the manuscript's identification of
gradients. -/
lemma space_eq_of_inner_eq {x y : Space} (h : ∀ v : Space, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
  ext_inner_left ℝ fun v => by rw [real_inner_comm, real_inner_comm y v]; exact h v

/-- Chain rule of `sec:quotient`: for a differentiable potential `φ`,
`∇(φ(λ ·))(x) = λ ∇φ(λ x)`.  The factor `λ` produced by the chain rule is
exactly the amplitude factor carried by the critical dilation of Proposition
`prop:scaling`. -/
lemma gradient_comp_smul {φ : Space → ℝ} (hφ : Differentiable ℝ φ) (lam : ℝ) (x : Space) :
    gradient (fun y : Space => φ (lam • y)) x = lam • gradient φ (lam • x) := by
  have hlin : HasFDerivAt (fun y : Space => lam • y)
      (lam • ContinuousLinearMap.id ℝ Space) x := (hasFDerivAt_id x).const_smul lam
  have hcomp : HasFDerivAt (fun y : Space => φ (lam • y))
      ((fderiv ℝ φ (lam • x)).comp (lam • ContinuousLinearMap.id ℝ Space)) x :=
    (hφ (lam • x)).hasFDerivAt.comp x hlin
  refine space_eq_of_inner_eq fun v => ?_
  rw [inner_gradient_left, hcomp.fderiv, real_inner_smul_left, inner_gradient_left]
  simp

/-- Step 2 of the manuscript's invariance claim: the critical dilation maps the
gradient of a potential to the gradient of the dilated potential,
`dilate λ (∇φ) = ∇(φ(λ ·))`. -/
theorem dilate_gradient (lam : ℝ) {φ : Space → ℝ} (hφ : Differentiable ℝ φ) :
    dilate lam (gradient φ) = gradient (fun x : Space => φ (lam • x)) := by
  funext x
  exact (gradient_comp_smul hφ lam x).symm

/-- The class of test potentials `C_c^∞(ℝ³)` of `sec:quotient` is stable under
the spatial rescaling `φ ↦ φ(λ ·)` for `λ ≠ 0`: smoothness is preserved by
composition with a linear homeomorphism, and the support is rescaled by
`λ⁻¹`. -/
lemma IsTestPotential.comp_smul {φ : Space → ℝ} (hφ : IsTestPotential φ) {lam : ℝ}
    (hlam : lam ≠ 0) : IsTestPotential (fun x : Space => φ (lam • x)) :=
  ⟨hφ.1.comp (lam • ContinuousLinearMap.id ℝ Space).contDiff,
    hφ.2.comp_homeomorph (Homeomorph.smulOfNeZero lam hlam)⟩

/-- Step 2, `L³` form: the critical dilation maps the generating set of the
manuscript's `𝒢₃` into itself. -/
lemma dilateL3_mem_gradientGenerators {lam : ℝ} (hlam : 0 < lam) {g : L3}
    (hg : g ∈ gradientGenerators) : dilateL3 lam hlam g ∈ gradientGenerators := by
  obtain ⟨φ, hφ, hgφ⟩ := hg
  refine ⟨fun x => φ (lam • x), hφ.comp_smul hlam.ne', ?_⟩
  refine (coeFn_dilateL3Fun lam hlam g).trans ?_
  refine (dilate_congr_ae hlam.ne' hgφ).trans ?_
  rw [dilate_gradient lam (hφ.1.differentiable (by norm_num))]

/-- Step 2, `L³` form: the critical dilation maps the generating set of `𝒢₃`
*onto* itself, since the dilation by `λ⁻¹` is its inverse. -/
lemma dilateL3_image_gradientGenerators {lam : ℝ} (hlam : 0 < lam) :
    (dilateL3 lam hlam) '' gradientGenerators = gradientGenerators := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact dilateL3_mem_gradientGenerators hlam hg
  · intro g hg
    refine ⟨(dilateL3 lam hlam).symm g, ?_, (dilateL3 lam hlam).apply_symm_apply g⟩
    rw [dilateL3_symm_apply]
    exact dilateL3_mem_gradientGenerators (inv_pos.mpr hlam) hg

/-! ### Step 2, closure: the dilation preserves `𝒢₃` -/

/-- The critical dilation maps the linear span of the generators of `𝒢₃` onto
itself, because it maps the generating set onto itself. -/
lemma dilateL3_map_span {lam : ℝ} (hlam : 0 < lam) :
    Submodule.map (dilateL3 lam hlam).toLinearEquiv.toLinearMap
        (Submodule.span ℝ gradientGenerators)
      = Submodule.span ℝ gradientGenerators := by
  rw [Submodule.map_span]
  congr 1
  exact dilateL3_image_gradientGenerators hlam

/-- Set form of `dilateL3_map_span`. -/
lemma dilateL3_image_span {lam : ℝ} (hlam : 0 < lam) :
    (dilateL3 lam hlam) '' (Submodule.span ℝ gradientGenerators : Set L3)
      = (Submodule.span ℝ gradientGenerators : Set L3) := by
  have h := dilateL3_map_span hlam
  rw [SetLike.ext'_iff, Submodule.map_coe] at h
  exact h

/-- Step 2 of the manuscript's invariance claim, closed form: the critical
dilation maps the manuscript's gradient space `𝒢₃` into itself.  The generating
set is mapped into `𝒢₃` by the chain rule (`dilate_gradient`), and the
dilation is continuous, so the closure is mapped into the closure. -/
theorem dilateL3_mem_gradientSubspace {lam : ℝ} (hlam : 0 < lam) {u : L3}
    (hu : u ∈ gradientSubspace) : dilateL3 lam hlam u ∈ gradientSubspace := by
  have hu' : u ∈ closure ((Submodule.span ℝ gradientGenerators : Set L3)) := by
    rw [← SetLike.mem_coe, gradientSubspace, Submodule.topologicalClosure_coe] at hu
    exact hu
  have h1 : dilateL3 lam hlam u
      ∈ closure ((dilateL3 lam hlam) '' (Submodule.span ℝ gradientGenerators : Set L3)) :=
    image_closure_subset_closure_image (dilateL3 lam hlam).continuous ⟨u, hu', rfl⟩
  rw [dilateL3_image_span hlam] at h1
  rw [← SetLike.mem_coe, gradientSubspace, Submodule.topologicalClosure_coe]
  exact h1

/-- Membership in `𝒢₃` is invariant under the critical dilation, in both
directions. -/
theorem dilateL3_mem_gradientSubspace_iff {lam : ℝ} (hlam : 0 < lam) {u : L3} :
    dilateL3 lam hlam u ∈ gradientSubspace ↔ u ∈ gradientSubspace := by
  refine ⟨fun h => ?_, dilateL3_mem_gradientSubspace hlam⟩
  have := dilateL3_mem_gradientSubspace (inv_pos.mpr hlam) h
  rwa [dilateL3_apply, dilateL3_apply, dilateL3Fun_inv_left] at this

/-- The inverse dilation also preserves `𝒢₃`. -/
lemma dilateL3_symm_mem_gradientSubspace {lam : ℝ} (hlam : 0 < lam) {u : L3}
    (hu : u ∈ gradientSubspace) : (dilateL3 lam hlam).symm u ∈ gradientSubspace := by
  rw [dilateL3_symm_apply]
  exact dilateL3_mem_gradientSubspace (inv_pos.mpr hlam) hu

/-- Step 2 of the manuscript's invariance claim, final form: the critical
dilation maps `𝒢₃` **onto** `𝒢₃`. -/
theorem dilateL3_gradientSubspace {lam : ℝ} (hlam : 0 < lam) :
    Submodule.map (dilateL3 lam hlam).toLinearEquiv.toLinearMap gradientSubspace
      = gradientSubspace := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact dilateL3_mem_gradientSubspace hlam hv
  · intro u hu
    exact ⟨(dilateL3 lam hlam).symm u, dilateL3_symm_mem_gradientSubspace hlam hu,
      (dilateL3 lam hlam).apply_symm_apply u⟩

/-! ### Step 3: invariance of the quotient functional -/

/-- Step 3, the manuscript's claim that "the functional is invariant under the
critical spatial scaling": `𝒬(dilate λ u) = 𝒬(u)` for every `u ∈ L³` and
`λ > 0`.  The infimum over `𝒢₃` is transported by the `L³` isometry, which maps
`𝒢₃` onto `𝒢₃`. -/
theorem quotientFunctional_dilateL3 {lam : ℝ} (hlam : 0 < lam) (u : L3) :
    quotientFunctional (dilateL3 lam hlam u) = quotientFunctional u := by
  refine le_antisymm (le_ciInf fun q => ?_) (le_ciInf fun r => ?_)
  · have hmem : dilateL3 lam hlam (q : L3) ∈ gradientSubspace :=
      dilateL3_mem_gradientSubspace hlam q.2
    have hnorm : ‖dilateL3 lam hlam u + dilateL3 lam hlam (q : L3)‖ = ‖u + (q : L3)‖ := by
      rw [← (dilateL3 lam hlam).map_add, (dilateL3 lam hlam).norm_map]
    calc quotientFunctional (dilateL3 lam hlam u)
        ≤ (1 / 3 : ℝ) * ‖dilateL3 lam hlam u + dilateL3 lam hlam (q : L3)‖ ^ 3 :=
          quotientFunctional_le _ _ hmem
      _ = (1 / 3 : ℝ) * ‖u + (q : L3)‖ ^ 3 := by rw [hnorm]
  · have hmem : (dilateL3 lam hlam).symm (r : L3) ∈ gradientSubspace :=
      dilateL3_symm_mem_gradientSubspace hlam r.2
    have hnorm : ‖u + (dilateL3 lam hlam).symm (r : L3)‖ = ‖dilateL3 lam hlam u + (r : L3)‖ := by
      rw [← (dilateL3 lam hlam).norm_map (u + (dilateL3 lam hlam).symm (r : L3)),
        (dilateL3 lam hlam).map_add, (dilateL3 lam hlam).apply_symm_apply]
    calc quotientFunctional u
        ≤ (1 / 3 : ℝ) * ‖u + (dilateL3 lam hlam).symm (r : L3)‖ ^ 3 :=
          quotientFunctional_le _ _ hmem
      _ = (1 / 3 : ℝ) * ‖dilateL3 lam hlam u + (r : L3)‖ ^ 3 := by rw [hnorm]

/-- The manuscript sentence of `sec:quotient` in one statement: `𝒬` is cubic in
amplitude and invariant under the critical spatial scaling,
`𝒬(a · dilate λ u) = |a|³ 𝒬(u)`.  The amplitude half is
`quotientFunctional_smul` from `NavierFormal/QuotientObjects.lean`, the scaling
half is `quotientFunctional_dilateL3`. -/
theorem quotientFunctional_smul_dilateL3 {lam : ℝ} (hlam : 0 < lam) (a : ℝ) (u : L3) :
    quotientFunctional (a • dilateL3 lam hlam u) = |a| ^ 3 * quotientFunctional u := by
  rw [quotientFunctional_smul, quotientFunctional_dilateL3 hlam]

/-! ### Step 4: transport of minimizing representatives -/

/-- Step 4: the critical dilation transports minimizing representatives.  If
`w` is a minimizing representative of `u` in the sense of `sec:quotient`, then
`dilate λ w` is one for `dilate λ u`. -/
theorem isQuotientMinimizer_dilateL3 {u w : L3} (h : IsQuotientMinimizer u w) {lam : ℝ}
    (hlam : 0 < lam) :
    IsQuotientMinimizer (dilateL3 lam hlam u) (dilateL3 lam hlam w) := by
  refine ⟨?_, fun q hq => ?_⟩
  · rw [← (dilateL3 lam hlam).map_sub]
    exact dilateL3_mem_gradientSubspace hlam h.1
  · have hmem : (dilateL3 lam hlam).symm q ∈ gradientSubspace :=
      dilateL3_symm_mem_gradientSubspace hlam hq
    have hnorm : ‖u + (dilateL3 lam hlam).symm q‖ = ‖dilateL3 lam hlam u + q‖ := by
      rw [← (dilateL3 lam hlam).norm_map (u + (dilateL3 lam hlam).symm q),
        (dilateL3 lam hlam).map_add, (dilateL3 lam hlam).apply_symm_apply]
    calc ‖dilateL3 lam hlam w‖ = ‖w‖ := (dilateL3 lam hlam).norm_map w
      _ ≤ ‖u + (dilateL3 lam hlam).symm q‖ := h.2 _ hmem
      _ = ‖dilateL3 lam hlam u + q‖ := hnorm

end NavierFormal

end

