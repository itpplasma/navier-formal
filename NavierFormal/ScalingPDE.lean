import NavierFormal.Basic
import NavierFormal.Calculus
import NavierFormal.SolutionClass
import NavierFormal.Scaling
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# The critical dilation preserves classical solutions (manuscript `prop:scaling`(i))

This module formalizes the PDE half of the manuscript's Proposition
`prop:scaling`, part (i): for `λ > 0` the critical dilation

`u_λ(x,t) = λ u(λx, λ²t)`,  `p_λ(x,t) = λ² p(λx, λ²t)`

of a classical solution `(u,p)` of the manuscript's `eq:NS` with viscosity `ν`
and datum `u₀` on `ℝ³ × [0,T)` is again a classical solution, with the *same*
viscosity `ν` and datum `λ u₀(λ·)`, on `ℝ³ × [0,T/λ²)`.

`NavierFormal.Scaling` already records the purely metric consequences of this
dilation (the `Lᵖ` scaling identities); nothing there asserts a PDE fact.  This
module adds the pointwise chain-rule lemmas for the spatial dilation `x ↦ λ•x`
(homogeneity of `convection`, `divergence`, `gradient`, `Δ` under this
dilation, mirrored on `IsClassicalSolution.nuNormalization`'s treatment of the
*time* reparametrization in `NavierFormal.SolutionClass`) and the main theorem
`IsClassicalSolution.dilate`.

## Convention

The curried convention of `NavierFormal.SolutionClass` is used throughout,
`u : ℝ → Space → Space`, so the dilated velocity is written
`fun t x => λ • u (λ ^ 2 * t) (λ • x)`, i.e. time first.  This is the same
object as `NavierFormal.Scaling.dilateSpaceTime λ (fun q => u q.1 q.2)`
uncurried; `dilateSpaceTime_uncurry` below records the translation, but the
main theorem is stated directly in the curried form so that it can be read off
against `IsClassicalSolution` without unfolding `dilateSpaceTime`.

Nothing here is a theorem about the Millennium problem.
-/

open MeasureTheory

open scoped ENNReal ContDiff Gradient Laplacian

noncomputable section

namespace NavierFormal

/-! ## Pointwise chain rules for the spatial dilation `x ↦ λ • x` -/

section ChainRules

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Fréchet derivative of a field precomposed with the spatial dilation
`x ↦ c • x`, as a continuous linear map: for `f` differentiable at `c • x`,
`D(f(c·))(x) = (Df(c•x)) ∘ (c • id)`.  The chain-rule ingredient for every
homogeneity lemma below. -/
theorem hasFDerivAt_comp_dilate {f : Space → F} {c : ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f (c • x)) :
    HasFDerivAt (fun y => f (c • y))
      ((fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)) x :=
  hf.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)

/-- `f(c·)` is differentiable at `x` whenever `f` is differentiable at `c • x`. -/
theorem differentiableAt_comp_dilate {f : Space → F} {c : ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f (c • x)) : DifferentiableAt ℝ (fun y => f (c • y)) x :=
  (hasFDerivAt_comp_dilate hf).differentiableAt

/-- The pointwise chain rule for the spatial dilation:
`D(f(c·))(x)h = c • Df(c•x)h` for every direction `h`. -/
theorem fderiv_comp_dilate_apply {f : Space → F} {c : ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f (c • x)) (h : Space) :
    fderiv ℝ (fun y => f (c • y)) x h = c • fderiv ℝ f (c • x) h := by
  rw [(hasFDerivAt_comp_dilate hf).fderiv]
  simp

/-- Convection scales cubically under the critical dilation: for
`u_λ = λ u(λ·)`, `(u_λ·∇)u_λ = λ³((u·∇)u)(λ·)`.  This is the convection half
of the manuscript's `prop:scaling`(i). -/
theorem convection_dilate {v : Space → Space} (c : ℝ) {x : Space}
    (hv : DifferentiableAt ℝ v (c • x)) :
    convection (fun y => c • v (c • y)) x = c ^ 3 • convection v (c • x) := by
  have hd : DifferentiableAt ℝ (fun y => v (c • y)) x := differentiableAt_comp_dilate hv
  have hfd : fderiv ℝ (fun y => c • v (c • y)) x = c • fderiv ℝ (fun y => v (c • y)) x :=
    fderiv_const_smul hd c
  have hstep : convection (fun y => c • v (c • y)) x
      = c • fderiv ℝ (fun y => v (c • y)) x (c • v (c • x)) := by
    simp only [convection, hfd, smul_apply]
  rw [hstep, fderiv_comp_dilate_apply hv, map_smul]
  show c • c • c • convection v (c • x) = c ^ 3 • convection v (c • x)
  rw [smul_smul, smul_smul, show c * c * c = c ^ 3 from by ring]

/-- Divergence scales linearly under the plain spatial dilation `v(λ·)`:
`∇·(v(λ·)) = λ (∇·v)(λ·)`.  Used with the amplitude `λ` in
`divergence_dilate_full` for the manuscript's `prop:scaling`(i). -/
theorem divergence_dilate {v : Space → Space} (c : ℝ) {x : Space}
    (hv : DifferentiableAt ℝ v (c • x)) :
    divergence (fun y => v (c • y)) x = c * divergence v (c • x) := by
  simp only [divergence_eq_sum_component, fderiv_comp_dilate_apply hv]
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Divergence scales quadratically under the critical dilation: for
`u_λ = λ u(λ·)`, `∇·u_λ = λ²(∇·u)(λ·)`.  This is the incompressibility half of
the manuscript's `prop:scaling`(i) (used at value `0`). -/
theorem divergence_dilate_full {v : Space → Space} (c : ℝ) {x : Space}
    (hv : DifferentiableAt ℝ v (c • x)) :
    divergence (fun y => c • v (c • y)) x = c ^ 2 * divergence v (c • x) := by
  have hd : DifferentiableAt ℝ (fun y => v (c • y)) x := differentiableAt_comp_dilate hv
  rw [divergence_const_smul c hd, divergence_dilate c hv]
  ring

/-- The gradient of a scalar field of the form `c² q(c·)` scales cubically:
`∇(c² q(c·)) = c³(∇q)(c·)`.  This is the pressure-gradient half of the
manuscript's `prop:scaling`(i), matching the pressure normalization
`p_λ = λ² p(λ·)`. -/
theorem gradient_const_smul_dilate {q : Space → ℝ} (c : ℝ) {x : Space}
    (hq : DifferentiableAt ℝ q (c • x)) :
    ∇ (fun y => c ^ 2 * q (c • y)) x = c ^ 3 • ∇ q (c • x) := by
  have hd : DifferentiableAt ℝ (fun y => q (c • y)) x := differentiableAt_comp_dilate hq
  have h1 : ∇ (fun y => c ^ 2 * q (c • y)) x = c ^ 2 • ∇ (fun y => q (c • y)) x :=
    gradient_const_smul (c ^ 2) hd
  have h2 : ∇ (fun y => q (c • y)) x = c • ∇ q (c • x) := by
    refine ext_inner_right ℝ fun w => ?_
    rw [inner_gradient_apply, real_inner_smul_left, inner_gradient_apply,
      fderiv_comp_dilate_apply hq, smul_eq_mul]
  rw [h1, h2, smul_smul]
  congr 1

/-- The plain second-order chain rule for the spatial dilation: `Δ(v(c·)) =
c²(Δv)(c·)`, for `v` globally `C^∞`. -/
theorem laplacian_dilate {v : Space → Space} (c : ℝ) (hv : ContDiff ℝ ∞ v) (x : Space) :
    Δ (fun y => v (c • y)) x = c ^ 2 • Δ v (c • x) := by
  have hv2 : ContDiff ℝ 2 v := hv.of_le IsClassicalSolution.two_le_infty
  have hkey := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := 2) c hv2
  have hpt : ∀ i : Fin 3, iteratedFDeriv ℝ 2 (fun y => v (c • y)) x ![e i, e i]
      = c ^ 2 • iteratedFDeriv ℝ 2 v (c • x) ![e i, e i] := by
    intro i
    have := congrFun hkey x
    rw [this]
    simp
  rw [laplacian_eq_sum_iteratedFDeriv, laplacian_eq_sum_iteratedFDeriv]
  simp_rw [hpt]
  rw [Finset.smul_sum]

/-- The Laplacian scales cubically under the critical dilation: for
`u_λ = λ u(λ·)`, `Δu_λ = λ³(Δu)(λ·)`.  This is the diffusion half of the
manuscript's `prop:scaling`(i). -/
theorem laplacian_const_smul_dilate {v : Space → Space} (c : ℝ) (hv : ContDiff ℝ ∞ v)
    (x : Space) : Δ (fun y => c • v (c • y)) x = c ^ 3 • Δ v (c • x) := by
  have hinner : ContDiff ℝ ∞ (fun y => v (c • y)) :=
    hv.comp (contDiff_const_smul c)
  have hd : ContDiffAt ℝ 2 (fun y => v (c • y)) x :=
    (hinner.contDiffAt).of_le IsClassicalSolution.two_le_infty
  show Δ (c • fun y => v (c • y)) x = c ^ 3 • Δ v (c • x)
  rw [InnerProductSpace.laplacian_smul c hd, laplacian_dilate c hv, smul_smul]
  congr 1
  ring

end ChainRules

/-! ## Joint space-time chain rules on the open/closed slab -/

section SpaceTimeChainRules

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint smoothness of a jointly `C^∞` field is preserved by the critical
space-time reparametrization `(s,y) ↦ (c²s, c•y)`: if `U` is jointly `C^∞` on
`(0,T) × ℝ³` and `c > 0`, then `(s,y) ↦ U(c²s, c•y)` is jointly `C^∞` on
`(0,T/c²) × ℝ³`.  This is the smoothness ingredient of the manuscript's
`prop:scaling`(i). -/
theorem contDiffOn_spaceTimeDilate {U : ℝ → Space → F} {T c : ℝ} (hc : 0 < c)
    (h : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2)
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Space => U (c ^ 2 * q.1) (c • q.2))
      (Set.Ioo 0 (T / c ^ 2) ×ˢ (Set.univ : Set Space)) := by
  have hΦ : ContDiff ℝ ∞ (fun q : ℝ × Space => ((c ^ 2 * q.1, c • q.2) : ℝ × Space)) :=
    (contDiff_const.mul contDiff_fst).prodMk (contDiff_snd.const_smul c)
  have hc2 : (0:ℝ) < c ^ 2 := by positivity
  have hmaps : Set.MapsTo (fun q : ℝ × Space => ((c ^ 2 * q.1, c • q.2) : ℝ × Space))
      (Set.Ioo 0 (T / c ^ 2) ×ˢ (Set.univ : Set Space))
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space)) := by
    rintro ⟨s, y⟩ ⟨⟨hs0, hsT⟩, -⟩
    refine ⟨⟨by positivity, ?_⟩, Set.mem_univ _⟩
    have : c ^ 2 * s < c ^ 2 * (T / c ^ 2) := by
      exact mul_lt_mul_of_pos_left hsT hc2
    rwa [mul_div_cancel₀ T hc2.ne'] at this
  exact h.comp hΦ.contDiffOn hmaps

/-- Joint continuity up to the initial time is preserved by the critical
space-time reparametrization. -/
theorem continuousOn_spaceTimeDilate {U : ℝ → Space → F} {T c : ℝ} (hc : 0 < c)
    (h : ContinuousOn (fun q : ℝ × Space => U q.1 q.2)
      (Set.Ico 0 T ×ˢ (Set.univ : Set Space))) :
    ContinuousOn (fun q : ℝ × Space => U (c ^ 2 * q.1) (c • q.2))
      (Set.Ico 0 (T / c ^ 2) ×ˢ (Set.univ : Set Space)) := by
  have hΦ : Continuous (fun q : ℝ × Space => ((c ^ 2 * q.1, c • q.2) : ℝ × Space)) :=
    (continuous_const.mul continuous_fst).prodMk (continuous_snd.const_smul c)
  have hc2 : (0:ℝ) < c ^ 2 := by positivity
  have hmaps : Set.MapsTo (fun q : ℝ × Space => ((c ^ 2 * q.1, c • q.2) : ℝ × Space))
      (Set.Ico 0 (T / c ^ 2) ×ˢ (Set.univ : Set Space))
      (Set.Ico 0 T ×ˢ (Set.univ : Set Space)) := by
    rintro ⟨s, y⟩ ⟨⟨hs0, hsT⟩, -⟩
    refine ⟨⟨by positivity, ?_⟩, Set.mem_univ _⟩
    have : c ^ 2 * s < c ^ 2 * (T / c ^ 2) := by
      exact mul_lt_mul_of_pos_left hsT hc2
    rwa [mul_div_cancel₀ T hc2.ne'] at this
  exact h.comp hΦ.continuousOn hmaps

end SpaceTimeChainRules

/-! ## The main theorem: the critical dilation preserves classical solutions -/

namespace IsClassicalSolution

variable {ν T : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}

/-- The manuscript's Proposition `prop:scaling`(i): the critical dilation
`u_λ(x,t) = λu(λx,λ²t)`, `p_λ(x,t) = λ²p(λx,λ²t)` of a classical solution is a
classical solution with the *same* viscosity `ν` and datum `λu₀(λ·)`, on the
rescaled interval `[0,T/λ²)`.

Transcription: stated in the curried convention of `IsClassicalSolution`,
`u : ℝ → Space → Space`, so the dilated velocity is
`fun s x => λ • u (λ ^ 2 * s) (λ • x)` (time first, matching
`NavierFormal.Scaling.dilateSpaceTime` up to argument order — see
`dilateSpaceTime_uncurry` below) and the dilated pressure is
`fun s x => λ ^ 2 * p (λ ^ 2 * s) (λ • x)`.  No hypothesis beyond `λ > 0` is
added. -/
theorem dilate {lam : ℝ} (hlam : 0 < lam) (h : IsClassicalSolution ν u₀ T u p) :
    IsClassicalSolution ν (fun x => lam • u₀ (lam • x)) (T / lam ^ 2)
      (fun s x => lam • u (lam ^ 2 * s) (lam • x))
      (fun s x => lam ^ 2 * p (lam ^ 2 * s) (lam • x)) where
  smooth_u := (contDiffOn_spaceTimeDilate hlam h.smooth_u).const_smul lam
  smooth_p := by
    have := (contDiffOn_spaceTimeDilate hlam h.smooth_p).const_smul (lam ^ 2)
    simpa only [smul_eq_mul] using this
  cont_u := (continuousOn_spaceTimeDilate hlam h.cont_u).const_smul lam
  cont_p := (continuousOn_spaceTimeDilate hlam h.cont_p).const_smul (lam ^ 2)
  initial := by
    intro x
    simp only [mul_zero, h.initial (lam • x)]
  momentum := by
    intro s x hs hsT
    set t : ℝ := lam ^ 2 * s with ht_def
    have hlam2 : (0:ℝ) < lam ^ 2 := by positivity
    have ht : 0 < t := by rw [ht_def]; positivity
    have htT : t < T := by
      rw [ht_def]
      have : lam ^ 2 * s < lam ^ 2 * (T / lam ^ 2) := mul_lt_mul_of_pos_left hsT hlam2
      rwa [mul_div_cancel₀ T hlam2.ne'] at this
    -- pointwise data at the interior time `t` and dilated position `lam • x`
    have hdu : DifferentiableAt ℝ (u t) (lam • x) := h.differentiableAt_velocity ht htT (lam • x)
    have hdp : DifferentiableAt ℝ (p t) (lam • x) := h.differentiableAt_pressure ht htT (lam • x)
    have hdt : DifferentiableAt ℝ (fun σ => u σ (lam • x)) t :=
      h.differentiableAt_time ht htT (lam • x)
    have hCDu : ContDiff ℝ ∞ (u t) :=
      contDiff_iff_contDiffAt.2 fun y => h.contDiffAt_velocity ht htT y
    -- the time derivative, by the chain rule for `σ ↦ λ² σ`
    have hchain : HasDerivAt (fun σ : ℝ => lam • u (lam ^ 2 * σ) (lam • x))
        (lam ^ 3 • deriv (fun σ => u σ (lam • x)) t) s := by
      have h1 : HasDerivAt (fun σ : ℝ => lam ^ 2 * σ) (lam ^ 2) s := by
        simpa using (hasDerivAt_id s).const_mul (lam ^ 2)
      have h2 : HasDerivAt (fun σ : ℝ => u σ (lam • x))
          (deriv (fun σ => u σ (lam • x)) t) t := hdt.hasDerivAt
      have h3 : HasDerivAt ((fun σ : ℝ => u σ (lam • x)) ∘ fun σ : ℝ => lam ^ 2 * σ)
          (lam ^ 2 • deriv (fun σ => u σ (lam • x)) t) s := HasDerivAt.scomp s h2 h1
      have h4 := h3.const_smul lam
      rw [smul_smul, show lam * lam ^ 2 = lam ^ 3 from by ring] at h4
      exact h4
    have hut : timeDeriv u t (lam • x) = deriv (fun σ => u σ (lam • x)) t :=
      timeDeriv_eq_deriv ht (lam • x)
    have htd : timeDeriv (fun s x => lam • u (lam ^ 2 * s) (lam • x)) s x
        = lam ^ 3 • deriv (fun σ => u σ (lam • x)) t := by
      rw [timeDeriv_eq_deriv hs x]
      exact hchain.deriv
    -- the convection term
    have hconv : convection (fun y => lam • u t (lam • y)) x
        = lam ^ 3 • convection (u t) (lam • x) :=
      convection_dilate lam hdu
    -- the pressure gradient
    have hgrad : ∇ (fun y => lam ^ 2 * p t (lam • y)) x = lam ^ 3 • ∇ (p t) (lam • x) :=
      gradient_const_smul_dilate lam hdp
    -- the Laplacian
    have hlap : Δ (fun y => lam • u t (lam • y)) x = lam ^ 3 • Δ (u t) (lam • x) :=
      laplacian_const_smul_dilate lam hCDu x
    have key : deriv (fun σ => u σ (lam • x)) t + convection (u t) (lam • x)
        + ∇ (p t) (lam • x) = ν • Δ (u t) (lam • x) := by
      rw [← hut]; exact h.momentum t (lam • x) ht htT
    show timeDeriv (fun s x => lam • u (lam ^ 2 * s) (lam • x)) s x
        + convection (fun y => lam • u t (lam • y)) x
        + ∇ (fun y => lam ^ 2 * p t (lam • y)) x
        = ν • Δ (fun y => lam • u t (lam • y)) x
    rw [htd, hconv, hgrad, hlap, ← smul_add, ← smul_add, key]
    rw [smul_smul, mul_comm, ← smul_smul]
  incompressible := by
    intro s x hs hsT
    set t : ℝ := lam ^ 2 * s with ht_def
    have hlam2 : (0:ℝ) < lam ^ 2 := by positivity
    have ht : 0 < t := by rw [ht_def]; positivity
    have htT : t < T := by
      rw [ht_def]
      have : lam ^ 2 * s < lam ^ 2 * (T / lam ^ 2) := mul_lt_mul_of_pos_left hsT hlam2
      rwa [mul_div_cancel₀ T hlam2.ne'] at this
    have hdu : DifferentiableAt ℝ (u t) (lam • x) := h.differentiableAt_velocity ht htT (lam • x)
    show divergence (fun y => lam • u t (lam • y)) x = 0
    rw [divergence_dilate_full lam hdu, h.incompressible t (lam • x) ht htT, mul_zero]

end IsClassicalSolution

/-! ## Relation to `NavierFormal.Scaling.dilateSpaceTime` -/

/-- The dilated field of `IsClassicalSolution.dilate`, uncurried, is
`NavierFormal.Scaling.dilateSpaceTime`: for `U : ℝ × Space → F` curried as
`fun t x => U (t, x)`, `dilateSpaceTime lam U (s,x) = lam • U (lam² s, lam•x)`,
matching `fun s x => lam • (fun t y => U (t,y)) (lam^2*s) (lam•x)` pointwise.
Recorded for cross-reference with `NavierFormal.Scaling`; not used in the
proof of `IsClassicalSolution.dilate` above, which is stated directly in the
curried convention. -/
theorem dilateSpaceTime_uncurry {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : ℝ × Space → F) (lam : ℝ) (s : ℝ) (x : Space) :
    dilateSpaceTime lam U (s, x) = lam • U (lam ^ 2 * s, lam • x) := rfl

end NavierFormal
