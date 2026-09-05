import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NavierFormal.Basic

/-!
# The regularized speed of `prop:pressure`

This module formalizes the pointwise calculus of the regularization used in the
proof of Proposition `prop:pressure` (Exact pressure balance) of the manuscript
`../navier-paper/main.tex`.  The proof there tests the Navier–Stokes system
against `r_ε u` with

* `r_ε = (|u|² + ε)^{1/2}` (`NavierFormal.rEps`), and
* the time primitive
  `H_ε(u) = ((|u|² + ε)^{3/2} - ε^{3/2}) / 3` (`NavierFormal.HEps`),

the constant `ε^{3/2}` being subtracted to make the primitive integrable on
`ℝ³`.  The manuscript's proof uses exactly the following facts about this pair,
all of which are pointwise and are proved here:

* the elementary bounds `|u|²/r_ε ≤ |u|` and `|u|/r_ε ≤ 1` that supply the
  dominating functions for the `ε ↓ 0` limit;
* the majorant `H_ε(u) ≤ C_ε (|u|² + |u|³)` for the time primitive;
* the chain rule `d H_ε(u) = r_ε u · du`, i.e. the statement that `H_ε` is the
  time primitive of `r_ε u · u_t`;
* the gradient bound `|∇ r_ε(u)| ≤ |∇u|`, the pointwise form of the
  manuscript's `|∇|u|| ≤ |∇u|`;
* the pointwise limits `r_ε → |u|` and `H_ε(u) → |u|³/3` as `ε ↓ 0`;
* the product rule for `r_ε u`, whose trace is the divergence identity
  `div (r_ε u) = (|u|/r_ε) u · ∇|u|` quoted in the manuscript.

Everything is stated for a general real inner product space `E`, so that it can
later move to a generic analysis library; the three-dimensional specializations
to `NavierFormal.Space` are recorded at the end.  There are no integrals here:
the measure-theoretic limit of the manuscript's proof is a separate step.

Nothing in this file is a theorem about the Millennium problem.
-/

namespace NavierFormal

open scoped RealInnerProductSpace
open Filter Topology

section General

variable {E : Type*} [NormedAddCommGroup E]

/-- The regularized speed `r_ε = (|v|² + ε)^{1/2}` of the proof of
Proposition `prop:pressure`. -/
noncomputable def rEps (ε : ℝ) (v : E) : ℝ := Real.sqrt (‖v‖ ^ 2 + ε)

/-- The time primitive `H_ε(v) = ((|v|² + ε)^{3/2} - ε^{3/2}) / 3` of
`r_ε v · v_t` used in the proof of Proposition `prop:pressure`.  The constant
`ε^{3/2}` is subtracted exactly as in the manuscript, so that the primitive
vanishes at `v = 0` and is integrable on `ℝ³`. -/
noncomputable def HEps (ε : ℝ) (v : E) : ℝ :=
  ((‖v‖ ^ 2 + ε) ^ ((3 : ℝ) / 2) - ε ^ ((3 : ℝ) / 2)) / 3

/-- The explicit constant `C_ε = 1 + √ε` of the majorant
`H_ε(v) ≤ C_ε (|v|² + |v|³)` used in the proof of Proposition
`prop:pressure`. -/
noncomputable def HEpsConst (ε : ℝ) : ℝ := 1 + Real.sqrt ε

variable {ε : ℝ}

/-- Auxiliary real identity `√a ³ = a^{3/2}` behind the manuscript's writing of
the time primitive `H_ε` of Proposition `prop:pressure` in terms of `r_ε`. -/
theorem sqrt_cube_eq_rpow {a : ℝ} (ha : 0 ≤ a) : Real.sqrt a ^ 3 = a ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (a ^ ((1 : ℝ) / 2)) 3, ← Real.rpow_mul ha]
  norm_num

/-- `r_ε v ² = |v|² + ε`: the defining relation of the regularized speed of
Proposition `prop:pressure`. -/
theorem rEps_sq (hε : 0 ≤ ε) (v : E) : rEps ε v ^ 2 = ‖v‖ ^ 2 + ε :=
  Real.sq_sqrt (add_nonneg (by positivity) hε)

/-- Step (1) of the regularization of Proposition `prop:pressure`: the
regularized speed is strictly positive, which is the whole point of the
regularization. -/
theorem rEps_pos (hε : 0 < ε) (v : E) : 0 < rEps ε v :=
  Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (by positivity) hε)

/-- Step (1) of the regularization of Proposition `prop:pressure`:
`|v| ≤ r_ε v`. -/
theorem norm_le_rEps (hε : 0 ≤ ε) (v : E) : ‖v‖ ≤ rEps ε v := by
  have h : Real.sqrt (‖v‖ ^ 2) ≤ Real.sqrt (‖v‖ ^ 2 + ε) := Real.sqrt_le_sqrt (by linarith)
  rwa [Real.sqrt_sq (norm_nonneg v)] at h

/-- Upper bound `r_ε v ≤ |v| + √ε` for the regularized speed of Proposition
`prop:pressure`; it turns the majorant `H_ε(v) ≤ |v|² r_ε v` into the
manuscript's `C_ε (|v|² + |v|³)`. -/
theorem rEps_le_norm_add_sqrt (hε : 0 ≤ ε) (v : E) : rEps ε v ≤ ‖v‖ + Real.sqrt ε := by
  have hs : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
  have h : ‖v‖ ^ 2 + ε ≤ (‖v‖ + Real.sqrt ε) ^ 2 := by
    nlinarith [Real.sqrt_nonneg ε, norm_nonneg v]
  calc rEps ε v ≤ Real.sqrt ((‖v‖ + Real.sqrt ε) ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖v‖ + Real.sqrt ε := Real.sqrt_sq (by positivity)

/-- Monotonicity of the regularized speed of Proposition `prop:pressure` in the
regularization parameter, the monotone half of the limit `r_ε ↓ |v|`. -/
theorem rEps_mono {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) (v : E) : rEps ε₁ v ≤ rEps ε₂ v :=
  Real.sqrt_le_sqrt (by linarith)

/-- Step (2) of the regularization of Proposition `prop:pressure`: the
dominating bound `|v|²/r_ε ≤ |v|` for the diffusion term. -/
theorem norm_sq_div_rEps_le (hε : 0 < ε) (v : E) : ‖v‖ ^ 2 / rEps ε v ≤ ‖v‖ := by
  rw [div_le_iff₀ (rEps_pos hε v), sq]
  exact mul_le_mul_of_nonneg_left (norm_le_rEps hε.le v) (norm_nonneg v)

/-- Step (2) of the regularization of Proposition `prop:pressure`: the
dominating bound `|v|/r_ε ≤ 1` for the pressure-divergence term. -/
theorem norm_div_rEps_le_one (hε : 0 < ε) (v : E) : ‖v‖ / rEps ε v ≤ 1 :=
  (div_le_one (rEps_pos hε v)).mpr (norm_le_rEps hε.le v)

/-- The regularized speed cubed is the `3/2`-power appearing in the time
primitive `H_ε` of Proposition `prop:pressure`. -/
theorem rEps_cube (hε : 0 ≤ ε) (v : E) : rEps ε v ^ 3 = (‖v‖ ^ 2 + ε) ^ ((3 : ℝ) / 2) :=
  sqrt_cube_eq_rpow (add_nonneg (by positivity) hε)

/-- The time primitive of Proposition `prop:pressure` written through the
regularized speed: `H_ε(v) = (r_ε v ³ - √ε ³)/3`. -/
theorem HEps_eq_cube (hε : 0 ≤ ε) (v : E) :
    HEps ε v = (rEps ε v ^ 3 - Real.sqrt ε ^ 3) / 3 := by
  rw [HEps, ← rEps_cube hε v, ← sqrt_cube_eq_rpow hε]

/-- Step (3) of the regularization of Proposition `prop:pressure`: the time
primitive is nonnegative, so that subtracting `ε^{3/2}` does not spoil sign
information. -/
theorem HEps_nonneg (hε : 0 ≤ ε) (v : E) : 0 ≤ HEps ε v := by
  have h : ε ^ ((3 : ℝ) / 2) ≤ (‖v‖ ^ 2 + ε) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hε (by nlinarith [sq_nonneg ‖v‖]) (by norm_num)
  rw [HEps]
  linarith

/-- Sharp form of the majorant of Proposition `prop:pressure`:
`H_ε(v) ≤ |v|² r_ε v`.  This is the algebraic content of the manuscript's mean
value estimate, obtained here without the mean value theorem from
`r³ - s³ = (r - s)(r² + rs + s²)` and `r² - s² = |v|²`. -/
theorem HEps_le_norm_sq_mul_rEps (hε : 0 ≤ ε) (v : E) : HEps ε v ≤ ‖v‖ ^ 2 * rEps ε v := by
  rw [HEps_eq_cube hε]
  have hr0 : 0 ≤ rEps ε v := Real.sqrt_nonneg _
  have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hsr : Real.sqrt ε ≤ rEps ε v := by
    have : Real.sqrt ε ≤ Real.sqrt (‖v‖ ^ 2 + ε) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖v‖])
    exact this
  have hdiff : rEps ε v ^ 2 - Real.sqrt ε ^ 2 = ‖v‖ ^ 2 := by
    rw [rEps_sq hε, Real.sq_sqrt hε]; ring
  nlinarith [mul_nonneg (sub_nonneg.mpr hsr) (mul_nonneg hr0 hr0),
    mul_nonneg (sub_nonneg.mpr hsr) (mul_nonneg hr0 hs0),
    mul_nonneg (sub_nonneg.mpr hsr) (mul_nonneg hs0 hs0),
    mul_nonneg (sub_nonneg.mpr hsr) (sub_nonneg.mpr (mul_le_mul hsr hsr hs0 hr0))]

/-- Step (3) of the regularization of Proposition `prop:pressure`: the explicit
majorant `H_ε(v) ≤ C_ε (|v|² + |v|³)` with `C_ε = 1 + √ε`, the integrable
time-primitive majorant of the manuscript. -/
theorem HEps_le (hε : 0 ≤ ε) (v : E) : HEps ε v ≤ HEpsConst ε * (‖v‖ ^ 2 + ‖v‖ ^ 3) := by
  have h1 := HEps_le_norm_sq_mul_rEps hε v
  have h2 : ‖v‖ ^ 2 * rEps ε v ≤ ‖v‖ ^ 2 * (‖v‖ + Real.sqrt ε) :=
    mul_le_mul_of_nonneg_left (rEps_le_norm_add_sqrt hε v) (by positivity)
  have hn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hs : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  rw [HEpsConst]
  nlinarith [mul_nonneg hs (pow_nonneg hn 3), pow_nonneg hn 2, pow_nonneg hn 3]

/-- Absolute-value form of the majorant of Proposition `prop:pressure`, the
shape in which the dominated convergence theorem consumes it. -/
theorem abs_HEps_le (hε : 0 ≤ ε) (v : E) :
    |HEps ε v| ≤ HEpsConst ε * (‖v‖ ^ 2 + ‖v‖ ^ 3) := by
  rw [abs_of_nonneg (HEps_nonneg hε v)]
  exact HEps_le hε v

/-- Majorant of Proposition `prop:pressure` that is uniform in the
regularization parameter on `0 < ε ≤ 1`: `|H_ε(v)| ≤ 2 (|v|² + |v|³)`.  This is
the dominating function for the limit `ε ↓ 0`. -/
theorem abs_HEps_le_two (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (v : E) :
    |HEps ε v| ≤ 2 * (‖v‖ ^ 2 + ‖v‖ ^ 3) := by
  have hc : HEpsConst ε ≤ 2 := by
    have : Real.sqrt ε ≤ 1 := by
      have h := Real.sqrt_le_sqrt hε1
      rwa [Real.sqrt_one] at h
    rw [HEpsConst]; linarith
  refine (abs_HEps_le hε v).trans ?_
  exact mul_le_mul_of_nonneg_right hc (by positivity)


/-- Step (6) of the regularization of Proposition `prop:pressure`: the
regularized speed converges to the speed, `r_ε v → |v|` as `ε ↓ 0`. -/
theorem tendsto_rEps (v : E) :
    Tendsto (fun ε : ℝ => rEps ε v) (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖v‖) := by
  have hc : Continuous fun ε : ℝ => rEps ε v := (continuous_const.add continuous_id).sqrt
  have h0 : rEps 0 v = ‖v‖ := by
    simp [rEps, Real.sqrt_sq (norm_nonneg v)]
  have h : Tendsto (fun ε : ℝ => rEps ε v) (nhdsWithin 0 (Set.Ioi 0)) (nhds (rEps 0 v)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  rwa [h0] at h

/-- Step (6) of the regularization of Proposition `prop:pressure`: the
regularized time primitive converges to the primitive of the cubic energy
density, `H_ε(v) → |v|³/3` as `ε ↓ 0`. -/
theorem tendsto_HEps (v : E) :
    Tendsto (fun ε : ℝ => HEps ε v) (nhdsWithin 0 (Set.Ioi 0)) (nhds (‖v‖ ^ 3 / 3)) := by
  have hc : Continuous fun ε : ℝ =>
      (Real.sqrt (‖v‖ ^ 2 + ε) ^ 3 - Real.sqrt ε ^ 3) / 3 :=
    ((((continuous_const.add continuous_id).sqrt).pow 3).sub
      (Real.continuous_sqrt.pow 3)).div_const 3
  have h0 : (Real.sqrt (‖v‖ ^ 2 + (0 : ℝ)) ^ 3 - Real.sqrt (0 : ℝ) ^ 3) / 3 = ‖v‖ ^ 3 / 3 := by
    simp [Real.sqrt_sq (norm_nonneg v)]
  have ht : Tendsto (fun ε : ℝ => (Real.sqrt (‖v‖ ^ 2 + ε) ^ 3 - Real.sqrt ε ^ 3) / 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (‖v‖ ^ 3 / 3)) := by
    have h : Tendsto (fun ε : ℝ => (Real.sqrt (‖v‖ ^ 2 + ε) ^ 3 - Real.sqrt ε ^ 3) / 3)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((Real.sqrt (‖v‖ ^ 2 + (0 : ℝ)) ^ 3 - Real.sqrt (0 : ℝ) ^ 3) / 3)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    rwa [h0] at h
  refine Filter.Tendsto.congr' ?_ ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (HEps_eq_cube (le_of_lt hε) v).symm

end General

section Differential

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {ε : ℝ}

/-- The value of the candidate differential of `r_ε ∘ u` from Proposition
`prop:pressure`: it is the manuscript's `u · du / r_ε`. -/
theorem rEps_fderiv_apply (ε : ℝ) (v : E) (L : X →L[ℝ] E) (h : X) :
    ((rEps ε v)⁻¹ • ((innerSL ℝ v).comp L)) h = ⟪v, L h⟫ / rEps ε v := by
  simp [div_eq_inv_mul]

/-- Step (4) of the regularization of Proposition `prop:pressure`: the chain
rule for the regularized speed.  For a map `u` differentiable at `x` the
composition `r_ε ∘ u` is differentiable at `x` with differential
`h ↦ ⟪u x, u' h⟫ / r_ε (u x)`. -/
theorem hasFDerivAt_rEps {u : X → E} {u' : X →L[ℝ] E} {x : X} (hε : 0 < ε)
    (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => rEps ε (u y))
      ((rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp u')) x := by
  have hpos : (0 : ℝ) < ‖u x‖ ^ 2 + ε := add_pos_of_nonneg_of_pos (by positivity) hε
  have h1 : HasFDerivAt (fun y => ‖u y‖ ^ 2 + ε) (2 • (innerSL ℝ (u x)).comp u') x :=
    hu.norm_sq.add_const ε
  have h2 : HasFDerivAt (fun y => rEps ε (u y))
      ((1 / (2 * Real.sqrt (‖u x‖ ^ 2 + ε))) • (2 • ((innerSL ℝ (u x)).comp u'))) x :=
    h1.sqrt hpos.ne'
  refine h2.congr_fderiv ?_
  have hr : Real.sqrt (‖u x‖ ^ 2 + ε) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  ext h
  simp only [rEps]
  simp
  field_simp

/-- Step (4) of the regularization of Proposition `prop:pressure`: `H_ε` is the
time primitive of `r_ε u · u_t`.  For a map `u` differentiable at `x` the
composition `H_ε ∘ u` is differentiable at `x` with differential
`h ↦ r_ε (u x) ⟪u x, u' h⟫`, which is the manuscript's identity
`d/dt H_ε(u) = r_ε u · u_t`. -/
theorem hasFDerivAt_HEps {u : X → E} {u' : X →L[ℝ] E} {x : X} (hε : 0 < ε)
    (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => HEps ε (u y))
      (rEps ε (u x) • ((innerSL ℝ (u x)).comp u')) x := by
  have hfun : (fun y => HEps ε (u y))
      = fun y => (3 : ℝ)⁻¹ * (rEps ε (u y) ^ 3 - Real.sqrt ε ^ 3) := by
    funext y
    rw [HEps_eq_cube hε.le]
    ring
  rw [hfun]
  have hr := hasFDerivAt_rEps hε hu
  have h3 := ((hr.pow 3).sub_const (Real.sqrt ε ^ 3)).const_mul (3 : ℝ)⁻¹
  refine h3.congr_fderiv ?_
  have hrne : rEps ε (u x) ≠ 0 := (rEps_pos hε (u x)).ne'
  ext h
  simp
  field_simp

/-- Step (5) of the regularization of Proposition `prop:pressure`: the gradient
bound `|∇ r_ε(u)| ≤ |∇u|` in operator norm.  It is the regularized form of the
manuscript's `|∇|u|| ≤ |∇u|`, and is what makes the diffusion terms dominated
uniformly in `ε`. -/
theorem opNorm_rEps_fderiv_le (hε : 0 < ε) (v : E) (L : X →L[ℝ] E) :
    ‖(rEps ε v)⁻¹ • ((innerSL ℝ v).comp L)‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun h => ?_
  have hr : 0 < rEps ε v := rEps_pos hε v
  have h1 : ‖((rEps ε v)⁻¹ • ((innerSL ℝ v).comp L)) h‖ = |⟪v, L h⟫| / rEps ε v := by
    rw [rEps_fderiv_apply, Real.norm_eq_abs, abs_div, abs_of_pos hr]
  rw [h1, div_le_iff₀ hr]
  have hb : |⟪v, L h⟫| ≤ ‖v‖ * ‖L h‖ := abs_real_inner_le_norm v (L h)
  have key : ‖v‖ * ‖L h‖ ≤ rEps ε v * (‖L‖ * ‖h‖) :=
    mul_le_mul (norm_le_rEps hε.le v) (L.le_opNorm h) (norm_nonneg _) hr.le
  linarith

/-- The value of the candidate differential of `x ↦ r_ε (u x) • u x` from
Proposition `prop:pressure`. -/
theorem rEps_smul_fderiv_apply (ε : ℝ) (v : E) (L : X →L[ℝ] E) (h : X) :
    ((((rEps ε v)⁻¹ • ((innerSL ℝ v).comp L)).smulRight v) + rEps ε v • L) h
      = (⟪v, L h⟫ / rEps ε v) • v + rEps ε v • L h := by
  simp [div_eq_inv_mul]

/-- The divergence-type identity of Proposition `prop:pressure`: the product
rule for the tested field `r_ε u`.  For a field `u` differentiable at `x`,
`x ↦ r_ε (u x) • u x` is differentiable at `x` and its differential in the
direction `h` is `(⟪u x, u' h⟫ / r_ε (u x)) • u x + r_ε (u x) • u' h`.  Taking
the trace of this differential is the manuscript's
`div (r_ε u) = (|u|/r_ε) u · ∇|u|`. -/
theorem hasFDerivAt_rEps_smul {u : X → E} {u' : X →L[ℝ] E} {x : X} (hε : 0 < ε)
    (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => rEps ε (u y) • u y)
      ((((rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp u')).smulRight (u x))
        + rEps ε (u x) • u') x := by
  have h : HasFDerivAt (fun y => rEps ε (u y) • u y)
      (rEps ε (u x) • u'
        + (((rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp u')).smulRight (u x))) x :=
    (hasFDerivAt_rEps hε hu).smul hu
  exact h.congr_fderiv (add_comm _ _)

end Differential

section ThreeDimensional

variable {ε : ℝ}

/-- Three-dimensional specialization of the chain rule for the regularized
speed of Proposition `prop:pressure`, on `NavierFormal.Space = ℝ³`. -/
theorem hasFDerivAt_rEps_space {u : Space → Space} {u' : Space →L[ℝ] Space} {x : Space}
    (hε : 0 < ε) (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => rEps ε (u y))
      ((rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp u')) x :=
  hasFDerivAt_rEps hε hu

/-- Three-dimensional specialization of the time-primitive identity
`d H_ε(u) = r_ε u · du` of Proposition `prop:pressure`, on
`NavierFormal.Space = ℝ³`. -/
theorem hasFDerivAt_HEps_space {u : Space → Space} {u' : Space →L[ℝ] Space} {x : Space}
    (hε : 0 < ε) (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => HEps ε (u y))
      (rEps ε (u x) • ((innerSL ℝ (u x)).comp u')) x :=
  hasFDerivAt_HEps hε hu

/-- Three-dimensional specialization of the divergence-type product rule for
the tested field `r_ε u` of Proposition `prop:pressure`, on
`NavierFormal.Space = ℝ³`. -/
theorem hasFDerivAt_rEps_smul_space {u : Space → Space} {u' : Space →L[ℝ] Space} {x : Space}
    (hε : 0 < ε) (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => rEps ε (u y) • u y)
      ((((rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp u')).smulRight (u x))
        + rEps ε (u x) • u') x :=
  hasFDerivAt_rEps_smul hε hu

end ThreeDimensional

end NavierFormal

