import NavierFormal.Basic
import NavierFormal.Calculus
import NavierFormal.IBP
import NavierFormal.SolutionClass
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The energy identity (manuscript `prop:energy`)

Placeholder header; filled in once the mathematics is in place.
-/

open MeasureTheory InnerProductSpace Laplacian
open scoped RealInnerProductSpace ENNReal ContDiff Gradient

noncomputable section

namespace NavierFormal
namespace Energy

/-! ## The `L²` curve attached to a time-dependent field -/

open scoped Classical in
/-- The `L²` element represented by a field, with junk value `0` for a field
outside `L²`.  This is a proof-free implementation device: it lets the
time-dependent field of `eq:NS` be differentiated as a curve in the Hilbert
space `L²(ℝ³)³` without carrying `MemLp` proof terms inside any statement.  It
occurs in no statement of this module. -/
def toL2 (v : Space → Space) : Space →₂[volume] Space :=
  if h : MemLp v 2 volume then h.toLp v else 0

theorem coeFn_toL2 {v : Space → Space} (h : MemLp v 2 volume) :
    ⇑(toL2 v) =ᵐ[volume] v := by
  classical
  rw [toL2, dif_pos h]
  exact h.coeFn_toLp

theorem norm_toL2 {v : Space → Space} (h : MemLp v 2 volume) :
    ‖toL2 v‖ = (eLpNorm v 2 volume).toReal := by
  classical
  rw [toL2, dif_pos h, Lp.norm_toLp]

/-- The squared `L²` norm of the curve is the manuscript's `‖v‖₂²`, i.e.
`NavierFormal.kineticEnergy v = ∫ |v|²`. -/
theorem norm_toL2_sq {v : Space → Space} (h : MemLp v 2 volume) :
    ‖toL2 v‖ ^ 2 = kineticEnergy v := by
  have h1 : ⟪toL2 v, toL2 v⟫ = ‖toL2 v‖ ^ 2 := real_inner_self_eq_norm_sq _
  have h2 : ⟪toL2 v, toL2 v⟫ = ∫ x, ⟪(toL2 v : Space → Space) x, (toL2 v : Space → Space) x⟫ :=
    L2.inner_def _ _
  rw [← h1, h2]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 h] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- The `L²` inner product of two curves is the manuscript's `⟨v,w⟩_{L²}`. -/
theorem inner_toL2 {v w : Space → Space} (hv : MemLp v 2 volume) (hw : MemLp w 2 volume) :
    ⟪toL2 v, toL2 w⟫ = ∫ x, ⟪v x, w x⟫ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 hv, coeFn_toL2 hw] with x hx hy
  rw [hx, hy]


/-! ## Differentiability in `L²` (manuscript `lem:R-consequences`(a)) -/

/-- The manuscript's `lem:R-consequences`(a) at one time: the difference quotients
`(τ-t)⁻¹(u(τ)-u(t))` converge **in `L²(ℝ³)³`** to the field `ut` as `τ → t` inside
`s`, one-sided at an endpoint of `s`.  This is the statement `u ∈ C¹([0,T];L²)`
localized at `t`, which the manuscript reads off from the local theory and which
is the only input of Step 1 of the proof of `prop:energy`.

The convergence is written with `eLpNorm … 2 volume` in `ℝ≥0∞`, so no `MemLp`
proof term occurs in the predicate and the condition is *not* vacuously true for
a field outside `L²`. -/
def HasL2DerivWithinAt (u : ℝ → Space → Space) (ut : Space → Space) (s : Set ℝ) (t : ℝ) : Prop :=
  Filter.Tendsto
    (fun τ => eLpNorm (fun x => (τ - t)⁻¹ • (u τ x - u t x) - ut x) 2 volume)
    (nhdsWithin t (s \ {t})) (nhds 0)

/-- Unbundling of `HasL2DerivWithinAt`: an `L²`-differentiable field is a
differentiable curve in the Hilbert space `L²(ℝ³)³`. -/
theorem hasDerivWithinAt_toL2 {u : ℝ → Space → Space} {ut : Space → Space} {s : Set ℝ} {t : ℝ}
    (hmem : ∀ τ ∈ s, MemLp (u τ) 2 volume) (hts : t ∈ s) (hut : MemLp ut 2 volume)
    (h : HasL2DerivWithinAt u ut s t) :
    HasDerivWithinAt (fun τ => toL2 (u τ)) (toL2 ut) s t := by
  rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ τ ∈ s \ {t},
      ‖slope (fun σ => toL2 (u σ)) t τ - toL2 ut‖
        = (eLpNorm (fun x => (τ - t)⁻¹ • (u τ x - u t x) - ut x) 2 volume).toReal := by
    intro τ hτ
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (slope (fun σ => toL2 (u σ)) t τ) (toL2 ut),
      Lp.coeFn_smul (τ - t)⁻¹ (toL2 (u τ) - toL2 (u t)),
      Lp.coeFn_sub (toL2 (u τ)) (toL2 (u t)),
      coeFn_toL2 (hmem τ hτ.1), coeFn_toL2 (hmem t hts), coeFn_toL2 hut] with x h1 h2 h3 h4 h5 h6
    rw [slope_def_module] at h1 ⊢
    simp only [Pi.sub_apply, Pi.smul_apply] at h1 h2 h3
    rw [h1, h2, h3, h4, h5, h6]
  have hcomp : Filter.Tendsto
      (fun τ => (eLpNorm (fun x => (τ - t)⁻¹ • (u τ x - u t x) - ut x) 2 volume).toReal)
      (nhdsWithin t (s \ {t})) (nhds 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [Function.comp_def] using this
  exact hcomp.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
    (fun τ hτ => (key τ hτ).symm))

/-! ## Step 1: differentiation of the energy -/

/-- **Step 1 of the manuscript's proof of `prop:energy`.**  If the field is
`L²`-differentiable in time at `t` (manuscript `lem:R-consequences`(a)), then the
kinetic energy `‖u(τ)‖₂² = ∫|u(τ)|²` is differentiable at `t` with

`d/dτ ‖u(τ)‖₂²|_{τ=t} = 2 ∫ ⟪u(t), u_t(t)⟫`,

which is the manuscript's `eq:energy-derivative` (there written for
`E = ½‖u‖₂²`).  The proof is the manuscript's: the difference quotient of the
energy is `½⟪(u(τ)-u(t))/(τ-t), u(τ)+u(t)⟫_{L²}`, and continuity of the `L²`
inner product passes to the limit.  Here that argument is Mathlib's chain rule
for `‖·‖²` on the Hilbert space `L²(ℝ³)³`. -/
theorem hasDerivWithinAt_kineticEnergy {u : ℝ → Space → Space} {ut : Space → Space}
    {s : Set ℝ} {t : ℝ} (hmem : ∀ τ ∈ s, MemLp (u τ) 2 volume) (hts : t ∈ s)
    (hut : MemLp ut 2 volume) (h : HasL2DerivWithinAt u ut s t) :
    HasDerivWithinAt (fun τ => kineticEnergy (u τ)) (2 * ∫ x, ⟪u t x, ut x⟫) s t := by
  have hsq := (hasDerivWithinAt_toL2 hmem hts hut h).norm_sq
  rw [inner_toL2 (hmem t hts) hut] at hsq
  exact hsq.congr (fun τ hτ => (norm_toL2_sq (hmem τ hτ)).symm)
    (norm_toL2_sq (hmem t hts)).symm

/-! ## Steps 2–4: the three spatial integrals -/

/-- The integrability input that the manuscript's proof of `prop:energy` takes
from the local theory at a single time (manuscript `lem:R-consequences`(b),(c),
via the `H^k` bounds of the regularity package `R`).

Each field is exactly one hypothesis of one of the four boundary-free
integrations by parts of `NavierFormal.IBP`, and none of them follows from
`IsClassicalSolution` alone: Mathlib's integration by parts is the "integrable
function with integrable derivative" version, so the decay of `u` and `p` has to
enter as an explicit `L¹` statement.  In the manuscript the same conditions are
obtained from `u(t), p(t) ∈ H^k` for all `k` together with `u(t) ∈ L^q`,
`2 ≤ q ≤ ∞`; the Hölder estimates carrying that out are `lem:R-consequences`(c). -/
structure SpatialIntegrability (v : Space → Space) (q : Space → ℝ) : Prop where
  /-- `|v| |∇v| ∈ L¹`: the primitive of the viscous integration by parts. -/
  norm_mul_fderiv : Integrable (fun x => ‖v x‖ * ‖fderiv ℝ v x‖) volume
  /-- `‖∇v‖_F² ∈ L¹`: the dissipation itself is finite. -/
  enstrophy : Integrable (enstrophyDensity v) volume
  /-- `|v| |∇²v| ∈ L¹`: the left-hand side `⟪v, Δv⟫` of the viscous identity. -/
  norm_mul_fderiv2 : Integrable (fun x => ‖v x‖ * ‖fderiv ℝ (fderiv ℝ v) x‖) volume
  /-- `|v|³ ∈ L¹`, i.e. `v ∈ L³`: the primitive `v|v|²` of the transport term. -/
  norm_cube : Integrable (fun x => ‖v x‖ ^ 3) volume
  /-- `|v|² |∇v| ∈ L¹`: the derivative of that primitive. -/
  norm_sq_mul_fderiv : Integrable (fun x => ‖v x‖ ^ 2 * ‖fderiv ℝ v x‖) volume
  /-- `|q| |v| ∈ L¹`: the primitive `q v` of the pressure term. -/
  pressure_mul : Integrable (fun x => ‖q x‖ * ‖v x‖) volume
  /-- `|q| |∇v| ∈ L¹`: half of the derivative of that primitive. -/
  pressure_mul_fderiv : Integrable (fun x => ‖q x‖ * ‖fderiv ℝ v x‖) volume
  /-- `|∇q| |v| ∈ L¹`: the other half, and the left-hand side `⟪v, ∇q⟫`. -/
  fderiv_pressure_mul : Integrable (fun x => ‖fderiv ℝ q x‖ * ‖v x‖) volume

/-- `1 ≤ ∞` in the smoothness-order lattice, the companion of
`NavierFormal.IsClassicalSolution.two_le_infty`. -/
theorem one_le_infty : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
  WithTop.coe_le_coe.2 le_top

variable {ν T : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}

/-- At an interior time the velocity of a classical solution is `C²` on all of
`ℝ³`, which is what the viscous integration by parts asks for. -/
theorem contDiff_velocity (hsol : IsClassicalSolution ν u₀ T u p) {τ : ℝ}
    (hτ : 0 < τ) (hτT : τ < T) : ContDiff ℝ 2 (u τ) :=
  contDiff_iff_contDiffAt.2 fun x =>
    (hsol.contDiffAt_velocity hτ hτT x).of_le IsClassicalSolution.two_le_infty

/-- At an interior time the pressure of a classical solution is `C¹` on all of
`ℝ³`. -/
theorem contDiff_pressure (hsol : IsClassicalSolution ν u₀ T u p) {τ : ℝ}
    (hτ : 0 < τ) (hτT : τ < T) : ContDiff ℝ 1 (p τ) :=
  contDiff_iff_contDiffAt.2 fun x => (hsol.contDiffAt_pressure hτ hτT x).of_le one_le_infty

/-- **Steps 2–4 of the manuscript's proof of `prop:energy`, assembled.**

For a classical solution of `eq:NS` at an interior time `τ`, with the manuscript's
`L¹` input,

`∫ ⟪u(τ), ∂ₜu(τ)⟫ = -ν ∫ ‖∇u(τ)‖²`.

The three terms of `eq:energy-derivative` are evaluated by the three
integrations by parts of `NavierFormal.IBP`: the diffusion term gives
`∫⟪u,Δu⟫ = -∫‖∇u‖²` (Step 2), the convection term vanishes for a
divergence-free field (Step 3), and the pressure term vanishes because
`∫⟪u,∇p⟫ = -∫ p (∇·u) = 0` (Step 4).  The dissipation density is the Frobenius
one, `enstrophyDensity`, as everywhere in this development. -/
theorem integral_inner_timeDeriv_eq (hsol : IsClassicalSolution ν u₀ T u p) {τ : ℝ}
    (hτ : 0 < τ) (hτT : τ < T) (hint : SpatialIntegrability (u τ) (p τ)) :
    ∫ x, ⟪u τ x, timeDeriv u τ x⟫ = -(ν * ∫ x, enstrophyDensity (u τ) x) := by
  have hu2 : ContDiff ℝ 2 (u τ) := contDiff_velocity hsol hτ hτT
  have hu1 : ContDiff ℝ 1 (u τ) := hu2.of_le one_le_two
  have hp1 : ContDiff ℝ 1 (p τ) := contDiff_pressure hsol hτ hτT
  have hdiv : ∀ x, divergence (u τ) x = 0 := fun x => hsol.incompressible τ x hτ hτT
  have hucont : Continuous (u τ) := hu1.continuous
  have hdu : Continuous (fderiv ℝ (u τ)) := hu1.continuous_fderiv one_ne_zero
  have hdp : Continuous (fderiv ℝ (p τ)) := hp1.continuous_fderiv one_ne_zero
  -- the three terms of `eq:energy-derivative` are integrable
  have IL : Integrable (fun x => ⟪u τ x, Δ (u τ) x⟫) volume := by
    refine (hint.norm_mul_fderiv2.const_mul 3).mono'
      (hucont.inner (IBP.continuous_laplacian hu2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖u τ x‖ * ‖Δ (u τ) x‖ ≤ ‖u τ x‖ * (3 * ‖fderiv ℝ (fderiv ℝ (u τ)) x‖) := by
          gcongr
          exact IBP.norm_laplacian_le _ x
      _ = 3 * (‖u τ x‖ * ‖fderiv ℝ (fderiv ℝ (u τ)) x‖) := by ring
  have IC : Integrable (fun x => ⟪u τ x, convection (u τ) x⟫) volume := by
    refine hint.norm_sq_mul_fderiv.mono'
      (hucont.inner (hdu.clm_apply hucont)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖u τ x‖ * ‖convection (u τ) x‖
        ≤ ‖u τ x‖ * (‖fderiv ℝ (u τ) x‖ * ‖u τ x‖) := by
          gcongr
          exact (fderiv ℝ (u τ) x).le_opNorm (u τ x)
      _ = ‖u τ x‖ ^ 2 * ‖fderiv ℝ (u τ) x‖ := by ring
  have IP : Integrable (fun x => fderiv ℝ (p τ) x (u τ x)) volume := by
    refine hint.fderiv_pressure_mul.mono'
      (hdp.clm_apply hucont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simpa using (fderiv ℝ (p τ) x).le_opNorm (u τ x)
  -- the pointwise form of `eq:energy-derivative`
  have hpt : ∀ x, ⟪u τ x, timeDeriv u τ x⟫
      = ν * ⟪u τ x, Δ (u τ) x⟫ - ⟪u τ x, convection (u τ) x⟫
        - fderiv ℝ (p τ) x (u τ x) := by
    intro x
    have hm := hsol.momentum τ x hτ hτT
    have hts : timeDeriv u τ x = ν • Δ (u τ) x - convection (u τ) x - ∇ (p τ) x := by
      rw [← hm]; abel
    have hgrad : ⟪u τ x, ∇ (p τ) x⟫ = fderiv ℝ (p τ) x (u τ x) := by
      rw [real_inner_comm]
      exact inner_gradient_apply (p τ) x (u τ x)
    rw [hts, inner_sub_right, inner_sub_right, real_inner_smul_right, hgrad]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have e1 : ∫ x, (ν * ⟪u τ x, Δ (u τ) x⟫ - ⟪u τ x, convection (u τ) x⟫
        - fderiv ℝ (p τ) x (u τ x))
      = (∫ x, (ν * ⟪u τ x, Δ (u τ) x⟫ - ⟪u τ x, convection (u τ) x⟫))
        - ∫ x, fderiv ℝ (p τ) x (u τ x) :=
    integral_sub ((IL.const_mul ν).sub IC) IP
  have e2 : ∫ x, (ν * ⟪u τ x, Δ (u τ) x⟫ - ⟪u τ x, convection (u τ) x⟫)
      = (∫ x, ν * ⟪u τ x, Δ (u τ) x⟫) - ∫ x, ⟪u τ x, convection (u τ) x⟫ :=
    integral_sub (IL.const_mul ν) IC
  have e3 : ∫ x, ν * ⟪u τ x, Δ (u τ) x⟫ = ν * ∫ x, ⟪u τ x, Δ (u τ) x⟫ :=
    integral_const_mul _ _
  have e4 := IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity hu2
    hint.norm_mul_fderiv hint.enstrophy hint.norm_mul_fderiv2
  have e5 : ∫ x, ⟪u τ x, convection (u τ) x⟫ = 0 :=
    IBP.integral_inner_convection_eq_zero hu1 hdiv hint.norm_cube hint.norm_sq_mul_fderiv
  have e6 : ∫ x, fderiv ℝ (p τ) x (u τ x) = 0 := by
    rw [IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence hu1 hp1 hint.pressure_mul
      hint.pressure_mul_fderiv hint.fderiv_pressure_mul]
    simp [hdiv]
  rw [e1, e2, e3, e4, e5, e6]
  ring

/-! ## Step 5: the energy identity -/

/-- The manuscript's dissipation `‖∇v‖₂² = ∫ ‖∇v‖²`, with the Frobenius density
`NavierFormal.enstrophyDensity` (design decision D7).  Junk value `0` for a field
whose gradient is not square integrable; inside `prop:energy` the finiteness is
the hypothesis `SpatialIntegrability.enstrophy`. -/
def dissipation (v : Space → Space) : ℝ := ∫ x, enstrophyDensity v x

theorem dissipation_nonneg (v : Space → Space) : 0 ≤ dissipation v :=
  integral_nonneg fun x => enstrophyDensity_nonneg v x

/-- Steps 1–4 combined: for a classical solution of `eq:NS` which is
`L²`-differentiable in time, the energy `E(τ) = ½‖u(τ)‖₂²` is differentiable at
every interior time with `E'(τ) = -ν‖∇u(τ)‖₂²`.  This is the displayed
conclusion of Step 5 of the manuscript's proof of `prop:energy`. -/
theorem hasDerivWithinAt_energy (hsol : IsClassicalSolution ν u₀ T u p) {a b τ : ℝ}
    (hmem : ∀ σ ∈ Set.Icc a b, MemLp (u σ) 2 volume)
    (hut : ∀ σ ∈ Set.Icc a b, MemLp (timeDeriv u σ) 2 volume)
    (hL2 : ∀ σ ∈ Set.Icc a b, HasL2DerivWithinAt u (timeDeriv u σ) (Set.Icc a b) σ)
    (hτ : τ ∈ Set.Icc a b) (hτ0 : 0 < τ) (hτT : τ < T)
    (hint : SpatialIntegrability (u τ) (p τ)) :
    HasDerivWithinAt (fun σ => kineticEnergy (u σ) / 2) (-(ν * dissipation (u τ)))
      (Set.Icc a b) τ := by
  have h1 := (hasDerivWithinAt_kineticEnergy hmem hτ (hut τ hτ) (hL2 τ hτ)).div_const 2
  rw [integral_inner_timeDeriv_eq hsol hτ0 hτT hint] at h1
  have h2 : (2 : ℝ) * -(ν * ∫ x, enstrophyDensity (u τ) x) / 2 = -(ν * dissipation (u τ)) := by
    show (2 : ℝ) * -(ν * ∫ x, enstrophyDensity (u τ) x) / 2
      = -(ν * ∫ x, enstrophyDensity (u τ) x)
    ring
  rwa [h2] at h1

/-- Continuity of the energy on the closed interval, from `L²`-differentiability
alone (no use of `eq:NS`).  This is the "`E ∈ C¹`" half of Step 5. -/
theorem continuousOn_energy {a b : ℝ}
    (hmem : ∀ σ ∈ Set.Icc a b, MemLp (u σ) 2 volume)
    (hut : ∀ σ ∈ Set.Icc a b, MemLp (timeDeriv u σ) 2 volume)
    (hL2 : ∀ σ ∈ Set.Icc a b, HasL2DerivWithinAt u (timeDeriv u σ) (Set.Icc a b) σ) :
    ContinuousOn (fun σ => kineticEnergy (u σ) / 2) (Set.Icc a b) := fun σ hσ =>
  ((hasDerivWithinAt_kineticEnergy hmem hσ (hut σ hσ)
    (hL2 σ hσ)).continuousWithinAt).div_const 2

/-- **The energy identity, manuscript `prop:energy` `eq:energy`.**

For a classical solution of `eq:NS` on `ℝ³ × [0,T)` which carries the
manuscript's regularity input on a compact time interval `[a,b] ⊆ [0,T)`,

`½‖u(b)‖₂² + ν ∫_a^b ‖∇u(τ)‖₂² dτ = ½‖u(a)‖₂²`.

The proof is the manuscript's Step 5: `E(τ) = ½‖u(τ)‖₂²` is continuous on
`[a,b]`, differentiable on `(a,b)` with `E'(τ) = -ν‖∇u(τ)‖₂²` (Steps 1–4), and
the fundamental theorem of calculus applies. -/
theorem energy_identity (hsol : IsClassicalSolution ν u₀ T u p) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 ≤ a) (hbT : b < T)
    (hmem : ∀ σ ∈ Set.Icc a b, MemLp (u σ) 2 volume)
    (hut : ∀ σ ∈ Set.Icc a b, MemLp (timeDeriv u σ) 2 volume)
    (hL2 : ∀ σ ∈ Set.Icc a b, HasL2DerivWithinAt u (timeDeriv u σ) (Set.Icc a b) σ)
    (hint : ∀ σ ∈ Set.Ioo a b, SpatialIntegrability (u σ) (p σ))
    (hdiss : IntervalIntegrable (fun σ => dissipation (u σ)) volume a b) :
    kineticEnergy (u b) / 2 + ν * ∫ σ in a..b, dissipation (u σ) = kineticEnergy (u a) / 2 := by
  have hcont : ContinuousOn (fun σ => kineticEnergy (u σ) / 2) (Set.Icc a b) :=
    continuousOn_energy hmem hut hL2
  have hderiv : ∀ τ ∈ Set.Ioo a b,
      HasDerivWithinAt (fun σ => kineticEnergy (u σ) / 2) (-(ν * dissipation (u τ)))
        (Set.Ioi τ) τ := by
    intro τ hτ
    have hmemτ : Set.Icc a b ∈ nhds τ :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hτ) Set.Ioo_subset_Icc_self
    have h := hasDerivWithinAt_energy hsol hmem hut hL2 (Set.Ioo_subset_Icc_self hτ)
      (lt_of_le_of_lt ha hτ.1) (lt_trans hτ.2 hbT) (hint τ hτ)
    exact (h.hasDerivAt hmemτ).hasDerivWithinAt
  have hintg : IntervalIntegrable (fun σ => -(ν * dissipation (u σ))) volume a b :=
    (hdiss.const_mul ν).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hintg
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hFTC
  linarith

end Energy
end NavierFormal

end
