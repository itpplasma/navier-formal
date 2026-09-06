import NavierFormal.DensityBridge
import NavierFormal.IBP
import NavierFormal.SolutionClass
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The exact pressure balance (manuscript `prop:pressure`)

Work in progress.
-/

namespace NavierFormal

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

noncomputable section

variable {ε : ℝ} {q : Space → ℝ} {v : Space → Space} {x : Space}

/-! ## The regularized objects of the proof -/

/-- The manuscript's regularized time primitive integral
`Φ_ε = ∫ H_ε(v)`. -/
def HEpsIntegral (ε : ℝ) (v : Space → Space) : ℝ := ∫ x, HEps ε (v x)

/-- The density of the manuscript's regularized dissipation `D_ε`. -/
def D3densityEps (ε : ℝ) (v : Space → Space) (x : Space) : ℝ :=
  rEps ε (v x) * frobeniusNormSq (fderiv ℝ v x) + ‖gradTranspose v x‖ ^ 2 / rEps ε (v x)

/-- The manuscript's regularized dissipation `D_ε`. -/
def D3Eps (ε : ℝ) (v : Space → Space) : ℝ := ∫ x, D3densityEps ε v x

/-- The density of the manuscript's regularized pressure work `P_ε`. -/
def P3densityEps (ε : ℝ) (q : Space → ℝ) (v : Space → Space) (x : Space) : ℝ :=
  q x * ⟪v x, gradTranspose v x⟫ / rEps ε (v x)

/-- The manuscript's regularized pressure work `P_ε`. -/
def P3Eps (ε : ℝ) (q : Space → ℝ) (v : Space → Space) : ℝ := ∫ x, P3densityEps ε q v x

/-! ## Continuity of the integrands -/

/-- The transposed Jacobian of a `C¹` field is continuous. -/
theorem continuous_gradTranspose (hv : ContDiff ℝ 1 v) : Continuous (gradTranspose v) := by
  unfold gradTranspose
  exact ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space) (F := Space)).continuous.comp
    (hv.continuous_fderiv one_ne_zero)).clm_apply hv.continuous

/-- The regularized speed of a continuous field is continuous. -/
theorem continuous_rEps_comp (hv : Continuous v) : Continuous fun x => rEps ε (v x) :=
  (((hv.norm.pow 2).add continuous_const)).sqrt

/-- The regularized time primitive of a continuous field is continuous. -/
theorem continuous_HEps_comp (hε : 0 ≤ ε) (hv : Continuous v) :
    Continuous fun x => HEps ε (v x) := by
  have h : Continuous fun x => (rEps ε (v x) ^ 3 - Real.sqrt ε ^ 3) / 3 :=
    (((continuous_rEps_comp hv).pow 3).sub continuous_const).div_const 3
  exact h.congr fun x => (HEps_eq_cube hε (v x)).symm

/-- The regularized dissipation density of a `C¹` field is continuous. -/
theorem continuous_D3densityEps (hε : 0 < ε) (hv : ContDiff ℝ 1 v) :
    Continuous (D3densityEps ε v) := by
  have hr : Continuous fun x => rEps ε (v x) := continuous_rEps_comp hv.continuous
  have hne : ∀ x, rEps ε (v x) ≠ 0 := fun x => (rEps_pos hε (v x)).ne'
  exact (hr.mul (IBP.continuous_enstrophyDensity hv)).add
    (((continuous_gradTranspose hv).norm.pow 2).div hr hne)

/-- The regularized pressure-work density of a `C¹` field is continuous. -/
theorem continuous_P3densityEps (hε : 0 < ε) (hq : Continuous q) (hv : ContDiff ℝ 1 v) :
    Continuous (P3densityEps ε q v) := by
  have hr : Continuous fun x => rEps ε (v x) := continuous_rEps_comp hv.continuous
  have hne : ∀ x, rEps ε (v x) ≠ 0 := fun x => (rEps_pos hε (v x)).ne'
  exact ((hq.mul (hv.continuous.inner (continuous_gradTranspose hv))).div hr hne)

/-- The `D₃` density of a `C¹` field is continuous away from the zero set, and
measurable everywhere: it is a quotient of continuous functions with the
`a / 0 = 0` convention. -/
theorem measurable_D3density (hv : ContDiff ℝ 1 v) : Measurable (D3density v) :=
  ((hv.continuous.norm.mul (IBP.continuous_enstrophyDensity hv)).measurable).add
    ((((continuous_gradTranspose hv).norm.pow 2).measurable).div hv.continuous.norm.measurable)

/-- The `P₃` density of a `C¹` field against a continuous weight is measurable. -/
theorem measurable_P3density (hq : Continuous q) (hv : ContDiff ℝ 1 v) :
    Measurable (P3density q v) :=
  (((hq.mul (hv.continuous.inner (continuous_gradTranspose hv)))).measurable).div
    hv.continuous.norm.measurable


/-! ## The dominating functions of the manuscript's Steps 5 and 6 -/

/-- Manuscript `prop:pressure`, Step 5(b): the regularized form of the
Cauchy–Schwarz bound `|(∇v)ᵀv|²/r_ε ≤ |v| ‖∇v‖_F²`.  It is
`NavierFormal.norm_gradTranspose_sq_div_le` with `|v|` replaced by the strictly
positive `r_ε(v)` in the denominator, so that no zero-set convention is needed. -/
theorem norm_gradTranspose_sq_div_rEps_le (hε : 0 < ε) (v : Space → Space) (x : Space) :
    ‖gradTranspose v x‖ ^ 2 / rEps ε (v x) ≤ ‖v x‖ * frobeniusNormSq (fderiv ℝ v x) := by
  have hr : 0 < rEps ε (v x) := rEps_pos hε (v x)
  rw [div_le_iff₀ hr]
  have hb : ‖gradTranspose v x‖ ≤ frobeniusNorm (fderiv ℝ v x) * ‖v x‖ :=
    norm_gradTranspose_le v x
  have hsq : ‖gradTranspose v x‖ ^ 2 ≤ frobeniusNormSq (fderiv ℝ v x) * ‖v x‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rwa [mul_pow, frobeniusNorm_sq] at h
  have hnr : ‖v x‖ ^ 2 ≤ ‖v x‖ * rEps ε (v x) := by
    nlinarith [norm_le_rEps hε.le (v x), norm_nonneg (v x)]
  nlinarith [frobeniusNormSq_nonneg (fderiv ℝ v x)]

/-- Manuscript `prop:pressure`, Step 5(b): the regularized dissipation density is
nonnegative. -/
theorem D3densityEps_nonneg (hε : 0 < ε) (v : Space → Space) (x : Space) :
    0 ≤ D3densityEps ε v x :=
  add_nonneg (mul_nonneg (rEps_pos hε (v x)).le (frobeniusNormSq_nonneg _))
    (div_nonneg (sq_nonneg _) (rEps_pos hε (v x)).le)

/-- Manuscript `prop:pressure`, Step 5(b): the dominating function
`g = (2|v| + 1)‖∇v‖_F²` of the regularized dissipation density, uniform in
`ε ∈ (0,1]`.  This is the majorant that carries both limits `R → ∞` and
`ε ↓ 0` of the manuscript's proof. -/
theorem D3densityEps_le (hε : 0 < ε) (hε1 : ε ≤ 1) (v : Space → Space) (x : Space) :
    D3densityEps ε v x ≤ (2 * ‖v x‖ + 1) * enstrophyDensity v x := by
  have hs : Real.sqrt ε ≤ 1 := by
    have h := Real.sqrt_le_sqrt hε1
    rwa [Real.sqrt_one] at h
  have h1 : rEps ε (v x) * frobeniusNormSq (fderiv ℝ v x)
      ≤ (‖v x‖ + 1) * frobeniusNormSq (fderiv ℝ v x) := by
    refine mul_le_mul_of_nonneg_right ?_ (frobeniusNormSq_nonneg _)
    exact (rEps_le_norm_add_sqrt hε.le (v x)).trans (by linarith)
  have h2 := norm_gradTranspose_sq_div_rEps_le hε v x
  simp only [D3densityEps, enstrophyDensity]
  nlinarith

/-- Manuscript `prop:pressure`, Step 5(c): the dominating function
`h = |q| ‖∇v‖_F |v|` of the regularized pressure-work density, uniform in
`ε > 0`. -/
theorem abs_P3densityEps_le (hε : 0 < ε) (q : Space → ℝ) (v : Space → Space) (x : Space) :
    |P3densityEps ε q v x| ≤ |q x| * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) := by
  have hr : 0 < rEps ε (v x) := rEps_pos hε (v x)
  rw [P3densityEps, abs_div, abs_of_pos hr, abs_mul, div_le_iff₀ hr]
  have hcs : |⟪v x, gradTranspose v x⟫| ≤ ‖v x‖ * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_gradTranspose_le v x) (norm_nonneg _))
  have hF : 0 ≤ frobeniusNorm (fderiv ℝ v x) := frobeniusNorm_nonneg _
  have hq : 0 ≤ |q x| := abs_nonneg _
  have hc : 0 ≤ |q x| * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) := by positivity
  calc |q x| * |⟪v x, gradTranspose v x⟫|
      ≤ |q x| * (‖v x‖ * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖)) :=
        mul_le_mul_of_nonneg_left hcs hq
    _ = |q x| * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) * ‖v x‖ := by ring
    _ ≤ |q x| * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) * rEps ε (v x) :=
        mul_le_mul_of_nonneg_left (norm_le_rEps hε.le (v x)) hc

/-! ## The pointwise limits `ε ↓ 0` of the manuscript's Step 6 -/

/-- Manuscript `prop:pressure`, Step 6(b): the regularized dissipation density
converges pointwise to the `D₃` density as `ε ↓ 0`.  On the zero set of `v` both
sides are `0`, which is the manuscript's convention "integrand `= 0` where
`u = 0`". -/
theorem tendsto_D3densityEps (v : Space → Space) (x : Space) :
    Tendsto (fun ε : ℝ => D3densityEps ε v x) (𝓝[>] 0) (𝓝 (D3density v x)) := by
  have h1 : Tendsto (fun ε : ℝ => rEps ε (v x) * frobeniusNormSq (fderiv ℝ v x))
      (𝓝[>] 0) (𝓝 (‖v x‖ * frobeniusNormSq (fderiv ℝ v x))) :=
    (tendsto_rEps (v x)).mul_const _
  have h2 : Tendsto (fun ε : ℝ => ‖gradTranspose v x‖ ^ 2 / rEps ε (v x))
      (𝓝[>] 0) (𝓝 (‖gradTranspose v x‖ ^ 2 / ‖v x‖)) := by
    by_cases hx : v x = 0
    · have hg : gradTranspose v x = 0 := by simp [gradTranspose, hx]
      simp [hg]
    · exact tendsto_const_nhds.div (tendsto_rEps (v x)) (norm_ne_zero_iff.mpr hx)
  exact h1.add h2

/-- Manuscript `prop:pressure`, Step 6(c): the regularized pressure-work density
converges pointwise to the `P₃` density as `ε ↓ 0`, with both sides `0` on the
zero set of `v`. -/
theorem tendsto_P3densityEps (q : Space → ℝ) (v : Space → Space) (x : Space) :
    Tendsto (fun ε : ℝ => P3densityEps ε q v x) (𝓝[>] 0) (𝓝 (P3density q v x)) := by
  by_cases hx : v x = 0
  · have hg : gradTranspose v x = 0 := by simp [gradTranspose, hx]
    simp [P3densityEps, P3density, hg, hx]
  · exact tendsto_const_nhds.div (tendsto_rEps (v x)) (norm_ne_zero_iff.mpr hx)

/-! ## The dominated-convergence limits of the manuscript's Step 6

These are the three limits `ε ↓ 0` of the manuscript's Step 6, at a fixed time.
Each is Mathlib's `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
along the filter `𝓝[>] 0`, with the majorant of Step 5 and the pointwise limit
proved above.  The manuscript takes the limit along the sequence `ε = 1/n`; the
filter form here is strictly stronger and specializes to it. -/

/-- The regularization parameter is eventually in `(0,1]` along `ε ↓ 0`; this is
the range on which the manuscript's majorants are uniform. -/
theorem eventually_mem_Ioc_one : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε ∧ ε ≤ 1 := by
  have h : ∀ᶠ ε : ℝ in 𝓝 (0:ℝ), ε < 1 := Iio_mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin, h.filter_mono nhdsWithin_le_nhds] with ε h1 h2
  exact ⟨h1, h2.le⟩

/-- **Manuscript `prop:pressure`, Step 6(a).**  `∫ H_ε(v) → ⅓∫|v|³ = ⅓X` as
`ε ↓ 0`, by dominated convergence with the `ε`-independent majorant
`2(|v|² + |v|³)` of `NavierFormal.abs_HEps_le_two`.  The hypothesis is the
manuscript's `(R2)` at a fixed time: `v ∈ L² ∩ L³`. -/
theorem tendsto_HEpsIntegral (hv : Continuous v)
    (hint : Integrable (fun x => 2 * (‖v x‖ ^ 2 + ‖v x‖ ^ 3)) volume) :
    Tendsto (fun ε : ℝ => HEpsIntegral ε v) (𝓝[>] 0) (𝓝 (X3Real v / 3)) := by
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      AEStronglyMeasurable (fun x => HEps ε (v x)) (volume : Measure Space) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (continuous_HEps_comp (le_of_lt hε) hv).aestronglyMeasurable
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ x ∂(volume : Measure Space),
      ‖HEps ε (v x)‖ ≤ 2 * (‖v x‖ ^ 2 + ‖v x‖ ^ 3) := by
    filter_upwards [eventually_mem_Ioc_one] with ε hε
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_HEps_le_two hε.1.le hε.2 (v x)
  have hlim : ∀ᵐ x ∂(volume : Measure Space),
      Tendsto (fun ε : ℝ => HEps ε (v x)) (𝓝[>] 0) (𝓝 (‖v x‖ ^ 3 / 3)) :=
    Filter.Eventually.of_forall fun x => tendsto_HEps (v x)
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure Space)) (l := 𝓝[>] (0:ℝ))
    (fun x => 2 * (‖v x‖ ^ 2 + ‖v x‖ ^ 3)) hmeas hb hint hlim
  simpa [HEpsIntegral, X3Real, integral_div] using h

/-- **Manuscript `prop:pressure`, Step 6(b).**  `D_ε → D₃` as `ε ↓ 0`, by
dominated convergence with the `ε`-independent majorant
`g = (2|v| + 1)‖∇v‖_F²`.  The hypothesis is the manuscript's `(R2)` at a fixed
time, in the form in which Step 5(b) uses it: `(2|v| + 1)|∇v|² ∈ L¹`. -/
theorem tendsto_D3Eps (hv : ContDiff ℝ 1 v)
    (hint : Integrable (fun x => (2 * ‖v x‖ + 1) * enstrophyDensity v x) volume) :
    Tendsto (fun ε : ℝ => D3Eps ε v) (𝓝[>] 0) (𝓝 (D3 v)) := by
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      AEStronglyMeasurable (D3densityEps ε v) (volume : Measure Space) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (continuous_D3densityEps hε hv).aestronglyMeasurable
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ x ∂(volume : Measure Space),
      ‖D3densityEps ε v x‖ ≤ (2 * ‖v x‖ + 1) * enstrophyDensity v x := by
    filter_upwards [eventually_mem_Ioc_one] with ε hε
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (D3densityEps_nonneg hε.1 v x)]
    exact D3densityEps_le hε.1 hε.2 v x
  have hlim : ∀ᵐ x ∂(volume : Measure Space),
      Tendsto (fun ε : ℝ => D3densityEps ε v x) (𝓝[>] 0) (𝓝 (D3density v x)) :=
    Filter.Eventually.of_forall fun x => tendsto_D3densityEps v x
  exact tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure Space)) (l := 𝓝[>] (0:ℝ))
    (fun x => (2 * ‖v x‖ + 1) * enstrophyDensity v x) hmeas hb hint hlim

/-- **Manuscript `prop:pressure`, Step 6(c).**  `P_ε → P₃` as `ε ↓ 0`, by
dominated convergence with the `ε`-independent majorant `h = |q| |v| ‖∇v‖_F`.
The hypothesis is the manuscript's `(R2)` at a fixed time, in the form in which
Step 5(c) uses it: `|q| |v| |∇v| ∈ L¹`. -/
theorem tendsto_P3Eps (hq : Continuous q) (hv : ContDiff ℝ 1 v)
    (hint : Integrable (fun x => |q x| * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖)) volume) :
    Tendsto (fun ε : ℝ => P3Eps ε q v) (𝓝[>] 0) (𝓝 (P3 q v)) := by
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      AEStronglyMeasurable (P3densityEps ε q v) (volume : Measure Space) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (continuous_P3densityEps hε hq hv).aestronglyMeasurable
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ x ∂(volume : Measure Space),
      ‖P3densityEps ε q v x‖ ≤ |q x| * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_P3densityEps_le hε q v x
  have hlim : ∀ᵐ x ∂(volume : Measure Space),
      Tendsto (fun ε : ℝ => P3densityEps ε q v x) (𝓝[>] 0) (𝓝 (P3density q v x)) :=
    Filter.Eventually.of_forall fun x => tendsto_P3densityEps q v x
  exact tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure Space)) (l := 𝓝[>] (0:ℝ))
    (fun x => |q x| * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖)) hmeas hb hint hlim

/-! ## Part (iv): the null integral of `W(u,∇u)` and gauge invariance of `P₃`

The manuscript's Step 7.  The tested field is `ρ_ε u` with
`ρ_ε = r_ε(u) - √ε`, whose divergence is the regularized `P₃` integrand with
unit weight.  Where the manuscript multiplies by a cutoff `χ_R` and lets
`R → ∞`, the Lean proof uses Mathlib's boundary-free divergence theorem
(`NavierFormal.IBP.integral_divergence_eq_zero`) directly: it needs no cutoff,
only the integrability of `ρ_ε u` and of its Jacobian, which the manuscript's
majorants `ρ_ε|u| ≤ |u|²` and `|∇(ρ_ε u)| ≤ 2|u||∇u|` supply. -/

/-- The manuscript's `W(u,∇u) = u·∇|u|`, written through the transposed
Jacobian as `⟪u, (∇u)ᵀu⟫/|u|` (amendment A2), with the value `0` where `u = 0`.
It is the `P₃` integrand with unit weight. -/
def Wdensity (v : Space → Space) (x : Space) : ℝ := ⟪v x, gradTranspose v x⟫ / ‖v x‖

/-- `W` is the `P₃` density with unit weight. -/
theorem P3density_one (v : Space → Space) (x : Space) :
    P3density (fun _ => (1 : ℝ)) v x = Wdensity v x := by
  simp [P3density, Wdensity]

/-- The `P₃` density factors through `W`: `P₃ density = q · W`. -/
theorem P3density_eq_mul_Wdensity (q : Space → ℝ) (v : Space → Space) (x : Space) :
    P3density q v x = q x * Wdensity v x := by
  rw [P3density_eq_mul_div, Wdensity]

/-- Manuscript `prop:pressure`, Step 7: `0 ≤ ρ_ε(a) = r_ε(a) - √ε ≤ |a|`, so
that `ρ_ε |a| ≤ |a|²`.  This is Lemma `lem:reg-calculus`(iv). -/
theorem rhoEps_nonneg_le (hε : 0 ≤ ε) (a : Space) :
    0 ≤ rEps ε a - Real.sqrt ε ∧ rEps ε a - Real.sqrt ε ≤ ‖a‖ := by
  refine ⟨?_, by linarith [rEps_le_norm_add_sqrt hε a]⟩
  have h : Real.sqrt ε ≤ Real.sqrt (‖a‖ ^ 2 + ε) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖a‖])
  simpa [rEps] using h

/-- Manuscript `prop:pressure`, Step 7: the tested field `ρ_ε u` of the
manuscript is `C¹` when `u` is. -/
theorem contDiff_rhoEps_smul (hε : 0 < ε) {u : Space → Space} (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 fun y => (rEps ε (u y) - Real.sqrt ε) • u y := by
  have hsq : ContDiff ℝ 1 fun y => ‖u y‖ ^ 2 + ε := (hu.norm_sq ℝ).add contDiff_const
  have hr : ContDiff ℝ 1 fun y => rEps ε (u y) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hsq.contDiffAt).sqrt (by positivity)
  exact (hr.sub contDiff_const).smul hu

/-- Manuscript `prop:pressure`, Step 7: the divergence of the tested field
`ρ_ε u`, `div(ρ_ε u) = ⟪(∇u)ᵀu, u⟫/r_ε + ρ_ε (∇·u)`.  Since `∇ρ_ε = ∇r_ε`, this
is the identity `NavierFormal.divergence_rEps_smul_add` with the constant
`√ε` subtracted from the weight. -/
theorem divergence_rhoEps_smul_add (hε : 0 < ε) {u : Space → Space} {x : Space}
    (hu : DifferentiableAt ℝ u x) :
    divergence (fun y => (rEps ε (u y) - Real.sqrt ε) • u y) x
      = ⟪gradTranspose u x, u x⟫ / rEps ε (u x)
        + (rEps ε (u x) - Real.sqrt ε) * divergence u x := by
  have hρ : HasFDerivAt (fun y => rEps ε (u y) - Real.sqrt ε)
      ((rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp (fderiv ℝ u x))) x :=
    (hasFDerivAt_rEps hε hu.hasFDerivAt).sub_const _
  have hF : HasFDerivAt (fun y => (rEps ε (u y) - Real.sqrt ε) • u y)
      ((rEps ε (u x) - Real.sqrt ε) • fderiv ℝ u x
        + ((rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp (fderiv ℝ u x))).smulRight (u x)) x :=
    hρ.smul hu.hasFDerivAt
  have hfd := hF.fderiv
  have hterm : ∀ i : Fin 3,
      ⟪e i, fderiv ℝ (fun y => (rEps ε (u y) - Real.sqrt ε) • u y) x (e i)⟫
        = (u x) i * ⟪u x, fderiv ℝ u x (e i)⟫ / rEps ε (u x)
          + (rEps ε (u x) - Real.sqrt ε) * ⟪e i, fderiv ℝ u x (e i)⟫ := by
    intro i
    rw [hfd]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_add_right,
      real_inner_smul_right, inner_e, smul_eq_mul]
    ring
  rw [divergence, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    ← Finset.sum_div, sum_component_inner_fderiv, ← Finset.mul_sum, divergence]

/-- Manuscript `prop:pressure`, Step 7: for a solenoidal field the divergence of
the tested field is exactly the regularized `P₃` integrand with unit weight,
`div(ρ_ε u) = ⟪u, (∇u)ᵀu⟫/r_ε`. -/
theorem divergence_rhoEps_smul (hε : 0 < ε) {u : Space → Space} {x : Space}
    (hu : DifferentiableAt ℝ u x) (hdiv : divergence u x = 0) :
    divergence (fun y => (rEps ε (u y) - Real.sqrt ε) • u y) x
      = P3densityEps ε (fun _ => (1 : ℝ)) u x := by
  rw [divergence_rhoEps_smul_add hε hu, hdiv, mul_zero, add_zero, P3densityEps,
    real_inner_comm]
  simp

/-- **Manuscript `prop:pressure`, Step 7, the regularized identity.**  For every
`ε > 0` and every solenoidal `C¹` field with `|u|² ∈ L¹` and `|u||∇u| ∈ L¹`,

`∫ ⟪u, (∇u)ᵀu⟫ / r_ε(u) = 0`.

This is the manuscript's `∫ u·(∇u)ᵀu / r_ε dx = 0`, obtained from the
boundary-free divergence theorem applied to `ρ_ε u = (r_ε(u) - √ε) u`. -/
theorem P3Eps_one_eq_zero (hε : 0 < ε) {u : Space → Space} (hu : ContDiff ℝ 1 u)
    (hdiv : ∀ x, divergence u x = 0)
    (hu2 : Integrable (fun x => ‖u x‖ ^ 2) volume)
    (hu1 : Integrable (fun x => ‖u x‖ * ‖fderiv ℝ u x‖) volume) :
    P3Eps ε (fun _ => (1 : ℝ)) u = 0 := by
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hFcd : ContDiff ℝ 1 fun y => (rEps ε (u y) - Real.sqrt ε) • u y :=
    contDiff_rhoEps_smul hε hu
  have hFd : Differentiable ℝ fun y => (rEps ε (u y) - Real.sqrt ε) • u y :=
    hFcd.differentiable one_ne_zero
  -- `‖ρ_ε u‖ ≤ |u|²`
  have hFi : Integrable (fun y => (rEps ε (u y) - Real.sqrt ε) • u y) volume := by
    refine hu2.mono' hFcd.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h := rhoEps_nonneg_le hε.le (u x)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h.1, sq]
    exact mul_le_mul_of_nonneg_right h.2 (norm_nonneg _)
  -- `‖∇(ρ_ε u)‖ ≤ 2 |u| |∇u|`
  have hdFi : Integrable
      (fun x => fderiv ℝ (fun y => (rEps ε (u y) - Real.sqrt ε) • u y) x) volume := by
    refine (hu1.const_mul 2).mono'
      ((hFcd.continuous_fderiv one_ne_zero).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have hρ : HasFDerivAt (fun y => rEps ε (u y) - Real.sqrt ε)
        ((rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp (fderiv ℝ u x))) x :=
      (hasFDerivAt_rEps hε (hud x).hasFDerivAt).sub_const _
    have hF : HasFDerivAt (fun y => (rEps ε (u y) - Real.sqrt ε) • u y)
        ((rEps ε (u x) - Real.sqrt ε) • fderiv ℝ u x
          + ((rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp (fderiv ℝ u x))).smulRight (u x)) x :=
      hρ.smul (hud x).hasFDerivAt
    have hb := rhoEps_nonneg_le hε.le (u x)
    have hop := opNorm_rEps_fderiv_le (X := Space) hε (u x) (fderiv ℝ u x)
    rw [hF.fderiv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, Real.norm_eq_abs,
      abs_of_nonneg hb.1]
    have h1 : (rEps ε (u x) - Real.sqrt ε) * ‖fderiv ℝ u x‖ ≤ ‖u x‖ * ‖fderiv ℝ u x‖ :=
      mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
    have h2 : ‖(rEps ε (u x))⁻¹ • ((innerSL ℝ (u x)).comp (fderiv ℝ u x))‖ * ‖u x‖
        ≤ ‖fderiv ℝ u x‖ * ‖u x‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    nlinarith
  have h0 : ∫ x, divergence (fun y => (rEps ε (u y) - Real.sqrt ε) • u y) x = 0 :=
    IBP.integral_divergence_eq_zero hFd hFi hdFi
  rw [P3Eps, ← h0]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (divergence_rhoEps_smul hε (hud x) (hdiv x)).symm)

/-- **Manuscript `prop:pressure`(iv).**  `∫ W(u,∇u) = 0` for a solenoidal `C¹`
field with `|u|² ∈ L¹` and `|u| |∇u|_F ∈ L¹`: the regularized identity
`P3Eps_one_eq_zero` holds for every `ε > 0`, and the dominated-convergence limit
`ε ↓ 0` of Step 6(c) transports it to the limit integrand.  Together with
`NavierFormal.P3_add_const` this is the manuscript's statement that `P₃` is
unchanged when the pressure is shifted by a function of time alone. -/
theorem integral_Wdensity_eq_zero {u : Space → Space} (hu : ContDiff ℝ 1 u)
    (hdiv : ∀ x, divergence u x = 0)
    (hu2 : Integrable (fun x => ‖u x‖ ^ 2) volume)
    (huF : Integrable (fun x => frobeniusNorm (fderiv ℝ u x) * ‖u x‖) volume) :
    ∫ x, Wdensity u x = 0 := by
  have hu1 : Integrable (fun x => ‖u x‖ * ‖fderiv ℝ u x‖) volume := by
    refine huF.mono' (hu.continuous.norm.mul
      ((hu.continuous_fderiv one_ne_zero).norm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖u x‖ * ‖fderiv ℝ u x‖ ≤ ‖u x‖ * frobeniusNorm (fderiv ℝ u x) :=
          mul_le_mul_of_nonneg_left (opNorm_le_frobeniusNorm _) (norm_nonneg _)
      _ = frobeniusNorm (fderiv ℝ u x) * ‖u x‖ := mul_comm _ _
  have hint : Integrable
      (fun x => |(1 : ℝ)| * (frobeniusNorm (fderiv ℝ u x) * ‖u x‖)) volume := by
    simpa using huF
  have hlim := tendsto_P3Eps (q := fun _ => (1 : ℝ)) continuous_const hu hint
  have hzero : (fun ε : ℝ => P3Eps ε (fun _ => (1 : ℝ)) u) =ᶠ[𝓝[>] (0:ℝ)]
      fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact P3Eps_one_eq_zero hε hu hdiv hu2 hu1
  have hP3 : P3 (fun _ => (1 : ℝ)) u = 0 :=
    tendsto_nhds_unique (hlim.congr' hzero) tendsto_const_nhds
  rw [← hP3, P3]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (P3density_one u x).symm)

/-- **Manuscript `prop:pressure`(iv), gauge invariance.**  `P₃` is unchanged when
the pressure is shifted by a constant (in the manuscript, by any function `c(t)`
of time alone): `P₃(q + c, u) = P₃(q, u)` whenever `∫ W = 0` and both integrands
are integrable. -/
theorem P3_add_const {u : Space → Space} (c : ℝ) (q : Space → ℝ)
    (hW : ∫ x, Wdensity u x = 0)
    (hqW : Integrable (fun x => q x * Wdensity u x) volume)
    (hWi : Integrable (Wdensity u) volume) :
    P3 (fun x => q x + c) u = P3 q u := by
  have hpt : ∀ x, P3density (fun x => q x + c) u x
      = P3density q u x + c * Wdensity u x := by
    intro x
    rw [P3density_eq_mul_Wdensity, P3density_eq_mul_Wdensity]
    ring
  rw [P3, P3, integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_add (hqW.congr (Filter.Eventually.of_forall fun x =>
      (P3density_eq_mul_Wdensity q u x).symm)) (hWi.const_mul c),
    integral_const_mul, hW, mul_zero, add_zero]

end

end NavierFormal
