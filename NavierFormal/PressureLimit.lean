import NavierFormal.Pressure

/-!
# The `ε ↓ 0` limit of the pressure route (manuscript `prop:pressure`)

This module was assigned the recorded gap of `docs/verification-status.md` for
Proposition `prop:pressure`: "the `ε ↓ 0` limit to `P3density`/`D3density` and
everything integral remain open" (see the entries for
`NavierFormal.fderiv_rEps_apply_self` and
`NavierFormal.divergence_rEps_smul`/`inner_gradTranspose_self_div_rEps_eq`).

**Finding.** By the time this lane ran, `NavierFormal/Pressure.lean` (owned by
another lane, already committed at `aad2b0e`) had independently discharged
exactly this gap: it already contains

* `NavierFormal.D3densityEps`, `NavierFormal.P3densityEps` (the ε-regularized
  densities, definitionally the ones requested here),
* `NavierFormal.tendsto_D3densityEps`, `NavierFormal.tendsto_P3densityEps`
  (the pointwise limits `ε ↓ 0`, including the `v x = 0` case by `by_cases`),
* `NavierFormal.D3densityEps_le`, `NavierFormal.abs_P3densityEps_le`,
  `NavierFormal.abs_HEps_le_two` (the `ε`-uniform majorants on `0 < ε ≤ 1`),
* `NavierFormal.tendsto_HEpsIntegral`, `NavierFormal.tendsto_D3Eps`,
  `NavierFormal.tendsto_P3Eps` (the three dominated-convergence integral
  limits `eq:eps-identity` needs, via
  `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` along
  `𝓝[>] 0`).

so `docs/verification-status.md`'s "not proved" remark for these two rows is
stale as of this state of the repository (a fact for the controller to
reconcile there; this lane does not own that file). Since this lane owns only
this file, it does not restate that proof; restating it under new names would
duplicate, not extend, the existing development. What this file adds on top:

* the exact declaration names requested by the lane brief
  (`tendsto_P3density_eps`, `tendsto_D3density_eps`, and the three
  `tendsto_integral_*` limits), as thin definitional aliases of the
  declarations above, so that the gap closure is visible under the names the
  manuscript-tracking brief anticipated;
* a genuinely new, sharper-than-`Pressure.lean` uniform majorant for `P₃`:
  `NavierFormal.abs_P3densityEps_le_opNorm` bounds `|P3densityEps|` by
  `|q x| * ‖v x‖ * ‖fderiv ℝ v x‖` (the *operator* norm, as requested by the
  lane brief), sharper than `Pressure.lean`'s `abs_P3densityEps_le`, which
  uses the Frobenius norm `frobeniusNorm (fderiv ℝ v x) ≥ ‖fderiv ℝ v x‖`. The
  `D₃` request ("`(‖v x‖ + 1) * frobeniusNormSq (fderiv ℝ v x)
  + ‖v x‖ * ‖fderiv ℝ v x‖ ^ 2` or a similar clean bound") is already met by
  `Pressure.lean`'s `D3densityEps_le` (the "similar clean bound" the brief
  explicitly allows for), so no separate `D₃` majorant is added here.

Nothing in this file is a theorem about the Millennium problem.
-/

namespace NavierFormal

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

variable {ε : ℝ} {q : Space → ℝ} {v : Space → Space} {x : Space}

/-! ## A sharper, operator-norm uniform majorant for `P₃` -/

/-- Sharper form of `NavierFormal.norm_gradTranspose_le` for Proposition
`prop:pressure`: the transposed Jacobian is bounded by the *operator* norm of
the Jacobian, `‖(∇v)ᵀv‖ ≤ ‖∇v‖ ‖v‖`, rather than by the (larger) Frobenius
norm. This is immediate from `gradTranspose` being an adjoint applied to `v x`,
without going through the Frobenius comparison
`NavierFormal.opNorm_le_frobeniusNorm` that `norm_gradTranspose_le` uses. -/
theorem norm_gradTranspose_le_opNorm (v : Space → Space) (x : Space) :
    ‖gradTranspose v x‖ ≤ ‖fderiv ℝ v x‖ * ‖v x‖ := by
  have hadj : ‖ContinuousLinearMap.adjoint (fderiv ℝ v x)‖ = ‖fderiv ℝ v x‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  calc ‖gradTranspose v x‖
      ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ v x)‖ * ‖v x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ v x‖ * ‖v x‖ := by rw [hadj]

/-- Manuscript `prop:pressure`, Step 5(c), operator-norm form: the
`ε`-uniform majorant `|P₃ density_ε| ≤ |q| ‖v‖ ‖∇v‖` for the regularized
pressure-work density, with `‖∇v‖` the operator norm rather than the
Frobenius norm of `NavierFormal.abs_P3densityEps_le`. This is the dominating
function requested for the `ε ↓ 0` limit of `∫ P3densityEps`. -/
theorem abs_P3densityEps_le_opNorm (hε : 0 < ε) (q : Space → ℝ) (v : Space → Space)
    (x : Space) : |P3densityEps ε q v x| ≤ |q x| * ‖v x‖ * ‖fderiv ℝ v x‖ := by
  have hr : 0 < rEps ε (v x) := rEps_pos hε (v x)
  rw [P3densityEps, abs_div, abs_of_pos hr, abs_mul, div_le_iff₀ hr]
  have hcs : |⟪v x, gradTranspose v x⟫| ≤ ‖v x‖ * (‖fderiv ℝ v x‖ * ‖v x‖) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_gradTranspose_le_opNorm v x) (norm_nonneg _))
  have hq : 0 ≤ |q x| := abs_nonneg _
  calc |q x| * |⟪v x, gradTranspose v x⟫|
      ≤ |q x| * (‖v x‖ * (‖fderiv ℝ v x‖ * ‖v x‖)) := mul_le_mul_of_nonneg_left hcs hq
    _ = |q x| * ‖v x‖ * ‖fderiv ℝ v x‖ * ‖v x‖ := by ring
    _ ≤ |q x| * ‖v x‖ * ‖fderiv ℝ v x‖ * rEps ε (v x) :=
        mul_le_mul_of_nonneg_left (norm_le_rEps hε.le (v x)) (by positivity)

/-! ## The pointwise limits `ε ↓ 0`, under the names requested for this gap -/

/-- Manuscript `prop:pressure`: the regularized `P₃` integrand converges to
`P3density` as `ε ↓ 0`, including at `v x = 0` where both sides vanish (there
`gradTranspose v x = 0` by definition of `gradTranspose` as an adjoint applied
to `v x = 0`). Definitional alias of `NavierFormal.tendsto_P3densityEps`
(`Pressure.lean`), stated at the literal expression named by the lane brief. -/
theorem tendsto_P3density_eps (q : Space → ℝ) (v : Space → Space) (x : Space) :
    Tendsto (fun ε : ℝ => q x * ⟪v x, gradTranspose v x⟫ / rEps ε (v x)) (𝓝[>] 0)
      (𝓝 (P3density q v x)) :=
  tendsto_P3densityEps q v x

/-- Manuscript `prop:pressure`: the regularized `D₃` integrand converges to
`D3density` as `ε ↓ 0`, including at `v x = 0`. Definitional alias of
`NavierFormal.tendsto_D3densityEps` (`Pressure.lean`), stated at the literal
expression named by the lane brief. -/
theorem tendsto_D3density_eps (v : Space → Space) (x : Space) :
    Tendsto (fun ε : ℝ =>
        rEps ε (v x) * frobeniusNormSq (fderiv ℝ v x) + ‖gradTranspose v x‖ ^ 2 / rEps ε (v x))
      (𝓝[>] 0) (𝓝 (D3density v x)) :=
  tendsto_D3densityEps v x

/-! ## The dominated-convergence integral limits, under the names requested for
this gap -/

/-- Manuscript `prop:pressure`, `eq:eps-identity`: `∫ H_ε(v) → ⅓ ∫ ‖v‖³` as
`ε ↓ 0`. Definitional alias of `NavierFormal.tendsto_HEpsIntegral`
(`Pressure.lean`), unfolded from `HEpsIntegral` to the literal integral named
by the lane brief. -/
theorem tendsto_integral_HEps_eps (hv : Continuous v)
    (hint : Integrable (fun x => 2 * (‖v x‖ ^ 2 + ‖v x‖ ^ 3)) volume) :
    Tendsto (fun ε : ℝ => ∫ x, HEps ε (v x)) (𝓝[>] 0) (𝓝 (X3Real v / 3)) :=
  tendsto_HEpsIntegral hv hint

/-- Manuscript `prop:pressure`, `eq:eps-identity`: `∫ D3densityEps → D₃` as
`ε ↓ 0`. Definitional alias of `NavierFormal.tendsto_D3Eps` (`Pressure.lean`),
unfolded from `D3Eps` to the literal integral named by the lane brief. -/
theorem tendsto_integral_D3density_eps (hv : ContDiff ℝ 1 v)
    (hint : Integrable (fun x => (2 * ‖v x‖ + 1) * enstrophyDensity v x) volume) :
    Tendsto (fun ε : ℝ => ∫ x, D3densityEps ε v x) (𝓝[>] 0) (𝓝 (D3 v)) :=
  tendsto_D3Eps hv hint

/-- Manuscript `prop:pressure`, `eq:eps-identity`: `∫ P3densityEps → P₃` as
`ε ↓ 0`. Definitional alias of `NavierFormal.tendsto_P3Eps` (`Pressure.lean`),
unfolded from `P3Eps` to the literal integral named by the lane brief. The
hypothesis matches `Pressure.lean`'s Frobenius-norm majorant; the sharper
`abs_P3densityEps_le_opNorm` above gives the same conclusion under the
(weaker) operator-norm integrability hypothesis
`Integrable (fun x => |q x| * (‖v x‖ * ‖fderiv ℝ v x‖)) volume`, but proving
that variant would duplicate `NavierFormal.tendsto_P3Eps`'s
dominated-convergence argument rather than reuse it, so it is not restated
here. -/
theorem tendsto_integral_P3density_eps (hq : Continuous q) (hv : ContDiff ℝ 1 v)
    (hint : Integrable (fun x => |q x| * (frobeniusNorm (fderiv ℝ v x) * ‖v x‖)) volume) :
    Tendsto (fun ε : ℝ => ∫ x, P3densityEps ε q v x) (𝓝[>] 0) (𝓝 (P3 q v)) :=
  tendsto_P3Eps hq hv hint

end

end NavierFormal
