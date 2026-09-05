# Verification status

Reader-facing status has three values:

- **Paper only:** the manuscript contains the proof, but Phase I is open.
- **Phase I complete:** Lean reaches a checked literature theorem, but that
  theorem has not yet been proved from Mathlib.
- **Phase II complete:** Lean proves the claim from Mathlib.

Current state: CP03a and CP03b integrated. `prop:ode` and the norm-scaling
half of `prop:scaling` (plus the two scalar remarks inside its proof) are
proved from Mathlib in `NavierFormal/Ode.lean`, `NavierFormal/Scaling.lean`,
and `NavierFormal/InterpolationMismatch.lean`. The PDE half of `prop:scaling`
(that `(u_λ, p_λ)` solves the system) and estimate `eq:L4L3` are not yet in
Lean. CP03b adds the pointwise and almost-everywhere supporting lemmas of the
proof of `prop:pressure` (`NavierFormal/Regularization.lean`,
`NavierFormal/NormGradient.lean`); the proposition itself, its integral
identities, and the dominated-convergence limit remain paper only. CP03c adds
the statement surface (`NavierFormal/Calculus.lean`, `SolutionClass.lean`,
`QuotientObjects.lean`: the operators of `eq:NS`, the classical solution
class, `def:target`, `hyp:critical`, `D₃`, `P₃`, the quotient objects) and
three families of proof sentences (`IBP.lean`: boundary-free integrations by
parts; `Interpolation.lean`: Lyapunov interpolation, Sobolev without compact
support, Young; `SolutionClass.lean`: `eq:nu-normalization`). CP03d adds two
pointwise/functional bridges (`NavierFormal/DensityBridge.lean`: the `∇|u|`
form of the `D₃`, `P₃` densities and the divergence identity
`div(r_ε u) = (|u|/r_ε) u·∇|u|` of the proof of `prop:pressure`;
`NavierFormal/QuotientScaling.lean`: the critical dilation as a linear
isometry of `L³` onto itself and the invariance `𝒬(u_λ) = 𝒬(u)` of
`sec:quotient`). Every labelled
manuscript result keeps the status in the table below; the fidelity audit of
each definition is in `paper-lean-specification.md`.
`Challenge.lean` still carries only the labelled placeholder. The
machine-readable boundary is `formalization-coverage.yaml`; literature inputs
are in `literature-assumptions.yaml`.

| Manuscript label | Lean declaration | Status |
| --- | --- | --- |
| `prop:energy` | — | paper only |
| `prop:scaling` (norm identity `‖u_λ(t)‖_q = λ^{1-3/q}‖u(λ²t)‖_q`, `0 < q < ∞`) | `NavierFormal.eLpNorm_dilate`, `NavierFormal.eLpNorm_dilateSpaceTime` (definitions `NavierFormal.dilate`, `NavierFormal.dilateSpaceTime`; lemmas `NavierFormal.map_smul_volume`, `NavierFormal.rpow_dilate_factor`, `NavierFormal.eLpNorm_comp_smul`) | Phase II complete (no literature input) |
| `prop:scaling` (`L³` invariant; `‖u‖₂²` scales by `λ⁻¹`) | `NavierFormal.eLpNorm_dilate_three`, `NavierFormal.eLpNorm_dilate_two`, `NavierFormal.eLpNorm_dilate_two_sq` | Phase II complete (no literature input) |
| `prop:scaling` (proof remark: scalar `L⁴(0,T) ⊄ L^∞(0,T)`; `2/4 + 3/3 = 3/2 > 1`) | `NavierFormal.exists_memLp_four_not_memLp_top`, `NavierFormal.exists_memLp_four_eLpNorm_top_eq_top`, `NavierFormal.L4L3_supercritical` (witness `NavierFormal.scalingWitness`; lemmas `NavierFormal.aestronglyMeasurable_scalingWitness`, `NavierFormal.integrable_scalingWitness_rpow_four`, `NavierFormal.memLp_scalingWitness_four`, `NavierFormal.lt_scalingWitness`, `NavierFormal.eLpNormEssSup_scalingWitness`) | Phase II complete (no literature input) |
| `prop:scaling` (PDE half: `(u_λ, p_λ)` solves `eq:NS`; estimate `eq:L4L3`) | — | paper only |
| `prop:enstrophy` | — | paper only |
| `prop:ode` | `NavierFormal.scalar_obstruction_exists` (witness `NavierFormal.scalarObstruction`; lemmas `NavierFormal.scalarObstruction_base_pos`, `NavierFormal.scalarObstruction_pos`, `NavierFormal.hasDerivAt_scalarObstruction`, `NavierFormal.intervalIntegrable_scalarObstruction`, `NavierFormal.integrableOn_scalarObstruction`, `NavierFormal.tendsto_scalarObstruction`; proof value `∫_0^T y = √(2T/C)` as `NavierFormal.integral_scalarObstruction`) | Phase II complete (no literature input) |
| `prop:pressure` | — (supporting lemmas only; see the table below) | paper only |
| `prop:lowpressure` | — | paper only |
| `thm:continuation` | — | paper only (imports ESS/GKP) |
| `thm:conditional` | — | paper only (conditional on `hyp:critical`) |
| `sec:quotient` results | — (objects only: `NavierFormal.L3`, `gradientSubspace`, `quotientFunctional`, `IsQuotientMinimizer`, `cubicMap`, `IsSolenoidalL3`, `quotientDissipation`, `strainFlux`; see the definitions table; the sentence "cubic in amplitude and invariant under the critical spatial scaling" is a supporting lemma below) | paper only (HF17, audited) |
| `def:target` | `NavierFormal.ClayAlternativeA`, `NavierFormal.ClayAlternativeA_all` (statement only) | paper only (statement formalized; nothing proved about it) |
| `hyp:critical` | `NavierFormal.CriticalBound`, `NavierFormal.CriticalHypothesis` (statement only) | paper only (hypothesis formalized; not asserted) |
| `eq:nu-normalization` (`v_s + (v·∇)v + ∇q = Δv`, `‖v(s)‖₃ = ν⁻¹‖u(s/ν)‖₃`) | `NavierFormal.IsClassicalSolution.nuNormalization`, `NavierFormal.eLpNorm_three_nuNormalization` (lemmas `NavierFormal.convection_const_smul`, `divergence_const_smul`, `gradient_const_smul`, `contDiffOn_timeScale`, `continuousOn_timeScale`, `timeDeriv_eq_deriv`) | Phase II complete (no literature input); the clause `S_* = νT_*` is only the interval endpoint `νT`, no maximal time is defined |

## Supporting lemmas

Supporting lemmas formalize single sentences inside a manuscript proof, not a
labelled manuscript result. Their status is Phase II only for that sentence;
the manuscript result they serve keeps its own row above. The fidelity audit
for each is in `paper-lean-specification.md` once recorded there; the gaps
found at integration are listed after the table.

| Manuscript label (sentence of the proof) | Lean declaration | Status |
| --- | --- | --- |
| `prop:pressure` (`r_ε = (\|u\|²+ε)^{1/2}`, `H_ε(u) = ⅓((\|u\|²+ε)^{3/2} − ε^{3/2})`, constant `C_ε`) | `NavierFormal.rEps`, `NavierFormal.HEps`, `NavierFormal.HEpsConst` (definitions); `NavierFormal.rEps_sq`, `NavierFormal.rEps_pos`, `NavierFormal.rEps_cube`, `NavierFormal.HEps_eq_cube`, `NavierFormal.sqrt_cube_eq_rpow` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (bounds `\|u\|²/r_ε ≤ \|u\|`, `\|u\|/r_ε ≤ 1`, `\|u\| ≤ r_ε`) | `NavierFormal.norm_sq_div_rEps_le`, `NavierFormal.norm_div_rEps_le_one`, `NavierFormal.norm_le_rEps`, `NavierFormal.rEps_le_norm_add_sqrt`, `NavierFormal.rEps_mono` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (`H_ε(u) ≤ C_ε(\|u\|²+\|u\|³)`, pointwise majorant; `C_ε = 1 + √ε`) | `NavierFormal.HEps_le`, `NavierFormal.abs_HEps_le`, `NavierFormal.abs_HEps_le_two` (ε-uniform on `0 < ε ≤ 1`); sharp form `NavierFormal.HEps_le_norm_sq_mul_rEps`; `NavierFormal.HEps_nonneg` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (`H_ε` is the time primitive of `r_ε u · u_t`; chain rule for `r_ε ∘ u`) | `NavierFormal.hasFDerivAt_HEps`, `NavierFormal.hasFDerivAt_rEps`, `NavierFormal.rEps_fderiv_apply`; on `ℝ³`: `NavierFormal.hasFDerivAt_HEps_space`, `NavierFormal.hasFDerivAt_rEps_space` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (product rule for `r_ε u`, the differential whose trace is `div(r_ε u)`) | `NavierFormal.hasFDerivAt_rEps_smul`, `NavierFormal.rEps_smul_fderiv_apply`; on `ℝ³`: `NavierFormal.hasFDerivAt_rEps_smul_space` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (regularized gradient bound `\|∇ r_ε(u)\| ≤ \|∇u\|`) | `NavierFormal.opNorm_rEps_fderiv_le` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (pointwise limits `r_ε → \|u\|`, `H_ε(u) → \|u\|³/3` as `ε ↓ 0`) | `NavierFormal.tendsto_rEps`, `NavierFormal.tendsto_HEps` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (chain rule `∇\|u\| = ⟨u, ∇u⟩/\|u\|` off the zero set) | `NavierFormal.hasFDerivAt_norm_of_ne_zero`, `NavierFormal.fderiv_norm_apply_of_ne_zero` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (`\|∇\|u\|\| ≤ \|∇u\|`, pointwise where both derivatives exist) | `NavierFormal.norm_apply_le_of_hasFDerivAt_norm`, `NavierFormal.opNorm_le_of_hasFDerivAt_norm`, `NavierFormal.norm_fderiv_norm_le` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (`∇\|u\| = 0` on the zero set of `u`, Fréchet form) | `NavierFormal.hasFDerivAt_norm_eq_zero_of_eq_zero`, `NavierFormal.fderiv_norm_eq_zero_of_eq_zero` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (a.e. differentiability of `\|u\|` and a.e. `\|∇\|u\|\| ≤ \|∇u\|`, under a global Lipschitz bound; Rademacher from Mathlib) | `NavierFormal.ae_differentiableAt_norm`, `NavierFormal.ae_norm_fderiv_norm_le`, `NavierFormal.ae_norm_fderiv_norm_le_of_contDiff`; on `ℝ³`: `NavierFormal.ae_norm_fderiv_norm_le_space` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (a.e. dichotomy: chain rule off the zero set, `∇\|u\| = 0` on it; under a global Lipschitz bound) | `NavierFormal.ae_hasFDerivAt_norm`; on `ℝ³`: `NavierFormal.ae_hasFDerivAt_norm_space` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (`\|∇u\|` in `D₃` is the Frobenius norm; comparison with the operator norm `‖L‖ ≤ ‖L‖_F ≤ √3‖L‖`) | `NavierFormal.opNorm_le_frobeniusNorm`, `frobeniusNorm_le_sqrt_three_mul`, `opNorm_sq_le_frobeniusNormSq`, `frobeniusNormSq_le_three_mul`, `norm_apply_le_frobeniusNorm_mul`, `frobeniusNorm_sq`, `frobeniusNormSq_nonneg`, `frobeniusNorm_nonneg`; basis API `e_eq_basisFun`, `norm_e`, `sum_smul_e`, `inner_e` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (`D₃` integrand `\|u\|\|∇u\|² + \|u\|\|∇\|u\|\|²` through `(∇u)ᵀu`: `\|(∇u)ᵀu\|²/\|u\| ≤ \|u\|\|∇u\|²`, nonnegativity, zero at `u = 0`, `((∇u)ᵀu)ⱼ = ⟨u, ∂ⱼu⟩`) | `NavierFormal.inner_gradTranspose_left`, `gradTranspose_component`, `inner_self_gradTranspose`, `norm_gradTranspose_le`, `norm_gradTranspose_sq_div_le`, `D3density_nonneg`, `D3density_le_two_mul`, `D3density_eq_zero_of_eq_zero`, `enstrophyDensity_nonneg` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (`P₃` integrand `p u·∇\|u\|` through `(∇u)ᵀu`: convection form, zero at `u = 0`, `\|p u·∇\|u\|\| ≤ \|p\|\|∇u\|\|u\|`) | `NavierFormal.P3density_eq_mul_div`, `P3density_eq_convection`, `P3density_eq_zero_of_eq_zero`, `abs_P3density_le` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (`∇r_ε(u) = (∇u)ᵀu / r_ε(u)`, the regularized `P₃` integrand `⟨u,(∇u)ᵀu⟩/r_ε`) | `NavierFormal.hasFDerivAt_rEps_gradTranspose`, `fderiv_rEps_apply`, `fderiv_rEps_apply_self` | Phase II complete (supporting lemma, no literature input); the `ε ↓ 0` limit to `P3density` is not proved |
| `prop:pressure` (chain rule in the `(∇u)ᵀu` form: `∇\|u\| = (∇u)ᵀu/\|u\|`, `(∇u)ᵀu = \|u\|∇\|u\|`, `\|∇\|u\|\| = \|(∇u)ᵀu\|/\|u\|`, where `u` is differentiable and `u ≠ 0`) | `NavierFormal.fderiv_norm_apply_eq_inner_gradTranspose_div`, `gradient_norm_eq_smul_gradTranspose`, `gradTranspose_eq_smul_gradient_norm`, `norm_gradient_norm_eq` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (`D₃` integrand in the manuscript's form: `\|(∇u)ᵀu\|²/\|u\| = \|u\|\|∇\|u\|\|²`, hence `D3density = \|u\|\|∇u\|_F² + \|u\|\|∇\|u\|\|²` on `{u ≠ 0}`) | `NavierFormal.norm_gradTranspose_sq_div_eq`, `D3density_eq_gradient_norm`, `D3density_eq_enstrophy_add_gradient_norm` | Phase II complete (supporting lemma, no literature input); pointwise, under `DifferentiableAt ℝ u x` and `u x ≠ 0` |
| `prop:pressure` (`P₃` integrand in the manuscript's form: `u·∇\|u\| = ⟨u,(∇u)ᵀu⟩/\|u\|`, `P3density = p u·∇\|u\|` on `{u ≠ 0}`) | `NavierFormal.inner_self_gradient_norm`, `P3density_eq_gradient_norm` | Phase II complete (supporting lemma, no literature input); pointwise, under `DifferentiableAt ℝ u x` and `u x ≠ 0` |
| `prop:pressure` ("the integrand is zero at `u = 0`": `∇\|u\| = 0`, `D₃`, `P₃` densities and their manuscript-form integrands vanish on `{u = 0}`; Riesz/`gradient` form) | `NavierFormal.gradient_norm_of_zero`, `D3density_of_zero`, `D3density_gradient_norm_of_zero`, `P3density_of_zero`, `P3density_gradient_norm_of_zero` | Phase II complete (supporting lemma, no literature input); `gradient_norm_of_zero` needs no differentiability of `u` |
| `prop:pressure` (regularized chain rule in Riesz form: `∇r_ε(u) = r_ε(u)⁻¹(∇u)ᵀu`) | `NavierFormal.fderiv_rEps_apply_inner_gradTranspose`, `gradient_rEps_eq_smul_gradTranspose` | Phase II complete (supporting lemma, no literature input) |
| `prop:pressure` (divergence identity for the tested field: `div(r_ε u) = ⟨(∇u)ᵀu,u⟩/r_ε + r_ε ∇·u`; for solenoidal `u`, `div(r_ε u) = (\|u\|/r_ε) u·∇\|u\|`; zero-set case) | `NavierFormal.sum_component_inner_fderiv`, `divergence_rEps_smul_add`, `divergence_rEps_smul`, `inner_gradTranspose_self_div_rEps_eq`, `divergence_rEps_smul_eq_gradient_norm`, `divergence_rEps_smul_of_zero` | Phase II complete (supporting lemma, no literature input); pointwise at points of differentiability with `∇·u(x) = 0`; the `ε ↓ 0` limit to `P3density` is still not proved |
| `prop:pressure`, `def:target` (`∫\|u\|²`, `∫\|u\|³` as integrals; nonnegativity; `ofReal` bridges; measurability for continuous fields) | `NavierFormal.kineticEnergy_nonneg`, `X3Real_nonneg`, `kineticEnergyLintegral_eq`, `X3_eq_lintegral_ofReal`, `measurable_norm_sq`, `measurable_norm_pow_three` | Phase II complete (supporting lemma, no literature input) |
| `eq:NS` (`Δ = ∑ᵢ∂ᵢ²`, `(∇p)ᵢ = ∂ᵢp`, `∇·u = ∑ᵢ(∂ᵢu)ᵢ` in Mathlib's operators) | `NavierFormal.laplacian_eq_sum_iteratedFDeriv`, `NavierFormal.IBP.laplacian_eq_sum`, `NavierFormal.inner_gradient_apply`, `gradient_component`, `divergence_eq_sum_component` | Phase II complete (supporting lemma, no literature input) |
| `prop:energy` (`∫ ∇·F dx = 0`; product rule `∇·(pu) = u·∇p + p∇·u`) | `NavierFormal.IBP.integral_fderiv_apply_eq_zero`, `IBP.integral_divergence_eq_zero`, `IBP.divergence_smul` (auxiliary `IBP.coord`, `coord_apply`, `abs_coord_le`, `abs_divergence_le`, `fderiv_coord`, `continuous_divergence`) | Phase II complete (supporting lemma, no literature input); explicit `L¹` hypotheses, see gaps below |
| `prop:energy` (pressure term `∫ u·∇p dx = -∫ p ∇·u dx`) | `NavierFormal.IBP.integral_fderiv_apply_eq_neg_integral_mul_divergence` | Phase II complete (supporting lemma, no literature input); explicit `L¹` hypotheses |
| `prop:energy`, `prop:enstrophy` (viscous term `∫ u·Δu dx = -‖∇u‖₂²`, Frobenius) | `NavierFormal.IBP.integral_inner_laplacian_eq_neg_integral_enstrophyDensity` (auxiliary `IBP.fderiv_inner_dir_self`, `differentiable_inner_dir`, `norm_laplacian_le`, `continuous_laplacian`, `continuous_enstrophyDensity`, `sq_le_enstrophyDensity`) | Phase II complete (supporting lemma, no literature input); explicit `L¹` hypotheses |
| `prop:energy` (convection integral `½∫ u·∇\|u\|² = -½∫(∇·u)\|u\|² = 0`) | `NavierFormal.IBP.integral_inner_convection_eq_zero` | Phase II complete (supporting lemma, no literature input); explicit `L¹` hypotheses |
| `prop:scaling` (interpolation `‖u‖₃ ≤ ‖u‖₂^{1/2}‖u‖₆^{1/2}`) | `NavierFormal.eLpNorm_three_le`; general `eLpNorm'_interpolate`, `eLpNorm_interpolate`, `eLpNorm_interpolate_top`; `eLpNorm_tenThirds_le` | Phase II complete (supporting lemma, no literature input) |
| `prop:scaling`, `prop:enstrophy` (Sobolev `‖u‖₆ ≤ C‖∇u‖₂` on `ℝ³`, without compact support) | `NavierFormal.eLpNorm_six_le_eLpNorm_fderiv_two`, `sobolevSixWithoutCompactSupport` (constant `sobolevSixConst`; compactly supported case `eLpNorm_six_le_eLpNorm_fderiv_two_of_hasCompactSupport`; cutoffs `sobolevBump`, `sobolevCutoff`, `sobolevCutoff_contDiff`, `sobolevCutoff_nonneg`, `sobolevCutoff_le_one`, `sobolevCutoff_eq_one`, `sobolevCutoff_hasCompactSupport`, `exists_bound_norm_fderiv_sobolevBump`, `norm_fderiv_sobolevCutoff_le`, `eLpNorm_six_sobolevCutoff_smul_le`, `lintegral_enorm_rpow_six_eq`) | Phase II complete (supporting lemma, no literature input; Mathlib's Gagliardo–Nirenberg–Sobolev theorem plus a cutoff argument); operator norm in `‖∇u‖₂` |
| `prop:enstrophy` (Young's inequality, conjugate exponents `4/3` and `4`) | `NavierFormal.young_four_thirds`, `young_four_thirds_eps`, `young_holderConjugate_eps`, `holderConjugate_four_thirds_four` (companions `young_five_fourths`, `young_five_fourths_eps`, `holderConjugate_five_fourths_five`) | Phase II complete (supporting lemma, no literature input) |
| `premise:local`, `thm:conditional` (restriction of a classical solution and of the regularity package to a shorter interval; smoothness, differentiability, measurability of `u(t)`, `p(t)` at interior times) | `NavierFormal.IsClassicalSolution.mono`, `RegularityPackage.mono`, `IsClassicalSolution.contDiffAt_velocity`, `contDiffAt_pressure`, `differentiableAt_velocity`, `differentiableAt_pressure`, `differentiableAt_time`, `continuous_velocity`, `aestronglyMeasurable_velocity` (auxiliary `contDiffAt_space_of_smooth`, `contDiffAt_time_of_smooth`, `two_le_infty`, `infty_ne_zero`; `SchwartzDivFree.contDiff`, `.continuous`, `.differentiable`; `timeDerivIter_zero`, `timeDerivIter_succ`) | Phase II complete (supporting lemma, no literature input) |
| `sec:quotient` (`𝒢₃` closed, generators in `𝒢₃`; `𝒬 ≥ 0`, `𝒬(u) ≤ ⅓‖u‖₃³`, `𝒬(0) = 0`, `𝒬(au) = \|a\|³𝒬(u)`; minimizer attains `𝒬`; `\|A\| = \|w\|²`, `A` measurable and a.e. well defined; `0` solenoidal; `D_𝒬(w,0) = 0`, strain flux linear at `0`) | `NavierFormal.isClosed_gradientSubspace`, `gradientGenerators_subset`, `memLp_gradient_toLp_mem_gradientSubspace`, `quotientFunctional_bddBelow`, `quotientFunctional_nonneg`, `quotientFunctional_le`, `quotientFunctional_le_cube`, `quotientFunctional_zero`, `quotientFunctional_smul`, `IsQuotientMinimizer.quotientFunctional_eq`, `IsQuotientMinimizer.cube_norm_eq`, `cubicMap_apply`, `norm_cubicMap`, `aestronglyMeasurable_cubicMap`, `cubicMap_congr`, `isSolenoidalL3_zero`, `quotientDissipation_zero`, `strainFlux_zero` | Phase II complete (supporting lemma, no literature input); existence/uniqueness of minimizers, coercivity, heat monotonicity, differentiability, `eq:quotient-evolution` remain paper only |
| `sec:quotient`, `prop:scaling` (critical dilation `u_λ(x) = λu(λx)` preserves `L³` and is a linear isometry of `L³(ℝ³;ℝ³)` onto itself with inverse the dilation by `λ⁻¹`; pointwise algebra of `dilate`) | `NavierFormal.memLp_dilate`, `dilateL3` (`L3 ≃ₗᵢ[ℝ] L3`), `dilateL3_apply`, `dilateL3_symm_apply`, `coeFn_dilateL3Fun`, `norm_dilateL3Fun`, `dilateL3Fun_add`, `dilateL3Fun_smul`, `dilateL3Fun_inv_left`, `dilateL3Fun_inv_right`, `dilate_congr_ae`, `quasiMeasurePreserving_smul_space`, `dilate_add`, `dilate_const_smul`, `dilate_dilate`, `dilate_one`, `dilate_inv_dilate`, `dilate_dilate_inv` | Phase II complete (supporting lemma, no literature input); `λ > 0` |
| `sec:quotient` (`𝒢₃` is invariant under the critical dilation: `dilate λ (∇φ) = ∇(φ(λ·))`, test potentials are closed under `x ↦ λx`, generators and `𝒢₃` are mapped onto themselves) | `NavierFormal.gradient_comp_smul`, `dilate_gradient`, `IsTestPotential.comp_smul`, `dilateL3_mem_gradientGenerators`, `dilateL3_image_gradientGenerators`, `dilateL3_map_span`, `dilateL3_image_span`, `dilateL3_mem_gradientSubspace`, `dilateL3_mem_gradientSubspace_iff`, `dilateL3_symm_mem_gradientSubspace`, `dilateL3_gradientSubspace` (auxiliary `space_eq_of_inner_eq`) | Phase II complete (supporting lemma, no literature input) |
| `sec:quotient` ("the functional is cubic in amplitude and invariant under the critical spatial scaling": `𝒬(u_λ) = 𝒬(u)`, `𝒬(a u_λ) = \|a\|³𝒬(u)`; minimizing representatives are transported) | `NavierFormal.quotientFunctional_dilateL3`, `quotientFunctional_smul_dilateL3`, `isQuotientMinimizer_dilateL3` | Phase II complete (supporting lemma, no literature input); `λ > 0` |

## Supporting definitions (statement surface)

Definitions carry no status; their fidelity is audited row by row in
`paper-lean-specification.md`. They are listed here so that the axiom report
covers them.

| Manuscript object | Lean definition |
| --- | --- |
| standard basis `eᵢ` of `ℝ³`; Frobenius norm of a Jacobian | `NavierFormal.e`, `frobeniusNormSq`, `frobeniusNorm` |
| `∇·`, `(u·∇)u`, `(∇u)ᵀu`, `\|∇u\|²` density, `∂ₜ`, `∂ₜʲ` | `NavierFormal.divergence`, `convection`, `gradTranspose`, `enstrophyDensity`, `timeDeriv`, `timeDerivIter` (`Δ` and `∇` are Mathlib's) |
| `∫\|u\|²`, `∫\|u\|³`, `D₃`, `P₃` and their densities | `NavierFormal.kineticEnergy`, `kineticEnergyLintegral`, `X3`, `X3Real`, `D3density`, `D3`, `P3density`, `P3` |
| datum class, classical solution, regularity package, Clay target, critical hypothesis | `NavierFormal.SchwartzDivFree`, `IsClassicalSolution`, `RegularityPackage`, `ClayAlternativeA`, `ClayAlternativeA_all`, `CriticalBound`, `CriticalHypothesis` |
| Sobolev constant, cutoff family, packaged Sobolev statement | `NavierFormal.sobolevSixConst`, `sobolevBump`, `sobolevCutoff`, `SobolevSixWithoutCompactSupport` |
| `L³`, test potentials, `𝒢₃`, `𝒬`, minimizers, `A = \|w\|w`, solenoidal, `D_𝒬`, strain flux | `NavierFormal.L3`, `IsTestPotential`, `gradientGenerators`, `gradientSubspace`, `quotientFunctional`, `IsQuotientMinimizer`, `cubicMap`, `IsSolenoidalL3`, `quotientDissipation`, `strainFlux` |
| coordinate functional `yᵢ = ⟨eᵢ, y⟩` (bookkeeping) | `NavierFormal.IBP.coord` |
| critical dilation on `L³` classes, `u ↦ u_λ` as a map and as a linear isometry `L³ ≃ L³` | `NavierFormal.dilateL3Fun`, `dilateL3` |

Fidelity gaps between these lemmas and the proof of `prop:pressure` found at
the CP03b integration (none of them is closed by the files above):

- Solution class. The a.e. statements assume `LipschitzWith C u` on all of
  `ℝ³` (Mathlib's Rademacher hypothesis). The manuscript applies them to the
  maximal classical solution of Schwartz data on a compact time interval,
  where `∇u(t)` is bounded; the bridge "classical solution on `[0, τ]` ⇒
  `u(t)` globally Lipschitz" is not in Lean. (CP03c: the class now exists as
  `NavierFormal.IsClassicalSolution` in `SolutionClass.lean`, without
  integrability bounds; the bridge is still open.)
- Sobolev representative. The manuscript's "`∇\|u\| = 0` a.e. on the zero set
  of its Sobolev representative" is a statement about the weak gradient. Lean
  proves it for the Fréchet derivative (and `fderiv` uses the junk value `0`
  where `\|u\|` is not differentiable). The identification of the a.e.
  Fréchet derivative of a Lipschitz map with its weak gradient is not stated.
- Norms. Lean's `\|∇u\|` in the CP03b lemmas is the operator norm of the
  Fréchet derivative; the manuscript's `\|∇u\|` in `D₃` is the Euclidean
  (Frobenius) norm of the Jacobian. The Lean bound is the stronger one
  (operator ≤ Frobenius). (CP03c: the comparison `‖L‖ ≤ ‖L‖_F ≤ √3‖L‖` is now
  `NavierFormal.opNorm_le_frobeniusNorm`, `frobeniusNorm_le_sqrt_three_mul`,
  and `D3density` uses the Frobenius norm.)
- Sobolev representative, `∇|u|` form (CP03d). The pointwise dictionary between
  the `(∇u)ᵀu` form of `D3density`, `P3density` and the manuscript's `∇\|u\|`
  form is now `D3density_eq_gradient_norm`, `P3density_eq_gradient_norm`
  (on `{u ≠ 0}`, at points of differentiability) with `gradient_norm_of_zero`
  on the zero set; `gradient` is Mathlib's Riesz gradient of the Fréchet
  derivative, so the weak-gradient identification above is still open.
- Divergence identity. `hasFDerivAt_rEps_smul` gives the full differential of
  `r_ε u`; taking the trace, using `div u = 0`, and rewriting through
  `∇\|u\|` to reach `div(r_ε u) = (\|u\|/r_ε) u·∇\|u\|` is not done.
  (CP03c: `fderiv_rEps_apply_self` gives `d(r_ε∘u)(x)[u(x)] = ⟨u,(∇u)ᵀu⟩/r_ε`,
  the numerator of that identity in the `(∇u)ᵀu` form; the trace step and the
  `ε ↓ 0` limit to `P3density` remain open.) (CP03d: the trace step is done,
  `divergence_rEps_smul_add`, `divergence_rEps_smul`,
  `divergence_rEps_smul_eq_gradient_norm`, pointwise at points of
  differentiability with `∇·u(x) = 0`; the `ε ↓ 0` limit remains open.)
- Everything integral. Testing the equation against `r_ε u`, the spatial
  cutoff, integrability of `H_ε(u)` on `ℝ³`, the `L²∩L⁶ ⇒ L³∩L⁴` interpolation,
  `p = R_iR_j(u_iu_j) ∈ L²∩L³`, dominated convergence in `ε` and in the cutoff
  radius, the limiting time term `X'/3`, both integrations by parts, and the
  pressure-normalization remark are paper only. The Lean limits
  `tendsto_rEps`, `tendsto_HEps` are pointwise.
- Not proved (worker report): monotonicity of `H_ε` in `ε`; not needed by
  the manuscript sentence.

Fidelity gaps found at the CP03c integration (statement surface; none is
closed by the files above; details per row in `paper-lean-specification.md`):

- Class identification. `IsClassicalSolution` has no integrability class
  (amendment A5), so it is wider than Tao's `H¹` mild uniqueness class;
  `CriticalBound` therefore quantifies over a possibly larger family than
  `hyp:critical` and is at least as strong as it. `hyp:critical → CriticalBound`
  is the direction carrying an obligation (R-CRIT, R-CLASS); no maximal
  solution or maximal time is defined.
- Regularity package. `RegularityPackage` is a `t`-uniform bound on
  `eLpNorm (iteratedFDeriv ℝ k …) 2`, not continuity in time and not
  measurability (R-REG).
- Smoothness at `t = 0`. `C^∞(ℝ³×[0,∞))` in `ClayAlternativeA` is `ContDiffOn`
  on the closed half-space, one-sided; extendability across `t = 0` is not
  stated (R-T0).
- `D₃`, `P₃`. Written through `(∇u)ᵀu` (amendment A2) with `a/0 = 0` at
  `u = 0`; the pointwise identity with the manuscript's `\|u\|\|∇\|u\|\|²`
  form on `{u ≠ 0}` is now stated (CP03d, `D3density_eq_gradient_norm`,
  `P3density_eq_gradient_norm`); `p = R_iR_j(u_iu_j)` is not encoded;
  `D3`, `P3`, `kineticEnergy`, `X3Real` are Bochner integrals with junk
  value `0` for non-integrable integrands (R-JUNK).
- Integration by parts. The `IBP` identities carry explicit `L¹` hypotheses
  on `‖p‖‖u‖`, `‖p‖‖∇u‖`, `‖∇p‖‖u‖`, `‖u‖‖∇u‖`, `‖∇u‖_F²`, `‖u‖‖D²u‖`,
  `‖u‖³`, `‖u‖²‖∇u‖`; the manuscript's "strong-solution Sobolev bounds" and
  radial cutoff are not derived from `IsClassicalSolution` or
  `RegularityPackage`. `∫ u·∇p` is spelled `fderiv ℝ p x (u x)`, related to
  `⟨∇p, u⟩` by `inner_gradient_apply` but not rewritten.
- Sobolev. `‖∇u‖₂` in `eLpNorm_six_le_eLpNorm_fderiv_two` is the operator
  norm (R-NORM; safe in an inequality with an opaque constant); hypotheses
  `u ∈ L²`, `∇u ∈ L²` are required. `‖∇u‖₃ ≤ C‖∇u‖₂^{1/2}‖Δu‖₂^{1/2}` of
  `prop:enstrophy` is not in Lean.
- Quotient objects. `𝒢₃` is the closure of the *span* of a.e.-classes of
  `∇φ`; `∇φ ∈ L³` is a hypothesis, not proved; existence and uniqueness of
  minimizers, coercivity, heat monotonicity, differentiability, and
  `eq:quotient-evolution` are not stated; `quotientDissipation` applies `Δ`
  to a bare field. (CP03d: the scaling invariance `𝒬(u_λ) = 𝒬(u)` is now
  `quotientFunctional_dilateL3`, for `λ > 0`; the manuscript does not restrict
  the sign of `λ`, and `λ < 0` is not covered. The transported minimizer
  statement `isQuotientMinimizer_dilateL3` quantifies over given minimizers
  and asserts no existence.)

Axiom reports are recorded here after each integration.

## Axiom report: CP03a integration (2026-09-05)

Checked with `lake env lean research/check_cp03a.lean` after a clean
`lake build` (only warning: the pre-existing `sorry` in `Challenge.lean:19`).
Every declaration listed in the `prop:ode` and `prop:scaling` rows above
reported exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

namely all 28 declarations: `NavierFormal.scalarObstruction`,
`scalarObstruction_base_pos`, `scalarObstruction_pos`,
`hasDerivAt_scalarObstruction`, `intervalIntegrable_scalarObstruction`,
`integrableOn_scalarObstruction`, `tendsto_scalarObstruction`,
`integral_scalarObstruction`, `scalar_obstruction_exists`, `dilate`,
`dilateSpaceTime`, `map_smul_volume`, `rpow_dilate_factor`,
`eLpNorm_comp_smul`, `eLpNorm_dilate`, `eLpNorm_dilate_three`,
`eLpNorm_dilate_two`, `eLpNorm_dilate_two_sq`, `eLpNorm_dilateSpaceTime`,
`scalingWitness`, `aestronglyMeasurable_scalingWitness`,
`integrable_scalingWitness_rpow_four`, `memLp_scalingWitness_four`,
`lt_scalingWitness`, `eLpNormEssSup_scalingWitness`,
`exists_memLp_four_not_memLp_top`, `exists_memLp_four_eLpNorm_top_eq_top`,
`L4L3_supercritical` (all in namespace `NavierFormal`). No project axiom is
involved.

## Axiom report: CP03b integration (2026-09-05)

Checked with `lake env lean research/check_cp03b.lean` after a clean
`lake build` (only warning: the pre-existing `sorry` in `Challenge.lean:19`).
Every declaration in the Supporting-lemmas table reported exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

namely all 42 declarations. From `NavierFormal/Regularization.lean` (29):
`NavierFormal.rEps`, `HEps`, `HEpsConst`, `sqrt_cube_eq_rpow`, `rEps_sq`,
`rEps_pos`, `norm_le_rEps`, `rEps_le_norm_add_sqrt`, `rEps_mono`,
`norm_sq_div_rEps_le`, `norm_div_rEps_le_one`, `rEps_cube`, `HEps_eq_cube`,
`HEps_nonneg`, `HEps_le_norm_sq_mul_rEps`, `HEps_le`, `abs_HEps_le`,
`abs_HEps_le_two`, `tendsto_rEps`, `tendsto_HEps`, `rEps_fderiv_apply`,
`hasFDerivAt_rEps`, `hasFDerivAt_HEps`, `opNorm_rEps_fderiv_le`,
`rEps_smul_fderiv_apply`, `hasFDerivAt_rEps_smul`, `hasFDerivAt_rEps_space`,
`hasFDerivAt_HEps_space`, `hasFDerivAt_rEps_smul_space`. From
`NavierFormal/NormGradient.lean` (13): `hasFDerivAt_norm_of_ne_zero`,
`fderiv_norm_apply_of_ne_zero`, `norm_apply_le_of_hasFDerivAt_norm`,
`opNorm_le_of_hasFDerivAt_norm`, `norm_fderiv_norm_le`,
`hasFDerivAt_norm_eq_zero_of_eq_zero`, `fderiv_norm_eq_zero_of_eq_zero`,
`ae_differentiableAt_norm`, `ae_norm_fderiv_norm_le`,
`ae_norm_fderiv_norm_le_of_contDiff`, `ae_hasFDerivAt_norm`,
`ae_norm_fderiv_norm_le_space`, `ae_hasFDerivAt_norm_space` (all in
namespace `NavierFormal`). No project axiom is involved.

## Axiom report: CP03c integration (2026-09-05)

Checked with `lake env lean research/check_cp03c.lean` after a clean
`lake build` (only warning: the pre-existing `sorry` in `Challenge.lean:19`;
no warning from any of the five new files). All 163 declarations of
`NavierFormal/Calculus.lean` (53), `NavierFormal/IBP.lean` (19),
`NavierFormal/Interpolation.lean` (28), `NavierFormal/QuotientObjects.lean`
(28), and `NavierFormal/SolutionClass.lean` (35) listed in
`research/check_cp03c.lean` — every definition and lemma of the tables above —
reported exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

with one exception: `NavierFormal.IsClassicalSolution.two_le_infty` (the
plumbing fact `(2 : ℕ∞ω) ≤ ∞`) reported the strictly smaller list

```
depends on axioms: [propext, Quot.sound]
```

No project axiom is involved; `NavierFormal/Literature/` is unchanged and
still contains no axiom.

## Axiom report: CP03d integration (2026-09-05)

Checked with `lake env lean research/check_cp03d.lean` after a clean
`lake build` (only warning: the pre-existing `sorry` in `Challenge.lean:19`;
no warning from either new file). All 56 declarations of
`NavierFormal/DensityBridge.lean` (22) and `NavierFormal/QuotientScaling.lean`
(34) listed in `research/check_cp03d.lean` — every declaration of the two
files — reported exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

From `NavierFormal/DensityBridge.lean` (22):
`NavierFormal.fderiv_norm_apply_eq_inner_gradTranspose_div`,
`gradient_norm_eq_smul_gradTranspose`, `gradTranspose_eq_smul_gradient_norm`,
`norm_gradient_norm_eq`, `norm_gradTranspose_sq_div_eq`,
`D3density_eq_gradient_norm`, `D3density_eq_enstrophy_add_gradient_norm`,
`inner_self_gradient_norm`, `P3density_eq_gradient_norm`,
`gradient_norm_of_zero`, `D3density_of_zero`,
`D3density_gradient_norm_of_zero`, `P3density_of_zero`,
`P3density_gradient_norm_of_zero`, `fderiv_rEps_apply_inner_gradTranspose`,
`gradient_rEps_eq_smul_gradTranspose`, `sum_component_inner_fderiv`,
`divergence_rEps_smul_add`, `divergence_rEps_smul`,
`inner_gradTranspose_self_div_rEps_eq`,
`divergence_rEps_smul_eq_gradient_norm`, `divergence_rEps_smul_of_zero`.
From `NavierFormal/QuotientScaling.lean` (34): `dilate_add`,
`dilate_const_smul`, `dilate_dilate`, `dilate_one`, `dilate_inv_dilate`,
`dilate_dilate_inv`, `quasiMeasurePreserving_smul_space`, `dilate_congr_ae`,
`memLp_dilate`, `dilateL3Fun`, `coeFn_dilateL3Fun`, `norm_dilateL3Fun`,
`dilateL3Fun_add`, `dilateL3Fun_smul`, `dilateL3Fun_inv_left`,
`dilateL3Fun_inv_right`, `dilateL3`, `dilateL3_apply`, `dilateL3_symm_apply`,
`space_eq_of_inner_eq`, `gradient_comp_smul`, `dilate_gradient`,
`IsTestPotential.comp_smul`, `dilateL3_mem_gradientGenerators`,
`dilateL3_image_gradientGenerators`, `dilateL3_map_span`,
`dilateL3_image_span`, `dilateL3_mem_gradientSubspace`,
`dilateL3_mem_gradientSubspace_iff`, `dilateL3_symm_mem_gradientSubspace`,
`dilateL3_gradientSubspace`, `quotientFunctional_dilateL3`,
`quotientFunctional_smul_dilateL3`, `isQuotientMinimizer_dilateL3` (all in
namespace `NavierFormal`). No project axiom is involved;
`NavierFormal/Literature/` is unchanged and still contains no axiom.
