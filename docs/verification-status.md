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
identities, and the dominated-convergence limit remain paper only.
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
| `sec:quotient` results | — | paper only (HF17, audited) |

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

Fidelity gaps between these lemmas and the proof of `prop:pressure` found at
the CP03b integration (none of them is closed by the files above):

- Solution class. The a.e. statements assume `LipschitzWith C u` on all of
  `ℝ³` (Mathlib's Rademacher hypothesis). The manuscript applies them to the
  maximal classical solution of Schwartz data on a compact time interval,
  where `∇u(t)` is bounded; the bridge "classical solution on `[0, τ]` ⇒
  `u(t)` globally Lipschitz" is not in Lean, and no solution class exists in
  `NavierFormal/Basic.lean` yet.
- Sobolev representative. The manuscript's "`∇\|u\| = 0` a.e. on the zero set
  of its Sobolev representative" is a statement about the weak gradient. Lean
  proves it for the Fréchet derivative (and `fderiv` uses the junk value `0`
  where `\|u\|` is not differentiable). The identification of the a.e.
  Fréchet derivative of a Lipschitz map with its weak gradient is not stated.
- Norms. Lean's `\|∇u\|` is the operator norm of the Fréchet derivative; the
  manuscript's `\|∇u\|` in `D₃` is the Euclidean (Frobenius) norm of the
  Jacobian. The Lean bound is the stronger one (operator ≤ Frobenius), but
  the comparison lemma is not stated.
- Divergence identity. `hasFDerivAt_rEps_smul` gives the full differential of
  `r_ε u`; taking the trace, using `div u = 0`, and rewriting through
  `∇\|u\|` to reach `div(r_ε u) = (\|u\|/r_ε) u·∇\|u\|` is not done.
- Everything integral. Testing the equation against `r_ε u`, the spatial
  cutoff, integrability of `H_ε(u)` on `ℝ³`, the `L²∩L⁶ ⇒ L³∩L⁴` interpolation,
  `p = R_iR_j(u_iu_j) ∈ L²∩L³`, dominated convergence in `ε` and in the cutoff
  radius, the limiting time term `X'/3`, both integrations by parts, and the
  pressure-normalization remark are paper only. The Lean limits
  `tendsto_rEps`, `tendsto_HEps` are pointwise.
- Not proved (worker report): monotonicity of `H_ε` in `ε`; not needed by
  the manuscript sentence.

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
