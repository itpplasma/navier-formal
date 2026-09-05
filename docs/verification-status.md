# Verification status

Reader-facing status has three values:

- **Paper only:** the manuscript contains the proof, but Phase I is open.
- **Phase I complete:** Lean reaches a checked literature theorem, but that
  theorem has not yet been proved from Mathlib.
- **Phase II complete:** Lean proves the claim from Mathlib.

Current state: CP03a integrated. `prop:ode` and the norm-scaling half of
`prop:scaling` (plus the two scalar remarks inside its proof) are proved from
Mathlib in `NavierFormal/Ode.lean`, `NavierFormal/Scaling.lean`, and
`NavierFormal/InterpolationMismatch.lean`. The PDE half of `prop:scaling`
(that `(u_λ, p_λ)` solves the system) and estimate `eq:L4L3` are not yet in
Lean. `Challenge.lean` still carries only the labelled placeholder. The
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
| `prop:pressure` | — | paper only |
| `prop:lowpressure` | — | paper only |
| `thm:continuation` | — | paper only (imports ESS/GKP) |
| `thm:conditional` | — | paper only (conditional on `hyp:critical`) |
| `sec:quotient` results | — | paper only (HF17, audited) |

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
