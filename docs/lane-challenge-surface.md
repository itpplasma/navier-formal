# The advertised statement surface

This note records the CP1 statement surface that replaced the skeleton
placeholder: what `Challenge.lean` now advertises, why each item is on the
list, what was deliberately left off, and the checks that were run. It is a
lane report, not a status list; the live status remains `../navier/PLAN.md`
and `verification-status.md`.

## What changed

`Challenge.lean` previously carried one placeholder,
`NavierFormal.skeleton_placeholder : (2 : ℕ) + 2 = 4`, proved by `sorry`, and
`Solution.lean` proved the same by `norm_num`. Both files now carry nine
advertised statements in the namespace `NavierFormal.CP1`, and
`comparator.json` names those nine.

`Challenge.lean` imports Mathlib only. It defines nothing: every advertised
statement is written out of Mathlib objects, with the two definitions of the
development that the statements would otherwise need — `NavierFormal.dilate`
and `NavierFormal.dilateSpaceTime` for the critical dilation,
`NavierFormal.scalingWitness` and `NavierFormal.scalarObstruction` for the two
witnesses — either inlined as a lambda or removed by existential
quantification. Consequently `definition_names` in `comparator.json` is empty
and a reader auditing the surface needs no knowledge of `NavierFormal/`.
`Space` is spelled `EuclideanSpace ℝ (Fin 3)` rather than through the
development's `abbrev`.

`Solution.lean` re-declares the nine statements with identical types and
proves them. It does not import `Challenge`. It imports only
`NavierFormal.Ode`, `NavierFormal.Scaling` and
`NavierFormal.InterpolationMismatch`, not the `NavierFormal` root, so the
advertised surface depends on no other module of the development and on no
module another lane is currently writing. Every proof is a single `exact`
against the corresponding development declaration; each inlined lambda is
definitionally the development definition, so no `simp` or `unfold` step is
needed.

## The advertised list

Types as elaborated, with numeric types shown. `eLpNorm`, `MemLp`,
`IntegrableOn` and `volume` are `MeasureTheory`'s; the real exponents are
`Real.rpow`, the natural ones `Monoid.npow`.

1. `NavierFormal.CP1.eLpNorm_dilation` — manuscript `prop:scaling`(ii),
   identity `eq:scaling-norm`, for `0 < q < ∞`. Proved from
   `NavierFormal.eLpNorm_dilate`.

   ```
   ∀ (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {q : ENNReal},
     q ≠ 0 → q ≠ ⊤ → ∀ {lam : ℝ}, 0 < lam →
       eLpNorm (fun x => lam • v (lam • x)) q volume =
         ENNReal.ofReal (lam ^ (1 - 3 / q.toReal)) * eLpNorm v q volume
   ```

2. `NavierFormal.CP1.eLpNorm_dilation_slice` — the same identity on the time
   slice of the rescaled field `u_λ(x,t) = λ u(λ x, λ² t)`, that is
   `‖u_λ(t)‖_q = λ^{1-3/q}‖u(λ² t)‖_q`. Proved from
   `NavierFormal.eLpNorm_dilateSpaceTime`.

   ```
   ∀ (u : ℝ × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
     {q : ENNReal}, q ≠ 0 → q ≠ ⊤ → ∀ {lam : ℝ}, 0 < lam →
       eLpNorm (fun x => lam • u (lam ^ 2 * t, lam • x)) q volume =
         ENNReal.ofReal (lam ^ (1 - 3 / q.toReal)) *
           eLpNorm (fun x => u (lam ^ 2 * t, x)) q volume
   ```

3. `NavierFormal.CP1.eLpNorm_dilation_three` — `prop:scaling`(ii), first
   consequence: `L³` is invariant under the critical dilation. Proved from
   `NavierFormal.eLpNorm_dilate_three`.

   ```
   ∀ (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {lam : ℝ},
     0 < lam →
       eLpNorm (fun x => lam • v (lam • x)) 3 volume = eLpNorm v 3 volume
   ```

4. `NavierFormal.CP1.eLpNorm_dilation_two_sq` — `prop:scaling`(ii), second
   consequence: `‖u_λ(t)‖₂² = λ⁻¹‖u(λ² t)‖₂²`. Proved from
   `NavierFormal.eLpNorm_dilate_two_sq`.

   ```
   ∀ (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {lam : ℝ},
     0 < lam →
       eLpNorm (fun x => lam • v (lam • x)) 2 volume ^ 2 =
         ENNReal.ofReal lam⁻¹ * eLpNorm v 2 volume ^ 2
   ```

5. `NavierFormal.CP1.exists_memLp_four_not_memLp_top` — manuscript
   `rem:mismatch`(a), the interpolation mismatch inside the proof of
   `prop:scaling`. Proved from
   `NavierFormal.exists_memLp_four_not_memLp_top`.

   ```
   ∀ {T : ℝ}, 0 < T →
     ∃ g, MemLp g 4 (volume.restrict (Set.Ioo 0 T)) ∧
       ¬MemLp g ⊤ (volume.restrict (Set.Ioo 0 T))
   ```

6. `NavierFormal.CP1.exists_memLp_four_eLpNorm_top_eq_top` — the same remark in
   the essential-supremum form the manuscript states. Proved from
   `NavierFormal.exists_memLp_four_eLpNorm_top_eq_top`.

   ```
   ∀ {T : ℝ}, 0 < T →
     ∃ g, MemLp g 4 (volume.restrict (Set.Ioo 0 T)) ∧
       eLpNorm g ⊤ (volume.restrict (Set.Ioo 0 T)) = ⊤
   ```

7. `NavierFormal.CP1.L4L3_supercritical` — manuscript `rem:mismatch`(b), the
   Ladyzhenskaya–Prodi–Serrin arithmetic for `(r,q) = (4,3)` under
   `eq:L4L3`. Proved from `NavierFormal.L4L3_supercritical`.

   ```
   (2 / 4 : ℝ) + (3 / 3 : ℝ) = (3 / 2 : ℝ) ∧ (1 : ℝ) < (3 / 2 : ℝ)
   ```

8. `NavierFormal.CP1.scalar_obstruction_exists` — manuscript `prop:ode`
   (scalar obstruction). Proved from
   `NavierFormal.scalar_obstruction_exists`.

   ```
   ∀ {C T : ℝ}, 0 < C → 0 < T →
     ∃ y, (∀ t ∈ Set.Ico (0 : ℝ) T, 0 < y t) ∧
       (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (C * y t ^ 3) t) ∧
       IntegrableOn y (Set.Ico 0 T) volume ∧
       Filter.Tendsto y (nhdsWithin T (Set.Iio T)) Filter.atTop
   ```

9. `NavierFormal.CP1.integral_scalar_obstruction` — the value
   `∫_0^T y = √(2T/C)` computed in the proof of `prop:ode`, with the
   manuscript's witness written out. Proved from
   `NavierFormal.integral_scalarObstruction`.

   ```
   ∀ {C T : ℝ}, 0 < C → 0 ≤ T →
     ∫ (t : ℝ) in (0 : ℝ)..T, (2 * C * (T - t)) ^ (-(1 / 2) : ℝ) = √(2 * T / C)
   ```

Items 1, 2, 5, 7, 8 and 9 are exactly the declarations the manuscript already
names as machine-checked in `rem:lean`, transcribed into Mathlib-only form.
Items 3, 4 and 6 are the further consequences that `verification-status.md`
records as Phase II complete with no literature input.

## Axiom hygiene

Every advertised theorem was checked with `#print axioms` against the
`Solution.lean` declaration, in a file importing `Solution` only. All nine
report exactly the permitted set.

```
'NavierFormal.CP1.eLpNorm_dilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierFormal.CP1.eLpNorm_dilation_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierFormal.CP1.eLpNorm_dilation_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierFormal.CP1.eLpNorm_dilation_two_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierFormal.CP1.exists_memLp_four_not_memLp_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierFormal.CP1.exists_memLp_four_eLpNorm_top_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierFormal.CP1.L4L3_supercritical' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierFormal.CP1.scalar_obstruction_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierFormal.CP1.integral_scalar_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry` appears outside `Challenge.lean`, where there are exactly nine, one
per advertised statement, and no `axiom` declaration exists anywhere in the
repository.

## How type identity was verified

Not by eye. Two independent mechanical checks.

First, both files are generated from one source text, so the statement blocks
are byte-identical. Extracting from each file everything between
`namespace NavierFormal.CP1` and `end NavierFormal.CP1` and dropping only the
proof lines after `:= by` gives two 4525-byte texts that `diff` reports as
identical. The files differ only in their imports, their module docstring, and
the proof line of each theorem.

Second, byte-identical source does not by itself force identical elaboration,
because `Solution.lean` imports the development and could in principle pick up
a different instance or notation. So the elaborated types were compared:
`set_option pp.all true` followed by `#check @<name>` for all nine names was
run once in a file importing `Challenge` and once in a file importing
`Solution`. The two outputs are 288673 bytes each and `diff` reports them
identical. At `pp.all` the printed term carries every implicit argument,
instance and universe, so identical output is identical type up to renaming of
bound variables.

The two modules cannot be imported into one file to compare the constants
directly, since they declare the same names; the `pp.all` diff is the
substitute.

To reproduce, after `lake build`: write a file with `import Solution` followed
by `#print axioms <name>` for the nine names of `comparator.json` and run it
with `lake env lean`; then write two files, one with `import Challenge` and one
with `import Solution`, each followed by `set_option pp.all true` and
`#check @<name>` for the same nine names, run both with `lake env lean` and
`diff` the outputs. The harness files were kept outside the repository, since
this lane owns only `Challenge.lean`, `Solution.lean`, `comparator.json` and
this note.

## What was deliberately not advertised, and why

The rule applied was: advertise a *complete* manuscript unit that is proved
from Mathlib today, never a fragment of the proof of a result that is still
paper only.

- The PDE half of `prop:scaling`(i) — that `(u_λ, p_λ)` again solves
  `eq:NS` — is paper only and is not advertised. Item 2 says only that the
  norms of the slices scale; it asserts nothing about the equations.
- The estimate `eq:L4L3` of `prop:scaling`(iii) is paper only.
- The endpoint `q = ∞` of `eq:scaling-norm` is not in Lean:
  `NavierFormal.eLpNorm_dilate` needs `q ≠ ∞`. The manuscript states
  `1 ≤ q ≤ ∞`, the advertised statement covers `0 < q < ∞`. The two
  hypotheses `q ≠ 0`, `q ≠ ⊤` are visible in the advertised type.
- `prop:energy`, `prop:enstrophy`, `prop:pressure`, `prop:lowpressure`,
  `thm:continuation`, `thm:conditional` and every result of `sec:quotient`
  are paper only; nothing about them is advertised. In particular the
  conditional Clay alternative A theorem is not advertised in any form, and
  neither `ClayAlternativeA` nor `CriticalBound` appears in the surface: they
  are formalized statements about which nothing is proved.
- `eq:nu-normalization` (`IsClassicalSolution.nuNormalization`,
  `eLpNorm_three_nuNormalization`) is Phase II complete but is a statement
  about `NavierFormal.IsClassicalSolution`, a structure with six fields built
  on `timeDeriv`, `convection`, `divergence` and Mathlib's `Δ` and `∇`.
  Advertising it would mean inlining that whole solution class into
  `Challenge.lean`, which would make the trusted surface larger than the
  results it carries and would import the class-identification obligations
  R-CLASS and R-CRIT into a file whose purpose is to be small. It is left off.
- The Phase II supporting lemmas — the interpolation
  `‖u‖₃ ≤ ‖u‖₂^{1/2}‖u‖₆^{1/2}`, the Sobolev inequality without compact
  support, Young's inequality, the boundary-free integrations by parts, the
  pointwise `prop:pressure` calculus of `Regularization.lean`,
  `NormGradient.lean` and `DensityBridge.lean`, and the quotient objects and
  their scaling invariance in `QuotientObjects.lean` and
  `QuotientScaling.lean` — are all single sentences inside the proof of a
  proposition that is itself paper only. Several of them are statable from
  Mathlib alone, and all of them are axiom-clean, but advertising a proof
  sentence of an unproved proposition would misrepresent the state of the
  programme. `rem:mismatch`(a) and (b) are the exception that proves the rule:
  they are complete labelled remarks of the manuscript, not fragments, and
  both halves of each are proved.

Under-advertising is the safe direction, and the surface is on that side.
Nothing on the list is a claim about the Millennium problem; taken together
the nine statements say that one dilation identity, its two consequences, one
scalar counterexample, one arithmetic inequality and one scalar ODE construction
are correct.

## Build status

`lake build` completes with zero errors: `Build completed successfully (3102
jobs)`. The only warnings are the nine intended
`declaration uses 'sorry'` in `Challenge.lean`. `Solution.lean` compiles with
no warning at all. Toolchain `leanprover/lean4:v4.33.1` and the pinned Mathlib
`v4.33.1` are untouched, as are `lakefile.toml`, `lake-manifest.json` and
everything under `NavierFormal/`.

## Adjacent work not done in this lane

Three files now describe the surface as a placeholder and are stale, but they
belong to the controller's integration step rather than to this lane:

- `formalization.yaml`: `status.scope` still reads "Skeleton only. The
  advertised statements have not yet been written", and `alignment.statements`
  is still `[]`.
- `docs/formalization-coverage.yaml`: `declarations` is still `[]` and
  `boundary.overall_status` is still `skeleton`.
- `docs/verification-status.md`: the sentence "`Challenge.lean` still carries
  only the labelled placeholder" is no longer true, and the axiom report for
  this integration is not yet recorded there.
