# External audit: `openai/NavierStokesAndEuler`

Audited clone: `/home/ert/proj/openai-NavierStokesAndEuler`, commit
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` (2026-09-08). Lean
`v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`. Read-only
audit; no build was run. All file:line references are to this clone unless
stated otherwise.

Scope note: this document evaluates *fitness for our unforced whole-space
programme* (Clay alternative (A) or an unforced counterexample). OpenAI's
result is the *forced* alternative (C)/(D); nothing here disputes the forced
result, only whether/how it can be reused.

---

## 1. Statement faithfulness

### 1.1 `ComparatorChallenges/NavierStokes.lean` vs the upstream Formal Conjectures file

`diff` between the upstream copy
(`/tmp/.../scratchpad/fc-NavierStokes.lean`, formal-conjectures commit
`8bf45ed70d48b2b2a501de9c00b26bfa38c573ee`) and
`ComparatorChallenges/NavierStokes.lean` (286 lines) produces a 151-line
diff, but it is entirely mechanical:

- Import changed `import FormalConjecturesUtil` → `import Mathlib`; all
  utility notation (`ℝ^n`, `ℝ³`, `∇⬝`) is inlined as `local notation`
  instead of imported.
- Namespace changed `NavierStokes` → `NavierStokes.Comparator`.
- All `@[category ..., AMS ...]` metadata attributes are stripped (cosmetic,
  formal-conjectures bookkeeping only).
- The module docstring is rewritten to explain the adaptation and drops the
  references to the Clay Institute PDF and to the errata discussion
  (paraphrased, not incorporated).
- **The two existence alternatives (A)
  `navier_stokes_existence_and_smoothness_R3` and (B)
  `navier_stokes_existence_and_smoothness_periodic` are deleted outright.**
  Only (C) `navier_stokes_breakdown_R3` and (D)
  `navier_stokes_breakdown_periodic` are kept — consistent with this being a
  breakdown-only comparator, but it means the file cannot be used as a
  Comparator target for alternative (A) at all; a positive existence
  challenge would need a separate reference statement.
- Every definition, structure, and hypothesis body (`divergence`,
  `IsOnePeriodic`, `InitialVelocityCondition(Decay/Periodic)`,
  `ForceCondition(Decay/Periodic)`, `NavierStokesExistenceAndSmoothness(Rn/Periodic)`)
  is copied **verbatim**, character-for-character except for the stripped
  attributes and the `local` qualifier on `notation`.
- The bodies of `navier_stokes_breakdown_R3` and `navier_stokes_breakdown_periodic`
  (statement text, not proof) are **verbatim** identical to upstream; only
  the attribute line above each and the enclosing namespace changed. The
  proofs are `sorry` in both files (upstream: intentional open-conjecture
  placeholder; here: intentional "comparator challenge" placeholder that the
  Solution side never imports — see §2).

Conclusion: the two breakdown theorem *statements* are verbatim transcriptions
of the Formal Conjectures statements, not restatements. No semantic drift was
introduced by OpenAI in the challenge file itself.

### 1.2 Reading of the definitions against Fefferman's alternative (C)

Fefferman's (C), as read in our manuscript: force $f$ smooth with all
derivatives decaying like $C/(1+|x|+t)^K$ for every $K$; **nonexistence** of
$u,p$ smooth on $\mathbb R^3\times[0,\infty)$ solving the forced equations
with **uniformly bounded energy** (Clay condition 7), for the stated
$u_0, f$.

The Lean structures do capture this reading component-by-component:

- `ForceConditionDecay.decay` (`ComparatorChallenges/NavierStokes.lean:185-191`):
  $\forall m,K,\exists C,\ \|\partial^m_{x,t}f(x,t)\| \le C/(1+\|x\|+t)^K$ for
  $t\ge0$ — matches Clay condition 5 exactly, including joint space-time
  derivative order $m$ (stronger than a fixed-order statement).
- `NavierStokesExistenceAndSmoothnessRn.globally_bounded_energy`
  (line 253): `∃ E, ∀ t ≥ 0, (∫ x, ‖v x t‖^2) < E` — this is Clay condition 7,
  a genuine Lebesgue integral (`MeasureTheory.integral`, real-valued, so it
  silently returns `0` if `v(·,t)` is not integrable — see caveat below).
- `navier_stokes_breakdown_R3` (line 273-277) is exactly "$\exists u_0,f$
  satisfying the decay/smoothness hypotheses such that **no** $(v,p)$
  satisfies `NavierStokesExistenceAndSmoothnessRn`" — the direct Lean
  negation of "(C) fails to hold for every candidate", i.e. exactly Fefferman's
  disjunct (C).

Points the Lean statement does **not** capture or leaves looser than a naive
reading of the manuscript's (C):

1. **The datum is not required to be zero.** `navier_stokes_breakdown_R3`
   existentially quantifies over `u₀ : ℝ³ → ℝ³` satisfying
   `InitialVelocityConditionDecay`; nothing forces `u₀ = 0`. The paper's
   claim ("forced blowup from zero datum") is *stronger* than what this
   theorem states — the theorem is compatible with, but does not assert,
   zero datum. (The *witness actually constructed* is zero — see §3.6 — but
   that is a fact about the proof, not about the statement.)
2. **`∫ x, ‖v x t‖^2` uses the plain (real-valued) Bochner/Lebesgue
   `integral`, not `lintegral`.** Mathlib's `∫` returns `0` for a
   non-integrable integrand. Combined with the separate hypothesis
   `integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2` (line 250), the intent is
   `MemLp` is required and *then* the numeric bound applies to a genuine
   finite integral — the two-field structure is not itself unsound, but
   an isolated reading of `globally_bounded_energy` without `integrable` in
   view would be too weak (any non-`L²` `v` could trivially satisfy
   `∫ = 0 < E`). Correct provided both fields of
   `NavierStokesExistenceAndSmoothnessRn` are used jointly, which they are
   in every proof site checked (§3).
3. **No pressure growth or pressure normalization is constrained** anywhere
   in `NavierStokesExistenceAndSmoothness` beyond `pressure_smooth :
   ContDiffOn ℝ ∞ (↿p) (univ ×ˢ Ici 0)` — matching the manuscript's own
   silence on pressure growth in (C) (Fefferman imposes none for the
   whole-space case either).
4. **The time derivative is `derivWithin … (Set.Ici 0)`, i.e. one-sided at
   $t=0$ and ordinary for $t>0$** (`ComparatorChallenges/NavierStokes.lean:223`,
   comment at lines 56-57) — consistent with the Clay closed half-line
   convention and with our own `NavierFormal.timeDeriv` (`SolutionClass.lean:80-83`),
   which uses the identical `derivWithin (Set.Ici 0)` convention.
5. **Pressure periodicity for (D):** the upstream/adapted file *does* include
   `isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)`
   (line 269) as the Clay errata requires; this is correctly retained.
6. **"No global smooth solution with uniformly bounded energy" is the right
   negation of (C)'s existence claim**, given the definitions above, *as a
   pointwise, non-quantified-over-competitors-with-different-decay
   statement* — there is no extra constraint (support, faster decay,
   pressure bound, weak-solution admissibility criterion) imposed on the
   hypothetical competitor `(v, p)` beyond smoothness, incompressibility,
   the same datum equation and finite/bounded energy, so the theorem is a
   strong ("beats every conceivable smooth finite-energy competitor")
   nonexistence claim, not a narrower one.

**Important separate finding — the paper-faithful statement is not what is
proved.** The repository additionally carries a much more literal
transcription of the paper's Theorem 1.1/1.1(R³) in
`NavierStokes/ProblemStatement.lean` and `NavierStokes/R3/ProblemStatement.lean`
(`candidateStatement`, `coreBreakdownStatement`, `breakdownStatement`; see
§3.1). These use zero datum by construction, a single compact spatial
support `K` uniform over the pre-singular interval, an explicit finite
blow-up time (`t = 1`), and (for R³) a `GlobalFiniteEnergySolution` structure
with *no* periodicity/support/pressure-growth assumption on the competitor —
closer to a textbook reading of Fefferman's (C). **`breakdownStatement` and
`coreBreakdownStatement` are never proved anywhere in the repository** (only
the trivial logical implication `breakdown_implies_core`, itself conditional
on `breakdownStatement`, exists — `NavierStokes/R3/ProblemStatement.lean:217-220`).
What *is* proved and exported (`navier_stokes_breakdown_R3` /
`_periodic`) is the Formal-Conjectures-style Comparator statement, which is
weaker in the sense of point 1 above (existential, not zero-forced) even
though its concrete witness is zero-datum. The formalization.yaml
"main_results" table (§2) lists only the Comparator-style theorems as
"proved"; it does not list `breakdownStatement`/`coreBreakdownStatement` at
all, so this gap is not mis-advertised, but a reader expecting the literal
paper statement to be the Lean-proved object should not assume so without
checking `ProblemStatement.lean` explicitly.

---

## 2. Axiom claims (self-assessed, not independently replicated here)

`formalization.yaml` (repo root) claims, for all four listed main results
(`navier_stokes_breakdown_R3`, `navier_stokes_breakdown_periodic`,
`Euler.euler_breakdown_R3`, `Euler.exists_compact_smooth_euler_singularity`):

```yaml
sorry_count: 0
axioms:
  - "propext"
  - "Classical.choice"
  - "Quot.sound"
```
(`formalization.yaml:47-89`), matching the `permitted_axioms` list in
`ComparatorChallenges/NavierStokes.json:8-12` and the trailing
`#print axioms` calls in `NavierStokes/ComparatorSolution.lean:31-32`. This
is a **self-assessment** ("review: status: self-assessed",
`formalization.yaml:100-101`); this audit did not run `lake build` or
`#print axioms` and does not confirm the claim. A separate local build is
reportedly in progress elsewhere; that build, not this document, is the
place to verify it.

### 2.1 Repo-wide search for soundness-relevant constructs (excluding `.lake/`)

| Construct | Count | Notes |
|---|---:|---|
| `axiom ` (declaration) | 0 | The 3 grep hits are all inside doc comments/strings, not declarations (`Euler/BaseInductionStageNoOptions.lean:24`, `NavierStokes/ProblemStatement.lean:8,117` — all prose about *not* using axioms). |
| `sorry` | 5 | All 5 are in the two Comparator **challenge** files, never in `Solution`/`R3`/`Euler` proof modules: `ComparatorChallenges/NavierStokes.lean:29` (doc comment), `:277`, `:284` (the two challenge theorem bodies); `ComparatorChallenges/Euler.lean:88`, `:184` (challenge theorem bodies). The formalization.yaml `sorry_count: 0` claim refers to the **Solution** modules, which is consistent with this grep — the challenge module's `sorry`s are intentional placeholders never imported by the proof (`NavierStokes/ComparatorSolution.lean:8`: "The adapters import `ComparatorDefinitions`, never the challenge module."). |
| `native_decide` | 0 | none found. |
| `decide` (tactic) | 201 | 40 in `NavierStokes/` (top level), 3 in `NavierStokes/R3/`, 39 in `Euler/`, remainder scattered; sampled ~12 at random (`NavierStokes/R3/CompactForceBound.lean:50`, `Euler/EulerProof.lean:15729,16667,17957,17971,17980`, `Euler/InviscidCorrectionUniqueness.lean:81`, `Euler/PacketReferenceRatio.lean:37`, `Euler/PacketKnownTermProfiles.lean:62`, `Euler/PacketPhysicalSign.lean:75`, `Euler/TerminalTimePrimitive.lean:330`, `NavierStokes/GrowingMode.lean:178`) — all are ordinary `Decidable`-instance closes of small numeric propositions (`2 ≠ 0`, `6 ≤ 40`, literal inequalities), not `native_decide` and not large kernel computations. |
| `unsafe` | 0 | none. |
| `implemented_by` | 0 | none. |
| `@[extern ...]` | 0 | none. |
| `opaque` | 0 (declarations) | 1 grep hit is prose in `NavierStokes/ParticularWaveBounds.lean:1582` ("keep the finite-path solver opaque"), not an `opaque` declaration. |
| `partial def` | 0 | none. |
| `set_option maxHeartbeats` / `maxRecDepth` | 0 | none found anywhere in the tree. |

File counts (excluding `.lake/`): 2486 `.lean` files total — `NavierStokes/`
top level 579, `NavierStokes/R3/` 64, `Euler/` top level 1839,
`ComparatorChallenges/` 2, plus 2 root aggregator files. Source size
excluding `.lake` is 44 MB (`du -sh --exclude=.lake .`); the full checkout
including the `.lake` package cache (Mathlib, Comparator, etc.) is 8.2 GB.

**Conclusion on axioms:** nothing in the tree outside the two intentional
comparator-challenge `sorry`s undermines the "0 sorries, 3 standard axioms"
self-assessment on a textual/grep basis. This is not a substitute for
actually building the project and running `#print axioms` on the two
exported theorems, which this audit did not do.

---

## 3. Reusable route-invariant infrastructure

### 3.1 `NavierStokes/ProblemStatement.lean` and `NavierStokes/R3/ProblemStatement.lean`

These are the **paper-faithful statement layer**, deliberately kept apart
from any proof (see §1.2). Both are pure statement/API modules with no
`sorry` and no axiom, but the top-level propositions they define
(`candidateStatement` in the periodic file, `breakdownStatement` /
`coreBreakdownStatement` in the R³ file) are only *conditionally* related to
each other, and only the periodic `candidateStatement` is actually proved
(as `NavierStokes.ActualCandidateAssembly.selected_candidate`, §3.6). Key
definitions (periodic, viscosity hard-wired to 1):

```lean
abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev SpaceTime := ℝ × Space              -- (t, x), time first
def temporalDerivative (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (fun s : ℝ => u (s, x)) t 1
def advection (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative u t x (u (t, x))
def navierStokesResidual (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) : Space :=
  temporalDerivative u t x + advection u t x - spatialLaplacian u t x +
    pressureGradient p t x
```
(`NavierStokes/ProblemStatement.lean:30-85`). Note: **ordinary `fderiv`**,
not `derivWithin`, and the equation is imposed only on the *open* interval
`Ioo 0 1` (`CandidateProperties.navier_stokes`, line 112-113); `t=0` is
handled separately by `zero_initial_velocity`. This differs from the
Comparator file's `derivWithin (Set.Ici 0)` convention (§1.2 point 4) — a
genuine, if benign, convention split *inside the same repository* between
the paper-faithful statement layer and the Clay-comparator statement layer.

R³ layer adds viscosity as a parameter, compact spatial support `K`, uniform
finite energy, and the "no competitor from the same zero datum"
`GlobalFiniteEnergySolution` structure (`NavierStokes/R3/ProblemStatement.lean:92-153`,
quoted in full in §1.2). Import closure: `NavierStokes.ProblemStatement`
pulls in 1 non-Mathlib module (itself); `NavierStokes.R3.ProblemStatement`
pulls in 2 (itself + the periodic `ProblemStatement`). Both are cheap to
import in isolation, but neither is where the actual theorems live.

### 3.2 `NavierStokes/PeriodicUniqueness.lean` / `NavierStokes/PeriodicIntegration.lean`

`PeriodicIntegration.lean` builds the unit-cube (`Icc 0 1` per coordinate,
pulled back through `EuclideanSpace.equiv`) integral, `cubeIntegral`, and
periodic integration-by-parts (`cubeIntegral_partial_eq_zero`,
`:123-172`) from Mathlib's box divergence theorem — this is intrinsically
**periodic/torus** machinery (it integrates over one fundamental domain);
it does not generalize to whole-space `ℝ³` integration and is not reusable
for an unforced whole-space route.

`PeriodicUniqueness.lean` defines `Comparison.slab`-style domains under its
own top-level `abbrev slab` (`NavierStokes/PeriodicUniqueness.lean:35`, used
by other periodic files) and proves the periodic classical-uniqueness chain,
culminating in:

```lean
theorem classical_uniqueness_on_Icc ... -- line 643
theorem candidate_unique_on_Icc {u p f K} (h : CandidateProperties 1 u p f) ... -- line 686
```
Both are hard-wired to viscosity 1 (via `CandidateProperties 1 u p f`, no
`ν` argument) and to the periodic torus (via `UnitSpatialPeriodsOn`
hypotheses baked into the `CandidateProperties` structure used). Not
directly usable for whole-space `ℝ³`.

### 3.3 Whole-space comparison, `NavierStokes/R3/`

`NavierStokesR3.Comparison.slab` (`NavierStokes/R3/ComparisonSetup.lean:22`):

```lean
abbrev slab (a b : ℝ) : Set SpaceTime := Icc a b ×ˢ univ   -- univ : Set Space
```
i.e. a genuine whole-space (non-compact spatial factor) time slab — this is
the R³-specific redefinition, distinct from (but same shape as) the periodic
`slab` in `PeriodicUniqueness.lean`.

**(a) `NavierStokes/R3/WholeSpaceUniqueness.lean`** — top comparison/uniqueness results:

```lean
theorem classical_uniqueness_on_Icc {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    ... -- (NavierStokes/R3/WholeSpaceUniqueness.lean:30-38, cont'd)
```

```lean
theorem candidate_unique_on_Icc {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties 1 u p f K)
    {T : ℝ} (hT : T < 1) {v : VelocityField} {q : PressureField}
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, navierStokesResidual 1 v q t x = f (t, x))
    (hvzero : ∀ x, v (0, x) = 0) : ...  -- (:72-80)
```

```lean
theorem candidate_global_agrees_before_one {u p f K}
    (h : CandidateProperties 1 u p f K)
    (v : GlobalFiniteEnergySolution 1 f) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v.velocity (t, x)  -- (:104-107)
```

**All three are hard-wired to `ν = 1`** (`CandidateProperties 1 …`,
`navierStokesResidual 1 …`). General viscosity is recovered elsewhere only
by the rescaling trick in `ComparatorR3Theorem.lean` (§3.6), which requires
the *reference* solution to be the specific constructed candidate, not an
arbitrary one. The critical hypothesis for `classical_uniqueness_on_Icc`
and `candidate_unique_on_Icc` is `hK : IsCompact K` +
`hsupp : … tsupport (fun x => u (t,x)) ⊆ K` on the **reference field `u`**
(the candidate), i.e. **the comparison technique requires the reference
solution to have compact spatial support at every time in the slab**; the
*competitor* `v`/`q` is only required to have finite energy, not compact
support. Import closure of `WholeSpaceUniqueness`: 67 non-Mathlib modules.

**(b) Energy, `NavierStokes/R3/CompactEnergy.lean`:**

```lean
theorem energy_balance {u f : VelocityField} {p : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = f (t, x)) :
    energyRate u t = -2 * dissipation u t + 2 * ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ
    -- (:202-209)
```

```lean
theorem hasDerivAt_energy_balance {a b t : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hp : ContDiffOn ℝ ∞ p (slab a b)) (hf : Continuous (fun x => f (t, x)))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K) (ht : t ∈ Ioo a b)
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = f (t, x)) :
    HasDerivAt (l2Sq u) (-2 * dissipation u t + 2 * ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) t
    -- (:323-333)
```

```lean
theorem uniform_finite_energy {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K)
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hinitial : ∀ x, u (0, x) = 0)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual u p t x = f (t, x)) :
    ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u
    -- (:343-352)
```

Every one of these **requires `HasCompactSupport`/`tsupport ⊆ K` on `u`
itself** (the field whose energy is being bounded), and requires a *compact*
force (`hcf : HasCompactSupport f`) for `uniform_finite_energy`. Viscosity is
implicitly 1 (`navierStokesResidual` here is the fixed-viscosity-1 version
from `ProblemStatement.lean`). Import closure: 8 non-Mathlib modules — very
cheap, but not usable for a non-compactly-supported field.

**(c) `NavierStokes/R3/PressureRecovery.lean`:**

```lean
structure Hypotheses (T : ℝ) (u v : VelocityField) (p q : PressureField) : Prop where
  positive : 0 < T
  smooth_u : ContDiffOn ℝ ∞ u (Comparison.slab 0 T)
  smooth_v : ContDiffOn ℝ ∞ v (Comparison.slab 0 T)
  smooth_p : ContDiffOn ℝ ∞ p (Comparison.slab 0 T)
  smooth_q : ContDiffOn ℝ ∞ q (Comparison.slab 0 T)
  div_u : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0
  div_v : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0
  equation : ∀ t ∈ Ioo 0 T, ∀ x,
    navierStokesResidual u p t x = navierStokesResidual v q t x
  energy_u : UniformFiniteEnergy (Icc 0 T) u
  energy_v : UniformFiniteEnergy (Icc 0 T) v
  -- (:33-44)

theorem pressure_gradient_recovery {T t u v p q}
    (hT : 0 < T) (hu ...) (hv ...) (hp ...) (hq ...)
    (hdivu ...) (hdivv ...) (hNS : ∀ s ∈ Ioo 0 T, ∀ x,
      navierStokesResidual u p s x = navierStokesResidual v q s x)
    (heu : UniformFiniteEnergy (Icc 0 T) u) (hev : UniformFiniteEnergy (Icc 0 T) v)
    (ht : t ∈ Ioo 0 T) {ψ : Space → ℝ} ... -- (:419-431)
```

Notably `Hypotheses` requires **only finite energy, not compact support**,
for both `u` and `v` — this is a genuinely whole-space, no-compact-support
pressure-recovery lemma (uses a compactly-supported *test function* `ψ`, not
compactly-supported fields). This is the most promising building block for
an unforced route with Schwartz (non-compactly-supported) data, since it
does not itself demand compact support of the physical fields. Import
closure: 36 non-Mathlib modules.

**(d) `NavierStokes/R3/SmoothSobolevL6.lean`:**

```lean
theorem smooth_eLpNorm_six_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) :
    eLpNorm f 6 volume ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume
    -- (:72-77)
```
Genuinely general (no support/periodicity assumption, only `C¹` and `L²`);
directly reusable Gagliardo–Nirenberg-type `H¹ ↪ L⁶` bound for any route.
Import closure: 7 non-Mathlib modules — cheap.

**(e) Riesz transform / heat kernel modules** (one line each, all under
`NavierStokes/R3/`):

| Module | Representative statement |
|---|---|
| `HeatKernel.lean` | `heatKernel_pos`, `hasFDerivAt_heatKernel` — pointwise positivity/differentiability of the ordinary heat kernel `heatKernel s z`. |
| `HeatKernelCancellation.lean` | Cutoff-difference bounds `cutoffSquareDifference_abs_le_lipschitz` for a comparison test cutoff. |
| `HeatKernelCommutator.lean` | `riesz_commutator_eq_heatKernel`, `riesz_commutator_pair_bound` — commutator of Riesz second-derivative operator with the heat semigroup expressed via the heat kernel. |
| `HeatKernelFourier.lean` | `fourierIntegral_gaussian_real`, `fourierIntegralInv_heatGaussian` — explicit Fourier transform of Gaussians/heat kernel. |
| `HeatKernelFubini.lean` | Fubini/measurability lemmas for time-integrated kernel convolutions (`cancelledTimeKernel_integral_swap`). |
| `HeatKernelPairedBound.lean` | `rieszCommutatorConstant_pos`, joint measurability of `heatKernelSecond`. |
| `HeatKernelTimeBound.lean` | `integral_inverseTimeGamma`, `integral_inverseTimeGamma_square_scale` — time-integral Gamma-function bounds for the kernel envelope. |
| `RieszHeatRepresentation.lean` | `integral_heatSecondSymbol`, `integral_norm_heatSecondSymbol` — Riesz transform symbol represented as an integral of the heat semigroup symbol. |
| `RieszL2Bounds.lean` | `norm_rieszTest_pairing_le`, `rieszTest_memLp_and_l2_bound` — $L^2$ boundedness of Riesz-transform test pairings (Calderón–Zygmund-type $L^2$ bound). |
| `RieszLinearityDecay.lean` | `rieszTest_add`, `rieszTestLinear` (a `LinearMap`) — the Riesz test map is linear. |
| `RieszPairing.lean` | `integral_fourierInv_mul`, `fourierInv_conj_apply` — Parseval-type pairing identities. |
| `RieszSymbolRegularity.lean` | `norm_rieszSymbol_le`, `measurable_rieszSymbol` — the Riesz multiplier symbol $\xi_i\xi_j/|\xi|^2$ is bounded and measurable. |
| `RieszTestOperators.lean` | `fourier_pderivTest`, `fderiv_fourierInv_apply` — derivative/Fourier commutation for the test operator. |

None of these Riesz/heat-kernel lemmas mention compact support or
periodicity in their statements as shown above — they are stated for
general Schwartz/`ComplexTest` test functions or general `Space → E`
functions, and are the most library-like, reusable pieces of the whole
tree (general Fourier-analytic facts about the Newtonian/heat kernel and
the Riesz transform on $\mathbb R^3$). They are, however, deeply
project-specific in *naming and packaging* (`ComplexTest`, `rieszTest`,
project-local Riesz-symbol conventions), not exposed as a standalone
library API, and each carries import weight from the surrounding
`NavierStokes.R3` namespace.

**(f) `WeakFourierUniqueness.lean`, `SchwartzCompactApproximation.lean`, `WholeSpaceEnergyLimit.lean`:**

- `WeakFourierUniqueness.lean:25-75` — `ae_eq_zero_of_integral_real_test_mul_eq_zero`,
  `ae_eq_zero_of_integral_schwartz_test_mul_eq_zero`,
  `eq_zero_of_integral_weight_normSq_test_eq_zero`: a.e.-uniqueness from
  vanishing pairing against all (real/Schwartz) test functions — general
  Fourier-uniqueness lemmas, no support assumption.
- `SchwartzCompactApproximation.lean:25-64` — `truncate` (compactly
  supported Schwartz approximant of a general Schwartz function),
  `truncate_hasCompactSupport`, `weighted_tail_le`,
  `uniform_cutoff_derivative_bound`: **this module explicitly approximates
  a general Schwartz function by a compactly-supported cutoff** — it is the
  one piece of infrastructure that is built exactly for turning
  non-compactly-supported (Schwartz) data into compactly-supported data for
  use with the compact-support-hungry comparison lemmas in (a)/(b). This is
  the natural entry point if one wanted to adapt the whole-space comparison
  technique to Schwartz (not already compact) data — but it only
  *approximates*, it does not remove the need for the reference/candidate
  solution `u` itself (not just the datum) to stay compactly supported for
  all `t` in the slab, which the heat/Navier–Stokes flow does not preserve
  (see §3.7).
- `WholeSpaceEnergyLimit.lean:25-70` — `eq_zero_of_l2Sq_eq_zero`,
  `eq_zero_of_radius_bound`, `eq_zero_of_weighted_rate_bound`: weighted-decay
  arguments forcing a field to vanish from an $L^2$ rate bound, general
  (`Continuous w`, no compact support required on `w` itself, though the
  weight/bound hypotheses effectively require decay).

### 3.4 Usability assessment

| Route | (i) Unforced positive route (classical solution, maximal branch) | (ii) Unforced counterexample verification ("this field is *the* solution and blows up") |
|---|---|---|
| `WholeSpaceUniqueness` (a) | Not directly: proves agreement of a *compactly-supported* candidate with any competitor, conditioned on the candidate already satisfying the PDE with a witness `f`; for an unforced (`f=0`) route the "candidate vs `f`" bridge collapses to comparing two solutions of the same *unforced* equation, which is a legitimate weak/strong-uniqueness statement, but only as long as the reference solution `u` in `hsupp` stays compactly supported — false for a generic evolving Schwartz flow (§3.7). | Not usable as-is for a Schwartz-datum candidate, for the same reason: `candidate_unique_on_Icc`/`classical_uniqueness_on_Icc` need `tsupport (u t) ⊆ K` for one fixed compact `K` over the whole slab. |
| `CompactEnergy` (b) | Same obstacle: `uniform_finite_energy` needs `HasCompactSupport (fun x => u (t,x))` via `hsupp`, and a compactly supported force; for `f = 0` the force hypothesis is trivially satisfiable, but the *velocity* compact-support hypothesis is not, for Schwartz data evolving under the heat semigroup. | Same. |
| `PressureRecovery` (c) | **Usable in principle** — `Hypotheses`/`pressure_gradient_recovery` require only `UniformFiniteEnergy`, not compact support, on both fields being compared. If an unforced route can establish finite energy directly (e.g. via a decay estimate) rather than via compact support, this pressure-recovery machinery transfers without modification. | Same — usable if finite energy (not compact support) can be shown directly for the candidate. |
| `SmoothSobolevL6` (d) | Yes, unconditionally reusable Sobolev embedding. | Yes. |
| Riesz/heat-kernel modules (e) | Yes for the underlying kernel/Fourier facts; would need re-derivation of the specific "residual ⇒ pressure formula" wiring, but the raw analytic facts (kernel positivity, Riesz symbol bounds, Parseval identities) transfer. | Yes, same caveat. |
| `WeakFourierUniqueness`, `WholeSpaceEnergyLimit` (f) | Yes, general. | Yes, general. |
| `SchwartzCompactApproximation` (f) | Partial: gives compactly-supported *approximants* of Schwartz data, but does not solve the problem that the *evolved* field is not compactly supported. | Same. |

### 3.5 The exact obstacle for our unforced use

`NavierStokes/R3CompactCandidate.lean:22-33` states the property bundle
actually driving the proved `navier_stokes_breakdown_R3`:

```lean
structure Properties (u : VelocityField) (p : PressureField) (f : VelocityField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  force_smooth : ContDiffOn ℝ ∞ f futureDomain
  velocity_support : ∃ K : Set Space, IsCompact K ∧
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0
  pressure_support : ∃ K : Set Space, IsCompact K ∧
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → p (t, x) = 0
  force_support : ∃ K : Set Space, IsCompact K ∧ CompactSpatialForceDecay.SupportedIn K f
  zero_initial_velocity : ∀ x, u (0, x) = 0
  force_time_support : CompactFutureTimeSupport f
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual u p t x = f (t, x)
  speed_unbounded : SpeedUnboundedAtOne u
```

The velocity and pressure of *the candidate solution itself* have compact
spatial support at **every** time in `[0,1)` (a single `K`), not merely the
initial datum. The comparison chain (`R3FiniteEnergyComparison.lean:37-49`,
`compact_candidate_excludes_global_solution`) relies on this to run the
whole-space comparison/Gronwall argument on a genuinely compact reference.

For our programme this is a hard obstacle, not a paperwork one: **an
unforced viscous flow started from nonzero Schwartz (rapidly-decaying, not
compactly-supported) or even compactly-supported data does not stay
compactly supported for any `t>0`** — the heat semigroup (and a fortiori
the full nonlinear Navier–Stokes flow) has infinite propagation speed, so
`u(t,\cdot)` is generically supported everywhere in $\mathbb R^3$ for all
`t>0` even if `u_0` were compact. OpenAI's construction sidesteps this only
because their candidate is *forced*: the compactly-supported forcing term
`f` (`CompactPositiveTimeSupport`, `R3/ProblemStatement.lean:66-67`) is used
to actively hold the solution inside a compact carrier by construction
(this is visible in the file names under top-level `NavierStokes/`:
`Actual*CarrierGeometry`, `Actual*CarrierTransport*`, i.e. the whole
"carrier" apparatus exists specifically to engineer compact spatial support
against the diffusive spreading, using the force as the mechanism). An
unforced flow has no such external control, so:

- The **compact-support-based** comparison/energy lemmas ((a), (b), and by
  extension `R3CompactCandidate`/`R3FiniteEnergyComparison`/
  `MaximalLifespan`) cannot be reused for an unforced Schwartz-datum
  candidate without first re-deriving finite-energy/uniqueness bounds that
  do not assume compact support of the *evolving* field — i.e., replacing
  every `HasCompactSupport`/`tsupport ⊆ K` hypothesis with a genuine `L²`
  (or weighted) decay estimate proved from the PDE itself.
- The **finite-energy-only** lemmas ((c) `PressureRecovery`, (d)
  `SmoothSobolevL6`, (f) `WeakFourierUniqueness`/`WholeSpaceEnergyLimit`,
  and the raw Fourier/Riesz facts in (e)) do not have this obstacle built
  in and are the credible reuse candidates, provided finite energy of the
  unforced candidate is established independently (which is itself
  non-trivial, but is a standard step, not a re-derivation of this whole
  repository's carrier machinery).

### 3.6 The actual (forced) proof chain, for context

`navier_stokes_breakdown_R3`/`_periodic` do **not** go through
`ProblemStatement.candidateStatement`/`breakdownStatement` directly; they go
through the Comparator adapters:

```lean
-- NavierStokes/ComparatorTheorem.lean:48-54 (periodic, option D)
theorem navier_stokes_breakdown_periodic (ν : ℝ) (hν : ν > 0) : ... := by
  obtain ⟨u, p, f, h⟩ := ActualCandidateAssembly.selected_candidate
  exact option_D_of_candidate h ν hν
```
```lean
-- NavierStokes/ComparatorR3Theorem.lean:36-42 (R³, option C)
theorem navier_stokes_breakdown_R3 (ν : ℝ) (hν : ν > 0) : ... := by
  obtain ⟨u, p, f, h⟩ := R3CompactCandidate.selected_compact_candidate
  exact option_C_of_compact_candidate h ν hν
```
`ActualCandidateAssembly.lean:1183` proves
`selected_candidate : ProblemStatement.candidateStatement` (the *periodic*
`candidateStatement`, which **is** proved, unlike the R³
`breakdownStatement`). Both `option_C_of_compact_candidate` and
`option_D_of_candidate` construct the witness with **zero initial
velocity** (`fun _ => 0` at `ComparatorTheorem.lean:38`,
`ComparatorR3Theorem.lean:30`) and a **rescaled version of the fixed
viscosity-1 candidate's force** (`rescaledForce ν f`) to handle arbitrary
`ν>0`. The "no competitor" step uses
`MaximalLifespan.candidate_excludes_global_solution` (periodic) /
`compact_candidate_excludes_global_solution` (R³), both of which take the
rescaled global solution, rescale it *back* to viscosity 1
(`normalized_solution`/`normalized_solution_Rn`), and hand it to the
viscosity-1 comparison lemmas of §3.3(a)/(b).

### 3.7 Import-closure sizes (static import-graph count, non-Mathlib modules only)

| Root module | Closure size |
|---|---:|
| `NavierStokes.ProblemStatement` (periodic) | 1 |
| `NavierStokes.R3.ProblemStatement` | 2 |
| `NavierStokes.R3.SmoothSobolevL6` | 7 |
| `NavierStokes.R3.CompactEnergy` | 8 |
| `NavierStokes.R3.PressureRecovery` | 36 |
| `NavierStokes.R3.WholeSpaceUniqueness` | 67 |
| `NavierStokes.ComparatorTheorem` | 509 |
| `NavierStokes.ComparatorR3Theorem` | 578 |
| `NavierStokes.ComparatorSolution` (the exported theorem file) | 580 |

`ComparatorSolution`'s closure (580 of the 579 top-level `NavierStokes/*`
files, i.e. essentially the *entire* `NavierStokes/` tree) means depending
on the proved theorems pulls in almost everything under `NavierStokes/`,
including the ~1000+ `Actual*` carrier/cycle/particular files that exist
purely to engineer the forced, compactly-supported blow-up profile and are
irrelevant to an unforced route. Depending only on the smaller, targeted
modules (`SmoothSobolevL6`, `PressureRecovery`, the Riesz/heat-kernel files,
`WeakFourierUniqueness`, `WholeSpaceEnergyLimit`) is feasible and cheap
(computed above), and does **not** require importing the 580-module
Comparator closure, since these targeted files sit low in the
`NavierStokes/R3/` import graph and do not depend on `ComparatorBridge`,
`ActualCandidateAssembly`, or the carrier files (independently confirmed:
the closures listed above for (c)/(d) do not include `ComparatorTheorem` or
`ActualCandidateAssembly` in their transitive import sets, by construction
of the closure computation, which only follows `import` lines actually
present in each file's own source).

---

## 4. Definitions dictionary

| OpenAI (`NavierStokes/ProblemStatement.lean` unless noted) | Our `NavierFormal` (unless noted) | Comparison |
|---|---|---|
| `Space := EuclideanSpace ℝ (Fin 3)` | `Space` (same Mathlib type, defined in our `Basic.lean`) | Identical. |
| `SpaceTime := ℝ × Space`, uncurried `u : SpaceTime → Space` | `u : ℝ → Space → Space`, curried | **Argument-order/currying difference.** Their velocity is a function of a pair `(t,x)`; ours is curried so `u t : Space → Space` is directly usable with `fderiv`/`Δ`/`eLpNorm`. Mathematically equivalent (`Function.uncurry`/`Function.curry`), but every lemma statement differs syntactically; no direct term-level reuse without an explicit bridge (which is exactly what `NavierStokes/ComparatorBridge.lean`'s `toComparator`/`fromComparator` do for *their own* two conventions — `ComparatorBridge.lean:19-23`). |
| `spatialDivergence u t x := ∑ i, (spatialDerivative u t x (coordinateVector i)) i` (`:67-68`); Comparator file's `divergence v x := (fderiv ℝ v x).trace ℝ (ℝ^n)` (`ComparatorChallenges/NavierStokes.lean:81`) | `divergence v x := ∑ i, ⟪e i, fderiv ℝ v x (e i)⟫` (`Calculus.lean:179-180`) | Same quantity (`∑ᵢ ∂ᵢvᵢ`), three encodings across the two repos (`trace`, `∑ component`, `∑ inner`) — all provably equal for finite-dim Euclidean space but not defeq; a shared route would need a bridge lemma either way. |
| `advection u t x := spatialDerivative u t x (u (t, x))` (`:63-64`) | `convection v x := fderiv ℝ v x (v x)` (`Calculus.lean:222`), applied as `convection (u t) x` | Same object `(v·∇)v`; naming differs (`advection` vs `convection`) — cosmetic. Theirs takes `(t,x)` and looks up `u (t,x)` inside `SpaceTime → Space`; ours takes the pre-sliced `v = u t : Space → Space`. |
| `navierStokesResidual u p t x := temporalDerivative u t x + advection u t x - spatialLaplacian u t x + pressureGradient p t x` (`:82-85`, viscosity 1); R³ version multiplies the Laplacian term by `ν` (`NavierStokes/R3/ProblemStatement.lean:57-62`) | No explicit "residual"; the PDE is written directly as an equation `timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x` (`SolutionClass.lean:210-211`) | **Algebraically identical PDE and sign convention** once rearranged: their `residual = f` reads `∂ₜu+(u·∇)u-νΔu+∇p=f`; ours (unforced, `f=0`) reads `∂ₜu+(u·∇)u+∇p=νΔu`, i.e. `∂ₜu+(u·∇)u+∇p-νΔu=0` — the same equation. No sign discrepancy. |
| `UniformFiniteEnergy (times) (u) := ∃ E, 0 ≤ E ∧ ∀ t ∈ times, SquareIntegrableAtTime u t ∧ kineticEnergy u t ≤ E` (`R3/ProblemStatement.lean:81-83`), with `kineticEnergy u t := (1/2) * ∫ x, ‖u (t,x)‖^2` (real Bochner integral, `:76-77`) | `kineticEnergyLintegral v := ∫⁻ x, ‖v x‖ₑ^2` (`Calculus.lean:274`), an `ℝ≥0∞`-valued Lebesgue integral, and `ClayAlternativeA`'s energy clause `∃ C, ∀ t ≥ 0, ∫⁻ x, ‖u t x‖ₑ^2 ≤ ENNReal.ofReal C` (`SolutionClass.lean:264`) | **Encoding difference with a soundness note.** Theirs uses the *real-valued* Mathlib `∫` plus a separate explicit `MemLp`/`SquareIntegrableAtTime` conjunct (so the real integral cannot silently read `0` for a non-`L²` field without also failing the `MemLp` conjunct). Ours uses the extended-real `∫⁻` (`lintegral`) throughout specifically so that "energy is bounded" cannot be vacuously true for a field outside `L²` (documented rationale at `SolutionClass.lean:118-120`, "never `.toReal` of a possibly infinite quantity"). Functionally equivalent as long as their `MemLp` conjunct is always used alongside the real integral (checked true at every proof site inspected in §3), but ours is the more defensive encoding by construction. |
| `SpeedUnboundedAtOne u := ∀ M>0, ∀ δ>0, ∃ t ∈ (0,1), 1-δ<t ∧ M<‖u(t,x)‖` (`ProblemStatement.lean:94-96`) | No direct analogue (our programme targets global existence/counterexample, not a fixed blow-up time `t=1`); closest structural analogue would be a negation of `RegularityPackage`/`IsClassicalSolution.mono`'s maximal-time extension, not currently named. | Not directly transferable; theirs is specific to the paper's normalized blow-up time `t=1` on `[0,1)`, an artifact of their rescaling convention, not a general "blows up somewhere" predicate. |
| `CandidateProperties` (`ProblemStatement.lean:101-114`, periodic; `R3CompactCandidate.Properties`, `R3/ProblemStatement.lean:92-109`, whole-space) | `IsClassicalSolution ν u₀ T u p` (`SolutionClass.lean:186-211`) | Structurally analogous role (bundle of smoothness + incompressibility + PDE + initial data), but theirs additionally bundles the eventual blow-up/support/decay conditions specific to their construction; ours is a bare local-solution predicate with no maximality or blow-up condition built in — cleanly separable, which is the right shape for reuse in either a positive-existence or counterexample role. |
| `GlobalFiniteEnergySolution ν f` (`R3/ProblemStatement.lean:125-135`) | `ClayAlternativeA ν u₀` (`SolutionClass.lean:257-266`, existential form) | Same role (the "no competitor" / "the positive alternative" object) but opposite polarity: theirs is a structure bundling one specific hypothetical competitor (used inside a `¬ Nonempty (...)` claim); ours is a `Prop` bundling existence of `u,p` directly. Trivial to inter-convert (`Nonempty S ↔ (∃ ..., S-fields)` is exactly `S.mk`/projection), not yet done since the two are never on the same proof site. |
| `Comparison.slab a b := Icc a b ×ˢ univ` — two independent definitions, `NavierStokes.PeriodicUniqueness.slab` (periodic torus context, `PeriodicUniqueness.lean:35`) and `NavierStokesR3.Comparison.slab` (whole space, `R3/ComparisonSetup.lean:22`) | No named `slab`; our closed/open-slab domains are written inline as `Set.Ico 0 T ×ˢ Set.univ` / `Set.Ioo 0 T ×ˢ Set.univ` in `IsClassicalSolution` (`SolutionClass.lean:190-191`,`:195`) | Same shape (`Set` product of a time interval with `univ : Set Space`), unnamed on our side; trivial to name if reused. |
| `derivWithin (v x ·) (Set.Ici 0) t` (Comparator file only, `ComparatorChallenges/NavierStokes.lean:223`) vs plain `fderiv ℝ (fun s => u (s,x)) t 1` (paper-faithful `ProblemStatement.lean:56`, only on the open interval) | `timeDeriv u t x := derivWithin (fun s => u s x) (Set.Ici 0) t` (`SolutionClass.lean:80-83`), used at all `t ≥ 0` including `t=0` | Our convention matches OpenAI's *Comparator*-file convention exactly (`derivWithin … (Set.Ici 0)`), not their paper-faithful `ProblemStatement.lean` convention (which uses ordinary `fderiv` and never touches `t=0` inside the PDE clause). If depending on OpenAI modules, the `PressureRecovery`/`WholeSpaceUniqueness`/`CompactEnergy` lemmas (§3.3) are written against the `ProblemStatement.lean` convention (plain `fderiv`, open-interval only), which is *closer* to a possible bridge with ours than the Comparator file's `derivWithin` convention is — a detail worth remembering when wiring anything together. |
| `Δ`/Laplacian: `spatialLaplacian u t x := ∑ i, fderiv ℝ (fun y => spatialDerivative u t y (coordinateVector i)) x (coordinateVector i)` (`ProblemStatement.lean:76-79`, hand-rolled second-derivative sum) | `Δ` = Mathlib's `InnerProductSpace` Laplacian (trace of the second Fréchet derivative), via `open scoped Laplacian` (`SolutionClass.lean:65-66`) | Same mathematical operator (`∑ᵢ ∂ᵢ²`), but theirs is a from-scratch iterated-`fderiv` sum while ours is Mathlib's library `Δ`. A bridge lemma (`Δ = spatialLaplacian`, provable but not present in either repo) would be needed for any shared statement. |

---

## 5. Palomar / licence compatibility summary

| Item | Finding |
|---|---|
| Licence | Apache License 2.0, `LICENSE` (root) — same licence family as the upstream Formal Conjectures file it adapts, and Apache-2.0 is generally compatible with reuse in another Apache/MIT-family project provided attribution/NOTICE terms are kept; the adapted comparator file already carries a "modified from its original form" notice (`ComparatorChallenges/NavierStokes.lean:4-5`), which is the correct pattern to imitate if we vendor or reference anything. |
| Toolchain pin | `lean-toolchain`: `leanprover/lean4:v4.34.0-rc2` (exact match to what was told in context). |
| Mathlib pin | `lakefile.toml` requires `mathlib` at `rev = "v4.34.0-rc2"`; `lake-manifest.json` resolves it to commit `85e3a25e006c35636f0e53b0e9296caca2685bc0` — matches the commit given in the task context. |
| Repo size | Source excluding `.lake`: 44 MB, 2486 `.lean` files (579 `NavierStokes/` top level, 64 `NavierStokes/R3/`, 1839 `Euler/`, 2 `ComparatorChallenges/`). Full checkout with `.lake` package cache (Mathlib et al.): 8.2 GB. |
| Challenge imports only Mathlib | Yes for `ComparatorChallenges/NavierStokes.lean` — `import Mathlib` only (line 20), confirmed by `diff` against upstream and by direct grep of the file's import block; the module docstring itself asserts "only Mathlib is imported" and "Neither the proof root nor the submission imports this reference" (`:31-32`), consistent with what we observed for the Solution side (`ComparatorSolution.lean` imports only `ComparatorR3Theorem`/`ComparatorTheorem`, never `ComparatorChallenges.*`). |
| Comparator/lean4export transitive deps | `lakefile.toml` has a **direct** `[[require]] name = "Comparator" git = "https://github.com/leanprover/comparator.git" rev = "v4.34.0-rc2"` (root lakefile). `lake-manifest.json` additionally resolves `lean4export` (commit `cacf989b...`) as a transitive package (pulled in by `Comparator`, used by its axiom-export/checking machinery per the acknowledgements section of `formalization.yaml`). **If we take a pinned dependency on this repo's `Solution`-side modules for our Palomar-style setup, `Comparator` and `lean4export` become transitive dependencies of our build too**, even though our own `Challenge.lean` would never import them (matching the Palomar rule that `Challenge.lean` imports only Mathlib — the transitive pull-in would sit entirely on the Solution side, same as it does for OpenAI). This is a real but bounded increase in our dependency surface, not a licence or axiom problem (`Comparator`/`lean4export` are leanprover-org tooling, not extra proof content, and are not on the axiom-permission list because they are not imported by anything that produces a term — they are the *checking* tool, not proof infrastructure). |
| Concerns | (1) The 580-module import closure of the actually-exported theorems (§3.7) means a naive "depend on `NavierStokes.ComparatorSolution`" pull-in would import almost the entire forced-blowup carrier machinery, most of it irrelevant to an unforced route — prefer depending on the narrow modules identified in §3.3(c)/(d)/(e)/(f) instead. (2) The paper-faithful `breakdownStatement`/`coreBreakdownStatement` (§1.2, §3.1) are **not proved** in this repository; do not cite this repository as having formally verified the literal textbook reading of Theorem 1.1 without checking which of the two statement layers (Comparator-style vs `ProblemStatement`-style) is meant. (3) This audit is textual/static only; it does not replace an independent `lake build` + `#print axioms` verification of the self-assessed axiom claim in `formalization.yaml`. |

---

## Summary of file locations referenced

- Challenge (adapted comparator): `/home/ert/proj/openai-NavierStokesAndEuler/ComparatorChallenges/NavierStokes.lean`
- Upstream original (for diff): `/tmp/claude-1000/-home-ert-proj-navier/e3e4d7f7-0e11-4d8c-a55c-18aafe035a2c/scratchpad/fc-NavierStokes.lean`
- Solution adapters: `NavierStokes/ComparatorSolution.lean`, `NavierStokes/ComparatorTheorem.lean`, `NavierStokes/ComparatorR3Theorem.lean`, `NavierStokes/ComparatorBridge.lean`, `NavierStokes/ComparatorR3Bridge.lean`, `NavierStokes/ComparatorDefinitions.lean`
- Paper-faithful (unproved-for-R³) statement layer: `NavierStokes/ProblemStatement.lean`, `NavierStokes/R3/ProblemStatement.lean`
- Periodic route-invariant infrastructure: `NavierStokes/PeriodicUniqueness.lean`, `NavierStokes/PeriodicIntegration.lean`
- Whole-space route-invariant infrastructure: `NavierStokes/R3/*.lean` (64 files; key ones cited above)
- Metadata: `formalization.yaml`, `ComparatorChallenges/NavierStokes.json`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `LICENSE`
- Our own conventions compared against: `/home/ert/proj/navier-formal/NavierFormal/SolutionClass.lean`, `/home/ert/proj/navier-formal/NavierFormal/Calculus.lean`, `/home/ert/proj/navier-formal/AGENTS.md`
