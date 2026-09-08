# Agent rules

This is the Lean 4 formalization of checkpoint CP1 of the private Navier–Stokes
programme. The live status is `../navier/PLAN.md`; never keep a second status
list here. The manuscript is `../navier-paper/main.tex`. Read
`docs/verification-status.md` and `docs/literature-assumptions.yaml` before
adding a theorem, axiom, or claim.

## Phases

Phase I: every manuscript-owned step is proved in Lean down to the literature
it cites. An axiom may remain only if it is a cited published theorem with a
verified direct-source record in `docs/literature-assumptions.yaml`, or an
assumption implied by such a theorem through a single trust-zero implication.
A construction the manuscript performs itself is never relabelled as a
literature axiom. Phase II: every remaining axiom is proved from Mathlib.
There is no third case, and Phase I is never a terminal state.

## Layout

`Challenge.lean` states the advertised results with Mathlib-only imports and
one `sorry` per advertised declaration. `Solution.lean` proves them.
`comparator.json` names the compared declarations and permits only
`propext`, `Quot.sound`, `Classical.choice`. `NavierFormal/` holds the
development; `NavierFormal/Literature/` holds literature axioms with source
records and nothing else. Application-independent analysis goes under a
generic namespace so that it can later move to a library.

## Working rules

- Toolchain and Mathlib are pinned (`lean-toolchain`, `lakefile.toml`) to
  `v4.34.0-rc2` / Mathlib `85e3a25e`, the pin of the external Solution-only
  dependency `openai/NavierStokesAndEuler@8937a8f4` (Apache-2.0). Do not bump
  them without the controller.
- Only modules under `NavierFormal/External/` may import the external
  package, `Challenge.lean` never does, and every imported declaration needs a
  statement-faithfulness row and an axiom report (`docs/external-openai-audit.md`,
  `docs/verification-status.md`). Imported forced-blowup facts are not unforced
  theorems.
- Parallel workers own disjoint files. Check a single file with
  `lake env lean NavierFormal/Foo.lean`; run `lake build` only when the
  controller integrates. Never run concurrent `lake build`s.
- Every new declaration has a docstring naming the manuscript label it
  formalizes. Every axiom has a source record. `#print axioms` output for the
  root exports is recorded in `docs/verification-status.md`.
- A zero-sorry file is not evidence that it formalizes the paper theorem;
  faithfulness is a separate audit recorded in
  `docs/paper-lean-specification.md`.
- Do not vendor Mathlib or copy external Lean code without its licence and
  attribution. Do not commit `.lake/`, oleans, or PDFs.
- Public since 2026-09-08 (Apache-2.0). No Palomar registration, submission, journal publication, or
  contact without the owner's explicit authorization. Signed commits only;
  do not bypass signing.


Publication note (2026-09-08): this repository and `itpplasma/navier` are
public; `navier-paper` stays private. No submission, Palomar registration or
outside contact is authorized by that change.
