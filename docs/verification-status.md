# Verification status

Reader-facing status has three values:

- **Paper only:** the manuscript contains the proof, but Phase I is open.
- **Phase I complete:** Lean reaches a checked literature theorem, but that
  theorem has not yet been proved from Mathlib.
- **Phase II complete:** Lean proves the claim from Mathlib.

Current state: skeleton. No CP1 statement has been written in Lean yet. The
only declaration is a labelled placeholder that keeps the Palomar layout
building. The machine-readable boundary is `formalization-coverage.yaml`;
literature inputs are in `literature-assumptions.yaml`.

| Manuscript label | Lean declaration | Status |
| --- | --- | --- |
| `prop:energy` | — | paper only |
| `prop:scaling` | — | paper only |
| `prop:enstrophy` | — | paper only |
| `prop:ode` | — | paper only |
| `prop:pressure` | — | paper only |
| `prop:lowpressure` | — | paper only |
| `thm:continuation` | — | paper only (imports ESS/GKP) |
| `thm:conditional` | — | paper only (conditional on `hyp:critical`) |
| `sec:quotient` results | — | paper only (HF17, audited) |

Axiom reports are recorded here after each integration; none yet.
