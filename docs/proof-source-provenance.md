# Proof-source provenance

## Status boundary

This repository formalizes checkpoint CP1 and conditional continuation results from the Navier programme. The unrestricted unforced NS-R3 terminal theorem remains unproved in the research repository, with no unforced counterexample constructed.

## Authoritative upstream sources

Research/status repository: `itpplasma/navier`.

Read in this order:

1. `itpplasma/navier/PLAN.md` — sole live research status and terminal boundary;
2. `itpplasma/navier/paper/main.tex` — current manuscript proof record for the formalized checkpoint/conditional route;
3. this repository's `docs/paper-lean-specification.md` — manuscript-label to Lean correspondence;
4. this repository's `docs/verification-status.md` — checked formal boundary;
5. this repository's `docs/literature-assumptions.yaml` and `docs/external-openai-audit.md` — external theorem trust boundary.

Historical Navier plans and the archived `navier-paper` repository are not current proof specifications.

## Agent rule

Formalize only manuscript-owned CP1/conditional statements that are actually proved or explicitly reduced to cited literature. Do not interpret goal mode as an instruction to solve NS-R3. The arbitrary-data critical `L^3` producer remains a research-open input and must stay explicit. Forced-blowup results do not prove an unforced statement.