# navier-formal

Lean 4 formalization of parts of a conditional argument for the
three-dimensional incompressible Navier-Stokes Cauchy problem on whole space.
The manuscript, research notes and plan live in the companion repository
[navier](https://github.com/itpplasma/navier).

Status: partial and conditional. Nothing here proves global regularity or
constructs a blow-up; the arbitrary-data critical `L³` bound is an explicit
hypothesis that nothing in either repository produces.

## What is formalized

- `Challenge.lean` / `Solution.lean`: nine statements from the manuscript's
  scaling and obstruction material (critical-dilation norm identities, the
  `L⁴`/`L³` interpolation mismatch, the scalar ODE obstruction), listed in
  `comparator.json`. `Challenge.lean` imports only Mathlib; three of the
  statements are proved there directly and six are left as intentional
  `sorry` placeholders, all nine are proved in `Solution.lean`, and the
  comparator permits only `propext`, `Quot.sound` and `Classical.choice`.
- `NavierFormal` (root library): the statement surface (operators, classical
  solution class, critical hypothesis, quotient objects), energy and
  enstrophy identities, integration by parts, interpolation inequalities and
  pressure lemmas, and a Hessian/Laplacian `L²` identity under explicit
  integration-by-parts hypotheses. It contains no `sorry` and no `axiom`
  declarations.
- `NavierFormalConditional` (separate library): `conditional_clay_A`
  (critical hypothesis implies Clay alternative A) and
  `conditional_clay_A_of_tao`. These depend on literature results stated as
  axioms in `NavierFormal/Literature/`: `localTheory`, `taoLocalTheory`,
  `endpointContinuation` and `essL3ToL5` (four axioms in total; each theorem
  uses two of them). Their sources are recorded in
  [docs/literature-assumptions.yaml](docs/literature-assumptions.yaml).

Modules under `NavierFormal/External/` import whole-space uniqueness and
related results from OpenAI's Apache-2.0 Lean development
[NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler); no
other module may import it. The imported modules are whole-space uniqueness,
an `L⁶` Sobolev bound and pressure recovery, not OpenAI's forced blow-up
theorem. See [docs/external-openai-audit.md](docs/external-openai-audit.md).

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain is
`leanprover/lean4:v4.34.0-rc2`; `lakefile.toml` pins Mathlib `v4.34.0-rc2`
and NavierStokesAndEuler at commit `8937a8f4`.

```sh
lake exe cache get
lake build
```

This builds `NavierFormal`, `NavierFormalConditional`, `Challenge` and
`Solution`. Axiom checks for individual declarations are in
`research/check_*.lean` (for example
`lake env lean research/check_conditional.lean`).

## Documentation

- [docs/verification-status.md](docs/verification-status.md): status of each
  manuscript result and recorded axiom reports.
- [docs/paper-lean-specification.md](docs/paper-lean-specification.md):
  manuscript definitions and claims versus Lean declarations.
- [docs/proof-map.md](docs/proof-map.md): dependency boundary of the current
  route.
- [docs/open-problems.md](docs/open-problems.md): the remaining formal and
  mathematical gaps.
- [docs/literature-assumptions.yaml](docs/literature-assumptions.yaml):
  literature axioms and their sources.

## License

Apache-2.0; see [LICENSE](LICENSE). No priority claim is made; the
manuscript, research notes and this formalization are parts of one project.
