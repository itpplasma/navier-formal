# Navier–Stokes formalization proof map

This compact map records the current dependency boundary; the live allocation
and paper status remain in `../navier/PLAN.md`.

```text
Challenge.lean
  └─ Solution.lean
       ├─ Phase-II pointwise/calculus and energy pieces
       ├─ HessianLaplacianL2.lean: integrated Hessian/Laplacian identity
       │    [explicit IBP package]
       │    └─ CompactSupportIBP/Adapter.lean: compact-support + C³ adapter
       │         [H²-to-pointwise-C³ bridge OPEN]
       ├─ Phase-I conditional bridge: NavierFormalConditional
       │    └─ Tao local theory + ESS input
       └─ paper terminal route
            └─ finite-horizon critical L³ producer [OPEN]
```

The nine `Challenge.lean` statements are deliberately interface placeholders;
`Solution.lean` proves the corresponding advertised declarations. This file
does not promote the conditional route or the paper-only critical estimate.
The integrated Hessian/Laplacian node is a checked draft boundary until the
pinned toolchain replay is available; its independent Gaussian oracle is
recorded in `research/check_hessian_laplacian_l2_oracle.py`. The compact-support
adapter supplies all seven explicit integrability fields under pointwise
`ContDiff ℝ 3` and `HasCompactSupport`; its independent bump oracle is
`research/compact_support_ibp_oracle.py`. It does not identify a generic
manuscript `H²` representative with a `C³` field.
