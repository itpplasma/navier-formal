# Navier–Stokes formalization proof map

This compact map records the current dependency boundary; the live allocation
and paper status remain in `../navier/PLAN.md`.

```text
Challenge.lean
  └─ Solution.lean
       ├─ Phase-II pointwise/calculus and energy pieces
       ├─ HessianLaplacianL2.lean: integrated Hessian/Laplacian identity
       │    [explicit IBP package; compact-support bridge OPEN]
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
recorded in `research/check_hessian_laplacian_l2_oracle.py`.
