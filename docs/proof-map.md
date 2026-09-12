# Navier–Stokes formalization proof map

This compact map records the current dependency boundary; the live allocation
and paper status remain in `../navier/PLAN.md`.

```text
Challenge.lean
  └─ Solution.lean
       ├─ Phase-II pointwise/calculus and energy pieces
       ├─ Phase-I conditional bridge: NavierFormalConditional
       │    └─ Tao local theory + ESS input
       └─ paper terminal route
            └─ finite-horizon critical L³ producer [OPEN]
```

The nine `Challenge.lean` statements are deliberately interface placeholders;
`Solution.lean` proves the corresponding advertised declarations. This file
does not promote the conditional route or the paper-only critical estimate.
