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
       │         └─ CompactSupportIBP/GradientInterpolation.lean: Jacobian
       │              Sobolev/interpolation consumer [explicit C³ package]
       │              └─ CompactSupportIBP/FiniteDimensionalNormBridge.lean:
       │                   eLpNorm operator/Frobenius comparison [explicit package]
       │                   └─ HessianLaplacianEnstrophy.lean: exact `ha2`
       │                        bookkeeping consumer [explicit IBP package]
       │                        └─ BoundedEnstrophyConsumer.lean: bounded
       │                             explicit-data composition
       │              [H²-to-pointwise-C³ and critical L³ producer OPEN]
       ├─ Phase-I conditional bridge: NavierFormalConditional
       │    └─ Tao local theory + ESS input
       └─ paper terminal route
            └─ finite-horizon critical L³ producer [OPEN]
```

The nine `Challenge.lean` statements are the advertised interface; six remain
deliberate placeholders while `L4L3_supercritical` and
`integral_scalar_obstruction` and `scalar_obstruction_exists` are now proved directly. `Solution.lean` proves the
corresponding advertised declarations. This file
does not promote the conditional route or the paper-only critical estimate.
The integrated Hessian/Laplacian node replayed successfully against the pinned
toolchain under explicit packages; its independent Gaussian oracle is
recorded in `research/check_hessian_laplacian_l2_oracle.py`. The compact-support
adapter supplies all seven explicit integrability fields under pointwise
`ContDiff ℝ 3` and `HasCompactSupport`; its independent bump oracle is
`research/compact_support_ibp_oracle.py`. The new
`CompactSupportIBP/GradientInterpolation.lean` consumes the same package to
prove the operator-norm Sobolev/interpolation step, with
`research/gradient_interpolation_oracle.py` as an independent numerical check.
`CompactSupportIBP/FiniteDimensionalNormBridge.lean` lifts the existing
pointwise operator/Frobenius inequalities to eLpNorms and supplies the
Jacobian specialization; `research/finite_dimensional_norm_bridge_oracle.py`
is its independent exact check.
The 2026-09-12 Sol repair corrected the Sobolev domain dimension from `9` to
`3`; Astra review found no further source-level repair without the pinned
cache. The paper bridge remains open because generic `H²` does not imply
pointwise `C³`, compact support requires a cutoff/limit argument, and the
Hessian/Frobenius-to-Laplacian norm and integral comparison is now composed
into the exact `ha2` consumer by `HessianLaplacianEnstrophy.lean`, still under
the explicit IBP package; the manuscript H²-to-C³/IBP bridge remains open.
Neither file identifies a generic manuscript `H²` representative with a `C³`
field or with the manuscript's Frobenius norm convention.

`CompactSupportIBP/BoundedEnstrophyConsumer.lean` is the checked bounded
composition of these interfaces. Its result record keeps the exact `ha2`, the
operator-norm Jacobian interpolation estimate, and the Jacobian
operator/Frobenius eLpNorm comparisons separate; it does not identify the
second-derivative operator norm with `hessianFrobeniusSq` or produce critical
`L³` control.
