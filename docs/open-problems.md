# Open problems

The only open input of the positive route is mathematical: the
finite-horizon critical `L³` bound (`hyp:critical` in the manuscript).
Nothing in this repository or in [navier](https://github.com/itpplasma/navier)
produces it. The formal gaps below are listed roughly in order of value.

1. **Hessian versus Laplacian.** `‖D²u‖₂ = ‖Δu‖₂` for compactly supported
   smooth `u` on `ℝ³` is proved in `NavierFormal/HessianLaplacianL2.lean`
   under an explicit integration-by-parts package.
   `CompactSupportIBP/Adapter.lean` derives that package from compact support
   and pointwise `C³`; `CompactSupportIBP/GradientInterpolation.lean` and
   `CompactSupportIBP/FiniteDimensionalNormBridge.lean` give the Jacobian
   Sobolev/interpolation step and the norm comparisons under the same
   hypotheses; `NavierFormal/HessianLaplacianEnstrophy.lean` and
   `NavierFormal/CompactSupportIBP/BoundedEnstrophyConsumer.lean` feed the result into the
   enstrophy inequality. Still missing: deriving pointwise `C³` and the
   integration-by-parts data from the manuscript's compact-support / `H²`
   hypotheses.
2. **Endpoint continuation.** Discharge the four explicit hypotheses of
   `endpointContinuation_of_ess` (uniform `L²` bound, identification of the
   abstract enstrophy with the gradient norm, `SerrinHypotheses`,
   interval-integral monotonicity) from `taoLocalTheory`, so that
   `conditional_clay_A` depends only on `taoLocalTheory` and `essL3ToL5`.
3. **Time regularity.** `lem:R-consequences`(a), the `L²` difference-quotient
   limit of `u` in time, from the regularity package alone. This needs a
   Bochner Taylor remainder with Minkowski's integral inequality; it is
   currently a clause of the `taoLocalTheory` axiom.
4. **Leray-Hopf class.** Formalize Leray-Hopf weak solutions so that
   `essL3ToL5` can be split into the published ESS theorem (Theorem 1.3)
   plus a proved `lem:leray-hopf`.
5. **Local theory.** Prove `taoLocalTheory` (local classical theory for
   Schwartz data). This is standard PDE theory absent from Mathlib, and
   large.
6. **Statement surface.** `IsClassicalSolution` carries no integrability
   class, so `CriticalBound` quantifies over a wider family than the
   manuscript's `hyp:critical`; the implication `hyp:critical → CriticalBound`
   needs uniqueness in that class.
