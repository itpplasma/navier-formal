import NavierFormal.SolutionClass
import NavierStokes.R3.WholeSpaceUniqueness
import NavierStokes.R3.SmoothSobolevL6
import NavierStokes.R3.PressureRecovery

/-!
# Adapter to OpenAI's `NavierStokesAndEuler` whole-space uniqueness (PLAN FC6)

This module is the sole importer, in this repository, of the external Apache-2.0
package `openai/NavierStokesAndEuler` (commit
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`), pinned Solution-only in
`lakefile.toml`. It bridges our curried classical-solution predicate
`NavierFormal.IsClassicalSolution` (`NavierFormal/SolutionClass.lean`) to that
package's uncurried spacetime fields and its whole-space finite-energy
comparison theorem `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`,
following the dictionary of `docs/external-openai-audit.md` §§3–4.

## The obstacle this adapter documents rather than solves (audit §3.5, §3.7)

`classical_uniqueness_on_Icc` requires the *reference* field `u` to have one
compact spatial support `K` throughout the closed time interval `[0,T']`. An
unforced viscous flow started from nonzero (Schwartz or even compactly
supported) data does **not** stay compactly supported for any `t > 0`: the
heat semigroup, and a fortiori the full nonlinear flow, has infinite
propagation speed. So `classical_uniqueness_of_compact_support` below applies
only to an `[OA]`-type candidate that is *already* known to be compactly
supported at every time in `[0,T']` (e.g. a hypothetical compactly supported
classical solution, not a generic Schwartz-data flow); it is not, by itself,
a uniqueness theorem for the manuscript's Schwartz-datum classical solutions.

## Sign and time conventions (audit §1.2, §4)

The external package's `navierStokesResidual ν u p t x` is
`∂ₜu + (u·∇)u - ν·Δu + ∇p` (their `NavierStokes/R3/ProblemStatement.lean:57-62`,
viscosity multiplying only the Laplacian term); the residual equation
`navierStokesResidual ν u p = f` for `f = 0` (the unforced case) reads
`∂ₜu + (u·∇)u + ∇p = νΔu`, algebraically identical to our
`NavierFormal.IsClassicalSolution.momentum`, with **no sign discrepancy**.
Their time derivative on the paper-faithful `ProblemStatement.lean` layer used
here is the *ordinary* `fderiv`/`deriv`, imposed only at interior times
`0 < t < T` (never at `t = 0`); this matches `NavierFormal.timeDeriv` for
`t > 0` via `NavierFormal.timeDeriv_eq_deriv`, since `NavierFormal.timeDeriv`
is `derivWithin (Set.Ici 0)` which coincides with the ordinary derivative away
from `t = 0`.

## Smoothness gap (audit item 2 of the task)

`NavierFormal.IsClassicalSolution.smooth_u` gives joint `ContDiffOn ℝ ∞` on the
*open* slab `Set.Ioo 0 T ×ˢ Set.univ`, jointly in `(t, x)` (time first, matching
this package's `SpaceTime := ℝ × Space` convention). The comparison theorem
needs `ContDiffOn ℝ ∞ _ (Comparison.slab 0 T')` where
`Comparison.slab a b = Set.Icc a b ×ˢ Set.univ`, i.e. smoothness up to *both*
endpoints `t = 0` and `t = T'`. `IsClassicalSolution` gives only continuity
(not smoothness) at `t = 0`, so this is genuinely not derivable from it: the
adapter theorems below take the slab smoothness as an explicit extra
hypothesis `hsmooth`, which a classical solution with the manuscript's
one-sided smoothness at `t = 0` (`lem:global-smooth`, `prop:localtheory`(iii))
would supply, but which `NavierFormal.IsClassicalSolution` does not.
-/

noncomputable section

namespace NavierFormal.External

open NavierFormal MeasureTheory
open scoped ENNReal ContDiff Gradient Laplacian

/-! ## Spacetime currying -/

/-- Uncurry a time-dependent field `u : ℝ → Space → F` to the spacetime field
`ℝ × Space → F` used throughout `NavierStokes.ProblemStatement` (their
`SpaceTime := ℝ × Space`, time first, matching our convention). Used for both
velocity (`F = Space`) and pressure (`F = ℝ`) fields. -/
def toSpacetime {F : Type*} (u : ℝ → Space → F) : ℝ × Space → F := fun q => u q.1 q.2

/-- Curry a spacetime field back to a time-dependent field; the inverse of
`toSpacetime`. -/
def ofSpacetime {F : Type*} (U : ℝ × Space → F) : ℝ → Space → F := fun t x => U (t, x)

/-- `ofSpacetime` is a left inverse of `toSpacetime`. -/
theorem ofSpacetime_toSpacetime {F : Type*} (u : ℝ → Space → F) :
    ofSpacetime (toSpacetime u) = u := rfl

/-- `toSpacetime` is a left inverse of `ofSpacetime`. -/
theorem toSpacetime_ofSpacetime {F : Type*} (U : ℝ × Space → F) :
    toSpacetime (ofSpacetime U) = U := rfl

/-! ## Pointwise dictionary between the two conventions (audit §4) -/

/-- Their standard coordinate vector is our standard basis vector: both are
`EuclideanSpace.single i 1`. -/
theorem coordinateVector_eq_e (i : Fin 3) :
    NavierStokes.ProblemStatement.coordinateVector i = e i := rfl

/-- Their spatial Fréchet derivative of a spacetime-uncurried field at fixed
time is our `fderiv` of the curried time-slice. -/
theorem spatialDerivative_toSpacetime (u : ℝ → Space → Space) (t : ℝ) (x : Space) :
    NavierStokes.ProblemStatement.spatialDerivative (toSpacetime u) t x
      = fderiv ℝ (u t) x := rfl

/-- Their advection term `(u·∇)u` at a spacetime point is our `convection` of
the curried time-slice. -/
theorem advection_toSpacetime (u : ℝ → Space → Space) (t : ℝ) (x : Space) :
    NavierStokes.ProblemStatement.advection (toSpacetime u) t x
      = NavierFormal.convection (u t) x := rfl

/-- Their Euclidean divergence of a spacetime-uncurried field at fixed time is
our `divergence` of the curried time-slice. -/
theorem spatialDivergence_toSpacetime (u : ℝ → Space → Space) (t : ℝ) (x : Space) :
    NavierStokes.ProblemStatement.spatialDivergence (toSpacetime u) t x
      = NavierFormal.divergence (u t) x := by
  rw [NavierStokes.ProblemStatement.spatialDivergence, NavierFormal.divergence_eq_sum_component]
  simp only [spatialDerivative_toSpacetime, coordinateVector_eq_e]

/-- Their Euclidean pressure gradient of a spacetime-uncurried field at fixed
time is Mathlib's `gradient` of the curried time-slice, our `∇`. -/
theorem pressureGradient_toSpacetime (p : ℝ → Space → ℝ) (t : ℝ) (x : Space) :
    NavierStokes.ProblemStatement.pressureGradient (toSpacetime p) t x
      = ∇ (p t) x := by
  rw [NavierStokes.ProblemStatement.pressureGradient]
  have hterm : ∀ i : Fin 3,
      (fderiv ℝ (fun y : Space => (toSpacetime p) (t, y)) x
          (NavierStokes.ProblemStatement.coordinateVector i))
        • NavierStokes.ProblemStatement.coordinateVector i
      = (∇ (p t) x i) • e i := by
    intro i
    rw [coordinateVector_eq_e]
    congr 1
    exact (NavierFormal.gradient_component (p t) x i).symm
  simp only [hterm]
  exact NavierFormal.sum_smul_e (∇ (p t) x)

/-- Their ordinary time derivative of a spacetime-uncurried field at a positive
time is our `timeDeriv` of the curried field: both are `deriv (fun s => u s x) t`.
Restricted to `t > 0` because `timeDeriv` uses the one-sided derivative within
`Set.Ici 0` at `t = 0`, which their ordinary `fderiv`-based definition does not
match there (audit §4, row on `derivWithin`). -/
theorem temporalDerivative_toSpacetime {u : ℝ → Space → Space} {t : ℝ} (ht : 0 < t)
    (x : Space) :
    NavierStokes.ProblemStatement.temporalDerivative (toSpacetime u) t x
      = NavierFormal.timeDeriv u t x := by
  rw [NavierFormal.timeDeriv_eq_deriv ht x]
  rfl

/-! ## The Laplacian bridge

Their `spatialLaplacian` is a hand-rolled sum of iterated directional
derivatives; our `Δ` is Mathlib's `InnerProductSpace` Laplacian, the trace of
the second Fréchet derivative in an orthonormal basis
(`NavierFormal.laplacian_eq_sum_iteratedFDeriv`). The two coincide at points
where the field is twice differentiable; we record this under the pointwise
smoothness a classical solution provides at interior times. -/

/-- A `C^∞` (in particular `C^2`) field has a differentiable derivative map. -/
private theorem differentiableAt_fderiv_of_contDiffAt {v : Space → Space} {x : Space}
    (hv : ContDiffAt ℝ ∞ v x) : DifferentiableAt ℝ (fderiv ℝ v) x := by
  have h2 : (1 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by norm_num
  exact (hv.fderiv_right h2).differentiableAt (by norm_num)

/-- Second-order chain rule for evaluation at a fixed vector: the derivative of
`y ↦ (fderiv v y) c` at `x`, applied to `c`, is the doubly-iterated derivative
`(fderiv (fderiv v) x) c c`. -/
private theorem fderiv_apply_const_apply_eq {v : Space → Space} {x c : Space}
    (hv : DifferentiableAt ℝ (fderiv ℝ v) x) :
    fderiv ℝ (fun y => fderiv ℝ v y c) x c = fderiv ℝ (fderiv ℝ v) x c c := by
  have h := hv.hasFDerivAt.clm_apply (hasFDerivAt_const c x)
  have hfd := h.fderiv
  rw [hfd]
  simp

/-- The doubly-iterated directional derivative at a repeated direction `e i` is
the Mathlib second iterated Fréchet derivative in that direction, at a point
where the field is `C^∞`. -/
private theorem fderiv_fderiv_apply_eq_iteratedFDeriv {v : Space → Space} {x : Space}
    (hv : ContDiffAt ℝ ∞ v x) (i : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ v y (e i)) x (e i) = iteratedFDeriv ℝ 2 v x ![e i, e i] := by
  rw [fderiv_apply_const_apply_eq (differentiableAt_fderiv_of_contDiffAt hv)]
  have := bilinearIteratedFDerivTwo_eq_iteratedFDeriv (𝕜 := ℝ) v x (e i) (e i)
  simpa [bilinearIteratedFDerivTwo] using this

/-- Their Euclidean Laplacian of a spacetime-uncurried field at fixed time is
Mathlib's `Δ` of the curried time-slice, at a point where the time-slice is
`C^∞` (as it is at every interior time of a classical solution). -/
theorem spatialLaplacian_toSpacetime {u : ℝ → Space → Space} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ ∞ (u t) x) :
    NavierStokes.ProblemStatement.spatialLaplacian (toSpacetime u) t x = Δ (u t) x := by
  rw [NavierFormal.laplacian_eq_sum_iteratedFDeriv, NavierStokes.ProblemStatement.spatialLaplacian]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordinateVector_eq_e]
  have hstep : ∀ y : Space,
      NavierStokes.ProblemStatement.spatialDerivative (toSpacetime u) t y (e i)
        = fderiv ℝ (u t) y (e i) := fun y => spatialDerivative_toSpacetime u t y ▸ rfl
  simp only [hstep]
  exact fderiv_fderiv_apply_eq_iteratedFDeriv hu i

/-! ## The residual identity for a classical solution (unforced case) -/

/-- **The unforced residual identity.** At an interior time of a classical
solution, the external package's Navier–Stokes residual of the corresponding
spacetime fields vanishes: this is exactly
`NavierFormal.IsClassicalSolution.momentum` rearranged, using the sign
convention `navierStokesResidual ν u p = ∂ₜu + (u·∇)u - ν·Δu + ∇p`
(no sign discrepancy with our `∂ₜu + (u·∇)u + ∇p = νΔu`, audit §1.2/§4). -/
theorem navierStokesResidual_toSpacetime_eq_zero {ν T : ℝ} {u₀ : Space → Space}
    {u : ℝ → Space → Space} {p : ℝ → Space → ℝ} (h : IsClassicalSolution ν u₀ T u p)
    {t : ℝ} {x : Space} (ht : 0 < t) (htT : t < T) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν (toSpacetime u) (toSpacetime p) t x
      = 0 := by
  have hmom : timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x :=
    h.momentum t x ht htT
  rw [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative_toSpacetime ht x,
    advection_toSpacetime, pressureGradient_toSpacetime,
    spatialLaplacian_toSpacetime (h.contDiffAt_velocity ht htT x), ← hmom]
  abel

/-! ## Energy bridge: our extended-real kinetic energy to their `UniformFiniteEnergy` -/

/-- Scaling of the extended-real kinetic energy under a scalar multiple: `∫⁻
‖c•w‖ₑ² = ofReal(c²) · ∫⁻ ‖w‖ₑ²`. Used to transport an energy bound through the
manuscript's viscosity rescaling `eq:nu-normalization`. -/
private theorem kineticEnergyLintegral_const_smul (c : ℝ) (w : Space → Space) :
    kineticEnergyLintegral (fun x => c • w x) = ENNReal.ofReal (c ^ 2) * kineticEnergyLintegral w
    := by
  simp only [kineticEnergyLintegral]
  have hpt : ∀ x, ‖c • w x‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖w x‖ₑ ^ 2 := by
    intro x
    rw [enorm_smul, mul_pow, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg c),
      sq_abs]
  simp_rw [hpt]
  exact MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (c ^ 2)) (fun x => ‖w x‖ₑ ^ 2)
    ENNReal.ofReal_ne_top

/-- **The `UniformFiniteEnergy` bridge.** A uniform bound `∫⁻ ‖v t‖ₑ² ≤ ofReal C`
on the extended-real kinetic energy of a continuous field, for every `t` in a
set `S`, yields the external package's `UniformFiniteEnergy S (toSpacetime v)`:
their predicate additionally requires the honest (real, Bochner) integrability
`SquareIntegrableAtTime`, obtained here from finiteness of the `ℝ≥0∞`-valued
integral via `integrable_toReal_of_lintegral_ne_top`, and their `kineticEnergy`
(their `(1/2)·∫‖v‖²`, `NavierStokes/R3/ProblemStatement.lean:76-77`) is bounded
by the same constant `C` (a factor-of-two slack against the tight bound `C/2`,
harmless since their predicate only asks for *some* uniform bound). -/
theorem uniformFiniteEnergy_toSpacetime_of_bound {v : ℝ → Space → Space} {S : Set ℝ}
    (hcont : ∀ t ∈ S, Continuous (v t)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ∈ S, kineticEnergyLintegral (v t) ≤ ENNReal.ofReal C) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy S (toSpacetime v) := by
  refine ⟨C, hC, fun t ht => ?_⟩
  have hmeas : AEMeasurable (fun x => ‖v t x‖ₑ ^ 2) (volume : Measure Space) :=
    ((hcont t ht).measurable.enorm.pow_const 2).aemeasurable
  have hlt : (∫⁻ x, ‖v t x‖ₑ ^ 2 ∂(volume : Measure Space)) ≠ ⊤ :=
    (lt_of_le_of_lt (hbound t ht) ENNReal.ofReal_lt_top).ne
  have hint0 : Integrable (fun x => (‖v t x‖ₑ ^ 2).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hmeas hlt
  have heq : (fun x => (‖v t x‖ₑ ^ 2).toReal) = fun x => ‖v t x‖ ^ 2 := by
    funext x
    rw [ENNReal.toReal_pow, toReal_enorm]
  rw [heq] at hint0
  have hkey : ENNReal.ofReal (∫ x, ‖v t x‖ ^ 2) ≤ ENNReal.ofReal C := by
    rw [ofReal_integral_eq_lintegral_ofReal hint0 (ae_of_all _ fun _ => sq_nonneg _),
      ← NavierFormal.kineticEnergyLintegral_eq]
    exact hbound t ht
  have hnn : (0 : ℝ) ≤ ∫ x : Space, ‖v t x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hle : (∫ x : Space, ‖v t x‖ ^ 2) ≤ C := (ENNReal.ofReal_le_ofReal_iff hC).mp hkey
  refine ⟨hint0, ?_⟩
  show NavierStokesR3.ProblemStatement.kineticEnergy (toSpacetime v) t ≤ C
  have hI : (∫ x : Space, ‖(toSpacetime v) (t, x)‖ ^ 2) = ∫ x : Space, ‖v t x‖ ^ 2 := rfl
  rw [NavierStokesR3.ProblemStatement.kineticEnergy, hI]
  linarith

/-! ## The main adapter, viscosity `1` -/

/-- **The main adapter (`ν = 1`), PLAN FC6.** If `(u,u₀,p)` and `(v,u₀,q)` are
two classical solutions with the *same* datum `u₀` on `ℝ³ × [0,T)` (viscosity
`1`), if their curried spacetime forms are smooth up to the closed slab
`[0,T']` (the extra hypothesis of the module docstring, since
`IsClassicalSolution` gives only continuity, not smoothness, at `t = 0`), if
`u` has one compact spatial support `K` throughout `[0,T']`, and if `v` has
uniform finite kinetic energy on `[0,T']`, then `u` and `v` agree pointwise on
`[0,T'] × ℝ³`.

This is `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`
transported through the spacetime dictionary above; see the module docstring
for the obstacle to using it on a genuine (non-compactly-supported)
Schwartz-datum classical solution: the *reference* field `u` must already be
known to have this compact support at every time, which an unforced flow does
not generically preserve. -/
theorem classical_uniqueness_of_compact_support
    {u₀ : Space → Space} {T T' : ℝ} {u v : ℝ → Space → Space} {p q : ℝ → Space → ℝ}
    (h : IsClassicalSolution 1 u₀ T u p) (h' : IsClassicalSolution 1 u₀ T v q)
    (hT' : 0 < T') (hT'T : T' < T)
    (hsu : ContDiffOn ℝ ∞ (toSpacetime u) (NavierStokesR3.Comparison.slab 0 T'))
    (hsv : ContDiffOn ℝ ∞ (toSpacetime v) (NavierStokesR3.Comparison.slab 0 T'))
    (hsp : ContDiffOn ℝ ∞ (toSpacetime p) (NavierStokesR3.Comparison.slab 0 T'))
    (hsq : ContDiffOn ℝ ∞ (toSpacetime q) (NavierStokesR3.Comparison.slab 0 T'))
    {K : Set Space} (hK : IsCompact K) (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) T', tsupport (u t) ⊆ K)
    (hev : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Set.Icc (0 : ℝ) T')
      (toSpacetime v)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ x, u t x = v t x := by
  have hdu : ∀ t ∈ Set.Ioo (0 : ℝ) T', ∀ x, NavierStokes.ProblemStatement.spatialDivergence
      (toSpacetime u) t x = 0 := fun t ht x => by
    rw [spatialDivergence_toSpacetime]
    exact h.incompressible t x ht.1 (ht.2.trans hT'T)
  have hdv : ∀ t ∈ Set.Ioo (0 : ℝ) T', ∀ x, NavierStokes.ProblemStatement.spatialDivergence
      (toSpacetime v) t x = 0 := fun t ht x => by
    rw [spatialDivergence_toSpacetime]
    exact h'.incompressible t x ht.1 (ht.2.trans hT'T)
  have hNS : ∀ t ∈ Set.Ioo (0 : ℝ) T', ∀ x,
      NavierStokesR3.ProblemStatement.navierStokesResidual 1 (toSpacetime u) (toSpacetime p) t x
        = NavierStokesR3.ProblemStatement.navierStokesResidual 1 (toSpacetime v) (toSpacetime q)
          t x := fun t ht x => by
    rw [navierStokesResidual_toSpacetime_eq_zero h ht.1 (ht.2.trans hT'T),
      navierStokesResidual_toSpacetime_eq_zero h' ht.1 (ht.2.trans hT'T)]
  have hzero : ∀ x, (toSpacetime u) (0, x) = (toSpacetime v) (0, x) := fun x => by
    show u 0 x = v 0 x
    rw [h.initial x, h'.initial x]
  exact NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc hT' hsu hsv hsp hsq hK
    hsupp hev hdu hdv hNS hzero

/-! ## The general-viscosity adapter, via `eq:nu-normalization` -/

/-- Support is unchanged by a nonzero pointwise scalar rescaling. -/
private theorem tsupport_const_smul_eq {c : ℝ} (hc : c ≠ 0) (w : Space → Space) :
    tsupport (fun x => c • w x) = tsupport w := by
  have : (Function.support fun x => c • w x) = Function.support w := by
    ext x
    simp [Function.mem_support, hc]
  simp [tsupport, this]

/-- The interval bookkeeping of `eq:nu-normalization`: `t/ν ∈ [0,T']` iff
`t ∈ [0,νT']`, for `ν > 0`. -/
private theorem mem_Icc_div_of_mem_Icc_mul {t T' ν : ℝ} (hν : 0 < ν)
    (ht : t ∈ Set.Icc (0 : ℝ) (ν * T')) : t / ν ∈ Set.Icc (0 : ℝ) T' := by
  refine ⟨div_nonneg ht.1 hν.le, (div_le_iff₀ hν).2 ?_⟩
  calc t ≤ ν * T' := ht.2
    _ = T' * ν := mul_comm _ _

/-- **The general-viscosity adapter, PLAN FC6.** The `ν = 1` adapter
`classical_uniqueness_of_compact_support`, transported to an arbitrary
viscosity `ν > 0` by the manuscript's rescaling `eq:nu-normalization`
(`NavierFormal.IsClassicalSolution.nuNormalization`): `s ↦ ν⁻¹u(x,s/ν)` is a
classical solution with viscosity `1` on `ℝ³ × [0,νT)`. Compact support of `u`
transports unchanged under the pointwise scalar `ν⁻¹ ≠ 0`
(`tsupport_const_smul_eq`); the uniform finite-energy bound for `v` transports
with the factor `ν⁻²` of `kineticEnergyLintegral_const_smul`. The smoothness
hypotheses are supplied directly for the rescaled fields, for the same reason
given in the module docstring: `IsClassicalSolution` gives no smoothness at
`t = 0` to rescale in the first place. -/
theorem classical_uniqueness_of_compact_support_nu
    {ν : ℝ} (hν : 0 < ν) {u₀ : Space → Space} {T T' : ℝ}
    {u v : ℝ → Space → Space} {p q : ℝ → Space → ℝ}
    (h : IsClassicalSolution ν u₀ T u p) (h' : IsClassicalSolution ν u₀ T v q)
    (hT' : 0 < T') (hT'T : T' < T)
    (hsu : ContDiffOn ℝ ∞ (toSpacetime fun s x => ν⁻¹ • u (s / ν) x)
      (NavierStokesR3.Comparison.slab 0 (ν * T')))
    (hsv : ContDiffOn ℝ ∞ (toSpacetime fun s x => ν⁻¹ • v (s / ν) x)
      (NavierStokesR3.Comparison.slab 0 (ν * T')))
    (hsp : ContDiffOn ℝ ∞ (toSpacetime fun s x => (ν ^ 2)⁻¹ * p (s / ν) x)
      (NavierStokesR3.Comparison.slab 0 (ν * T')))
    (hsq : ContDiffOn ℝ ∞ (toSpacetime fun s x => (ν ^ 2)⁻¹ * q (s / ν) x)
      (NavierStokesR3.Comparison.slab 0 (ν * T')))
    {K : Set Space} (hK : IsCompact K) (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) T', tsupport (u t) ⊆ K)
    {C : ℝ} (hC : 0 ≤ C)
    (hcont : ∀ t ∈ Set.Icc (0 : ℝ) T', Continuous (v t))
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T', kineticEnergyLintegral (v t) ≤ ENNReal.ofReal C) :
    ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ x, u t x = v t x := by
  have hνinv : ν⁻¹ ≠ 0 := inv_ne_zero hν.ne'
  have h1 := h.nuNormalization hν
  have h1' := h'.nuNormalization hν
  have hT'' : 0 < ν * T' := mul_pos hν hT'
  have hT''T : ν * T' < ν * T := mul_lt_mul_of_pos_left hT'T hν
  have hK' : ∀ t ∈ Set.Icc (0 : ℝ) (ν * T'), tsupport (fun x => ν⁻¹ • u (t / ν) x) ⊆ K := by
    intro t ht
    rw [tsupport_const_smul_eq hνinv]
    exact hsupp (t / ν) (mem_Icc_div_of_mem_Icc_mul hν ht)
  have hcont' : ∀ t ∈ Set.Icc (0 : ℝ) (ν * T'), Continuous (fun x => ν⁻¹ • v (t / ν) x) :=
    fun t ht => (hcont (t / ν) (mem_Icc_div_of_mem_Icc_mul hν ht)).const_smul ν⁻¹
  have hbound' : ∀ t ∈ Set.Icc (0 : ℝ) (ν * T'),
      kineticEnergyLintegral (fun x => ν⁻¹ • v (t / ν) x) ≤ ENNReal.ofReal (ν⁻¹ ^ 2 * C) := by
    intro t ht
    rw [kineticEnergyLintegral_const_smul, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact hbound (t / ν) (mem_Icc_div_of_mem_Icc_mul hν ht)
  have hev' : NavierStokesR3.ProblemStatement.UniformFiniteEnergy
      (Set.Icc (0 : ℝ) (ν * T')) (toSpacetime fun s x => ν⁻¹ • v (s / ν) x) :=
    uniformFiniteEnergy_toSpacetime_of_bound hcont' (by positivity) hbound'
  have hmain := classical_uniqueness_of_compact_support h1 h1' hT'' hT''T hsu hsv hsp hsq hK
    hK' hev'
  intro t ht x
  have hs : ν * t ∈ Set.Icc (0 : ℝ) (ν * T') :=
    ⟨mul_nonneg hν.le ht.1, mul_le_mul_of_nonneg_left ht.2 hν.le⟩
  have hdiv : ν * t / ν = t := by field_simp
  have := hmain (ν * t) hs x
  simp only [hdiv] at this
  exact smul_right_injective Space hνinv this
