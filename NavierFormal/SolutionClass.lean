import NavierFormal.Basic
import NavierFormal.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The classical solution class, the Clay target, and the finite-horizon critical bound

This module is the statement surface of the manuscript's solution class.  It
formalizes, for the unforced incompressible Navier–Stokes system on `ℝ³`,

`∂ₜu + (u·∇)u + ∇p = νΔu`,  `∇·u = 0`,  `u(0) = u₀`   (manuscript `eq:NS`),

the following manuscript objects.

* `NavierFormal.SchwartzDivFree` — the datum class of `eq:NS`: a divergence-free
  Schwartz vector field, Fefferman's admissible datum.
* `NavierFormal.IsClassicalSolution` — the classical solution on `ℝ³ × [0,T)`
  used throughout the manuscript (`premise:local`, `thm:continuation`,
  `hyp:critical`).
* `NavierFormal.RegularityPackage` — the regularity package `R` recorded after
  `premise:local`: `∂ₜʲu(t), ∂ₜʲp(t) ∈ H^k` uniformly on every compact
  subinterval, for all `j, k`.
* `NavierFormal.ClayAlternativeA` / `ClayAlternativeA_all` — the manuscript's
  Theorem `def:target`, i.e. Fefferman's unforced whole-space positive
  alternative (A).
* `NavierFormal.CriticalBound` / `CriticalHypothesis` — the manuscript's
  Hypothesis `hyp:critical` (finite-horizon critical estimate), quantified over
  *all* classical solutions on `[0,T')` with `T' ≤ H`, with no maximal time.

and proves the three structural facts the manuscript uses about this class:

* `NavierFormal.IsClassicalSolution.mono` — restriction to a shorter interval;
* `NavierFormal.IsClassicalSolution.nuNormalization` — the manuscript's
  viscosity normalization `eq:nu-normalization`,
  `v(x,s) = ν⁻¹u(x,s/ν)`, `q(x,s) = ν⁻²p(x,s/ν)`, which is a classical solution
  with viscosity `1` on `[0,νT)`;
* `NavierFormal.eLpNorm_three_nuNormalization` — the accompanying fixed-time
  identity `‖v(s)‖₃ = ν⁻¹‖u(s/ν)‖₃`.

Nothing here asserts that a solution exists; no Millennium-problem claim is
made in this file.

## Conventions and encoding choices

* The viscosity `ν` is a free real parameter of every definition; no
  normalization `ν = 1` is built into the statement surface.
* Time-dependent fields are curried, `u : ℝ → Space → Space`, so that `u t` is
  directly usable with `fderiv`, `Δ`, and `eLpNorm`.
* `Δ` is Mathlib's `InnerProductSpace` Laplacian (the trace of the second
  Fréchet derivative), which on `Space` is `∑ᵢ ∂ᵢ²`; `∇` is Mathlib's
  `gradient`, the Riesz representative of the Fréchet derivative.
* `(u·∇)u` is `fderiv ℝ (u t) x (u t x)`, i.e. the derivative in the direction
  `u(t,x)`; `∇·u` is `∑ᵢ ∂ᵢuᵢ` written through `fderiv`.
* The time derivative is `derivWithin … (Set.Ici 0)`, the one-sided derivative
  at `t = 0` and the ordinary derivative for `t > 0`
  (`NavierFormal.timeDeriv_eq_deriv`).
* Smoothness up to the initial time (Fefferman's `C^∞(ℝ³ × [0,∞))`) is
  Mathlib's `ContDiffOn` on the closed half-space `Set.Ici 0 ×ˢ Set.univ`, i.e.
  the "Taylor expansions within the set" notion.  This is smoothness up to the
  boundary, not extendability across it (Seeley extension is not in Mathlib).
* `L³` and `L²` quantities are extended reals (`eLpNorm`, `lintegral`), never
  `.toReal` of a possibly infinite quantity, so that a bound is never vacuously
  true for a field outside the space.

The spatial differential operators `divergence` and `convection` are those of
`NavierFormal.Calculus`; this module adds only the time derivative
`timeDeriv`/`timeDerivIter` and the homogeneity lemmas used by
`eq:nu-normalization`.
-/

open MeasureTheory

open scoped ENNReal ContDiff Gradient Laplacian

noncomputable section

namespace NavierFormal

section TimeDerivative

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The time derivative `∂ₜ` of a time-dependent field, taken within `[0,∞)`:
the one-sided (right) derivative at `t = 0` and the ordinary derivative for
`t > 0` (`timeDeriv_eq_deriv`).  This is `∂ₜu` in the manuscript's
`eq:NS`, and it is the derivative used at the initial time in Fefferman's
formulation on `ℝ³ × [0,∞)`. -/
def timeDeriv (u : ℝ → Space → F) (t : ℝ) (x : Space) : F :=
  derivWithin (fun s => u s x) (Set.Ici 0) t

/-- The iterated time derivative `∂ₜʲ` of a time-dependent field, used in the
regularity package `R` of the manuscript's `premise:local`. -/
def timeDerivIter (j : ℕ) (u : ℝ → Space → F) : ℝ → Space → F :=
  timeDeriv^[j] u

@[simp] theorem timeDerivIter_zero (u : ℝ → Space → F) : timeDerivIter 0 u = u := rfl

@[simp] theorem timeDerivIter_succ (j : ℕ) (u : ℝ → Space → F) :
    timeDerivIter (j + 1) u = timeDerivIter j (timeDeriv u) :=
  Function.iterate_succ_apply _ _ _

/-- For positive times the time derivative within `[0,∞)` is the ordinary
derivative: `[0,∞)` is a neighbourhood of every `t > 0`. -/
theorem timeDeriv_eq_deriv {u : ℝ → Space → F} {t : ℝ} (ht : 0 < t) (x : Space) :
    timeDeriv u t x = deriv (fun s => u s x) t :=
  derivWithin_of_mem_nhds (Ici_mem_nhds ht)

/-- The convection term scales quadratically: for a constant `c` and a field
differentiable at `x`, `((c·v)·∇)(c·v) = c² (v·∇)v`.  This is the convection
half of the manuscript's viscosity normalization `eq:nu-normalization`. -/
theorem convection_const_smul {v : Space → Space} {x : Space} (c : ℝ)
    (hv : DifferentiableAt ℝ v x) :
    convection (fun y => c • v y) x = (c * c) • convection v x := by
  have hfd : fderiv ℝ (fun y => c • v y) x = c • fderiv ℝ v x := fderiv_const_smul hv c
  simp only [convection, hfd, smul_apply, map_smul, smul_smul]

/-- The divergence is homogeneous: `∇·(c•v) = c (∇·v)` for a field
differentiable at `x`.  This is the incompressibility half of the manuscript's
viscosity normalization `eq:nu-normalization`. -/
theorem divergence_const_smul {v : Space → Space} {x : Space} (c : ℝ)
    (hv : DifferentiableAt ℝ v x) :
    divergence (fun y => c • v y) x = c * divergence v x := by
  have hfd : fderiv ℝ (fun y => c • v y) x = c • fderiv ℝ v x := fderiv_const_smul hv c
  simp only [divergence_eq_sum_component, hfd, smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [PiLp.smul_apply]

/-- The gradient is homogeneous: `∇(c·f) = c ∇f` for a scalar function
differentiable at `x`.  This is the pressure half of the manuscript's viscosity
normalization `eq:nu-normalization`. -/
theorem gradient_const_smul {f : Space → ℝ} {x : Space} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    ∇ (fun y => c * f y) x = c • ∇ f x := by
  have hfd : fderiv ℝ (fun y => c • f y) x = c • fderiv ℝ f x := fderiv_const_smul hf c
  simp only [gradient, smul_eq_mul] at hfd ⊢
  rw [hfd, map_smul]

end TimeDerivative

/-! ## Admissible data -/

/-- Fefferman's admissible datum for the manuscript's `eq:NS`: a divergence-free
vector field in the Schwartz class `𝒮(ℝ³)³`.

`SchwartzMap` is `C^∞` with `‖x‖^k ‖iteratedFDeriv ℝ n f x‖` bounded for all
`k, n`, which is Fefferman's decay requirement
`|∂^α u₀(x)| ≤ C_{α,K}(1+|x|)^{-K}` for all multi-indices `α` and all `K`. -/
structure SchwartzDivFree where
  /-- The underlying Schwartz vector field `u₀ : ℝ³ → ℝ³`. -/
  toSchwartz : SchwartzMap Space Space
  /-- Pointwise incompressibility of the datum, `∇·u₀ = 0` everywhere. -/
  div_free : ∀ x : Space, divergence (⇑toSchwartz) x = 0

/-- A divergence-free Schwartz datum is used as the function `ℝ³ → ℝ³` it is. -/
instance : CoeFun SchwartzDivFree (fun _ => Space → Space) :=
  ⟨fun u₀ => ⇑u₀.toSchwartz⟩

/-- An admissible datum of the manuscript's `eq:NS` is smooth. -/
theorem SchwartzDivFree.contDiff (u₀ : SchwartzDivFree) (n : ℕ∞) :
    ContDiff ℝ n (⇑u₀ : Space → Space) :=
  u₀.toSchwartz.smooth n

/-- An admissible datum of the manuscript's `eq:NS` is continuous, hence
measurable. -/
theorem SchwartzDivFree.continuous (u₀ : SchwartzDivFree) :
    Continuous (⇑u₀ : Space → Space) :=
  u₀.toSchwartz.continuous

/-- An admissible datum of the manuscript's `eq:NS` is differentiable. -/
theorem SchwartzDivFree.differentiable (u₀ : SchwartzDivFree) :
    Differentiable ℝ (⇑u₀ : Space → Space) :=
  u₀.toSchwartz.differentiable

/-! ## The classical solution class -/

/-- A classical solution of the manuscript's `eq:NS`,

`∂ₜu + (u·∇)u + ∇p = νΔu`,  `∇·u = 0`,  `u(0) = u₀`,

with viscosity `ν` on the slab `ℝ³ × [0,T)`.  This is exactly the manuscript's
notion: joint smoothness on the open slab, joint continuity up to the initial
time, attainment of the datum, and the pointwise equations for `0 < t < T`.  No
integrability class is built in; the regularity package of `premise:local` is
the separate predicate `RegularityPackage`. -/
structure IsClassicalSolution (ν : ℝ) (u₀ : Space → Space) (T : ℝ)
    (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) : Prop where
  /-- The velocity is jointly `C^∞` in `(t,x)` on the open slab `(0,T) × ℝ³`. -/
  smooth_u : ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2)
    (Set.Ioo 0 T ×ˢ (Set.univ : Set Space))
  /-- The pressure is jointly `C^∞` in `(t,x)` on the open slab `(0,T) × ℝ³`. -/
  smooth_p : ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2)
    (Set.Ioo 0 T ×ˢ (Set.univ : Set Space))
  /-- The velocity is jointly continuous up to the initial time, on
  `[0,T) × ℝ³`. -/
  cont_u : ContinuousOn (fun q : ℝ × Space => u q.1 q.2)
    (Set.Ico 0 T ×ˢ (Set.univ : Set Space))
  /-- The pressure is jointly continuous up to the initial time, on
  `[0,T) × ℝ³`. -/
  cont_p : ContinuousOn (fun q : ℝ × Space => p q.1 q.2)
    (Set.Ico 0 T ×ˢ (Set.univ : Set Space))
  /-- The initial condition `u(0) = u₀` of `eq:NS`, pointwise in `x`. -/
  initial : ∀ x, u 0 x = u₀ x
  /-- The momentum equation `∂ₜu + (u·∇)u + ∇p = νΔu` of `eq:NS`, pointwise on
  the open slab. -/
  momentum : ∀ t x, 0 < t → t < T →
    timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x
  /-- Incompressibility `∇·u = 0` of `eq:NS`, pointwise on the open slab. -/
  incompressible : ∀ t x, 0 < t → t < T → divergence (u t) x = 0

/-- The regularity package `R` recorded by the manuscript after `premise:local`:
for every compact subinterval `[0,T'] ⊂ [0,T)` and all orders `j, k`, the fields
`∂ₜʲu(t)` and `∂ₜʲp(t)` lie in `H^k(ℝ³)` uniformly for `t ∈ [0,T']`.

Encoding choice: `H^k` membership is recorded as finiteness — with a bound
uniform in `t` — of the `L²` norm of the `k`-th iterated Fréchet derivative.
Since the condition is imposed for *every* `k`, the resulting family of
conditions is equivalent to membership in every `H^k` (an `H^k` norm is the sum
of the `L²` norms of the derivatives of order `≤ k`).  Mathlib's
tempered-distribution Sobolev predicate `TemperedDistribution.memSobolev` is not
used, because stating it would require first exhibiting each field as a tempered
distribution, i.e. carrying a proof term inside the predicate.  Fidelity risk:
this formulation asserts a uniform norm bound, not measurability; measurability
is automatic for the smooth fields of `IsClassicalSolution` but is not part of
the predicate. -/
def RegularityPackage (T : ℝ) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) : Prop :=
  ∀ (j k : ℕ) (T' : ℝ), 0 ≤ T' → T' < T → ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T',
      eLpNorm (iteratedFDeriv ℝ k (timeDerivIter j u t)) 2 volume ≤ C ∧
      eLpNorm (iteratedFDeriv ℝ k (timeDerivIter j p t)) 2 volume ≤ C

/-- The regularity package restricts to shorter intervals, alongside
`IsClassicalSolution.mono`. -/
theorem RegularityPackage.mono {T T' : ℝ} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : RegularityPackage T u p) (hT : T' ≤ T) : RegularityPackage T' u p :=
  fun j k S hS hST => h j k S hS (lt_of_lt_of_le hST hT)

/-! ## The Clay target -/

/-- The manuscript's Theorem `def:target`, i.e. Fefferman's unforced whole-space
positive alternative (A), for one viscosity `ν` and one admissible datum `u₀`:
there are `u, p ∈ C^∞(ℝ³ × [0,∞))` solving `eq:NS` with datum `u₀` and one
constant `C` with `∫|u(x,t)|²dx ≤ C` for every `t ≥ 0`.

Transcription notes.  Smoothness on the closed half-space is `ContDiffOn` on
`Set.Ici 0 ×ˢ Set.univ`, Mathlib's "Taylor expansion within the set" notion,
which is one-sided smoothness up to `t = 0`; the time derivative in the equation
is correspondingly the derivative within `[0,∞)`, so the equation is imposed on
all of `[0,∞)` as in the official statement.  The energy bound is
`sup_{t≥0}∫|u|² < ∞` written as a single constant, and the integral is a
Lebesgue integral in `ℝ≥0∞`, so the bound is not vacuous for a field of infinite
energy.  Fefferman imposes no normalization on `p`, and none is imposed here. -/
def ClayAlternativeA (ν : ℝ) (u₀ : SchwartzDivFree) : Prop :=
  ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
    ContDiffOn ℝ ∞ (fun q : ℝ × Space => u q.1 q.2)
      (Set.Ici 0 ×ˢ (Set.univ : Set Space)) ∧
    ContDiffOn ℝ ∞ (fun q : ℝ × Space => p q.1 q.2)
      (Set.Ici 0 ×ˢ (Set.univ : Set Space)) ∧
    (∀ x, u 0 x = u₀ x) ∧
    (∀ t x, 0 ≤ t →
      timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x) ∧
    (∀ t x, 0 ≤ t → divergence (u t) x = 0) ∧
    ∃ C : ℝ, ∀ t, 0 ≤ t → ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ENNReal.ofReal C

/-- The manuscript's Theorem `def:target` in full: the positive alternative for
every viscosity `ν > 0` and every divergence-free Schwartz datum. -/
def ClayAlternativeA_all : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzDivFree, ClayAlternativeA ν u₀

/-! ## The finite-horizon critical hypothesis -/

/-- The manuscript's Hypothesis `hyp:critical` (finite-horizon critical
estimate) for one pair `(ν, u₀)`: for every finite horizon `H > 0` there is a
finite nonnegative `M = M(ν,u₀,H)` bounding `‖u(t)‖₃` for *every* classical
solution with datum `u₀` on *any* interval `[0,T')` with `T' ≤ H`, at every
time `0 < t < T'`.

No maximal solution is mentioned: the quantification is over all classical
solutions on all short enough intervals, which is the requested form.  The
manuscript's `sup_{0<t<min(H,T_*)}‖u(t)‖₃ ≤ M` is recovered by restricting the
maximal branch, and conversely uniqueness in the class turns every such solution
into a restriction of that branch.  The bound is stated in `ℝ≥0∞`, so a state
outside `L³` violates it rather than satisfying it vacuously. -/
def CriticalBound (ν : ℝ) (u₀ : SchwartzDivFree) : Prop :=
  ∀ H : ℝ, 0 < H → ∃ M : ℝ, 0 ≤ M ∧
    ∀ (T' : ℝ) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
      T' ≤ H → IsClassicalSolution ν (⇑u₀) T' u p →
      ∀ t, 0 < t → t < T' → eLpNorm (u t) 3 volume ≤ ENNReal.ofReal M

/-- The manuscript's Hypothesis `hyp:critical` as stated there: the critical
bound for every viscosity `ν > 0` and every divergence-free Schwartz datum. -/
def CriticalHypothesis : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzDivFree, CriticalBound ν u₀

/-! ## Elementary API for the class -/

namespace IsClassicalSolution

variable {ν T : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}

/-- `2 ≤ ∞` in the smoothness-order lattice `WithTop ℕ∞`, the order in which
`C^∞` is expressed. -/
theorem two_le_infty : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
  WithTop.coe_le_coe.2 le_top

/-- `∞ ≠ 0` in the smoothness-order lattice `WithTop ℕ∞`; this is the
side condition of `ContDiffAt.differentiableAt`. -/
theorem infty_ne_zero : (∞ : ℕ∞ω) ≠ 0 := by
  exact_mod_cast ENat.top_ne_zero

/-- On the open slab, a jointly smooth field is smooth in the space variable at
fixed time. -/
theorem contDiffAt_space_of_smooth {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : ℝ → Space → F}
    (h : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2)
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space)))
    {t : ℝ} (ht : 0 < t) (htT : t < T) (x : Space) : ContDiffAt ℝ ∞ (U t) x := by
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Space)) :=
    isOpen_Ioo.prod isOpen_univ
  have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Space) ∈ nhds ((t, x) : ℝ × Space) :=
    hopen.mem_nhds ⟨⟨ht, htT⟩, Set.mem_univ x⟩
  exact (h.contDiffAt hmem).comp x ((contDiff_const.prodMk contDiff_id).contDiffAt)

/-- On the open slab, a jointly smooth field is smooth in the time variable at
fixed position. -/
theorem contDiffAt_time_of_smooth {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : ℝ → Space → F}
    (h : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2)
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space)))
    {t : ℝ} (ht : 0 < t) (htT : t < T) (x : Space) :
    ContDiffAt ℝ ∞ (fun s => U s x) t := by
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Space)) :=
    isOpen_Ioo.prod isOpen_univ
  have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Space) ∈ nhds ((t, x) : ℝ × Space) :=
    hopen.mem_nhds ⟨⟨ht, htT⟩, Set.mem_univ x⟩
  exact (h.contDiffAt hmem).comp t ((contDiff_id.prodMk contDiff_const).contDiffAt)

/-- The velocity of a classical solution is `C^∞` in space at each interior
time. -/
theorem contDiffAt_velocity (h : IsClassicalSolution ν u₀ T u p) {t : ℝ}
    (ht : 0 < t) (htT : t < T) (x : Space) : ContDiffAt ℝ ∞ (u t) x :=
  contDiffAt_space_of_smooth h.smooth_u ht htT x

/-- The pressure of a classical solution is `C^∞` in space at each interior
time. -/
theorem contDiffAt_pressure (h : IsClassicalSolution ν u₀ T u p) {t : ℝ}
    (ht : 0 < t) (htT : t < T) (x : Space) : ContDiffAt ℝ ∞ (p t) x :=
  contDiffAt_space_of_smooth h.smooth_p ht htT x

/-- The velocity of a classical solution is differentiable in space at each
interior time. -/
theorem differentiableAt_velocity (h : IsClassicalSolution ν u₀ T u p) {t : ℝ}
    (ht : 0 < t) (htT : t < T) (x : Space) : DifferentiableAt ℝ (u t) x :=
  (h.contDiffAt_velocity ht htT x).differentiableAt infty_ne_zero

/-- The pressure of a classical solution is differentiable in space at each
interior time. -/
theorem differentiableAt_pressure (h : IsClassicalSolution ν u₀ T u p) {t : ℝ}
    (ht : 0 < t) (htT : t < T) (x : Space) : DifferentiableAt ℝ (p t) x :=
  (h.contDiffAt_pressure ht htT x).differentiableAt infty_ne_zero

/-- The velocity of a classical solution is differentiable in time at each
interior time. -/
theorem differentiableAt_time (h : IsClassicalSolution ν u₀ T u p) {t : ℝ}
    (ht : 0 < t) (htT : t < T) (x : Space) : DifferentiableAt ℝ (fun s => u s x) t :=
  (contDiffAt_time_of_smooth h.smooth_u ht htT x).differentiableAt infty_ne_zero

/-- The velocity of a classical solution is continuous in space at each interior
time; in particular each `u t` is measurable. -/
theorem continuous_velocity (h : IsClassicalSolution ν u₀ T u p) {t : ℝ}
    (ht : 0 < t) (htT : t < T) : Continuous (u t) :=
  continuous_iff_continuousAt.2 fun x =>
    ((h.differentiableAt_velocity ht htT x).continuousAt)

/-- The velocity of a classical solution is almost everywhere strongly
measurable at each interior time, so its `eLpNorm`s are the honest Lebesgue
norms. -/
theorem aestronglyMeasurable_velocity (h : IsClassicalSolution ν u₀ T u p) {t : ℝ}
    (ht : 0 < t) (htT : t < T) :
    AEStronglyMeasurable (u t) (volume : Measure Space) :=
  (h.continuous_velocity ht htT).aestronglyMeasurable

/-- Restriction of a classical solution to a shorter interval: if `(u,p)` solves
`eq:NS` on `ℝ³ × [0,T)` and `T' ≤ T`, then the same pair solves `eq:NS` on
`ℝ³ × [0,T')`.  This is the step used whenever the manuscript passes from the
maximal interval to a finite horizon. -/
theorem mono {T' : ℝ} (h : IsClassicalSolution ν u₀ T u p) (hT : T' ≤ T) :
    IsClassicalSolution ν u₀ T' u p where
  smooth_u := h.smooth_u.mono (Set.prod_mono (Set.Ioo_subset_Ioo le_rfl hT) le_rfl)
  smooth_p := h.smooth_p.mono (Set.prod_mono (Set.Ioo_subset_Ioo le_rfl hT) le_rfl)
  cont_u := h.cont_u.mono (Set.prod_mono (Set.Ico_subset_Ico le_rfl hT) le_rfl)
  cont_p := h.cont_p.mono (Set.prod_mono (Set.Ico_subset_Ico le_rfl hT) le_rfl)
  initial := h.initial
  momentum := fun t x ht htT => h.momentum t x ht (lt_of_lt_of_le htT hT)
  incompressible := fun t x ht htT => h.incompressible t x ht (lt_of_lt_of_le htT hT)

end IsClassicalSolution

/-! ## The viscosity normalization `eq:nu-normalization` -/

/-- Time rescaling of a jointly smooth field: if `U` is jointly `C^∞` on
`(0,T) × ℝ³` and `ν > 0`, then `(s,x) ↦ U(s/ν, x)` is jointly `C^∞` on
`(0,νT) × ℝ³`.  This is the smoothness half of the manuscript's
`eq:nu-normalization`. -/
theorem contDiffOn_timeScale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ℝ → Space → F} {T ν : ℝ} (hν : 0 < ν)
    (h : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2)
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Space => U (q.1 / ν) q.2)
      (Set.Ioo 0 (ν * T) ×ˢ (Set.univ : Set Space)) := by
  have hΦ : ContDiff ℝ ∞ (fun q : ℝ × Space => ((q.1 / ν, q.2) : ℝ × Space)) :=
    (contDiff_fst.div_const ν).prodMk contDiff_snd
  have hmaps : Set.MapsTo (fun q : ℝ × Space => ((q.1 / ν, q.2) : ℝ × Space))
      (Set.Ioo 0 (ν * T) ×ˢ (Set.univ : Set Space))
      (Set.Ioo 0 T ×ˢ (Set.univ : Set Space)) := by
    rintro ⟨s, x⟩ ⟨⟨hs0, hsT⟩, -⟩
    refine ⟨⟨div_pos hs0 hν, (div_lt_iff₀ hν).2 ?_⟩, Set.mem_univ _⟩
    calc s < ν * T := hsT
      _ = T * ν := mul_comm _ _
  exact h.comp hΦ.contDiffOn hmaps

/-- Time rescaling of a jointly continuous field up to the initial time. -/
theorem continuousOn_timeScale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ℝ → Space → F} {T ν : ℝ} (hν : 0 < ν)
    (h : ContinuousOn (fun q : ℝ × Space => U q.1 q.2)
      (Set.Ico 0 T ×ˢ (Set.univ : Set Space))) :
    ContinuousOn (fun q : ℝ × Space => U (q.1 / ν) q.2)
      (Set.Ico 0 (ν * T) ×ˢ (Set.univ : Set Space)) := by
  have hΦ : Continuous (fun q : ℝ × Space => ((q.1 / ν, q.2) : ℝ × Space)) :=
    (continuous_fst.div_const ν).prodMk continuous_snd
  have hmaps : Set.MapsTo (fun q : ℝ × Space => ((q.1 / ν, q.2) : ℝ × Space))
      (Set.Ico 0 (ν * T) ×ˢ (Set.univ : Set Space))
      (Set.Ico 0 T ×ˢ (Set.univ : Set Space)) := by
    rintro ⟨s, x⟩ ⟨⟨hs0, hsT⟩, -⟩
    refine ⟨⟨div_nonneg hs0 hν.le, (div_lt_iff₀ hν).2 ?_⟩, Set.mem_univ _⟩
    calc s < ν * T := hsT
      _ = T * ν := mul_comm _ _
  exact h.comp hΦ.continuousOn hmaps

/-- The manuscript's viscosity normalization `eq:nu-normalization`:
if `(u,p)` is a classical solution of `eq:NS` with viscosity `ν > 0` and datum
`u₀` on `ℝ³ × [0,T)`, then

`v(x,s) = ν⁻¹u(x,s/ν)`,  `q(x,s) = ν⁻²p(x,s/ν)`

is a classical solution with viscosity `1` and datum `ν⁻¹u₀` on `ℝ³ × [0,νT)`,
i.e. `v_s + (v·∇)v + ∇q = Δv`, `∇·v = 0`.  The maximal-time statement
`S_* = νT_*` of the manuscript is the interval bookkeeping `[0,νT)` here. -/
theorem IsClassicalSolution.nuNormalization {ν T : ℝ} {u₀ : Space → Space}
    {u : ℝ → Space → Space} {p : ℝ → Space → ℝ} (hν : 0 < ν)
    (h : IsClassicalSolution ν u₀ T u p) :
    IsClassicalSolution 1 (fun x => ν⁻¹ • u₀ x) (ν * T)
      (fun s x => ν⁻¹ • u (s / ν) x) (fun s x => (ν ^ 2)⁻¹ * p (s / ν) x) where
  smooth_u := (contDiffOn_timeScale hν h.smooth_u).const_smul ν⁻¹
  smooth_p := by
    have := (contDiffOn_timeScale hν h.smooth_p).const_smul (ν ^ 2)⁻¹
    simpa only [smul_eq_mul] using this
  cont_u := (continuousOn_timeScale hν h.cont_u).const_smul ν⁻¹
  cont_p := (continuousOn_timeScale hν h.cont_p).const_smul (ν ^ 2)⁻¹
  initial := by
    intro x
    simp only [zero_div, h.initial x]
  momentum := by
    intro s x hs hsT
    -- the corresponding time for the original solution
    set t : ℝ := s / ν with ht_def
    have ht : 0 < t := div_pos hs hν
    have htT : t < T := by
      rw [ht_def]
      refine (div_lt_iff₀ hν).2 ?_
      calc s < ν * T := hsT
        _ = T * ν := mul_comm _ _
    have hdu : DifferentiableAt ℝ (u t) x := h.differentiableAt_velocity ht htT x
    have hdp : DifferentiableAt ℝ (p t) x := h.differentiableAt_pressure ht htT x
    have hdt : DifferentiableAt ℝ (fun σ => u σ x) t := h.differentiableAt_time ht htT x
    -- the time derivative, by the chain rule for `σ ↦ σ/ν`
    have hchain : HasDerivAt (fun σ : ℝ => ν⁻¹ • u (σ / ν) x)
        ((ν⁻¹ * ν⁻¹) • deriv (fun σ => u σ x) t) s := by
      have h1 : HasDerivAt (fun σ : ℝ => σ / ν) ν⁻¹ s := by
        simpa [div_eq_mul_inv] using (hasDerivAt_id s).mul_const ν⁻¹
      have h2 : HasDerivAt (fun σ : ℝ => u σ x) (deriv (fun σ => u σ x) t) t := hdt.hasDerivAt
      have h3 : HasDerivAt ((fun σ : ℝ => u σ x) ∘ fun σ : ℝ => σ / ν)
          (ν⁻¹ • deriv (fun σ => u σ x) t) s := HasDerivAt.scomp s h2 h1
      have h4 := h3.const_smul ν⁻¹
      rw [smul_smul] at h4
      exact h4
    have hut : timeDeriv u t x = deriv (fun σ => u σ x) t := timeDeriv_eq_deriv ht x
    have htd : timeDeriv (fun s x => ν⁻¹ • u (s / ν) x) s x
        = (ν⁻¹ * ν⁻¹) • deriv (fun σ => u σ x) t := by
      rw [timeDeriv_eq_deriv hs x]
      exact hchain.deriv
    -- the convection term
    have hconv : convection (fun y => ν⁻¹ • u t y) x
        = (ν⁻¹ * ν⁻¹) • convection (u t) x :=
      convection_const_smul ν⁻¹ hdu
    -- the pressure gradient
    have hgrad : ∇ (fun y => (ν ^ 2)⁻¹ * p t y) x = (ν ^ 2)⁻¹ • ∇ (p t) x :=
      gradient_const_smul (ν ^ 2)⁻¹ hdp
    -- the Laplacian
    have hlap : Δ (fun y => ν⁻¹ • u t y) x = ν⁻¹ • Δ (u t) x :=
      InnerProductSpace.laplacian_smul (F := Space) ν⁻¹
        ((h.contDiffAt_velocity ht htT x).of_le IsClassicalSolution.two_le_infty)
    have hν2 : (ν ^ 2)⁻¹ = ν⁻¹ * ν⁻¹ := by rw [sq]; exact mul_inv _ _
    have key : deriv (fun σ => u σ x) t + convection (u t) x + ∇ (p t) x
        = ν • Δ (u t) x := by
      rw [← hut]; exact h.momentum t x ht htT
    show timeDeriv (fun s x => ν⁻¹ • u (s / ν) x) s x
        + convection (fun y => ν⁻¹ • u t y) x + ∇ (fun y => (ν ^ 2)⁻¹ * p t y) x
        = (1 : ℝ) • Δ (fun y => ν⁻¹ • u t y) x
    rw [htd, hconv, hgrad, hlap, hν2, ← smul_add, ← smul_add, key, smul_smul, one_smul]
    congr 1
    field_simp
  incompressible := by
    intro s x hs hsT
    set t : ℝ := s / ν with ht_def
    have ht : 0 < t := div_pos hs hν
    have htT : t < T := by
      rw [ht_def]
      refine (div_lt_iff₀ hν).2 ?_
      calc s < ν * T := hsT
        _ = T * ν := mul_comm _ _
    have hdu : DifferentiableAt ℝ (u t) x := h.differentiableAt_velocity ht htT x
    rw [divergence_const_smul ν⁻¹ hdu, h.incompressible t x ht htT, mul_zero]

/-- The fixed-time critical norm identity accompanying the manuscript's
`eq:nu-normalization`: `‖v(s)‖₃ = ν⁻¹‖u(s/ν)‖₃` for `v(x,s) = ν⁻¹u(x,s/ν)`.
No spatial rescaling occurs, so this is pure homogeneity of the `L³` norm. -/
theorem eLpNorm_three_nuNormalization {ν : ℝ} (hν : 0 < ν) (u : ℝ → Space → Space)
    (s : ℝ) :
    eLpNorm (fun x => ν⁻¹ • u (s / ν) x) 3 volume
      = ENNReal.ofReal ν⁻¹ * eLpNorm (u (s / ν)) 3 volume := by
  have h := eLpNorm_const_smul (𝕜 := ℝ) ν⁻¹ (u (s / ν)) 3 (volume : Measure Space)
  rw [Real.enorm_eq_ofReal (by positivity)] at h
  exact h

end NavierFormal
