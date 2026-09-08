import NavierFormal.Basic
import NavierFormal.Calculus
import NavierFormal.SolutionClass
import NavierFormal.Blowup
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# The full amplitude/time viscosity rescaling, and `UnforcedCounterexample` normalization

This module extends `NavierFormal.SolutionClass`'s one-directional windowed
viscosity normalization `eq:nu-normalization`
(`NavierFormal.IsClassicalSolution.nuNormalization`, `v(x,s)=ν⁻¹u(x,s/ν)`,
`q(x,s)=ν⁻²p(x,s/ν)`, viscosity `ν ↦ 1`) to a **general one-parameter
rescaling family** `c > 0` acting on the *global* smooth-solution class
`NavierFormal.IsGlobalSmoothSolution` of `NavierFormal.Blowup` as well as on
the windowed class, in both directions.  It is the residual of PLAN task
`8.2a` ("global viscosity rescaling in Blowup") reported unfinished by the
`Blowup.lean` lane: that report identified two missing ingredients —

(a) a reparametrization lemma for `NavierFormal.SpeedUnboundedAt` under the
    time change `t = c s`, and
(b) the **converse** rescaling of `NavierFormal.IsGlobalSmoothSolution` from
    viscosity `1` back to an arbitrary `ν`, since
    `IsClassicalSolution.nuNormalization` is one-directional (`ν ↦ 1` only)
    and windowed (`IsClassicalSolution`, not `IsGlobalSmoothSolution`).

Both are supplied here, uniformly, as instances of one two-parameter algebra
check (manuscript `eq:nu-normalization`, generalized): for `c > 0`, if `(u,p)`
solves `eq:NS` with viscosity `ν`, then

`v(s,x) = c • u(c·s, x)`,  `q(s,x) = c² · p(c·s, x)`

solves `eq:NS` with viscosity `c·ν`.  No spatial rescaling occurs (`x` is
untouched), only a *time* rescaling `t = c·s` composed with the *amplitude*
rescaling `c`; the exponents `(c, c², c)` on `(v, q, Δv)` are forced by the
quadratic degree of the convection term against the single time derivative,
exactly as in `IsClassicalSolution.nuNormalization` (`ν⁻¹, ν⁻², ν⁻¹` there is
the case `c = ν⁻¹`).  Taking `c = ν⁻¹` recovers
`IsClassicalSolution.nuNormalization` exactly (up to the domain
`T/c = ν·T`); taking `c = ν` afterwards inverts it, which is the missing
converse (b).

## Contents

* `IsGlobalSmoothSolution.rescale`, `IsClassicalSolution.rescale` — the
  general-`c` rescaling of the global and windowed classes.
* `IsGlobalSmoothSolution.rescale_iff` — the `ν ↦ 1` specialization of the
  global rescaling as a two-way statement, PLAN `eq:nu-normalization`.
* `SpeedUnboundedAt.rescale`, `UniformFiniteEnergyOn.rescale` — the missing
  diagnostic (a) and the windowed energy transport under `t = c·s`.
* `UnforcedCounterexample.rescale`, `.nuNormalization`, `.of_nuNormalization`
  and the `Some`/`All` equivalences with `UnforcedCounterexample 1` — the PLAN
  `8.2a` main deliverable.

Nothing here asserts that any `UnforcedCounterexample` holds; every
declaration is either a definition-free rescaling lemma or a theorem
conditional on `UnforcedCounterexample`/`IsClassicalSolution`/
`IsGlobalSmoothSolution` hypotheses supplied by the caller.
-/

open MeasureTheory Set
open scoped ENNReal ContDiff Gradient Laplacian

noncomputable section

namespace NavierFormal

/-! ## Time-rescaling helpers for the closed half-line `Ici 0` -/

section TimeScaleIci

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Time rescaling `t = c·s` of a jointly smooth field on the closed half-space
`Ici 0 ×ˢ univ`, `c > 0`: `(s,x) ↦ U(c·s, x)` is again jointly `C^∞` there,
since `s ↦ c·s` maps `Ici 0` into itself. This is the `IsGlobalSmoothSolution`
analogue of `NavierFormal.contDiffOn_timeScale` (which is stated for the
bounded windowed domain `Ioo 0 T` with a division). -/
private theorem contDiffOn_timeScale_ici {U : ℝ → Space → F} {c : ℝ} (hc : 0 < c)
    (h : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2) (Ici 0 ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Space => U (c * q.1) q.2) (Ici 0 ×ˢ (univ : Set Space)) := by
  have hΦ : ContDiff ℝ ∞ (fun q : ℝ × Space => ((c * q.1, q.2) : ℝ × Space)) :=
    (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  have hmaps : MapsTo (fun q : ℝ × Space => ((c * q.1, q.2) : ℝ × Space))
      (Ici 0 ×ˢ (univ : Set Space)) (Ici 0 ×ˢ (univ : Set Space)) := by
    rintro ⟨s, x⟩ ⟨hs0, -⟩
    exact ⟨mul_nonneg hc.le hs0, mem_univ _⟩
  exact h.comp hΦ.contDiffOn hmaps

omit [NormedSpace ℝ F] in
/-- Time rescaling `t = c·s` of a jointly continuous field on `Ici 0 ×ˢ univ`,
`c > 0`; the continuity half of `contDiffOn_timeScale_ici`. -/
private theorem continuousOn_timeScale_ici {U : ℝ → Space → F} {c : ℝ} (hc : 0 < c)
    (h : ContinuousOn (fun q : ℝ × Space => U q.1 q.2) (Ici 0 ×ˢ (univ : Set Space))) :
    ContinuousOn (fun q : ℝ × Space => U (c * q.1) q.2) (Ici 0 ×ˢ (univ : Set Space)) := by
  have hΦ : Continuous (fun q : ℝ × Space => ((c * q.1, q.2) : ℝ × Space)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hmaps : MapsTo (fun q : ℝ × Space => ((c * q.1, q.2) : ℝ × Space))
      (Ici 0 ×ˢ (univ : Set Space)) (Ici 0 ×ˢ (univ : Set Space)) := by
    rintro ⟨s, x⟩ ⟨hs0, -⟩
    exact ⟨mul_nonneg hc.le hs0, mem_univ _⟩
  exact h.comp hΦ.continuousOn hmaps

/-- Restricting a jointly smooth field on `Ici 0 ×ˢ univ` to a fixed time
`t ≥ 0` (including the boundary time `t = 0`) gives a spatially smooth field,
by composing with the everywhere-smooth embedding `y ↦ (t,y)` into the closed
half-space. This is the `Ici 0` analogue of
`IsClassicalSolution.contDiffAt_space_of_smooth`, which needs the *open*
interval `Ioo 0 T` and so cannot reach `t = 0`. -/
private theorem contDiffAt_space_of_smooth_ici {U : ℝ → Space → F}
    (h : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2) (Ici 0 ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : 0 ≤ t) (x : Space) : ContDiffAt ℝ ∞ (U t) x := by
  have hι : ContDiffOn ℝ ∞ (fun y : Space => ((t, y) : ℝ × Space)) (univ : Set Space) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : MapsTo (fun y : Space => ((t, y) : ℝ × Space)) (univ : Set Space)
      (Ici 0 ×ˢ (univ : Set Space)) := fun y _ => ⟨ht, mem_univ y⟩
  exact (h.comp hι hmaps).contDiffAt (isOpen_univ.mem_nhds (mem_univ x))

/-- Restricting a jointly smooth field on `Ici 0 ×ˢ univ` to a fixed position
`x`, over the *whole* closed half-line `Ici 0` (not just a single time),
by composing with the everywhere-smooth embedding `s ↦ (s,x)`. Used to extract
one-sided time-differentiability at `t = 0` from joint smoothness up to the
boundary. -/
private theorem contDiffOn_time_of_smooth_ici {U : ℝ → Space → F}
    (h : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2) (Ici 0 ×ˢ (univ : Set Space)))
    (x : Space) : ContDiffOn ℝ ∞ (fun s => U s x) (Ici (0 : ℝ)) := by
  have hι : ContDiffOn ℝ ∞ (fun s : ℝ => ((s, x) : ℝ × Space)) (Ici (0 : ℝ)) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmaps : MapsTo (fun s : ℝ => ((s, x) : ℝ × Space)) (Ici (0 : ℝ))
      (Ici 0 ×ˢ (univ : Set Space)) := fun s hs => ⟨hs, mem_univ x⟩
  exact h.comp hι hmaps

/-- One-sided time-differentiability at every `t ≥ 0`, including `t = 0`, for
a spatial slice of a jointly smooth field on `Ici 0 ×ˢ univ`: the `Ici 0`
analogue of `IsClassicalSolution.differentiableAt_time`. -/
private theorem hasDerivWithinAt_timeDeriv {U : ℝ → Space → F}
    (h : ContDiffOn ℝ ∞ (fun q : ℝ × Space => U q.1 q.2) (Ici 0 ×ˢ (univ : Set Space)))
    (x : Space) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => U s x) (timeDeriv U t x) (Ici 0) t := by
  have hdiff : DifferentiableWithinAt ℝ (fun s => U s x) (Ici (0 : ℝ)) t :=
    (contDiffOn_time_of_smooth_ici h x).differentiableOn IsClassicalSolution.infty_ne_zero t ht
  simpa only [timeDeriv] using hdiff.hasDerivWithinAt

end TimeScaleIci

/-! ## Rescaling of the energy diagnostic (`Ici 0` case) -/

/-- Pointwise scaling of the extended-real kinetic-energy integrand under a
constant multiple: `∫⁻ ‖c•w‖ₑ² = ofReal(c²) · ∫⁻ ‖w‖ₑ²`. Reproves, for this
module, the private lemma of the same shape in
`NavierFormal.External.OpenAIUniqueness`
(`kineticEnergyLintegral_const_smul`) and the inline computation of
`NavierFormal.UniformFiniteEnergyOn.nuNormalization`. -/
private theorem lintegral_enorm_sq_const_smul (c : ℝ) (w : Space → Space) :
    (∫⁻ x, ‖c • w x‖ₑ ^ 2) = ENNReal.ofReal (c ^ 2) * ∫⁻ x, ‖w x‖ₑ ^ 2 := by
  have hpt : ∀ x : Space, ‖c • w x‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖w x‖ₑ ^ 2 := by
    intro x
    rw [enorm_smul, mul_pow, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg c),
      sq_abs]
  simp_rw [hpt]
  exact lintegral_const_mul' _ _ (by finiteness)

/-- Uniformly finite energy on `Ici 0` rescales along `v(s,x) = c•u(c·s,x)`,
`c > 0`: the `Ici 0` case of the energy transport, used inside
`IsGlobalSmoothSolution.rescale`. -/
theorem UniformFiniteEnergyOn.rescale_ici {c : ℝ} (hc : 0 < c) {u : ℝ → Space → Space}
    (h : UniformFiniteEnergyOn (Ici 0) u) :
    UniformFiniteEnergyOn (Ici 0) (fun s x => c • u (c * s) x) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨c ^ 2 * C, fun s hs => ?_⟩
  have hcs : c * s ∈ (Ici (0 : ℝ)) := mul_nonneg hc.le hs
  rw [lintegral_enorm_sq_const_smul, ENNReal.ofReal_mul (by positivity)]
  gcongr
  exact hC _ hcs

/-! ## Rescaling of the global smooth-solution class -/

/-- **The general one-parameter rescaling, PLAN `8.2a`, `eq:nu-normalization`
generalized.** If `(u,p)` is a global smooth finite-energy solution of
`eq:NS` with viscosity `ν` and datum `u₀`, and `c > 0`, then

`v(s,x) = c • u(c·s, x)`,  `q(s,x) = c² · p(c·s, x)`

is a global smooth finite-energy solution with viscosity `c·ν` and datum
`c • u₀`. No spatial rescaling occurs. Taking `c = ν⁻¹` (with `ν > 0`)
specializes to the missing `ν ↦ 1` global normalization identified in the
`Blowup.lean` lane report; taking `c = ν` afterwards is the converse
`1 ↦ ν` that `IsClassicalSolution.nuNormalization` does not supply. -/
theorem IsGlobalSmoothSolution.rescale {ν c : ℝ} {u₀ : Space → Space}
    {u : ℝ → Space → Space} {p : ℝ → Space → ℝ} (hc : 0 < c)
    (h : IsGlobalSmoothSolution ν u₀ u p) :
    IsGlobalSmoothSolution (c * ν) (fun x => c • u₀ x) (fun s x => c • u (c * s) x)
      (fun s x => c ^ 2 * p (c * s) x) := by
  obtain ⟨hsmooth_u, hsmooth_p, hinit, hmom, hdiv, henergy⟩ := h
  refine ⟨(contDiffOn_timeScale_ici hc hsmooth_u).const_smul c, ?_, ?_, ?_, ?_, ?_⟩
  · have := (contDiffOn_timeScale_ici hc hsmooth_p).const_smul (c ^ 2)
    simpa only [smul_eq_mul] using this
  · intro x; simp only [mul_zero, hinit x]
  · intro s x hs
    set t : ℝ := c * s with ht_def
    have ht : 0 ≤ t := mul_nonneg hc.le hs
    -- the time derivative, by the within-chain rule for `σ ↦ c·σ` on `Ici 0`
    have hdu : ContDiffAt ℝ ∞ (u t) x := contDiffAt_space_of_smooth_ici hsmooth_u ht x
    have h2 : HasDerivWithinAt (fun σ => u σ x) (timeDeriv u t x) (Ici 0) t :=
      hasDerivWithinAt_timeDeriv hsmooth_u x ht
    have h1 : HasDerivWithinAt (fun σ : ℝ => c * σ) c (Ici 0) s := by
      simpa using ((hasDerivAt_id s).const_mul c).hasDerivWithinAt
    have hmaps : MapsTo (fun σ : ℝ => c * σ) (Ici 0) (Ici 0) :=
      fun σ hσ => mul_nonneg hc.le hσ
    have h3 : HasDerivWithinAt ((fun σ => u σ x) ∘ fun σ : ℝ => c * σ)
        (c • timeDeriv u t x) (Ici 0) s := h2.scomp s h1 hmaps
    have h4 : HasDerivWithinAt (fun σ : ℝ => c • u (c * σ) x)
        (c • c • timeDeriv u t x) (Ici 0) s := h3.const_smul c
    have huniq : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) s := uniqueDiffOn_Ici 0 s hs
    have htd : timeDeriv (fun s x => c • u (c * s) x) s x = (c * c) • timeDeriv u t x := by
      rw [timeDeriv, h4.derivWithin huniq, smul_smul]
    -- the convection term, the pressure gradient, and the Laplacian
    have hconv : convection (fun y => c • u t y) x = (c * c) • convection (u t) x :=
      convection_const_smul c (hdu.differentiableAt IsClassicalSolution.infty_ne_zero)
    have hgrad : ∇ (fun y => c ^ 2 * p t y) x = c ^ 2 • ∇ (p t) x := by
      have := gradient_const_smul (c ^ 2)
        ((contDiffAt_space_of_smooth_ici hsmooth_p ht x).differentiableAt
          IsClassicalSolution.infty_ne_zero)
      simpa using this
    have hlap : Δ (fun y => c • u t y) x = c • Δ (u t) x :=
      InnerProductSpace.laplacian_smul (F := Space) c (hdu.of_le IsClassicalSolution.two_le_infty)
    have key : timeDeriv u t x + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x := hmom t x ht
    show timeDeriv (fun s x => c • u (c * s) x) s x + convection (fun y => c • u t y) x
        + ∇ (fun y => c ^ 2 * p t y) x = (c * ν) • Δ (fun y => c • u t y) x
    have hc2 : (c : ℝ) ^ 2 = c * c := sq c
    rw [htd, hconv, hgrad, hc2, ← smul_add, ← smul_add, key, hlap, smul_smul, smul_smul]
    congr 1
    ring
  · intro s x hs
    set t : ℝ := c * s with ht_def
    have ht : 0 ≤ t := mul_nonneg hc.le hs
    have hdu : DifferentiableAt ℝ (u t) x :=
      (contDiffAt_space_of_smooth_ici hsmooth_u ht x).differentiableAt
        IsClassicalSolution.infty_ne_zero
    rw [divergence_const_smul c hdu, hdiv t x ht, mul_zero]
  · exact UniformFiniteEnergyOn.rescale_ici hc henergy

/-! ## Rescaling of the windowed energy and speed diagnostics -/

/-- **The windowed energy transport under `t = c·s`.** Uniformly finite
energy on `Ico 0 T` rescales along `v(s,x) = c•u(c·s,x)`, `c > 0`, to
uniformly finite energy on `Ico 0 (T/c)`: the windowed analogue of
`UniformFiniteEnergyOn.rescale_ici`, generalizing
`NavierFormal.UniformFiniteEnergyOn.nuNormalization` (the case `c = ν⁻¹`). -/
theorem UniformFiniteEnergyOn.rescale {T c : ℝ} (hc : 0 < c) {u : ℝ → Space → Space}
    (h : UniformFiniteEnergyOn (Ico 0 T) u) :
    UniformFiniteEnergyOn (Ico 0 (T / c)) (fun s x => c • u (c * s) x) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨c ^ 2 * C, fun s hs => ?_⟩
  have hcs : c * s ∈ Ico (0 : ℝ) T :=
    ⟨mul_nonneg hc.le hs.1, by rw [mul_comm]; exact (lt_div_iff₀ hc).1 hs.2⟩
  rw [lintegral_enorm_sq_const_smul, ENNReal.ofReal_mul (by positivity)]
  gcongr
  exact hC _ hcs

/-- **The missing reparametrization lemma (a) of the `Blowup.lean` lane
report.** Pointwise-unbounded speed on approach to `T` rescales along
`v(s,x) = c•u(c·s,x)`, `c > 0`, to pointwise-unbounded speed on approach to
`T/c`: given any proposed bound `M` and any `s₀ < T/c`, the original
diagnostic (applied to `M/c` and `c·s₀ < T`) supplies a later time `t < T`
and point `x` with `M/c < ‖u t x‖`; `s := t/c ∈ (s₀, T/c)` and
`‖v s x‖ = c‖u t x‖ > M` since `c > 0`. -/
theorem SpeedUnboundedAt.rescale {T c : ℝ} (hc : 0 < c) {u : ℝ → Space → Space}
    (h : SpeedUnboundedAt T u) :
    SpeedUnboundedAt (T / c) (fun s x => c • u (c * s) x) := by
  intro M s₀ hs₀
  have hcs₀ : c * s₀ < T := by rw [mul_comm]; exact (lt_div_iff₀ hc).1 hs₀
  obtain ⟨t, ht, x, hx⟩ := h (M / c) (c * s₀) hcs₀
  have hst : c * (t / c) = t := by field_simp
  have hs₀lt : s₀ < t / c := by
    rw [lt_div_iff₀ hc]; rw [mul_comm]; exact ht.1
  have hltTc : t / c < T / c := (div_lt_div_iff_of_pos_right hc).2 ht.2
  refine ⟨t / c, ⟨hs₀lt, hltTc⟩, x, ?_⟩
  show M < ‖c • u (c * (t / c)) x‖
  rw [hst, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hMeq : c * (M / c) = M := by field_simp
  calc M = c * (M / c) := hMeq.symm
    _ < c * ‖u t x‖ := by exact mul_lt_mul_of_pos_left hx hc

/-! ## Rescaling of the windowed classical-solution class -/

/-- **The general one-parameter rescaling of the windowed class.** The
windowed analogue of `IsGlobalSmoothSolution.rescale`, and the generalization
of `IsClassicalSolution.nuNormalization` (`NavierFormal.SolutionClass`) from
the fixed exponent `c = ν⁻¹` (target viscosity `1`) to an arbitrary `c > 0`
(target viscosity `c·ν`): this is exactly the missing converse direction (b)
of the `Blowup.lean` lane report, since taking `c = ν` sends viscosity `1`
back to `ν`, which `nuNormalization` (a `ν ↦ 1` map only) cannot do. The proof
follows `nuNormalization`'s structure verbatim with `ν⁻¹` replaced by `c` and
`s/ν` replaced by `c·s`; no field-inverse bookkeeping is needed since `c²` is
already `c·c`. -/
theorem IsClassicalSolution.rescale {ν T c : ℝ} {u₀ : Space → Space}
    {u : ℝ → Space → Space} {p : ℝ → Space → ℝ} (hc : 0 < c)
    (h : IsClassicalSolution ν u₀ T u p) :
    IsClassicalSolution (c * ν) (fun x => c • u₀ x) (T / c)
      (fun s x => c • u (c * s) x) (fun s x => c ^ 2 * p (c * s) x) where
  smooth_u := by
    have hthis := (contDiffOn_timeScale (inv_pos.2 hc) h.smooth_u).const_smul c
    have heq : (fun q : ℝ × Space => c • u (q.1 / c⁻¹) q.2)
        = (fun q : ℝ × Space => c • u (c * q.1) q.2) := by
      funext q; rw [div_eq_mul_inv, inv_inv, mul_comm]
    rw [heq, show c⁻¹ * T = T / c from by rw [inv_mul_eq_div]] at hthis
    exact hthis
  smooth_p := by
    have hthis := (contDiffOn_timeScale (inv_pos.2 hc) h.smooth_p).const_smul (c ^ 2)
    have heq : (fun q : ℝ × Space => c ^ 2 • p (q.1 / c⁻¹) q.2)
        = (fun q : ℝ × Space => c ^ 2 * p (c * q.1) q.2) := by
      funext q; rw [div_eq_mul_inv, inv_inv, smul_eq_mul, mul_comm q.1 c]
    rw [heq, show c⁻¹ * T = T / c from by rw [inv_mul_eq_div]] at hthis
    exact hthis
  cont_u := by
    have hthis := (continuousOn_timeScale (inv_pos.2 hc) h.cont_u).const_smul c
    have heq : (c • fun q : ℝ × Space => u (q.1 / c⁻¹) q.2)
        = (fun q : ℝ × Space => c • u (c * q.1) q.2) := by
      funext q; rw [Pi.smul_apply, div_eq_mul_inv, inv_inv, mul_comm]
    rw [heq, show c⁻¹ * T = T / c from by rw [inv_mul_eq_div]] at hthis
    exact hthis
  cont_p := by
    have hthis := (continuousOn_timeScale (inv_pos.2 hc) h.cont_p).const_smul (c ^ 2)
    have heq : (c ^ 2 • fun q : ℝ × Space => p (q.1 / c⁻¹) q.2)
        = (fun q : ℝ × Space => c ^ 2 * p (c * q.1) q.2) := by
      funext q; rw [Pi.smul_apply, div_eq_mul_inv, inv_inv, smul_eq_mul, mul_comm q.1 c]
    rw [heq, show c⁻¹ * T = T / c from by rw [inv_mul_eq_div]] at hthis
    exact hthis
  initial := by intro x; simp only [mul_zero, h.initial x]
  momentum := by
    intro s x hs hsT
    set t : ℝ := c * s with ht_def
    have ht : 0 < t := mul_pos hc hs
    have htT : t < T := by
      rw [ht_def, mul_comm]; exact (lt_div_iff₀ hc).1 hsT
    have hdu : DifferentiableAt ℝ (u t) x := h.differentiableAt_velocity ht htT x
    have hdp : DifferentiableAt ℝ (p t) x := h.differentiableAt_pressure ht htT x
    have hdt : DifferentiableAt ℝ (fun σ => u σ x) t := h.differentiableAt_time ht htT x
    have hchain : HasDerivAt (fun σ : ℝ => c • u (c * σ) x) ((c * c) • deriv (fun σ => u σ x) t)
        s := by
      have h1 : HasDerivAt (fun σ : ℝ => c * σ) c s := by
        simpa using (hasDerivAt_id s).const_mul c
      have h2 : HasDerivAt (fun σ : ℝ => u σ x) (deriv (fun σ => u σ x) t) t := hdt.hasDerivAt
      have h3 : HasDerivAt ((fun σ : ℝ => u σ x) ∘ fun σ : ℝ => c * σ)
          (c • deriv (fun σ => u σ x) t) s := HasDerivAt.scomp s h2 h1
      have h4 := h3.const_smul c
      rw [smul_smul] at h4
      exact h4
    have hut : timeDeriv u t x = deriv (fun σ => u σ x) t := timeDeriv_eq_deriv ht x
    have htd : timeDeriv (fun s x => c • u (c * s) x) s x = (c * c) • deriv (fun σ => u σ x) t := by
      rw [timeDeriv_eq_deriv hs x]; exact hchain.deriv
    have hconv : convection (fun y => c • u t y) x = (c * c) • convection (u t) x :=
      convection_const_smul c hdu
    have hgrad : ∇ (fun y => c ^ 2 * p t y) x = (c ^ 2) • ∇ (p t) x := by
      simpa using gradient_const_smul (c ^ 2) hdp
    have hlap : Δ (fun y => c • u t y) x = c • Δ (u t) x :=
      InnerProductSpace.laplacian_smul (F := Space) c
        ((h.contDiffAt_velocity ht htT x).of_le IsClassicalSolution.two_le_infty)
    have key : deriv (fun σ => u σ x) t + convection (u t) x + ∇ (p t) x = ν • Δ (u t) x := by
      rw [← hut]; exact h.momentum t x ht htT
    show timeDeriv (fun s x => c • u (c * s) x) s x + convection (fun y => c • u t y) x
        + ∇ (fun y => c ^ 2 * p t y) x = (c * ν) • Δ (fun y => c • u t y) x
    have hc2 : (c : ℝ) ^ 2 = c * c := sq c
    rw [htd, hconv, hgrad, hc2, ← smul_add, ← smul_add, key, hlap, smul_smul, smul_smul]
    congr 1
    ring
  incompressible := by
    intro s x hs hsT
    set t : ℝ := c * s with ht_def
    have ht : 0 < t := mul_pos hc hs
    have htT : t < T := by
      rw [ht_def, mul_comm]; exact (lt_div_iff₀ hc).1 hsT
    have hdu : DifferentiableAt ℝ (u t) x := h.differentiableAt_velocity ht htT x
    rw [divergence_const_smul c hdu, h.incompressible t x ht htT, mul_zero]

/-! ## The `ν ↦ 1` global normalization, PLAN `eq:nu-normalization` -/

/-- **`IsGlobalSmoothSolution.rescale_iff`, PLAN `eq:nu-normalization`.** The
family `IsGlobalSmoothSolution.rescale` is invertible (`c ↦ c⁻¹`): existence
of a global smooth solution with viscosity `ν > 0` and datum `d` is
equivalent to existence of one with viscosity `1` and datum `ν⁻¹ • d`. This
is the datum-existence form of the missing global normalization identified in
the `Blowup.lean` lane report, matching `IsClassicalSolution.nuNormalization`
at the level of existence statements. -/
theorem IsGlobalSmoothSolution.rescale_iff {ν : ℝ} (hν : 0 < ν) (d : Space → Space) :
    (∃ v q, IsGlobalSmoothSolution ν d v q) ↔
      (∃ v q, IsGlobalSmoothSolution 1 (fun x => ν⁻¹ • d x) v q) := by
  constructor
  · rintro ⟨v, q, hvq⟩
    have hrw := hvq.rescale (inv_pos.2 hν)
    rw [inv_mul_cancel₀ hν.ne'] at hrw
    exact ⟨_, _, hrw⟩
  · rintro ⟨v, q, hvq⟩
    have hrw := hvq.rescale hν
    rw [mul_one] at hrw
    have heq : (fun x => ν • (ν⁻¹ • d x)) = d := by
      funext x; rw [smul_smul, mul_inv_cancel₀ hν.ne', one_smul]
    rw [heq] at hrw
    exact ⟨_, _, hrw⟩

/-! ## The `UnforcedCounterexample` normalization, PLAN `8.2a` main deliverable -/

/-- **The general one-parameter rescaling of `UnforcedCounterexample`.** If
`UnforcedCounterexample ν` holds and `c > 0`, then `UnforcedCounterexample
(c·ν)` holds, via the rescaled datum `d.smul c`, window `T/c`, and fields
`(v,q) = (c•u(c·-), c²·p(c·-))`: nonvanishing of the datum
(`SchwartzDivFree.smul_ne_zero`), positivity of the window, the classical
solution property (`IsClassicalSolution.rescale`), uniformly finite energy
(`UniformFiniteEnergyOn.rescale`), pointwise-unbounded speed
(`SpeedUnboundedAt.rescale`), and the non-existence clause, which is proved by
inverting the rescaling (`c⁻¹`) on a hypothetical global solution at `c·ν` to
produce one at `ν`, contradicting the `ν`-instance's non-existence clause.
This closes both gaps (a), (b) of the `Blowup.lean` lane report. -/
theorem UnforcedCounterexample.rescale {ν c : ℝ} (hc : 0 < c)
    (h : UnforcedCounterexample ν) : UnforcedCounterexample (c * ν) := by
  obtain ⟨d, T, u, p, hd, hT, hsol, hufe, hspeed, hno⟩ := h
  refine ⟨d.smul c, T / c, fun s x => c • u (c * s) x, fun s x => c ^ 2 * p (c * s) x,
    SchwartzDivFree.smul_ne_zero hc.ne' hd, div_pos hT hc, ?_, hufe.rescale hc, hspeed.rescale hc,
    ?_⟩
  · have := hsol.rescale hc
    simpa [SchwartzDivFree.coe_smul] using this
  · rintro ⟨v, q, hex⟩
    apply hno
    have hex' : IsGlobalSmoothSolution (c * ν) (⇑(d.smul c)) v q := hex
    have hrw := hex'.rescale (inv_pos.2 hc)
    rw [show c⁻¹ * (c * ν) = ν from by field_simp] at hrw
    have heq : (fun x => c⁻¹ • (⇑(d.smul c) : Space → Space) x) = (⇑d : Space → Space) := by
      funext x
      simp only [SchwartzDivFree.coe_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    rw [heq] at hrw
    exact ⟨_, _, hrw⟩

/-- **PLAN `8.2a` main deliverable, `ν ↦ 1`.** An `UnforcedCounterexample` at
any viscosity `ν > 0` normalizes to one at viscosity `1`, completing the
`UnforcedCounterexample` half of `eq:nu-normalization` left unfinished by the
`Blowup.lean` lane (its `nuNormalization_energy` proves only the datum,
window, classical-solution, and energy clauses, not the speed or
non-existence clauses). -/
theorem UnforcedCounterexample.nuNormalization {ν : ℝ} (hν : 0 < ν)
    (h : UnforcedCounterexample ν) : UnforcedCounterexample 1 := by
  have := h.rescale (inv_pos.2 hν)
  rwa [inv_mul_cancel₀ hν.ne'] at this

/-- **The converse of `nuNormalization`, `1 ↦ ν`.** This is exactly gap (b)
of the `Blowup.lean` lane report: `IsClassicalSolution.nuNormalization`
supplies only the forward `ν ↦ 1` direction. -/
theorem UnforcedCounterexample.of_nuNormalization {ν : ℝ} (hν : 0 < ν)
    (h : UnforcedCounterexample 1) : UnforcedCounterexample ν := by
  have := h.rescale hν
  rwa [mul_one] at this

/-- `UnforcedCounterexampleSome` is equivalent to `UnforcedCounterexample 1`:
forward by `nuNormalization` at the witnessing viscosity, backward by the
trivial witness `ν = 1`. -/
theorem unforcedCounterexampleSome_iff : UnforcedCounterexampleSome ↔ UnforcedCounterexample 1 :=
  ⟨fun ⟨_ν, hν, h⟩ => h.nuNormalization hν, fun h => ⟨1, one_pos, h⟩⟩

/-- `UnforcedCounterexampleAll` is equivalent to `UnforcedCounterexample 1`:
forward by specializing to `ν = 1`, backward by `of_nuNormalization` at every
`ν > 0`. -/
theorem unforcedCounterexampleAll_iff : UnforcedCounterexampleAll ↔ UnforcedCounterexample 1 :=
  ⟨fun h => h 1 one_pos, fun h _ν hν => h.of_nuNormalization hν⟩

end NavierFormal
