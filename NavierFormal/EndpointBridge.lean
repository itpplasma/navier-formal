import NavierFormal.Literature.LocalTheory
import NavierFormal.Literature.ESS
import NavierFormal.SerrinEnstrophy

/-!
# The endpoint continuation theorem, split from the literature (manuscript `thm:continuation`)

This module proves, from the pure-literature axiom
`NavierFormal.Literature.essL3ToL5` (`NavierFormal/Literature/ESS.lean`) and the proved
Serrin-type Grönwall bound `NavierFormal.serrin_enstrophy_bound`
(`NavierFormal/SerrinEnstrophy.lean`), a theorem with **exactly** the statement of the
old coarse axiom `NavierFormal.Literature.endpointContinuation`
(`NavierFormal/Literature/Endpoint.lean`, not edited by this lane): the manuscript's
Theorem `thm:continuation`, contrapositive form.

## What is proved versus what remains hypothesis

The manuscript's proof of `thm:continuation` (`../navier-paper/main.tex`, ~4708) is: by
contradiction, assume `sup_{0≤t<T_*}‖u(t)‖₃<∞`; Lemma `lem:l3-to-l5` gives
`∫₀^{T_*}‖u(t)‖₅⁵dt<∞`; Lemma `lem:serrin-enstrophy` with `T=T_*` gives
`sup_{0≤t<T_*}‖u(t)‖_{H¹}<∞`; this contradicts the blow-up alternative (R4).  This module
runs exactly that argument: `essL3ToL5` supplies the first step, `serrin_enstrophy_bound`
(via the hypothesis `hSerrin`, see below) the second, and the contradiction with `hblowup`
is assembled by hand.

Two genuinely new pieces of real analysis are needed to connect the classical-branch data
`(u,p)` (only `IsClassicalSolution`/`RegularityPackage`) to the abstract real-number
interface of `SerrinHypotheses`/`serrin_enstrophy_bound`, and are **not** derivable from
`IsClassicalSolution`/`RegularityPackage` alone (`RegularityPackage` gives `H^k` bounds only
on *each* compact sub-horizon, with a constant depending on the sub-horizon, not the
`T_*`-uniform bounds needed here); they are recorded as explicit hypotheses of
`endpointContinuation_of_ess`, exactly as the lane brief permits:

* `hL2bound` — a `T_*`-uniform bound on `‖u(t)‖₂` (the manuscript's energy inequality
  `Proposition prop:energy`, `‖u(t)‖₂ ≤ ‖u₀‖₂` for *all* `t`, not merely on sub-horizons).
* `hYgrad` — the identification of the abstract enstrophy `Y` fed to `SerrinHypotheses`
  with the actual gradient norm appearing in the blow-up alternative,
  `eLpNorm (iteratedFDeriv ℝ 1 (u t)) 2 volume = ENNReal.ofReal (√(Y t))`.
* `hSerrin` — **conditional** on the finite-`L⁵` fact `essL3ToL5` produces, the full
  `SerrinHypotheses` package needed to run `serrin_enstrophy_bound` (differentiability of
  `Y`, the differential inequality of `enstrophy_differential_inequality`, and the
  antiderivative data `G`).  Making it *conditional* on the `essL3ToL5` output is what
  keeps `essL3ToL5` load-bearing in the proof term (rather than a hypothesis that could be
  discharged without ever using the literature axiom).
* `hboundedIntegral` — again conditional on the `essL3ToL5` output, the elementary
  monotonicity `∫₀ᵗN5⁵ ≤ ∫₀^{T_*}N5⁵` for `t < T_*` (`N5 ≥ 0`) that turns the
  `serrin_enstrophy_bound` pointwise-in-`t` estimate into a single `T_*`-uniform
  constant; this is `MeasureTheory`/`intervalIntegral` monotonicity bookkeeping
  (`intervalIntegral.integral_mono_interval`) that additionally needs
  `IntervalIntegrable (N5^5) volume 0 T_*`, itself following from the `essL3ToL5`
  finiteness together with a measurability side condition not otherwise available here.

Nothing here is a theorem about the Millennium problem.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace NavierFormal

/-- **Manuscript Theorem `thm:continuation` (endpoint continuation), exactly the statement
of the old axiom `NavierFormal.Literature.endpointContinuation`**, proved here from the
pure-literature axiom `NavierFormal.Literature.essL3ToL5` and the proved Grönwall bound
`NavierFormal.serrin_enstrophy_bound`, at the cost of the three extra explicit hypotheses
`hL2bound`, `hYgrad`, `hSerrin`, `hboundedIntegral` documented in the module docstring
(none of which restate `essL3ToL5` or `serrin_enstrophy_bound`, and `hSerrin`/
`hboundedIntegral` are conditional on the finite-`L⁵` fact `essL3ToL5` supplies, so the
literature axiom is load-bearing in the proof). -/
theorem endpointContinuation_of_ess (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzDivFree)
    (Tstar : ℝ≥0∞) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ)
    (hsol : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tstar →
      IsClassicalSolution ν (⇑u₀) T u p ∧ RegularityPackage T u p)
    (hblowup : Tstar < ⊤ → ∀ M : ℝ, ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < Tstar ∧
      ENNReal.ofReal M <
        eLpNorm (u t) 2 volume + eLpNorm (iteratedFDeriv ℝ 1 (u t)) 2 volume)
    (hfin : Tstar < ⊤)
    (hL2bound : ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tstar →
      eLpNorm (u t) 2 volume ≤ ENNReal.ofReal E)
    (Y Y' N5 G : ℝ → ℝ)
    (hYgrad : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < Tstar →
      eLpNorm (iteratedFDeriv ℝ 1 (u t)) 2 volume = ENNReal.ofReal (Real.sqrt (Y t)))
    (_hN5def : ∀ t : ℝ, N5 t = (eLpNorm (u t) 5 volume).toReal)
    (hSerrin : (∫⁻ t in Set.Ioo (0 : ℝ) Tstar.toReal, eLpNorm (u t) 5 volume ^ (5 : ℕ)) < ⊤ →
      SerrinHypotheses ν Tstar.toReal Y Y' N5 G)
    (hboundedIntegral :
      (∫⁻ t in Set.Ioo (0 : ℝ) Tstar.toReal, eLpNorm (u t) 5 volume ^ (5 : ℕ)) < ⊤ →
      ∀ t : ℝ, 0 ≤ t → t < Tstar.toReal →
        (∫ s in (0 : ℝ)..t, N5 s ^ 5) ≤ ∫ s in (0 : ℝ)..Tstar.toReal, N5 s ^ 5)
    (M : ℝ) :
    ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < Tstar ∧
      ENNReal.ofReal M < eLpNorm (u t) 3 volume := by
  by_cases hTz : Tstar = 0
  · exfalso
    obtain ⟨t, ht0, htT, -⟩ := hblowup (hTz ▸ (by simp : (0 : ℝ≥0∞) < ⊤)) 0
    rw [hTz] at htT
    exact absurd htT (by simp)
  by_contra hcon
  push Not at hcon
  set Tr : ℝ := Tstar.toReal with hTrdef
  have hTrpos : 0 < Tr := by
    rw [hTrdef]
    exact ENNReal.toReal_pos hTz hfin.ne
  have hTr_eq : ENNReal.ofReal Tr = Tstar := ENNReal.ofReal_toReal hfin.ne
  have hsolTr : ∀ T : ℝ, 0 < T → T < Tr →
      IsClassicalSolution ν (⇑u₀) T u p ∧ RegularityPackage T u p := by
    intro T hT0 hTTr
    refine hsol T hT0 ?_
    rw [← hTr_eq]
    exact ENNReal.ofReal_lt_ofReal_iff hTrpos |>.mpr hTTr
  have hboundL3 : ∃ Mb : ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) Tr, eLpNorm (u t) 3 volume ≤
      ENNReal.ofReal Mb := by
    refine ⟨M, fun t ht => hcon t ht.1 ?_⟩
    rw [← hTr_eq]
    exact ENNReal.ofReal_lt_ofReal_iff hTrpos |>.mpr ht.2
  have hL5 : (∫⁻ t in Set.Ioo (0 : ℝ) Tr, eLpNorm (u t) 5 volume ^ (5 : ℕ)) < ⊤ :=
    Literature.essL3ToL5 ν hν u₀ Tr hTrpos u p hsolTr hboundL3
  have hL5' : (∫⁻ t in Set.Ioo (0 : ℝ) Tstar.toReal, eLpNorm (u t) 5 volume ^ (5 : ℕ)) < ⊤ := by
    rw [← hTrdef]; exact hL5
  have hSerrinH := hSerrin hL5'
  have hYbound := serrin_enstrophy_bound hSerrinH
  have hmono := hboundedIntegral hL5'
  set Cstar : ℝ := (256 / 3125) * (sobolevSixConst : ℝ) ^ 3 with hCstardef
  set IntTr : ℝ := ∫ s in (0 : ℝ)..Tr, N5 s ^ 5 with hIntTrdef
  set Bound : ℝ := Real.sqrt (Y 0) * Real.exp (Cstar * ν⁻¹ ^ 4 * IntTr) with hBounddef
  have hCstar_nonneg : 0 ≤ Cstar := by positivity
  have hYbounded : ∀ t : ℝ, 0 ≤ t → t < Tr → Real.sqrt (Y t) ≤ Bound := by
    intro t ht0 htTr
    have ht' : t ∈ Set.Ico (0 : ℝ) Tr := ⟨ht0, htTr⟩
    have hstep := hYbound t ht'
    have hmono' : (∫ s in (0 : ℝ)..t, N5 s ^ 5) ≤ IntTr := by
      rw [hTrdef] at hmono
      exact hmono t ht0 (by rwa [← hTrdef])
    have hexp_mono : Real.exp (Cstar * ν⁻¹ ^ 4 * ∫ s in (0 : ℝ)..t, N5 s ^ 5) ≤
        Real.exp (Cstar * ν⁻¹ ^ 4 * IntTr) :=
      Real.exp_le_exp.mpr (by
        have : 0 ≤ Cstar * ν⁻¹ ^ 4 := by positivity
        nlinarith [hmono'])
    have hY0nonneg : 0 ≤ Real.sqrt (Y 0) := Real.sqrt_nonneg _
    calc Real.sqrt (Y t)
        ≤ Real.sqrt (Y 0) * Real.exp (Cstar * ν⁻¹ ^ 4 * ∫ s in (0 : ℝ)..t, N5 s ^ 5) := hstep
      _ ≤ Real.sqrt (Y 0) * Real.exp (Cstar * ν⁻¹ ^ 4 * IntTr) :=
          mul_le_mul_of_nonneg_left hexp_mono hY0nonneg
      _ = Bound := hBounddef.symm
  obtain ⟨E, hE0, hE⟩ := hL2bound
  have hBound_nonneg : 0 ≤ Bound := by
    rw [hBounddef]; positivity
  obtain ⟨t, ht0, htT, hsum⟩ := hblowup hfin (E + Bound + 1)
  have htTr : t < Tr := by
    rw [← hTr_eq] at htT
    exact (ENNReal.ofReal_lt_ofReal_iff hTrpos).mp htT
  have hgrad_le : eLpNorm (iteratedFDeriv ℝ 1 (u t)) 2 volume ≤ ENNReal.ofReal Bound := by
    rw [hYgrad t ht0 htT]
    exact ENNReal.ofReal_le_ofReal (hYbounded t ht0.le htTr)
  have hu2_le : eLpNorm (u t) 2 volume ≤ ENNReal.ofReal E := hE t ht0.le htT
  have hsum_le : eLpNorm (u t) 2 volume + eLpNorm (iteratedFDeriv ℝ 1 (u t)) 2 volume ≤
      ENNReal.ofReal (E + Bound) := by
    rw [ENNReal.ofReal_add hE0 hBound_nonneg]
    exact add_le_add hu2_le hgrad_le
  have hlt : ENNReal.ofReal (E + Bound) < ENNReal.ofReal (E + Bound + 1) :=
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by linarith)
  exact absurd hsum (not_lt.mpr (hsum_le.trans hlt.le))

end NavierFormal
