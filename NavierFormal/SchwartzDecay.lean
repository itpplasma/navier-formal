import NavierFormal.SolutionClass
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Fefferman's admissible-datum decay condition (4) and the Schwartz class

This module formalizes Step 0 ("the data class") of the proof of the
manuscript's `thm:conditional` (`../navier-paper/main.tex`), and the datum
clause of `premise:local`: the equivalence between Fefferman's admissible
decay condition (4),
`|∂_x^α u₀(x)| ≤ C_{αK}(1+|x|)^{-K}` on `ℝ³` for every multi-index `α` and
every real `K` [Fefferman2000, p. 57], and membership `u₀ ∈ 𝒮(ℝ³)³` in the
Schwartz class.  In the Formal Conjectures reference formulation this decay
clause is
`∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K`
(`InitialVelocityConditionDecay`), where `^ K` is `Real.rpow`; note that for
`K < 0` this reads as a *weaker* bound than for `K ≥ 0`, since
`(1 + ‖x‖) ^ K ≤ 1` there.

Objects and results proved here.

* `SchwartzMap.decay_fefferman` — every Schwartz map satisfies the Fefferman
  decay clause, for general normed spaces `E`, `F`.  This is the forward
  half of the manuscript's Step 0 equivalence, in the quantitative form used
  there: given a real `K`, set `k := ⌈K⌉₊` and bound
  `(1+‖x‖)^k ‖∂^m f(x)‖` by a Schwartz seminorm
  (`SchwartzMap.one_add_le_sup_seminorm_apply`), then use
  `(1+‖x‖)^K ≤ (1+‖x‖)^k` (since `1 + ‖x‖ ≥ 1` and `K ≤ k`).
* `SchwartzMap.ofDecay` — the converse: a `C^∞` function satisfying the
  Fefferman decay clause for all `m, K` is (packaged as) a Schwartz map.  The
  structure's `decay'` field asks for polynomial bounds in `‖x‖^k`, obtained
  from the hypothesis at `K = k` via `‖x‖^k ≤ (1+‖x‖)^k`.
* `SchwartzDivFree.decay_fefferman` — the specialization to
  `NavierFormal.SchwartzDivFree` (`Space = EuclideanSpace ℝ (Fin 3)`),
  packaging exactly the three `InitialVelocityConditionDecay`-shaped clauses
  used in Step 0: smoothness `ContDiff ℝ ∞ ⇑u₀`, pointwise
  incompressibility `divergence ⇑u₀ x = 0`, and the decay clause.
* `SchwartzDivFree.ofFefferman` — the converse constructor of an admissible
  datum from smoothness, divergence-freeness, and the Fefferman decay clause.

Fidelity notes.  The manuscript's condition (4) is stated for integer
multi-indices `α` and directional partial derivatives; here, as throughout
this development, derivatives are the Mathlib `iteratedFDeriv ℝ m` of order
`m : ℕ` (all directions at once), which controls every partial derivative of
order `≤ m` and is controlled by them, so no strength is gained or lost.
`SchwartzMap` is `C^∞` (`ContDiff ℝ ∞`, i.e. `ContDiff ℝ ⊤` in `ℕ∞ω`), matching
the manuscript's "smooth divergence-free field" (`eq:NS`, `premise:local`).

Nothing here asserts existence of a solution; no Millennium-problem claim is
made in this file.
-/

open scoped SchwartzMap ContDiff

namespace NavierFormal

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Step 0, forward direction** (`thm:conditional`, Fefferman condition (4)).
Every Schwartz map satisfies Fefferman's decay clause: for every derivative
order `m` and every real `K` there is `C` with
`‖∂^m f(x)‖ ≤ C / (1+‖x‖)^K` for all `x`, where `^ K` is `Real.rpow`.

Proof: with `k := ⌈K⌉₊`, `SchwartzMap.one_add_le_sup_seminorm_apply` bounds
`(1+‖x‖)^k ‖∂^m f(x)‖` by a fixed Schwartz seminorm value `C`; since
`K ≤ (k:ℝ)` (`Nat.le_ceil`) and `1 + ‖x‖ ≥ 1`, monotonicity of `rpow` in the
exponent gives `(1+‖x‖)^K ≤ (1+‖x‖)^k`, hence `C/(1+‖x‖)^k ≤ C/(1+‖x‖)^K`. -/
theorem SchwartzMap.decay_fefferman (f : 𝓢(E, F)) (m : ℕ) (K : ℝ) :
    ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv ℝ m f x‖ ≤ C / (1 + ‖x‖) ^ K := by
  set k : ℕ := ⌈K⌉₊ with hk_def
  set C : ℝ := 2 ^ k * (Finset.Iic ((k, m) : ℕ × ℕ)).sup
      (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f with hC_def
  have hbound : ∀ x : E, (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ C :=
    fun x => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, m))
      (k := k) (n := m) le_rfl le_rfl f x
  have hC0 : 0 ≤ C := by
    have h0 := hbound 0
    have h1 : (1 : ℝ) ≤ (1 + ‖(0 : E)‖) ^ k := by simp
    nlinarith [norm_nonneg (iteratedFDeriv ℝ m f (0 : E))]
  refine ⟨C, fun x => ?_⟩
  have hpos : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hposk : (0 : ℝ) < (1 + ‖x‖) ^ k := by positivity
  have hderiv : ‖iteratedFDeriv ℝ m f x‖ ≤ C / (1 + ‖x‖) ^ k := by
    rw [le_div_iff₀ hposk]
    have := hbound x
    linarith [this]
  have hKk : K ≤ (k : ℝ) := Nat.le_ceil K
  have hrpow : (1 + ‖x‖) ^ K ≤ (1 + ‖x‖) ^ (k : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) hKk
  have hcast : (1 + ‖x‖) ^ (k : ℝ) = (1 + ‖x‖) ^ k := Real.rpow_natCast _ k
  have hKpos : (0 : ℝ) < (1 + ‖x‖) ^ K := Real.rpow_pos_of_pos hpos K
  calc ‖iteratedFDeriv ℝ m f x‖
      ≤ C / (1 + ‖x‖) ^ k := hderiv
    _ = C / (1 + ‖x‖) ^ (k : ℝ) := by rw [hcast]
    _ ≤ C / (1 + ‖x‖) ^ K := div_le_div_of_nonneg_left hC0 hKpos hrpow

/-- **Step 0, converse direction** (`thm:conditional`, Fefferman condition
(4)).  A `C^∞` function satisfying the Fefferman decay clause for all `m, K`
is the underlying function of a Schwartz map.

Proof: the structure's `decay'` field at `(k,n)` asks for a bound on
`‖x‖^k ‖∂^n f(x)‖`; specializing the hypothesis at `K = (k:ℝ)` gives
`C` with `‖∂^n f(x)‖ ≤ C/(1+‖x‖)^k` (as `Real.rpow`, rewritten to the natural
power via `Real.rpow_natCast`), and `‖x‖^k ≤ (1+‖x‖)^k` finishes it. -/
noncomputable def SchwartzMap.ofDecay (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hdecay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x : E,
      ‖iteratedFDeriv ℝ m f x‖ ≤ C / (1 + ‖x‖) ^ K) : 𝓢(E, F) where
  toFun := f
  smooth' := hf
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := hdecay n (k : ℝ)
    refine ⟨max C 0, fun x => ?_⟩
    have hpos : (0 : ℝ) < 1 + ‖x‖ := by positivity
    have hposk : (0 : ℝ) < (1 + ‖x‖) ^ k := by positivity
    have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    have hcast : (1 + ‖x‖) ^ (k : ℝ) = (1 + ‖x‖) ^ k := Real.rpow_natCast _ k
    have hbound : ‖iteratedFDeriv ℝ n f x‖ ≤ C / (1 + ‖x‖) ^ k := by
      have := hC x
      rwa [hcast] at this
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
        ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ :=
          mul_le_mul_of_nonneg_right hxk (norm_nonneg _)
      _ ≤ (1 + ‖x‖) ^ k * (C / (1 + ‖x‖) ^ k) :=
          mul_le_mul_of_nonneg_left hbound (le_of_lt hposk)
      _ = C := by field_simp
      _ ≤ max C 0 := le_max_left _ _

@[simp] theorem SchwartzMap.coe_ofDecay (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hdecay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x : E,
      ‖iteratedFDeriv ℝ m f x‖ ≤ C / (1 + ‖x‖) ^ K) :
    ⇑(SchwartzMap.ofDecay f hf hdecay) = f := rfl

/-- **Step 0 of `thm:conditional`, specialized to the datum class**: an
admissible datum `u₀ : SchwartzDivFree` (Fefferman's smooth divergence-free
field, `eq:NS`, `premise:local`) satisfies exactly the three
`InitialVelocityConditionDecay`-shaped clauses of the Formal Conjectures
reference formulation: `C^∞` smoothness, pointwise incompressibility, and
Fefferman's decay condition (4). -/
theorem SchwartzDivFree.decay_fefferman (u₀ : SchwartzDivFree) :
    ContDiff ℝ ∞ (⇑u₀ : Space → Space) ∧
      (∀ x : Space, divergence (⇑u₀ : Space → Space) x = 0) ∧
      ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x : Space,
        ‖iteratedFDeriv ℝ m (⇑u₀ : Space → Space) x‖ ≤ C / (1 + ‖x‖) ^ K :=
  ⟨u₀.toSchwartz.smooth', u₀.div_free, SchwartzMap.decay_fefferman u₀.toSchwartz⟩

/-- **Step 0 of `thm:conditional`, converse constructor**: a smooth,
divergence-free field on `Space = ℝ³` satisfying Fefferman's decay condition
(4) for all orders `m` and all real `K` is an admissible datum
`SchwartzDivFree`. -/
noncomputable def SchwartzDivFree.ofFefferman (u₀ : Space → Space)
    (hsmooth : ContDiff ℝ ∞ u₀) (hdiv : ∀ x : Space, divergence u₀ x = 0)
    (hdecay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x : Space,
      ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K) : SchwartzDivFree where
  toSchwartz := SchwartzMap.ofDecay u₀ hsmooth hdecay
  div_free := hdiv

end

end NavierFormal
