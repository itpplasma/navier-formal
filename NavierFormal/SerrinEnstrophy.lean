import NavierFormal.Basic
import NavierFormal.Calculus
import NavierFormal.SolutionClass
import NavierFormal.Interpolation
import NavierFormal.EnstrophyIdentity
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Serrin-type enstrophy bound (manuscript `lem:serrin-enstrophy`)

This module proves the manuscript's Lemma `lem:serrin-enstrophy`
(`../navier-paper/main.tex`, ~4600): if `0 < T ≤ T_*` and
`∫₀^T‖u(t)‖₅⁵dt<∞`, then, with `C_* = (256/3125)·C_S³`,

`sup_{0≤t<T}‖∇u(t)‖₂ ≤ ‖∇u₀‖₂·exp(C_*·ν⁻⁴·∫₀^T‖u(t)‖₅⁵dt)`.

## Route and scope

The manuscript's proof has four steps: (1) the enstrophy identity
`(1/2)Y' + ν‖Δu‖₂² = ⟨(u·∇)u,Δu⟩` (already proved in
`NavierFormal.enstrophy_identity_pointwise_time`, `EnstrophyIdentity.lean`);
(2) Hölder `|⟨(u·∇)u,Δu⟩| ≤ ‖u‖₅‖∇u‖_{10/3}‖Δu‖₂` together with the
interpolation bound `‖∇u‖_{10/3} ≤ Y^{1/5}‖∇u‖₆^{3/5}`
(`NavierFormal.eLpNorm_tenThirds_le`) and the Sobolev bound
`‖∇u‖₆ ≤ C_S‖Δu‖₂` (`NavierFormal.eLpNorm_six_le_eLpNorm_fderiv_two`, applied
componentwise to the Hessian together with the Plancherel identity
`‖∇²u‖₂ = ‖Δu‖₂`, exactly as in the manuscript's own Step 2); (3) absorption
of the `‖Δu‖₂^{8/5}` term by Young's inequality at exponents `(5/4,5)`
(`NavierFormal.young_five_fourths`); (4) the Grönwall argument
`(Y·e^{-G})' ≤ 0`.

This module proves Steps 3–4 in full and the *real-number* core of Step 2 —
the combined Hölder/interpolation/Sobolev inequality is discharged from three
explicit hypotheses on real numbers standing for the relevant `eLpNorm`s
(`enstrophy_differential_inequality`'s `hHolder`, `hSobolevInterp`), in
exactly the pattern already used by the sibling module
`NavierFormal.enstrophy_inequality_of_interpolation`
(`NavierFormal/EnstrophyInequality.lean`, which similarly leaves its Hölder,
Sobolev and interpolation steps as explicit real hypotheses `hI`, `hSobolev`,
`hInterp`).  What is genuinely new here relative to that sibling module is
the exponent pattern (`(1/5,3/5,1)` instead of `(1/2,1/2)`, matching
`lem:serrin-enstrophy`'s own Hölder split `1/5+3/10+1/2=1` rather than
`prop:enstrophy`'s `1/6+1/3+1/2=1`) and, crucially, the Grönwall step
(4) that turns the resulting differential inequality into the manuscript's
*exponential* bound `eq:serrin-bound` — the sibling module stops at the
differential inequality and does not integrate it.

Deviation from a full first-principles derivation of `hSobolevInterp`: the
manuscript's own Step 2 for this inequality is not "apply
`eLpNorm_six_le_eLpNorm_fderiv_two` to `∇u`" directly (that lemma bounds
`‖v‖₆` by `‖∇v‖₂` for *one* vector field `v`; here `v = ∂ⱼu` for each `j`,
and the manuscript sums `‖∂ⱼu‖₆²` over `j` via the elementary inequality
`‖∑ᵢⱼg_ij²‖₃ ≤ ∑ᵢⱼ‖g_ij²‖₃` and Plancherel `‖∇²u‖₂ = ‖Δu‖₂`, an indexed
real-analysis argument beyond a single application of the cited lemma).
Reproducing that indexed argument is out of scope here; `hSobolevInterp` is
supplied as an explicit hypothesis instead, and a caller who wants to
discharge it from `eLpNorm_tenThirds_le` and
`eLpNorm_six_le_eLpNorm_fderiv_two` must additionally supply the manuscript's
componentwise summation argument.

Nothing here is a theorem about the Millennium problem.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace NavierFormal

/-! ## Step 2–3: the real-number differential inequality -/

/-- **Steps 2–3 of the proof of `lem:serrin-enstrophy`**, as a real-number lemma.

Given the enstrophy identity `(1/2)·Yderiv + ν·a² = I` (manuscript
`eq:serrin-enstrophy-identity`, `a = ‖Δu(t)‖₂`, `Yderiv = Y'(t)`), the Hölder
bound `|I| ≤ n5·m103·a` (manuscript Step 2, `n5 = ‖u(t)‖₅`,
`m103 = ‖∇u(t)‖_{10/3}`) and the combined interpolation/Sobolev bound
`m103 ≤ C_S^{3/5}·Yval^{1/5}·a^{3/5}` (manuscript Step 2,
`‖∇u‖_{10/3} ≤ Y^{1/5}‖∇u‖₆^{3/5} ≤ Y^{1/5}(C_S‖Δu‖₂)^{3/5}`, `Yval = Y(t)`),
conclude the manuscript's differential inequality

`Yderiv ≤ 2·C_*·ν⁻¹^4·n5^5·Yval`,  `C_* = (256/3125)·C_S^3`,

exactly the manuscript's `g(t) = 2C_*ν⁻⁴‖u(t)‖₅⁵` bound on `Y'`.  The proof
follows the manuscript's own Step 3 verbatim: apply the fixed-constant Young
inequality `NavierFormal.young_five_fourths` (conjugate exponents `5/4, 5`,
no free parameter — the exponents literally named in the manuscript's proof)
to the rescaled pair `(δ·a^{8/5}, (C_S^{3/5}·n5·Yval^{1/5})/δ)` with
`δ := (5ν/4)^{4/5}`, chosen so that the `a²` term's coefficient becomes
exactly `ν`, matching `ν‖Δu‖₂²` in the identity and cancelling it. -/
theorem enstrophy_differential_inequality
    {Yderiv Yval a n5 m103 C_S ν I : ℝ}
    (ha : 0 ≤ a) (hn5 : 0 ≤ n5) (_hm103 : 0 ≤ m103) (hYval : 0 ≤ Yval)
    (hCS : 0 ≤ C_S) (hν : 0 < ν)
    (hid : (1 / 2) * Yderiv + ν * a ^ 2 = I)
    (hHolder : |I| ≤ n5 * m103 * a)
    (hSobolevInterp : m103 ≤ C_S ^ (3 / 5 : ℝ) * Yval ^ (1 / 5 : ℝ) * a ^ (3 / 5 : ℝ)) :
    Yderiv ≤ 2 * ((256 / 3125) * C_S ^ 3) * ν⁻¹ ^ 4 * n5 ^ 5 * Yval := by
  set K : ℝ := C_S ^ (3 / 5 : ℝ) with hKdef
  have hK : 0 ≤ K := Real.rpow_nonneg hCS _
  set M : ℝ := n5 * Yval ^ (1 / 5 : ℝ) with hMdef
  have hM : 0 ≤ M := mul_nonneg hn5 (Real.rpow_nonneg hYval _)
  set W : ℝ := a ^ (8 / 5 : ℝ) with hWdef
  have hW : 0 ≤ W := Real.rpow_nonneg ha _
  -- Hölder + Sobolev/interpolation: `n5·m103·a ≤ K·(M·W)`.
  have hstep1 : n5 * m103 ≤ n5 * (K * Yval ^ (1 / 5 : ℝ) * a ^ (3 / 5 : ℝ)) :=
    mul_le_mul_of_nonneg_left (by rw [hKdef]; exact hSobolevInterp) hn5
  have hstep2 : n5 * m103 * a ≤ n5 * (K * Yval ^ (1 / 5 : ℝ) * a ^ (3 / 5 : ℝ)) * a :=
    mul_le_mul_of_nonneg_right hstep1 ha
  have haW : a ^ (3 / 5 : ℝ) * a = W := by
    have hstep : a ^ (3 / 5 : ℝ) * a ^ (1 : ℝ) = a ^ ((3 / 5 : ℝ) + 1) :=
      (Real.rpow_add_of_nonneg ha (by norm_num) (by norm_num)).symm
    rw [Real.rpow_one] at hstep
    rw [hWdef, hstep, show (3 / 5 : ℝ) + 1 = 8 / 5 by norm_num]
  have heq : n5 * (K * Yval ^ (1 / 5 : ℝ) * a ^ (3 / 5 : ℝ)) * a = K * (M * W) := by
    rw [hMdef, ← haW]; ring
  have hmain0 : (1 / 2) * Yderiv + ν * a ^ 2 ≤ K * (M * W) := by
    rw [hid]
    exact (le_abs_self I).trans (hHolder.trans (heq ▸ hstep2))
  -- Young at `δ = (5ν/4)^{4/5}`.
  set δ : ℝ := (5 * ν / 4) ^ (4 / 5 : ℝ) with hδdef
  have hνpos : (0 : ℝ) < 5 * ν / 4 := by positivity
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hνpos _
  have hδ54 : δ ^ (5 / 4 : ℝ) = 5 * ν / 4 := by
    rw [hδdef, ← Real.rpow_mul hνpos.le, show (4 / 5 : ℝ) * (5 / 4) = 1 by norm_num,
      Real.rpow_one]
  have hδ5 : δ ^ (5 : ℝ) = (5 * ν / 4) ^ (4 : ℝ) := by
    rw [hδdef, ← Real.rpow_mul hνpos.le, show (4 / 5 : ℝ) * 5 = 4 by norm_num]
  have hδ5' : δ ^ (5 : ℝ) = 625 * ν ^ 4 / 256 := by
    rw [hδ5, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hprod_eq : K * (M * W) = (δ * W) * ((K * M) / δ) := by field_simp
  have hYoung := young_five_fourths (a := δ * W) (b := (K * M) / δ)
    (by positivity) (by positivity)
  have hleft : (δ * W) ^ (5 / 4 : ℝ) = (5 * ν / 4) * a ^ 2 := by
    rw [Real.mul_rpow hδpos.le hW, hδ54, hWdef, ← Real.rpow_mul ha,
      show (8 / 5 : ℝ) * (5 / 4) = 2 by norm_num,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hright : ((K * M) / δ) ^ (5 : ℝ) = 256 * (K ^ 5 * M ^ 5) / (625 * ν ^ 4) := by
    rw [Real.div_rpow (by positivity) hδpos.le, hδ5', Real.mul_rpow hK hM,
      show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
    field_simp
  rw [hleft, hright] at hYoung
  have hYoung' : K * (M * W) ≤ ν * a ^ 2 + (256 / 3125) * (K ^ 5 * M ^ 5) / ν ^ 4 := by
    rw [hprod_eq]
    calc (δ * W) * ((K * M) / δ)
        ≤ (4 / 5) * ((5 * ν / 4) * a ^ 2) + (1 / 5) * (256 * (K ^ 5 * M ^ 5) / (625 * ν ^ 4)) :=
          hYoung
      _ = ν * a ^ 2 + (256 / 3125) * (K ^ 5 * M ^ 5) / ν ^ 4 := by ring
  have hfinal : (1 / 2) * Yderiv + ν * a ^ 2 ≤ ν * a ^ 2 + (256 / 3125) * (K ^ 5 * M ^ 5) / ν ^ 4 :=
    hmain0.trans hYoung'
  have hM5 : M ^ 5 = n5 ^ 5 * Yval := by
    have h1 : (1 / 5 : ℝ) * ((5 : ℕ) : ℝ) = 1 := by norm_num
    have h2 : (Yval ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = Yval := by
      rw [← Real.rpow_natCast (Yval ^ (1 / 5 : ℝ)) 5, ← Real.rpow_mul hYval, h1, Real.rpow_one]
    rw [hMdef, mul_pow, h2]
  have hK5 : K ^ 5 = C_S ^ 3 := by
    have h1 : (3 / 5 : ℝ) * ((5 : ℕ) : ℝ) = 3 := by norm_num
    rw [hKdef, ← Real.rpow_natCast (C_S ^ (3 / 5 : ℝ)) 5, ← Real.rpow_mul hCS, h1,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hν4 : ν⁻¹ ^ 4 = 1 / ν ^ 4 := by rw [inv_pow, one_div]
  have htarget : 2 * ((256 / 3125) * C_S ^ 3) * ν⁻¹ ^ 4 * n5 ^ 5 * Yval
      = 2 * ((256 / 3125) * (K ^ 5 * M ^ 5) / ν ^ 4) := by
    rw [hK5, hM5, hν4]; ring
  rw [htarget]
  linarith [hfinal]

/-! ## Step 4: the Grönwall argument -/

/-- The analytic hypotheses of the Grönwall step (manuscript `lem:serrin-enstrophy`,
proof Step 4), bundled so that `serrin_enstrophy_bound` states exactly one hypothesis
object.  `Y` is the enstrophy `‖∇u(t)‖₂²`, `Y'` its derivative (`hYderiv`), `N5 t =
‖u(t)‖₅`, and `G` is the manuscript's antiderivative `G(t) = ∫₀ᵗg` of the Grönwall
coefficient `g(t) = 2C_*ν⁻⁴N5(t)^5` (`hbound` is the conclusion of
`enstrophy_differential_inequality` at each interior time).

`hGderiv` and `hGeq` are the fundamental-theorem-of-calculus content that would
otherwise need a one-sided/two-sided boundary continuity development at `t = 0`: the
manuscript's (R1) gives `u` (hence `N5`, `Y`, `G`) genuinely smooth up to the initial
time, which is exactly what `hGderiv` records at `t = 0` as well as on the open
interval; deriving it from a bare `ContinuousOn N5 (Set.Ico 0 T')` hypothesis would
only yield a *one-sided* derivative of `G` at `t = 0` (Mathlib's
`intervalIntegral.integral_hasDerivAt_right` needs `ContinuousAt` at the point, not
`ContinuousWithinAt`), so the two-sided statement at `t = 0` is recorded here as an
explicit hypothesis rather than re-derived, exactly as the lane brief permits. -/
structure SerrinHypotheses (ν T' : ℝ) (Y Y' N5 G : ℝ → ℝ) : Prop where
  /-- The viscosity is positive. -/
  hν : 0 < ν
  /-- The horizon `T` of the manuscript's `lem:serrin-enstrophy` is positive. -/
  hT' : 0 < T'
  /-- The enstrophy `Y(t) = ‖∇u(t)‖₂²` is nonnegative. -/
  hYnonneg : ∀ t, 0 ≤ Y t
  /-- `Y` is differentiable on `[0,T)` with derivative `Y'`. -/
  hYderiv : ∀ t ∈ Set.Ico (0 : ℝ) T', HasDerivAt Y (Y' t) t
  /-- `N5(t) = ‖u(t)‖₅` is nonnegative. -/
  hN5nonneg : ∀ t, 0 ≤ N5 t
  /-- `G` is an antiderivative on `[0,T)` of the Grönwall coefficient
  `g(t) = 2C_*ν⁻⁴N5(t)^5`; see the structure docstring for why this is taken as a
  hypothesis rather than derived from a continuity assumption on `N5`. -/
  hGderiv : ∀ t ∈ Set.Ico (0 : ℝ) T',
    HasDerivAt G (2 * ((256 / 3125) * (sobolevSixConst : ℝ) ^ 3) * ν⁻¹ ^ 4 * N5 t ^ 5) t
  /-- `G` vanishes at the origin, `G(0) = ∫₀⁰g = 0`. -/
  hG0 : G 0 = 0
  /-- `G` is literally the manuscript's `∫₀ᵗg`, so that `serrin_enstrophy_bound`'s
  conclusion can be phrased with the actual `∫₀ᵗN5(s)^5ds`. -/
  hGeq : ∀ t ∈ Set.Ico (0 : ℝ) T', G t =
    2 * ((256 / 3125) * (sobolevSixConst : ℝ) ^ 3) * ν⁻¹ ^ 4 * ∫ s in (0 : ℝ)..t, N5 s ^ 5
  /-- The differential inequality `Y' ≤ 2C_*ν⁻⁴N5⁵Y` of
  `enstrophy_differential_inequality`, holding on `[0,T)`. -/
  hbound : ∀ t ∈ Set.Ico (0 : ℝ) T',
    Y' t ≤ 2 * ((256 / 3125) * (sobolevSixConst : ℝ) ^ 3) * ν⁻¹ ^ 4 * N5 t ^ 5 * Y t

/-- The squared (`Y`-level) form of the Grönwall step, with the manuscript's `2C_*`
coefficient (before the square root splits it back into `C_*`): under
`SerrinHypotheses ν T' Y Y' N5 G`,

`Y(t) ≤ Y(0)·exp(2C_*·ν⁻⁴·∫₀ᵗN5(s)^5ds)` for every `t ∈ [0,T')`.

Proof (manuscript Step 4): with `g(t) := 2C_*ν⁻⁴N5(t)^5` and `Z(t) := Y(t)·exp(-G(t))`,
`Z` is differentiable at every `t ∈ [0,T')` (product/chain rule from `hYderiv`,
`hGderiv`) with `Z'(t) = exp(-G(t))·(Y'(t) - g(t)Y(t)) ≤ 0` by `hbound`. Since
`interior (Set.Ico 0 T') = Set.Ioo 0 T' ⊆ Set.Ico 0 T'`, `Z` is continuous and
differentiable on all of `[0,T')` (hence on the interior), so
`antitoneOn_of_deriv_nonpos` gives `Z` antitone on `[0,T')`; in particular
`Z(t) ≤ Z(0) = Y(0)·exp(-G(0)) = Y(0)` (`hG0`), i.e. `Y(t) ≤ Y(0)·exp(G(t))`, and
`hGeq` identifies `G(t)` with the displayed integral. -/
theorem serrin_enstrophy_bound_sq {ν T' : ℝ} {Y Y' N5 G : ℝ → ℝ}
    (H : SerrinHypotheses ν T' Y Y' N5 G) :
    ∀ t ∈ Set.Ico (0 : ℝ) T', Y t ≤ Y 0 *
      Real.exp (2 * ((256 / 3125) * (sobolevSixConst : ℝ) ^ 3) * ν⁻¹ ^ 4 *
        ∫ s in (0 : ℝ)..t, N5 s ^ 5) := by
  set Cstar : ℝ := (256 / 3125) * (sobolevSixConst : ℝ) ^ 3 with hCstardef
  set g : ℝ → ℝ := fun s => 2 * Cstar * ν⁻¹ ^ 4 * N5 s ^ 5 with hgdef
  set Z : ℝ → ℝ := fun s => Y s * Real.exp (-(G s)) with hZdef
  have hZderiv : ∀ t ∈ Set.Ico (0 : ℝ) T', HasDerivAt Z
      (Y' t * Real.exp (-(G t)) + Y t * (Real.exp (-(G t)) * -(g t))) t := by
    intro t ht
    have hY' : HasDerivAt Y (Y' t) t := H.hYderiv t ht
    have hG' : HasDerivAt G (g t) t := H.hGderiv t ht
    have hexp : HasDerivAt (fun s => Real.exp (-(G s))) (Real.exp (-(G t)) * -(g t)) t :=
      (hG'.neg).exp
    exact hY'.mul hexp
  have hZderiv_le : ∀ t ∈ Set.Ico (0 : ℝ) T', deriv Z t ≤ 0 := by
    intro t ht
    rw [(hZderiv t ht).deriv]
    have hbd := H.hbound t ht
    have hgt : g t = 2 * ((256 / 3125) * (sobolevSixConst : ℝ) ^ 3) * ν⁻¹ ^ 4 * N5 t ^ 5 := by
      simp only [hgdef, hCstardef]
    have hkey : Y' t ≤ g t * Y t := by rw [hgt]; nlinarith [hbd]
    have hexp_pos : (0 : ℝ) < Real.exp (-(G t)) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_left hkey hexp_pos.le
    nlinarith [hmul]
  have hZcont : ContinuousOn Z (Set.Ico (0 : ℝ) T') :=
    fun t ht => (hZderiv t ht).continuousAt.continuousWithinAt
  have hZdiff : DifferentiableOn ℝ Z (interior (Set.Ico (0 : ℝ) T')) := by
    rw [interior_Ico]
    exact fun t ht => (hZderiv t (Set.Ioo_subset_Ico_self ht)).differentiableAt.differentiableWithinAt
  have hZanti : AntitoneOn Z (Set.Ico (0 : ℝ) T') := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico 0 T') hZcont hZdiff ?_
    rw [interior_Ico]
    exact fun t ht => hZderiv_le t (Set.Ioo_subset_Ico_self ht)
  intro t ht
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T' := ⟨le_refl 0, H.hT'⟩
  have hZt0 : Z t ≤ Z 0 := hZanti h0 ht ht.1
  have hZ0 : Z 0 = Y 0 := by simp [hZdef, H.hG0]
  have hZtform : Z t = Y t * Real.exp (-(G t)) := rfl
  have hYbound : Y t * Real.exp (-(G t)) ≤ Y 0 := hZ0 ▸ hZtform ▸ hZt0
  have hexp_pos : (0 : ℝ) < Real.exp (-(G t)) := Real.exp_pos _
  have hYbound2 : Y t ≤ Y 0 * Real.exp (G t) := by
    have h1 : Y t * Real.exp (-(G t)) * Real.exp (G t) ≤ Y 0 * Real.exp (G t) :=
      mul_le_mul_of_nonneg_right hYbound (Real.exp_pos _).le
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h1
  rw [H.hGeq t ht] at hYbound2
  exact hYbound2

/-- **Manuscript Lemma `lem:serrin-enstrophy`, `eq:serrin-bound`**: under
`SerrinHypotheses ν T' Y Y' N5 G`,

`√(Y t) ≤ √(Y 0)·exp(C_*·ν⁻⁴·∫₀ᵗN5(s)^5ds)` for every `t ∈ [0,T')`,

`C_* = (256/3125)·sobolevSixConst^3`, matching the manuscript's
`sup_{0≤t<T}‖u(t)‖... ‖∇u(t)‖₂ ≤ ‖∇u₀‖₂·exp(C_*ν⁻⁴∫₀^T‖u‖₅⁵)` with `Y = ‖∇u‖₂²`
(so `√Y = ‖∇u‖₂`), taken pointwise rather than as a `sup` (the manuscript derives
the `sup` form from the same bound holding at every `t`, since the right side is
monotone increasing in `t`). Immediate from `serrin_enstrophy_bound_sq` by taking
square roots: `√(Y(0)·exp(2x)) = √(Y 0)·exp(x)` since `exp(2x) = exp(x)^2 ≥ 0`. -/
theorem serrin_enstrophy_bound {ν T' : ℝ} {Y Y' N5 G : ℝ → ℝ}
    (H : SerrinHypotheses ν T' Y Y' N5 G) :
    ∀ t ∈ Set.Ico (0 : ℝ) T', Real.sqrt (Y t) ≤ Real.sqrt (Y 0) *
      Real.exp ((256 / 3125) * (sobolevSixConst : ℝ) ^ 3 * ν⁻¹ ^ 4 *
        ∫ s in (0 : ℝ)..t, N5 s ^ 5) := by
  intro t ht
  have hsq := serrin_enstrophy_bound_sq H t ht
  set x : ℝ := (256 / 3125) * (sobolevSixConst : ℝ) ^ 3 * ν⁻¹ ^ 4 *
      ∫ s in (0 : ℝ)..t, N5 s ^ 5 with hxdef
  have hrw : (2 : ℝ) * ((256 / 3125) * (sobolevSixConst : ℝ) ^ 3) * ν⁻¹ ^ 4 *
      (∫ s in (0 : ℝ)..t, N5 s ^ 5) = 2 * x := by rw [hxdef]; ring
  rw [hrw] at hsq
  have hexpx : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [two_mul, Real.exp_add]
  rw [hexpx] at hsq
  have hY0 : 0 ≤ Y 0 := H.hYnonneg 0
  have hexp0 : 0 ≤ Real.exp x := (Real.exp_pos _).le
  calc Real.sqrt (Y t) ≤ Real.sqrt (Y 0 * (Real.exp x * Real.exp x)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Y 0) * Real.exp x := by
        rw [show Y 0 * (Real.exp x * Real.exp x) = Y 0 * Real.exp x ^ 2 by ring,
          Real.sqrt_mul hY0, Real.sqrt_sq hexp0]

end NavierFormal
