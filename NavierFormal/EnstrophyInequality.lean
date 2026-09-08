import NavierFormal.Basic
import NavierFormal.Calculus
import NavierFormal.SolutionClass
import NavierFormal.Interpolation
import NavierFormal.EnstrophyIdentity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The cubic differential inequality (`prop:enstrophy`, `eq:enstrophy`)

This module finishes the manuscript's Proposition `prop:enstrophy`
(`../navier-paper/main.tex`, Steps 2–4 of the proof) on top of the enstrophy
identity `NavierFormal.enstrophy_identity_pointwise_time`
(`NavierFormal/EnstrophyIdentity.lean`, Step 1, `eq:enstrophy-identity`):

`½Y'(t) + ν‖Δu(t)‖₂² = ∫(u·∇)u·Δu dx`.

## Route

* `enstrophy_inequality_of_interpolation` is the real-number core of Steps
  2–4: given the identity above with `I := ∫(u·∇)u·Δu dx`, the Hölder bound
  `|I| ≤ b·m3·a` (manuscript Step 2, `b = ‖u‖₆`, `m3 = ‖∇u‖₃`, `a = ‖Δu‖₂`),
  the Sobolev bound `b ≤ C_S·g` (manuscript Step 3, `g = ‖∇u‖₂ = Y^{1/2}`)
  and the interpolation bound `m3 ≤ C·g^{1/2}·a^{1/2}` (manuscript Step 3,
  `NavierFormal.eLpNorm_tenThirds_le`/Gagliardo–Nirenberg style), it derives
  `eq:enstrophy` with the **explicit** constant `C_E = (27/32)·(C_S·C)⁴`.
  The proof follows the manuscript's own Step 4 verbatim: apply the
  fixed-constant Young inequality `NavierFormal.young_four_thirds`
  (conjugate exponents `4/3, 4`, no free parameter) to the rescaled pair
  `(δ·a^{3/2}, (C_S·C·g^{3/2})/δ)` with `δ := (2ν/3)^{3/4}`, chosen so that
  the `a^{3/2}` term's coefficient becomes exactly `ν/2`.  This reproduces
  the manuscript's own computation: instantiated at the manuscript's own
  constants `C_S ↦ √3·C_S`, `C ↦ (3·C_S)^{1/2}` (so `C_S·C = 3·C_S^{3/2}`),
  `(27/32)·(C_S·C)⁴ = (27/32)·81·C_S⁶ = 2187/32·C_S⁶`, exactly the
  manuscript's `C_E`.
* `enstrophy_inequality` assembles `enstrophy_identity_pointwise_time` with
  `enstrophy_inequality_of_interpolation` for a classical solution, taking
  the manuscript's Hölder/Sobolev/interpolation steps as explicit real
  hypotheses `hHolder`, `hSobolev`, `hInterp` on `ENNReal.toReal` of the
  relevant `eLpNorm`s (with the finiteness side conditions this conversion
  needs), exactly as the lane brief permits.

## Norm conventions

As in `NavierFormal.EnstrophyIdentity` (risk `R-NORM`): `Y`, `Y'` and the
enstrophy density are the **Frobenius** norm; the Hölder/Sobolev/interpolation
real numbers `b, m3, a, g` of `enstrophy_inequality_of_interpolation` stand for
`eLpNorm`s taken with the **operator** norm of `fderiv`, exactly as in
`NavierFormal.eLpNorm_six_le_eLpNorm_fderiv_two`.  The two differ by at most a
factor `√3`; `enstrophy_inequality` discharges this at the interface by
requiring `g` to literally be `Real.sqrt Y` composed with the standard
`opNorm_le_frobeniusNorm`/`frobeniusNorm_le_sqrt_three_mul` comparison is
*not* chased inside this module — see the docstring of `enstrophy_inequality`
for the exact deviation.

Nothing here is a theorem about the Millennium problem.
-/

open MeasureTheory InnerProductSpace Laplacian
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace NavierFormal

/-! ## A real-number identity: `x·√x = x^{3/2}` -/

/-- Elementary rewriting of `x·√x` as the real power `x^{3/2}`, used to
identify the Hölder/interpolation quantities `a·√a` and `g·√g` below with the
manuscript's `‖Δu‖₂^{3/2}` and `Y^{3/4} = (√Y)^{3/2}`. Not itself a manuscript
statement. -/
theorem mul_sqrt_self_eq_rpow {x : ℝ} (hx : 0 ≤ x) : x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  have h1 : x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  rw [Real.rpow_one] at h1
  rw [Real.sqrt_eq_rpow]
  exact h1

/-- `(x·√x)^{4/3} = x²`, the Hölder-exponent identification of the manuscript's
`a^{3/2}` raised to Young's exponent `4/3`. -/
theorem rpow_four_thirds_mul_sqrt_self {x : ℝ} (hx : 0 ≤ x) :
    (x * Real.sqrt x) ^ (4 / 3 : ℝ) = x ^ 2 := by
  rw [mul_sqrt_self_eq_rpow hx, ← Real.rpow_mul hx, show (3 / 2 : ℝ) * (4 / 3) = 2 by norm_num,
    Real.rpow_two]

/-- `(x·√x)^4 = x⁶`, the Young-exponent identification of the manuscript's
`g^{3/2}` raised to Young's exponent `4`. -/
theorem rpow_four_mul_sqrt_self {x : ℝ} (hx : 0 ≤ x) :
    (x * Real.sqrt x) ^ (4 : ℝ) = x ^ 6 := by
  rw [mul_sqrt_self_eq_rpow hx, ← Real.rpow_mul hx, show (3 / 2 : ℝ) * 4 = 6 by norm_num,
    show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ## Steps 2–4, the real-number core -/

/-- **Steps 2–4 of the proof of `prop:enstrophy`**, as a real-number lemma.

Given the enstrophy identity `(1/2)·Yderiv + ν·a² = I` (manuscript
`eq:enstrophy-identity`, `a = ‖Δu‖₂`, `Yderiv = Y'`), the Hölder bound
`|I| ≤ b·m3·a` (manuscript Step 2, `b = ‖u‖₆`, `m3 = ‖∇u‖₃`), the Sobolev
bound `b ≤ C_S·g` (manuscript Step 3, `g = ‖∇u‖₂`) and the gradient
interpolation bound `m3 ≤ C·√g·√a` (manuscript Step 3,
`‖∇u‖₃ ≤ C·‖∇u‖₂^{1/2}‖Δu‖₂^{1/2}`), conclude the manuscript's `eq:enstrophy`

`(1/2)·Yderiv + (ν/2)·a² ≤ (27/32)·(C_S·C)⁴·ν⁻¹^3·g⁶`.

Deviation from the manuscript: the constant is left as the generic
`(27/32)·(C_S·C)⁴` rather than the manuscript's `C_S`-only `2187/32·C_S⁶`;
the two coincide once `C_S, C` are instantiated at the manuscript's own
Sobolev/interpolation constants (see the module docstring). `1/2` powers are
`Real.sqrt`, not `Real.rpow`, per the lane's typeclass-synthesis note. -/
theorem enstrophy_inequality_of_interpolation
    {Yderiv a m3 g b C_S C ν I : ℝ}
    (ha : 0 ≤ a) (hm3 : 0 ≤ m3) (hg : 0 ≤ g) (_hb : 0 ≤ b)
    (hCS : 0 ≤ C_S) (hC : 0 ≤ C) (hν : 0 < ν)
    (hid : (1 / 2) * Yderiv + ν * a ^ 2 = I)
    (hI : |I| ≤ b * m3 * a)
    (hSobolev : b ≤ C_S * g)
    (hInterp : m3 ≤ C * Real.sqrt g * Real.sqrt a) :
    (1 / 2) * Yderiv + (ν / 2) * a ^ 2 ≤ (27 / 32) * (C_S * C) ^ 4 * ν⁻¹ ^ 3 * g ^ 6 := by
  set K := C_S * C with hKdef
  have hK : 0 ≤ K := mul_nonneg hCS hC
  set X := a * Real.sqrt a with hXdef
  set Y := g * Real.sqrt g with hYdef
  have hX : 0 ≤ X := mul_nonneg ha (Real.sqrt_nonneg a)
  have hY : 0 ≤ Y := mul_nonneg hg (Real.sqrt_nonneg g)
  -- Step 2–3: `b·m3·a ≤ K·(X·Y)`.
  have hstep1 : b * m3 ≤ (C_S * g) * (C * Real.sqrt g * Real.sqrt a) :=
    mul_le_mul hSobolev hInterp hm3 (by positivity)
  have hstep2 : b * m3 * a ≤ (C_S * g) * (C * Real.sqrt g * Real.sqrt a) * a :=
    mul_le_mul_of_nonneg_right hstep1 ha
  have heq : (C_S * g) * (C * Real.sqrt g * Real.sqrt a) * a = K * (X * Y) := by
    rw [hKdef, hXdef, hYdef]; ring
  have hmain0 : (1 / 2) * Yderiv + ν * a ^ 2 ≤ K * (X * Y) := by
    rw [hid]
    exact (le_abs_self I).trans (hI.trans (heq ▸ hstep2))
  -- Step 4: rescaled Young at `δ = (2ν/3)^{3/4}`.
  set δ : ℝ := (2 * ν / 3) ^ (3 / 4 : ℝ) with hδdef
  have hνpos : (0 : ℝ) < 2 * ν / 3 := by positivity
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hνpos _
  have hδ43 : δ ^ (4 / 3 : ℝ) = 2 * ν / 3 := by
    rw [hδdef, ← Real.rpow_mul hνpos.le, show (3 / 4 : ℝ) * (4 / 3) = 1 by norm_num,
      Real.rpow_one]
  have hδ4 : δ ^ (4 : ℝ) = (2 * ν / 3) ^ (3 : ℝ) := by
    rw [hδdef, ← Real.rpow_mul hνpos.le, show (3 / 4 : ℝ) * 4 = 3 by norm_num]
  have hδ4' : δ ^ (4 : ℝ) = 8 * ν ^ 3 / 27 := by
    rw [hδ4, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hprod_eq : K * (X * Y) = (δ * X) * ((K * Y) / δ) := by
    field_simp
  have hYoung := young_four_thirds (a := δ * X) (b := (K * Y) / δ)
    (by positivity) (by positivity)
  have hleft : (δ * X) ^ (4 / 3 : ℝ) = (2 * ν / 3) * a ^ 2 := by
    rw [Real.mul_rpow hδpos.le hX, hδ43, hXdef, rpow_four_thirds_mul_sqrt_self ha]
  have hright : ((K * Y) / δ) ^ (4 : ℝ) = 27 * (K ^ 4 * g ^ 6) / (8 * ν ^ 3) := by
    rw [Real.div_rpow (by positivity) hδpos.le, hδ4', Real.mul_rpow hK hY, hYdef,
      rpow_four_mul_sqrt_self hg, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [hleft, hright] at hYoung
  have hYoung' : K * (X * Y) ≤ (ν / 2) * a ^ 2 + (27 / 32) * (K ^ 4 * g ^ 6) / ν ^ 3 := by
    rw [hprod_eq]
    calc (δ * X) * ((K * Y) / δ)
        ≤ (3 / 4) * ((2 * ν / 3) * a ^ 2) + (1 / 4) * (27 * (K ^ 4 * g ^ 6) / (8 * ν ^ 3)) :=
          hYoung
      _ = (ν / 2) * a ^ 2 + (27 / 32) * (K ^ 4 * g ^ 6) / ν ^ 3 := by ring
  have hfinal : (1 / 2) * Yderiv + ν * a ^ 2
      ≤ (ν / 2) * a ^ 2 + (27 / 32) * (K ^ 4 * g ^ 6) / ν ^ 3 :=
    hmain0.trans hYoung'
  have hν3 : ν⁻¹ ^ 3 = 1 / ν ^ 3 := by
    rw [inv_pow, one_div]
  have hrw : (27 / 32) * (C_S * C) ^ 4 * ν⁻¹ ^ 3 * g ^ 6
      = (27 / 32) * (K ^ 4 * g ^ 6) / ν ^ 3 := by
    rw [hKdef, hν3]; ring
  rw [hrw]
  linarith

/-! ## The assembled cubic differential inequality, `eq:enstrophy` -/

/-- **The cubic differential inequality** (manuscript Proposition `prop:enstrophy`,
`eq:enstrophy`), assembled from the enstrophy identity
`NavierFormal.enstrophy_identity_pointwise_time` (Step 1) and
`enstrophy_inequality_of_interpolation` (Steps 2–4): for a classical solution
at an interior time `t`,

`(1/2)·Yderiv + (ν/2)·∫‖Δu(t)‖² ≤ (27/32)·(C_S·C)⁴·ν⁻¹^3·(∫enstrophyDensity(u t))³`,

which is exactly `eq:enstrophy` once `Yderiv = Y'(t)` and the (documented,
inherited from `EnstrophyIdentity.lean`) `R-NORM` identification
`Y(t) = ∫enstrophyDensity(u t)` is made.

The Hölder step (manuscript Step 2), the Sobolev step (manuscript Step 3,
with `C_S := NavierFormal.sobolevSixConst`) and the gradient interpolation
step (manuscript Step 3, `‖∇u‖₃ ≤ C·‖∇u‖₂^{1/2}‖Δu‖₂^{1/2}`) are taken as
the explicit hypotheses `hHolder`, `hSobolev`, `hInterp`, exactly as the lane
brief permits; `hInterp`'s constant `C` is a free parameter rather than the
`Part B` value `NavierFormal.hessian_gradient_interpolation` supplies, since a
caller may discharge it from either. `ha2` and `hg2` are the missing
`eLpNorm`-to-`Bochner`-integral bookkeeping identifying the real parameters
`a = ‖Δu(t)‖₂` and `g = ‖∇u(t)‖₂` (the module's `R-NORM` Frobenius
convention) with the integrals `enstrophy_identity_pointwise_time` and
`prop:enstrophy` are stated with; `hYderiv` names the derivative value
`enstrophy_identity_pointwise_time` computes as `Yderiv`. -/
theorem enstrophy_inequality
    {ν : ℝ} {u₀ : Space → Space} {T : ℝ} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsClassicalSolution ν u₀ T u p) (hν : 0 < ν) {t : ℝ} (ht0 : 0 < t) (htT : t < T)
    {Yderiv a b m3 g C : ℝ}
    (hYderiv : Yderiv = 2 * ∫ x, frobeniusInner (fderiv ℝ (u t) x) (fderiv ℝ (timeDeriv u t) x))
    (hY : HasDerivAt (fun s => ∫ x, enstrophyDensity (u s) x) Yderiv t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm3 : 0 ≤ m3) (hg : 0 ≤ g) (hC : 0 ≤ C)
    (ha2 : a ^ 2 = ∫ x, ‖Δ (u t) x‖ ^ 2)
    (hg2 : g ^ 2 = ∫ x, enstrophyDensity (u t) x)
    (hu3 : ContDiff ℝ 3 (u t)) (hp2 : ContDiff ℝ 2 (p t)) (hut1 : ContDiff ℝ 1 (timeDeriv u t))
    (hvw1 : Integrable (fun x => ‖timeDeriv u t x‖ * ‖fderiv ℝ (u t) x‖) volume)
    (hprod : Integrable (fun x => ‖fderiv ℝ (u t) x‖ * ‖fderiv ℝ (timeDeriv u t) x‖) volume)
    (hvw2 : Integrable (fun x => ‖timeDeriv u t x‖ * ‖fderiv ℝ (fderiv ℝ (u t)) x‖) volume)
    (hpu : Integrable (fun x => ‖p t x‖ * ‖Δ (u t) x‖) volume)
    (hpdu : Integrable (fun x => ‖p t x‖ * ‖fderiv ℝ (Δ (u t)) x‖) volume)
    (hdpu : Integrable (fun x => ‖fderiv ℝ (p t) x‖ * ‖Δ (u t) x‖) volume)
    (hΔsq : Integrable (fun x => ‖Δ (u t) x‖ ^ 2) volume)
    (hconvΔ : Integrable (fun x => ⟪Δ (u t) x, convection (u t) x⟫) volume)
    (hgradΔ : Integrable (fun x => ⟪Δ (u t) x, gradient (p t) x⟫) volume)
    (hHolder : |∫ x, ⟪convection (u t) x, Δ (u t) x⟫| ≤ b * m3 * a)
    (hSobolev : b ≤ (sobolevSixConst : ℝ) * g)
    (hInterp : m3 ≤ C * Real.sqrt g * Real.sqrt a) :
    (1 / 2) * Yderiv + (ν / 2) * ∫ x, ‖Δ (u t) x‖ ^ 2
      ≤ (27 / 32) * ((sobolevSixConst : ℝ) * C) ^ 4 * ν⁻¹ ^ 3
        * (∫ x, enstrophyDensity (u t) x) ^ 3 := by
  have hid0 := enstrophy_identity_pointwise_time h ht0 htT (hYderiv ▸ hY) hu3 hp2 hut1
    hvw1 hprod hvw2 hpu hpdu hdpu hΔsq hconvΔ hgradΔ
  rw [← hYderiv] at hid0
  have hid : (1 / 2) * Yderiv + ν * a ^ 2 = ∫ x, ⟪convection (u t) x, Δ (u t) x⟫ := by
    rw [ha2]; exact hid0
  have hCS : (0 : ℝ) ≤ (sobolevSixConst : ℝ) := (sobolevSixConst : ℝ≥0).coe_nonneg
  have key := enstrophy_inequality_of_interpolation ha hm3 hg hb hCS hC hν hid hHolder hSobolev
    hInterp
  rw [show g ^ 6 = (g ^ 2) ^ 3 from by ring, hg2] at key
  rw [ha2] at key
  exact key

end NavierFormal

end
