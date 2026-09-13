import NavierFormal.HessianLaplacianL2

/-!
# Compact support supplies the Hessian--Laplacian IBP package

This module formalizes the compact-support adapter for manuscript
`prop:enstrophy`, `lem:plancherel`(ii).  A `C³` vector field with compact
support has compactly supported derivatives of every order used by the
existing whole-space Green identities.  Continuity then turns those supports
into the exact Bochner `L¹` hypotheses recorded by
`HessianLaplacianIBPData`.

The `C³` premise is deliberate: the existing integrated identity uses the
pointwise Laplacian of first derivatives and the derivative of `Δ u`, so this
adapter does not identify a generic Sobolev `H²` representative with a
pointwise smooth one.  It proves the strongest compact-support route supplied
by the current pointwise statement and leaves no integrability field implicit.
-/

open Function Set Filter MeasureTheory InnerProductSpace Laplacian
open scoped RealInnerProductSpace

noncomputable section

namespace NavierFormal

/-- Continuity of the operator norm in the bounded-convergence topology, used
to turn the compact-support `C³` package into the explicit `L¹` fields of
manuscript `prop:enstrophy`, `lem:plancherel`(ii). -/
private theorem continuous_clm_opNorm :
    Continuous (fun T : Space →L[ℝ] Space →L[ℝ] Space => ‖T‖) := by
  let p : Seminorm ℝ (Space →L[ℝ] Space →L[ℝ] Space) :=
    ContinuousLinearMap.seminorm
  have hp : Continuous (⇑p) := by
    refine p.continuous (r := 1) ?_
    refine ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.2 ?_
    refine ⟨(Metric.ball (0 : Space) 1,
      Metric.ball (0 : Space →L[ℝ] Space) (1 / 4 : ℝ)), ?_, ?_⟩
    · exact ⟨NormedSpace.isVonNBounded_ball ℝ Space 1,
        Metric.ball_mem_nhds _ (by norm_num)⟩
    · intro f hf
      rw [p.mem_ball_zero]
      change ‖f‖ < 1
      have hf' : ‖f‖ ≤ (1 / 2 : ℝ) :=
        ContinuousLinearMap.opNorm_le_of_shell (f := f) one_pos (by norm_num)
          (c := (2 : ℝ)) (by norm_num) (by
          intro x hxlow hxupper
          have hxball : x ∈ Metric.ball (0 : Space) 1 := by
            simpa [Metric.mem_ball, dist_eq_norm] using hxupper
          have hxf := hf x hxball
          have hxf' : ‖f x‖ < (1 / 4 : ℝ) := by
            simpa [Metric.mem_ball, dist_eq_norm] using hxf
          have hxlower : (1 / 2 : ℝ) ≤ ‖x‖ := by
            simpa using hxlow
          nlinarith)
      linarith
  exact hp.congr (fun T => rfl)
  -- The bounded-convergence neighbourhoods contain a smaller operator-norm
  -- ball, obtained by testing on the unit ball.

/-- Compact-support smoothness at the exact order required by the integrated
Hessian--Laplacian identity of manuscript `prop:enstrophy`,
`lem:plancherel`(ii).  This is a pointwise `C³` hypothesis, not a claim that a
generic `H²` class has a `C³` representative. -/
structure CompactSupportC3Hypotheses (u : Space → Space) : Prop where
  /-- The pointwise smoothness needed by the existing Green identities for
  manuscript `prop:enstrophy`, `lem:plancherel`(ii). -/
  smooth : ContDiff ℝ 3 u
  /-- The spatial compact-support premise used for manuscript
  `prop:enstrophy`, `lem:plancherel`(ii). -/
  compact : HasCompactSupport u

/-- Compact support and `C³` smoothness imply every explicit whole-space
integration-by-parts field in `HessianLaplacianIBPData` for manuscript
`prop:enstrophy`, `lem:plancherel`(ii).  Each integrability conclusion is
obtained from continuity and compact support; no decay or Sobolev-to-pointwise
identification is folded into the result. -/
theorem CompactSupportC3Hypotheses.toHessianLaplacianIBPData
    {u : Space → Space} (h : CompactSupportC3Hypotheses u) :
    HessianLaplacianIBPData u := by
  have hu : ContDiff ℝ 3 u := h.smooth
  have hdu_support : HasCompactSupport (fderiv ℝ u) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) h.compact

  have hdir_cd : ∀ j : Fin 3,
      ContDiff ℝ 2 (firstDirectionalDerivative u j) := by
    intro j
    have huf : ContDiff ℝ 2 (fderiv ℝ u) :=
      hu.fderiv_right (m := 2) (by norm_num)
    have hcomp := (ContinuousLinearMap.apply ℝ Space (e j)).contDiff.comp huf
    change ContDiff ℝ 2 (fun x => (fderiv ℝ u x) (e j))
    exact hcomp

  have hdir_support : ∀ j : Fin 3,
      HasCompactSupport (firstDirectionalDerivative u j) := by
    intro j
    change HasCompactSupport (fun x => (fderiv ℝ u x) (e j))
    exact HasCompactSupport.fderiv_apply (𝕜 := ℝ) h.compact (e j)

  have hdir_jac_support : ∀ j : Fin 3,
      HasCompactSupport (fderiv ℝ (firstDirectionalDerivative u j)) := by
    intro j
    exact HasCompactSupport.fderiv (𝕜 := ℝ) (hdir_support j)

  have hdir_second_cont : ∀ j : Fin 3,
      Continuous (fderiv ℝ (fderiv ℝ (firstDirectionalDerivative u j))) := by
    intro j
    exact ((hdir_cd j).fderiv_right (m := 1) (by norm_num)).continuous_fderiv
      (by norm_num)

  have hbase_second_cd : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)

  have hdelta_cd : ContDiff ℝ 1 (Δ u) := by
    have hsum : Δ u = fun x =>
        ∑ i : Fin 3, fderiv ℝ (fderiv ℝ u) x (e i) (e i) :=
      funext (IBP.laplacian_eq_sum u)
    rw [hsum]
    refine ContDiff.sum fun i _ => ?_
    have hcomp := (ContinuousLinearMap.apply ℝ Space (e i)).contDiff.comp
      ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (e i)).contDiff.comp
        hbase_second_cd)
    simpa [Function.comp_def] using hcomp

  have hdelta_support : HasCompactSupport (Δ u) := by
    have hsecond_support : HasCompactSupport (fderiv ℝ (fderiv ℝ u)) :=
      HasCompactSupport.fderiv (𝕜 := ℝ) hdu_support
    apply hsecond_support.mono
    intro x hx
    contrapose! hx
    simp only [mem_support, not_not] at hx ⊢
    rw [IBP.laplacian_eq_sum, hx]
    simp

  have hden_support : ∀ j : Fin 3,
      HasCompactSupport (enstrophyDensity (firstDirectionalDerivative u j)) := by
    intro j
    apply (hdir_jac_support j).mono
    intro x hx
    contrapose! hx
    simp only [mem_support, not_not] at hx ⊢
    simp [enstrophyDensity, frobeniusNormSq, hx]

  have hdir_lap_inner_support : ∀ j : Fin 3,
      HasCompactSupport (fun x =>
        ⟪firstDirectionalDerivative u j x,
          Δ (firstDirectionalDerivative u j) x⟫) := by
    intro j
    apply (hdir_support j).mono
    intro x hx
    contrapose! hx
    simp only [mem_support, not_not] at hx ⊢
    rw [hx, inner_zero_left]

  refine
    { directional_primitive := fun j => ?_
      directional_hessian := fun j => ?_
      directional_second := fun j => ?_
      directional_laplacian_inner := fun j => ?_
      base_primitive := ?_
      base_gradient_product := ?_
      base_second := ?_ }
  · have hc : Continuous (fun x =>
        ‖firstDirectionalDerivative u j x‖ *
          ‖fderiv ℝ (firstDirectionalDerivative u j) x‖) :=
      (hdir_cd j).continuous.norm.mul
        ((hdir_cd j).continuous_fderiv (by norm_num)).norm
    exact hc.integrable_of_hasCompactSupport ((hdir_support j).norm.mul_right)
  · have hc : Continuous (enstrophyDensity (firstDirectionalDerivative u j)) :=
      IBP.continuous_enstrophyDensity ((hdir_cd j).of_le (by norm_num))
    exact hc.integrable_of_hasCompactSupport (hden_support j)
  · have hc : Continuous (fun x =>
      ‖firstDirectionalDerivative u j x‖ *
          ‖fderiv ℝ (fderiv ℝ (firstDirectionalDerivative u j)) x‖) :=
      by
        let hsecondnorm : Continuous (fun x =>
            ‖fderiv ℝ (fderiv ℝ (firstDirectionalDerivative u j)) x‖) := by
          exact continuous_clm_opNorm.comp (hdir_second_cont j)
        exact (hdir_cd j).continuous.norm.mul hsecondnorm
    exact hc.integrable_of_hasCompactSupport ((hdir_support j).norm.mul_right)
  · have hc : Continuous (fun x =>
        ⟪firstDirectionalDerivative u j x,
          Δ (firstDirectionalDerivative u j) x⟫) :=
      (hdir_cd j).continuous.inner (IBP.continuous_laplacian (hdir_cd j))
    exact hc.integrable_of_hasCompactSupport (hdir_lap_inner_support j)
  · have hc : Continuous (fun x =>
        ‖Δ u x‖ * ‖fderiv ℝ u x‖) :=
      hdelta_cd.continuous.norm.mul (hu.continuous_fderiv (by norm_num)).norm
    exact hc.integrable_of_hasCompactSupport (hdelta_support.norm.mul_right)
  · have hc : Continuous (fun x =>
        ‖fderiv ℝ u x‖ * ‖fderiv ℝ (Δ u) x‖) :=
      (hu.continuous_fderiv (by norm_num)).norm.mul
        (hdelta_cd.continuous_fderiv (by norm_num)).norm
    exact hc.integrable_of_hasCompactSupport (hdu_support.norm.mul_right)
  · have hc : Continuous (fun x =>
        ‖Δ u x‖ * ‖fderiv ℝ (fderiv ℝ u) x‖) :=
      by
        let hsecondnorm : Continuous (fun x => ‖fderiv ℝ (fderiv ℝ u) x‖) := by
          exact continuous_clm_opNorm.comp hbase_second_cd.continuous
        exact hdelta_cd.continuous.norm.mul hsecondnorm
    exact hc.integrable_of_hasCompactSupport (hdelta_support.norm.mul_right)

/-- The compact-support `C³` wrapper for the integrated Hessian--Laplacian
identity of manuscript `prop:enstrophy`, `lem:plancherel`(ii):
`∫ ‖D²u‖_F² = ∫ ‖Δu‖²`. -/
theorem hessian_laplacian_L2_identity_of_compactSupportC3
    {u : Space → Space} (h : CompactSupportC3Hypotheses u) :
    ∫ x, hessianFrobeniusSq u x = ∫ x, ‖Δ u x‖ ^ 2 := by
  exact hessian_laplacian_L2_identity h.smooth
    (CompactSupportC3Hypotheses.toHessianLaplacianIBPData h)

end NavierFormal

end
