import Frourio.Analysis.Gaussian
import Frourio.Analysis.MellinBasic
import Frourio.Analysis.HilbertSpaceCore
import Frourio.Analysis.SchwartzDensity.SchwartzDensityCore2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Order.Filter.Basic

open MeasureTheory Measure Real Complex SchwartzMap intervalIntegral Set
open scoped ENNReal Topology ComplexConjugate

namespace Frourio

section SchwartzDensity

/-- L² functions can be approximated by continuous
  compactly supported functions in weighted L² spaces -/
lemma lp_to_continuous_approx {σ : ℝ} (hσ_lower : 1 / 2 < σ)
    (f : Lp ℂ 2 (weightedMeasure σ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g_cont : ℝ → ℂ) (hg_cont_memLp : MemLp g_cont 2 (weightedMeasure σ)),
      HasCompactSupport g_cont ∧
      Continuous g_cont ∧
      dist f (hg_cont_memLp.toLp g_cont) < ε := by
  classical
  haveI : Fact (1 / 2 < σ) := ⟨hσ_lower⟩
  let μ := weightedMeasure σ
  have hf_mem : MemLp (fun x : ℝ => (f : ℝ → ℂ) x) 2 μ := Lp.memLp f
  have hε_half : 0 < ε / 2 := half_pos hε
  obtain ⟨R, hR_pos, f_R, hf_R_memLp, hf_R_compact, h_trunc⟩ :=
    truncation_approximation hσ_lower (fun x : ℝ => (f : ℝ → ℂ) x) hf_mem ε hε
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
  have hε_ofReal_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hε_half]
  obtain ⟨g_cont, hg_compact, hg_bound, hg_continuous, hg_memLp⟩ :=
    MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le
      (μ := μ) (p := (2 : ℝ≥0∞)) (f := f_R) h_two_ne_top hf_R_memLp
      (ε := ENNReal.ofReal (ε / 2)) hε_ofReal_ne
  let fR_Lp := hf_R_memLp.toLp f_R
  let g_Lp := hg_memLp.toLp g_cont
  have hf_toLp :
      hf_mem.toLp (fun x : ℝ => (f : ℝ → ℂ) x) = f := by
    apply Lp.ext
    simp
  have hf_diff_mem :
      MemLp (fun x : ℝ => (f : ℝ → ℂ) x - f_R x) 2 μ := hf_mem.sub hf_R_memLp
  have h_dist_trunc_lt : dist f fR_Lp < ε / 2 := by
    have hcalc :
        (hf_mem.sub hf_R_memLp).toLp
            (fun x : ℝ => (f : ℝ → ℂ) x - f_R x)
          = f - fR_Lp := by
      simpa [hf_toLp, fR_Lp] using MemLp.toLp_sub hf_mem hf_R_memLp
    have hnorm_eq :
        ‖f - fR_Lp‖
          = ENNReal.toReal
              (eLpNorm (fun x : ℝ => (f : ℝ → ℂ) x - f_R x) 2 μ) := by
      simpa [dist_eq_norm, fR_Lp, hcalc] using
        (Lp.norm_toLp (μ := μ)
          (f := fun x : ℝ => (f : ℝ → ℂ) x - f_R x) hf_diff_mem)
    have hfinite :
        eLpNorm (fun x : ℝ => (f : ℝ → ℂ) x - f_R x) 2 μ ≠ ∞ := hf_diff_mem.2.ne
    have htoReal_lt :
        ENNReal.toReal (eLpNorm (fun x : ℝ => (f : ℝ → ℂ) x - f_R x) 2 μ)
          < ε / 2 := by
      have := (ENNReal.toReal_lt_toReal hfinite (by simp)).2 h_trunc
      simpa [ENNReal.toReal_ofReal (le_of_lt hε_half)] using this
    simpa [dist_eq_norm, hnorm_eq] using htoReal_lt
  have hg_diff_mem : MemLp (fun x : ℝ => f_R x - g_cont x) 2 μ :=
    hf_R_memLp.sub hg_memLp
  have h_dist_cont_le : dist fR_Lp g_Lp ≤ ε / 2 := by
    have hcalc :
        (hf_R_memLp.sub hg_memLp).toLp (fun x : ℝ => f_R x - g_cont x)
          = fR_Lp - g_Lp := by
      simpa [fR_Lp, g_Lp] using MemLp.toLp_sub hf_R_memLp hg_memLp
    have hnorm_eq :
        ‖fR_Lp - g_Lp‖
          = ENNReal.toReal (eLpNorm (fun x : ℝ => f_R x - g_cont x) 2 μ) := by
      simpa [dist_eq_norm, fR_Lp, g_Lp, hcalc] using
        (Lp.norm_toLp (μ := μ)
          (f := fun x : ℝ => f_R x - g_cont x) hg_diff_mem)
    have hfinite :
        eLpNorm (fun x : ℝ => f_R x - g_cont x) 2 μ ≠ ∞ := hg_diff_mem.2.ne
    have htoReal_le :
        ENNReal.toReal (eLpNorm (fun x : ℝ => f_R x - g_cont x) 2 μ)
          ≤ ε / 2 := by
      have := (ENNReal.toReal_le_toReal hfinite (by simp)).2 hg_bound
      simpa [ENNReal.toReal_ofReal (le_of_lt hε_half)] using this
    simpa [dist_eq_norm, hnorm_eq] using htoReal_le
  refine ⟨g_cont, hg_memLp, hg_compact, hg_continuous, ?_⟩
  have hsum_lt :
      dist f fR_Lp + dist fR_Lp (hg_memLp.toLp g_cont) < ε := by
    have h_add := add_lt_add_of_lt_of_le h_dist_trunc_lt h_dist_cont_le
    have hsum : ε / 2 + ε / 2 = ε := by ring
    simpa [g_Lp, add_comm, add_left_comm, add_assoc, hsum] using h_add
  refine lt_of_le_of_lt ?_ hsum_lt
  simpa using dist_triangle f fR_Lp (hg_memLp.toLp g_cont)

/-- Given a function with compact support on `ℝ`, there exists a radius `R > 0` such that the
topological support is contained in the closed ball of radius `R`. -/
lemma HasCompactSupport.exists_radius_closedBall {f : ℝ → ℂ}
    (hf : HasCompactSupport f) : ∃ R : ℝ, 0 < R ∧ tsupport f ⊆ Metric.closedBall 0 R := by
  classical
  have hK_compact : IsCompact (tsupport f) := hf
  by_cases hK_empty : tsupport f = (∅ : Set ℝ)
  · refine ⟨1, zero_lt_one, ?_⟩
    simp [hK_empty]
  · have hK_nonempty : (tsupport f).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hK_empty
    obtain ⟨x₀, hx₀, hx₀_max⟩ :=
      hK_compact.exists_isMaxOn hK_nonempty
        ((continuous_norm : Continuous fun x : ℝ => ‖x‖).continuousOn)
    have hx0_pos : 0 < ‖x₀‖ + 1 := by
      have hx0_nonneg : 0 ≤ ‖x₀‖ := norm_nonneg _
      exact add_pos_of_nonneg_of_pos hx0_nonneg zero_lt_one
    refine ⟨‖x₀‖ + 1, hx0_pos, ?_⟩
    intro x hx
    have hx_le : ‖x‖ ≤ ‖x₀‖ := hx₀_max hx
    have hx_le' : ‖x‖ ≤ ‖x₀‖ + 1 := le_trans hx_le (by linarith)
    simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using hx_le'

/-- A continuous function with compact support on `ℝ` is uniformly continuous. -/
lemma Continuous.uniformContinuous_of_hasCompactSupport {f : ℝ → ℂ}
    (hf : Continuous f) (hf_support : HasCompactSupport f) : UniformContinuous f := by
  classical
  obtain ⟨R, hR_pos, hR_subset⟩ := HasCompactSupport.exists_radius_closedBall hf_support
  let B := Metric.closedBall (0 : ℝ) (R + 1)
  have hf_zero : ∀ {x : ℝ}, R < ‖x‖ → f x = 0 := by
    intro x hx
    have hx_not : x ∉ tsupport f := by
      intro hx_mem
      have hx_le : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using hR_subset hx_mem
      exact (not_le_of_gt hx) hx_le
    simpa using image_eq_zero_of_notMem_tsupport hx_not
  have hf_cont_on_ball : ContinuousOn f B := by
    intro x hx
    have hx_cont : ContinuousAt f x := hf.continuousAt
    exact hx_cont.continuousWithinAt
  have hB_compact : IsCompact B := by
    simpa [B] using (isCompact_closedBall (0 : ℝ) (R + 1))
  have hf_uc_on : UniformContinuousOn f B :=
    hB_compact.uniformContinuousOn_of_continuous hf_cont_on_ball
  refine Metric.uniformContinuous_iff.2 ?_
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.uniformContinuousOn_iff.mp hf_uc_on ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀_pos zero_lt_one, ?_⟩
  intro x y hxy
  have outside_case :
      ∀ {a b : ℝ}, a ∉ B → dist a b < min δ₀ 1 → dist (f a) (f b) < ε := by
    intro a b ha_out hdist
    have ha_norm_gt : R + 1 < ‖a‖ := by
      have ha_dist_gt : R + 1 < dist a 0 := lt_of_not_ge
        (by simpa [B, Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using ha_out)
      simpa [Real.dist_eq, sub_eq_add_neg] using ha_dist_gt
    have ha_gt : R < ‖a‖ :=
      lt_of_le_of_lt (by linarith : R ≤ R + 1) ha_norm_gt
    have ha_zero : f a = 0 := hf_zero ha_gt
    have hdist_lt_one : dist a b < 1 := lt_of_lt_of_le hdist (min_le_right _ _)
    have hdist_le_one : dist a b ≤ 1 := le_of_lt hdist_lt_one
    have ha_minus_one_gt : R < ‖a‖ - 1 := by linarith [ha_norm_gt]
    have ha_minus_ge : ‖a‖ - 1 ≤ ‖a‖ - dist a b :=
      sub_le_sub_left hdist_le_one ‖a‖
    have ha_minus_gt : R < ‖a‖ - dist a b :=
      lt_of_lt_of_le ha_minus_one_gt ha_minus_ge
    have htriangle : ‖a‖ ≤ dist a b + ‖b‖ := by
      have h := dist_triangle a b 0
      simpa [Real.dist_eq, sub_eq_add_neg, add_comm] using h
    have ha_minus_le_norm_b : ‖a‖ - dist a b ≤ ‖b‖ := by
      linarith
    have hb_gt : R < ‖b‖ := lt_of_lt_of_le ha_minus_gt ha_minus_le_norm_b
    have hb_zero : f b = 0 := hf_zero hb_gt
    simpa [ha_zero, hb_zero] using hε
  by_cases hx_mem : x ∈ B
  · by_cases hy_mem : y ∈ B
    · have hdist_lt_δ : dist x y < δ₀ := lt_of_lt_of_le hxy (min_le_left _ _)
      exact hδ₀ x hx_mem y hy_mem hdist_lt_δ
    · have hy_not : y ∉ B := hy_mem
      have hdist_yx : dist y x < min δ₀ 1 := by simpa [dist_comm] using hxy
      have hy_case := outside_case hy_not hdist_yx
      simpa [dist_comm] using hy_case
  · have hx_not : x ∉ B := hx_mem
    exact outside_case hx_not hxy

/-- A smooth cut-off function that equals `1` on the closed ball of radius `R` and whose
support is contained in the closed ball of radius `R + 1`. -/
lemma exists_smooth_cutoff_closedBall (R : ℝ) (hR : 0 < R) :
    ∃ χ : ℝ → ℝ,
      HasCompactSupport χ ∧
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      (∀ x ∈ Metric.closedBall (0 : ℝ) R, χ x = 1) ∧
      tsupport χ = Metric.closedBall (0 : ℝ) (R + 1) := by
  classical
  let χ_bump : ContDiffBump (0 : ℝ) :=
    ⟨R, R + 1, hR, by linarith⟩
  refine ⟨(fun x : ℝ => χ_bump x), ?_, ?_, ?_, ?_⟩
  · simpa using χ_bump.hasCompactSupport
  · have h_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => χ_bump x) := by
      simpa using (χ_bump.contDiff (n := (⊤ : ℕ∞)))
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => χ_bump x)
    exact h_smooth
  · intro x hx
    have hx' : x ∈ Metric.closedBall (0 : ℝ) χ_bump.rIn := by
      simpa using hx
    exact χ_bump.one_of_mem_closedBall hx'
  · simpa using χ_bump.tsupport_eq

/-- If two functions coincide outside a measurable set of finite measure and are uniformly
close on that set, then their L²-distance with respect to the weighted measure is controlled by
the uniform bound and the measure of the set. -/
lemma lp_dist_le_of_uniform_bound_on_set {μ : Measure ℝ} {f g : ℝ → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {K : Set ℝ} (hK_meas : MeasurableSet K)
    (hK_fin : μ K < ∞) (h_eq : ∀ x, x ∉ K → f x = g x)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (h_bound : ∀ x ∈ K, ‖f x - g x‖ ≤ C) :
    dist (hf.toLp f) (hg.toLp g) ≤ C * Real.sqrt ((μ K).toReal) := by
  classical
  set h := fun x : ℝ => f x - g x
  have h_mem : MemLp h 2 μ := hf.sub hg
  have h_dist_eq :
      dist (hf.toLp f) (hg.toLp g) = ENNReal.toReal (eLpNorm h 2 μ) := by
    have hcalc : hf.toLp f - hg.toLp g = h_mem.toLp h := by
      simpa [h] using (MemLp.toLp_sub hf hg).symm
    have hnorm : ‖h_mem.toLp h‖ = ENNReal.toReal (eLpNorm h 2 μ) := by
      simp
    calc
      dist (hf.toLp f) (hg.toLp g)
          = ‖hf.toLp f - hg.toLp g‖ := by simp [dist_eq_norm]
      _ = ‖h_mem.toLp h‖ := by simp [hcalc]
      _ = ENNReal.toReal (eLpNorm h 2 μ) := hnorm
  have h_indicator : h =ᵐ[μ] K.indicator h :=
    Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp [h, hx]
      · have hx_eq : f x = g x := h_eq x hx
        simp [h, hx, hx_eq]
  have h_eLp_restrict : eLpNorm h 2 μ = eLpNorm h 2 (μ.restrict K) := by
    have h_norm_indicator :
        ∀ᵐ x ∂μ, ‖h x‖ = ‖K.indicator h x‖ :=
      h_indicator.mono fun x hx => by simp [h, hx]
    have := eLpNorm_congr_norm_ae (μ := μ) (p := (2 : ℝ≥0∞)) h_norm_indicator
    simpa [eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (s := K) (f := h) hK_meas]
      using this
  have h_bound_all : ∀ x, ‖h x‖ ≤ C := by
    intro x
    by_cases hx : x ∈ K
    · exact h_bound x hx
    · have hx_eq : h x = 0 := by
        simp [h, h_eq x hx]
      simp [hx_eq, hC_nonneg]
  have h_bound_restrict : ∀ᵐ x ∂μ.restrict K, ‖h x‖ ≤ C :=
    (ae_of_all _ h_bound_all)
  have h_eLp_bound :
      eLpNorm h 2 (μ.restrict K)
        ≤ μ.restrict K Set.univ ^ (1 / ((2 : ℝ≥0∞).toReal)) * ENNReal.ofReal C := by
    simpa [one_div] using
      (eLpNorm_le_of_ae_bound (μ := μ.restrict K) (p := (2 : ℝ≥0∞))
        (f := h) h_bound_restrict)
  have h_restrict_univ : μ.restrict K Set.univ = μ K := by
    simp [Measure.restrict_apply]
  have h_mu_pow : μ.restrict K Set.univ ^ (1 / ((2 : ℝ≥0∞).toReal))
      = (μ K) ^ (1 / 2 : ℝ) := by
    simp [h_restrict_univ]
  have h_eLp_bound' : eLpNorm h 2 μ ≤ (μ K) ^ (1 / 2 : ℝ) * ENNReal.ofReal C := by
    simpa [h_eLp_restrict, h_mu_pow]
      using h_eLp_bound
  have hμ_ne_top : μ K ≠ ∞ := ne_of_lt hK_fin
  have h_pow_ne_top : (μ K) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hμ_ne_top
  have h_rhs_ne_top : (μ K) ^ (1 / 2 : ℝ) * ENNReal.ofReal C ≠ ∞ :=
    ENNReal.mul_ne_top h_pow_ne_top (by simp)
  have h_eLp_fin : eLpNorm h 2 μ ≠ ∞ :=
    (ne_of_lt h_mem.2)
  have h_toReal_le :
      ENNReal.toReal (eLpNorm h 2 μ)
        ≤ ENNReal.toReal ((μ K) ^ (1 / 2 : ℝ) * ENNReal.ofReal C) := by
    exact (ENNReal.toReal_le_toReal h_eLp_fin h_rhs_ne_top).2 h_eLp_bound'
  have h_toReal_mul :
      ENNReal.toReal ((μ K) ^ (1 / 2 : ℝ) * ENNReal.ofReal C)
        = Real.sqrt ((μ K).toReal) * C := by
    have h_pow_sqrt : ENNReal.toReal ((μ K) ^ (1 / 2 : ℝ))
        = Real.sqrt ((μ K).toReal) := by
      have h₁ := (ENNReal.toReal_rpow (μ K) (1 / 2 : ℝ)).symm
      have h₂ := (Real.sqrt_eq_rpow ((μ K).toReal)).symm
      simpa using h₁.trans h₂
    have h_toReal_C : ENNReal.toReal (ENNReal.ofReal C) = C :=
      ENNReal.toReal_ofReal hC_nonneg
    calc
      ENNReal.toReal ((μ K) ^ (1 / 2 : ℝ) * ENNReal.ofReal C)
          = ENNReal.toReal ((μ K) ^ (1 / 2 : ℝ)) *
              ENNReal.toReal (ENNReal.ofReal C) := by
            simp [ENNReal.toReal_mul]
      _ = Real.sqrt ((μ K).toReal) *
              ENNReal.toReal (ENNReal.ofReal C) := by
            rw [h_pow_sqrt]
      _ = Real.sqrt ((μ K).toReal) * C := by
            rw [h_toReal_C]
  have h_norm_le :
      ENNReal.toReal (eLpNorm h 2 μ)
        ≤ Real.sqrt ((μ K).toReal) * C := by
    calc
      ENNReal.toReal (eLpNorm h 2 μ)
          ≤ ENNReal.toReal ((μ K) ^ (1 / 2 : ℝ) * ENNReal.ofReal C) := h_toReal_le
      _ = Real.sqrt ((μ K).toReal) * C := h_toReal_mul
  have h_dist_le :
      dist (hf.toLp f) (hg.toLp g)
        ≤ Real.sqrt ((μ K).toReal) * C := by
    simpa [h_dist_eq] using h_norm_le
  have h_final :
      dist (hf.toLp f) (hg.toLp g)
        ≤ C * Real.sqrt ((μ K).toReal) := by
    calc
      dist (hf.toLp f) (hg.toLp g)
            ≤ Real.sqrt ((μ K).toReal) * C := h_dist_le
      _ = C * Real.sqrt ((μ K).toReal) := by exact (mul_comm _ _)
  exact h_final

/-- Continuous compactly supported functions can be approximated
  by smooth compactly supported functions -/
lemma continuous_to_smooth_approx {σ : ℝ} (hσ_lower : 1 / 2 < σ)
    (g_cont : ℝ → ℂ) (hg_cont_memLp : MemLp g_cont 2 (weightedMeasure σ))
    (hg_cont_compact : HasCompactSupport g_cont) (hg_cont_continuous : Continuous g_cont)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : ℝ → ℂ) (hg_memLp : MemLp g 2 (weightedMeasure σ)),
      HasCompactSupport g ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      dist (hg_cont_memLp.toLp g_cont) (hg_memLp.toLp g) < ε := by
  classical
  haveI : Fact (1 / 2 < σ) := ⟨hσ_lower⟩
  set μ := weightedMeasure σ
  obtain ⟨R, hR_pos, hR_subset⟩ :=
    HasCompactSupport.exists_radius_closedBall hg_cont_compact
  set B : Set ℝ := Metric.closedBall (0 : ℝ) (R + 1)
  have hB_meas : MeasurableSet B := by
    simpa [B] using
      (measurableSet_closedBall :
        MeasurableSet (Metric.closedBall (0 : ℝ) (R + 1)))
  have hB_compact : IsCompact B := by
    simpa [B] using isCompact_closedBall (0 : ℝ) (R + 1)
  have hμ_Ioc_zero_one := weightedMeasure_Ioc_zero_one_lt_top (σ := σ) hσ_lower
  have hμ_Ioc_one_R : μ (Set.Ioc (1 : ℝ) (R + 1)) < ∞ := by
    have h_subset : Set.Ioc (1 : ℝ) (R + 1) ⊆ Set.Ioo (1 : ℝ) (R + 2) := by
      intro x hx; exact ⟨hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩
    have h_fin :=
      weightedMeasure_finite_on_bounded (σ := σ) (a := 1) (b := R + 2)
        zero_lt_one (by linarith [hR_pos])
    exact lt_of_le_of_lt (measure_mono h_subset) h_fin
  have h_subset_union :
      Set.Ioc (0 : ℝ) (R + 1)
        ⊆ Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc (1 : ℝ) (R + 1) := by
    intro x hx
    by_cases hx_le : x ≤ 1
    · exact Or.inl ⟨hx.1, hx_le⟩
    · exact Or.inr ⟨lt_of_not_ge hx_le, hx.2⟩
  have hμ_Ioc_lt_top : μ (Set.Ioc (0 : ℝ) (R + 1)) < ∞ := by
    have h_le :=
      (measure_mono h_subset_union).trans
        (measure_union_le (μ := μ)
          (s := Set.Ioc (0 : ℝ) 1) (t := Set.Ioc (1 : ℝ) (R + 1)))
    exact lt_of_le_of_lt h_le (ENNReal.add_lt_top.mpr ⟨hμ_Ioc_zero_one, hμ_Ioc_one_R⟩)
  have hμ_B_eq : μ B = μ (B ∩ Set.Ioi (0 : ℝ)) := by
    have h₁ := weightedMeasure_apply σ B hB_meas
    have h₂ :=
      weightedMeasure_apply σ (B ∩ Set.Ioi (0 : ℝ))
        (hB_meas.inter measurableSet_Ioi)
    have h_inter :
        B ∩ Set.Ioi (0 : ℝ) ∩ Set.Ioi (0 : ℝ)
          = B ∩ Set.Ioi (0 : ℝ) := by
      ext x; constructor <;> intro hx
      · rcases hx with ⟨hx₁, _hx₂⟩
        rcases hx₁ with ⟨hxB, hx_pos⟩
        exact ⟨hxB, hx_pos⟩
      · rcases hx with ⟨hxB, hx_pos⟩
        exact ⟨⟨hxB, hx_pos⟩, hx_pos⟩
    have h₁' :
        μ B = ∫⁻ x in B ∩ Set.Ioi (0 : ℝ),
          ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
      simpa [μ] using h₁
    have h₂' :
        μ (B ∩ Set.Ioi (0 : ℝ)) =
          ∫⁻ x in B ∩ Set.Ioi (0 : ℝ),
            ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
      simpa [μ, h_inter, Set.inter_assoc, Set.inter_left_comm,
        Set.inter_right_comm] using h₂
    exact h₁'.trans h₂'.symm
  have h_subset_B : B ∩ Set.Ioi (0 : ℝ) ⊆ Set.Ioc (0 : ℝ) (R + 1) := by
    intro x hx
    rcases hx with ⟨hx_ball, hx_pos⟩
    have hx_dist : dist x 0 ≤ R + 1 := Metric.mem_closedBall.mp hx_ball
    have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
    have hx_abs : |x| = x := abs_of_nonneg hx_nonneg
    have hx_abs_le : |x| ≤ R + 1 := by
      simpa [Real.dist_eq, sub_eq_add_neg] using hx_dist
    have hx_le : x ≤ R + 1 := by simpa [hx_abs] using hx_abs_le
    exact ⟨hx_pos, hx_le⟩
  have hμ_B_lt_top : μ B < ∞ := by
    refine lt_of_le_of_lt ?_ hμ_Ioc_lt_top
    have h_le := measure_mono (μ := μ) h_subset_B
    simpa [hμ_B_eq] using h_le
  have hμ_B_ne_top : μ B ≠ ∞ := (ne_of_lt hμ_B_lt_top)
  set δ := ε / (Real.sqrt ((μ B).toReal) + 1) with hδ_def
  have h_den_pos : 0 < Real.sqrt ((μ B).toReal) + 1 :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) one_pos
  have hδ_pos : 0 < δ := by
    have hε_pos : 0 < ε := hε
    simp [δ, hε_pos, h_den_pos]
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hg_uniform : UniformContinuous g_cont :=
    Continuous.uniformContinuous_of_hasCompactSupport hg_cont_continuous hg_cont_compact
  obtain ⟨g₀, hg₀_smooth, hg₀_close⟩ :=
    hg_uniform.exists_contDiff_dist_le hδ_pos
  have hg₀_smooth' : ContDiff ℝ (⊤ : ℕ∞) g₀ := by
    simpa using hg₀_smooth
  let χ_bump : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR_pos, by linarith⟩
  let χ : ℝ → ℝ := fun x => χ_bump x
  have hχ_support : HasCompactSupport χ := by
    simpa [χ] using χ_bump.hasCompactSupport
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := by
    simpa [χ] using (χ_bump.contDiff (n := (⊤ : ℕ∞)))
  have hχ_one : ∀ x ∈ Metric.closedBall (0 : ℝ) R, χ x = 1 := by
    intro x hx; simpa [χ] using χ_bump.one_of_mem_closedBall hx
  have hχ_tsupport : tsupport χ = B := by
    simpa [χ, B] using χ_bump.tsupport_eq
  have hχ_nonneg : ∀ x, 0 ≤ χ x := by
    intro x; simpa [χ] using χ_bump.nonneg' x
  have hχ_le_one : ∀ x, χ x ≤ 1 := by
    intro x; simpa [χ] using χ_bump.le_one
  let g : ℝ → ℂ := fun x => χ x • g₀ x
  have hg_contDiff : ContDiff ℝ (⊤ : ℕ∞) g := by
    simpa [g] using hχ_smooth.smul hg₀_smooth'
  have hχ_zero_outside : ∀ {x : ℝ}, x ∉ B → χ x = 0 := by
    intro x hx
    have hx_not : x ∉ tsupport χ := by simpa [hχ_tsupport] using hx
    exact image_eq_zero_of_notMem_tsupport hx_not
  have hg_zero_outside : ∀ {x : ℝ}, x ∉ B → g x = 0 := by
    intro x hx; simp [g, hχ_zero_outside hx]
  have hg_support : HasCompactSupport g := by
    refine HasCompactSupport.intro hB_compact ?_
    intro x hx; exact hg_zero_outside hx
  have hg_continuous : Continuous g := hg_contDiff.continuous
  have hg_cont_zero : ∀ {x : ℝ}, R < ‖x‖ → g_cont x = 0 := by
    intro x hx
    have hx_not : x ∉ tsupport g_cont := by
      intro hx_mem
      have hx_dist : dist x 0 ≤ R := Metric.mem_closedBall.mp (hR_subset hx_mem)
      have hx_abs_le : |x| ≤ R := by
        simpa [Real.dist_eq, sub_eq_add_neg] using hx_dist
      have hx_norm_le : ‖x‖ ≤ R := by simpa [Real.norm_eq_abs] using hx_abs_le
      exact (not_le_of_gt hx) hx_norm_le
    exact image_eq_zero_of_notMem_tsupport hx_not
  have hg_eq_outside : ∀ {x : ℝ}, x ∉ B → g_cont x = g x := by
    intro x hx
    have hx_norm : R + 1 < ‖x‖ := by
      have := Metric.mem_closedBall.not.1 hx
      simpa [B, Real.dist_eq, sub_eq_add_neg] using this
    have hx_gt : R < ‖x‖ :=
      (lt_trans (lt_add_of_pos_right R (by exact zero_lt_one)) hx_norm)
    have hg_cont_zero' : g_cont x = 0 := hg_cont_zero hx_gt
    have hg_zero' : g x = 0 := by
      have hx_not : x ∉ B := hx
      exact hg_zero_outside hx_not
    simp [hg_cont_zero', hg_zero']
  have h_bound_on_B : ∀ x ∈ B, ‖g x - g_cont x‖ ≤ δ := by
    intro x hxB
    have hx_dist : dist x 0 ≤ R + 1 := Metric.mem_closedBall.mp hxB
    have hx_norm : ‖x‖ ≤ R + 1 := by
      simpa [Real.dist_eq, sub_eq_add_neg] using hx_dist
    by_cases hx_inner : ‖x‖ ≤ R
    · have hx_ball : x ∈ Metric.closedBall (0 : ℝ) R := by
        simpa [Real.dist_eq, sub_eq_add_neg] using hx_inner
      have hχ_one' : χ x = 1 := hχ_one x hx_ball
      have hdiff_lt : ‖g₀ x - g_cont x‖ < δ := by
        simpa [dist_eq_norm, g] using hg₀_close x
      have : g x - g_cont x = g₀ x - g_cont x := by
        simp [g, hχ_one']
      simpa [this] using (le_of_lt hdiff_lt)
    · have hx_gt : R < ‖x‖ := lt_of_not_ge hx_inner
      have hg_cont_zero' : g_cont x = 0 := hg_cont_zero hx_gt
      have h_norm_lt : ‖g₀ x‖ < δ := by
        simpa [dist_eq_norm, hg_cont_zero'] using hg₀_close x
      have hχ_le' : χ x ≤ 1 := hχ_le_one x
      have hχ_nn' : 0 ≤ χ x := hχ_nonneg x
      have : ‖g x - g_cont x‖ = χ x * ‖g₀ x‖ := by
        simp [g, hg_cont_zero', Real.norm_eq_abs, abs_of_nonneg hχ_nn']
      have hχ_mul_le : χ x * ‖g₀ x‖ ≤ 1 * δ := by
        have h_norm_le : ‖g₀ x‖ ≤ δ := le_of_lt h_norm_lt
        have hχ_mul_le' : χ x * ‖g₀ x‖ ≤ χ x * δ :=
          mul_le_mul_of_nonneg_left h_norm_le hχ_nn'
        have hχδ_le : χ x * δ ≤ 1 * δ :=
          mul_le_mul_of_nonneg_right hχ_le' hδ_nonneg
        exact hχ_mul_le'.trans hχδ_le
      simpa [this] using hχ_mul_le.trans_eq (by simp)
  have h_diff_zero_outside : ∀ x, x ∉ B → g x - g_cont x = 0 := by
    intro x hx
    have hg0 := hg_eq_outside hx
    simp [hg0]
  have hC_nonneg : 0 ≤ δ := hδ_nonneg
  set diff := fun x : ℝ => g x - g_cont x with hdiff_def
  have hdiff_meas : AEStronglyMeasurable diff μ :=
    (hg_continuous.aestronglyMeasurable.sub hg_cont_continuous.aestronglyMeasurable)
  have h_indicator_mem :
      MemLp (Set.indicator B fun _ : ℝ => (1 : ℂ)) 2 μ :=
    memLp_indicator_const 2 hB_meas (1 : ℂ) (Or.inr hμ_B_ne_top)
  have hdiff_bound_indicator :
      ∀ᵐ x ∂μ, ‖diff x‖ ≤ δ * ‖(Set.indicator B fun _ : ℝ => (1 : ℂ)) x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hxB : x ∈ B
    · have hχ : (Set.indicator B (fun _ : ℝ => (1 : ℂ)) x) = 1 :=
        Set.indicator_of_mem hxB _
      have hdiff_le := h_bound_on_B x hxB
      have : ‖diff x‖ ≤ δ := by simpa [diff, hdiff_def] using hdiff_le
      simpa [hχ, diff, hdiff_def] using this
    · have hχ : (Set.indicator B (fun _ : ℝ => (1 : ℂ)) x) = 0 :=
        Set.indicator_of_notMem hxB _
      have hzero : diff x = 0 := by
        simpa [diff, hdiff_def] using h_diff_zero_outside x hxB
      simp [hχ, hzero]
  have hdiff_mem : MemLp diff 2 μ :=
    MemLp.of_le_mul h_indicator_mem hdiff_meas hdiff_bound_indicator
  have hg_memLp : MemLp g 2 μ := by
    have hsum := hdiff_mem.add hg_cont_memLp
    have hsum_fun : diff + g_cont = g := by
      funext x
      simp [Pi.add_apply, diff, g, sub_eq_add_neg]
    simpa [hsum_fun] using hsum
  have h_dist_le :=
    lp_dist_le_of_uniform_bound_on_set (μ := μ) (K := B) (C := δ)
      hg_cont_memLp hg_memLp hB_meas hμ_B_lt_top
      (by
        intro x hx
        simpa using hg_eq_outside (x := x) hx)
      hC_nonneg
      (by
        intro x hx
        simpa [norm_sub_rev] using h_bound_on_B x hx)
  have h_ratio_lt_one :
      Real.sqrt ((μ B).toReal) / (Real.sqrt ((μ B).toReal) + 1) < 1 :=
    (div_lt_one₀ h_den_pos).2 (by linarith)
  have h_mul_lt : δ * Real.sqrt ((μ B).toReal) < ε := by
    have hε_pos : 0 < ε := hε
    have := mul_lt_mul_of_pos_left h_ratio_lt_one hε_pos
    have h_eq : ε * (Real.sqrt ((μ B).toReal) / (Real.sqrt ((μ B).toReal) + 1))
        = δ * Real.sqrt ((μ B).toReal) := by
      set a := Real.sqrt ((μ B).toReal)
      set d := a + 1
      have : ε * (a / d) = a * (ε / d) := by
        simp [a, d, div_eq_mul_inv, mul_left_comm]
      simp [δ, a, d, div_eq_mul_inv, mul_comm, mul_left_comm]
    simpa [h_eq, mul_comm] using this
  have h_dist_lt :
      dist (hg_cont_memLp.toLp g_cont) (hg_memLp.toLp g) < ε :=
    lt_of_le_of_lt h_dist_le h_mul_lt
  refine ⟨g, hg_memLp, hg_support, ?_, h_dist_lt⟩
  simpa using hg_contDiff

/-- Norm equality for Lp elements under measure change -/
lemma lp_norm_eq_under_measure_change {σ : ℝ} (f : ℝ → ℂ) (g : ℝ → ℂ)
    (hf_weightedMeasure : MemLp f 2 (weightedMeasure σ))
    (hg_memLp : MemLp g 2 (weightedMeasure σ))
    (μ : Measure ℝ)
    (h_measure_eq : weightedMeasure σ = μ)
    (hf_memLp_μ : MemLp f 2 μ)
    (hg_memLp_μ : MemLp g 2 μ) :
    ‖hf_weightedMeasure.toLp f - hg_memLp.toLp g‖ =
    ‖hf_memLp_μ.toLp f - hg_memLp_μ.toLp g‖ := by
  subst h_measure_eq
  rfl

/-- Distance equivalence under measure equality for Lp spaces -/
lemma lp_dist_measure_equiv {σ : ℝ} (f : Hσ σ) (g : ℝ → ℂ)
    (f_Lp : Lp ℂ 2 (weightedMeasure σ))
    (hf_weightedMeasure : MemLp (Hσ.toFun f) 2 (weightedMeasure σ))
    (hf_Lp_eq : f_Lp = hf_weightedMeasure.toLp (Hσ.toFun f))
    (hg_memLp : MemLp g 2 (weightedMeasure σ))
    (h_measure_eq : weightedMeasure σ =
        mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :
    dist f (MemLp.toLp g (by rw [← h_measure_eq]; exact hg_memLp)) =
    dist f_Lp (hg_memLp.toLp g) := by
  classical
  subst hf_Lp_eq
  set μ := mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1)) with hμ
  have h_measure_eq' : weightedMeasure σ = μ := by
    simpa [μ, hμ] using h_measure_eq
  have hf_memLp : MemLp (Hσ.toFun f) 2 μ := by
    simpa [μ, h_measure_eq'] using hf_weightedMeasure
  have hf_toLp_eq : hf_memLp.toLp (Hσ.toFun f) = f := by
    apply Lp.ext
    refine (MemLp.coeFn_toLp hf_memLp).trans ?_
    simp [μ, Hσ.toFun]
  have hg_memLp' : MemLp g 2 μ := by
    simpa [μ, h_measure_eq'] using hg_memLp
  have h_left :
      ‖f - MemLp.toLp g (by simpa [μ, h_measure_eq'] using hg_memLp)‖ =
        ‖hf_memLp.toLp (Hσ.toFun f) - hg_memLp'.toLp g‖ := by
    simp [hf_toLp_eq, μ]
  have h_right :
      ‖hf_weightedMeasure.toLp (Hσ.toFun f) - MemLp.toLp g hg_memLp‖ =
        ‖hf_memLp.toLp (Hσ.toFun f) - hg_memLp'.toLp g‖ :=
    lp_norm_eq_under_measure_change (Hσ.toFun f)
      g hf_weightedMeasure hg_memLp μ h_measure_eq' hf_memLp hg_memLp'
  exact h_left.trans h_right.symm

/-- Triangle inequality chain for Lp approximation sequence -/
lemma lp_approximation_triangle_chain {σ : ℝ}
    (f_Lp : Lp ℂ 2 (weightedMeasure σ))
    (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (g_cont : ℝ → ℂ) (hg_cont_memLp : MemLp g_cont 2 (weightedMeasure σ))
    (g : ℝ → ℂ) (hg_memLp : MemLp g 2 (weightedMeasure σ)) (ε : ℝ)
    (hs_close : dist f_Lp (↑s) < ε / 2)
    (hg_cont_close : dist (↑s) (hg_cont_memLp.toLp g_cont) < ε / 4)
    (hg_mollify_close : dist (hg_cont_memLp.toLp g_cont) (hg_memLp.toLp g) < ε / 4) :
    dist f_Lp (hg_memLp.toLp g) < ε := by
  have h_triangle :
      dist f_Lp (hg_memLp.toLp g)
        ≤ dist f_Lp (↑s) +
            dist (↑s) (hg_cont_memLp.toLp g_cont) +
              dist (hg_cont_memLp.toLp g_cont) (hg_memLp.toLp g) := by
    calc
      dist f_Lp (hg_memLp.toLp g)
          ≤ dist f_Lp (↑s) + dist (↑s) (hg_memLp.toLp g) :=
            dist_triangle _ _ _
      _ ≤
          dist f_Lp (↑s) +
              (dist (↑s) (hg_cont_memLp.toLp g_cont) +
                dist (hg_cont_memLp.toLp g_cont) (hg_memLp.toLp g)) := by
            have h₂ :=
              dist_triangle (↑s) (hg_cont_memLp.toLp g_cont)
                (hg_memLp.toLp g)
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left h₂ (dist f_Lp (↑s))
      _ =
          dist f_Lp (↑s) + dist (↑s) (hg_cont_memLp.toLp g_cont) +
              dist (hg_cont_memLp.toLp g_cont) (hg_memLp.toLp g) := by
            simp [add_assoc]
  have hsum₀ :
      dist f_Lp (↑s) + dist (↑s) (hg_cont_memLp.toLp g_cont)
          < ε / 2 + ε / 4 := add_lt_add hs_close hg_cont_close
  have h_sum_lt :
      dist f_Lp (↑s) + dist (↑s) (hg_cont_memLp.toLp g_cont) +
          dist (hg_cont_memLp.toLp g_cont) (hg_memLp.toLp g) < ε := by
    have h := add_lt_add hsum₀ hg_mollify_close
    have h_eps : ε / 2 + (ε / 4 + ε / 4) = ε := by ring
    simpa [add_comm, add_left_comm, add_assoc, h_eps] using h
  exact lt_of_le_of_lt h_triangle h_sum_lt

/-- Smooth compactly supported functions are dense in weighted L² spaces for σ > 1/2 -/
lemma smooth_compactSupport_dense_in_weightedL2 {σ : ℝ} (hσ_lower : 1 / 2 < σ)
    (_hσ_upper : σ < 3 / 2)
    (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) : ∃ (g : ℝ → ℂ) (hg_mem : MemLp g 2
    (mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))),
     HasCompactSupport g ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
     dist f (hg_mem.toLp g) < ε := by
  -- Use the density of smooth compactly supported functions in weighted L² spaces
  -- Use the fact that for σ > 1/2, the weight function x^(2σ-1) is locally integrable
  have h_weight_integrable := weight_locallyIntegrable hσ_lower

  -- Step 1: First approximate by simple functions
  -- Elements of `Hσ σ` are already in the weighted L² space used to define the norm
  have hf_mem_base := memLp_of_Hσ (σ := σ) f

  have h_measure_equiv := weightedMeasure_eq_withDensity σ

  have hf_weightedMeasure :
      MemLp (Hσ.toFun f) 2 (weightedMeasure σ) := by
    simpa [h_measure_equiv, Hσ.toFun] using hf_mem_base

  -- Convert to Lp space element
  let f_Lp : Lp ℂ 2 (weightedMeasure σ) :=
    hf_weightedMeasure.toLp (Hσ.toFun f)

  -- Get simple function approximation from HilbertSpaceCore
  obtain ⟨s, hs_close⟩ := exists_simple_func_approximation f_Lp (ε / 2) (half_pos hε)

  have h_continuous_approx := lp_to_continuous_approx hσ_lower s (ε / 4) (by linarith)

  obtain ⟨g_cont, hg_cont_memLp, hg_cont_compact,
    hg_cont_continuous, hg_cont_close⟩ := h_continuous_approx

  have h_smooth_approx := continuous_to_smooth_approx hσ_lower g_cont hg_cont_memLp
      hg_cont_compact hg_cont_continuous (ε / 4) (by linarith)

  obtain ⟨g, hg_memLp, hg_compact, hg_smooth, hg_mollify_close⟩ := h_smooth_approx

  have h_measure_equiv_final := weightedMeasure_eq_withDensity σ

  -- Convert hg_memLp to the required measure type
  have hg_memLp_converted : MemLp g 2 (mulHaar.withDensity (fun x =>
    ENNReal.ofReal (x ^ (2 * σ - 1)))) := by
    rwa [h_measure_equiv_final] at hg_memLp

  use g, hg_memLp_converted
  constructor
  · exact hg_compact
  constructor
  · exact hg_smooth
  · -- Convert distances to work with consistent measures
    -- Apply the approximation error bound
    have hs_close' : dist f_Lp s < ε / 2 := by
      rw [dist_comm]
      exact hs_close
    -- Apply distance bound through approximation chain using triangle inequality
    -- We have the chain: f ≡ f_Lp → s → g_cont → g where:
    -- dist(f_Lp, s) < ε/2, dist(s, g_cont) < ε/4, dist(g_cont, g) < ε/4

    -- Apply approximation bounds using the triangle inequality
    -- The goal is to show dist f (hg_memLp_converted.toLp g) < ε
    -- We have approximation steps: f ≈ f_Lp ≈ s ≈ g_cont ≈ g

    -- Step 1: Convert to common measure space and apply triangle inequality
    have h_approx_bound : dist f (hg_memLp_converted.toLp g) < ε := by
      -- The distance bound follows from:
      -- 1. f = f_Lp (by construction)
      -- 2. dist(f_Lp, s) < ε/2 (given)
      -- 3. dist(s, g_cont) < ε/4 (given)
      -- 4. dist(g_cont, g) < ε/4 (given)
      -- 5. Triangle inequality: dist(f, g) ≤ sum of intermediate distances

      -- The key insight: we can work directly with the distances in weightedMeasure space
      -- and use the fact that hg_memLp_converted corresponds to hg_memLp under measure equivalence
      -- Since f_Lp was constructed from f and hg_memLp_converted from hg_memLp,
      -- the distance should be equivalent to working in the original space
      have h_dist_equiv : dist f (hg_memLp_converted.toLp g) = dist f_Lp (hg_memLp.toLp g) :=
        lp_dist_measure_equiv f g f_Lp hf_weightedMeasure rfl hg_memLp h_measure_equiv_final

      rw [h_dist_equiv]

      -- Apply triangle inequality in the weightedMeasure space: f_Lp → s → g_cont → g
      -- The key insight is we have bounds:
      -- dist f_Lp s < ε/2, dist s g_cont < ε/4, dist g_cont g < ε/4
      have h_triangle_chain : dist f_Lp (hg_memLp.toLp g) < ε :=
        lp_approximation_triangle_chain f_Lp s g_cont hg_cont_memLp g hg_memLp ε
          hs_close' hg_cont_close hg_mollify_close
      exact h_triangle_chain

    exact h_approx_bound

/-- Schwartz functions are dense in Hσ for σ > 1/2 -/
lemma schwartz_dense_in_Hσ {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2) :
    DenseRange (schwartzToHσ hσ_lower) := by
  -- Use the characterization: a subspace is dense iff its closure equals the whole space
  rw [denseRange_iff_closure_range]
  -- Show that closure of range equals the whole space
  rw [Set.eq_univ_iff_forall]
  intro f
  -- For any f ∈ Hσ, we can approximate it arbitrarily well by Schwartz functions
  -- Use the characterization: f ∈ closure S ↔ ∀ ε > 0, ∃ s ∈ S, dist f s < ε
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Need to find a Schwartz function φ such that dist f (schwartzToHσ hσ φ) < ε
  -- Strategy: First approximate f by a compactly supported smooth function,
  -- then extend it to a Schwartz function

  -- Step 1: Use the density of compactly supported smooth functions in L²
  -- For this, we use the fact that C_c^∞ functions are dense in L² spaces
  have h_smooth_dense := smooth_compactSupport_dense_in_weightedL2 hσ_lower hσ_upper f
    (ε / 2) (half_pos hε)

  obtain ⟨g, hg_mem, hg_compact, hg_smooth, hg_close⟩ := h_smooth_dense

  -- Step 2: Extend g to a Schwartz function
  -- Since g has compact support and is smooth, it's already a Schwartz function
  -- We just need to construct the SchwartzMap structure

  -- First verify that smooth compactly supported functions are Schwartz
  have hg_schwartz : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    intro k n
    -- Since g has compact support, say in [-R, R], and is smooth
    -- The bound is simply 0 outside [-R, R] and finite inside
    classical
    -- Define the auxiliary function whose boundedness we need
    set h : ℝ → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖
    have h_nonneg : ∀ x, 0 ≤ h x := by
      intro x
      exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    -- Since g has compact support and is smooth, its derivatives also have compact support
    -- and are supported in the same set
    set K := tsupport g with hK_def
    have hK_compact : IsCompact K := by
      rw [hK_def]
      exact hg_compact
    have hK_subset : tsupport (iteratedFDeriv ℝ n g) ⊆ K := by
      simpa [hK_def] using
        (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := g) (n := n))
    -- If the support is empty, the function vanishes everywhere and we can take C = 0
    by_cases h_empty : tsupport (iteratedFDeriv ℝ n g) = ∅
    · refine ⟨0, fun x => ?_⟩
      have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := by simp [h_empty]
      have hx_zero : iteratedFDeriv ℝ n g x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      simp [hx_zero]
    -- Otherwise, the image of h over the compact set K attains a maximum
    · have h_tsupport_nonempty :
        (tsupport (iteratedFDeriv ℝ n g)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr h_empty
      obtain ⟨x₀, hx₀_support⟩ := h_tsupport_nonempty
      have hx₀K : x₀ ∈ K := hK_subset hx₀_support
      -- Continuity of the auxiliary function
      have h_cont : Continuous h := by
        have h_pow_cont : Continuous fun x : ℝ => ‖x‖ ^ k :=
          (continuous_norm : Continuous fun x : ℝ => ‖x‖).pow _
        have h_iter_cont :
            Continuous fun x : ℝ => iteratedFDeriv ℝ n g x :=
          (hg_smooth.continuous_iteratedFDeriv (m := n)
            (hm := by exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))))
        exact h_pow_cont.mul (h_iter_cont.norm)
      -- The image of h on K is compact, hence admits a greatest element
      have h_image_compact : IsCompact (h '' K) := hK_compact.image h_cont
      have h_image_nonempty : (h '' K).Nonempty := ⟨h x₀, ⟨x₀, hx₀K, rfl⟩⟩
      obtain ⟨C, hC_isGreatest⟩ :=
        h_image_compact.exists_isGreatest h_image_nonempty
      rcases hC_isGreatest with ⟨hC_mem, hC_max⟩
      rcases hC_mem with ⟨xC, hxC_K, rfl⟩
      have hC_le : ∀ y ∈ h '' K, y ≤ h xC := (mem_upperBounds).1 hC_max
      refine ⟨h xC, ?_⟩
      intro x
      by_cases hxK : x ∈ K
      · have hx_mem : h x ∈ h '' K := ⟨x, hxK, rfl⟩
        exact hC_le _ hx_mem
      · have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := fun hx => hxK (hK_subset hx)
        have hx_zero : iteratedFDeriv ℝ n g x = 0 := image_eq_zero_of_notMem_tsupport hx_not
        have hC_nonneg : 0 ≤ h xC := h_nonneg xC
        have hx_val : h x = 0 := by simp [h, hx_zero]
        have hx_le : h x ≤ h xC := by simpa [hx_val] using hC_nonneg
        simpa [h] using hx_le

  -- Construct the Schwartz function from g
  let φ : SchwartzMap ℝ ℂ := ⟨g, hg_smooth, hg_schwartz⟩

  -- Step 3: Show that schwartzToHσ hσ_lower φ approximates f
  -- We need to show ∃ y ∈ Set.range (schwartzToHσ hσ_lower), dist f y < ε
  use schwartzToHσ hσ_lower φ
  refine ⟨?_, ?_⟩
  · -- Show that schwartzToHσ hσ φ is in the range
    use φ
  · -- Show the distance bound
    classical
    set μ := mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) with hμ
    have hμ_zero : μ (Set.Iic (0 : ℝ)) = 0 := by
      -- First note that the underlying Haar measure vanishes on nonpositive reals
      have h_base_zero : mulHaar (Set.Iic (0 : ℝ)) = 0 := by
        have h_inter : Set.Iic (0 : ℝ) ∩ Set.Ioi (0 : ℝ) = (∅ : Set ℝ) := by
          ext x
          constructor
          · intro hx
            rcases hx with ⟨hx_le, hx_gt⟩
            have hx_not : ¬(0 < x) := not_lt_of_ge hx_le
            exact (hx_not hx_gt).elim
          · intro hx
            simp at hx
        have h_meas : MeasurableSet (Set.Iic (0 : ℝ)) := measurableSet_Iic
        have :
            mulHaar (Set.Iic (0 : ℝ)) =
              (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
                (Set.Iic (0 : ℝ) ∩ Set.Ioi (0 : ℝ)) := by
          simp [mulHaar, h_meas]
        simpa [h_inter] using this
      -- Absolute continuity of the weighted measure
      have h_ac :=
        withDensity_absolutelyContinuous
          (μ := mulHaar) (f := fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))
      have : μ ≪ mulHaar := by
        simpa [hμ] using h_ac
      exact this.null_mono h_base_zero
    -- The two L² representatives coincide almost everywhere
    have h_ae_eq : g =ᵐ[μ] fun x : ℝ => if x > 0 then g x else 0 := by
      have h_subset :
          {x : ℝ | g x ≠ if x > 0 then g x else 0} ⊆ Set.Iic (0 : ℝ) := by
        intro x hx
        by_contra hx_pos
        have hx_pos' : 0 < x := lt_of_not_ge hx_pos
        change g x ≠ if x > 0 then g x else 0 at hx
        rw [if_pos hx_pos'] at hx
        exact hx rfl
      have h_diff_zero :
          μ {x : ℝ | g x ≠ if x > 0 then g x else 0} = 0 :=
        measure_mono_null h_subset hμ_zero
      refine (ae_iff).2 ?_
      simpa using h_diff_zero
    -- therefore the corresponding L² elements coincide
    have h_toLp_eq :
        hg_mem.toLp g =
          MemLp.toLp (fun x : ℝ => if x > 0 then φ x else 0)
            (schwartz_mem_Hσ hσ_lower φ) := by
      have h_ae_eq' : g =ᵐ[μ] fun x : ℝ => if x > 0 then φ x else 0 := by
        simpa [hμ] using h_ae_eq
      exact
        ((MemLp.toLp_eq_toLp_iff (hf := hg_mem)
              (hg := schwartz_mem_Hσ hσ_lower φ)).2 h_ae_eq')
    have h_toLp_eq' : hg_mem.toLp g = schwartzToHσ hσ_lower φ := by
      simpa [schwartzToHσ, hμ] using h_toLp_eq
    -- Conclude using the approximation provided by `hg_close`
    have h_lt : dist f (hg_mem.toLp g) < ε :=
      lt_trans hg_close (half_lt_self hε)
    simpa [h_toLp_eq'] using h_lt

/-- For any f ∈ Hσ and ε > 0, there exists a Schwartz function approximating f for σ > 1/2 -/
lemma exists_schwartz_approximation {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2)
    (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ_lower φ - f‖ < ε := by
  have h_dense := schwartz_dense_in_Hσ hσ_lower hσ_upper
  -- h_dense: Dense (Set.range (schwartzToHσ hσ_lower))
  -- This means closure (Set.range (schwartzToHσ hσ_lower)) = Set.univ
  have hf_in_closure : f ∈ closure (Set.range (schwartzToHσ hσ_lower)) := by
    have : closure (Set.range (schwartzToHσ hσ_lower)) = Set.univ := Dense.closure_eq h_dense
    rw [this]
    exact Set.mem_univ f
  rw [Metric.mem_closure_iff] at hf_in_closure
  obtain ⟨g, hg_range, hg_close⟩ := hf_in_closure ε hε
  obtain ⟨φ, rfl⟩ := hg_range
  use φ
  rw [dist_eq_norm] at hg_close
  rw [←norm_sub_rev]
  exact hg_close

/-- Schwartz approximation with a.e. convergence for σ > 1/2 -/
lemma schwartz_ae_dense {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2)
    (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ_lower φ - f‖ < ε ∧
    (schwartzToHσ hσ_lower φ : ℝ → ℂ) =ᵐ[mulHaar.withDensity (fun x =>
      ENNReal.ofReal (x ^ (2 * σ - 1)))] (fun x => if x > 0 then φ x else 0) := by
  obtain ⟨φ, hφ⟩ := exists_schwartz_approximation hσ_lower hσ_upper f ε hε
  use φ
  constructor
  · exact hφ
  · exact schwartzToHσ_ae_eq hσ_lower φ

end SchwartzDensity

end Frourio
