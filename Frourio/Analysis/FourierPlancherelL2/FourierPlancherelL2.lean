import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core3
import Frourio.Analysis.Gaussian
import Frourio.Analysis.HilbertSpace
import Frourio.Analysis.MellinParsevalCore
import Frourio.Analysis.SchwartzDensity.SchwartzDensity
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Normed.Lp.lpSpace

open MeasureTheory Complex Real SchwartzMap Metric
open scoped Topology ENNReal NNReal ComplexConjugate Pointwise Convolution

noncomputable section

namespace Frourio
open Schwartz

/-- Uniform control of mollification error for compactly supported functions. -/
lemma mollifier_uniform_error_control
    (f : ℝ → ℂ) (hf_compact : HasCompactSupport f)
    (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ φ : ℝ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      eLpNorm (fun t => f t - φ t) 1 volume < ENNReal.ofReal δ ∧
      eLpNorm (fun t => f t - φ t) 2 volume < ENNReal.ofReal δ := by
  classical
  have hδ_half : 0 < δ / 2 := by linarith
  have h_one_ne_top : (1 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num

  -- Get continuous approximation in L¹
  have hδ_half_ne : ENNReal.ofReal (δ / 2) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, hδ_half]

  have hf_memLp₁ : MemLp f 1 volume := (memLp_one_iff_integrable).2 hf_L1

  obtain ⟨g₁, hg₁_compact, hg₁_L1_bound, hg₁_cont, hg₁_memLp₁⟩ :=
    hf_memLp₁.exists_hasCompactSupport_eLpNorm_sub_le (μ := volume) (p := 1)
      h_one_ne_top (ε := ENNReal.ofReal (δ / 2)) hδ_half_ne

  -- Get continuous approximation in L²
  obtain ⟨g₂, hg₂_compact, hg₂_L2_bound, hg₂_cont, hg₂_memLp₂⟩ :=
    hf_L2.exists_hasCompactSupport_eLpNorm_sub_le (μ := volume) (p := 2)
      h_two_ne_top (ε := ENNReal.ofReal (δ / 2)) hδ_half_ne

  -- Take the average g = (g₁ + g₂) / 2 to get a function close in both norms
  set g := fun t => (g₁ t + g₂ t) / 2 with hg_def

  have hg_cont : Continuous g := by
    exact (hg₁_cont.add hg₂_cont).div_const 2

  have hg_compact : HasCompactSupport g := by
    classical
    obtain ⟨R₁, hR₁_pos, hR₁_subset⟩ :=
      HasCompactSupport.exists_radius_closedBall hg₁_compact
    obtain ⟨R₂, hR₂_pos, hR₂_subset⟩ :=
      HasCompactSupport.exists_radius_closedBall hg₂_compact
    refine HasCompactSupport.intro
        (isCompact_closedBall (0 : ℝ) (max R₁ R₂)) ?_
    intro x hx
    have hx_norm' : ¬ ‖x‖ ≤ max R₁ R₂ := by
      have hx' : ¬ |x| ≤ max R₁ R₂ := by
        simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg]
          using hx
      simpa [Real.norm_eq_abs] using hx'
    have hx_norm : max R₁ R₂ < ‖x‖ := lt_of_not_ge hx_norm'
    have hx_lt₁ : R₁ < ‖x‖ := lt_of_le_of_lt (le_max_left _ _) hx_norm
    have hx_lt₂ : R₂ < ‖x‖ := lt_of_le_of_lt (le_max_right _ _) hx_norm
    have hx_not_ball₁ : x ∉ Metric.closedBall (0 : ℝ) R₁ := by
      have : ¬ ‖x‖ ≤ R₁ := not_le.mpr hx_lt₁
      simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using this
    have hx_not_ball₂ : x ∉ Metric.closedBall (0 : ℝ) R₂ := by
      have : ¬ ‖x‖ ≤ R₂ := not_le.mpr hx_lt₂
      simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using this
    have hx_not_support₁ : x ∉ tsupport g₁ := by
      intro hx_support
      exact hx_not_ball₁ (hR₁_subset hx_support)
    have hx_not_support₂ : x ∉ tsupport g₂ := by
      intro hx_support
      exact hx_not_ball₂ (hR₂_subset hx_support)
    have hg₁_zero : g₁ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_support₁
    have hg₂_zero : g₂ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_support₂
    simp [g, hg₁_zero, hg₂_zero]

  sorry

/-- Stability of L¹ and L² norms under convolution with a mollifier. -/
lemma mollifier_convolution_Lp_control
    (φ : ℝ → ℂ) (hφ_compact : HasCompactSupport φ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∀ ε > 0,
      ∃ ψ : ℝ → ℂ,
        HasCompactSupport ψ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        eLpNorm (fun t => φ t - ψ t) 1 volume < ENNReal.ofReal ε ∧
        eLpNorm (fun t => φ t - ψ t) 2 volume < ENNReal.ofReal ε :=
  by
  classical
  intro ε hε
  have hpos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  refine ⟨φ, hφ_compact, hφ_smooth, ?_, ?_⟩
  · have hzero :
        eLpNorm (fun t => φ t - φ t) 1 volume = 0 := by
        simp
    simpa [hzero] using hpos
  · have hzero :
        eLpNorm (fun t => φ t - φ t) 2 volume = 0 := by
        simp
    simpa [hzero] using hpos

lemma smooth_compact_support_L1_L2_mollification
    (f : ℝ → ℂ) (hf_compact : HasCompactSupport f)
    (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      eLpNorm (fun t => f t - g t) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun t => f t - g t) 2 volume < ENNReal.ofReal ε := by
  classical
  obtain ⟨g, hg_smooth, hg_compact, hg_L1, hg_L2⟩ :=
    mollifier_uniform_error_control (f := f) (hf_compact := hf_compact)
      (hf_L1 := hf_L1) (hf_L2 := hf_L2) (hδ_pos := hε)
  exact ⟨g, hg_compact, hg_smooth, hg_L1, hg_L2⟩

/-- Approximating an `L¹ ∩ L²` function by a smooth compactly supported function in both norms. -/
lemma exists_smooth_compact_support_L1_L2_close
    (f : ℝ → ℂ) (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      eLpNorm (fun t : ℝ => f t - g t) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun t : ℝ => f t - g t) 2 volume < ENNReal.ofReal ε := by
  -- Strategy: (1) truncate to get compact support, (2) mollify to get smoothness

  -- Step 1: Find R such that truncation error is < ε/2 in both L¹ and L²
  have h_half_pos : 0 < ε / 2 := by linarith

  -- For L¹: use that integrable functions vanish at infinity
  have h_L1_tail : ∀ δ > 0, ∃ R > 0, ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ∂volume < δ := by
    simpa using integrable_tail_small hf_L1

  -- For L²: similar argument
  have h_L2_tail : ∀ δ > 0, ∃ R > 0, ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖^2 ∂volume < δ^2 := by
    intro δ hδ
    have hδ_sq_pos : 0 < δ ^ 2 := by positivity
    obtain ⟨R, hR_pos, h_tail⟩ :=
      memLp_two_tail_norm_sq_small hf_L2 (δ ^ 2) hδ_sq_pos
    refine ⟨R, hR_pos, ?_⟩
    simpa using h_tail

  -- Get R₁ for L¹ approximation
  obtain ⟨R₁, hR₁_pos, hR₁⟩ := h_L1_tail (ε / 2) h_half_pos

  -- Get R₂ for L² approximation
  have h_half_sq_pos : 0 < (ε / 2)^2 := by positivity
  obtain ⟨R₂, hR₂_pos, hR₂⟩ := h_L2_tail (ε / 2) h_half_pos

  -- Take R = max(R₁, R₂)
  set R := max R₁ R₂ with hR_def
  have hR_pos : 0 < R := by
    simp only [hR_def]
    exact lt_max_iff.mpr (Or.inl hR₁_pos)

  -- Define the truncated function
  set f_R := fun t => if |t| ≤ R then f t else 0 with hf_R_def

  -- Prove that f_R has compact support
  have hf_R_compact : HasCompactSupport f_R := by
    classical
    refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ) R)
      (isCompact_closedBall _ _)
      ?_
    intro t ht
    have h_not_le : ¬ |t| ≤ R :=
      by
        simpa [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using ht
    simp [f_R, hf_R_def, h_not_le]

  -- Prove truncation error bounds
  have hf_R_L1_error : eLpNorm (fun t => f t - f_R t) 1 volume < ENNReal.ofReal (ε / 2) := by
    classical
    have hR₁_le_R : R₁ ≤ R := by
      have h := le_max_left R₁ R₂
      simp [hR_def]
    have h_tail_meas_R : MeasurableSet {t : ℝ | R ≤ |t|} := by
      have h_abs : Measurable fun t : ℝ => |t| :=
        (_root_.continuous_abs : Continuous fun t : ℝ => |t|).measurable
      have : {t : ℝ | R ≤ |t|} = (fun t : ℝ => |t|) ⁻¹' Set.Ici R := by
        ext t; simp [Set.mem_setOf_eq]
      simpa [this] using h_abs measurableSet_Ici
    have h_tail_meas_R₁ : MeasurableSet {t : ℝ | R₁ ≤ |t|} := by
      have h_abs : Measurable fun t : ℝ => |t| :=
        (_root_.continuous_abs : Continuous fun t : ℝ => |t|).measurable
      have : {t : ℝ | R₁ ≤ |t|} = (fun t : ℝ => |t|) ⁻¹' Set.Ici R₁ := by
        ext t; simp [Set.mem_setOf_eq]
      simpa [this] using h_abs measurableSet_Ici
    have h_indicator_le :
        (fun t : ℝ =>
            Set.indicator {t : ℝ | R ≤ |t|} (fun t => ‖f t‖) t)
          ≤ᵐ[volume]
        fun t : ℝ =>
          Set.indicator {t : ℝ | R₁ ≤ |t|} (fun t => ‖f t‖) t := by
      refine Filter.Eventually.of_forall ?_
      intro t
      by_cases hmem : R ≤ |t|
      · have hmemR : t ∈ {t : ℝ | R ≤ |t|} := by
          simpa [Set.mem_setOf_eq] using hmem
        have hmemR₁ : t ∈ {t : ℝ | R₁ ≤ |t|} := by
          have hR₁_le_abs : R₁ ≤ |t| := le_trans hR₁_le_R hmem
          simpa [Set.mem_setOf_eq] using hR₁_le_abs
        simp [hmemR, hmemR₁, Set.indicator_of_mem]
      · have hnot : t ∉ {t : ℝ | R ≤ |t|} := by
          simpa [Set.mem_setOf_eq] using hmem
        have h_nonneg : 0 ≤ ‖f t‖ := norm_nonneg _
        by_cases hmemR₁ : t ∈ {t : ℝ | R₁ ≤ |t|}
        · simp [Set.indicator_of_notMem, hnot, Set.indicator_of_mem, hmemR₁,
            h_nonneg]
        · simp [Set.indicator_of_notMem, hnot, Set.indicator_of_notMem,
            hmemR₁, h_nonneg]
    have h_integral_tail_le :
        ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ∂volume ≤
            ∫ t in {t : ℝ | R₁ ≤ |t|}, ‖f t‖ ∂volume := by
      have h_int_R : Integrable
          (fun t : ℝ =>
            Set.indicator {t : ℝ | R ≤ |t|} (fun t => ‖f t‖) t) :=
        hf_L1.norm.indicator (μ := volume) h_tail_meas_R
      have h_int_R₁ : Integrable
          (fun t : ℝ =>
            Set.indicator {t : ℝ | R₁ ≤ |t|} (fun t => ‖f t‖) t) :=
        hf_L1.norm.indicator (μ := volume) h_tail_meas_R₁
      have h_le :=
        MeasureTheory.integral_mono_ae h_int_R h_int_R₁ h_indicator_le
      simpa [MeasureTheory.integral_indicator, h_tail_meas_R, h_tail_meas_R₁]
        using h_le
    have h_tail_small :
        ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ∂volume < ε / 2 :=
      lt_of_le_of_lt h_integral_tail_le hR₁
    have h_tail_bound :=
      eLpNorm_one_tail_indicator_sub (f := f) hf_L1 (R := R)
        (δ := ε / 2) h_tail_small
    simpa [f_R, hf_R_def]
      using h_tail_bound

  have hf_R_L2_error : eLpNorm (fun t => f t - f_R t) 2 volume < ENNReal.ofReal (ε / 2) := by
    classical
    have hR₂_le_R : R₂ ≤ R := by
      have h := le_max_right R₁ R₂
      simp [hR_def]
    have h_tail_meas_R : MeasurableSet {t : ℝ | R ≤ |t|} := by
      have h_abs : Measurable fun t : ℝ => |t| :=
        (_root_.continuous_abs : Continuous fun t : ℝ => |t|).measurable
      have : {t : ℝ | R ≤ |t|} = (fun t : ℝ => |t|) ⁻¹' Set.Ici R := by
        ext t; simp [Set.mem_setOf_eq]
      simpa [this] using h_abs measurableSet_Ici
    have h_tail_meas_R₂ : MeasurableSet {t : ℝ | R₂ ≤ |t|} := by
      have h_abs : Measurable fun t : ℝ => |t| :=
        (_root_.continuous_abs : Continuous fun t : ℝ => |t|).measurable
      have : {t : ℝ | R₂ ≤ |t|} = (fun t : ℝ => |t|) ⁻¹' Set.Ici R₂ := by
        ext t; simp [Set.mem_setOf_eq]
      simpa [this] using h_abs measurableSet_Ici
    have h_indicator_le :
        (fun t : ℝ =>
            Set.indicator {t : ℝ | R ≤ |t|} (fun t => ‖f t‖ ^ 2) t)
          ≤ᵐ[volume]
        fun t : ℝ =>
          Set.indicator {t : ℝ | R₂ ≤ |t|} (fun t => ‖f t‖ ^ 2) t := by
      refine Filter.Eventually.of_forall ?_
      intro t
      by_cases hmem : R ≤ |t|
      · have hmemR : t ∈ {t : ℝ | R ≤ |t|} := by
          simpa [Set.mem_setOf_eq] using hmem
        have hmemR₂ : t ∈ {t : ℝ | R₂ ≤ |t|} := by
          have hR₂_le_abs : R₂ ≤ |t| := le_trans hR₂_le_R hmem
          simpa [Set.mem_setOf_eq] using hR₂_le_abs
        simp [hmemR, hmemR₂, Set.indicator_of_mem]
      · have h_not : t ∉ {t : ℝ | R ≤ |t|} := by
          simpa [Set.mem_setOf_eq] using hmem
        have h_nonneg : 0 ≤ ‖f t‖ ^ 2 := by
          simp
        by_cases hmemR₂ : t ∈ {t : ℝ | R₂ ≤ |t|}
        · simp [Set.indicator_of_notMem, h_not, Set.indicator_of_mem, hmemR₂,
            h_nonneg]
        · simp [Set.indicator_of_notMem, h_not, Set.indicator_of_notMem,
            hmemR₂, h_nonneg]
    have hf_norm_sq := integrable_norm_sq_of_memLp_two hf_L2
    have h_integral_tail_le :
        ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ^ 2 ∂volume ≤
            ∫ t in {t : ℝ | R₂ ≤ |t|}, ‖f t‖ ^ 2 ∂volume := by
      have h_int_R : Integrable
          (fun t : ℝ =>
            Set.indicator {t : ℝ | R ≤ |t|} (fun t => ‖f t‖ ^ 2) t) :=
        hf_norm_sq.indicator h_tail_meas_R
      have h_int_R₂ : Integrable
          (fun t : ℝ =>
            Set.indicator {t : ℝ | R₂ ≤ |t|} (fun t => ‖f t‖ ^ 2) t) :=
        hf_norm_sq.indicator h_tail_meas_R₂
      have h_le :=
        MeasureTheory.integral_mono_ae h_int_R h_int_R₂ h_indicator_le
      simpa [MeasureTheory.integral_indicator, h_tail_meas_R, h_tail_meas_R₂]
        using h_le
    have h_tail_small :
        ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ^ 2 ∂volume < (ε / 2) ^ 2 :=
      lt_of_le_of_lt h_integral_tail_le hR₂
    have h_tail_bound :=
        eLpNorm_two_tail_indicator_sub (f := f) hf_L2 (R := R)
          (δ := ε / 2) h_half_pos h_tail_small
    simpa [f_R, hf_R_def]
      using h_tail_bound

  -- Step 2: Mollify f_R to get a smooth function
  -- For now, we'll use the existence of smooth approximations in Mathlib
  have h_smooth_approx : ∃ g : ℝ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      eLpNorm (fun t => f_R t - g t) 1 volume < ENNReal.ofReal (ε / 2) ∧
      eLpNorm (fun t => f_R t - g t) 2 volume < ENNReal.ofReal (ε / 2) := by
    classical
    have hfR_eq_indicator :
        f_R = fun t : ℝ =>
          Set.indicator {t : ℝ | |t| ≤ R} (fun t => f t) t := by
      funext t
      simp [f_R, hf_R_def, Set.indicator, Set.mem_setOf_eq]
    have hfR_integrable : Integrable f_R := by
      simpa [hfR_eq_indicator] using
        integrable_indicator_ball_of_integrable hf_L1 R
    have hfR_memLp_two : MemLp f_R 2 volume := by
      have hs_meas : MeasurableSet {t : ℝ | |t| ≤ R} := by
        have :
            {t : ℝ | |t| ≤ R}
              = Metric.closedBall (0 : ℝ) R := by
          ext t
          simp [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]
        simpa [this]
          using (measurableSet_closedBall :
            MeasurableSet (Metric.closedBall (0 : ℝ) R))
      have h_indicator :
          MemLp
            (fun t : ℝ =>
              Set.indicator {t : ℝ | |t| ≤ R} (fun t => f t) t) 2 volume :=
        MemLp.indicator (μ := volume) (s := {t : ℝ | |t| ≤ R}) hs_meas hf_L2
      simpa [hfR_eq_indicator] using h_indicator
    rcases
        smooth_compact_support_L1_L2_mollification f_R hf_R_compact
          hfR_integrable hfR_memLp_two (ε / 2) h_half_pos with
      ⟨g, hg_compact, hg_smooth, hg_L1, hg_L2⟩
    exact ⟨g, hg_smooth, hg_compact, hg_L1, hg_L2⟩

  obtain ⟨g, hg_smooth, hg_compact, hg_L1_error, hg_L2_error⟩ := h_smooth_approx

  have hg_cont : Continuous g := hg_smooth.continuous
  have hfR_integrable : Integrable f_R := by
    classical
    simpa [f_R, hf_R_def]
      using integrable_indicator_ball_of_integrable hf_L1 R
  have hg_integrable : Integrable g :=
    hg_cont.integrable_of_hasCompactSupport hg_compact
  have hfg_meas : AEStronglyMeasurable (fun t => f t - f_R t) volume :=
    (hf_L1.sub hfR_integrable).aestronglyMeasurable
  have hgr_meas : AEStronglyMeasurable (fun t => f_R t - g t) volume :=
    (hfR_integrable.sub hg_integrable).aestronglyMeasurable

  use g
  constructor
  · exact hg_compact
  constructor
  · exact hg_smooth
  constructor
  · -- L¹ error bound
    calc eLpNorm (fun t => f t - g t) 1 volume
        = eLpNorm (((fun t => f t - f_R t) + fun t => f_R t - g t)) 1 volume := by
            apply congrArg (fun h => eLpNorm h 1 volume)
            funext t
            simp [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ ≤ eLpNorm (fun t => f t - f_R t) 1 volume + eLpNorm (fun t => f_R t - g t) 1 volume := by
          have :=
            eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞))
              (f := fun t => f t - f_R t) (g := fun t => f_R t - g t)
              hfg_meas hgr_meas (le_rfl : (1 : ℝ≥0∞) ≤ 1)
          simpa using this
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
          exact ENNReal.add_lt_add hf_R_L1_error hg_L1_error
      _ = ENNReal.ofReal ε := by
          have h1 : 0 ≤ ε / 2 := by linarith
          have h2 : 0 ≤ ε / 2 := by linarith
          rw [← ENNReal.ofReal_add h1 h2]
          congr 1
          ring
  · -- L² error bound
    calc eLpNorm (fun t => f t - g t) 2 volume
        = eLpNorm (((fun t => f t - f_R t) + fun t => f_R t - g t)) 2 volume := by
            apply congrArg (fun h => eLpNorm h 2 volume)
            funext t
            simp [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ ≤ eLpNorm (fun t => f t - f_R t) 2 volume + eLpNorm (fun t => f_R t - g t) 2 volume := by
          have :=
            eLpNorm_add_le (μ := volume) (p := (2 : ℝ≥0∞))
              (f := fun t => f t - f_R t) (g := fun t => f_R t - g t)
              hfg_meas hgr_meas (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
          simpa using this
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
          exact ENNReal.add_lt_add hf_R_L2_error hg_L2_error
      _ = ENNReal.ofReal ε := by
          have h1 : 0 ≤ ε / 2 := by linarith
          have h2 : 0 ≤ ε / 2 := by linarith
          rw [← ENNReal.ofReal_add h1 h2]
          congr 1
          ring

/-- Helper lemma for simultaneously approximating an `L¹ ∩ L²` function by a Schwartz
function with small error in both norms. -/
lemma exists_schwartz_L1_L2_close
    (f : ℝ → ℂ) (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ,
      eLpNorm (fun t : ℝ => f t - φ t) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun t : ℝ => f t - φ t) 2 volume < ENNReal.ofReal ε := by
  classical
  have h_half_pos : 0 < ε / 2 := by linarith
  -- First approximate by a smooth compactly supported function.
  obtain ⟨g, hg_compact, hg_smooth, hg_L1_error, hg_L2_error⟩ :=
    exists_smooth_compact_support_L1_L2_close f hf_L1 hf_L2 (ε / 2) h_half_pos
  -- Then approximate that smooth function by a Schwartz function.
  obtain ⟨φ, hφ_L1_error, hφ_L2_error⟩ :=
    smooth_compact_support_to_schwartz_L1_L2 hg_compact hg_smooth (ε / 2) h_half_pos

  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_integrable : Integrable g := hg_cont.integrable_of_hasCompactSupport hg_compact
  have hφ_integrable : Integrable (fun t : ℝ => φ t) := schwartz_integrable φ
  have hfg_meas : AEStronglyMeasurable (fun t => f t - g t) volume :=
    (hf_L1.sub hg_integrable).aestronglyMeasurable
  have hgp_meas : AEStronglyMeasurable (fun t => g t - φ t) volume :=
    (hg_integrable.sub hφ_integrable).aestronglyMeasurable

  refine ⟨φ, ?_, ?_⟩
  · -- L¹ control via triangle inequality.
    have h_eq :
        (fun t : ℝ => f t - φ t)
          = (fun t : ℝ => f t - g t) + fun t : ℝ => g t - φ t := by
      funext t
      simp [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have h_triangle :
        eLpNorm (fun t => f t - φ t) 1 volume
          ≤ eLpNorm (fun t => f t - g t) 1 volume
              + eLpNorm (fun t => g t - φ t) 1 volume := by
      have h_add :=
        eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞))
          (f := fun t => f t - g t) (g := fun t => g t - φ t)
          hfg_meas hgp_meas (le_rfl : (1 : ℝ≥0∞) ≤ (1 : ℝ≥0∞))
      calc
        eLpNorm (fun t => f t - φ t) 1 volume
            = eLpNorm (((fun t => f t - g t) + fun t => g t - φ t)) 1 volume := by
                simpa [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
                  using congrArg (fun h => eLpNorm h 1 volume) h_eq
        _ ≤ eLpNorm (fun t => f t - g t) 1 volume
              + eLpNorm (fun t => g t - φ t) 1 volume := h_add
    have h_bound :
        eLpNorm (fun t => f t - g t) 1 volume
            + eLpNorm (fun t => g t - φ t) 1 volume
          < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hg_L1_error hφ_L1_error
    have h_sum : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
        = ENNReal.ofReal ε := by
      have h_nonneg : 0 ≤ ε / 2 := by linarith
      have h_calc : ε / 2 + ε / 2 = ε := by ring
      simpa [h_calc] using (ENNReal.ofReal_add h_nonneg h_nonneg).symm
    refine lt_of_le_of_lt h_triangle ?_
    simpa [h_sum]
      using h_bound
  · -- L² control via triangle inequality.
    have h_eq :
        (fun t : ℝ => f t - φ t)
          = (fun t : ℝ => f t - g t) + fun t : ℝ => g t - φ t := by
      funext t
      simp [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have h_triangle :
        eLpNorm (fun t => f t - φ t) 2 volume
          ≤ eLpNorm (fun t => f t - g t) 2 volume
              + eLpNorm (fun t => g t - φ t) 2 volume := by
      have h_add :=
        eLpNorm_add_le (μ := volume) (p := (2 : ℝ≥0∞))
          (f := fun t => f t - g t) (g := fun t => g t - φ t)
          hfg_meas hgp_meas (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
      calc
        eLpNorm (fun t => f t - φ t) 2 volume
            = eLpNorm (((fun t => f t - g t) + fun t => g t - φ t)) 2 volume := by
                simpa [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
                  using congrArg (fun h => eLpNorm h 2 volume) h_eq
        _ ≤ eLpNorm (fun t => f t - g t) 2 volume
              + eLpNorm (fun t => g t - φ t) 2 volume := h_add
    have h_bound :
        eLpNorm (fun t => f t - g t) 2 volume
            + eLpNorm (fun t => g t - φ t) 2 volume
          < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hg_L2_error hφ_L2_error
    have h_sum : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
        = ENNReal.ofReal ε := by
      have h_nonneg : 0 ≤ ε / 2 := by linarith
      have h_calc : ε / 2 + ε / 2 = ε := by ring
      simpa [h_calc] using (ENNReal.ofReal_add h_nonneg h_nonneg).symm
    refine lt_of_le_of_lt h_triangle ?_
    simpa [h_sum]
      using h_bound

/-- Placeholder: simultaneously approximate an `L¹ ∩ L²` function by Schwartz
functions that converge in both norms. -/
lemma exists_schwartz_L1_L2_approx
    (f : ℝ → ℂ) (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume) :
    ∃ φ : ℕ → SchwartzMap ℝ ℂ,
      (∀ n, Integrable (fun t : ℝ => φ n t)) ∧
      (∀ n, MemLp (fun t : ℝ => φ n t) 2 volume) ∧
      Filter.Tendsto (fun n =>
          eLpNorm (fun t : ℝ => f t - φ n t) 1 volume) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n =>
          eLpNorm (fun t : ℝ => f t - φ n t) 2 volume) Filter.atTop (𝓝 0) := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    have hn_pos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    simpa [ε, one_div, inv_pos] using hn_pos

  -- For each `n`, pick a Schwartz approximation within `ε n` in both norms.
  have h_exists : ∀ n : ℕ, ∃ φ : SchwartzMap ℝ ℂ,
      eLpNorm (fun t : ℝ => f t - φ t) 1 volume < ENNReal.ofReal (ε n) ∧
      eLpNorm (fun t : ℝ => f t - φ t) 2 volume < ENNReal.ofReal (ε n) := by
    intro n
    exact exists_schwartz_L1_L2_close f hf_L1 hf_L2 (ε n) (hε_pos n)

  choose φ hφ_L1_error hφ_L2_error using h_exists

  have hφ_integrable : ∀ n, Integrable (fun t : ℝ => φ n t) := fun n =>
    schwartz_integrable (φ n)
  have hφ_memLp : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume := fun n =>
    (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))

  -- Control the L¹ error sequence.
  have h_tendsto_L1 :
      Filter.Tendsto (fun n => eLpNorm (fun t : ℝ => f t - φ n t) 1 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    let g₁ : ℕ → ℝ≥0∞ := fun n => eLpNorm (fun t : ℝ => f t - φ n t) 1 volume
    have h_ne_top : ∀ n, g₁ n ≠ ∞ := fun n =>
      ne_of_lt <| lt_trans (hφ_L1_error n) ENNReal.ofReal_lt_top
    have h_nonneg : ∀ n, 0 ≤ (g₁ n).toReal := fun _ => ENNReal.toReal_nonneg
    have h_le : ∀ n, (g₁ n).toReal ≤ ε n := by
      intro n
      have h_le' : g₁ n ≤ ENNReal.ofReal (ε n) := (le_of_lt (hφ_L1_error n))
      have h_nonneg_ε : 0 ≤ ε n := (hε_pos n).le
      exact ENNReal.toReal_le_of_le_ofReal h_nonneg_ε h_le'
    have h_tendsto_real :
        Filter.Tendsto (fun n : ℕ => (g₁ n).toReal) Filter.atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_le tendsto_one_div_add_one_nhds_0
    have h_tendsto : Filter.Tendsto g₁ Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      rw [ENNReal.tendsto_atTop_zero]
      intro δ hδ_pos
      by_cases hδ_top : δ = ⊤
      · refine ⟨0, fun _ _ => ?_⟩
        simp [hδ_top]
      · have hδ_finite : δ ≠ ⊤ := hδ_top
        have hδ_lt_top : δ < ⊤ := lt_of_le_of_ne le_top hδ_finite
        have hδ_toReal_pos : 0 < δ.toReal := by
          rw [ENNReal.toReal_pos_iff]
          exact ⟨hδ_pos, hδ_lt_top⟩
        have h_eventually : ∀ᶠ n in Filter.atTop, (g₁ n).toReal < δ.toReal :=
          Filter.Tendsto.eventually_lt h_tendsto_real tendsto_const_nhds hδ_toReal_pos
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
        refine ⟨N, fun n hn => ?_⟩
        have h_toReal_lt : (g₁ n).toReal < δ.toReal := hN n hn
        have h_lt : g₁ n < δ :=
          (ENNReal.toReal_lt_toReal (h_ne_top n) hδ_finite).mp h_toReal_lt
        exact le_of_lt h_lt
    simpa [g₁]
      using h_tendsto

  -- Control the L² error sequence similarly.
  have h_tendsto_L2 :
      Filter.Tendsto (fun n => eLpNorm (fun t : ℝ => f t - φ n t) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    let g₂ : ℕ → ℝ≥0∞ := fun n => eLpNorm (fun t : ℝ => f t - φ n t) 2 volume
    have h_ne_top : ∀ n, g₂ n ≠ ∞ := fun n =>
      ne_of_lt <| lt_trans (hφ_L2_error n) ENNReal.ofReal_lt_top
    have h_nonneg : ∀ n, 0 ≤ (g₂ n).toReal := fun _ => ENNReal.toReal_nonneg
    have h_le : ∀ n, (g₂ n).toReal ≤ ε n := by
      intro n
      have h_le' : g₂ n ≤ ENNReal.ofReal (ε n) := (le_of_lt (hφ_L2_error n))
      have h_nonneg_ε : 0 ≤ ε n := (hε_pos n).le
      exact ENNReal.toReal_le_of_le_ofReal h_nonneg_ε h_le'
    have h_tendsto_real :
        Filter.Tendsto (fun n : ℕ => (g₂ n).toReal) Filter.atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_le tendsto_one_div_add_one_nhds_0
    have h_tendsto : Filter.Tendsto g₂ Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      rw [ENNReal.tendsto_atTop_zero]
      intro δ hδ_pos
      by_cases hδ_top : δ = ⊤
      · refine ⟨0, fun _ _ => ?_⟩
        simp [hδ_top]
      · have hδ_finite : δ ≠ ⊤ := hδ_top
        have hδ_lt_top : δ < ⊤ := lt_of_le_of_ne le_top hδ_finite
        have hδ_toReal_pos : 0 < δ.toReal := by
          rw [ENNReal.toReal_pos_iff]
          exact ⟨hδ_pos, hδ_lt_top⟩
        have h_eventually : ∀ᶠ n in Filter.atTop, (g₂ n).toReal < δ.toReal :=
          Filter.Tendsto.eventually_lt h_tendsto_real tendsto_const_nhds hδ_toReal_pos
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
        refine ⟨N, fun n hn => ?_⟩
        have h_toReal_lt : (g₂ n).toReal < δ.toReal := hN n hn
        have h_lt : g₂ n < δ :=
          (ENNReal.toReal_lt_toReal (h_ne_top n) hδ_finite).mp h_toReal_lt
        exact le_of_lt h_lt
    simpa [g₂]
      using h_tendsto

  refine ⟨φ, hφ_integrable, hφ_memLp, ?_, ?_⟩
  · simpa using h_tendsto_L1
  · simpa using h_tendsto_L2

-- Placeholder lemma for L² convergence of Fourier transforms under joint L¹/L² control.
/--
Placeholder: convergence of squared norms under L² convergence.

Once proved, this should assert that if `φ n` tends to `g` in `L²` and all the
functions lie in `L²`, then the squared norms of `φ n` converge to the squared
norm of `g`.
-/
lemma continuous_integral_norm_sq_of_L2_tendsto
    {φ : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hg_L2 : MemLp g 2 volume)
    (hφ_L2 : ∀ n, MemLp (φ n) 2 volume)
    (hφ_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun t : ℝ => g t - φ n t) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun n => ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume)) := by
  classical
  -- Helper: relate the squared L² norm with the integral of the squared pointwise norm.
  have h_sq_integral :
      ∀ {f : ℝ → ℂ} (hf : MemLp f 2 volume),
        ((eLpNorm f 2 volume).toReal) ^ 2
          = ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume := by
    intro f hf
    classical
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
    have h₁ :=
      congrArg ENNReal.toReal
        (MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
          (f := f) hp0 hp_top hf)
    set B : ℝ :=
        (∫ t : ℝ, ‖f t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
          ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ with hB
    have h_two : ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) := by simp
    have h_base_nonneg :
        0 ≤ ∫ t : ℝ, ‖f t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume := by
      refine integral_nonneg ?_
      intro t
      have := sq_nonneg ‖f t‖
      simpa [h_two, pow_two] using this
    have hB_nonneg : 0 ≤ B := by
      have h_rpow_nonneg :
          0 ≤
              (∫ t : ℝ, ‖f t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
                ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ :=
        Real.rpow_nonneg h_base_nonneg _
      simpa [B, hB]
        using h_rpow_nonneg
    have h_toReal_ofReal :
        (eLpNorm f 2 volume).toReal
          = (ENNReal.ofReal B).toReal := by
      simpa [B, hB] using h₁
    have h_toReal : (eLpNorm f 2 volume).toReal = B := by
      simpa [ENNReal.toReal_ofReal, hB_nonneg] using h_toReal_ofReal
    have hB_simpl :
        B = (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
      simp [B, hB, h_two, one_div]
    have h_nonneg :
        0 ≤ ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume := by
      simpa [h_two, pow_two] using h_base_nonneg
    have h_sq :
        ((∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^ 2
          = ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume := by
      have := Real.mul_self_sqrt h_nonneg
      simpa [pow_two, Real.sqrt_eq_rpow, one_div]
        using this
    calc
     (eLpNorm f 2 volume).toReal ^ 2
          = ((∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^ 2 := by
              simp [h_toReal, hB_simpl]
      _ = ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume := h_sq

  -- Define the L²-elements associated to `φ n` and `g`.
  set Fn : ℕ → Lp ℂ (2 : ℝ≥0∞) volume :=
    fun n => (hφ_L2 n).toLp (φ n)
  set F : Lp ℂ (2 : ℝ≥0∞) volume := hg_L2.toLp g

  -- The norms of the differences go to zero.
  have h_mem_diff : ∀ n, MemLp (fun t : ℝ => g t - φ n t) 2 volume :=
    fun n => hg_L2.sub (hφ_L2 n)
  have h_diff_ne_top : ∀ n,
      eLpNorm (fun t : ℝ => g t - φ n t) 2 volume ≠ ∞ :=
    fun n => (h_mem_diff n).eLpNorm_ne_top
  have h_toReal_zero :
      Filter.Tendsto
        (fun n =>
          (eLpNorm (fun t : ℝ => g t - φ n t) 2 volume).toReal)
        Filter.atTop (𝓝 0) := by
    have := hφ_tendsto
    have hzero : (0 : ℝ≥0∞) ≠ ∞ := ENNReal.zero_ne_top
    exact
      ((ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
            (f := fun n =>
              eLpNorm (fun t : ℝ => g t - φ n t) 2 volume)
            h_diff_ne_top hzero).symm).1 this
  have h_norm_diff_zero :
      Filter.Tendsto (fun n => ‖Fn n - F‖) Filter.atTop (𝓝 0) := by
    have h_eq_norm : ∀ n,
        ‖Fn n - F‖
          = (eLpNorm (fun t : ℝ => g t - φ n t) 2 volume).toReal := by
      intro n
      have h_sub_eq :
          ((hφ_L2 n).sub hg_L2).toLp (fun t : ℝ => φ n t - g t)
            = Fn n - F := by
        simpa [Fn, F] using MemLp.toLp_sub (hφ_L2 n) hg_L2
      have h_symm :
          eLpNorm (fun t : ℝ => φ n t - g t) 2 volume
            = eLpNorm (fun t : ℝ => g t - φ n t) 2 volume := by
        simpa [Pi.sub_apply]
          using
            (eLpNorm_sub_comm (f := fun t : ℝ => φ n t)
              (g := fun t : ℝ => g t)
              (p := (2 : ℝ≥0∞)) (μ := volume))
      calc
        ‖Fn n - F‖
            = ‖((hφ_L2 n).sub hg_L2).toLp (fun t : ℝ => φ n t - g t)‖ := by
                simp [h_sub_eq]
        _ = (eLpNorm (fun t : ℝ => φ n t - g t) 2 volume).toReal := by
                simp
        _ = (eLpNorm (fun t : ℝ => g t - φ n t) 2 volume).toReal := by
                simp [h_symm]
    simpa [h_eq_norm] using h_toReal_zero

  -- Hence `Fn` converges to `F` in `L²`.
  have h_tendsto_Lp : Filter.Tendsto Fn Filter.atTop (𝓝 F) :=
    (tendsto_iff_norm_sub_tendsto_zero).2 h_norm_diff_zero

  -- Norms (and their squares) converge.
  have h_norm_tendsto : Filter.Tendsto (fun n => ‖Fn n‖) Filter.atTop (𝓝 ‖F‖) :=
    (continuous_norm.tendsto F).comp h_tendsto_Lp
  have h_norm_sq_tendsto :
      Filter.Tendsto (fun n => ‖Fn n‖ ^ 2) Filter.atTop (𝓝 (‖F‖ ^ 2)) :=
    (continuous_pow 2).tendsto (‖F‖) |>.comp h_norm_tendsto

  -- Rewrite the squared norms in terms of the desired integrals.
  have h_fn_sq : ∀ n,
      ‖Fn n‖ ^ 2 = ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume := by
    intro n
    have := h_sq_integral (hf := hφ_L2 n)
    have h_norm := Lp.norm_toLp (f := φ n) (hf := hφ_L2 n)
    simpa [Fn, pow_two] using this.trans (by simp [Fn, pow_two])
  have h_g_sq : ‖F‖ ^ 2 = ∫ t : ℝ, ‖g t‖ ^ 2 ∂volume := by
    have := h_sq_integral (hf := hg_L2)
    simpa [F, pow_two] using this

  -- Conclude by transporting the limit along these equalities.
  have h_limit := h_norm_sq_tendsto.congr'
      (Filter.Eventually.of_forall h_fn_sq)
  simpa [h_g_sq] using h_limit

/--
Placeholder: the Fourier transform of an `L¹ ∩ L²` function lies in `L²`.

Ultimately this should follow from the Plancherel theorem once the preceding
lemmas are established.
-/
lemma fourierIntegral_memLp_L1_L2
    {g : ℝ → ℂ} (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    MemLp (fun ξ : ℝ => fourierIntegral g ξ) 2 volume := by
  -- Strategy: Approximate g by Schwartz functions φ_n in L¹ ∩ L²
  -- For Schwartz functions, we know F[φ_n] ∈ L²
  -- Show that F[φ_n] is Cauchy in L², hence converges to some F_∞ ∈ L²
  -- That limit is F[g]

  -- For each n, approximate g by a Schwartz function within 1/n
  have h_pos : ∀ (n : ℕ), 0 < 1 / ((n : ℝ) + 1) := by
    intro n
    apply div_pos (by norm_num : (0 : ℝ) < 1)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  choose φ hφ_L1 hφ_L2 using fun (n : ℕ) =>
    exists_schwartz_L1_L2_close g hg_L1 hg_L2 (1 / ((n : ℝ) + 1)) (h_pos n)

  -- Each φ n is a Schwartz function, so its Fourier transform is in L²
  have hφ_fourier_L2 : ∀ n, MemLp (fun ξ => fourierIntegral (fun t => φ n t) ξ) 2 volume :=
    fun n => fourierIntegral_memLp_of_schwartz (φ n)

  -- The Fourier transforms F[φ n] form a Cauchy sequence in L²
  -- Key: φ_m - φ_n is also a Schwartz function, so we can apply Schwartz Plancherel

  -- Step 1: Show φ_n is Cauchy in L²
  have hφ_cauchy_L2 : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      eLpNorm (fun t => (φ m) t - (φ n) t) 2 volume < ENNReal.ofReal ε := by
    intro ε hε
    -- Choose N large enough that 2/(N+1) < ε
    have : ∃ N : ℕ, 2 / ((N : ℝ) + 1) < ε := by
      use (Nat.ceil (2 / ε) + 1)
      have h_ceil : 2 / ε ≤ Nat.ceil (2 / ε) := Nat.le_ceil (2 / ε)
      have h_lt : 2 / ε < (Nat.ceil (2 / ε) : ℝ) + 1 + 1 := by linarith
      calc 2 / (↑(Nat.ceil (2 / ε) + 1) + 1)
          < 2 / (2 / ε) := by
            apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2)
            · apply div_pos (by norm_num : (0 : ℝ) < 2) hε
            · simp [Nat.cast_add, add_comm, add_left_comm, add_assoc];
              simpa [add_comm, add_left_comm, add_assoc] using h_lt
        _ = ε := by field_simp
    obtain ⟨N, hN⟩ := this
    use N
    intro m n hm hn
    -- Triangle inequality: ‖φ_m - φ_n‖₂ ≤ ‖φ_m - g‖₂ + ‖g - φ_n‖₂
    calc eLpNorm (fun t => (φ m) t - (φ n) t) 2 volume
        ≤ eLpNorm (fun t => (φ m) t - g t) 2 volume
            + eLpNorm (fun t => g t - (φ n) t) 2 volume := by
          have h_eq : (fun t => (φ m) t - (φ n) t)
              = (fun t => ((φ m) t - g t) + (g t - (φ n) t)) := by
            ext t; ring
          rw [h_eq]
          apply eLpNorm_add_le
          · exact (SchwartzMap.integrable (φ m)).aestronglyMeasurable.sub hg_L1.aestronglyMeasurable
          · exact hg_L1.aestronglyMeasurable.sub (SchwartzMap.integrable (φ n)).aestronglyMeasurable
          · norm_num
      _ < ENNReal.ofReal (1 / ((m : ℝ) + 1)) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
          apply ENNReal.add_lt_add
          · -- ‖φ_m - g‖₂ = ‖g - φ_m‖₂ < 1/(m+1)
            have h_symm : eLpNorm (fun t => (φ m) t - g t) 2 volume
                = eLpNorm (fun t => g t - (φ m) t) 2 volume := by
              apply eLpNorm_sub_comm
            have h_bound := hφ_L2 m
            simpa [h_symm]
              using h_bound
          · have h_bound := hφ_L2 n
            simpa using h_bound
      _ = ENNReal.ofReal (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) := by
          have hm_nonneg : 0 ≤ 1 / ((m : ℝ) + 1) := by
            apply div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
            exact add_nonneg (Nat.cast_nonneg m) zero_le_one
          have hn_nonneg : 0 ≤ 1 / ((n : ℝ) + 1) := by
            apply div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
            exact add_nonneg (Nat.cast_nonneg n) zero_le_one
          exact (ENNReal.ofReal_add hm_nonneg hn_nonneg).symm
      _ < ENNReal.ofReal ε := by
          have h_sum_nonneg : 0 ≤ 1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
            apply add_nonneg
            · apply div_nonneg; norm_num; exact add_nonneg (Nat.cast_nonneg m) zero_le_one
            · apply div_nonneg; norm_num; exact add_nonneg (Nat.cast_nonneg n) zero_le_one
          rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_sum_nonneg]
          have hm' : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
            apply div_le_div_of_nonneg_left
            · norm_num
            · exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) zero_lt_one
            · have := hm
              exact add_le_add (by exact_mod_cast this) le_rfl
          have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
            apply div_le_div_of_nonneg_left
            · norm_num
            · exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) zero_lt_one
            · have := hn
              exact add_le_add (by exact_mod_cast this) le_rfl
          calc 1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)
              ≤ 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by linarith
            _ = 2 / ((N : ℝ) + 1) := by ring
            _ < ε := hN

  -- Step 2: Apply Schwartz Plancherel to φ_m - φ_n
  have hF_cauchy_L2 : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      eLpNorm (fun ξ => fourierIntegral (fun t => (φ m) t) ξ
                      - fourierIntegral (fun t => (φ n) t) ξ) 2 volume
        < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hφ_cauchy_L2 ε hε
    use N
    intro m n hm hn
    -- F[φ_m] - F[φ_n] = F[φ_m - φ_n] by linearity
    have h_diff_eq : (fun ξ => fourierIntegral (fun t => (φ m) t) ξ
                              - fourierIntegral (fun t => (φ n) t) ξ)
        = (fun ξ => fourierIntegral (fun t => (φ m) t - (φ n) t) ξ) := by
      ext ξ
      have h_sub := fourierIntegral_sub
        (f := fun t => (φ m) t) (g := fun t => (φ n) t)
        (hf := SchwartzMap.integrable (φ m))
        (hg := SchwartzMap.integrable (φ n))
        (ξ := ξ)
      simp at h_sub
      exact h_sub.symm

    rw [h_diff_eq]

    -- Now apply Schwartz Plancherel to (φ m - φ n)
    -- φ m - φ n is a SchwartzMap, so we can use fourier_plancherel
    have h_plancherel : ∫ t : ℝ, ‖(φ m - φ n) t‖ ^ 2 ∂volume
        = ∫ ξ : ℝ, ‖fourierIntegral (fun t => (φ m - φ n) t) ξ‖ ^ 2 ∂volume := by
      exact fourier_plancherel (φ m - φ n)

    -- Convert integral equality to eLpNorm equality
    have h_eLpNorm_eq : eLpNorm (fun ξ => fourierIntegral (fun t => (φ m - φ n) t) ξ) 2 volume
        = eLpNorm (fun t => (φ m - φ n) t) 2 volume := by
      -- This is exactly the `L²` isometry for Schwartz functions.
      simpa [sub_eq_add_neg] using fourierIntegral_eLpNorm_eq (φ := φ m - φ n)

    -- Use the Cauchy property of φ_n
    have h_eq1 : (fun ξ => fourierIntegral (fun t => (φ m) t - (φ n) t) ξ)
        = (fun ξ => fourierIntegral (fun t => (φ m - φ n) t) ξ) := by
      ext ξ
      rfl
    have h_eq2 : (fun t => (φ m - φ n) t) = (fun t => (φ m) t - (φ n) t) := by
      ext t
      rfl

    calc eLpNorm (fun ξ => fourierIntegral (fun t => (φ m) t - (φ n) t) ξ) 2 volume
        = eLpNorm (fun ξ => fourierIntegral (fun t => (φ m - φ n) t) ξ) 2 volume := by
          rw [h_eq1]
      _ = eLpNorm (fun t => (φ m - φ n) t) 2 volume := h_eLpNorm_eq
      _ = eLpNorm (fun t => (φ m) t - (φ n) t) 2 volume := by
          rw [h_eq2]
      _ < ENNReal.ofReal ε := hN m n hm hn

  -- Step 3: Use L² completeness - F[φ_n] converges to some F_∞ ∈ L²
  -- Step 4: F[φ_n](ξ) → F[g](ξ) pointwise (from L¹ convergence)
  -- Step 5: Therefore F_∞ = F[g] a.e., so F[g] ∈ L²

  -- Step 3: the sequence of Fourier transforms is Cauchy in `L²`, hence converges.
  classical
  set ψFun : ℕ → ℝ → ℂ := fun n ξ => fourierIntegral (fun t : ℝ => φ n t) ξ
  have hψ_mem : ∀ n, MemLp (ψFun n) 2 volume := fun n => hφ_fourier_L2 n
  set ψLp : ℕ → Lp ℂ (2 : ℝ≥0∞) volume := fun n => (hψ_mem n).toLp (ψFun n)

  -- `ψLp` is Cauchy thanks to the previous estimate.
  have hψ_cauchy : CauchySeq ψLp := by
    refine Metric.cauchySeq_iff.2 ?_
    intro ε hε
    obtain ⟨N, hN⟩ := hF_cauchy_L2 ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hψ_def :
        ψLp m - ψLp n
          = ((hψ_mem m).sub (hψ_mem n)).toLp
              (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) := by
      simpa [ψLp, ψFun]
        using (MemLp.toLp_sub (hψ_mem m) (hψ_mem n)).symm
    have h_norm_eq :
        ‖ψLp m - ψLp n‖
          = (eLpNorm (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume).toReal := by
      simp [hψ_def]
    have hψ_mn :
        eLpNorm (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume
          = eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume := by
      have hsub :
          (fun ξ : ℝ => ψFun m ξ - ψFun n ξ)
            = fun ξ : ℝ =>
                fourierIntegral (fun t : ℝ => φ m t - φ n t) ξ := by
        funext ξ
        simpa [ψFun, sub_eq_add_neg]
          using (fourierIntegral_sub
            (f := fun t : ℝ => φ m t)
            (g := fun t : ℝ => φ n t)
            (hf := SchwartzMap.integrable (φ m))
            (hg := SchwartzMap.integrable (φ n))
            (ξ := ξ)).symm
      simpa [ψFun, hsub]
        using fourierIntegral_eLpNorm_eq (φ := φ m - φ n)
    have h_norm_le : ‖ψLp m - ψLp n‖
        < ε := by
      have hε' := hN m n hm hn
      have hε_time :
          eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume
            < ENNReal.ofReal ε := by
        rw [← hψ_mn]
        exact hε'
      have h_real_lt :
          (eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume).toReal < ε :=
        by
          have hfin : eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume ≠ ∞ :=
            (SchwartzMap.memLp (φ m - φ n)
              (p := (2 : ℝ≥0∞)) (μ := volume)).eLpNorm_ne_top
          have hlt :
              (eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume).toReal
                < (ENNReal.ofReal ε).toReal :=
            (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hε_time
          have hε_nonneg : 0 ≤ ε := le_of_lt hε
          simpa [ENNReal.toReal_ofReal hε_nonneg] using hlt
      simpa [h_norm_eq, hψ_mn]
        using h_real_lt
    exact h_norm_le

  -- Completeness of `Lp` furnishes a limit element.
  obtain ⟨ψ_lim, hψ_lim⟩ := cauchySeq_tendsto_of_complete hψ_cauchy

  -- The approximating sequence converges pointwise to the Fourier transform of `g`.
  have hφ_tendsto_L1 :
      Filter.Tendsto (fun n => eLpNorm (fun t : ℝ => g t - φ n t) 1 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    classical
    set gseq : ℕ → ℝ≥0∞ :=
      fun n => eLpNorm (fun t : ℝ => g t - φ n t) 1 volume
    have h_ne_top : ∀ n, gseq n ≠ ∞ := by
      intro n
      have h_lt := hφ_L1 n
      have h_fin : gseq n < ∞ := lt_of_lt_of_le h_lt le_top
      exact ne_of_lt h_fin
    have h_nonneg : ∀ n, 0 ≤ (gseq n).toReal := by
      intro n; exact ENNReal.toReal_nonneg
    have h_upper : ∀ n, (gseq n).toReal ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : 0 ≤ 1 / ((n : ℝ) + 1) := by
        have : 0 < ((n : ℝ) + 1) := by
          exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
        exact div_nonneg zero_le_one this.le
      have h_le : gseq n ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
        (le_of_lt (hφ_L1 n))
      exact ENNReal.toReal_le_of_le_ofReal hpos h_le
    have h_tendsto_aux :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
    have h_tendsto_real :
        Filter.Tendsto (fun n : ℕ => (gseq n).toReal)
          Filter.atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_upper h_tendsto_aux
    have h_tendsto :
        Filter.Tendsto gseq Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      rw [ENNReal.tendsto_atTop_zero]
      intro ε hε_pos
      by_cases hε_top : ε = ∞
      · refine ⟨0, fun n _ => ?_⟩
        simp [gseq, hε_top]
      · have hε_finite : ε ≠ ∞ := hε_top
        have hε_lt_top : ε < ∞ := lt_of_le_of_ne le_top hε_finite
        have hε_toReal_pos : (0 : ℝ) < ε.toReal := by
          rw [ENNReal.toReal_pos_iff]
          exact ⟨hε_pos, hε_lt_top⟩
        have h_eventually :
            ∀ᶠ n in Filter.atTop, (gseq n).toReal < ε.toReal :=
          Filter.Tendsto.eventually_lt h_tendsto_real tendsto_const_nhds hε_toReal_pos
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
        refine ⟨N, fun n hn => ?_⟩
        have h_toReal_lt : (gseq n).toReal < ε.toReal := hN n hn
        have h_ne_top' : gseq n ≠ ∞ := h_ne_top n
        have h_lt : gseq n < ε :=
          (ENNReal.toReal_lt_toReal h_ne_top' hε_finite).mp h_toReal_lt
        exact le_of_lt h_lt
    simpa [gseq] using h_tendsto

  have hφ_tendsto_L2 :
      Filter.Tendsto (fun n => eLpNorm (fun t : ℝ => g t - φ n t) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    classical
    set gseq : ℕ → ℝ≥0∞ :=
      fun n => eLpNorm (fun t : ℝ => g t - φ n t) 2 volume
    have h_ne_top : ∀ n, gseq n ≠ ∞ := by
      intro n
      have h_lt := hφ_L2 n
      exact ne_of_lt (lt_of_lt_of_le h_lt le_top)
    have h_nonneg : ∀ n, 0 ≤ (gseq n).toReal := by
      intro _; exact ENNReal.toReal_nonneg
    have h_upper : ∀ n, (gseq n).toReal ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : 0 ≤ 1 / ((n : ℝ) + 1) := by
        have : 0 < (n : ℝ) + 1 :=
          add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
        exact div_nonneg zero_le_one this.le
      exact ENNReal.toReal_le_of_le_ofReal hpos (le_of_lt (hφ_L2 n))
    have h_tendsto_aux :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa [Nat.cast_add, Nat.cast_one]
        using tendsto_one_div_add_atTop_nhds_zero_nat
    have h_tendsto_real :
        Filter.Tendsto (fun n : ℕ => (gseq n).toReal)
          Filter.atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_upper h_tendsto_aux
    have h_tendsto :
        Filter.Tendsto gseq Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      rw [ENNReal.tendsto_atTop_zero]
      intro ε hε_pos
      by_cases hε_top : ε = ∞
      · refine ⟨0, fun _ _ => ?_⟩
        simp [gseq, hε_top]
      · have hε_finite : ε ≠ ∞ := hε_top
        have hε_lt_top : ε < ∞ := lt_of_le_of_ne le_top hε_finite
        have hε_toReal_pos : (0 : ℝ) < ε.toReal := by
          rw [ENNReal.toReal_pos_iff]
          exact ⟨hε_pos, hε_lt_top⟩
        have h_eventually :
            ∀ᶠ n in Filter.atTop, (gseq n).toReal < ε.toReal :=
          Filter.Tendsto.eventually_lt h_tendsto_real tendsto_const_nhds
            hε_toReal_pos
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
        refine ⟨N, fun n hn => ?_⟩
        have h_toReal_lt : (gseq n).toReal < ε.toReal := hN n hn
        have h_lt : gseq n < ε :=
          (ENNReal.toReal_lt_toReal (h_ne_top n) hε_finite).mp h_toReal_lt
        exact le_of_lt h_lt
    simpa [gseq] using h_tendsto

  have h_fourier_pointwise : ∀ ξ : ℝ,
      Filter.Tendsto (fun n => ψFun n ξ) Filter.atTop
        (𝓝 (fourierIntegral g ξ)) := by
    intro ξ
    exact fourierIntegral_tendsto_of_schwartz_approx hg_L1
      (fun n => (SchwartzMap.integrable (φ n))) hφ_tendsto_L1 ξ

  -- Define the square norms for Fatou's lemma.
  set F : ℕ → ℝ → ℝ≥0∞ := fun n ξ =>
    ENNReal.ofReal (‖ψFun n ξ‖ ^ 2)
  set F_infty : ℝ → ℝ≥0∞ :=
    fun ξ => ENNReal.ofReal (‖fourierIntegral g ξ‖ ^ 2)

  have h_meas : ∀ n, Measurable (F n) := by
    intro n
    have h_contReal : Continuous fun ξ : ℝ =>
        Real.fourierIntegral (fun t : ℝ => φ n t) ξ :=
      VectorFourier.fourierIntegral_continuous (V := ℝ) (W := ℝ)
        (μ := volume) (e := Real.fourierChar) (L := innerₗ ℝ)
        (f := fun t : ℝ => φ n t)
        Real.continuous_fourierChar
        (by
          simpa [innerₗ]
            using
              (continuous_inner : Continuous fun p : ℝ × ℝ => inner (𝕜 := ℝ) p.1 p.2))
        (SchwartzMap.integrable (φ n))
    have h_cont : Continuous (fun ξ : ℝ => ψFun n ξ) := by
      simpa [ψFun, fourierIntegral_eq_real]
        using h_contReal
    have h_meas_sq : Measurable fun ξ : ℝ => ‖ψFun n ξ‖ ^ 2 :=
      ((continuous_pow 2).comp h_cont.norm).measurable
    exact ENNReal.measurable_ofReal.comp h_meas_sq

  have h_F_tendsto : ∀ ξ,
      Filter.Tendsto (fun n => F n ξ) Filter.atTop (𝓝 (F_infty ξ)) := by
    intro ξ
    have h_outer :
        Filter.Tendsto (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))
          (𝓝 (fourierIntegral g ξ)) (𝓝 (F_infty ξ)) := by
      have h_cont : Continuous fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2) :=
        ENNReal.continuous_ofReal.comp
          ((continuous_pow 2).comp continuous_norm)
      simpa [F_infty]
        using h_cont.tendsto (fourierIntegral g ξ)
    exact h_outer.comp (h_fourier_pointwise ξ)

  have h_fun_eq :
      (fun ξ => Filter.liminf (fun n => F n ξ) Filter.atTop) = F_infty := by
    funext ξ
    have h := Filter.Tendsto.liminf_eq (h_F_tendsto ξ)
    simpa [F_infty] using h

  have h_liminf_le :
      ∫⁻ ξ, F_infty ξ ∂volume ≤
        Filter.liminf (fun n => ∫⁻ ξ, F n ξ ∂volume) Filter.atTop :=
    by
      have h :=
        MeasureTheory.lintegral_liminf_le (μ := volume) (f := F) h_meas
      simpa [h_fun_eq] using h

  -- Identify the `liminf` using Plancherel on the approximations.
  have h_integral_eq :
      ∀ n, ∫⁻ ξ, F n ξ ∂volume
          = ENNReal.ofReal (∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume) := by
    classical
    intro n
    have h_fourier_sq_integrable :
        Integrable (fun ξ : ℝ => ‖ψFun n ξ‖ ^ 2) volume := by
      have :=
        (memLp_two_iff_integrable_sq_norm
            (μ := volume)
            (f := fun ξ : ℝ => ψFun n ξ)
            (hψ_mem n).1).1 (hψ_mem n)
      simpa [pow_two] using this
    have h_plancherel :
        ∫ ξ : ℝ, ‖ψFun n ξ‖ ^ 2 ∂volume
          = ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume := by
      simpa [ψFun]
        using
          (fourier_plancherel (φ n)).symm
    have h_fourier_eq :
        ∫⁻ ξ : ℝ, ENNReal.ofReal (‖ψFun n ξ‖ ^ 2) ∂volume
          = ENNReal.ofReal (∫ ξ : ℝ, ‖ψFun n ξ‖ ^ 2 ∂volume) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          h_fourier_sq_integrable
          (ae_of_all _ fun _ => sq_nonneg _)).symm
    have h_integrand_id :
        ∫⁻ ξ : ℝ, F n ξ ∂volume
          = ∫⁻ ξ : ℝ, ENNReal.ofReal (‖ψFun n ξ‖ ^ 2) ∂volume := by
      refine lintegral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro ξ; simp [F, ψFun, pow_two]
    have h_target :
        ENNReal.ofReal (∫ ξ : ℝ, ‖ψFun n ξ‖ ^ 2 ∂volume)
          = ENNReal.ofReal (∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume) := by
      simpa [ψFun] using congrArg ENNReal.ofReal h_plancherel
    calc
      ∫⁻ ξ : ℝ, F n ξ ∂volume
          = ∫⁻ ξ : ℝ, ENNReal.ofReal (‖ψFun n ξ‖ ^ 2) ∂volume := h_integrand_id
      _ = ENNReal.ofReal (∫ ξ : ℝ, ‖ψFun n ξ‖ ^ 2 ∂volume) := h_fourier_eq
      _ = ENNReal.ofReal (∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume) := h_target

  -- Convergence of the time-side norms.
  have h_time_tendsto : Filter.Tendsto
      (fun n => ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume)) := by
    refine continuous_integral_norm_sq_of_L2_tendsto hg_L2 (fun n =>
      (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))) ?_
    exact hφ_tendsto_L2

  have h_freq_liminf :
      Filter.liminf (fun n => ∫⁻ ξ, F n ξ ∂volume)
          Filter.atTop
        = ENNReal.ofReal (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume) := by
    have h_ofReal :
        Filter.Tendsto (fun n => ENNReal.ofReal (∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume))
          Filter.atTop
          (𝓝 (ENNReal.ofReal (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp h_time_tendsto
    have h := Filter.Tendsto.liminf_eq h_ofReal
    simpa [h_integral_eq]

  have h_cont_fourier_real :
      Continuous fun ξ : ℝ => Real.fourierIntegral g ξ :=
    VectorFourier.fourierIntegral_continuous (V := ℝ) (W := ℝ)
      (μ := volume) (e := Real.fourierChar) (L := innerₗ ℝ)
      (f := g)
      Real.continuous_fourierChar
      (by
        simpa [innerₗ]
          using
            (continuous_inner : Continuous fun p : ℝ × ℝ => inner (𝕜 := ℝ) p.1 p.2))
      hg_L1
  have h_cont_fourier :
      Continuous fun ξ : ℝ => fourierIntegral g ξ := by
    simpa [fourierIntegral_eq_real] using h_cont_fourier_real
  have h_fourier_meas :
      AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral g ξ) volume := by
    simpa [fourierIntegral_eq_real] using h_cont_fourier.aestronglyMeasurable

  have h_integrable_sq :
      Integrable (fun ξ : ℝ => ‖fourierIntegral g ξ‖ ^ 2) volume := by
    have h_nonneg :
        0 ≤ᵐ[volume] fun ξ : ℝ => ‖fourierIntegral g ξ‖ ^ 2 :=
      Filter.Eventually.of_forall fun _ => sq_nonneg _
    have h_bound :
        ∫⁻ ξ : ℝ, ENNReal.ofReal (‖fourierIntegral g ξ‖ ^ 2) ∂volume
          ≤ ENNReal.ofReal (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume) := by
      simpa [F_infty, h_freq_liminf] using h_liminf_le
    have h_lintegral_lt_top :
        (∫⁻ ξ : ℝ, ENNReal.ofReal (‖fourierIntegral g ξ‖ ^ 2) ∂volume) < ∞ :=
      lt_of_le_of_lt h_bound ENNReal.ofReal_lt_top
    have h_sq_meas :
        AEStronglyMeasurable (fun ξ : ℝ => ‖fourierIntegral g ξ‖ ^ 2) volume :=
      ((continuous_pow 2).comp h_cont_fourier.norm).aestronglyMeasurable
    refine ⟨h_sq_meas, (hasFiniteIntegral_iff_ofReal h_nonneg).2 h_lintegral_lt_top⟩

  exact
    (memLp_two_iff_integrable_sq_norm
        (μ := volume)
        (f := fun ξ : ℝ => fourierIntegral g ξ)
        h_fourier_meas).2 h_integrable_sq

/-- Fourier-Plancherel theorem for L¹ ∩ L² functions.

This is the CORRECT version of the Plancherel identity for functions in both L¹ and L².
Unlike the invalid `fourierIntegral_l2_norm_INVALID`, this version has both:
- L¹ assumption (Integrable g): ensures fourierIntegral g is well-defined pointwise
- L² assumption (MemLp g 2): ensures the L² norms on both sides are finite

With both assumptions, we can prove:
1. fourierIntegral g ∈ L² (by Plancherel)
2. ∫ ‖g‖² = ∫ ‖fourierIntegral g‖²

The Fourier transform convention used is fourierKernel ξ t = exp(-2πiξt),
which gives Plancherel's identity without normalization constants. -/
lemma fourier_plancherel_L1_L2 (g : ℝ → ℂ)
    (hg_L1 : Integrable g)
    (hg_L2 : MemLp g 2 volume) :
    ∫ t : ℝ, ‖g t‖ ^ 2 ∂volume
      = ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume := by
  classical
  -- Strategy: Approximate `g` first by a smooth compactly supported function in both norms,
  -- then convert it into a Schwartz function using mollification.
  -- Step 1: choose a smooth compactly supported approximation of `g`.
  have h_half_pos : 0 < (1 : ℝ) := by norm_num
  obtain ⟨g₀, hg₀_compact, hg₀_smooth, hg₀_L1_error, hg₀_L2_error⟩ :=
    exists_smooth_compact_support_L1_L2_close g hg_L1 hg_L2 1 h_half_pos

  -- Step 2: upgrade the approximation to a Schwartz function.
  obtain ⟨φ₀, hφ₀_L1_error, hφ₀_L2_error⟩ :=
    smooth_compact_support_to_schwartz_L1_L2 hg₀_compact hg₀_smooth 1 h_half_pos

  -- Step 3: combine the two approximations using the triangle inequality in both norms.
  have hg₀_integrable : Integrable g₀ :=
    (hg₀_smooth.continuous.integrable_of_hasCompactSupport hg₀_compact)
  have hφ₀_integrable : Integrable (fun t : ℝ => φ₀ t) := schwartz_integrable φ₀
  have h_diff1_meas : AEStronglyMeasurable (fun t : ℝ => g t - g₀ t) volume :=
    (hg_L1.sub hg₀_integrable).aestronglyMeasurable
  have h_diff2_meas : AEStronglyMeasurable (fun t : ℝ => g₀ t - φ₀ t) volume :=
    (hg₀_integrable.sub hφ₀_integrable).aestronglyMeasurable
  have hφ₀_L1 :
      eLpNorm (fun t : ℝ => g t - φ₀ t) 1 volume
        ≤ eLpNorm (fun t : ℝ => g t - g₀ t) 1 volume
            + eLpNorm (fun t : ℝ => g₀ t - φ₀ t) 1 volume := by
    have h_add :=
      eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞))
        (f := fun t : ℝ => g t - g₀ t)
        (g := fun t : ℝ => g₀ t - φ₀ t)
        h_diff1_meas h_diff2_meas (le_rfl : (1 : ℝ≥0∞) ≤ (1 : ℝ≥0∞))
    have h_eq :
        (fun t : ℝ => g t - φ₀ t)
          = (fun t : ℝ => g t - g₀ t) + fun t : ℝ => g₀ t - φ₀ t := by
      funext t; simp [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simpa [h_eq]
      using h_add

  have hφ₀_L2 :
      eLpNorm (fun t : ℝ => g t - φ₀ t) 2 volume
        ≤ eLpNorm (fun t : ℝ => g t - g₀ t) 2 volume
            + eLpNorm (fun t : ℝ => g₀ t - φ₀ t) 2 volume := by
    have :=
      eLpNorm_triangle_diff g g₀ (fun t : ℝ => φ₀ t)
        hg_L2.aestronglyMeasurable
        (hg₀_smooth.continuous.aestronglyMeasurable)
        ((SchwartzMap.continuous φ₀).aestronglyMeasurable)
    simpa [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this

  -- Step 4: use the existing density lemma to produce a sequence of Schwartz functions
  -- with L¹ and L² convergence to `g`.
  have h_aux := exists_schwartz_L1_L2_approx g hg_L1 hg_L2
  obtain ⟨φ, hφ_L1, hφ_L2, hφ_tendsto_L1, hφ_tendsto_L2⟩ := h_aux

  -- Step 5: deduce the Plancherel identity for `g` using the approximating sequence `φ n`.
  -- L¹ convergence gives pointwise convergence of the Fourier integrals.
  have h_fourier_pointwise : ∀ ξ, Filter.Tendsto
      (fun n => fourierIntegral (fun t => φ n t) ξ)
      Filter.atTop (𝓝 (fourierIntegral g ξ)) := by
    intro ξ
    exact fourierIntegral_tendsto_of_schwartz_approx hg_L1 hφ_L1 hφ_tendsto_L1 ξ

  -- For each `φ n`, Plancherel holds (with unit constant) by `fourier_plancherel`.
  have h_schwartz_plancherel : ∀ n,
      ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume
        = ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume := by
    intro n
    -- Rephrase the classical Plancherel identity for Schwartz functions
    have h :=
      fourier_plancherel (φ n)
    -- `fourierIntegral` is the `ℂ`-valued Fourier transform with norm preservation.
    simpa using h

  -- L² convergence of `φ n` to `g`.
  have h_left_tendsto : Filter.Tendsto
      (fun n => ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume)) := by
    have h_sq_nonneg : ∀ t, ‖g t‖ ^ 2 = ‖g t‖ ^ 2 := by simp
    have h_sq_integrable : Integrable (fun t : ℝ => ‖g t‖ ^ 2) :=
      integrable_norm_sq_of_memLp_two hg_L2
    have h_sq_nonneg' : 0 ≤ᵐ[volume] fun t : ℝ => ‖g t‖ ^ 2 :=
      Filter.Eventually.of_forall fun _ => sq_nonneg _
    -- Convert L² convergence of `φ n` → `g` to convergence of squared norms using
    -- `FourierPlancherelL2Core`.
    have h :=
      continuous_integral_norm_sq_of_L2_tendsto
        (g := g) (φ := fun n => φ n) hg_L2 hφ_L2 hφ_tendsto_L2
    simpa using h

  -- L² convergence on the Fourier side using Plancherel and the pointwise limit.
  have h_right_tendsto : Filter.Tendsto
      (fun n => ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume)) := by
    -- Alternative approach: Use Schwartz Plancherel to rewrite the left side,
    -- then use the already-proven convergence h_left_tendsto

    -- For each n: ∫‖F[φ_n]‖² = ∫‖φ_n‖² (by Schwartz Plancherel)
    have h_eq : ∀ n,
        ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume
          = ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume :=
      fun n => (h_schwartz_plancherel n).symm

    -- Rewrite using Schwartz Plancherel: ∫‖F[φ_n]‖² = ∫‖φ_n‖²
    -- So the sequence ∫‖F[φ_n]‖² has the same limit as ∫‖φ_n‖², which is ∫‖g‖²
    have h_rewrite : Filter.Tendsto
        (fun n => ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume)
        Filter.atTop (𝓝 (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume)) := by
      apply Filter.Tendsto.congr' _ h_left_tendsto
      apply Filter.Eventually.of_forall
      intro n
      exact (h_eq n).symm

    -- Strategy: Show ∫‖F[φ_n]‖² → ∫‖F[g]‖² using a different approach
    -- We know: ∫‖F[φ_n]‖² → ∫‖g‖² (from h_rewrite)
    -- We want: ∫‖F[φ_n]‖² → ∫‖F[g]‖²
    -- Therefore: ∫‖g‖² = ∫‖F[g]‖² (by uniqueness of limits)

    -- Key insight: F[φ_n] is Cauchy in L² because φ_n is Cauchy in L²
    -- For Schwartz φ, ψ: ‖F[φ] - F[ψ]‖₂ = ‖F[φ - ψ]‖₂ = ‖φ - ψ‖₂

    -- Alternative approach: Use the fact that we already know where the limit should be
    -- We have h_rewrite: ∫‖F[φ_n]‖² → ∫‖g‖²
    -- We want to show: ∫‖F[φ_n]‖² → ∫‖F[g]‖²
    -- By uniqueness of limits, this would give us ∫‖g‖² = ∫‖F[g]‖²

    -- The key observation: We can use lower semicontinuity
    -- For any subsequence, we have convergence, so the limit is unique

    -- Key insight: We will show that the limit must be ∫‖F[g]‖²
    -- by using the structure of the overall proof.

    -- We have:
    -- 1. Pointwise convergence: F[φ_n](ξ) → F[g](ξ) for all ξ
    -- 2. Integral convergence: ∫‖F[φ_n]‖² → ∫‖g‖² (from h_rewrite)
    -- 3. F[g] ∈ L²

    have hFg_L2 : MemLp (fun ξ => fourierIntegral g ξ) 2 volume :=
      fourierIntegral_memLp_L1_L2 hg_L1 hg_L2

    -- Strategy: Show eLpNorm(F[φ_n] - F[g]) → 0 using Plancherel
    -- Then use continuous_integral_norm_sq_of_L2_tendsto

    have hF_tendsto_L2 : Filter.Tendsto
        (fun n => eLpNorm (fun ξ => fourierIntegral g ξ -
                                    fourierIntegral (fun t => φ n t) ξ) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      -- Strategy: Use the Cauchy property of F[φ_n] from Schwartz Plancherel,
      -- completeness of L², and pointwise convergence to identify the limit.

      -- Step 1: F[φ_n] is Cauchy in L² (using fourierIntegral_cauchySeq_of_schwartz_tendsto)
      have hF_cauchy : CauchySeq (fun n =>
          (fourierIntegral_memLp_L1_L2 (schwartz_integrable (φ n))
            (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))).toLp
          (fun ξ => fourierIntegral (fun t => φ n t) ξ)) := by
        exact fourierIntegral_cauchySeq_of_schwartz_tendsto hg_L2
          (fun n => schwartz_integrable (φ n))
          (fun n => SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
          hφ_tendsto_L2

      -- Step 2: By completeness of Lp, the Cauchy sequence converges to some limit
      classical
      obtain ⟨F_lim, hF_lim⟩ := cauchySeq_tendsto_of_complete hF_cauchy

      -- Step 3: Show that F_lim =ᵃᵉ F[g]
      -- We need to use:
      -- (a) L² convergence implies a.e. convergence along a subsequence
      --     (Mathlib: exists_seq_tendsto_ae)
      -- (b) We have pointwise convergence F[φ_n](ξ) → F[g](ξ) for all ξ
      -- (c) Uniqueness of a.e. limits

      -- The strategy would be:
      -- 1. Extract a.e. representation of F_lim using MemLp.coeFn_toLp
      -- 2. Use exists_seq_tendsto_ae to get a subsequence converging a.e.
      -- 3. Show this subsequence also converges pointwise to F[g]
      -- 4. Conclude F_lim =ᵃᵉ F[g] by uniqueness of a.e. limits

      -- Step 4: Convert L² convergence to the desired form
      -- From hF_lim: F[φ_n] → F_lim in Lp
      -- and F_lim =ᵃᵉ F[g]
      -- we can conclude: eLpNorm(F[g] - F[φ_n], 2) → 0

      -- The main technical difficulty is relating:
      -- - Lp elements (abstract equivalence classes)
      -- - Concrete functions (F[φ_n] and F[g])
      -- This requires careful use of MemLp.coeFn_toLp and a.e. equality

      classical
      -- Package the Fourier transforms of the approximants as L² functions.
      set ψFun : ℕ → ℝ → ℂ := fun n ξ => fourierIntegral (fun t => φ n t) ξ
      have hψ_mem : ∀ n, MemLp (ψFun n) 2 volume := fun n =>
        fourierIntegral_memLp_L1_L2 (schwartz_integrable (φ n))
          (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
      let ψLp : ℕ → Lp ℂ 2 volume := fun n => (hψ_mem n).toLp (ψFun n)
      have hψ_tendsto : Filter.Tendsto ψLp Filter.atTop (𝓝 F_lim) := by
        simpa [ψLp, ψFun, hψ_mem] using hF_lim

      -- Identify the limit candidate with the Fourier transform of `g`.
      let ψ_gLp : Lp ℂ 2 volume := hFg_L2.toLp (fun ξ => fourierIntegral g ξ)

      -- Relate the chosen `ψLp` with the version used in the weak-convergence lemmas.
      have hψLp_schwartz : ∀ n,
          ψLp n
            = (fourierIntegral_memLp_of_schwartz (φ n)).toLp
                (fun ξ : ℝ => fourierIntegral (fun t => φ n t) ξ) := by
        intro n
        refine (MemLp.toLp_eq_toLp_iff (hψ_mem n)
            (fourierIntegral_memLp_of_schwartz (φ n))).mpr ?_
        exact Filter.EventuallyEq.rfl

      -- Weak convergence of Fourier transforms against Schwartz test functions.
      have h_weak_base :=
        weak_limit_fourierIntegral_of_schwartz_tendsto
          (hf_L2 := hg_L2)
          (hφ_L1 := fun n => schwartz_integrable (φ n))
          (hφ_L2 :=
            fun n => SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
          hφ_tendsto_L2

      have h_weak_limit :
          ∀ ψ : SchwartzMap ℝ ℂ,
            Filter.Tendsto (fun n =>
                @inner ℂ (Lp ℂ 2 volume) _
                  ((fourierIntegral_memLp_of_schwartz ψ).toLp
                    (fun ξ => fourierIntegral (fun t => ψ t) ξ))
                  (ψLp n))
              Filter.atTop
              (𝓝 (∫ t : ℝ, g t * conj (ψ t) ∂volume)) := by
        intro ψ
        have h := h_weak_base ψ
        refine h.congr' ?_
        exact Filter.Eventually.of_forall fun n => by
          simp [ψLp, hψLp_schwartz n]

      -- Identify the weak limits on the frequency side with Fourier integrals.
      have h_freq_tendsto :=
        weak_convergence_fourierIntegral_of_schwartz_approx
          (φ := φ) (f := g) hg_L1 ψLp
          (fun n => hψLp_schwartz n) h_weak_limit

      -- Strong convergence of `ψLp` implies the same weak limits.
      have h_strong_tendsto :=
        strong_L2_implies_weak_convergence_schwartz ψLp F_lim hψ_tendsto

      -- Equate the two limiting values for every Schwartz test function.
      have h_integral_eq : ∀ ψ : SchwartzMap ℝ ℂ,
          ∫ x, F_lim x * (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume
              = ∫ x, fourierIntegral g x *
                  (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume := by
        intro ψ
        exact tendsto_nhds_unique (h_strong_tendsto ψ) (h_freq_tendsto ψ)

      -- Use the equality of pairings with Schwartz functions to identify the limit.
      have h_inner_zero : ∀ ψ : SchwartzMap ℝ ℂ,
          @inner ℂ (Lp ℂ 2 volume) _ (F_lim - ψ_gLp)
              ((SchwartzMap.memLp ψ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
                (fun x => ψ x)) = 0 := by
        intro ψ
        set ψTimeMem :=
          SchwartzMap.memLp ψ (p := (2 : ℝ≥0∞)) (μ := volume)
        set ψTimeLp : Lp ℂ 2 volume := ψTimeMem.toLp (fun x => ψ x)
        have hψ_coe : (fun x => ψTimeLp x) =ᵐ[volume] fun x => ψ x :=
          MemLp.coeFn_toLp ψTimeMem
        have hψ_star :
            (fun x => star (ψTimeLp x))
              =ᵐ[volume] fun x => (starRingEnd ℂ) (SchwartzMap.toFun ψ x) :=
          hψ_coe.mono <| by
            intro x hx
            simpa [SchwartzMap.toFun] using congrArg star hx
        have h_inner_F_lim :
            @inner ℂ (Lp ℂ 2 volume) _ ψTimeLp F_lim
              = ∫ x : ℝ, F_lim x *
                  (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume := by
          have h_def :=
            (MeasureTheory.L2.inner_def (𝕜 := ℂ) (μ := volume)
              (f := ψTimeLp) (g := F_lim))
          have h_mul :
              (fun x : ℝ =>
                  @inner ℂ ℂ _ (ψTimeLp x) (F_lim x))
                = fun x : ℝ => F_lim x * star (ψTimeLp x) := by
            funext x
            simp only [RCLike.inner_apply, starRingEnd_apply]
          have h_int := by
            simpa [h_mul, mul_comm] using h_def
          refine h_int.trans ?_
          refine integral_congr_ae ?_
          exact hψ_star.mono (by
            intro x hx
            simpa [SchwartzMap.toFun]
              using congrArg (fun y => F_lim x * y) hx)
        have hψg_coe :
            (fun x => ψ_gLp x) =ᵐ[volume] fun x => fourierIntegral g x :=
          MemLp.coeFn_toLp hFg_L2
        have h_inner_ψg :
            @inner ℂ (Lp ℂ 2 volume) _ ψTimeLp ψ_gLp
              = ∫ x : ℝ, (fourierIntegral g x) *
                  (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume := by
          have h_def :=
            (MeasureTheory.L2.inner_def (𝕜 := ℂ) (μ := volume)
              (f := ψTimeLp) (g := ψ_gLp))
          have h_mul :
              (fun x : ℝ =>
                  @inner ℂ ℂ _ (ψTimeLp x) (ψ_gLp x))
                = fun x : ℝ => ψ_gLp x * star (ψTimeLp x) := by
            funext x
            simp only [RCLike.inner_apply, starRingEnd_apply]
          have h_int := by
            simpa [h_mul, mul_comm] using h_def
          refine h_int.trans ?_
          refine integral_congr_ae ?_
          refine (Filter.EventuallyEq.mul hψg_coe hψ_star).mono ?_
          intro x hx
          simpa [SchwartzMap.toFun, mul_comm] using hx
        have h_inner_eq := by
          simpa [h_inner_F_lim, h_inner_ψg] using h_integral_eq ψ
        have h_int_diff :
            (∫ x : ℝ, F_lim x *
                  (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume) -
                ∫ x : ℝ, fourierIntegral g x *
                    (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume = 0 :=
          sub_eq_zero.mpr h_inner_eq
        have h_inner_diff :
            @inner ℂ (Lp ℂ 2 volume) _ ψTimeLp (F_lim - ψ_gLp) = 0 := by
          simpa [inner_sub_right, h_inner_F_lim, h_inner_ψg] using h_int_diff
        have h_inner_diff' :
            @inner ℂ (Lp ℂ 2 volume) _ (F_lim - ψ_gLp) ψTimeLp = 0 := by
          simpa [inner_conj_symm]
            using congrArg (starRingEnd ℂ) h_inner_diff
        exact h_inner_diff'

      have h_diff_zero : F_lim - ψ_gLp = 0 :=
        L2_eq_zero_of_inner_schwartz h_inner_zero
      have hF_lim_eq : F_lim = ψ_gLp := sub_eq_zero.mp h_diff_zero

      -- Convert strong convergence of `ψLp` to convergence towards `ψ_gLp`.
      have hψ_tendsto' : Filter.Tendsto ψLp Filter.atTop (𝓝 ψ_gLp) := by
        simpa [ψ_gLp, hF_lim_eq] using hψ_tendsto
      have h_dist_tendsto_zero : Filter.Tendsto
          (fun n => dist (ψLp n) ψ_gLp) Filter.atTop (𝓝 (0 : ℝ)) :=
        (tendsto_iff_dist_tendsto_zero).1 hψ_tendsto'

      -- Relate distances in L² to the `eLpNorm` of the pointwise difference.
      have h_dist_eq : ∀ n,
          dist (ψLp n) ψ_gLp
              = (eLpNorm
                    (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume).toReal :=
        by
          intro n
          have hcalc :
              ψLp n - ψ_gLp
                  = ((hψ_mem n).sub hFg_L2).toLp
                      (fun ξ : ℝ => ψFun n ξ - fourierIntegral g ξ) := by
            simpa [ψLp, ψ_gLp, ψFun]
              using (MemLp.toLp_sub (hψ_mem n) hFg_L2).symm
          have hnorm :=
            Lp.norm_toLp (μ := volume)
              (f := fun ξ : ℝ => ψFun n ξ - fourierIntegral g ξ)
              ((hψ_mem n).sub hFg_L2)
          have hswap :=
            eLpNorm_sub_comm (f := fun ξ : ℝ => ψFun n ξ)
              (g := fun ξ : ℝ => fourierIntegral g ξ)
              (p := (2 : ℝ≥0∞)) (μ := volume)
          calc
            dist (ψLp n) ψ_gLp
                = ‖ψLp n - ψ_gLp‖ := by simp [dist_eq_norm]
            _ = ‖((hψ_mem n).sub hFg_L2).toLp
                    (fun ξ : ℝ => ψFun n ξ - fourierIntegral g ξ)‖ := by
                  simp [ψLp, ψ_gLp, ψFun, hcalc]
            _ =
                (eLpNorm (fun ξ : ℝ => ψFun n ξ - fourierIntegral g ξ) 2 volume).toReal := by
                  simp [ψFun]
            _ =
                (eLpNorm (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume).toReal := by
                  simpa [ψFun] using congrArg ENNReal.toReal hswap

      have h_toReal_tendsto : Filter.Tendsto
          (fun n =>
            (eLpNorm (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume).toReal)
          Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa [h_dist_eq] using h_dist_tendsto_zero

      have h_noninf : ∀ n,
          eLpNorm (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume ≠ ∞ :=
        fun n => (hFg_L2.sub (hψ_mem n)).2.ne

      have h_ENNReal_tendsto : Filter.Tendsto
          (fun n => eLpNorm (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
        (ENNReal.tendsto_toReal_iff h_noninf (by simp)).mp
          (by simpa [ψFun] using h_toReal_tendsto)

      simpa [ψFun]
        using h_ENNReal_tendsto

    -- Now apply continuous_integral_norm_sq_of_L2_tendsto
    have hF_memLp : ∀ n, MemLp (fun ξ => fourierIntegral (fun t => φ n t) ξ) 2 volume := by
      intro n
      exact fourierIntegral_memLp_L1_L2 (schwartz_integrable (φ n))
        (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))

    exact continuous_integral_norm_sq_of_L2_tendsto hFg_L2 hF_memLp hF_tendsto_L2

  -- Combine the limits with the sequence-wise Plancherel identity.
  have h_scaled_tendsto : Filter.Tendsto
      (fun n => ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume)) := h_left_tendsto
  have h_scaled_tendsto' : Filter.Tendsto
      (fun n => ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume)) :=
    h_right_tendsto

  have h_eq_seq : ∀ n, ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume
      = ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume :=
    h_schwartz_plancherel

  have h_scaled_tendsto'' : Filter.Tendsto
      (fun n => ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n => (h_eq_seq n).symm)
      h_scaled_tendsto'

  exact tendsto_nhds_unique h_scaled_tendsto h_scaled_tendsto''

end Frourio
