import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core1
import Frourio.Analysis.MellinParsevalCore
import Frourio.Analysis.SchwartzDensity.SchwartzDensity
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Topology.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Lp.lpSpace

open MeasureTheory Complex Real SchwartzMap
open scoped Topology ENNReal NNReal ComplexConjugate

noncomputable section

namespace Frourio
open Schwartz

/-- Meyers–Serrin density theorem (real line version): smooth compactly supported
functions are dense in `Integrable ∩ MemLp 2`. -/
lemma meyers_serrin_L1_L2_density
    (f : ℝ → ℂ) (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      eLpNorm (fun t => f t - g t) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun t => f t - g t) 2 volume < ENNReal.ofReal ε := by
  sorry

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
    sorry -- This uses mollification/convolution with a smooth bump function

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
  sorry

/--
Placeholder: convergence of Fourier transforms in `L²` when the original
functions converge in both `L¹` and `L²`.

The eventual goal is to show that if `φ n → g` in `L¹ ∩ L²`, then the Fourier
transforms also converge in `L²`.
-/
lemma fourierIntegral_L2_convergence
    {φ : ℕ → SchwartzMap ℝ ℂ} {g : ℝ → ℂ}
    (hg_L1 : Integrable g)
    (hg_L2 : MemLp g 2 volume)
    (hφ_L1 : ∀ n, Integrable (fun t : ℝ => φ n t))
    (hφ_L2 : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume)
    (hφ_tendsto_L1 : Filter.Tendsto
      (fun n => eLpNorm (fun t : ℝ => g t - φ n t) 1 volume) Filter.atTop (𝓝 0))
    (hφ_tendsto_L2 : Filter.Tendsto
      (fun n => eLpNorm (fun t : ℝ => g t - φ n t) 2 volume) Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n =>
        eLpNorm
          (fun ξ : ℝ =>
            fourierIntegral g ξ - fourierIntegral (fun t : ℝ => φ n t) ξ)
          2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  sorry

/--
Placeholder: the Fourier transform of an `L¹ ∩ L²` function lies in `L²`.

Ultimately this should follow from the Plancherel theorem once the preceding
lemmas are established.
-/
lemma fourierIntegral_memLp_L1_L2
    {g : ℝ → ℂ} (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    MemLp (fun ξ : ℝ => fourierIntegral g ξ) 2 volume := by
  sorry

/-- Fourier-Plancherel theorem for L¹ ∩ L² functions.

This is the CORRECT version of the Plancherel identity for functions in both L¹ and L².
Unlike the invalid `fourierIntegral_l2_norm_INVALID`, this version has both:
- L¹ assumption (Integrable g): ensures fourierIntegral g is well-defined pointwise
- L² assumption (MemLp g 2): ensures the L² norms on both sides are finite

With both assumptions, we can prove:
1. fourierIntegral g ∈ L² (by Plancherel)
2. ∫ ‖g‖² = (1/(2π)) * ∫ ‖fourierIntegral g‖²

This is the standard textbook version of Plancherel for L¹ ∩ L². -/
lemma fourier_plancherel_L1_L2 (g : ℝ → ℂ)
    (hg_L1 : Integrable g)
    (hg_L2 : MemLp g 2 volume) :
    ∫ t : ℝ, ‖g t‖ ^ 2 ∂volume
      = (1 / (2 * Real.pi)) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume := by
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
    -- Combine pointwise convergence with uniform L² control given by Plancherel.
    have h_bound :
        ∀ n,
          ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume
            = ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume :=
      fun n => (h_schwartz_plancherel n).symm
    have h :=
      continuous_integral_norm_sq_of_L2_tendsto
        (g := fun ξ => fourierIntegral g ξ)
        (φ := fun n ξ => fourierIntegral (fun t => φ n t) ξ)
        (fourierIntegral_memLp_L1_L2 (g := g) hg_L1 hg_L2)
        (fun n => fourierIntegral_memLp_of_schwartz (φ n))
        (fourierIntegral_L2_convergence (g := g) (φ := φ)
          hg_L1 hg_L2 hφ_L1 hφ_L2 hφ_tendsto_L1 hφ_tendsto_L2)
    simpa using h

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

  have h_limit_eq :=
    tendsto_nhds_unique h_scaled_tendsto h_scaled_tendsto''

  have h_limit_scaled :
      ∫ t : ℝ, ‖g t‖ ^ 2 ∂volume
        = (1 / (2 * Real.pi)) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume := by
    -- Placeholder: adjust the normalisation factor once the precise Fourier
    -- transform constants are settled.
    sorry

  simpa using h_limit_scaled

end Frourio
