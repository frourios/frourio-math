import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core1
import Frourio.Analysis.HilbertSpace
import Frourio.Analysis.MellinParsevalCore
import Frourio.Analysis.SchwartzDensity.SchwartzDensity
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Lp.lpSpace

open MeasureTheory Complex Real SchwartzMap Metric
open scoped Topology ENNReal NNReal ComplexConjugate Pointwise Convolution

noncomputable section

namespace Frourio
open Schwartz

lemma exists_compact_support_L1_L2_close
    (f : ℝ → ℂ) (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      HasCompactSupport g ∧
      eLpNorm (fun t => f t - g t) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun t => f t - g t) 2 volume < ENNReal.ofReal ε := by
  classical
  have h_half_pos : 0 < ε / 2 := by linarith

  -- L¹ tail control for an integrable function
  have h_L1_tail : ∀ δ > 0, ∃ R > 0,
      ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ∂volume < δ := by
    simpa using integrable_tail_small hf_L1

  -- L² tail control coming from the `MemLp` hypothesis
  have h_L2_tail : ∀ δ > 0, ∃ R > 0,
      ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ^ 2 ∂volume < δ ^ 2 := by
    intro δ hδ
    have hδ_sq_pos : 0 < δ ^ 2 := by positivity
    obtain ⟨R, hR_pos, h_tail⟩ :=
      memLp_two_tail_norm_sq_small hf_L2 (δ ^ 2) hδ_sq_pos
    exact ⟨R, hR_pos, by simpa using h_tail⟩

  -- Choose radii controlling the L¹ and L² tails simultaneously
  obtain ⟨R₁, hR₁_pos, hR₁⟩ := h_L1_tail (ε / 2) h_half_pos
  obtain ⟨R₂, hR₂_pos, hR₂⟩ := h_L2_tail (ε / 2) h_half_pos
  set R := max R₁ R₂ with hR_def
  have hR_pos : 0 < R := by
    have h := lt_of_lt_of_le hR₁_pos (le_max_left R₁ R₂)
    simpa [hR_def] using h

  -- Truncate outside the ball of radius `R`
  set g := fun t : ℝ => if |t| ≤ R then f t else 0 with hg_def

  -- The truncated function has compact support
  have hg_compact : HasCompactSupport g := by
    refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ) R)
        (isCompact_closedBall _ _)
        ?_
    intro t ht
    have h_not_le : ¬ |t| ≤ R :=
      by
        simpa [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using ht
    simp [g, hg_def, h_not_le]

  -- L¹ error estimate between `f` and its truncation
  have hg_L1_half : eLpNorm (fun t => f t - g t) 1 volume
      < ENNReal.ofReal (ε / 2) := by
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
      · have h_not : t ∉ {t : ℝ | R ≤ |t|} := by
          simpa [Set.mem_setOf_eq] using hmem
        have h_nonneg : 0 ≤ ‖f t‖ := norm_nonneg _
        by_cases hmemR₁ : t ∈ {t : ℝ | R₁ ≤ |t|}
        · simp [Set.indicator_of_notMem, h_not, Set.indicator_of_mem, hmemR₁,
            h_nonneg]
        · simp [Set.indicator_of_notMem, h_not, Set.indicator_of_notMem,
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
    simpa [g, hg_def] using h_tail_bound

  -- L² error estimate between `f` and its truncation
  have hg_L2_half : eLpNorm (fun t => f t - g t) 2 volume
      < ENNReal.ofReal (ε / 2) := by
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
    simpa [g, hg_def]
      using h_tail_bound

  -- Upgrade the `ε / 2`-control to `ε`
  have h_half_le_ε : ENNReal.ofReal (ε / 2) ≤ ENNReal.ofReal ε := by
    have h_le : ε / 2 ≤ ε := by linarith
    exact ENNReal.ofReal_le_ofReal h_le

  refine ⟨g, hg_compact, ?_, ?_⟩
  · exact lt_of_lt_of_le hg_L1_half h_half_le_ε
  · exact lt_of_lt_of_le hg_L2_half h_half_le_ε

lemma smooth_compact_support_uniform_mollification
    (f : ℝ → ℂ) (hf_compact : HasCompactSupport f) (hf_cont : Continuous f) :
    ∀ ε > 0,
      ∃ g : ℝ → ℂ,
        HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
        (∀ t, ‖f t - g t‖ ≤ ε) := by
  intro ε hε
  classical
  -- Uniform continuity follows from compact support.
  have hf_uc : UniformContinuous f :=
    Continuous.uniformContinuous_of_hasCompactSupport hf_cont hf_compact

  -- Choose a radius capturing the support of `f`.
  obtain ⟨R, hR_pos, hR_subset⟩ :=
    HasCompactSupport.exists_radius_closedBall hf_compact
  have hR_nonneg : 0 ≤ R := le_of_lt hR_pos

  -- Smooth approximation in the sup norm via uniform continuity.
  obtain ⟨h, hh_smooth, hh_close⟩ := hf_uc.exists_contDiff_dist_le hε

  -- Bump function that is identically 1 on the support and cuts off outside.
  let bump : ContDiffBump (0 : ℝ) :=
    { rIn := R + 1
      rOut := R + 2
      rIn_pos := add_pos_of_nonneg_of_pos hR_nonneg zero_lt_one
      rIn_lt_rOut := by linarith }
  let χ : ℝ → ℝ := fun x => bump x
  have hχ_one : ∀ x ∈ Metric.closedBall (0 : ℝ) (R + 1), χ x = 1 := by
    intro x hx
    simpa [χ] using bump.one_of_mem_closedBall hx
  have hχ_zero_outside : ∀ x, R + 2 ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    have hx' : dist x (0 : ℝ) ≥ R + 2 := by
      simpa [Real.dist_eq, sub_eq_add_neg] using hx
    have := bump.zero_of_le_dist (x := x) (c := (0 : ℝ)) hx'
    simpa [χ, Real.dist_eq, sub_eq_add_neg] using this
  have hχ_nonneg : ∀ x, 0 ≤ χ x := by
    intro x; simpa [χ] using bump.nonneg' x
  have hχ_le_one : ∀ x, χ x ≤ 1 := by
    intro x; simpa [χ] using bump.le_one (c := (0 : ℝ)) (x := x)

  -- Define the smooth compactly supported approximation.
  let g : ℝ → ℂ := fun x => (χ x) • h x
  have hh_smooth' : ContDiff ℝ (⊤ : ℕ∞) h := by
    simpa using hh_smooth
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := by
    simpa [χ] using bump.contDiff (n := (⊤ : ℕ∞))
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    simpa [g, χ] using hχ_smooth.smul hh_smooth'

  -- Compact support of `g`.
  have hg_compact : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R + 2)) ?_
    intro x hx
    have hx_gt : R + 2 < ‖x‖ := by
      have hx' := Metric.mem_closedBall.not.1 hx
      simpa [Real.dist_eq, sub_eq_add_neg] using hx'
    have hx_ge : R + 2 ≤ ‖x‖ := le_of_lt hx_gt
    have hχ_zero := hχ_zero_outside x hx_ge
    simp [g, χ, hχ_zero]

  -- Pointwise error bound.
  have h_close_norm' : ∀ x, ‖h x - f x‖ ≤ ε := by
    intro x
    have hx := hh_close x
    have hx_lt : ‖h x - f x‖ < ε := by
      simpa [dist_eq_norm, sub_eq_add_neg] using hx
    exact (le_of_lt hx_lt)
  have h_close_norm : ∀ x, ‖f x - h x‖ ≤ ε := by
    intro x
    have hx := h_close_norm' x
    simpa [norm_sub_rev] using hx

  refine ⟨g, hg_compact, hg_smooth, ?_⟩
  intro x
  by_cases hx : ‖x‖ ≤ R + 1
  · have hx_ball : x ∈ Metric.closedBall (0 : ℝ) (R + 1) := by
      simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using hx
    have hχ_one' : χ x = 1 := hχ_one x hx_ball
    have hg_eq : g x = h x := by simp [g, χ, hχ_one']
    simpa [hg_eq, norm_sub_rev] using h_close_norm x
  · have hx_gt : R + 1 < ‖x‖ := lt_of_not_ge hx
    have hx_not_mem : x ∉ tsupport f := by
      intro hx_mem
      have hx_ball : x ∈ Metric.closedBall (0 : ℝ) R := hR_subset hx_mem
      have hx_le : ‖x‖ ≤ R :=
        by simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using hx_ball
      exact (not_le_of_gt hx_gt) (le_trans hx_le (by linarith))
    have hf_zero : f x = 0 :=
      by simpa using image_eq_zero_of_notMem_tsupport (f := f) hx_not_mem
    have hχ_abs_le : |χ x| ≤ (1 : ℝ) := by
      have hχ_le := hχ_le_one x
      have hχ_nn := hχ_nonneg x
      simpa [abs_of_nonneg hχ_nn] using hχ_le
    have hnorm_le : ‖h x‖ ≤ ε := by
      simpa [hf_zero] using h_close_norm' x
    have hg_le_h : ‖g x‖ ≤ ‖h x‖ := by
      have h_norm_eq : ‖g x‖ = |χ x| * ‖h x‖ := by
        -- Explicitly choose the scalar type to avoid typeclass search issues
        have := norm_smul (α := ℝ) (β := ℂ) (r := χ x) (x := h x)
        simp [g, χ, Real.norm_eq_abs]
      have : |χ x| * ‖h x‖ ≤ ‖h x‖ := by
        have h_norm_nonneg : 0 ≤ ‖h x‖ := norm_nonneg (h x)
        have := mul_le_of_le_one_right h_norm_nonneg hχ_abs_le
        simpa [mul_comm] using this
      simpa [h_norm_eq] using this
    have hg_le : ‖g x‖ ≤ ε := hg_le_h.trans hnorm_le
    have hg_diff : ‖f x - g x‖ = ‖g x‖ := by simp [hf_zero, g]
    exact hg_diff.le.trans hg_le

lemma integrable_comp_sub
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun y : ℝ => f (x - y)) := by
  classical
  -- Decompose the map `y ↦ x - y` as a composition of reflection and translation.
  let negMap : ℝ → ℝ := fun y => -y
  have h_neg :
      MeasurePreserving negMap (μa := volume) (μb := volume) :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  have h_trans :
      MeasurePreserving (translationMap (-x)) (μa := volume) (μb := volume) :=
    translation_measurePreserving (-x)
  have h_map :
      MeasurePreserving ((translationMap (-x)) ∘ negMap)
        (μa := volume) (μb := volume) :=
    h_trans.comp h_neg
  have h_meas : AEStronglyMeasurable f (volume : Measure ℝ) :=
    hf.aestronglyMeasurable
  have h_integrable :=
    (MeasurePreserving.integrable_comp h_map h_meas).mpr hf
  -- Simplify the composite map to obtain the desired statement.
  have h_comp :
      f ∘ translationMap (-x) ∘ negMap = fun y => f (x - y) := by
    funext y
    simp [Function.comp, negMap, translationMap, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]
  simpa [h_comp] using h_integrable

lemma HasCompactSupport.convolution_hasCompactSupport
    {f φ : ℝ → ℂ} (hφ : HasCompactSupport φ) (hf : HasCompactSupport f) :
    HasCompactSupport (fun x : ℝ => ∫ y, φ y * f (x - y) ∂volume) := by
  classical
  set F : ℝ → ℂ := fun x => ∫ y, φ y * f (x - y) ∂volume
  have hφ_compact : IsCompact (tsupport φ) := hφ
  have hf_compact : IsCompact (tsupport f) := hf
  have h_compact : IsCompact (tsupport f + tsupport φ) :=
    hf_compact.add hφ_compact
  refine HasCompactSupport.intro h_compact ?_
  intro x hx
  have hx' : x ∉ tsupport f + tsupport φ := hx
  have h_integrand_zero : (fun y : ℝ => φ y * f (x - y)) = fun _ => (0 : ℂ) := by
    funext y
    classical
    by_cases hy : y ∈ tsupport φ
    · have hx_minus : x - y ∉ tsupport f := by
        intro hx_minus
        have hx_mem : x ∈ tsupport f + tsupport φ :=
          ⟨x - y, hx_minus, y, hy, by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]⟩
        exact hx' hx_mem
      have : f (x - y) = 0 := image_eq_zero_of_notMem_tsupport hx_minus
      simp [hy, this]
    · have : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hy, this]
  have : F x = 0 := by
    simp [F, h_integrand_zero]
  simpa [F] using this

lemma smooth_compact_support_convolution_memLp
    (f : ℝ → ℂ) (hf_L1 : Integrable f) (hf_compact : HasCompactSupport f)
    (φ : ℝ → ℂ) (hφ_compact : HasCompactSupport φ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Integrable (fun x : ℝ => ∫ y, φ y * f (x - y) ∂volume) ∧
      MemLp (fun x : ℝ => ∫ y, φ y * f (x - y) ∂volume) 2 volume := by
  classical
  set F : ℝ → ℂ := fun x => ∫ y, φ y * f (x - y) ∂volume
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have h_loc_int : LocallyIntegrable f volume := hf_L1.locallyIntegrable
  have hF_eq_conv :
      F = fun x => (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] φ) x := by
    funext x
    have hconv :=
      convolution_mul_swap (μ := volume) (G := ℝ) (f := f) (g := φ) (x := x)
    simpa [F, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hconv.symm
  have hF_cont : Continuous F := by
    have :=
      hφ_compact.continuous_convolution_right
        (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume)
        h_loc_int hφ_cont
    simpa [hF_eq_conv] using this
  have hF_compact : HasCompactSupport F := by
    have :=
      HasCompactSupport.convolution_hasCompactSupport
        (f := f) (φ := φ) hφ_compact hf_compact
    simpa [F] using this
  have hF_integrable : Integrable F :=
    hF_cont.integrable_of_hasCompactSupport hF_compact
  have hF_memLp : MemLp F 2 volume :=
    hF_cont.memLp_of_hasCompactSupport hF_compact
  exact ⟨hF_integrable, hF_memLp⟩

lemma volume_tsupport_lt_top {f : ℝ → ℂ}
    (hf : HasCompactSupport f) : volume (tsupport f) < ∞ := by
  classical
  obtain ⟨R, _hR_pos, h_subset⟩ := HasCompactSupport.exists_radius_closedBall hf
  have h_ball_lt_top : volume (Metric.closedBall (0 : ℝ) R) < ∞ :=
    MeasureTheory.measure_closedBall_lt_top (x := (0 : ℝ)) (r := R)
  exact lt_of_le_of_lt (measure_mono h_subset) h_ball_lt_top

lemma eLpNorm_one_le_of_uniform_bound_on_support
    {f : ℝ → ℂ} {ε : ℝ} (h_bound : ∀ x ∈ tsupport f, ‖f x‖ ≤ ε) :
    eLpNorm f 1 volume ≤ ENNReal.ofReal ε * volume (tsupport f) := by
  classical
  -- Outside the support the function vanishes
  have hf_zero : ∀ x ∉ tsupport f, f x = 0 := by
    intro x hx
    simpa using image_eq_zero_of_notMem_tsupport (f := f) hx

  -- Rewrite the L¹ semi-norm as an integral over the support
  have h_indicator_eq :
      (fun x : ℝ => ENNReal.ofReal ‖f x‖)
        = Set.indicator (tsupport f) (fun x : ℝ => ENNReal.ofReal ‖f x‖) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · simp [Set.indicator_of_mem, hx]
    · have : f x = 0 := hf_zero x hx
      simp [Set.indicator_of_notMem, hx, this]

  have h_point_le :
      ∀ x : ℝ,
        Set.indicator (tsupport f) (fun x : ℝ => ENNReal.ofReal ‖f x‖) x
          ≤ Set.indicator (tsupport f) (fun _ : ℝ => ENNReal.ofReal ε) x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · have h_le := h_bound x hx
      have : ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal ε :=
        ENNReal.ofReal_le_ofReal h_le
      simpa [Set.indicator_of_mem, hx] using this
    · have : f x = 0 := hf_zero x hx
      simp [Set.indicator_of_notMem, hx, this]

  have hs_meas : MeasurableSet (tsupport f) :=
    (isClosed_tsupport (f := f)).measurableSet

  have h_eLp :
      eLpNorm f 1 volume
        = ∫⁻ x, Set.indicator (tsupport f)
            (fun x : ℝ => ENNReal.ofReal ‖f x‖) x ∂volume := by
    have h : eLpNorm f 1 volume
        = ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂volume := by
      simp [eLpNorm_one_eq_lintegral_enorm]
    have h_indicator_lintegral :
        ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂volume
          = ∫⁻ x, Set.indicator (tsupport f)
              (fun x : ℝ => ENNReal.ofReal ‖f x‖) x ∂volume := by
      have htemp :=
        congrArg (fun g : ℝ → ℝ≥0∞ => ∫⁻ x, g x ∂volume) h_indicator_eq
      simpa using htemp
    exact h.trans h_indicator_lintegral

  have h_lintegral_le :
      ∫⁻ x, Set.indicator (tsupport f)
          (fun x : ℝ => ENNReal.ofReal ‖f x‖) x ∂volume
        ≤ ∫⁻ x, Set.indicator (tsupport f)
            (fun _ : ℝ => ENNReal.ofReal ε) x ∂volume :=
    lintegral_mono h_point_le

  have h_indicator_const :
      ∫⁻ x, Set.indicator (tsupport f)
          (fun _ : ℝ => ENNReal.ofReal ε) x ∂volume
        = ENNReal.ofReal ε * volume (tsupport f) := by
    simp [MeasureTheory.lintegral_const, hs_meas, mul_comm, mul_left_comm, mul_assoc]

  calc
    eLpNorm f 1 volume
        = ∫⁻ x, Set.indicator (tsupport f)
            (fun x : ℝ => ENNReal.ofReal ‖f x‖) x ∂volume := h_eLp
    _ ≤ ∫⁻ x, Set.indicator (tsupport f)
            (fun _ : ℝ => ENNReal.ofReal ε) x ∂volume := h_lintegral_le
    _ = ENNReal.ofReal ε * volume (tsupport f) := h_indicator_const

-- Normalization integral of the raw mollifier kernel on the open interval.
lemma mollifier_kernel_integral (δ : ℝ) :
    ∫ x in Set.Ioo (-δ) δ, Real.exp (-1 / (δ ^ 2 - x ^ 2)) =
      ∫ x in Set.Ioc (-δ) δ, Real.exp (-1 / (δ ^ 2 - x ^ 2)) := by
  classical
  by_cases hδ_pos : 0 < δ
  · set f : ℝ → ℝ := fun x => Real.exp (-1 / (δ ^ 2 - x ^ 2)) with hf_def
    set S := Set.Ioo (-δ) δ with hS_def
    have hS_meas : MeasurableSet S := by
      simp [hS_def]

    have h_measurable : Measurable f := by
      have h₁ : Measurable fun x : ℝ => δ ^ 2 - x ^ 2 :=
        (measurable_const.sub ((continuous_id.pow 2).measurable))
      have h₂ : Measurable fun x : ℝ => 1 / (δ ^ 2 - x ^ 2) := by
        simpa [one_div] using h₁.inv
      have h₃ : Measurable fun x : ℝ => -(1 / (δ ^ 2 - x ^ 2)) := h₂.neg
      have h₄ : Measurable fun x : ℝ => Real.exp (-1 / (δ ^ 2 - x ^ 2)) := by
        simpa [one_div, div_eq_mul_inv] using
          (Real.continuous_exp.measurable.comp h₃)
      simpa [hf_def] using h₄

    have h_bound_all : ∀ x, x ∈ S → ‖f x‖ ≤ 1 := by
      intro x hx
      have hx_sq_lt : x ^ 2 < δ ^ 2 := by
        apply sq_lt_sq'
        · linarith [hx.1]
        · linarith [hx.2]
      have h_den_pos : 0 < δ ^ 2 - x ^ 2 := by linarith
      have h_le_zero : -1 / (δ ^ 2 - x ^ 2) ≤ 0 := by
        have h_inv_nonneg : 0 ≤ 1 / (δ ^ 2 - x ^ 2) := (one_div_pos.mpr h_den_pos).le
        simpa [div_eq_mul_inv] using neg_nonpos.mpr h_inv_nonneg
      have h_exp_le : Real.exp (-1 / (δ ^ 2 - x ^ 2)) ≤ 1 :=
        by simpa using Real.exp_le_exp.mpr h_le_zero
      have h_pos : 0 < Real.exp (-1 / (δ ^ 2 - x ^ 2)) :=
        Real.exp_pos _
      have h_norm_eq : ‖f x‖ = Real.exp (-1 / (δ ^ 2 - x ^ 2)) := by
        simp [hf_def, Real.norm_eq_abs, abs_of_pos h_pos]
      simpa [hf_def, h_norm_eq] using h_exp_le

    have h_bound_aemeas : ∀ᵐ x ∂volume, x ∈ S → ‖f x‖ ≤ 1 :=
      Filter.Eventually.of_forall h_bound_all
    have h_bound_restrict : ∀ᵐ x ∂volume.restrict S, ‖f x‖ ≤ 1 :=
      (ae_restrict_iff' hS_meas).2 h_bound_aemeas

    have hμfinite : volume S < ∞ := by
      simp [hS_def]

    have hf_aesm : AEStronglyMeasurable f (volume.restrict S) :=
      h_measurable.aestronglyMeasurable

    have hf_hasFinite : HasFiniteIntegral f (volume.restrict S) :=
      MeasureTheory.hasFiniteIntegral_restrict_of_bounded
        (μ := volume) (s := S) (C := (1 : ℝ)) hμfinite h_bound_restrict

    have hf_integrable_S : IntegrableOn f S volume :=
      ⟨hf_aesm, hf_hasFinite⟩

    have hf_aesm_single : AEStronglyMeasurable f (volume.restrict ({δ} : Set ℝ)) :=
      h_measurable.aestronglyMeasurable

    have h_bound_single_all : ∀ᵐ x ∂volume,
        x ∈ ({δ} : Set ℝ) → ‖f x‖ ≤ ‖f δ‖ :=
      Filter.Eventually.of_forall fun x hx => by
        have hx_eq : x = δ := by simpa [Set.mem_singleton_iff] using hx
        simp [hf_def, hx_eq]

    have h_bound_single : ∀ᵐ x ∂volume.restrict ({δ} : Set ℝ), ‖f x‖ ≤ ‖f δ‖ :=
      (ae_restrict_iff' (measurableSet_singleton δ)).2 h_bound_single_all

    have hμ_singleton : volume ({δ} : Set ℝ) < ∞ := by
      simp [measure_singleton δ]

    have hf_hasFinite_single : HasFiniteIntegral f (volume.restrict ({δ} : Set ℝ)) :=
      MeasureTheory.hasFiniteIntegral_restrict_of_bounded
        (μ := volume) (s := ({δ} : Set ℝ)) (C := ‖f δ‖) hμ_singleton h_bound_single

    have hf_integrable_single : IntegrableOn f ({δ} : Set ℝ) volume :=
      ⟨hf_aesm_single, hf_hasFinite_single⟩

    have h_decomp : Set.Ioc (-δ) δ = S ∪ ({δ} : Set ℝ) := by
      ext x; constructor
      · intro hx
        have hx₁ : -δ < x := hx.1
        have hx₂ : x ≤ δ := hx.2
        by_cases hxlt : x < δ
        · left; exact ⟨hx₁, hxlt⟩
        · right
          have hx_eq : x = δ := le_antisymm hx₂ (le_of_not_gt hxlt)
          simp [Set.mem_singleton_iff, hx_eq]
      · intro hx
        rcases hx with hx | hx
        · exact ⟨hx.1, hx.2.le⟩
        · obtain rfl : x = δ := by simpa [Set.mem_singleton_iff] using hx
          refine ⟨?_, le_rfl⟩
          · exact neg_lt_self hδ_pos

    have h_disj : Disjoint S ({δ} : Set ℝ) := by
      simp [Set.disjoint_singleton_right, hS_def, Set.mem_Ioo]

    have h_union :=
      setIntegral_union (μ := volume) (f := f) h_disj (measurableSet_singleton δ)
        hf_integrable_S hf_integrable_single

    have h_singleton_int : ∫ x in ({δ} : Set ℝ), f x ∂volume = 0 := by
      have hfδ : f δ = Real.exp 0 := by
        simp [hf_def]
      simp [hf_def, measure_singleton δ, hfδ]

    have h_eq : ∫ x in Set.Ioc (-δ) δ, f x ∂volume
        = ∫ x in S, f x ∂volume := by
      simpa [hS_def, h_decomp, h_singleton_int, hf_def, add_comm]
        using h_union

    have hIoo := h_eq.symm
    simpa [hf_def, hS_def] using hIoo
  · have hδ_nonpos : δ ≤ 0 := le_of_not_gt hδ_pos
    have h_le : δ ≤ -δ := by
      have : 0 ≤ -δ := neg_nonneg.mpr hδ_nonpos
      exact le_trans hδ_nonpos this
    have hIoo_empty : Set.Ioo (-δ) δ = (∅ : Set ℝ) := by
      ext x; constructor
      · intro hx
        have hx_gt : -δ < x := hx.1
        have hx_gt' : δ < x := lt_of_le_of_lt h_le hx_gt
        have hx_lt : x < δ := hx.2
        exact (lt_irrefl δ) (lt_trans hx_gt' hx_lt)
      · intro hx; simp at hx
    have hIoc_empty : Set.Ioc (-δ) δ = (∅ : Set ℝ) := by
      ext x; constructor
      · intro hx
        have hx_gt : -δ < x := hx.1
        have hx_gt' : δ < x := lt_of_le_of_lt h_le hx_gt
        have hx_le : x ≤ δ := hx.2
        exact (lt_irrefl δ) (lt_of_lt_of_le hx_gt' hx_le)
      · intro hx; simp at hx
    simp [hIoo_empty, hIoc_empty]

-- Basic bounds and measurability for the normalized mollifier kernel.
lemma mollifier_kernel_indicator_props
    (δ : ℝ) :
    (∀ᵐ x ∂volume.restrict (Set.Ioo (-δ) δ),
        ‖Real.exp (-1 / (δ ^ 2 - x ^ 2))‖ ≤ 1) ∧
      AEStronglyMeasurable
        (fun x => Real.exp (-1 / (δ ^ 2 - x ^ 2))) (volume.restrict (Set.Ioo (-δ) δ)) := by
  classical
  set S := Set.Ioo (-δ) δ with hS_def
  set f : ℝ → ℝ := fun x => Real.exp (-1 / (δ ^ 2 - x ^ 2)) with hf_def
  have hS_meas : MeasurableSet S := by
    simp [hS_def]

  -- Measurability of the kernel
  have h_measurable_denom :
      Measurable fun x : ℝ => δ ^ 2 - x ^ 2 :=
    (continuous_const.sub (continuous_id.pow 2)).measurable
  have h_measurable_inv :
      Measurable fun x : ℝ => (δ ^ 2 - x ^ 2)⁻¹ :=
    measurable_inv.comp h_measurable_denom
  have h_measurable :
      Measurable f := by
    have h_measurable_mul :
        Measurable fun x : ℝ => (-1) * (δ ^ 2 - x ^ 2)⁻¹ :=
      (measurable_const.mul h_measurable_inv)
    have h_measurable_arg :
        Measurable fun x : ℝ => -1 / (δ ^ 2 - x ^ 2) := by
      simpa [hf_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using h_measurable_mul
    simpa [hf_def]
      using (Real.continuous_exp.measurable.comp h_measurable_arg)

  -- Pointwise bound inside the open interval
  have h_bound_all : ∀ x ∈ S, ‖f x‖ ≤ 1 := by
    intro x hx
    have hx_pair : -δ < x ∧ x < δ := by
      simpa [hS_def, Set.mem_Ioo] using hx
    have h_pos₁ : 0 < δ - x := sub_pos.mpr hx_pair.2
    have h_pos₂ : 0 < δ + x := by linarith [hx_pair.1]
    have h_den_pos : 0 < δ ^ 2 - x ^ 2 := by
      have h_mul : 0 < (δ - x) * (δ + x) := mul_pos h_pos₁ h_pos₂
      have h_sq : δ ^ 2 - x ^ 2 = (δ - x) * (δ + x) := by ring
      simpa [h_sq]
        using h_mul
    have h_inv_nonneg : 0 ≤ 1 / (δ ^ 2 - x ^ 2) :=
      (one_div_pos.mpr h_den_pos).le
    have h_le_zero : -1 / (δ ^ 2 - x ^ 2) ≤ 0 :=
      by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using neg_nonpos.mpr h_inv_nonneg
    have h_exp_le : Real.exp (-1 / (δ ^ 2 - x ^ 2)) ≤ 1 := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr h_le_zero
    have h_pos : 0 < f x := by
      have := Real.exp_pos (-1 / (δ ^ 2 - x ^ 2))
      simpa [hf_def] using this
    have h_norm_eq : ‖f x‖ = f x := by
      simp [hf_def, Real.norm_eq_abs, abs_of_pos h_pos]
    simpa [hf_def, h_norm_eq] using h_exp_le

  -- Convert the pointwise bound into an a.e. statement on the restricted measure
  have h_bound_restrict :
      ∀ᵐ x ∂volume.restrict S, ‖f x‖ ≤ 1 := by
    have h_eventually :
        ∀ᵐ x ∂volume, x ∈ S → ‖f x‖ ≤ 1 :=
      Filter.Eventually.of_forall h_bound_all
    exact (ae_restrict_iff' hS_meas).2 h_eventually

  -- Measurability with respect to the restricted measure
  have h_aestrong :
      AEStronglyMeasurable f (volume.restrict S) :=
    h_measurable.aestronglyMeasurable

  exact ⟨h_bound_restrict, h_aestrong⟩

lemma integral_mollifier_indicator
    (δ : ℝ) :
    ∫ x, Set.indicator (Set.Ioo (-δ) δ)
        (fun x : ℝ => Real.exp (-1 / (δ ^ 2 - x ^ 2))) x ∂volume
      = ∫ x in Set.Ioo (-δ) δ, Real.exp (-1 / (δ ^ 2 - x ^ 2)) := by
  classical
  set S := Set.Ioo (-δ) δ with hS_def
  set g : ℝ → ℝ := fun x => Real.exp (-1 / (δ ^ 2 - x ^ 2)) with hg_def
  have hS_meas : MeasurableSet S := by
    simp [hS_def]
  simpa [hg_def, hS_def]
    using MeasureTheory.integral_indicator (μ := volume) (f := g) hS_meas

lemma mollifier_normalized_integral
    (δ : ℝ) (hδ_pos : 0 < δ) :
    HasCompactSupport (create_mollifier δ) ∧
      IntegrableOn (fun x : ℝ => create_mollifier δ x)
        (Set.Ioo (-δ) δ) volume := by
  classical
  set S := Set.Ioo (-δ) δ with hS_def
  set g : ℝ → ℝ := fun x => Real.exp (-1 / (δ ^ 2 - x ^ 2)) with hg_def
  set Z := ∫ t in S, g t with hZ_def

  have hZ_pos : 0 < Z := by
    simpa [hS_def, hg_def, hZ_def]
      using mollifier_normalization_positive δ hδ_pos
  have hZ_ne : (Z : ℝ) ≠ 0 := by exact ne_of_gt hZ_pos

  -- Compact support: the mollifier vanishes outside the closed ball of radius δ.
  have h_support : HasCompactSupport (create_mollifier δ) := by
    refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ) δ)
        (isCompact_closedBall _ _) ?_
    intro x hx
    have hx_dist : ¬dist x (0 : ℝ) ≤ δ := by
      simpa [Metric.mem_closedBall] using hx
    have hx_abs : ¬|x| < δ := by
      have hx_gt : δ < |x| :=
        by simpa [Real.dist_eq] using lt_of_not_ge hx_dist
      exact not_lt.mpr hx_gt.le
    simp [create_mollifier, hx_abs]

  -- Integrability on the open interval.
  have hS_meas : MeasurableSet S := by
    simp [hS_def]
  let C : ℝ := 1 / Z

  have h_meas_g : Measurable g := by
    have h₁ : Measurable fun x : ℝ => δ ^ 2 - x ^ 2 :=
      (continuous_const.sub ((continuous_id.pow 2))).measurable
    have h₂ : Measurable fun x : ℝ => (δ ^ 2 - x ^ 2)⁻¹ := h₁.inv
    have h₃ : Measurable fun x : ℝ => (-1 : ℝ) * (δ ^ 2 - x ^ 2)⁻¹ :=
      (measurable_const.mul h₂)
    have h₄ : Measurable fun x : ℝ => -1 / (δ ^ 2 - x ^ 2) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using h₃
    simpa [hg_def]
      using (Real.continuous_exp.measurable.comp h₄)

  have h_meas_cm : Measurable fun x : ℝ => create_mollifier δ x := by
    have h_set : MeasurableSet {x : ℝ | |x| < δ} :=
      ((_root_.continuous_abs : Continuous fun x => |x|).measurable)
        measurableSet_Iio
    have h_branch : Measurable fun x : ℝ => g x / Z := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using h_meas_g.mul_const (1 / Z)
    refine Measurable.ite h_set h_branch
        (measurable_const : Measurable fun _ : ℝ => (0 : ℝ))

  have h_bound_pointwise : ∀ x ∈ S, ‖create_mollifier δ x‖ ≤ C := by
    intro x hx
    have hx_pair : -δ < x ∧ x < δ := by
      simpa [hS_def, Set.mem_Ioo] using hx
    have hx_abs : |x| < δ := abs_lt.mpr hx_pair
    have hx_pos : 0 < g x := by
      have := Real.exp_pos (-1 / (δ ^ 2 - x ^ 2))
      simpa [hg_def] using this
    have hx_le_one : g x ≤ 1 := by
      have h_pos₁ : 0 < δ - x := sub_pos.mpr hx_pair.2
      have h_pos₂ : 0 < δ + x := by linarith [hx_pair.1, hδ_pos]
      have h_mul : 0 < (δ - x) * (δ + x) := mul_pos h_pos₁ h_pos₂
      have h_sq : (δ - x) * (δ + x) = δ ^ 2 - x ^ 2 := by ring
      have h_den_pos : 0 < δ ^ 2 - x ^ 2 := by simpa [h_sq] using h_mul
      have h_inv_nonneg : 0 ≤ 1 / (δ ^ 2 - x ^ 2) := (one_div_pos.mpr h_den_pos).le
      have h_exp_le : Real.exp (-1 / (δ ^ 2 - x ^ 2)) ≤ 1 := by
        simpa [Real.exp_zero] using Real.exp_le_exp.mpr
          (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
            using neg_nonpos.mpr h_inv_nonneg)
      simpa [hg_def] using h_exp_le
    have hx_div : g x / Z ≤ 1 / Z := by
      have := (mul_le_mul_of_nonneg_right hx_le_one (inv_nonneg.mpr hZ_pos.le))
      simpa [div_eq_mul_inv, C] using this
    have h_val : create_mollifier δ x = g x / Z := by
      simp [create_mollifier, hg_def, hZ_def, hS_def, hx_abs]
    have h_norm : ‖create_mollifier δ x‖ = g x / Z := by
      have h_abs : ‖create_mollifier δ x‖ = |g x| / |Z| := by
        simp [h_val, Real.norm_eq_abs, abs_div]
      have h_abs_g : |g x| = g x := abs_of_pos hx_pos
      have h_abs_Z : |Z| = Z := abs_of_pos hZ_pos
      simp [h_abs, h_abs_g, h_abs_Z, div_eq_mul_inv]
    simpa [h_norm, C] using hx_div

  have h_bound_restrict :
      ∀ᵐ x ∂volume.restrict S, ‖create_mollifier δ x‖ ≤ C :=
    (ae_restrict_iff' hS_meas).2 <| Filter.Eventually.of_forall h_bound_pointwise

  have hμfinite : volume S < ∞ := by
    simp [hS_def]

  have h_aemeas : AEStronglyMeasurable (fun x => create_mollifier δ x)
      (volume.restrict S) := h_meas_cm.aestronglyMeasurable

  have h_hasFinite : HasFiniteIntegral (fun x => create_mollifier δ x)
      (volume.restrict S) :=
    MeasureTheory.hasFiniteIntegral_restrict_of_bounded
      (μ := volume) (s := S) (C := C) hμfinite h_bound_restrict

  have h_integrable :
      IntegrableOn (fun x : ℝ => create_mollifier δ x) S volume :=
    ⟨h_aemeas, h_hasFinite⟩

  exact ⟨h_support, h_integrable⟩

lemma mollifier_self_convolution_eq_one (δ : ℝ) (hδ_pos : 0 < δ) :
    ∫ x, create_mollifier δ x ∂volume = 1 := by
  classical
  set S := Set.Ioo (-δ) δ with hS_def
  set g : ℝ → ℝ := fun x => Real.exp (-1 / (δ ^ 2 - x ^ 2)) with hg_def
  set Z := ∫ t in S, g t with hZ_def

  have hS_meas : MeasurableSet S := by
    simp [hS_def]
  have hZ_pos : 0 < Z := by
    simpa [hS_def, hg_def, hZ_def] using mollifier_normalization_positive δ hδ_pos
  have hZ_ne : (Z : ℝ) ≠ 0 := ne_of_gt hZ_pos

  -- Express the mollifier via an indicator on `S`.
  have h_abs_mem : ∀ {x}, |x| < δ → x ∈ S := by
    intro x hx
    have hx_pair := abs_lt.mp hx
    simpa [hS_def, Set.mem_Ioo] using hx_pair
  have h_indicator_eq :
      (fun x : ℝ => create_mollifier δ x)
        = Set.indicator S (fun x : ℝ => g x / Z) := by
    funext x
    by_cases hx_mem : x ∈ S
    · have hx_pair : -δ < x ∧ x < δ := by
        simpa [hS_def, Set.mem_Ioo] using hx_mem
      have hx_abs : |x| < δ := abs_lt.mpr hx_pair
      have hx_mem_Ioo : x ∈ Set.Ioo (-δ) δ := by
        simpa [hS_def] using hx_mem
      simp [create_mollifier, hS_def, hg_def, hZ_def, hx_abs, hx_mem,
        hx_mem_Ioo, Set.indicator_of_mem hx_mem_Ioo]
    · have hx_abs : ¬ |x| < δ := by
        intro h_abs
        have hx_pair := abs_lt.mp h_abs
        have hx_mem' : x ∈ S := by
          simpa [hS_def, Set.mem_Ioo] using hx_pair
        exact hx_mem hx_mem'
      have hx_not_mem_Ioo : x ∉ Set.Ioo (-δ) δ := by
        simpa [hS_def] using hx_mem
      simp [create_mollifier, hS_def, hg_def, hx_abs, hx_mem,
        hx_not_mem_Ioo, Set.indicator_of_notMem hx_not_mem_Ioo]

  -- Integrability of the kernel on `S`.
  obtain ⟨h_bound_kernel, h_meas_kernel⟩ :=
    mollifier_kernel_indicator_props δ
  have hμS_lt : volume S < ∞ := by
    simp [hS_def]
  have h_hasFinite_g : HasFiniteIntegral g (volume.restrict S) :=
    MeasureTheory.hasFiniteIntegral_restrict_of_bounded
      (μ := volume) (s := S) (C := (1 : ℝ)) hμS_lt h_bound_kernel
  have h_integrable_g : Integrable (fun x => g x) (volume.restrict S) :=
    ⟨h_meas_kernel, h_hasFinite_g⟩

  -- Evaluate the integral.
  calc
    ∫ x, create_mollifier δ x ∂volume
        = ∫ x, Set.indicator S (fun x : ℝ => g x / Z) x ∂volume := by
            simp [h_indicator_eq]
    _ = ∫ x in S, g x / Z ∂volume :=
            MeasureTheory.integral_indicator (μ := volume)
              (f := fun x : ℝ => g x / Z) hS_meas
    _ = ∫ x in S, (1 / Z) * g x ∂volume := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = (1 / Z) * ∫ x in S, g x ∂volume := by
            have h_restrict :
                ∫ x in S, (1 / Z) * g x ∂volume
                  = ∫ x, (1 / Z) * g x ∂(volume.restrict S) := rfl
            have h_restrict' :
                ∫ x in S, g x ∂volume
                  = ∫ x, g x ∂(volume.restrict S) := rfl
            simpa [h_restrict, h_restrict'] using
              (MeasureTheory.integral_const_mul (μ := volume.restrict S)
                (r := (1 / Z)) (f := fun x => g x))
    _ = (1 / Z) * Z := by
            simp [hZ_def]
    _ = 1 := by field_simp [hZ_ne]

lemma mollifier_support_subset_interval (δ : ℝ) :
    Function.support (create_mollifier δ) ⊆ Set.Icc (-δ) δ := by
  classical
  intro x hx
  have hx_ne : create_mollifier δ x ≠ 0 := by
    simpa [Function.mem_support] using hx
  have hx_abs_lt : |x| < δ := by
    by_contra hx_ge
    have : create_mollifier δ x = 0 := by
      simp [create_mollifier, hx_ge]
    exact hx_ne this
  have hx_pair := abs_lt.mp hx_abs_lt
  refine ⟨hx_pair.1.le, hx_pair.2.le⟩

lemma create_mollifier_nonneg (δ x : ℝ) :
    0 ≤ create_mollifier δ x := by
  classical
  by_cases hδ : 0 < δ
  · have hZ_pos :
      0 < ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ ^ 2 - t ^ 2)) := by
        simpa using mollifier_normalization_positive δ hδ
    have hZ_nonneg :
        0 ≤ ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ ^ 2 - t ^ 2)) := hZ_pos.le
    have h_exp_nonneg : 0 ≤ Real.exp (-1 / (δ ^ 2 - x ^ 2)) :=
      (Real.exp_pos _).le
    have h_div_nonneg :
        0 ≤ Real.exp (-1 / (δ ^ 2 - x ^ 2)) /
          ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ ^ 2 - t ^ 2)) :=
      div_nonneg h_exp_nonneg hZ_nonneg
    by_cases hx : |x| < δ
    · simpa [create_mollifier, hx] using h_div_nonneg
    · simp [create_mollifier, hx]
  · have hδ_nonpos : δ ≤ 0 := le_of_not_gt hδ
    have hx' : ¬ |x| < δ :=
      not_lt_of_ge <| (calc
        δ ≤ 0 := hδ_nonpos
        _ ≤ |x| := abs_nonneg x)
    simp [create_mollifier, hx']

lemma create_mollifier_le_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > 0, ∀ x, create_mollifier δ x ≤ C := by
  classical
  set S := Set.Ioo (-δ) δ with hS_def
  set kernel : ℝ → ℝ := fun x => Real.exp (-1 / (δ ^ 2 - x ^ 2)) with hKernel_def
  set Z := ∫ t in S, kernel t with hZ_def
  have hZ_pos : 0 < Z := by
    simpa [hS_def, hKernel_def, hZ_def]
      using mollifier_normalization_positive δ hδ
  refine ⟨1 / Z, one_div_pos.mpr hZ_pos, ?_⟩
  intro x
  by_cases hx : |x| < δ
  · have hx_pair := abs_lt.mp hx
    have h_mul_pos₁ : 0 < δ - x := sub_pos.mpr hx_pair.2
    have h_mul_pos₂ : 0 < δ + x := by
      have hx_gt : -δ < x := hx_pair.1
      have : 0 < δ + x := by linarith
      simpa [add_comm] using this
    have h_den_pos : 0 < δ ^ 2 - x ^ 2 := by
      have h_mul_pos : 0 < (δ - x) * (δ + x) := mul_pos h_mul_pos₁ h_mul_pos₂
      have h_poly : (δ - x) * (δ + x) = δ ^ 2 - x ^ 2 := by ring
      simpa [h_poly] using h_mul_pos
    have h_inv_nonneg : 0 ≤ 1 / (δ ^ 2 - x ^ 2) := (one_div_pos.mpr h_den_pos).le
    have h_exp_le : kernel x ≤ 1 := by
      have h_exp_le' := Real.exp_le_exp.mpr (by
        have h_inv' : 0 ≤ (δ ^ 2 - x ^ 2)⁻¹ := by
          have := h_inv_nonneg
          simpa [one_div] using this
        have h_neg_le : -(δ ^ 2 - x ^ 2)⁻¹ ≤ 0 := neg_nonpos.mpr h_inv'
        have h_target : -1 / (δ ^ 2 - x ^ 2) ≤ 0 := by
          simpa [one_div, div_eq_mul_inv] using h_neg_le
        simpa [hKernel_def] using h_target)
      simpa [Real.exp_zero, hKernel_def] using h_exp_le'
    have h_inv_nonneg' : 0 ≤ Z⁻¹ := inv_nonneg.mpr hZ_pos.le
    have h_kernel_le_div : kernel x / Z ≤ Z⁻¹ := by
      have := mul_le_mul_of_nonneg_right h_exp_le h_inv_nonneg'
      simpa [div_eq_mul_inv] using this
    have h_goal :
        Real.exp (-1 / (δ ^ 2 - x ^ 2)) /
            ∫ (t : ℝ) in Set.Ioo (-δ) δ, Real.exp (-1 / (δ ^ 2 - t ^ 2)) ≤
          (∫ (t : ℝ) in Set.Ioo (-δ) δ, Real.exp (-1 / (δ ^ 2 - t ^ 2)))⁻¹ := by
      simpa [hKernel_def, hZ_def, div_eq_mul_inv] using h_kernel_le_div
    simp [create_mollifier, hx, hKernel_def, hS_def, hZ_def, h_goal, one_div]
  · have hx_zero : create_mollifier δ x = 0 := by
      simp [create_mollifier, hx]
    have h_inv_nonneg : 0 ≤ 1 / Z := by
      have : 0 ≤ Z⁻¹ := inv_nonneg.mpr hZ_pos.le
      simpa [one_div] using this
    simpa [hx_zero] using h_inv_nonneg

lemma abs_create_mollifier (δ x : ℝ) :
    |create_mollifier δ x| = create_mollifier δ x :=
  abs_of_nonneg (create_mollifier_nonneg δ x)

lemma create_mollifier_measurable (δ : ℝ) :
    Measurable fun x : ℝ => create_mollifier δ x := by
  classical
  have h_set : MeasurableSet {x : ℝ | |x| < δ} :=
    ((_root_.continuous_abs : Continuous fun x : ℝ => |x|).measurable)
      measurableSet_Iio
  have h_inner : Measurable fun x : ℝ => Real.exp (-1 / (δ ^ 2 - x ^ 2)) := by
    have h₁ : Measurable fun x : ℝ => δ ^ 2 - x ^ 2 :=
      (continuous_const.sub ((continuous_id.pow 2))).measurable
    have h₂ : Measurable fun x : ℝ => (δ ^ 2 - x ^ 2)⁻¹ := h₁.inv
    have h₃ : Measurable fun x : ℝ => -1 / (δ ^ 2 - x ^ 2) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using (measurable_const.mul h₂ : Measurable fun x : ℝ => (-1 : ℝ) * (δ ^ 2 - x ^ 2)⁻¹)
    simpa using (Real.continuous_exp.measurable.comp h₃)
  refine Measurable.ite h_set ?_ (measurable_const : Measurable fun _ => (0 : ℝ))
  -- Inside the set we divide by the normalization constant; this is still measurable
  have h_const : Measurable fun _ : ℝ =>
      (∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ ^ 2 - t ^ 2)))⁻¹ := measurable_const
  simpa [create_mollifier, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using h_inner.mul h_const

lemma norm_complex_create_mollifier (δ x : ℝ) :
    ‖(create_mollifier δ x : ℂ)‖ = create_mollifier δ x := by
  have h := create_mollifier_nonneg δ x
  simp [Real.norm_eq_abs, Complex.norm_ofReal, abs_of_nonneg h]

-- Helper lemma: translation invariance of L^1 norm for complex functions
lemma eLpNorm_one_comp_sub (f : ℝ → ℂ) (y : ℝ)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun t => f (t - y)) 1 volume = eLpNorm f 1 volume :=
  eLpNorm_comp_sub f 1 y hf

/-- The L¹ norm of a convolution with a mollifier is at most the L¹ norm of the original function.
This follows from the fact that `create_mollifier δ` is a probability density (integrates to 1
and is nonnegative) when δ > 0. The proof uses Minkowski's integral inequality (or Young's
convolution inequality for L¹ * L¹ → L¹). -/
lemma mollifier_convolution_L1_contract
    (f : ℝ → ℂ) (δ : ℝ) (hf_meas : AEStronglyMeasurable f volume) (hf_L1 : Integrable f volume):
    eLpNorm (fun t : ℝ => ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 1 volume
      ≤ eLpNorm f 1 volume := by
  classical
  by_cases hδ : 0 < δ
  · -- Case: δ > 0, use the fact that create_mollifier integrates to 1
    have h_mollifier_nonneg : ∀ y, 0 ≤ create_mollifier δ y := create_mollifier_nonneg δ
    have h_mollifier_integral : ∫ y, create_mollifier δ y ∂volume = 1 :=
      mollifier_self_convolution_eq_one δ hδ
    -- Step 1: Define the convolution function
    set g := fun t : ℝ => ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume with hg_def
    -- Support control and global bound for the mollifier
    set S := Set.Icc (-δ) δ with hS_def
    have hS_meas : MeasurableSet S := by
      classical
      simp [hS_def]
    obtain ⟨C, hC_pos, hC_bound⟩ := create_mollifier_le_bound δ hδ
    have hC_nonneg : 0 ≤ C := hC_pos.le

    -- Step 2: We will show ‖g(t)‖ ≤ ∫ y, φ(y) * ‖f(t-y)‖ for each t
    have h_norm_bound : ∀ t, ‖g t‖ ≤ ∫ y, create_mollifier δ y * ‖f (t - y)‖ ∂volume := by
      intro t
      rw [hg_def]
      -- Apply norm_integral_le_integral_norm
      calc ‖∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume‖
          ≤ ∫ y, ‖(create_mollifier δ y : ℂ) * f (t - y)‖ ∂volume := by
            exact norm_integral_le_integral_norm _
        _ = ∫ y, ‖(create_mollifier δ y : ℂ)‖ * ‖f (t - y)‖ ∂volume := by
            congr 1; ext y; exact norm_mul _ _
        _ = ∫ y, create_mollifier δ y * ‖f (t - y)‖ ∂volume := by
            congr 1; ext y
            rw [norm_complex_create_mollifier]

    -- Step 3: Integrate the bound to get the L¹ norm inequality
    -- Use lintegral_mono with h_norm_bound
    calc eLpNorm g 1 volume
        = (∫⁻ t, ‖g t‖ₑ ∂volume) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
      _ = ∫⁻ t, ENNReal.ofReal ‖g t‖ ∂volume := by
          congr 1; ext t
          exact (ofReal_norm_eq_enorm _).symm
      _ ≤ ∫⁻ t, ENNReal.ofReal (∫ y, create_mollifier δ y * ‖f (t - y)‖ ∂volume) ∂volume := by
          apply lintegral_mono
          intro t
          exact ENNReal.ofReal_le_ofReal (h_norm_bound t)
      _ = ∫⁻ t, (∫⁻ y, ENNReal.ofReal (create_mollifier δ y * ‖f (t - y)‖) ∂volume) ∂volume := by
          congr 1; ext t
          -- Convert integral to lintegral for nonnegative function
          have h_nn : ∀ y, 0 ≤ create_mollifier δ y * ‖f (t - y)‖ := by
            intro y
            exact mul_nonneg (h_mollifier_nonneg y) (norm_nonneg _)
          have h_integrable_shift := integrable_comp_sub hf_L1 (x := t)
          have h_integrable_norm : Integrable (fun y => ‖f (t - y)‖) :=
            h_integrable_shift.norm
          have h_indicator_integrable :
              Integrable (fun y => Set.indicator S (fun y => ‖f (t - y)‖) y) :=
            h_integrable_norm.indicator (μ := volume) hS_meas
          have h_majorant_integrable : Integrable
              (fun y => C * Set.indicator S (fun y => ‖f (t - y)‖) y) :=
            h_indicator_integrable.const_mul C
          have h_bound_aemeas : ∀ᵐ y ∂volume,
              create_mollifier δ y * ‖f (t - y)‖
                ≤ C * Set.indicator S (fun y => ‖f (t - y)‖) y := by
            refine Filter.Eventually.of_forall ?_
            intro y
            classical
            by_cases hy : y ∈ S
            · have hy_indicator :
                  Set.indicator S (fun y => ‖f (t - y)‖) y = ‖f (t - y)‖ := by
                simp [Set.indicator_of_mem, hy]
              have h_abs : |create_mollifier δ y| = create_mollifier δ y :=
                abs_create_mollifier δ y
              have h_norm_nonneg : 0 ≤ ‖f (t - y)‖ := by
                exact norm_nonneg (f (t - y))
              have h_mul := mul_le_mul_of_nonneg_right (hC_bound y) h_norm_nonneg
              simpa [hy_indicator, h_abs] using h_mul
            · have h_support := mollifier_support_subset_interval δ
              have hy_support : y ∉ Function.support (create_mollifier δ) := by
                intro hy_supp
                have : y ∈ S := h_support hy_supp
                exact hy this
              have h_zero : create_mollifier δ y = 0 := by
                simpa [Function.mem_support] using hy_support
              have h_indicator_zero :
                  Set.indicator S (fun y => ‖f (t - y)‖) y = 0 := by
                simp [Set.indicator_of_notMem, hy]
              have h_abs : |create_mollifier δ y| = create_mollifier δ y :=
                abs_create_mollifier δ y
              simp [h_zero, h_indicator_zero, h_abs]
          have h_norm_eq : ∀ᵐ y ∂volume,
              ‖create_mollifier δ y * ‖f (t - y)‖‖
                = create_mollifier δ y * ‖f (t - y)‖ := by
            refine Filter.Eventually.of_forall ?_
            intro y
            have h_nonneg := h_nn y
            have h_norm :
                ‖(create_mollifier δ y * ‖f (t - y)‖ : ℝ)‖
                  = create_mollifier δ y * ‖f (t - y)‖ :=
              Real.norm_of_nonneg h_nonneg
            simpa using h_norm
          have h_bound_aemeas_norm : ∀ᵐ y ∂volume,
              ‖create_mollifier δ y * ‖f (t - y)‖‖
                ≤ C * Set.indicator S (fun y => ‖f (t - y)‖) y := by
            filter_upwards [h_bound_aemeas, h_norm_eq] with y hy_bound hy_norm
            simpa [hy_norm] using hy_bound
          have h_measurePres :=
            (translation_measurePreserving (-t)).comp
              (Measure.measurePreserving_neg (volume : Measure ℝ))
          have h_meas_shift₀ :
              AEStronglyMeasurable (fun y : ℝ => f (translationMap (-t) (-y))) volume := by
            simpa [Function.comp] using hf_meas.comp_measurePreserving h_measurePres
          have h_meas_shift' :
              AEStronglyMeasurable (fun y : ℝ => f (-y + t)) volume := by
            simpa [translationMap, sub_eq_add_neg, add_comm, add_left_comm] using h_meas_shift₀
          have h_meas_shift :
              AEStronglyMeasurable (fun y => f (t - y)) volume := by
            simpa [sub_eq_add_neg, add_comm] using h_meas_shift'
          have h_meas_norm :
              AEStronglyMeasurable (fun y => ‖f (t - y)‖) volume :=
            h_meas_shift.norm
          have h_meas_cm : AEStronglyMeasurable (fun y => create_mollifier δ y) volume :=
            (create_mollifier_measurable δ).aestronglyMeasurable
          have h_meas_integrand : AEStronglyMeasurable
              (fun y => create_mollifier δ y * ‖f (t - y)‖) volume :=
            h_meas_cm.mul h_meas_norm
          have h_integrable :
              Integrable (fun y => create_mollifier δ y * ‖f (t - y)‖) :=
            Integrable.mono' h_majorant_integrable h_meas_integrand h_bound_aemeas_norm
          have h_eq :=
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_integrable
              (Filter.Eventually.of_forall h_nn)
          simpa using h_eq
      _ = ∫⁻ y, ∫⁻ t, ENNReal.ofReal (create_mollifier δ y * ‖f (t - y)‖) ∂volume ∂volume := by
          have h_prod_meas : AEMeasurable
              (fun z : ℝ × ℝ =>
                ENNReal.ofReal (create_mollifier δ z.2 * ‖f (z.1 - z.2)‖))
              (volume.prod volume) := by
            have h_cm_meas : Measurable fun z : ℝ × ℝ => create_mollifier δ z.2 :=
              (create_mollifier_measurable δ).comp measurable_snd
            have hf_aemeas : AEMeasurable f volume := hf_meas.aemeasurable
            have h_sub_qmp : Measure.QuasiMeasurePreserving
                (fun z : ℝ × ℝ => z.1 - z.2) (volume.prod volume) volume := by
              have h_measPres : MeasurePreserving
                  (fun z : ℝ × ℝ => (z.1 - z.2, z.2))
                    (volume.prod volume) (volume.prod volume) :=
                measurePreserving_sub_prod (μ := volume) (ν := volume)
              have h_fst : Measure.QuasiMeasurePreserving
                  (fun z : ℝ × ℝ => z.1)
                  (volume.prod volume) volume := by
                refine ⟨measurable_fst, ?_⟩
                refine Measure.AbsolutelyContinuous.mk ?_
                intro s hs hs_zero
                have h_preimage :
                    (fun z : ℝ × ℝ => z.1) ⁻¹' s = s ×ˢ (Set.univ : Set ℝ) := by
                  ext z; simp [Set.mem_preimage]
                have h_measure :
                    (volume.prod volume) ((fun z : ℝ × ℝ => z.1) ⁻¹' s)
                      = volume s * volume (Set.univ : Set ℝ) := by
                  simp [h_preimage]
                simp [h_measure, hs_zero]
              simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm] using
                h_fst.comp h_measPres.quasiMeasurePreserving
            have hf_comp : AEMeasurable
                (fun z : ℝ × ℝ => f (z.1 - z.2)) (volume.prod volume) :=
              hf_aemeas.comp_quasiMeasurePreserving h_sub_qmp
            have hf_norm : AEMeasurable
                (fun z : ℝ × ℝ => ‖f (z.1 - z.2)‖) (volume.prod volume) :=
              hf_comp.norm
            have h_mul : AEMeasurable
                (fun z : ℝ × ℝ => create_mollifier δ z.2 * ‖f (z.1 - z.2)‖)
                (volume.prod volume) :=
              (h_cm_meas.aemeasurable).mul hf_norm
            exact h_mul.ennreal_ofReal
          simpa [Function.comp] using
            MeasureTheory.lintegral_lintegral_swap (μ := volume) (ν := volume) h_prod_meas
      _ = ∫⁻ y, ENNReal.ofReal (create_mollifier δ y) *
                (∫⁻ t, ENNReal.ofReal ‖f (t - y)‖ ∂volume) ∂volume := by
          congr 1; ext y
          have h_nonneg_cm : 0 ≤ create_mollifier δ y := h_mollifier_nonneg y
          have h_mul_eq :
              (fun t : ℝ => ENNReal.ofReal (create_mollifier δ y * ‖f (t - y)‖))
                = fun t : ℝ => ENNReal.ofReal (create_mollifier δ y) *
                    ENNReal.ofReal ‖f (t - y)‖ := by
            funext t
            have h :=
              ENNReal.ofReal_mul (p := create_mollifier δ y) (q := ‖f (t - y)‖)
                (show 0 ≤ create_mollifier δ y from h_nonneg_cm)
            simpa [mul_comm, mul_left_comm, mul_assoc] using h
          have h_aemeas_norm :
              AEMeasurable (fun t : ℝ => ENNReal.ofReal ‖f (t - y)‖) volume := by
            have h_shift :
                AEStronglyMeasurable (fun t : ℝ => f (t - y)) volume := by
              simpa [Function.comp, translationMap, sub_eq_add_neg]
                using hf_meas.comp_measurePreserving
                    (translation_measurePreserving y)
            have h_shift_norm :
                AEStronglyMeasurable (fun t : ℝ => ‖f (t - y)‖) volume :=
              h_shift.norm
            exact h_shift_norm.aemeasurable.ennreal_ofReal
          calc
            ∫⁻ t, ENNReal.ofReal (create_mollifier δ y * ‖f (t - y)‖) ∂volume
                = ∫⁻ t, (ENNReal.ofReal (create_mollifier δ y) *
                    ENNReal.ofReal ‖f (t - y)‖) ∂volume := by
                  simp [h_mul_eq]
            _ = ENNReal.ofReal (create_mollifier δ y) *
                (∫⁻ t, ENNReal.ofReal ‖f (t - y)‖ ∂volume) := by
              simpa using
                lintegral_const_mul'' (μ := volume)
                  (r := ENNReal.ofReal (create_mollifier δ y))
                  (f := fun t : ℝ => ENNReal.ofReal ‖f (t - y)‖)
                  h_aemeas_norm
      _ = ∫⁻ y, ENNReal.ofReal (create_mollifier δ y) *
                (∫⁻ t, ENNReal.ofReal ‖f t‖ ∂volume) ∂volume := by
          congr 1; ext y
          congr 1
          have h_map : Measure.map (translationMap y) (volume : Measure ℝ)
              = (volume : Measure ℝ) :=
            (translation_measurePreserving y).map_eq
          have h_integrand :
              AEMeasurable (fun t : ℝ => ENNReal.ofReal ‖f t‖)
                (Measure.map (translationMap y) (volume : Measure ℝ)) := by
            rw [h_map]
            exact (hf_meas.norm.aemeasurable).ennreal_ofReal
          have h_change :
              ∫⁻ t, ENNReal.ofReal ‖f (t - y)‖ ∂volume
                = ∫⁻ t, ENNReal.ofReal ‖f t‖ ∂volume := by
            calc
              ∫⁻ t, ENNReal.ofReal ‖f (t - y)‖ ∂volume
                  = ∫⁻ t, ENNReal.ofReal ‖f (translationMap y t)‖ ∂volume := by
                    simp [translationMap, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
              _ = ∫⁻ t, ENNReal.ofReal ‖f t‖ ∂Measure.map (translationMap y) volume := by
                    symm
                    exact lintegral_map' h_integrand
                      (aemeasurable_id'.comp_measurable
                        (measurable_translation y))
              _ = ∫⁻ t, ENNReal.ofReal ‖f t‖ ∂volume := by
                    simp [h_map]
          simpa using h_change
      _ = (∫⁻ t, ENNReal.ofReal ‖f t‖ ∂volume) *
          (∫⁻ y, ENNReal.ofReal (create_mollifier δ y) ∂volume) := by
          set A := ∫⁻ t, ENNReal.ofReal ‖f t‖ ∂volume
          have h_cm_aemeas : AEMeasurable (fun y : ℝ => ENNReal.ofReal (create_mollifier δ y))
              volume :=
            (create_mollifier_measurable δ).aemeasurable.ennreal_ofReal
          have h_mul :=
            lintegral_mul_const'' (μ := volume)
              (r := A)
              (f := fun y : ℝ => ENNReal.ofReal (create_mollifier δ y))
              h_cm_aemeas
          simpa [A, mul_comm] using h_mul
      _ = (∫⁻ t, ENNReal.ofReal ‖f t‖ ∂volume) * ENNReal.ofReal 1 := by
          congr 1
          classical
          have h_data := mollifier_normalized_integral δ hδ
          set S₀ := Set.Ioo (-δ) δ with hS₀_def
          have hS₀_meas : MeasurableSet S₀ := by
            simp [hS₀_def]
          have h_integrableOn := (mollifier_normalized_integral δ hδ).2
          have h_indicator_int :=
            (integrable_indicator_iff (μ := volume) (s := S₀)
                (f := fun y : ℝ => create_mollifier δ y) hS₀_meas).2 h_integrableOn
          have h_indicator_eq :
              (Set.indicator S₀ (fun y : ℝ => create_mollifier δ y))
                =ᵐ[volume] fun y : ℝ => create_mollifier δ y := by
            refine Filter.Eventually.of_forall ?_
            intro y
            classical
            by_cases hy : y ∈ S₀
            · simp [Set.indicator_of_mem hy]
            · have hy_abs : ¬ |y| < δ := by
                intro habs
                have hy_mem : y ∈ S₀ := by
                  have hy_pair := abs_lt.mp habs
                  simpa [hS₀_def, Set.mem_Ioo] using hy_pair
                exact hy hy_mem
              have hy_zero : create_mollifier δ y = 0 := by
                simp [create_mollifier, hy_abs]
              have hy_indicator :
                  Set.indicator S₀ (fun y : ℝ => create_mollifier δ y) y = 0 := by
                simp [Set.indicator_of_notMem hy]
              simp [hy_indicator, hy_zero]
          have h_integrable_cm : Integrable (fun y : ℝ => create_mollifier δ y) :=
            h_indicator_int.congr h_indicator_eq
          have h_ofReal :=
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_integrable_cm
              (Filter.Eventually.of_forall (fun y => h_mollifier_nonneg y))
          simpa [h_mollifier_integral] using h_ofReal.symm
      _ = (∫⁻ t, ENNReal.ofReal ‖f t‖ ∂volume) * 1 := by
          rw [ENNReal.ofReal_one]
      _ = ∫⁻ t, ENNReal.ofReal ‖f t‖ ∂volume := by
          rw [mul_one]
      _ = ∫⁻ t, ‖f t‖ₑ ∂volume := by
          congr 1; ext t
          exact ofReal_norm_eq_enorm _
      _ = eLpNorm f 1 volume := by
          rw [eLpNorm_one_eq_lintegral_enorm]
  · -- Case: δ ≤ 0, create_mollifier δ = 0 everywhere
    have h_zero : ∀ x, create_mollifier δ x = 0 := by
      intro x
      simp only [create_mollifier]
      have : ¬ (|x| < δ) := by
        by_contra h
        have : 0 ≤ |x| := abs_nonneg x
        linarith
      simp [this]
    simp only [h_zero, Complex.ofReal_zero, zero_mul, integral_zero]
    have : eLpNorm (fun _ : ℝ => (0 : ℂ)) 1 volume = 0 := eLpNorm_zero
    rw [this]
    exact zero_le _

end Frourio
