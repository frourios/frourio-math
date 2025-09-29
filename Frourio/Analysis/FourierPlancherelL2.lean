import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.MellinParsevalCore
import Frourio.Analysis.SchwartzDensity.SchwartzDensity
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Topology.Basic
import Mathlib.Data.ENNReal.Basic

/-!
# Fourier–Plancherel in `L²`

This file sets up the statements needed to extend the explicit Fourier integral
to an isometry on `L²(ℝ)`.  The key intermediate results (still left as goals)
are:

* the Fourier integral of an `L¹ ∩ L²` function belongs to `L²`;
* the Plancherel identity relating the `L²` norms on the time and frequency
  sides with the `1 / (2π)` normalisation used in
  `Frourio.Analysis.FourierPlancherel`.
-/

open MeasureTheory Complex Real SchwartzMap
open scoped Topology ENNReal ComplexConjugate

noncomputable section

namespace Frourio
open Schwartz

instance fact_one_le_two_ennreal : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
instance volume_hasTemperateGrowth :
    (volume : Measure ℝ).HasTemperateGrowth := by infer_instance

section Auxiliary

lemma smooth_compactly_supported_dense_L2 (f_L2 : ℝ → ℂ)
    (hf : MemLp f_L2 2 volume) (ε : ℝ) (hε_pos : ε > 0) :
    ∃ g : ℝ → ℂ, HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
        eLpNorm (f_L2 - g) 2 volume < ENNReal.ofReal ε := by
  classical
  -- Step 1: approximate by a continuous compactly supported function.
  have hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hε_half_pos : 0 < ε / 2 := half_pos hε_pos
  have hε_half_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hε_half_pos))
  obtain ⟨g₀, hg₀_support, hg₀_close_le, hg₀_continuous, hg₀_memLp⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (μ := volume) (p := (2 : ℝ≥0∞)) hp
      (ε := ENNReal.ofReal (ε / 2)) hε_half_ne
  have hg₀_meas : AEStronglyMeasurable g₀ volume := hg₀_memLp.aestronglyMeasurable

  -- Enclose the support of g₀ in a convenient closed ball.
  obtain ⟨R, hR_pos, hR_subset⟩ :=
    HasCompactSupport.exists_radius_closedBall hg₀_support
  have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
  let S : Set ℝ := Metric.closedBall (0 : ℝ) (R + 2)
  have hS_meas : MeasurableSet S := measurableSet_closedBall
  have hS_lt_top : volume S < ∞ := by simp [S]
  set μS : ℝ := (volume S).toReal with hμS_def
  have hμS_nonneg : 0 ≤ μS := by simp [μS]
  let M : ℝ := Real.sqrt μS
  have hM_nonneg : 0 ≤ M := Real.sqrt_nonneg _
  have hM_plus_pos : 0 < M + 1 := add_pos_of_nonneg_of_pos hM_nonneg zero_lt_one

  -- Choose the target uniform approximation tolerance δ.
  have hdenom_pos : 0 < 4 * (M + 1) := mul_pos (by norm_num) hM_plus_pos
  have hδ_pos : 0 < ε / (4 * (M + 1)) := by
    exact div_pos hε_pos hdenom_pos
  set δ : ℝ := ε / (4 * (M + 1)) with hδ_def
  have hδ_pos' : 0 < δ := by simpa [δ] using hδ_pos
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos'

  -- Uniformly approximate by a smooth function.
  have hg₀_uc : UniformContinuous g₀ :=
    Continuous.uniformContinuous_of_hasCompactSupport hg₀_continuous hg₀_support
  obtain ⟨h, hh_smooth, hh_close⟩ := hg₀_uc.exists_contDiff_dist_le hδ_pos'

  -- Build a smooth bump function used to cut off the approximation.
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
    have := bump.zero_of_le_dist (x := x) (c := (0 : ℝ))
      (by simpa [Real.dist_eq, sub_eq_add_neg] using hx')
    simpa [χ, Real.dist_eq, sub_eq_add_neg] using this
  have hχ_nonneg : ∀ x, 0 ≤ χ x := by
    intro x; simpa [χ] using bump.nonneg' x
  have hχ_le_one : ∀ x, χ x ≤ 1 := by
    intro x; simpa [χ] using bump.le_one (c := (0 : ℝ)) (x := x)

  -- Define the smooth compactly supported approximation `g`.
  let g : ℝ → ℂ := fun x => (χ x) • h x
  have hh_smooth' : ContDiff ℝ (⊤ : ℕ∞) h := by
    simpa using hh_smooth
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := by
    simpa [χ] using (bump.contDiff (n := (⊤ : ℕ∞)))
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    simpa [g, χ] using hχ_smooth.smul hh_smooth'
  have hg_continuous : Continuous g := hg_smooth.continuous
  have hg_compact : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R + 2)) ?_
    intro x hx
    have hx_gt : R + 2 < ‖x‖ := by
      have := Metric.mem_closedBall.not.1 hx
      simpa [S, Real.dist_eq, sub_eq_add_neg] using this
    have hx_ge : R + 2 ≤ ‖x‖ := le_of_lt hx_gt
    have hχ_zero' := hχ_zero_outside x hx_ge
    simp [g, χ, hχ_zero']

  -- Auxiliary facts about the original approximation g₀.
  have hg₀_zero_outside : ∀ x, R < ‖x‖ → g₀ x = 0 := by
    intro x hx
    have hx_not : x ∉ tsupport g₀ := by
      intro hx_mem
      have hx_ball : x ∈ Metric.closedBall (0 : ℝ) R := hR_subset hx_mem
      have hx_le : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using hx_ball
      exact (not_le_of_gt hx) hx_le
    simpa using image_eq_zero_of_notMem_tsupport (f := g₀) hx_not

  -- Pointwise control of the difference `g₀ - g`.
  have h_pointwise_bound : ∀ x, ‖g₀ x - g x‖ ≤ δ := by
    intro x
    have hclose := hh_close x
    have hclose_le : ‖h x - g₀ x‖ ≤ δ :=
      le_of_lt (by simpa [dist_eq_norm, sub_eq_add_neg] using hclose)
    by_cases hx : ‖x‖ ≤ R + 1
    · have hx_ball : x ∈ Metric.closedBall (0 : ℝ) (R + 1) :=
        by simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using hx
      have hχ_one' : χ x = 1 := hχ_one x hx_ball
      have : g x = h x := by simp [g, χ, hχ_one']
      simpa [this, norm_sub_rev] using hclose_le
    · have hx_gt : R + 1 < ‖x‖ := lt_of_not_ge hx
      have hx_gt' : R < ‖x‖ := by
        have hR_lt : R < R + 1 := by linarith
        exact lt_trans hR_lt hx_gt
      have hg₀_zero := hg₀_zero_outside x hx_gt'
      have hχ_abs_le : ‖χ x‖ ≤ 1 := by
        have hχ_nn := hχ_nonneg x
        have hχ_le := hχ_le_one x
        have : ‖χ x‖ = χ x := by
          have := abs_of_nonneg hχ_nn
          simpa [Real.norm_eq_abs] using this
        simpa [this] using hχ_le
      have hnorm_h : ‖h x‖ ≤ δ := by
        simpa [hg₀_zero, norm_sub_rev] using hclose_le
      have hdiff_eq : ‖g₀ x - g x‖ = ‖χ x‖ * ‖h x‖ := by
        simp [g, χ, hg₀_zero]
      have hmul_le' : ‖χ x‖ * ‖h x‖ ≤ ‖h x‖ := by
        have hnn : 0 ≤ ‖h x‖ := norm_nonneg _
        have := mul_le_of_le_one_right hnn hχ_abs_le
        simpa [mul_comm] using this
      have hmul_le : ‖χ x‖ * ‖h x‖ ≤ δ :=
        hmul_le'.trans hnorm_h
      exact (by simpa [hdiff_eq] using hmul_le)

  -- The difference vanishes outside the compact set `S`.
  have h_diff_zero_outside : ∀ x, x ∉ S → g₀ x - g x = 0 := by
    intro x hx
    have hx_gt : R + 2 < ‖x‖ := by
      have := Metric.mem_closedBall.not.1 hx
      simpa [S, Real.dist_eq, sub_eq_add_neg] using this
    have hx_ge : R + 2 ≤ ‖x‖ := le_of_lt hx_gt
    have hR_lt : R < R + 2 := by linarith
    have hg₀_zero := hg₀_zero_outside x (lt_trans hR_lt hx_gt)
    have hχ_zero := hχ_zero_outside x hx_ge
    simp [g, χ, hg₀_zero, hχ_zero]

  -- Control the L² norm on the compact set using the uniform bound.
  have h_integrand_le :
      ∀ x, ‖g₀ x - g x‖₊ ^ 2
          ≤ Set.indicator S (fun _ => ENNReal.ofReal (δ ^ 2)) x := by
    intro x
    classical
    by_cases hx : x ∈ S
    · have hnorm_le := h_pointwise_bound x
      have hnorm_nonneg : 0 ≤ ‖g₀ x - g x‖ := norm_nonneg _
      have hpow_le : ‖g₀ x - g x‖ ^ 2 ≤ δ ^ 2 := by
        have := mul_le_mul hnorm_le hnorm_le hnorm_nonneg hδ_nonneg
        simpa [pow_two, mul_comm] using this
      have hpow_eq :
          (‖g₀ x - g x‖₊ : ℝ≥0∞) ^ 2
            = ENNReal.ofReal (‖g₀ x - g x‖ ^ 2) := by
        simp [pow_two, ENNReal.coe_mul, ENNReal.ofReal_mul, hnorm_nonneg]
      have hpow_bound :
          (‖g₀ x - g x‖₊ : ℝ≥0∞) ^ 2
            ≤ ENNReal.ofReal (δ ^ 2) := by
        rw [hpow_eq]
        exact ENNReal.ofReal_le_ofReal hpow_le
      have hx_indicator :
          Set.indicator S (fun _ => ENNReal.ofReal (δ ^ 2)) x
            = ENNReal.ofReal (δ ^ 2) := by
        simp [Set.indicator_of_mem, hx]
      exact hx_indicator.symm ▸ hpow_bound
    · have hzero := h_diff_zero_outside x hx
      simp [Set.indicator_of_notMem, hx, hzero]

  have h_integral_bound :
      ∫⁻ x, ‖g₀ x - g x‖₊ ^ 2 ∂volume
        ≤ ENNReal.ofReal (δ ^ 2) * volume S := by
    have h_le :
        ∀ᵐ x ∂volume,
          ‖g₀ x - g x‖₊ ^ 2
            ≤ Set.indicator S (fun _ => ENNReal.ofReal (δ ^ 2)) x :=
      ae_of_all _ h_integrand_le
    refine (lintegral_mono_ae h_le).trans ?_
    have h_indicator :=
      MeasureTheory.lintegral_indicator (μ := volume)
        (f := fun _ : ℝ => ENNReal.ofReal (δ ^ 2)) (hs := hS_meas)
    have h_const :
        ∫⁻ x, ENNReal.ofReal (δ ^ 2) ∂(volume.restrict S)
          = ENNReal.ofReal (δ ^ 2) * (volume.restrict S) Set.univ := by
      simp
    have h_restrict : (volume.restrict S) Set.univ = volume S := by
      simp [Measure.restrict_apply]
    have h_result :
        ∫⁻ x, Set.indicator S (fun _ => ENNReal.ofReal (δ ^ 2)) x ∂volume
          = ENNReal.ofReal (δ ^ 2) * volume S := by
      simpa [h_const, h_restrict] using h_indicator
    exact le_of_eq h_result

  have hμS_eq : ENNReal.ofReal μS = volume S := by
    simpa [μS] using ENNReal.ofReal_toReal (ne_of_lt hS_lt_top)
  have h_integral_bound' :
      ∫⁻ x, ‖g₀ x - g x‖₊ ^ 2 ∂volume
        ≤ ENNReal.ofReal (δ ^ 2 * μS) := by
    have hδ_sq_nonneg : 0 ≤ δ ^ 2 := by
      have := sq_nonneg δ
      simpa [pow_two] using this
    have hrewrite₀ :
        ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal μS
          = ENNReal.ofReal (δ ^ 2 * μS) := by
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using
          (ENNReal.ofReal_mul (p := δ ^ 2) (q := μS)
            (hp := hδ_sq_nonneg)).symm
    have hrewrite :
        ENNReal.ofReal (δ ^ 2) * volume S
          = ENNReal.ofReal (δ ^ 2 * μS) := by
      simpa [hμS_eq.symm] using hrewrite₀
    simpa [hrewrite] using h_integral_bound

  have hμS_sq : μS = M ^ 2 := by
    simp [M, pow_two, hμS_nonneg]
  have hδM_le : δ * M ≤ ε / 4 := by
    have hδ_nonneg : 0 ≤ δ := hδ_nonneg
    have hM_le : M ≤ M + 1 := by linarith
    have hmul : δ * M ≤ δ * (M + 1) := by
      have := mul_le_mul_of_nonneg_left hM_le hδ_nonneg
      simpa [δ, mul_comm] using this
    have hδM1 : δ * (M + 1) = ε / 4 := by
      have hne : M + 1 ≠ 0 := ne_of_gt hM_plus_pos
      calc
        δ * (M + 1)
            = ε / (4 * (M + 1)) * (M + 1) := by simp [δ, mul_comm]
        _ = (ε * (M + 1)) / (4 * (M + 1)) := by
            simpa [mul_comm, mul_assoc]
              using (div_mul_eq_mul_div (ε) (4 * (M + 1)) (M + 1))
        _ = ε / 4 := by
            simpa [mul_comm, mul_assoc]
              using (mul_div_mul_left (a := ε) (b := (4 : ℝ))
                (c := M + 1) hne)
    exact hmul.trans (le_of_eq hδM1)
  have hδ_sq_le : δ ^ 2 * μS ≤ (ε / 4) ^ 2 := by
    have hε4_nonneg : 0 ≤ ε / 4 := div_nonneg hε_pos.le (by norm_num)
    have hδM_nonneg : 0 ≤ δ * M := mul_nonneg hδ_nonneg hM_nonneg
    have hmul := mul_le_mul hδM_le hδM_le hδM_nonneg hε4_nonneg
    have hleft_eq : (δ * M) * (δ * M) = δ ^ 2 * μS := by
      simp [pow_two, hμS_sq, mul_mul_mul_comm]
    have hright_eq : (ε / 4) * (ε / 4) = (ε / 4) ^ 2 := by
      simp [pow_two]
    have hprod_le : (δ * M) * (δ * M) ≤ (ε / 4) * (ε / 4) := hmul
    have h' : δ ^ 2 * μS ≤ (ε / 4) ^ 2 := by
      simpa [hleft_eq, hright_eq] using hprod_le
    exact h'
  have h_integral_final :
      ∫⁻ x, ‖g₀ x - g x‖₊ ^ 2 ∂volume
        ≤ ENNReal.ofReal ((ε / 4) ^ 2) := by
    refine h_integral_bound'.trans ?_
    have := ENNReal.ofReal_le_ofReal hδ_sq_le
    simpa using this

  -- Convert the integral bound to an L² norm bound.
  have h_eLp_le : eLpNorm (g₀ - g) 2 volume ≤ ENNReal.ofReal (ε / 4) := by
    have hp0' : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp_top' : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have h_formula :=
      eLpNorm_eq_lintegral_rpow_enorm (μ := volume) (f := g₀ - g) hp0' hp_top'
    have h_twoReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    have h_half_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have h_pow_le :=
      ENNReal.rpow_le_rpow h_integral_final h_half_nonneg
    have hε_quarter_nonneg : 0 ≤ ε / 4 := div_nonneg hε_pos.le (by norm_num)
    have htarget_pow_raw :
        (ENNReal.ofReal (ε / 4 * (ε / 4))) ^ (1 / 2 : ℝ)
          = ENNReal.ofReal (ε / 4) := by
      have hpos : 0 ≤ ε / 4 * (ε / 4) :=
        mul_nonneg hε_quarter_nonneg hε_quarter_nonneg
      have hcoeff : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have hpow_eval₀ : ((ε / 4) ^ 2) ^ (1 / 2 : ℝ) = ε / 4 := by
        have hsqrt : ((ε / 4) ^ 2) ^ (1 / 2 : ℝ)
            = Real.sqrt ((ε / 4) ^ 2) := by
          simp [Real.sqrt_eq_rpow]
        have hsq : Real.sqrt ((ε / 4) ^ 2) = ε / 4 := by
          simpa [pow_two] using Real.sqrt_sq hε_quarter_nonneg
        exact hsqrt.trans hsq
      have hpow_eval : (ε / 4 * (ε / 4)) ^ (1 / 2 : ℝ) = ε / 4 := by
        have hrewrite : ε / 4 * (ε / 4) = (ε / 4) ^ 2 := by
          simp [pow_two]
        simpa [hrewrite] using hpow_eval₀
      calc
        (ENNReal.ofReal (ε / 4 * (ε / 4))) ^ (1 / 2 : ℝ)
            = ENNReal.ofReal ((ε / 4 * (ε / 4)) ^ (1 / 2 : ℝ)) :=
              ENNReal.ofReal_rpow_of_nonneg hpos hcoeff
        _ = ENNReal.ofReal (ε / 4) := by rw [hpow_eval]
    have htarget_pow :
        (ENNReal.ofReal (ε / 4 * (ε / 4))) ^ (2⁻¹ : ℝ)
          = ENNReal.ofReal (ε / 4) := by
      simpa [one_div] using htarget_pow_raw
    have htarget_ofReal :
        ENNReal.ofReal ((ε / 4 * (ε / 4)) ^ (2⁻¹ : ℝ))
          = ENNReal.ofReal (ε / 4) := by
      have hpow_eval_raw : (ε / 4 * (ε / 4)) ^ (1 / 2 : ℝ) = ε / 4 := by
        have hpow_eval_sq : ((ε / 4) ^ 2) ^ (1 / 2 : ℝ) = ε / 4 := by
          have hsqrt : ((ε / 4) ^ 2) ^ (1 / 2 : ℝ)
              = Real.sqrt ((ε / 4) ^ 2) := by
            simp [Real.sqrt_eq_rpow]
          have hsq : Real.sqrt ((ε / 4) ^ 2) = ε / 4 := by
            have hε_quarter_nonneg : 0 ≤ ε / 4 :=
              div_nonneg hε_pos.le (by norm_num)
            simpa [pow_two] using Real.sqrt_sq hε_quarter_nonneg
          exact hsqrt.trans hsq
        have hrewrite : ε / 4 * (ε / 4) = (ε / 4) ^ 2 := by
          simp [pow_two]
        simpa [hrewrite] using hpow_eval_sq
      have htarget_ofReal_raw :
          ENNReal.ofReal ((ε / 4 * (ε / 4)) ^ (1 / 2 : ℝ))
            = ENNReal.ofReal (ε / 4) :=
        congrArg ENNReal.ofReal hpow_eval_raw
      simpa [one_div] using htarget_ofReal_raw
    have hleft :
        eLpNorm (g₀ - g) 2 volume
          = (∫⁻ x, ‖g₀ x - g x‖₊ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
      simpa [h_twoReal, one_div] using h_formula
    have h_pow_le' :
        eLpNorm (g₀ - g) 2 volume
          ≤ (ENNReal.ofReal (ε / 4 * (ε / 4))) ^ (1 / 2 : ℝ) := by
      simpa [hleft, pow_two, mul_comm, one_div, htarget_ofReal] using h_pow_le
    simpa [htarget_pow, one_div] using h_pow_le'

  -- Combine approximations using the triangle inequality.
  have hf_meas : AEStronglyMeasurable f_L2 volume := hf.aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable g volume := hg_continuous.aestronglyMeasurable
  have h_triangle :=
    eLpNorm_triangle_diff f_L2 g₀ g hf_meas hg₀_meas hg_meas
  have h_total_le :
      eLpNorm (f_L2 - g) 2 volume
        ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) :=
    h_triangle.trans <| add_le_add hg₀_close_le h_eLp_le
  have hε_half_nonneg : 0 ≤ ε / 2 := div_nonneg hε_pos.le (by norm_num)
  have hε_quarter_nonneg : 0 ≤ ε / 4 := div_nonneg hε_pos.le (by norm_num)
  have hsum_eq :
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4)
        = ENNReal.ofReal (3 * ε / 4) := by
    have hε_quarter_pos : 0 ≤ ε / 4 := hε_quarter_nonneg
    have hε_half_pos : 0 ≤ ε / 2 := hε_half_nonneg
    have hring : ε / 2 + ε / 4 = 3 * ε / 4 := by ring
    have hsum := (ENNReal.ofReal_add hε_half_pos hε_quarter_pos).symm
    simpa [hring] using hsum
  have hthree_lt_real : 3 * ε / 4 < ε := by
    have hε_quarter_pos : 0 < ε / 4 := div_pos hε_pos (by norm_num)
    have hrewrite : 3 * ε / 4 = ε - ε / 4 := by ring
    simpa [hrewrite] using sub_lt_self ε hε_quarter_pos
  have hthree_lt : ENNReal.ofReal (3 * ε / 4) < ENNReal.ofReal ε := by
    have hε_pos' : 0 < ε := hε_pos
    exact (ENNReal.ofReal_lt_ofReal_iff hε_pos').2 hthree_lt_real
  have h_final_lt : eLpNorm (f_L2 - g) 2 volume < ENNReal.ofReal ε :=
    lt_of_le_of_lt (by simpa [hsum_eq] using h_total_le) hthree_lt

  refine ⟨g, hg_compact, hg_smooth, h_final_lt⟩

/-- The sequence `n ↦ 1/(n+1)` tends to zero. -/
lemma tendsto_one_div_add_one_nhds_0 :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (𝓝 0) := by
  classical
  simpa using tendsto_one_div_add_atTop_nhds_zero_nat

/-- Produce a sequence of compactly supported smooth approximations for an `L²` function. -/
lemma smooth_compactly_supported_dense_L2_sequence
    (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    ∃ ψ : ℕ → ℝ → ℂ,
      (∀ n, HasCompactSupport (ψ n)) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n)) ∧
      Filter.Tendsto (fun n => eLpNorm (fun t : ℝ => f t - ψ n t) 2 volume) Filter.atTop (𝓝 0) := by
  classical
  -- For each `n`, pick a smooth compactly supported approximation with error `1 / (n + 1)`.
  have h_exists :
      ∀ n : ℕ,
        ∃ ψ : ℝ → ℂ,
          HasCompactSupport ψ ∧
          ContDiff ℝ (⊤ : ℕ∞) ψ ∧
          eLpNorm (fun t : ℝ => f t - ψ t) 2 volume
              < ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have h_pos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
      exact one_div_pos.2 (Nat.cast_add_one_pos n)
    simpa using
      smooth_compactly_supported_dense_L2 (f_L2 := f) hf (1 / (n + 1 : ℝ)) h_pos
  -- Choose the sequence and record the corresponding bounds.
  choose ψ hψ_support hψ_smooth hψ_norm using h_exists
  refine ⟨ψ, hψ_support, hψ_smooth, ?_⟩
  -- Show that the error sequence converges to zero.
  let g : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun t : ℝ => f t - ψ n t) 2 volume
  have h_not_top : ∀ n, g n ≠ ⊤ := by
    intro n
    exact ne_of_lt (lt_trans (hψ_norm n) ENNReal.ofReal_lt_top)
  -- Work with the real-valued sequence given by `toReal`.
  have h_nonneg : ∀ n, 0 ≤ (g n).toReal := fun n => ENNReal.toReal_nonneg
  have h_le : ∀ n, (g n).toReal ≤ 1 / (n + 1 : ℝ) := by
    intro n
    have h_le' : g n ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := le_of_lt (hψ_norm n)
    have h_nonneg' : 0 ≤ (1 : ℝ) / (n + 1 : ℝ) :=
      one_div_nonneg.mpr (Nat.cast_add_one_pos n).le
    exact ENNReal.toReal_le_of_le_ofReal h_nonneg' h_le'
  have h_tendsto_real :
      Filter.Tendsto (fun n : ℕ => (g n).toReal) Filter.atTop (𝓝 0) := by
    have h_tendsto_aux :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_one_nhds_0
    exact squeeze_zero h_nonneg h_le h_tendsto_aux
  -- Convert the real convergence back to `ℝ≥0∞`.
  have h_tendsto :
      Filter.Tendsto g Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε_pos
    -- Use the real convergence to find N
    by_cases hε_top : ε = ⊤
    · refine ⟨0, fun n _ => ?_⟩
      simp [hε_top]
    · have hε_finite : ε ≠ ⊤ := hε_top
      have hε_lt_top : ε < ⊤ := lt_of_le_of_ne le_top hε_finite
      have hε_toReal_pos : (0 : ℝ) < ε.toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨hε_pos, hε_lt_top⟩
      have h_eventually : ∀ᶠ n in Filter.atTop, (g n).toReal < ε.toReal := by
        exact Filter.Tendsto.eventually_lt h_tendsto_real tendsto_const_nhds hε_toReal_pos
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
      refine ⟨N, fun n hn => ?_⟩
      have h_toReal_lt : (g n).toReal < ε.toReal := hN n hn
      have h_ne_top : g n ≠ ⊤ := h_not_top n
      have h_lt : g n < ε := (ENNReal.toReal_lt_toReal h_ne_top hε_finite).mp h_toReal_lt
      exact le_of_lt h_lt
  simpa [g] using h_tendsto

/-- The Fourier integral of a Schwartz function is in every `Lᵖ`. -/
lemma Schwartz.memLp_fourierIntegral (φ : SchwartzMap ℝ ℂ) {p : ℝ≥0∞} :
    MemLp (fun ξ : ℝ => fourierIntegral (fun t : ℝ => φ t) ξ) p volume := by
  classical
  have hSchwartz : MemLp ((SchwartzMap.fourierTransformCLM ℂ) φ) p volume :=
    SchwartzMap.memLp ((SchwartzMap.fourierTransformCLM ℂ) φ) p (μ := volume)
  have hSchwartz' :
      MemLp (fun ξ : ℝ => Real.fourierIntegral (fun t : ℝ => φ t) ξ) p volume := by
    simpa [SchwartzMap.fourierTransformCLM_apply]
      using hSchwartz
  simpa [fourierIntegral_eq_real] using hSchwartz'

/-- Pairing the Fourier transform of an integrable function with a Schwartz test
function can be rewritten using the conjugated transform. -/
lemma fourierIntegral_inner_schwartz
    {f : ℝ → ℂ} (hf_L1 : Integrable f) (ψ : SchwartzMap ℝ ℂ) :
    ∫ ξ : ℝ,
        VectorFourier.fourierIntegral fourierChar volume (innerₗ ℝ) f ξ
          * Schwartz.conjFourierTransform ψ ξ ∂volume
      = ∫ t : ℝ, f t *
          VectorFourier.fourierIntegral fourierChar volume (innerₗ ℝ)
            (Schwartz.conjFourierTransform ψ) t ∂volume := by
  classical
  -- The conjugated Fourier transform of `ψ` is integrable on the frequency side.
  have hψ_conj_int : Integrable (Schwartz.conjFourierTransform ψ) :=
    Schwartz.integrable_conj_fourierIntegral ψ
  -- Apply the general self-adjointness identity for the Fourier integral.
  have h_selfAdj :=
    VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
      (L := innerₗ ℝ) (f := f)
      (g := Schwartz.conjFourierTransform ψ)
      Real.continuous_fourierChar (by continuity) hf_L1 hψ_conj_int
  -- Interpret the outcome of the self-adjointness lemma.
  -- The statement is exactly the conclusion obtained from the general formula.
  simpa [Schwartz.conjFourierTransform, smul_eq_mul, Pi.mul_apply]
    using h_selfAdj

/-- Frequency-side pairing with a Schwartz function can be rewritten using the
explicit kernel formulation. -/
lemma fourierIntegral_inner_schwartz_conj
    {f : ℝ → ℂ} (hf_L1 : Integrable f) (ψ : SchwartzMap ℝ ℂ) :
    ∫ ξ : ℝ, fourierIntegral f ξ * conj (fourierIntegral (fun t : ℝ => ψ t) ξ) ∂volume
      = ∫ t : ℝ, f t * conj (ψ t) ∂volume := by
  classical
  -- Start from the vector-valued self-adjointness identity.
  have h := fourierIntegral_inner_schwartz (hf_L1 := hf_L1) (ψ := ψ)
  -- First rewrite the identity using the `Real`-valued Fourier integral.
  have h_real :=
    (by
      simpa [Real.fourierIntegral, smul_eq_mul, Schwartz.conjFourierTransform]
        using h)
  -- Move from the `Real` normalisation to the explicit kernel formulation.
  have h_explicit :
      ∫ ξ : ℝ, fourierIntegral f ξ * conj (fourierIntegral (fun t : ℝ => ψ t) ξ) ∂volume
        = ∫ t : ℝ, f t *
            fourierIntegral (Schwartz.conjFourierTransform ψ) t ∂volume := by
    have h_lhs : ∀ ξ, VectorFourier.fourierIntegral fourierChar volume (innerₗ ℝ) f ξ =
        Real.fourierIntegral f ξ := by
      intro ξ
      rfl
    have h_rhs : ∀ t, VectorFourier.fourierIntegral fourierChar volume (innerₗ ℝ)
        (Schwartz.conjFourierTransform ψ) t =
        Real.fourierIntegral (Schwartz.conjFourierTransform ψ) t := by
      intro t
      rfl
    simp only [h_lhs, h_rhs, fourierIntegral_eq_real, fourierIntegral_eq_real] at h_real
    exact h_real
  -- Finally replace the Fourier transform of the conjugated Schwartz function.
  have h_final :
      fourierIntegral (Schwartz.conjFourierTransform ψ) = fun t : ℝ => conj (ψ t) := by
    simpa [Schwartz.doubleFourierTransform] using
      Schwartz.fourierIntegral_conj_fourierIntegral ψ
  simpa [h_final] using h_explicit

end Auxiliary

section Approximation

variable {f : ℝ → ℂ}

/-- For Schwartz functions the Fourier integral belongs to `L²`. -/
lemma fourierIntegral_memLp_of_schwartz (φ : SchwartzMap ℝ ℂ) :
    MemLp (fun ξ : ℝ => fourierIntegral (fun t : ℝ => φ t) ξ) 2 volume := by
  classical
  have hp : 1 ≤ (2 : ℝ≥0∞) := by norm_num
  simpa using (Schwartz.memLp_fourierIntegral (φ := φ) (p := (2 : ℝ≥0∞)))

lemma fourierIntegral_eLpNorm_eq (φ : SchwartzMap ℝ ℂ) :
    eLpNorm (fun ξ : ℝ => fourierIntegral (fun t : ℝ => φ t) ξ) 2 volume
      = eLpNorm (fun t : ℝ => φ t) 2 volume := by
  classical
  set F : ℝ → ℂ := fun ξ => fourierIntegral (fun t : ℝ => φ t) ξ
  set G : ℝ → ℂ := fun t => φ t
  have hF_mem : MemLp F 2 volume := fourierIntegral_memLp_of_schwartz φ
  have hG_mem : MemLp G 2 volume :=
    (SchwartzMap.memLp (φ) (p := (2 : ℝ≥0∞)) (μ := volume))
  have hF_int_sq : Integrable (fun ξ : ℝ => ‖F ξ‖ ^ 2) volume := by
    have := (memLp_two_iff_integrable_sq_norm hF_mem.1).1 hF_mem
    simpa [F, pow_two] using this
  have hG_int_sq : Integrable (fun t : ℝ => ‖G t‖ ^ 2) volume := by
    have := (memLp_two_iff_integrable_sq_norm hG_mem.1).1 hG_mem
    simpa [G, pow_two] using this
  have hF_nonneg : 0 ≤ᵐ[volume] fun ξ : ℝ => ‖F ξ‖ ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hG_nonneg : 0 ≤ᵐ[volume] fun t : ℝ => ‖G t‖ ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hF_ofReal :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF_int_sq hF_nonneg
  have hG_ofReal :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG_int_sq hG_nonneg
  have hF_lintegral :
      ∫⁻ ξ : ℝ, (‖F ξ‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ∫⁻ ξ : ℝ, ENNReal.ofReal (‖F ξ‖ ^ 2) ∂volume := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro ξ
    simp [F, pow_two, ENNReal.ofReal_mul]
  have hG_lintegral :
      ∫⁻ t : ℝ, (‖G t‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ∫⁻ t : ℝ, ENNReal.ofReal (‖G t‖ ^ 2) ∂volume := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro t
    simp [G, pow_two, ENNReal.ofReal_mul]
  have hF_eq :
      ∫⁻ ξ : ℝ, (‖F ξ‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ENNReal.ofReal (∫ ξ : ℝ, ‖F ξ‖ ^ 2 ∂volume) := by
    simpa [hF_lintegral] using hF_ofReal.symm
  have hG_eq :
      ∫⁻ t : ℝ, (‖G t‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ENNReal.ofReal (∫ t : ℝ, ‖G t‖ ^ 2 ∂volume) := by
    simpa [hG_lintegral] using hG_ofReal.symm
  have h_plancherel := fourier_plancherel φ
  have h_eq_integral :
      ∫ ξ : ℝ, ‖F ξ‖ ^ 2 ∂volume = ∫ t : ℝ, ‖G t‖ ^ 2 ∂volume := by
    simpa [F, G, fourierIntegral_eq_real] using h_plancherel.symm
  have h_eq_lintegral :
      ∫⁻ ξ : ℝ, (‖F ξ‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ∫⁻ t : ℝ, (‖G t‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    simp [hF_eq, hG_eq, h_eq_integral]
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_twoReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  have hF_formula :=
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
      (μ := volume) (f := F) (p := (2 : ℝ≥0∞))
      (hp_ne_zero := hp0) (hp_ne_top := hp_top)
  have hG_formula :=
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
      (μ := volume) (f := G) (p := (2 : ℝ≥0∞))
      (hp_ne_zero := hp0) (hp_ne_top := hp_top)
  have hF_eval :
      eLpNorm F 2 volume
        = (∫⁻ ξ : ℝ, (‖F ξ‖₊ : ℝ≥0∞) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    simpa [h_twoReal, one_div] using hF_formula
  have hG_eval :
      eLpNorm G 2 volume
        = (∫⁻ t : ℝ, (‖G t‖₊ : ℝ≥0∞) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    simpa [h_twoReal, one_div] using hG_formula
  simp [F, G, h_eq_lintegral, hF_eval, hG_eval]

/-- A Schwartz function is integrable. -/
lemma schwartz_integrable (φ : SchwartzMap ℝ ℂ) : Integrable (fun t : ℝ => φ t) :=
  (integrable φ : Integrable (fun t : ℝ => φ t))

/-- `L¹ ∩ L²` functions can be approximated in `L²` by Schwartz functions.
    This is a preparatory statement for the Plancherel extension. -/
lemma exists_schwartz_L2_approx (f : ℝ → ℂ)
    (_hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume) :
    ∃ (φ : ℕ → SchwartzMap ℝ ℂ),
      (∀ n, Integrable (fun t : ℝ => φ n t)) ∧
      (∀ n, MemLp (fun t : ℝ => φ n t) 2 volume) ∧
      Filter.Tendsto (fun n => eLpNorm (fun t : ℝ => f t - φ n t) 2 volume) Filter.atTop (𝓝 0) := by
  classical
  -- Define the tolerance used at stage `n`.
  let ε : ℕ → ℝ := fun n => 1 / (2 * (n + 1 : ℝ))
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    have h_two : 0 < (2 : ℝ) := by norm_num
    have h_succ : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hden : 0 < 2 * (n + 1 : ℝ) :=
      by simpa [mul_comm, mul_left_comm, mul_assoc] using mul_pos h_two h_succ
    simpa [ε, one_div, inv_pos] using hden

  -- Step 1: approximate by smooth compactly supported functions.
  have h_exists_g :
      ∀ n : ℕ,
        ∃ g : ℝ → ℂ,
          HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
            eLpNorm (fun t : ℝ => f t - g t) 2 volume < ENNReal.ofReal (ε n) := by
    intro n
    have hε : 0 < ε n := hε_pos n
    simpa [ε]
      using
        smooth_compactly_supported_dense_L2 (f_L2 := f) hf_L2 (ε := ε n) hε
  choose g hg_support hg_smooth hg_close using h_exists_g

  -- Step 2: approximate each of these by a Schwartz function with the same tolerance.
  have h_exists_phi :
      ∀ n : ℕ, ∃ φ : SchwartzMap ℝ ℂ,
        eLpNorm (fun t : ℝ => g n t - φ t) 2 volume < ENNReal.ofReal (ε n) := by
    intro n
    have hε : 0 < ε n := hε_pos n
    obtain hφ :=
      schwartz_approximates_smooth_compactly_supported (g := g n)
        (hg_compact := hg_support n) (hg_smooth := hg_smooth n)
        (ε := ε n) hε
    simpa using hφ
  choose φ hφ_close using h_exists_phi

  -- Record measurability data for later use.
  have hf_meas : AEStronglyMeasurable f volume := hf_L2.aestronglyMeasurable
  have hg_meas : ∀ n, AEStronglyMeasurable (g n) volume := fun n =>
    (hg_smooth n).continuous.aestronglyMeasurable
  have hφ_meas : ∀ n, AEStronglyMeasurable (fun t : ℝ => φ n t) volume := fun n =>
    (SchwartzMap.continuous (φ n)).aestronglyMeasurable

  -- Control the error for the Schwartz approximations.
  have h_final_lt :
      ∀ n,
        eLpNorm (fun t : ℝ => f t - φ n t) 2 volume
            < ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have htriangle :=
      eLpNorm_triangle_diff f (g n) (fun t : ℝ => φ n t)
        hf_meas (hg_meas n) (hφ_meas n)
    have hsum_lt :
        eLpNorm (fun t : ℝ => f t - g n t) 2 volume
            + eLpNorm (fun t : ℝ => g n t - φ n t) 2 volume
          < ENNReal.ofReal (ε n) + ENNReal.ofReal (ε n) :=
      ENNReal.add_lt_add (hg_close n) (hφ_close n)
    have hsum_eq : ENNReal.ofReal (ε n) + ENNReal.ofReal (ε n)
        = ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      have hε_nonneg : 0 ≤ ε n := (hε_pos n).le
      have hε_double : 2 * ε n = 1 / (n + 1 : ℝ) := by
        simp [ε, mul_comm, mul_left_comm]
      have hε_sum : ε n + ε n = 1 / (n + 1 : ℝ) := by
        simpa [hε_double] using (two_mul (ε n)).symm
      simpa [hε_sum]
        using (ENNReal.ofReal_add hε_nonneg hε_nonneg).symm
    exact lt_of_le_of_lt htriangle <| by simpa [hsum_eq] using hsum_lt

  -- Assemble the desired sequence.
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro n
    exact schwartz_integrable (φ n)
  · intro n
    simpa using (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
  · -- Show that the error sequence converges to zero.
    let gseq : ℕ → ℝ≥0∞ := fun n =>
      eLpNorm (fun t : ℝ => f t - φ n t) 2 volume
    have h_ne_top : ∀ n, gseq n ≠ ∞ := fun n =>
      ne_of_lt <| lt_trans (h_final_lt n) ENNReal.ofReal_lt_top
    have h_nonneg : ∀ n, 0 ≤ (gseq n).toReal := fun _ => ENNReal.toReal_nonneg
    have h_le : ∀ n, (gseq n).toReal ≤ 1 / (n + 1 : ℝ) := by
      intro n
      have h_le' : gseq n ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) :=
        (le_of_lt (h_final_lt n))
      have h_pos : 0 ≤ 1 / (n + 1 : ℝ) := by
        have hn_pos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
        exact div_nonneg zero_le_one hn_pos.le
      exact ENNReal.toReal_le_of_le_ofReal h_pos h_le'
    have h_tendsto_aux := tendsto_one_div_add_one_nhds_0
    have h_tendsto_real :
        Filter.Tendsto (fun n : ℕ => (gseq n).toReal)
          Filter.atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_le h_tendsto_aux
    have h_tendsto :
        Filter.Tendsto gseq Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      rw [ENNReal.tendsto_atTop_zero]
      intro ε hε_pos
      by_cases hε_top : ε = ⊤
      · refine ⟨0, fun n _ => ?_⟩
        simp [hε_top]
      · have hε_finite : ε ≠ ⊤ := hε_top
        have hε_lt_top : ε < ⊤ := lt_of_le_of_ne le_top hε_finite
        have hε_toReal_pos : (0 : ℝ) < ε.toReal := by
          rw [ENNReal.toReal_pos_iff]
          exact ⟨hε_pos, hε_lt_top⟩
        have h_eventually : ∀ᶠ n in Filter.atTop, (gseq n).toReal < ε.toReal := by
          exact Filter.Tendsto.eventually_lt h_tendsto_real tendsto_const_nhds hε_toReal_pos
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
        refine ⟨N, fun n hn => ?_⟩
        have h_toReal_lt : (gseq n).toReal < ε.toReal := hN n hn
        have h_ne_top : gseq n ≠ ⊤ := h_ne_top n
        have h_lt : gseq n < ε :=
          (ENNReal.toReal_lt_toReal h_ne_top hε_finite).mp h_toReal_lt
        exact le_of_lt h_lt
    simpa [gseq] using h_tendsto

lemma tendsto_inner_const_right_of_L2_tendsto
    {φ : ℕ → Lp ℂ 2 (volume : Measure ℝ)} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hφ : Filter.Tendsto φ Filter.atTop (𝓝 f))
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    Filter.Tendsto (fun n => @inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ (φ n) g)
    Filter.atTop (𝓝 (@inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ f g)) := by
  classical
  have h_norm :
      Filter.Tendsto (fun n => ‖φ n - f‖) Filter.atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).1 hφ
  have h_mul :
      Filter.Tendsto (fun n => ‖φ n - f‖ * ‖g‖) Filter.atTop (𝓝 0) := by
    simpa [zero_mul] using (h_norm.mul tendsto_const_nhds)
  have h_nonneg : ∀ n, 0 ≤ ‖@inner
      ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ (φ n - f) g‖ := fun _ => norm_nonneg _
  have h_le : ∀ n, ‖@inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ (φ n - f) g‖ ≤ ‖φ n - f‖ * ‖g‖ := by
    intro n
    simpa using norm_inner_le_norm (φ n - f) g
  have h_squeeze : Filter.Tendsto (fun n => ‖@inner ℂ
      (Lp ℂ 2 (volume : Measure ℝ)) _ (φ n - f) g‖) Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_mul
      (Filter.Eventually.of_forall h_nonneg) (Filter.Eventually.of_forall h_le)
  refine (tendsto_iff_norm_sub_tendsto_zero).2 ?_
  have h_norm_diff : Filter.Tendsto (fun n => ‖@inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ (φ n) g -
      @inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ f g‖) Filter.atTop (𝓝 0) := by
    simpa [inner_sub_left] using h_squeeze
  simpa using h_norm_diff

lemma tendsto_inner_const_left_of_L2_tendsto
    {φ : ℕ → Lp ℂ 2 (volume : Measure ℝ)} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hφ : Filter.Tendsto φ Filter.atTop (𝓝 f))
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    Filter.Tendsto (fun n => @inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ g (φ n))
      Filter.atTop (𝓝 (@inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ g f)) := by
  classical
  have h_right := tendsto_inner_const_right_of_L2_tendsto hφ g
  have h_conj :=
    (Complex.continuous_conj.tendsto
        (@inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ f g)).comp h_right
  refine (by
      convert h_conj using 1
      · ext n; simp [Function.comp, inner_conj_symm]
      · simp [inner_conj_symm])

/-- Each `L²` function can be approximated arbitrarily well by a Schwartz function. -/
lemma exists_schwartz_L2_approx_general (f : ℝ → ℂ)
    (hf_L2 : MemLp f 2 volume) (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ,
      eLpNorm (fun t : ℝ => f t - φ t) 2 volume < ENNReal.ofReal ε := by
  classical
  obtain ⟨g, hg_support, hg_smooth, hg_close⟩ :=
    smooth_compactly_supported_dense_L2 f hf_L2 (ε / 2) (half_pos hε_pos)
  obtain ⟨φ, hφ_close⟩ :=
    schwartz_approximates_smooth_compactly_supported g hg_support hg_smooth
      (ε / 2) (half_pos hε_pos)
  have hf_meas : AEStronglyMeasurable f volume := hf_L2.aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable g volume :=
    (hg_smooth.continuous.aestronglyMeasurable)
  have hφ_meas : AEStronglyMeasurable (fun t : ℝ => φ t) volume :=
    (SchwartzMap.continuous φ).aestronglyMeasurable
  have htriangle :=
    eLpNorm_triangle_diff f g (fun t : ℝ => φ t)
      hf_meas hg_meas hφ_meas
  have hsum_lt :
      eLpNorm (fun t : ℝ => f t - g t) 2 volume
          + eLpNorm (fun t : ℝ => g t - φ t) 2 volume
        < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
    ENNReal.add_lt_add hg_close hφ_close
  have hε_nonneg : 0 ≤ ε := hε_pos.le
  have hε_half_nonneg : 0 ≤ ε / 2 := by exact div_nonneg hε_nonneg (by norm_num)
  have hsum_eq :
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
        = ENNReal.ofReal ε := by
    have hsum : ε / 2 + ε / 2 = ε := by ring
    simpa [hsum] using
      (ENNReal.ofReal_add hε_half_nonneg hε_half_nonneg).symm
  have h_lt :
      eLpNorm (fun t : ℝ => f t - φ t) 2 volume < ENNReal.ofReal ε :=
    lt_of_le_of_lt htriangle <| by simpa [hsum_eq] using hsum_lt
  exact ⟨φ, h_lt⟩

/-- Schwartz functions are dense in `L²(ℝ)` viewed as `Lp`. -/
lemma denseRange_schwartz_toLp_L2 :
    DenseRange (fun φ : SchwartzMap ℝ ℂ =>
      (SchwartzMap.memLp (φ) (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
        (fun t : ℝ => φ t)) := by
  classical
  refine (denseRange_iff_closure_range).2 ?_
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro f _
    refine (Metric.mem_closure_iff).2 ?_
    intro ε hε_pos
    have hf_mem : MemLp (fun t : ℝ => (f : Lp ℂ 2 volume) t) 2 volume := Lp.memLp f
    obtain ⟨φ, hφ_close⟩ :=
      exists_schwartz_L2_approx_general (fun t : ℝ => (f : ℝ → ℂ) t)
        hf_mem ε hε_pos
    set φLp : Lp ℂ 2 volume :=
      (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp (fun t : ℝ => φ t)
    have hdiff_mem : MemLp
        (fun t : ℝ => (f : ℝ → ℂ) t - φ t) 2 volume :=
      hf_mem.sub (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume))
    have h_ne_top :
        eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ t) 2 volume ≠ ∞ :=
      hdiff_mem.2.ne
    have hcalc :
        ((hf_mem).sub (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume))).toLp
            (fun t : ℝ => (f : ℝ → ℂ) t - φ t)
          = f - φLp := by
      simpa [φLp]
        using
          MemLp.toLp_sub hf_mem
            (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume))
    have h_norm_eq :
        ‖f - φLp‖
          = ENNReal.toReal
              (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ t) 2 volume) := by
      have hnorm :=
        Lp.norm_toLp (μ := volume)
          (f := fun t : ℝ => (f : ℝ → ℂ) t - φ t) hdiff_mem
      simpa [hdiff_mem, hcalc]
        using hnorm
    have h_toReal_lt :
        ENNReal.toReal
            (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ t) 2 volume)
          < ε := by
      have :=
        (ENNReal.toReal_lt_toReal h_ne_top (by simp)).2 hφ_close
      have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
      simpa [ENNReal.toReal_ofReal hε_nonneg] using this
    have h_dist_lt : dist f φLp < ε := by
      simpa [dist_eq_norm, h_norm_eq] using h_toReal_lt
    refine ⟨φLp, ?_, h_dist_lt⟩
    exact ⟨φ, rfl⟩

/-- Every `L²` function is the limit of a sequence of Schwartz functions in the
`L²` topology. This upgrades the density statement to a sequential form that is
convenient for limit arguments. -/
lemma tendsto_schwartz_toLp_L2
    (f : Lp ℂ 2 volume) :
    ∃ φ : ℕ → SchwartzMap ℝ ℂ,
      Filter.Tendsto (fun n : ℕ =>
          (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
            (fun t : ℝ => φ n t))
        Filter.atTop (𝓝 f) := by
  classical
  -- Work with a concrete representative of `f`.
  have hf_mem : MemLp (fun t : ℝ => (f : ℝ → ℂ) t) 2 volume := Lp.memLp f
  -- Tolerance used at stage `n`.
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
    simpa [ε, one_div, inv_pos] using hn
  -- Choose a Schwartz approximation at each stage with the prescribed tolerance.
  have h_exists :
      ∀ n : ℕ, ∃ φ : SchwartzMap ℝ ℂ,
        eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ t) 2 volume
          < ENNReal.ofReal (ε n) := by
    intro n
    exact
      exists_schwartz_L2_approx_general (fun t : ℝ => (f : ℝ → ℂ) t) hf_mem
        (ε n) (hε_pos n)
  choose φ hφ_close using h_exists
  -- Package the approximations as elements of `Lp`.
  let φLp : ℕ → Lp ℂ 2 volume := fun n =>
    (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
      (fun t : ℝ => φ n t)
  -- Distances against `f` are controlled by the chosen tolerances.
  have hdist_control :
      ∀ n : ℕ,
        dist (φLp n) f < ε n := by
    intro n
    have hdiff_mem :
        MemLp
            (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume :=
      hf_mem.sub (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
    have h_ne_top :
        eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume ≠ ∞ :=
      hdiff_mem.2.ne
    have hcalc :
        ((hf_mem).sub
            (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))).toLp
            (fun t : ℝ => (f : ℝ → ℂ) t - φ n t)
          = f - φLp n := by
      simpa [φLp]
        using
          MemLp.toLp_sub hf_mem
            (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
    have hdist_eq :
        dist (φLp n) f
          = ENNReal.toReal
              (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume) := by
      have hnorm :=
        Lp.norm_toLp (μ := volume)
          (f := fun t : ℝ => (f : ℝ → ℂ) t - φ n t) hdiff_mem
      have hnorm_eq' :
          ‖f - φLp n‖
            = (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume).toReal := by
        simpa [hdiff_mem, hcalc] using hnorm
      have hnorm_eq :
          ‖φLp n - f‖
            = (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume).toReal := by
        simpa [norm_sub_rev] using hnorm_eq'
      simp [dist_eq_norm, hnorm_eq]
    have hε_nonneg : 0 ≤ ε n := (hε_pos n).le
    have h_toReal_lt :
        ENNReal.toReal
            (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume)
          < ε n := by
      have :=
        (ENNReal.toReal_lt_toReal h_ne_top (by simp)).2 (hφ_close n)
      simpa [hε_nonneg, ENNReal.toReal_ofReal] using this
    simpa [hdist_eq] using h_toReal_lt
  -- The distances to `f` are given by the `L²` error terms.
  have hdist_eq :
      (fun n => dist (φLp n) f)
        = fun n =>
            (eLpNorm
                (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume).toReal := by
    funext n
    have hdiff_mem :
        MemLp
            (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume :=
      hf_mem.sub (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
    have hcalc :
        ((hf_mem).sub
            (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))).toLp
            (fun t : ℝ => (f : ℝ → ℂ) t - φ n t)
          = f - φLp n := by
      simpa [φLp]
        using
          MemLp.toLp_sub hf_mem
            (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
    have hnorm :=
      Lp.norm_toLp (μ := volume)
        (f := fun t : ℝ => (f : ℝ → ℂ) t - φ n t)
        hdiff_mem
    have hnorm_eq' :
        ‖f - φLp n‖
          = (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume).toReal := by
      simpa [hdiff_mem, hcalc]
        using hnorm
    have hnorm_eq :
        ‖φLp n - f‖
          = (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume).toReal := by
      simpa [norm_sub_rev] using hnorm_eq'
    simp [dist_eq_norm, hnorm_eq]
  -- The error terms tend to zero, hence so do the distances.
  have hdist_tendsto :
      Filter.Tendsto (fun n => dist (φLp n) f) Filter.atTop (𝓝 0) := by
    have h_nonneg : ∀ n, 0 ≤
        (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume).toReal :=
      fun _ => ENNReal.toReal_nonneg
    have h_le : ∀ n,
        (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume).toReal
          ≤ ε n := by
      intro n
      have hε_nonneg : 0 ≤ ε n := (hε_pos n).le
      have h_ne_top :
          eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume ≠ ∞ :=
        (hf_mem.sub
            (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))).2.ne
      have h_le' :
          eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume
            ≤ ENNReal.ofReal (ε n) := (hφ_close n).le
      have := ENNReal.toReal_le_of_le_ofReal hε_nonneg h_le'
      simpa [ε] using this
    have hε_tendsto : Filter.Tendsto ε Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_one_nhds_0
    have h_tendsto_toReal :
        Filter.Tendsto (fun n =>
            (eLpNorm (fun t : ℝ => (f : ℝ → ℂ) t - φ n t) 2 volume).toReal)
          Filter.atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_le hε_tendsto
    simpa [hdist_eq]
      using h_tendsto_toReal
  refine ⟨φ, ?_⟩
  exact (tendsto_iff_dist_tendsto_zero).2 hdist_tendsto

/-- If an `L²` function is nonzero, some Schwartz test function detects it via the inner product. -/
lemma exists_schwartz_inner_ne_zero
    {h : Lp ℂ 2 volume} (hh : h ≠ 0) :
    ∃ ψ : SchwartzMap ℝ ℂ,
      inner ℂ h
          ((SchwartzMap.memLp ψ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
            (fun t : ℝ => ψ t)) ≠ 0 := by
  classical
  obtain ⟨φ, hφ_tendsto⟩ := tendsto_schwartz_toLp_L2 h
  -- Package the approximating Schwartz functions as elements of `L²`.
  let φLp : ℕ → Lp ℂ 2 volume := fun n =>
    (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
      (fun t : ℝ => φ n t)
  -- Inner products with the approximations converge to `‖h‖²`.
  have h_limit :=
    tendsto_inner_const_left_of_L2_tendsto hφ_tendsto h
  have hnorm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hnorm_sq_pos : 0 < ‖h‖ ^ 2 := by
    simpa [pow_two] using mul_pos hnorm_pos hnorm_pos
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.1 h_limit (‖h‖ ^ 2 / 2) (half_pos hnorm_sq_pos)
  have h_inner_ne : inner ℂ h (φLp N) ≠ 0 := by
    intro hzero
    have hnorm_sq : inner ℂ h h = ‖h‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq_to_K (𝕜 := ℂ) h
    have hdiff_norm : ‖inner ℂ h (φLp N) - inner ℂ h h‖ = ‖h‖ ^ 2 := by
      simp [hzero, hnorm_sq]
    have hlt := hN N (le_rfl : N ≤ N)
    have hdist : ‖inner ℂ h (φLp N) - inner ℂ h h‖ < ‖h‖ ^ 2 / 2 := by
      simpa [dist_eq_norm] using hlt
    have : ‖h‖ ^ 2 < ‖h‖ ^ 2 / 2 := by
      simpa [hdiff_norm] using hdist
    have hhalf_lt : ‖h‖ ^ 2 / 2 < ‖h‖ ^ 2 := half_lt_self hnorm_sq_pos
    have hcontr := this.trans hhalf_lt
    exact (lt_irrefl (‖h‖ ^ 2)) hcontr
  refine ⟨φ N, ?_⟩
  simpa [φLp] using h_inner_ne

/-- If the inner product against every Schwartz test function vanishes, then the `L²` function is
identically zero. -/
lemma L2_eq_zero_of_inner_schwartz
    {h : Lp ℂ 2 volume}
    (hh : ∀ ψ : SchwartzMap ℝ ℂ,
      inner ℂ h
          ((SchwartzMap.memLp ψ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
            (fun t : ℝ => ψ t)) = 0) :
    h = 0 := by
  classical
  by_contra hzero
  obtain ⟨ψ, hψ⟩ := exists_schwartz_inner_ne_zero (h := h) hzero
  exact hψ (hh ψ)

lemma eLpNorm_tendsto_toReal_of_tendsto
    {φ : ℕ → SchwartzMap ℝ ℂ} {f : ℝ → ℂ}
    (hf_L2 : MemLp f 2 volume)
    (hφ_L2 : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume)
    (hφ_tendsto : Filter.Tendsto (fun n =>
        eLpNorm (fun t : ℝ => f t - φ n t) 2 volume) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n =>
        (eLpNorm (fun t : ℝ => f t - φ n t) 2 volume).toReal)
        Filter.atTop (𝓝 0) := by
  have h_ne_top : ∀ n,
      eLpNorm (fun t : ℝ => f t - φ n t) 2 volume ≠ ∞ := fun n =>
    (hf_L2.sub (hφ_L2 n)).2.ne
  have h_zero_ne_top : (0 : ENNReal) ≠ ∞ := by simp
  exact (ENNReal.tendsto_toReal_iff h_ne_top h_zero_ne_top).mpr hφ_tendsto

lemma toLp_tendsto_of_eLpNorm_tendsto
    {φ : ℕ → SchwartzMap ℝ ℂ} {f : ℝ → ℂ}
    (hf_L2 : MemLp f 2 volume)
    (hφ_L2 : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume)
    (hφ_tendsto : Filter.Tendsto (fun n =>
        eLpNorm (fun t : ℝ => f t - φ n t) 2 volume) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => (hφ_L2 n).toLp (fun t : ℝ => φ n t))
        Filter.atTop (𝓝 (hf_L2.toLp f)) := by
  let φLp : ℕ → Lp ℂ 2 volume := fun n =>
    (hφ_L2 n).toLp (fun t : ℝ => φ n t)
  let fLp : Lp ℂ 2 volume := hf_L2.toLp f
  -- First translate the convergence statement to the metric on `Lp`.
  have hdist_eq :
      (fun n => dist (φLp n) fLp)
        = fun n =>
            (eLpNorm (fun t : ℝ => f t - φ n t) 2 volume).toReal := by
    funext n
    have hcalc :
        ((hφ_L2 n).sub hf_L2).toLp
            (fun t : ℝ => φ n t - f t)
          = φLp n - fLp := by
      simpa [φLp, fLp] using MemLp.toLp_sub (hφ_L2 n) hf_L2
    have hnorm :=
      Lp.norm_toLp (μ := volume)
        (f := fun t : ℝ => φ n t - f t) ((hφ_L2 n).sub hf_L2)
    have hdist :
        dist (φLp n) fLp
          = (eLpNorm (fun t : ℝ => f t - φ n t) 2 volume).toReal := by
      calc
        dist (φLp n) fLp
            = ‖φLp n - fLp‖ := by simp [dist_eq_norm]
        _ = ‖((hφ_L2 n).sub hf_L2).toLp (fun t : ℝ => φ n t - f t)‖ := by
              simp [φLp, fLp, hcalc]
        _ = (eLpNorm (fun t : ℝ => φ n t - f t) 2 volume).toReal := by
              simp
        _ = (eLpNorm (fun t : ℝ => f t - φ n t) 2 volume).toReal := by
              simpa [sub_eq_add_neg]
                using
                  congrArg ENNReal.toReal
                    (eLpNorm_sub_comm
                      (f := fun t : ℝ => φ n t)
                      (g := fun t : ℝ => f t)
                      (p := (2 : ℝ≥0∞)) (μ := volume))
    exact hdist
  have hφ_cauchy := eLpNorm_tendsto_toReal_of_tendsto hf_L2 hφ_L2 hφ_tendsto
  have hdist_tendsto :
      Filter.Tendsto (fun n => dist (φLp n) fLp) Filter.atTop (𝓝 0) := by
    simpa [hdist_eq] using hφ_cauchy
  exact (tendsto_iff_dist_tendsto_zero).2 hdist_tendsto

lemma weak_limit_fourierIntegral_of_schwartz_tendsto
    {φ : ℕ → SchwartzMap ℝ ℂ} {f : ℝ → ℂ} (hf_L2 : MemLp f 2 volume)
    (hφ_L1 : ∀ n, Integrable (fun t : ℝ => φ n t))
    (hφ_L2 : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume)
    (hφ_tendsto : Filter.Tendsto (fun n =>
        eLpNorm (fun t : ℝ => f t - φ n t) 2 volume) Filter.atTop (𝓝 0)) :
    ∀ ψ : SchwartzMap ℝ ℂ,
      Filter.Tendsto (fun n =>
          @inner ℂ (Lp ℂ 2 volume) _
            ((fourierIntegral_memLp_of_schwartz ψ).toLp
              (fun ξ : ℝ => fourierIntegral (fun t : ℝ => ψ t) ξ))
            ((fourierIntegral_memLp_of_schwartz (φ n)).toLp
              (fun ξ => fourierIntegral (fun t : ℝ => φ n t) ξ)))
        Filter.atTop
        (𝓝 (∫ t : ℝ, f t * conj (ψ t) ∂volume)) := by
  intro ψ
  -- Set up the objects.
  let ψFun : ℕ → ℝ → ℂ := fun n ξ => fourierIntegral (fun t : ℝ => φ n t) ξ
  have hψ_mem : ∀ n, MemLp (ψFun n) 2 volume := fun n =>
    fourierIntegral_memLp_of_schwartz (φ n)
  let ψLp : ℕ → Lp ℂ 2 volume := fun n => (hψ_mem n).toLp (ψFun n)
  let φLp : ℕ → Lp ℂ 2 volume := fun n => (hφ_L2 n).toLp (fun t : ℝ => φ n t)
  let fLp : Lp ℂ 2 volume := hf_L2.toLp f

  -- The time-side sequence converges.
  have hφLp_tendsto : Filter.Tendsto φLp Filter.atTop (𝓝 fLp) := by
    simpa [φLp, fLp] using toLp_tendsto_of_eLpNorm_tendsto hf_L2 hφ_L2 hφ_tendsto

  -- Frequency and time test functions in L².
  set ψFreqMem := fourierIntegral_memLp_of_schwartz ψ
  set ψFreq : Lp ℂ 2 volume :=
    ψFreqMem.toLp (fun ξ : ℝ => fourierIntegral (fun t : ℝ => ψ t) ξ)
  set ψTimeMem := SchwartzMap.memLp ψ (p := (2 : ℝ≥0∞)) (μ := volume)
  set ψTime : Lp ℂ 2 volume := ψTimeMem.toLp (fun t : ℝ => ψ t)

  -- Identify the frequency inner product with the time inner product.
  have h_inner_eq :
      ∀ n,
        @inner ℂ (Lp ℂ 2 volume) _ ψFreq (ψLp n)
          = @inner ℂ (Lp ℂ 2 volume) _ ψTime (φLp n) := by
    intro n
    -- Identify both inner products with explicit integral expressions.
    have hψLp_eq :
        (fun ξ => (ψLp n : ℝ → ℂ) ξ) =ᵐ[volume] fun ξ => ψFun n ξ :=
      MemLp.coeFn_toLp (hψ_mem n)
    have hψFreq_eq :
        (fun ξ => (ψFreq : ℝ → ℂ) ξ) =ᵐ[volume]
          fun ξ => fourierIntegral (fun t : ℝ => ψ t) ξ :=
      MemLp.coeFn_toLp ψFreqMem
    have hψFreq_conj : (fun ξ => conj (ψFreq ξ))
        =ᵐ[volume] fun ξ => conj (fourierIntegral (fun t : ℝ => ψ t) ξ) :=
      hψFreq_eq.mono <| by
        intro ξ hξ
        simp [hξ]
    have h_freq :
        @inner ℂ (Lp ℂ 2 volume) _ ψFreq (ψLp n)
          = ∫ ξ : ℝ,
              fourierIntegral (fun t : ℝ => φ n t) ξ
                * conj (fourierIntegral (fun t : ℝ => ψ t) ξ) ∂volume := by
      calc
        @inner ℂ (Lp ℂ 2 volume) _ ψFreq (ψLp n)
            = ∫ ξ : ℝ, (ψLp n ξ) * conj (ψFreq ξ) ∂volume := by
              simpa [ψLp, ψFreq, RCLike.inner_apply]
                using (MeasureTheory.L2.inner_def (𝕜 := ℂ) (μ := volume)
                  (f := ψFreq) (g := ψLp n))
        _ = ∫ ξ : ℝ, ψFun n ξ
              * conj (fourierIntegral (fun t : ℝ => ψ t) ξ) ∂volume := by
              refine integral_congr_ae (Filter.EventuallyEq.mul hψLp_eq hψFreq_conj)
        _ = ∫ ξ : ℝ, fourierIntegral (fun t : ℝ => φ n t) ξ
              * conj (fourierIntegral (fun t : ℝ => ψ t) ξ) ∂volume := by
              simp [ψFun]
    have hφLp_eq :
        (fun t => (φLp n : ℝ → ℂ) t) =ᵐ[volume] fun t => φ n t :=
      MemLp.coeFn_toLp (hφ_L2 n)
    have hψTime_eq :
        (fun t => (ψTime : ℝ → ℂ) t) =ᵐ[volume] fun t => ψ t :=
      MemLp.coeFn_toLp ψTimeMem
    have hψTime_conj : (fun t => conj (ψTime t))
        =ᵐ[volume] fun t => conj (ψ t) :=
      hψTime_eq.mono <| by
        intro t ht
        simp [ht]
    have h_time_inner :
        @inner ℂ (Lp ℂ 2 volume) _ ψTime (φLp n)
          = ∫ t : ℝ, φ n t * conj (ψ t) ∂volume := by
      calc
        @inner ℂ (Lp ℂ 2 volume) _ ψTime (φLp n)
            = ∫ t : ℝ, (φLp n t) * conj (ψTime t) ∂volume := by
              simpa [φLp, ψTime, RCLike.inner_apply]
                using (MeasureTheory.L2.inner_def (𝕜 := ℂ) (μ := volume)
                  (f := ψTime) (g := φLp n))
        _ = ∫ t : ℝ, φ n t * conj (ψ t) ∂volume := by
              refine integral_congr_ae (Filter.EventuallyEq.mul hφLp_eq hψTime_conj)
    have h_time :=
      fourierIntegral_inner_schwartz_conj
        (f := fun t : ℝ => φ n t)
        (hf_L1 := hφ_L1 n) (ψ := ψ)
    simpa [h_freq, h_time_inner] using h_time

  -- Transfer convergence along the time-side sequence.
  have h_time_limit :=
    (tendsto_inner_const_right_of_L2_tendsto hφLp_tendsto ψTime)
  have h_time_limit_left :
      Filter.Tendsto (fun n =>
          @inner ℂ (Lp ℂ 2 volume) _ ψTime (φLp n))
        Filter.atTop
        (𝓝 (@inner ℂ (Lp ℂ 2 volume) _ ψTime fLp)) := by
    have h_conj : Filter.Tendsto
        (fun n => (starRingEnd ℂ) (inner ℂ (φLp n) ψTime)) Filter.atTop
        (𝓝 ((starRingEnd ℂ) (inner ℂ fLp ψTime))) :=
      (Complex.continuous_conj.tendsto
          (@inner ℂ (Lp ℂ 2 volume) _ fLp ψTime)).comp h_time_limit
    have h_time_limit_left' : Filter.Tendsto
        (fun n => inner ℂ ψTime (φLp n)) Filter.atTop
        (𝓝 ((starRingEnd ℂ) (inner ℂ fLp ψTime))) := by
      refine Filter.Tendsto.congr'
          (Filter.Eventually.of_forall fun n => by
            simp [inner_conj_symm]) h_conj
    simpa [inner_conj_symm] using h_time_limit_left'
  have h_freq_limit :
      Filter.Tendsto (fun n =>
          @inner ℂ (Lp ℂ 2 volume) _ ψFreq (ψLp n))
        Filter.atTop
        (𝓝 (@inner ℂ (Lp ℂ 2 volume) _ ψTime fLp)) := by
    simpa [h_inner_eq] using h_time_limit_left

  -- Evaluate the limit explicitly.
  have hfLp_eq :
      (fun t => (fLp : ℝ → ℂ) t) =ᵐ[volume] f := MemLp.coeFn_toLp hf_L2
  have hψTime_eq :
      (fun t => (ψTime : ℝ → ℂ) t) =ᵐ[volume] fun t => ψ t :=
    MemLp.coeFn_toLp ψTimeMem
  have hψTime_conj : (fun t => conj (ψTime t))
      =ᵐ[volume] fun t => conj (ψ t) :=
    hψTime_eq.mono <| by
      intro t ht
      simp [ht]
  have h_time_eval :
      @inner ℂ (Lp ℂ 2 volume) _ ψTime fLp
        = ∫ t : ℝ, f t * conj (ψ t) ∂volume := by
    calc
      @inner ℂ (Lp ℂ 2 volume) _ ψTime fLp
          = ∫ t : ℝ, fLp t * conj (ψTime t) ∂volume := by
            simpa [ψTime, fLp, RCLike.inner_apply]
              using (MeasureTheory.L2.inner_def (𝕜 := ℂ) (μ := volume)
                (f := ψTime) (g := fLp))
      _ = ∫ t : ℝ, f t * conj (ψ t) ∂volume := by
            refine integral_congr_ae (Filter.EventuallyEq.mul hfLp_eq hψTime_conj)
  exact h_freq_limit.trans <| by simp [h_time_eval]

lemma fourierIntegral_cauchySeq_of_schwartz_tendsto
    {φ : ℕ → SchwartzMap ℝ ℂ} {f : ℝ → ℂ}
    (hf_L2 : MemLp f 2 volume)
    (hφ_L1 : ∀ n, Integrable (fun t : ℝ => φ n t))
    (hφ_L2 : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume)
    (hφ_tendsto : Filter.Tendsto (fun n =>
        eLpNorm (fun t : ℝ => f t - φ n t) 2 volume) Filter.atTop (𝓝 0)) :
    CauchySeq (fun n =>
        (fourierIntegral_memLp_of_schwartz (φ n)).toLp
          (fun ξ => fourierIntegral (fun t : ℝ => φ n t) ξ)) := by
  -- Set up the objects.
  let ψFun : ℕ → ℝ → ℂ := fun n ξ => fourierIntegral (fun t : ℝ => φ n t) ξ
  have hψ_mem : ∀ n, MemLp (ψFun n) 2 volume := fun n =>
    fourierIntegral_memLp_of_schwartz (φ n)
  let ψLp : ℕ → Lp ℂ 2 volume := fun n => (hψ_mem n).toLp (ψFun n)
  let φLp : ℕ → Lp ℂ 2 volume := fun n => (hφ_L2 n).toLp (fun t : ℝ => φ n t)
  let fLp : Lp ℂ 2 volume := hf_L2.toLp f

  -- The time-side sequence converges.
  have hφLp_tendsto : Filter.Tendsto φLp Filter.atTop (𝓝 fLp) := by
    simpa [φLp, fLp] using toLp_tendsto_of_eLpNorm_tendsto hf_L2 hφ_L2 hφ_tendsto

  refine Metric.cauchySeq_iff.mpr ?_
  intro ε hε_pos
  have hε_halves : (0 : ℝ) < ε / 2 := half_pos hε_pos
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hφLp_tendsto (ε / 2) hε_halves
  refine ⟨N, fun m hm n hn => ?_⟩

  -- Distances on the frequency side agree with the time side.
  have hdiff_mem :
      MemLp (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume :=
    (hψ_mem m).sub (hψ_mem n)
  have hsubψ := MemLp.toLp_sub (hψ_mem m) (hψ_mem n)
  have hnormψ :=
    Lp.norm_toLp (μ := volume)
      (f := fun ξ : ℝ => ψFun m ξ - ψFun n ξ) hdiff_mem
  have hdist_eq :
      dist (ψLp m) (ψLp n)
        = ENNReal.toReal
            (eLpNorm (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume) := by
    calc
      dist (ψLp m) (ψLp n)
          = ‖ψLp m - ψLp n‖ := by simp [dist_eq_norm]
      _ = ‖((hψ_mem m).sub (hψ_mem n)).toLp
            (fun ξ : ℝ => ψFun m ξ - ψFun n ξ)‖ := by
            simpa [ψLp, hsubψ]
      _ = (eLpNorm (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume).toReal := by
            simp
  have hFourier_diff :
      eLpNorm (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume
        = eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume := by
    have hrewrite :
        (fun ξ : ℝ => ψFun m ξ - ψFun n ξ)
          = fun ξ => fourierIntegral
              (fun t : ℝ => φ m t - φ n t) ξ := by
      funext ξ
      have :=
        (fourierIntegral_sub (hf := hφ_L1 m) (hg := hφ_L1 n)
          (ξ := ξ))
      simpa [ψFun, sub_eq_add_neg] using this.symm
    simpa [hrewrite]
      using fourierIntegral_eLpNorm_eq (φ := φ m - φ n)
  have hsubφ := MemLp.toLp_sub (hφ_L2 m) (hφ_L2 n)
  have hnormφ :=
    Lp.norm_toLp (μ := volume)
      (f := fun t : ℝ => φ m t - φ n t)
      ((hφ_L2 m).sub (hφ_L2 n))
  have hdist_phi :
      dist (φLp m) (φLp n)
        = ENNReal.toReal
            (eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume) := by
    calc
      dist (φLp m) (φLp n)
          = ‖φLp m - φLp n‖ := by simp [dist_eq_norm]
      _ = ‖((hφ_L2 m).sub (hφ_L2 n)).toLp
            (fun t : ℝ => φ m t - φ n t)‖ := by
            simpa [φLp, hsubφ]
      _ = (eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume).toReal := by
            simp
  have hψ_val :
      dist (ψLp m) (ψLp n)
        = ENNReal.toReal
            (eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume) := by
    calc
      dist (ψLp m) (ψLp n)
          = ENNReal.toReal
              (eLpNorm (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume) := hdist_eq
      _ = ENNReal.toReal
              (eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume) := by
            simpa [ψFun, sub_eq_add_neg]
              using congrArg ENNReal.toReal hFourier_diff
  have hψφ_eq : dist (ψLp m) (ψLp n) = dist (φLp m) (φLp n) :=
    hψ_val.trans hdist_phi.symm
  have hmε : dist (φLp m) fLp < ε / 2 := hN m hm
  have hnε : dist (φLp n) fLp < ε / 2 := hN n hn
  have hsum_lt : dist (φLp m) fLp + dist (φLp n) fLp < ε := by
    have h := add_lt_add hmε hnε
    have hsum_eq : ε / 2 + ε / 2 = ε := by ring
    simpa [hsum_eq, add_comm, add_left_comm, add_assoc]
      using h
  have htriangle :
      dist (φLp m) (φLp n)
        ≤ dist (φLp m) fLp + dist (φLp n) fLp := by
    simpa [dist_comm]
      using dist_triangle (φLp m) fLp (φLp n)
  have hψ_lt : dist (ψLp m) (ψLp n) < ε := by
    have hφ_lt : dist (φLp m) (φLp n) < ε :=
      lt_of_le_of_lt htriangle hsum_lt
    simpa [hψφ_eq] using hφ_lt
  exact hψ_lt

/-- Continuity of the Fourier integral on `L²`, expressed for an approximating
sequence of Schwartz functions. -/
lemma fourierIntegral_memLp_limit
    {φ : ℕ → SchwartzMap ℝ ℂ} {f : ℝ → ℂ}
    (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (hφ_L1 : ∀ n, Integrable (fun t : ℝ => φ n t))
    (hφ_L2 : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume)
    (hφ_tendsto : Filter.Tendsto (fun n =>
        eLpNorm (fun t : ℝ => f t - φ n t) 2 volume) Filter.atTop (𝓝 0)) :
    MemLp (fun ξ : ℝ => fourierIntegral f ξ) 2 volume := by
  classical
  -- Frequency-side functions associated with the Schwartz approximations.
  let ψFun : ℕ → ℝ → ℂ := fun n ξ => fourierIntegral (fun t : ℝ => φ n t) ξ
  have hψ_mem : ∀ n, MemLp (ψFun n) 2 volume := fun n =>
    fourierIntegral_memLp_of_schwartz (φ n)

  -- L² objects for the time and frequency sides.
  let ψLp : ℕ → Lp ℂ 2 volume := fun n =>
    (hψ_mem n).toLp (ψFun n)
  let φLp : ℕ → Lp ℂ 2 volume := fun n =>
    (hφ_L2 n).toLp (fun t : ℝ => φ n t)
  let fLp : Lp ℂ 2 volume := hf_L2.toLp f

  -- Useful measurability data.
  have hf_meas : AEStronglyMeasurable f volume := hf_L2.aestronglyMeasurable
  have hφ_meas : ∀ n, AEStronglyMeasurable (fun t : ℝ => φ n t) volume := fun n =>
    (SchwartzMap.continuous (φ n)).aestronglyMeasurable

  -- The L²-distance between φₙ and φₘ is controlled by their distance to f.
  have hφ_cauchy := eLpNorm_tendsto_toReal_of_tendsto hf_L2 hφ_L2 hφ_tendsto

  -- The time-side sequence converges to `f` in `L²`.
  have hφLp_tendsto :
      Filter.Tendsto φLp Filter.atTop (𝓝 fLp) := by
    simpa [φLp, fLp] using toLp_tendsto_of_eLpNorm_tendsto hf_L2 hφ_L2 hφ_tendsto

  -- The frequency-side sequence is Cauchy in `L²`.
  have hψ_cauchy : CauchySeq ψLp := by
    simpa [ψLp, ψFun] using
      fourierIntegral_cauchySeq_of_schwartz_tendsto hf_L2 hφ_L1 hφ_L2 hφ_tendsto

  -- Weak limit against Schwartz test functions matches the classical pairing.
  have h_weak_limit :
      ∀ ψ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun n =>
            @inner ℂ (Lp ℂ 2 volume) _
              ((fourierIntegral_memLp_of_schwartz ψ).toLp
                (fun ξ : ℝ => fourierIntegral (fun t : ℝ => ψ t) ξ)) (ψLp n))
          Filter.atTop
          (𝓝 (∫ t : ℝ, f t * conj (ψ t) ∂volume)) := by
    simpa [ψLp] using
      weak_limit_fourierIntegral_of_schwartz_tendsto hf_L2 hφ_L1 hφ_L2 hφ_tendsto

  -- Since ψLp is Cauchy, it converges to some limit in the complete space Lp.
  have hψ_complete : ∃ ψ_lim : Lp ℂ 2 volume, Filter.Tendsto ψLp Filter.atTop (𝓝 ψ_lim) :=
    cauchySeq_tendsto_of_complete hψ_cauchy

  -- Extract the limit and its convergence.
  obtain ⟨ψ_lim, hψ_lim⟩ := hψ_complete

  -- The limit ψ_lim corresponds to a function in L².
  have hψ_lim_mem : MemLp (fun ξ : ℝ => (ψ_lim : ℝ → ℂ) ξ) 2 volume :=
    Lp.memLp ψ_lim

  sorry

-- The Fourier integral sends `L¹ ∩ L²` functions into `L²`.
lemma fourierIntegral_memLp_of_memLp (f : ℝ → ℂ)
    (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume) :
    MemLp (fun ξ : ℝ => fourierIntegral f ξ) 2 volume := by
  classical
  obtain ⟨φ, hφ_L1, hφ_L2, hφ_tendsto⟩ :=
    exists_schwartz_L2_approx f hf_L1 hf_L2
  exact
    fourierIntegral_memLp_limit hf_L1 hf_L2 hφ_L1 hφ_L2 hφ_tendsto

end Approximation

/-- Plancherel identity for `L¹ ∩ L²` functions with the explicit kernel. -/
lemma fourierIntegral_l2_norm (f : ℝ → ℂ)
    (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume) :
    ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume
      = (1 / (2 * Real.pi)) * ∫ ξ : ℝ, ‖fourierIntegral f ξ‖ ^ 2 ∂volume := by
  sorry

end Frourio
