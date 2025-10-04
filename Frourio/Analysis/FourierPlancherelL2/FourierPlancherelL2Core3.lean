import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core2
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

lemma mollifier_convolution_L1_tendsto (f : ℝ → ℂ)
    (hf_compact : HasCompactSupport f) (hf_L1 : Integrable f) (hf_cont : Continuous f) :
    Filter.Tendsto (fun δ : ℝ =>
        eLpNorm (fun t => f t -
          ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 1 volume)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
  classical
  -- Strategy: Use mollifier properties to show convergence
  -- The key is to rewrite f(t) - ∫ φ_δ(y) f(t-y) dy using φ_δ integrates to 1

  have hf_unif : UniformContinuous f :=
    Continuous.uniformContinuous_of_hasCompactSupport hf_cont hf_compact

  -- Get support radius
  obtain ⟨R, hR_pos, hR_support⟩ :=
    HasCompactSupport.exists_radius_closedBall hf_compact

  -- Use the definition of tendsto for nhdsWithin
  refine (Filter.tendsto_iff_forall_eventually_mem).2 ?_
  intro s hs

  -- Since 0 is in the target neighborhood, we can work with a small order interval around 0
  rcases ENNReal.nhds_zero_basis.mem_iff.mp hs with ⟨ε, hε_pos, hε_subset⟩
  classical
  set εR : ℝ := if hε_top : ε = ∞ then 1 else ε.toReal / 2 with hεR_def
  have hεR_pos : 0 < εR := by
    by_cases hε_top : ε = ∞
    · simp [εR, hε_top]
    · have hε_ne_zero : ε ≠ 0 := ne_of_gt hε_pos
      have h_toReal_pos : 0 < ε.toReal := ENNReal.toReal_pos hε_ne_zero hε_top
      have : 0 < ε.toReal / 2 := by
        have := h_toReal_pos
        nlinarith
      simpa [εR, hε_top] using this
  have hεR_nonneg : 0 ≤ εR := by
    by_cases hε_top : ε = ∞
    · simp [εR, hε_top]
    · have h_toReal_nonneg : 0 ≤ ε.toReal := ENNReal.toReal_nonneg
      have : 0 ≤ ε.toReal / 2 := by
        have := h_toReal_nonneg
        nlinarith
      simpa [εR, hε_top] using this
  have hεR_lt : ENNReal.ofReal εR < ε := by
    by_cases hε_top : ε = ∞
    · simp [εR, hε_top]
    · have hε_ne_zero : ε ≠ 0 := ne_of_gt hε_pos
      have h_toReal_pos : 0 < ε.toReal := ENNReal.toReal_pos hε_ne_zero hε_top
      have h_toReal_ne_top : ε ≠ ∞ := hε_top
      have h_half_lt : ε.toReal / 2 < ε.toReal := by
        have := h_toReal_pos
        nlinarith
      have h_nonneg : 0 ≤ ε.toReal / 2 := by
        have := ENNReal.toReal_nonneg (a := ε)
        nlinarith
      have := ENNReal.ofReal_lt_iff_lt_toReal h_nonneg h_toReal_ne_top
      simpa [εR, hε_top] using this.mpr h_half_lt
  have hε_subset' : Set.Iio (ENNReal.ofReal εR) ⊆ s := by
    intro x hx
    refine hε_subset ?_
    exact lt_trans hx hεR_lt

  -- Use uniform continuity to get δ₀
  have h_den_pos : 0 < 4 * R + 2 := by nlinarith [hR_pos]
  have h_ratio_pos : 0 < εR / (4 * R + 2) := by exact div_pos hεR_pos h_den_pos
  obtain ⟨δ₀, hδ₀_pos, h_unif⟩ :=
    Metric.uniformContinuous_iff.mp hf_unif (εR / (4 * R + 2)) h_ratio_pos

  -- Show that eventually in nhdsWithin, the values are in s
  rw [eventually_nhdsWithin_iff]
  have h_ball_pos : 0 < min δ₀ 1 := by
    have hδ₀_pos' : 0 < δ₀ := hδ₀_pos
    have h_one_pos : 0 < (1 : ℝ) := by norm_num
    exact lt_min_iff.mpr ⟨hδ₀_pos', h_one_pos⟩
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds (x := 0) (ε := min δ₀ 1) h_ball_pos) ?_
  intro δ hδ_ball hδ_pos

  -- δ is in the ball and positive
  simp [Metric.mem_ball, Real.dist_eq] at hδ_ball
  have hδ_abs : |δ| < min δ₀ 1 :=
    lt_min_iff.mpr ⟨hδ_ball.1, hδ_ball.2⟩
  have hδ_bound : δ < min δ₀ 1 := by
    have := abs_lt.mp hδ_abs
    exact this.2

  -- Key inequality: use mollifier integral = 1 to rewrite the difference
  have h_mol_int := mollifier_self_convolution_eq_one δ hδ_pos

  have h_mol_int_complex :
      ∫ x, (create_mollifier δ x : ℂ) ∂volume = (1 : ℂ) := by
    simp [h_mol_int, Complex.ofReal_one]

  -- Rewrite f(t) = ∫ φ_δ(y) f(t) dy using the normalization of the mollifier
  have h_rewrite : ∀ t, f t = ∫ y, (create_mollifier δ y : ℂ) * f t ∂volume := by
    intro t
    calc
      f t = (1 : ℂ) * f t := by simp
      _ = (∫ y, (create_mollifier δ y : ℂ) ∂volume) * f t := by
        simp [h_mol_int_complex]
      _ = ∫ y, (create_mollifier δ y : ℂ) * f t ∂volume := by
        simpa using
          (MeasureTheory.integral_mul_const (μ := volume)
            (f := fun y => (create_mollifier δ y : ℂ)) (r := f t)).symm

  have h_mollifier_integrable_real :
      Integrable (fun y : ℝ => create_mollifier δ y) := by
    classical
    have hδ_pos' : 0 < δ := by
      have : δ ∈ Set.Ioi (0 : ℝ) := hδ_pos
      simpa [Set.mem_Ioi] using this
    set S := Set.Ioo (-δ) δ with hS_def
    have hS_meas : MeasurableSet S := by simp [hS_def]
    obtain ⟨-, h_integrableOn⟩ := mollifier_normalized_integral δ hδ_pos'
    have h_indicator_int :
        Integrable
          (fun y : ℝ =>
            Set.indicator S (fun y : ℝ => create_mollifier δ y) y) := by
      exact
        (integrable_indicator_iff (μ := volume) (s := S)
            (f := fun y : ℝ => create_mollifier δ y) hS_meas).2
          h_integrableOn
    have h_indicator_eq :
        (fun y : ℝ =>
            Set.indicator S (fun y : ℝ => create_mollifier δ y) y)
          =ᵐ[volume] fun y : ℝ => create_mollifier δ y := by
      refine Filter.Eventually.of_forall ?_
      intro y
      by_cases hy : y ∈ S
      · simp [Set.indicator_of_mem, hy]
      · have h_not : ¬ |y| < δ := by
          intro h_lt
          apply hy
          have h_pair := abs_lt.mp h_lt
          simpa [hS_def, Set.mem_Ioo] using h_pair
        have h_zero : create_mollifier δ y = 0 := by
          simp [create_mollifier, h_not]
        simp [Set.indicator_of_notMem, hy, h_zero]
    exact h_indicator_int.congr h_indicator_eq

  have h_mollifier_integrable_complex :
      Integrable (fun y : ℝ => (create_mollifier δ y : ℂ)) :=
    h_mollifier_integrable_real.ofReal

  have h_const_integrable :
      ∀ t : ℝ,
        Integrable (fun y : ℝ => (create_mollifier δ y : ℂ) * f t) := by
    intro t
    simpa using h_mollifier_integrable_complex.mul_const (f t)

  have h_shift_integrable :
      ∀ t : ℝ,
        Integrable (fun y : ℝ => (create_mollifier δ y : ℂ) * f (t - y)) := by
    intro t
    classical
    have hδ_pos' : 0 < δ := by
      have : δ ∈ Set.Ioi (0 : ℝ) := hδ_pos
      simpa [Set.mem_Ioi] using this
    obtain ⟨C, hC_pos, hC_bound⟩ := create_mollifier_le_bound δ hδ_pos'
    have h_shift : Integrable (fun y : ℝ => f (t - y)) :=
      integrable_comp_sub hf_L1 (x := t)
    have h_memLp :
        MemLp (fun y : ℝ => (create_mollifier δ y : ℂ)) ∞ volume := by
      have h_meas :
          AEStronglyMeasurable (fun y : ℝ => (create_mollifier δ y : ℂ)) volume :=
        (Complex.measurable_ofReal.comp (create_mollifier_measurable δ)).aestronglyMeasurable
      refine memLp_top_of_bound h_meas (C := C) ?_
      refine Filter.Eventually.of_forall ?_
      intro y
      have h_abs : |create_mollifier δ y| = create_mollifier δ y :=
        abs_create_mollifier _ _
      simpa [Complex.norm_ofReal, h_abs] using hC_bound y
    have h_smul :=
      Integrable.smul_of_top_right (μ := volume)
        (f := fun y : ℝ => f (t - y))
        (φ := fun y : ℝ => (create_mollifier δ y : ℂ))
        h_shift h_memLp
    simpa [smul_eq_mul] using h_smul

  -- Now the difference becomes ∫ φ_δ(y) [f(t) - f(t-y)] dy
  have h_diff : ∀ t, f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume
      = ∫ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) ∂volume := by
    intro t
    have h_lhs :
        f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume
          =
            (∫ y, (create_mollifier δ y : ℂ) * f t ∂volume)
              - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume := by
      simpa using
        congrArg
          (fun z : ℂ =>
            z - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume)
          (h_rewrite t)
    have h_const_integrable' := h_const_integrable t
    have h_shift_integrable' := h_shift_integrable t
    have h_sub :=
      MeasureTheory.integral_sub h_const_integrable' h_shift_integrable'
    have h_eq :
        (fun y : ℝ =>
            (create_mollifier δ y : ℂ) * f t -
              (create_mollifier δ y : ℂ) * f (t - y))
          = fun y : ℝ =>
              (create_mollifier δ y : ℂ) * (f t - f (t - y)) := by
      funext y
      simp [mul_sub]
    exact h_lhs.trans <| (by simpa [Pi.sub_def, h_eq] using h_sub.symm)

  -- Use L¹ norm estimate
  have h_mem_Iio :
      eLpNorm
          (fun t => f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 1 volume
        ∈ Set.Iio (ENNReal.ofReal εR) := by
    have h_congr :
        (fun t => f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume)
            = fun t => ∫ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) ∂volume := by
      funext t
      exact h_diff t
    have h_bound :
        eLpNorm
            (fun t => ∫ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) ∂volume) 1 volume
          < ENNReal.ofReal εR := by
      classical
      set g := fun t : ℝ =>
        ∫ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) ∂volume with hg_def
      set Cε : ℝ := εR / (4 * R + 2) with hCε_def

      have hCε_pos : 0 < Cε := by
        simpa [hCε_def] using h_ratio_pos
      have hCε_nonneg : 0 ≤ Cε := hCε_pos.le

      have hδ_lt_one : δ < (1 : ℝ) :=
        lt_of_lt_of_le hδ_bound (min_le_right _ _)

      have hf_zero : ∀ {x : ℝ}, R < |x| → f x = 0 := by
        intro x hx
        have hx_not_ball : x ∉ Metric.closedBall (0 : ℝ) R := by
          intro hx_ball
          have hx_le : |x| ≤ R := by
            simpa [Metric.mem_closedBall, Real.dist_eq] using hx_ball
          have : R < R := lt_of_lt_of_le hx hx_le
          exact (lt_irrefl _ this).elim
        have hx_not_support : x ∉ tsupport f := by
          intro hx_support
          exact hx_not_ball (hR_support hx_support)
        exact image_eq_zero_of_notMem_tsupport hx_not_support

      have h_pointwise : ∀ t, ‖g t‖ ≤ Cε := by
        intro t
        have h_const_integrable' := h_const_integrable t
        have h_shift_integrable' := h_shift_integrable t
        have h_diff_integrable' := h_const_integrable'.sub h_shift_integrable'
        have h_diff_eq :
            (fun y : ℝ =>
                (create_mollifier δ y : ℂ) * f t -
                  (create_mollifier δ y : ℂ) * f (t - y))
              =ᵐ[volume]
              (fun y : ℝ =>
                (create_mollifier δ y : ℂ) * (f t - f (t - y))) := by
          refine Filter.Eventually.of_forall ?_
          intro y
          simp [mul_sub]
        have h_diff_integrable :
            Integrable
              (fun y : ℝ => (create_mollifier δ y : ℂ) * (f t - f (t - y))) :=
          h_diff_integrable'.congr h_diff_eq

        have h_norm_le :
            ‖g t‖
              ≤ ∫ y, create_mollifier δ y * ‖f t - f (t - y)‖ ∂volume := by
          have :=
            norm_integral_le_integral_norm (μ := volume)
              (fun y : ℝ => (create_mollifier δ y : ℂ) * (f t - f (t - y)))
          simpa [hg_def, norm_mul, norm_complex_create_mollifier,
            abs_create_mollifier]
            using this

        have h_bound_integrand :
            ∀ y : ℝ,
              create_mollifier δ y * ‖f t - f (t - y)‖
                ≤ create_mollifier δ y * Cε := by
          intro y
          have hcm_nonneg : 0 ≤ create_mollifier δ y :=
            create_mollifier_nonneg δ y
          by_cases hy_zero : create_mollifier δ y = 0
          · simp [hy_zero, hcm_nonneg]
          · have hy_abs_lt : |y| < δ := by
              by_contra hy_abs
              have : create_mollifier δ y = 0 := by
                simp [create_mollifier, hy_abs]
              exact hy_zero this
            have hy_lt_delta0 : |y| < δ₀ := by
              have hδ_lt_delta0 : δ < δ₀ :=
                lt_of_lt_of_le hδ_bound (min_le_left _ _)
              exact lt_of_lt_of_le hy_abs_lt hδ_lt_delta0.le
            have h_dist : dist t (t - y) < δ₀ := by
              simpa [Real.dist_eq, abs_sub_comm] using hy_lt_delta0
            have h_uc := h_unif h_dist
            have h_norm_lt : ‖f t - f (t - y)‖ < Cε := by
              simpa [hCε_def, Complex.dist_eq, sub_eq_add_neg] using h_uc
            have h_norm_le : ‖f t - f (t - y)‖ ≤ Cε := le_of_lt h_norm_lt
            have :
                create_mollifier δ y * ‖f t - f (t - y)‖
                  ≤ create_mollifier δ y * Cε := by
              exact mul_le_mul_of_nonneg_left h_norm_le hcm_nonneg
            simpa using this

        have h_integrable_left :
            Integrable
              (fun y : ℝ => create_mollifier δ y * ‖f t - f (t - y)‖) := by
          have := h_diff_integrable.norm
          simpa [norm_mul, norm_complex_create_mollifier, abs_create_mollifier]
            using this

        have h_integrable_right :
            Integrable (fun y : ℝ => create_mollifier δ y * Cε) := by
          simpa using h_mollifier_integrable_real.mul_const (c := Cε)

        have h_int_le :
            ∫ y, create_mollifier δ y * ‖f t - f (t - y)‖ ∂volume
              ≤ ∫ y, create_mollifier δ y * Cε ∂volume := by
          refine MeasureTheory.integral_mono_ae
              h_integrable_left h_integrable_right ?_
          refine Filter.Eventually.of_forall h_bound_integrand

        have h_int_right :
            ∫ y, create_mollifier δ y * Cε ∂volume = Cε := by
          have h_integral :=
            MeasureTheory.integral_mul_const (μ := volume)
              (f := fun y : ℝ => create_mollifier δ y) Cε
          simpa [Cε, hCε_def, h_mol_int, mul_comm, mul_left_comm, mul_assoc]
            using h_integral

        have h_norm_le' :
            ‖g t‖ ≤ Cε := by
          have := le_trans h_norm_le (le_trans h_int_le (le_of_eq h_int_right))
          simpa [hg_def] using this
        exact h_norm_le'

      have h_support_g :
          ∀ ⦃t⦄, R + 1 < |t| → g t = 0 := by
        intro t ht
        have hR_lt_abs : R < |t| := by
          have hR_lt : R < R + 1 := by linarith
          exact lt_trans hR_lt ht
        have hf_t : f t = 0 := hf_zero hR_lt_abs
        have h_integrand_zero :
            ∀ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) = 0 := by
          intro y
          by_cases hy_zero : create_mollifier δ y = 0
          · simp [hy_zero, hf_t]
          · have hy_abs_lt : |y| < δ := by
              by_contra hy_abs
              have : create_mollifier δ y = 0 := by
                simp [create_mollifier, hy_abs]
              exact hy_zero this
            have hy_lt_one : |y| < 1 := lt_of_lt_of_le hy_abs_lt hδ_lt_one.le
            have hR_lt_sub : R < |t - y| := by
              have hR_add_lt : R + |y| < |t| := by
                have h_aux : R + |y| < R + 1 := by
                  have := add_lt_add_left hy_lt_one R
                  simpa [add_comm, add_left_comm, add_assoc] using this
                exact lt_trans h_aux ht
              have h_gt : R < |t| - |y| := (lt_sub_iff_add_lt).2 hR_add_lt
              have h_one_le_abs_t : (1 : ℝ) ≤ |t| := by
                have : (1 : ℝ) ≤ R + 1 := by nlinarith [hR_pos]
                exact le_trans this (le_of_lt ht)
              have hy_le_abs_t : |y| ≤ |t| := le_trans hy_lt_one.le h_one_le_abs_t
              have h_nonneg : 0 ≤ |t| - |y| := sub_nonneg.mpr hy_le_abs_t
              have h_abs_le : |t| - |y| ≤ |t - y| := by
                have h_aux := abs_sub_abs_le_abs_sub t y
                have h_abs_eq : |t| - |y| = |t| - |y| := by
                  simp [abs_of_nonneg h_nonneg]
                simpa [h_abs_eq] using h_aux
              exact lt_of_lt_of_le h_gt h_abs_le
            have hf_ty : f (t - y) = 0 := hf_zero hR_lt_sub
            simp [hf_t, hf_ty]
        have h_integrand_zero' :
            (fun y : ℝ => (create_mollifier δ y : ℂ) * (f t - f (t - y))) = 0 := by
          funext y; exact h_integrand_zero y
        simp [hg_def, h_integrand_zero']

      let S : Set ℝ := Metric.closedBall (0 : ℝ) (R + 1)

      have h_indicator_eq :
          (fun t : ℝ => ENNReal.ofReal ‖g t‖)
            = Set.indicator S (fun t : ℝ => ENNReal.ofReal ‖g t‖) := by
        funext t
        by_cases ht : t ∈ S
        · simp [ht]
        · have ht_abs : R + 1 < |t| := by
            simpa [S, Metric.mem_closedBall, Real.dist_eq, not_le] using ht
          have hg_zero : g t = 0 := h_support_g ht_abs
          simp [ht, hg_zero]

      have hS_meas : MeasurableSet S := (Metric.isClosed_closedBall).measurableSet

      have h_indicator_le :
          (fun t : ℝ => ENNReal.ofReal ‖g t‖)
            ≤ᵐ[volume]
              Set.indicator S (fun _ : ℝ => ENNReal.ofReal Cε) := by
        refine Filter.Eventually.of_forall ?_
        intro t
        by_cases ht : t ∈ S
        · have h_norm := h_pointwise t
          have h_norm' : ENNReal.ofReal ‖g t‖ ≤ ENNReal.ofReal Cε := by
            refine (ENNReal.ofReal_le_ofReal_iff hCε_nonneg).2 ?_
            simpa using h_norm
          have h_norm'' : ↑‖g t‖₊ ≤ ENNReal.ofReal Cε := by
            simpa using h_norm'
          simp [h_indicator_eq, ht, h_norm'', hCε_nonneg]
        · have ht_abs : R + 1 < |t| := by
            simpa [S, Metric.mem_closedBall, Real.dist_eq, not_le] using ht
          have hg_zero : g t = 0 := h_support_g ht_abs
          simp [h_indicator_eq, ht, hg_zero, hCε_nonneg]

      have h_lintegral_le :
          ∫⁻ t, ENNReal.ofReal ‖g t‖ ∂volume
            ≤ ∫⁻ t, Set.indicator S (fun _ : ℝ => ENNReal.ofReal Cε) t ∂volume :=
        lintegral_mono_ae h_indicator_le

      have h_volume : volume S = ENNReal.ofReal (2 * (R + 1)) := by
        simp [S, two_mul, add_comm, add_left_comm, add_assoc]

      have h_lintegral_const :
          ∫⁻ t, Set.indicator S (fun _ : ℝ => ENNReal.ofReal Cε) t ∂volume
            = ENNReal.ofReal Cε * volume S := by
        simp [hS_meas, h_volume, hCε_nonneg]

      have h_norm_le_const :
          eLpNorm g 1 volume
              ≤ ENNReal.ofReal Cε * volume S := by
        have :=
          calc
            eLpNorm g 1 volume
                = ∫⁻ t, ENNReal.ofReal ‖g t‖ ∂volume := by
                    simp [hg_def, eLpNorm_one_eq_lintegral_enorm]
            _ ≤ ∫⁻ t, Set.indicator S (fun _ : ℝ => ENNReal.ofReal Cε) t ∂volume :=
                    h_lintegral_le
            _ = ENNReal.ofReal Cε * volume S := h_lintegral_const
        exact this

      have h_product_lt :
          ENNReal.ofReal Cε * volume S < ENNReal.ofReal εR := by
        have h_real_lt : Cε * (2 * (R + 1)) < εR := by
          have h_den_pos' : 0 < 4 * R + 2 := by
            simpa using h_den_pos
          have h_ratio_lt_one : 2 * (R + 1) < 4 * R + 2 := by
            nlinarith [hR_pos]
          have h_ratio_lt_one' :
              (2 * (R + 1)) / (4 * R + 2) < 1 :=
            (div_lt_one h_den_pos').2 h_ratio_lt_one
          have hεR_pos' : 0 < εR := hεR_pos
          calc
            Cε * (2 * (R + 1))
                = εR * ((2 * (R + 1)) / (4 * R + 2)) := by
                    simp [Cε, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
            _ < εR * 1 := by
                    exact mul_lt_mul_of_pos_left h_ratio_lt_one' hεR_pos'
            _ = εR := by simp
        have h_pos_mul : 0 ≤ 2 * (R + 1) := by nlinarith [hR_pos]
        have h_lt :
            ENNReal.ofReal (Cε * (2 * (R + 1))) < ENNReal.ofReal εR :=
          (ENNReal.ofReal_lt_ofReal_iff hεR_pos).2 h_real_lt
        simpa [h_volume, ENNReal.ofReal_mul hCε_nonneg, h_pos_mul]
          using h_lt

      refine lt_of_le_of_lt h_norm_le_const h_product_lt
    have h_lt :
        eLpNorm
            (fun t => f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 1 volume
          < ENNReal.ofReal εR := by
      simpa [h_congr] using h_bound
    simpa [Set.mem_Iio] using h_lt
  exact hε_subset' h_mem_Iio

lemma mollifier_convolution_L2_tendsto (f : ℝ → ℂ)
    (hf_compact : HasCompactSupport f) (hf_L1 : Integrable f) (hf_cont : Continuous f) :
    Filter.Tendsto (fun δ : ℝ =>
        eLpNorm (fun t => f t -
          ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 2 volume)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
  classical

  have hf_unif : UniformContinuous f :=
    Continuous.uniformContinuous_of_hasCompactSupport hf_cont hf_compact

  obtain ⟨R, hR_pos, hR_support⟩ :=
    HasCompactSupport.exists_radius_closedBall hf_compact

  refine (Filter.tendsto_iff_forall_eventually_mem).2 ?_
  intro s hs

  rcases ENNReal.nhds_zero_basis.mem_iff.mp hs with ⟨ε, hε_pos, hε_subset⟩
  set εR : ℝ := if hε_top : ε = ∞ then 1 else ε.toReal / 2 with hεR_def
  have hεR_pos : 0 < εR := by
    by_cases hε_top : ε = ∞
    · simp [εR, hε_top]
    · have hε_ne_zero : ε ≠ 0 := ne_of_gt hε_pos
      have h_toReal_pos : 0 < ε.toReal := ENNReal.toReal_pos hε_ne_zero hε_top
      have : 0 < ε.toReal / 2 := by
        have := h_toReal_pos
        nlinarith
      simpa [εR, hε_top] using this
  have hεR_nonneg : 0 ≤ εR := hεR_pos.le
  have hεR_lt : ENNReal.ofReal εR < ε := by
    by_cases hε_top : ε = ∞
    · simp [εR, hε_top]
    · have hε_ne_zero : ε ≠ 0 := ne_of_gt hε_pos
      have h_toReal_pos : 0 < ε.toReal := ENNReal.toReal_pos hε_ne_zero hε_top
      have h_half_lt : ε.toReal / 2 < ε.toReal := by
        have := h_toReal_pos
        nlinarith
      have h_nonneg : 0 ≤ ε.toReal / 2 := by
        have := ENNReal.toReal_nonneg (a := ε)
        nlinarith
      have := ENNReal.ofReal_lt_iff_lt_toReal h_nonneg hε_top
      simpa [εR, hε_top] using this.mpr h_half_lt
  have hε_subset' : Set.Iio (ENNReal.ofReal εR) ⊆ s := by
    intro x hx
    refine hε_subset ?_
    exact lt_trans hx hεR_lt

  have h_den_pos : 0 < 4 * R + 2 := by nlinarith [hR_pos]
  have h_ratio_pos : 0 < εR / (4 * R + 2) := div_pos hεR_pos h_den_pos
  obtain ⟨δ₀, hδ₀_pos, h_unif⟩ :=
    Metric.uniformContinuous_iff.mp hf_unif (εR / (4 * R + 2)) h_ratio_pos

  rw [eventually_nhdsWithin_iff]
  have h_ball_pos : 0 < min δ₀ 1 :=
    lt_min_iff.mpr ⟨hδ₀_pos, show (0 : ℝ) < 1 by norm_num⟩
  refine Filter.eventually_of_mem
      (Metric.ball_mem_nhds (x := 0) (ε := min δ₀ 1) h_ball_pos) ?_
  intro δ hδ_ball hδ_pos

  simp [Metric.mem_ball, Real.dist_eq] at hδ_ball
  have hδ_abs : |δ| < min δ₀ 1 := lt_min_iff.mpr ⟨hδ_ball.1, hδ_ball.2⟩
  have hδ_bound : δ < min δ₀ 1 :=
    let ⟨h_neg, h_pos⟩ := abs_lt.mp hδ_abs
    h_pos

  have h_mol_int := mollifier_self_convolution_eq_one δ hδ_pos
  have h_mol_int_complex :
      ∫ x, (create_mollifier δ x : ℂ) ∂volume = 1 :=
    by simpa [Complex.ofReal_one] using h_mol_int

  have h_rewrite : ∀ t, f t = ∫ y, (create_mollifier δ y : ℂ) * f t ∂volume := by
    intro t
    calc
      f t = (1 : ℂ) * f t := by simp
      _ = (∫ y, (create_mollifier δ y : ℂ) ∂volume) * f t := by
        simp [h_mol_int_complex]
      _ = ∫ y, (create_mollifier δ y : ℂ) * f t ∂volume := by
        simpa using
          (MeasureTheory.integral_mul_const (μ := volume)
            (f := fun y => (create_mollifier δ y : ℂ)) (r := f t)).symm

  have h_mollifier_integrable_real : Integrable (fun y : ℝ => create_mollifier δ y) := by
    have hδ_pos' : 0 < δ := hδ_pos
    set S := Set.Ioo (-δ) δ with hS_def
    have hS_meas : MeasurableSet S := by simp [hS_def]
    obtain ⟨-, h_integrableOn⟩ := mollifier_normalized_integral δ hδ_pos'
    have h_indicator_int :
        Integrable
          (fun y : ℝ =>
            Set.indicator S (fun y : ℝ => create_mollifier δ y) y) := by
      exact
        (integrable_indicator_iff (μ := volume) (s := S)
            (f := fun y => create_mollifier δ y) hS_meas).2 h_integrableOn
    have h_indicator_eq :
        (fun y : ℝ =>
            Set.indicator S (fun y : ℝ => create_mollifier δ y) y)
          =ᵐ[volume] fun y : ℝ => create_mollifier δ y := by
      refine Filter.Eventually.of_forall ?_
      intro y
      by_cases hy : y ∈ S
      · simp [Set.indicator_of_mem, hy]
      · have h_not : ¬ |y| < δ := by
          intro h_lt
          apply hy
          have h_pair := abs_lt.mp h_lt
          simpa [hS_def, Set.mem_Ioo] using h_pair
        have h_zero : create_mollifier δ y = 0 := by
          simp [create_mollifier, h_not]
        simp [Set.indicator_of_notMem, hy, h_zero]
    exact h_indicator_int.congr h_indicator_eq

  have h_mollifier_integrable_complex :
      Integrable (fun y : ℝ => (create_mollifier δ y : ℂ)) :=
    h_mollifier_integrable_real.ofReal

  have h_const_integrable :
      ∀ t, Integrable (fun y : ℝ => (create_mollifier δ y : ℂ) * f t) := by
    intro t
    simpa using h_mollifier_integrable_complex.mul_const (f t)

  have h_shift_integrable :
      ∀ t, Integrable (fun y : ℝ => (create_mollifier δ y : ℂ) * f (t - y)) := by
    intro t
    obtain ⟨C, hC_pos, hC_bound⟩ :=
      create_mollifier_le_bound δ
        (by
          have : δ ∈ Set.Ioi (0 : ℝ) := hδ_pos
          simpa [Set.mem_Ioi] using this)
    have h_shift := integrable_comp_sub hf_L1 (x := t)
    have h_memLp :
        MemLp (fun y : ℝ => (create_mollifier δ y : ℂ)) ∞ volume := by
      have h_meas :
          AEStronglyMeasurable (fun y : ℝ => (create_mollifier δ y : ℂ)) volume :=
        (Complex.measurable_ofReal.comp (create_mollifier_measurable δ)).aestronglyMeasurable
      exact memLp_top_of_bound h_meas (C := C)
        (Filter.Eventually.of_forall fun y => by
          have h_abs : |create_mollifier δ y| = create_mollifier δ y :=
            abs_create_mollifier _ _
          simpa [Complex.norm_ofReal, h_abs] using hC_bound y)
    simpa [smul_eq_mul] using
      Integrable.smul_of_top_right (f := fun y => f (t - y))
        (φ := fun y => (create_mollifier δ y : ℂ)) h_shift h_memLp

  have h_diff : ∀ t,
      f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume
        = ∫ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) ∂volume := by
    intro t
    have h_lhs :
        f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume =
          (∫ y, (create_mollifier δ y : ℂ) * f t ∂volume)
            - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume := by
      simpa using
        congrArg
          (fun z : ℂ =>
            z - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume)
          (h_rewrite t)
    have h_sub :=
      MeasureTheory.integral_sub (h_const_integrable t) (h_shift_integrable t)
    have h_eq :
        (fun y : ℝ =>
            (create_mollifier δ y : ℂ) * f t -
              (create_mollifier δ y : ℂ) * f (t - y))
          = fun y : ℝ =>
              (create_mollifier δ y : ℂ) * (f t - f (t - y)) := by
      funext y; simp [mul_sub]
    exact h_lhs.trans <| (by simpa [Pi.sub_def, h_eq] using h_sub.symm)

  have h_mem_Iio :
      eLpNorm
          (fun t => f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 2 volume
        ∈ Set.Iio (ENNReal.ofReal εR) := by
    have h_congr :
        (fun t => f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume)
            = fun t => ∫ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) ∂volume := by
      funext t; exact h_diff t
    have h_bound :
        eLpNorm
            (fun t => ∫ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) ∂volume) 2 volume
          < ENNReal.ofReal εR := by
      classical
      set g := fun t : ℝ =>
        ∫ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) ∂volume with hg_def
      set Cε : ℝ := εR / (4 * R + 2) with hCε_def

      have hCε_pos : 0 < Cε := by
        simpa [hCε_def] using h_ratio_pos
      have hCε_nonneg : 0 ≤ Cε := hCε_pos.le

      have hδ_lt_one : δ < 1 :=
        lt_of_lt_of_le hδ_bound (min_le_right _ _)

      have hf_zero : ∀ {x : ℝ}, R < |x| → f x = 0 := by
        intro x hx
        have hx_not_ball : x ∉ Metric.closedBall (0 : ℝ) R := by
          intro hx_ball
          have hx_le : |x| ≤ R := by
            simpa [Metric.mem_closedBall, Real.dist_eq] using hx_ball
          have : R < R := lt_of_lt_of_le hx hx_le
          exact (lt_irrefl _ this).elim
        have hx_not_support : x ∉ tsupport f := by
          intro hx_support
          exact hx_not_ball (hR_support hx_support)
        exact image_eq_zero_of_notMem_tsupport hx_not_support

      have h_pointwise : ∀ t, ‖g t‖ ≤ Cε := by
        intro t
        have h_const_integrable' := h_const_integrable t
        have h_shift_integrable' := h_shift_integrable t
        have h_diff_integrable' := h_const_integrable'.sub h_shift_integrable'
        have h_diff_eq :
            (fun y : ℝ =>
                (create_mollifier δ y : ℂ) * f t -
                  (create_mollifier δ y : ℂ) * f (t - y))
              =ᵐ[volume]
              (fun y : ℝ =>
                (create_mollifier δ y : ℂ) * (f t - f (t - y))) := by
          refine Filter.Eventually.of_forall ?_
          intro y; simp [mul_sub]
        have h_diff_integrable :
            Integrable
              (fun y : ℝ => (create_mollifier δ y : ℂ) * (f t - f (t - y))) :=
          h_diff_integrable'.congr h_diff_eq

        have h_norm_le :
            ‖g t‖
              ≤ ∫ y, create_mollifier δ y * ‖f t - f (t - y)‖ ∂volume := by
          have :=
            norm_integral_le_integral_norm (μ := volume)
              (fun y : ℝ => (create_mollifier δ y : ℂ) * (f t - f (t - y)))
          simpa [hg_def, norm_mul, norm_complex_create_mollifier,
            abs_create_mollifier]
            using this

        have h_bound_integrand :
            ∀ y : ℝ,
              create_mollifier δ y * ‖f t - f (t - y)‖
                ≤ create_mollifier δ y * Cε := by
          intro y
          have hcm_nonneg : 0 ≤ create_mollifier δ y :=
            create_mollifier_nonneg δ y
          by_cases hy_zero : create_mollifier δ y = 0
          · simp [hy_zero, hcm_nonneg]
          · have hy_abs_lt : |y| < δ := by
              by_contra hy_abs
              have : create_mollifier δ y = 0 := by
                simp [create_mollifier, hy_abs]
              exact hy_zero this
            have hy_lt_delta0 : |y| < δ₀ := by
              have hδ_lt_delta0 : δ < δ₀ :=
                lt_of_lt_of_le hδ_bound (min_le_left _ _)
              exact lt_of_lt_of_le hy_abs_lt hδ_lt_delta0.le
            have h_dist : dist t (t - y) < δ₀ := by
              simpa [Real.dist_eq, abs_sub_comm] using hy_lt_delta0
            have h_uc := h_unif h_dist
            have h_norm_lt : ‖f t - f (t - y)‖ < Cε := by
              simpa [hCε_def, Complex.dist_eq, sub_eq_add_neg] using h_uc
            have h_norm_le : ‖f t - f (t - y)‖ ≤ Cε := le_of_lt h_norm_lt
            have :
                create_mollifier δ y * ‖f t - f (t - y)‖
                  ≤ create_mollifier δ y * Cε := by
              exact mul_le_mul_of_nonneg_left h_norm_le hcm_nonneg
            simpa using this

        have h_integrable_left :
            Integrable
              (fun y : ℝ => create_mollifier δ y * ‖f t - f (t - y)‖) := by
          have := h_diff_integrable.norm
          simpa [norm_mul, norm_complex_create_mollifier, abs_create_mollifier]
            using this

        have h_integrable_right :
            Integrable (fun y : ℝ => create_mollifier δ y * Cε) := by
          simpa using h_mollifier_integrable_real.mul_const (c := Cε)

        have h_int_le :
            ∫ y, create_mollifier δ y * ‖f t - f (t - y)‖ ∂volume
              ≤ ∫ y, create_mollifier δ y * Cε ∂volume := by
          refine MeasureTheory.integral_mono_ae
              h_integrable_left h_integrable_right ?_
          refine Filter.Eventually.of_forall h_bound_integrand

        have h_int_right :
            ∫ y, create_mollifier δ y * Cε ∂volume = Cε := by
          have h_integral :=
            MeasureTheory.integral_mul_const (μ := volume)
              (f := fun y : ℝ => create_mollifier δ y) Cε
          simpa [Cε, hCε_def, h_mol_int, mul_comm, mul_left_comm, mul_assoc]
            using h_integral

        have h_norm_le' :
            ‖g t‖ ≤ Cε := by
          have := le_trans h_norm_le (le_trans h_int_le (le_of_eq h_int_right))
          simpa [hg_def] using this
        exact h_norm_le'

      have h_support_g :
          ∀ ⦃t⦄, R + 1 < |t| → g t = 0 := by
        intro t ht
        have hR_lt_abs : R < |t| := by
          have hR_lt : R < R + 1 := by linarith
          exact lt_trans hR_lt ht
        have hf_t : f t = 0 := hf_zero hR_lt_abs
        have h_integrand_zero :
            ∀ y, (create_mollifier δ y : ℂ) * (f t - f (t - y)) = 0 := by
          intro y
          by_cases hy_zero : create_mollifier δ y = 0
          · simp [hy_zero, hf_t]
          · have hy_abs_lt : |y| < δ := by
              by_contra hy_abs
              have : create_mollifier δ y = 0 := by
                simp [create_mollifier, hy_abs]
              exact hy_zero this
            have hy_lt_one : |y| < 1 := lt_of_lt_of_le hy_abs_lt hδ_lt_one.le
            have hR_lt_sub : R < |t - y| := by
              have hR_add_lt : R + |y| < |t| := by
                have h_aux : R + |y| < R + 1 := by
                  have := add_lt_add_left hy_lt_one R
                  simpa [add_comm, add_left_comm, add_assoc] using this
                exact lt_trans h_aux ht
              have h_gt : R < |t| - |y| := (lt_sub_iff_add_lt).2 hR_add_lt
              have h_one_le_abs_t : (1 : ℝ) ≤ |t| := by
                have : (1 : ℝ) ≤ R + 1 := by nlinarith [hR_pos]
                exact le_trans this (le_of_lt ht)
              have hy_le_abs_t : |y| ≤ |t| := le_trans hy_lt_one.le h_one_le_abs_t
              have h_nonneg : 0 ≤ |t| - |y| := sub_nonneg.mpr hy_le_abs_t
              have h_abs_le : |t| - |y| ≤ |t - y| := by
                have h_aux := abs_sub_abs_le_abs_sub t y
                have h_abs_eq : |t| - |y| = |t| - |y| := by
                  simp [abs_of_nonneg h_nonneg]
                simpa [h_abs_eq] using h_aux
              exact lt_of_lt_of_le h_gt h_abs_le
            have hf_ty : f (t - y) = 0 := hf_zero hR_lt_sub
            simp [hf_t, hf_ty]
        have h_integrand_zero' :
            (fun y : ℝ => (create_mollifier δ y : ℂ) * (f t - f (t - y))) = 0 := by
          funext y; exact h_integrand_zero y
        simp [hg_def, h_integrand_zero']

      let S : Set ℝ := Metric.closedBall (0 : ℝ) (R + 1)

      have h_indicator_eq :
          (fun t : ℝ => ENNReal.ofReal ‖g t‖)
            = Set.indicator S (fun t : ℝ => ENNReal.ofReal ‖g t‖) := by
        funext t
        by_cases ht : t ∈ S
        · simp [ht]
        · have ht_abs : R + 1 < |t| := by
            simpa [S, Metric.mem_closedBall, Real.dist_eq, not_le] using ht
          have hg_zero : g t = 0 := h_support_g ht_abs
          simp [ht, hg_zero]

      have h_indicator_sq_eq :
          (fun t : ℝ => ENNReal.ofReal (‖g t‖ ^ 2))
            = Set.indicator S (fun t : ℝ => ENNReal.ofReal (‖g t‖ ^ 2)) := by
        funext t
        by_cases ht : t ∈ S
        · simp [ht]
        · have ht_abs : R + 1 < |t| := by
            simpa [S, Metric.mem_closedBall, Real.dist_eq, not_le] using ht
          have hg_zero : g t = 0 := h_support_g ht_abs
          simp [ht, hg_zero]

      have hS_meas : MeasurableSet S := (Metric.isClosed_closedBall).measurableSet

      have h_indicator_le :
          (fun t : ℝ => ENNReal.ofReal ‖g t‖)
            ≤ᵐ[volume]
              Set.indicator S (fun _ : ℝ => ENNReal.ofReal Cε) := by
        refine Filter.Eventually.of_forall ?_
        intro t
        by_cases ht : t ∈ S
        · have h_norm := h_pointwise t
          have h_norm' : ENNReal.ofReal ‖g t‖ ≤ ENNReal.ofReal Cε := by
            refine (ENNReal.ofReal_le_ofReal_iff hCε_nonneg).2 ?_
            simpa using h_norm
          have h_norm'' : ↑‖g t‖₊ ≤ ENNReal.ofReal Cε := by
            simpa using h_norm'
          simp [h_indicator_eq, ht, h_norm'', hCε_nonneg]
        · have ht_abs : R + 1 < |t| := by
            simpa [S, Metric.mem_closedBall, Real.dist_eq, not_le] using ht
          have hg_zero : g t = 0 := h_support_g ht_abs
          simp [h_indicator_eq, ht, hg_zero, hCε_nonneg]

      have h_indicator_sq_le :
          (fun t : ℝ => ENNReal.ofReal (‖g t‖ ^ 2))
            ≤ᵐ[volume]
              Set.indicator S (fun _ : ℝ => ENNReal.ofReal (Cε ^ 2)) := by
        refine Filter.Eventually.of_forall ?_
        intro t
        by_cases ht : t ∈ S
        · have h_norm := h_pointwise t
          have h_norm_sq : ‖g t‖ ^ 2 ≤ Cε ^ 2 := by
            have h_norm_nonneg : 0 ≤ ‖g t‖ := norm_nonneg _
            calc
              ‖g t‖ ^ 2 = ‖g t‖ * ‖g t‖ := by simp [pow_two]
              _ ≤ Cε * Cε := mul_le_mul h_norm h_norm h_norm_nonneg hCε_nonneg
              _ = Cε ^ 2 := by simp [pow_two]
          have h_norm' : ENNReal.ofReal (‖g t‖ ^ 2) ≤ ENNReal.ofReal (Cε ^ 2) := by
            refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg Cε)).2 ?_
            simpa using h_norm_sq
          simp [h_indicator_sq_eq, ht, h_norm']
        · have ht_abs : R + 1 < |t| := by
            simpa [S, Metric.mem_closedBall, Real.dist_eq, not_le] using ht
          have hg_zero : g t = 0 := h_support_g ht_abs
          simp [h_indicator_sq_eq, ht, hg_zero]

      have h_lintegral_le :
          ∫⁻ t, ENNReal.ofReal ‖g t‖ ∂volume
            ≤ ∫⁻ t, Set.indicator S (fun _ : ℝ => ENNReal.ofReal Cε) t ∂volume :=
        lintegral_mono_ae h_indicator_le

      have h_lintegral_sq_le :
          ∫⁻ t, ENNReal.ofReal (‖g t‖ ^ 2) ∂volume
            ≤ ∫⁻ t, Set.indicator S (fun _ : ℝ => ENNReal.ofReal (Cε ^ 2)) t ∂volume :=
        lintegral_mono_ae h_indicator_sq_le

      have h_volume : volume S = ENNReal.ofReal (2 * (R + 1)) := by
        simp [S, two_mul, add_comm, add_left_comm, add_assoc]

      have h_lintegral_const :
          ∫⁻ t, Set.indicator S (fun _ : ℝ => ENNReal.ofReal Cε) t ∂volume
            = ENNReal.ofReal Cε * volume S := by
        simp [hS_meas, h_volume, hCε_nonneg]

      have h_lintegral_sq_const :
          ∫⁻ t, Set.indicator S (fun _ : ℝ => ENNReal.ofReal (Cε ^ 2)) t ∂volume
            = ENNReal.ofReal (Cε ^ 2) * volume S := by
        have hCε_sq_nonneg : 0 ≤ Cε ^ 2 := sq_nonneg _
        simp [hS_meas, h_volume, hCε_sq_nonneg]

      have h_norm_le_const :
          eLpNorm g 1 volume
              ≤ ENNReal.ofReal Cε * volume S := by
        have :=
          calc
            eLpNorm g 1 volume
                = ∫⁻ t, ENNReal.ofReal ‖g t‖ ∂volume := by
                    simp [hg_def, eLpNorm_one_eq_lintegral_enorm]
            _ ≤ ∫⁻ t, Set.indicator S (fun _ : ℝ => ENNReal.ofReal Cε) t ∂volume :=
                    h_lintegral_le
            _ = ENNReal.ofReal Cε * volume S := h_lintegral_const
        exact this

      have h_norm_sq_le_const :
          eLpNorm g 2 volume
              ≤ (ENNReal.ofReal (Cε ^ 2) * volume S) ^ (1 / 2 : ℝ) := by
        have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
        have h_two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
        have h_l2_def :=
          eLpNorm_eq_lintegral_rpow_enorm (p := (2 : ℝ≥0∞))
            (f := g) (μ := volume) h_two_ne_zero h_two_ne_top
        have h_integrand_eq :
            ∀ t, ‖g t‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖g t‖ ^ 2) := by
          intro t
          simp [pow_two, sq, ENNReal.ofReal_mul, norm_nonneg]
        have h_nn_eq :
            ∀ t, (↑‖g t‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖g t‖ ^ 2) := by
          intro t
          simp [pow_two, ENNReal.ofReal_mul, norm_nonneg]
        have h_integral_eq :
            ∫⁻ t, ‖g t‖ₑ ^ (2 : ℝ) ∂volume
              = ∫⁻ t, ENNReal.ofReal (‖g t‖ ^ 2) ∂volume := by
          refine lintegral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro t
          exact h_integrand_eq t
        have h_pow_le :
            ∫⁻ t, ‖g t‖ₑ ^ (2 : ℝ) ∂volume
              ≤ ENNReal.ofReal (Cε ^ 2) * volume S := by
          calc
            ∫⁻ t, ‖g t‖ₑ ^ (2 : ℝ) ∂volume
                = ∫⁻ t, ENNReal.ofReal (‖g t‖ ^ 2) ∂volume := by
                    simpa using h_integral_eq
            _ ≤ ∫⁻ t, Set.indicator S (fun _ : ℝ => ENNReal.ofReal (Cε ^ 2)) t ∂volume :=
                h_lintegral_sq_le
            _ = ENNReal.ofReal (Cε ^ 2) * volume S := h_lintegral_sq_const
        have h_sqrt_le_aux :=
          ENNReal.rpow_le_rpow h_pow_le (by norm_num : 0 ≤ (1 / 2 : ℝ))
        have h_sqrt_le_aux' :
            (∫⁻ t, ‖g t‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
              ≤ (ENNReal.ofReal (Cε ^ 2) * volume S) ^ (1 / 2 : ℝ) := by
          simpa using h_sqrt_le_aux
        have h_l2_eval :
            eLpNorm g 2 volume
              = (∫⁻ t, ‖g t‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
          simp [h_l2_def]
        have h_sqrt_le :
            eLpNorm g 2 volume
              ≤ (ENNReal.ofReal (Cε ^ 2) * volume S) ^ (1 / 2 : ℝ) := by
          rw [h_l2_eval]
          exact h_sqrt_le_aux'
        exact h_sqrt_le

      have h_product_sq_lt :
          ENNReal.ofReal (Cε ^ 2) * volume S
            < (ENNReal.ofReal εR) ^ 2 := by
        have h_pos_mul : 0 ≤ 2 * (R + 1) := by nlinarith [hR_pos]
        have h_left :
            ENNReal.ofReal (Cε ^ 2) * volume S
              = ENNReal.ofReal (Cε ^ 2 * (2 * (R + 1))) := by
            simp [h_volume, ENNReal.ofReal_mul, sq_nonneg _, h_pos_mul]
        have h_right :
            (ENNReal.ofReal εR) ^ 2 = ENNReal.ofReal (εR ^ 2) := by
          simp [pow_two, sq, ENNReal.ofReal_mul, hεR_nonneg]
        have h_ratio_lt_one :
            (2 * (R + 1)) / (4 * R + 2) ^ 2 < 1 := by
          have h_den_sq_pos : 0 < (4 * R + 2) ^ 2 := sq_pos_of_pos h_den_pos
          have h_num_lt : 2 * (R + 1) < (4 * R + 2) ^ 2 := by
            have h_diff_eq :
                (4 * R + 2) ^ 2 - 2 * (R + 1) = 16 * R ^ 2 + 14 * R + 2 := by ring
            have h_square_nonneg : 0 ≤ 16 * R ^ 2 := by
              have : 0 ≤ R ^ 2 := sq_nonneg _
              exact mul_nonneg (by norm_num) this
            have h14R_nonneg : 0 ≤ 14 * R := by
              have : 0 ≤ R := hR_pos.le
              exact mul_nonneg (by norm_num) this
            have h_quad_nonneg : 0 ≤ 16 * R ^ 2 + 14 * R :=
              add_nonneg h_square_nonneg h14R_nonneg
            have h_two_pos : 0 < (2 : ℝ) := by norm_num
            have h_rhs_pos : 0 < 16 * R ^ 2 + 14 * R + 2 :=
              add_pos_of_nonneg_of_pos h_quad_nonneg h_two_pos
            have h_diff_pos : 0 < (4 * R + 2) ^ 2 - 2 * (R + 1) := by
              simpa [h_diff_eq] using h_rhs_pos
            exact sub_pos.mp h_diff_pos
          exact (div_lt_one h_den_sq_pos).2 h_num_lt
        have h_eq : Cε ^ 2 * (2 * (R + 1))
            = εR ^ 2 * ((2 * (R + 1)) / (4 * R + 2) ^ 2) := by
          simp [Cε, hCε_def, pow_two, sq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        have h_real_lt : Cε ^ 2 * (2 * (R + 1)) < εR ^ 2 := by
          have h_eps_sq_pos : 0 < εR ^ 2 := sq_pos_of_pos hεR_pos
          have := mul_lt_mul_of_pos_left h_ratio_lt_one h_eps_sq_pos
          simpa [h_eq] using this
        have h_eps_sq_pos : 0 < εR ^ 2 := sq_pos_of_pos hεR_pos
        have := (ENNReal.ofReal_lt_ofReal_iff h_eps_sq_pos).2 h_real_lt
        simpa [h_left, h_right] using this

      have h_sqrt_lt :
          (ENNReal.ofReal (Cε ^ 2) * volume S) ^ (1 / 2 : ℝ)
            < ENNReal.ofReal εR := by
        have h_pow := ENNReal.rpow_lt_rpow h_product_sq_lt (by norm_num : (0 : ℝ) < 1 / 2)
        have h_pow'' :
            (ENNReal.ofReal (Cε ^ 2) * volume S) ^ (1 / 2 : ℝ)
              < ((ENNReal.ofReal εR) ^ 2) ^ (1 / 2 : ℝ) := by
          simpa [one_div] using h_pow
        have h_base : ((ENNReal.ofReal εR) ^ 2) = ENNReal.ofReal (εR ^ 2) := by
          simp [pow_two, sq, ENNReal.ofReal_mul, hεR_nonneg]
        have h_pow' :
            (ENNReal.ofReal (Cε ^ 2) * volume S) ^ (1 / 2 : ℝ)
              < ENNReal.ofReal (εR ^ 2) ^ (1 / 2 : ℝ) := by
          simpa [h_base] using h_pow''
        have h_sq_nonneg : 0 ≤ εR ^ 2 := sq_nonneg εR
        have h_rpow_eq : (εR ^ 2) ^ (1 / 2 : ℝ) = εR := by
          have h_sqrt := Real.sqrt_sq (le_of_lt hεR_pos)
          have h_pow := Real.sqrt_eq_rpow (εR ^ 2)
          simpa [h_pow, one_div] using h_sqrt
        have h_rhs :
            ENNReal.ofReal (εR ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal εR := by
          have h_eq0 :
              ENNReal.ofReal (εR ^ 2) ^ (1 / 2 : ℝ)
                = ENNReal.ofReal ((εR ^ 2) ^ (1 / 2 : ℝ)) := by
            simpa [one_div] using
              ENNReal.ofReal_rpow_of_nonneg (x := εR ^ 2)
                h_sq_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))
          have h_eq1 := congrArg ENNReal.ofReal h_rpow_eq
          exact h_eq0.trans h_eq1
        have h_sqrt_lt :
            (ENNReal.ofReal (Cε ^ 2) * volume S) ^ (1 / 2 : ℝ)
              < ENNReal.ofReal εR := h_rhs ▸ h_pow'
        exact h_sqrt_lt

      have h_lt :
          eLpNorm g 2 volume < ENNReal.ofReal εR :=
        lt_of_le_of_lt h_norm_sq_le_const h_sqrt_lt
      exact h_lt
    have h_lt :
        eLpNorm
            (fun t => f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 2 volume
          < ENNReal.ofReal εR := by
      simpa [h_congr] using h_bound
    simpa [Set.mem_Iio] using h_lt
  exact hε_subset' h_mem_Iio

/-- Convolution with a mollifier of vanishing radius approximates a compactly supported
function simultaneously in `L¹` and `L²`. -/
lemma mollifier_convolution_L1_L2_small
    (f : ℝ → ℂ) (hf_compact : HasCompactSupport f)
    (hf_L1 : Integrable f) (hf_cont : Continuous f) :
    ∀ ε > 0,
      ∃ δ > 0,
        eLpNorm
            (fun t =>
              f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 1 volume
              < ENNReal.ofReal ε ∧
        eLpNorm
            (fun t =>
              f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 2 volume
              < ENNReal.ofReal ε := by
  classical
  intro ε hε
  have hε_pos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hL1_tendsto := mollifier_convolution_L1_tendsto f hf_compact hf_L1 hf_cont
  have hL2_tendsto := mollifier_convolution_L2_tendsto f hf_compact hf_L1 hf_cont

  -- Define the error functions in L¹ and L².
  set F₁ : ℝ → ℝ≥0∞ := fun δ =>
      eLpNorm
        (fun t =>
          f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 1 volume
  set F₂ : ℝ → ℝ≥0∞ := fun δ =>
      eLpNorm
        (fun t =>
          f t - ∫ y, (create_mollifier δ y : ℂ) * f (t - y) ∂volume) 2 volume

  -- Using the tendsto statements, both error sets are members of the filter.
  have h_set₁ : {δ : ℝ | F₁ δ < ENNReal.ofReal ε}
      ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
    have h_target : Set.Iio (ENNReal.ofReal ε) ∈ 𝓝 (0 : ℝ≥0∞) :=
      Iio_mem_nhds hε_pos
    simpa [F₁] using hL1_tendsto h_target

  have h_set₂ : {δ : ℝ | F₂ δ < ENNReal.ofReal ε}
      ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
    have h_target : Set.Iio (ENNReal.ofReal ε) ∈ 𝓝 (0 : ℝ≥0∞) :=
      Iio_mem_nhds hε_pos
    simpa [F₂] using hL2_tendsto h_target

  -- Intersect the two eventuality sets.
  have h_inter := Filter.inter_mem h_set₁ h_set₂
  have h_ball_subset : ∃ η > 0,
      ball (0 : ℝ) η ∩ Set.Ioi (0 : ℝ)
        ⊆ ({δ : ℝ | F₁ δ < ENNReal.ofReal ε}
            ∩ {δ : ℝ | F₂ δ < ENNReal.ofReal ε}) := by
    simpa [F₁, F₂] using (mem_nhdsWithin_iff).1 h_inter

  obtain ⟨η, hη_pos, h_subset⟩ := h_ball_subset
  -- Choose δ = η/2, which lies in the intersection of the ball and the positive half-line.
  refine ⟨η / 2, half_pos hη_pos, ?_⟩
  have hδ_ball : (η / 2) ∈ ball (0 : ℝ) η := by
    have h_nonneg : 0 ≤ η / 2 := by positivity
    have h_lt : η / 2 < η := half_lt_self hη_pos
    have h_abs : |η / 2| = η / 2 := abs_of_nonneg h_nonneg
    simpa [Metric.ball, Real.dist_eq, h_abs] using h_lt
  have hδ_pos : η / 2 ∈ Set.Ioi (0 : ℝ) := by
    simpa using half_pos hη_pos

  have hδ_mem := h_subset ⟨hδ_ball, hδ_pos⟩
  have hδ_mem' :
      (η / 2) ∈ {δ : ℝ | F₁ δ < ENNReal.ofReal ε}
        ∧ (η / 2) ∈ {δ : ℝ | F₂ δ < ENNReal.ofReal ε} := by
    simpa [Set.mem_inter] using hδ_mem
  have hδ_mem₁ : F₁ (η / 2) < ENNReal.ofReal ε :=
    by simpa [F₁] using hδ_mem'.1
  have hδ_mem₂ : F₂ (η / 2) < ENNReal.ofReal ε :=
    by simpa [F₂] using hδ_mem'.2
  exact ⟨by simpa [F₁] using hδ_mem₁, by simpa [F₂] using hδ_mem₂⟩

lemma eLpNorm_one_le_mul_two_of_support_closedBall
    {h : ℝ → ℂ} {R : ℝ}
    (h_mem : MemLp h 2 volume)
    (h_support : ∀ ⦃t : ℝ⦄, R < ‖t‖ → h t = 0) :
    eLpNorm h 1 volume
      ≤ (volume (Metric.closedBall (0 : ℝ) R)) ^ (1 / 2 : ℝ)
          * eLpNorm h 2 volume := by
  classical
  set B : Set ℝ := Metric.closedBall (0 : ℝ) R with hB_def
  set F : ℝ → ℝ≥0∞ := fun t => ‖h t‖ₑ with hF_def
  set G : ℝ → ℝ≥0∞ :=
      fun t => Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t with hG_def

  have h_indicator_mul : ∀ t, F t = F t * G t := by
    intro t
    classical
    by_cases ht : t ∈ B
    · classical
      have hG_def' :
          G t = Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t := rfl
      have h_indicator :=
        Set.indicator_of_mem ht (fun _ : ℝ => (1 : ℝ≥0∞))
      have hG_eq : G t = 1 :=
        hG_def'.trans (h_indicator.trans rfl)
      have hF_mul : F t = F t * (1 : ℝ≥0∞) :=
        (mul_one (F t)).symm
      have h_mul' : F t * (1 : ℝ≥0∞) = F t * G t := by
        rw [hG_eq]
      exact hF_mul.trans h_mul'
    · have hnot : ¬ |t| ≤ R := by
        simpa [B, hB_def, Metric.mem_closedBall, Real.dist_eq,
          sub_eq_add_neg, not_le] using ht
      have habs : R < |t| := lt_of_not_ge hnot
      have hnorm : R < ‖t‖ := by simpa [Real.norm_eq_abs] using habs
      have ht_zero : h t = 0 := h_support hnorm
      classical
      have hG_def' :
          G t = Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t := rfl
      have h_indicator :=
        Set.indicator_of_notMem ht (fun _ : ℝ => (1 : ℝ≥0∞))
      have hG_eq : G t = 0 := hG_def'.trans h_indicator
      have hF_zero : F t = 0 := by
        simp [F, hF_def, ht_zero]
      have h_zero_mul : 0 = 0 * G t := (zero_mul (G t)).symm
      have hFG_zero : 0 * G t = F t * G t :=
        (congrArg (fun x : ℝ≥0∞ => x * G t) hF_zero).symm
      exact hF_zero.trans (h_zero_mul.trans hFG_zero)

  have h_indicator_ae :
      (fun t => F t) =ᵐ[volume] fun t => F t * G t :=
    Filter.Eventually.of_forall h_indicator_mul

  have h_eLpNorm_one :
      eLpNorm h 1 volume = ∫⁻ t, F t ∂volume := by
    simp [F, hF_def, eLpNorm_one_eq_lintegral_enorm]

  have h_lintegral_eq :
      ∫⁻ t, F t ∂volume = ∫⁻ t, F t * G t ∂volume := by
    simpa using lintegral_congr_ae h_indicator_ae

  have hF_meas : AEMeasurable F (volume : Measure ℝ) :=
    (h_mem.1.enorm : AEMeasurable (fun t => ‖h t‖ₑ) volume)

  have hB_meas : MeasurableSet B :=
    Metric.isClosed_closedBall.measurableSet

  have hG_meas : AEMeasurable G (volume : Measure ℝ) := by
    change AEMeasurable
      (fun t => Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t) volume
    exact (measurable_const.indicator hB_meas).aemeasurable

  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) := by
    refine Real.holderConjugate_iff.mpr ?_
    refine ⟨by norm_num, ?_⟩; norm_num

  have h_holder :
      ∫⁻ t, F t * G t ∂volume
        ≤ (∫⁻ t, (F t) ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
            * (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
    simpa [Pi.mul_apply] using
      ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := volume) hpq hF_meas hG_meas

  have h_eLpNorm_two :
      (∫⁻ t, (F t) ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
        = eLpNorm h 2 volume := by
    have h₂_ne_zero : ((2 : ℝ≥0∞)) ≠ 0 := by simp
    have h₂_ne_top : ((2 : ℝ≥0∞)) ≠ ∞ := by simp
    have :=
      (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        (μ := volume) (f := h) (p := (2 : ℝ≥0∞)) h₂_ne_zero h₂_ne_top).symm
    simpa [F, hF_def, one_div] using this

  have hG_pow_eq :
      (fun t : ℝ => (G t) ^ (2 : ℝ))
        = Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) := by
    classical
    funext t
    by_cases ht : t ∈ B
    · have h_indicator :
          Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t = 1 :=
        (Set.indicator_of_mem ht _).trans rfl
      have hG_eval :
          G t = Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t := by
        simp [G]
      have hG_eq : G t = 1 := hG_eval.trans h_indicator
      have h_pow : G t ^ (2 : ℝ) = 1 := by
        simp [hG_eq]
      exact h_pow.trans h_indicator.symm
    · have h_indicator :
          Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t = 0 :=
        Set.indicator_of_notMem ht _
      have hG_eval :
          G t = Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t := by
        simp [G]
      have hG_eq : G t = 0 := hG_eval.trans h_indicator
      have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
      have h_pow : G t ^ (2 : ℝ) = 0 := by
        simp [hG_eq]
      exact h_pow.trans h_indicator.symm

  have hG_integral :
      (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume)
        = volume B := by
    classical
    have h_indicator_integral :
        (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume)
          = ∫⁻ t, Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t ∂volume := by
      simpa [hG_pow_eq] using
        congrArg (fun f : ℝ → ℝ≥0∞ => ∫⁻ t, f t ∂volume) hG_pow_eq
    calc
      (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume)
          = ∫⁻ t, Set.indicator B (fun _ : ℝ => (1 : ℝ≥0∞)) t ∂volume :=
        h_indicator_integral
      _ = ∫⁻ t in B, (1 : ℝ≥0∞) ∂volume := by
            simpa using
              MeasureTheory.lintegral_indicator (μ := volume)
                (hs := hB_meas)
                  (f := fun _ : ℝ => (1 : ℝ≥0∞))
      _ = volume B := by
            simp [MeasureTheory.lintegral_const, hB_meas]

  have h_volume_pow :
      (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
        = (volume B) ^ (1 / 2 : ℝ) := by
    simpa using
      congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) hG_integral

  have h_bound :
      eLpNorm h 1 volume
        ≤ (∫⁻ t, (F t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ) *
            (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ) := by
    calc
      eLpNorm h 1 volume = ∫⁻ t, F t ∂volume := h_eLpNorm_one
      _ = ∫⁻ t, F t * G t ∂volume := h_lintegral_eq
      _ ≤ (∫⁻ t, (F t) ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) *
            (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := h_holder
      _ = (∫⁻ t, (F t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ) *
            (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ) := by
            simp [one_div]

  have h_first_factor :
      (∫⁻ t, (F t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ)
        = eLpNorm h 2 volume := by
    simpa [one_div] using h_eLpNorm_two

  have h_second_factor :
      (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ)
        = (volume B) ^ (2⁻¹ : ℝ) := by
    simpa [one_div] using h_volume_pow

  have h_le_twice :
      eLpNorm h 1 volume
        ≤ eLpNorm h 2 volume * (volume B) ^ (2⁻¹ : ℝ) := by
    have h_intermediate :
        eLpNorm h 1 volume
          ≤ eLpNorm h 2 volume *
              (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ) := by
      calc
        eLpNorm h 1 volume
            ≤ (∫⁻ t, (F t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ) *
                (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ) :=
              h_bound
        _ = eLpNorm h 2 volume *
                (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ) := by
              rw [h_first_factor]
    calc
      eLpNorm h 1 volume
          ≤ eLpNorm h 2 volume *
              (∫⁻ t, (G t) ^ (2 : ℝ) ∂volume) ^ (2⁻¹ : ℝ) := h_intermediate
      _ = eLpNorm h 2 volume * (volume B) ^ (2⁻¹ : ℝ) := by
            rw [h_second_factor]

  have h_le :
      eLpNorm h 1 volume
        ≤ eLpNorm h 2 volume * (volume B) ^ (1 / 2 : ℝ) := by
    simpa [one_div] using h_le_twice

  simpa [B, hB_def, mul_comm] using h_le

end Frourio
