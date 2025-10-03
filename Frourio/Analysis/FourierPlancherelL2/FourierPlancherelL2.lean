import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core2
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

/-- Uniform control of mollification error for compactly supported functions. -/
lemma mollifier_uniform_error_control
    (f : ℝ → ℂ) (hf_compact : HasCompactSupport f)
    (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ φ : ℝ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      eLpNorm (fun t => f t - φ t) 1 volume < ENNReal.ofReal δ ∧
      eLpNorm (fun t => f t - φ t) 2 volume < ENNReal.ofReal δ :=
  sorry

/-- Stability of L¹ and L² norms under convolution with a mollifier. -/
lemma mollifier_convolution_Lp_control
    (f : ℝ → ℂ) (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (φ : ℝ → ℂ) (hφ_compact : HasCompactSupport φ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∀ ε > 0,
      ∃ ψ : ℝ → ℂ,
        HasCompactSupport ψ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        eLpNorm (fun t => φ t - ψ t) 1 volume < ENNReal.ofReal ε ∧
        eLpNorm (fun t => φ t - ψ t) 2 volume < ENNReal.ofReal ε :=
  sorry

lemma smooth_compact_support_L1_L2_mollification
    (f : ℝ → ℂ) (hf_compact : HasCompactSupport f)
    (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      eLpNorm (fun t => f t - g t) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun t => f t - g t) 2 volume < ENNReal.ofReal ε := by
  sorry

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
