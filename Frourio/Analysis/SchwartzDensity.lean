import Frourio.Analysis.MellinBasic
import Frourio.Analysis.HilbertSpaceCore
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

open MeasureTheory Measure Real Complex SchwartzMap intervalIntegral
open scoped ENNReal Topology ComplexConjugate

namespace Frourio

section SchwartzDensity

/-- Manual construction of lintegral_union for disjoint sets -/
lemma lintegral_union_disjoint {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t)
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in s ∪ t, f x ∂μ = ∫⁻ x in s, f x ∂μ + ∫⁻ x in t, f x ∂μ := by
  -- Use the basic properties of set integrals and indicators
  have h_union_meas : MeasurableSet (s ∪ t) := hs.union ht

  -- Express set integrals using indicator functions
  have h_eq : ∫⁻ x in s ∪ t, f x ∂μ = ∫⁻ x, (s ∪ t).indicator f x ∂μ := by
    rw [(lintegral_indicator h_union_meas f).symm]

  rw [h_eq]

  -- Split the indicator function using disjointness
  have h_indicator : (s ∪ t).indicator f = s.indicator f + t.indicator f := by
    funext x
    simp only [Set.indicator]
    by_cases hx_s : x ∈ s
    · simp [hx_s, Set.mem_union]
      -- If x ∈ s, then by disjointness x ∉ t
      have hx_not_t : x ∉ t := Set.disjoint_left.mp hst hx_s
      simp [hx_not_t]
    · by_cases hx_t : x ∈ t
      · simp [hx_s, hx_t, Set.mem_union]
      · simp [hx_s, hx_t, Set.mem_union]

  rw [h_indicator]
  -- Convert function addition to explicit form
  have h_add : (fun x => (s.indicator f + t.indicator f) x) =
      (fun x => s.indicator f x + t.indicator f x) := by
    funext x
    rfl
  rw [h_add]
  rw [lintegral_add_left (hf.indicator hs)]
  rw [←lintegral_indicator hs f]
  rw [←lintegral_indicator ht f]

/-- Schwartz functions have finite weighted L² norm on (0,1] for σ > 1/2 -/
lemma schwartz_finite_on_unit_interval {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) :
    ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ₑ ^ (2 : ℝ)
      ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) < ∞ := by
  -- Schwartz functions are bounded, and the weight is integrable for σ > 1/2
  -- Step 1: rewrite the restricted integral using an indicator with respect to a named measure.
  set μ := mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) with hμμ
  have h_indicator :
      ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ₑ ^ (2 : ℝ) ∂μ =
        ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂μ := by
    simp [μ]
  -- Step 2: control the integrand by a constant depending on the 0-th seminorm of `f`.
  set C := SchwartzMap.seminorm ℝ 0 0 f with hC_def
  have hC_nonneg : 0 ≤ C := by
    simp [C]
  have h_indicator_bound :
      Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun x : ℝ => ‖f x‖ₑ ^ (2 : ℝ)) ≤
        Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun _ : ℝ => ENNReal.ofReal (C ^ 2)) := by
    classical
    intro x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · have h_norm : ‖f x‖ ≤ C := by
        simpa [C] using (SchwartzMap.norm_le_seminorm ℝ f x)
      have h_sq : ‖f x‖ ^ 2 ≤ C ^ 2 := by
        have hx_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
        have h_mul := mul_le_mul h_norm h_norm hx_nonneg hC_nonneg
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h_mul
      have h_le : ‖f x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (C ^ 2) := by
        calc
          ‖f x‖ₑ ^ (2 : ℝ)
              = ENNReal.ofReal (‖f x‖ ^ 2) := by
                simp [pow_two, ENNReal.ofReal_mul, norm_nonneg]
          _ ≤ ENNReal.ofReal (C ^ 2) := ENNReal.ofReal_le_ofReal h_sq
      simpa [hx] using h_le
    · simp [hx]
  -- Use the pointwise bound to estimate the integral by a constant multiple of the measure.
  have h_integral_le :
      ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂μ ≤
        ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun _ : ℝ => ENNReal.ofReal (C ^ 2)) x ∂μ :=
    lintegral_mono h_indicator_bound
  have h_const_integral :
      ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun _ : ℝ => ENNReal.ofReal (C ^ 2)) x ∂μ
        = ENNReal.ofReal (C ^ 2) * μ (Set.Ioc (0 : ℝ) 1) := by
    classical
    simp [μ, measurableSet_Ioc]
  have h_integral_bound :
      ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ₑ ^ (2 : ℝ) ∂μ ≤
        ENNReal.ofReal (C ^ 2) * μ (Set.Ioc (0 : ℝ) 1) := by
    calc
      ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ₑ ^ (2 : ℝ) ∂μ
          = ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂μ := h_indicator
      _ ≤ ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun _ : ℝ => ENNReal.ofReal (C ^ 2)) x ∂μ := h_integral_le
      _ = ENNReal.ofReal (C ^ 2) * μ (Set.Ioc (0 : ℝ) 1) := by
          simp [h_const_integral]
  -- Step 3: rewrite the weighted measure of `(0,1]` via an explicit power integral.
  have h_exp_nonneg : 0 ≤ 2 * σ - 1 := by linarith [hσ]
  have h_pow_meas :
      Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) :=
    (ENNReal.continuous_ofReal.comp
        (Real.continuous_rpow_const h_exp_nonneg)).measurable
  have h_meas_indicator :
      Measurable
        (fun x : ℝ =>
          Set.indicator (Set.Ioc (0 : ℝ) 1)
            (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) x) :=
    h_pow_meas.indicator measurableSet_Ioc
  have hμ_indicator :
      μ (Set.Ioc (0 : ℝ) 1) =
        ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
            (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) x ∂mulHaar := by
    simp [μ, measurableSet_Ioc]
  have hμ_volume_indicator :
      ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) x ∂mulHaar =
        ∫⁻ x in Set.Ioi (0 : ℝ),
          Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) x *
            ENNReal.ofReal (1 / x) ∂volume := by
    simpa using lintegral_mulHaar_expand (hg := h_meas_indicator)
  have hμ_volume' :
      μ (Set.Ioc (0 : ℝ) 1) =
        ∫⁻ x in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume := by
    classical
    have h_prod :
        (fun x : ℝ =>
            Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) x *
            ENNReal.ofReal (1 / x))
          = Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1) / x)) := by
      funext x; by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
      · have := weight_product_simplify (σ := σ) x
            (by simpa [Set.mem_Ioi] using hx.1)
        simpa [Set.indicator_of_mem hx, this, div_eq_mul_inv, one_div]
      · simp [hx]
    have h_subset : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := by
      intro x hx; exact hx.1
    have h_inter :
        Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 :=
      Set.inter_eq_left.mpr h_subset
    have h_restrict :=
      setLIntegral_indicator (μ := volume) (s := Set.Ioc (0 : ℝ) 1)
        (t := Set.Ioi (0 : ℝ))
        (f := fun x => ENNReal.ofReal (x ^ (2 * σ - 1) / x))
        measurableSet_Ioc
    have h_restrict' :
        ∫⁻ x in Set.Ioi (0 : ℝ),
            Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1) / x)) x ∂volume
          = ∫⁻ x in Set.Ioc (0 : ℝ) 1,
              ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume := by
      simp [h_inter]
    calc
      μ (Set.Ioc (0 : ℝ) 1)
          = ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) x ∂mulHaar := hμ_indicator
      _ = ∫⁻ x in Set.Ioi (0 : ℝ),
            Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) x *
            ENNReal.ofReal (1 / x) ∂volume := hμ_volume_indicator
      _ = ∫⁻ x in Set.Ioi (0 : ℝ),
            Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1) / x)) x ∂volume := by
        refine lintegral_congr_ae ?_
        refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
        refine Filter.Eventually.of_forall ?_
        intro x hx
        by_cases hx' : x ∈ Set.Ioc (0 : ℝ) 1
        · have hx_simplify := weight_product_simplify (σ := σ) x hx
          simpa [h_prod, hx', one_div] using hx_simplify
        · simp [hx', one_div]
      _ = ∫⁻ x in Set.Ioc (0 : ℝ) 1,
            ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume := h_restrict'
  have h_exp_neg : -1 < 2 * σ - 2 := by linarith [hσ]
  have h_denom_pos : 0 < 2 * σ - 1 := by linarith [hσ]
  let ν := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hμ_volume0 :
      μ (Set.Ioc (0 : ℝ) 1) =
        ∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂ν := by
    simpa [ν] using hμ_volume'
  have h_ae_simplify :
      (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1) / x)) =ᵐ[ν]
        (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 2))) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx_pos : 0 < x := hx.1
    have hx_eq : x ^ (2 * σ - 1) / x = x ^ (2 * σ - 2) := by
      have hx_pow_one : x ^ (1 : ℝ) = x := by simp
      have hx_rpow := (Real.rpow_sub hx_pos (2 * σ - 1) 1).symm
      have hx_eq_rw : x ^ (2 * σ - 1) / x = x ^ ((2 * σ - 1) - 1) := by
        simpa [hx_pow_one] using hx_rpow
      have hx_sub : (2 * σ - 1) - 1 = 2 * σ - 2 := by ring
      simpa [hx_sub] using hx_eq_rw
    simp [hx_eq]
  have hμ_volume'' :
      μ (Set.Ioc (0 : ℝ) 1) =
        ∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 2)) ∂ν := by
    calc
      μ (Set.Ioc (0 : ℝ) 1)
          = ∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂ν := hμ_volume0
      _ = ∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 2)) ∂ν :=
        lintegral_congr_ae h_ae_simplify
  have h_integrable_on :
      IntegrableOn (fun x : ℝ => x ^ (2 * σ - 2)) (Set.Ioc (0 : ℝ) 1) volume := by
    have h_int :=
      (intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
        (r := 2 * σ - 2) h_exp_neg)
    have :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
          (a := (0 : ℝ)) (b := 1) (by norm_num)
          (f := fun x : ℝ => x ^ (2 * σ - 2))).mp h_int
    simpa using this
  have h_integrable :
      Integrable (fun x : ℝ => x ^ (2 * σ - 2)) ν := by
    simpa [IntegrableOn, ν] using h_integrable_on
  have h_nonneg :
      0 ≤ᵐ[ν] fun x : ℝ => x ^ (2 * σ - 2) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact Real.rpow_nonneg (le_of_lt hx.1) _
  have h_ofReal :
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 2)) ∂ν =
        ENNReal.ofReal (∫ x, x ^ (2 * σ - 2) ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg).symm
  have h_set_to_interval :
      ∫ x, x ^ (2 * σ - 2) ∂ν =
        ∫ x in (0 : ℝ)..1, x ^ (2 * σ - 2) ∂volume := by
    have h₁ :
        ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (2 * σ - 2) ∂volume =
          ∫ x in (0 : ℝ)..1, x ^ (2 * σ - 2) ∂volume := by
      simpa using
        (intervalIntegral.integral_of_le (μ := volume)
            (f := fun x : ℝ => x ^ (2 * σ - 2))
            (a := (0 : ℝ)) (b := 1) (by norm_num)).symm
    simpa [ν] using h₁
  have h_interval_value :
      ∫ x in (0 : ℝ)..1, x ^ (2 * σ - 2) ∂volume = (2 * σ - 1)⁻¹ := by
    have h_int :=
      integral_rpow (a := (0 : ℝ)) (b := 1)
        (r := 2 * σ - 2) (Or.inl h_exp_neg)
    have h_zero : (0 : ℝ) ^ (2 * σ - 1) = 0 :=
      by simpa using Real.zero_rpow (ne_of_gt h_denom_pos)
    have h_one : (1 : ℝ) ^ (2 * σ - 1) = 1 :=
      by simp
    have h_sub : 2 * σ - 2 + 1 = 2 * σ - 1 := by ring
    simpa [h_sub, h_zero, h_one] using h_int
  have h_int_value :
      ∫ x, x ^ (2 * σ - 2) ∂ν = (2 * σ - 1)⁻¹ := by
    simp [h_set_to_interval, h_interval_value]
  have hμ_value :
      μ (Set.Ioc (0 : ℝ) 1) = ENNReal.ofReal (1 / (2 * σ - 1)) := by
    simp [hμ_volume'', h_ofReal, h_int_value, one_div]
  have hμ_lt_top : μ (Set.Ioc (0 : ℝ) 1) < ∞ := by
    simp [hμ_value]
  have h_rhs_lt_top :
      ENNReal.ofReal (C ^ 2) * μ (Set.Ioc (0 : ℝ) 1) < ∞ :=
    ENNReal.mul_lt_top (by simp) hμ_lt_top
  have h_integral_lt_top :
      ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ∞ :=
    lt_of_le_of_lt h_integral_bound h_rhs_lt_top
  exact h_integral_lt_top

/-- Schwartz functions have finite weighted L² norm on (1,∞) for any σ -/
lemma schwartz_finite_on_tail {σ : ℝ} (f : SchwartzMap ℝ ℂ) :
    ∫⁻ x in Set.Ioi (1 : ℝ), ‖f x‖ₑ ^ (2 : ℝ)
      ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) < ∞ := by
  -- Schwartz rapid decay dominates polynomial growth at infinity
  classical
  -- Step 1: rewrite the integral over mulHaar.withDensity using indicators and `mulHaar`.
  set μ := mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))) with hμ
  have h_indicator :
      ∫⁻ x in Set.Ioi (1 : ℝ), ‖f x‖ₑ ^ (2 : ℝ) ∂μ =
        ∫⁻ x, Set.indicator (Set.Ioi (1 : ℝ))
          (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂μ := by
    simp [μ]
  have h_indicator_ofReal :
      ∫⁻ x, Set.indicator (Set.Ioi (1 : ℝ))
          (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂μ =
        ∫⁻ x, Set.indicator (Set.Ioi (1 : ℝ))
          (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x ∂μ := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    classical
    by_cases hx : x ∈ Set.Ioi (1 : ℝ)
    · simp [Set.indicator, hx, pow_two, ENNReal.ofReal_mul, norm_nonneg]
    · simp [Set.indicator, hx]
  have h_weight_meas :
      Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) := by
    measurability
  have h_indicator_meas :
      Measurable fun x : ℝ =>
        Set.indicator (Set.Ioi (1 : ℝ)) (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x := by
    classical
    have h_cont : Continuous fun x : ℝ => (f x : ℂ) := SchwartzMap.continuous f
    have h_cont_norm : Continuous fun x : ℝ => ‖f x‖ := h_cont.norm
    have h_cont_sq : Continuous fun x : ℝ => ‖f x‖ ^ 2 := by
      simpa [pow_two] using (h_cont_norm.mul h_cont_norm)
    have h_meas_sq :
        Measurable fun x : ℝ => ENNReal.ofReal (‖f x‖ ^ 2) :=
      (ENNReal.measurable_ofReal.comp h_cont_sq.measurable)
    exact h_meas_sq.indicator measurableSet_Ioi
  have h_withDensity :
      ∫⁻ x, Set.indicator (Set.Ioi (1 : ℝ))
          (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x ∂μ =
        ∫⁻ x,
          Set.indicator (Set.Ioi (1 : ℝ))
            (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x *
            ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar := by
    simpa [μ, hμ] using
      lintegral_withDensity_expand (g := fun x =>
        Set.indicator (Set.Ioi (1 : ℝ)) (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x)
        (wσ := fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
        h_indicator_meas h_weight_meas
  have h_mulHaar_meas :
      Measurable fun x : ℝ =>
        Set.indicator (Set.Ioi (1 : ℝ)) (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x *
          ENNReal.ofReal (x ^ (2 * σ - 1)) :=
    h_indicator_meas.mul h_weight_meas
  have h_mulHaar :
      ∫⁻ x,
          Set.indicator (Set.Ioi (1 : ℝ))
            (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x *
            ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            Set.indicator (Set.Ioi (1 : ℝ))
              (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x *
              ENNReal.ofReal (x ^ (2 * σ - 1)) *
              ENNReal.ofReal (1 / x) ∂volume := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      lintegral_mulHaar_expand
        (g := fun x : ℝ =>
          Set.indicator (Set.Ioi (1 : ℝ))
            (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x *
            ENNReal.ofReal (x ^ (2 * σ - 1))) h_mulHaar_meas
  let g : ℝ → ℝ≥0∞ :=
    fun x => Set.indicator (Set.Ioi (1 : ℝ))
      (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x *
      ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal (1 / x)
  have h_volume_eq :
      ∫⁻ x in Set.Ioi (1 : ℝ), ‖f x‖ₑ ^ (2 : ℝ) ∂μ =
        ∫⁻ x in Set.Ioi (0 : ℝ), g x ∂volume := by
    calc
      ∫⁻ x in Set.Ioi (1 : ℝ), ‖f x‖ₑ ^ (2 : ℝ) ∂μ
          = ∫⁻ x, Set.indicator (Set.Ioi (1 : ℝ))
              (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂μ := h_indicator
      _ = ∫⁻ x,
              Set.indicator (Set.Ioi (1 : ℝ))
                (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x ∂μ := h_indicator_ofReal
      _ = ∫⁻ x,
              Set.indicator (Set.Ioi (1 : ℝ))
                (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x *
                ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar := h_withDensity
      _ = ∫⁻ x in Set.Ioi (0 : ℝ), g x ∂volume := by
        have := h_mulHaar
        simpa [g] using this
  have h_indicator_eq :
      Set.indicator (Set.Ioi (0 : ℝ)) g = Set.indicator (Set.Ioi (1 : ℝ)) g := by
    funext x
    classical
    by_cases hx1 : x ∈ Set.Ioi (1 : ℝ)
    · have hx0 : x ∈ Set.Ioi (0 : ℝ) :=
        lt_trans (show 0 < (1 : ℝ) by norm_num) hx1
      have hx_left : Set.indicator (Set.Ioi (0 : ℝ)) g x = g x :=
        Set.indicator_of_mem hx0 (f := g)
      have hx_right : Set.indicator (Set.Ioi (1 : ℝ)) g x = g x :=
        Set.indicator_of_mem hx1 (f := g)
      simp [hx_left, hx_right]
    · by_cases hx0 : x ∈ Set.Ioi (0 : ℝ)
      · have hx_indicator :
            (Set.Ioi (1 : ℝ)).indicator
              (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x = 0 :=
          Set.indicator_of_notMem hx1
            (f := fun x => ENNReal.ofReal (‖f x‖ ^ 2))
        have hgx : g x = 0 := by
          have := congrArg
              (fun z =>
                z * ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal (1 / x))
              hx_indicator
          simpa [g] using this
        have hx_left : Set.indicator (Set.Ioi (0 : ℝ)) g x = g x :=
          Set.indicator_of_mem hx0 (f := g)
        have hx_right : Set.indicator (Set.Ioi (1 : ℝ)) g x = 0 :=
          Set.indicator_of_notMem hx1 (f := g)
        refine ?_
        calc
          Set.indicator (Set.Ioi (0 : ℝ)) g x
              = g x := hx_left
          _ = 0 := hgx
          _ = Set.indicator (Set.Ioi (1 : ℝ)) g x := hx_right.symm
      · simp [g, Set.indicator, hx0, hx1]
  have h_restrict :
      ∫⁻ x in Set.Ioi (0 : ℝ), g x ∂volume =
        ∫⁻ x in Set.Ioi (1 : ℝ), g x ∂volume := by
    classical
    have h_int :
        ∫⁻ x, (Set.Ioi (0 : ℝ)).indicator g x ∂volume =
          ∫⁻ x, (Set.Ioi (1 : ℝ)).indicator g x ∂volume :=
      congrArg (fun h => ∫⁻ x, h x ∂volume) h_indicator_eq
    simpa [lintegral_indicator, measurableSet_Ioi] using h_int
  have h_weight_simplify :
      g =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
        fun x => ENNReal.ofReal (‖f x‖ ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) := by
    classical
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx_pos : 0 < x := lt_trans (show 0 < (1 : ℝ) by norm_num) hx
    have hx_simplify := weight_product_simplify (σ := σ) x hx_pos
    have hx_div_pow : x ^ (2 * σ - 1) / x = x ^ (2 * σ - 2) := by
      have hx_pow_one : x ^ (1 : ℝ) = x := by simp
      have hx_rpow := (Real.rpow_sub hx_pos (2 * σ - 1) 1).symm
      have hx_sub : (2 * σ - 1) - 1 = 2 * σ - 2 := by ring
      simpa [div_eq_mul_inv, hx_pow_one, hx_sub] using hx_rpow
    have hx_mul :
        ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal (1 / x)
          = ENNReal.ofReal (x ^ (2 * σ - 2)) := by
      simpa [one_div, hx_div_pow] using hx_simplify
    have hx_lt : 1 < x := hx
    have hx_indicator :
        (Set.Ioi (1 : ℝ)).indicator
            (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) x
          = ENNReal.ofReal (‖f x‖ ^ 2) :=
      Set.indicator_of_mem hx
        (f := fun x => ENNReal.ofReal (‖f x‖ ^ 2))
    have hx_g : g x =
        ENNReal.ofReal (‖f x‖ ^ 2) *
          ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal (1 / x) := by
      have := congrArg
          (fun z =>
            z * ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal (1 / x))
          hx_indicator
      simpa [g, mul_comm, mul_left_comm, mul_assoc] using this
    have hx_mul_inv :
        ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal x⁻¹
          = ENNReal.ofReal (x ^ (2 * σ - 2)) := by
      simpa [one_div] using hx_mul
    calc
      g x
          = ENNReal.ofReal (‖f x‖ ^ 2) *
              ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal (1 / x) := hx_g
      _ = ENNReal.ofReal (‖f x‖ ^ 2) *
              (ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal x⁻¹) := by
                simp [mul_comm, mul_assoc]
      _ = ENNReal.ofReal (‖f x‖ ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) := by
                simp [hx_mul_inv]
  have h_step1 :
      ∫⁻ x in Set.Ioi (1 : ℝ), ‖f x‖ₑ ^ (2 : ℝ) ∂μ =
        ∫⁻ x in Set.Ioi (1 : ℝ),
          ENNReal.ofReal (‖f x‖ ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
    have h_lintegral := lintegral_congr_ae h_weight_simplify
    have h_final :
        ∫⁻ x in Set.Ioi (1 : ℝ), g x ∂volume =
          ∫⁻ x in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (‖f x‖ ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
      simpa using h_lintegral
    calc
      ∫⁻ x in Set.Ioi (1 : ℝ), ‖f x‖ₑ ^ (2 : ℝ) ∂μ
          = ∫⁻ x in Set.Ioi (0 : ℝ), g x ∂volume := h_volume_eq
      _ = ∫⁻ x in Set.Ioi (1 : ℝ), g x ∂volume := h_restrict
      _ = ∫⁻ x in Set.Ioi (1 : ℝ),
              ENNReal.ofReal (‖f x‖ ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := h_final
  -- Step 2 onwards: control the integrand using Schwartz decay and show integrability.
  -- These estimates will be supplied in subsequent steps.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, σ + 1 < k := exists_nat_gt (σ + 1)
  set C := SchwartzMap.seminorm ℝ k 0 f with hC_def
  have hC_nonneg : 0 ≤ C := by
    have := apply_nonneg (SchwartzMap.seminorm ℝ k 0) f
    simp [C]
  have h_polynomial_decay :
      ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (1 : ℝ) → ‖f x‖ ≤ C / x ^ k := by
    intro x hx
    have hx_gt_one : 1 < x := hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx_gt_one
    have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
    have hx_abs : |x| = x := abs_of_nonneg hx_nonneg
    have h_mul := (SchwartzMap.norm_pow_mul_le_seminorm ℝ f k x)
    have h_mul' : ‖f x‖ * |x| ^ k ≤ C := by
      simpa [C, Real.norm_eq_abs, hx_abs, mul_comm, mul_left_comm, mul_assoc] using h_mul
    have hx_abs_pos : 0 < |x| := by simpa [hx_abs] using hx_pos
    have hx_pow_pos : 0 < |x| ^ k := pow_pos hx_abs_pos _
    have h_div : ‖f x‖ ≤ C / |x| ^ k := (le_div_iff₀ hx_pow_pos).2 h_mul'
    simpa [hx_abs] using h_div
  have h_decay_sq :
      ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (1 : ℝ) →
        ENNReal.ofReal (‖f x‖ ^ 2) ≤ ENNReal.ofReal ((C / x ^ k) ^ 2) := by
    intro x hx
    have h_decay_x := h_polynomial_decay hx
    have hx_gt_one : 1 < x := hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx_gt_one
    have hx_pow_pos : 0 < x ^ k := pow_pos hx_pos _
    have h_rhs_nonneg : 0 ≤ C / x ^ k := div_nonneg hC_nonneg (le_of_lt hx_pow_pos)
    have h_sq := mul_le_mul h_decay_x h_decay_x (norm_nonneg _) h_rhs_nonneg
    have h_sq' : ‖f x‖ ^ 2 ≤ (C / x ^ k) ^ 2 := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h_sq
    exact ENNReal.ofReal_le_ofReal h_sq'
  have h_integrand_bound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (1 : ℝ)),
        ENNReal.ofReal (‖f x‖ ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) ≤
          ENNReal.ofReal ((C / x ^ k) ^ 2) *
            ENNReal.ofReal (x ^ (2 * σ - 2)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx_gt_one : 1 < x := hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx_gt_one
    have h_le := h_decay_sq hx
    have hx_weight_pos : 0 < x ^ (2 * σ - 2) := Real.rpow_pos_of_pos hx_pos _
    have hx_weight_ne_zero : ENNReal.ofReal (x ^ (2 * σ - 2)) ≠ 0 :=
      (ENNReal.ofReal_ne_zero_iff).2 hx_weight_pos
    have h_mul :=
      (ENNReal.mul_le_mul_right hx_weight_ne_zero (by simp)).2 h_le
    exact h_mul
  -- Step 3: use `h_integrand_bound` together with integrability of the dominating weight
  -- to conclude the finiteness of the tail integral.
  set a : ℝ := 2 * σ - 2 - 2 * (k : ℝ) with ha_def
  have hk_real : σ + 1 < (k : ℝ) := by exact_mod_cast hk
  have hk_diff : σ - 1 - (k : ℝ) < -2 := by
    linarith [hk_real]
  have ha_eq : a = (2 : ℝ) * (σ - 1 - (k : ℝ)) := by
    simp [ha_def, sub_eq_add_neg, mul_add]
  have ha_lt4 : a < -4 := by
    have two_pos : (0 : ℝ) < 2 := by norm_num
    have h_mul := mul_lt_mul_of_pos_left hk_diff two_pos
    have h_rhs : (2 : ℝ) * (-2) = -4 := by norm_num
    simpa [ha_eq, h_rhs] using h_mul
  have ha_lt : a < -1 := ha_lt4.trans (by norm_num)
  have h_integrable_rpow :
      IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioi (1 : ℝ)) volume :=
    integrableOn_Ioi_rpow_of_lt ha_lt zero_lt_one
  let φ : ℝ → ℝ := fun x => C ^ 2 * x ^ a
  have h_integrable_phi :
      IntegrableOn φ (Set.Ioi (1 : ℝ)) volume := by
    have h_int :=
      Integrable.const_mul (μ := volume.restrict (Set.Ioi (1 : ℝ)))
        (c := C ^ 2) (IntegrableOn.integrable h_integrable_rpow)
    simpa [IntegrableOn, φ]
  have h_lintegral_le :
      ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (‖f x‖ ^ 2) *
          ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume ≤
        ∫⁻ x in Set.Ioi (1 : ℝ),
            ENNReal.ofReal ((C / x ^ k) ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
    have :=
      lintegral_mono_ae
        (μ := volume.restrict (Set.Ioi (1 : ℝ))) h_integrand_bound
    simpa using this
  have h_phi_eq :
      (fun x : ℝ => ENNReal.ofReal ((C / x ^ k) ^ 2) *
          ENNReal.ofReal (x ^ (2 * σ - 2))) =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
        fun x => ENNReal.ofReal (φ x) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
    have hx_rpow_sub :
        x ^ a = x ^ (2 * σ - 2) / x ^ (2 * (k : ℝ)) := by
      simpa [ha_def] using
        Real.rpow_sub hx_pos (2 * σ - 2) (2 * (k : ℝ))
    have hx_rpow_nat : x ^ (k : ℝ) = x ^ k := by
      simp
    have hx_rpow_mul : x ^ (2 * (k : ℝ)) = (x ^ k) ^ 2 := by
      have hx_mul := Real.rpow_mul hx_nonneg (k : ℝ) (2 : ℝ)
      have hk_comm : (k : ℝ) * 2 = 2 * (k : ℝ) := by ring
      simpa [hk_comm, hx_rpow_nat, pow_two] using hx_mul
    have hx_div_eq : x ^ (2 * σ - 2) / (x ^ k) ^ 2 = x ^ a := by
      simpa [hx_rpow_mul, ha_def] using hx_rpow_sub.symm
    have hx_expr : (C / x ^ k) ^ 2 = C ^ 2 / (x ^ k) ^ 2 := by
      simpa [pow_two] using (div_pow C (x ^ k) (2 : ℕ))
    have hx_eq :
        (C / x ^ k) ^ 2 * x ^ (2 * σ - 2) =
          C ^ 2 * x ^ (2 * σ - 2) / (x ^ k) ^ 2 := by
      calc
        (C / x ^ k) ^ 2 * x ^ (2 * σ - 2)
            = (C ^ 2 / (x ^ k) ^ 2) * x ^ (2 * σ - 2) := by
                simp [hx_expr, mul_comm]
        _ = C ^ 2 * x ^ (2 * σ - 2) / (x ^ k) ^ 2 :=
              (div_mul_eq_mul_div (C ^ 2) ((x ^ k) ^ 2) (x ^ (2 * σ - 2)))
    have hx_phi_formula :
        φ x = C ^ 2 * x ^ (2 * σ - 2) / (x ^ k) ^ 2 := by
      unfold φ
      have hx_div_eq' : x ^ a = x ^ (2 * σ - 2) / (x ^ k) ^ 2 := by
        simpa using hx_div_eq.symm
      calc
        C ^ 2 * x ^ a
            = C ^ 2 * (x ^ (2 * σ - 2) / (x ^ k) ^ 2) := by
                rw [hx_div_eq']
        _ = C ^ 2 * x ^ (2 * σ - 2) / (x ^ k) ^ 2 := by
                simp [div_eq_mul_inv, mul_comm, mul_assoc]
    have hx_sq_nonneg : 0 ≤ (C / x ^ k) ^ 2 := sq_nonneg _
    have hx_rpow_nonneg : 0 ≤ x ^ (2 * σ - 2) :=
      Real.rpow_nonneg hx_nonneg _
    have hx_mul_value :
        ENNReal.ofReal ((C / x ^ k) ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) =
          ENNReal.ofReal (C ^ 2 * x ^ (2 * σ - 2) / (x ^ k) ^ 2) := by
      have hx_mul' :
          ENNReal.ofReal ((C / x ^ k) ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) =
            ENNReal.ofReal (((C / x ^ k) ^ 2) * x ^ (2 * σ - 2)) := by
          simp [ENNReal.ofReal_mul, hx_sq_nonneg]
      simpa [hx_eq] using hx_mul'
    have hx_phi_value :
        ENNReal.ofReal (φ x) =
          ENNReal.ofReal (C ^ 2 * x ^ (2 * σ - 2) / (x ^ k) ^ 2) := by
      simp [hx_phi_formula]
    have hx_final :
        ENNReal.ofReal ((C / x ^ k) ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) =
          ENNReal.ofReal (φ x) := by
      simpa [hx_phi_value] using hx_mul_value
    exact hx_final
  have h_integral_dom_lt :
      ∫⁻ x in Set.Ioi (1 : ℝ),
          ENNReal.ofReal ((C / x ^ k) ^ 2) *
            ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume < ∞ := by
    have h_lintegral_phi :=
      IntegrableOn.setLIntegral_lt_top (μ := volume) (s := Set.Ioi (1 : ℝ))
        h_integrable_phi
    have h_congr :=
      lintegral_congr_ae (μ := volume.restrict (Set.Ioi (1 : ℝ))) h_phi_eq
    have h_eq :
        ∫⁻ x in Set.Ioi (1 : ℝ),
            ENNReal.ofReal ((C / x ^ k) ^ 2) *
              ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume
          = ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (φ x) ∂volume := by
      simpa using h_congr
    exact h_eq ▸ h_lintegral_phi
  have h_tail_le :
      ∫⁻ x in Set.Ioi (1 : ℝ), ‖f x‖ₑ ^ (2 : ℝ) ∂μ ≤
        ∫⁻ x in Set.Ioi (1 : ℝ),
            ENNReal.ofReal ((C / x ^ k) ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
    exact (le_of_eq h_step1).trans h_lintegral_le
  have h_tail_lt := lt_of_le_of_lt h_tail_le h_integral_dom_lt
  simpa [h_step1] using h_tail_lt

/-- Schwartz functions restricted to (0,∞) belong to Hσ for σ > 1/2 -/
lemma schwartz_mem_Hσ {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => if x > 0 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
  -- For σ > 1/2, the weight x^(2σ-2) ensures integrability near 0
  -- A Schwartz function has rapid decay, so the integral converges at infinity

  -- Step 1: Show the function is AEStronglyMeasurable
  have h_meas : AEStronglyMeasurable (fun x => if x > 0 then f x else 0)
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
    -- Schwartz functions are continuous, hence measurable
    -- The restriction to (0,∞) preserves measurability
    apply AEStronglyMeasurable.indicator
    · -- Show f is AEStronglyMeasurable on the whole space
      have : Continuous (fun x : ℝ => (f x : ℂ)) := SchwartzMap.continuous f
      exact Continuous.aestronglyMeasurable this
    · -- Show {x : x > 0} is a measurable set
      exact measurableSet_Ioi

  -- Step 2: Show the L² norm is finite
  rw [MemLp]
  constructor
  · -- AEStronglyMeasurable part
    exact h_meas
  · -- eLpNorm is finite
    -- We need to show: ∫⁻ x, ‖if x > 0 then f x else 0‖^2 * x^(2*σ-1) < ∞

    -- Convert to ENNReal integral over (0,∞)
    have h_eq : eLpNorm (fun x => if x > 0 then f x else 0) 2
        (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) < ∞ := by
      -- The eLpNorm for p = 2 is the square root of the integral
      have hp_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
      have hp_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
      rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
      simp only [ENNReal.toReal_ofNat]

      -- Show that the integral is finite
      have h_integral : ∫⁻ x, ‖if x > 0 then f x else 0‖ₑ ^ (2 : ℝ)
          ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) < ∞ := by
        -- The integral simplifies to an integral over (0,∞)
        -- Split into (0,1] and (1,∞) for analysis

        -- Key observation: on mulHaar.withDensity, the integral is over (0,∞) with weight
        -- For the indicator function, we only integrate over (0,∞)

        -- Simplify the integral using the indicator function
        have h_indicator : ∫⁻ x, ‖if x > 0 then f x else 0‖ₑ ^ (2 : ℝ)
            ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) =
            ∫⁻ x in Set.Ioi (0 : ℝ), ‖f x‖ₑ ^ (2 : ℝ)
            ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
          -- The indicator function agrees with f on (0,∞)
          -- We use the fact that the integral of an indicator function
          -- equals the integral over the indicated set

          -- First, rewrite the left side using indicator notation
          have h_eq : (fun x => ‖if x > 0 then f x else 0‖ₑ ^ (2 : ℝ)) =
              (fun x => Set.indicator (Set.Ioi (0 : ℝ)) (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x) := by
            funext x
            simp only [Set.indicator]
            by_cases h : x > 0
            · -- x > 0 case
              simp only [if_pos h, Set.mem_Ioi.mpr h, if_pos]
            · -- x ≤ 0 case
              simp only [if_neg h]
              have hx_not_in : x ∉ Set.Ioi 0 := by
                simp only [Set.mem_Ioi, not_lt]
                exact le_of_not_gt h
              simp only [hx_not_in, if_neg, not_false_iff]
              -- 0^2 = 0 for ENNReal
              norm_num

          rw [h_eq]
          -- Now use set_lintegral for indicator functions
          rw [lintegral_indicator measurableSet_Ioi]

        rw [h_indicator]

        -- Now we need to show the integral over (0,∞) is finite
        -- This requires:
        -- 1. Near 0: x^(2σ-1) * 1/x = x^(2σ-2) is integrable for σ > 1/2
        -- 2. At infinity: Schwartz decay dominates any polynomial growth

        -- Split the integral into (0,1] and (1,∞)
        have h_split : ∫⁻ x in Set.Ioi (0 : ℝ), ‖f x‖ₑ ^ (2 : ℝ)
            ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) =
            ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ₑ ^ (2 : ℝ)
              ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) +
            ∫⁻ x in Set.Ioi (1 : ℝ), ‖f x‖ₑ ^ (2 : ℝ)
              ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
          -- Split Ioi 0 = Ioc 0 1 ∪ Ioi 1
          -- Note: Ioc 0 1 = {x | 0 < x ≤ 1}, Ioi 1 = {x | 1 < x}
          have h_union : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
            ext x
            simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
            constructor
            · intro hx
              by_cases h : x ≤ 1
              · left
                exact ⟨hx, h⟩
              · right
                -- h : ¬(x ≤ 1) means 1 < x
                push_neg at h
                exact h
            · intro h
              cases h with
              | inl h => exact h.1
              | inr h => exact zero_lt_one.trans h

          -- The sets are disjoint
          have h_disj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) := by
            rw [Set.disjoint_iff]
            intro x hx
            simp only [Set.mem_Ioc, Set.mem_Ioi, Set.mem_inter_iff, Set.mem_empty_iff_false] at hx ⊢
            exact not_lt.mpr hx.1.2 hx.2

          -- Apply lintegral_union for disjoint measurable sets
          rw [show ∫⁻ x in Set.Ioi (0 : ℝ), ‖f x‖ₑ ^ (2 : ℝ)
                ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) =
              ∫⁻ x in Set.Ioc 0 1 ∪ Set.Ioi 1, ‖f x‖ₑ ^ (2 : ℝ)
                ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) by
            rw [←h_union]]
          -- Apply the correct lintegral_union for disjoint sets
          -- Try different argument orders to find the correct signature
          have h_meas1 : MeasurableSet (Set.Ioc (0 : ℝ) 1) := measurableSet_Ioc
          have h_meas2 : MeasurableSet (Set.Ioi (1 : ℝ)) := measurableSet_Ioi

          -- Apply our custom lintegral_union_disjoint lemma
          rw [lintegral_union_disjoint (mulHaar.withDensity fun x =>
              ENNReal.ofReal (x ^ (2 * σ - 1)))
              h_meas1 h_meas2 h_disj (fun x => ‖f x‖ₑ ^ (2 : ℝ))]
          -- Show measurability of the function
          · apply Measurable.pow_const
            apply Measurable.enorm
            exact SchwartzMap.continuous f |>.measurable

        rw [h_split]

        -- Show both parts are finite
        have h_finite_1 : ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ₑ ^ (2 : ℝ)
            ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) < ∞ :=
          schwartz_finite_on_unit_interval hσ f

        have h_finite_2 : ∫⁻ x in Set.Ioi (1 : ℝ), ‖f x‖ₑ ^ (2 : ℝ)
            ∂(mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) < ∞ :=
          schwartz_finite_on_tail f

        exact ENNReal.add_lt_top.mpr ⟨h_finite_1, h_finite_2⟩

      -- If the integral is finite, then its square root is also finite
      have h_pos : (0 : ℝ) < 1 / 2 := by norm_num
      rw [ENNReal.rpow_lt_top_iff_of_pos h_pos]
      exact h_integral

    exact h_eq

/-- The embedding of Schwartz functions into Hσ for σ > 1/2 -/
noncomputable def schwartzToHσ {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) : Hσ σ :=
  MemLp.toLp (fun x => if x > 0 then f x else 0) (schwartz_mem_Hσ hσ f)

/-- The embedding is linear for σ > 1/2 -/
lemma schwartzToHσ_linear {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∀ (a : ℂ) (f g : SchwartzMap ℝ ℂ),
    schwartzToHσ hσ (a • f + g) = a • schwartzToHσ hσ f + schwartzToHσ hσ g := by
  intro a f g
  -- Show that the underlying functions agree almost everywhere
  have h_ae : (fun x => if x > 0
      then (a • f + g) x else 0) =ᵐ[mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))]
      (fun x => a • (if x > 0 then f x else 0) + (if x > 0 then g x else 0)) := by
    apply ae_of_all
    intro x
    by_cases h : x > 0
    · -- Case x > 0
      simp only [if_pos h]
      rw [SchwartzMap.add_apply, SchwartzMap.smul_apply]
    · -- Case x ≤ 0
      simp only [if_neg h]
      simp only [smul_zero, zero_add]

  -- Use linearity of MemLp.toLp
  rw [schwartzToHσ, schwartzToHσ, schwartzToHσ]
  -- Convert to a statement about MemLp.toLp
  have h_mem_af_g : MemLp (fun x => if x > 0 then (a • f + g) x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    schwartz_mem_Hσ hσ (a • f + g)

  have h_mem_f : MemLp (fun x => if x > 0 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    schwartz_mem_Hσ hσ f

  have h_mem_g : MemLp (fun x => if x > 0 then g x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    schwartz_mem_Hσ hσ g

  -- The key insight: MemLp.toLp preserves linear combinations
  -- when the underlying functions agree almost everywhere
  have h_smul_mem : MemLp (fun x => a • (if x > 0 then f x else 0)) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    MemLp.const_smul h_mem_f a

  have h_sum_mem : MemLp (fun x => a • (if x > 0 then f x else 0) + (if x > 0 then g x else 0)) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    MemLp.add h_smul_mem h_mem_g

  -- Convert h_mem_af_g using h_ae to match the linear combination
  have h_eq_ae : MemLp.toLp (fun x => if x > 0 then (a • f + g) x else 0) h_mem_af_g =
      MemLp.toLp (fun x => a • (if x > 0 then f x else 0) +
      (if x > 0 then g x else 0)) h_sum_mem := by
    apply MemLp.toLp_congr h_mem_af_g h_sum_mem h_ae

  rw [h_eq_ae]
  -- Apply the linearity theorems directly
  -- First, recognize that h_sum_mem = h_smul_mem.add h_mem_g
  have h_eq1 : MemLp.toLp (fun x => a • (if x > 0 then f x else 0) +
      (if x > 0 then g x else 0)) h_sum_mem =
      MemLp.toLp (fun x => a • (if x > 0 then f x else 0)) h_smul_mem +
      MemLp.toLp (fun x => if x > 0 then g x else 0) h_mem_g := by
    -- Use the fact that h_sum_mem was constructed as MemLp.add h_smul_mem h_mem_g
    exact MemLp.toLp_add h_smul_mem h_mem_g

  rw [h_eq1]
  -- Now apply scalar multiplication linearity
  have h_eq2 : MemLp.toLp (fun x => a • (if x > 0 then f x else 0)) h_smul_mem =
      a • MemLp.toLp (fun x => if x > 0 then f x else 0) h_mem_f := by
    -- Use the fact that h_smul_mem was constructed as MemLp.const_smul h_mem_f a
    exact MemLp.toLp_const_smul a h_mem_f

  rw [h_eq2]

/-- The norm of the toLp embedding equals the ENNReal.toReal of the eLpNorm -/
lemma norm_toLp_eq_toReal_eLpNorm {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) :
    ‖(schwartz_mem_Hσ hσ f).toLp (fun x => if x > 0 then f x else 0)‖ =
    ENNReal.toReal (eLpNorm (fun x => if x > 0 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) := by
  exact MeasureTheory.Lp.norm_toLp _ _

/-- Bound for the eLpNorm of a Schwartz function on the tail (1,∞) -/
lemma eLpNorm_bound_on_tail {σ : ℝ} {k₁ : ℕ} (f : SchwartzMap ℝ ℂ) :
    eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
    ENNReal.ofReal (SchwartzMap.seminorm ℝ k₁ 0 f) := by
  -- At infinity: use Schwartz decay property
  -- The key insight: for x > 1, we have ‖f(x)‖ ≤ C * x^(-k₁) for some C
  -- and x^(2σ-1) * x^(-2k₁) is integrable if k₁ is large enough

  -- Use the Schwartz seminorm bound: ‖x‖^k₁ * ‖iteratedFDeriv ℝ 0 f(x)‖ ≤ seminorm k₁ 0 f
  have h_schwartz_bound : ∀ x : ℝ, ‖x‖ ^ k₁ *
      ‖iteratedFDeriv ℝ 0 f x‖ ≤ SchwartzMap.seminorm ℝ k₁ 0 f := by
    intro x
    exact SchwartzMap.le_seminorm ℝ k₁ 0 f x

  -- Since iteratedFDeriv ℝ 0 f gives f(x) as a 0-multilinear map
  have h_norm_iteratedFDeriv_zero : ∀ x : ℝ,
      ‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖ := by
    intro x
    -- This should follow from the fact that iteratedFDeriv at order 0
    -- is essentially the identity after unwrapping the multilinear structure
    sorry

  -- For x > 1, this gives ‖f(x)‖ ≤ (seminorm / x^k₁)
  have h_decay_bound : ∀ x : ℝ, x > 1 →
      ‖f x‖ ≤ SchwartzMap.seminorm ℝ k₁ 0 f / x ^ k₁ := by
    intro x hx
    have h_pos : 0 < x ^ k₁ := by
      apply pow_pos
      linarith [hx]
    -- Use the fact that for x > 1, we have ‖x‖ = x
    have hx_eq : ‖x‖ = x := by
      simp only [Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hx)]
    -- Apply the Schwartz bound
    specialize h_schwartz_bound x
    rw [h_norm_iteratedFDeriv_zero x, hx_eq] at h_schwartz_bound
    -- Now h_schwartz_bound says: x^k₁ * ‖f x‖ ≤ seminorm
    -- We want: ‖f x‖ ≤ seminorm / x^k₁
    rw [le_div_iff₀ h_pos, mul_comm]
    exact h_schwartz_bound

  -- Use this decay bound to control the eLpNorm integral
  sorry -- Apply the decay bound to bound the weighted L² norm

/-- Bound for the eLpNorm of a Schwartz function on the unit interval (0,1] -/
lemma eLpNorm_bound_on_unit_interval {σ : ℝ} (hσ : 1 / 2 < σ)
    (f : SchwartzMap ℝ ℂ) (M : ℝ)
    (hM_bound : (∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal M) :
    eLpNorm (fun x => if x ∈ Set.Ioc 0 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
    ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 f * M) := by
  -- Near 0: use boundedness from the fact that Schwartz functions are bounded
  -- and the weight is integrable on (0,1]
  sorry -- Use boundedness and weight integrability

/-- Splitting the eLpNorm of a function on (0,∞) into (0,1] and (1,∞) parts -/
lemma eLpNorm_split_at_one {σ : ℝ} (f : SchwartzMap ℝ ℂ) :
    eLpNorm (fun x => if x > 0 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
    eLpNorm (fun x => if x ∈ Set.Ioc 0 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) +
    eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
  -- This follows from the triangle inequality for eLpNorm
  -- since (0,∞) = (0,1] ∪ (1,∞)
  sorry -- Triangle inequality for eLpNorm

/-- The weight function has finite L² norm for σ > 1/2 -/
lemma weight_function_L2_bound {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ M : ℝ, 0 < M ∧
    (∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar) ^ (1/2 : ℝ) ≤ ENNReal.ofReal M := by
  -- The L^2 norm of the weight function is finite for σ > 1/2
  -- This follows from the integrability of x^(2σ-1) on (0,∞) when 2σ - 1 > -1
  sorry -- Technical bound on weight function

/-- The embedding is continuous with respect to appropriate Schwartz seminorms for σ > 1/2 -/
lemma schwartzToHσ_continuous {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ (k₁ k₂ : ℕ) (C : ℝ), 0 < C ∧
    ∀ f : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ f‖ ≤ C * SchwartzMap.seminorm ℝ k₁ k₂ f := by
  -- For σ > 1/2, the weight x^(2σ-2) is integrable near 0
  -- The seminorms k₁, k₂ need to control the behavior at infinity
  -- k₁ controls polynomial growth, k₂ controls smoothness

  -- Choose seminorm parameters: k₁ for polynomial decay, k₂ = 0 for just function values
  let k₁ : ℕ := ⌊4 * σ + 2⌋₊  -- Ensure enough decay at infinity
  let k₂ : ℕ := 0              -- Only need function values, not derivatives

  -- Define the constant C based on the weight integral bounds
  obtain ⟨M, hM_pos, hM_bound⟩ := weight_function_L2_bound hσ
  use k₁, k₂, M + 1
  constructor
  · linarith [hM_pos]
  · intro f
    -- Estimate the Hilbert space norm
    rw [schwartzToHσ]
    -- Use the fact that ‖MemLp.toLp f hf‖ = ENNReal.toReal (eLpNorm f p μ)
    rw [norm_toLp_eq_toReal_eLpNorm hσ f]

    -- Show that ENNReal.toReal of a bound gives the desired inequality
    suffices h_eLp : eLpNorm (fun x => if x > 0 then f x else 0) 2
        (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
        ENNReal.ofReal ((M + 1) * SchwartzMap.seminorm ℝ k₁ k₂ f) by
      have h_nonneg : 0 ≤ (M + 1) * SchwartzMap.seminorm ℝ k₁ k₂ f := by
        apply mul_nonneg
        · linarith [hM_pos]
        · exact apply_nonneg (SchwartzMap.seminorm ℝ k₁ k₂) f
      exact ENNReal.toReal_le_of_le_ofReal h_nonneg h_eLp

    -- The L^2 norm with weight can be bounded by Schwartz seminorms
    -- Split the integral into (0,1] and (1,∞)
    have h_split := @eLpNorm_split_at_one σ f

    -- Bound each part using Schwartz properties
    have h_bound1 := eLpNorm_bound_on_unit_interval hσ f M hM_bound

    have h_bound2 := @eLpNorm_bound_on_tail σ k₁ f

    -- Combine bounds
    have h_seminorm_mono : SchwartzMap.seminorm ℝ 0 0 f ≤ SchwartzMap.seminorm ℝ k₁ k₂ f := by
        -- Seminorms are monotonic in their indices
        sorry

    -- Complete the bound combination
    -- Use triangle inequality and the bounds we've established
    -- Combine the bounds using the splitting and individual estimates
    have h_final : eLpNorm (fun x => if x > 0 then f x else 0) 2
          (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
        ENNReal.ofReal ((M + 1) * SchwartzMap.seminorm ℝ k₁ k₂ f) := by
      -- Apply splitting inequality then individual bounds
      have step1 := le_trans h_split (add_le_add h_bound1 h_bound2)
      -- Use seminorm monotonicity to get the final bound
      sorry -- Complete the seminorm bound combination
    exact h_final

/-- Schwartz functions are dense in Hσ for σ > 1/2 -/
theorem schwartz_dense_in_Hσ {σ : ℝ} (hσ : 1 / 2 < σ) :
    DenseRange (schwartzToHσ hσ) := by
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
  have h_smooth_dense : ∃ (g : ℝ → ℂ)
      (hg_mem : MemLp g 2 (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))),
      HasCompactSupport g ∧ ContDiff ℝ ⊤ g ∧ dist f (hg_mem.toLp g) < ε / 2 := by
    -- Use the density of smooth compactly supported functions in weighted L² spaces
    -- First, we note that for σ > 1/2, the weight function x^(2σ-1) is locally integrable
    have h_weight_integrable : LocallyIntegrableOn
        (fun x : ℝ => x ^ (2 * σ - 1 : ℝ)) (Set.Ioi 0) mulHaar := by
      -- For σ > 1/2, we have 2σ - 1 > 0, so x^(2σ-1) is integrable near 0
      -- Use the fact that x^α is locally integrable for α > -1
      have h_exponent_pos : 2 * σ - 1 > -1 := by
        linarith [hσ]  -- Since σ > 1/2, we have 2σ > 1, so 2σ - 1 > 0 > -1
      -- Apply standard integrability result for power functions
      -- For the Haar measure on ℝ, we need to establish it's locally finite
      -- Since continuous functions on locally finite measures are locally integrable
      sorry -- LocallyIntegrableOn for power functions with Haar measure

    -- Use the standard density result for weighted L² spaces
    -- This follows from mollification and truncation arguments
    sorry -- Apply density theorem for weighted L² spaces

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
    sorry -- Bound using compact support

  -- Construct the Schwartz function from g
  -- Note: SchwartzMap requires ContDiff ℝ (↑⊤) but we have ContDiff ℝ ⊤
  -- These are the same, but we need to handle the type difference
  let φ : SchwartzMap ℝ ℂ := {
    toFun := g
    smooth' := by
      -- Use the fact that ContDiff ℝ ⊤ g implies smoothness
      sorry -- Type conversion for smoothness
    decay' := hg_schwartz
  }

  -- Step 3: Show that schwartzToHσ hσ φ approximates f
  -- We need to show ∃ y ∈ Set.range (schwartzToHσ hσ), dist f y < ε
  use schwartzToHσ hσ φ
  refine ⟨?_, ?_⟩
  · -- Show that schwartzToHσ hσ φ is in the range
    use φ
  · -- Show the distance bound
    sorry -- Show dist f (schwartzToHσ hσ φ) < ε using hg_close

/-- For any f ∈ Hσ, schwartzToHσ hσ φ and the truncated φ agree a.e. for σ > 1/2 -/
lemma schwartzToHσ_ae_eq {σ : ℝ} (hσ : 1 / 2 < σ) (φ : SchwartzMap ℝ ℂ) :
    (schwartzToHσ hσ φ : ℝ → ℂ) =ᵐ[mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))]
      (fun x => if x > 0 then φ x else 0) := by
  -- This follows from the definition of MemLp.toLp
  exact MemLp.coeFn_toLp _

/-- For any f ∈ Hσ and ε > 0, there exists a Schwartz function approximating f for σ > 1/2 -/
lemma exists_schwartz_approximation {σ : ℝ} (hσ : 1 / 2 < σ) (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ φ - f‖ < ε := by
  have h_dense := schwartz_dense_in_Hσ hσ
  rw [DenseRange] at h_dense
  have hf_in_closure := h_dense.closure_eq ▸ Set.mem_univ f
  rw [Metric.mem_closure_iff] at hf_in_closure
  obtain ⟨g, hg_range, hg_close⟩ := hf_in_closure ε hε
  obtain ⟨φ, rfl⟩ := hg_range
  use φ
  rw [dist_eq_norm] at hg_close
  rw [←norm_sub_rev]
  exact hg_close

/-- Schwartz approximation with a.e. convergence for σ > 1/2 -/
lemma schwartz_ae_dense {σ : ℝ} (hσ : 1 / 2 < σ) (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ φ - f‖ < ε ∧
    (schwartzToHσ hσ φ : ℝ → ℂ) =ᵐ[mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))]
      (fun x => if x > 0 then φ x else 0) := by
  obtain ⟨φ, hφ⟩ := exists_schwartz_approximation hσ f ε hε
  use φ
  constructor
  · exact hφ
  · exact schwartzToHσ_ae_eq hσ φ

end SchwartzDensity

end Frourio
