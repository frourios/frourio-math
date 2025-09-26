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
                simp [hx_div_eq']
        _ = (C ^ 2 * x ^ (2 * σ - 2)) / (x ^ k) ^ 2 := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  (mul_div_assoc (C ^ 2) (x ^ (2 * σ - 2)) ((x ^ k) ^ 2)).symm
        _ = C ^ 2 * x ^ (2 * σ - 2) / (x ^ k) ^ 2 := rfl
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

/-- For any f ∈ Hσ, schwartzToHσ hσ φ and the truncated φ agree a.e. for σ > 1/2 -/
lemma schwartzToHσ_ae_eq {σ : ℝ} (hσ : 1 / 2 < σ) (φ : SchwartzMap ℝ ℂ) :
    (schwartzToHσ hσ φ : ℝ → ℂ) =ᵐ[mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))]
      (fun x => if x > 0 then φ x else 0) := by
  -- This follows from the definition of MemLp.toLp
  exact MemLp.coeFn_toLp _

/- Bound for the eLpNorm of a Schwartz function on the tail (1,∞) when the
decay exponent dominates the weight. -/
lemma eLpNorm_bound_on_tail {σ : ℝ} {k₁ : ℕ}
    (hσk : σ + 1 / 2 ≤ (k₁ : ℝ)) (f : SchwartzMap ℝ ℂ) :
    eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
    ENNReal.ofReal (SchwartzMap.seminorm ℝ k₁ 0 f * Real.sqrt (1 / (2 * k₁ - 2 * σ))) := by
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
    simp

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
  have h_pointwise_decay : ∀ x : ℝ,
      ‖if x ∈ Set.Ioi (1 : ℝ) then f x else 0‖ ≤
        (if x ∈ Set.Ioi (1 : ℝ) then
          SchwartzMap.seminorm ℝ k₁ 0 f / x ^ k₁ else 0) := by
    intro x
    by_cases hx : x ∈ Set.Ioi (1 : ℝ)
    · have hx_gt : x > 1 := hx
      simpa [hx] using h_decay_bound x hx_gt
    · simp [hx]
  set μ := mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))
  set C := SchwartzMap.seminorm ℝ k₁ 0 f with hC_def
  have hC_nonneg : 0 ≤ C := by
    have := apply_nonneg (SchwartzMap.seminorm ℝ k₁ 0) f
    simp [C]
  have h_cast_nat : ((2 * k₁ : ℕ) : ℝ) = 2 * (k₁ : ℝ) := by norm_cast
  have h_ae_decay_bound :
      (fun x => ‖if x ∈ Set.Ioi (1 : ℝ) then f x else 0‖)
        ≤ᵐ[μ]
      (fun x => if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : x ∈ Set.Ioi (1 : ℝ)
    · have hx_gt : x > 1 := hx
      simpa [μ, C, hx] using h_decay_bound x hx_gt
    · simp [hx]
  have h_ae_decay_sq :
      (fun x => ENNReal.ofReal (‖if x ∈ Set.Ioi (1 : ℝ) then f x else 0‖ ^ 2))
        ≤ᵐ[μ]
      (fun x => ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2)) := by
    refine h_ae_decay_bound.mono ?_
    intro x hx
    by_cases hx_set : x ∈ Set.Ioi (1 : ℝ)
    · have hx_bound : ‖f x‖ ≤ C / x ^ k₁ := by
        simpa [μ, C, hx_set] using hx
      have hx_gt : 1 < x := hx_set
      have hx_pos : 0 < x := lt_trans zero_lt_one hx_gt
      have hx_pow_nonneg : 0 ≤ x ^ k₁ := pow_nonneg (le_of_lt hx_pos) _
      have hx_rhs_nonneg : 0 ≤ C / x ^ k₁ := div_nonneg hC_nonneg hx_pow_nonneg
      have h_sq := mul_le_mul hx_bound hx_bound (norm_nonneg _) hx_rhs_nonneg
      have h_sq' : ‖f x‖ ^ 2 ≤ (C / x ^ k₁) ^ 2 := by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h_sq
      have hx_norm_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
      have hx_norm_sq_pow : ‖f x‖ₑ ^ 2 = ENNReal.ofReal (‖f x‖ ^ 2) := by
        simp
      have hx_ofReal :
          ENNReal.ofReal (‖f x‖ ^ 2) ≤ ENNReal.ofReal ((C / x ^ k₁) ^ 2) :=
        ENNReal.ofReal_le_ofReal h_sq'
      have hx_target :
          ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal ((C / x ^ k₁) ^ 2) := by
        simpa using (hx_norm_sq_pow.symm ▸ hx_ofReal)
      simpa [hx_set] using hx_target
    · simp [hx_set]
  have h_integral_bound :
      ∫⁻ x, ENNReal.ofReal (‖if x ∈ Set.Ioi (1 : ℝ) then f x else 0‖ ^ 2) ∂μ ≤
        ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ :=
    lintegral_mono_ae h_ae_decay_sq
  -- Use the definition of eLpNorm to bound it using the integral
  -- eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ^2 ∂μ)^(1/2)

  have h_fun :
      (fun x : ℝ => if x ∈ Set.Ioi 1 then f x else 0) =
        fun x : ℝ => if 1 < x then f x else 0 := by
    funext x
    by_cases hx : 1 < x
    · simp [hx, Set.mem_Ioi]
    · simp [hx, Set.mem_Ioi]

  have h_eLpNorm_sq : (eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2 μ) ^ (2 : ℝ) =
      ∫⁻ x, ‖if x ∈ Set.Ioi 1 then f x else 0‖ₑ ^ (2 : ℝ) ∂μ := by
    have h :=
      (eLpNorm_nnreal_pow_eq_lintegral
        (μ := μ)
        (f := fun x : ℝ => if x ∈ Set.Ioi (1 : ℝ) then f x else 0)
        (p := (2 : NNReal))
        (by
          exact_mod_cast (two_ne_zero : (2 : ℝ) ≠ 0)))
    have h_coe : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_cast
    simpa [h_coe, h_fun] using h

  -- Convert the norm to match our bound
  have h_norm_eq : ∫⁻ x, ‖if x ∈ Set.Ioi 1 then f x else 0‖ₑ ^ (2 : ℝ) ∂μ =
      ∫⁻ x, ENNReal.ofReal (‖if x ∈ Set.Ioi 1 then f x else 0‖ ^ 2) ∂μ := by
    congr
    funext x
    simp [pow_two]

  -- First, use the integral bound to get an inequality for the square
  have h_sq_bound : (eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2 μ) ^ (2 : ℝ) ≤
      ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ := by
    have h' := h_integral_bound
    calc
      (eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2 μ) ^ (2 : ℝ)
          = ∫⁻ x, ‖if x ∈ Set.Ioi 1 then f x else 0‖ₑ ^ (2 : ℝ) ∂μ := h_eLpNorm_sq
      _ ≤ ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ := by
          simpa [h_norm_eq.symm, Set.mem_Ioi, h_fun] using h'

  -- Take square root of both sides
  have h_sqrt : eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2 μ ≤
      (∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ)
        ^ (1/2 : ℝ) := by
    have h := ENNReal.rpow_le_rpow h_sq_bound (by positivity : 0 ≤ (1 / 2 : ℝ))
    have h_left :
        ((eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2 μ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
          eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2 μ := by
      simp only [one_div]
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
    rw [h_left] at h
    convert h using 1

  -- The integral can be computed explicitly for large k₁
  -- This gives a bound in terms of C and the Schwartz seminorm
  -- For now, we establish the bound using the calculation of the integral
  have h_integral_comp :
      (∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ)
        ^ (1/2 : ℝ) ≤ ENNReal.ofReal (C * Real.sqrt (1 / (2 * k₁ - 2 * σ))) := by
    -- The integral equals C² * ∫₁^∞ x^(2σ-1-2k₁) dx
    -- Since k₁ ≥ σ + 1/2, we have 2σ-1-2k₁ ≤ -2, so the integral converges
    -- and we can bound it appropriately
    have h_exp_bound : 2 * σ - 1 - 2 * (k₁ : ℝ) ≤ -2 := by
      have h1 : (k₁ : ℝ) ≥ σ + 1/2 := by
        exact_mod_cast hσk
      linarith
    -- Use this to show the integral is finite and bounded by C
    -- First, compute the integral by expanding the measure
    have h_integral_expand :
        ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ =
        ENNReal.ofReal (C ^ 2) * ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
        (x ^ (2 * σ - 1 - (↑(2 * k₁) : ℝ))) ∂mulHaar := by
      simp only [μ]
      -- Use the definition of Lebesgue integral with density
      have h_weight : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) :=
        ENNReal.measurable_ofReal.comp (measurable_id.pow_const (2 * σ - 1))
      have h_fun_meas : Measurable fun x : ℝ =>
          ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) := by
        classical
        have h_meas_pow : Measurable fun x : ℝ => x ^ k₁ :=
          (continuous_pow k₁).measurable
        have h_meas_div : Measurable fun x : ℝ => C / x ^ k₁ := by
          simpa [div_eq_mul_inv] using (measurable_const.mul h_meas_pow.inv)
        have h_meas_indicator :
            Measurable fun x : ℝ =>
              if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0 := by
          have h_ind :
              Measurable fun x : ℝ =>
                (Set.Ioi (1 : ℝ)).indicator (fun x => C / x ^ k₁) x :=
            h_meas_div.indicator measurableSet_Ioi
          have h_indicator_eq :
              (fun x : ℝ => (Set.Ioi (1 : ℝ)).indicator (fun x => C / x ^ k₁) x) =
                fun x : ℝ => if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0 := by
            funext x
            by_cases hx : x ∈ Set.Ioi (1 : ℝ)
            · simp [Set.indicator, hx]
            · simp [Set.indicator, hx]
          simpa [h_indicator_eq] using h_ind
        have h_meas_sq :
            Measurable fun x : ℝ =>
              (if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ (2 : ℕ) :=
          h_meas_indicator.pow_const 2
        simpa [Set.mem_Ioi] using ENNReal.measurable_ofReal.comp h_meas_sq
      have h_eq :=
        (lintegral_withDensity_eq_lintegral_mul (μ := mulHaar)
          (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))) h_weight) h_fun_meas
      have h_eq' :
          ∫⁻ x,
              ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2)
                ∂(mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
            = ∫⁻ x,
                ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) *
                  ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar := by
        simpa [Pi.mul_apply, mul_comm]
          using h_eq
      rw [h_eq']
      -- Now simplify the integrand
      have h_integrand : ∀ x, (ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ)
          then C / x ^ k₁ else 0) ^ 2)) * (ENNReal.ofReal (x ^ (2 * σ - 1))) =
          if x ∈ Set.Ioi (1 : ℝ) then
          ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 1 - (↑(2 * k₁) : ℝ))) else 0 := by
        intro x
        by_cases hx : x ∈ Set.Ioi (1 : ℝ)
        · simp [hx]
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C ^ 2)]
          have hx_pos : 0 < x := lt_trans zero_lt_one (Set.mem_Ioi.mp hx)
          have h_cast_nat : ((2 * k₁ : ℕ) : ℝ) = 2 * (k₁ : ℝ) := by norm_cast
          field_simp [ne_of_gt hx_pos]
          rw [pow_two]
          have h_eq : C * C / (x ^ k₁) ^ 2 * x ^ (2 * σ - 1) =
              C * C * x ^ (2 * σ - 1 - 2 * (k₁ : ℝ)) := by
            have : (x ^ k₁) ^ 2 = x ^ (2 * k₁) := by
              rw [← pow_mul, mul_comm]
            rw [this]
            calc C * C / x ^ (2 * k₁) * x ^ (2 * σ - 1)
              = C * C * (x ^ (2 * σ - 1) / x ^ (2 * k₁)) := by ring
              _ = C * C * x ^ ((2 * σ - 1) - (2 * k₁ : ℝ)) := by
                  congr 1
                  rw [← Real.rpow_natCast x (2 * k₁)]
                  rw [← Real.rpow_sub hx_pos]
                  rw [h_cast_nat]
              _ = C * C * x ^ (2 * σ - 1 - 2 * (k₁ : ℝ)) := by
                  rfl
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C * C / (x ^ k₁) ^ 2)]
          exact congr_arg ENNReal.ofReal h_eq
        · simp [hx]
      simp_rw [h_integrand]
      -- Convert if-then-else to indicator
      have h_ind : (fun x =>
          if x ∈ Set.Ioi (1 : ℝ) then
            ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (x ^ (2 * σ - 1 - (↑(2 * k₁) : ℝ))) else 0) =
          fun x =>
            (Set.Ioi (1 : ℝ)).indicator (fun x => ENNReal.ofReal (C ^ 2) *
            ENNReal.ofReal (x ^ (2 * σ - 1 - (↑(2 * k₁) : ℝ)))) x := by
        ext x
        simp [Set.indicator]
      rw [h_ind]
      rw [lintegral_indicator measurableSet_Ioi]
      rw [lintegral_const_mul]
      · have h_meas : Measurable fun x : ℝ =>
            ENNReal.ofReal (x ^ (2 * σ - 1 - (↑(2 * k₁) : ℝ))) :=
          (ENNReal.measurable_ofReal.comp
            (measurable_id.pow_const (2 * σ - 1 - (↑(2 * k₁) : ℝ))))
        exact h_meas
    -- Now bound the remaining integral
    have h_integral_bound : ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
        (x ^ (2 * σ - 1 - (↑(2 * k₁) : ℝ))) ∂mulHaar ≤ ENNReal.ofReal
        (1 / (2 * k₁ - 2 * σ + 1)) := by
      classical
      -- Define the exponent and the associated positive parameter
      set β : ℝ := 2 * σ - 1 - (↑(2 * k₁) : ℝ) with hβ
      set γ : ℝ := 2 * (k₁ : ℝ) - 2 * σ + 1 with hγ
      have hβγ : β = -γ := by
        have h_cast : (↑(2 * k₁) : ℝ) = 2 * (k₁ : ℝ) := by norm_cast
        simp [β, γ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul]
      have hγ_pos : 0 < γ := by
        have hdiff : (1 / 2 : ℝ) ≤ (k₁ : ℝ) - σ := by
          linarith [hσk]
        have htwo : (1 : ℝ) ≤ 2 * ((k₁ : ℝ) - σ) := by
          have := mul_le_mul_of_nonneg_left hdiff (show (0 : ℝ) ≤ 2 by norm_num)
          simpa [two_mul, one_div] using this
        have hge' : (2 : ℝ) ≤ 2 * ((k₁ : ℝ) - σ) + 1 := by
          linarith [htwo]
        have hge : (2 : ℝ) ≤ γ := by
          simpa [γ, two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hge'
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hge
      -- Convert the integral with respect to `mulHaar` into a Lebesgue integral
      have h_convert :
          ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (x ^ β) ∂mulHaar =
            ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (x ^ (β - 1)) ∂volume := by
        classical
        have h_meas_pow : Measurable fun x : ℝ => ENNReal.ofReal (x ^ β) :=
          (ENNReal.measurable_ofReal.comp (by measurability))
        have h_meas_indicator :
            Measurable
              (fun x : ℝ =>
                (Set.Ioi (1 : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ β)) x) :=
          h_meas_pow.indicator measurableSet_Ioi
        have h_expand :=
          lintegral_mulHaar_expand
            (g := fun x : ℝ =>
              (Set.Ioi (1 : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ β)) x)
            h_meas_indicator
        have h_subset : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
          intro x hx
          exact lt_trans (show (0 : ℝ) < 1 by norm_num) hx
        have h_inter :
            Set.Ioi (1 : ℝ) ∩ Set.Ioi (0 : ℝ) = Set.Ioi (1 : ℝ) :=
          Set.inter_eq_left.mpr h_subset
        have h_restrict :=
          setLIntegral_indicator (μ := volume) (s := Set.Ioi (1 : ℝ))
            (t := Set.Ioi (0 : ℝ))
            (f := fun x : ℝ => ENNReal.ofReal (x ^ (β - 1)))
            measurableSet_Ioi
        have h_restrict' :
            ∫⁻ x in Set.Ioi (0 : ℝ),
                (Set.Ioi (1 : ℝ)).indicator
                  (fun x => ENNReal.ofReal (x ^ (β - 1))) x ∂volume
              = ∫⁻ x in Set.Ioi (1 : ℝ),
                  ENNReal.ofReal (x ^ (β - 1)) ∂volume := by
          simp [h_inter, h_restrict]
        have h_prod :
            (fun x : ℝ =>
                (Set.Ioi (1 : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ β)) x *
                  ENNReal.ofReal (1 / x))
              = (Set.Ioi (1 : ℝ)).indicator
                  (fun x => ENNReal.ofReal (x ^ (β - 1))) := by
          funext x
          classical
          by_cases hx : x ∈ Set.Ioi (1 : ℝ)
          · have hx0 : 0 < x := lt_trans (show (0 : ℝ) < 1 by norm_num) hx
            have hxβ_nonneg : 0 ≤ x ^ β := Real.rpow_nonneg (le_of_lt hx0) _
            have hx_sub := Real.rpow_sub hx0 β (1 : ℝ)
            have hx_pow_one : x ^ (1 : ℝ) = x := by simp
            have hx_exp : x ^ (β - 1) = x ^ β / x := by
              simpa [hx_pow_one] using hx_sub
            have hx_mul : x ^ β * (1 / x) = x ^ (β - 1) := by
              simp [hx_exp, div_eq_mul_inv, mul_comm]
            have hx_prod' :=
              (ENNReal.ofReal_mul (p := x ^ β) (q := 1 / x) (hp := hxβ_nonneg)).symm
            have hx_eq :
                ENNReal.ofReal (x ^ β * (1 / x)) =
                  ENNReal.ofReal (x ^ (β - 1)) := by
              simpa [hx_mul]
                using congrArg ENNReal.ofReal hx_mul
            calc
              (Set.Ioi (1 : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ β)) x *
                  ENNReal.ofReal (1 / x)
                  = ENNReal.ofReal (x ^ β) * ENNReal.ofReal (1 / x) := by
                    simp [Set.indicator_of_mem hx]
              _ = ENNReal.ofReal (x ^ β * (1 / x)) := hx_prod'
              _ = ENNReal.ofReal (x ^ (β - 1)) := hx_eq
              _ = (Set.Ioi (1 : ℝ)).indicator
                    (fun x => ENNReal.ofReal (x ^ (β - 1))) x := by
                    simp [Set.indicator_of_mem hx]
          · have hx_le : x ≤ 1 := le_of_not_gt hx
            have hx_indicator :=
              Set.indicator_of_notMem hx
                (f := fun x : ℝ => ENNReal.ofReal (x ^ β))
            have hx_indicator' :=
              Set.indicator_of_notMem hx
                (f := fun x : ℝ => ENNReal.ofReal (x ^ (β - 1)))
            simp [hx_le]
        calc
          ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (x ^ β) ∂mulHaar
              = ∫⁻ x,
                  (Set.Ioi (1 : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ β)) x
                    ∂mulHaar := by simp
          _ = ∫⁻ x in Set.Ioi (0 : ℝ),
                (Set.Ioi (1 : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ β)) x *
                ENNReal.ofReal (1 / x) ∂volume := by
              simpa using h_expand
          _ = ∫⁻ x in Set.Ioi (0 : ℝ),
                (Set.Ioi (1 : ℝ)).indicator
                  (fun x => ENNReal.ofReal (x ^ (β - 1))) x ∂volume := by
            refine lintegral_congr_ae ?_
            refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
            refine Filter.Eventually.of_forall ?_
            intro x hx
            classical
            by_cases hx1 : x ∈ Set.Ioi (1 : ℝ)
            · have hx0 : 0 < x := lt_trans (show (0 : ℝ) < 1 by norm_num) hx1
              have hxβ_nonneg : 0 ≤ x ^ β := Real.rpow_nonneg (le_of_lt hx0) _
              have hx_sub := Real.rpow_sub hx0 β (1 : ℝ)
              have hx_pow_one : x ^ (1 : ℝ) = x := by simp
              have hx_exp : x ^ (β - 1) = x ^ β / x := by
                simpa [hx_pow_one] using hx_sub
              have hx_mul : x ^ β * (1 / x) = x ^ (β - 1) := by
                simp [hx_exp, div_eq_mul_inv, mul_comm]
              have hx_prod' :=
                (ENNReal.ofReal_mul (p := x ^ β) (q := 1 / x) (hp := hxβ_nonneg)).symm
              have hx_eq :
                  ENNReal.ofReal (x ^ β * (1 / x)) =
                    ENNReal.ofReal (x ^ (β - 1)) := by
                simpa [hx_mul]
                  using congrArg ENNReal.ofReal hx_mul
              calc
                (Set.Ioi (1 : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ β)) x *
                    ENNReal.ofReal (1 / x)
                    = ENNReal.ofReal (x ^ β) * ENNReal.ofReal (1 / x) := by
                      simp [Set.indicator_of_mem hx1]
                _ = ENNReal.ofReal (x ^ β * (1 / x)) := hx_prod'
                _ = ENNReal.ofReal (x ^ (β - 1)) := hx_eq
                _ = (Set.Ioi (1 : ℝ)).indicator
                      (fun x => ENNReal.ofReal (x ^ (β - 1))) x := by
                      simp [Set.indicator_of_mem hx1]
            · have hx_le : x ≤ 1 := le_of_not_gt hx1
              have hx_indicator :=
                Set.indicator_of_notMem hx1
                  (f := fun x : ℝ => ENNReal.ofReal (x ^ β))
              have hx_indicator' :=
                Set.indicator_of_notMem hx1
                  (f := fun x : ℝ => ENNReal.ofReal (x ^ (β - 1)))
              simp [hx_le]
          _ = ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (x ^ (β - 1)) ∂volume :=
            h_restrict'
      -- Evaluate the resulting Lebesgue integral explicitly
      have h_param : β - 1 < -1 := by
        have hneg : -γ < 0 := neg_lt_zero.mpr hγ_pos
        have : -γ - 1 < -1 := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm] using add_lt_add_right hneg (-1)
        simpa [β, γ, hβγ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have h_value : ∫ x in Set.Ioi (1 : ℝ), x ^ (β - 1) ∂volume = 1 / γ := by
        have h_temp := integral_Ioi_rpow_of_lt h_param zero_lt_one
        have h_temp' :
            ∫ x in Set.Ioi (1 : ℝ), x ^ (β - 1) ∂volume =
              -1 / ((β - 1) + 1) := by
          simpa [one_div] using integral_Ioi_rpow_of_lt h_param zero_lt_one
        have hβ1 : β - 1 + 1 = β := by ring
        have h_temp'' : ∫ x in Set.Ioi (1 : ℝ), x ^ (β - 1) ∂volume = -1 / β := by
          simpa [hβ1] using h_temp'
        have h_eq : -1 / β = 1 / γ := by
          simp [hβγ, one_div]
        exact (h_temp''.trans h_eq)
      have h_nonneg :
          0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] fun x : ℝ => x ^ (β - 1) := by
        refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
        refine Filter.Eventually.of_forall ?_
        intro x hx
        have hx_pos : 0 < x :=
          lt_trans (show (0 : ℝ) < 1 by norm_num) hx
        exact Real.rpow_nonneg (le_of_lt hx_pos) _
      have h_integrable : Integrable (fun x : ℝ => x ^ (β - 1))
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
        exact integrableOn_Ioi_rpow_of_lt h_param zero_lt_one
      have h_ofReal :=
          ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg
      have h_target :
          ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (x ^ (β - 1)) ∂volume
            = ENNReal.ofReal (1 / γ) := by
        have h_eq := congrArg ENNReal.ofReal h_value
        exact h_ofReal.symm.trans h_eq
      have h_target' :
          ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (x ^ β) ∂mulHaar ≤
            ENNReal.ofReal (1 / γ) :=
        le_of_eq (h_convert.trans h_target)
      -- The goal is already proven by h_target'
      exact h_target'
    -- The bound follows from h_integral_expand and h_integral_bound
    -- The calculation shows (C² * integral)^(1/2) ≤ C * sqrt(1/(2k₁-2σ))
    classical
    -- abbreviate the exponent gap
    set δ : ℝ := 2 * (k₁ : ℝ) - 2 * σ with hδ
    -- show the gap is at least 1, hence positive
    have hhalf_le : (1 / 2 : ℝ) ≤ (k₁ : ℝ) - σ := by
      have := sub_le_sub_right hσk σ
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hδ_ge_one : (1 : ℝ) ≤ δ := by
      have := mul_le_mul_of_nonneg_left hhalf_le (show (0 : ℝ) ≤ 2 by norm_num)
      simpa [δ, two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hδ_pos : 0 < δ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hδ_ge_one
    have hδ_inv_nonneg : 0 ≤ 1 / δ := le_of_lt (one_div_pos.mpr hδ_pos)

    -- compare the reciprocal with the bound obtained above
    have h_one_div_le : 1 / (δ + 1) ≤ 1 / δ := by
      have hδ_le : δ ≤ δ + 1 :=
        le_of_lt (lt_add_of_pos_right δ (by norm_num : (0 : ℝ) < 1))
      exact one_div_le_one_div_of_le hδ_pos hδ_le

    -- strengthen the bound on B using the comparison above
    have hB_le :
        ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
            (x ^ (2 * σ - 1 - (↑(2 * k₁) : ℝ))) ∂mulHaar ≤
          ENNReal.ofReal (1 / δ) := by
      refine le_trans h_integral_bound ?_
      have h' : ENNReal.ofReal (1 / (δ + 1)) ≤ ENNReal.ofReal (1 / δ) := by
        simpa using ENNReal.ofReal_le_ofReal h_one_div_le
      exact h'

    -- turn the inequality for B into the desired one for the full integral A
    have hA_le :
        ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ ≤
          ENNReal.ofReal (1 / δ) * ENNReal.ofReal (C ^ 2) := by
      have hC_sq_nn : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (C ^ 2) := by exact bot_le
      have h_indicator_sq :
          (fun x : ℝ => ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2)) =
            fun x : ℝ => ENNReal.ofReal (if 1 < x then (C / x ^ k₁) ^ 2 else 0) := by
        funext x
        by_cases hx : 1 < x
        · simp [Set.mem_Ioi, hx]
        · simp [Set.mem_Ioi, hx]
      have h_rewrite :
          ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ =
            ∫⁻ x, ENNReal.ofReal (if 1 < x then (C / x ^ k₁) ^ 2 else 0) ∂μ := by
        simp
      have h_integral_eq :
          ∫⁻ x, ENNReal.ofReal (if 1 < x then (C / x ^ k₁) ^ 2 else 0) ∂μ =
            ENNReal.ofReal (C ^ 2) *
              ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
                  (x ^ (2 * σ - 1 - (↑(2 * k₁) : ℝ))) ∂mulHaar := by
        -- Use the rewrite relation from h_rewrite and h_integral_expand
        rw [← h_rewrite, h_integral_expand]
      calc
        ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ
            = ∫⁻ x, ENNReal.ofReal (if 1 < x then (C / x ^ k₁) ^ 2 else 0) ∂μ :=
              h_rewrite
        _ = ENNReal.ofReal (C ^ 2) *
              ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
                  (x ^ (2 * σ - 1 - (↑(2 * k₁) : ℝ))) ∂mulHaar :=
              h_integral_eq
        _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (1 / δ) := by
              exact mul_le_mul_of_nonneg_left hB_le hC_sq_nn
        _ = ENNReal.ofReal (1 / δ) * ENNReal.ofReal (C ^ 2) := by
              simp [mul_comm]
    -- rewrite the product as the ENNReal of a single real number
    have hC_sq_nonneg : 0 ≤ C ^ 2 := sq_nonneg _
    -- Use the already established bound directly
    have hA_le' :
        ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ ≤
          ENNReal.ofReal ((1 / δ) * C ^ 2) := by
      -- We already have h_goal that gives us this bound in the equivalent form
      -- We need to convert between the two integral representations
      have h_mul : ENNReal.ofReal (1 / δ) * ENNReal.ofReal (C ^ 2) =
          ENNReal.ofReal ((1 / δ) * C ^ 2) :=
        (ENNReal.ofReal_mul hδ_inv_nonneg).symm
      -- h_rewrite establishes the equivalence of the integrands
      rw [← h_mul]
      -- Use the existing bound from the previous calculation chain
      exact hA_le

    -- identify the bound with a square to prepare for taking square roots
    have h_sq_eq : (1 / δ) * C ^ 2 = (C * Real.sqrt (1 / δ)) ^ 2 := by
      -- Use the fact that (a * b)^2 = a^2 * b^2 and sqrt(x)^2 = x for x ≥ 0
      have hsqrt_sq : (Real.sqrt (1 / δ)) ^ 2 = 1 / δ :=
        Real.sq_sqrt hδ_inv_nonneg
      have h_expand : (C * Real.sqrt (1 / δ)) ^ 2 = C ^ 2 * (Real.sqrt (1 / δ)) ^ 2 := by
        ring
      rw [h_expand, hsqrt_sq]
      ring

    have hA_le'' :
        ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ ≤
          ENNReal.ofReal ((C * Real.sqrt (1 / δ)) ^ 2) := by
      rw [← h_sq_eq]
      exact hA_le'

    -- take square roots on both sides in ENNReal
    have h_bound := ENNReal.rpow_le_rpow hA_le'' (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h_right :
        (ENNReal.ofReal ((C * Real.sqrt (1 / δ)) ^ 2)) ^ (1 / 2 : ℝ)
          = ENNReal.ofReal (C * Real.sqrt (1 / δ)) := by
      -- For nonnegative a, (ENNReal.ofReal (a^2))^(1/2) = ENNReal.ofReal a
      have hC_sqrt_nonneg : 0 ≤ C * Real.sqrt (1 / δ) :=
        mul_nonneg hC_nonneg (Real.sqrt_nonneg _)
      have h_sq_nonneg : 0 ≤ (C * Real.sqrt (1 / δ)) ^ 2 := sq_nonneg _
      -- Use the fact that sqrt(a^2) = |a| = a when a ≥ 0
      have h_rpow_eq : ((C * Real.sqrt (1 / δ)) ^ 2) ^ (1 / 2 : ℝ) = C * Real.sqrt (1 / δ) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_sq hC_sqrt_nonneg
      rw [ENNReal.ofReal_rpow_of_nonneg h_sq_nonneg, h_rpow_eq]
      norm_num
    -- conclude the desired inequality
    rw [h_right] at h_bound
    -- Convert back to the original form using δ = 2 * k₁ - 2 * σ
    have h_final : C * Real.sqrt (1 / δ) =
        SchwartzMap.seminorm ℝ k₁ 0 f * Real.sqrt (1 / (2 * k₁ - 2 * σ)) := by
      rw [← hC_def, hδ]
    rw [h_final] at h_bound
    exact h_bound
  exact le_trans h_sqrt h_integral_comp

/-- Bound for the eLpNorm of a Schwartz function on the unit interval (0,1] -/
lemma eLpNorm_bound_on_unit_interval {σ : ℝ}
    (f : SchwartzMap ℝ ℂ) (M : ℝ)
    (hM_bound : (∫⁻ x in Set.Ioc 0 1, ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar) ^
    (1 / 2 : ℝ) ≤ ENNReal.ofReal M) :
    eLpNorm (fun x => if x ∈ Set.Ioc 0 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
    ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 f * M) := by
  classical
  set μ :=
      mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))
    with hμ_def
  set g : ℝ → ℂ := fun x => if x ∈ Set.Ioc (0 : ℝ) 1 then f x else 0
  set C : ℝ := SchwartzMap.seminorm ℝ 0 0 f with hC_def
  have hC_nonneg : 0 ≤ C := by
    simp [hC_def]
  have h_eLp_sq : (eLpNorm g 2 μ) ^ (2 : ℝ) =
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
    have h :=
      (eLpNorm_nnreal_pow_eq_lintegral
        (μ := μ) (f := g) (p := (2 : NNReal))
        (by
          exact_mod_cast (two_ne_zero : (2 : ℝ) ≠ 0)))
    have h_coe : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_cast
    simpa [g, h_coe] using h
  have h_indicator_eq :
      (fun x : ℝ => ‖g x‖ₑ ^ (2 : ℝ)) =
        Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun x => ‖f x‖ₑ ^ (2 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · simp [g, Set.indicator_of_mem, hx]
      have h_mem : 0 < x ∧ x ≤ 1 := by
        rwa [Set.mem_Ioc] at hx
      rw [if_pos h_mem]
    · simp [g, Set.indicator_of_notMem, hx]
      intros h1 h2
      exfalso
      exact hx ⟨h1, h2⟩
  have h_integral_indicator :
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ =
        ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂μ := by
    rw [h_indicator_eq, lintegral_indicator]
    exact measurableSet_Ioc
  have h_indicator_bound :
      Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun x : ℝ => ‖f x‖ₑ ^ (2 : ℝ)) ≤
        Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun _ : ℝ => ENNReal.ofReal (C ^ 2)) := by
    classical
    intro x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · have h_norm : ‖f x‖ ≤ C := by
        simpa [hC_def] using (SchwartzMap.norm_le_seminorm ℝ f x)
      have h_sq : ‖f x‖ ^ 2 ≤ C ^ 2 := by
        have hx_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
        have := mul_le_mul h_norm h_norm hx_nonneg hC_nonneg
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      have h_le : ENNReal.ofReal (‖f x‖ ^ 2) ≤ ENNReal.ofReal (C ^ 2) :=
        ENNReal.ofReal_le_ofReal h_sq
      simpa [Set.indicator_of_mem hx, pow_two, ENNReal.ofReal_mul, norm_nonneg]
        using h_le
    · simp [hx]
  have h_integral_le :
      ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂μ ≤
        ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun _ : ℝ => ENNReal.ofReal (C ^ 2)) x ∂μ :=
    lintegral_mono h_indicator_bound
  have h_const_integral :
      ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
          (fun _ : ℝ => ENNReal.ofReal (C ^ 2)) x ∂μ =
        ENNReal.ofReal (C ^ 2) * μ (Set.Ioc (0 : ℝ) 1) := by
    classical
    simp [μ, measurableSet_Ioc]
  have h_sq_le : (eLpNorm g 2 μ) ^ (2 : ℝ) ≤
      ENNReal.ofReal (C ^ 2) * μ (Set.Ioc (0 : ℝ) 1) := by
    calc
      (eLpNorm g 2 μ) ^ (2 : ℝ)
          = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := h_eLp_sq
      _ = ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂μ := h_integral_indicator
      _ ≤ ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun _ : ℝ => ENNReal.ofReal (C ^ 2)) x ∂μ := h_integral_le
      _ = ENNReal.ofReal (C ^ 2) * μ (Set.Ioc (0 : ℝ) 1) := h_const_integral
  have h_sqrt : eLpNorm g 2 μ ≤
      (ENNReal.ofReal (C ^ 2) * μ (Set.Ioc (0 : ℝ) 1)) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.rpow_le_rpow h_sq_le (by positivity : 0 ≤ (1 / 2 : ℝ))
    have h_left :
        ((eLpNorm g 2 μ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = eLpNorm g 2 μ := by
      simp only [one_div]
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
    rw [h_left] at h
    exact h
  have hC_pow : ENNReal.ofReal (C ^ 2) =
      (ENNReal.ofReal C) ^ (2 : ℝ) := by
    have h := ENNReal.ofReal_rpow_of_nonneg (by exact hC_nonneg) (by norm_num : 0 ≤ (2 : ℝ))
    simpa [Real.rpow_natCast] using h.symm
  have h_factor :
      ((ENNReal.ofReal C) ^ (2 : ℝ) * μ (Set.Ioc (0 : ℝ) 1)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal C * (μ (Set.Ioc (0 : ℝ) 1)) ^ (1 / 2 : ℝ) := by
    have h_mul :=
      ENNReal.mul_rpow_of_nonneg ((ENNReal.ofReal C) ^ (2 : ℝ))
        (μ (Set.Ioc (0 : ℝ) 1)) (by positivity : 0 ≤ (1 / 2 : ℝ))
    have h_pow :=
      (ENNReal.rpow_mul (ENNReal.ofReal C) (2 : ℝ) (1 / 2 : ℝ)).symm
    have h_two_half : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
    rw [h_mul]
    congr 1
    rw [h_pow, h_two_half, ENNReal.rpow_one]
  have h_sqrt' : eLpNorm g 2 μ ≤
      ENNReal.ofReal C * (μ (Set.Ioc (0 : ℝ) 1)) ^ (1 / 2 : ℝ) := by
    rw [hC_pow, h_factor] at h_sqrt
    exact h_sqrt
  have h_measure_indicator :
      μ (Set.Ioc (0 : ℝ) 1) =
        ∫⁻ x in Set.Ioc 0 1, ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar := by
    classical
    simp [μ, measurableSet_Ioc]
  have hM' : (μ (Set.Ioc (0 : ℝ) 1)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal M := by
    simpa [h_measure_indicator] using hM_bound
  have h_final : eLpNorm g 2 μ ≤ ENNReal.ofReal C * ENNReal.ofReal M :=
    (le_trans h_sqrt') <| mul_le_mul_left' hM' (ENNReal.ofReal C)
  have h_mul_eq : ENNReal.ofReal C * ENNReal.ofReal M =
      ENNReal.ofReal (C * M) := by
    by_cases hM : 0 ≤ M
    · simp [ENNReal.ofReal_mul, hC_nonneg]
    · have hM_neg : M < 0 := lt_of_not_ge hM
      have hCM_nonpos : C * M ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hC_nonneg hM_neg.le
      simp [ENNReal.ofReal_of_nonpos hM_neg.le, ENNReal.ofReal_of_nonpos hCM_nonpos]
  have h_result : eLpNorm g 2 μ ≤ ENNReal.ofReal (C * M) := by
    simpa [h_mul_eq] using h_final
  simpa [g, μ, hμ_def, hC_def] using h_result

/-- Splitting the eLpNorm of a function on (0,∞) into (0,1] and (1,∞) parts -/
lemma eLpNorm_split_at_one {σ : ℝ} (f : SchwartzMap ℝ ℂ) :
    eLpNorm (fun x => if x > 0 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
    eLpNorm (fun x => if x ∈ Set.Ioc 0 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) +
    eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
  classical
  -- Use the triangle inequality for `eLpNorm` after rewriting the function as a sum.
  set μ := mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))
  set g₀ : ℝ → ℂ := Set.indicator (Set.Ioi (0 : ℝ)) fun x => f x
  set g₁ : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) 1) fun x => f x
  set g₂ : ℝ → ℂ := Set.indicator (Set.Ioi (1 : ℝ)) fun x => f x
  have hg₀_def : g₀ = fun x : ℝ => if x > 0 then f x else 0 := by
    funext x
    by_cases hx : 0 < x
    · simp [g₀, Set.mem_Ioi, hx]
    · simp [g₀, Set.mem_Ioi, hx]
  have hg₁_def : g₁ = fun x : ℝ => if x ∈ Set.Ioc 0 1 then f x else 0 := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · simp [g₁, hx]
    · simp [g₁, hx]
  have hg₂_def : g₂ = fun x : ℝ => if x ∈ Set.Ioi 1 then f x else 0 := by
    funext x
    by_cases hx : x ∈ Set.Ioi (1 : ℝ)
    · simp [g₂, hx]
    · simp [g₂, hx]
  have hg₀_eq : g₀ = g₁ + g₂ := by
    classical
    funext x
    by_cases hx_pos : 0 < x
    · by_cases hx_le_one : x ≤ 1
      · have hx_mem : x ∈ Set.Ioc (0 : ℝ) 1 := ⟨hx_pos, hx_le_one⟩
        have hx_not_gt : ¬ 1 < x := not_lt.mpr hx_le_one
        simp [g₀, g₁, g₂, Set.indicator, Set.mem_Ioi, hx_pos, hx_mem, hx_not_gt]
      · have hx_gt_one : 1 < x := lt_of_not_ge hx_le_one
        have hx_not_mem : x ∉ Set.Ioc (0 : ℝ) 1 := by
          intro hx_mem
          exact hx_le_one hx_mem.2
        simp [g₀, g₁, g₂, Set.indicator, Set.mem_Ioi, hx_pos, hx_gt_one, hx_not_mem]
    · have hx_not_mem₁ : x ∉ Set.Ioc (0 : ℝ) 1 := by
        intro hx_mem
        exact hx_pos hx_mem.1
      have hx_not_mem₂ : x ∉ Set.Ioi (1 : ℝ) := by
        intro hx_mem
        exact hx_pos (lt_trans (zero_lt_one : (0 : ℝ) < 1) hx_mem)
      simp [g₀, g₁, g₂, Set.indicator, Set.mem_Ioi, hx_pos, hx_not_mem₁, hx_not_mem₂]
  have hf_meas : AEStronglyMeasurable (fun x : ℝ => f x) μ :=
    (SchwartzMap.continuous f).aestronglyMeasurable
  have hg₁_meas : AEStronglyMeasurable g₁ μ := by
    simpa [g₁] using hf_meas.indicator measurableSet_Ioc
  have hg₂_meas : AEStronglyMeasurable g₂ μ := by
    simpa [g₂] using hf_meas.indicator measurableSet_Ioi
  have h_tri := eLpNorm_add_le hg₁_meas hg₂_meas (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_tri' :
      eLpNorm g₀ 2 μ ≤
        eLpNorm g₁ 2 μ + eLpNorm g₂ 2 μ := by
    simpa [hg₀_eq.symm] using h_tri
  simpa [μ, hg₀_def, hg₁_def, hg₂_def] using h_tri'

/-- The weight function has finite L² norm on (0,1] for σ > 1/2 -/
lemma weight_function_L2_bound_unit {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ M : ℝ, 0 < M ∧
    (∫⁻ x in Set.Ioc 0 1, ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar) ^
        (1 / 2 : ℝ) ≤ ENNReal.ofReal M := by
  classical
  set I :=
      (∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar)
    with hI_def
  have h_exp_neg : -1 < 2 * σ - 2 := by linarith [hσ]
  have h_denom_pos : 0 < 2 * σ - 1 := by linarith [hσ]
  have hI_value : I = ENNReal.ofReal (1 / (2 * σ - 1)) := by
    classical
    set μ := mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) with hμ_def
    have hI_measure : I = μ (Set.Ioc (0 : ℝ) 1) := by
      have h_apply := withDensity_apply (μ := mulHaar)
        (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
        (s := Set.Ioc (0 : ℝ) 1)
        (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))
      simp [I, μ]
    have h_exp_nonneg : 0 ≤ 2 * σ - 1 := by linarith [hσ]
    have h_pow_meas :
        Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_rpow_const h_exp_nonneg)).measurable
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
      simp [μ, (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))]
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
          (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))
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
      have hx_pow_one : x ^ (1 : ℝ) = x := by simp
      have hx_rpow := (Real.rpow_sub hx_pos (2 * σ - 1) 1).symm
      have hx_sub : (2 * σ - 1) - 1 = 2 * σ - 2 := by ring
      have hx_eq : x ^ (2 * σ - 1) / x = x ^ (2 * σ - 2) := by
        simpa [div_eq_mul_inv, hx_pow_one, hx_sub] using hx_rpow
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
      have h_int := (intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
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
      have h_one : (1 : ℝ) ^ (2 * σ - 1) = 1 := by simp
      have h_sub : 2 * σ - 2 + 1 = 2 * σ - 1 := by ring
      simpa [h_sub, h_zero, h_one]
        using h_int
    have h_int_value :
        ∫ x, x ^ (2 * σ - 2) ∂ν = (2 * σ - 1)⁻¹ := by
      simp [h_set_to_interval, h_interval_value]
    have hμ_value :
        μ (Set.Ioc (0 : ℝ) 1) = ENNReal.ofReal (1 / (2 * σ - 1)) := by
      simp [hμ_volume'', h_ofReal, h_int_value, one_div]
    simpa [one_div] using hI_measure.trans hμ_value
  let M := Real.sqrt (1 / (2 * σ - 1))
  have hM_pos : 0 < M := by
    have h_pos : 0 < 1 / (2 * σ - 1) := one_div_pos.mpr h_denom_pos
    simpa [M] using Real.sqrt_pos.mpr h_pos
  refine ⟨M, hM_pos, ?_⟩
  have h_nonneg : 0 ≤ 1 / (2 * σ - 1) := one_div_nonneg.mpr (le_of_lt h_denom_pos)
  have h_pow_eq' :=
    ENNReal.ofReal_rpow_of_nonneg (x := 1 / (2 * σ - 1)) h_nonneg
      (by positivity : 0 ≤ (1 / 2 : ℝ))
  have h_sqrt' : (1 / (2 * σ - 1)) ^ (2⁻¹ : ℝ) = M := by
    simpa [M] using (Real.sqrt_eq_rpow (1 / (2 * σ - 1))).symm
  have h_pow_eq :
      ENNReal.ofReal ((2 * σ - 1)⁻¹) ^ (2⁻¹ : ℝ) =
        ENNReal.ofReal (((2 * σ - 1)⁻¹) ^ (2⁻¹ : ℝ)) := by
    simpa [one_div] using h_pow_eq'
  have h_sqrt_inv : ((2 * σ - 1)⁻¹) ^ (2⁻¹ : ℝ) = M := by
    simpa [one_div] using h_sqrt'
  have hI_pow : I ^ (2⁻¹ : ℝ) = ENNReal.ofReal M := by
    calc
      I ^ (2⁻¹ : ℝ)
          = (ENNReal.ofReal ((2 * σ - 1)⁻¹)) ^ (2⁻¹ : ℝ) := by
              simp [I, hI_value, one_div]
      _ = ENNReal.ofReal (((2 * σ - 1)⁻¹) ^ (2⁻¹ : ℝ)) := h_pow_eq
      _ = ENNReal.ofReal M := by simp [h_sqrt_inv]
  simp [hI_pow]

/-- Finiteness of the mulHaar measure on a positive closed interval. -/
lemma mulHaar_measure_Icc_lt_top {a b : ℝ} (ha : 0 < a) (_ : a ≤ b) :
    mulHaar (Set.Icc a b) < ∞ := by
  classical
  have h_subset : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have h_meas : MeasurableSet (Set.Icc a b) := measurableSet_Icc
  have h_inter : Set.Icc a b ∩ Set.Ioi (0 : ℝ) = Set.Icc a b := by
    refine Set.inter_eq_left.mpr ?_
    exact fun x hx ↦ h_subset hx
  have h_measure := mulHaar_apply (s := Set.Icc a b) h_meas
  have h_eq : mulHaar (Set.Icc a b) =
      ∫⁻ x in Set.Icc a b, ENNReal.ofReal (1 / x) ∂volume := by
    simpa [h_inter]
      using h_measure
  have h_bound : ∀ x ∈ Set.Icc a b, ENNReal.ofReal (1 / x) ≤ ENNReal.ofReal (1 / a) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    have hx_le : a ≤ x := hx.1
    have h_inv : 1 / x ≤ 1 / a := one_div_le_one_div_of_le ha hx_le
    exact ENNReal.ofReal_le_ofReal h_inv
  have h_bound_ae :
      ∀ᵐ x ∂volume.restrict (Set.Icc a b),
        ENNReal.ofReal (1 / x) ≤ ENNReal.ofReal (1 / a) := by
    have h_all : ∀ᵐ x ∂volume, x ∈ Set.Icc a b →
        ENNReal.ofReal (1 / x) ≤ ENNReal.ofReal (1 / a) :=
      Filter.Eventually.of_forall fun x hx => h_bound x hx
    exact (ae_restrict_iff' h_meas).2 h_all
  have h_lintegral_le :
      ∫⁻ x in Set.Icc a b, ENNReal.ofReal (1 / x) ∂volume ≤
        ∫⁻ x in Set.Icc a b, ENNReal.ofReal (1 / a) ∂volume :=
    lintegral_mono_ae h_bound_ae
  have h_const :
      ∫⁻ x in Set.Icc a b, ENNReal.ofReal (1 / a) ∂volume =
        ENNReal.ofReal (1 / a) * volume (Set.Icc a b) := by
    classical
    simp
  have h_volume_lt_top : volume (Set.Icc a b) < ∞ := by
    simp [volume_Icc]
  have h_rhs_lt_top :
      ENNReal.ofReal (1 / a) * volume (Set.Icc a b) < ∞ :=
    ENNReal.mul_lt_top (by simp) h_volume_lt_top
  have h_left_lt_top :
      ∫⁻ x in Set.Icc a b, ENNReal.ofReal (1 / x) ∂volume < ∞ :=
    lt_of_le_of_lt h_lintegral_le (by simpa [h_const] using h_rhs_lt_top)
  simpa [h_eq]
    using h_left_lt_top

/-- Integrability of the weight x^(2σ-1) on a positive closed interval with respect to mulHaar. -/
lemma weight_integrableOn_Icc {σ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun x : ℝ => x ^ (2 * σ - 1 : ℝ)) (Set.Icc a b) mulHaar := by
  classical
  have h_meas : MeasurableSet (Set.Icc a b) := measurableSet_Icc
  have h_compact : IsCompact (Set.Icc a b) := isCompact_Icc
  have h_subset : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have h_cont : ContinuousOn (fun x : ℝ => x ^ (2 * σ - 1 : ℝ)) (Set.Icc a b) := by
    have h_cont' :
        ContinuousOn (fun x : ℝ => x ^ (2 * σ - 1 : ℝ)) (Set.Ioi (0 : ℝ)) := by
      intro x hx
      exact
        (Real.continuousAt_rpow_const x (2 * σ - 1 : ℝ)
            (Or.inl (ne_of_gt hx))).continuousWithinAt
    exact h_cont'.mono h_subset
  have hμ_lt := mulHaar_measure_Icc_lt_top ha hab
  have hf_meas :
      AEStronglyMeasurable
        (fun x : ℝ => x ^ (2 * σ - 1 : ℝ)) (mulHaar.restrict (Set.Icc a b)) :=
    ContinuousOn.aestronglyMeasurable_of_isCompact h_cont h_compact h_meas
  refine ⟨hf_meas, ?_⟩
  haveI : IsFiniteMeasure (mulHaar.restrict (Set.Icc a b)) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply, h_meas, Set.inter_univ] using hμ_lt
  obtain ⟨C, hC_pos, hC⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ (fun x : ℝ => x ^ (2 * σ - 1 : ℝ)) '' Set.Icc a b, ‖x‖ ≤ C :=
    Bornology.IsBounded.exists_pos_norm_le
      (h_compact.image_of_continuousOn h_cont).isBounded
  have h_bound :
      ∀ᵐ x ∂mulHaar.restrict (Set.Icc a b),
        ‖x ^ (2 * σ - 1 : ℝ)‖ ≤ C := by
    have h_all : ∀ᵐ x ∂mulHaar, x ∈ Set.Icc a b →
        ‖x ^ (2 * σ - 1 : ℝ)‖ ≤ C :=
      Filter.Eventually.of_forall fun x hx =>
        hC _ (Set.mem_image_of_mem _ hx)
    exact (ae_restrict_iff' h_meas).2 h_all
  have h_integrable :=
    HasFiniteIntegral.of_bounded
      (μ := mulHaar.restrict (Set.Icc a b))
      (f := fun x : ℝ => x ^ (2 * σ - 1 : ℝ))
      (C := C) h_bound
  simpa [IntegrableOn, h_meas] using h_integrable

/-- The weight function x^(2σ-1) is locally integrable on (0,∞) for σ > 1/2 -/
lemma weight_locallyIntegrable {σ : ℝ} (_ : 1 / 2 < σ) :
    LocallyIntegrableOn (fun x : ℝ => x ^ (2 * σ - 1 : ℝ)) (Set.Ioi 0) mulHaar := by
  classical
  have h_loc : IsLocallyClosed (Set.Ioi (0 : ℝ)) := isOpen_Ioi.isLocallyClosed
  refine (locallyIntegrableOn_iff
      (s := Set.Ioi (0 : ℝ)) (μ := mulHaar)
      (f := fun x : ℝ => x ^ (2 * σ - 1 : ℝ)) h_loc).2 ?_
  intro K hK_subset hK_compact
  by_cases hK : K = ∅
  · simp [hK]
  · have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK
    obtain ⟨a, ha⟩ := hK_compact.exists_isLeast hK_nonempty
    obtain ⟨b, hb⟩ := hK_compact.exists_isGreatest hK_nonempty
    have ha_mem : a ∈ K := ha.1
    have hb_mem : b ∈ K := hb.1
    have ha_pos : 0 < a := by
      have : a ∈ Set.Ioi (0 : ℝ) := hK_subset ha_mem
      simpa using this
    have hab : a ≤ b := ha.2 hb_mem
    have h_subset_Icc : K ⊆ Set.Icc a b := by
      intro x hx
      exact ⟨ha.2 hx, hb.2 hx⟩
    have h_integrable_Icc := weight_integrableOn_Icc (σ := σ) ha_pos hab
    exact h_integrable_Icc.mono_set h_subset_Icc

/-- Elements of `Hσ σ` lie in the defining weighted L² space. -/
lemma memLp_of_Hσ {σ : ℝ} (f : Hσ σ) :
    MemLp (Hσ.toFun f)
      2 (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
  simpa [Hσ.toFun] using
    (Lp.memLp
      (f :=
        (f : Lp ℂ 2
          (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))))

/-- Simple functions with bounded support are integrable in Lebesgue measure -/
lemma simpleFunc_bounded_support_integrable
    (f : SimpleFunc ℝ ℂ) (R : ℝ) (_ : 0 < R)
    (hR_bound : Function.support (f : ℝ → ℂ) ⊆ Set.Icc (-R) R) :
    Integrable f volume := by
  -- f is a SimpleFunc which is integrable on bounded sets
  classical
  -- Denote the ambient set and note that it has finite Lebesgue measure.
  set s : Set ℝ := Set.Icc (-R) R
  have hs_meas : MeasurableSet s := measurableSet_Icc
  have hμs_lt_top : volume s < ∞ := by
    -- Closed intervals in ℝ have finite volume
    have hs_eq : volume s = ENNReal.ofReal (R - (-R)) := by
      simp [s, sub_neg_eq_add]
    have : ENNReal.ofReal (R - (-R)) < ∞ := by simp
    simp [hs_eq]
  haveI : IsFiniteMeasure (volume.restrict s) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply, hs_meas, Set.inter_univ] using hμs_lt_top
  -- Obtain a global bound on ‖f‖ since simple functions take finitely many values.
  obtain ⟨C, hC⟩ := (f.map fun z : ℂ => (‖z‖ : ℝ)).exists_forall_le
  have h_bound : ∀ x, ‖f x‖ ≤ C := by
    intro x
    simpa using hC x
  have h_bound_ae :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ C :=
    Filter.Eventually.of_forall h_bound
  -- f is integrable on s with respect to the restricted measure.
  have hf_integrable_restrict : Integrable f (volume.restrict s) := by
    refine ⟨?_, ?_⟩
    · exact SimpleFunc.aestronglyMeasurable (μ := volume.restrict s) f
    · exact HasFiniteIntegral.of_bounded (μ := volume.restrict s) h_bound_ae
  have hf_integrableOn : IntegrableOn f s volume := by
    simpa [IntegrableOn] using hf_integrable_restrict
  -- Replace f with its indicator on s; outside s the function vanishes.
  have hf_indicator_integrable :
      Integrable (Set.indicator s fun x => f x) volume :=
    (integrable_indicator_iff hs_meas).2 hf_integrableOn
  have h_indicator_eq : Set.indicator s (fun x => f x) = f := by
    funext x
    classical
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem, hx]
    · have hx_not : x ∉ Function.support (f : ℝ → ℂ) := fun hx_support => hx (hR_bound hx_support)
      have hx_zero : f x = 0 := by
        simpa [Function.mem_support] using hx_not
      simp [hx, hx_zero]
  simpa [h_indicator_eq] using hf_indicator_integrable

/-- Simple functions with finite support have bounded support -/
lemma finite_support_bounded (f : ℝ → ℂ)
    (hf_finite : Set.Finite (Function.support f)) :
    ∃ R : ℝ, 0 < R ∧ Function.support f ⊆ Metric.closedBall 0 R := by
  have h_bounded := Set.Finite.isBounded hf_finite
  -- Get a closed ball that contains the support with some wiggle room
  obtain ⟨R, hR⟩ := h_bounded.subset_closedBall 0
  use max R 0 + 1
  constructor
  · linarith [le_max_right R 0]
  · exact subset_trans (subset_trans hR (Metric.closedBall_subset_closedBall (le_max_left _ _)))
      (Metric.closedBall_subset_closedBall (by simp : max R 0 ≤ max R 0 + 1))

lemma range_norm_subset_tsupport_image_with_zero (φ : ℝ → ℝ) :
    Set.range (fun x => ‖φ x‖) ⊆ Set.insert 0 ((fun x => ‖φ x‖) '' (tsupport φ)) := by
  intro y ⟨x, hyx⟩
  by_cases h : φ x = 0
  · -- If φ x = 0, then ‖φ x‖ = 0
    simp [h] at hyx
    subst hyx
    -- 0 is explicitly in the insert
    exact Set.mem_insert 0 _
  · -- If φ x ≠ 0, then x ∈ support φ ⊆ tsupport φ
    right
    use x
    constructor
    · exact subset_tsupport _ h
    · exact hyx

/-- Convolution of integrable function with smooth compact support function is continuous -/
lemma continuous_convolution_integrable_smooth (f : ℝ → ℂ) (φ : ℝ → ℝ)
    (hf_integrable : Integrable f) (hφ_smooth : ContDiff ℝ (↑⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) :
    Continuous (fun x => ∫ y, f y * (φ (x - y) : ℂ)) := by
  classical
  let φℂ : ℝ → ℂ := fun x => (φ x : ℂ)
  have h_support_eq : Function.support φℂ = Function.support φ := by
    ext x; simp [φℂ, Function.mem_support]
  have hφℂ_compact : HasCompactSupport φℂ := by
    simpa [HasCompactSupport, tsupport, φℂ, h_support_eq] using hφ_compact
  have hφℂ_smooth : ContDiff ℝ (⊤ : ℕ∞) φℂ := by
    simpa [φℂ, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp hφ_smooth)
  have h_contDiff :=
    hφℂ_compact.contDiff_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
      (hf := hf_integrable.locallyIntegrable) (hg := hφℂ_smooth)
  have h_cont : Continuous (convolution f φℂ (ContinuousLinearMap.mul ℝ ℂ) volume) :=
    h_contDiff.continuous
  -- Show that the convolution equals the integral we want
  have h_eq : (fun x => ∫ y, f y * (φ (x - y) : ℂ)) =
              convolution f φℂ (ContinuousLinearMap.mul ℝ ℂ) volume := by
    ext x
    rw [convolution_def]
    simp only [φℂ]
    simp
  rw [h_eq]
  exact h_cont

/-- Truncations of simple functions are integrable -/
lemma simpleFunc_truncation_integrable {σ : ℝ} (_ : 1 / 2 < σ)
    (f : SimpleFunc ℝ ℂ) (R : ℝ) :
    Integrable (fun x => if |x| ≤ R then f x else 0) := by
  -- Simple functions are bounded and measurable
  -- Their truncations have compact support, hence are integrable
  classical
  -- Work with the ambient bounded interval
  set s : Set ℝ := Set.Icc (-R) R
  have hs_meas : MeasurableSet s := measurableSet_Icc
  -- The interval has finite Lebesgue measure
  have hs_volume_lt_top : volume s < ∞ := by
    have hs_eq : volume s = ENNReal.ofReal (R - (-R)) := by
      simp [s, sub_neg_eq_add]
    have : ENNReal.ofReal (R - (-R)) < ∞ := by simp
    simp [hs_eq]
  -- Hence the restricted measure is finite
  haveI : IsFiniteMeasure (volume.restrict s) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply, hs_meas, Set.inter_univ]
      using hs_volume_lt_top
  -- Obtain a uniform bound on the simple function
  obtain ⟨C, hC⟩ := (f.map fun z : ℂ => (‖z‖ : ℝ)).exists_forall_le
  have h_bound : ∀ x, ‖f x‖ ≤ C := by
    intro x
    simpa using hC x
  have h_bound_ae : ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ C :=
    Filter.Eventually.of_forall h_bound
  -- Show integrability on the bounded interval
  have hf_integrable_restrict : Integrable f (volume.restrict s) := by
    refine ⟨?_, ?_⟩
    · exact SimpleFunc.aestronglyMeasurable (μ := volume.restrict s) f
    · exact HasFiniteIntegral.of_bounded (μ := volume.restrict s) h_bound_ae
  have hf_integrableOn : IntegrableOn f s volume := by
    simpa [IntegrableOn] using hf_integrable_restrict
  -- The truncation is the indicator of the interval applied to f
  have h_indicator_eq :
      (fun x => if |x| ≤ R then f x else 0) = Set.indicator s (fun x => f x) := by
    funext x
    by_cases hx : |x| ≤ R
    · have hx_mem : x ∈ s := by
        change -R ≤ x ∧ x ≤ R
        exact (abs_le.mp hx)
      simp [s, hx, hx_mem]
    · have hx_not : x ∉ s := by
        refine fun hx_mem ↦ hx ?_
        have : -R ≤ x ∧ x ≤ R := by
          simpa [s, Set.mem_Icc] using hx_mem
        exact abs_le.mpr this
      simp [s, hx, hx_not]
  -- Apply the indicator integrability criterion
  have hf_indicator_integrable :
      Integrable (Set.indicator s fun x => f x) volume :=
    (integrable_indicator_iff hs_meas).2 hf_integrableOn
  simpa [h_indicator_eq]
    using hf_indicator_integrable

end SchwartzDensity

end Frourio
