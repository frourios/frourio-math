import Frourio.Analysis.MellinBasic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory Measure Real Complex SchwartzMap intervalIntegral
open scoped ENNReal Topology ComplexConjugate

namespace Frourio

/-!
# Weighted L² Hilbert Spaces for Mellin Transform Theory

This file implements the weighted L² spaces Hσ that are central to the Mellin transform
formulation of Frourio mathematics. These spaces are L²((0,∞), x^(2σ-1) dx) with respect
to the multiplicative Haar measure.

## Main Definitions

- `weightFunction`: The weight function x^(2σ-1) for the measure
- `weightedMeasure`: The weighted measure x^(2σ-1) * (dx/x)
- Inner product structure on Hσ
- Completeness of Hσ

## Main Theorems

- `Hσ.completeSpace`: Hσ is a complete metric space
- `weightedMeasure_finite_conditions`: Characterization of when the weighted measure is finite
- `schwartz_dense_in_Hσ`: Schwartz functions are dense in Hσ
-/

section WeightFunction

/-- The weight function for the weighted L² space -/
noncomputable def weightFunction (σ : ℝ) : ℝ → ℝ≥0∞ :=
  fun x => if x > 0 then ENNReal.ofReal (x ^ (2 * σ - 1)) else 0

lemma weightFunction_measurable (σ : ℝ) : Measurable (weightFunction σ) := by
  unfold weightFunction
  apply Measurable.ite
  · exact measurableSet_Ioi
  · apply Measurable.ennreal_ofReal
    apply Measurable.pow measurable_id (measurable_const)
  · exact measurable_const

/-- The weighted measure for Hσ -/
noncomputable def weightedMeasure (σ : ℝ) : Measure ℝ :=
  mulHaar.withDensity (weightFunction σ)

lemma weightedMeasure_apply (σ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    weightedMeasure σ s = ∫⁻ x in s ∩ Set.Ioi 0, ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
  have h_measure :
      weightedMeasure σ =
        (volume.withDensity fun x => ENNReal.ofReal (1 / x)).withDensity
          ((Set.Ioi (0 : ℝ)).indicator (weightFunction σ)) := by
    simpa [weightedMeasure, mulHaar] using
      (withDensity_indicator (μ := volume.withDensity fun x => ENNReal.ofReal (1 / x))
        (s := Set.Ioi (0 : ℝ)) (f := weightFunction σ) measurableSet_Ioi).symm
  have h_div : Measurable fun x : ℝ => ENNReal.ofReal (1 / x) := by
    apply Measurable.ennreal_ofReal
    simpa using (Measurable.div measurable_const measurable_id)
  have h_indicator_meas :
      Measurable fun x : ℝ =>
        Set.indicator (s ∩ Set.Ioi (0 : ℝ)) (weightFunction σ) x := by
    apply Measurable.indicator
    · exact weightFunction_measurable σ
    · exact hs.inter measurableSet_Ioi
  have h0 :
      weightedMeasure σ s =
        ∫⁻ x in s,
          (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x
            ∂ (volume.withDensity fun x => ENNReal.ofReal (1 / x)) := by
    simp [h_measure, withDensity_apply, hs]
  have h1 :
      ∫⁻ x in s,
          (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x
            ∂ (volume.withDensity fun x => ENNReal.ofReal (1 / x))
        = ∫⁻ x in s ∩ Set.Ioi 0, weightFunction σ x
            ∂ (volume.withDensity fun x => ENNReal.ofReal (1 / x)) := by
    simp [Set.inter_comm]
  have h2 :
      ∫⁻ x in s ∩ Set.Ioi 0, weightFunction σ x
          ∂ (volume.withDensity fun x => ENNReal.ofReal (1 / x))
        = ∫⁻ x in s ∩ Set.Ioi 0,
            ENNReal.ofReal (1 / x) * weightFunction σ x ∂ volume := by
    have :
        (fun x : ℝ =>
            ENNReal.ofReal (1 / x) *
              Set.indicator (s ∩ Set.Ioi 0) (weightFunction σ) x)
          = Set.indicator (s ∩ Set.Ioi 0)
              (fun y : ℝ => ENNReal.ofReal (1 / y) * weightFunction σ y) := by
      funext x
      by_cases hx : x ∈ s ∩ Set.Ioi 0
      · simp [Set.indicator_of_mem, hx, mul_comm]
      · simp [Set.indicator_of_notMem, hx, mul_comm]
    calc
      ∫⁻ x in s ∩ Set.Ioi 0, weightFunction σ x
          ∂ (volume.withDensity fun x => ENNReal.ofReal (1 / x))
          = ∫⁻ x,
              Set.indicator (s ∩ Set.Ioi 0) (weightFunction σ) x
                ∂ (volume.withDensity fun x => ENNReal.ofReal (1 / x)) := by
            simp [lintegral_indicator, hs.inter measurableSet_Ioi]
      _ = ∫⁻ x,
            ENNReal.ofReal (1 / x) *
                Set.indicator (s ∩ Set.Ioi 0) (weightFunction σ) x ∂ volume := by
            simpa [Pi.mul_apply, mul_comm] using
              (lintegral_withDensity_eq_lintegral_mul
                (μ := volume) h_div h_indicator_meas)
      _ = ∫⁻ x,
            Set.indicator (s ∩ Set.Ioi 0)
                (fun y : ℝ => ENNReal.ofReal (1 / y) * weightFunction σ y) x ∂ volume := by
            simp only [this]
      _ = ∫⁻ x in s ∩ Set.Ioi 0,
            ENNReal.ofReal (1 / x) * weightFunction σ x ∂ volume := by
            simp [lintegral_indicator, hs.inter measurableSet_Ioi]
  have h3 :
      ∫⁻ x in s ∩ Set.Ioi 0,
          ENNReal.ofReal (1 / x) * weightFunction σ x ∂ volume
        = ∫⁻ x in s ∩ Set.Ioi 0, ENNReal.ofReal (x ^ (2 * σ - 2)) ∂ volume := by
    apply setLIntegral_congr_fun (μ := volume)
      (f := fun x : ℝ => ENNReal.ofReal (1 / x) * weightFunction σ x)
      (g := fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 2)))
      (s := s ∩ Set.Ioi 0)
      (hs := hs.inter measurableSet_Ioi)
    intro x hx
    have hx_pos : 0 < x := hx.2
    have hx1 : 0 ≤ 1 / x := by positivity
    have hx2 : 0 ≤ x ^ (2 * σ - 1) := by positivity
    have hcalc' : x ^ (2 * σ - 2) = x ^ (2 * σ - 1) / x := by
      have := Real.rpow_sub hx_pos (2 * σ - 1) 1
      have hExp : (2 * σ - 1) - 1 = 2 * σ - 2 := by ring
      simpa [hExp, Real.rpow_one] using this
    have hWF : weightFunction σ x = ENNReal.ofReal (x ^ (2 * σ - 1)) := by
      simp [weightFunction, hx_pos]
    have hcalc_div : x ^ (2 * σ - 1) / x = x ^ (2 * σ - 2) := by
      have hExp : (2 * σ - 1) - 1 = 2 * σ - 2 := by ring
      simpa [hExp, Real.rpow_one] using
        (Real.rpow_sub hx_pos (2 * σ - 1) 1).symm
    have hcalc_mul : (1 / x) * x ^ (2 * σ - 1) = x ^ (2 * σ - 2) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hcalc_div
    have hcalc_inv : x⁻¹ * x ^ (2 * σ - 1) = x ^ (2 * σ - 2) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hcalc_div
    have hx_mul :
        ENNReal.ofReal (1 / x) * ENNReal.ofReal (x ^ (2 * σ - 1)) =
          ENNReal.ofReal ((1 / x) * x ^ (2 * σ - 1)) :=
      (ENNReal.ofReal_mul (p := 1 / x) (q := x ^ (2 * σ - 1)) hx1).symm
    calc
      ENNReal.ofReal (1 / x) * weightFunction σ x
          = ENNReal.ofReal (1 / x) * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
            simp [hWF]
      _ = ENNReal.ofReal ((1 / x) * x ^ (2 * σ - 1)) := hx_mul
      _ = ENNReal.ofReal (x ^ (2 * σ - 2)) := by
            simp [hcalc_inv]
  exact (h0.trans h1).trans (h2.trans h3)

end WeightFunction

section InnerProduct

/-- Inner product on Hσ inherited from L² structure -/
noncomputable instance Hσ.innerProductSpace (σ : ℝ) : InnerProductSpace ℂ (Hσ σ) :=
  inferInstance

/-- The inner product on Hσ is the L2 inner product with weighted measure -/
theorem Hσ_inner_def (σ : ℝ) (f g : Hσ σ) :
    @inner ℂ (Hσ σ) _ f g =
    ∫ x, conj (Hσ.toFun f x) * (Hσ.toFun g x)
      ∂(mulHaar.withDensity (fun x => ENNReal.ofReal (x^(2*σ-1)))) := by
  rw [L2.inner_def]
  congr 1
  ext x
  simp only [Hσ.toFun, Inner.inner]
  ring

/-- The inner product conjugate symmetry in Hσ -/
theorem Hσ_inner_conj_symm (σ : ℝ) (f g : Hσ σ) :
    @inner ℂ (Hσ σ) _ f g = conj (@inner ℂ (Hσ σ) _ g f) := by
  rw [inner_conj_symm]

lemma Hσ.norm_squared (σ : ℝ) (f : Hσ σ) :
    ‖f‖^2 = (∫⁻ x, ‖Hσ.toFun f x‖₊^2
      ∂(mulHaar.withDensity (fun x => ENNReal.ofReal (x^(2*σ-1))))).toReal := by
  -- Apply Lp_norm_sq_as_lintegral from MellinBasic
  exact Lp_norm_sq_as_lintegral f

end InnerProduct

section Completeness

/-- Hσ is a complete metric space -/
instance Hσ.completeSpace (σ : ℝ) : CompleteSpace (Hσ σ) :=
  -- L² spaces are complete by default
  inferInstance

/-- Cauchy sequences in Hσ converge -/
theorem Hσ.cauchy_complete (σ : ℝ) (f : ℕ → Hσ σ) (hf : CauchySeq f) :
    ∃ g : Hσ σ, Filter.Tendsto f Filter.atTop (𝓝 g) := by
  exact CompleteSpace.complete hf

end Completeness

section MeasureFiniteness

/-- Conditions for the weighted measure to be finite on bounded sets -/
theorem weightedMeasure_finite_on_bounded (σ : ℝ) (a b : ℝ) (ha : 0 < a) (hb : a < b) :
    weightedMeasure σ (Set.Ioo a b) < ∞ := by
  rw [weightedMeasure_apply]
  · have : Set.Ioo a b ∩ Set.Ioi 0 = Set.Ioo a b := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
      constructor
      · intro ⟨h, _⟩; exact h
      · intro h; exact ⟨h, by linarith [h.1]⟩
    rw [this]
    -- The integral ∫_a^b x^(2σ-2) dx is finite for all σ
    -- For bounded intervals [a,b] with a > 0, x^(2σ-2) is bounded
    have : ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume < ∞ := by
      have hμ : volume (Set.Ioo a b) ≠ ∞ := by
        simp [Real.volume_Ioo]
      set p : ℝ := 2 * σ - 2
      have hb_pos : 0 < b := lt_trans ha hb
      have hbound : ∀ x ∈ Set.Ioo a b, x ^ p ≤ max (a ^ p) (b ^ p) := by
        intro x hx
        have hx_pos : 0 < x := lt_trans ha hx.1
        have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
        by_cases hp : p ≤ 0
        · have hx_le : x ^ p ≤ a ^ p :=
            Real.rpow_le_rpow_of_nonpos ha (le_of_lt hx.1) hp
          exact hx_le.trans (le_max_left _ _)
        · have hp_nonneg : 0 ≤ p := le_of_lt (lt_of_not_ge hp)
          have hx_le : x ^ p ≤ b ^ p :=
            Real.rpow_le_rpow hx_nonneg (le_of_lt hx.2) hp_nonneg
          exact hx_le.trans (le_max_right _ _)
      have ha_nonneg : 0 ≤ a ^ p := Real.rpow_nonneg (le_of_lt ha) p
      have hM_nonneg : 0 ≤ max (a ^ p) (b ^ p) :=
        ha_nonneg.trans (le_max_left _ _)
      let M := max (a ^ p) (b ^ p)
      refine MeasureTheory.setLIntegral_lt_top_of_le_nnreal hμ ?_
      refine ⟨⟨M, hM_nonneg⟩, ?_⟩
      intro x hx
      have hx_le : x ^ p ≤ M := hbound x hx
      have hx_ofReal : ENNReal.ofReal (x ^ p) ≤ ENNReal.ofReal M :=
        ENNReal.ofReal_le_ofReal hx_le
      simp only [ENNReal.coe_nnreal_eq]
      exact hx_ofReal
    exact this
  · exact measurableSet_Ioo

lemma weightedMeasure_Ioc_zero_one_lt_top {σ : ℝ} (hσ : 1 / 2 < σ) :
    weightedMeasure σ (Set.Ioc (0 : ℝ) 1) < ∞ := by
  classical
  have h_apply :=
    weightedMeasure_apply σ (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
  have h_inter :
      Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi 0 = Set.Ioc (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, hx.1⟩
  have h_measure :
      weightedMeasure σ (Set.Ioc (0 : ℝ) 1)
        = ∫⁻ x in Set.Ioc (0 : ℝ) 1,
            ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
    simpa [h_inter] using h_apply
  have h_denom_pos : 0 < 2 * σ - 1 := by linarith [hσ]
  have h_exp_neg : -1 < 2 * σ - 2 := by linarith [hσ]
  set ν := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have h_integrableOn :
      IntegrableOn (fun x : ℝ => x ^ (2 * σ - 2)) (Set.Ioc (0 : ℝ) 1) volume := by
    have h_int :=
      (intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
          (r := 2 * σ - 2) h_exp_neg)
    have :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
          (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) ≤ 1)
          (f := fun x : ℝ => x ^ (2 * σ - 2))).mp h_int
    simpa using this
  have h_integrable : Integrable (fun x : ℝ => x ^ (2 * σ - 2)) ν := by
    simpa [ν, IntegrableOn] using h_integrableOn
  have h_nonneg :
      0 ≤ᵐ[ν] fun x : ℝ => x ^ (2 * σ - 2) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact Real.rpow_nonneg (le_of_lt hx.1) _
  have h_lintegral :
      ∫⁻ x in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume
        = ENNReal.ofReal (∫ x, x ^ (2 * σ - 2) ∂ν) := by
    simpa [ν, h_inter] using
      (ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg).symm
  have h₁ :
      ∫ x, x ^ (2 * σ - 2) ∂ν
        = ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (2 * σ - 2) ∂volume := by
    simp [ν]
  have h_integral_value :
      ∫ x, x ^ (2 * σ - 2) ∂ν = (2 * σ - 1)⁻¹ := by
    have h_interval :
        ∫ x in (0 : ℝ)..1, x ^ (2 * σ - 2) ∂volume = (2 * σ - 1)⁻¹ := by
      have h_int :=
        integral_rpow (a := (0 : ℝ)) (b := 1)
          (r := 2 * σ - 2) (Or.inl h_exp_neg)
      have h_zero : (0 : ℝ) ^ (2 * σ - 1) = 0 := by
        simpa using Real.zero_rpow (ne_of_gt h_denom_pos)
      have h_one : (1 : ℝ) ^ (2 * σ - 1) = 1 := by simp
      have h_sum : 2 * σ - 2 + 1 = 2 * σ - 1 := by ring
      simpa [h_sum, h_zero, h_one] using h_int
    have h₂ :
        ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (2 * σ - 2) ∂volume
          = (2 * σ - 1)⁻¹ := by
      have h_convert :=
        (intervalIntegral.integral_of_le (μ := volume)
            (f := fun x : ℝ => x ^ (2 * σ - 2))
            (a := (0 : ℝ)) (b := 1) (by norm_num)).symm
      simpa [h_convert] using h_interval
    calc
      ∫ x, x ^ (2 * σ - 2) ∂ν
          = ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (2 * σ - 2) ∂volume := h₁
      _ = (2 * σ - 1)⁻¹ := h₂
  have h_measure_value :
      weightedMeasure σ (Set.Ioc (0 : ℝ) 1)
        = ENNReal.ofReal (1 / (2 * σ - 1)) := by
    have h_inv : (2 * σ - 1)⁻¹ = (1 : ℝ) / (2 * σ - 1) := by
      simp [one_div]
    calc
      weightedMeasure σ (Set.Ioc (0 : ℝ) 1)
          = ∫⁻ x in Set.Ioc (0 : ℝ) 1,
              ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := h_measure
      _ = ENNReal.ofReal (∫ x, x ^ (2 * σ - 2) ∂ν) := h_lintegral
      _ = ENNReal.ofReal ((2 * σ - 1)⁻¹) :=
        congrArg ENNReal.ofReal h_integral_value
      _ = ENNReal.ofReal (1 / (2 * σ - 1)) := by
        rw [h_inv]
  have h_lt_top : ENNReal.ofReal (1 / (2 * σ - 1)) < ∞ := by
    simp
  rw [h_measure_value]
  exact h_lt_top

instance weightedMeasure_isLocallyFinite (σ : ℝ) [Fact (1 / 2 < σ)] :
    IsLocallyFiniteMeasure (weightedMeasure σ) := by
  classical
  refine ⟨fun x => ?_⟩
  have hσ : 1 / 2 < σ := (inferInstance : Fact (1 / 2 < σ)).out
  cases lt_trichotomy x 0 with
  | inl hx_neg =>
      -- any negative neighbourhood has zero weighted measure
      refine ⟨Set.Iio (0 : ℝ), (isOpen_Iio.mem_nhds hx_neg), ?_⟩
      have h_apply :=
        weightedMeasure_apply σ (Set.Iio (0 : ℝ)) measurableSet_Iio
      have h_inter : Set.Iio (0 : ℝ) ∩ Set.Ioi 0 = (∅ : Set ℝ) := by
        ext t; constructor
        · rintro ⟨ht₁, ht₂⟩
          have : (0 : ℝ) < 0 := lt_trans ht₂ ht₁
          exact (lt_irrefl _ this).elim
        · intro ht; simpa using ht.elim
      have h_measure : weightedMeasure σ (Set.Iio (0 : ℝ)) = 0 := by
        simpa [h_inter] using h_apply
      rw [h_measure]
      exact ENNReal.zero_lt_top
  | inr hx_ge =>
      cases hx_ge with
      | inl hx_eq =>
          -- a symmetric interval around 0 has finite measure
          have hx_zero : x = 0 := hx_eq
          refine ⟨Set.Ioo (-1 : ℝ) 1, ?_, ?_⟩
          · have hx_mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by simp
            simpa [hx_zero] using (isOpen_Ioo.mem_nhds hx_mem)
          · have h_apply_neg :=
              weightedMeasure_apply σ (Set.Ioo (-1 : ℝ) 1) measurableSet_Ioo
            have h_inter_neg :
                Set.Ioo (-1 : ℝ) 1 ∩ Set.Ioi 0 = Set.Ioo (0 : ℝ) 1 := by
              ext t; constructor
              · rintro ⟨ht₁, ht₂⟩; exact ⟨ht₂, ht₁.2⟩
              · intro ht; exact ⟨⟨lt_of_le_of_lt (by norm_num) ht.1, ht.2⟩, ht.1⟩
            have h_apply_pos :=
              weightedMeasure_apply σ (Set.Ioo (0 : ℝ) 1) measurableSet_Ioo
            have h_inter_pos :
                Set.Ioo (0 : ℝ) 1 ∩ Set.Ioi 0 = Set.Ioo (0 : ℝ) 1 := by
              ext t; constructor
              · rintro ⟨ht₁, ht₂⟩; exact ⟨ht₂, ht₁.2⟩
              · intro ht; exact ⟨⟨ht.1, ht.2⟩, ht.1⟩
            have h_neg' :
                weightedMeasure σ (Set.Ioo (-1 : ℝ) 1)
                  = ∫⁻ x in Set.Ioo (0 : ℝ) 1,
                      ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
              simpa [h_inter_neg] using h_apply_neg
            have h_pos' :
                weightedMeasure σ (Set.Ioo (0 : ℝ) 1)
                  = ∫⁻ x in Set.Ioo (0 : ℝ) 1,
                      ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
              simpa [h_inter_pos] using h_apply_pos
            have h_eq :
                weightedMeasure σ (Set.Ioo (-1 : ℝ) 1)
                  = weightedMeasure σ (Set.Ioo (0 : ℝ) 1) :=
              h_neg'.trans h_pos'.symm
            have h_subset :
                Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc (0 : ℝ) 1 := by
              intro t ht; exact ⟨ht.1, le_of_lt ht.2⟩
            have h_le :
                weightedMeasure σ (Set.Ioo (0 : ℝ) 1)
                  ≤ weightedMeasure σ (Set.Ioc (0 : ℝ) 1) :=
              measure_mono h_subset
            have h_fin := weightedMeasure_Ioc_zero_one_lt_top (σ := σ) hσ
            exact h_eq ▸ lt_of_le_of_lt h_le h_fin
      | inr hx_pos =>
          -- use a bounded interval around the positive point
          have hx_pos' : 0 < x := hx_pos
          let s := Set.Ioo (x / 2) (x + 1)
          have hs_open : IsOpen s := isOpen_Ioo
          have hx_mem : x ∈ s := by
            constructor
            · exact div_lt_self hx_pos' (by norm_num)
            · exact by simp
          have hs_mem : s ∈ 𝓝 x := hs_open.mem_nhds hx_mem
          have ha : 0 < x / 2 := by simpa using (half_pos hx_pos')
          have hb : x / 2 < x + 1 := by
            have hx_lt : x / 2 < x := div_lt_self hx_pos' (by norm_num)
            exact hx_lt.trans (lt_add_one x)
          have h_fin :=
            weightedMeasure_finite_on_bounded (σ := σ) (a := x / 2)
              (b := x + 1) ha hb
          exact ⟨s, hs_mem, h_fin⟩

/-- mulHaar is sigma-finite -/
instance mulHaar_sigmaFinite : SigmaFinite mulHaar := by
  -- mulHaar = (volume.withDensity (fun x => ENNReal.ofReal (1 / x))).restrict (Set.Ioi 0)
  -- Step 1: volume is sigma-finite
  -- Step 2: withDensity_ofReal preserves sigma-finiteness
  -- Step 3: Restrict.sigmaFinite preserves sigma-finiteness
  unfold mulHaar
  -- Apply Restrict.sigmaFinite
  have h1 : SigmaFinite (volume.withDensity fun x => ENNReal.ofReal (1 / x)) := by
    exact SigmaFinite.withDensity_ofReal _
  exact Restrict.sigmaFinite _ _

/-- The weighted measure is sigma-finite -/
instance weightedMeasure_sigmaFinite (σ : ℝ) : SigmaFinite (weightedMeasure σ) := by
  -- weightedMeasure = mulHaar.withDensity (weightFunction σ)
  -- mulHaar is sigma-finite (proven above)
  -- weightFunction is essentially ENNReal.ofReal, so we can use withDensity_ofReal
  unfold weightedMeasure weightFunction
  -- The weight function can be expressed as ENNReal.ofReal of a real function
  have : mulHaar.withDensity (fun x => if x > 0 then ENNReal.ofReal (x ^ (2 * σ - 1)) else 0) =
         mulHaar.withDensity (fun x => ENNReal.ofReal (if x > 0 then x ^ (2 * σ - 1) else 0)) := by
    congr 1
    ext x
    split_ifs <;> simp
  rw [this]
  exact SigmaFinite.withDensity_ofReal _

/-- The global weighted measure is always infinite.
We postpone the analytic divergence proof for a future refinement. -/
theorem weightedMeasure_global_infinite (σ : ℝ) :
    weightedMeasure σ (Set.Ioi 0) = ∞ := by
  classical
  have happly :
      weightedMeasure σ (Set.Ioi (0 : ℝ)) =
        ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
    have := weightedMeasure_apply σ (Set.Ioi (0 : ℝ)) measurableSet_Ioi
    simpa [Set.inter_self] using this
  have hchange :
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ (σ * 2 - 2)) ∂volume
        = ∫⁻ t, ENNReal.ofReal (Real.exp (t * (σ + σ - 1))) ∂volume := by
    have hcv :=
      lintegral_change_of_variables_exp
        (α := 2 * σ - 2)
        (f := fun _ : ℝ => (1 : ℝ≥0∞))
        (hf := measurable_const)
    have hrewrite :
        (fun t : ℝ => ENNReal.ofReal (Real.exp (t * (σ * 2 - 2) + t)))
          = fun t : ℝ => ENNReal.ofReal (Real.exp (t * (σ + σ - 1))) := by
      funext t
      have : t * (σ * 2 - 2) + t = t * (σ + σ - 1) := by
        ring
      simp [this]
    simp [hrewrite, mul_comm, one_mul] at hcv
    exact hcv
  set β : ℝ := 2 * σ - 1
  have hexp : ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂volume = ∞ := by
    have hcases : 0 ≤ β ∨ β ≤ 0 := le_total 0 β
    cases hcases with
    | inl hβ_nonneg =>
        set S := Set.Ioi (0 : ℝ)
        have hmono :
            (fun _ : ℝ => (1 : ℝ≥0∞)) ≤ᵐ[volume.restrict S]
                fun t => ENNReal.ofReal (Real.exp (β * t)) := by
          refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
          refine Filter.Eventually.of_forall ?_
          intro t ht
          have ht_pos : 0 < t := ht
          have hnonneg : (0 : ℝ) ≤ β * t := by
            exact mul_nonneg hβ_nonneg ht_pos.le
          have hexp_ge : (1 : ℝ) ≤ Real.exp (β * t) := by
            have := Real.exp_le_exp.mpr hnonneg
            simpa [Real.exp_zero] using this
          have hle := ENNReal.ofReal_le_ofReal hexp_ge
          simpa using hle
        have hset :
            ∞ ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂(volume.restrict S) := by
          have hmono' := lintegral_mono_ae (μ := volume.restrict S) hmono
          have hconst :
              (∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂(volume.restrict S)) = ∞ := by
            simp [Measure.restrict_apply, S, Real.volume_Ioi]
          have hineq :
              (∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂(volume.restrict S))
                ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂(volume.restrict S) :=
            hmono'
          simpa [hconst] using hineq
        have hindicator :
            (fun t : ℝ =>
              Set.indicator S
                (fun t => ENNReal.ofReal (Real.exp (β * t))) t)
              ≤ᵐ[volume]
                fun t => ENNReal.ofReal (Real.exp (β * t)) := by
          refine Filter.Eventually.of_forall ?_
          intro t
          by_cases ht : t ∈ S
          · simp [S, ht]
          · simp [S, ht]
        have htotal_ge :
            ∞ ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂volume := by
          have := lintegral_mono_ae (μ := volume) hindicator
          have hrestrict' :
              (∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂(volume.restrict S))
                ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂volume := by
            simpa [lintegral_indicator, Measure.restrict_apply, S] using this
          exact le_trans hset hrestrict'
        exact top_le_iff.mp htotal_ge
    | inr hβ_nonpos =>
        set S := Set.Iio (0 : ℝ)
        have hmono :
            (fun _ : ℝ => (1 : ℝ≥0∞)) ≤ᵐ[volume.restrict S]
                fun t => ENNReal.ofReal (Real.exp (β * t)) := by
          refine (ae_restrict_iff' measurableSet_Iio).2 ?_
          refine Filter.Eventually.of_forall ?_
          intro t ht
          have ht_neg : t < 0 := ht
          have hnonneg : (0 : ℝ) ≤ β * t := by
            exact mul_nonneg_of_nonpos_of_nonpos hβ_nonpos (le_of_lt ht_neg)
          have hexp_ge : (1 : ℝ) ≤ Real.exp (β * t) := by
            have := Real.exp_le_exp.mpr hnonneg
            simpa [Real.exp_zero] using this
          have hle := ENNReal.ofReal_le_ofReal hexp_ge
          simpa using hle
        have hset :
            ∞ ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂(volume.restrict S) := by
          have hmono' := lintegral_mono_ae (μ := volume.restrict S) hmono
          have hconst :
              (∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂(volume.restrict S)) = ∞ := by
            simp [Measure.restrict_apply, S, Real.volume_Iio]
          have hineq :
              (∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂(volume.restrict S))
                ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂(volume.restrict S) :=
            hmono'
          simpa [hconst] using hineq
        have hindicator :
            (fun t : ℝ =>
              Set.indicator S
                (fun t => ENNReal.ofReal (Real.exp (β * t))) t)
              ≤ᵐ[volume]
                fun t => ENNReal.ofReal (Real.exp (β * t)) := by
          refine Filter.Eventually.of_forall ?_
          intro t
          by_cases ht : t ∈ S
          · simp [S, ht]
          · simp [S, ht]
        have htotal_ge :
            ∞ ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂volume := by
          have := lintegral_mono_ae (μ := volume) hindicator
          have hrestrict' :
              (∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂(volume.restrict S))
                ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂volume := by
            simpa [lintegral_indicator, Measure.restrict_apply, S] using this
          exact le_trans hset hrestrict'
        exact top_le_iff.mp htotal_ge
  have hβ : β = σ + σ - 1 := by ring
  have hexp' :
      ∫⁻ t, ENNReal.ofReal (Real.exp (t * (σ + σ - 1))) ∂volume = ∞ := by
    simpa [β, hβ, mul_comm] using hexp
  have hIoi' :
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ (σ * 2 - 2)) ∂volume = ∞ :=
    hchange.trans hexp'
  have hσswap : σ * 2 - 2 = 2 * σ - 2 := by ring
  have hIoi :
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume = ∞ := by
    simpa [hσswap] using hIoi'
  exact happly.trans hIoi

lemma exists_simple_func_approximation {σ : ℝ} (f' : Lp ℂ 2 (weightedMeasure σ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Lp.simpleFunc ℂ 2 (weightedMeasure σ),
      dist (↑s : Lp ℂ 2 (weightedMeasure σ)) f' < ε := by
  have dense_simple := Lp.simpleFunc.isDenseEmbedding (p := 2) (μ := weightedMeasure σ) (E := ℂ)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  -- Use DenseRange of the embedding
  have : DenseRange ((↑) : Lp.simpleFunc ℂ 2 (weightedMeasure σ) → Lp ℂ 2 (weightedMeasure σ)) :=
    dense_simple.toIsDenseInducing.dense
  -- Apply the density property
  have mem_closure := this.closure_eq ▸ Set.mem_univ f'
  rw [Metric.mem_closure_iff] at mem_closure
  specialize mem_closure ε hε
  obtain ⟨y, hy_range, hy_close⟩ := mem_closure
  obtain ⟨s, rfl⟩ := hy_range
  have : dist (↑s : Lp ℂ 2 (weightedMeasure σ)) f' < ε := by
    rw [dist_comm]
    exact hy_close
  exact ⟨s, this⟩

/-- Helper lemma: eLpNorm of indicator function is at most the original -/
lemma eLpNorm_indicator_le_simple {σ : ℝ} (f : ℝ → ℂ)
    (S : Set ℝ) (_ : MeasurableSet S) :
    eLpNorm (Set.indicator S f) 2 (weightedMeasure σ) ≤
    eLpNorm f 2 (weightedMeasure σ) := by
  -- Use the fact that |indicator S f x| ≤ |f x| for all x
  -- This implies eLpNorm (indicator S f) ≤ eLpNorm f
  have h_pointwise : ∀ x, ‖Set.indicator S f x‖ ≤ ‖f x‖ := by
    intro x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, norm_nonneg]
  -- Apply the monotonicity of eLpNorm
  -- We need to show that eLpNorm of a dominated function is smaller
  -- Use eLpNorm_mono or a similar lemma from MeasureTheory
  have h_ae : ∀ᵐ x ∂(weightedMeasure σ), ‖Set.indicator S f x‖ ≤ ‖f x‖ := by
    exact Filter.Eventually.of_forall h_pointwise
  -- Apply the monotonicity lemma for eLpNorm
  exact eLpNorm_mono_ae h_ae

/-- Measurability of the extended mollifier function -/
lemma measurable_extended_mollifier (δ : ℝ) :
    Measurable (fun t => if t ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - t^2)) else 0) := by
  apply Measurable.piecewise measurableSet_Ioo
  · apply Measurable.exp
    apply Measurable.div
    · exact measurable_const
    · apply Measurable.sub
      · exact measurable_const
      · exact continuous_pow 2 |>.measurable
  · exact measurable_const

/-- Helper lemma: The indicator of toSimpleFunc on a measurable set is AE strongly measurable -/
lemma indicator_toSimpleFunc_aestrongly_measurable {σ : ℝ}
    (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ)) (S : Set ℝ) (hS : MeasurableSet S) :
    AEStronglyMeasurable (Set.indicator S (Lp.simpleFunc.toSimpleFunc s : ℝ → ℂ))
    (weightedMeasure σ) := by
  have h_meas : Measurable (Lp.simpleFunc.toSimpleFunc s : ℝ → ℂ) := Lp.simpleFunc.measurable s
  exact AEStronglyMeasurable.indicator h_meas.aestronglyMeasurable hS

/-- Helper lemma: A truncated simple function with compact support is in L² -/
lemma truncated_simple_func_mem_Lp {σ : ℝ} (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (n : ℕ) :
    let truncate := fun x : ℝ => if 1/(n : ℝ) < x ∧ x < (n : ℝ)
      then Lp.simpleFunc.toSimpleFunc s x else 0
    MemLp truncate 2 (weightedMeasure σ) := by
  intro truncate
  -- To prove MemLp, we need to show the function is AEStronglyMeasurable and has finite Lp seminorm
  refine ⟨?_, ?_⟩
  -- First: prove truncate is AEStronglyMeasurable
  · -- The simple function s is measurable
    have hs_meas : AEStronglyMeasurable (s : ℝ → ℂ) (weightedMeasure σ) :=
      Lp.aestronglyMeasurable (↑s : Lp ℂ 2 (weightedMeasure σ))
    -- The truncation preserves measurability
    have h_set : MeasurableSet {x : ℝ | 1/(n : ℝ) < x ∧ x < (n : ℝ)} := by
      apply MeasurableSet.inter
      · exact measurableSet_Ioi
      · exact measurableSet_Iio
    change AEStronglyMeasurable (fun x : ℝ => if 1/(n : ℝ) < x ∧ x < (n : ℝ)
      then Lp.simpleFunc.toSimpleFunc s x else 0) _
    -- Convert to indicator form
    have h_eq : (fun x : ℝ => if 1/(n : ℝ) < x ∧ x < (n : ℝ)
        then Lp.simpleFunc.toSimpleFunc s x else 0) =
        Set.indicator {x | 1/(n : ℝ) < x ∧ x < (n : ℝ)} (Lp.simpleFunc.toSimpleFunc s) := by
      ext x
      simp only [Set.indicator, Set.mem_setOf_eq]
      split_ifs <;> rfl
    rw [h_eq]
    -- Apply the helper lemma
    exact indicator_toSimpleFunc_aestrongly_measurable s _ h_set
  -- Second: prove the Lp seminorm is finite
  · -- The truncated function has compact support [1/n, n] and is bounded by s
    -- Since s is in L² and we're restricting to a bounded interval, the norm is finite
    -- Use a simpler approach: directly show finiteness
    suffices eLpNorm truncate 2 (weightedMeasure σ) < ⊤ by exact this
    -- Use the extracted lemma for s's finite norm
    have h_s_finite := Lp.eLpNorm_lt_top (↑s : Lp ℂ 2 (weightedMeasure σ))
    -- The truncated function's norm is at most s's norm
    -- First note that toSimpleFunc s =ᵐ[weightedMeasure σ] s
    have h_ae_eq : (Lp.simpleFunc.toSimpleFunc s : ℝ → ℂ) =ᵐ[weightedMeasure σ] (s : ℝ → ℂ) :=
      Lp.simpleFunc.toSimpleFunc_eq_toFun s
    calc eLpNorm truncate 2 (weightedMeasure σ)
        ≤ eLpNorm (Lp.simpleFunc.toSimpleFunc s : ℝ → ℂ) 2 (weightedMeasure σ) := by
          -- truncate is s restricted to {x | 1/n < x < n}
          -- Use the fact that restricting to a subset reduces the norm
          simp only [truncate]
          -- Convert to indicator function form
          have h_eq : (fun x => if 1/(n : ℝ) < x ∧ x < (n : ℝ)
              then Lp.simpleFunc.toSimpleFunc s x else 0)
              = Set.indicator {x | 1/(n : ℝ) < x ∧ x < (n : ℝ)} (Lp.simpleFunc.toSimpleFunc s) := by
            ext x
            simp only [Set.indicator, Set.mem_setOf_eq]
            split_ifs <;> rfl
          rw [h_eq]
          -- Apply the extracted lemma for indicator inequality
          apply eLpNorm_indicator_le_simple (Lp.simpleFunc.toSimpleFunc s)
          apply MeasurableSet.inter
          · exact measurableSet_Ioi
          · exact measurableSet_Iio
        _ = eLpNorm (s : ℝ → ℂ) 2 (weightedMeasure σ) := by
          -- Use the a.e. equality
          exact eLpNorm_congr_ae h_ae_eq
        _ < ⊤ := h_s_finite

lemma mollifier_extended_continuous : ∀ (δ' : ℝ) (_ : 0 < δ'),
    ContinuousOn (fun s => if |s| < δ' then Real.exp (-1 / (δ'^2 - s^2)) else 0)
                  (Set.uIcc (-δ') δ') := by
  intro δ' hδ'_pos
  -- Define the function explicitly
  set f_extended := fun s => if |s| < δ' then Real.exp (-1 / (δ'^2 - s^2)) else 0 with hf

  -- Strategy: Show continuity by cases
  -- 1. On the interior |t| < δ': the function is continuous as composition of continuous functions
  -- 2. At the boundary points t = ±δ': need to show limit from inside equals 0
  -- 3. Outside |t| > δ': the function is constantly 0

  -- Step 1: Show continuity on the open interval (-δ', δ')
  have h_cont_interior : ∀ t ∈ Set.Ioo (-δ') δ',
      ContinuousWithinAt f_extended (Set.uIcc (-δ') δ') t := by
    intro t ht
    -- On the interior, |t| < δ' so the function equals exp(-1/(δ'²-t²))
    -- This is continuous as composition of continuous functions

    -- First show that |t| < δ' from the open interval condition
    have ht_abs : |t| < δ' := by
      rw [abs_lt]
      exact ⟨ht.1, ht.2⟩

    -- Find a neighborhood where the function has the explicit form
    have h_nbhd : ∃ ε > 0, ∀ s ∈ Metric.ball t ε, |s| < δ' := by
      use (δ' - |t|) / 2
      constructor
      · apply div_pos
        · linarith
        · norm_num
      · intro s hs
        rw [Metric.mem_ball, Real.dist_eq] at hs
        have h1 : |s - t| < (δ' - |t|) / 2 := hs
        calc |s| = |t + (s - t)| := by ring_nf
        _ ≤ |t| + |s - t| := abs_add _ _
        _ < |t| + (δ' - |t|) / 2 := by linarith
        _ = δ' - (δ' - |t|) / 2 := by ring
        _ < δ' := by linarith

    -- On this neighborhood, f_extended equals exp(-1/(δ'²-s²))
    obtain ⟨ε, hε_pos, hε_ball⟩ := h_nbhd

    -- The function equals exp(-1/(δ'²-s²)) for all s in the ball
    have h_eq : ∀ᶠ s in 𝓝 t, f_extended s = Real.exp (-1 / (δ'^2 - s^2)) := by
      apply eventually_nhds_iff.mpr
      use {s | |s| < δ'}
      constructor
      · intro s hs
        simp only [f_extended]
        split_ifs with h
        · rfl
        · -- Case: |s| ≥ δ' but s ∈ {s | |s| < δ'}, contradiction
          exfalso
          exact h hs
      · constructor
        · -- Show that {s | |s| < δ'} is open
          have : {s : ℝ | |s| < δ'} = abs ⁻¹' Set.Iio δ' := by
            ext x; simp [Set.mem_preimage, Set.mem_Iio]
          rw [this]
          exact isOpen_Iio.preimage continuous_norm
        · exact ht_abs

    -- Now show continuity of s ↦ exp(-1/(δ'²-s²)) at t
    have h_cont : ContinuousAt (fun s => Real.exp (-1 / (δ'^2 - s^2))) t := by
      -- δ'² - t² > 0 since |t| < δ'
      have h_pos : 0 < δ'^2 - t^2 := by
        have : t^2 < δ'^2 := by
          -- Use that t ∈ (-δ', δ') means -δ' < t < δ'
          have ht_lower : -δ' < t := ht.1
          have ht_upper : t < δ' := ht.2
          exact sq_lt_sq' ht_lower ht_upper
        linarith

      -- The function s ↦ -1 / (δ'^2 - s^2) is continuous at t
      have h_inner : ContinuousAt (fun s => -1 / (δ'^2 - s^2)) t := by
        apply ContinuousAt.div
        · exact continuousAt_const
        · apply ContinuousAt.sub
          · exact continuousAt_const
          · exact ContinuousAt.pow continuousAt_id 2
        · exact h_pos.ne'

      -- Real.exp is continuous, so composition is continuous
      exact Real.continuous_exp.continuousAt.comp h_inner

    -- Transfer continuity through the eventual equality
    have h_cont_within : ContinuousWithinAt f_extended (Set.uIcc (-δ') δ') t := by
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.congr_of_eventuallyEq h_cont
      -- h_eq says: ∀ᶠ s in 𝓝 t, f_extended s = Real.exp (-1 / (δ'^2 - s^2))
      -- We need: f_extended =ᶠ[𝓝 t] fun s => Real.exp (-1 / (δ'^2 - s^2))
      exact h_eq
    exact h_cont_within

  -- Step 2: Show continuity at the boundary points
  have h_cont_boundary : ∀ (t : ℝ), (t = -δ' ∨ t = δ') →
      ContinuousWithinAt f_extended (Set.uIcc (-δ') δ') t := by
    intro t ht
    -- At boundary points, the function equals 0
    -- Need to show the limit from inside approaches 0

    -- First, show that f_extended(t) = 0 at the boundary
    have ht_eq : f_extended t = 0 := by
      simp only [f_extended]
      split_ifs with h
      · -- Case: |t| < δ', but we know t = ±δ'
        exfalso
        cases ht with
        | inl h_left =>
          -- t = -δ', so |t| = |-δ'| = δ'
          rw [h_left] at h
          rw [abs_neg, abs_of_nonneg (le_of_lt hδ'_pos)] at h
          exact lt_irrefl δ' h
        | inr h_right =>
          -- t = δ', so |t| = |δ'| = δ'
          rw [h_right] at h
          rw [abs_of_nonneg (le_of_lt hδ'_pos)] at h
          exact lt_irrefl δ' h
      · -- Case: |t| ≥ δ', which is true
        rfl

    -- Now show continuity within the interval
    rw [ContinuousWithinAt, ht_eq]

    -- We need to show: Tendsto f_extended (𝓝[Set.uIcc (-δ') δ'] t) (𝓝 0)
    -- This requires showing that as s → t within [-δ', δ'], f_extended(s) → 0

    -- Use the metric characterization of tendsto
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε_pos

    -- We need to find δ > 0 such that for all s ∈ [-δ', δ'] with dist s t < δ,
    -- we have dist (f_extended s) 0 < ε

    -- Key insight: As s approaches ±δ' from inside, exp(-1/(δ'^2 - s^2)) → 0
    -- because -1/(δ'^2 - s^2) → -∞

    -- Choose δ small enough that for s with |s - t| < δ and s ∈ [-δ', δ'],
    -- we have f_extended(s) < ε

    -- Since exp(x) → 0 as x → -∞, we can find M > 0 such that
    -- exp(-M) < ε
    have h_exp_small : ∃ M > 0, Real.exp (-M) < ε := by
      -- Choose M large enough that exp(-M) < ε
      -- We can use M = max(1, -log(ε))
      by_cases hε_small : ε < 1
      · -- Case: ε < 1, so we need M > -log(ε)
        -- Use M = -log(ε/2), so exp(-M) = ε/2 < ε
        use -Real.log (ε/2)
        constructor
        · -- Show -log(ε/2) > 0
          have h1 : 0 < ε/2 := by linarith
          have h2 : ε/2 < 1 := by linarith
          have : Real.log (ε/2) < 0 := Real.log_neg h1 h2
          linarith
        · -- Show exp(-(-log(ε/2))) < ε
          simp only [neg_neg]
          have h1 : 0 < ε/2 := by linarith
          rw [Real.exp_log h1]
          linarith
      · -- Case: ε ≥ 1, so exp(-1) < 1 ≤ ε works
        use 1
        constructor
        · norm_num
        · calc Real.exp (-1)
            _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
            _ ≤ ε := le_of_not_gt hε_small

    obtain ⟨M, hM_pos, hM_bound⟩ := h_exp_small

    -- Choose δ₁ such that when |s - t| < δ₁ and s ∈ (-δ', δ'),
    -- we have -1/(δ'^2 - s^2) < -M
    -- This happens when δ'^2 - s^2 < 1/M
    have h_delta_choice : ∃ δ₁ > 0, ∀ s, |s - t| < δ₁ → s ∈ Set.Ioo (-δ') δ' →
        -1 / (δ'^2 - s^2) < -M := by
      -- For any small enough δ₁, if s is in the open interval and near the boundary,
      -- then δ'^2 - s^2 is small, making -1/(δ'^2 - s^2) very negative
      -- We need to ensure -1/(δ'^2 - s^2) < -M
      -- This is equivalent to δ'^2 - s^2 < 1/M

      -- Key insight: For t = ±δ' (boundary points), if s is close to t,
      -- then δ'^2 - s^2 becomes small, making -1/(δ'^2 - s^2) very negative.

      -- Choose δ₁ small enough so that for all s with |s - t| < δ₁ and s ∈ (-δ', δ'),
      -- we have δ'^2 - s^2 < 1/M

      -- Since t = ±δ', let's handle both cases uniformly
      -- If t = δ' and s is close to δ', then s ≈ δ' but s < δ'
      -- So δ' - s is small and positive, and δ'^2 - s^2 = (δ' - s)(δ' + s) ≈ 2δ'(δ' - s)

      -- Similarly if t = -δ' and s is close to -δ', then s ≈ -δ' but s > -δ'
      -- So s + δ' is small and positive, and δ'^2 - s^2 = (δ' - s)(δ' + s) ≈ 2δ'(s + δ')

      -- In both cases, we need the product to be less than 1/M
      -- Choose δ₁ = min(δ'/2, 1/(4Mδ'))

      have h_delta_pos : 0 < 1/(4*M*δ') := by
        apply div_pos one_pos
        apply mul_pos
        · apply mul_pos
          · norm_num
          · exact hM_pos
        · exact hδ'_pos

      use min (δ'/2) (1/(4*M*δ'))
      constructor
      · apply lt_min
        · linarith
        · exact h_delta_pos
      · intro s hs_dist hs_interval
        -- Goal: -1/(δ'^2 - s^2) < -M
        -- Equivalent to: δ'^2 - s^2 < 1/M

        have hs_pos : 0 < δ'^2 - s^2 := by
          rw [Set.mem_Ioo] at hs_interval
          have : s^2 < δ'^2 := sq_lt_sq' hs_interval.1 hs_interval.2
          linarith

        -- Key estimate: bound δ'^2 - s^2 from above
        -- Since t = ±δ', we consider both cases
        cases ht with
        | inl ht_neg =>
          -- t = -δ'
          rw [ht_neg] at hs_dist
          -- |s - (-δ')| = |s + δ'| < min(δ'/2, 1/(4Mδ'))
          have h_sum_bound : |s + δ'| < 1/(4*M*δ') := by
            calc |s + δ'|
              _ = |s - (-δ')| := by simp only [sub_neg_eq_add]
              _ < min (δ'/2) (1/(4*M*δ')) := hs_dist
              _ ≤ 1/(4*M*δ') := min_le_right _ _

          -- Since s > -δ', we have s + δ' > 0
          have h_sum_pos : 0 < s + δ' := by linarith [hs_interval.1]

          -- Therefore s + δ' < 1/(4Mδ')
          have h_sum : s + δ' < 1/(4*M*δ') := by
            rw [abs_of_pos h_sum_pos] at h_sum_bound
            exact h_sum_bound

          -- Also, δ' - s < 2δ' (since s > -δ')
          have h_diff : δ' - s < 2*δ' := by linarith [hs_interval.1]

          -- Therefore δ'^2 - s^2 = (δ' - s)(δ' + s) < 2δ' · 1/(4Mδ') = 1/(2M) < 1/M
          have h_bound : δ'^2 - s^2 < 1/M := by
            calc δ'^2 - s^2
              _ = (δ' - s) * (δ' + s) := by ring
              _ = (δ' - s) * (s + δ') := by ring
              _ < 2*δ' * (1/(4*M*δ')) := by
                apply mul_lt_mul'
                · exact le_of_lt h_diff
                · exact h_sum
                · exact le_of_lt h_sum_pos
                · linarith
              _ = 1/(2*M) := by field_simp; ring
              _ < 1/M := by
                have : (2 : ℝ) > 1 := by norm_num
                have : 2 * M > M := by linarith
                exact div_lt_div_of_pos_left one_pos hM_pos this

          -- Now convert to -1/(δ'^2 - s^2) < -M
          have h_exp_bound : -1/(δ'^2 - s^2) < -M := by
            -- Since δ'^2 - s^2 < 1/M and both are positive
            have h1 : M * (δ'^2 - s^2) < 1 := by
              calc M * (δ'^2 - s^2)
                _ < M * (1/M) := by exact mul_lt_mul_of_pos_left h_bound hM_pos
                _ = 1 := by field_simp
            -- Therefore 1/(δ'^2 - s^2) > M, so -1/(δ'^2 - s^2) < -M
            have h2 : 1/(δ'^2 - s^2) > M := by
              -- From h1: M * (δ'^2 - s^2) < 1, we get M < 1/(δ'^2 - s^2)
              -- Use basic algebraic manipulation
              have h_pos_inv : 0 < 1/(δ'^2 - s^2) := one_div_pos.mpr hs_pos
              have h_mul : M * (δ'^2 - s^2) * (1/(δ'^2 - s^2)) < 1 * (1/(δ'^2 - s^2)) := by
                exact mul_lt_mul_of_pos_right h1 h_pos_inv
              -- Simplify using field_simp
              field_simp [ne_of_gt hs_pos] at h_mul
              exact h_mul
            -- From h2, we get -1/(δ'^2 - s^2) < -M
            rw [neg_div]
            exact neg_lt_neg_iff.mpr h2

          -- We have shown that -1/(δ'^2 - s^2) < -M
          -- This is exactly what we need
          exact h_exp_bound

        | inr ht_pos =>
          -- t = δ'
          rw [ht_pos] at hs_dist
          -- |s - δ'| < min(δ'/2, 1/(4Mδ'))
          have h_diff_bound : |s - δ'| < 1/(4*M*δ') := by
            calc |s - δ'|
              _ < min (δ'/2) (1/(4*M*δ')) := hs_dist
              _ ≤ 1/(4*M*δ') := min_le_right _ _

          -- Since s < δ', we have δ' - s > 0
          have h_diff_pos : 0 < δ' - s := by linarith [hs_interval.2]

          -- Therefore δ' - s < 1/(4Mδ')
          have h_diff : δ' - s < 1/(4*M*δ') := by
            have : |s - δ'| = |δ' - s| := abs_sub_comm s δ'
            rw [this, abs_of_pos h_diff_pos] at h_diff_bound
            exact h_diff_bound

          -- Also, δ' + s < 2δ' (since s < δ')
          have h_sum : δ' + s < 2*δ' := by linarith [hs_interval.2]

          -- Therefore δ'^2 - s^2 = (δ' - s)(δ' + s) < 1/(4Mδ') · 2δ' = 1/(2M) < 1/M
          have h_bound : δ'^2 - s^2 < 1/M := by
            calc δ'^2 - s^2
              _ = (δ' - s) * (δ' + s) := by ring
              _ < (1/(4*M*δ')) * (2*δ') := by
                apply mul_lt_mul'
                · exact le_of_lt h_diff
                · exact h_sum
                · linarith [hs_interval.1]
                · exact h_delta_pos
              _ = 1/(2*M) := by field_simp; ring
              _ < 1/M := by
                have : (1 : ℝ) / (2*M) < 1/M := by
                  -- Clear denominators by multiplying both sides by M * (2*M)
                  have h_mult : M * (2*M) > 0 := mul_pos hM_pos
                    (mul_pos (by norm_num : (0 : ℝ) < 2) hM_pos)
                  rw [one_div_lt_one_div (mul_pos (by norm_num : (0 : ℝ) < 2) hM_pos) hM_pos]
                  linarith
                exact this

          -- Now convert to -1/(δ'^2 - s^2) < -M
          have h_exp_bound : -1/(δ'^2 - s^2) < -M := by
            -- Since δ'^2 - s^2 < 1/M and both are positive
            have h1 : M * (δ'^2 - s^2) < 1 := by
              calc M * (δ'^2 - s^2)
                _ < M * (1/M) := by exact mul_lt_mul_of_pos_left h_bound hM_pos
                _ = 1 := by field_simp
            -- Therefore 1/(δ'^2 - s^2) > M, so -1/(δ'^2 - s^2) < -M
            have h2 : 1/(δ'^2 - s^2) > M := by
              -- From h1: M * (δ'^2 - s^2) < 1, we get M < 1/(δ'^2 - s^2)
              -- Use basic algebraic manipulation
              have h_pos_inv : 0 < 1/(δ'^2 - s^2) := one_div_pos.mpr hs_pos
              have h_mul : M * (δ'^2 - s^2) * (1/(δ'^2 - s^2)) < 1 * (1/(δ'^2 - s^2)) := by
                exact mul_lt_mul_of_pos_right h1 h_pos_inv
              -- Simplify using field_simp
              field_simp [ne_of_gt hs_pos] at h_mul
              exact h_mul
            -- From h2, we get -1/(δ'^2 - s^2) < -M
            rw [neg_div]
            exact neg_lt_neg_iff.mpr h2

          -- We have shown that -1/(δ'^2 - s^2) < -M
          -- This is exactly what we need
          exact h_exp_bound

    obtain ⟨δ₁, hδ₁_pos, hδ₁_prop⟩ := h_delta_choice

    -- Choose the final δ
    use δ₁
    constructor
    · exact hδ₁_pos
    · intro s hs_interval hs_dist
      -- Need to show: dist (f_extended s) 0 < ε
      simp only [dist_zero_right, Real.norm_eq_abs]

      -- Case analysis on whether |s| < δ'
      by_cases hs_interior : |s| < δ'
      · -- Interior case: f_extended s = exp(-1/(δ'^2 - s^2))
        simp only [f_extended, hs_interior, if_pos]

        -- We need to ensure s ∈ Set.Ioo (-δ') δ' for hδ₁_prop
        have hs_open : s ∈ Set.Ioo (-δ') δ' := by
          rw [Set.mem_Ioo, ← abs_lt]
          exact hs_interior

        -- Apply our bound
        have h_bound := hδ₁_prop s hs_dist hs_open

        -- Since exp is increasing and -1/(δ'^2 - s^2) < -M
        have : Real.exp (-1 / (δ'^2 - s^2)) < Real.exp (-M) := by
          exact Real.exp_lt_exp.mpr h_bound

        -- Combine with hM_bound
        calc
          |Real.exp (-1 / (δ'^2 - s^2))| = Real.exp (-1 / (δ'^2 - s^2)) := by
            apply abs_of_nonneg
            exact Real.exp_nonneg _
          _ < Real.exp (-M) := this
          _ < ε := hM_bound

      · -- Boundary or exterior case: f_extended s = 0
        simp only [f_extended, hs_interior, if_neg, not_false_iff, abs_zero]
        exact hε_pos

  -- Step 3: Combine to get continuity on the whole interval
  -- ContinuousOn is defined as ∀ x ∈ s, ContinuousWithinAt f s x
  intro pt hpt
  by_cases h : pt ∈ Set.Ioo (-δ') δ'
  · exact h_cont_interior pt h
  · -- pt must be a boundary point
    have : pt = -δ' ∨ pt = δ' := by
      -- pt ∈ Set.uIcc (-δ') δ' means -δ' ≤ pt ≤ δ'
      -- pt ∉ Set.Ioo (-δ') δ' means ¬(-δ' < pt < δ')
      -- Therefore pt = -δ' or pt = δ'
      rw [Set.mem_uIcc] at hpt
      rw [Set.mem_Ioo, not_and_or] at h
      rcases hpt with h_case1 | h_case2
      · -- Case: -δ' ≤ pt ≤ δ'
        rcases h with h_left | h_right
        · -- ¬(-δ' < pt), so pt ≤ -δ'
          have : pt ≤ -δ' := le_of_not_gt h_left
          exact Or.inl (le_antisymm this h_case1.1)
        · -- ¬(pt < δ'), so δ' ≤ pt
          have : δ' ≤ pt := le_of_not_gt h_right
          exact Or.inr (le_antisymm h_case1.2 this)
      · -- Case: δ' ≤ pt ≤ -δ' (impossible if δ' > 0)
        exfalso
        have : δ' ≤ -δ' := le_trans h_case2.1 h_case2.2
        linarith [hδ'_pos]
    exact h_cont_boundary pt this

/-- The integral of exp(-1/(δ²-t²)) over the open interval (-δ, δ)
    equals its interval integral over [-δ, δ] with extended function -/
lemma integral_Ioo_eq_intervalIntegral (δ : ℝ) (hδ_pos : 0 < δ) :
    let f_extended : ℝ → ℝ := fun t =>
      if t ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - t^2)) else 0
    (∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2))) =
    (∫ t in (-δ)..δ, f_extended t) := by

  -- The extended function agrees with the original on the open interval
  have h_agree : ∀ t ∈ Set.Ioo (-δ) δ,
      (if t ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - t^2)) else 0) =
      Real.exp (-1 / (δ^2 - t^2)) := by
    intro t ht
    simp only [ht, if_true]

  -- The extended function is 0 at the boundaries
  have h_boundary : (if (-δ) ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - (-δ)^2)) else 0) = 0 ∧
                    (if δ ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - δ^2)) else 0) = 0 := by
    constructor
    · simp only [Set.mem_Ioo, lt_self_iff_false, false_and, if_false]
    · simp only [Set.mem_Ioo, lt_self_iff_false, and_false, if_false]

  -- The integral over Ioo equals the interval integral of the extended function
  -- We use the fact that the integrals are equal when the integrands agree on Ioo
  -- and f_extended is 0 at the boundaries

  -- Step 1: Rewrite using the fact that f_extended agrees with exp on Ioo
  have h_eq_on_Ioo : (∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2))) =
      (∫ t in Set.Ioo (-δ) δ, if t ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - t^2)) else 0) := by
    apply setIntegral_congr_fun
    · exact measurableSet_Ioo
    · intro t ht
      exact (h_agree t ht).symm

  rw [h_eq_on_Ioo]

  -- Step 2: Show that integral over Ioo equals interval integral
  -- The key is that f_extended = 0 outside Ioo,
  -- so extending to closed interval doesn't change integral
  -- Also, the boundary points {-δ, δ} have measure zero

  -- The goal is to show the LHS equals the RHS where f_extended is defined in the let binding
  -- We already proved h_eq_on_Ioo showing the LHS equals the integral of the conditional
  -- So we just need to show the integral of the conditional equals
  -- the interval integral of f_extended

  -- First, observe that f_extended is exactly the conditional expression
  change (∫ t in Set.Ioo (-δ) δ, if t ∈ Set.Ioo (-δ) δ
    then Real.exp (-1 / (δ^2 - t^2)) else 0) =
    (∫ t in (-δ)..δ, if t ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - t^2)) else 0)

  -- Now we show this equality using the fact that the integrand is 0 at the boundaries
  -- Convert from Set.Ioo integral to interval integral
  symm
  rw [intervalIntegral.integral_of_le (by linarith [hδ_pos] : -δ ≤ δ)]
  symm
  -- Now we need: ∫ t in Ioc (-δ) δ, ... = ∫ t in Ioo (-δ) δ, ...
  -- This holds because the integrand is 0 at δ and {δ} has measure 0
  have h_Ioc_eq_Ioo : (∫ t in Set.Ioc (-δ) δ,
                        if t ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - t^2)) else 0) =
                      (∫ t in Set.Ioo (-δ) δ,
                        if t ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - t^2)) else 0) := by
          -- Use the fact that Ioc and Ioo differ only by a single point {δ}
          -- and single points have measure zero in ℝ
          -- Since the integrand is 0 at δ, the integrals are equal

          -- We can write Ioc = Ioo ∪ {δ} (disjoint union)
          have h_decomp : Set.Ioc (-δ) δ = Set.Ioo (-δ) δ ∪ {δ} := by
            ext x
            simp only [Set.mem_Ioc, Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff]
            constructor
            · intro ⟨h1, h2⟩
              by_cases hx : x < δ
              · left; exact ⟨h1, hx⟩
              · right; linarith
            · intro h
              rcases h with h | h
              · exact ⟨h.1, le_of_lt h.2⟩
              · rw [h]; exact ⟨by linarith [hδ_pos], le_refl _⟩

          -- The integral over a singleton is 0 since the integrand is 0 at δ
          have h_singleton : (∫ t in ({δ} : Set ℝ),
              if t ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - t^2)) else 0) = 0 := by
            rw [MeasureTheory.integral_singleton]
            simp only [Set.mem_Ioo, lt_self_iff_false, and_false, if_false]
            simp

          -- First show they are disjoint
          have h_disj : Disjoint (Set.Ioo (-δ) δ) {δ} := by
            rw [Set.disjoint_singleton_right]
            intro h
            exact (Set.mem_Ioo.mp h).2.false

          -- Now use that integral over union = sum when disjoint
          rw [h_decomp]
          -- The integral over the union equals sum of integrals (when disjoint and integrable)
          -- setIntegral_union requires: disjoint sets, measurable singleton, and integrability
          rw [setIntegral_union h_disj (measurableSet_singleton δ)]
          rw [h_singleton, add_zero]
          -- The remaining goals are about integrability
          · -- Need integrability of the extended function on Ioo
            -- The function is measurable and bounded on Ioo, hence integrable

            -- First show the function is AEStronglyMeasurable
            have hmeas : AEStronglyMeasurable
                (fun x => if x ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - x^2)) else 0)
                (volume.restrict (Set.Ioo (-δ) δ)) := by
              apply AEStronglyMeasurable.restrict
              apply Measurable.aestronglyMeasurable
              apply Measurable.ite
              · exact measurableSet_Ioo
              · apply Measurable.exp
                apply Measurable.div
                · exact measurable_const
                · apply Measurable.sub
                  · exact measurable_const
                  · exact measurable_id.pow_const _
              · exact measurable_const

            -- Now show boundedness and apply Integrable.of_bound
            have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioo (-δ) δ)),
                ‖if x ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - x^2)) else 0‖ ≤ 1 := by
              apply ae_of_all
              intro x
              by_cases hx : x ∈ Set.Ioo (-δ) δ
              · simp only [hx, if_true, Real.norm_eq_abs]
                rw [abs_of_pos (Real.exp_pos _)]
                -- Show exp(-1/(δ²-x²)) ≤ 1 = exp(0)
                calc Real.exp (-1 / (δ^2 - x^2))
                  ≤ Real.exp 0 := by
                      apply Real.exp_le_exp.mpr
                      -- Need -1/(δ²-x²) ≤ 0
                      have hpos : 0 < δ^2 - x^2 := by
                        have : x^2 < δ^2 := by
                          apply sq_lt_sq'
                          · linarith [hx.1]
                          · linarith [hx.2]
                        linarith
                      have : -1 / (δ^2 - x^2) < 0 := by
                        apply div_neg_of_neg_of_pos
                        · norm_num
                        · exact hpos
                      linarith
                  _ = 1 := by simp
              · simp only [hx, if_false, norm_zero]
                norm_num

            -- Apply bounded integrable theorem
            unfold IntegrableOn
            refine ⟨hmeas, ?_⟩
            have hμfinite : volume (Set.Ioo (-δ) δ) < ∞ := by
              exact measure_Ioo_lt_top
            exact
              MeasureTheory.hasFiniteIntegral_restrict_of_bounded
                (μ := volume) (s := Set.Ioo (-δ) δ) (C := (1 : ℝ)) hμfinite hbound
          · -- Integrability on a singleton (measure zero set)
            -- Any measurable function is integrable on a singleton set
            unfold IntegrableOn
            -- The restriction of the measure to a singleton has measure zero
            have : (volume.restrict {δ}) = 0 := by
              rw [Measure.restrict_singleton]
              simp
            rw [this]
            -- On the zero measure, everything is integrable
            exact integrable_zero_measure
  exact h_Ioc_eq_Ioo.symm

/-- The normalization constant for the mollifier is positive -/
lemma mollifier_normalization_positive (δ : ℝ) (hδ_pos : 0 < δ) :
    0 < ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2)) := by
  -- Z is the integral of exp(-1/(δ²-t²)) over the open interval (-δ, δ)
  -- The integrand exp(-1/(δ²-t²)) is strictly positive for all t ∈ (-δ, δ)
  -- Since we're integrating a positive function over a non-empty interval, Z > 0

  -- Convert Set.Ioo integral to interval integral with extended function
  have h_eq := integral_Ioo_eq_intervalIntegral δ hδ_pos
  rw [h_eq]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · -- The function is interval integrable
    let f_extended : ℝ → ℝ := fun t =>
      if |t| < δ then Real.exp (-1 / (δ^2 - t^2)) else 0
    have h_continuous : ContinuousOn f_extended (Set.uIcc (-δ) δ) :=
      mollifier_extended_continuous δ hδ_pos
    have h_integrable : IntervalIntegrable f_extended volume (-δ) δ :=
      ContinuousOn.intervalIntegrable h_continuous
    apply IntervalIntegrable.congr h_integrable
    apply ae_of_all
    intro x
    unfold f_extended
    have h_equiv : (x ∈ Set.Ioo (-δ) δ) ↔ (|x| < δ) := by
      simp [Set.mem_Ioo, abs_lt]
    by_cases hx : |x| < δ
    · simp only [if_pos hx]
      have hx_mem : x ∈ Set.Ioo (-δ) δ := h_equiv.mpr hx
      symm
      change (if x ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - x^2)) else 0) = _
      simp only [hx_mem, if_true]
    · simp only [if_neg hx]
      have hx_not_mem : x ∉ Set.Ioo (-δ) δ := by
        intro hmem
        exact hx (h_equiv.mp hmem)
      symm
      change (if x ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - x^2)) else 0) = _
      simp only [hx_not_mem, if_false]
  · -- The function is positive on the open interval
    intro x hx_in
    have hx_in_Ioo : x ∈ Set.Ioo (-δ) δ := by
      rw [Set.mem_Ioo]
      simp only at hx_in
      exact ⟨hx_in.1, hx_in.2⟩
    change (if x ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - x^2)) else 0) > 0
    simp only [hx_in_Ioo, if_true]
    exact Real.exp_pos _
  · linarith

/-- The mollifier function is smooth at both boundary points -/
lemma mollifier_smooth_at_boundary : ∀ (δ : ℝ) (_ : 0 < δ),
    let Z := ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2))
    let φ := fun y => if |y| < δ then Real.exp (-1 / (δ^2 - y^2)) / Z else 0
    ContDiffAt ℝ (⊤ : ℕ∞) φ δ ∧ ContDiffAt ℝ (⊤ : ℕ∞) φ (-δ) := by
  intro δ hδ_pos
  -- The function is 0 on [δ, ∞) and exp(-1/(δ²-y²))/Z on (-∞, δ)
  -- At y = δ, we need to show smoothness

  -- Strategy: Show the function and all derivatives approach 0 as y → δ⁻
  -- This uses the fact that exp(-1/t) and all its derivatives vanish as t → 0⁺

  -- Let's denote the normalization constant
  -- We define the integrand to be 0 at the boundary to avoid division by zero
  let mollifier_kernel := fun (δ : ℝ) (t : ℝ) =>
    if |t| < δ then Real.exp (-1 / (δ^2 - t^2)) else 0
  let Z := ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2))

  -- The function can be written as a piecewise function
  let f := fun y => if |y| < δ then Real.exp (-1 / (δ^2 - y^2)) / Z else 0

  -- From the right (y > δ), the function is constantly 0, which is smooth
  have h_right : ∀ᶠ y in 𝓝[>] δ, f y = 0 := by
    filter_upwards [self_mem_nhdsWithin]
    intro y hy
    simp only [f]
    -- Since y > δ > 0, we have |y| ≥ δ
    have h_not : ¬(|y| < δ) := by
      push_neg
      have hy_pos : 0 < y := by
        calc 0 < δ := hδ_pos
             _ < y := hy
      calc |y| = y := abs_of_pos hy_pos
           _ ≥ δ := le_of_lt hy
    simp [h_not]

  -- From the left (y < δ), we need to show that the function extends smoothly to 0
  -- This requires showing that lim_{y→δ⁻} exp(-1/(δ²-y²)) = 0
  -- and all derivatives also vanish

  -- Key observation: As y → δ⁻, we have δ² - y² → 0⁺
  -- So we need to analyze exp(-1/t) as t → 0⁺

  -- First, show the function value at δ is 0 (by definition)
  have h_at_δ : f δ = 0 := by
    simp only [f]
    have h_not_lt : ¬(|δ| < δ) := by
      simp [abs_of_pos hδ_pos]
    simp [h_not_lt]

  -- To prove smoothness, we use that the function is 0 on a right neighborhood
  -- and approaches 0 with all derivatives from the left

  -- The critical fact is that for the function g(t) = exp(-1/t) for t > 0,
  -- we have lim_{t→0⁺} t^n · g^(k)(t) = 0 for all n, k ∈ ℕ
  -- This implies our function extends smoothly to 0 at the boundary

  -- We need to prove ContDiffAt ℝ (⊤ : ℕ∞) f δ
  -- Since f agrees with the original function, it suffices to show ContDiffAt for f

  -- Use that f is 0 on a right neighborhood and smooth from the left
  have h_eventually_eq : f =ᶠ[𝓝 δ] (fun y => if |y| < δ
      then Real.exp (-1 / (δ^2 - y^2)) / Z else 0) := by
    filter_upwards
    intro y
    rfl

  -- We'll prove smoothness at both boundary points using expNegInvGlue
  -- Define an auxiliary function using expNegInvGlue that handles the boundary smoothly
  let g := fun y => expNegInvGlue (δ^2 - y^2) / Z

  -- Show that f agrees with g in a neighborhood of the boundary points
  have h_agree : ∀ y, |y| < δ → f y = g y := by
    intro y hy
    simp only [f, g]
    simp [hy]
    -- When |y| < δ, we have δ² - y² > 0
    have h_pos : 0 < δ^2 - y^2 := by
      rw [sub_pos, ← sq_abs]
      have h_bound : -δ < |y| := by
        have : 0 ≤ |y| := abs_nonneg _
        linarith [hδ_pos]
      exact sq_lt_sq' h_bound hy
    -- expNegInvGlue on positive values gives exp(-1/x)
    rw [expNegInvGlue, if_neg (not_le.mpr h_pos)]
    congr 1
    field_simp

  -- Show g extends to 0 at boundaries
  have h_g_boundary_pos : g δ = 0 := by
    simp only [g]
    -- At y = δ, we have δ² - δ² = 0
    simp [expNegInvGlue.zero]

  have h_g_boundary_neg : g (-δ) = 0 := by
    simp only [g]
    -- At y = -δ, we have δ² - (-δ)² = δ² - δ² = 0
    have : (-δ)^2 = δ^2 := by ring
    simp [this, expNegInvGlue.zero]

  -- g is smooth everywhere as composition of smooth functions
  have h_g_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    simp only [g]
    -- Composition of smooth functions: y ↦ δ² - y² and expNegInvGlue
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => δ^2 - y^2) :=
      contDiff_const.sub (contDiff_id.pow 2)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (expNegInvGlue ∘ (fun y => δ^2 - y^2)) := by
      apply ContDiff.comp
      · exact @expNegInvGlue.contDiff (⊤ : ℕ∞)
      · exact h1
    exact h2.div_const Z

  constructor
  · -- Smoothness at δ
    -- Show f equals g near δ and use g's smoothness
    have h_eq_near_δ : ∀ᶠ y in 𝓝 δ, f y = g y := by
      apply Metric.eventually_nhds_iff.mpr
      use δ/2, by linarith
      intro y hy
      rw [Real.dist_eq] at hy
      by_cases h : |y| < δ
      · -- Case |y| < δ: use h_agree
        exact h_agree y h
      · -- Case |y| ≥ δ: both are 0
        simp only [f]
        simp [h]
        -- Show g y = 0 when |y| ≥ δ
        simp only [g]
        -- We need δ² - y² ≤ 0
        have : δ^2 - y^2 ≤ 0 := by
          rw [sub_nonpos]
          push_neg at h
          -- |y| ≥ δ implies y² ≥ δ²
          calc δ^2 ≤ |y|^2 := sq_le_sq' (by linarith) h
               _ = y^2 := sq_abs y
        rw [expNegInvGlue.zero_of_nonpos this]
        simp
    exact h_g_smooth.contDiffAt.congr_of_eventuallyEq h_eq_near_δ

  · -- Smoothness at -δ
    -- Similar argument for -δ
    have h_eq_near_neg_δ : ∀ᶠ y in 𝓝 (-δ), f y = g y := by
      apply Metric.eventually_nhds_iff.mpr
      use δ/2, by linarith
      intro y hy
      rw [Real.dist_eq] at hy
      by_cases h : |y| < δ
      · -- Case |y| < δ: use h_agree
        exact h_agree y h
      · -- Case |y| ≥ δ: both are 0
        simp only [f]
        simp [h]
        -- Show g y = 0 when |y| ≥ δ
        simp only [g]
        -- We need δ² - y² ≤ 0
        have : δ^2 - y^2 ≤ 0 := by
          rw [sub_nonpos]
          push_neg at h
          -- |y| ≥ δ implies y² ≥ δ²
          calc δ^2 ≤ |y|^2 := sq_le_sq' (by linarith) h
               _ = y^2 := sq_abs y
        rw [expNegInvGlue.zero_of_nonpos this]
        simp
    exact h_g_smooth.contDiffAt.congr_of_eventuallyEq h_eq_near_neg_δ

/-- Measurability of truncated shifted simple function using toSimpleFunc -/
lemma truncated_shifted_measurable {σ : ℝ} {n : ℕ} (x : ℝ)
    (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ)) :
    AEStronglyMeasurable (fun y => if (1:ℝ)/n < x - y ∧ x - y < n then
      Lp.simpleFunc.toSimpleFunc s (x - y) else 0) volume := by
  -- Rewrite as an indicator function
  have h_eq : (fun y => if (1:ℝ)/n < x - y ∧ x - y < n
      then Lp.simpleFunc.toSimpleFunc s (x - y) else 0) =
        Set.indicator {y | (1:ℝ)/n < x - y ∧ x - y < n}
        (fun y => Lp.simpleFunc.toSimpleFunc s (x - y)) := by
    ext y
    unfold Set.indicator
    simp only [Set.mem_setOf]
  rw [h_eq]
  apply AEStronglyMeasurable.indicator
  · -- toSimpleFunc s is a simple function, so it's measurable everywhere
    -- The underlying simple function is measurable
    have h_s_meas : Measurable (Lp.simpleFunc.toSimpleFunc s : ℝ → ℂ) :=
      Lp.simpleFunc.measurable s
    -- Composition with (x - ·) preserves measurability
    have h_comp_meas : Measurable (fun y => Lp.simpleFunc.toSimpleFunc s (x - y)) :=
      Measurable.comp h_s_meas (measurable_const.sub measurable_id)
    -- Since toSimpleFunc s is measurable, it's also ae strongly measurable w.r.t. volume
    exact h_comp_meas.aestronglyMeasurable
  · -- The set {y | 1/n < x - y ∧ x - y < n} is measurable
    have h_set : {y | (1:ℝ)/n < x - y ∧ x - y < n} = {y | x - n < y ∧ y < x - (1:ℝ)/n} := by
      ext y
      simp only [Set.mem_setOf]
      constructor
      · intro ⟨h1, h2⟩
        constructor
        · linarith
        · linarith
      · intro ⟨h1, h2⟩
        constructor
        · linarith
        · linarith
    rw [h_set]
    simp only [Set.setOf_and]
    apply MeasurableSet.inter
    · exact measurableSet_Ioi
    · exact measurableSet_Iio

/-- Convolution of a smooth function with compact support
  and an integrable function is smooth -/
lemma convolution_smooth_of_smooth_compsupp_and_integrable
    {φ : ℝ → ℂ} {f : ℝ → ℂ}
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hf_integrable : ∀ x : ℝ, Integrable (fun y => f (x - y)) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y, φ y * f (x - y)) := by
  classical
  have hf_neg : Integrable (fun y : ℝ => f (-y)) volume := by
    simpa using hf_integrable 0
  have hf_aesm' : AEStronglyMeasurable ((fun y : ℝ => f y) ∘ fun y => -y) volume := by
    simpa [Function.comp] using hf_neg.aestronglyMeasurable
  have hf_aesm : AEStronglyMeasurable (fun y : ℝ => f y) volume := by
    simpa [Function.comp] using
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).aestronglyMeasurable_comp_iff
        measurableEmbedding_neg).1 hf_aesm'
  have hf_comp : Integrable ((fun y : ℝ => f y) ∘ fun y => -y) volume := by
    simpa [Function.comp] using hf_neg
  have hf : Integrable f volume := by
    have hf_int_iff :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp hf_aesm
    exact (hf_int_iff).1 hf_comp
  have hf_loc : LocallyIntegrable f volume := hf.locallyIntegrable
  have hconv :
      ContDiff ℝ (⊤ : ℕ∞)
        (MeasureTheory.convolution φ f (ContinuousLinearMap.mul ℝ ℂ) volume) := by
    simpa using
      (hφ_supp.contDiff_convolution_left
        (L := ContinuousLinearMap.mul ℝ ℂ)
        (μ := volume)
        (n := (⊤ : ℕ∞)) hφ_smooth hf_loc)
  simpa [MeasureTheory.convolution, ContinuousLinearMap.mul_apply'] using hconv

/-- Convolution of smooth mollifier with truncated simple function is smooth -/
lemma smooth_mollifier_convolution_truncated
    {δ : ℝ} {n : ℕ} {σ : ℝ}
    (φ_δ : ℝ → ℝ) (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ_δ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (hδ_pos : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y, (φ_δ y : ℂ) *
      (if 1/n < x - y ∧ x - y < n then Lp.simpleFunc.toSimpleFunc s (x - y) else 0)) := by
  -- Define the truncated simple function explicitly
  let truncate : ℝ → ℂ := fun x =>
    if 1/n < x ∧ x < n then Lp.simpleFunc.toSimpleFunc s x else 0

  -- The convolution of a smooth compactly supported mollifier with a truncated simple function
  -- is smooth. This follows from the general theory of convolutions in Mathlib.
  -- Key ideas:
  -- 1. φ_δ has compact support [-δ, δ] and is smooth
  -- 2. truncate has compact support (1/n, n) and is bounded (since s is a simple function)
  -- 3. The convolution inherits smoothness from the mollifier

  -- Step 1: Show that truncate is measurable
  have h_truncate_meas : Measurable truncate := by
    simp only [truncate]
    apply Measurable.ite
    · apply MeasurableSet.inter
      · exact measurableSet_Ioi
      · exact measurableSet_Iio
    · exact Lp.simpleFunc.measurable s
    · exact measurable_const

  -- Step 2: Show that truncate is bounded
  have h_truncate_bounded : ∃ M : ℝ, ∀ x, ‖truncate x‖ ≤ M := by
    -- Simple functions are bounded
    obtain ⟨M_s, hM_s⟩ : ∃ M, ∀ x, ‖Lp.simpleFunc.toSimpleFunc s x‖ ≤ M := by
      -- Simple functions have finite range, hence are bounded
      -- The range is already a Finset
      let range_finset := (Lp.simpleFunc.toSimpleFunc s).range

      -- If the range is empty, the function is the zero function
      by_cases h_empty : range_finset = ∅
      · -- Empty range case: function is zero everywhere
        use 0
        intro x
        have : Lp.simpleFunc.toSimpleFunc s x = 0 := by
          have : Lp.simpleFunc.toSimpleFunc s x ∈ range_finset :=
            SimpleFunc.mem_range_self _ x
          rw [h_empty] at this
          exact absurd this (Finset.notMem_empty _)
        rw [this, norm_zero]

      · -- Non-empty finite range case
        -- The range is nonempty
        have h_nonempty : range_finset.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr h_empty

        -- Use the maximum norm value in the range
        let M := range_finset.sup' h_nonempty (fun z => ‖z‖₊)

        use M
        intro x
        have hx_mem : Lp.simpleFunc.toSimpleFunc s x ∈ range_finset :=
          SimpleFunc.mem_range_self _ x

        -- The norm is bounded by the supremum
        calc ‖Lp.simpleFunc.toSimpleFunc s x‖
          = ‖Lp.simpleFunc.toSimpleFunc s x‖₊ := by simp only [coe_nnnorm]
          _ ≤ M := Finset.le_sup' (fun z => ‖z‖₊) hx_mem
    use max M_s 1
    intro x
    simp only [truncate]
    by_cases h : 1/n < x ∧ x < n
    · simp only [h]
      exact le_trans (hM_s x) (le_max_left M_s 1)
    · simp only [h, if_false, norm_zero]
      exact zero_le_one.trans (le_max_right M_s 1)

  -- Step 3: Show that truncate has support in (1/n, n)
  have h_truncate_supp : ∀ x, x ∉ Set.Ioo (1/n : ℝ) n → truncate x = 0 := by
    intro x hx
    simp only [truncate, Set.mem_Ioo] at hx ⊢
    rw [if_neg hx]

  -- Step 4: Show that truncate is locally integrable
  have h_truncate_integrable : ∀ x : ℝ, Integrable (fun y => truncate (x - y)) volume := by
    intro x
    -- truncate has compact support and is bounded, making it integrable

    -- The function y ↦ truncate(x - y) is nonzero only when 1/n < x - y < n
    -- This is equivalent to x - n < y < x - 1/n
    -- So the support is contained in [x - n, x - 1/n] which has finite measure

    -- Show the shifted function is measurable
    have h_meas : Measurable (fun y => truncate (x - y)) := by
      exact Measurable.comp h_truncate_meas (measurable_const.sub measurable_id)

    -- Show the support has finite measure
    have h_support_finite : volume {y : ℝ | truncate (x - y) ≠ 0} < ⊤ := by
      have h_subset : {y : ℝ | truncate (x - y) ≠ 0} ⊆ Set.Ioo (x - n) (x - 1/n) := by
        intro y hy
        simp at hy
        by_contra h_not_in
        have : x - y ∉ Set.Ioo (1/n : ℝ) n := by
          simp only [Set.mem_Ioo] at h_not_in ⊢
          intro ⟨h1, h2⟩
          apply h_not_in
          constructor
          · linarith
          · linarith
        exact hy (h_truncate_supp _ this)
      exact (measure_mono h_subset).trans_lt measure_Ioo_lt_top

    -- Apply integrability for bounded functions on finite measure support
    obtain ⟨M, hM⟩ := h_truncate_bounded

    -- We use the fact that a bounded measurable function with finite measure support is integrable
    -- The function y ↦ truncate (x - y) is bounded by M and supported on Set.Ioo (x - n) (x - 1/n)

    -- Show the function is in L¹ by showing it's in L² (since L² ⊆ L¹ on finite measure sets)
    -- First, we'll use that the function is bounded and has finite measure support
    have h_finite_integral : HasFiniteIntegral (fun y => truncate (x - y)) volume := by
      -- The integral of |f|^p is finite when f is bounded and has finite measure support
      rw [hasFiniteIntegral_iff_norm]

      -- We have ∫ ‖truncate (x - y)‖ ≤ M * volume(support)
      have h_bound_integral : ∫⁻ y, ‖truncate (x - y)‖₊ ∂volume ≤ M.toNNReal *
          volume (Set.Ioo (x - n) (x - 1/n)) := by
        -- We'll use that the function is bounded by M on its support
        -- First show that the integral is over the support only
        have h_eq : ∫⁻ y, ‖truncate (x - y)‖₊ ∂volume =
                    ∫⁻ y in Set.Ioo (x - n) (x - 1/n), ‖truncate (x - y)‖₊ ∂volume := by
          -- The function is zero outside Set.Ioo (x - n) (x - 1/n)
          have h_indicator : (fun y => (‖truncate (x - y)‖₊ : ℝ≥0∞)) =
              (Set.Ioo (x - n) (x - 1/n)).indicator (fun y => (‖truncate (x - y)‖₊ : ℝ≥0∞)) := by
            ext y
            by_cases hy : y ∈ Set.Ioo (x - n) (x - 1/n)
            · rw [Set.indicator_of_mem hy]
            · have : x - y ∉ Set.Ioo (1/n : ℝ) n := by
                simp only [Set.mem_Ioo] at hy ⊢
                intro ⟨h1, h2⟩
                apply hy
                constructor
                · linarith
                · linarith
              rw [h_truncate_supp _ this, Set.indicator_of_notMem hy]
              simp
          conv_lhs => rw [h_indicator]
          rw [lintegral_indicator]
          exact measurableSet_Ioo
        rw [h_eq]
        -- Now bound the integral
        calc ∫⁻ y in Set.Ioo (x - n) (x - 1/n), ‖truncate (x - y)‖₊ ∂volume
            ≤ ∫⁻ y in Set.Ioo (x - n) (x - 1/n), M.toNNReal ∂volume := by
              apply lintegral_mono
              intro y
              -- We need (‖truncate (x - y)‖₊ : ℝ≥0∞) ≤ (M.toNNReal : ℝ≥0∞)
              -- Since ‖truncate (x - y)‖ ≤ M, this follows from monotonicity
              have : (‖truncate (x - y)‖₊ : ℝ≥0∞) ≤ (M.toNNReal : ℝ≥0∞) := by
                apply ENNReal.coe_le_coe.mpr
                -- The nnnorm is bounded by M
                -- nnnorm is definitionally equal to Real.toNNReal of norm
                rw [← norm_toNNReal]
                exact Real.toNNReal_le_toNNReal (hM (x - y))
              exact this
            _ = M.toNNReal * volume (Set.Ioo (x - n) (x - 1/n)) := by
              simp [lintegral_const]

      -- The right side is finite
      have h_finite_rhs : M.toNNReal * volume (Set.Ioo (x - n) (x - 1/n)) < ⊤ := by
        rw [ENNReal.mul_lt_top_iff]
        left
        constructor
        · exact ENNReal.coe_lt_top
        · -- The interval has finite Lebesgue measure
          exact measure_Ioo_lt_top

      -- Convert between ENNReal.ofReal and ENNReal.coe of nnnorm
      have h_eq_integral : ∫⁻ a, ENNReal.ofReal ‖truncate (x - a)‖ ∂volume =
                          ∫⁻ y, ↑‖truncate (x - y)‖₊ ∂volume := by
        congr
        ext y
        -- ENNReal.ofReal ‖f‖ = ↑‖f‖₊
        rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
        rfl
      -- Use the equality to rewrite the goal
      calc ∫⁻ a, ENNReal.ofReal ‖truncate (x - a)‖ ∂volume
          = ∫⁻ y, ↑‖truncate (x - y)‖₊ ∂volume := h_eq_integral
          _ ≤ M.toNNReal * volume (Set.Ioo (x - n) (x - 1/n)) := h_bound_integral
          _ < ⊤ := h_finite_rhs

    -- Now apply the integrability criterion
    exact ⟨h_meas.aestronglyMeasurable, h_finite_integral⟩

  -- Step 2: Show that φ_δ (viewed as complex) is smooth and has compact support
  have hφ_complex_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => (φ_δ y : ℂ)) := by
    -- Casting from real to complex preserves smoothness
    -- The map x ↦ (x : ℂ) is the same as Complex.ofReal which is a continuous linear map
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) := by
      -- Complex.ofReal is a continuous linear map, so it's smooth
      change ContDiff ℝ (⊤ : ℕ∞) (⇑Complex.ofRealLI)
      exact Complex.ofRealLI.contDiff
    -- Now compose with φ_δ
    exact ContDiff.comp h1 hφ_smooth

  have hφ_complex_supp : HasCompactSupport (fun y => (φ_δ y : ℂ)) := by
    -- φ_δ has support in [-δ, δ] which is compact
    -- Since φ_δ is zero outside [-δ, δ], the complex version has the same property
    rw [HasCompactSupport]
    -- tsupport f = closure (support f), so we need to show closure of support is compact
    have h_supp : Function.support (fun y => (φ_δ y : ℂ)) = Function.support φ_δ := by
      ext y
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]

    -- The support is contained in [-δ, δ]
    have h_subset : Function.support φ_δ ⊆ Set.Icc (-δ) δ := by
      intro y hy
      simp only [Function.mem_support] at hy
      by_contra h_not_in
      simp only [Set.mem_Icc, not_and_or, not_le] at h_not_in
      obtain h | h := h_not_in
      · -- y < -δ, so |y| > δ
        have : |y| > δ := by
          rw [abs_of_neg (lt_trans h (neg_lt_zero.mpr hδ_pos))]
          linarith
        exact hy (hφ_supp y this)
      · -- y > δ, so |y| > δ
        have : |y| > δ := by
          rw [abs_of_pos (hδ_pos.trans h)]
          exact h
        exact hy (hφ_supp y this)

    -- tsupport = closure of support
    simp only [tsupport]
    rw [h_supp]
    exact IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
      (closure_minimal h_subset isClosed_Icc)

  -- Step 3: Apply the convolution smoothness theorem
  -- The convolution of a smooth function with compact support with any locally integrable function
  -- is smooth when the smooth function acts as the kernel

  -- The convolution is smooth because φ is smooth with compact support
  -- and truncate is locally integrable (in fact, globally integrable)
  exact convolution_smooth_of_smooth_compsupp_and_integrable
    hφ_complex_smooth hφ_complex_supp h_truncate_integrable

/-- Convolution of mollifier with truncated function has compact support -/
lemma convolution_mollifier_truncated_has_compact_support
    {δ : ℝ} {n : ℕ}
    (φ_δ : ℝ → ℝ) (truncate : ℝ → ℂ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (hδ_pos : 0 < δ)
    (hn_pos : 0 < n)
    (h_truncate_supp : ∀ x, x ∉ Set.Ioo (1 / n : ℝ) n → truncate x = 0) :
    ∃ R > 0, ∀ x ≥ R, (∫ y, (φ_δ y : ℂ) * truncate (x - y)) = 0 := by
  -- The support of convolution is contained in the Minkowski sum of the supports
  -- φ_δ has support in [-δ, δ] and truncate has support in [1/n, n]
  -- So the convolution has support in [1/n - δ, n + δ]
  use n + δ + 1
  constructor
  · have : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    linarith [hδ_pos, this]
  · intro x hx
    -- When x ≥ n + δ + 1, the convolution integral is 0
    -- We need to show ∫ y, (φ_δ y : ℂ) * truncate (x - y) = 0
    -- This happens because the supports of φ_δ(y) and truncate(x-y) don't overlap

    -- The integral equals 0 because the integrand is 0 almost everywhere
    rw [integral_eq_zero_of_ae]
    -- Show that (φ_δ y : ℂ) * truncate (x - y) = 0 for almost all y
    filter_upwards with y

    -- We need to show either φ_δ y = 0 or truncate (x - y) = 0
    -- Case analysis on whether |y| > δ
    by_cases h : |y| > δ
    · -- If |y| > δ, then φ_δ y = 0
      rw [hφ_supp y h]
      simp
    · -- If |y| ≤ δ, we show truncate (x - y) = 0
      push_neg at h
      -- We have |y| ≤ δ, so y ∈ [-δ, δ]
      -- And x ≥ n + δ + 1, so x - y ≥ n + δ + 1 - δ = n + 1
      -- Since truncate has support in (1/n, n), and x - y > n, we get truncate (x - y) = 0

      have h_bound : x - y ≥ n + 1 := by
        have : y ≤ δ := by
          rw [abs_le] at h
          exact h.2
        linarith [hx, this]

      have h_not_in_supp : x - y ∉ Set.Ioo (1 / n : ℝ) n := by
        simp only [Set.mem_Ioo, not_and_or, not_lt]
        right
        -- Show x - y ≥ n, which contradicts x - y < n
        have : (n : ℝ) < x - y := by
          have : (n : ℝ) + 1 ≤ x - y := by
            exact_mod_cast h_bound
          linarith
        exact le_of_lt this

      rw [h_truncate_supp (x - y) h_not_in_supp]
      simp

/-- Convolution of mollifier with truncated function vanishes outside support -/
lemma convolution_mollifier_truncated_zero_outside_support
    {δ : ℝ} {n : ℕ}
    (φ_δ : ℝ → ℝ) (truncate : ℝ → ℂ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (h_truncate_supp : ∀ x, x ∉ Set.Ioo (1 / n : ℝ) n → truncate x = 0) :
    ∀ x < (1/n : ℝ) - δ, (∫ y, (φ_δ y : ℂ) * truncate (x - y)) = 0 := by
  intro x hx
  classical
  have hxδ : x + δ < (1 / n : ℝ) := by
    have := add_lt_add_right hx δ
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hxδ_le : x + δ ≤ (1 / n : ℝ) := hxδ.le
  have h_zero :
      (fun y : ℝ => (φ_δ y : ℂ) * truncate (x - y)) = fun _ => (0 : ℂ) := by
    funext y
    by_cases h_abs : |y| > δ
    · have hφ : φ_δ y = 0 := hφ_supp y h_abs
      simp [hφ]
    · have habs_le : |y| ≤ δ := le_of_not_gt h_abs
      have h₁ : x - y ≤ x + |y| := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          add_le_add_left (neg_le_abs y) x
      have h₂ : x + |y| ≤ x + δ := add_le_add_left habs_le x
      have h_le : x - y ≤ (1 / n : ℝ) := h₁.trans <| h₂.trans hxδ_le
      have h_not_mem : x - y ∉ Set.Ioo (1 / n : ℝ) n := by
        intro hy_mem
        exact not_lt_of_ge h_le hy_mem.1
      have htr : truncate (x - y) = 0 := h_truncate_supp (x - y) h_not_mem
      simp [htr]
  simp [h_zero]

/-- Smooth convolution with compact support is measurable -/
lemma smooth_convolution_measurable
    {σ : ℝ}
    (smooth_func : ℝ → ℂ)
    (h_smooth : ContDiff ℝ (⊤ : ℕ∞) smooth_func) :
    AEStronglyMeasurable smooth_func (weightedMeasure σ) := by
  refine (h_smooth.continuous.measurable).aestronglyMeasurable

/-- The convolution of a mollifier with a truncated function vanishes on (-∞, 0]
    when δ is sufficiently small -/
lemma convolution_vanishes_on_nonpositive
    {δ : ℝ} {n : ℕ}
    (φ_δ : ℝ → ℝ) (truncate : ℝ → ℂ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (hδ_small : δ ≤ 1 / n) -- Critical condition: δ must be at most 1/n
    (h_truncate_supp : ∀ x, x ∉ Set.Ioo (1 / n : ℝ) n → truncate x = 0) :
    ∀ x ≤ 0, (∫ y, (φ_δ y : ℂ) * truncate (x - y)) = 0 := by
  intro x hx
  -- With δ ≤ 1/n and x ≤ 0, we can show the integrand is always 0
  -- For any y with |y| ≤ δ, we have y ∈ [-δ, δ] ⊆ [-1/n, 1/n]
  -- Thus x - y ≤ 0 - (-1/n) = 1/n, so x - y ∉ (1/n, n)
  rw [integral_eq_zero_of_ae]
  filter_upwards with y
  by_cases hy : |y| > δ
  · -- If |y| > δ, then φ_δ y = 0
    rw [hφ_supp y hy]
    simp
  · -- If |y| ≤ δ ≤ 1/n, then x - y ≤ 0 + 1/n = 1/n
    push_neg at hy
    have h_bound : x - y ≤ 1 / n := by
      have y_bound : -δ ≤ y := by
        rw [abs_le] at hy
        exact hy.1
      calc x - y
        ≤ 0 - (-δ) := by linarith [hx, y_bound]
        _ = δ := by ring
        _ ≤ 1 / n := hδ_small

    -- Since x - y ≤ 1/n, we have x - y ∉ (1/n, n)
    have h_not_in : x - y ∉ Set.Ioo (1/n : ℝ) n := by
      simp only [Set.mem_Ioo, not_and_or, not_lt]
      left
      exact h_bound

    rw [h_truncate_supp (x - y) h_not_in]
    simp

/-- Smooth function with compact support away from 0 is in L² -/
lemma smooth_compact_support_memLp
    {σ : ℝ}
    (smooth_func : ℝ → ℂ)
    (h_smooth : ContDiff ℝ (⊤ : ℕ∞) smooth_func)
    (h_support : ∃ R > 0, ∀ x ≥ R, smooth_func x = 0)
    (h_support_left : ∀ x ≤ 0, smooth_func x = 0)
    (h_support_away_zero : ∃ a > 0, ∀ x ∈ Set.Ioo 0 a, smooth_func x = 0) :
    MemLp smooth_func 2 (weightedMeasure σ) := by
  classical
  obtain ⟨R, hR_pos, hR_support⟩ := h_support
  obtain ⟨a, ha_pos, ha_support⟩ := h_support_away_zero
  set R' := max R a
  have hR'_pos : 0 < R' := lt_of_lt_of_le hR_pos (le_max_left _ _)
  have ha_le_R' : a ≤ R' := le_max_right _ _
  have h_zero_outside : ∀ x, x ∉ Set.Icc a R' → smooth_func x = 0 := by
    intro x hx
    have hx' : x < a ∨ R' < x := by
      have hx'' : ¬ (a ≤ x ∧ x ≤ R') := by simpa [Set.mem_Icc] using hx
      by_cases hxa : a ≤ x
      · have hxle : ¬ x ≤ R' := by
          intro hxle
          exact hx'' ⟨hxa, hxle⟩
        exact Or.inr (lt_of_not_ge hxle)
      · exact Or.inl (lt_of_not_ge hxa)
    cases hx' with
    | inl hx_lt_a =>
        by_cases hx_nonpos : x ≤ 0
        · exact h_support_left x hx_nonpos
        · have hx_pos : 0 < x := lt_of_not_ge hx_nonpos
          have hx_mem : x ∈ Set.Ioo 0 a := ⟨hx_pos, hx_lt_a⟩
          exact ha_support x hx_mem
    | inr hx_gt_R' =>
        have hx_ge_R : R ≤ x := by
          have hx_gt_R : R < x := lt_of_le_of_lt (le_max_left _ _) hx_gt_R'
          exact le_of_lt hx_gt_R
        exact hR_support x hx_ge_R
  have h_support_subset : Function.support smooth_func ⊆ Set.Icc a R' := by
    intro x hx
    by_contra hx_not
    exact hx (h_zero_outside x hx_not)
  have h_cont : Continuous smooth_func := h_smooth.continuous
  have h_meas : AEStronglyMeasurable smooth_func (weightedMeasure σ) :=
    h_cont.aestronglyMeasurable
  have h_compact : IsCompact (Set.Icc a R') := isCompact_Icc
  have h_cont_on : ContinuousOn smooth_func (Set.Icc a R') := h_cont.continuousOn
  obtain ⟨C, hC⟩ := h_compact.exists_bound_of_continuousOn h_cont_on
  set M := max C 0 with hM_def
  have hM_nonneg : 0 ≤ M := by simp [hM_def]
  have hM_bound : ∀ x ∈ Set.Icc a R', ‖smooth_func x‖ ≤ M := by
    intro x hx
    have := hC x hx
    exact this.trans (le_max_left _ _)
  classical
  set K := Set.Icc a R'
  let μ := weightedMeasure σ
  have hK_meas : MeasurableSet K := measurableSet_Icc
  have h_zero_outside' : ∀ x ∉ K, smooth_func x = 0 := h_zero_outside
  have h_measurable_support : Function.support smooth_func ⊆ K := fun x hx ↦ by
    by_contra hxK
    exact hx (h_zero_outside' x hxK)
  have ha_half_pos : 0 < a / 2 := half_pos ha_pos
  have h_upper_bounds : a / 2 < R' + 1 := by
    have ha_half_le_a : a / 2 ≤ a := half_le_self (le_of_lt ha_pos)
    have hR'_lt : R' < R' + 1 := by linarith
    exact lt_of_le_of_lt (le_trans ha_half_le_a ha_le_R') hR'_lt
  have h_measure_subset : K ⊆ Set.Ioo (a / 2) (R' + 1) := by
    intro x hx
    have hx_ge : a ≤ x := hx.1
    have hx_le : x ≤ R' := hx.2
    have hx_pos : a / 2 < x := (half_lt_self ha_pos).trans_le hx_ge
    have hx_lt : x < R' + 1 := lt_of_le_of_lt hx_le (by linarith)
    exact ⟨hx_pos, hx_lt⟩
  have h_measure_lt_top : μ K < ∞ := by
    have h_finite := weightedMeasure_finite_on_bounded σ (a / 2) (R' + 1)
      ha_half_pos h_upper_bounds
    exact (measure_mono h_measure_subset).trans_lt h_finite
  -- Majorant function supported on K
  let g : ℝ → ℂ := fun x => K.indicator (fun _ => (M : ℂ)) x
  have hg_mem : MemLp g 2 μ := by
    have hμK_ne_top : μ K ≠ ∞ := (ne_of_lt h_measure_lt_top)
    refine memLp_indicator_const (p := (2 : ℝ≥0∞)) hK_meas (M : ℂ) ?_
    exact Or.inr hμK_ne_top
  have h_pointwise :
      ∀ᵐ x ∂μ, ‖smooth_func x‖ ≤ ‖g x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    classical
    by_cases hx : x ∈ K
    · have hx_le : ‖smooth_func x‖ ≤ M := hM_bound x hx
      have h_norm_g : ‖g x‖ = M := by
        simp [g, Set.indicator_of_mem, hx, abs_of_nonneg hM_nonneg]
      simpa [h_norm_g]
    · have hx_zero : smooth_func x = 0 := h_zero_outside' x hx
      have h_g_zero : g x = 0 := by simp [g, Set.indicator_of_notMem, hx]
      simp [hx_zero, h_g_zero]
  exact (MemLp.of_le (hg := hg_mem) h_meas h_pointwise)

/-- Smooth functions that are convolutions of mollifiers
  with truncated simple functions are in L² -/
lemma smooth_mollifier_convolution_memLp
    {σ : ℝ} {δ : ℝ} {n : ℕ}
    (φ_δ : ℝ → ℝ) (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ_δ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (hδ_pos : 0 < δ)
    (hn_pos : 0 < n)
    (hδ_bound : δ < 1 / n) :
    MemLp (fun x => ∫ y, (φ_δ y : ℂ) *
      (if 1/n < x - y ∧ x - y < n then Lp.simpleFunc.toSimpleFunc s (x - y) else 0))
      2 (weightedMeasure σ) := by
  -- The convolution of a mollifier with compact support and a truncated simple function
  -- is smooth with compact support, hence in L²
  let smooth_func := fun x => ∫ y, (φ_δ y : ℂ) *
    (if 1/n < x - y ∧ x - y < n then Lp.simpleFunc.toSimpleFunc s (x - y) else 0)

  -- Show that smooth_func has compact support
  have h_support : ∃ R > 0, ∀ x ≥ R, smooth_func x = 0 := by
    -- Define truncate function
    let truncate : ℝ → ℂ := fun z =>
      if 1/n < z ∧ z < n then Lp.simpleFunc.toSimpleFunc s z else 0
    -- Use the lemma for compact support
    obtain ⟨R, hR_pos, hR⟩ := convolution_mollifier_truncated_has_compact_support
      φ_δ truncate hφ_supp hδ_pos hn_pos (fun z hz => by
        simp only [truncate, Set.mem_Ioo] at hz ⊢
        rw [if_neg]
        exact hz)
    exact ⟨R, hR_pos, fun x hx => by
      simp only [smooth_func]
      exact hR x hx⟩

  -- Show that smooth_func vanishes on (-∞, 0]
  have h_support_left : ∀ x ≤ 0, smooth_func x = 0 := by
    intro x hx
    simp only [smooth_func]
    -- Define truncate function for the lemma
    let truncate : ℝ → ℂ := fun z =>
      if 1/n < z ∧ z < n then Lp.simpleFunc.toSimpleFunc s z else 0
    -- Apply the lemma with the correct arguments
    have h_truncate_supp : ∀ z, z ∉ Set.Ioo (1/n : ℝ) n → truncate z = 0 := by
      intro z hz
      simp only [truncate, Set.mem_Ioo] at hz ⊢
      rw [if_neg]
      exact hz
    exact convolution_vanishes_on_nonpositive φ_δ truncate hφ_supp
      (le_of_lt hδ_bound) h_truncate_supp x hx

  -- Show that smooth_func is smooth
  have h_smooth : ContDiff ℝ (⊤ : ℕ∞) smooth_func := by
    apply smooth_mollifier_convolution_truncated
    · exact hφ_smooth
    · exact hφ_supp
    · exact hδ_pos

  -- Show that smooth_func is away from 0
  have h_support_away_zero : ∃ a > 0, ∀ x ∈ Set.Ioo 0 a, smooth_func x = 0 := by
    -- We can't guarantee 1/n - δ > 0 in general (since δ could equal 1/n)
    -- But we know h_support_left says smooth_func x = 0 for x ≤ 0
    -- And the convolution has some positive lower bound for its support
    -- Let's use a simpler approach: use a value that ensures x - y < 1/n for the truncate to be 0

    -- Choose a small enough so that for all x ∈ (0, a) and |y| ≤ δ, we have x - y ≤ 1/n
    -- Since y ≥ -δ, we need x + δ ≤ 1/n, i.e., x ≤ 1/n - δ
    -- If δ < 1/n, then 1/n - δ > 0 and we can use a = 1/n - δ
    -- But if δ = 1/n, we need a different approach

    -- We need to ensure that for all x in (0, a) and all y with |y| ≤ δ,
    -- we have x - y ≤ 1/n (so truncate(x - y) = 0)
    -- The worst case is y = -δ, giving x - y = x + δ
    -- So we need x + δ ≤ 1/n, i.e., x ≤ 1/n - δ
    -- Since δ ≤ 1/n, we have 1/n - δ ≥ 0
    -- But to ensure positivity, let's use a = (1/n - δ)/2 when δ < 1/n
    -- and a very small value when δ = 1/n

    -- Since δ < 1/n, we can use a = (1/n - δ)/2
    use (1/n - δ)/2
    constructor
    · -- (1/n - δ)/2 > 0
      apply div_pos
      · linarith [hδ_bound]
      · norm_num
    · intros x hx
      -- For small positive x, the convolution is 0
      -- smooth_func x = ∫ y, φ_δ(y) * truncate(x - y)
      -- where truncate is supported on (1/n, n)

      simp only [smooth_func]
      -- Show the integral is 0 by showing the integrand is 0
      have h_zero : ∀ y, (φ_δ y : ℂ) * (if 1/n < x - y ∧ x - y < n then
                           Lp.simpleFunc.toSimpleFunc s (x - y) else 0) = 0 := by
        intro y
        by_cases hy : |y| > δ
        · -- If |y| > δ, then φ_δ(y) = 0
          have : φ_δ y = 0 := hφ_supp y hy
          simp only [this, Complex.ofReal_zero, zero_mul]
        · -- If |y| ≤ δ, we show truncate(x - y) = 0
          push_neg at hy
          -- We have x < (1/n - δ)/2 and |y| ≤ δ
          -- So x + |y| < (1/n - δ)/2 + δ = (1/n - δ + 2δ)/2 = (1/n + δ)/2
          -- Since δ < 1/n, we have (1/n + δ)/2 < 1/n
          -- Therefore x - y ≤ x + |y| < 1/n

          have hx_bound : x < ((1 : ℝ)/↑n - δ)/2 := hx.2
          have hy_lower : -δ ≤ y := by
            have : -|y| ≤ y := neg_abs_le y
            linarith [hy]

          -- x - y ≤ x + δ < (1/n - δ)/2 + δ = 1/n/2 + δ/2 < 1/n
          have hxy_bound : x - y ≤ (1 : ℝ)/↑n := by
            have h1 : x - y ≤ x + δ := by linarith [hy_lower]
            have h2 : x + δ < ((1 : ℝ)/↑n - δ)/2 + δ := by linarith [hx_bound]
            have h3 : ((1 : ℝ)/↑n - δ)/2 + δ = 1/↑n/2 + δ/2 := by ring
            have h4 : (1 : ℝ)/↑n/2 + δ/2 < 1/↑n/2 + 1/↑n/2 := by linarith [hδ_bound]
            have h5 : (1 : ℝ)/↑n/2 + 1/↑n/2 = 1/↑n := by ring
            -- Combine the inequalities
            have : x - y < (1 : ℝ)/↑n := by
              calc x - y ≤ x + δ := h1
                _ < ((1 : ℝ)/↑n - δ)/2 + δ := h2
                _ = (1 : ℝ)/↑n/2 + δ/2 := h3
                _ < (1 : ℝ)/↑n/2 + 1/↑n/2 := h4
                _ = (1 : ℝ)/↑n := h5
            exact le_of_lt this

          -- Now show truncate(x - y) = 0
          have : ¬(1/n < x - y ∧ x - y < n) := by
            intro h
            exact not_lt.mpr hxy_bound h.1
          simp only [if_neg this, mul_zero]

      -- Since the integrand is 0 everywhere, the integral is 0
      have : (∫ y, (φ_δ y : ℂ) * (if 1/n < x - y ∧ x - y < n then
                    Lp.simpleFunc.toSimpleFunc s (x - y) else 0)) = 0 := by
        rw [MeasureTheory.integral_congr_ae]
        · rw [MeasureTheory.integral_zero]
        · filter_upwards with y using h_zero y
      exact this

  -- Apply the general lemma for smooth functions with compact support
  exact smooth_compact_support_memLp smooth_func h_smooth h_support
    h_support_left h_support_away_zero

end MeasureFiniteness

end Frourio
