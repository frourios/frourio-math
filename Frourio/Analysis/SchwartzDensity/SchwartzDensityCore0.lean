import Frourio.Analysis.MellinBasic
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

/-- Algebraic simplification lemma: (C/x^k)^2 * x^(2σ-1) = C^2 * x^(2σ-1-2k) for x > 0. -/
lemma rpow_div_pow_sq_mul_rpow {C : ℝ} {x : ℝ} {k : ℕ} {σ : ℝ} (hx : 0 < x) :
    (C / x ^ k) ^ 2 * x ^ (2 * σ - 1) = C ^ 2 * x ^ (2 * σ - 1 - 2 * (k : ℝ)) := by
  have hx_ne : (x ^ k) ≠ 0 := by
    exact pow_ne_zero _ (ne_of_gt hx)
  have h_cast_nat : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by
    norm_cast
  have h_pow_sq : (x ^ k) ^ 2 = x ^ (2 * k) := by
    -- (x^k)^2 = x^(2*k)
    simpa [mul_comm] using (pow_mul x k 2).symm
  -- Rewrite (C / x^k)^2 as C^2 / (x^k)^2 and use the above power identity
  calc
    (C / x ^ k) ^ 2 * x ^ (2 * σ - 1)
        = (C ^ 2 / (x ^ k) ^ 2) * x ^ (2 * σ - 1) := by
              -- expand square of a quotient
              have : (C / x ^ k) ^ 2 = C ^ 2 / (x ^ k) ^ 2 := by
                -- (C / y)^2 = C^2 / y^2
                field_simp [pow_two, hx_ne]
              simp [this]
    _ = (C ^ 2 / x ^ (2 * k)) * x ^ (2 * σ - 1) := by
          simp [h_pow_sq]
    _ = C ^ 2 * (x ^ (2 * σ - 1) / x ^ (2 * k)) := by
          -- a/b * c = a * c / b
          rw [div_mul_eq_mul_div]
          ring
    _ = C ^ 2 * x ^ ((2 * σ - 1) - (2 * k : ℝ)) := by
          -- turn division of rpow into subtraction of exponents
          congr 1
          have hdiv : x ^ (2 * σ - 1) / x ^ (2 * k)
              = x ^ ((2 * σ - 1) - (2 * k : ℝ)) := by
            -- use rpow_sub with denominator exponent cast to ℝ
            have : x ^ (2 * k) = x ^ ((2 * k : ℕ) : ℝ) := (Real.rpow_natCast x (2 * k)).symm
            rw [this, h_cast_nat]
            exact (Real.rpow_sub hx (2 * σ - 1) (2 * (k : ℝ))).symm
          simpa using hdiv

/-- Lintegral identity for withDensity on a restricted set.
For a function G and density ρ, the integral of G with respect to the weighted measure
equals the integral of G * ρ with respect to the base measure. -/
lemma lintegral_withDensity_eq_lintegral_mul_restrict
    {σ : ℝ} (G : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hGm : Measurable G) :
    let μ0 := volume.restrict (Set.Ioi (0 : ℝ))
    let μ := μ0.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))
    ∫⁻ x in s, ENNReal.ofReal (G x) ∂μ
      = ∫⁻ x in s, ENNReal.ofReal (G x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂μ0 := by
  classical
  -- Expand the definitions for convenience
  set μ0 := volume.restrict (Set.Ioi (0 : ℝ)) with hμ0
  set μ := μ0.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) with hμ
  -- Rewrite set-integral as integral of an indicator, then apply withDensity lemma
  have h_left :
      ∫⁻ x in s, ENNReal.ofReal (G x) ∂μ
        = ∫⁻ x, Set.indicator s (fun x => ENNReal.ofReal (G x)) x ∂μ := by
    simp [lintegral_indicator, hs]
  have h_withDensity :=
    (lintegral_withDensity_eq_lintegral_mul
      (μ := μ0)
      (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
      (g := Set.indicator s (fun x => ENNReal.ofReal (G x))))
  have h_prod_indicator :
      (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) *
          Set.indicator s (fun x => ENNReal.ofReal (G x)) x)
        = Set.indicator s
            (fun x : ℝ => ENNReal.ofReal (G x) * ENNReal.ofReal (x ^ (2 * σ - 1))) := by
    funext x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx, mul_comm, mul_left_comm]
    · simp [Set.indicator_of_notMem hx]
  have h_right :
      ∫⁻ x, Set.indicator s (fun x => ENNReal.ofReal (G x)) x ∂μ
        = ∫⁻ x in s,
            ENNReal.ofReal (G x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂μ0 := by
    -- Move to base measure via withDensity and fold indicator back into a set integral
    calc ∫⁻ x, Set.indicator s (fun x => ENNReal.ofReal (G x)) x ∂μ
        = ∫⁻ x, (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)) *
                    Set.indicator s (fun x => ENNReal.ofReal (G x)) x) x ∂μ0 := by
              conv_lhs => rw [hμ]
              apply lintegral_withDensity_eq_lintegral_mul
              · exact Measurable.ennreal_ofReal (by measurability :
                  Measurable fun x => x ^ (2 * σ - 1))
              · apply Measurable.indicator
                · exact Measurable.ennreal_ofReal hGm
                · exact hs
      _ = ∫⁻ x, Set.indicator s (fun x => ENNReal.ofReal (G x) *
                    ENNReal.ofReal (x ^ (2 * σ - 1))) x ∂μ0 := by
              simp only [← h_prod_indicator]
      _ = ∫⁻ x in s, ENNReal.ofReal (G x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂μ0 := by
              rw [lintegral_indicator]
              exact hs
  -- Conclude by chaining the equalities
  calc ∫⁻ x in s, ENNReal.ofReal (G x) ∂μ
      = ∫⁻ x, Set.indicator s (fun x => ENNReal.ofReal (G x)) x ∂μ := h_left
    _ = ∫⁻ x in s, ENNReal.ofReal (G x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂μ0 := h_right

/-- Finiteness of lintegral of C^2 * x^(2σ-1-2k) on (1,∞) when the exponent < -1.
This is used to show integrability on the tail of the domain. -/
lemma lintegral_rpow_mul_const_lt_top {C : ℝ} {k : ℕ} {σ : ℝ}
    (h_integrable : IntegrableOn
      (fun (x : ℝ) => x ^ (2 * σ - 1 - 2 * (k : ℝ))) (Set.Ioi 1) volume) :
    ∫⁻ (x : ℝ) in Set.Ioi 1, ENNReal.ofReal
      (C ^ 2 * x ^ (2 * σ - 1 - 2 * (k : ℝ))) ∂volume < ∞ := by
  classical
  -- Denote the exponent by α for readability
  set α : ℝ := 2 * σ - 1 - 2 * (k : ℝ) with hα
  -- On (1, ∞), x > 0, so we can split `ofReal (C^2 * x^α)` into a product
  have h_ae_mul :
      (fun x : ℝ => ENNReal.ofReal (C ^ 2 * x ^ α))
        =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun x : ℝ => ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (x ^ α)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx
    have hx_nonneg : 0 ≤ x ^ α := Real.rpow_nonneg (le_of_lt hxpos) _
    have hC2_nonneg : 0 ≤ C ^ 2 := sq_nonneg C
    simp only
    rw [ENNReal.ofReal_mul hC2_nonneg]
  -- Rewrite set-lintegral using the a.e. identity above
  have h_rewrite :
      ∫⁻ (x : ℝ) in Set.Ioi 1, ENNReal.ofReal (C ^ 2 * x ^ α) ∂volume
        = ∫⁻ (x : ℝ) in Set.Ioi 1,
            ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (x ^ α) ∂volume := by
    simpa [hα] using lintegral_congr_ae h_ae_mul
  -- Factor out the constant inside the lintegral
  have h_meas : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ α)) :=
    (ENNReal.measurable_ofReal.comp (by
      simpa using (measurable_id.pow_const α)))
  have h_const_factor :
      ∫⁻ (x : ℝ) in Set.Ioi 1, ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (x ^ α) ∂volume
        = ENNReal.ofReal (C ^ 2) *
          ∫⁻ (x : ℝ) in Set.Ioi 1, ENNReal.ofReal (x ^ α) ∂volume := by
    -- `lintegral_const_mul` over the restricted measure
    rw [← lintegral_const_mul (ENNReal.ofReal (C ^ 2)) h_meas]
  -- Show the remaining lintegral is finite using integrability and nonnegativity
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] fun x : ℝ => x ^ α := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    exact Filter.Eventually.of_forall
      (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hx)) _)
  have h_ofReal_eq :
      ∫⁻ (x : ℝ) in Set.Ioi 1, ENNReal.ofReal (x ^ α) ∂volume
        = ENNReal.ofReal (∫ x in Set.Ioi 1, x ^ α ∂volume) := by
    simpa [hα] using
      (ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg).symm
  have h_inner_lt_top :
      ∫⁻ (x : ℝ) in Set.Ioi 1, ENNReal.ofReal (x ^ α) ∂volume < ∞ := by
    simp [h_ofReal_eq]
  -- Combine all pieces
  have h_const_fin : ENNReal.ofReal (C ^ 2) < ∞ := by simp
  have : ENNReal.ofReal (C ^ 2) *
      ∫⁻ (x : ℝ) in Set.Ioi 1, ENNReal.ofReal (x ^ α) ∂volume < ∞ := by
    refine ENNReal.mul_lt_top ?_ ?_
    · exact h_const_fin
    · exact h_inner_lt_top
  simpa [h_rewrite, h_const_factor]

/-- Tail square-integrability of a truncated Schwartz function under the weighted measure.
For σ > 1/2 and φ ∈ 𝒮(ℝ), the function x ↦ ‖(if x>0 then φ x else 0)‖^2 is integrable on (1,∞)
with respect to (volume.restrict (0,∞)).withDensity (x ↦ x^(2σ-1)).
Skeleton: use Schwartz decay to dominate the weight on (1,∞). -/
lemma schwartz_integrable_sq_tail_Hσ {σ : ℝ} (f : SchwartzMap ℝ ℂ) :
    IntegrableOn (fun x => ‖(if x > 0 then f x else 0)‖ ^ 2)
      (Set.Ioi (1 : ℝ))
      ((volume.restrict (Set.Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) := by
  classical
  -- Set up notations
  set μ0 := volume.restrict (Set.Ioi (0 : ℝ)) with hμ0
  set μ := μ0.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))) with hμ
  set G : ℝ → ℝ := fun x => ‖(if x > 0 then f x else 0)‖ ^ 2 with hG

  -- Measurability on the restricted measure μ.restrict (Ioi 1)
  have hf_meas : AEStronglyMeasurable (fun x : ℝ => f x) μ :=
    (SchwartzMap.continuous f).aestronglyMeasurable
  have hG_meas : AEStronglyMeasurable G (μ.restrict (Set.Ioi (1 : ℝ))) := by
    set g : ℝ → ℂ := fun x => if 0 < x then f x else 0 with hg
    have hg_meas_full : AEStronglyMeasurable g μ := by
      have hg_indicator : g = Set.indicator (Set.Ioi (0 : ℝ)) (fun x : ℝ => f x) := by
        funext x
        by_cases hx : 0 < x
        · simp [g, hg, Set.indicator, Set.mem_Ioi, hx]
        · simp [g, hg, Set.indicator, Set.mem_Ioi, hx]
      simpa [hg_indicator] using hf_meas.indicator measurableSet_Ioi
    have : AEStronglyMeasurable (fun x : ℝ => ‖g x‖ ^ 2) μ := by
      have := hg_meas_full.norm
      simpa [pow_two] using this.pow 2
    simpa [G, hG, hg] using this.restrict

  -- Choose k₁ with k₁ ≥ σ + 1/2 (stronger than needed, but convenient)
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, σ + 1 / 2 ≤ (k₁ : ℝ) := by
    rcases exists_nat_ge (σ + 1 / 2) with ⟨N, hN⟩
    exact ⟨N, hN⟩
  set C : ℝ := SchwartzMap.seminorm ℝ k₁ 0 f with hC
  have hC_nonneg : 0 ≤ C := by simp [hC]

  -- Schwartz decay: for x > 1, ‖f x‖ ≤ C / x^k₁
  have h_decay : ∀ x : ℝ, 1 < x → ‖f x‖ ≤ C / x ^ k₁ := by
    intro x hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    have hx_eq : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_pos hx_pos]
    have h_semi : ‖x‖ ^ k₁ * ‖iteratedFDeriv ℝ 0 f x‖ ≤ C := by
      simpa [hC] using SchwartzMap.le_seminorm ℝ k₁ 0 f x
    have h0 : ‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖ := by simp
    have hx_pow_pos : 0 < x ^ k₁ := pow_pos hx_pos _
    have : x ^ k₁ * ‖f x‖ ≤ C := by simpa [hx_eq, h0] using h_semi
    exact (le_div_iff₀ hx_pow_pos).mpr (by simpa [mul_comm] using this)

  -- Pointwise domination of the (weighted) integrand on (1,∞)
  have h_bound_weighted :
      (fun x => Set.indicator (Set.Ioi (1 : ℝ))
          (fun x => ENNReal.ofReal (G x) * ENNReal.ofReal (x ^ (2 * σ - 1))) x)
        ≤ (fun x => Set.indicator (Set.Ioi (1 : ℝ))
          (fun x => ENNReal.ofReal (C ^ 2 * x ^ (2 * σ - 1 - 2 * k₁))) x) := by
    intro x
    by_cases hx : x ∈ Set.Ioi (1 : ℝ)
    · have hx1 : 1 < x := hx
      have hx_pos : 0 < x := lt_trans zero_lt_one hx1
      have hf_sq_le : ‖f x‖ ^ 2 ≤ (C / x ^ k₁) ^ 2 := by
        have h_le := h_decay x hx1
        have hx_pow_nonneg : 0 ≤ x ^ k₁ := by exact pow_nonneg (le_of_lt hx_pos) _
        have hrhs_nonneg : 0 ≤ C / x ^ k₁ := div_nonneg hC_nonneg hx_pow_nonneg
        have := mul_le_mul h_le h_le (by exact norm_nonneg _) hrhs_nonneg
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      have hx_mul : ‖f x‖ ^ 2 * x ^ (2 * σ - 1)
            ≤ (C / x ^ k₁) ^ 2 * x ^ (2 * σ - 1) :=
        mul_le_mul_of_nonneg_right hf_sq_le (by exact Real.rpow_nonneg (le_of_lt hx_pos) _)
      -- Algebraic simplification: (C/x^k)^2 * x^(2σ-1) = C^2 * x^(2σ-1-2k)
      have hx_simpl : (C / x ^ k₁) ^ 2 * x ^ (2 * σ - 1) = C ^ 2 * x ^ (2 * σ - 1 - 2 * (k₁ : ℝ)) :=
        rpow_div_pow_sq_mul_rpow hx_pos
      have hx_fin :
          ENNReal.ofReal (‖f x‖ ^ 2 * x ^ (2 * σ - 1)) ≤
            ENNReal.ofReal (C ^ 2 * x ^ (2 * σ - 1 - 2 * (k₁ : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        calc ‖f x‖ ^ 2 * x ^ (2 * σ - 1)
            ≤ (C / x ^ k₁) ^ 2 * x ^ (2 * σ - 1) := hx_mul
          _ = C ^ 2 * x ^ (2 * σ - 1 - 2 * (k₁ : ℝ)) := hx_simpl
      -- Now incorporate the indicator and the weight factor ENNReal.ofReal (x^(...))
      have : ENNReal.ofReal (G x) * ENNReal.ofReal (x ^ (2 * σ - 1))
            ≤ ENNReal.ofReal (C ^ 2 * x ^ (2 * σ - 1 - 2 * (k₁ : ℝ))) := by
        -- since G x = ‖f x‖^2 for x>1
        have hG_eq : G x = ‖f x‖ ^ 2 := by
          simp [G, hG, hx_pos]
        have hx_rpow_nonneg : 0 ≤ x ^ (2 * σ - 1) := Real.rpow_nonneg (le_of_lt hx_pos) _
        have hfx_sq_nonneg : 0 ≤ ‖f x‖ ^ 2 := sq_nonneg _
        rw [hG_eq, ← ENNReal.ofReal_mul hfx_sq_nonneg]
        exact hx_fin
      simpa [Set.indicator_of_mem hx]
        using this
    · simp [Set.indicator_of_notMem hx]

  -- Convert IntegrableOn to a finiteness statement for a lintegral via withDensity
  -- and bound it using the pointwise estimate above with an integrable power.
  have h_lint_weighted :
      ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (G x) ∂μ
        = ∫⁻ x in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (G x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂μ0 := by
    -- Use the lintegral withDensity identity
    -- prove measurability of G on ℝ
    have hGm : Measurable G := by
      -- G x = ‖(if 0 < x then f x else 0)‖^2
      have h_meas : Measurable (fun x : ℝ => if 0 < x then f x else (0 : ℂ)) := by
        refine Measurable.ite measurableSet_Ioi
          (SchwartzMap.continuous f).measurable
          measurable_const
      -- measurability of norm, then square via multiplication
      have h_norm : Measurable (fun x : ℝ => ‖(if 0 < x then f x else (0 : ℂ))‖) :=
        h_meas.norm
      have h_sq : Measurable
          (fun x : ℝ => ‖(if 0 < x then f x else (0 : ℂ))‖ * ‖(if 0 < x then f x else (0 : ℂ))‖) :=
        h_norm.mul h_norm
      -- rewrite to G using pow_two
      simpa [G, hG, gt_iff_lt, pow_two, mul_comm, mul_left_comm, mul_assoc]
        using h_sq
    exact lintegral_withDensity_eq_lintegral_mul_restrict G (Set.Ioi 1) measurableSet_Ioi hGm

  have h_lint_bound :
      ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (G x) ∂μ ≤
        ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (C ^ 2 * x ^ (2 * σ - 1 - 2 * (k₁ : ℝ))) ∂μ0 := by
    have := lintegral_mono
      (μ := μ0)
      (f := Set.indicator (Set.Ioi (1 : ℝ))
        (fun x => ENNReal.ofReal (G x) * ENNReal.ofReal (x ^ (2 * σ - 1))))
      (g := Set.indicator (Set.Ioi (1 : ℝ))
        (fun x => ENNReal.ofReal (C ^ 2 * x ^ (2 * σ - 1 - 2 * (k₁ : ℝ)))))
      h_bound_weighted
    simpa [h_lint_weighted]
      using this

  -- The majorant on the right is finite since exponent < -1 on (1,∞)
  have h_exp_lt : (2 * σ - 1) - 2 * (k₁ : ℝ) < -1 := by
    have : 2 * σ - 1 - 2 * (k₁ : ℝ) ≤ -2 := by linarith [hk₁]
    exact lt_of_le_of_lt this (by norm_num)
  have h_integrable_pow :
      IntegrableOn (fun x : ℝ => x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ))) (Set.Ioi (1 : ℝ)) volume := by
    exact integrableOn_Ioi_rpow_of_lt h_exp_lt zero_lt_one
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
        (fun x : ℝ => x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ))) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    exact Filter.Eventually.of_forall
      (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hx)) _)

  have h_rhs_lt_top_vol : ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
      (C ^ 2 * x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ))) ∂volume < ∞ := by
    exact lintegral_rpow_mul_const_lt_top (C := C) (k := k₁) (σ := σ)
      h_integrable_pow

  -- The same finiteness holds with μ0 = volume.restrict (Ioi 0) since we integrate on Ioi 1 ⊆ Ioi 0
  have h_rhs_lt_top : ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
      (C ^ 2 * x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ))) ∂μ0 < ∞ := by
    -- identify the restricted measures on Ioi 1
    have hμeq : μ0.restrict (Set.Ioi (1 : ℝ)) = volume.restrict (Set.Ioi (1 : ℝ)) := by
      have := Measure.restrict_restrict (μ := volume)
          (s := Set.Ioi (0 : ℝ)) (t := Set.Ioi (1 : ℝ)) measurableSet_Ioi
      have hsubset : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
        intro x hx
        simp only [Set.mem_Ioi] at hx ⊢
        exact lt_trans zero_lt_one hx
      simp [μ0, Set.inter_eq_right.mpr hsubset]
    -- convert set-lintegrals to integrals over restricted measures and rewrite using hμeq
    have h_lhs_rewrite :
        ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (C ^ 2 * x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ))) ∂μ0 =
        ∫⁻ x, ENNReal.ofReal (C ^ 2 * x ^ ((2 * σ - 1) - 2 *
          (k₁ : ℝ))) ∂(μ0.restrict (Set.Ioi (1 : ℝ))) := by
      -- standard rewrite between set integral and restricted measure
      simp [lintegral_indicator, measurableSet_Ioi]
    have h_rhs_rewrite :
        ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
          (C ^ 2 * x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ))) ∂volume =
        ∫⁻ x, ENNReal.ofReal (C ^ 2 * x ^ ((2 * σ - 1) - 2 *
          (k₁ : ℝ))) ∂(volume.restrict (Set.Ioi (1 : ℝ))) := by
      simp [lintegral_indicator, measurableSet_Ioi]
    -- compare via the equality of restricted measures, then conclude finiteness
    have :
        ∫⁻ x, ENNReal.ofReal (C ^ 2 * x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ)))
            ∂(μ0.restrict (Set.Ioi (1 : ℝ)))
          = ∫⁻ x, ENNReal.ofReal (C ^ 2 * x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ)))
            ∂(volume.restrict (Set.Ioi (1 : ℝ))) := by
      simp [hμeq]
    -- put pieces together
    have :
        ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
          (C ^ 2 * x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ))) ∂μ0
          = ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal
              (C ^ 2 * x ^ ((2 * σ - 1) - 2 * (k₁ : ℝ))) ∂volume := by
      simpa [h_lhs_rewrite, h_rhs_rewrite] using this
    -- now use the volume finiteness
    simpa [this]

  -- Conclude IntegrableOn: via measurability and finiteness of lintegral under μ
  -- Show the finiteness on μ.restrict (Ioi 1)
  have h_left_lt_top :
      (∫⁻ x, ENNReal.ofReal (G x) ∂(μ.restrict (Set.Ioi (1 : ℝ)))) < ∞ := by
    -- rewrite to a set integral and apply the bound h_lint_bound
    have h_rewrite :
        ∫⁻ x, ENNReal.ofReal (G x) ∂(μ.restrict (Set.Ioi (1 : ℝ)))
          = ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (G x) ∂μ := by
      simp [lintegral_indicator, measurableSet_Ioi]
    -- combine ≤ bound with RHS finiteness
    have hle := le_trans (le_of_eq h_rewrite) h_lint_bound
    exact lt_of_le_of_lt hle h_rhs_lt_top
  -- package as IntegrableOn using hasFiniteIntegral_iff_ofReal
  have h_nonnegG : 0 ≤ᵐ[μ.restrict (Set.Ioi (1 : ℝ))] fun x => G x := by
    exact Filter.Eventually.of_forall (by intro x; dsimp [G, hG]; exact sq_nonneg _)
  -- Integrable on a set is Integrable with respect to the restricted measure
  dsimp [IntegrableOn]
  refine ⟨hG_meas, ?_⟩
  -- HasFiniteIntegral from the finiteness of the lintegral of ofReal
  exact (hasFiniteIntegral_iff_ofReal (μ := μ.restrict (Set.Ioi (1 : ℝ)))
      (f := G) h_nonnegG).2 h_left_lt_top

/-- Square-integrability of a truncated Schwartz function in the weighted measure on (0,∞).
This isolates the analytic content needed by `schwartz_mem_Hσ`.
Skeleton: proof splits into (0,1] and (1,∞) and uses σ > 1/2. -/
lemma schwartz_integrable_sq_Hσ {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖(if x > 0 then f x else 0)‖ ^ 2)
      ((volume.restrict (Set.Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) := by
  classical
  -- Outline:
  -- 1) Near 0: boundedness of f on [0,1] and ∫_0^1 x^(2σ-1) dx < ∞ (σ > 0)
  -- 2) Tail: Schwartz decay dominates x^(2σ-1) for large k, giving convergence on (1,∞)
  -- 3) Combine via splitting and standard integrability criteria.
  set μ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))) with hμ_def
  set G : ℝ → ℝ := fun x => ‖(if x > 0 then f x else 0)‖ ^ 2 with hG_def

  -- Split domain into (0,1] and (1,∞)
  have hs0 : MeasurableSet (Set.Ioc (0 : ℝ) 1) := measurableSet_Ioc
  have hs1 : MeasurableSet (Set.Ioi (1 : ℝ)) := measurableSet_Ioi
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx0 hx1
    exact (lt_of_le_of_lt hx0.2 hx1).false
  have hcover : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext x; constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · show (0 : ℝ) < x
        have h1x : (1 : ℝ) < x := hx
        calc (0 : ℝ)
            < 1 := zero_lt_one
          _ < x := h1x
    · intro hx
      by_cases hle : x ≤ 1
      · exact Or.inl ⟨hx, hle⟩
      · exact Or.inr (lt_of_not_ge hle)

  -- Local integrability on (0,1]: use boundedness and the near-zero weight integrability
  have h_int0 : IntegrableOn G (Set.Ioc (0 : ℝ) 1) μ := by
    -- We prove IntegrableOn by boundedness on a set of finite μ-measure.
    -- Step 0: measurability of G on the restricted measure
    have hf_meas : AEStronglyMeasurable (fun x : ℝ => f x) μ :=
      (SchwartzMap.continuous f).aestronglyMeasurable
    have hG_meas : AEStronglyMeasurable G (μ.restrict (Set.Ioc (0 : ℝ) 1)) := by
      -- G(x) = ‖(if 0 < x then f x else 0)‖^2 is obtained from a measurable map by
      -- indicator + norm + power; all preserve AE-strong measurability.
      set g : ℝ → ℂ := fun x => if 0 < x then f x else 0 with hg_def
      have hg_meas_full : AEStronglyMeasurable g μ := by
        have hg_indicator :
            g = Set.indicator (Set.Ioi (0 : ℝ)) (fun x : ℝ => f x) := by
          funext x
          by_cases hx : 0 < x
          · simp [g, hg_def, Set.indicator, Set.mem_Ioi, hx]
          · simp [g, hg_def, Set.indicator, Set.mem_Ioi, hx]
        simpa [hg_indicator] using hf_meas.indicator measurableSet_Ioi
      have h_comp :
          AEStronglyMeasurable (fun x : ℝ => ‖g x‖ ^ 2) μ := by
        have : AEStronglyMeasurable (fun x : ℝ => ‖g x‖) μ := hg_meas_full.norm
        simpa [pow_two] using this.pow 2
      exact h_comp.restrict
    -- Step 1: bound G by a constant on (0,1]
    set C : ℝ := SchwartzMap.seminorm ℝ 0 0 f with hC_def
    have hC_nonneg : 0 ≤ C := by simp [hC_def]
    have h_bound : ∀ᵐ x ∂μ.restrict (Set.Ioc (0 : ℝ) 1), ‖G x‖ ≤ C ^ 2 := by
      -- On (0,1], x>0 so G = ‖f x‖^2 ≤ C^2 by the seminorm bound.
      refine (ae_restrict_iff' (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      have hx_pos : 0 < x := hx.1
      have h_eq : G x = ‖f x‖ ^ 2 := by
        simp [G, hG_def, hx_pos]
      have h_norm_le : ‖f x‖ ≤ C := by
        simpa [hC_def] using (SchwartzMap.norm_le_seminorm ℝ f x)
      have hx_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
      have h_sq : ‖f x‖ ^ 2 ≤ C ^ 2 := by
        have := mul_le_mul h_norm_le h_norm_le hx_nonneg hC_nonneg
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      simpa [h_eq] using h_sq
    -- Step 2: show μ(Set.Ioc 0 1) < ∞ using the weight bound x^(2σ-1) ≤ 1 on (0,1]
    have hμ_set_lt_top : μ (Set.Ioc (0 : ℝ) 1) < ∞ := by
      -- Compute μ on (0,1] and bound via volume
      have hμ_apply :
          μ (Set.Ioc (0 : ℝ) 1) =
            ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal
            (x ^ (2 * σ - 1)) ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
        classical
        simp [μ, hμ_def, measurableSet_Ioc]
      have h_weight_le_one :
          (fun x : ℝ => Set.indicator (Set.Ioc (0 : ℝ) 1)
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) x)
            ≤ (fun x : ℝ => Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) x) := by
        intro x
        by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
        · have hx_pos : 0 < x := hx.1
          have hx_le1 : x ≤ 1 := hx.2
          have hpow_le_one : x ^ (2 * σ - 1) ≤ 1 := by
            -- 0 < x ≤ 1 and exponent positive ⇒ x^r ≤ 1
            have hr_pos : 0 ≤ 2 * σ - 1 := by linarith [hσ]
            have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
            exact Real.rpow_le_one hx_nonneg hx_le1 hr_pos
          have : ENNReal.ofReal (x ^ (2 * σ - 1)) ≤ 1 := by
            have hpow_nonneg : 0 ≤ x ^ (2 * σ - 1) := Real.rpow_nonneg (le_of_lt hx_pos) _
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal hpow_le_one
          simpa [Set.indicator_of_mem hx] using this
        · simp [Set.indicator_of_notMem hx]
      have h_lint_le :
          ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal
            (x ^ (2 * σ - 1)) ∂(volume.restrict (Set.Ioi (0 : ℝ))) ≤
            ∫⁻ x in Set.Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
        -- Rewrite as integrals with indicators
        have eq1 : ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal
            (x ^ (2 * σ - 1)) ∂(volume.restrict (Set.Ioi (0 : ℝ)))
            = ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1) (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) x
                ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
          symm
          apply lintegral_indicator
          exact measurableSet_Ioc
        rw [eq1]
        have eq2 : ∫⁻ x in Set.Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) ∂(volume.restrict (Set.Ioi (0 : ℝ)))
            = ∫⁻ x, Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) x
                ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
          symm
          apply lintegral_indicator
          exact measurableSet_Ioc
        rw [eq2]
        exact lintegral_mono h_weight_le_one
      have h_rhs :
          ∫⁻ x in Set.Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) ∂(volume.restrict (Set.Ioi (0 : ℝ)))
            = (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioc (0 : ℝ) 1) := by
        classical
        simp
      have h_vol_eq : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioc (0 : ℝ) 1) =
          volume (Set.Ioc (0 : ℝ) 1) := by
        classical
        have h_subset : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := by
          intro x hx; exact hx.1
        have h_inter : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 :=
          Set.inter_eq_left.mpr h_subset
        simp [Measure.restrict_apply, measurableSet_Ioc, h_inter]
      have h_vol_lt_top : volume (Set.Ioc (0 : ℝ) 1) < ∞ := by
        simp [Real.volume_Ioc, volume_Ioc]
      -- Conclude finiteness via the chain of inequalities
      have : μ (Set.Ioc (0 : ℝ) 1) ≤ volume (Set.Ioc (0 : ℝ) 1) := by
        simpa [hμ_apply, h_rhs, h_vol_eq] using h_lint_le
      exact lt_of_le_of_lt this h_vol_lt_top
    -- Step 3: assemble IntegrableOn using the boundedness over a finite-measure set
    unfold IntegrableOn
    refine ⟨hG_meas, ?_⟩
    exact
      MeasureTheory.hasFiniteIntegral_restrict_of_bounded
        (μ := μ) (s := Set.Ioc (0 : ℝ) 1) (f := G) (C := C ^ 2)
        hμ_set_lt_top h_bound

  -- Local integrability on (1,∞): use Schwartz decay to dominate the weight
  have h_int1 : IntegrableOn G (Set.Ioi (1 : ℝ)) μ := by
    -- Delegate the tail integrability to a dedicated lemma.
    simpa [μ, G, hG_def] using schwartz_integrable_sq_tail_Hσ (σ := σ) f

  -- Combine via union (the two pieces are disjoint and cover (0,∞))
  have h_int_on : IntegrableOn G (Set.Ioi (0 : ℝ)) μ := by
    -- Integrable on union of disjoint measurable sets
    -- IntegrableOn.union : IntegrableOn f s μ → IntegrableOn f t μ → IntegrableOn f (s ∪ t) μ
    have h_union : IntegrableOn G (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)) μ :=
      h_int0.union h_int1
    rw [hcover] at h_union
    exact h_union

  -- Upgrade from IntegrableOn (Ioi 0) to Integrable on μ
  -- Since μ is supported on (0,∞), IntegrableOn on (0,∞) is the same as Integrable on μ.
  -- μ = (volume.restrict (Ioi 0)).withDensity ρ, so μ is already supported on (Ioi 0)
  -- Therefore μ.restrict (Ioi 0) = μ, and IntegrableOn G (Ioi 0) μ = Integrable G μ
  have h_restrict_eq : μ.restrict (Set.Ioi (0 : ℝ)) = μ := by
    -- Use `restrict_withDensity` with base measure `volume.restrict (Ioi 0)` and set `Ioi 0`.
    -- This yields: ((volume.restrict Ioi0).withDensity w).restrict Ioi0
    --   = ((volume.restrict Ioi0).restrict Ioi0).withDensity w,
    -- and `restrict_restrict` simplifies the RHS back to `(volume.restrict Ioi0).withDensity w`.
    have hres := restrict_withDensity
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
    simpa [hμ_def, Measure.restrict_restrict measurableSet_Ioi]
      using hres
  rw [IntegrableOn, h_restrict_eq] at h_int_on
  exact h_int_on

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

/-- Schwartz functions restricted to (0,∞) belong to Hσ for σ > 1/2 -/
lemma schwartz_mem_Hσ {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => if x > 0 then f x else 0) 2
      ((volume.restrict (Set.Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) := by
  -- Skeleton of the proof under the given assumption σ > 1/2.
  -- Step A: Set up the weighted measure on (0, ∞) and the truncated function.
  classical
  set μ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))) with hμ_def
  set g : ℝ → ℂ := fun x => if x > 0 then f x else 0 with hg_def

  -- Step B: g is AE-strongly measurable (f is continuous; add an indicator on (0, ∞)).
  have hf_meas : AEStronglyMeasurable (fun x : ℝ => f x) μ :=
    (SchwartzMap.continuous f).aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable g μ := by
    -- Rewrite g as the indicator of (0, ∞) applied to f, then use hf_meas.indicator.
    have hg_indicator :
        g = Set.indicator (Set.Ioi (0 : ℝ)) (fun x : ℝ => f x) := by
      funext x
      by_cases hx : 0 < x
      · simp [g, hg_def, Set.indicator, Set.mem_Ioi, hx]
      · simp [g, hg_def, Set.indicator, Set.mem_Ioi, hx]
    simpa [hg_indicator] using hf_meas.indicator measurableSet_Ioi

  -- Step C: Reduce MemLp g 2 μ to integrability of ‖g‖^2 via the standard criterion.
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
  -- It suffices to show Integrable (‖g‖^2) with respect to μ.
  have hg_integrable_sq : Integrable (fun x => ‖g x‖ ^ 2) μ := by
    -- Delegate the analytic content to a separate lemma.
    simpa [μ, g, hg_def] using schwartz_integrable_sq_Hσ (σ := σ) hσ f
  have hg_int_pow : Integrable (fun x => ‖g x‖ ^ (2 : ℝ≥0∞).toReal) μ := by
    simpa [ENNReal.toReal_ofNat, pow_two] using hg_integrable_sq
  -- Conclude MemLp via the norm^p integrability characterization.
  -- integrable_norm_rpow_iff: Integrable (‖g‖^p.toReal) ↔ MemLp g p
  exact (integrable_norm_rpow_iff (μ := μ) (f := g) hg_meas h_two_ne_zero h_two_ne_top).1 hg_int_pow

/-- The embedding of Schwartz functions into Hσ for σ > 1/2 -/
noncomputable def schwartzToHσ {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) : Hσ σ :=
  MemLp.toLp (fun x : ℝ => if x > 0 then f x else 0)
    (schwartz_mem_Hσ (σ := σ) hσ f)

/-- The embedding is linear for σ > 1/2 -/
lemma schwartzToHσ_linear {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∀ (a : ℂ) (f g : SchwartzMap ℝ ℂ),
    schwartzToHσ hσ (a • f + g) = a • schwartzToHσ hσ f + schwartzToHσ hσ g := by
  intro a f g
  classical
  -- Prove equality in Lp by a.e. equality of representatives
  apply Lp.ext
  -- Left: coeFn equals the truncated sum a.e.
  have hL :
      (((schwartzToHσ hσ (a • f + g) : Hσ σ) : ℝ → ℂ))
        =ᵐ[((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))]
        (fun x => if 0 < x then a • f x + g x else 0) := by
    simpa [schwartzToHσ]
      using (MemLp.coeFn_toLp (schwartz_mem_Hσ hσ (a • f + g)))
  -- Right: coeFn equals the same function a.e. by distributing smul/add under the indicator
  have hf := (MemLp.coeFn_toLp (schwartz_mem_Hσ hσ f))
  have hg := (MemLp.coeFn_toLp (schwartz_mem_Hσ hσ g))
  have h_add :
      (((a • schwartzToHσ hσ f + schwartzToHσ hσ g : Hσ σ) : ℝ → ℂ))
        =ᵐ[((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))]
        (fun x =>
          (((a • schwartzToHσ hσ f : Hσ σ) : ℝ → ℂ) x)
          + (((schwartzToHσ hσ g : Hσ σ) : ℝ → ℂ) x)) := by
    simpa using (Lp.coeFn_add (a • schwartzToHσ hσ f) (schwartzToHσ hσ g))
  have h_smul :
      (fun x => (((a • schwartzToHσ hσ f : Hσ σ) : ℝ → ℂ) x))
        =ᵐ[((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))]
        (fun x => a • (((schwartzToHσ hσ f : Hσ σ) : ℝ → ℂ) x)) := by
    simpa [Pi.smul_apply]
      using (Lp.coeFn_smul ((RingHom.id ℂ) a) (schwartzToHσ hσ f))
  have hR_step1 :
      (((a • schwartzToHσ hσ f + schwartzToHσ hσ g : Hσ σ) : ℝ → ℂ))
        =ᵐ[((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))]
        (fun x => a • (((schwartzToHσ hσ f : Hσ σ) : ℝ → ℂ) x)
                  + (((schwartzToHσ hσ g : Hσ σ) : ℝ → ℂ) x)) := by
    refine h_add.trans ?_
    -- replace the first summand a.e. using h_smul
    refine h_smul.mono ?_
    intro x hx
    simp [hx]
  -- Replace the representatives of f and g by their truncated versions a.e.
  have h_smul_rep :
      (fun x => a • (((schwartzToHσ hσ f : Hσ σ) : ℝ → ℂ) x))
        =ᵐ[((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))]
        (fun x => a • (if 0 < x then f x else 0)) := by
    refine hf.mono ?_
    intro x hx
    simpa using congrArg (fun z => a • z) hx
  have h_rep_g :
      (fun x => (((schwartzToHσ hσ g : Hσ σ) : ℝ → ℂ) x))
        =ᵐ[((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))]
        (fun x => (if 0 < x then g x else 0)) := by
    simpa using hg
  -- Combine the two a.e. equalities additively
  have h_sum_reps :
      (fun x => a • (((schwartzToHσ hσ f : Hσ σ) : ℝ → ℂ) x)
                + (((schwartzToHσ hσ g : Hσ σ) : ℝ → ℂ) x))
        =ᵐ[((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))]
        (fun x => a • (if 0 < x then f x else 0)
                + (if 0 < x then g x else 0)) := by
    -- Use properties of EventuallyEq under addition
    refine (h_smul_rep.add h_rep_g)
  have hR :
      (((a • schwartzToHσ hσ f + schwartzToHσ hσ g : Hσ σ) : ℝ → ℂ))
        =ᵐ[((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))]
        (fun x => a • (if 0 < x then f x else 0)
                + (if 0 < x then g x else 0)) :=
    hR_step1.trans h_sum_reps
  -- Pointwise, distributing the indicator gives the truncated sum
  have h_pointwise :
      (fun x => if 0 < x then a • f x + g x else 0)
        = (fun x => a • (if 0 < x then f x else 0)
                + (if 0 < x then g x else 0)) := by
    funext x; by_cases hx : 0 < x <;> simp [hx]
  -- Conclude equality in Lp via both sides agreeing a.e. with the same function
  refine hL.trans ?_
  rw [h_pointwise]
  exact hR.symm

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
      have hx_norm_sq_pow : (‖f x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖f x‖ ^ 2) := by
        simpa using (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
      have hx_ofReal :
          ENNReal.ofReal (‖f x‖ ^ 2) ≤ ENNReal.ofReal ((C / x ^ k₁) ^ 2) :=
        ENNReal.ofReal_le_ofReal h_sq'
      simpa [hx_set, hx_norm_sq_pow] using hx_ofReal
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
    simpa using (ENNReal.ofReal_pow (norm_nonneg _) 2).symm

  -- First, use the integral bound to get an inequality for the square
  have h_sq_bound : (eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2 μ) ^ (2 : ℝ) ≤
      ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ := by
    have h' := h_integral_bound
    calc
      (eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2 μ) ^ (2 : ℝ)
          = ∫⁻ x, ‖if x ∈ Set.Ioi 1 then f x else 0‖ₑ ^ (2 : ℝ) ∂μ := h_eLpNorm_sq
      _ ≤ ∫⁻ x, ENNReal.ofReal ((if x ∈ Set.Ioi (1 : ℝ) then C / x ^ k₁ else 0) ^ 2) ∂μ := by
          rw [h_norm_eq]
          simpa [Set.mem_Ioi, h_fun] using h'

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
    hasFiniteIntegral_of_bounded
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
    · exact hasFiniteIntegral_of_bounded (μ := volume.restrict s) h_bound_ae
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
    · exact hasFiniteIntegral_of_bounded (μ := volume.restrict s) h_bound_ae
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
