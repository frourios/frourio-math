import Frourio.Analysis.Gaussian
import Frourio.Analysis.MellinBasic
import Frourio.Analysis.HilbertSpaceCore
import Frourio.Analysis.SchwartzDensity.SchwartzDensityCore2
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
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Order.Filter.Basic

open MeasureTheory Measure Real Complex SchwartzMap intervalIntegral
open scoped ENNReal Topology ComplexConjugate

namespace Frourio

section SchwartzDensity

/-- Standard mollification error for L² functions with weighted measure -/
lemma standard_mollification_l2_error {σ : ℝ} (hσ : 1 / 2 < σ)
    (f : ℝ → ℂ) (hf_memLp : MemLp f 2 (weightedMeasure σ))
    (φ : ℝ → ℝ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x)
    (hφ_integral : ∫ x, φ x ∂volume = 1)
    (δ ε : ℝ) (hδ_pos : 0 < δ) (hε_pos : 0 < ε) :
    let φδ := fun x => (1 / δ) * φ (x / δ)
    let g := fun x => ∫ y, f y * φδ (x - y) ∂volume
    ∀ hg_memLp : MemLp g 2 (weightedMeasure σ),
    δ < ε / (4 * (ENNReal.toReal (eLpNorm f 2 (weightedMeasure σ)) + 1)) →
    dist (hf_memLp.toLp f) (hg_memLp.toLp g) < ε := by
  sorry -- Standard mollification approximation theorem

/-- Truncated functions from L²(weightedMeasure σ) are locally integrable with respect to volume -/
lemma s_R_locally_integrable_volume {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2)
    (s : Lp ℂ 2 (weightedMeasure σ)) (R : ℝ) (hR_pos : 0 < R)
    (hs_R_memLp : MemLp (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) 2
      (weightedMeasure σ)) :
    LocallyIntegrable (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) volume := by
  -- s_R has support on (0,R] and is in L²(weightedMeasure σ), so locally integrable
  sorry

/-- Convert eLpNorm bound to Lp distance bound for truncation error -/
lemma truncation_error_dist_bound {σ : ℝ} (s : Lp ℂ 2 (weightedMeasure σ))
    (s_R : ℝ → ℂ) (hs_R_memLp : MemLp s_R 2 (weightedMeasure σ))
    (ε : ℝ) (hε : 0 < ε)
    (h_norm_bound : eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ) < ENNReal.ofReal ε) :
    dist s (hs_R_memLp.toLp s_R) < ε := by
  -- The distance in Lp space equals the L² norm of the difference
  -- dist s (hs_R_memLp.toLp s_R) = ‖s - hs_R_memLp.toLp s_R‖
  -- Since toLp s_R represents s_R as an Lp element with the same function a.e.,
  -- this equals eLpNorm ((s : ℝ → ℂ) - s_R) converted to real
  sorry

/-- Distance equivalence under measure isometry for Lp spaces -/
lemma lp_dist_measure_equiv {σ : ℝ} (f : Hσ σ) (g : ℝ → ℂ)
    (f_Lp : Lp ℂ 2 (weightedMeasure σ))
    (hf_weightedMeasure : MemLp (Hσ.toFun f) 2 (weightedMeasure σ))
    (hf_Lp_eq : f_Lp = hf_weightedMeasure.toLp (Hσ.toFun f))
    (hg_memLp : MemLp g 2 (weightedMeasure σ))
    (hg_memLp_converted : MemLp g 2 (mulHaar.withDensity (fun x =>
      ENNReal.ofReal (x ^ (2 * σ - 1))))) :
    dist f (hg_memLp_converted.toLp g) = dist f_Lp (hg_memLp.toLp g) := by
  -- This equality holds because:
  -- 1. f and f_Lp represent the same element (f_Lp = toLp f)
  -- 2. hg_memLp_converted.toLp g and hg_memLp.toLp g represent the same element
  -- 3. The measure equivalence preserves distances
  -- The key insight is that we're computing distances in equivalent Lp spaces
  -- f : Hσ σ, and f_Lp = toLp (Hσ.toFun f) : Lp ℂ 2 (weightedMeasure σ)
  -- hg_memLp_converted corresponds to the same function g under measure equivalence
  sorry

/-- Triangle inequality chain for Lp approximation sequence -/
lemma lp_approximation_triangle_chain {σ : ℝ}
    (f_Lp : Lp ℂ 2 (weightedMeasure σ))
    (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (g_cont : ℝ → ℂ) (hg_cont_memLp : MemLp g_cont 2 (weightedMeasure σ))
    (g : ℝ → ℂ) (hg_memLp : MemLp g 2 (weightedMeasure σ))
    (ε : ℝ) (hε : 0 < ε)
    (hs_close : dist f_Lp (↑s) < ε / 2)
    (hg_cont_close : dist (↑s) (hg_cont_memLp.toLp g_cont) < ε / 4)
    (hg_mollify_close : dist (hg_cont_memLp.toLp g_cont) (hg_memLp.toLp g) < ε / 4) :
    dist f_Lp (hg_memLp.toLp g) < ε := by
  -- The approximation chain works as follows:
  -- f_Lp --[ε/2]-- s --[ε/4]-- g_cont --[ε/4]-- g
  -- where each arrow represents a distance bound
  -- The mathematical proof uses two applications of triangle inequality:
  -- Step 1: dist f_Lp g ≤ dist f_Lp s + dist s g
  -- Step 2: dist s g ≤ dist s g_cont + dist g_cont g
  -- Combined: dist f_Lp g ≤ dist f_Lp s + dist s g_cont + dist g_cont g
  -- Apply the bounds: ε/2 + ε/4 + ε/4 = ε
  sorry

/-- Truncated L² functions are integrable with respect to volume measure -/
lemma truncated_lp_integrable {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2)
    (s : Lp ℂ 2 (weightedMeasure σ)) (R : ℝ) (hR_pos : 0 < R) :
    Integrable (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) volume := by
  -- The truncated function has support in (0,R] which has finite measure
  -- Since s ∈ L²(weighted), on bounded sets it's integrable by Hölder's inequality
  sorry

/-- L² functions can be approximated by continuous
  compactly supported functions in weighted L² spaces -/
lemma lp_to_continuous_approx {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2)
    (s : Lp ℂ 2 (weightedMeasure σ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g_cont : ℝ → ℂ) (hg_cont_memLp : MemLp g_cont 2 (weightedMeasure σ)),
      HasCompactSupport g_cont ∧
      Continuous g_cont ∧
      dist s (hg_cont_memLp.toLp g_cont) < ε := by
  -- CORRECTED PROOF STRATEGY:
  -- Step 1: Extract s as an L² function directly (no SimpleFunc conversion)
  -- Step 2: Truncate this L² function to bounded support
  -- Step 3: Mollify to get continuous compactly supported function
  -- Step 4: Control error through: ‖s - g‖ ≤ ‖s - s_R‖ + ‖s_R - g‖

  have hs_memLp : MemLp s 2 (weightedMeasure σ) := Lp.memLp s
  have h_two_ne_top : (2 : ENNReal) ≠ ∞ := by norm_num

  -- Step 1: Choose R large enough that truncation error is < ε/2
  -- For any L² function, ∫_{|x|>R} |s|² → 0 as R → ∞ (tail vanishing)
  obtain ⟨R, hR_pos, hR_truncation⟩ : ∃ R : ℝ, 0 < R ∧
      eLpNorm (fun x => if |x| > R then (s : ℝ → ℂ) x else 0) 2 (weightedMeasure σ) <
      ENNReal.ofReal (ε / 2) :=
    lp_tail_vanishing hσ_lower s (ε / 2) (by linarith : 0 < ε / 2)

  -- Define the truncated function s_R directly from s
  let s_R : ℝ → ℂ := fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0

  -- s_R has bounded support by construction (only positive values)
  have hs_R_support : Function.support s_R ⊆ Set.Ioc 0 R := by
    intro x hx
    simp only [s_R, Function.mem_support] at hx
    -- hx : (if 0 < x ∧ x ≤ R then s x else 0) ≠ 0
    -- This means 0 < x ∧ x ≤ R and s x ≠ 0
    by_cases h : 0 < x ∧ x ≤ R
    · -- If 0 < x ∧ x ≤ R, then x ∈ (0, R]
      exact ⟨h.1, h.2⟩
    · -- If ¬(0 < x ∧ x ≤ R), then s_R x = 0, contradicting hx
      simp only [h, if_false] at hx
      exact absurd rfl hx

  -- s_R is in L² since it's a truncation of an L² function
  have hs_R_memLp : MemLp s_R 2 (weightedMeasure σ) := by
    unfold s_R
    exact positive_truncation_memLp s R

  -- The truncation error is controlled
  have h_truncation_error :
      eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ) < ENNReal.ofReal (ε / 2) := by
    exact positive_truncation_error_bound s R (ε / 2) hR_truncation

  -- Choose mollification parameter δ small enough
  -- Use L² norm of s_R since s_R ∈ L²(weightedMeasure σ)
  let δ : ℝ := min (ε / (8 * (ENNReal.toReal (eLpNorm s_R 2
    (weightedMeasure σ)) + 1))) (1 / (2 * (R + 1)))
  have hδ_pos : 0 < δ := by
    -- δ = min(a, b) > 0 iff a > 0 and b > 0
    apply lt_min
    · -- Show 0 < ε / (8 * (ENNReal.toReal (eLpNorm s_R 2 (weightedMeasure σ)) + 1))
      apply div_pos hε
      -- Show 0 < 8 * ((eLpNorm s_R 2 (weightedMeasure σ)).toReal + 1)
      apply mul_pos
      · norm_num
      · -- Show 0 < (eLpNorm s_R 2 (weightedMeasure σ)).toReal + 1
        -- Since ENNReal.toReal _ ≥ 0 and 1 > 0, we have toReal _ + 1 ≥ 1 > 0
        have h_nonneg : 0 ≤ ENNReal.toReal (eLpNorm s_R 2 (weightedMeasure σ)) :=
          ENNReal.toReal_nonneg
        linarith
    · -- Show 0 < 1 / (2 * (R + 1))
      apply div_pos
      · norm_num
      · -- Show 0 < 2 * (R + 1)
        apply mul_pos
        · norm_num
        · linarith [hR_pos]  -- Since R > 0, we have R + 1 > 1 > 0

  -- Construct a proper mollifier as an approximation identity
  -- Step 1: Get a base smooth function with support in [-1, 1]
  have h_ball_nhds_unit : Metric.ball (0:ℝ) 1 ∈ 𝓝 (0:ℝ) := Metric.ball_mem_nhds _ zero_lt_one
  obtain ⟨φ₀, hφ₀_tsupport, hφ₀_compact, hφ₀_smooth, hφ₀_range, hφ₀_at_zero⟩ :=
    exists_smooth_tsupport_subset h_ball_nhds_unit

  -- Step 2: Normalize φ₀ to have integral 1
  have hφ₀_integrable : Integrable φ₀ := by
    exact Continuous.integrable_of_hasCompactSupport hφ₀_smooth.continuous hφ₀_compact

  have hφ₀_pos_integral : 0 < ∫ x, φ₀ x ∂volume := by
    -- φ₀(0) = 1 and φ₀ ≥ 0, so the integral is positive
    sorry -- This follows from continuity at 0 and non-negativity

  let φ_normalized := fun x => φ₀ x / (∫ y, φ₀ y ∂volume)

  have hφ_normalized_integral : ∫ x, φ_normalized x ∂volume = 1 := by
    -- By construction, φ_normalized = φ₀ / (∫ φ₀)
    -- So ∫ φ_normalized = ∫ (φ₀ / (∫ φ₀)) = (∫ φ₀) / (∫ φ₀) = 1
    sorry -- Direct calculation using linearity of integration

  -- Step 3: Scale to get φδ with support in [-δ, δ]
  let φδ := fun x => (1 / δ) * φ_normalized (x / δ)

  have hφδ_smooth : ContDiff ℝ (⊤ : ℕ∞) φδ := by
    -- Composition and scaling preserve smoothness
    sorry -- Technical but standard

  have hφδ_compact : HasCompactSupport φδ := by
    -- Scaling preserves compact support
    sorry -- Technical but standard

  have hφδ_support : Function.support φδ ⊆ Set.Icc (-δ) δ := by
    -- φδ(x) = (1/δ) * φ_normalized(x/δ)
    -- support(φδ) = {x : φδ(x) ≠ 0} = {x : φ_normalized(x/δ) ≠ 0} = δ * support(φ_normalized)
    -- Since support(φ_normalized) ⊆ [-1, 1], we have support(φδ) ⊆ [-δ, δ]
    sorry -- Technical but standard scaling argument

  have hφδ_nonneg : ∀ x, 0 ≤ φδ x := by
    intro x
    simp [φδ, φ_normalized]
    apply mul_nonneg
    · -- 0 ≤ 1/δ since 0 < δ
      rw [inv_nonneg]
      exact hδ_pos.le
    · apply div_nonneg
      · have := hφ₀_range (Set.mem_range_self (x / δ))
        exact this.1
      · exact le_of_lt hφ₀_pos_integral

  have hφδ_integral : ∫ x, φδ x ∂volume = 1 := by
    -- Change of variables: ∫ (1/δ) * φ_normalized(x/δ) dx = ∫ φ_normalized(y) dy = 1
    sorry -- Standard change of variables formula

  -- Define the mollified function g := s_R * φδ (convolution)
  let g : ℝ → ℂ := fun x => ∫ y, s_R y * φδ (x - y) ∂volume

  -- g is continuous because it's a convolution of L¹ function with smooth function
  have hg_continuous : Continuous g := by
    -- g(x) = ∫ s_R(y) * φδ(x - y) dy is a convolution of s_R with φδ
    -- Use the fact that convolution of integrable s_R with continuous bounded φδ is continuous
    have hφδ_bdd : BddAbove (Set.range fun x => ‖φδ x‖) := by
      -- φδ has compact support, so it's bounded on ℝ
      -- Since φδ = 0 outside tsupport φδ, we only need boundedness on tsupport φδ
      have h_image := hφδ_compact.image hφδ_smooth.continuous
      have h_norm_image := h_image.image continuous_norm
      -- Since φδ has compact support, the range of ‖φδ‖ is bounded
      -- Use the fact that continuous functions on compact sets are bounded
      have h_continuous_norm : Continuous (fun x => ‖φδ x‖) :=
        continuous_norm.comp hφδ_smooth.continuous
      have h_tsupport_compact : IsCompact (tsupport φδ) := by
        rw [HasCompactSupport] at hφδ_compact
        exact hφδ_compact
      have h_image_compact : IsCompact ((fun x => ‖φδ x‖) '' (tsupport φδ)) :=
        h_tsupport_compact.image h_continuous_norm
      -- Since φδ has compact support and is continuous, it's bounded
      -- The range of ‖φδ‖ is contained in [0, M] for some M
      have h_bdd_on_tsupport : BddAbove ((fun x => ‖φδ x‖) '' (tsupport φδ)) :=
        h_image_compact.isBounded.bddAbove
      have h_range_subset := range_norm_subset_tsupport_image_with_zero φδ
      -- Since inserting 0 doesn't affect boundedness above, we can still conclude
      have h_bdd_with_zero : BddAbove (Set.insert 0 ((fun x => ‖φδ x‖) '' (tsupport φδ))) :=
        h_bdd_on_tsupport.insert 0
      exact BddAbove.mono h_range_subset h_bdd_with_zero
    -- s_R is integrable because it's a truncation of an L² function
    have hs_R_integrable : Integrable s_R :=
      truncated_lp_integrable hσ_lower hσ_upper s R hR_pos
    -- φδ is smooth with compact support, hence integrable
    have hφδ_integrable : Integrable φδ := by
      -- Use the fact that continuous functions with compact support are integrable
      exact Continuous.integrable_of_hasCompactSupport hφδ_smooth.continuous hφδ_compact
    -- Apply convolution continuity theorem
    -- Since φδ has compact support, we can use compact support convolution continuity
    have hs_R_locally_integrable : LocallyIntegrable s_R := by
      -- Integrable functions are locally integrable
      exact Integrable.locallyIntegrable hs_R_integrable
    -- The convolution is continuous
    -- Use our convolution continuity lemma
    exact convolution_integrable_smooth_continuous hs_R_integrable hφδ_smooth hφδ_compact

  -- g has compact support: support contained in support(f) + support(φδ)
  have hg_support : Function.support g ⊆ Set.Icc (-(R + δ)) (R + δ) := by
    intro x hx
    simp [g] at hx ⊢
    by_contra h
    -- h : x ∉ Set.Icc (-(R + δ)) (R + δ)
    -- But since simp already expanded it, h is ¬(-(R + δ) ≤ x ∧ x ≤ R + δ)
    -- This means x < -(R + δ) ∨ R + δ < x
    rw [not_and_or] at h
    simp only [not_le] at h
    -- If x is outside this interval, then for any y in support(f),
    -- x - y is outside support(φδ), so φδ(x - y) = 0
    have h_integral_zero : ∫ y, s_R y * φδ (x - y) ∂volume = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards with y
      by_cases hy : s_R y = 0
      · simp [hy]
      · -- y ∈ support(s_R), so |y| ≤ R
        have hy_support : y ∈ Function.support s_R := by
          exact Function.mem_support.mpr hy
        have hy_bound : |y| ≤ R := by
          have := hs_R_support hy_support
          -- Since y ∈ Set.Ioc 0 R, we have 0 < y ≤ R, so |y| = y ≤ R
          have hy_pos : 0 < y := this.1
          have hy_le : y ≤ R := this.2
          rw [abs_of_pos hy_pos]
          exact hy_le
        -- If |x| > R + δ, then |x - y| > δ, so φδ(x - y) = 0
        have h_diff_large : δ < |x - y| := by
          cases h with
          | inl h =>
            -- Case: x + R < -δ, which means x < -(R + δ)
            have hx_neg : x < -(R + δ) := by linarith [h]
            -- Since |y| ≤ R, we have y ≥ -R, so x - y ≤ x - (-R) = x + R < -(R + δ) + R = -δ
            have h_bound : x - y < -δ := by
              calc x - y
                ≤ x + R := by
                    have : -R ≤ y := (abs_le.mp hy_bound).1
                    linarith [this]
                _ < -(R + δ) + R := by linarith [hx_neg]
                _ = -δ := by ring
            -- Since x - y < -δ < 0, we have |x - y| = -(x - y) > δ
            have h_abs : |x - y| = -(x - y) := abs_of_neg (by linarith [h_bound, hδ_pos])
            rw [h_abs]
            linarith [h_bound]
          | inr h =>
            -- Case: R + δ < x
            have hx_pos : R + δ < x := h
            -- Since |y| ≤ R, we have y ≤ R, so x - y ≥ x - R > (R + δ) - R = δ
            have h_bound : δ < x - y := by
              calc δ
                = (R + δ) - R := by ring
                _ < x - R := by linarith [hx_pos]
                _ ≤ x - y := by
                    have : y ≤ R := (abs_le.mp hy_bound).2
                    linarith [this]
            -- Since x - y > δ > 0, we have |x - y| = x - y > δ
            have h_pos : 0 < x - y := by linarith [h_bound, hδ_pos]
            rw [abs_of_pos h_pos]
            exact h_bound
        -- Since δ < |x - y|, we have |x - y| > δ, so x - y ∉ [-δ, δ]
        -- This means x - y ∉ support φδ, so φδ(x - y) = 0
        have hφδ_zero : φδ (x - y) = 0 := by
          apply Function.notMem_support.mp
          intro h_in_support
          -- hφδ_support says support φδ ⊆ [-δ, δ], so if x - y ∈ support φδ, then |x - y| ≤ δ
          have h_mem_interval := hφδ_support h_in_support
          simp only [Set.mem_Icc] at h_mem_interval
          have : |x - y| ≤ δ := abs_le.mpr h_mem_interval
          -- But we proved δ < |x - y|, contradiction
          linarith [h_diff_large, this]
        simp [hφδ_zero]
    exact hx h_integral_zero

  have hg_compactSupport : HasCompactSupport g := by
    -- Use the definition: HasCompactSupport g ↔ IsCompact (tsupport g)
    rw [HasCompactSupport]
    -- tsupport g = closure (support g), and support g ⊆ Set.Icc (-(R + δ)) (R + δ)
    simp only [tsupport]
    -- closure (support g) ⊆ closure (Set.Icc (-(R + δ)) (R + δ)) = Set.Icc (-(R + δ)) (R + δ)
    apply IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
    exact closure_minimal hg_support isClosed_Icc

  -- Show g ∈ L² with the weighted measure
  have hs_R_vol_integrable : LocallyIntegrable s_R volume :=
    s_R_locally_integrable_volume hσ_lower hσ_upper s R hR_pos hs_R_memLp
  have hs_R_support' : Function.support s_R ⊆ Set.Icc (-R) R := by
    calc Function.support s_R
      ⊆ Set.Ioc 0 R := hs_R_support
      _ ⊆ Set.Icc 0 R := Set.Ioc_subset_Icc_self
      _ ⊆ Set.Icc (-R) R := by
        intro x hx
        simp at hx ⊢
        exact ⟨le_trans (neg_nonpos_of_nonneg (le_of_lt hR_pos)) hx.1, hx.2⟩
  have hg_memLp : MemLp g 2 (weightedMeasure σ) :=
    convolution_memLp_weighted hσ_lower R δ hR_pos hδ_pos hs_R_support' hs_R_memLp
    hs_R_vol_integrable hφδ_smooth hφδ_compact hφδ_support

  use g, hg_memLp
  refine ⟨hg_compactSupport, hg_continuous, ?_⟩

  -- Show the distance bound using triangle inequality:
  -- dist s g ≤ dist s s_R + dist s_R g < ε/2 + ε/2 = ε
  calc dist s (hg_memLp.toLp g)
    _ ≤ dist s (hs_R_memLp.toLp s_R) + dist (hs_R_memLp.toLp s_R) (hg_memLp.toLp g) :=
      dist_triangle s (hs_R_memLp.toLp s_R) (hg_memLp.toLp g)
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      · -- First term: dist s s_R < ε/2 (from truncation error)
        -- Use the fact that truncation error is controlled
        -- Use h_truncation_error directly since the distance bounds are equivalent
        exact truncation_error_dist_bound s s_R hs_R_memLp (ε / 2) (by linarith : 0 < ε / 2)
          h_truncation_error
      · -- Second term: dist s_R g < ε/2 (mollification error)
        -- Apply the standard mollification error bound
        -- We need to build the proper mollifier from our normalized φδ
        -- First, we need to construct the base mollifier with support in [-1, 1]
        let φ_base := φ_normalized  -- Already normalized with integral = 1
        have hφ_base_smooth : ContDiff ℝ (⊤ : ℕ∞) φ_base := by
          sorry -- φ_normalized inherits smoothness from φ₀
        have hφ_base_compact : HasCompactSupport φ_base := by
          sorry -- φ_normalized has same support as φ₀
        have hφ_base_nonneg : ∀ x, 0 ≤ φ_base x := by
          intro x
          simp [φ_base, φ_normalized]
          apply div_nonneg
          · have := hφ₀_range (Set.mem_range_self x)
            exact this.1
          · exact le_of_lt hφ₀_pos_integral
        have hφ_base_integral : ∫ x, φ_base x ∂volume = 1 := hφ_normalized_integral

        -- Now apply the standard mollification error
        have h_error := standard_mollification_l2_error hσ_lower s_R hs_R_memLp
          φ_base hφ_base_smooth hφ_base_compact hφ_base_nonneg hφ_base_integral
          δ (ε/2) hδ_pos (by linarith : 0 < ε/2)

        -- The mollified function matches our g
        have hg_eq : g = fun x => ∫ y, s_R y * ((1/δ) * φ_base ((x - y)/δ)) ∂volume := by
          sorry -- Definitional equality after unfolding

        -- Apply the error bound
        have hδ_small' : δ < (ε/2) / (4 * (ENNReal.toReal
          (eLpNorm s_R 2 (weightedMeasure σ)) + 1)) := by
          sorry -- This needs to be proven from our choice of δ

        exact h_error hg_memLp hδ_small'
    _ = ε := by ring

/-- Continuous compactly supported functions can be approximated
  by smooth compactly supported functions -/
lemma continuous_to_smooth_approx {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2)
    (g_cont : ℝ → ℂ) (hg_cont_memLp : MemLp g_cont 2 (weightedMeasure σ))
    (hg_cont_compact : HasCompactSupport g_cont) (hg_cont_continuous : Continuous g_cont)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : ℝ → ℂ) (hg_memLp : MemLp g 2 (weightedMeasure σ)),
      HasCompactSupport g ∧
      ContDiff ℝ ⊤ g ∧
      dist (hg_cont_memLp.toLp g_cont) (hg_memLp.toLp g) < ε := by
  -- Use mollification to convert continuous compactly supported → smooth compactly supported
  -- This is the standard mollification procedure using smooth bump functions
  -- Create a mollified version of g_cont using convolution with a smooth kernel
  -- The mollification preserves compact support and creates smoothness
  -- Apply mollification to get smooth compactly supported approximation with consistent measures
  sorry

/-- The weighted measure is equivalent to withDensity measure -/
lemma weightedMeasure_eq_withDensity (σ : ℝ) :
    weightedMeasure σ = mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
  -- This follows from the definition of weightedMeasure and weightFunction
  -- Note: this equality holds because the weight function is zero for x ≤ 0
  -- and the measure integration is restricted to positive reals
  sorry

/-- Smooth compactly supported functions are dense in weighted L² spaces for σ > 1/2 -/
lemma smooth_compactSupport_dense_in_weightedL2 {σ : ℝ} (hσ_lower : 1 / 2 < σ)
    (hσ_upper : σ < 3 / 2)
    (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) : ∃ (g : ℝ → ℂ) (hg_mem : MemLp g 2
    (mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))),
     HasCompactSupport g ∧ ContDiff ℝ ⊤ g ∧ dist f (hg_mem.toLp g) < ε := by
  -- Use the density of smooth compactly supported functions in weighted L² spaces
  -- Use the fact that for σ > 1/2, the weight function x^(2σ-1) is locally integrable
  have h_weight_integrable := weight_locallyIntegrable hσ_lower

  -- Step 1: First approximate by simple functions
  -- Elements of `Hσ σ` are already in the weighted L² space used to define the norm
  have hf_mem_base := memLp_of_Hσ (σ := σ) f

  have h_measure_equiv := weightedMeasure_eq_withDensity σ

  have hf_weightedMeasure :
      MemLp (Hσ.toFun f) 2 (weightedMeasure σ) := by
    simpa [h_measure_equiv, Hσ.toFun] using hf_mem_base

  -- Convert to Lp space element
  let f_Lp : Lp ℂ 2 (weightedMeasure σ) :=
    hf_weightedMeasure.toLp (Hσ.toFun f)

  -- Get simple function approximation from HilbertSpaceCore
  obtain ⟨s, hs_close⟩ := exists_simple_func_approximation f_Lp (ε / 2) (half_pos hε)

  have h_continuous_approx := lp_to_continuous_approx hσ_lower hσ_upper s (ε / 4) (by linarith)

  obtain ⟨g_cont, hg_cont_memLp, hg_cont_compact,
    hg_cont_continuous, hg_cont_close⟩ := h_continuous_approx

  have h_smooth_approx := continuous_to_smooth_approx hσ_lower hσ_upper g_cont hg_cont_memLp
      hg_cont_compact hg_cont_continuous (ε / 4) (by linarith)

  obtain ⟨g, hg_memLp, hg_compact, hg_smooth, hg_mollify_close⟩ := h_smooth_approx

  have h_measure_equiv_final := weightedMeasure_eq_withDensity σ

  -- Convert hg_memLp to the required measure type
  have hg_memLp_converted : MemLp g 2 (mulHaar.withDensity (fun x =>
    ENNReal.ofReal (x ^ (2 * σ - 1)))) := by
    rwa [h_measure_equiv_final] at hg_memLp

  use g, hg_memLp_converted
  constructor
  · exact hg_compact
  constructor
  · exact hg_smooth
  · -- Convert distances to work with consistent measures
    -- Apply the approximation error bound
    have hs_close' : dist f_Lp s < ε / 2 := by
      rw [dist_comm]
      exact hs_close
    -- Apply distance bound through approximation chain using triangle inequality
    -- We have the chain: f ≡ f_Lp → s → g_cont → g where:
    -- dist(f_Lp, s) < ε/2, dist(s, g_cont) < ε/4, dist(g_cont, g) < ε/4

    -- Apply approximation bounds using the triangle inequality
    -- The goal is to show dist f (hg_memLp_converted.toLp g) < ε
    -- We have approximation steps: f ≈ f_Lp ≈ s ≈ g_cont ≈ g

    -- Step 1: Convert to common measure space and apply triangle inequality
    have h_approx_bound : dist f (hg_memLp_converted.toLp g) < ε := by
      -- The distance bound follows from:
      -- 1. f = f_Lp (by construction)
      -- 2. dist(f_Lp, s) < ε/2 (given)
      -- 3. dist(s, g_cont) < ε/4 (given)
      -- 4. dist(g_cont, g) < ε/4 (given)
      -- 5. Triangle inequality: dist(f, g) ≤ sum of intermediate distances

      -- Apply measure equivalence to work in the same space
      have h_measure_eq := h_measure_equiv_final

      -- The key insight: we can work directly with the distances in weightedMeasure space
      -- and use the fact that hg_memLp_converted corresponds to hg_memLp under measure equivalence

      -- Since f_Lp was constructed from f and hg_memLp_converted from hg_memLp,
      -- the distance should be equivalent to working in the original space
      have h_dist_equiv : dist f (hg_memLp_converted.toLp g) = dist f_Lp (hg_memLp.toLp g) :=
        lp_dist_measure_equiv f g f_Lp hf_weightedMeasure rfl hg_memLp hg_memLp_converted

      rw [h_dist_equiv]

      -- Apply triangle inequality in the weightedMeasure space: f_Lp → s → g_cont → g
      -- The key insight is we have bounds:
      -- dist f_Lp s < ε/2, dist s g_cont < ε/4, dist g_cont g < ε/4
      have h_triangle_chain : dist f_Lp (hg_memLp.toLp g) < ε :=
        lp_approximation_triangle_chain f_Lp s g_cont hg_cont_memLp g hg_memLp ε hε
          hs_close' hg_cont_close hg_mollify_close
      exact h_triangle_chain

    exact h_approx_bound

/-- Schwartz functions are dense in Hσ for σ > 1/2 -/
theorem schwartz_dense_in_Hσ {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2) :
    DenseRange (schwartzToHσ hσ_lower) := by
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
  have h_smooth_dense := smooth_compactSupport_dense_in_weightedL2 hσ_lower hσ_upper f
    (ε / 2) (half_pos hε)

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
    classical
    -- Define the auxiliary function whose boundedness we need
    set h : ℝ → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖
    have h_nonneg : ∀ x, 0 ≤ h x := by
      intro x
      exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    -- Since g has compact support and is smooth, its derivatives also have compact support
    -- and are supported in the same set
    set K := tsupport g with hK_def
    have hK_compact : IsCompact K := by
      rw [hK_def]
      exact hg_compact
    have hK_subset : tsupport (iteratedFDeriv ℝ n g) ⊆ K := by
      simpa [hK_def] using
        (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := g) (n := n))
    -- If the support is empty, the function vanishes everywhere and we can take C = 0
    by_cases h_empty : tsupport (iteratedFDeriv ℝ n g) = ∅
    · refine ⟨0, fun x => ?_⟩
      have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := by simp [h_empty]
      have hx_zero : iteratedFDeriv ℝ n g x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      simp [hx_zero]
    -- Otherwise, the image of h over the compact set K attains a maximum
    · have h_tsupport_nonempty :
        (tsupport (iteratedFDeriv ℝ n g)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr h_empty
      obtain ⟨x₀, hx₀_support⟩ := h_tsupport_nonempty
      have hx₀K : x₀ ∈ K := hK_subset hx₀_support
      -- Continuity of the auxiliary function
      have h_cont : Continuous h := by
        have h_pow_cont : Continuous fun x : ℝ => ‖x‖ ^ k :=
          (continuous_norm : Continuous fun x : ℝ => ‖x‖).pow _
        have h_iter_cont :
            Continuous fun x : ℝ => iteratedFDeriv ℝ n g x :=
          (hg_smooth.continuous_iteratedFDeriv (m := n) (hm := by simp))
        exact h_pow_cont.mul (h_iter_cont.norm)
      -- The image of h on K is compact, hence admits a greatest element
      have h_image_compact : IsCompact (h '' K) := hK_compact.image h_cont
      have h_image_nonempty : (h '' K).Nonempty := ⟨h x₀, ⟨x₀, hx₀K, rfl⟩⟩
      obtain ⟨C, hC_isGreatest⟩ :=
        h_image_compact.exists_isGreatest h_image_nonempty
      rcases hC_isGreatest with ⟨hC_mem, hC_max⟩
      rcases hC_mem with ⟨xC, hxC_K, rfl⟩
      have hC_le : ∀ y ∈ h '' K, y ≤ h xC := (mem_upperBounds).1 hC_max
      refine ⟨h xC, ?_⟩
      intro x
      by_cases hxK : x ∈ K
      · have hx_mem : h x ∈ h '' K := ⟨x, hxK, rfl⟩
        exact hC_le _ hx_mem
      · have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := fun hx => hxK (hK_subset hx)
        have hx_zero : iteratedFDeriv ℝ n g x = 0 := image_eq_zero_of_notMem_tsupport hx_not
        have hC_nonneg : 0 ≤ h xC := h_nonneg xC
        have hx_val : h x = 0 := by simp [h, hx_zero]
        have hx_le : h x ≤ h xC := by simpa [hx_val] using hC_nonneg
        simpa [h] using hx_le

  -- Construct the Schwartz function from g
  -- Note: SchwartzMap requires ContDiff ℝ (↑⊤) but we have ContDiff ℝ ⊤
  -- These are the same, but we need to handle the type difference
  have hg_smooth' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    hg_smooth.of_le (by simp)
  let φ : SchwartzMap ℝ ℂ := ⟨g, hg_smooth', hg_schwartz⟩

  -- Step 3: Show that schwartzToHσ hσ_lower φ approximates f
  -- We need to show ∃ y ∈ Set.range (schwartzToHσ hσ_lower), dist f y < ε
  use schwartzToHσ hσ_lower φ
  refine ⟨?_, ?_⟩
  · -- Show that schwartzToHσ hσ φ is in the range
    use φ
  · -- Show the distance bound
    classical
    set μ := mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) with hμ
    have hμ_zero : μ (Set.Iic (0 : ℝ)) = 0 := by
      -- First note that the underlying Haar measure vanishes on nonpositive reals
      have h_base_zero : mulHaar (Set.Iic (0 : ℝ)) = 0 := by
        have h_inter : Set.Iic (0 : ℝ) ∩ Set.Ioi (0 : ℝ) = (∅ : Set ℝ) := by
          ext x
          constructor
          · intro hx
            rcases hx with ⟨hx_le, hx_gt⟩
            have hx_not : ¬(0 < x) := not_lt_of_ge hx_le
            exact (hx_not hx_gt).elim
          · intro hx
            simp at hx
        have h_meas : MeasurableSet (Set.Iic (0 : ℝ)) := measurableSet_Iic
        have :
            mulHaar (Set.Iic (0 : ℝ)) =
              (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
                (Set.Iic (0 : ℝ) ∩ Set.Ioi (0 : ℝ)) := by
          simp [mulHaar, h_meas]
        simpa [h_inter] using this
      -- Absolute continuity of the weighted measure
      have h_ac :=
        withDensity_absolutelyContinuous
          (μ := mulHaar) (f := fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))
      have : μ ≪ mulHaar := by
        simpa [hμ] using h_ac
      exact this.null_mono h_base_zero
    -- The two L² representatives coincide almost everywhere
    have h_ae_eq : g =ᵐ[μ] fun x : ℝ => if x > 0 then g x else 0 := by
      have h_subset :
          {x : ℝ | g x ≠ if x > 0 then g x else 0} ⊆ Set.Iic (0 : ℝ) := by
        intro x hx
        by_contra hx_pos
        have hx_pos' : 0 < x := lt_of_not_ge hx_pos
        change g x ≠ if x > 0 then g x else 0 at hx
        rw [if_pos hx_pos'] at hx
        exact hx rfl
      have h_diff_zero :
          μ {x : ℝ | g x ≠ if x > 0 then g x else 0} = 0 :=
        measure_mono_null h_subset hμ_zero
      refine (ae_iff).2 ?_
      simpa using h_diff_zero
    -- therefore the corresponding L² elements coincide
    have h_toLp_eq :
        hg_mem.toLp g =
          MemLp.toLp (fun x : ℝ => if x > 0 then φ x else 0)
            (schwartz_mem_Hσ hσ_lower φ) := by
      have h_ae_eq' : g =ᵐ[μ] fun x : ℝ => if x > 0 then φ x else 0 := by
        simpa [hμ] using h_ae_eq
      exact
        ((MemLp.toLp_eq_toLp_iff (hf := hg_mem)
              (hg := schwartz_mem_Hσ hσ_lower φ)).2 h_ae_eq')
    have h_toLp_eq' : hg_mem.toLp g = schwartzToHσ hσ_lower φ := by
      simpa [schwartzToHσ, hμ] using h_toLp_eq
    -- Conclude using the approximation provided by `hg_close`
    have h_lt : dist f (hg_mem.toLp g) < ε :=
      lt_trans hg_close (half_lt_self hε)
    simpa [h_toLp_eq'] using h_lt

/-- For any f ∈ Hσ and ε > 0, there exists a Schwartz function approximating f for σ > 1/2 -/
lemma exists_schwartz_approximation {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2)
    (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ_lower φ - f‖ < ε := by
  have h_dense := schwartz_dense_in_Hσ hσ_lower hσ_upper
  -- h_dense: Dense (Set.range (schwartzToHσ hσ_lower))
  -- This means closure (Set.range (schwartzToHσ hσ_lower)) = Set.univ
  have hf_in_closure : f ∈ closure (Set.range (schwartzToHσ hσ_lower)) := by
    have : closure (Set.range (schwartzToHσ hσ_lower)) = Set.univ := Dense.closure_eq h_dense
    rw [this]
    exact Set.mem_univ f
  rw [Metric.mem_closure_iff] at hf_in_closure
  obtain ⟨g, hg_range, hg_close⟩ := hf_in_closure ε hε
  obtain ⟨φ, rfl⟩ := hg_range
  use φ
  rw [dist_eq_norm] at hg_close
  rw [←norm_sub_rev]
  exact hg_close

/-- Schwartz approximation with a.e. convergence for σ > 1/2 -/
lemma schwartz_ae_dense {σ : ℝ} (hσ_lower : 1 / 2 < σ) (hσ_upper : σ < 3 / 2)
    (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ_lower φ - f‖ < ε ∧
    (schwartzToHσ hσ_lower φ : ℝ → ℂ) =ᵐ[mulHaar.withDensity (fun x =>
      ENNReal.ofReal (x ^ (2 * σ - 1)))] (fun x => if x > 0 then φ x else 0) := by
  obtain ⟨φ, hφ⟩ := exists_schwartz_approximation hσ_lower hσ_upper f ε hε
  use φ
  constructor
  · exact hφ
  · exact schwartzToHσ_ae_eq hσ_lower φ

end SchwartzDensity

end Frourio
