import Frourio.Analysis.MellinBasic
import Frourio.Analysis.HilbertSpaceCore
import Frourio.Analysis.SchwartzDensity.SchwartzDensityCore0
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

/-- The weighted measure is finite on compact sets for σ > 1/2 -/
lemma weightedMeasure_finite_on_compact {σ : ℝ} (hσ : 1 / 2 < σ) {K : Set ℝ}
    (hK_compact : IsCompact K) :
    weightedMeasure σ K < ∞ := by
  classical
  set μ := weightedMeasure σ
  have h_exp_neg : -1 < 2 * σ - 2 := by
    linarith [hσ]
  -- Step 1: the weighted measure of (0,1] is finite.
  have h_unit_lt : μ (Set.Ioc (0 : ℝ) 1) < ∞ := by
    have h_subset : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun x hx => hx.1
    have h_inter :
        Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 :=
      Set.inter_eq_left.mpr h_subset
    have h_apply :=
      weightedMeasure_apply (σ := σ) (s := Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
    have hμ_eq :
        μ (Set.Ioc (0 : ℝ) 1) =
          ∫⁻ x in Set.Ioc (0 : ℝ) 1,
            ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
      simpa [μ, h_inter] using h_apply
    set ν := volume.restrict (Set.Ioc (0 : ℝ) 1)
    have h_integrable_on :
        IntegrableOn (fun x : ℝ => x ^ (2 * σ - 2))
          (Set.Ioc (0 : ℝ) 1) volume := by
      have h_int :=
        intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
          (r := 2 * σ - 2) h_exp_neg
      have :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
            (a := (0 : ℝ)) (b := 1) (by norm_num)
            (f := fun x : ℝ => x ^ (2 * σ - 2))).mp h_int
      simpa using this
    have h_integrable :
        Integrable (fun x : ℝ => x ^ (2 * σ - 2)) ν := by
      simpa [IntegrableOn, ν] using h_integrable_on
    have h_lintegral_lt :
        ∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 2)) ∂ν < ∞ :=
      (Integrable.lintegral_lt_top h_integrable)
    have hμ_eq' :
        μ (Set.Ioc (0 : ℝ) 1) =
          ∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 2)) ∂ν := by
      simpa [ν] using hμ_eq
    simpa [hμ_eq'] using h_lintegral_lt
  -- Step 2: deduce finiteness on arbitrary bounded positive intervals.
  have h_interval :
      ∀ R : ℝ, 0 ≤ R → μ (Set.Ioc (0 : ℝ) R) < ∞ := by
    intro R hR_nonneg
    by_cases hR_nonpos : R ≤ 0
    · have h_empty : Set.Ioc (0 : ℝ) R = (∅ : Set ℝ) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx_le_zero : x ≤ 0 := hx.2.trans hR_nonpos
        exact (not_le_of_gt hx.1) hx_le_zero
      simp [μ, h_empty]
    · have hR_pos : 0 < R := lt_of_not_ge hR_nonpos
      by_cases hR_le_one : R ≤ (1 : ℝ)
      · have h_subset : Set.Ioc (0 : ℝ) R ⊆ Set.Ioc (0 : ℝ) 1 := by
          intro x hx
          exact ⟨hx.1, hx.2.trans hR_le_one⟩
        have h_le := measure_mono (μ := μ) h_subset
        exact lt_of_le_of_lt h_le h_unit_lt
      · have hR_gt_one : 1 < R := lt_of_not_ge hR_le_one
        set A := Set.Ioc (0 : ℝ) 1
        set B := Set.Ioo (1 / 2 : ℝ) (R + 1)
        have h_subset_union :
            Set.Ioc (0 : ℝ) R ⊆ A ∪ B := by
          intro x hx
          have hx_pos := hx.1
          have hx_le := hx.2
          by_cases hx_le_one : x ≤ (1 : ℝ)
          · exact Or.inl ⟨hx_pos, hx_le_one⟩
          · have hx_gt_one : 1 < x := lt_of_not_ge hx_le_one
            refine Or.inr ?_
            refine ⟨?_, ?_⟩
            · have : (1 / 2 : ℝ) < 1 := by norm_num
              exact this.trans hx_gt_one
            · have hx_lt_R : x ≤ R := hx_le
              have hR_lt : R < R + 1 := lt_add_of_pos_right R zero_lt_one
              exact lt_of_le_of_lt hx_lt_R hR_lt
        have h_le_union := measure_mono (μ := μ) h_subset_union
        have hA_lt : μ A < ∞ := h_unit_lt
        have hB_lt : μ B < ∞ := by
          have h_half_pos : 0 < (1 / 2 : ℝ) := by norm_num
          have h_b_lt : (1 / 2 : ℝ) < R + 1 := by
            have h_half_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
            have h_lt_R : (1 / 2 : ℝ) < R := h_half_lt_one.trans hR_gt_one
            have h_le : R ≤ R + 1 := le_of_lt (lt_add_of_pos_right R zero_lt_one)
            exact lt_of_lt_of_le h_lt_R h_le
          simpa [μ, B] using
            (weightedMeasure_finite_on_bounded (σ := σ)
              (a := (1 / 2 : ℝ)) (b := R + 1)
              h_half_pos h_b_lt)
        have h_union_lt : μ (A ∪ B) < ∞ := by
          have h_union_le := measure_union_le (μ := μ) (s := A) (t := B)
          have h_sum_lt : μ A + μ B < ∞ := by
            simp [ENNReal.add_lt_top, hA_lt, hB_lt]
          exact lt_of_le_of_lt h_union_le h_sum_lt
        exact lt_of_le_of_lt h_le_union h_union_lt
  -- Step 3: use compactness to reduce to a closed ball and conclude.
  have hK_bounded : Bornology.IsBounded K := hK_compact.isBounded
  obtain ⟨R₀, hK_subset₀⟩ := hK_bounded.subset_closedBall (0 : ℝ)
  set R := max R₀ 1
  have hR_nonneg : 0 ≤ R := by
    have : (1 : ℝ) ≤ R := by
      simp [R]
    exact (zero_le_one.trans this)
  have hK_subset : K ⊆ Metric.closedBall (0 : ℝ) R := by
    refine hK_subset₀.trans ?_
    have hR₀_le_R : R₀ ≤ R := by
      simp [R]
    simpa [R] using (Metric.closedBall_subset_closedBall hR₀_le_R)
  have h_inter_ball :
      Metric.closedBall (0 : ℝ) R ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) R := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨hx_ball, hx_pos⟩
      have hx_abs : |x| ≤ R := by
        simpa [Metric.closedBall, Real.dist_eq] using hx_ball
      have hx_le : x ≤ R := by
        have hx_abs_pos : |x| = x :=
          abs_of_pos hx_pos
        simpa [hx_abs_pos] using hx_abs
      exact ⟨hx_pos, hx_le⟩
    · intro hx
      refine ⟨?_, hx.1⟩
      have hx_abs : |x| = x := abs_of_pos hx.1
      have hx_le : x ≤ R := hx.2
      have hx_abs_le : |x| ≤ R := by simpa [hx_abs] using hx_le
      simpa [Metric.closedBall, Real.dist_eq] using hx_abs_le
  have h_inter_ioc :
      Set.Ioc (0 : ℝ) R ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) R :=
    Set.inter_eq_left.mpr (fun x hx => hx.1)
  have h_closedBall_eq :
      μ (Metric.closedBall (0 : ℝ) R) = μ (Set.Ioc (0 : ℝ) R) := by
    have h_ball :=
      weightedMeasure_apply (σ := σ)
        (s := Metric.closedBall (0 : ℝ) R) measurableSet_closedBall
    have h_ioc :=
      weightedMeasure_apply (σ := σ) (s := Set.Ioc (0 : ℝ) R) measurableSet_Ioc
    calc
      μ (Metric.closedBall (0 : ℝ) R)
          = ∫⁻ x in Set.Ioc (0 : ℝ) R,
              ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := by
            simpa [μ, h_inter_ball] using h_ball
      _ = μ (Set.Ioc (0 : ℝ) R) := by
            simpa [μ, h_inter_ioc] using h_ioc.symm
  have h_closedBall_lt : μ (Metric.closedBall (0 : ℝ) R) < ∞ := by
    have h_ioc_lt := h_interval R hR_nonneg
    simpa [h_closedBall_eq] using h_ioc_lt
  have h_le := measure_mono (μ := μ) hK_subset
  exact lt_of_le_of_lt h_le h_closedBall_lt

/-- Convert HasFiniteIntegral and AEStronglyMeasurable to MemLp for p = 2 -/
lemma memLp_of_hasFiniteIntegral_and_aestronglyMeasurable {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_finite : HasFiniteIntegral (fun x => ‖f x‖ ^ 2) μ) :
    MemLp f 2 μ := by
  classical
  have hg_meas : AEStronglyMeasurable (fun x : ℝ => ‖f x‖ ^ 2) μ :=
    (continuous_pow 2).comp_aestronglyMeasurable hf_meas.norm
  have hg_integrable : Integrable (fun x : ℝ => ‖f x‖ ^ 2) μ := ⟨hg_meas, hf_finite⟩
  have h_int_norm : Integrable (fun x : ℝ => ‖f x‖ ^ (2 : ℝ≥0∞).toReal) μ := by
    simpa [ENNReal.toReal_ofNat, pow_two] using hg_integrable
  have h_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
  exact
    (integrable_norm_rpow_iff (μ := μ) (f := f) hf_meas h_zero h_top).1 h_int_norm

/-- For a function with compact support that is dominated a.e. by a constant on its support,
    if the weighted measure of the support is finite, then the function has finite integral -/
lemma hasFiniteIntegral_of_dominated_on_compactSupport {μ : Measure ℝ} {g : ℝ → ℂ} {M : ℝ}
    (h_dominated : ∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ M ^ 2)
    (h_finite_on_support : μ (tsupport g) < ∞) :
    HasFiniteIntegral (fun x => ‖g x‖ ^ 2) μ := by
  classical
  set s := tsupport g
  have hs_meas : MeasurableSet s := (isClosed_tsupport g).measurableSet
  -- Control the integral on the restricted measure `μ.restrict s` using the domination.
  have h_dominated_restrict : ∀ᵐ x ∂μ.restrict s, ‖g x‖ ^ 2 ≤ M ^ 2 :=
    ae_restrict_of_ae h_dominated
  have h_abs_eq : ∀ x, ‖‖g x‖ ^ 2‖ = ‖g x‖ ^ 2 := fun x => by
    have hx : 0 ≤ ‖g x‖ ^ 2 := by
      simp
    simp
  have h_bound : ∀ᵐ x ∂μ.restrict s, ‖‖g x‖ ^ 2‖ ≤ M ^ 2 :=
    h_dominated_restrict.mono fun x hx => by simpa [h_abs_eq x] using hx
  have h_restrict : HasFiniteIntegral (fun x => ‖g x‖ ^ 2) (μ.restrict s) :=
    HasFiniteIntegral.restrict_of_bounded (μ := μ) (s := s)
      (f := fun x => ‖g x‖ ^ 2) (C := M ^ 2) h_finite_on_support h_bound
  -- Relate the integral over `μ` to the integral over `μ.restrict s` via the indicator of `s`.
  have h_indicator_eq :
      (fun x => ‖g x‖ₑ ^ 2) =
        fun x => Set.indicator s (fun y => ‖g y‖ₑ ^ 2) x := by
    funext x
    by_cases hx : x ∈ s
    · simp [hx]
    · have hx0 : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hx, hx0, Set.indicator_of_notMem]
  have h_integral_eq_sq :
      ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ =
        ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ.restrict s := by
    have h_left :
        ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ =
          ∫⁻ x, Set.indicator s (fun y => ‖g y‖ₑ ^ 2) x ∂μ := by
      simpa using
        congrArg (fun f : ℝ → ℝ≥0∞ => ∫⁻ x, f x ∂μ) h_indicator_eq
    have h_right :
        ∫⁻ x, Set.indicator s (fun y => ‖g y‖ₑ ^ 2) x ∂μ =
          ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ.restrict s := by
      simp [lintegral_indicator, hs_meas, s]
    exact h_left.trans h_right
  have h_sq_eq :
      (fun x => ENNReal.ofReal (‖g x‖ ^ 2)) = fun x => ‖g x‖ₑ ^ 2 := by
    funext x
    simp
  have h_integral_eq :
      ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ =
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ.restrict s := by
    simpa [h_sq_eq] using h_integral_eq_sq
  -- Use the finiteness on the restricted measure.
  have h_integral_lt_top :
      ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ < ∞ := by
    have h_restrict_lt :
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ.restrict s < ∞ := by
      simpa [HasFiniteIntegral] using h_restrict
    have h_restrict_sq_lt :
        ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ.restrict s < ∞ := by
      simpa [h_sq_eq] using h_restrict_lt
    have h_sq_lt_top :
        ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ < ∞ := by
      simpa [h_integral_eq_sq] using h_restrict_sq_lt
    simpa [h_sq_eq] using h_sq_lt_top
  -- Express the conclusion in terms of the original integrand.
  have h_abs : ∀ x, ‖(fun x => ‖g x‖ ^ 2) x‖ₑ = ENNReal.ofReal (‖g x‖ ^ 2) := by
    intro x
    have hx : 0 ≤ ‖g x‖ ^ 2 := by
      simp
    have hxnorm : ‖‖g x‖ ^ 2‖ = ‖g x‖ ^ 2 := Real.norm_of_nonneg hx
    simp
  simpa [HasFiniteIntegral, h_abs] using h_integral_lt_top

/-- Convolution of simple function truncation with smooth compact support function is in L² -/
lemma memLp_convolution_simpleFunc_truncation {σ : ℝ} (hσ : 1 / 2 < σ)
    (f_simple : SimpleFunc ℝ ℂ) (φ : ℝ → ℝ) (R δ : ℝ)
    (_ : MemLp (fun x => if |x| ≤ R then f_simple x else 0) 2 (weightedMeasure σ))
    (hφ_smooth : ContDiff ℝ (↑⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_support : Function.support φ ⊆ Set.Icc (-δ) δ)
    (hR_pos : 0 < R) (hδ_pos : 0 < δ) :
    MemLp (fun x => ∫ y, (if |y| ≤ R then f_simple y else 0) * (φ (x - y) : ℂ)) 2
      (weightedMeasure σ) := by
  -- SPECIALIZED APPROACH for simple function truncations
  -- Since f_simple is a SimpleFunc and we truncate it, we have:
  -- 1. The truncated function is bounded and has support in [-R, R]
  -- 2. φ is smooth with compact support in [-δ, δ] and hence integrable
  -- 3. The convolution has support in [-(R+δ), R+δ]
  -- 4. Simple functions are essentially bounded, so the convolution is well-defined
  -- 5. For σ > 1/2, the weighted L² norm can be controlled

  -- Step 1: Show the truncated function is integrable
  let f_trunc : ℝ → ℂ := fun x => if |x| ≤ R then f_simple x else 0
  have hf_trunc_integrable : Integrable f_trunc :=
    simpleFunc_truncation_integrable hσ f_simple R

  -- Step 2: Show φ is integrable (continuous with compact support)
  have hφ_integrable : Integrable φ := by
    exact Continuous.integrable_of_hasCompactSupport hφ_smooth.continuous hφ_compact

  -- Step 3: The convolution is well-defined and continuous
  have h_convolution_continuous :
    Continuous (fun x => ∫ y, f_trunc y * (φ (x - y) : ℂ)) := by
    exact continuous_convolution_integrable_smooth f_trunc φ
      hf_trunc_integrable hφ_smooth hφ_compact

  -- Step 4: The convolution has compact support in [-(R+δ), R+δ]
  have h_convolution_support :
    Function.support (fun x => ∫ y, f_trunc y * (φ (x - y) : ℂ)) ⊆
    Set.Icc (-(R + δ)) (R + δ) := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    by_contra h_not_in_interval
    -- If x is outside [-(R+δ), R+δ], show the integral is zero
    have h_integral_zero : ∫ y, f_trunc y * (φ (x - y) : ℂ) = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards with y
      -- For any y where f_trunc y ≠ 0, we have |y| ≤ R
      -- For such y, if x is outside [-(R+δ), R+δ], then x-y is outside [-δ, δ]
      -- Hence φ(x-y) = 0
      by_cases hy_zero : f_trunc y = 0
      · simp [hy_zero]
      · -- f_trunc y ≠ 0 implies |y| ≤ R
        have hy_bound : |y| ≤ R := by
          simp only [f_trunc] at hy_zero
          by_contra h_not_bound
          have : ¬|y| ≤ R := h_not_bound
          simp [this] at hy_zero
        -- Show φ(x - y) = 0 when x is outside the expected range
        have hφ_zero : φ (x - y) = 0 := by
          apply Function.notMem_support.mp
          intro h_in_support
          have h_support_bound := hφ_support h_in_support
          simp only [Set.mem_Icc] at h_support_bound
          have h_abs_bound : |x - y| ≤ δ := abs_le.mpr h_support_bound
          -- But this contradicts x being outside [-(R+δ), R+δ]
          -- We have |x - y| ≤ δ and |y| ≤ R
          -- This implies |x| ≤ |x - y| + |y| ≤ δ + R = R + δ
          -- So x ∈ [-(R+δ), R+δ], contradicting h_not_in_interval
          have h_triangle : |x| ≤ |x - y| + |y| := by
            have h1 : |x| = |(x - y) + y| := by ring_nf
            rw [h1]
            exact abs_add _ _
          have h_bound : |x| ≤ δ + R := by
            calc |x|
              _ ≤ |x - y| + |y| := h_triangle
              _ ≤ δ + R := add_le_add h_abs_bound hy_bound
          have h_in_interval : x ∈ Set.Icc (-(R + δ)) (R + δ) := by
            rw [Set.mem_Icc]
            constructor
            · linarith [neg_le_abs x, h_bound]
            · linarith [le_abs_self x, h_bound]
          -- We have h_in_interval : x ∈ Set.Icc (-(R + δ)) (R + δ)
          -- But h_not_in_interval : x ∉ Set.Icc (-(R + δ)) (R + δ)
          -- This is a direct contradiction
          exact h_not_in_interval h_in_interval
        simp [hφ_zero]
    exact hx h_integral_zero

  -- Step 5: Apply L² theory for functions with compact support
  -- For σ > 1/2 and compact support, we can bound the weighted L² norm
  have h_convolution_compactSupport : HasCompactSupport
    (fun x => ∫ y, f_trunc y * (φ (x - y) : ℂ)) := by
    rw [HasCompactSupport]
    -- tsupport is the closure of support, which is contained in closure of [-(R+δ), R+δ]
    apply IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
    exact closure_minimal h_convolution_support isClosed_Icc

  -- For continuous functions with compact support, we can apply integrability results
  have h_convolution_integrable : Integrable
    (fun x => ∫ y, f_trunc y * (φ (x - y) : ℂ)) := by
    exact Continuous.integrable_of_hasCompactSupport
      h_convolution_continuous h_convolution_compactSupport

  have h_bounded_interval : tsupport (fun x => ∫ y, f_trunc y * (φ (x - y) : ℂ)) ⊆
    Set.Icc (-(R + δ)) (R + δ) := by
    exact closure_minimal h_convolution_support isClosed_Icc

  have h_memLp : MemLp (fun x => ∫ y, f_trunc y * (φ (x - y) : ℂ)) 2
    (weightedMeasure σ) := by
    -- For continuous functions with compact support, we can bound the L² norm
    -- Since the function has support in [-(R+δ), R+δ], we can integrate over this interval
    let g := fun x => ∫ y, f_trunc y * (φ (x - y) : ℂ)

    -- Step 1: Show g is AEStronglyMeasurable
    have hg_meas : AEStronglyMeasurable g (weightedMeasure σ) := by
      exact Continuous.aestronglyMeasurable h_convolution_continuous

    -- Step 2: Show the L² norm is finite
    have hg_finite : HasFiniteIntegral (fun x => ‖g x‖ ^ 2) (weightedMeasure σ) := by
      -- Since g has compact support in [-(R+δ), R+δ] and is continuous,
      -- we can bound ∫ |g(x)|² * x^(2σ-1) dx over the bounded interval

      -- Get a uniform bound on g over its compact support
      have hg_bounded : ∃ M : ℝ, ∀ x ∈ tsupport g, ‖g x‖ ≤ M := by
        -- Continuous functions on compact sets are bounded
        have htsupport_compact : IsCompact (tsupport g) := h_convolution_compactSupport
        have hg_cont_on : ContinuousOn (fun x => ‖g x‖) (tsupport g) := by
          exact (h_convolution_continuous.continuousOn).norm
        -- Check if the support is nonempty
        by_cases h_empty : (tsupport g).Nonempty
        · -- Nonempty case: use compactness to get maximum
          obtain ⟨x_max, hx_max_mem, hx_max_bound⟩ :=
            htsupport_compact.exists_isMaxOn h_empty hg_cont_on
          use ‖g x_max‖
          intro x hx
          exact hx_max_bound hx
        · -- Empty case: any bound works since there are no points
          use 0
          intro x hx
          exfalso
          exact h_empty ⟨x, hx⟩

      obtain ⟨M, hM_bound⟩ := hg_bounded

      -- For x outside the support, g(x) = 0, so we only integrate over [-(R+δ), R+δ]
      have h_support_subset : tsupport g ⊆ Set.Icc (-(R + δ)) (R + δ) := h_bounded_interval

      -- The integral is bounded by M² times the weighted measure of [-(R+δ), R+δ]
      -- For σ > 1/2, this weighted measure is finite
      -- For functions with compact support, use decomposition into positive parts
      -- The support is in [-(R+δ), R+δ], split into negative and positive parts
      have h_support_decomp : tsupport g ⊆ Set.Icc (-(R + δ)) (R + δ) := h_bounded_interval

      -- For the positive part, use weightedMeasure_finite_on_bounded
      have h_pos_finite : weightedMeasure σ (Set.Ioo (δ/2) (R + δ)) < ∞ := by
        apply weightedMeasure_finite_on_bounded σ (δ/2) (R + δ)
        · linarith [hδ_pos]
        · linarith [hR_pos, hδ_pos]

      -- For continuous functions with compact support in a sigma-finite measure,
      -- the L² integral is finite
      -- Since g has compact support and is continuous, and weightedMeasure is sigma-finite,
      -- we can use the general theory of L^p spaces
      -- The key insight is that g is bounded on its compact support

      -- Show the integral is dominated by a finite measure
      have h_dominated : ∀ᵐ x ∂(weightedMeasure σ), ‖g x‖ ^ 2 ≤ M ^ 2 := by
        filter_upwards with x
        by_cases hx : x ∈ tsupport g
        · have : ‖g x‖ ≤ M := hM_bound x hx
          have h_sq : ‖g x‖ ^ 2 ≤ M ^ 2 := by
            rw [pow_two, pow_two]
            exact mul_self_le_mul_self (norm_nonneg _) this
          exact h_sq
        · have hx_zero : g x = 0 := image_eq_zero_of_notMem_tsupport hx
          simp [hx_zero]
          exact sq_nonneg M

      -- The dominating function has finite integral on the compact support
      have h_finite_on_support : (weightedMeasure σ) (tsupport g) < ∞ := by
        -- Use that weightedMeasure is finite on compact sets for σ > 1/2
        apply weightedMeasure_finite_on_compact hσ
        -- g has compact support, so tsupport g is compact
        -- From the definition of h_convolution_compactSupport, we know tsupport g is compact
        rw [HasCompactSupport] at h_convolution_compactSupport
        exact h_convolution_compactSupport

      -- Apply dominated convergence principle
      -- Since ‖g x‖^2 ≤ M^2 a.e. and g has compact support with finite weighted measure,
      -- the L^2 integral is finite
      exact hasFiniteIntegral_of_dominated_on_compactSupport h_dominated h_finite_on_support

    -- Package the results for MemLp
    -- For p = 2, HasFiniteIntegral (‖g‖^2) μ is equivalent to MemLp g 2 μ
    -- Use the standard conversion
    exact memLp_of_hasFiniteIntegral_and_aestronglyMeasurable hg_meas hg_finite

  -- The convolution equals the target function
  exact h_memLp

/-- eLpNorm equality for Lp element and function difference -/
lemma eLpNorm_lp_function_diff_eq {σ : ℝ} (s : Lp ℂ 2 (weightedMeasure σ))
    (f : ℝ → ℂ) (hf_memLp : MemLp f 2 (weightedMeasure σ)) :
    eLpNorm ((s : ℝ → ℂ) - (hf_memLp.toLp f : ℝ → ℂ)) 2 (weightedMeasure σ) =
    eLpNorm ((s : ℝ → ℂ) - (f : ℝ → ℂ)) 2 (weightedMeasure σ) := by
  -- The coercions are equal ae, so eLpNorms are equal
  -- MemLp.toLp f =ᵐ f, so (s - toLp f) =ᵐ (s - f)
  have h_ae_eq : (hf_memLp.toLp f : ℝ → ℂ) =ᵐ[weightedMeasure σ] f := by
    exact MemLp.coeFn_toLp hf_memLp
  -- Apply ae equality to the difference
  have h_diff_eq : (fun x => (s : ℝ → ℂ) x - (hf_memLp.toLp f : ℝ → ℂ) x) =ᵐ[weightedMeasure σ]
                   (fun x => (s : ℝ → ℂ) x - f x) := by
    filter_upwards [h_ae_eq] with x hx
    simp [hx]
  exact eLpNorm_congr_ae h_diff_eq

/-- Compact intervals have finite weighted measure for σ > 1/2 -/
lemma weightedMeasure_finite_on_interval {σ : ℝ} (hσ : 1 / 2 < σ) (R : ℝ) :
    (weightedMeasure σ) (Set.Icc (-R) R) < ∞ := by
  classical
  -- Closed, bounded intervals are compact in ℝ
  have h_compact : IsCompact (Set.Icc (-R) R) := isCompact_Icc
  exact weightedMeasure_finite_on_compact hσ h_compact

/-- Unbounded level sets of L² simple functions have finite weighted measure for σ > 1/2 -/
lemma simpleFunc_unbounded_levelSet_finite_measure_L2 {σ : ℝ} (_hσ : 1 / 2 < σ)
    (f : SimpleFunc ℝ ℂ) (hf_memL2 : MemLp (f : ℝ → ℂ) 2 (weightedMeasure σ))
    (v : ℂ) (hv_nonzero : v ≠ 0) (_hv_range : v ∈ Set.range (f : ℝ → ℂ))
    (_h_unbounded : ¬∃ R > 0, {x : ℝ | f x = v} ⊆ Set.Icc (-R) R) :
    (weightedMeasure σ) {x : ℝ | f x = v} ≠ ∞ := by
  classical
  set μ := weightedMeasure σ
  set A := ((f : ℝ → ℂ) ⁻¹' {v}) with hA_def
  intro hμA_top
  have hμA_top' : μ A = ∞ := by
    simpa [A, hA_def, Set.preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      using hμA_top
  -- The fiber `A` is measurable since `f` is a simple function.
  have hA_meas : MeasurableSet A := by
    simpa [A, hA_def] using SimpleFunc.measurableSet_fiber f v
  -- Simple functions are (ae strongly) measurable, and the MemLp hypothesis gives
  -- finiteness of the squared-norm lintegral.
  rcases hf_memL2 with ⟨hf_meas, hf_snorm_lt⟩
  -- On the set `A`, the function is constantly equal to `v`, so the squared norm is
  -- constantly `‖v‖₊ ^ 2` there.
  have h_pointwise :
      ∀ x ∈ A, (‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) = (‖v‖₊ : ℝ≥0∞) ^ (2 : ℕ) := by
    intro x hx
    have hx' : f x = v := by
      simpa [A, hA_def, Set.mem_preimage, Set.mem_singleton_iff] using hx
    simp [hx']
  -- Compute the lintegral of `‖f‖²` over the fibre.
  have h_lintegral_A :
      ∫⁻ x in A, (‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂μ = (‖v‖₊ : ℝ≥0∞) ^ (2 : ℕ) * μ A := by
    calc
      ∫⁻ x in A, (‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂μ
          = ∫⁻ x in A, (‖v‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂μ :=
            setLIntegral_congr_fun (μ := μ) hA_meas h_pointwise
      _ = (‖v‖₊ : ℝ≥0∞) ^ (2 : ℕ) * μ A := by
            simp
  -- Since `v ≠ 0`, its squared norm is a positive constant, so the above lintegral is ∞.
  have hv_nnnorm_ne_zero : ‖v‖₊ ≠ 0 := by
    simp [nnnorm_eq_zero, hv_nonzero]
  have hv_pow_ne_zero : (‖v‖₊ : ℝ≥0∞) ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero _ (by simpa using ENNReal.coe_ne_zero.mpr hv_nnnorm_ne_zero)
  have h_lintegral_A_top :
      ∫⁻ x in A, (‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂μ = ∞ := by
    simp [h_lintegral_A, hμA_top', hv_pow_ne_zero]
  -- Deduce that the global squared-norm lintegral is infinite.
  have h_total_integral_top :
      ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂μ = ∞ := by
    have h_le :=
      setLIntegral_le_lintegral (μ := μ)
        (f := fun x => (‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) (s := A)
    have h_top_le : (⊤ : ℝ≥0∞) ≤ ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂μ := by
      simpa [h_lintegral_A_top] using h_le
    simpa [top_le_iff] using h_top_le
  -- Therefore the snorm of `f` at exponent 2 is `∞`, contradicting the MemLp hypothesis.
  have h_eLpNorm_top : eLpNorm (fun x => f x) 2 μ = ∞ := by
    have h_eq :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        (μ := μ) (f := fun x => f x) (p := (2 : ℝ≥0∞))
        (hp_ne_zero := by norm_num) (hp_ne_top := by simp)
    have h_pow :
        (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) = ∞ := by
      simp [h_total_integral_top]
    simpa [h_eq] using h_pow
  -- Contradiction with snorm finiteness furnished by the MemLp assumption.
  have hcontr : False := by
    have hlt := hf_snorm_lt
    simp [h_eLpNorm_top] at hlt
  exact hcontr.elim

lemma simpleFunc_levelSet_tail_measure_vanishing {σ : ℝ} (hσ : 1 / 2 < σ)
    (f : SimpleFunc ℝ ℂ) (hf_memL2 : MemLp (f : ℝ → ℂ) 2 (weightedMeasure σ))
    (v : ℂ) (hv_nonzero : v ≠ 0) (hv_range : v ∈ Set.range (f : ℝ → ℂ)) :
    Filter.Tendsto (fun R => (weightedMeasure σ) {x | f x = v ∧ R < |x|}) Filter.atTop (𝓝 0) := by
  -- With the L² assumption, we can show that tail measures vanish
  -- Key insight: If f ∈ L²(weightedMeasure σ), then:
  -- ∫ |f|² dμ < ∞ implies that for any v ≠ 0,
  -- the level set {x : f(x) = v} has controlled tail behavior

  -- The proof uses:
  -- 1. f ∈ L² ⟹ ∫_{level set} |v|² dμ < ∞
  -- 2. Continuity from above for finite measures
  -- 3. The fact that ⋂_R {x : f(x) = v ∧ |x| > R} = ∅

  set μ := weightedMeasure σ
  set A := {x : ℝ | f x = v} with hA_def

  -- The level set A is measurable
  have hA_measurable : MeasurableSet A := by
    rw [hA_def]
    exact SimpleFunc.measurableSet_fiber f v

  -- The tail sets are nested and decreasing
  have h_nested : ∀ R₁ R₂, R₁ ≤ R₂ →
    {x | f x = v ∧ R₂ < |x|} ⊆ {x | f x = v ∧ R₁ < |x|} := by
    intro R₁ R₂ h_le x hx
    exact ⟨hx.1, lt_of_le_of_lt h_le hx.2⟩

  -- The intersection of all tail sets is empty
  have h_inter_empty : ⋂ R : ℝ, {x | f x = v ∧ R < |x|} = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · intro h_forall
      -- For any x, there exists R > |x|, so x cannot be in all tail sets
      specialize h_forall (|x| + 1)
      have h_contra : |x| < |x| + 1 := by linarith
      exact lt_irrefl |x| (h_contra.trans h_forall.2)
    · intro h_false
      exact False.elim h_false

  -- Apply measure continuity from above
  -- Since μ is finite on A (level sets of simple functions have finite measure),
  -- we can apply continuity from above

  -- First show that A has finite measure
  have hA_finite : μ A ≠ ∞ := by
    -- Level sets of simple functions have finite measure under weighted measures with σ > 1/2
    -- This follows from the fact that f takes only finitely many values
    -- and each level set is measurable with appropriate weight decay

    -- For simple functions, the level set A = {x : f x = v} has a specific structure
    -- Since v ∈ range(f) and v ≠ 0, the set A is non-empty and measurable

    -- The key insight: weighted measures with σ > 1/2 have the property that
    -- any measurable set with appropriate growth bounds has finite measure

    -- Method 1: Use the fact that simple functions have essentially bounded support
    -- or can be decomposed into finitely many pieces, each with controlled measure

    -- For weighted measure μ = weightedMeasure σ, we have:
    -- μ(A) = ∫_A x^(2σ-2) dx (restricted to positive part)
    -- Since σ > 1/2, we have 2σ-2 > -1, so the integral converges

    -- The level set A is either bounded (giving finite measure immediately)
    -- or has a structure that ensures finite measure under the weight function

    by_cases h_bounded : ∃ R > 0, A ⊆ Set.Icc (-R) R
    · -- Case 1: A is bounded
      obtain ⟨R, hR_pos, hR_bound⟩ := h_bounded
      have h_subset : A ⊆ Set.Icc (-R) R := hR_bound
      have h_finite_compact : μ (Set.Icc (-R) R) < ∞ :=
        weightedMeasure_finite_on_interval hσ R
      exact ne_of_lt (measure_mono h_subset |>.trans_lt h_finite_compact)
    · -- Case 2: A is unbounded
      exact simpleFunc_unbounded_levelSet_finite_measure_L2 hσ f hf_memL2
        v hv_nonzero hv_range h_bounded

  -- Apply measure continuity from above
  -- The sequence {x | f x = v ∧ R < |x|} is decreasing and has empty intersection
  -- Since A has finite measure, we can apply continuity from above
  have h_continuity : Filter.Tendsto (fun R => μ {x | f x = v ∧ R < |x|})
      Filter.atTop (𝓝 (μ (⋂ R, {x | f x = v ∧ R < |x|}))) := by
    -- Use MeasureTheory.tendsto_measure_iInter_atTop for decreasing sequences
    apply MeasureTheory.tendsto_measure_iInter_atTop
    · -- The sets are measurable
      intro R
      have h_set_eq : {x | f x = v ∧ R < |x|} = A ∩ {x | R < |x|} := by
        ext x
        simp [A]
      rw [h_set_eq]
      exact (hA_measurable.inter
        (measurableSet_lt measurable_const continuous_abs.measurable)).nullMeasurableSet
    · -- The sets are decreasing (antitone)
      intro R₁ R₂ h_le
      exact h_nested R₁ R₂ h_le
    · -- One of the sets has finite measure
      use 0
      have h_subset : {x | f x = v ∧ 0 < |x|} ⊆ A := by
        intro x hx
        simp [A]
        exact hx.1
      have h_finite : μ {x | f x = v ∧ 0 < |x|} ≠ ∞ := by
        exact ne_of_lt (measure_mono h_subset |>.trans_lt (lt_top_iff_ne_top.mpr hA_finite))
      exact h_finite

  -- Since the intersection is empty, its measure is 0
  rw [h_inter_empty, measure_empty] at h_continuity
  exact h_continuity

/-- L² convergence of tail functions for simple functions -/
lemma simpleFunc_tail_l2_convergence {σ : ℝ} (_hσ : 1 / 2 < σ)
    (f : SimpleFunc ℝ ℂ) (_hf_memLp : MemLp (f : ℝ → ℂ) 2 (weightedMeasure σ))
    (_h_pointwise : ∀ x : ℝ,
      Filter.Tendsto (fun R => if |x| ≤ R then 0 else f x) Filter.atTop (𝓝 0))
    (_h_domination : ∀ R x, ‖if |x| ≤ R then 0 else f x‖ ≤ ‖f x‖)
    (h_tail_measure_vanishing : ∀ v : ℂ, v ≠ 0 → v ∈ Set.range (f : ℝ → ℂ) →
      Filter.Tendsto (fun R => (weightedMeasure σ) {x | f x = v ∧ R < |x|})
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun R => eLpNorm (fun x => if |x| ≤ R then 0 else f x) 2 (weightedMeasure σ))
      Filter.atTop (𝓝 0) := by
  classical
  set μ := weightedMeasure σ
  set tailSet : ℝ → Set ℝ := fun R => {x : ℝ | R < |x|}
  set gVal : ℂ → ℝ≥0∞ := fun z => (‖z‖ₑ) ^ (2 : ℕ)
  set gSimple := f.map gVal

  have h_tail_measurable : ∀ R : ℝ, MeasurableSet (tailSet R) := fun R =>
    (measurableSet_lt measurable_const continuous_abs.measurable)

  -- Express the squared norm of the tail truncation using an indicator of the tail set
  have h_indicator (R : ℝ) :
      (fun x => (‖if |x| ≤ R then 0 else f x‖ₑ) ^ (2 : ℕ))
        = Set.indicator (tailSet R) (fun x => gSimple x) := by
    funext x
    by_cases hx : |x| ≤ R
    · have hx_not : x ∉ tailSet R := by
        simp [tailSet, hx]
      simp [tailSet, gSimple, gVal, hx, hx_not]
    · have hx_mem : x ∈ tailSet R := by
        simp [tailSet, lt_of_not_ge hx]
      simp [tailSet, gSimple, gVal, hx, hx_mem]

  -- Rewrite the lintegral of the squared norm via the tail set
  have h_integral_sum (R : ℝ) :
      ∫⁻ x, (‖if |x| ≤ R then 0 else f x‖ₑ) ^ (2 : ℕ) ∂μ
        = ∑ v ∈ f.range,
            gVal v * μ {x : ℝ | f x = v ∧ R < |x|} := by
    have h_indicator' := h_indicator R
    have h_int_eq :
        ∫⁻ x, (‖if |x| ≤ R then 0 else f x‖ₑ) ^ (2 : ℕ) ∂μ
          = ∫⁻ x, gSimple x ∂ μ.restrict (tailSet R) := by
      simp [h_indicator', h_tail_measurable R, tailSet]
    have h_map_sum :=
      SimpleFunc.map_lintegral (μ := μ.restrict (tailSet R)) (g := gVal) f
    have h_preimage : ∀ v : ℂ,
        (μ.restrict (tailSet R)) (f ⁻¹' {v}) = μ {x : ℝ | f x = v ∧ R < |x|} := by
      intro v
      have hmeas := f.measurableSet_fiber v
      have := Measure.restrict_apply (μ := μ) (s := tailSet R) hmeas
      classical
      have hset :
          f ⁻¹' {v} ∩ tailSet R = {x : ℝ | f x = v ∧ R < |x|} := by
        ext x; simp [tailSet, Set.mem_preimage, Set.mem_setOf_eq]
      simpa [tailSet, hset] using this
    have h_map_apply : ∀ x, gSimple x = (‖f x‖ₑ) ^ (2 : ℕ) := by
      intro x; simp [gSimple, gVal]
    have h_int_simple :
        ∫⁻ x, gSimple x ∂ μ.restrict (tailSet R)
          = (f.map gVal).lintegral (μ.restrict (tailSet R)) := by
      simpa [h_map_apply, gSimple] using
        (SimpleFunc.lintegral_eq_lintegral (f.map gVal) (μ.restrict (tailSet R)))
    have h_sum := by
      simpa [tailSet, h_preimage, gVal] using h_map_sum
    simpa [h_int_eq, h_int_simple, h_sum]

  -- Define the finite sum that controls the squared L² norm
  let F : ℝ → ℝ≥0∞ := fun R =>
    ∑ v ∈ f.range, gVal v * μ {x : ℝ | f x = v ∧ R < |x|}

  have h_F_tendsto_zero :
      Filter.Tendsto F Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    classical
    have hF_def :
        F = fun R : ℝ => ∑ v ∈ f.range, gVal v * μ {x : ℝ | f x = v ∧ R < |x|} := rfl
    have h_sum :
        Filter.Tendsto (fun R : ℝ => ∑ v ∈ f.range, gVal v * μ {x : ℝ | f x = v ∧ R < |x|})
          Filter.atTop (𝓝 (∑ v ∈ f.range, (0 : ℝ≥0∞))) := by
      refine tendsto_finset_sum (s := f.range) ?_
      intro v hv
      by_cases hv_zero : v = 0
      · have h_const :
          (fun R : ℝ => gVal v * μ {x : ℝ | f x = v ∧ R < |x|}) = fun _ => 0 := by
          funext R; simp [gVal, hv_zero]
        exact h_const ▸ tendsto_const_nhds
      · have hv_range : v ∈ Set.range (f : ℝ → ℂ) := by
          simpa [SimpleFunc.mem_range] using hv
        have h_tail := h_tail_measure_vanishing v hv_zero hv_range
        have h_fin : gVal v ≠ ∞ := by
          simp [gVal]
        have h_mul := ENNReal.Tendsto.const_mul h_tail (Or.inr h_fin)
        have h_mul' := h_mul
        simp [gVal] at h_mul'
        exact h_mul'
    have h_zero : ∑ v ∈ f.range, (0 : ℝ≥0∞) = 0 := by simp
    simpa [hF_def, h_zero] using h_sum

  -- Identify the eLpNorm with the square root of F R
  have h_eLpNorm_eq (R : ℝ) :
      eLpNorm (fun x : ℝ => if |x| ≤ R then 0 else f x) 2 μ
        = (F R) ^ (1 / (2 : ℝ)) := by
    have h_base :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        (μ := μ) (f := fun x : ℝ => if |x| ≤ R then 0 else f x)
        (p := (2 : ℝ≥0∞)) (hp_ne_zero := by norm_num) (hp_ne_top := by simp)
    simpa [F, h_integral_sum R] using h_base

  -- Use continuity of the rpow map to conclude the limit of the eLpNorms
  have h_pow_tendsto :=
    Filter.Tendsto.ennrpow_const (r := 1 / (2 : ℝ)) h_F_tendsto_zero
  have h_zero_pow : (0 : ℝ≥0∞) ^ (1 / (2 : ℝ)) = 0 := by
    simp
  have h_fun_ext :
      (fun R => eLpNorm (fun x => if |x| ≤ R then 0 else f x) 2 μ)
        = fun R => (F R) ^ (1 / (2 : ℝ)) := by
    funext R; exact h_eLpNorm_eq R
  simpa [h_fun_ext, h_zero_pow] using h_pow_tendsto

/-- For simple functions, the tail truncation converges pointwise to zero -/
lemma simpleFunc_tail_pointwise_limit (f : SimpleFunc ℝ ℂ) :
    ∀ x : ℝ, Filter.Tendsto (fun R => if |x| ≤ R then 0 else f x) Filter.atTop (𝓝 0) := by
  intro x
  -- For any fixed x, once R > |x|, we have the function value = 0
  have h_eventually_zero : ∀ᶠ R in Filter.atTop, (if |x| ≤ R then 0 else f x) = 0 := by
    rw [Filter.eventually_atTop]
    use |x| + 1
    intro R hR
    have h_le : |x| ≤ R := by
      linarith [hR, abs_nonneg x]
    simp [h_le]
  -- Since the function is eventually constant at 0, it tends to 0
  -- Use the fact that convergence to 0 means eventually being arbitrarily close to 0
  -- But since our function is eventually exactly 0, this is immediate

  -- Transform the goal to show eventually_eq with the zero function
  have h_eq_zero : (fun R => if |x| ≤ R then 0 else f x) =ᶠ[Filter.atTop] fun _ => (0 : ℂ) :=
    h_eventually_zero

  -- Now use the fact that if f =ᶠ g and g → c, then f → c
  have h_zero_tendsto : Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds
  exact h_zero_tendsto.congr' h_eq_zero.symm

/-- Tail functions of L² simple functions converge to 0 in L² norm by dominated convergence -/
lemma simpleFunc_tail_L2_convergence {σ : ℝ} (hσ : 1 / 2 < σ)
    (f : SimpleFunc ℝ ℂ) (hf_memLp : MemLp (f : ℝ → ℂ) 2 (weightedMeasure σ)) :
    Filter.Tendsto (fun R => eLpNorm (fun x => if |x| ≤ R then 0 else f x) 2 (weightedMeasure σ))
      Filter.atTop (𝓝 0) := by
  set μ := weightedMeasure σ
  let g : ℝ → ℝ → ℂ := fun R x => if |x| ≤ R then 0 else f x

  -- Key properties for dominated convergence:
  -- 1. Pointwise convergence: g R x → 0 as R → ∞
  have h_pointwise : ∀ x : ℝ, Filter.Tendsto (fun R => g R x) Filter.atTop (𝓝 0) := by
    intro x
    -- This follows directly from simpleFunc_tail_pointwise_limit
    -- Note: g R x = if |x| ≤ R then 0 else f x
    have h_eq : (fun R => g R x) = (fun R => if |x| ≤ R then 0 else f x) := by
      funext R
      simp [g]
    rw [h_eq]
    exact simpleFunc_tail_pointwise_limit f x

  -- 2. Domination: |g R x| ≤ |f x| for all R, x
  have h_domination : ∀ R x, ‖g R x‖ ≤ ‖f x‖ := by
    intro R x
    simp only [g]
    by_cases h : |x| ≤ R
    · simp [h]
    · simp [h]

  -- 3. The dominating function f is in L²(μ) (given)
  -- Therefore |f|² ∈ L¹(μ), so we can apply DCT for L² convergence

  -- Apply dominated convergence theorem for L² norms
  -- Since g_R → 0 pointwise, |g_R|² → 0 pointwise
  -- Since |g_R x|² ≤ |f x|² and ∫|f|² < ∞, we have ∫|g_R|² → 0
  -- Therefore ‖g_R‖_{L²} → 0

  -- The key insight: For Simple functions, we can use their finite range structure
  -- to apply dominated convergence more directly

  -- Step 1: f has finite range, so we can decompose the convergence
  have hf_finite_range : (Set.range (f : ℝ → ℂ)).Finite := SimpleFunc.finite_range f

  -- Step 2: For each value v in the range of f, the level set is measurable
  have h_level_sets : ∀ v ∈ Set.range (f : ℝ → ℂ), MeasurableSet {x : ℝ | f x = v} := by
    intro v hv
    exact SimpleFunc.measurableSet_fiber f v

  -- Step 3: The main convergence follows from monotone/dominated convergence
  -- Since each g_R is dominated by f and converges pointwise to 0,
  -- and f has finite L² norm, we can apply dominated convergence

  -- For Simple functions, this reduces to showing that for each level set,
  -- the measure of the tail vanishes, which follows from the weight function properties

  -- The key is that weighted measures with σ > 1/2 have the right tail behavior
  -- to make this work for Simple functions with finite range

  -- Step 4: Apply a more direct approach using dominated convergence for Simple functions
  -- The key insight is that each level set {x : f x = v} has finite measure,
  -- and the weight function x^(2σ-1) has appropriate decay for σ > 1/2

  -- For each non-zero value v in the range of f, the contribution to the L² norm
  -- from the tail {x : f x = v, |x| > R} vanishes as R → ∞
  -- This is because μ({x : f x = v, |x| > R}) → 0

  have h_tail_measure_vanishing : ∀ v : ℂ, v ≠ 0 → v ∈ Set.range (f : ℝ → ℂ) →
    Filter.Tendsto (fun R => μ {x | f x = v ∧ R < |x|}) Filter.atTop (𝓝 0) := by
    intro v hv_nonzero hv_range
    exact simpleFunc_levelSet_tail_measure_vanishing hσ f hf_memLp v hv_nonzero hv_range

  -- Since f has finite range and each level set has appropriate measure behavior,
  -- we can apply a more elementary argument

  -- The key insight: for Simple functions with finite range,
  -- the L² convergence follows from the structure theorem for simple functions
  -- and the tail behavior of the weighted measure

  have h_final_convergence : Filter.Tendsto (fun R => eLpNorm (g R) 2 μ) Filter.atTop (𝓝 0) :=
    simpleFunc_tail_l2_convergence hσ f hf_memLp h_pointwise h_domination h_tail_measure_vanishing

  -- The result follows directly since g R = (fun x => if |x| ≤ R then 0 else f x)
  exact h_final_convergence

/-- L² functions have vanishing tails: for any ε > 0, there exists R > 0
    such that the L² norm of the function outside [-R, R] is less than ε -/
lemma l2_tail_vanishing {σ : ℝ} (hσ : 1 / 2 < σ)
    (f : SimpleFunc ℝ ℂ) (hf_memLp : MemLp (f : ℝ → ℂ) 2 (weightedMeasure σ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
    eLpNorm (fun x => if |x| ≤ R then 0 else f x) 2 (weightedMeasure σ) < ENNReal.ofReal ε := by
  classical
  set μ := weightedMeasure σ
  -- Since f is a SimpleFunc, it takes only finitely many values
  -- and has finite support on each level set
  have hf_finite_range : (Set.range (f : ℝ → ℂ)).Finite := SimpleFunc.finite_range f
  have hf_measurable : Measurable f := SimpleFunc.measurable f

  -- The sequence of tail functions converges to 0 pointwise as R → ∞
  have h_pointwise_limit : ∀ x : ℝ,
      Filter.Tendsto (fun R => if |x| ≤ R then 0 else f x) Filter.atTop (𝓝 0) :=
    simpleFunc_tail_pointwise_limit f

  -- For each value v in the range of f, the set {x : f x = v} is measurable
  have h_level_sets_measurable : ∀ v ∈ Set.range (f : ℝ → ℂ),
      MeasurableSet {x : ℝ | f x = v} := by
    intro v hv
    exact SimpleFunc.measurableSet_fiber f v

  -- Apply dominated convergence theorem
  -- Since |tail function| ≤ |f x| and f ∈ L², we can use dominated convergence
  -- to show that ‖tail function‖₂ → 0 as R → ∞

  -- Apply the tail L² convergence theorem for simple functions
  have h_L2_convergence : Filter.Tendsto
      (fun R => eLpNorm (fun x => if |x| ≤ R then 0 else f x) 2 μ) Filter.atTop (𝓝 0) :=
    simpleFunc_tail_L2_convergence hσ f hf_memLp

  -- Since eLpNorm (tail function) 2 μ → 0, there exists R₀ such that eLpNorm < ε
  have h_exists_R : ∃ R₀ : ℝ, 0 < R₀ ∧
      eLpNorm (fun x => if |x| ≤ R₀ then 0 else f x) 2 μ < ENNReal.ofReal ε := by
    -- Use the convergence to 0 and the fact that ε > 0
    have h_eventually_small : ∀ᶠ R in Filter.atTop,
        eLpNorm (fun x => if |x| ≤ R then 0 else f x) 2 μ < ENNReal.ofReal ε := by
      -- Since h_L2_convergence says eLpNorm → 0 and ε > 0, we have eventually < ε
      have h_pos : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
      exact Filter.Tendsto.eventually_lt h_L2_convergence tendsto_const_nhds h_pos
    -- Extract a specific R₀ from the eventually condition
    rw [Filter.eventually_atTop] at h_eventually_small
    obtain ⟨R₀, hR₀_bound⟩ := h_eventually_small
    use max R₀ 1
    constructor
    · exact lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)
    · apply hR₀_bound
      exact le_max_left R₀ 1

  exact h_exists_R

/-- Truncation of an L² function to a bounded interval remains in L² -/
lemma truncation_memLp {σ : ℝ} (hσ : 1 / 2 < σ)
    (f : SimpleFunc ℝ ℂ) (_hf_memLp : MemLp (f : ℝ → ℂ) 2 (weightedMeasure σ))
    (R : ℝ) (_hR_pos : 0 < R) :
    MemLp (fun x => if |x| ≤ R then f x else 0) 2 (weightedMeasure σ) := by
  classical
  set μ := weightedMeasure σ
  set s : Set ℝ := Set.Icc (-R) R
  have hs_meas : MeasurableSet s := measurableSet_Icc
  -- Simple function obtained by truncating `f` to the interval `[-R, R]`.
  let zeroSf : SimpleFunc ℝ ℂ := SimpleFunc.const (α := ℝ) (0 : ℂ)
  let gSimple : SimpleFunc ℝ ℂ := SimpleFunc.piecewise s hs_meas f zeroSf
  let g : ℝ → ℂ := fun x => if |x| ≤ R then f x else 0

  have hg_fun : (gSimple : ℝ → ℂ) = g := by
    funext x
    have hx_piece := SimpleFunc.piecewise_apply (s := s) hs_meas f zeroSf x
    have hx_piece' : gSimple x = if x ∈ s then f x else 0 := by
      simpa [gSimple, zeroSf] using hx_piece
    by_cases hx : x ∈ s
    · have hx_abs : |x| ≤ R := abs_le.mpr hx
      simpa [g, hx, hx_abs] using hx_piece'
    · have hx_abs : ¬ |x| ≤ R := by
        intro hx_le
        exact hx (abs_le.mp hx_le)
      simpa [g, hx, hx_abs] using hx_piece'

  -- `g` is a.e.-strongly measurable as a simple function.
  have hg_meas : AEStronglyMeasurable g μ := by
    simpa [gSimple, hg_fun] using (SimpleFunc.aestronglyMeasurable gSimple (μ := μ))

  -- `f` takes only finitely many values, hence is bounded in norm.
  obtain ⟨M, hM⟩ := (f.map fun z : ℂ => (‖z‖ : ℝ)).exists_forall_le
  have hM_nonneg : 0 ≤ M :=
    (norm_nonneg (f 0)).trans (hM 0)

  -- Pointwise bound on the truncated function.
  have h_norm_bound : ∀ x, ‖g x‖ ≤ M := by
    intro x
    by_cases hx : |x| ≤ R
    · have : ‖f x‖ ≤ M := hM x
      simpa [g, hx] using this
    · simp [g, hx, hM_nonneg]

  -- Dominating inequality `‖g x‖² ≤ M²` almost everywhere.
  have h_dom : ∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ M ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have h_bound := h_norm_bound x
    have h_abs_sq : |‖g x‖| ≤ |M| := by
      have h_norm_abs : |‖g x‖| = ‖g x‖ := abs_of_nonneg (norm_nonneg _)
      have hM_abs : |M| = M := abs_of_nonneg hM_nonneg
      simpa [h_norm_abs, hM_abs] using h_bound
    have h_sq := sq_le_sq.mpr h_abs_sq
    simpa [pow_two, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hM_nonneg] using h_sq

  -- The support of `g` is contained in `[-R, R]`.
  have h_support_subset : Function.support g ⊆ s := by
    intro x hx
    have hx_ne : g x ≠ 0 := by simpa [Function.mem_support] using hx
    by_cases hx_abs : |x| ≤ R
    · exact abs_le.mp hx_abs
    · have : g x = 0 := by simp [g, hx_abs]
      exact (hx_ne this).elim

  have h_tsupport_subset : tsupport g ⊆ s := by
    have h_closure := closure_minimal h_support_subset isClosed_Icc
    simpa [tsupport, g, Function.support] using h_closure

  -- Measure of the topological support of `g` is finite.
  have h_support_measure : μ (tsupport g) < ∞ :=
    lt_of_le_of_lt (measure_mono h_tsupport_subset)
      (by simpa [s] using weightedMeasure_finite_on_interval hσ R)

  -- `g` has finite integral of `‖·‖²` thanks to dominance on a compact support.
  have hg_hasFiniteIntegral : HasFiniteIntegral (fun x => ‖g x‖ ^ 2) μ :=
    hasFiniteIntegral_of_dominated_on_compactSupport h_dom h_support_measure

  -- Conclude `g` lies in L² with respect to the weighted measure.
  have h_memLp : MemLp g 2 μ :=
    memLp_of_hasFiniteIntegral_and_aestronglyMeasurable hg_meas hg_hasFiniteIntegral
  simpa [g] using h_memLp

/-- Tail vanishing property for Lp functions in weighted measure -/
lemma lp_tail_vanishing {σ : ℝ} (hσ : 1 / 2 < σ)
    (s : Lp ℂ 2 (weightedMeasure σ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      eLpNorm (fun x => if |x| > R then (s : ℝ → ℂ) x else 0) 2 (weightedMeasure σ) <
      ENNReal.ofReal ε := by
  classical
  have hs_memLp : MemLp (fun x => (s : ℝ → ℂ) x) 2 (weightedMeasure σ) := Lp.memLp s
  -- Approximate `s` in L² by a simple function with error ε/2.
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_eps_pos : (0 : ENNReal) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨f, hf_err, hf_memLp⟩ :=
    hs_memLp.exists_simpleFunc_eLpNorm_sub_lt h_two_ne_top
      (ne_of_gt h_eps_pos)
  have hf_meas : AEStronglyMeasurable (f : ℝ → ℂ) (weightedMeasure σ) :=
    SimpleFunc.aestronglyMeasurable f

  -- Tail control for the simple function `f`.
  have h_simple_tail :=
    l2_tail_vanishing hσ f hf_memLp (ε / 2) (by linarith)
  obtain ⟨R₀, hR₀_pos, hR₀_tail⟩ := h_simple_tail

  -- Define the tail function associated with a given radius.
  let tailFun := fun (R : ℝ) (hR : R ≥ R₀) (x : ℝ) =>
    if |x| ≤ R then 0 else (s : ℝ → ℂ) x

  have h_tailEq (R : ℝ) :
      (fun x : ℝ => if |x| > R then (s : ℝ → ℂ) x else 0)
        = fun x => (s : ℝ → ℂ) x - (fun y => if |y| ≤ R then (s : ℝ → ℂ) y else 0) x := by
    funext x; by_cases hx : |x| ≤ R
    · have hx' : ¬|x| > R := not_lt.mpr hx
      simp [hx, hx']
    · have hx' : |x| > R := lt_of_not_ge hx
      simp [hx, hx']

  -- For any R ≥ R₀, the L² difference between `s` and its truncation is controlled
  -- by splitting into the simple function approximation and its tail.
  have h_tail_estimate :
      ∀ R,
        eLpNorm (fun x : ℝ => if |x| > R then (s : ℝ → ℂ) x else 0) 2 (weightedMeasure σ)
          ≤ eLpNorm (fun x => (s : ℝ → ℂ) x - (f : ℝ → ℂ) x) 2 (weightedMeasure σ)
            + eLpNorm (fun x => if |x| > R then f x else 0) 2 (weightedMeasure σ) := by
    classical
    intro R
    let tailSet : Set ℝ := {x : ℝ | |x| > R}
    have h_open_tail : IsOpen tailSet := by
      have : tailSet = (fun x : ℝ => |x|) ⁻¹' Set.Ioi R := rfl
      simpa [this] using (isOpen_Ioi.preimage continuous_abs)
    have h_meas_tail : MeasurableSet tailSet := h_open_tail.measurableSet
    let tailS : ℝ → ℂ := tailSet.indicator fun x => (s : ℝ → ℂ) x
    let tailDiff : ℝ → ℂ := tailSet.indicator fun x =>
      (s : ℝ → ℂ) x - (f : ℝ → ℂ) x
    let tailF : ℝ → ℂ := tailSet.indicator fun x => f x
    have h_tailDiff_memLp : MemLp tailDiff 2 (weightedMeasure σ) :=
      MemLp.indicator h_meas_tail (hs_memLp.sub hf_memLp)
    have h_tailF_memLp : MemLp tailF 2 (weightedMeasure σ) :=
      MemLp.indicator h_meas_tail hf_memLp
    have h_tail_decomp : tailS = tailDiff + tailF := by
      funext x
      by_cases hx : x ∈ tailSet
      · simp [tailS, tailDiff, tailF, hx, sub_eq_add_neg, add_comm, add_left_comm]
      · simp [tailS, tailDiff, tailF, hx]
    have h_add_le :
        eLpNorm tailS 2 (weightedMeasure σ)
          ≤ eLpNorm tailDiff 2 (weightedMeasure σ) + eLpNorm tailF 2 (weightedMeasure σ) := by
      simpa [h_tail_decomp, tailS, tailDiff, tailF] using
        (eLpNorm_add_le (μ := weightedMeasure σ) (p := (2 : ℝ≥0∞))
          h_tailDiff_memLp.1 h_tailF_memLp.1
          (by exact (inferInstance : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))).1))
    have h_tailDiff_le :
        eLpNorm tailDiff 2 (weightedMeasure σ)
          ≤ eLpNorm (fun x => (s : ℝ → ℂ) x - (f : ℝ → ℂ) x) 2 (weightedMeasure σ) := by
      refine eLpNorm_mono ?_
      intro x
      by_cases hx : x ∈ tailSet
      · simp [tailDiff, tailSet, hx, sub_eq_add_neg]
      · simp [tailDiff, tailSet, hx]
    have h_result :=
      h_add_le.trans (add_le_add_right h_tailDiff_le _)
    have h_tailS_eq :
        tailS = fun x : ℝ => if |x| > R then (s : ℝ → ℂ) x else 0 := by
      funext x
      by_cases hx : |x| > R
      · simp [tailS, tailSet, hx]
      · simp [tailS, tailSet, hx]
    have h_tailF_eq :
        tailF = fun x : ℝ => if |x| > R then f x else 0 := by
      funext x
      by_cases hx : |x| > R
      · simp [tailF, tailSet, hx]
      · simp [tailF, tailSet, hx]
    simpa [h_tailS_eq, h_tailF_eq] using h_result

  -- Choose R large enough:
  obtain ⟨R₁, hR₁_pos, hR₁_bound⟩ :=
    l2_tail_vanishing hσ f hf_memLp (ε / 2) (by linarith : 0 < ε / 2)
  -- Final estimate combining approximation and simple tail bound.
  refine ⟨R₁, hR₁_pos, ?_⟩
  have h_norm_diff := hf_err
  have h_total_estimate :
      eLpNorm (fun x => if |x| > R₁ then (s : ℝ → ℂ) x else 0) 2 (weightedMeasure σ)
        ≤ eLpNorm (fun x => (s : ℝ → ℂ) x - (f : ℝ → ℂ) x) 2 (weightedMeasure σ)
          + eLpNorm (fun x => if |x| > R₁ then f x else 0) 2 (weightedMeasure σ) :=
    h_tail_estimate R₁

  have h_tail_form_eq :
      (fun x : ℝ => if |x| ≤ R₁ then 0 else f x) =
        (fun x : ℝ => if |x| > R₁ then f x else 0) := by
    funext x; by_cases hx : |x| ≤ R₁
    · have hx' : ¬|x| > R₁ := not_lt.mpr hx
      simp [hx, hx']
    · have hx' : |x| > R₁ := lt_of_not_ge hx
      simp [hx, hx']

  have h_sum_lt :
      eLpNorm (fun x => (s : ℝ → ℂ) x - (f : ℝ → ℂ) x) 2 (weightedMeasure σ)
          + eLpNorm (fun x => if |x| > R₁ then f x else 0) 2 (weightedMeasure σ)
        < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
    have h_norm_lt :
        eLpNorm (fun x => (s : ℝ → ℂ) x - (f : ℝ → ℂ) x) 2 (weightedMeasure σ)
          < ENNReal.ofReal (ε / 2) := by
      simpa using h_norm_diff
    have h_tail_lt :
        eLpNorm (fun x => if |x| > R₁ then f x else 0) 2 (weightedMeasure σ)
          < ENNReal.ofReal (ε / 2) := by
      simpa [h_tail_form_eq] using hR₁_bound
    exact ENNReal.add_lt_add h_norm_lt h_tail_lt

  have h_sum_eq :
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    have h_half_nonneg : 0 ≤ ε / 2 := by linarith [hε.le]
    simpa [add_halves] using (ENNReal.ofReal_add h_half_nonneg h_half_nonneg).symm

  have h_sum_lt' :
      eLpNorm (fun x => (s : ℝ → ℂ) x - (f : ℝ → ℂ) x) 2 (weightedMeasure σ)
          + eLpNorm (fun x => if |x| > R₁ then f x else 0) 2 (weightedMeasure σ)
        < ENNReal.ofReal ε := by
    exact h_sum_eq ▸ h_sum_lt

  have h_goal :
      eLpNorm (fun x => if |x| > R₁ then (s : ℝ → ℂ) x else 0) 2 (weightedMeasure σ)
        < ENNReal.ofReal ε := lt_of_le_of_lt h_total_estimate h_sum_lt'
  simpa [gt_iff_lt] using h_goal

/-- Truncation of Lp functions preserves Lp membership -/
lemma lp_truncation_memLp {σ : ℝ} (s : Lp ℂ 2 (weightedMeasure σ)) (R : ℝ) :
    MemLp (fun x => if |x| ≤ R then (s : ℝ → ℂ) x else 0) 2 (weightedMeasure σ) := by
  -- Truncation of an L² function is still in L²
  -- This follows because truncation can only decrease the L² norm
  -- |s_R(x)| ≤ |s(x)| for all x, so ∫|s_R|² ≤ ∫|s|² < ∞
  -- The key insight is that s_R(x) = s(x) if |x| ≤ R, and 0 otherwise
  -- So ∫|s_R|² = ∫_{|x|≤R} |s(x)|² ≤ ∫|s|² < ∞
  -- Since s ∈ L²(weightedMeasure σ), we have ∫|s|² weightFunction(σ, x) dx < ∞
  -- And the restriction to {|x| ≤ R} can only make the integral smaller
  classical
  set truncFun : ℝ → ℂ := fun x => if |x| ≤ R then (s : ℝ → ℂ) x else 0
  have h_goal : MemLp truncFun 2 (weightedMeasure σ) := by
    let A : Set ℝ := Set.Icc (-R) R
    have hA_meas : MeasurableSet A := measurableSet_Icc
    have hs_memLp : MemLp (fun x : ℝ => (s : ℝ → ℂ) x) 2 (weightedMeasure σ) :=
      Lp.memLp s
    have h_indicator_eq :
        A.indicator (fun x : ℝ => (s : ℝ → ℂ) x) = truncFun := by
      funext x
      have hx_mem : (x ∈ A) ↔ |x| ≤ R := by
        simp [A, abs_le]
      by_cases hx : |x| ≤ R
      · simp [truncFun, hx_mem, hx]
      · simp [truncFun, hx_mem, hx]
    simpa [truncFun, h_indicator_eq] using
      (MemLp.indicator hA_meas hs_memLp)
  simpa [truncFun] using h_goal

/-- Mollification parameter δ is small when defined as minimum -/
lemma mollification_delta_small (ε : ℝ) (hε_pos : 0 < ε)
    (s_R : ℝ → ℂ) (R : ℝ) (_hR_pos : 0 < R) (σ : ℝ) :
    let M := ENNReal.toReal (eLpNorm s_R 2 (weightedMeasure σ)) + 1
    let δ := min (ε / (8 * M)) (1 / (2 * (R + 1)))
    δ < ε / (4 * M) := by
  -- Choose δ as minimum of ε/(8M) and 1/(2(R+1))
  -- Then δ ≤ ε/(8M) < ε/(4M) since 8 > 4
  have h_pos_M : 0 < ENNReal.toReal (eLpNorm s_R 2 (weightedMeasure σ)) + 1 := by
    apply add_pos_of_nonneg_of_pos
    · exact ENNReal.toReal_nonneg
    · norm_num
  have h_bound : min (ε / (8 * (ENNReal.toReal (eLpNorm s_R 2 (weightedMeasure σ)) + 1)))
                     (1 / (2 * (R + 1)))
                 ≤ ε / (8 * (ENNReal.toReal (eLpNorm s_R 2 (weightedMeasure σ)) + 1)) :=
    min_le_left _ _
  have h_strict : ε / (8 * (ENNReal.toReal (eLpNorm s_R 2 (weightedMeasure σ)) + 1))
                  < ε / (4 * (ENNReal.toReal (eLpNorm s_R 2 (weightedMeasure σ)) + 1)) := by
    apply div_lt_div_of_pos_left hε_pos
    · apply mul_pos
      · norm_num
      · exact h_pos_M
    · apply mul_lt_mul_of_pos_right
      · norm_num
      · exact h_pos_M
  exact lt_of_le_of_lt h_bound h_strict

/-- The embedding is continuous with respect to a finite family of Schwartz seminorms for σ > 1/2 -/
lemma schwartzToHσ_continuous {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ (k₁ : ℕ) (C₀ C₁ : ℝ), 0 < C₀ ∧ 0 < C₁ ∧
    ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHσ hσ f‖ ≤
        C₀ * SchwartzMap.seminorm ℝ 0 0 f +
          C₁ * SchwartzMap.seminorm ℝ k₁ 0 f := by
  -- For σ > 1/2, the weight x^(2σ-2) is integrable near 0
  -- The seminorms k₁, k₂ need to control the behavior at infinity
  -- k₁ controls polynomial growth, k₂ controls smoothness

  -- Choose seminorm parameters: k₁ for polynomial decay at infinity
  classical
  let k₁ : ℕ := ⌊4 * σ + 2⌋₊  -- Ensure enough decay at infinity

  -- Define the constant C based on the weight integral bounds
  obtain ⟨M, hM_pos, hM_bound⟩ := weight_function_L2_bound_unit hσ
  -- Constants for the two seminorm controls
  let C₀ : ℝ := M
  have hC₀_pos : 0 < C₀ := by simpa using hM_pos
  have hC₀_nonneg : 0 ≤ C₀ := hC₀_pos.le

  -- Tail constant coming from polynomial decay
  have h_k₁_large : σ + 1 / 2 ≤ (k₁ : ℝ) := by
    have h_aux : (4 * σ + 2 : ℝ) < (k₁ : ℝ) + 1 := by
      simpa [k₁, add_comm, add_left_comm, add_assoc] using
        (Nat.lt_floor_add_one (4 * σ + 2))
    have h_floor : (4 * σ + 1 : ℝ) < (k₁ : ℝ) := by
      have := h_aux
      linarith
    have hσ_bound : σ + 1 / 2 ≤ 4 * σ + 1 := by
      linarith [hσ]
    exact (le_of_lt (lt_of_le_of_lt hσ_bound h_floor))

  have h_denom_pos : 0 < 2 * (k₁ : ℝ) - 2 * σ := by
    have h_aux := add_le_add h_k₁_large h_k₁_large
    have h_cast : (k₁ : ℝ) + (k₁ : ℝ) = 2 * (k₁ : ℝ) := by ring
    have h_sigma : σ + σ = 2 * σ := by ring
    have h_half : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
    have h_le : 2 * σ + 1 ≤ 2 * (k₁ : ℝ) := by
      have h_rewrite : σ + 1 / 2 + (σ + 1 / 2) = 2 * σ + 1 := by ring
      rw [← h_rewrite]
      rw [h_cast] at h_aux
      exact h_aux
    linarith

  let C₁ : ℝ := Real.sqrt (1 / (2 * (k₁ : ℝ) - 2 * σ))
  have hC₁_pos : 0 < C₁ := by
    have h_inv_pos : 0 < 1 / (2 * (k₁ : ℝ) - 2 * σ) := by
      exact one_div_pos.mpr h_denom_pos
    exact Real.sqrt_pos.mpr h_inv_pos

  use k₁, C₀, C₁
  refine ⟨hC₀_pos, hC₁_pos, ?_⟩
  intro f
  -- Estimate the Hilbert space norm
  rw [schwartzToHσ]
  -- Use the fact that ‖MemLp.toLp f hf‖ = ENNReal.toReal (eLpNorm f p μ)
  rw [norm_toLp_eq_toReal_eLpNorm hσ f]

  -- Show that ENNReal.toReal of a bound gives the desired inequality
  suffices h_eLp : eLpNorm (fun x => if x > 0 then f x else 0) 2
      (mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) ≤
      ENNReal.ofReal
        (C₀ * SchwartzMap.seminorm ℝ 0 0 f +
          C₁ * SchwartzMap.seminorm ℝ k₁ 0 f) by
    have h_nonneg :
        0 ≤ C₀ * SchwartzMap.seminorm ℝ 0 0 f +
            C₁ * SchwartzMap.seminorm ℝ k₁ 0 f := by
      apply add_nonneg
      · exact mul_nonneg hC₀_nonneg (apply_nonneg _ f)
      · exact mul_nonneg hC₁_pos.le (apply_nonneg _ f)
    exact ENNReal.toReal_le_of_le_ofReal h_nonneg h_eLp

  -- The L^2 norm with weight can be bounded by Schwartz seminorms
  -- Split the integral into (0,1] and (1,∞)
  have h_split := @eLpNorm_split_at_one σ f

  -- Bound each part using Schwartz properties
  have h_bound1 := eLpNorm_bound_on_unit_interval f C₀ hM_bound

  have h_bound2 := eLpNorm_bound_on_tail (σ := σ) (k₁ := k₁) h_k₁_large f

  -- Combine the estimates for the unit interval and the tail
  have h_combined := le_trans h_split (add_le_add h_bound1 h_bound2)

  -- Package the sum of the two bounds into a single `ENNReal.ofReal`
  have h_nonneg_unit : 0 ≤ SchwartzMap.seminorm ℝ 0 0 f * C₀ :=
    mul_nonneg (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) f) hC₀_nonneg
  have h_nonneg_tail :
      0 ≤ SchwartzMap.seminorm ℝ k₁ 0 f * C₁ :=
    mul_nonneg (apply_nonneg (SchwartzMap.seminorm ℝ k₁ 0) f) hC₁_pos.le
  have h_sum :
      eLpNorm (fun x => if x > 0 then f x else 0) 2
          (mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) ≤
        ENNReal.ofReal
          (C₀ * SchwartzMap.seminorm ℝ 0 0 f +
            C₁ * SchwartzMap.seminorm ℝ k₁ 0 f) := by
    -- Use the fact that C₁ = √(1 / (2 * ↑k₁ - 2 * σ))
    convert h_combined using 1
    rw [← ENNReal.ofReal_add]
    · congr 1
      ring
    · exact h_nonneg_unit
    · have : 0 ≤ SchwartzMap.seminorm ℝ k₁ 0 f * Real.sqrt (1 / (2 * (k₁ : ℝ) - 2 * σ)) := by
        exact mul_nonneg (apply_nonneg _ f) (Real.sqrt_nonneg _)
      exact this

  exact h_sum

end SchwartzDensity

end Frourio
