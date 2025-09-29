import Frourio.Analysis.Gaussian
import Frourio.Analysis.MellinBasic
import Frourio.Analysis.HilbertSpaceCore
import Frourio.Analysis.SchwartzDensity.SchwartzDensityCore1
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

/-- Helper identity converting the squared extended norm to an `ENNReal.ofReal` quadratic. -/
@[simp] lemma ennorm_sq_eq_ofReal_norm_sq (z : ℂ) :
    ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  simp [pow_two, ENNReal.ofReal_mul, hz]

@[simp] lemma norm_norm_sq (z : ℂ) : ‖‖z‖ ^ 2‖ = ‖z‖ ^ 2 := by
  have hz : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  simp [Real.norm_eq_abs, abs_of_nonneg hz]

/-- Helper lemma: Lp function restricted to a set is AE strongly measurable -/
lemma lp_restricted_aestronglyMeasurable {σ : ℝ} (s : Lp ℂ 2 (weightedMeasure σ)) (R : ℝ) :
    AEStronglyMeasurable (s : ℝ → ℂ) (volume.restrict (Set.Ioc 0 R)) := by
  -- Use the fact that Lp functions have a strongly measurable representative
  have h_sm : StronglyMeasurable (s : ℝ → ℂ) := by
    apply Lp.stronglyMeasurable
  exact h_sm.aestronglyMeasurable.restrict

/-- Composition of density functions for weighted measures -/
lemma withDensity_mul_indicator (σ : ℝ) :
    (volume.withDensity fun x : ℝ => ENNReal.ofReal x⁻¹).withDensity
        ((Set.Ioi (0 : ℝ)).indicator (weightFunction σ))
      = volume.withDensity
          (fun x : ℝ => ENNReal.ofReal x⁻¹ *
            (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x) := by
  classical
  have h_meas_inv₁ : Measurable fun x : ℝ => ENNReal.ofReal ((1 : ℝ) / x) := by
    refine (Measurable.ennreal_ofReal ?_)
    simpa using (Measurable.div measurable_const measurable_id)
  have h_meas_inv : Measurable fun x : ℝ => ENNReal.ofReal x⁻¹ := by
    simpa [one_div] using h_meas_inv₁
  have h_meas_indicator :
      Measurable fun x : ℝ =>
        (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x :=
    (weightFunction_measurable σ).indicator measurableSet_Ioi
  have h_mul :=
    MeasureTheory.withDensity_mul (μ := volume)
      (f := fun x : ℝ => ENNReal.ofReal x⁻¹)
      (g := fun x : ℝ => (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x)
      h_meas_inv h_meas_indicator
  simpa [Pi.mul_apply] using h_mul.symm

/-- Truncated Lp functions are in Lp with respect to volume measure on compact intervals
    NOTE: This requires σ ≤ 1 for the transfer from weighted to unweighted measure.
    For σ > 1, functions in L²(weightedMeasure σ) may not be in L²(volume).
    Example: σ = 6/5, s(x) = x^{-3/5} is in L²(weighted) but not L²(volume).
-/
lemma lp_truncation_memLp_on_Ioc {σ : ℝ} (hσ_upper : σ ≤ 1)
    (s : Lp ℂ 2 (weightedMeasure σ)) (R : ℝ) (p : ℝ≥0∞) (hp : p = 2) :
    MemLp (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0)
    p (volume.restrict (Set.Ioc 0 R)) := by
  classical
  subst hp
  set μ := volume.restrict (Set.Ioc (0 : ℝ) R)
  set f : ℝ → ℂ := fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0
  have hS_meas : MeasurableSet (Set.Ioc (0 : ℝ) R) := measurableSet_Ioc
  have hf_indicator :
      f = Set.indicator (Set.Ioc (0 : ℝ) R) (fun x => (s : ℝ → ℂ) x) := by
    funext x
    by_cases hx : 0 < x ∧ x ≤ R
    · simp [f, hx, Set.indicator_of_mem, Set.mem_Ioc]
    · simp [f, hx, Set.indicator_of_notMem, Set.mem_Ioc]
  by_cases hR_nonpos : R ≤ 0
  · have hf_zero : f = fun _ => (0 : ℂ) := by
      funext x
      by_cases hx : 0 < x ∧ x ≤ R
      · have hx_le : x ≤ 0 := hx.2.trans hR_nonpos
        exact (hx_le.not_gt hx.1).elim
      · simp [f, hx]
    have h_zero_mem : MemLp (fun _ : ℝ => (0 : ℂ)) 2 μ := by simp
    simp [μ, hf_zero, f]
  have hR_pos : 0 < R := lt_of_not_ge hR_nonpos
  have hf_meas : AEStronglyMeasurable f μ := by
    have hs_meas :=
      lp_restricted_aestronglyMeasurable (σ := σ) s R
    have hf_meas' :
        AEStronglyMeasurable
          (Set.indicator (Set.Ioc (0 : ℝ) R) fun x => (s : ℝ → ℂ) x) μ :=
      hs_meas.indicator hS_meas
    simpa [μ, f, hf_indicator] using hf_meas'
  -- Shortcut notation for the interval of truncation.
  set S : Set ℝ := Set.Ioc (0 : ℝ) R
  have hS_meas' : MeasurableSet S := hS_meas
  have hS_subset : S ⊆ Set.Ioi (0 : ℝ) := fun x hx => hx.1
  -- f agrees μ-a.e. with s, hence it suffices to control the integral of s on S.
  have hf_eq_s : f =ᵐ[μ] fun x => (s : ℝ → ℂ) x := by
    have h_forall : ∀ x ∈ S, f x = (s : ℝ → ℂ) x := by
      intro x hx
      have hx' : 0 < x ∧ x ≤ R := by
        simpa [S, Set.mem_Ioc] using hx
      simp [f, hx']
    exact ae_restrict_of_forall_mem (μ := volume) (s := S) hS_meas' h_forall
  -- Express the square-norm integrand in ENNReal form.
  set g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2)
  set w : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2))
  have h_exp_nonpos : 2 * σ - 2 ≤ 0 := by linarith [hσ_upper]
  have h_constant_nonneg : 0 ≤ R ^ (2 - 2 * σ) :=
    Real.rpow_nonneg (le_of_lt hR_pos) (2 - 2 * σ)
  -- Pointwise bound: on S, the unweighted square-norm is controlled by the weighted one.
  have h_indicator_bound :
      (fun x => Set.indicator S g x)
        ≤ fun x => ENNReal.ofReal (R ^ (2 - 2 * σ)) * Set.indicator S w x := by
    intro x
    by_cases hx : x ∈ S
    · have hx_pos : 0 < x := (hS_subset hx)
      have hx_le : x ≤ R := hx.2
      have hx_pow_bound : R ^ (2 * σ - 2) ≤ x ^ (2 * σ - 2) :=
        Real.rpow_le_rpow_of_nonpos hx_pos hx_le h_exp_nonpos
      have hx_weight_ge_one :
          (1 : ℝ) ≤ R ^ (2 - 2 * σ) * x ^ (2 * σ - 2) := by
        have h_mul :=
          mul_le_mul_of_nonneg_left hx_pow_bound h_constant_nonneg
        have h_prod_one :
            R ^ (2 - 2 * σ) * R ^ (2 * σ - 2) = 1 := by
          have h_sum : (2 - 2 * σ) + (2 * σ - 2) = (0 : ℝ) := by ring
          have h_mul_eq :
              R ^ (2 - 2 * σ) * R ^ (2 * σ - 2)
                = R ^ ((2 - 2 * σ) + (2 * σ - 2)) :=
            (Real.rpow_add hR_pos (2 - 2 * σ) (2 * σ - 2)).symm
          simpa [h_sum, Real.rpow_zero] using h_mul_eq
        simpa [h_prod_one] using h_mul
      have hx_sq_nonneg : 0 ≤ ‖(s : ℝ → ℂ) x‖ ^ 2 := sq_nonneg _
      have hx_real :
          (‖(s : ℝ → ℂ) x‖ ^ 2 : ℝ)
            ≤ R ^ (2 - 2 * σ) * (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2)) := by
        have hx_mul := mul_le_mul_of_nonneg_right hx_weight_ge_one hx_sq_nonneg
        simpa [mul_comm, mul_left_comm, mul_assoc] using hx_mul
      have hx_rhs_nonneg :
          0 ≤ R ^ (2 - 2 * σ) * (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2)) :=
        mul_nonneg h_constant_nonneg
          (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hx_pos) (2 * σ - 2)))
      have hx_lhs_nonneg : 0 ≤ ‖(s : ℝ → ℂ) x‖ ^ 2 := sq_nonneg _
      have hx_ennreal : g x ≤
          ENNReal.ofReal (R ^ (2 - 2 * σ)
            * (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2))) := by
        have := ENNReal.ofReal_le_ofReal hx_real
        simpa [g] using this
      have hx_rewrite :
          ENNReal.ofReal (R ^ (2 - 2 * σ)
              * (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2)))
            = ENNReal.ofReal (R ^ (2 - 2 * σ)) * w x := by
        have hx :=
          ENNReal.ofReal_mul'
            (p := ‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2))
            (q := R ^ (2 - 2 * σ)) h_constant_nonneg
        simpa [w, mul_comm, mul_left_comm, mul_assoc] using hx
      have hx_in : Set.indicator S g x = g x :=
        Set.indicator_of_mem hx _
      have hx_in_rhs : Set.indicator S w x = w x :=
        Set.indicator_of_mem hx _
      simpa [hx_in, hx_in_rhs, hx_rewrite]
        using hx_ennreal
    · simp [hx]
  -- Use the pointwise bound to control the lintegral.
  have h_integral_bound :
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal (R ^ (2 - 2 * σ)) *
          ∫⁻ x, ENNReal.ofReal
            (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2)) ∂μ := by
    classical
    have h_norm_sq :
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ
          = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
      refine lintegral_congr_ae ?_
      exact Filter.Eventually.of_forall (fun x => by simp)
    have h_lhs :
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ
          = ∫⁻ x, Set.indicator S g x ∂volume := by
      have hfg :
          (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) =ᵐ[μ] g := by
        refine hf_eq_s.mono ?_
        intro x hx
        simp [g, hx]
      have h_restrict :
          ∫⁻ x, g x ∂μ = ∫⁻ x, Set.indicator S g x ∂volume := by
        simp [μ, g, hS_meas', lintegral_indicator, S]
      exact (lintegral_congr_ae hfg).trans h_restrict
    have h_rhs :
        ∫⁻ x, ENNReal.ofReal
            (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2)) ∂μ
          = ∫⁻ x, Set.indicator S w x ∂volume := by
      simp [μ, w, hS_meas', lintegral_indicator, S]
    have h_indicator_bound' :
        ∫⁻ x, Set.indicator S g x ∂volume
          ≤ ∫⁻ x, ENNReal.ofReal (R ^ (2 - 2 * σ)) * Set.indicator S w x ∂volume := by
      simpa using
        lintegral_mono_ae (μ := volume)
          (Filter.Eventually.of_forall h_indicator_bound)
    have h_const_mul :
        ∫⁻ x, ENNReal.ofReal (R ^ (2 - 2 * σ)) * Set.indicator S w x ∂volume
          = ENNReal.ofReal (R ^ (2 - 2 * σ)) * ∫⁻ x, Set.indicator S w x ∂volume := by
      simpa using
        (lintegral_const_mul' (μ := volume)
          (r := ENNReal.ofReal (R ^ (2 - 2 * σ)))
          (f := fun x => Set.indicator S w x)
          (hr := ENNReal.ofReal_ne_top))
    have h_rewrite :
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ∫⁻ x, Set.indicator S g x ∂volume := by
      simp [h_norm_sq, h_lhs]
    have h_le_const :
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤
          ∫⁻ x, ENNReal.ofReal (R ^ (2 - 2 * σ)) * Set.indicator S w x ∂volume := by
      simpa [h_lhs] using h_indicator_bound'
    have h_le_mul :
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤
          ENNReal.ofReal (R ^ (2 - 2 * σ)) * ∫⁻ x, Set.indicator S w x ∂volume := by
      simpa [h_const_mul] using h_le_const
    have h_le_final' :
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤
          ENNReal.ofReal (R ^ (2 - 2 * σ)) * ∫⁻ x, Set.indicator S w x ∂volume := by
      simpa [h_norm_sq] using h_le_mul
    have h_le_final :
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤
          ENNReal.ofReal (R ^ (2 - 2 * σ)) *
            ∫⁻ x, ENNReal.ofReal
                (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2)) ∂μ := by
      simpa [h_rhs.symm] using h_le_final'
    exact h_le_final
  -- Show that the weighted integral on the right-hand side is finite.
  have h_weight_integral_lt :
      ∫⁻ x, ENNReal.ofReal
          (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2)) ∂μ < ∞ := by
    have h_subset : S ⊆ Set.Ioi (0 : ℝ) := hS_subset
    have h_indicator_le :
        Set.indicator S w ≤
          Set.indicator (Set.Ioi (0 : ℝ)) w := by
      intro x
      by_cases hx : x ∈ S
      · have hx' : x ∈ Set.Ioi (0 : ℝ) := h_subset hx
        simp [w, Set.indicator_of_mem, hx, hx']
      · simp [Set.indicator_of_notMem, hx]
    have h_restrict_le :
        ∫⁻ x, ENNReal.ofReal
            (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2)) ∂μ
          ≤ ∫⁻ x, Set.indicator (Set.Ioi (0 : ℝ)) w x ∂volume := by
      have :=
        lintegral_mono_ae (μ := volume)
          (Filter.Eventually.of_forall h_indicator_le)
      simpa [μ, w, hS_meas', lintegral_indicator]
        using this
    obtain hs_memLp : MemLp (fun x => (s : ℝ → ℂ) x) 2 (weightedMeasure σ) := Lp.memLp s
    have hs_integrable :
        Integrable (fun x => ‖(s : ℝ → ℂ) x‖ ^ 2) (weightedMeasure σ) := by
      have h_meas := Lp.aestronglyMeasurable (μ := weightedMeasure σ) s
      exact
        ((memLp_two_iff_integrable_sq_norm (μ := weightedMeasure σ)
            (f := fun x => (s : ℝ → ℂ) x) h_meas).mp hs_memLp)
    have h_weight :
        ∫⁻ x, ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2) ∂(weightedMeasure σ) < ∞ := by
      simpa [HasFiniteIntegral] using hs_integrable.hasFiniteIntegral
    have h_product :
        (fun x : ℝ => ENNReal.ofReal x⁻¹ *
            (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x)
          = (Set.Ioi (0 : ℝ)).indicator
              (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 2))) := by
      funext x
      by_cases hx : x ∈ Set.Ioi (0 : ℝ)
      · have hx_pos : 0 < x := hx
        have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
        have hx_value :
            (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x
              = ENNReal.ofReal (x ^ (2 * σ - 1)) := by
          simp [Set.indicator_of_mem, hx, weightFunction, hx_pos]
        have hx_indicator_rhs :
            (Set.Ioi (0 : ℝ)).indicator
                (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 2))) x
              = ENNReal.ofReal (x ^ (2 * σ - 2)) := by
          simp [Set.indicator_of_mem, hx]
        have hx_real :
            x ^ (-1 : ℝ) * x ^ (2 * σ - 1) = x ^ (2 * σ + -2) := by
          rw [← Real.rpow_add hx_pos (-1 : ℝ) (2 * σ - 1)]
          congr 1
          ring
        have hx_nonneg1 : 0 ≤ x ^ (-1 : ℝ) := Real.rpow_nonneg hx_nonneg _
        have hx_nonneg2 : 0 ≤ x ^ (2 * σ - 1) := Real.rpow_nonneg hx_nonneg _
        have hx_prod' :
            ENNReal.ofReal (x ^ (-1 : ℝ)) * ENNReal.ofReal (x ^ (2 * σ - 1))
              = ENNReal.ofReal (x ^ (2 * σ - 2)) := by
          rw [← ENNReal.ofReal_mul hx_nonneg1, hx_real]
          simp [sub_eq_add_neg]
        have hx_inv : ENNReal.ofReal x⁻¹ = ENNReal.ofReal (x ^ (-1 : ℝ)) := by
          simp [Real.rpow_neg_one, hx_pos]
        have hx_left :
            ENNReal.ofReal x⁻¹ *
                (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x
              = ENNReal.ofReal (x ^ (2 * σ - 2)) := by
          simpa [hx_value, hx_inv] using hx_prod'
        simpa [hx_indicator_rhs]
          using hx_left
      · have hx_not : x ∉ Set.Ioi (0 : ℝ) := hx
        simp [Set.indicator_of_notMem, hx_not]
    have h_weight_eq :
        ∫⁻ x, Set.indicator (Set.Ioi (0 : ℝ)) w x ∂volume
          = ∫⁻ x, ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2) ∂(weightedMeasure σ) := by
      have h_density :
          weightedMeasure σ = volume.withDensity
              (Set.indicator (Set.Ioi (0 : ℝ))
                fun x => ENNReal.ofReal (x ^ (2 * σ - 2))) := by
        unfold weightedMeasure
        have h_restrict_eq :
            ((volume.withDensity fun x : ℝ => ENNReal.ofReal x⁻¹).restrict
            (Set.Ioi (0 : ℝ))).withDensity (weightFunction σ)
              = (volume.withDensity fun x : ℝ => ENNReal.ofReal x⁻¹).withDensity
                  ((Set.Ioi (0 : ℝ)).indicator (weightFunction σ)) := by
          simpa using
            (withDensity_indicator (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal x⁻¹)
              (s := Set.Ioi (0 : ℝ)) (f := weightFunction σ) measurableSet_Ioi).symm
        have h_mul_density :
            (volume.withDensity fun x : ℝ => ENNReal.ofReal x⁻¹).withDensity
                ((Set.Ioi (0 : ℝ)).indicator (weightFunction σ))
              = volume.withDensity
                  (fun x : ℝ => ENNReal.ofReal x⁻¹ *
                    (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x) :=
          withDensity_mul_indicator σ
        have h_combined :
            ((volume.withDensity fun x : ℝ => ENNReal.ofReal x⁻¹).restrict
            (Set.Ioi (0 : ℝ))).withDensity (weightFunction σ)
              = volume.withDensity (Set.indicator (Set.Ioi (0 : ℝ))
                fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 2))) := by
          calc
            ((volume.withDensity fun x : ℝ => ENNReal.ofReal x⁻¹).restrict
            (Set.Ioi (0 : ℝ))).withDensity (weightFunction σ)
                = (volume.withDensity fun x : ℝ => ENNReal.ofReal x⁻¹).withDensity
                    ((Set.Ioi (0 : ℝ)).indicator (weightFunction σ)) := h_restrict_eq
            _ = volume.withDensity
                    (fun x : ℝ => ENNReal.ofReal x⁻¹ *
                      (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x) := h_mul_density
            _ = volume.withDensity
                    (Set.indicator (Set.Ioi (0 : ℝ))
                      fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 2))) := by
                simp [h_product]
        simpa [mulHaar] using h_combined
      have :=
        lintegral_withDensity_eq_lintegral_mul (μ := volume)
          (f := Set.indicator (Set.Ioi (0 : ℝ))
            fun x => ENNReal.ofReal (x ^ (2 * σ - 2)))
          (g := fun x => ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2))
      have h_mul :
          ∀ x,
            Set.indicator (Set.Ioi (0 : ℝ))
                (fun y => ENNReal.ofReal (y ^ (2 * σ - 2))) x
              * ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2)
              = Set.indicator (Set.Ioi (0 : ℝ)) w x := by
        intro x
        by_cases hx : x ∈ Set.Ioi (0 : ℝ)
        · have hx_pos : 0 < x := hx
          have hx_indicator :
              Set.indicator (Set.Ioi (0 : ℝ))
                  (fun y : ℝ => ENNReal.ofReal (y ^ (2 * σ - 2))) x
                = ENNReal.ofReal (x ^ (2 * σ - 2)) := by
            simp [Set.indicator_of_mem, hx]
          have hx_w_value :
              Set.indicator (Set.Ioi (0 : ℝ)) w x
                = ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 2)) := by
            simp [w, Set.indicator_of_mem, hx, mul_comm]
          have hx_pow_nonneg : 0 ≤ x ^ (2 * σ - 2) :=
            Real.rpow_nonneg (le_of_lt hx_pos) _
          have hx_prod :
              ENNReal.ofReal (x ^ (2 * σ - 2) * ‖(s : ℝ → ℂ) x‖ ^ 2)
                = ENNReal.ofReal (x ^ (2 * σ - 2))
                  * ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2) :=
            ENNReal.ofReal_mul hx_pow_nonneg
          calc
            Set.indicator (Set.Ioi (0 : ℝ))
                (fun y => ENNReal.ofReal (y ^ (2 * σ - 2))) x *
                  ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2)
                = ENNReal.ofReal (x ^ (2 * σ - 2)) *
                    ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2) := by
                  rw [hx_indicator]
            _ = ENNReal.ofReal (x ^ (2 * σ - 2) * ‖(s : ℝ → ℂ) x‖ ^ 2) := by
                  simpa [mul_comm, mul_left_comm, mul_assoc] using hx_prod.symm
            _ = Set.indicator (Set.Ioi (0 : ℝ)) w x := by
                  simp [hx_w_value, mul_comm]
        · simp [w, Set.indicator_of_notMem, hx]
      have h_measurable_norm :
          Measurable fun x => ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2) := by
        refine Measurable.ennreal_ofReal ?_
        exact ((Lp.stronglyMeasurable s).norm.pow 2).measurable
      have h_measurable_indicator :
          Measurable fun x : ℝ =>
            Set.indicator (Set.Ioi (0 : ℝ))
              (fun y => ENNReal.ofReal (y ^ (2 * σ - 2))) x := by
        have h_meas_inv₁ : Measurable fun x : ℝ => ENNReal.ofReal ((1 : ℝ) / x) := by
          refine Measurable.ennreal_ofReal ?_
          simpa using (Measurable.div measurable_const measurable_id)
        have h_meas_inv : Measurable fun x : ℝ => ENNReal.ofReal x⁻¹ := by
          simpa [one_div] using h_meas_inv₁
        have h_meas_weight :
            Measurable fun x : ℝ =>
              (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x :=
          (weightFunction_measurable σ).indicator measurableSet_Ioi
        have h_meas_prod :
            Measurable fun x : ℝ =>
              ENNReal.ofReal x⁻¹ *
                (Set.Ioi (0 : ℝ)).indicator (weightFunction σ) x :=
          h_meas_inv.mul h_meas_weight
        simpa [h_product] using h_meas_prod
      have h_indicator_integral :
          ∫⁻ x, Set.indicator (Set.Ioi (0 : ℝ)) w x ∂volume
            = ∫⁻ x,
                Set.indicator (Set.Ioi (0 : ℝ))
                    (fun y => ENNReal.ofReal (y ^ (2 * σ - 2))) x *
                  ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2) ∂volume := by
        refine lintegral_congr_ae ?_
        exact Filter.Eventually.of_forall fun x => (h_mul x).symm
      have h_eq := this h_measurable_indicator h_measurable_norm
      have h_eq' := h_eq.symm
      calc
        ∫⁻ x, Set.indicator (Set.Ioi (0 : ℝ)) w x ∂volume
            = ∫⁻ x,
                Set.indicator (Set.Ioi (0 : ℝ))
                    (fun y => ENNReal.ofReal (y ^ (2 * σ - 2))) x *
                  ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2) ∂volume := h_indicator_integral
        _ = ∫⁻ x, ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2)
              ∂volume.withDensity
                ((Set.Ioi (0 : ℝ)).indicator fun x =>
                  ENNReal.ofReal (x ^ (2 * σ - 2))) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq'
        _ = ∫⁻ x, ENNReal.ofReal (‖(s : ℝ → ℂ) x‖ ^ 2)
              ∂(weightedMeasure σ) := by
            simp [h_density]
    exact lt_of_le_of_lt h_restrict_le
      (by simpa [h_weight_eq] using h_weight)
  -- Conclude that the lintegral of ‖f‖² is finite.
  have h_norm_sq_global :
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ
        = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun x => by simp)
  have h_normsq_lt :
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ∞ :=
    lt_of_le_of_lt h_integral_bound
      (ENNReal.mul_lt_top (by simp) h_weight_integral_lt)
  have h_lintegral_finite :
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ < ∞ := by
    simpa [h_norm_sq_global] using h_normsq_lt
  have hf_finite : HasFiniteIntegral (fun x => ‖f x‖ ^ 2) μ := by
    simpa [HasFiniteIntegral] using h_lintegral_finite
  exact memLp_of_hasFiniteIntegral_and_aestronglyMeasurable hf_meas hf_finite

/-- Integrability on support for Lp functions on finite measure sets -/
lemma integrable_on_truncated_function {f : ℝ → ℂ} {R : ℝ} {p : ℝ≥0∞}
    (h_memLp : MemLp f p (volume.restrict (Set.Ioc 0 R))) (hp : 1 ≤ p) :
    IntegrableOn f (Set.Ioc 0 R) volume := by
  classical
  -- Work on the restricted measure μ := volume.restrict (Set.Ioc 0 R).
  set μ := volume.restrict (Set.Ioc (0 : ℝ) R)
  have h_meas_set : MeasurableSet (Set.Ioc (0 : ℝ) R) := measurableSet_Ioc
  -- The interval has finite measure, hence the restricted measure is finite.
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, Measure.restrict_apply, Set.univ_inter]
  -- Use monotonicity of the Lᵖ scale on finite measures to move from p to 1.
  have h_memLp_one : MemLp f 1 μ :=
    (MemLp.mono_exponent (μ := μ) (p := 1) (q := p) h_memLp hp)
  -- Membership in L¹ is equivalent to integrability.
  have hf_integrable : Integrable f μ :=
    (memLp_one_iff_integrable).mp h_memLp_one
  -- Translate back to an `IntegrableOn` statement.
  simpa [IntegrableOn, μ] using hf_integrable

/-- Truncated Lp functions are integrable with respect to volume measure
    NOTE: This requires σ ≤ 1 for the proof to work through L² membership.
    For σ > 1, a different approach would be needed.
-/
lemma lp_truncation_integrable {σ : ℝ} (hσ_upper : σ ≤ 1) (s : Lp ℂ 2 (weightedMeasure σ)) (R : ℝ) :
    Integrable (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) volume := by
  -- The main strategy: use Cauchy-Schwarz with the weight decomposition
  -- For σ ∈ (1/2, 3/2), we can bound ∫₀ᴿ |s(x)| dx using the weighted L² norm

  have h_meas : AEStronglyMeasurable
      (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) volume := by
    -- Use the fact that ite can be expressed as piecewise
    have h_eq : (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) =
                (Set.Ioc 0 R).piecewise (s : ℝ → ℂ) 0 := by
      ext x
      simp [Set.piecewise, Set.mem_Ioc]
    rw [h_eq]
    exact AEStronglyMeasurable.piecewise measurableSet_Ioc
      (lp_restricted_aestronglyMeasurable s R) aestronglyMeasurable_const.restrict

  have h_finite_support : volume (Set.Ioc 0 R) < ∞ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top

  have h_bounded_support : IsCompact (Set.Icc 0 R) := isCompact_Icc
  have h_supported : Function.support (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) ⊆
      Set.Icc 0 R := by
    intro x hx
    simp only [Function.mem_support, ite_ne_right_iff] at hx
    exact ⟨le_of_lt hx.1.1, hx.1.2⟩

  have h_restrict_finite : volume (Set.Ioc 0 R) < ∞ := h_finite_support
  have h_support_subset : Function.support (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) ⊆
      Set.Ioc 0 R := by
    intro x hx
    simp only [Function.mem_support, ite_ne_right_iff] at hx
    exact ⟨hx.1.1, hx.1.2⟩

  -- Apply the general principle: measurable functions with finite support on finite measure sets
  -- are integrable. Since [0,R] has finite volume and the function is measurable with support
  -- in [0,R], it is integrable by the standard theory of finite measure spaces

  -- Use that the truncated function is in Lp on the interval
  have h_memLp : MemLp (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) 2
      (volume.restrict (Set.Ioc 0 R)) :=
    lp_truncation_memLp_on_Ioc hσ_upper s R 2 rfl

  have h_integrable_on_support :
      IntegrableOn (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) (Set.Ioc 0 R) volume :=
    integrable_on_truncated_function h_memLp (by norm_num : 1 ≤ (2 : ℝ≥0∞))

  have h_eq_indicator : (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) =
      Set.indicator (Set.Ioc 0 R) (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) := by
    ext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) R
    · have hx' : 0 < x ∧ x ≤ R := hx
      simp [Set.indicator, hx, hx'.1, hx'.2]
    · have hx' : ¬ (0 < x ∧ x ≤ R) := by simpa [Set.mem_Ioc] using hx
      simp [Set.indicator, hx, hx']

  -- Use the indicator function characterization
  rw [h_eq_indicator]
  exact (integrable_indicator_iff measurableSet_Ioc).mpr h_integrable_on_support

/-- Positive truncation of Lp function is also in Lp for weighted measure -/
lemma positive_truncation_memLp {σ : ℝ} (s : Lp ℂ 2 (weightedMeasure σ)) (R : ℝ) :
    MemLp (fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) 2 (weightedMeasure σ) := by
  -- Since the positive truncation only differs from the original truncation on non-positive reals,
  -- and weightedMeasure σ vanishes there, they are equivalent in L²
  classical
  -- Express the truncation using an indicator on the interval `(0, R]`.
  have h_indicator_eq :
      (fun x : ℝ => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0)
        = Set.indicator (Set.Ioc (0 : ℝ) R) (fun x => (s : ℝ → ℂ) x) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) R
    · have hx' : 0 < x ∧ x ≤ R := hx
      simp [Set.indicator, hx, hx'.1, hx'.2]
    · have hx' : ¬ (0 < x ∧ x ≤ R) := by simpa [Set.mem_Ioc] using hx
      simp [Set.indicator, hx, hx']
  -- Apply the indicator lemma for `MemLp`.
  simpa [h_indicator_eq]
    using (MemLp.indicator (μ := weightedMeasure σ) (p := 2)
      (s := Set.Ioc (0 : ℝ) R) (f := fun x => (s : ℝ → ℂ) x)
      measurableSet_Ioc (Lp.memLp s))

/-- Error bound for positive truncation vs tail truncation -/
lemma positive_truncation_error_bound {σ : ℝ} (s : Lp ℂ 2 (weightedMeasure σ)) (R : ℝ) (ε : ℝ)
    (hR_truncation : eLpNorm (fun x => if |x| > R then (s : ℝ → ℂ) x else 0) 2
      (weightedMeasure σ) < ENNReal.ofReal ε) :
    let s_R : ℝ → ℂ := fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0
    eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ) < ENNReal.ofReal ε := by
  -- Since s_R only differs from the original truncation on non-positive reals,
  -- and weightedMeasure σ vanishes there, the L² norms are equal
  -- This follows because weightedMeasure σ has support only on (0,∞)
  classical
  change eLpNorm ((s : ℝ → ℂ) - fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0) 2
      (weightedMeasure σ) < ENNReal.ofReal ε
  set s_R_fun : ℝ → ℂ := fun x => if 0 < x ∧ x ≤ R then (s : ℝ → ℂ) x else 0 with hs_R_fun
  have h_goal :
      eLpNorm ((s : ℝ → ℂ) - s_R_fun) 2 (weightedMeasure σ) < ENNReal.ofReal ε := by
    classical
    set f : ℝ → ℂ := fun x => if 0 < x ∧ x ≤ R then (0 : ℂ) else (s : ℝ → ℂ) x with hf_def
    set g : ℝ → ℂ := fun x => if |x| > R then (s : ℝ → ℂ) x else 0 with hg_def
    have hf_eq : ((s : ℝ → ℂ) - s_R_fun) = f := by
      funext x
      by_cases hx : 0 < x ∧ x ≤ R
      · simp [hf_def, hs_R_fun, hx]
      · simp [hf_def, hs_R_fun, hx]
    have h_subset : {x : ℝ | f x ≠ g x} ⊆ Set.Icc (-R) 0 := by
      intro x hx
      by_cases hx_pos : 0 < x
      · have hx_abs : |x| = x := abs_of_pos hx_pos
        by_cases hx_le : x ≤ R
        · have hx_cond : 0 < x ∧ x ≤ R := ⟨hx_pos, hx_le⟩
          have hx_eq : f x = g x := by
            simp [hf_def, hg_def, hx_cond, hx_abs, not_lt_of_ge hx_le]
          exact (hx hx_eq).elim
        · have hx_gt : R < x := lt_of_not_ge hx_le
          have hx_eq : f x = g x := by
            simp [hf_def, hg_def, hx_pos, hx_le, hx_gt, hx_abs]
          exact (hx hx_eq).elim
      · have hx_nonpos : x ≤ 0 := le_of_not_gt hx_pos
        have hx_notpos : ¬ 0 < x := not_lt.mpr hx_nonpos
        by_cases hx_abs_gt : R < |x|
        · have hx_eq : f x = g x := by
            have hx_gtabs : |x| > R := hx_abs_gt
            simp [hf_def, hg_def, hx_notpos, hx_gtabs]
          exact (hx hx_eq).elim
        · have hx_abs_le : |x| ≤ R := le_of_not_gt hx_abs_gt
          have hx_bounds := abs_le.mp hx_abs_le
          exact ⟨hx_bounds.1, hx_nonpos⟩
    have h_zero_nonpos : (weightedMeasure σ) (Set.Iic (0 : ℝ)) = 0 := by
      have h_apply := weightedMeasure_apply σ (Set.Iic (0 : ℝ)) measurableSet_Iic
      have h_inter : Set.Iic (0 : ℝ) ∩ Set.Ioi (0 : ℝ) = (∅ : Set ℝ) := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨hx_le, hx_gt⟩
          have hx_gt' : 0 < x := hx_gt
          exact (not_lt_of_ge hx_le) hx_gt'
        · intro hx
          simp at hx
      simpa [h_inter] using h_apply
    have h_Icc_zero : (weightedMeasure σ) (Set.Icc (-R) 0) = 0 := by
      have hsubset : Set.Icc (-R) 0 ⊆ Set.Iic (0 : ℝ) := by
        intro x hx
        exact hx.2
      exact measure_mono_null hsubset h_zero_nonpos
    have h_diff_zero : (weightedMeasure σ) {x : ℝ | f x ≠ g x} = 0 :=
      measure_mono_null h_subset h_Icc_zero
    have h_ae_eq : f =ᵐ[weightedMeasure σ] g := (ae_iff).2 h_diff_zero
    calc
      eLpNorm ((s : ℝ → ℂ) - s_R_fun) 2 (weightedMeasure σ)
          = eLpNorm f 2 (weightedMeasure σ) := by
            simp [hf_eq]
      _ = eLpNorm g 2 (weightedMeasure σ) := eLpNorm_congr_ae h_ae_eq
      _ = eLpNorm (fun x : ℝ => if |x| > R then (s : ℝ → ℂ) x else 0) 2
            (weightedMeasure σ) := by simp [hg_def]
      _ < ENNReal.ofReal ε := hR_truncation
  simpa [hs_R_fun] using h_goal

/-- Convolution of integrable function with smooth compact support function is continuous -/
lemma convolution_integrable_smooth_continuous {f : ℝ → ℂ} {φ : ℝ → ℝ}
    (hf_integrable : Integrable f volume) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) :
    Continuous (fun x => ∫ y, f y * φ (x - y) ∂volume) := by
  classical
  -- Work with the complex-valued version of the kernel to apply convolution lemmas.
  let φℂ : ℝ → ℂ := fun x => (φ x : ℂ)
  have h_support_eq : Function.support φℂ = Function.support φ := by
    ext x; simp [φℂ, Function.mem_support]
  have hφℂ_compact : HasCompactSupport φℂ := by
    simpa [HasCompactSupport, tsupport, φℂ, h_support_eq] using hφ_compact
  have hφℂ_smooth : ContDiff ℝ (⊤ : ℕ∞) φℂ := by
    simpa [φℂ, Complex.ofRealCLM_apply]
      using (Complex.ofRealCLM.contDiff.comp hφ_smooth)
  -- Apply the general statement that convolution with a smooth compact kernel is smooth.
  have h_contDiff :=
    hφℂ_compact.contDiff_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
      (hf := hf_integrable.locallyIntegrable) (hg := hφℂ_smooth)
  have h_cont : Continuous
      (convolution f φℂ (ContinuousLinearMap.mul ℝ ℂ) volume) :=
    h_contDiff.continuous
  -- The convolution coincides with the desired integral expression.
  have h_eq : (fun x => ∫ y, f y * φ (x - y) ∂volume)
      = convolution f φℂ (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext x
    simp [convolution_def, φℂ]
  simpa [h_eq]
    using h_cont

/-- Volume convolution with smooth compact kernel preserves L² membership in weighted spaces
    when f has bounded support -/
lemma convolution_memLp_weighted {σ : ℝ} (hσ : 1 / 2 < σ)
    {f : ℝ → ℂ} {φ : ℝ → ℝ} (R δ : ℝ) (hR_pos : 0 < R) (hδ_pos : 0 < δ)
    (hf_support : Function.support f ⊆ Set.Icc (-R) R)
    (_hf_memLp : MemLp f 2 (weightedMeasure σ))
    (hf_vol_integrable : LocallyIntegrable f volume)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : Function.support φ ⊆ Set.Icc (-δ) δ) :
    MemLp (fun x => ∫ y, f y * φ (x - y) ∂volume) 2 (weightedMeasure σ) := by
  classical
  -- Introduce the convolution function that we want to study.
  set g : ℝ → ℂ := fun x => ∫ y, f y * (φ (x - y) : ℂ) ∂volume with hg_def

  -- Outside [-R, R] the function f vanishes thanks to the support assumption.
  have hf_zero_outside : ∀ {x}, x ∉ Set.Icc (-R) R → f x = 0 := by
    intro x hx
    by_contra hx0
    have hx_support : x ∈ Function.support f := by
      simp [Function.mem_support, hx0]
    have hx_mem := hf_support hx_support
    exact hx (by simpa [Set.mem_Icc] using hx_mem)

  -- f is integrable on its support, hence integrable on ℝ.
  have hf_integrableOn : IntegrableOn f (Set.Icc (-R) R) volume := by
    have :=
      (hf_vol_integrable.integrableOn_isCompact
        (μ := volume) (f := f) (k := Set.Icc (-R) R) isCompact_Icc)
    simpa using this
  have hf_eq_indicator :
      f = Set.indicator (Set.Icc (-R) R) f := by
    funext x
    by_cases hx : x ∈ Set.Icc (-R) R
    · simp [Set.indicator_of_mem, hx]
    · simp [Set.indicator_of_notMem, hx, hf_zero_outside hx]
  have hf_integrable_indicator :
      Integrable (Set.indicator (Set.Icc (-R) R) f) volume :=
    (integrable_indicator_iff (μ := volume) measurableSet_Icc).mpr hf_integrableOn
  have hf_ae_eq :
      Set.indicator (Set.Icc (-R) R) f =ᵐ[volume] f := by
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : x ∈ Set.Icc (-R) R
    · simp [Set.indicator_of_mem, hx]
    · simp [Set.indicator_of_notMem, hx, hf_zero_outside hx]
  have hf_integrable : Integrable f volume :=
    hf_integrable_indicator.congr hf_ae_eq

  -- The convolution is continuous by the standard convolution lemma.
  have hg_cont : Continuous g := by
    simpa [hg_def]
      using convolution_integrable_smooth_continuous hf_integrable hφ_smooth hφ_compact

  -- The support of g lies inside [-(R+δ), R+δ].
  have hg_support_subset :
      Function.support g ⊆ Set.Icc (-(R + δ)) (R + δ) := by
    intro x hx
    have hx_ne : g x ≠ 0 := hx
    have hx_in : x ∈ Set.Icc (-(R + δ)) (R + δ) := by
      by_contra hx_not
      have hx_cases : x < -(R + δ) ∨ R + δ < x := by
        by_cases hx_le : x ≤ R + δ
        · have hx_lt : x < -(R + δ) := by
            have : ¬(-(R + δ) ≤ x) := fun h => hx_not ⟨h, hx_le⟩
            exact lt_of_not_ge this
          exact Or.inl hx_lt
        · exact Or.inr (lt_of_not_ge hx_le)
      have h_zero : g x = 0 := by
        have h_pointwise :
            (fun y => f y * (φ (x - y) : ℂ)) = fun _ => (0 : ℂ) := by
          funext y
          classical
          by_cases hy : y ∈ Set.Icc (-R) R
          · have hy_lower : -R ≤ y := hy.1
            have hy_upper : y ≤ R := hy.2
            have hy_abs : |y| ≤ R := abs_le.mpr ⟨hy_lower, hy_upper⟩
            have hx_abs_big : |x| > R + δ := by
              cases hx_cases with
              | inl hx_lt =>
                  have hx_neg : x < 0 :=
                    lt_trans hx_lt (neg_lt_zero.mpr (add_pos hR_pos hδ_pos))
                  have hx_pos : -x > R + δ := by
                    have := neg_lt_neg hx_lt
                    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                  simpa [abs_of_neg hx_neg] using hx_pos
              | inr hx_gt =>
                  have hx_pos : 0 < x := lt_trans (add_pos hR_pos hδ_pos) hx_gt
                  simpa [abs_of_pos hx_pos] using hx_gt
            have hy_bound : |y| + δ ≤ R + δ := add_le_add_right hy_abs δ
            have hx_gt : |y| + δ < |x| := lt_of_le_of_lt hy_bound hx_abs_big
            have hx_minus : δ < |x| - |y| :=
              lt_sub_iff_add_lt.mpr (by simpa [add_comm] using hx_gt)
            have hx_diff_nonneg : 0 ≤ |x| - |y| :=
              le_of_lt (lt_trans hδ_pos hx_minus)
            have hx_abs : |x - y| > δ := by
              have hx_abs_sub : |x| - |y| ≤ |x - y| := by
                have := abs_abs_sub_abs_le_abs_sub x y
                simpa [abs_of_nonneg hx_diff_nonneg] using this
              exact lt_of_lt_of_le hx_minus hx_abs_sub
            have hx_not_mem : x - y ∉ Function.support φ := by
              intro hx_mem
              have hx_mem' := hφ_support hx_mem
              have hx_le : |x - y| ≤ δ := abs_le.mpr hx_mem'
              exact (not_le_of_gt hx_abs) hx_le
            have : φ (x - y) = 0 := Function.notMem_support.mp hx_not_mem
            simp [this]
          · have : f y = 0 := hf_zero_outside hy
            simp [this]
        simp [hg_def, h_pointwise]
      exact hx_ne h_zero
    exact hx_in

  -- Convert the support inclusion into actual compact support information.
  have hg_compactSupport : HasCompactSupport g := by
    rw [HasCompactSupport]
    apply IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
    exact closure_minimal hg_support_subset isClosed_Icc

  -- g is measurable with respect to the weighted measure thanks to continuity.
  have hg_meas : AEStronglyMeasurable g (weightedMeasure σ) :=
    hg_cont.aestronglyMeasurable

  -- Obtain a non-negative bound on g over its topological support.
  have hg_bounded : ∃ M ≥ 0, ∀ x ∈ tsupport g, ‖g x‖ ≤ M := by
    classical
    have h_compact : IsCompact (tsupport g) := hg_compactSupport
    by_cases h_nonempty : (tsupport g).Nonempty
    · obtain ⟨x₀, hx₀, hx₀_max⟩ :=
        h_compact.exists_isMaxOn h_nonempty ((hg_cont.continuousOn).norm)
      refine ⟨‖g x₀‖, norm_nonneg _, ?_⟩
      intro x hx
      exact hx₀_max hx
    · refine ⟨0, le_of_eq rfl, ?_⟩
      intro x hx
      exact (h_nonempty ⟨x, hx⟩).elim

  obtain ⟨M, hM_nonneg, hM_bound⟩ := hg_bounded

  -- Build a domination by a constant on the whole space.
  have h_dominated : ∀ᵐ x ∂(weightedMeasure σ), ‖g x‖ ^ 2 ≤ M ^ 2 := by
    filter_upwards with x
    by_cases hx : x ∈ tsupport g
    · have hx_le := hM_bound x hx
      have hx_nonneg : 0 ≤ ‖g x‖ := norm_nonneg _
      have hx_mul : ‖g x‖ * ‖g x‖ ≤ M * M :=
        mul_le_mul hx_le hx_le hx_nonneg hM_nonneg
      simpa [pow_two] using hx_mul
    · have hx_zero : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hM_sq_nonneg : 0 ≤ M * M := mul_self_nonneg M
      simp [hx_zero, pow_two, hM_sq_nonneg]

  -- The weighted measure of the compact support is finite.
  have h_support_measure : (weightedMeasure σ) (tsupport g) < ∞ := by
    have htsupport_compact : IsCompact (tsupport g) := hg_compactSupport
    exact weightedMeasure_finite_on_compact hσ htsupport_compact

  have hg_finite : HasFiniteIntegral (fun x => ‖g x‖ ^ 2) (weightedMeasure σ) :=
    hasFiniteIntegral_of_dominated_on_compactSupport h_dominated h_support_measure

  have hg_memLp : MemLp g 2 (weightedMeasure σ) :=
    memLp_of_hasFiniteIntegral_and_aestronglyMeasurable hg_meas hg_finite

  simpa [hg_def] using hg_memLp

/-- Distance bound from truncation error for Lp elements -/
lemma dist_lp_truncation_bound {σ : ℝ} (s : Lp ℂ 2 (weightedMeasure σ)) (ε : ℝ) (hε : 0 < ε)
    (s_R : ℝ → ℂ) (hs_R_memLp : MemLp s_R 2 (weightedMeasure σ))
    (h_truncation_error : eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ) < ENNReal.ofReal ε) :
    dist s (hs_R_memLp.toLp s_R) < ε := by
  classical
  -- Express the metric distance in terms of the extended L² norm difference.
  have h_dist_repr :
      dist s (hs_R_memLp.toLp s_R)
        = ENNReal.toReal
            (eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ)) := by
    have h_eLp_congr :
        eLpNorm ((s : ℝ → ℂ) - (hs_R_memLp.toLp s_R : ℝ → ℂ)) 2
            (weightedMeasure σ)
          = eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ) := by
      simpa using (eLpNorm_lp_function_diff_eq (σ := σ) s s_R hs_R_memLp)
    have h_norm_repr :
        ‖s - hs_R_memLp.toLp s_R‖
          = ENNReal.toReal
              (eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ)) := by
      have h_norm_def :
          ‖s - hs_R_memLp.toLp s_R‖
            = ENNReal.toReal
                (eLpNorm (((s - hs_R_memLp.toLp s_R : Lp ℂ 2 (weightedMeasure σ)) :
                    ℝ → ℂ)) 2 (weightedMeasure σ)) := by
        simp [Lp.norm_def]
      have h_coe_ae :
          ((s - hs_R_memLp.toLp s_R : Lp ℂ 2 (weightedMeasure σ)) : ℝ → ℂ)
            =ᵐ[weightedMeasure σ]
              (fun x => (s : ℝ → ℂ) x - (hs_R_memLp.toLp s_R : ℝ → ℂ) x) :=
        Lp.coeFn_sub s (hs_R_memLp.toLp s_R)
      have h_toReal_coe :
          ENNReal.toReal
              (eLpNorm (((s - hs_R_memLp.toLp s_R : Lp ℂ 2 (weightedMeasure σ)) :
                  ℝ → ℂ)) 2 (weightedMeasure σ))
            = ENNReal.toReal
                (eLpNorm ((s : ℝ → ℂ) - (hs_R_memLp.toLp s_R : ℝ → ℂ)) 2
                  (weightedMeasure σ)) :=
        congrArg ENNReal.toReal (eLpNorm_congr_ae h_coe_ae)
      have h_toReal_congr :
          ENNReal.toReal
              (eLpNorm ((s : ℝ → ℂ) - (hs_R_memLp.toLp s_R : ℝ → ℂ)) 2
                (weightedMeasure σ))
            = ENNReal.toReal
                (eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ)) :=
        congrArg ENNReal.toReal h_eLp_congr
      exact h_norm_def.trans (h_toReal_coe.trans h_toReal_congr)
    simpa [dist_eq_norm] using h_norm_repr
  -- Use the assumed truncation error bound to control this real quantity.
  have h_lt_top :
      eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ) < ∞ :=
    lt_of_lt_of_le h_truncation_error (le_top : ENNReal.ofReal ε ≤ ∞)
  have h_ne_top :
      eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ) ≠ ∞ :=
    ne_of_lt h_lt_top
  have h_toReal_lt :
      ENNReal.toReal
          (eLpNorm ((s : ℝ → ℂ) - s_R) 2 (weightedMeasure σ)) < ε := by
    have :=
      (ENNReal.toReal_lt_toReal h_ne_top ENNReal.ofReal_ne_top).2 h_truncation_error
    simpa [ENNReal.toReal_ofReal (le_of_lt hε)] using this
  -- Conclude the desired distance estimate.
  simpa [h_dist_repr] using h_toReal_lt

/-- Truncation approximation: Any L² function can be approximated
    by compactly supported functions -/
lemma truncation_approximation {σ : ℝ} (hσ : 1 / 2 < σ)
    (f : ℝ → ℂ) (hf_memLp : MemLp f 2 (weightedMeasure σ))
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ (R : ℝ) (_ : 0 < R) (f_R : ℝ → ℂ) (_ : MemLp f_R 2 (weightedMeasure σ)),
      HasCompactSupport f_R ∧
      eLpNorm (f - f_R) 2 (weightedMeasure σ) < ENNReal.ofReal (ε / 2) := by
  -- Use the tail vanishing property of L² functions
  -- For L² functions on weighted measure, the tail ∫_{|x|>R} |f|² → 0 as R → ∞
  obtain ⟨R, hR_pos, hR_truncation⟩ : ∃ R : ℝ, 0 < R ∧
      eLpNorm (fun x => if |x| > R then f x else 0) 2 (weightedMeasure σ) <
      ENNReal.ofReal (ε / 2) := by
    -- This uses the fact that L² functions have vanishing tails
    classical
    obtain ⟨R₀, hR₀_pos, hR₀_truncation⟩ :=
      lp_tail_vanishing hσ (hf_memLp.toLp f) (ε / 2) (by linarith : 0 < ε / 2)
    refine ⟨R₀, hR₀_pos, ?_⟩
    have h_ae_eq :
        (fun x : ℝ => if |x| > R₀ then (hf_memLp.toLp f : ℝ → ℂ) x else 0)
          =ᵐ[weightedMeasure σ]
        (fun x : ℝ => if |x| > R₀ then f x else 0) := by
      have h_coe := MemLp.coeFn_toLp hf_memLp
      filter_upwards [h_coe] with x hx
      by_cases h : |x| > R₀
      · have hx' : (hf_memLp.toLp f : ℝ → ℂ) x = f x := hx
        simp [h, hx']
      · have hx' : (hf_memLp.toLp f : ℝ → ℂ) x = f x := hx
        simp [h]
    have h_eq :
        eLpNorm (fun x : ℝ => if |x| > R₀ then (hf_memLp.toLp f : ℝ → ℂ) x else 0) 2
            (weightedMeasure σ) =
        eLpNorm (fun x : ℝ => if |x| > R₀ then f x else 0) 2 (weightedMeasure σ) :=
      eLpNorm_congr_ae (μ := weightedMeasure σ) (p := (2 : ℝ≥0∞)) h_ae_eq
    simpa [h_eq] using hR₀_truncation

  -- Define the truncated function
  let f_R : ℝ → ℂ := fun x => if |x| ≤ R then f x else 0

  -- Show f_R has compact support
  have hf_R_compact : HasCompactSupport f_R := by
    rw [HasCompactSupport]
    have h_support : Function.support f_R ⊆ Set.Icc (-R) R := by
      intro x hx
      simp [f_R, Function.mem_support] at hx
      by_cases h : |x| ≤ R
      · exact abs_le.mp h
      · simp [h] at hx
    apply IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
    exact closure_minimal h_support isClosed_Icc

  -- Show f_R is in L²
  have hf_R_memLp : MemLp f_R 2 (weightedMeasure σ) := by
    -- f_R is a truncation of an L² function, hence also in L²
    classical
    have h_meas : MeasurableSet {x : ℝ | |x| ≤ R} := by
      have h_closed : IsClosed {x : ℝ | |x| ≤ R} := by
        simpa [Set.preimage, Set.mem_setOf_eq]
          using (isClosed_Iic.preimage continuous_norm)
      exact h_closed.measurableSet
    have h_indicator_eq :
        f_R = Set.indicator {x : ℝ | |x| ≤ R} f := by
      funext x
      by_cases hx : |x| ≤ R
      · simp [f_R, Set.indicator, Set.mem_setOf_eq, hx]
      · simp [f_R, Set.indicator, Set.mem_setOf_eq, hx]
    have hf_indicator :
        MemLp (Set.indicator {x : ℝ | |x| ≤ R} f) 2 (weightedMeasure σ) :=
      MemLp.indicator (μ := weightedMeasure σ) (p := (2 : ℝ≥0∞))
        (s := {x : ℝ | |x| ≤ R}) (f := f) h_meas hf_memLp
    simpa [f_R, h_indicator_eq.symm]
      using hf_indicator -- Truncation preserves L² membership

  -- Show the approximation error
  have h_error : eLpNorm (f - f_R) 2 (weightedMeasure σ) < ENNReal.ofReal (ε / 2) := by
    -- f - f_R = (function that is f outside [-R,R] and 0 inside)
    have h_eq : f - f_R = fun x => if |x| > R then f x else 0 := by
      funext x
      simp [f_R]
      by_cases h : |x| ≤ R
      · simp [h]
      · simp [h, lt_of_not_ge h]
    rw [h_eq]
    exact hR_truncation

  exact ⟨R, hR_pos, f_R, hf_R_memLp, hf_R_compact, h_error⟩

/-- The weighted measure is equivalent to withDensity measure -/
lemma weightedMeasure_eq_withDensity (σ : ℝ) :
    weightedMeasure σ = mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
  classical
  have h :
      weightFunction σ =ᵐ[mulHaar]
        fun x => ENNReal.ofReal (x ^ (2 * σ - 1)) := by
    change
        weightFunction σ
            =ᵐ[(volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)).restrict
                (Set.Ioi (0 : ℝ))]
          fun x => ENNReal.ofReal (x ^ (2 * σ - 1))
    refine
      (ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))).2 ?_
    apply Filter.Eventually.of_forall
    intro x hx
    have hx_pos : 0 < x := by simpa [Set.mem_Ioi] using hx
    simp [weightFunction, hx_pos]
  simpa [weightedMeasure] using (withDensity_congr_ae h)

end SchwartzDensity

end Frourio
