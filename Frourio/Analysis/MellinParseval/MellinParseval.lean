import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore1
import Frourio.Analysis.HilbertSpaceCore
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

open MeasureTheory Measure Real Complex Set
open scoped ENNReal Topology FourierTransform

namespace Frourio
open Schwartz

section ParsevalEquivalence

-- Complex measure-theoretic proof involving pushforward measures and absolute continuity
/-- Integrability of the weighted LogPull is preserved under addition -/
lemma LogPull_integrable_add (σ : ℝ) (f g : Hσ σ)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
    (hg_int : Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :
    Integrable (fun t => LogPull σ (f + g) t * Complex.exp ((1 / 2 : ℝ) * t)) := by
  classical
  -- We will rewrite the integrand a.e. using the a.e. linearity of the Lp
  -- representative `Hσ.toFun` transported along `x = exp t`.
  -- Start from the a.e. identity on the physical side (x-variable).
  have h_add_ae_weighted := toFun_add_ae σ f g
  -- Transport the a.e. equality to the Lebesgue measure on (0,∞).
  have h_rev_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ
  have h_add_ae_vol :
      (fun x : ℝ => Hσ.toFun (f + g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x + Hσ.toFun g x) :=
    h_rev_ac.ae_eq h_add_ae_weighted
  -- Also, mulHaar is absolutely continuous w.r.t. the restricted Lebesgue measure.
  have h_mulHaar_to_volume : mulHaar ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    -- Absolute continuity for withDensity followed by restriction
    have h_base :
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)) ≪ volume := by
      simpa using
        (withDensity_absolutelyContinuous
          (μ := volume) (f := fun x : ℝ => ENNReal.ofReal (1 / x)))
    simpa [mulHaar] using h_base.restrict (Set.Ioi (0 : ℝ))
  -- Hence the equality also holds a.e. for mulHaar on (0,∞).
  have h_add_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (f + g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => Hσ.toFun f x + Hσ.toFun g x) :=
    h_mulHaar_to_volume.ae_eq h_add_ae_vol
  -- Push forward along log to obtain an a.e. equality on t with respect to volume.
  obtain ⟨c, hc0, hcTop, h_map⟩ := mulHaar_pushforward_log
  have h_meas_set : MeasurableSet
      {t : ℝ |
        Hσ.toFun (f + g) (Real.exp t)
          = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)} := by
    -- measurability of both sides composed with exp, then equality set
    have h_meas_l : Measurable (fun t : ℝ => Hσ.toFun (f + g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (f + g)).measurable.comp Real.measurable_exp
    have h_meas_f : Measurable (fun t : ℝ => Hσ.toFun f (Real.exp t)) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_meas_g : Measurable (fun t : ℝ => Hσ.toFun g (Real.exp t)) :=
      (Lp.stronglyMeasurable g).measurable.comp Real.measurable_exp
    have h_meas_r : Measurable (fun t : ℝ =>
        Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)) :=
      h_meas_f.add h_meas_g
    -- {t | u t = v t} is measurable as preimage of the diagonal
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (f + g) (Real.exp t),
         Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t))) :=
      h_meas_l.prodMk h_meas_r
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ |
          Hσ.toFun (f + g) (Real.exp t)
            = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (f + g) (Real.exp t),
               Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have hlog_aemeas : AEMeasurable Real.log mulHaar :=
    Real.measurable_log.aemeasurable
  -- Convert the x-a.e. equality to a t-a.e. equality via `ae_map_iff` and the pushforward.
  have h_ae_map : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (f + g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)) := by
    -- Use the equivalence `ae_map_iff` to pull back to mulHaar.
    have hiff := ae_map_iff (μ := mulHaar)
      (f := Real.log) hlog_aemeas h_meas_set
    rw [hiff]
    -- On x-side (mulHaar), the equality holds a.e.
    -- We need to rewrite x as exp(log x) for x > 0
    -- a.e. on mulHaar we have x > 0 since mulHaar is restricted to Ioi 0
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      -- unfold mulHaar and use `ae_restrict_mem`
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    -- Combine the a.e. equality on x with the positivity to rewrite exp (log x) = x
    refine (h_add_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq :
        Hσ.toFun (f + g) x = Hσ.toFun f x + Hσ.toFun g x := hx.1
    have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    -- Now rewrite the goal using `exp (log x) = x`.
    simpa [Set.mem_setOf_eq, h_exp_log]
  -- Identify the pushforward measure with Lebesgue measure (up to a positive scalar).
  have h_ae_t : (∀ᵐ t ∂ volume,
      Hσ.toFun (f + g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)) := by
    -- Define the predicate used for ae statements on t.
    let P : ℝ → Prop := fun t =>
      Hσ.toFun (f + g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | P t} := h_meas_set
    -- Use the identification `Measure.map Real.log mulHaar = c • volume`.
    have h_ae_cvol : (∀ᵐ t ∂ (c • volume), P t) := by
      -- First, rewrite the pushforward along the restricted mulHaar.
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by
        simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), P t) := by
        simpa [h_restrict'] using h_ae_map
      -- Then use `h_map` to identify the measure with `c • volume`.
      simpa [h_map] using h'
    -- Pass from `c • volume` to `volume` using that `c ≠ 0`.
    -- Use the `ae_iff` characterization via null sets.
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ P t} := hP_meas.compl
    have h_null_c : (c • volume) {t : ℝ | ¬ P t} = 0 := by
      -- Convert a.e. statement to null-set on `c • volume`.
      have := ((ae_iff (μ := (c • volume)) (p := fun t : ℝ => P t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : c * volume {t : ℝ | ¬ P t} = 0 := by
      -- Rewrite the smul-measure on measurable sets.
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable]
        using h_null_c
    have h_zero : volume {t : ℝ | ¬ P t} = 0 :=
      (mul_eq_zero.mp h_mul_zero).resolve_left hc0
    -- Conclude the a.e. statement for `volume`.
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => P t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  -- With the a.e. identity in hand, rewrite the integrand and conclude by additivity.
  have h_integrand_ae :
      (fun t => LogPull σ (f + g) t * Complex.exp ((1 / 2 : ℝ) * t))
        =ᵐ[volume]
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) +
        (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    refine h_ae_t.mono ?_
    intro t ht
    -- Expand LogPull and use the a.e. linearity of Hσ.toFun at x = exp t.
    simp [LogPull, LogPull_apply, ht, mul_add, mul_left_comm,
          mul_comm, mul_assoc]
  -- The right-hand side is integrable as a sum of integrable functions.
  have h_sum_int : Integrable
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) +
        (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :=
    (hf_int.add hg_int)
  -- Transfer integrability along the a.e. equality.
  exact h_sum_int.congr h_integrand_ae.symm

/-- Integrability of the weighted LogPull for subtraction -/
lemma LogPull_integrable_sub (σ : ℝ) (f g : Hσ σ)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
    (hg_int : Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :
    Integrable (fun t => LogPull σ (f - g) t * Complex.exp ((1 / 2 : ℝ) * t)) := by
  classical
  -- Start from the a.e. identity for subtraction on the physical side (x-variable).
  have h_sub_ae_weighted :
      (fun x : ℝ => Hσ.toFun (f - g) x)
        =ᵐ[mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun g x) :=
    (Lp.coeFn_sub (f := (f : Lp ℂ 2
      (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))))
      (g := (g : Lp ℂ 2
      (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))))
  -- Transport the a.e. equality to the Lebesgue measure on (0,∞).
  have h_rev_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ
  have h_sub_ae_vol :
      (fun x : ℝ => Hσ.toFun (f - g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun g x) :=
    h_rev_ac.ae_eq h_sub_ae_weighted
  -- Also, mulHaar is absolutely continuous w.r.t. the restricted Lebesgue measure.
  have h_mulHaar_to_volume : mulHaar ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    have h_base :
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)) ≪ volume := by
      simpa using
        (withDensity_absolutelyContinuous
          (μ := volume) (f := fun x : ℝ => ENNReal.ofReal (1 / x)))
    simpa [mulHaar] using h_base.restrict (Set.Ioi (0 : ℝ))
  -- Hence the equality also holds a.e. for mulHaar on (0,∞).
  have h_sub_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (f - g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun g x) :=
    h_mulHaar_to_volume.ae_eq h_sub_ae_vol
  -- Push forward along log to obtain an a.e. equality on t with respect to volume.
  obtain ⟨c, hc0, hcTop, h_map⟩ := mulHaar_pushforward_log
  have h_meas_set : MeasurableSet
      {t : ℝ |
        Hσ.toFun (f - g) (Real.exp t)
          = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)} := by
    -- measurability of both sides composed with exp, then equality set
    have h_meas_l : Measurable (fun t : ℝ => Hσ.toFun (f - g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (f - g)).measurable.comp Real.measurable_exp
    have h_meas_f : Measurable (fun t : ℝ => Hσ.toFun f (Real.exp t)) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_meas_g : Measurable (fun t : ℝ => Hσ.toFun g (Real.exp t)) :=
      (Lp.stronglyMeasurable g).measurable.comp Real.measurable_exp
    have h_meas_r : Measurable (fun t : ℝ =>
        Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)) :=
      h_meas_f.sub h_meas_g
    -- {t | u t = v t} is measurable as preimage of the diagonal
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (f - g) (Real.exp t),
         Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t))) :=
      h_meas_l.prodMk h_meas_r
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ |
          Hσ.toFun (f - g) (Real.exp t)
            = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (f - g) (Real.exp t),
               Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have hlog_aemeas : AEMeasurable Real.log mulHaar :=
    Real.measurable_log.aemeasurable
  -- Convert the x-a.e. equality to a t-a.e. equality via `ae_map_iff` and the pushforward.
  have h_ae_map : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (f - g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)) := by
    -- Use the equivalence `ae_map_iff` to pull back to mulHaar.
    have hiff := ae_map_iff (μ := mulHaar)
      (f := Real.log) hlog_aemeas h_meas_set
    rw [hiff]
    -- On x-side (mulHaar), the equality holds a.e.
    -- We need to rewrite x as exp(log x) for x > 0
    -- a.e. on mulHaar we have x > 0 since mulHaar is restricted to Ioi 0
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      -- unfold mulHaar and use `ae_restrict_mem`
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    -- Combine the a.e. equality on x with the positivity to rewrite exp (log x) = x
    refine (h_sub_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq :
        Hσ.toFun (f - g) x = Hσ.toFun f x - Hσ.toFun g x := hx.1
    have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    -- Now rewrite the goal using `exp (log x) = x`.
    simpa [Set.mem_setOf_eq, h_exp_log]
  -- Identify the pushforward measure with Lebesgue measure (up to a positive scalar).
  have h_ae_t : (∀ᵐ t ∂ volume,
      Hσ.toFun (f - g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)) := by
    -- Define the predicate used for ae statements on t.
    let P : ℝ → Prop := fun t =>
      Hσ.toFun (f - g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | P t} := h_meas_set
    -- Use the identification `Measure.map Real.log mulHaar = c • volume`.
    have h_ae_cvol : (∀ᵐ t ∂ (c • volume), P t) := by
      -- First, rewrite the pushforward along the restricted mulHaar.
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by
        simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), P t) := by
        simpa [h_restrict'] using h_ae_map
      -- Then use `h_map` to identify the measure with `c • volume`.
      simpa [h_map] using h'
    -- Pass from `c • volume` to `volume` using that `c ≠ 0`.
    -- Use the `ae_iff` characterization via null sets.
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ P t} := hP_meas.compl
    have h_null_c : (c • volume) {t : ℝ | ¬ P t} = 0 := by
      -- Convert a.e. statement to null-set on `c • volume`.
      have := ((ae_iff (μ := (c • volume)) (p := fun t : ℝ => P t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : c * volume {t : ℝ | ¬ P t} = 0 := by
      -- Rewrite the smul-measure on measurable sets.
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable]
        using h_null_c
    have h_zero : volume {t : ℝ | ¬ P t} = 0 :=
      (mul_eq_zero.mp h_mul_zero).resolve_left hc0
    -- Conclude the a.e. statement for `volume`.
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => P t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  -- With the a.e. identity in hand, rewrite the integrand and conclude by subtraction.
  have h_integrand_ae :
      (fun t => LogPull σ (f - g) t * Complex.exp ((1 / 2 : ℝ) * t))
        =ᵐ[volume]
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) -
        (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    refine h_ae_t.mono ?_
    intro t ht
    -- Expand LogPull and use the a.e. linearity of Hσ.toFun at x = exp t.
    simp [LogPull, LogPull_apply, ht, mul_sub, mul_left_comm,
          mul_comm, mul_assoc]
  -- The right-hand side is integrable as a difference of integrable functions.
  have h_diff_int : Integrable
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) -
        (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :=
    (hf_int.sub hg_int)
  -- Transfer integrability along the a.e. equality.
  exact h_diff_int.congr h_integrand_ae.symm

/-- Integrability of the weighted LogPull for addition with scalar multiplication -/
lemma LogPull_integrable_add_smul (σ : ℝ) (f g : Hσ σ) (c : ℂ)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
    (hg_int : Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :
    Integrable (fun t => LogPull σ (f + c • g) t * Complex.exp ((1 / 2 : ℝ) * t)) := by
  classical
  -- Start from the a.e. identity on the physical side (x-variable).
  have h_add_ae_weighted := toFun_add_ae σ f (c • g)
  have h_smul_ae_weighted := toFun_smul_ae σ c g
  -- Transport the a.e. equality to the Lebesgue measure on (0,∞).
  have h_rev_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ
  have h_add_ae_vol :
      (fun x : ℝ => Hσ.toFun (f + c • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x + Hσ.toFun (c • g) x) :=
    h_rev_ac.ae_eq h_add_ae_weighted
  have h_smul_ae_vol :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    h_rev_ac.ae_eq h_smul_ae_weighted
  -- Also, mulHaar is absolutely continuous w.r.t. the restricted Lebesgue measure.
  have h_mulHaar_to_volume : mulHaar ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    have h_base :
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)) ≪ volume := by
      simpa using
        (withDensity_absolutelyContinuous
          (μ := volume) (f := fun x : ℝ => ENNReal.ofReal (1 / x)))
    simpa [mulHaar] using h_base.restrict (Set.Ioi (0 : ℝ))
  -- Hence the equalities also hold a.e. for mulHaar on (0,∞).
  have h_add_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (f + c • g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => Hσ.toFun f x + Hσ.toFun (c • g) x) :=
    h_mulHaar_to_volume.ae_eq h_add_ae_vol
  have h_smul_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    h_mulHaar_to_volume.ae_eq h_smul_ae_vol
  -- Push forward along log to obtain a.e. equalities on t with respect to volume.
  obtain ⟨cm, hcm0, hcmTop, h_map⟩ := mulHaar_pushforward_log
  -- Measurability of equality sets after composing with exp.
  have h_meas_set_add : MeasurableSet
      {t : ℝ |
        Hσ.toFun (f + c • g) (Real.exp t)
          = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)} := by
    have h_meas_l : Measurable (fun t : ℝ => Hσ.toFun (f + c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (f + c • g)).measurable.comp Real.measurable_exp
    have h_meas_f : Measurable (fun t : ℝ => Hσ.toFun f (Real.exp t)) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_meas_cg : Measurable (fun t : ℝ => Hσ.toFun (c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (c • g)).measurable.comp Real.measurable_exp
    have h_meas_r : Measurable (fun t : ℝ =>
        Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)) :=
      h_meas_f.add h_meas_cg
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (f + c • g) (Real.exp t),
         Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t))) :=
      h_meas_l.prodMk h_meas_r
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ |
          Hσ.toFun (f + c • g) (Real.exp t)
            = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (f + c • g) (Real.exp t),
               Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have h_meas_set_smul : MeasurableSet
      {t : ℝ |
        Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)} := by
    have h_meas_cg : Measurable (fun t : ℝ => Hσ.toFun (c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (c • g)).measurable.comp Real.measurable_exp
    have h_meas_g : Measurable (fun t : ℝ => Hσ.toFun g (Real.exp t)) :=
      (Lp.stronglyMeasurable g).measurable.comp Real.measurable_exp
    have h_meas_rhs : Measurable (fun t : ℝ => c * Hσ.toFun g (Real.exp t)) :=
      measurable_const.mul h_meas_g
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (c • g) (Real.exp t), c * Hσ.toFun g (Real.exp t))) :=
      h_meas_cg.prodMk h_meas_rhs
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ | Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (c • g) (Real.exp t), c * Hσ.toFun g (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have hlog_aemeas : AEMeasurable Real.log mulHaar :=
    Real.measurable_log.aemeasurable
  -- Convert the x-a.e. equalities to t-a.e. equalities via `ae_map_iff` and the pushforward.
  have h_ae_map_add : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (f + c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)) := by
    have hiff := ae_map_iff (μ := mulHaar) (f := Real.log) hlog_aemeas h_meas_set_add
    rw [hiff]
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    refine (h_add_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq := hx.1; have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [Set.mem_setOf_eq, h_exp_log] using hx_eq
  have h_ae_map_smul : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)) := by
    have hiff := ae_map_iff (μ := mulHaar) (f := Real.log) hlog_aemeas h_meas_set_smul
    rw [hiff]
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    refine (h_smul_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq := hx.1; have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [Set.mem_setOf_eq, h_exp_log] using hx_eq
  -- Identify the pushforward measure with Lebesgue measure (up to a positive scalar).
  have h_ae_t_add : (∀ᵐ t ∂ volume,
      Hσ.toFun (f + c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)) := by
    -- define predicate for add
    let Padd : ℝ → Prop := fun t =>
      Hσ.toFun (f + c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | Padd t} := h_meas_set_add
    have h_ae_cvol : (∀ᵐ t ∂ (cm • volume), Padd t) := by
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), Padd t) := by
        simpa [h_restrict'] using h_ae_map_add
      simpa [h_map] using h'
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ Padd t} := hP_meas.compl
    have h_null_c : (cm • volume) {t : ℝ | ¬ Padd t} = 0 := by
      have := ((ae_iff (μ := (cm • volume)) (p := fun t : ℝ => Padd t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : cm * volume {t : ℝ | ¬ Padd t} = 0 := by
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable] using h_null_c
    have h_zero : volume {t : ℝ | ¬ Padd t} = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left hcm0
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => Padd t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  have h_ae_t_smul : (∀ᵐ t ∂ volume,
      Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)) := by
    let Psmul : ℝ → Prop := fun t => Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | Psmul t} := h_meas_set_smul
    have h_ae_cvol : (∀ᵐ t ∂ (cm • volume), Psmul t) := by
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), Psmul t) := by
        simpa [h_restrict'] using h_ae_map_smul
      simpa [h_map] using h'
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ Psmul t} := hP_meas.compl
    have h_null_c : (cm • volume) {t : ℝ | ¬ Psmul t} = 0 := by
      have := ((ae_iff (μ := (cm • volume)) (p := fun t : ℝ => Psmul t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : cm * volume {t : ℝ | ¬ Psmul t} = 0 := by
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable] using h_null_c
    have h_zero : volume {t : ℝ | ¬ Psmul t} = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left hcm0
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => Psmul t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  have h_integrand_ae :
      (fun t => LogPull σ (f + c • g) t * Complex.exp ((1 / 2 : ℝ) * t))
        =ᵐ[volume]
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) +
        c * (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    refine (h_ae_t_add.and h_ae_t_smul).mono ?_
    intro t hts
    have ht_add := hts.1
    have ht_smul := hts.2
    -- Expand LogPull and use the a.e. linearity at x = exp t and scalar multiplication.
    simp [LogPull, LogPull_apply, ht_add, ht_smul, mul_add, mul_left_comm,
          mul_comm, mul_assoc]
  -- The right-hand side is integrable as a sum of integrable functions and a constant multiple.
  have h_rhs_int : Integrable
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) +
        c * (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    exact hf_int.add (hg_int.const_mul c)
  -- Transfer integrability along the a.e. equality.
  exact h_rhs_int.congr h_integrand_ae.symm

/-- Integrability of the weighted LogPull for subtraction with scalar multiplication -/
lemma LogPull_integrable_sub_smul (σ : ℝ) (f g : Hσ σ) (c : ℂ)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
    (hg_int : Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :
    Integrable (fun t => LogPull σ (f - c • g) t * Complex.exp ((1 / 2 : ℝ) * t)) := by
  classical
  -- a.e. identities on the physical side (x-variable)
  have h_sub_ae_weighted :
      (fun x : ℝ => Hσ.toFun (f - c • g) x)
        =ᵐ[mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun (c • g) x) :=
    (Lp.coeFn_sub (f := (f : Lp ℂ 2
      (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))))
      (g := ((c • g) : Lp ℂ 2
      (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))))
  have h_smul_ae_weighted :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    toFun_smul_ae σ c g
  -- Transport the a.e. equalities to the Lebesgue measure on (0,∞).
  have h_rev_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ
  have h_sub_ae_vol :
      (fun x : ℝ => Hσ.toFun (f - c • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun (c • g) x) :=
    h_rev_ac.ae_eq h_sub_ae_weighted
  have h_smul_ae_vol :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    h_rev_ac.ae_eq h_smul_ae_weighted
  -- Also, mulHaar ≪ volume.restrict (Ioi 0)
  have h_mulHaar_to_volume : mulHaar ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    have h_base :
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)) ≪ volume := by
      simpa using
        (withDensity_absolutelyContinuous
          (μ := volume) (f := fun x : ℝ => ENNReal.ofReal (1 / x)))
    simpa [mulHaar] using h_base.restrict (Set.Ioi (0 : ℝ))
  -- Hence these also hold a.e. for mulHaar on (0,∞).
  have h_sub_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (f - c • g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun (c • g) x) :=
    h_mulHaar_to_volume.ae_eq h_sub_ae_vol
  have h_smul_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    h_mulHaar_to_volume.ae_eq h_smul_ae_vol
  -- Push forward along log to obtain t-a.e. equalities.
  obtain ⟨cm, hcm0, hcmTop, h_map⟩ := mulHaar_pushforward_log
  -- Measurability of equality sets after composing with exp.
  have h_meas_set_sub : MeasurableSet
      {t : ℝ |
        Hσ.toFun (f - c • g) (Real.exp t)
          = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)} := by
    have h_meas_l : Measurable (fun t : ℝ => Hσ.toFun (f - c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (f - c • g)).measurable.comp Real.measurable_exp
    have h_meas_f : Measurable (fun t : ℝ => Hσ.toFun f (Real.exp t)) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_meas_cg : Measurable (fun t : ℝ => Hσ.toFun (c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (c • g)).measurable.comp Real.measurable_exp
    have h_meas_r : Measurable (fun t : ℝ =>
        Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)) :=
      h_meas_f.sub h_meas_cg
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (f - c • g) (Real.exp t),
         Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t))) :=
      h_meas_l.prodMk h_meas_r
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ |
          Hσ.toFun (f - c • g) (Real.exp t)
            = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (f - c • g) (Real.exp t),
               Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have h_meas_set_smul : MeasurableSet
      {t : ℝ |
        Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)} := by
    have h_meas_cg : Measurable (fun t : ℝ => Hσ.toFun (c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (c • g)).measurable.comp Real.measurable_exp
    have h_meas_g : Measurable (fun t : ℝ => Hσ.toFun g (Real.exp t)) :=
      (Lp.stronglyMeasurable g).measurable.comp Real.measurable_exp
    have h_meas_rhs : Measurable (fun t : ℝ => c * Hσ.toFun g (Real.exp t)) :=
      measurable_const.mul h_meas_g
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (c • g) (Real.exp t), c * Hσ.toFun g (Real.exp t))) :=
      h_meas_cg.prodMk h_meas_rhs
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ | Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (c • g) (Real.exp t), c * Hσ.toFun g (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have hlog_aemeas : AEMeasurable Real.log mulHaar :=
    Real.measurable_log.aemeasurable
  -- Convert equalities via ae_map_iff
  have h_ae_map_sub : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (f - c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)) := by
    have hiff := ae_map_iff (μ := mulHaar) (f := Real.log) hlog_aemeas h_meas_set_sub
    rw [hiff]
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    refine (h_sub_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq := hx.1; have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [Set.mem_setOf_eq, h_exp_log] using hx_eq
  have h_ae_map_smul : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)) := by
    have hiff := ae_map_iff (μ := mulHaar) (f := Real.log) hlog_aemeas h_meas_set_smul
    rw [hiff]
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    refine (h_smul_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq := hx.1; have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [Set.mem_setOf_eq, h_exp_log] using hx_eq
  -- Identify the pushforward measure with Lebesgue measure (up to a positive scalar).
  have h_ae_t_sub : (∀ᵐ t ∂ volume,
      Hσ.toFun (f - c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)) := by
    let Psub : ℝ → Prop := fun t =>
      Hσ.toFun (f - c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | Psub t} := h_meas_set_sub
    have h_ae_cvol : (∀ᵐ t ∂ (cm • volume), Psub t) := by
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), Psub t) := by
        simpa [h_restrict'] using h_ae_map_sub
      simpa [h_map] using h'
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ Psub t} := hP_meas.compl
    have h_null_c : (cm • volume) {t : ℝ | ¬ Psub t} = 0 := by
      have := ((ae_iff (μ := (cm • volume)) (p := fun t : ℝ => Psub t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : cm * volume {t : ℝ | ¬ Psub t} = 0 := by
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable] using h_null_c
    have h_zero : volume {t : ℝ | ¬ Psub t} = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left hcm0
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => Psub t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  have h_ae_t_smul : (∀ᵐ t ∂ volume,
      Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)) := by
    let Psmul : ℝ → Prop := fun t => Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | Psmul t} := h_meas_set_smul
    have h_ae_cvol : (∀ᵐ t ∂ (cm • volume), Psmul t) := by
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), Psmul t) := by
        simpa [h_restrict'] using h_ae_map_smul
      simpa [h_map] using h'
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ Psmul t} := hP_meas.compl
    have h_null_c : (cm • volume) {t : ℝ | ¬ Psmul t} = 0 := by
      have := ((ae_iff (μ := (cm • volume)) (p := fun t : ℝ => Psmul t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : cm * volume {t : ℝ | ¬ Psmul t} = 0 := by
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable] using h_null_c
    have h_zero : volume {t : ℝ | ¬ Psmul t} = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left hcm0
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => Psmul t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  have h_integrand_ae :
      (fun t => LogPull σ (f - c • g) t * Complex.exp ((1 / 2 : ℝ) * t))
        =ᵐ[volume]
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) -
        c * (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    refine (h_ae_t_sub.and h_ae_t_smul).mono ?_
    intro t hts
    have ht_sub := hts.1
    have ht_smul := hts.2
    simp [LogPull, LogPull_apply, ht_sub, ht_smul, mul_sub, mul_left_comm,
          mul_comm, mul_assoc]
  -- The right-hand side is integrable as a difference of integrable functions with scalar multiple.
  have h_rhs_int : Integrable
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) -
        c * (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    exact hf_int.sub (hg_int.const_mul c)
  exact h_rhs_int.congr h_integrand_ae.symm

-- Complex measure-theoretic proof involving ENNReal to Real to Complex conversion
/-- Convert ENNReal norm equality to Complex, handling coercion of binary operations -/
lemma norm_squared_to_complex_add_sub (σ C : ℝ) (h : Hσ σ)
    (hC_pos : C > 0)
    (h_norm : ∫⁻ (x : ℝ) in Set.Ioi 0, ENNReal.ofReal
      (‖(h : Hσ σ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume =
      ENNReal.ofReal (C * ∫ (τ : ℝ), ‖mellinTransform
        ((h : Hσ σ) : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)) :
    Complex.ofReal
      ((∫⁻ (x : ℝ) in Set.Ioi 0,
          ENNReal.ofReal (‖(h : Hσ σ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume).toReal)
      =
    Complex.ofReal (C * ∫ τ : ℝ,
        ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) := by
  -- Convert the ENNReal equality into a real equality via `toReal`,
  -- then embed both sides into `ℂ` using `Complex.ofReal`.
  have h_toReal :
      (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖(h : Hσ σ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume).toReal
        = C * ∫ τ : ℝ,
            ‖mellinTransform ((h : Hσ σ) : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
    have := congrArg ENNReal.toReal h_norm
    -- Right-hand side is nonnegative, so `toReal (ofReal _) = _` applies
    have h_nonneg :
        0 ≤ C * ∫ τ : ℝ,
          ‖mellinTransform ((h : Hσ σ) : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
      refine mul_nonneg (le_of_lt hC_pos) ?_
      refine integral_nonneg ?hpos
      intro τ
      exact sq_nonneg _
    simpa [ENNReal.toReal_ofReal h_nonneg]
      using this
  simp [h_toReal]

/-- Mellin transform is linear in the input (addition) on its natural domain.
For the set integral definition used here, this requires integrability of both
integrands over `(0,∞)`.

`hf` and `hg` assert integrability of the Mellin integrands for `f` and `g` respectively. -/
lemma mellinTransform_add
    (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun t : ℝ => f t * t ^ (s - 1)) (Set.Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => g t * t ^ (s - 1)) (Set.Ioi (0 : ℝ)) volume) :
    mellinTransform (f + g) s = mellinTransform f s + mellinTransform g s := by
  classical
  unfold Frourio.mellinTransform
  -- Use linearity of the set integral under the given integrability hypotheses
  have hlin := (MeasureTheory.integral_add hf hg)
  -- Rewrite the integrand `(f+g) * k` as `f*k + g*k` and simplify
  have h_eq : ∀ t, (f + g) t * t ^ (s - 1) = f t * t ^ (s - 1) + g t * t ^ (s - 1) := by
    intro t
    simp [Pi.add_apply]
    ring
  simp only [h_eq, hlin]

/-- Mellin transform is linear in the input (subtraction) on its natural domain.
Requires integrability of both integrands over `(0,∞)`. -/
lemma mellinTransform_sub
    (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun t : ℝ => f t * t ^ (s - 1)) (Set.Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => g t * t ^ (s - 1)) (Set.Ioi (0 : ℝ)) volume) :
    mellinTransform (f - g) s = mellinTransform f s - mellinTransform g s := by
  classical
  unfold Frourio.mellinTransform
  have hlin := MeasureTheory.integral_sub hf hg
  have h_eq : ∀ t, (f - g) t * t ^ (s - 1) = f t * t ^ (s - 1) - g t * t ^ (s - 1) := by
    intro t
    simp [Pi.sub_apply]
    ring
  simp only [h_eq, hlin]

/-- Mellin transform commutes with scalar multiplication (no extra hypotheses).
We use linearity of the Bochner integral over the restricted measure. -/
lemma mellinTransform_smul (c : ℂ) (f : ℝ → ℂ) (s : ℂ) :
    mellinTransform (c • f) s = c * mellinTransform f s := by
  classical
  unfold Frourio.mellinTransform
  -- Switch to the restricted measure presentation and pull out the scalar
  have hrewrite :
      (fun t : ℝ => (c • f) t * (↑t) ^ (s - 1))
        = (fun t : ℝ => c • (f t * (↑t) ^ (s - 1))) := by
    funext t
    simp [smul_eq_mul, mul_left_comm, mul_assoc]
  have h_integral := MeasureTheory.integral_smul
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (c := c)
      (f := fun t : ℝ => f t * (↑t) ^ (s - 1))
  rw [hrewrite, h_integral, smul_eq_mul]

/-- Under the weighted L² norm condition, the Mellin integrand is integrable. -/
lemma mellin_integrable_of_weighted_L2 (σ : ℝ) (f : Hσ σ) (τ : ℝ)
    (hf_L2 : has_weighted_L2_norm σ f)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))) :
    IntegrableOn (fun t : ℝ => (f : ℝ → ℂ) t * t ^ (σ + I * τ - 1)) (Set.Ioi 0) := by
  sorry

/-- Integrability is preserved under scalar multiplication -/
lemma mellin_integrable_smul (σ : ℝ) (f : Hσ σ) (c : ℂ) (τ : ℝ)
    (hf_L2 : has_weighted_L2_norm σ f)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))) :
    IntegrableOn (fun t : ℝ => (c • f : ℝ → ℂ) t * t ^ (σ + I * τ - 1)) (Set.Ioi 0) := by
  sorry

/-- The Mellin-Plancherel formula relates to Fourier-Parseval -/
theorem parseval_identity_equivalence (σ : ℝ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (f g : Hσ σ),
    -- Additional L² and integrability conditions needed for convergence
    has_weighted_L2_norm σ f →
    Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) →
    has_weighted_L2_norm σ g →
    Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t)) →
    @inner ℂ _ _ f g = C * ∫ τ : ℝ,
      starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
      mellinTransform (g : ℝ → ℂ) (σ + I * τ) := by
  -- Get the constant from mellin_parseval_formula
  obtain ⟨C, hC_pos, hC_formula⟩ := mellin_parseval_formula σ

  use C
  constructor
  · -- C > 0 from mellin_parseval_formula
    exact hC_pos

  · -- For all f, g with the L² conditions and integrability, prove the identity
    intro f g hf_L2 hf_int hg_L2 hg_int

    -- Use the polarization identity to express inner product in terms of norms
    have h_polarization := complex_polarization_identity f g

    -- We already have hf_L2 and hg_L2 as hypotheses
    -- We also have hC_formula from the outer obtain statement

    -- Apply the polarization identity to both sides
    -- Left side: 4 * inner f g = ‖f+g‖^2 - ‖f-g‖^2 - i*‖f+ig‖^2 + i*‖f-ig‖^2
    -- Right side: Each norm can be expressed using mellin_parseval_formula

    -- Step 1: Apply the norm formula from mellin_parseval_formula to each term
    have h_fp_norm := hC_formula (f + g)
    have h_fm_norm := hC_formula (f - g)
    have h_fi_norm := hC_formula (f + Complex.I • g)
    have h_fmi_norm := hC_formula (f - Complex.I • g)

    -- Step 2: The Mellin transform is linear, so we can expand each transform
    have h_mellin_linear := mellin_transform_linear σ

    -- Step 3: Apply polarization identity in the Mellin domain
    have h_mellin_polarization : ∀ τ : ℝ,
        let F := mellinTransform (f : ℝ → ℂ) (σ + I * τ)
        let G := mellinTransform (g : ℝ → ℂ) (σ + I * τ)
        ‖F + G‖ ^ 2 - ‖F - G‖ ^ 2 - Complex.I * ‖F + Complex.I * G‖ ^ 2 +
          Complex.I * ‖F - Complex.I * G‖ ^ 2 =
          4 * (starRingEnd ℂ F * G) := by
      intro τ
      exact mellin_polarization_pointwise
        (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
        (mellinTransform (g : ℝ → ℂ) (σ + I * τ))

    -- Step A: gather the four norm identities for f±g and f±I•g
    have h_fpL2 : has_weighted_L2_norm σ (f + g) :=
      has_weighted_L2_norm_add σ hf_L2 hg_L2
    have h_fmL2 : has_weighted_L2_norm σ (f - g) :=
      has_weighted_L2_norm_sub σ hf_L2 hg_L2
    have h_fiL2 : has_weighted_L2_norm σ (f + Complex.I • g) := by
      have : has_weighted_L2_norm σ (Complex.I • g) :=
        has_weighted_L2_norm_smul σ Complex.I hg_L2
      simpa [add_comm] using has_weighted_L2_norm_add σ hf_L2 this
    have h_fmiL2 : has_weighted_L2_norm σ (f - Complex.I • g) := by
      have : has_weighted_L2_norm σ (Complex.I • g) :=
        has_weighted_L2_norm_smul σ Complex.I hg_L2
      simpa [sub_eq_add_neg] using has_weighted_L2_norm_add σ hf_L2
        (has_weighted_L2_norm_smul σ (-1 : ℂ) this)

    -- Auxiliary: integrability of the weighted LogPull for the combinations.
    -- This follows by linearity and stability of Integrable under addition/scalar.
    have h_fpInt : Integrable
        (fun t => LogPull σ (f + g) t * Complex.exp ((1 / 2 : ℝ) * t)) :=
      LogPull_integrable_add σ f g hf_int hg_int
    have h_fmInt : Integrable
        (fun t => LogPull σ (f - g) t * Complex.exp ((1 / 2 : ℝ) * t)) :=
      LogPull_integrable_sub σ f g hf_int hg_int
    have h_fiInt : Integrable
        (fun t => LogPull σ (f + Complex.I • g) t * Complex.exp ((1 / 2 : ℝ) * t)) :=
      LogPull_integrable_add_smul σ f g Complex.I hf_int hg_int
    have h_fmiInt : Integrable
        (fun t => LogPull σ (f - Complex.I • g) t * Complex.exp ((1 / 2 : ℝ) * t)) :=
      LogPull_integrable_sub_smul σ f g Complex.I hf_int hg_int

    -- Apply the norm formula to each combination
    have h_fp := h_fp_norm h_fpL2 h_fpInt
    have h_fm := h_fm_norm h_fmL2 h_fmInt
    have h_fi := h_fi_norm h_fiL2 h_fiInt
    have h_fmi := h_fmi_norm h_fmiL2 h_fmiInt

    -- Convert the ENNReal equalities to real equalities using finiteness
    -- and then to complex numbers (via `Complex.ofReal`).
    have h_ofReal_fp :
        Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖((f + g : Hσ σ) : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume).toReal)
          = Complex.ofReal (C * ∫ τ : ℝ,
              ‖mellinTransform (((f + g : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) :=
      norm_squared_to_complex_add_sub σ C (f + g) hC_pos h_fp

    have h_ofReal_fm :
        Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖((f - g : Hσ σ) : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume).toReal)
          = Complex.ofReal (C * ∫ τ : ℝ,
              ‖mellinTransform (((f - g : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) :=
      norm_squared_to_complex_add_sub σ C (f - g) hC_pos h_fm

    have h_ofReal_fi :
        Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖((f + Complex.I • g : Hσ σ) : ℝ → ℂ) x‖ ^ 2 *
                x ^ (2 * σ - 1)) ∂volume).toReal)
          = Complex.ofReal (C * ∫ τ : ℝ,
              ‖mellinTransform (((f + Complex.I • g : Hσ σ) : ℝ → ℂ))
                (σ + I * τ)‖ ^ 2 ∂volume) :=
      norm_squared_to_complex_add_sub σ C (f + Complex.I • g) hC_pos h_fi

    have h_ofReal_fmi :
        Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖((f - Complex.I • g : Hσ σ) : ℝ → ℂ) x‖ ^ 2 *
                x ^ (2 * σ - 1)) ∂volume).toReal)
          = Complex.ofReal (C * ∫ τ : ℝ,
              ‖mellinTransform (((f - Complex.I • g : Hσ σ) : ℝ → ℂ))
                (σ + I * τ)‖ ^ 2 ∂volume) :=
      norm_squared_to_complex_add_sub σ C (f - Complex.I • g) hC_pos h_fmi

    -- Substitute into the polarization identity for ⟪f,g⟫ and rearrange.
    have h_left := h_polarization
    -- Replace each squared norm with its Mellin-domain representation.
    -- Keep the original polarization identity form for now; translating
    -- each squared norm to Mellin-domain integrals will be handled later.
    have h_left' := h_left

    -- On the Mellin side, apply polarization pointwise and integrate.
    -- First, rewrite each term via linearity of Mellin transform.
    have h_lin₁ :
        (fun τ : ℝ =>
          ‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2)
          =
        (fun τ : ℝ =>
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
             + mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2) := by
        funext τ
        rw [mellinTransform_add]
        · exact mellin_integrable_of_weighted_L2 σ f τ hf_L2 hf_int
        · exact mellin_integrable_of_weighted_L2 σ g τ hg_L2 hg_int
    have h_lin₂ :
        (fun τ : ℝ =>
          ‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2)
          =
        (fun τ : ℝ =>
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
             - mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2) := by
      funext τ
      rw [mellinTransform_sub]
      · exact mellin_integrable_of_weighted_L2 σ f τ hf_L2 hf_int
      · exact mellin_integrable_of_weighted_L2 σ g τ hg_L2 hg_int
    have h_lin₃ :
        (fun τ : ℝ =>
          ‖mellinTransform (f + Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2)
          =
        (fun τ : ℝ =>
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
             + Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2) := by
      funext τ
      congr 1
      rw [mellinTransform_add, mellinTransform_smul]
      · exact mellin_integrable_of_weighted_L2 σ f τ hf_L2 hf_int
      · exact mellin_integrable_smul σ g Complex.I τ hg_L2 hg_int
    have h_lin₄ :
        (fun τ : ℝ =>
          ‖mellinTransform (f - Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2)
          =
        (fun τ : ℝ =>
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
             - Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2) := by
      funext τ
      congr 1
      rw [mellinTransform_sub, mellinTransform_smul]
      · exact mellin_integrable_of_weighted_L2 σ f τ hf_L2 hf_int
      · exact mellin_integrable_smul σ g Complex.I τ hg_L2 hg_int

    -- Use these to rewrite h_left' as an integral of the pointwise polarization identity.
    have h_right :
        Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)
          - Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)
          - Complex.I * Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (f + Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)
          + Complex.I * Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (f - Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)
        = C * ∫ τ : ℝ,
            (starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
              * mellinTransform (g : ℝ → ℂ) (σ + I * τ)) * 4 ∂volume := by
      -- Pull out C and integrate the pointwise polarization identity.
      -- The inner equality is exactly `h_mellin_polarization τ`.
      -- We rewrite the four integrands and then use linearity of the integral.
      have h_pol_ae :
          (fun τ : ℝ =>
            ((‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                + mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) : ℂ)
              - ((‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                - mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) : ℂ)
              - Complex.I *
                ((‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                  + Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) : ℂ)
              + Complex.I *
                ((‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                  - Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) : ℂ))
          =ᵐ[volume]
          (fun τ : ℝ => 4 *
            (starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
              * mellinTransform (g : ℝ → ℂ) (σ + I * τ))) := by
        refine Filter.Eventually.of_forall ?_
        intro τ
        simpa using h_mellin_polarization τ
      -- Now integrate both sides and multiply by C.
      -- Convert the outer `Complex.ofReal (C * ∫ ...)` into `C * Complex.ofReal (∫ ...)`.
      -- Then use linearity of integral and the previous `h_pol_ae`.
      have h_int_equal :
          Complex.ofReal (∫ τ : ℝ,
            (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                + mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                - mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.I * Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                + Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            + Complex.I * Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                - Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
          = ∫ τ : ℝ, 4 *
              (starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
                * mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume := by
        -- This requires integral_congr_ae h_pol_ae and linearity of Complex.ofReal with integrals
        sorry
      -- Pull out the constant C from `ofReal (C * ∫ ...)`.
      -- Note: `Complex.ofReal (C * A) = C • Complex.ofReal A` and
      -- we can rewrite scalar multiplication as multiplication since `C : ℝ`.
      -- Putting all together:
      have h_pullC :
          Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform (f + g : ℝ → ℂ)
            (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform (f - g : ℝ → ℂ)
            (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.I * Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform
              (f + Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            + Complex.I * Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform
              (f - Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
          = C * (Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.I * Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f + Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            + Complex.I * Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f - Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)) := by
        -- Use Complex.ofReal (C * A) = C * Complex.ofReal A and ring
        sorry
      -- Combine the last two displays.
      sorry

    -- Conclude by comparing both expressions for 4 ⟪f,g⟫ and divide by 4.
    sorry

/-- The Mellin transform preserves the L² structure up to normalization -/
theorem mellin_isometry_normalized (σ : ℝ) :
    ∃ (C : ℝ) (U : Hσ σ →L[ℂ] Lp ℂ 2 volume),
    C > 0 ∧ ∀ f : Hσ σ, ‖U f‖ = C * ‖f‖ ∧
    (U f : ℝ → ℂ) = fun τ : ℝ => mellinTransform (f : ℝ → ℂ) (σ + I * ↑τ) := by
  -- Construct the normalized Mellin transform operator
  sorry

end ParsevalEquivalence

section ClassicalParseval

/-- Connection between Mellin-Parseval and Fourier-Parseval -/
theorem mellin_fourier_parseval_connection (σ : ℝ) (f : Hσ σ) :
    let g := fun t => (f : ℝ → ℂ) (Real.exp t) * Complex.exp ((σ - (1/2)) * t)
    ∃ (hg : MemLp g 2 volume), ‖f‖ ^ 2 = ‖MemLp.toLp g hg‖ ^ 2 := by
  -- The weighted L² norm on (0,∞) with weight x^(2σ-1)
  -- equals the L² norm on ℝ after the transformation
  sorry

/-- The Mellin transform is unitarily equivalent to Fourier transform -/
theorem mellin_fourier_unitary_equivalence (σ : ℝ) :
    ∃ (V : Hσ σ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ)),
    ∀ (f : Hσ σ) (τ : ℝ),
    ∃ (c : ℂ), c ≠ 0 ∧ mellinTransform (f : ℝ → ℂ) (σ + I * τ) = c * (V f τ) := by
  -- The unitary equivalence via logarithmic change of variables
  sorry

end ClassicalParseval

section Applications

/-- Mellin convolution theorem via Parseval -/
theorem mellin_convolution_parseval (σ : ℝ) (f g : Hσ σ) :
    ∫ τ : ℝ, mellinTransform f (σ + I * τ) * starRingEnd ℂ (mellinTransform g (σ + I * τ)) =
    (2 * Real.pi) * ∫ x in Set.Ioi (0 : ℝ), (f x) *
    starRingEnd ℂ (g x) * (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := by
  -- This is the correct Mellin-Parseval identity for inner products
  -- ∫ M_f(σ+iτ) * conj(M_g(σ+iτ)) dτ = 2π * ∫ f(x) * conj(g(x)) * x^(2σ-1) dx
  -- Using starRingEnd ℂ for complex conjugation and proper complex exponentiation
  sorry

/-- Energy conservation in Mellin space -/
theorem mellin_energy_conservation (σ : ℝ) (f : Hσ σ) :
    ∫ x in Set.Ioi (0 : ℝ), ‖(f : ℝ → ℂ) x‖ ^ 2 * (x : ℝ) ^ (2 * σ - 1) ∂volume =
    (1 / (2 * Real.pi)) * ∫ τ : ℝ, ‖mellinTransform f (σ + I * τ)‖ ^ 2 := by
  -- Direct consequence of mellin_parseval_formula
  sorry

end Applications

end Frourio
