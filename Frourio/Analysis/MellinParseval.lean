import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParsevalCore
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

/-- Basic L² bound for functions on measurable sets -/
lemma lp2_holder_bound (f : ℝ → ℂ) (s : Set ℝ) (hs : MeasurableSet s) :
  ∫⁻ x in s, ‖f x‖₊ ^ 2 ∂volume ≤ (eLpNorm f 2 volume) ^ 2 := by
  classical
  -- view the restricted integral as an indicator integral so we can use monotonicity
  set g : ℝ → ℝ≥0∞ := fun x => (‖f x‖₊ : ℝ≥0∞) ^ 2
  have h_indicator :
      ∫⁻ x in s, g x ∂volume = ∫⁻ x, Set.indicator s g x ∂volume := by
    simp [g, hs]
  have h_indicator_le : Set.indicator s g ≤ g := by
    intro x
    by_cases hx : x ∈ s
    · simp [g, hx]
    · simp [g, hx]
  have h_subset_integral :
      ∫⁻ x in s, g x ∂volume ≤ ∫⁻ x, g x ∂volume := by
    simpa [h_indicator] using lintegral_mono h_indicator_le
  -- identify the full-space integral with the L² norm squared
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_eLp :=
      eLpNorm_eq_lintegral_rpow_enorm (μ := volume) (f := f) hp0 hp_top
  have h_eLp_sq :
      (eLpNorm f 2 volume) ^ 2 = ∫⁻ x, g x ∂volume := by
    have h_toReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    have h_integrand :
        (fun x => ‖f x‖ₑ ^ ((2 : ℝ≥0∞).toReal)) = g := by
      funext x
      simp [g, enorm_eq_nnnorm]
    have h_eLp' :
        eLpNorm f 2 volume =
          (∫⁻ x, g x ∂volume) ^ (1 / (2 : ℝ)) := by
      simpa [h_toReal, h_integrand] using h_eLp
    calc
      (eLpNorm f 2 volume) ^ 2
          = (eLpNorm f 2 volume) ^ (2 : ℝ) := by simp
      _ = ((∫⁻ x, g x ∂volume) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by simp [h_eLp']
      _ = (∫⁻ x, g x ∂volume) ^ ((1 / (2 : ℝ)) * (2 : ℝ)) := by
        simpa using
          (ENNReal.rpow_mul (∫⁻ x, g x ∂volume) (1 / (2 : ℝ)) (2 : ℝ)).symm
      _ = (∫⁻ x, g x ∂volume) ^ (1 : ℝ) := by
        simp [one_div]
      _ = ∫⁻ x, g x ∂volume := by simp
  -- combine the subset inequality with the identification of the total integral
  calc
    ∫⁻ x in s, ‖f x‖₊ ^ 2 ∂volume
        = ∫⁻ x in s, g x ∂volume := by rfl
    _ ≤ ∫⁻ x, g x ∂volume := h_subset_integral
    _ = (eLpNorm f 2 volume) ^ 2 := by simpa using h_eLp_sq.symm

/-- Change-of-variables identity for the squared norm of `LogPull`. -/
lemma logPull_sq_integral_eq (σ : ℝ) (f : Hσ σ) :
    ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure ℝ)
      = ∫⁻ x in Set.Ioi (0 : ℝ),
          (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
            * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂(volume : Measure ℝ) := by
  classical
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
  have hg_meas : Measurable g := by
    have h_comp : Measurable fun t : ℝ => Hσ.toFun f (Real.exp t) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_norm : Measurable fun t : ℝ => ‖Hσ.toFun f (Real.exp t)‖ := h_comp.norm
    have h_sq : Measurable fun t : ℝ => ‖Hσ.toFun f (Real.exp t)‖^2 := by
      simpa [pow_two] using h_norm.mul h_norm
    exact (Measurable.ennreal_ofReal h_sq)
  have h_pointwise :
      (fun t => (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ))
        =ᵐ[volume]
        fun t => g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h_logpull := LogPull_integrand_eq (σ := σ) (f := f) t
    have h_exp :
        ENNReal.ofReal (Real.exp ((2 * σ - 1) * t))
          = ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) := by
      have : (2 * σ - 1) * t = (2 * σ - 2) * t + t := by ring
      simp [this]
    calc
      (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
          = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
              * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t)) := h_logpull
      _ = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
              * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) := by
                simp [h_exp]
      _ = g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) := by
                simp [g]
  have h_lhs :
      ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) ∂volume :=
    lintegral_congr_ae h_pointwise
  have h_change_restrict :=
      lintegral_change_of_variables_exp (α := 2 * σ - 2) (f := g) hg_meas
  have h_rhs_restrict :
      ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 2))
            ∂(volume.restrict (Set.Ioi 0))
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 1) / x)
            ∂(volume.restrict (Set.Ioi 0)) := by
    refine lintegral_congr_ae ?_
    refine ((ae_restrict_iff' measurableSet_Ioi).2 ?_)
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hxpos : 0 < x := hx
    have hx_ne : x ≠ 0 := ne_of_gt hxpos
    have hpow_mul : x ^ (2 * σ - 1) = x ^ (2 * σ - 2) * x := by
      have : 2 * σ - 1 = (2 * σ - 2) + 1 := by ring
      simp [this, Real.rpow_add hxpos, Real.rpow_one]
    have hpow_div : ENNReal.ofReal (x ^ (2 * σ - 2))
        = ENNReal.ofReal (x ^ (2 * σ - 1) / x) := by
      have hdiv : x ^ (2 * σ - 1) / x = x ^ (2 * σ - 2) := by
        calc
          x ^ (2 * σ - 1) / x
              = (x ^ (2 * σ - 1)) * x⁻¹ := by simp [div_eq_mul_inv]
          _ = (x ^ (2 * σ - 2) * x) * x⁻¹ := by simp [hpow_mul]
          _ = x ^ (2 * σ - 2) * (x * x⁻¹) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
          _ = x ^ (2 * σ - 2) := by simp [hx_ne]
      simp [hdiv.symm]
    have h_g : g (Real.log x) = ENNReal.ofReal (‖Hσ.toFun f x‖^2) := by
      simp [g, Real.exp_log hxpos]
    have h_norm_sq :
        ENNReal.ofReal (‖Hσ.toFun f x‖^2)
          = (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) := by
      rw [pow_two]
      simp only [sq]
      rw [ENNReal.ofReal_mul (norm_nonneg _)]
      simp
    calc
      g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 2))
          = ENNReal.ofReal (‖Hσ.toFun f x‖^2)
              * ENNReal.ofReal (x ^ (2 * σ - 2)) := by
                simp [h_g]
      _ = (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 2)) := by
                simp [h_norm_sq]
      _ = (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 1) / x) := by
                simp [hpow_div]
  have h_change :
      ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) ∂volume := by
    simpa using h_change_restrict
  have h_rhs :
      ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume := by
    simpa using h_rhs_restrict
  calc
    ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) ∂volume := h_lhs
    _ = ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) *
        ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := h_change.symm
    _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
            * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume := h_rhs

/-- Helper lemma for multiplying inequalities with ENNReal powers -/
lemma ennreal_pow_mul_le_of_le {a b c d : ENNReal} (h1 : a ≤ b) (h2 : c < d) (n : ℕ) :
    a ^ n * c ≤ b ^ n * d := by
  have h_pow : a ^ n ≤ b ^ n := by
    -- For ENNReal, a ≤ b implies a^n ≤ b^n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul' ih h1
  exact mul_le_mul' h_pow (le_of_lt h2)

/-- The L² integral over a subset is bounded by the total L² norm squared -/
lemma l2_integral_volume_bound (f_L2 : ℝ → ℂ) (s : Set ℝ) (hs_meas : MeasurableSet s) :
    ∫⁻ x in s, ‖f_L2 x‖₊ ^ 2 ∂volume ≤ (eLpNorm f_L2 2 volume) ^ 2 := by
  -- This is the correct bound: ∫_s |f|² ≤ ∫_ℝ |f|² = ‖f‖_L²²
  -- The integral over a subset is at most the integral over the entire space
  simpa using lp2_holder_bound (f := f_L2) (s := s) (hs := hs_meas)

/-- Helper lemma for measure continuity on closed balls -/
lemma measure_continuity_closed_ball {R : ℝ}
    (h_empty_measure : volume (⋂ n : ℕ, {x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R) = 0) :
    Filter.Tendsto (fun n : ℕ => volume ({x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R))
      Filter.atTop (𝓝 0) := by
  -- Use measure continuity for decreasing sequences of sets
  -- The sequence is antimono and the intersection has measure 0
  have h_antimono : Antitone (fun n : ℕ => {x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R) := by
    intro n m hnm
    apply Set.inter_subset_inter_left
    intro x hx
    have h_le : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    exact lt_of_le_of_lt h_le hx
  -- The closed ball has finite measure, so the intersection has finite measure
  have h_finite_seq : ∀ n, volume ({x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R) < ∞ := by
    intro n
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_right)
      (MeasureTheory.measure_closedBall_lt_top (x := (0 : ℝ)) (r := R))
  -- Each set is null-measurable
  have h_null_measurable : ∀ n, NullMeasurableSet
      ({x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R) := by
    intro n
    apply NullMeasurableSet.inter
    · exact nullMeasurableSet_lt measurable_const.aemeasurable measurable_norm.aemeasurable
    · exact measurableSet_closedBall.nullMeasurableSet
  -- Apply measure continuity theorem for sequences indexed by ℕ
  -- The null measurable condition for ℕ
  have h_null_measurable_nat : ∀ n : ℕ, NullMeasurableSet
      ({x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R) := by
    intro n
    apply NullMeasurableSet.inter
    · exact nullMeasurableSet_lt measurable_const.aemeasurable measurable_norm.aemeasurable
    · exact measurableSet_closedBall.nullMeasurableSet
  -- The finite measure condition for ℕ
  have h_finite_exists_nat : ∃ n : ℕ, volume
      ({x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R) ≠ ∞ := by
    use 0
    simp only [Nat.cast_zero]
    exact (h_finite_seq 0).ne
  have h_tendsto := MeasureTheory.tendsto_measure_iInter_atTop
      h_null_measurable_nat h_antimono h_finite_exists_nat
  rw [h_empty_measure] at h_tendsto
  exact h_tendsto

/-- The measure of tail sets intersected with closed balls tends to zero -/
lemma tendsto_tail_measure_closed_ball_zero : ∀ R > 0, Filter.Tendsto
    (fun n : ℕ => volume ({x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R))
    Filter.atTop (𝓝 0) := by
  -- This is a standard result: as the radius n increases, the tail set {x : n < ‖x‖}
  -- becomes smaller and its measure tends to 0
  -- The proof uses that the sets form a decreasing sequence and their intersection is empty

  -- Key insight: The sets {x : n < ‖x‖} form a decreasing nested sequence
  -- As n → ∞, these sets shrink and their intersection is empty
  -- Therefore their measures tend to 0

  -- The sets are antimono: if n ≤ m then {x : m < ‖x‖} ⊆ {x : n < ‖x‖}
  have h_antimono : Antitone (fun n : ℕ => {x : ℝ | (n : ℝ) < ‖x‖}) := by
    intro n m hnm
    intro x hx
    -- If x ∈ {y : m < ‖y‖} and n ≤ m, then x ∈ {y : n < ‖y‖}
    -- Because if m < ‖x‖ and n ≤ m, then n < ‖x‖
    have h_le : (n : ℝ) ≤ (m : ℝ) := by exact Nat.cast_le.mpr hnm
    exact lt_of_le_of_lt h_le hx

  -- The intersection of all these sets is empty
  have h_empty_inter : ⋂ n, {x : ℝ | (n : ℝ) < ‖x‖} = ∅ := by
    -- For any point x, we can find n large enough so that n > ‖x‖
    -- Then x ∉ {y : n < ‖y‖}, so x is not in the intersection
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false]
    -- After simp, we need to show (∀ (i : ℝ), x ∈ {x | i < ‖x‖}) ↔ False
    -- This means showing that ∀ (i : ℝ), i < ‖x‖ is false
    constructor
    · -- Forward direction: if ∀ i, i < ‖x‖, then False
      intro h
      -- h : ∀ (i : ℝ), x ∈ {x_1 | i < ‖x_1‖}
      -- This means ∀ (i : ℝ), i < ‖x‖
      -- But this is false because we can take i = ‖x‖ + 1
      specialize h (‖x‖ + 1)
      -- h : x ∈ {x_1 | ‖x‖ + 1 < ‖x_1‖}
      -- This means ‖x‖ + 1 < ‖x‖
      simp at h
      -- h : ‖x‖ + 1 < ‖x‖
      linarith
    · -- Backward direction: False implies ∀ i, i < ‖x‖
      intro h
      -- h : False
      exact False.elim h

  -- Apply the standard measure theory result
  -- This uses the fact that decreasing sequences of sets with empty intersection
  -- have measures tending to 0 (when one set has finite measure)
  --
  -- We use MeasureTheory.tendsto_measure_iInter_atTop which states:
  -- For a decreasing sequence of measurable sets with empty intersection,
  -- if at least one set has finite measure, then the measures tend to 0
  --
  -- The theorem needs the intersection to be empty and the sequence to be antimono
  have h_inter_eq_measure_nat : volume (⋂ n : ℕ, {x : ℝ | (n : ℝ) < ‖x‖}) = 0 := by
    have h_eq : (⋂ n : ℕ, {x : ℝ | (n : ℝ) < ‖x‖}) = (⋂ n, {x : ℝ | (n : ℝ) < ‖x‖}) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h n
        -- We need to show n < ‖x‖ given ∀ (m : ℕ), (m : ℝ) < ‖x‖
        -- Take m = ⌈n⌉₊ (ceiling of n as a natural number)
        have ⟨m, hm⟩ : ∃ m : ℕ, n ≤ m := exists_nat_ge n
        have h_cast : (m : ℝ) < ‖x‖ := h m
        exact lt_of_le_of_lt hm h_cast
      · intro h m
        exact h (m : ℝ)
    rw [h_eq, h_empty_inter]
    exact MeasureTheory.measure_empty

  -- For any R > 0, show that the intersection with closed ball goes to 0
  intro R hR
  -- The sets {x : n < ‖x‖} ∩ closedBall(0,R) form a decreasing sequence
  -- When n > R, this intersection becomes empty
  have h_inter_empty : (⋂ n : ℕ, {x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_closedBall,
               dist_zero_right, Set.mem_empty_iff_false, iff_false]
    intro h
    -- h states: ∀ n, (n : ℝ < ‖x‖ ∧ ‖x‖ ≤ R)
    -- Take n = ⌈R⌉₊ + 1, then we have both (⌈R⌉₊ + 1) < ‖x‖ and ‖x‖ ≤ R
    have h_spec := h (Nat.ceil R + 1)
    have h_ball : ‖x‖ ≤ R := h_spec.2
    have h_large : (Nat.ceil R + 1 : ℝ) < ‖x‖ := by
      convert h_spec.1
      simp [Nat.cast_add, Nat.cast_one]
    have h_ge : R < Nat.ceil R + 1 := by
      calc R
        ≤ ⌈R⌉₊ := Nat.le_ceil R
        _ < ⌈R⌉₊ + 1 := by simp
    linarith

  -- We already have that this intersection is empty
  -- Let's use that fact directly
  have h_iInter_empty : (⋂ n : ℕ, {x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R) = ∅ :=
    h_inter_empty

  -- The measure of the empty set is 0
  have h_measure_zero :
      volume (⋂ n : ℕ, {x : ℝ | (n : ℝ) < ‖x‖} ∩ Metric.closedBall 0 R) = 0 := by
    rw [h_iInter_empty]; simp

  -- By measure continuity, the sequence converges to 0
  exact measure_continuity_closed_ball h_measure_zero

/-- The tail set `{x : ℝ | R < ‖x‖}` is measurable for every real `R`. -/
lemma measurableSet_tail_norm (R : ℝ) :
    MeasurableSet {x : ℝ | R < ‖x‖} := by
  classical
  simpa using measurableSet_lt measurable_const measurable_norm

/-- If `R₁ ≤ R₂`, then the tail sets are nested: `{‖x‖ > R₂} ⊆ {‖x‖ > R₁}`. -/
lemma tail_set_subset {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) :
    {x : ℝ | R₂ < ‖x‖} ⊆ {x : ℝ | R₁ < ‖x‖} := by
  intro x hx
  exact lt_of_le_of_lt hR hx

/-- For nonnegative functions, the indicators of nested sets satisfy a pointwise
    inequality. -/
lemma indicator_le_indicator_of_subset {α : Type*} {s t : Set α}
    (h_subset : s ⊆ t) (f : α → ℝ≥0∞) :
    Set.indicator s f ≤ Set.indicator t f := by
  classical
  intro x
  by_cases hx : x ∈ s
  · have hx' : x ∈ t := h_subset hx
    simp [Set.indicator, hx, hx']
  · simp [Set.indicator, hx]

/-- Increasing the tail radius can only decrease the tail integral. -/
lemma tail_integral_mono (f : ℝ → ℂ) {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) :
    ∫⁻ x in {x : ℝ | R₂ < ‖x‖}, ‖f x‖₊ ^ 2 ∂volume ≤
        ∫⁻ x in {x : ℝ | R₁ < ‖x‖}, ‖f x‖₊ ^ 2 ∂volume := by
  classical
  set g : ℝ → ℝ≥0∞ := fun x => ‖f x‖₊ ^ 2
  have h_subset : {x : ℝ | R₂ < ‖x‖} ⊆ {x : ℝ | R₁ < ‖x‖} := tail_set_subset hR
  have h_indicator_le :
      Set.indicator {x : ℝ | R₂ < ‖x‖} g ≤
        Set.indicator {x : ℝ | R₁ < ‖x‖} g :=
    indicator_le_indicator_of_subset h_subset g
  have h_indicator_le_ae :
      Set.indicator {x : ℝ | R₂ < ‖x‖} g ≤ᵐ[volume]
        Set.indicator {x : ℝ | R₁ < ‖x‖} g :=
    Filter.Eventually.of_forall h_indicator_le
  have h_meas_R₁ : MeasurableSet {x : ℝ | R₁ < ‖x‖} := measurableSet_tail_norm R₁
  have h_meas_R₂ : MeasurableSet {x : ℝ | R₂ < ‖x‖} := measurableSet_tail_norm R₂
  have h_indicator_integral_le :=
      MeasureTheory.lintegral_mono_ae h_indicator_le_ae
  have h_indicator_eq_R₁ :
      ∫⁻ x, Set.indicator {x : ℝ | R₁ < ‖x‖} g x ∂volume =
          ∫⁻ x in {x : ℝ | R₁ < ‖x‖}, g x ∂volume :=
    MeasureTheory.lintegral_indicator (μ := volume)
      (hs := h_meas_R₁) (f := g)
  have h_indicator_eq_R₂ :
      ∫⁻ x, Set.indicator {x : ℝ | R₂ < ‖x‖} g x ∂volume =
          ∫⁻ x in {x : ℝ | R₂ < ‖x‖}, g x ∂volume :=
    MeasureTheory.lintegral_indicator (μ := volume)
      (hs := h_meas_R₂) (f := g)
  -- Convert back to integrals over the restricted domains
  refine
    calc
      ∫⁻ x in {x : ℝ | R₂ < ‖x‖}, g x ∂volume
          = ∫⁻ x, Set.indicator {x : ℝ | R₂ < ‖x‖} g x ∂volume := by
            simpa [g] using h_indicator_eq_R₂.symm
      _ ≤ ∫⁻ x, Set.indicator {x : ℝ | R₁ < ‖x‖} g x ∂volume := h_indicator_integral_le
      _ = ∫⁻ x in {x : ℝ | R₁ < ‖x‖}, g x ∂volume := by
            simpa [g] using h_indicator_eq_R₁

/-- Every tail integral is bounded by the full L² norm squared. -/
lemma tail_integral_le_total (f : ℝ → ℂ) (R : ℝ) :
    ∫⁻ x in {x : ℝ | R < ‖x‖}, ‖f x‖₊ ^ 2 ∂volume ≤ (eLpNorm f 2 volume) ^ 2 :=
  l2_integral_volume_bound (f_L2 := f)
    (s := {x : ℝ | R < ‖x‖}) (hs_meas := measurableSet_tail_norm R)

/-- Tail integral of L² functions can be made arbitrarily small -/
lemma l2_tail_integral_small (f_L2 : ℝ → ℂ)
    (h_finite : eLpNorm f_L2 2 volume < ∞) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R₀ ≥ 1, ∀ R ≥ R₀, ∫⁻ x in {x : ℝ | R < ‖x‖}, ‖f_L2 x‖₊ ^ 2 ∂volume < ENNReal.ofReal δ := by
  classical
  set g : ℝ → ℝ≥0∞ := fun x => ‖f_L2 x‖₊ ^ 2
  set μ : Measure ℝ := volume.withDensity g
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) := by norm_num
  have h_eLp :=
    eLpNorm_eq_lintegral_rpow_enorm (μ := volume) (f := f_L2) hp0 hp_top
  have h_toReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  have h_integrand :
      (fun x => ‖f_L2 x‖ₑ ^ ((2 : ℝ≥0∞).toReal)) = g := by
    funext x
    simp [g, enorm_eq_nnnorm]
  have h_eLp' :
      eLpNorm f_L2 2 volume =
        (∫⁻ x, g x ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa [h_toReal, h_integrand] using h_eLp
  have h_total_eq :
      (eLpNorm f_L2 2 volume) ^ 2 = ∫⁻ x, g x ∂volume := by
    calc
      (eLpNorm f_L2 2 volume) ^ 2
          = (eLpNorm f_L2 2 volume) ^ (2 : ℝ) := by simp
      _ = ((∫⁻ x, g x ∂volume) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by
            simp [h_eLp']
      _ = (∫⁻ x, g x ∂volume) ^ ((1 / (2 : ℝ)) * (2 : ℝ)) := by
            simpa using
              (ENNReal.rpow_mul (∫⁻ x, g x ∂volume) (1 / (2 : ℝ)) (2 : ℝ)).symm
      _ = (∫⁻ x, g x ∂volume) ^ (1 : ℝ) := by simp [one_div]
      _ = ∫⁻ x, g x ∂volume := by simp
  have h_total_lt_top : ∫⁻ x, g x ∂volume < ∞ := by
    have h_sq_lt_top :
        (eLpNorm f_L2 2 volume) ^ 2 < ∞ := by
      have hf_lt_top : eLpNorm f_L2 2 volume < ∞ := h_finite
      have h_mul_lt_top :
          eLpNorm f_L2 2 volume * eLpNorm f_L2 2 volume < ∞ :=
        ENNReal.mul_lt_top hf_lt_top hf_lt_top
      simpa [pow_two] using h_mul_lt_top
    simpa [h_total_eq] using h_sq_lt_top
  have hμ_univ_lt_top : μ Set.univ < ∞ := by
    simpa [μ, h_total_eq] using h_total_lt_top
  let s : ℕ → Set ℝ := fun n => {x : ℝ | (n : ℝ) < ‖x‖}
  have hs_null : ∀ n, NullMeasurableSet (s n) μ := by
    intro n
    exact (measurableSet_tail_norm (n : ℝ)).nullMeasurableSet
  have hs_antitone : Antitone s := by
    intro n m hnm x hx
    have hx' : (m : ℝ) < ‖x‖ := by simpa [s] using hx
    have h_le : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    have hx'' : (n : ℝ) < ‖x‖ := lt_of_le_of_lt h_le hx'
    simpa [s] using hx''
  have hs_inter_empty : ⋂ n, s n = (∅ : Set ℝ) := by
    ext x; constructor
    · intro hx
      have hx_mem : ∀ n, x ∈ s n := Set.mem_iInter.1 hx
      have hx' : x ∈ s (Nat.floor ‖x‖ + 1) := hx_mem (Nat.floor ‖x‖ + 1)
      have h_not : ¬ ((Nat.floor ‖x‖ + 1 : ℝ) < ‖x‖) := by
        have h_lt : ‖x‖ < (Nat.floor ‖x‖ + 1 : ℝ) := by
          simpa using Nat.lt_floor_add_one (‖x‖)
        exact not_lt.mpr h_lt.le
      exact (h_not <| by simpa [s] using hx')
    · intro hx
      simpa using hx.elim
  have hs_inter_zero : μ (⋂ n, s n) = 0 := by
    simp [μ, hs_inter_empty]
  have hs_finite : ∃ n, μ (s n) ≠ ∞ := by
    refine ⟨0, ?_⟩
    have h_le : μ (s 0) ≤ μ Set.univ := by
      exact measure_mono (μ := μ) (by intro x _; trivial)
    have h_lt := lt_of_le_of_lt h_le hμ_univ_lt_top
    exact h_lt.ne
  have h_tendsto :=
    MeasureTheory.tendsto_measure_iInter_atTop (μ := μ) hs_null hs_antitone hs_finite
  have h_tendsto_zero :
      Filter.Tendsto (fun n : ℕ => μ (s n)) Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [hs_inter_zero] using h_tendsto
  have h_nhds : Set.Iio (ENNReal.ofReal δ) ∈ 𝓝 (0 : ℝ≥0∞) := by
    refine IsOpen.mem_nhds isOpen_Iio ?_
    simpa using ENNReal.ofReal_pos.mpr hδ
  have h_eventually := h_tendsto_zero.eventually h_nhds
  have h_eventually' : ∀ᶠ n in Filter.atTop, μ (s n) < ENNReal.ofReal δ := by
    refine h_eventually.mono ?_
    intro n hn
    simpa [Set.mem_Iio] using hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually'
  have h_tail_measure : ∀ R : ℝ,
      μ {x : ℝ | R < ‖x‖} = ∫⁻ x in {x : ℝ | R < ‖x‖}, g x ∂volume := by
    intro R
    have h_meas : MeasurableSet {x : ℝ | R < ‖x‖} := measurableSet_tail_norm R
    simpa [μ, g] using MeasureTheory.withDensity_apply g h_meas
  have h_tail_small_nat : ∀ n ≥ N,
      ∫⁻ x in {x : ℝ | (n : ℝ) < ‖x‖}, g x ∂volume < ENNReal.ofReal δ := by
    intro n hn
    have hμ_small := hN n hn
    have hμ_small_set : μ {x : ℝ | (n : ℝ) < ‖x‖} < ENNReal.ofReal δ := by
      simpa [s] using hμ_small
    have h_int_lt :
        ∫⁻ x in {x : ℝ | (n : ℝ) < ‖x‖}, g x ∂volume < ENNReal.ofReal δ := by
      convert hμ_small_set using 1
      exact (h_tail_measure (n : ℝ)).symm
    exact h_int_lt
  refine ⟨max (N : ℝ) 1, le_max_right _ _, ?_⟩
  intro R hR
  have hR_ge_cast : (N : ℝ) ≤ R :=
    (le_trans (le_max_left (N : ℝ) 1) hR)
  have hR_ge_one : (1 : ℝ) ≤ R :=
    (le_trans (le_max_right (N : ℝ) 1) hR)
  have hR_nonneg : 0 ≤ R := le_trans (show (0 : ℝ) ≤ 1 by norm_num) hR_ge_one
  set n := Nat.floor R with hn_def
  have hN_le_floor : N ≤ n := by
    have h_floor_mono := Nat.floor_mono hR_ge_cast
    have h_floor_nat : Nat.floor (N : ℝ) = N := by simp
    simpa [hn_def, h_floor_nat] using h_floor_mono
  have h_floor_le : (n : ℝ) ≤ R := by
    simpa [hn_def] using Nat.floor_le hR_nonneg
  have h_tail_floor_lt := h_tail_small_nat n hN_le_floor
  have h_tail_le :=
    tail_integral_mono (f := f_L2) (R₁ := (n : ℝ)) (R₂ := R) h_floor_le
  have h_lt := lt_of_le_of_lt h_tail_le h_tail_floor_lt
  simpa [g] using h_lt

/-- The L² norm of the difference between a function and its truncation equals the
    square root of the tail integral -/
lemma truncation_error_eq_tail_norm (f : ℝ → ℂ) (_hf : MemLp f 2 volume) (R : ℝ) (_hR : 0 < R) :
    eLpNorm (f - fun x => if ‖x‖ ≤ R then f x else 0) 2 volume =
    (∫⁻ x in {x : ℝ | R < ‖x‖}, ‖f x‖₊ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
  -- The difference f - f_R is nonzero exactly on {x | R < ‖x‖}
  -- So ‖f - f_R‖₂² = ∫_{‖x‖>R} ‖f(x)‖² dx
  classical
  set f_trunc : ℝ → ℂ := fun x => if ‖x‖ ≤ R then f x else 0
  set tail : Set ℝ := {x : ℝ | R < ‖x‖}
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_toReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  classical
  have h_norm_indicator :
      (fun x : ℝ => (‖(f - f_trunc) x‖₊ : ℝ≥0∞)) =
        Set.indicator tail (fun x : ℝ => (‖f x‖₊ : ℝ≥0∞)) := by
    classical
    funext x
    by_cases hx : x ∈ tail
    · have hx_not_le : ¬ ‖x‖ ≤ R := not_le_of_gt (by simpa [tail] using hx)
      have hx_abs_not_le : ¬ |x| ≤ R := by simpa [Real.norm_eq_abs] using hx_not_le
      have hx_abs_mem : x ∈ {x : ℝ | R < |x|} :=
        by simpa [tail, Real.norm_eq_abs] using hx
      simp [tail, hx_abs_not_le, hx_abs_mem, f_trunc,
        sub_eq_add_neg, Real.norm_eq_abs]
    · have hx_le : ‖x‖ ≤ R := le_of_not_gt (by simpa [tail] using hx)
      have hx_abs_le : |x| ≤ R := by simpa [Real.norm_eq_abs] using hx_le
      have hx_abs_not_mem : x ∉ {x : ℝ | R < |x|} :=
        by simpa [tail, Real.norm_eq_abs] using show x ∉ tail from hx
      simp [tail, hx_abs_le, hx_abs_not_mem, f_trunc, Real.norm_eq_abs]
  have h_indicator :
      (fun x : ℝ => ‖(f - f_trunc) x‖ₑ ^ ((2 : ℝ≥0∞).toReal)) =
        Set.indicator tail
          (fun x : ℝ => (‖f x‖₊ : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)) := by
    classical
    funext x
    by_cases hx : x ∈ tail
    · have hx_not_le : ¬ ‖x‖ ≤ R := not_le_of_gt (by simpa [tail] using hx)
      have hx_abs_not_le : ¬ |x| ≤ R := by simpa [Real.norm_eq_abs] using hx_not_le
      have hx_abs_mem : x ∈ {x : ℝ | R < |x|} :=
        by simpa [tail, Real.norm_eq_abs] using hx
      simp [tail, hx_abs_not_le, hx_abs_mem, f_trunc,
        sub_eq_add_neg, Real.norm_eq_abs]
    · have hx_le : ‖x‖ ≤ R := le_of_not_gt (by simpa [tail] using hx)
      have hx_abs_le : |x| ≤ R := by simpa [Real.norm_eq_abs] using hx_le
      have hx_abs_not_mem : x ∉ {x : ℝ | R < |x|} :=
        by simpa [tail, Real.norm_eq_abs] using show x ∉ tail from hx
      simp [tail, hx_abs_le, hx_abs_not_mem, f_trunc, Real.norm_eq_abs]
  have h_indicator_pow :
      (fun x : ℝ => (↑‖f x - f_trunc x‖₊ : ℝ≥0∞) ^ 2) =
        Set.indicator tail
          (fun x : ℝ => (‖f x‖₊ : ℝ≥0∞) ^ 2) := by
    classical
    funext x
    by_cases hx : x ∈ tail
    · have hx_not_le : ¬ ‖x‖ ≤ R := not_le_of_gt (by simpa [tail] using hx)
      have hx_abs_not_le : ¬ |x| ≤ R := by simpa [Real.norm_eq_abs] using hx_not_le
      have hx_abs_mem : x ∈ {x : ℝ | R < |x|} :=
        by simpa [tail, Real.norm_eq_abs] using hx
      simp [tail, hx_abs_not_le, hx_abs_mem, f_trunc,
        sub_eq_add_neg, Real.norm_eq_abs]
    · have hx_le : ‖x‖ ≤ R := le_of_not_gt (by simpa [tail] using hx)
      have hx_abs_le : |x| ≤ R := by simpa [Real.norm_eq_abs] using hx_le
      have hx_abs_not_mem : x ∉ {x : ℝ | R < |x|} :=
        by simpa [tail, Real.norm_eq_abs] using hx
      simp [tail, hx_abs_le, hx_abs_not_mem, f_trunc, Real.norm_eq_abs]
  have h_meas : MeasurableSet tail := by
    simpa [tail] using measurableSet_tail_norm R
  have h_lintegral :
      ∫⁻ x, ‖(f - f_trunc) x‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂volume =
        ∫⁻ x in tail, (‖f x‖₊ : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal) ∂volume := by
    classical
    calc
      ∫⁻ x, ‖(f - f_trunc) x‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂volume
          = ∫⁻ x,
              (↑‖f x - f_trunc x‖₊ : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)
              ∂volume := by
                have h_integrand :
                    (fun x : ℝ => ‖(f - f_trunc) x‖ₑ ^ ((2 : ℝ≥0∞).toReal)) =
                      fun x : ℝ =>
                        (↑‖f x - f_trunc x‖₊ : ℝ≥0∞) ^
                          ((2 : ℝ≥0∞).toReal) := by
                  funext x; simp [Pi.sub_apply, enorm_eq_nnnorm]
                simp
      _ = ∫⁻ x,
              (↑‖f x - f_trunc x‖₊ : ℝ≥0∞) ^ (2 : ℝ)
              ∂volume := by simp
      _ = ∫⁻ x,
              Set.indicator tail
                (fun x : ℝ => (‖f x‖₊ : ℝ≥0∞) ^ 2) x
                ∂volume := by
                simp [h_indicator_pow]
      _ = ∫⁻ x in tail, (‖f x‖₊ : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal) ∂volume := by
            simpa [h_toReal] using
              (MeasureTheory.lintegral_indicator (μ := volume)
                (hs := h_meas)
                (f := fun x : ℝ => (‖f x‖₊ : ℝ≥0∞) ^ 2))
  have h_lintegral_pow2 :
      ∫⁻ x, (↑‖f x - f_trunc x‖₊ : ℝ≥0∞) ^ 2 ∂volume =
        ∫⁻ x in tail, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    have h' :
        ∫⁻ x, (↑‖f x - f_trunc x‖₊ : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal) ∂volume =
          ∫⁻ x in tail, (‖f x‖₊ : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal) ∂volume := by
      simpa [Pi.sub_apply, enorm_eq_nnnorm] using h_lintegral
    simpa [h_toReal] using h'
  have h_eLp :=
    eLpNorm_eq_lintegral_rpow_enorm (μ := volume) (f := f - f_trunc) hp0 hp_top
  have h_target' :
      eLpNorm (f - f_trunc) 2 volume =
        (∫⁻ x in tail, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂volume) ^ (1 / (2 : ℝ≥0∞).toReal) :=
    by simpa [h_lintegral_pow2] using h_eLp
  have h_target :
      eLpNorm (f - f_trunc) 2 volume =
        (∫⁻ x in tail, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    simpa [h_toReal] using h_target'
  have h_pow : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  simpa [f_trunc, tail, Real.norm_eq_abs, h_pow] using h_target

/-- Smooth compactly supported functions are dense in L²(ℝ) -/
lemma l2_truncation_approximation (f_L2 : ℝ → ℂ) (hf : MemLp f_L2 2 volume) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, R > 0 ∧
    eLpNorm (f_L2 - fun x => if ‖x‖ ≤ R then f_L2 x else 0) 2 volume < ENNReal.ofReal ε := by
  -- This is a standard result: L² functions have tails that vanish in L² norm
  -- For f ∈ L²(ℝ), define f_R(x) = f(x) if |x| ≤ R, 0 otherwise
  -- Then ‖f - f_R‖₂² = ∫_{|x|>R} |f(x)|² dx → 0 as R → ∞
  -- This follows from the monotone convergence theorem applied to the tail integrals

  -- Step 1: Use the fact that f_L2 has finite L² norm
  have h_finite : eLpNorm f_L2 2 volume < ∞ := hf.eLpNorm_lt_top

  -- Step 2: Define the tail function for radius R
  let tail_norm_sq (R : ℝ) : ℝ≥0∞ := ∫⁻ x in {x : ℝ | R < ‖x‖}, ‖f_L2 x‖₊ ^ 2 ∂volume

  -- Step 3: Show that tail_norm_sq R → 0 as R → ∞
  have h_tail_vanish : ∀ δ > 0, ∃ R₀ > 0, ∀ R ≥ R₀, tail_norm_sq R < ENNReal.ofReal δ := by
    intro δ hδ
    -- Use the fact that ∫ ‖f‖² < ∞, so the tail integral vanishes
    -- This follows from the definition of L² and the monotone convergence theorem
    -- The sequence of sets {x | R < ‖x‖} is decreasing to ∅ as R → ∞
    have h_decreasing : ∀ R₁ R₂, R₁ ≤ R₂ → {x : ℝ | R₂ < ‖x‖} ⊆ {x : ℝ | R₁ < ‖x‖} := by
      intros R₁ R₂ h x hx
      simp at hx ⊢
      exact lt_of_le_of_lt h hx

    -- Use continuity of measure from above (since ∩_{n} {x | n < ‖x‖} = ∅)
    have h_inter_empty : (⋂ n : ℕ, {x : ℝ | (n : ℝ) < ‖x‖}) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      -- Goal: (∀ n : ℕ, (n : ℝ) < ‖x‖) ↔ False
      constructor
      · -- ∀ (i : ℕ), ↑i < ‖x‖ → False
        intro h_all
        -- h_all : ∀ n : ℕ, (n : ℝ) < ‖x‖
        -- This means ‖x‖ is greater than all natural numbers, which is impossible
        obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
        exact lt_irrefl (n : ℝ) (lt_trans (h_all n) hn)
      · -- False → ∀ (i : ℕ), ↑i < ‖x‖
        intro h_false
        exact False.elim h_false

    obtain ⟨R₀, hR₀_ge, h_tail_small⟩ := l2_tail_integral_small f_L2 h_finite δ hδ
    use max R₀ 1
    constructor
    · exact lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)

    intro R hR
    exact h_tail_small R (le_trans (le_max_left R₀ 1) hR)

  -- Step 4: Apply this to ε² to get the desired R
  have hε_sq_pos : 0 < ε ^ 2 := by
    have h_pos := mul_pos hε hε
    simpa [pow_two] using h_pos
  obtain ⟨R₀, hR₀_pos, hR₀⟩ := h_tail_vanish (ε ^ 2) hε_sq_pos
  use max R₀ 1
  constructor
  · exact lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)

  -- Step 5: Show that the truncation error equals the tail integral
  have h_max_pos : 0 < max R₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)
  have h_trunc_eq_tail := truncation_error_eq_tail_norm f_L2 hf (max R₀ 1) h_max_pos
  rw [h_trunc_eq_tail]
  -- Step 6: Apply the tail bound and take square roots
  have hR_bound := hR₀ (max R₀ 1) (le_max_left R₀ 1)
  have h_sqrt_bound := ENNReal.rpow_lt_rpow hR_bound (by norm_num : (0 : ℝ) < 1 / 2)
  have h_sqrt_bound' :
      tail_norm_sq (max R₀ 1) ^ (1 / 2 : ℝ) <
        ENNReal.ofReal (ε ^ 2) ^ (1 / 2 : ℝ) := by
    convert h_sqrt_bound
  have h_sq_nonneg : 0 ≤ ε ^ 2 := by
    have h_nonneg := mul_self_nonneg ε
    simpa [pow_two] using h_nonneg
  have h_rpow_eq : (ε ^ 2) ^ (1 / 2 : ℝ) = ε := by
    have h_sqrt := Real.sqrt_sq (le_of_lt hε)
    have h_pow := Real.sqrt_eq_rpow (ε ^ 2)
    simpa [h_pow] using h_sqrt
  have h_final : tail_norm_sq (max R₀ 1) ^ (1 / 2 : ℝ) < ENNReal.ofReal ε := by
    have h_eq0 :
        ENNReal.ofReal (ε ^ 2) ^ (1 / 2 : ℝ) =
          ENNReal.ofReal ((ε ^ 2) ^ (1 / 2 : ℝ)) := by
      simpa [one_div] using
        ENNReal.ofReal_rpow_of_nonneg (x := ε ^ 2) h_sq_nonneg
          (by norm_num : 0 ≤ (1 / 2 : ℝ))
    have h_eq1 :
        ENNReal.ofReal ((ε ^ 2) ^ (1 / 2 : ℝ)) = ENNReal.ofReal ε :=
      congrArg ENNReal.ofReal h_rpow_eq
    have h_eq := h_eq0.trans h_eq1
    exact lt_of_lt_of_eq h_sqrt_bound' h_eq
  simpa [tail_norm_sq] using h_final

/-- If f is in L² and we truncate it to a ball, the result is still in L² -/
lemma truncated_function_memLp (f : ℝ → ℂ) (hf : MemLp f 2 volume) (R : ℝ) :
    MemLp (fun x => if ‖x‖ ≤ R then f x else 0) 2 volume := by
  -- Since the truncated function is bounded by f and has compact support, it's in L²
  -- This follows from the fact that truncation preserves L² membership
  classical
  have h_meas : MeasurableSet (Metric.closedBall (0 : ℝ) R) :=
    measurableSet_closedBall
  have h_indicator :
      MemLp (Set.indicator (Metric.closedBall (0 : ℝ) R) f) 2 volume :=
    MemLp.indicator (μ := volume) (p := (2 : ℝ≥0∞))
      (s := Metric.closedBall (0 : ℝ) R) (f := f) h_meas hf
  have h_indicator_eq :
      Set.indicator (Metric.closedBall (0 : ℝ) R) f =
        fun x : ℝ => if ‖x‖ ≤ R then f x else 0 := by
    funext x
    simp [Set.indicator, Metric.mem_closedBall, dist_eq_norm]
  simpa [h_indicator_eq] using h_indicator

/-- Simple functions with compact support are dense in L² functions with compact support -/
lemma simple_function_approximation_compact_support (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hf_compact : HasCompactSupport f) (ε : ℝ) (hε : 0 < ε) :
    ∃ s_simple : SimpleFunc ℝ ℂ, HasCompactSupport s_simple ∧
    eLpNorm (fun x => f x - s_simple x) 2 volume < ENNReal.ofReal ε := by
  -- Use the standard simple function approximation theorem for functions with compact support
  -- This follows from the fact that SimpleFunc is dense in L² with compact support
  classical
  -- Step 1: Approximate `f` in L² by an arbitrary simple function.
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hε_ne : ENNReal.ofReal ε ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨s₀, hs₀_norm_lt, _hs₀_memLp⟩ :=
    MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt (μ := volume)
      (p := (2 : ℝ≥0∞)) (E := ℂ) hf hp_ne_top hε_ne

  -- Step 2: Restrict the simple function to the compact support of `f`.
  let K : Set ℝ := tsupport f
  have hK_compact : IsCompact K := hf_compact
  have hK_meas : MeasurableSet K := (isClosed_tsupport _).measurableSet
  let zeroSf : SimpleFunc ℝ ℂ := SimpleFunc.const ℝ (0 : ℂ)
  let s_simple : SimpleFunc ℝ ℂ := SimpleFunc.piecewise K hK_meas s₀ zeroSf

  -- Identify `s_simple` with the pointwise piecewise definition.
  have hs_simple_fun : (s_simple : ℝ → ℂ) = fun x => if x ∈ K then s₀ x else 0 := by
    funext x
    by_cases hx : x ∈ K
    · simp [s_simple, zeroSf, hx]
    · simp [s_simple, zeroSf, hx]

  -- The new simple function vanishes outside the compact support of `f`.
  have hs_support_zero : ∀ x, x ∉ K → (s_simple : ℝ → ℂ) x = 0 := by
    intro x hx
    simp [hs_simple_fun, hx]

  -- Hence `s_simple` inherits compact support from `f`.
  have hs_compact : HasCompactSupport s_simple :=
    HasCompactSupport.intro hK_compact hs_support_zero

  -- Step 3: Control the L² error after restricting to the support of `f`.
  have h_diff_eq_indicator :
      (fun x => f x - (s_simple : ℝ → ℂ) x) =
        Set.indicator K (fun x => f x - s₀ x) := by
    funext x
    by_cases hx : x ∈ K
    · simp [hs_simple_fun, hx]
    · have hf_zero : f x = 0 := by
        simpa [K] using image_eq_zero_of_notMem_tsupport (f := f) hx
      simp [hs_simple_fun, hx, hf_zero]

  have h_l2_le :
      eLpNorm (fun x => f x - (s_simple : ℝ → ℂ) x) 2 volume ≤
        eLpNorm (fun x => f x - s₀ x) 2 volume := by
    simpa [h_diff_eq_indicator]
      using (eLpNorm_indicator_le (s := K) (μ := volume) (p := (2 : ℝ≥0∞))
        (f := fun x => f x - s₀ x))

  -- Combine the bounds to obtain the desired inequality.
  refine ⟨s_simple, hs_compact, lt_of_le_of_lt h_l2_le ?_⟩
  simpa using hs₀_norm_lt

/-- A continuous function with compact support admits a uniform bound on its
topological support. -/
lemma continuous_bound_on_tsupport {f : ℝ → ℂ}
    (hf_cont : Continuous f) (hf_support : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ tsupport f, ‖f x‖ ≤ C := by
  classical
  have h_compact : IsCompact (tsupport f) := hf_support
  by_cases h_empty : tsupport f = (∅ : Set ℝ)
  · refine ⟨0, le_of_eq rfl, ?_⟩
    intro x hx
    simp [h_empty] at hx
  · have h_nonempty : (tsupport f).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr h_empty
    have h_norm_cont : ContinuousOn (fun x => ‖f x‖) (tsupport f) := by
      simpa using hf_cont.norm.continuousOn
    obtain ⟨x₀, hx₀, hx₀_max⟩ :=
      h_compact.exists_isMaxOn h_nonempty h_norm_cont
    have hx₀_max' : ∀ x ∈ tsupport f, ‖f x‖ ≤ ‖f x₀‖ := by
      simpa [IsMaxOn] using hx₀_max
    refine ⟨‖f x₀‖, norm_nonneg _, ?_⟩
    intro x hx
    exact hx₀_max' x hx

/-- Schwartz functions are dense in L² for the weighted LogPull function -/
lemma schwartz_density_weighted_logpull (σ : ℝ) (f : Hσ σ)
    (h_weighted_L2 : MemLp (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) 2 volume) :
    ∀ ε > 0, ∃ φ : SchwartzMap ℝ ℂ,
      eLpNorm ((fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t) -
      (φ : ℝ → ℂ) t) : ℝ → ℂ) 2 volume < ENNReal.ofReal ε := by
  -- This requires the density theorem for Schwartz functions in L²(ℝ)
  -- The function g(t) = LogPull σ f t * exp(t/2) is in L²(ℝ) by h_weighted_L2
  intro ε hε
  -- Apply the density of Schwartz functions in L²(ℝ)
  -- Since Schwartz functions are dense in L²(ℝ), and our function is in L²(ℝ),
  -- we can find a Schwartz function φ that approximates it arbitrarily well
  -- Use the fact that Schwartz functions are dense in L²(ℝ)
  -- This is a standard result from functional analysis
  have h_schwartz_dense : ∀ (f_L2 : ℝ → ℂ) (hf : MemLp f_L2 2 volume) (ε : ℝ) (hε_pos : ε > 0),
    ∃ φ : SchwartzMap ℝ ℂ, eLpNorm (f_L2 - (φ : ℝ → ℂ)) 2 volume < ENNReal.ofReal ε := by
    intro f_L2 hf ε hε_pos
    -- Use the standard density theorem:
    -- 1. Compactly supported smooth functions are dense in L²(ℝ)
    -- 2. Every compactly supported smooth function can be approximated by Schwartz functions
    -- Since f_L2 ∈ L²(ℝ), we can find a compactly supported smooth g with ‖f_L2 - g‖_L² < ε/2
    -- Then find a Schwartz φ with ‖g - φ‖_L² < ε/2, giving ‖f_L2 - φ‖_L² < ε by triangle inequality

    -- Step 1: Use density of compactly supported smooth functions in L²(ℝ)
    have hε_div_pos : 0 < ε / 2 := by linarith
    obtain ⟨g, hg_compact, hg_smooth, hg_close⟩ :=
      smooth_compactly_supported_dense_L2 f_L2 hf (ε / 2) hε_div_pos

    -- Step 2: Approximate the smooth compactly supported function by a Schwartz function
    obtain ⟨φ, hφ_approx⟩ :=
      schwartz_approximates_smooth_compactly_supported g hg_compact hg_smooth (ε / 2) hε_div_pos
    use φ

    -- Step 3: Apply triangle inequality and combine the bounds
    -- Establish measurability assumptions
    have hf_L2_meas : AEStronglyMeasurable f_L2 volume := hf.aestronglyMeasurable
    have hg_meas : AEStronglyMeasurable g volume :=
      (hg_smooth.continuous : Continuous g).aestronglyMeasurable
    have hφ_meas : AEStronglyMeasurable (φ : ℝ → ℂ) volume :=
      (SchwartzMap.continuous φ).aestronglyMeasurable
    calc eLpNorm (f_L2 - (φ : ℝ → ℂ)) 2 volume
      ≤ eLpNorm (f_L2 - g) 2 volume + eLpNorm (g - (φ : ℝ → ℂ)) 2 volume :=
          eLpNorm_triangle_diff f_L2 g (φ : ℝ → ℂ) hf_L2_meas hg_meas hφ_meas
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          ENNReal.add_lt_add hg_close hφ_approx
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by linarith : 0 ≤ ε / 2) (by linarith : 0 ≤ ε / 2)]
          congr 1
          linarith

  -- Apply this with our original function directly
  obtain ⟨φ, hφ⟩ := h_schwartz_dense (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))
    h_weighted_L2 ε hε
  use φ
  -- The result is already in the correct form
  exact hφ

/-- Connection between LogPull L² norm and Mellin transform L² norm
This states the Parseval-type equality for the Mellin transform.
Note: The actual proof requires implementing the Fourier-Plancherel theorem
for the specific weighted LogPull function. -/
lemma mellin_logpull_fourierIntegral (σ τ : ℝ) (f : Hσ σ) :
    mellinTransform (f : ℝ → ℂ) (σ + I * τ)
      = fourierIntegral
          (fun t : ℝ => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))
          (-τ / (2 * Real.pi)) := by
  classical
  have h_mellin :=
    mellin_logpull_relation (σ := σ) (f := f) (τ := τ)
  have h_kernel :
      ∀ t : ℝ,
        fourierKernel (-τ / (2 * Real.pi)) t
          * (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))
            = LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)
              * Complex.exp (Complex.I * τ * t) := by
    intro t
    have h_kernel := fourierKernel_neg_div_two_pi τ t
    -- rewrite the exponential kernel: fourierKernel(-τ/(2π)) t = exp(Iτt)
    simp only [LogPull, h_kernel]
    ring
  have h_integrand :
      ∀ t : ℝ,
        LogPull σ f t * Complex.exp (Complex.I * τ * t)
          * Complex.exp ((1 / 2 : ℝ) * t)
            = LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)
              * Complex.exp (Complex.I * τ * t) := by
    intro t; simp [mul_comm, mul_left_comm]
  -- identify the Mellin integrand with the Fourier kernel formulation
  have h_rewrite :
      (∫ t : ℝ,
          fourierKernel (-τ / (2 * Real.pi)) t
            * (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
        =
          ∫ t : ℝ,
            LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)
              * Complex.exp (Complex.I * τ * t) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro t; simpa using h_kernel t
  have h_mellin' :
      mellinTransform (f : ℝ → ℂ) (σ + I * τ)
        = ∫ t : ℝ,
            LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)
              * Complex.exp (Complex.I * τ * t) := by
    rw [h_mellin]
    congr 1
    ext t
    exact h_integrand t
  simp only [Frourio.fourierIntegral, h_mellin', ← h_rewrite]

lemma toFun_add_ae (σ : ℝ) (f g : Hσ σ) :
    (fun x : ℝ => Hσ.toFun (f + g) x) =ᵐ[
      mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
        fun x => Hσ.toFun f x + Hσ.toFun g x :=
  (Lp.coeFn_add (f := (f : Lp ℂ 2
    (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))))
    (g := (g : Lp ℂ 2
    (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))))

lemma toFun_smul_ae (σ : ℝ) (c : ℂ) (f : Hσ σ) :
    (fun x : ℝ => Hσ.toFun (c • f) x) =ᵐ[
      mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
        fun x => c * Hσ.toFun f x :=
  (Lp.coeFn_smul (c := (RingHom.id ℂ) c)
    (f := (f : Lp ℂ 2
      (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))))

lemma weightedMeasure_absolutelyContinuous_volume (σ : ℝ) :
    weightedMeasure σ ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
  classical
  -- First step: `weightedMeasure σ` is obtained from `mulHaar` via `withDensity`,
  -- hence it is absolutely continuous with respect to `mulHaar`.
  have h_weight_to_mulHaar :
      weightedMeasure σ ≪ mulHaar := by
    simpa [weightedMeasure] using
      (withDensity_absolutelyContinuous
        (μ := mulHaar) (f := weightFunction σ))
  -- The multiplicative Haar measure itself comes from Lebesgue measure via
  -- a density and a restriction to `(0, ∞)`, so it is absolutely continuous
  -- with respect to the restricted Lebesgue measure on `(0, ∞)`.
  have h_mulHaar_to_volume :
      mulHaar ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    -- Absolute continuity for `withDensity` followed by restriction.
    have h_base :
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)) ≪ volume := by
      simpa using
        (withDensity_absolutelyContinuous
          (μ := volume)
          (f := fun x : ℝ => ENNReal.ofReal (1 / x)))
    -- Restrict both measures to `(0, ∞)`.
    simpa [mulHaar] using h_base.restrict (Set.Ioi (0 : ℝ))
  exact h_weight_to_mulHaar.trans h_mulHaar_to_volume

lemma has_weighted_L2_norm_add (σ : ℝ) {f g : Hσ σ}
    (hf : has_weighted_L2_norm σ f) (hg : has_weighted_L2_norm σ g) :
    has_weighted_L2_norm σ (f + g) := by
  classical
  unfold has_weighted_L2_norm at hf hg ⊢
  have h_nonneg_weight : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ x ^ (2 * σ - 1) := by
    intro x hx
    exact Real.rpow_nonneg (le_of_lt hx) _
  -- Use the ae equality from toFun_add_ae
  have h_add_ae := toFun_add_ae σ f g
  -- Convert to ae inequality on (0, ∞)
  have h_pointwise_ae :
      ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ENNReal.ofReal
            (‖Hσ.toFun (f + g) x‖ ^ 2 * x ^ (2 * σ - 1))
          ≤
            ENNReal.ofReal
                (2 * ‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) +
              ENNReal.ofReal
                (2 * ‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1)) := by
    -- First relate the weighted measure to volume.restrict
    have h_ac := weightedMeasure_absolutelyContinuous_volume σ
    -- Transform h_add_ae to work with volume.restrict
    have h_add_ae' : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        Hσ.toFun (f + g) x = Hσ.toFun f x + Hσ.toFun g x := by
      -- We need to show the reverse absolute continuity
      -- volume.restrict (Ioi 0) ≪ mulHaar.withDensity (x ^ (2σ-1))
      -- This holds on (0,∞) because the density x^(2σ-1) * (1/x) is positive
      have h_reverse_ac : volume.restrict (Set.Ioi (0 : ℝ)) ≪
          mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
        sorry -- This requires showing the combined density is positive ae
      exact h_reverse_ac.ae_eq h_add_ae
    filter_upwards [h_add_ae'] with x hx
    have hx_in : x ∈ Set.Ioi (0 : ℝ) := by sorry
    have hx_weight_pos : 0 ≤ x ^ (2 * σ - 1) := by
      exact Real.rpow_nonneg (le_of_lt hx_in) _
    have h_triangle := norm_add_le (Hσ.toFun f x) (Hσ.toFun g x)
    have h_sq_triangle : ‖Hσ.toFun f x + Hσ.toFun g x‖^2
        ≤ (‖Hσ.toFun f x‖ + ‖Hσ.toFun g x‖)^2 := by
      have h_neg : -(‖Hσ.toFun f x‖ + ‖Hσ.toFun g x‖) ≤ ‖Hσ.toFun f x + Hσ.toFun g x‖ := by
        have : 0 ≤ ‖Hσ.toFun f x‖ + ‖Hσ.toFun g x‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
        linarith [norm_nonneg (Hσ.toFun f x + Hσ.toFun g x)]
      exact sq_le_sq' h_neg h_triangle
    have h_sq_bound :
        (‖Hσ.toFun f x‖ + ‖Hσ.toFun g x‖)^2
          ≤ 2 * ‖Hσ.toFun f x‖^2 + 2 * ‖Hσ.toFun g x‖^2 := by
      have h_expand :
          (‖Hσ.toFun f x‖ + ‖Hσ.toFun g x‖)^2
            = ‖Hσ.toFun f x‖^2 + ‖Hσ.toFun g x‖^2 +
                2 * (‖Hσ.toFun f x‖ * ‖Hσ.toFun g x‖) := by
        ring
      have h_mul : 2 * (‖Hσ.toFun f x‖ * ‖Hσ.toFun g x‖)
          ≤ ‖Hσ.toFun f x‖^2 + ‖Hσ.toFun g x‖^2 := by
        have := two_mul_le_add_sq (‖Hσ.toFun f x‖) (‖Hσ.toFun g x‖)
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      calc
        (‖Hσ.toFun f x‖ + ‖Hσ.toFun g x‖)^2
            = ‖Hσ.toFun f x‖^2 + ‖Hσ.toFun g x‖^2 +
                2 * (‖Hσ.toFun f x‖ * ‖Hσ.toFun g x‖) := h_expand
        _ ≤ ‖Hσ.toFun f x‖^2 + ‖Hσ.toFun g x‖^2 +
                (‖Hσ.toFun f x‖^2 + ‖Hσ.toFun g x‖^2) := by
              have h_le :
                  2 * (‖Hσ.toFun f x‖ * ‖Hσ.toFun g x‖)
                    ≤ ‖Hσ.toFun f x‖^2 + ‖Hσ.toFun g x‖^2 := h_mul
              exact add_le_add le_rfl h_le
        _ = 2 * ‖Hσ.toFun f x‖^2 + 2 * ‖Hσ.toFun g x‖^2 := by ring
    have h_sq_total :
        ‖Hσ.toFun (f + g) x‖^2
          ≤ 2 * ‖Hσ.toFun f x‖^2 + 2 * ‖Hσ.toFun g x‖^2 := by
      rw [hx]
      exact h_sq_triangle.trans h_sq_bound
    have h_mul_le :
        ‖Hσ.toFun (f + g) x‖^2 * x ^ (2 * σ - 1)
          ≤ (2 * ‖Hσ.toFun f x‖^2 + 2 * ‖Hσ.toFun g x‖^2) * x ^ (2 * σ - 1) := by
      have := mul_le_mul_of_nonneg_right h_sq_total hx_weight_pos
      simpa [mul_add, mul_left_comm, mul_comm, mul_assoc] using this
    have h_split :
        (2 * ‖Hσ.toFun f x‖^2 + 2 * ‖Hσ.toFun g x‖^2) * x ^ (2 * σ - 1)
          = 2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1) +
              2 * ‖Hσ.toFun g x‖^2 * x ^ (2 * σ - 1) := by
      ring
    have hx_total :=
      h_mul_le.trans_eq h_split
    have h_nonneg_a :
        0 ≤ ‖Hσ.toFun (f + g) x‖^2 * x ^ (2 * σ - 1) := by
      exact mul_nonneg (sq_nonneg _) hx_weight_pos
    have h_nonneg_b :
        0 ≤ 2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1) := by
      apply mul_nonneg
      apply mul_nonneg
      · norm_num
      · exact sq_nonneg _
      · exact hx_weight_pos
    have h_nonneg_c :
        0 ≤ 2 * ‖Hσ.toFun g x‖^2 * x ^ (2 * σ - 1) := by
      apply mul_nonneg
      apply mul_nonneg
      · norm_num
      · exact sq_nonneg _
      · exact hx_weight_pos
    have : ENNReal.ofReal (‖Hσ.toFun (f + g) x‖^2 * x ^ (2 * σ - 1))
        ≤ ENNReal.ofReal (2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1) +
                          2 * ‖Hσ.toFun g x‖^2 * x ^ (2 * σ - 1)) := by
      rw [ENNReal.ofReal_le_ofReal_iff (add_nonneg h_nonneg_b h_nonneg_c)]
      exact hx_total
    calc ENNReal.ofReal (‖Hσ.toFun (f + g) x‖^2 * x ^ (2 * σ - 1))
        ≤ ENNReal.ofReal (2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1) +
                          2 * ‖Hσ.toFun g x‖^2 * x ^ (2 * σ - 1)) := this
      _ = ENNReal.ofReal (2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) +
          ENNReal.ofReal (2 * ‖Hσ.toFun g x‖^2 * x ^ (2 * σ - 1)) := by
          rw [ENNReal.ofReal_add h_nonneg_b h_nonneg_c]
  have h_lintegral_le :
      (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun (f + g) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume)
        ≤
          (∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (2 * ‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) +
            (∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (2 * ‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) := by
    calc ∫⁻ x in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (‖Hσ.toFun (f + g) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume
        ≤ ∫⁻ x in Set.Ioi (0 : ℝ),
            (ENNReal.ofReal (2 * ‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) +
             ENNReal.ofReal (2 * ‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1))) ∂volume := by
          apply lintegral_mono_ae
          exact h_pointwise_ae
      _ = (∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (2 * ‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) +
            (∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (2 * ‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) := by
          rw [lintegral_add_right]
          sorry -- measurability
  have h_fin_f :
      (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) < ∞ := hf
  have h_fin_g :
      (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) < ∞ := hg
  have h_scaled_f :
      ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (2 * ‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume
        < ∞ := by
    have h_eq : ∀ x, ENNReal.ofReal (2 * ‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1))
        = 2 * ENNReal.ofReal (‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) := by
      intro x
      rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    simp_rw [h_eq]
    rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    exact ENNReal.mul_lt_top (by norm_num) h_fin_f
  have h_scaled_g :
      ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (2 * ‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume
        < ∞ := by
    have h_eq : ∀ x, ENNReal.ofReal (2 * ‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1))
        = 2 * ENNReal.ofReal (‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1)) := by
      intro x
      rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    simp_rw [h_eq]
    rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    exact ENNReal.mul_lt_top (by norm_num) h_fin_g
  calc ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun (f + g) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume
      ≤ (∫⁻ x in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (2 * ‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) +
          (∫⁻ x in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (2 * ‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) :=
        h_lintegral_le
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨h_scaled_f, h_scaled_g⟩

lemma has_weighted_L2_norm_smul (σ : ℝ) (c : ℂ) {f : Hσ σ}
    (hf : has_weighted_L2_norm σ f) :
    has_weighted_L2_norm σ (c • f) := by
  classical
  unfold has_weighted_L2_norm at hf ⊢
  have h_nonneg_weight : ∀ x : ℝ, 0 ≤ x ^ (2 * σ - 1) := by
    intro x
    by_cases hx : 0 ≤ x
    · exact Real.rpow_nonneg hx _
    · rw [Real.rpow_def_of_neg (not_le.mp hx)]
      apply mul_nonneg
      · exact le_of_lt (Real.exp_pos _)
      · sorry
  have h_lintegral :
      (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal
            (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume)
        = (ENNReal.ofReal (‖c‖^2)) *
          (∫⁻ x in Set.Ioi (0 : ℝ),
            ENNReal.ofReal
              (‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) := by
    have h_pointwise :
        ∀ x ∈ Set.Ioi (0 : ℝ),
          ENNReal.ofReal
              (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1))
            = ENNReal.ofReal (‖c‖^2) *
                ENNReal.ofReal
                  (‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) := by
      intro x hx
      have hx_pos : 0 < x := hx
      have h_mul :
          ‖Hσ.toFun (c • f) x‖ = ‖c‖ * ‖Hσ.toFun f x‖ := by
        have h_smul_ae := toFun_smul_ae σ c f
        have h_smul : Hσ.toFun (c • f) x = c * Hσ.toFun f x := by
          sorry -- need to extract from ae equality
        rw [h_smul, norm_mul]
      have h_pow :
          ‖Hσ.toFun (c • f) x‖ ^ 2 = ‖c‖^2 * ‖Hσ.toFun f x‖^2 := by
        simp [pow_two, h_mul, mul_comm, mul_left_comm, mul_assoc]
      have hx_nonneg : 0 ≤ x ^ (2 * σ - 1) := h_nonneg_weight x
      have hx' :
          ‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)
            = ‖c‖^2 * (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) := by
        ring
      have :
          ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1))
            = ENNReal.ofReal (‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) := by
        simp [h_pow]
      have h_nonneg :
          0 ≤ ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1) :=
        mul_nonneg (sq_nonneg _) (h_nonneg_weight x)
      calc
        ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1))
            = ENNReal.ofReal (‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) := by
          simp [h_pow]
        _ = ENNReal.ofReal (‖c‖^2 * (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1))) := by
          simp [hx']
        _ = ENNReal.ofReal (‖c‖^2) * ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
    have h_integrand_measurable :
        AEStronglyMeasurable
          (fun x : ℝ =>
            ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)))
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
      sorry
    have h_integrand' : AEStronglyMeasurable
        (fun x : ℝ => ENNReal.ofReal
          (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      sorry
    have h_eq : ∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume
      = ∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (‖c‖^2) * ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact h_pointwise x hx
    calc
      ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume
        = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖c‖^2) * ENNReal.ofReal
            (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := h_eq
      _ = ENNReal.ofReal (‖c‖^2) * ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := by
        rw [lintegral_const_mul' _ _ (by norm_num : ENNReal.ofReal (‖c‖^2) ≠ ∞)]
  sorry

lemma has_weighted_L2_norm_sub (σ : ℝ) {f g : Hσ σ}
    (hf : has_weighted_L2_norm σ f) (hg : has_weighted_L2_norm σ g) :
    has_weighted_L2_norm σ (f - g) := by
  classical
  simpa [sub_eq_add_neg]
    using has_weighted_L2_norm_add σ hf (has_weighted_L2_norm_smul σ (-1 : ℂ) hg)

lemma logpull_mellin_l2_relation (σ : ℝ) (f : Hσ σ)
    (h_weighted_L2 : MemLp (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) 2 volume)
    (h_integrable : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))) :
    ∫ t : ℝ, ‖LogPull σ f t‖^2 * Real.exp t ∂volume =
    (1 / (2 * Real.pi))^2 * ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖^2 ∂volume := by
  classical
  -- Define the weighted function g(t) := LogPull σ f t * exp((1/2) * t)
  set g : ℝ → ℂ := fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t) with hg_def

  -- We have both L¹ and L² assumptions for g
  have hg_L1 : Integrable g := h_integrable
  have hg_L2 : MemLp g 2 volume := h_weighted_L2

  -- Apply Fourier-Plancherel for L¹ ∩ L² functions
  -- This gives: ∫ ‖g‖² = (1/(2π)) * ∫ ‖fourierIntegral g ξ‖² dξ
  have h_plancherel := fourier_plancherel_L1_L2 g hg_L1 hg_L2

  -- The key relationship: mellinTransform f (σ + I * τ) = fourierIntegral g (-τ/(2π))
  have h_mellin_eq_fourier : ∀ τ : ℝ,
      mellinTransform (f : ℝ → ℂ) (σ + I * τ) = fourierIntegral g (-τ / (2 * Real.pi)) := by
    intro τ
    simp only [hg_def, g]
    exact mellin_logpull_fourierIntegral σ τ f

  -- Change of variables on the Fourier side so that the Mellin transform appears
  have h_change_of_var :
      ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume
        = (1 / (2 * Real.pi)) *
            ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
    classical
    have h_rescale := integral_fourierIntegral_rescale_sq g
    simp [fourierIntegral_eq_real] at h_rescale
    have hpi : (2 * Real.pi) ≠ 0 := by
      have : (2 : ℝ) ≠ 0 := by norm_num
      exact mul_ne_zero this Real.pi_ne_zero
    set A :=
        ∫ τ : ℝ, ‖fourierIntegral g (-τ / (2 * Real.pi))‖ ^ 2 ∂volume
      with hA
    set B := ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume with hB
    have h_rescaleAB : A = (2 * Real.pi) * B := by
      simpa [A, B, hA, hB] using h_rescale
    have h_eq_fun :
        (fun τ : ℝ => ‖fourierIntegral g (-τ / (2 * Real.pi))‖ ^ 2) =
          fun τ : ℝ =>
            ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 := by
      funext τ
      simp [sq, h_mellin_eq_fourier τ]
    have hA_mellin :
        A = ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
      simp [A, hA, h_eq_fun]
    have h_rescale_mellin :
        ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume
          = (2 * Real.pi) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume := by
      simpa [A, B, hA, hB, hA_mellin] using h_rescaleAB
    have h_rescale_mellin' :
        (2 * Real.pi) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume
          = ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume :=
      h_rescale_mellin.symm
    have hpi' : (2 * Real.pi) ≠ 0 := by
      have : (2 : ℝ) ≠ 0 := by norm_num
      exact mul_ne_zero this Real.pi_ne_zero
    have h_target :
        (2 * Real.pi) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume =
          (2 * Real.pi) *
            ((1 / (2 * Real.pi)) * ∫ τ : ℝ,
                ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume) := by
      calc
        (2 * Real.pi) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume
            = ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume :=
              h_rescale_mellin'
        _ = (2 * Real.pi) *
              ((1 / (2 * Real.pi)) * ∫ τ : ℝ,
                  ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume) := by
              simp [mul_comm, mul_left_comm, mul_assoc, one_div, Real.pi_ne_zero]
    exact mul_left_cancel₀ hpi' h_target

  -- Rewrite the LHS to match ∫ ‖g‖²
  have h_lhs_eq : ∫ t : ℝ, ‖LogPull σ f t‖^2 * Real.exp t ∂volume
      = ∫ t : ℝ, ‖g t‖^2 ∂volume := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    -- ‖g t‖² = ‖LogPull σ f t * exp((1/2) * t)‖²
    --        = ‖LogPull σ f t‖² * |exp((1/2) * t)|²
    --        = ‖LogPull σ f t‖² * exp(t)
    -- compare the integrands pointwise
    set a : ℂ := LogPull σ f t with ha
    set b : ℂ := Complex.exp ((1 / 2 : ℝ) * t) with hb
    have h_g : g t = a * b := by
      simp [hg_def, g, ha, hb]
    -- compute the norm of `b`
    have h_norm_b : ‖b‖ ^ 2 = Real.exp t := by
      have h_norm : ‖b‖ = Real.exp ((1 / 2 : ℝ) * t) := by
        simpa [hb] using Complex.norm_exp ((1 / 2 : ℂ) * (t : ℂ))
      have h_half : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
      have h_sum := (add_mul (1 / 2 : ℝ) (1 / 2 : ℝ) t).symm
      have h_temp : ((1 / 2 : ℝ) + (1 / 2 : ℝ)) * t = t := by
        have := congrArg (fun x : ℝ => x * t) h_half
        simpa using this
      have h_add : (1 / 2 : ℝ) * t + (1 / 2 : ℝ) * t = t := h_sum.trans h_temp
      calc
        ‖b‖ ^ 2
            = Real.exp ((1 / 2 : ℝ) * t) ^ 2 := by simp [h_norm]
        _ = Real.exp ((1 / 2 : ℝ) * t) * Real.exp ((1 / 2 : ℝ) * t) := by
              simp [pow_two]
        _ = Real.exp (((1 / 2 : ℝ) * t) + ((1 / 2 : ℝ) * t)) := by
              simpa using
                (Real.exp_add ((1 / 2 : ℝ) * t) ((1 / 2 : ℝ) * t)).symm
        _ = Real.exp t := by
              simpa using congrArg Real.exp h_add
    -- obtain the desired identity
    have h_eq : ‖a‖ ^ 2 * Real.exp t = ‖a * b‖ ^ 2 := by
      calc
        ‖a‖ ^ 2 * Real.exp t
            = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by simp [h_norm_b]
        _ = (‖a‖ * ‖b‖) ^ 2 := by
              simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
        _ = ‖a * b‖ ^ 2 := by
              simp [pow_two, norm_mul, mul_comm, mul_left_comm, mul_assoc]
    -- rewrite back in terms of `LogPull` and `g`
    simpa [ha, hb, h_g] using h_eq

  -- Combine using Plancherel and change of variables
  calc ∫ t : ℝ, ‖LogPull σ f t‖^2 * Real.exp t ∂volume
      = ∫ t : ℝ, ‖g t‖^2 ∂volume := h_lhs_eq
    _ = (1 / (2 * Real.pi)) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖^2 ∂volume := h_plancherel
    _ = (1 / (2 * Real.pi)) * ((1 / (2 * Real.pi)) * ∫ τ : ℝ,
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖^2 ∂volume) := by
        have := congrArg (fun x => (1 / (2 * Real.pi)) * x) h_change_of_var
        simpa [mul_left_comm, mul_assoc] using this
    _ = (1 / (2 * Real.pi))^2 * ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ)
          (σ + I * τ)‖^2 ∂volume := by
        simp [pow_two, mul_left_comm, mul_assoc]

/-- The Plancherel constant for our normalization is 1 -/
lemma plancherel_constant_is_one (σ : ℝ) (f : Hσ σ) :
    ∃ (C : ℝ), C > 0 ∧ ∫ τ : ℝ, ‖LogPull σ f τ‖^2 = C * ‖f‖^2 ∧ C = 1 := by
  classical
  refine ⟨1, by norm_num, ?_, rfl⟩
  -- We establish the norm identity directly from the structural lemmas
  -- developed in `MellinPlancherel.lean`.
  set g : ℝ → ℂ := LogPull σ f with hg

  have hMem : MemLp g 2 (volume : Measure ℝ) := by
    simpa [g, hg] using mellin_in_L2 σ f

  have hInt_sq : Integrable (fun τ : ℝ => ‖g τ‖ ^ 2) (volume : Measure ℝ) := by
    have := (memLp_two_iff_integrable_sq_norm hMem.1).1 hMem
    simpa [g, hg, pow_two] using this

  have hNonneg : 0 ≤ᵐ[volume] fun τ : ℝ => ‖g τ‖ ^ 2 :=
    Filter.Eventually.of_forall fun τ => sq_nonneg _

  have hOfReal :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt_sq hNonneg

  have hIntegral_nonneg :
      0 ≤ ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ) :=
    integral_nonneg fun τ => sq_nonneg _

  have hIntegral_eq :
      ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ)
        = (∫⁻ τ, ENNReal.ofReal (‖g τ‖ ^ 2)
            ∂(volume : Measure ℝ)).toReal := by
    have := congrArg ENNReal.toReal hOfReal
    simpa [hIntegral_nonneg, ENNReal.toReal_ofReal] using this

  set I : ℝ≥0∞ := ∫⁻ τ, (‖g τ‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure ℝ)
    with hI

  have hI_ofReal :
      (∫⁻ τ, ENNReal.ofReal (‖g τ‖ ^ 2) ∂(volume : Measure ℝ)) = I := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro τ
    have hnn : 0 ≤ ‖g τ‖ := norm_nonneg _
    simp [pow_two, ENNReal.ofReal_mul, g, hg, hnn]

  set J : ℝ≥0∞ := ∫⁻ x in Set.Ioi (0 : ℝ),
      (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) *
        ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume with hJ

  have hI_eq_J : I = J := by
    have := logPull_sq_integral_eq (σ := σ) (f := f)
    simpa [I, J, g, hg, LogPull]

  have hJ_toReal : J.toReal = ‖f‖ ^ 2 := by
    simpa [J] using (LogPull_isometry (σ := σ) (f := f)).symm

  have hI_toReal : I.toReal = ‖f‖ ^ 2 := by
    have := congrArg ENNReal.toReal hI_eq_J
    exact this.trans hJ_toReal

  have hIntegral_I :
      ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ) = I.toReal := by
    simpa [hI_ofReal] using hIntegral_eq

  have hFinal : ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ) = ‖f‖ ^ 2 :=
    hIntegral_I.trans hI_toReal

  simpa [g, hg, LogPull, one_mul] using hFinal

/-- Uniqueness of the Plancherel constant -/
lemma plancherel_constant_unique (σ : ℝ) (f : Hσ σ) (C₁ C₂ : ℝ)
    (hf : ‖f‖ ≠ 0)
    (h₁_eq : ∫ τ : ℝ, ‖LogPull σ f τ‖ ^ 2 = C₁ * ‖f‖ ^ 2)
    (h₂_eq : ∫ τ : ℝ, ‖LogPull σ f τ‖ ^ 2 = C₂ * ‖f‖ ^ 2) :
    C₁ = C₂ := by
  have h_equal : C₁ * ‖f‖ ^ 2 = C₂ * ‖f‖ ^ 2 := by
    rw [← h₁_eq, h₂_eq]
  have hf_sq : ‖f‖ ^ 2 ≠ 0 := pow_ne_zero 2 hf
  exact mul_right_cancel₀ hf_sq h_equal

/-- Explicit Mellin-Parseval formula (with necessary L² condition)
This relates the Hσ norm to the L² norm of the Mellin transform on vertical lines.
NOTE: The correct formulation requires relating weighted norms properly.

IMPORTANT: This theorem requires additional integrability condition for the weighted LogPull
function to apply the Fourier-Plancherel theorem. This aligns with plan.md Phase 1 goals. -/
theorem mellin_parseval_formula (σ : ℝ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (f : Hσ σ),
    -- Additional conditions for Fourier-Plancherel applicability:
    -- 1. The weighted norm must be finite (L² condition)
    ((∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2 * x^(2*σ - 1)) ∂volume) < ⊤) →
    -- 2. The weighted LogPull must be integrable (for Fourier transform)
    (Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))) →
    ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2 * x^(2*σ - 1)) ∂volume =
    ENNReal.ofReal (C * ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume) := by
  -- We need to establish this directly from the Plancherel formula in MellinPlancherel.lean
  -- The key is relating LogPull to mellinTransform

  -- From MellinPlancherel.lean, we have:
  -- ∃ C > 0, ∫ τ : ℝ, ‖LogPull σ f τ‖^2 ∂volume = C * ‖f‖^2
  -- where LogPull σ f t = e^((σ - 1/2) * t) * f(e^t)

  -- The Mellin transform at σ + iτ after change of variables x = e^t is:
  -- ∫ t : ℝ, f(e^t) * e^((σ + iτ) * t) dt

  -- The relationship between these requires careful analysis of the weights
  -- For now, we claim existence of such a constant

  use (1 / (2 * Real.pi))^2  -- This is the standard normalization

  constructor
  · -- Show (1/(2π))^2 > 0
    have hpos : 0 < (1 / (2 * Real.pi)) := by
      have hden : 0 < 2 * Real.pi := mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos
      exact one_div_pos.mpr hden
    have : 0 < (1 / (2 * Real.pi)) * (1 / (2 * Real.pi)) := mul_pos hpos hpos
    simpa [pow_two] using this

  · -- For all f with the additional conditions, the formula holds
    intro f h_extra h_integrable

    -- The proof strategy:
    -- 1. Use weighted_LogPull_integral_eq to relate the weighted L² norm of f to LogPull
    -- 2. Apply logpull_mellin_l2_relation to connect LogPull L² to Mellin transform L²
    -- 3. Chain these equalities together

    -- Step 1: Apply weighted_LogPull_integral_eq
    -- This gives us the relationship between the weighted L² norm of f and LogPull
    have h_weighted_eq := weighted_LogPull_integral_eq σ f

    -- Step 2: Convert the finiteness condition to show the weighted LogPull is in L²
    have h_finite : (∫⁻ t, ENNReal.ofReal
        (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2) ∂volume) < ⊤ := by
      rw [h_weighted_eq]
      exact h_extra

    -- Step 3: Convert to MemLp condition for logpull_mellin_l2_relation
    have h_memLp : MemLp (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) 2 volume := by
      -- This requires showing that the finiteness of the lintegral implies MemLp
      -- MemLp is defined as AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞
      constructor
      · -- AEStronglyMeasurable
        apply AEStronglyMeasurable.mul
        · -- LogPull is measurable
          exact (LogPull_measurable σ f).aestronglyMeasurable
        · -- Complex exponential is continuous hence measurable
          apply Continuous.aestronglyMeasurable
          apply Continuous.cexp
          apply Continuous.mul
          · apply continuous_const
          · exact continuous_ofReal.comp continuous_id
      · -- eLpNorm < ∞
        -- We use the fact that the L² norm is finite, which follows from h_finite
        -- For p = 2, eLpNorm f 2 μ = (∫⁻ ‖f‖^2)^(1/2)
        -- We need to show this is finite
        have hp_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
        have hp_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
        rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
        simp only [ENNReal.toReal_ofNat]

        -- The key insight: (∫⁻ ‖f‖^2)^(1/2) < ⊤ iff ∫⁻ ‖f‖^2 < ⊤
        -- Since 1/2 > 0, we can use rpow_lt_top_iff_of_pos
        have h_pos : (0 : ℝ) < 1 / 2 := by norm_num
        rw [ENNReal.rpow_lt_top_iff_of_pos h_pos]

        -- Show the integral is finite
        -- The goal is ∫⁻ ‖LogPull σ f x * exp(...)‖ₑ ^ 2 < ⊤
        -- We know ∫⁻ ENNReal.ofReal (‖LogPull σ f t * exp(...)‖ ^ 2) < ⊤ from h_finite
        -- The key insight is that these integrals are equal for non-negative functions

        -- Use the fact that h_finite gives us finiteness already
        -- The technical equality between ‖z‖ₑ^2 and ENNReal.ofReal (‖z‖^2) for complex z
        -- follows from the definition of ENorm, but requires careful handling
        convert h_finite using 1
        -- We need to show that ∫⁻ ‖f‖ₑ^2 = ∫⁻ ENNReal.ofReal(‖f‖^2)
        -- For complex numbers, this follows from the fundamental property:
        -- ‖z‖ₑ = ENNReal.ofReal(‖z‖) for normed spaces
        congr 1
        funext t
        -- Show ‖z‖ₑ^2 = ENNReal.ofReal(‖z‖^2) pointwise
        have h_eq : (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖ₑ : ℝ≥0∞) ^ (2 : ℝ) =
          ENNReal.ofReal (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖ ^ 2) := by
          -- Use ofReal_norm_eq_enorm: ENNReal.ofReal ‖a‖ = ‖a‖ₑ
          rw [← ofReal_norm_eq_enorm]
          -- Apply ENNReal.ofReal_rpow_of_nonneg
          rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
          -- Convert Real power to Natural power
          congr 1
          exact Real.rpow_natCast _ 2
        exact h_eq

    -- Step 4: Apply logpull_mellin_l2_relation with the integrability hypothesis
    have h_parseval := logpull_mellin_l2_relation σ f h_memLp h_integrable

    -- Step 5: Connect the weighted integrals
    -- We need to show that the left-hand side equals the right-hand side

    -- First, rewrite using weighted_LogPull_integral_eq
    rw [←h_weighted_eq]

    -- Now we need to connect the ENNReal integral with the Real integral from h_parseval
    -- Since h_finite shows the integral is finite, we can convert between ENNReal and Real

    -- The relationship is:
    -- ∫⁻ (ENNReal.ofReal ...) = ENNReal.ofReal (∫ ...)  when the integral is finite

    have h_ennreal_eq : ∫⁻ t, ENNReal.ofReal
        (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2) ∂volume =
        ENNReal.ofReal (∫ t : ℝ, ‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2 ∂volume) := by
      -- This follows from the finiteness and non-negativity of the integrand
      -- Since we have h_memLp showing the function is in L², we know the integral is finite
      -- and we can convert between ENNReal and Real representations

      -- The key is that for non-negative functions with finite integral,
      -- lintegral of ofReal equals ofReal of integral
      -- Use MeasureTheory.integral_eq_lintegral_of_nonneg_ae

      -- First establish non-negativity
      have h_nonneg : ∀ t, 0 ≤ ‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2 := by
        intro t
        exact sq_nonneg _

      -- Apply the conversion theorem for non-negative integrable functions
      -- For non-negative measurable functions with finite integral:
      -- ∫⁻ ENNReal.ofReal f = ENNReal.ofReal (∫ f)

      -- We need to show the function is integrable
      have h_integrable : Integrable (fun t =>
          ‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^(2 : ℕ)) := by
        -- This follows from h_memLp: if f ∈ L², then ‖f‖² is integrable
        -- Since h_memLp shows the function is in L², we can use MemLp.integrable_norm_rpow
        have : MemLp (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) 2 volume := h_memLp
        have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
        have h_int := MemLp.integrable_norm_rpow this two_ne_zero h_two_ne_top
        -- h_int gives integrability for ‖f‖^(toReal 2), but toReal 2 = 2
        simp only [ENNReal.toReal_ofNat] at h_int
        -- Convert from real exponent to natural exponent using the fact that x^(2:ℝ) = x^(2:ℕ)
        convert h_int using 1
        ext t
        simp

      -- Now apply the equality
      symm
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall h_nonneg) h_integrable.aestronglyMeasurable]
      -- Use ENNReal.ofReal_toReal for finite values
      rw [ENNReal.ofReal_toReal]
      exact LT.lt.ne h_finite

    rw [h_ennreal_eq]

    -- Apply norm_simplification_logpull
    rw [norm_simplification_logpull σ f]

    -- Apply the Parseval relation
    rw [h_parseval]

/-- Polarization identity for Mellin transforms -/
lemma mellin_polarization_pointwise (F G : ℂ) :
    ‖F + G‖ ^ 2 - ‖F - G‖ ^ 2 - Complex.I * ‖F + Complex.I * G‖ ^ 2 +
      Complex.I * ‖F - Complex.I * G‖ ^ 2 = 4 * (starRingEnd ℂ F * G) := by
  classical
  -- Specialise the abstract polarization identity to `ℂ` and rearrange.
  have h :=
    (complex_polarization_identity (E := ℂ) (f := F) (g := G)).symm
  have h' :
      ‖F + G‖ ^ 2 - ‖F - G‖ ^ 2 - Complex.I * ‖F + Complex.I * G‖ ^ 2 +
          Complex.I * ‖F - Complex.I * G‖ ^ 2 =
        4 * @inner ℂ ℂ _ F G := by
    simpa [smul_eq_mul] using h
  calc
    ‖F + G‖ ^ 2 - ‖F - G‖ ^ 2 - Complex.I * ‖F + Complex.I * G‖ ^ 2 +
        Complex.I * ‖F - Complex.I * G‖ ^ 2
        = 4 * @inner ℂ ℂ _ F G := h'
    _ = 4 * (starRingEnd ℂ F * G) := by
      simp [mul_comm]

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
        4 * (starRingEnd ℂ F * G) := fun τ => mellin_polarization_pointwise _ _

    -- Step 4: Combine everything
    -- We need to show: inner f g = (1/2π) * ∫ τ, conj(M_f(τ)) * M_g(τ)
    -- where M_f(τ) = mellinTransform f (σ + iτ)

    -- From the polarization identities and the norm formulas above,
    -- we can derive the desired identity
    -- We need to show: inner f g = C * ∫ τ, conj(M_f(τ)) * M_g(τ)

    calc @inner ℂ _ _ f g = (1/4) * (4 * @inner ℂ _ _ f g) := by ring
      _ = (1/4) * (((‖f + g‖ ^ 2 : ℝ) : ℂ) - ((‖f - g‖ ^ 2 : ℝ) : ℂ) -
            Complex.I * ((‖f + Complex.I • g‖ ^ 2 : ℝ) : ℂ) +
            Complex.I * ((‖f - Complex.I • g‖ ^ 2 : ℝ) : ℂ)) := by
          rw [h_polarization]
      _ = (1/4) * C * (∫ τ : ℝ, (‖mellinTransform ((f + g) : ℝ → ℂ) (σ + I * τ)‖ ^ 2 -
            ‖mellinTransform ((f - g) : ℝ → ℂ) (σ + I * τ)‖ ^ 2 -
            Complex.I * ‖mellinTransform ((f + Complex.I • g) : ℝ → ℂ) (σ + I * τ)‖ ^ 2 +
            Complex.I * ‖mellinTransform ((f - Complex.I • g) : ℝ → ℂ) (σ + I * τ)‖ ^ 2)) := by
          -- Apply the norm formulas from hC_formula
          -- We need L² conditions for the combined functions
          have hfpg_L2 : has_weighted_L2_norm σ (f + g) :=
            has_weighted_L2_norm_add σ hf_L2 hg_L2
          have hfmg_L2 : has_weighted_L2_norm σ (f - g) :=
            has_weighted_L2_norm_sub σ hf_L2 hg_L2
          have hfig_L2 : has_weighted_L2_norm σ (f + Complex.I • g) :=
            has_weighted_L2_norm_add σ hf_L2
              (has_weighted_L2_norm_smul σ Complex.I hg_L2)
          have hfmig_L2 : has_weighted_L2_norm σ (f - Complex.I • g) := by
            simpa [sub_eq_add_neg]
              using has_weighted_L2_norm_add σ hf_L2
                (has_weighted_L2_norm_smul σ (-Complex.I) hg_L2)

          -- Apply hC_formula to each combined function
          have eq1 := hC_formula (f + g) hfpg_L2
          have eq2 := hC_formula (f - g) hfmg_L2
          have eq3 := hC_formula (f + Complex.I • g) hfig_L2
          have eq4 := hC_formula (f - Complex.I • g) hfmig_L2

          -- The equations give us the norms in terms of integrals
          -- We need to substitute these into our expression
          sorry
      _ = C * ∫ τ : ℝ, starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
            mellinTransform (g : ℝ → ℂ) (σ + I * τ) := by
          -- Apply h_mellin_polarization pointwise
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
