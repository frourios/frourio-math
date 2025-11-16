import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore0
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
            * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂(volume : Measure ℝ) := by
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
        fun t => g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h_logpull := LogPull_integrand_eq (σ := σ) (f := f) t
    have h_exp :
        ENNReal.ofReal (Real.exp ((2 * σ) * t))
          = ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) := by
      have : (2 * σ) * t = (2 * σ - 1) * t + t := by ring
      simp [this]
    calc
      (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
          = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
              * ENNReal.ofReal (Real.exp ((2 * σ) * t)) := h_logpull
      _ = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
              * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) := by
                simp [h_exp]
      _ = g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) := by
                simp [g]
  have h_lhs :
      ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) ∂volume :=
    lintegral_congr_ae h_pointwise
  have h_change_restrict :=
      lintegral_change_of_variables_exp (α := 2 * σ - 1) (f := g) hg_meas
  have h_rhs_restrict :
      ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1))
            ∂(volume.restrict (Set.Ioi 0))
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 1))
            ∂(volume.restrict (Set.Ioi 0)) := by
    refine lintegral_congr_ae ?_
    refine ((ae_restrict_iff' measurableSet_Ioi).2 ?_)
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hxpos : 0 < x := hx
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
      g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1))
          = ENNReal.ofReal (‖Hσ.toFun f x‖^2)
              * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
                simp [h_g]
      _ = (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
                simp [h_norm_sq]
  have h_change :
      ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) ∂volume := by
    simpa using h_change_restrict
  have h_rhs :
      ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume := by
    simpa using h_rhs_restrict
  calc
    ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) ∂volume := h_lhs
    _ = ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) *
        ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume := h_change.symm
    _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
            * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume := h_rhs

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

/-- Connection between LogPull L² norm and Mellin transform L² norm
This states the Parseval-type equality for the Mellin transform.
Note: The actual proof requires implementing the Fourier-Plancherel theorem
for the specific weighted LogPull function. -/
lemma mellin_logpull_fourierIntegral (σ τ : ℝ) (f : Hσ σ) :
    mellinTransform (f : ℝ → ℂ) (σ + I * τ)
    = fourierIntegral (fun t : ℝ => LogPull σ f t) (-τ / (2 * Real.pi)) := by
  -- Start from the change-of-variables relation expressing Mellin via LogPull
  have h := mellin_logpull_relation (σ := σ) (f := f) (τ := τ)
  -- Algebraic identity to match the Fourier kernel: (-2π) * (-(τ)/(2π)) = τ
  have h₂π_ne : (2 * Real.pi) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  have h_real : (-2 * Real.pi) * (-τ / (2 * Real.pi)) = τ := by
    calc
      (-2 * Real.pi) * (-τ / (2 * Real.pi))
          = ((-2 * Real.pi) * (-τ)) / (2 * Real.pi) := by
              rw [mul_div_assoc]
      _ = ((2 * Real.pi) * τ) / (2 * Real.pi) := by
              ring
      _ = (τ * (2 * Real.pi)) / (2 * Real.pi) := by
              ring
      _ = τ := by
              rw [mul_div_cancel_right₀ τ h₂π_ne]
  -- Rewrite the exponential to the Fourier kernel with ξ = -τ/(2π)
  have h_kernel :
      (fun t : ℝ => Complex.exp (I * τ * t))
        = (fun t : ℝ =>
            Complex.exp (-2 * Real.pi * I * (-τ / (2 * Real.pi)) * t)) := by
    funext t
    -- Show equality of exponents and then apply congrArg Complex.exp
    have :
        ((-2 * Real.pi : ℝ) : ℂ) * I * ((-τ / (2 * Real.pi) : ℝ) : ℂ) * (t : ℂ)
          = I * (τ : ℂ) * (t : ℂ) := by
      -- Commute real scalars and use the real identity h_real
      have h_cast :
          (((-2 * Real.pi : ℝ) * (-τ / (2 * Real.pi) : ℝ)) : ℂ) = (τ : ℂ) := by
        exact_mod_cast h_real
      calc
        ((-2 * Real.pi : ℝ) : ℂ) * I * ((-τ / (2 * Real.pi) : ℝ) : ℂ) * (t : ℂ)
            = I * (((-2 * Real.pi : ℝ) : ℂ) * ((-τ / (2 * Real.pi) : ℝ) : ℂ)) * (t : ℂ) := by
                ring
        _ = I * (τ : ℂ) * (t : ℂ) := by
                rw [h_cast]
    have h_exp : Complex.exp (-2 * Real.pi * I * (-τ / (2 * Real.pi)) * t)
        = Complex.exp (I * τ * t) := by
      congr 1
      calc -2 * Real.pi * I * (-τ / (2 * Real.pi)) * t
          = ((-2 * Real.pi : ℝ) : ℂ) * I * ((-τ / (2 * Real.pi) : ℝ) : ℂ) * (t : ℂ) := by
              push_cast; ring
        _ = I * (τ : ℂ) * (t : ℂ) := this
        _ = I * τ * t := by rfl
    rw [h_exp]
  -- Rewrite h using h_kernel to express exp(I*τ*t) in terms of fourierKernel
  calc mellinTransform (f : ℝ → ℂ) (σ + I * τ)
      = ∫ t : ℝ, LogPull σ f t * Complex.exp (I * τ * t) := h
    _ = ∫ t : ℝ, LogPull σ f t * Complex.exp (-2 * Real.pi * I * (-τ / (2 * Real.pi)) * t) := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro t
        simp only []
        congr 1
        exact congrFun h_kernel t
    _ = fourierIntegral (fun t : ℝ => LogPull σ f t) (-τ / (2 * Real.pi)) := by
        rw [fourierIntegral]
        congr 1
        ext t
        simp only [fourierKernel]
        push_cast
        ring_nf

lemma toFun_add_ae (σ : ℝ) (f g : Hσ σ) :
    (fun x : ℝ => Hσ.toFun (f + g) x) =ᵐ[
      (volume.restrict (Set.Ioi 0)).withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
        fun x => Hσ.toFun f x + Hσ.toFun g x := by
  have : (f + g : Hσ σ) = (f : Hσ σ) + (g : Hσ σ) := rfl
  simp only [Hσ.toFun, this]
  exact Lp.coeFn_add f g

lemma toFun_smul_ae (σ : ℝ) (c : ℂ) (f : Hσ σ) :
    (fun x : ℝ => Hσ.toFun (c • f) x) =ᵐ[
      (volume.restrict (Set.Ioi 0)).withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
        fun x => c * Hσ.toFun f x := by
  have : (c • f : Hσ σ) = c • (f : Hσ σ) := rfl
  simp only [Hσ.toFun, this]
  exact Lp.coeFn_smul c f

lemma weightedMeasure_absolutelyContinuous_volume (σ : ℝ) :
    weightedMeasure σ ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
  classical
  -- Direct from `withDensity_absolutelyContinuous` on the base restricted measure
  simpa [weightedMeasure]
    using withDensity_absolutelyContinuous
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := weightFunction σ)

/-!
Auxiliary absolute continuity in the reverse direction.
This is used to transport a.e. equalities from the weighted measure back to
`volume.restrict (Ioi 0)` when rewriting integrands.
-/
lemma volume_restrict_absolutelyContinuous_weighted (σ : ℝ) :
    volume.restrict (Set.Ioi (0 : ℝ)) ≪
      mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
  classical
  -- Unfold `mulHaar` and introduce shorthand measures.
  have hμ : mulHaar
      = (volume.withDensity (fun x : ℝ => ENNReal.ofReal (1 / x))).restrict (Set.Ioi 0) := by
    simp [mulHaar]
  -- Base and intermediate measures
  set μ0 : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ0
  set ν : Measure ℝ :=
    ((volume.withDensity (fun x : ℝ => ENNReal.ofReal (1 / x))).restrict (Set.Ioi (0 : ℝ))) with hν
  -- Step 1: μ0 ≪ ν using positivity of 1/x on (0, ∞)
  have h_div_meas : Measurable (fun x : ℝ => ENNReal.ofReal (1 / x)) := by
    apply Measurable.ennreal_ofReal
    simpa using (Measurable.div measurable_const measurable_id)
  have h_div_aemeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal (1 / x)) μ0 :=
    h_div_meas.aemeasurable
  have h_div_ne_zero : ∀ᵐ x ∂ μ0, ENNReal.ofReal (1 / x) ≠ 0 := by
    refine ((ae_restrict_iff' measurableSet_Ioi).2 ?_)
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hx)))
  have h_ac_base :
      μ0 ≪ μ0.withDensity (fun x : ℝ => ENNReal.ofReal (1 / x)) :=
    withDensity_absolutelyContinuous' (μ := μ0)
      (f := fun x : ℝ => ENNReal.ofReal (1 / x)) h_div_aemeas h_div_ne_zero
  have h_rewrite_ν :
      μ0.withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹) = ν := by
    -- (volume.withDensity f).restrict s = (volume.restrict s).withDensity f,
    -- applied with s = Ioi 0 and f x = ofReal (1/x)
    have hres :=
      restrict_withDensity (μ := volume) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi (fun x : ℝ => ENNReal.ofReal (1 / x))
    -- Rearrange sides and rewrite μ0, ν definitions
    simpa [μ0, ν, one_div] using hres.symm
  have h_ac1 : μ0 ≪ ν := by simpa [h_rewrite_ν, one_div] using h_ac_base
  -- Step 2: ν ≪ ν.withDensity g using positivity of g on (0, ∞)
  set g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x ^ (2 * σ - 1)) with hg
  have hg_aemeas : AEMeasurable g ν := by
    -- use `AEMeasurable.pow_const` for `(fun x : ℝ => x) ^ const` and then `ennreal_ofReal`
    have hpow : AEMeasurable (fun x : ℝ => (x : ℝ) ^ (2 * σ - 1)) ν :=
      (aemeasurable_id.pow_const (2 * σ - 1))
    exact hpow.ennreal_ofReal
  have hg_ne_zero : ∀ᵐ x ∂ ν, g x ≠ 0 := by
    -- On the restricted measure to `(0, ∞)`, we have `x > 0` a.e.
    have h_mem : ∀ᵐ x ∂ ν, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [ν] using (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
        (s := Set.Ioi (0 : ℝ)))
    refine h_mem.mono ?_
    intro x hx
    have hxpos : 0 < x := hx
    have hxpow_pos : 0 < x ^ (2 * σ - 1) := Real.rpow_pos_of_pos hxpos _
    have : 0 < g x := by simpa [g, hg] using ENNReal.ofReal_pos.mpr hxpow_pos
    exact ne_of_gt this
  have h_ac2 : ν ≪ ν.withDensity g :=
    withDensity_absolutelyContinuous' (μ := ν) (f := g) hg_aemeas hg_ne_zero
  -- Transitivity gives the desired absolute continuity
  have h_goal : μ0 ≪ ν.withDensity g := h_ac1.trans h_ac2
  -- Replace back `ν` with `mulHaar`
  simpa [μ0, hμ, ν, hg] using h_goal

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
    -- Transform h_add_ae to work with volume.restrict
    -- h_add_ae is ae on (volume.restrict (Set.Ioi 0)).withDensity
    -- We need it ae on volume.restrict (Set.Ioi 0)
    have h_add_ae' : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        Hσ.toFun (f + g) x = Hσ.toFun f x + Hσ.toFun g x := by
      -- Transfer the a.e. equality from the weighted measure back to `volume.restrict`.
      -- Absolute continuity: μ0 ≪ μ0.withDensity(weight)
      have h_ac :
          (volume.restrict (Set.Ioi (0 : ℝ))) ≪
            (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
        -- AEMeasurability of the density
        have h_aemeas : AEMeasurable
            (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
            (volume.restrict (Set.Ioi (0 : ℝ))) := by
          have hpow : AEMeasurable (fun x : ℝ => (x : ℝ) ^ (2 * σ - 1))
              (volume.restrict (Set.Ioi (0 : ℝ))) :=
            (aemeasurable_id.pow_const (2 * σ - 1))
          exact hpow.ennreal_ofReal
        -- Positivity of the density a.e. on (0, ∞)
        have h_ne_zero : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
            ENNReal.ofReal (x ^ (2 * σ - 1)) ≠ 0 := by
          have hx_mem : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
              x ∈ Set.Ioi (0 : ℝ) := by
            simpa using (ae_restrict_mem (μ := volume)
              (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi)
          refine hx_mem.mono ?_
          intro x hx
          have hxpos : 0 < x := hx
          have hxpow_pos : 0 < x ^ (2 * σ - 1) := Real.rpow_pos_of_pos hxpos _
          exact ne_of_gt (by simpa using ENNReal.ofReal_pos.mpr hxpow_pos)
        -- Conclude absolute continuity via withDensity_absolutelyContinuous'
        exact withDensity_absolutelyContinuous'
          (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
          h_aemeas h_ne_zero
      -- Turn the a.e. equality into a null set via `ae_iff` on the weighted measure
      have h_null_weighted :
          ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
            (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))
            {x | Hσ.toFun (f + g) x ≠ Hσ.toFun f x + Hσ.toFun g x} = 0 := by
        have := ((ae_iff
          (μ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
            (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))
          (p := fun x : ℝ =>
            Hσ.toFun (f + g) x = Hσ.toFun f x + Hσ.toFun g x))).1 h_add_ae
        simpa [Set.compl_setOf] using this
      -- Use absolute continuity to deduce the base measure null set
      have h_null_base :
          (volume.restrict (Set.Ioi (0 : ℝ)))
            {x | Hσ.toFun (f + g) x ≠ Hσ.toFun f x + Hσ.toFun g x} = 0 :=
        h_ac h_null_weighted
      -- Convert back to an a.e. statement on the base measure
      exact ((ae_iff
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (p := fun x : ℝ =>
          Hσ.toFun (f + g) x = Hσ.toFun f x + Hσ.toFun g x))).2
        (by simpa [Set.compl_setOf] using h_null_base)
    filter_upwards [h_add_ae', (ae_restrict_mem (μ := volume)
      (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi)] with x hx hx_in
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
          -- measurability of the second summand
          have h_meas_coe : Measurable (fun x : ℝ => Hσ.toFun g x) :=
            (Lp.stronglyMeasurable g).measurable
          have h_meas_norm : Measurable (fun x : ℝ => ‖Hσ.toFun g x‖) := h_meas_coe.norm
          have h_meas_sq : Measurable (fun x : ℝ => ‖Hσ.toFun g x‖ ^ 2) := by
            simpa [pow_two] using h_meas_norm.mul h_meas_norm
          have h_meas_pow : Measurable (fun x : ℝ => x ^ (2 * σ - 1)) :=
            (measurable_id.pow_const (2 * σ - 1))
          have h_meas_prod : Measurable
              (fun x : ℝ => ‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1)) :=
            h_meas_sq.mul h_meas_pow
          have h_inside : Measurable
              (fun x : ℝ => 2 * (‖Hσ.toFun g x‖ ^ 2 * x ^ (2 * σ - 1))) :=
            measurable_const.mul h_meas_prod
          simpa [mul_assoc, mul_left_comm, mul_comm]
            using (Measurable.ennreal_ofReal h_inside)
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
  have h_nonneg_weight : ∀ ⦃x : ℝ⦄, 0 < x → 0 ≤ x ^ (2 * σ - 1) := by
    intro x hx
    exact Real.rpow_nonneg (le_of_lt hx) _
  have h_lintegral :
      (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal
            (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume)
        = (ENNReal.ofReal (‖c‖^2)) *
          (∫⁻ x in Set.Ioi (0 : ℝ),
            ENNReal.ofReal
              (‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) := by
    have h_pointwise_ae :
        (fun x : ℝ =>
          ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)))
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun x : ℝ =>
          ENNReal.ofReal (‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1))) := by
      -- First, obtain the a.e. equality of the underlying functions under the base measure.
      have h_smul_ae := toFun_smul_ae σ c f
      -- Convert a.e. equality from the weighted measure to `volume.restrict (Ioi 0)`.
      have h_ac :
          (volume.restrict (Set.Ioi (0 : ℝ))) ≪
            (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
        -- AEMeasurable density and positivity on (0, ∞)
        have h_aemeas : AEMeasurable
            (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
            (volume.restrict (Set.Ioi (0 : ℝ))) := by
          have hpow : AEMeasurable (fun x : ℝ => (x : ℝ) ^ (2 * σ - 1))
              (volume.restrict (Set.Ioi (0 : ℝ))) :=
            (aemeasurable_id.pow_const (2 * σ - 1))
          exact hpow.ennreal_ofReal
        have h_ne_zero : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
            ENNReal.ofReal (x ^ (2 * σ - 1)) ≠ 0 := by
          have hx_mem : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
              x ∈ Set.Ioi (0 : ℝ) := by
            simpa using (ae_restrict_mem (μ := volume)
              (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi)
          refine hx_mem.mono ?_
          intro x hx
          have hxpos : 0 < x := hx
          have hxpow_pos : 0 < x ^ (2 * σ - 1) := Real.rpow_pos_of_pos hxpos _
          exact ne_of_gt (by simpa using ENNReal.ofReal_pos.mpr hxpow_pos)
        exact withDensity_absolutelyContinuous'
          (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
          h_aemeas h_ne_zero
      have h_smul_ae' : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
          Hσ.toFun (c • f) x = c * Hσ.toFun f x := by
        -- Convert a.e. equality via null set transfer using `ae_iff`.
        have h_null_weighted :
            ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))
              {x | Hσ.toFun (c • f) x ≠ c * Hσ.toFun f x} = 0 := by
          have := ((ae_iff
            (μ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))
            (p := fun x : ℝ =>
              Hσ.toFun (c • f) x = c * Hσ.toFun f x))).1 h_smul_ae
          simpa [Set.compl_setOf] using this
        have h_null_base :
            (volume.restrict (Set.Ioi (0 : ℝ)))
              {x | Hσ.toFun (c • f) x ≠ c * Hσ.toFun f x} = 0 :=
          h_ac h_null_weighted
        exact ((ae_iff
          (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (p := fun x : ℝ =>
            Hσ.toFun (c • f) x = c * Hσ.toFun f x))).2
          (by simpa [Set.compl_setOf] using h_null_base)
      -- Now upgrade to the desired equality of the ENNReal-ofReal integrands.
      filter_upwards [h_smul_ae',
          (ae_restrict_mem (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi)]
        with x hx_eq hx_in
      -- Use pointwise norm equality and square both sides
      have hnorm_eq : ‖Hσ.toFun (c • f) x‖ = ‖c‖ * ‖Hσ.toFun f x‖ := by
        have : ‖Hσ.toFun (c • f) x‖ = ‖c * Hσ.toFun f x‖ := by
          simp [hx_eq]
        simpa [norm_mul] using this
      have hsq : ‖Hσ.toFun (c • f) x‖ ^ 2
          = ‖c‖^2 * ‖Hσ.toFun f x‖^2 := by
        have := congrArg (fun t : ℝ => t^2) hnorm_eq
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      -- Conclude equality inside `ofReal` (no sign condition needed for equality)
      have : ‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)
          = (‖c‖^2 * ‖Hσ.toFun f x‖^2) * x ^ (2 * σ - 1) := by
        simp [hsq]
      calc ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1))
          = ENNReal.ofReal ((‖c‖^2 * ‖Hσ.toFun f x‖^2) * x ^ (2 * σ - 1)) := by
              rw [this]
        _ = ENNReal.ofReal (‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) := by
              ring_nf

    have h_integrand_measurable :
        AEStronglyMeasurable
          (fun x : ℝ =>
            ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)))
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
      -- Show the integrand is measurable, then upgrade to AE-strongly measurable
      have h_meas_coe : Measurable (fun x : ℝ => Hσ.toFun (c • f) x) :=
        (Lp.stronglyMeasurable (c • f)).measurable
      have h_meas_norm : Measurable (fun x : ℝ => ‖Hσ.toFun (c • f) x‖) := h_meas_coe.norm
      have h_meas_sq : Measurable (fun x : ℝ => ‖Hσ.toFun (c • f) x‖ ^ 2) := by
        simpa [pow_two] using h_meas_norm.mul h_meas_norm
      have h_meas_pow : Measurable (fun x : ℝ => x ^ (2 * σ - 1)) :=
        (measurable_id.pow_const (2 * σ - 1))
      have h_meas_prod : Measurable
          (fun x : ℝ => ‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)) :=
        h_meas_sq.mul h_meas_pow
      exact (Measurable.ennreal_ofReal h_meas_prod).aestronglyMeasurable
    have h_integrand' : AEStronglyMeasurable
        (fun x : ℝ => ENNReal.ofReal
          (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      -- As above, show measurability then upgrade to AE-strongly measurable
      have h_meas_coe : Measurable (fun x : ℝ => Hσ.toFun f x) :=
        (Lp.stronglyMeasurable f).measurable
      have h_meas_norm : Measurable (fun x : ℝ => ‖Hσ.toFun f x‖) := h_meas_coe.norm
      have h_meas_sq : Measurable (fun x : ℝ => ‖Hσ.toFun f x‖ ^ 2) := by
        simpa [pow_two] using h_meas_norm.mul h_meas_norm
      have h_meas_pow : Measurable (fun x : ℝ => x ^ (2 * σ - 1)) :=
        (measurable_id.pow_const (2 * σ - 1))
      have h_meas_prod : Measurable
          (fun x : ℝ => ‖Hσ.toFun f x‖ ^ 2 * x ^ (2 * σ - 1)) :=
        h_meas_sq.mul h_meas_pow
      exact (Measurable.ennreal_ofReal h_meas_prod).aestronglyMeasurable
    have h_eq1 : ∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume
      = ∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := by
      -- Use a.e. equality on the restricted measure
      simpa using lintegral_congr_ae h_pointwise_ae
    -- Factor the constant `‖c‖^2` out of the integral (pointwise, a.e.)
    have h_factor_ae :
        (fun x : ℝ =>
          ENNReal.ofReal (‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)))
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun x : ℝ => ENNReal.ofReal (‖c‖^2) *
          ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1))) := by
      -- On `(0, ∞)`, the weight is nonnegative, so we can pull out the constant from `ofReal`.
      refine ((ae_restrict_iff' measurableSet_Ioi).2 ?_)
      refine Filter.Eventually.of_forall ?_
      intro x hx
      have hx_pos : 0 < x := hx
      have hx_nonneg : 0 ≤ ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hx_pos) _)
      have hx' :
          ‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)
            = ‖c‖^2 * (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) := by ring
      simp [hx', ENNReal.ofReal_mul (sq_nonneg _), hx_nonneg]
    have h_eq2 : ∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume
      = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖c‖^2) *
          ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := by
      simpa using lintegral_congr_ae h_factor_ae
    calc
      ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume
        = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖c‖^2 * ‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := h_eq1
      _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖c‖^2) * ENNReal.ofReal
            (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := h_eq2
      _ = ENNReal.ofReal (‖c‖^2) * ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := by
        rw [lintegral_const_mul' _ _ (by norm_num : ENNReal.ofReal (‖c‖^2) ≠ ∞)]
  -- Use the equality and finiteness of the base integral to conclude finiteness
  have h_const_ne_top : ENNReal.ofReal (‖c‖^2) ≠ ∞ := by simp
  have h_const_lt_top : ENNReal.ofReal (‖c‖^2) < ∞ := by
    simp [lt_top_iff_ne_top]
  have h_fin :
      (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun (c • f) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume) < ∞ := by
    -- Rewrite using h_lintegral and apply `ENNReal.mul_lt_top`
    have := ENNReal.mul_lt_top h_const_lt_top hf
    simpa [h_lintegral] using this
  exact h_fin

lemma has_weighted_L2_norm_sub (σ : ℝ) {f g : Hσ σ}
    (hf : has_weighted_L2_norm σ f) (hg : has_weighted_L2_norm σ g) :
    has_weighted_L2_norm σ (f - g) := by
  classical
  simpa [sub_eq_add_neg]
    using has_weighted_L2_norm_add σ hf (has_weighted_L2_norm_smul σ (-1 : ℂ) hg)

/-!
Unweighted L² relation between LogPull and the Mellin transform.

This version applies Plancherel to `g = LogPull σ f` directly, hence the left-hand
side is the unweighted L² norm of `LogPull σ f` and the right-hand side integrates the
Mellin transform along the vertical line `Re s = σ` with the usual `1/(2π)` factor.
-/
lemma logpull_mellin_l2_relation (σ : ℝ) (f : Hσ σ)
    (h_L2 : MemLp (LogPull σ f) 2 volume)
    (h_L1 : Integrable (LogPull σ f)) :
    ∫ t : ℝ, ‖LogPull σ f t‖^2 ∂volume
      = (1 / (2 * Real.pi)) *
          ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖^2 ∂volume := by
  classical
  -- Set g := LogPull σ f and apply Fourier–Plancherel on g
  set g : ℝ → ℂ := LogPull σ f with hg
  have hg_L1 : Integrable g := by simpa [hg]
    using h_L1
  have hg_L2 : MemLp g 2 volume := by simpa [hg]
    using h_L2
  have h_plancherel := fourier_plancherel_L1_L2 g hg_L1 hg_L2
  -- Identify fourierIntegral g(-τ/(2π)) with the Mellin transform on Re s = σ
  have h_mellin_eq_fourier : ∀ τ : ℝ,
      mellinTransform (f : ℝ → ℂ) (σ + I * τ) =
        fourierIntegral g (-τ / (2 * Real.pi)) := by
    intro τ
    -- Use the established equality without additional weights
    have := mellin_logpull_fourierIntegral σ τ f
    have h_funext : (fun t ↦ LogPull σ f t) = g := by
      ext t
      rw [← hg]
    rw [h_funext] at this
    exact this
  -- Rescale the frequency variable to move from ξ to τ
  have h_change_of_var :
      ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume
        = (1 / (2 * Real.pi)) *
            ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
    classical
    have h_rescale := integral_fourierIntegral_rescale_sq g
    simp [fourierIntegral_eq_real] at h_rescale
    set A :=
        ∫ τ : ℝ, ‖fourierIntegral g (-τ / (2 * Real.pi))‖ ^ 2 ∂volume with hA
    set B := ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume with hB
    have h_rescaleAB : A = (2 * Real.pi) * B := by
      simpa [A, B, hA, hB] using h_rescale
    have h_eq_fun :
        (fun τ : ℝ => ‖fourierIntegral g (-τ / (2 * Real.pi))‖ ^ 2)
          = fun τ : ℝ =>
              ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 := by
      funext τ; simp [sq, h_mellin_eq_fourier τ]
    have hA_mellin :
        A = ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
      simp [A, hA, h_eq_fun]
    have h_rescale_mellin :
        ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume
          = (2 * Real.pi) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume := by
      simpa [A, B, hA, hB, hA_mellin] using h_rescaleAB
    -- Divide both sides by (2π)
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
              h_rescale_mellin.symm
        _ = (2 * Real.pi) *
              ((1 / (2 * Real.pi)) * ∫ τ : ℝ,
                  ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume) := by
              simp [mul_comm, mul_left_comm, mul_assoc, one_div, Real.pi_ne_zero]
    exact mul_left_cancel₀ hpi' h_target
  -- Combine Plancherel with the rescaling identity
  calc ∫ t : ℝ, ‖LogPull σ f t‖^2 ∂volume
      = ∫ t : ℝ, ‖g t‖^2 ∂volume := by simp [hg]
    _ = ∫ ξ : ℝ, ‖fourierIntegral g ξ‖^2 ∂volume := h_plancherel
    _ = (1 / (2 * Real.pi)) * ∫ τ : ℝ,
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖^2 ∂volume := h_change_of_var

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
    -- 3. L¹ integrability of LogPull itself (needed by logpull_mellin_l2_relation)
    (Integrable (LogPull σ f)) →
    ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2 * x^(2*σ - 1)) ∂volume =
    ENNReal.ofReal (C * ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume) := by
  classical
  -- Natural Parseval/Plancherel normalization constant
  refine ⟨(1 / (2 * Real.pi)), ?_, ?_⟩
  · -- Positivity of 1/(2π)
    have hpos : 0 < (2 * Real.pi) := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      exact mul_pos h2 Real.pi_pos
    simpa using (one_div_pos.mpr hpos)
  · -- Skeleton: use change-of-variables for LogPull and Plancherel identity
    intro f hL2_weighted hInt hL1
    -- Step 1: the weighted L² finiteness yields L² for LogPull via Core0 lemma.
    have h_extra : has_weighted_L2_norm σ f := by
      -- Definition matches the first hypothesis syntactically.
      simpa using hL2_weighted
    have h_memLp : MemLp (LogPull σ f) 2 (volume : Measure ℝ) :=
      weighted_LogPull_memLp σ f h_extra

    -- Step 2: convert the weighted lintegral to the ENNReal-ofReal of the real L² integral.
    -- First, identify the weighted side with the lintegral of ofReal(‖LogPull‖²).
    have h_weight_eq :
        (∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2 * x^(2*σ - 1)) ∂volume)
          = ∫⁻ t, ENNReal.ofReal (‖LogPull σ f t‖^2) ∂volume := by
      -- Use the prepared change-of-variables lemma in Core0
      simpa using (weighted_LogPull_integral_eq (σ := σ) (f := f)).symm

    -- Next, relate the lintegral of ofReal(‖LogPull‖²) to ofReal of the real integral.
    have h_sq_int : Integrable (fun t : ℝ => ‖LogPull σ f t‖^2) (volume : Measure ℝ) := by
      -- From MemLp with p=2
      exact (memLp_two_iff_integrable_sq_norm (μ := volume)
        (f := LogPull σ f) h_memLp.1).1 h_memLp
    have h_nonneg_sq : 0 ≤ᵐ[volume] fun t : ℝ => ‖LogPull σ f t‖^2 :=
      Filter.Eventually.of_forall (by intro t; exact sq_nonneg _)
    have h_lint_eq_ofReal :
        ∫⁻ t, ENNReal.ofReal (‖LogPull σ f t‖^2) ∂volume
          = ENNReal.ofReal (∫ t, ‖LogPull σ f t‖^2 ∂volume) := by
      -- Convert lintegral of ofReal to ofReal of integral for nonneg integrable function
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_sq_int h_nonneg_sq).symm

    -- Step 3: apply the L² Parseval relation between LogPull and Mellin transform.
    -- We need both L² (available) and L¹ (recorded here as a local obligation).
    have h_L2 : MemLp (LogPull σ f) 2 (volume : Measure ℝ) := h_memLp
    have h_L1 : Integrable (LogPull σ f) := hL1
    have h_pl :
        ∫ t : ℝ, ‖LogPull σ f t‖^2 ∂volume
          = (1 / (2 * Real.pi)) *
              ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖^2 ∂volume :=
      logpull_mellin_l2_relation (σ := σ) (f := f) h_L2 h_L1

    -- Step 4: assemble the chain and conclude with the chosen constant C.
    calc
      ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2 * x^(2*σ - 1)) ∂volume
          = ∫⁻ t, ENNReal.ofReal (‖LogPull σ f t‖^2) ∂volume := h_weight_eq
      _ = ENNReal.ofReal (∫ t, ‖LogPull σ f t‖^2 ∂volume) := h_lint_eq_ofReal
      _ = ENNReal.ofReal
            ((1 / (2 * Real.pi)) * ∫ τ : ℝ,
                ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume) := by
              simpa [one_div, Real.pi_ne_zero] using congrArg ENNReal.ofReal h_pl

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

end ParsevalEquivalence

end Frourio
