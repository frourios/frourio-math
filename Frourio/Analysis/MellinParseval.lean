import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.SchwartzDensity.SchwartzDensity
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

/-- The Lebesgue measure of the topological support of a compactly supported
function is finite. -/
lemma volume_tsupport_lt_top {f : ℝ → ℂ}
    (hf : HasCompactSupport f) : volume (tsupport f) < ∞ := by
  classical
  obtain ⟨R, _hR_pos, h_subset⟩ := HasCompactSupport.exists_radius_closedBall hf
  have h_ball_lt_top : volume (Metric.closedBall (0 : ℝ) R) < ∞ :=
    MeasureTheory.measure_closedBall_lt_top (x := (0 : ℝ)) (r := R)
  exact lt_of_le_of_lt (measure_mono h_subset) h_ball_lt_top

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

lemma smooth_compactly_supported_dense_L2 (f_L2 : ℝ → ℂ)
    (hf : MemLp f_L2 2 volume) (ε : ℝ) (hε_pos : ε > 0) :
    ∃ g : ℝ → ℂ, HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
        eLpNorm (f_L2 - g) 2 volume < ENNReal.ofReal ε := by
  classical
  -- Step 1: approximate by a continuous compactly supported function.
  have hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hε_half_pos : 0 < ε / 2 := half_pos hε_pos
  have hε_half_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hε_half_pos))
  obtain ⟨g₀, hg₀_support, hg₀_close_le, hg₀_continuous, hg₀_memLp⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (μ := volume) (p := (2 : ℝ≥0∞)) hp
      (ε := ENNReal.ofReal (ε / 2)) hε_half_ne
  have hg₀_meas : AEStronglyMeasurable g₀ volume := hg₀_memLp.aestronglyMeasurable

  -- Enclose the support of g₀ in a convenient closed ball.
  obtain ⟨R, hR_pos, hR_subset⟩ :=
    HasCompactSupport.exists_radius_closedBall hg₀_support
  have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
  let S : Set ℝ := Metric.closedBall (0 : ℝ) (R + 2)
  have hS_meas : MeasurableSet S := measurableSet_closedBall
  have hS_lt_top : volume S < ∞ := by
    simpa [S] using
      (MeasureTheory.measure_closedBall_lt_top (μ := volume)
        (x := (0 : ℝ)) (r := R + 2))
  set μS : ℝ := (volume S).toReal with hμS_def
  have hμS_nonneg : 0 ≤ μS := by simp [μS]
  let M : ℝ := Real.sqrt μS
  have hM_nonneg : 0 ≤ M := Real.sqrt_nonneg _
  have hM_plus_pos : 0 < M + 1 := add_pos_of_nonneg_of_pos hM_nonneg zero_lt_one

  -- Choose the target uniform approximation tolerance δ.
  have hdenom_pos : 0 < 4 * (M + 1) := mul_pos (by norm_num) hM_plus_pos
  have hδ_pos : 0 < ε / (4 * (M + 1)) := by
    exact div_pos hε_pos hdenom_pos
  set δ : ℝ := ε / (4 * (M + 1)) with hδ_def
  have hδ_pos' : 0 < δ := by simpa [δ] using hδ_pos
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos'

  -- Uniformly approximate by a smooth function.
  have hg₀_uc : UniformContinuous g₀ :=
    Continuous.uniformContinuous_of_hasCompactSupport hg₀_continuous hg₀_support
  obtain ⟨h, hh_smooth, hh_close⟩ := hg₀_uc.exists_contDiff_dist_le hδ_pos'

  -- Build a smooth bump function used to cut off the approximation.
  let bump : ContDiffBump (0 : ℝ) :=
    { rIn := R + 1
      rOut := R + 2
      rIn_pos := add_pos_of_nonneg_of_pos hR_nonneg zero_lt_one
      rIn_lt_rOut := by linarith }
  let χ : ℝ → ℝ := fun x => bump x
  have hχ_one : ∀ x ∈ Metric.closedBall (0 : ℝ) (R + 1), χ x = 1 := by
    intro x hx
    simpa [χ] using bump.one_of_mem_closedBall hx
  have hχ_zero_outside : ∀ x, R + 2 ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    have hx' : dist x (0 : ℝ) ≥ R + 2 := by
      simpa [Real.dist_eq, sub_eq_add_neg] using hx
    have := bump.zero_of_le_dist (x := x) (c := (0 : ℝ))
      (by simpa [Real.dist_eq, sub_eq_add_neg] using hx')
    simpa [χ, Real.dist_eq, sub_eq_add_neg] using this
  have hχ_nonneg : ∀ x, 0 ≤ χ x := by
    intro x; simpa [χ] using bump.nonneg' x
  have hχ_le_one : ∀ x, χ x ≤ 1 := by
    intro x; simpa [χ] using bump.le_one (c := (0 : ℝ)) (x := x)

  -- Define the smooth compactly supported approximation `g`.
  let g : ℝ → ℂ := fun x => (χ x) • h x
  have hh_smooth' : ContDiff ℝ (⊤ : ℕ∞) h := by
    simpa using hh_smooth
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := by
    simpa [χ] using (bump.contDiff (n := (⊤ : ℕ∞)))
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    simpa [g, χ] using hχ_smooth.smul hh_smooth'
  have hg_continuous : Continuous g := hg_smooth.continuous
  have hg_compact : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R + 2)) ?_
    intro x hx
    have hx_gt : R + 2 < ‖x‖ := by
      have := Metric.mem_closedBall.not.1 hx
      simpa [S, Real.dist_eq, sub_eq_add_neg] using this
    have hx_ge : R + 2 ≤ ‖x‖ := le_of_lt hx_gt
    have hχ_zero' := hχ_zero_outside x hx_ge
    simp [g, χ, hχ_zero']

  -- Auxiliary facts about the original approximation g₀.
  have hg₀_zero_outside : ∀ x, R < ‖x‖ → g₀ x = 0 := by
    intro x hx
    have hx_not : x ∉ tsupport g₀ := by
      intro hx_mem
      have hx_ball : x ∈ Metric.closedBall (0 : ℝ) R := hR_subset hx_mem
      have hx_le : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using hx_ball
      exact (not_le_of_gt hx) hx_le
    simpa using image_eq_zero_of_notMem_tsupport (f := g₀) hx_not

  -- Pointwise control of the difference `g₀ - g`.
  have h_pointwise_bound : ∀ x, ‖g₀ x - g x‖ ≤ δ := by
    intro x
    have hclose := hh_close x
    have hclose_le : ‖h x - g₀ x‖ ≤ δ :=
      le_of_lt (by simpa [dist_eq_norm, sub_eq_add_neg] using hclose)
    by_cases hx : ‖x‖ ≤ R + 1
    · have hx_ball : x ∈ Metric.closedBall (0 : ℝ) (R + 1) :=
        by simpa [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] using hx
      have hχ_one' : χ x = 1 := hχ_one x hx_ball
      have : g x = h x := by simp [g, χ, hχ_one']
      simpa [this, norm_sub_rev] using hclose_le
    · have hx_gt : R + 1 < ‖x‖ := lt_of_not_ge hx
      have hx_gt' : R < ‖x‖ := by
        have hR_lt : R < R + 1 := by linarith
        exact lt_trans hR_lt hx_gt
      have hg₀_zero := hg₀_zero_outside x hx_gt'
      have hχ_abs_le : ‖χ x‖ ≤ 1 := by
        have hχ_nn := hχ_nonneg x
        have hχ_le := hχ_le_one x
        have : ‖χ x‖ = χ x := by
          have := abs_of_nonneg hχ_nn
          simpa [Real.norm_eq_abs] using this
        simpa [this] using hχ_le
      have hnorm_h : ‖h x‖ ≤ δ := by
        simpa [hg₀_zero, norm_sub_rev] using hclose_le
      have hdiff_eq : ‖g₀ x - g x‖ = ‖χ x‖ * ‖h x‖ := by
        simp [g, χ, hg₀_zero]
      have hmul_le' : ‖χ x‖ * ‖h x‖ ≤ ‖h x‖ := by
        have hnn : 0 ≤ ‖h x‖ := norm_nonneg _
        have := mul_le_of_le_one_right hnn hχ_abs_le
        simpa [mul_comm] using this
      have hmul_le : ‖χ x‖ * ‖h x‖ ≤ δ :=
        hmul_le'.trans hnorm_h
      exact (by simpa [hdiff_eq] using hmul_le)

  -- The difference vanishes outside the compact set `S`.
  have h_diff_zero_outside : ∀ x, x ∉ S → g₀ x - g x = 0 := by
    intro x hx
    have hx_gt : R + 2 < ‖x‖ := by
      have := Metric.mem_closedBall.not.1 hx
      simpa [S, Real.dist_eq, sub_eq_add_neg] using this
    have hx_ge : R + 2 ≤ ‖x‖ := le_of_lt hx_gt
    have hR_lt : R < R + 2 := by linarith
    have hg₀_zero := hg₀_zero_outside x (lt_trans hR_lt hx_gt)
    have hχ_zero := hχ_zero_outside x hx_ge
    simp [g, χ, hg₀_zero, hχ_zero]

  -- Control the L² norm on the compact set using the uniform bound.
  have h_integrand_le :
      ∀ x, ‖g₀ x - g x‖₊ ^ 2
          ≤ Set.indicator S (fun _ => ENNReal.ofReal (δ ^ 2)) x := by
    intro x
    classical
    by_cases hx : x ∈ S
    · have hnorm_le := h_pointwise_bound x
      have hnorm_nonneg : 0 ≤ ‖g₀ x - g x‖ := norm_nonneg _
      have hpow_le : ‖g₀ x - g x‖ ^ 2 ≤ δ ^ 2 := by
        have := mul_le_mul hnorm_le hnorm_le hnorm_nonneg hδ_nonneg
        simpa [pow_two, mul_comm] using this
      have hpow_eq :
          (‖g₀ x - g x‖₊ : ℝ≥0∞) ^ 2
            = ENNReal.ofReal (‖g₀ x - g x‖ ^ 2) := by
        simp [pow_two]
      have hpow_bound :
          (‖g₀ x - g x‖₊ : ℝ≥0∞) ^ 2
            ≤ ENNReal.ofReal (δ ^ 2) := by
        rw [hpow_eq]
        exact ENNReal.ofReal_le_ofReal hpow_le
      have hx_indicator :
          Set.indicator S (fun _ => ENNReal.ofReal (δ ^ 2)) x
            = ENNReal.ofReal (δ ^ 2) := by
        simp [Set.indicator_of_mem, hx]
      exact hx_indicator.symm ▸ hpow_bound
    · have hzero := h_diff_zero_outside x hx
      simp [Set.indicator_of_notMem, hx, hzero]

  have h_integral_bound :
      ∫⁻ x, ‖g₀ x - g x‖₊ ^ 2 ∂volume
        ≤ ENNReal.ofReal (δ ^ 2) * volume S := by
    have h_le :
        ∀ᵐ x ∂volume,
          ‖g₀ x - g x‖₊ ^ 2
            ≤ Set.indicator S (fun _ => ENNReal.ofReal (δ ^ 2)) x :=
      ae_of_all _ h_integrand_le
    refine (lintegral_mono_ae h_le).trans ?_
    have h_indicator :=
      MeasureTheory.lintegral_indicator (μ := volume)
        (f := fun _ : ℝ => ENNReal.ofReal (δ ^ 2)) (hs := hS_meas)
    have h_const :
        ∫⁻ x, ENNReal.ofReal (δ ^ 2) ∂(volume.restrict S)
          = ENNReal.ofReal (δ ^ 2) * (volume.restrict S) Set.univ := by
      simp
    have h_restrict : (volume.restrict S) Set.univ = volume S := by
      simp [Measure.restrict_apply]
    have h_result :
        ∫⁻ x, Set.indicator S (fun _ => ENNReal.ofReal (δ ^ 2)) x ∂volume
          = ENNReal.ofReal (δ ^ 2) * volume S := by
      simpa [h_const, h_restrict] using h_indicator
    exact le_of_eq h_result

  have hμS_eq : ENNReal.ofReal μS = volume S := by
    simpa [μS] using ENNReal.ofReal_toReal (ne_of_lt hS_lt_top)
  have h_integral_bound' :
      ∫⁻ x, ‖g₀ x - g x‖₊ ^ 2 ∂volume
        ≤ ENNReal.ofReal (δ ^ 2 * μS) := by
    have hδ_sq_nonneg : 0 ≤ δ ^ 2 := by
      have := sq_nonneg δ
      simpa [pow_two] using this
    have hrewrite₀ :
        ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal μS
          = ENNReal.ofReal (δ ^ 2 * μS) := by
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using
          (ENNReal.ofReal_mul (p := δ ^ 2) (q := μS)
            (hp := hδ_sq_nonneg)).symm
    have hrewrite :
        ENNReal.ofReal (δ ^ 2) * volume S
          = ENNReal.ofReal (δ ^ 2 * μS) := by
      simpa [hμS_eq.symm] using hrewrite₀
    simpa [hrewrite] using h_integral_bound

  have hμS_sq : μS = M ^ 2 := by
    simp [M, pow_two, hμS_nonneg]
  have hδM_le : δ * M ≤ ε / 4 := by
    have hδ_nonneg : 0 ≤ δ := hδ_nonneg
    have hM_le : M ≤ M + 1 := by linarith
    have hmul : δ * M ≤ δ * (M + 1) := by
      have := mul_le_mul_of_nonneg_left hM_le hδ_nonneg
      simpa [δ, mul_comm] using this
    have hδM1 : δ * (M + 1) = ε / 4 := by
      have hne : M + 1 ≠ 0 := ne_of_gt hM_plus_pos
      calc
        δ * (M + 1)
            = ε / (4 * (M + 1)) * (M + 1) := by simp [δ, mul_comm]
        _ = (ε * (M + 1)) / (4 * (M + 1)) := by
            simpa [mul_comm, mul_assoc]
              using (div_mul_eq_mul_div (ε) (4 * (M + 1)) (M + 1))
        _ = ε / 4 := by
            simpa [mul_comm, mul_assoc]
              using (mul_div_mul_left (a := ε) (b := (4 : ℝ))
                (c := M + 1) hne)
    exact hmul.trans (le_of_eq hδM1)
  have hδ_sq_le : δ ^ 2 * μS ≤ (ε / 4) ^ 2 := by
    have hε4_nonneg : 0 ≤ ε / 4 := div_nonneg hε_pos.le (by norm_num)
    have hδM_nonneg : 0 ≤ δ * M := mul_nonneg hδ_nonneg hM_nonneg
    have hmul := mul_le_mul hδM_le hδM_le hδM_nonneg hε4_nonneg
    have hleft_eq : (δ * M) * (δ * M) = δ ^ 2 * μS := by
      simp [pow_two, hμS_sq, mul_mul_mul_comm]
    have hright_eq : (ε / 4) * (ε / 4) = (ε / 4) ^ 2 := by
      simp [pow_two]
    have hprod_le : (δ * M) * (δ * M) ≤ (ε / 4) * (ε / 4) := hmul
    have h' : δ ^ 2 * μS ≤ (ε / 4) ^ 2 := by
      simpa [hleft_eq, hright_eq] using hprod_le
    exact h'
  have h_integral_final :
      ∫⁻ x, ‖g₀ x - g x‖₊ ^ 2 ∂volume
        ≤ ENNReal.ofReal ((ε / 4) ^ 2) := by
    refine h_integral_bound'.trans ?_
    have := ENNReal.ofReal_le_ofReal hδ_sq_le
    simpa using this

  -- Convert the integral bound to an L² norm bound.
  have h_eLp_le : eLpNorm (g₀ - g) 2 volume ≤ ENNReal.ofReal (ε / 4) := by
    have hp0' : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp_top' : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have h_formula :=
      eLpNorm_eq_lintegral_rpow_enorm (μ := volume) (f := g₀ - g) hp0' hp_top'
    have h_twoReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    have h_half_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have h_pow_le :=
      ENNReal.rpow_le_rpow h_integral_final h_half_nonneg
    have hε_quarter_nonneg : 0 ≤ ε / 4 := div_nonneg hε_pos.le (by norm_num)
    have htarget_pow_raw :
        (ENNReal.ofReal (ε / 4 * (ε / 4))) ^ (1 / 2 : ℝ)
          = ENNReal.ofReal (ε / 4) := by
      have hpos : 0 ≤ ε / 4 * (ε / 4) :=
        mul_nonneg hε_quarter_nonneg hε_quarter_nonneg
      have hcoeff : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have hpow_eval₀ : ((ε / 4) ^ 2) ^ (1 / 2 : ℝ) = ε / 4 := by
        have hsqrt : ((ε / 4) ^ 2) ^ (1 / 2 : ℝ)
            = Real.sqrt ((ε / 4) ^ 2) := by
          simp [Real.sqrt_eq_rpow]
        have hsq : Real.sqrt ((ε / 4) ^ 2) = ε / 4 := by
          simpa [pow_two] using Real.sqrt_sq hε_quarter_nonneg
        exact hsqrt.trans hsq
      have hpow_eval : (ε / 4 * (ε / 4)) ^ (1 / 2 : ℝ) = ε / 4 := by
        have hrewrite : ε / 4 * (ε / 4) = (ε / 4) ^ 2 := by
          simp [pow_two]
        simpa [hrewrite] using hpow_eval₀
      calc
        (ENNReal.ofReal (ε / 4 * (ε / 4))) ^ (1 / 2 : ℝ)
            = ENNReal.ofReal ((ε / 4 * (ε / 4)) ^ (1 / 2 : ℝ)) :=
              ENNReal.ofReal_rpow_of_nonneg hpos hcoeff
        _ = ENNReal.ofReal (ε / 4) := by rw [hpow_eval]
    have htarget_pow :
        (ENNReal.ofReal (ε / 4 * (ε / 4))) ^ (2⁻¹ : ℝ)
          = ENNReal.ofReal (ε / 4) := by
      simpa [one_div] using htarget_pow_raw
    have htarget_ofReal :
        ENNReal.ofReal ((ε / 4 * (ε / 4)) ^ (2⁻¹ : ℝ))
          = ENNReal.ofReal (ε / 4) := by
      have hpow_eval_raw : (ε / 4 * (ε / 4)) ^ (1 / 2 : ℝ) = ε / 4 := by
        have hpow_eval_sq : ((ε / 4) ^ 2) ^ (1 / 2 : ℝ) = ε / 4 := by
          have hsqrt : ((ε / 4) ^ 2) ^ (1 / 2 : ℝ)
              = Real.sqrt ((ε / 4) ^ 2) := by
            simp [Real.sqrt_eq_rpow]
          have hsq : Real.sqrt ((ε / 4) ^ 2) = ε / 4 := by
            have hε_quarter_nonneg : 0 ≤ ε / 4 :=
              div_nonneg hε_pos.le (by norm_num)
            simpa [pow_two] using Real.sqrt_sq hε_quarter_nonneg
          exact hsqrt.trans hsq
        have hrewrite : ε / 4 * (ε / 4) = (ε / 4) ^ 2 := by
          simp [pow_two]
        simpa [hrewrite] using hpow_eval_sq
      have htarget_ofReal_raw :
          ENNReal.ofReal ((ε / 4 * (ε / 4)) ^ (1 / 2 : ℝ))
            = ENNReal.ofReal (ε / 4) :=
        congrArg ENNReal.ofReal hpow_eval_raw
      simpa [one_div] using htarget_ofReal_raw
    have hleft :
        eLpNorm (g₀ - g) 2 volume
          = (∫⁻ x, ‖g₀ x - g x‖₊ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
      simpa [h_twoReal, one_div] using h_formula
    have h_pow_le' :
        eLpNorm (g₀ - g) 2 volume
          ≤ (ENNReal.ofReal (ε / 4 * (ε / 4))) ^ (1 / 2 : ℝ) := by
      simpa [hleft, pow_two, mul_comm, one_div, htarget_ofReal] using h_pow_le
    simpa [htarget_pow, one_div] using h_pow_le'

  -- Combine approximations using the triangle inequality.
  have hf_meas : AEStronglyMeasurable f_L2 volume := hf.aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable g volume := hg_continuous.aestronglyMeasurable
  have h_triangle :=
    eLpNorm_triangle_diff f_L2 g₀ g hf_meas hg₀_meas hg_meas
  have h_total_le :
      eLpNorm (f_L2 - g) 2 volume
        ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) :=
    h_triangle.trans <| add_le_add hg₀_close_le h_eLp_le
  have hε_half_nonneg : 0 ≤ ε / 2 := div_nonneg hε_pos.le (by norm_num)
  have hε_quarter_nonneg : 0 ≤ ε / 4 := div_nonneg hε_pos.le (by norm_num)
  have hsum_eq :
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4)
        = ENNReal.ofReal (3 * ε / 4) := by
    have hε_quarter_pos : 0 ≤ ε / 4 := hε_quarter_nonneg
    have hε_half_pos : 0 ≤ ε / 2 := hε_half_nonneg
    have hring : ε / 2 + ε / 4 = 3 * ε / 4 := by ring
    have hsum := (ENNReal.ofReal_add hε_half_pos hε_quarter_pos).symm
    simpa [hring] using hsum
  have hthree_lt_real : 3 * ε / 4 < ε := by
    have hε_quarter_pos : 0 < ε / 4 := div_pos hε_pos (by norm_num)
    have hrewrite : 3 * ε / 4 = ε - ε / 4 := by ring
    simpa [hrewrite] using sub_lt_self ε hε_quarter_pos
  have hthree_lt : ENNReal.ofReal (3 * ε / 4) < ENNReal.ofReal ε := by
    have hε_pos' : 0 < ε := hε_pos
    exact (ENNReal.ofReal_lt_ofReal_iff hε_pos').2 hthree_lt_real
  have h_final_lt : eLpNorm (f_L2 - g) 2 volume < ENNReal.ofReal ε :=
    lt_of_le_of_lt (by simpa [hsum_eq] using h_total_le) hthree_lt

  refine ⟨g, hg_compact, hg_smooth, h_final_lt⟩

/-- Smooth compactly supported functions can be approximated by Schwartz functions in L²(ℝ) -/
lemma schwartz_approximates_smooth_compactly_supported (g : ℝ → ℂ)
    (hg_compact : HasCompactSupport g) (hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (ε : ℝ) (hε_pos : ε > 0) :
    ∃ φ : SchwartzMap ℝ ℂ, eLpNorm (g - (φ : ℝ → ℂ)) 2 volume < ENNReal.ofReal ε := by
  classical
  -- Show that every derivative of `g` is bounded by taking the maximum on the compact support.
  have hg_schwartz : ∀ k n : ℕ, ∃ C : ℝ,
      ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    intro k n
    classical
    set K := tsupport g with hK_def
    have hK_compact : IsCompact K := by
      simpa [hK_def] using hg_compact
    set h : ℝ → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖
    have h_nonneg : ∀ x, 0 ≤ h x := by
      intro x
      exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    have hK_subset : tsupport (iteratedFDeriv ℝ n g) ⊆ K := by
      simpa [hK_def] using
        (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := g) (n := n))
    by_cases h_support_empty :
        tsupport (iteratedFDeriv ℝ n g) = (∅ : Set ℝ)
    · refine ⟨0, ?_⟩
      intro x
      have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := by
        simp [h_support_empty]
      have hx_zero : iteratedFDeriv ℝ n g x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      simp [hx_zero]
    · have h_support_nonempty :
          (tsupport (iteratedFDeriv ℝ n g)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr (by simpa using h_support_empty)
      obtain ⟨x₀, hx₀_support⟩ := h_support_nonempty
      have hx₀K : x₀ ∈ K := hK_subset hx₀_support
      have h_pow_cont : Continuous fun x : ℝ => ‖x‖ ^ k :=
        (continuous_norm : Continuous fun x : ℝ => ‖x‖).pow _
      have h_iter_cont :
          Continuous fun x : ℝ => iteratedFDeriv ℝ n g x :=
        (hg_smooth.continuous_iteratedFDeriv (hm := by
          exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))))
      have h_cont : Continuous h := h_pow_cont.mul (h_iter_cont.norm)
      have h_image_compact : IsCompact (h '' K) := hK_compact.image h_cont
      have h_image_nonempty : (h '' K).Nonempty := ⟨h x₀, ⟨x₀, hx₀K, rfl⟩⟩
      obtain ⟨C, hC_isGreatest⟩ :=
        h_image_compact.exists_isGreatest h_image_nonempty
      obtain ⟨⟨xC, hxC_K, rfl⟩, hC_max⟩ := hC_isGreatest
      refine ⟨h xC, ?_⟩
      intro x
      by_cases hxK : x ∈ K
      · have hx_mem : h x ∈ h '' K := ⟨x, hxK, rfl⟩
        exact hC_max hx_mem
      · have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := fun hx => hxK (hK_subset hx)
        have hx_zero : iteratedFDeriv ℝ n g x = 0 :=
          image_eq_zero_of_notMem_tsupport hx_not
        have h_nonneg_xC : 0 ≤ h xC := h_nonneg xC
        have hx_val : h x = 0 := by simp [h, hx_zero]
        have hx_le : h x ≤ h xC := by simpa [hx_val] using h_nonneg_xC
        simpa [h] using hx_le
  -- Construct the Schwartz function associated to `g`.
  let φ : SchwartzMap ℝ ℂ := ⟨g, hg_smooth, hg_schwartz⟩
  have h_diff_zero : g - (φ : ℝ → ℂ) = (fun _ => 0 : ℝ → ℂ) := by
    funext x
    change g x - g x = 0
    simp
  have h_eLp_zero :
      eLpNorm (g - (φ : ℝ → ℂ)) 2 volume = 0 := by
    simp [h_diff_zero]
  refine ⟨φ, ?_⟩
  have hε_pos' : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε_pos
  simpa [h_eLp_zero] using hε_pos'

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

lemma logpull_mellin_l2_relation (σ : ℝ) (f : Hσ σ)
    (h_weighted_L2 : MemLp (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) 2 volume)
    (h_integrable : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))) :
    ∫ t : ℝ, ‖LogPull σ f t‖^2 * Real.exp t ∂volume =
    (1 / (2 * Real.pi)) * ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖^2 ∂volume := by
  sorry

/-- The Plancherel constant for our normalization is 1 -/
lemma plancherel_constant_is_one (σ : ℝ) (f : Hσ σ) :
    ∃ (C : ℝ), C > 0 ∧ ∫ τ : ℝ, ‖LogPull σ f τ‖^2 = C * ‖f‖^2 ∧ C = 1 := by
  obtain ⟨C, hC_pos, hC_eq⟩ := mellin_plancherel_formula σ f
  -- From the construction in MellinPlancherel.lean, mellin_direct_isometry explicitly gives C = 1
  -- We need to extract this value
  have h_C_one : C = 1 := by
    -- This follows from mellin_direct_isometry which constructs C = 1
    sorry
  exact ⟨C, hC_pos, hC_eq, h_C_one⟩

/-- Uniqueness of the Plancherel constant -/
lemma plancherel_constant_unique (σ : ℝ) (f : Hσ σ) (C₁ C₂ : ℝ)
    (h₁_pos : C₁ > 0) (h₂_pos : C₂ > 0)
    (h₁_eq : ∫ τ : ℝ, ‖LogPull σ f τ‖ ^ 2 = C₁ * ‖f‖ ^ 2)
    (h₂_eq : ∫ τ : ℝ, ‖LogPull σ f τ‖ ^ 2 = C₂ * ‖f‖ ^ 2) :
    C₁ = C₂ := by
  -- If ‖f‖ = 0, then the integral is also 0, and both constants work trivially
  -- If ‖f‖ ≠ 0, we can divide to get C₁ = C₂
  by_cases hf : ‖f‖ = 0
  · -- Case: ‖f‖ = 0
    -- Then the integral is 0, so C₁ * 0 = C₂ * 0 = 0
    -- This doesn't determine C₁ and C₂ uniquely, but we need more structure
    sorry
  · -- Case: ‖f‖ ≠ 0
    have : C₁ * ‖f‖^2 = C₂ * ‖f‖^2 := by rw [←h₁_eq, h₂_eq]
    have hf_sq : ‖f‖^2 ≠ 0 := pow_ne_zero 2 hf
    exact mul_right_cancel₀ hf_sq this

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

  use 1 / (2 * Real.pi)  -- This is the standard normalization

  constructor
  · -- Show 1/(2π) > 0
    simp [Real.pi_pos]

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

/-- Integrability of Mellin kernel for functions in Hσ on the critical line Re(s) = σ
    This holds specifically when s = σ + iτ for real τ -/
lemma mellin_kernel_integrable_on_critical_line (σ : ℝ) (f : Hσ σ) (τ : ℝ)
    (hf_L2 : has_weighted_L2_norm σ f) :
    Integrable (fun t => f t * t ^ ((σ + I * τ) - 1)) (volume.restrict (Set.Ioi 0)) := by
  -- For f ∈ Hσ σ and s = σ + iτ on the critical line:
  -- We have |t^(s-1)| = t^(Re(s)-1) = t^(σ-1)
  -- So we need ∫ |f(t)| * t^(σ-1) dt < ∞

  -- The integrability follows from the weighted L² condition and properties of the Mellin kernel
  -- For s = σ + iτ, we have |t^(s-1)| = t^(Re(s)-1) = t^(σ-1)
  have h_norm_eq : ∀ t : ℝ, 0 < t → ‖(t : ℂ) ^ ((σ + I * τ) - 1)‖ = t ^ (σ - 1) := by
    intro t ht
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
    congr 1
    simp [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.I_re, Complex.mul_re]

  -- Apply the standard integrability characterization using Integrable definition
  refine ⟨?_, ?_⟩
  · -- Measurability: f is continuous on Hσ, complex power is measurable
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · -- f is strongly measurable (from Lp)
      exact (Lp.stronglyMeasurable f).measurable
    · -- Complex power function is measurable
      apply Measurable.pow_const
      exact Complex.measurable_ofReal
  · -- Finite integral: use the weighted L² condition
    rw [hasFiniteIntegral_iff_norm]
    -- We need to show that the norm is integrable, using the weighted L² condition
    -- The key insight is that |t^(s-1)| = t^(σ-1) for s = σ + iτ
    have h_eq : (fun t => ‖f t * (t : ℂ) ^ ((σ + I * τ) - 1)‖) =ᵐ[volume.restrict (Set.Ioi 0)]
                (fun t => ‖f t‖ * t ^ (σ - 1)) := by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
      intro t ht
      simp only [norm_mul]
      congr 1
      exact h_norm_eq t ht
    sorry

/-- Alternative version: Linearity on the critical line Re(s) = σ -/
lemma mellin_transform_linear_critical_line (σ : ℝ) (h k : Hσ σ) (c : ℂ) (τ : ℝ)
    (hh_L2 : has_weighted_L2_norm σ h) (hk_L2 : has_weighted_L2_norm σ k) :
    mellinTransform ((h + c • k) : ℝ → ℂ) (σ + I * τ) =
      mellinTransform (h : ℝ → ℂ) (σ + I * τ) + c * mellinTransform (k : ℝ → ℂ) (σ + I * τ) := by
  apply mellin_transform_linear σ
  · -- Integrability of h on the critical line
    exact mellin_kernel_integrable_on_critical_line σ h τ hh_L2
  · -- Integrability of k on the critical line
    exact mellin_kernel_integrable_on_critical_line σ k τ hk_L2

/-- Polarization identity for Mellin transforms -/
lemma mellin_polarization_pointwise (F G : ℂ) :
    ‖F + G‖ ^ 2 - ‖F - G‖ ^ 2 - Complex.I * ‖F + Complex.I * G‖ ^ 2 +
      Complex.I * ‖F - Complex.I * G‖ ^ 2 = 4 * (starRingEnd ℂ F * G) := by
  -- This is the pointwise polarization identity for complex numbers
  sorry

/-- The Mellin-Plancherel formula relates to Fourier-Parseval -/
theorem parseval_identity_equivalence (σ : ℝ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (f g : Hσ σ),
    -- Additional L² conditions needed for convergence
    has_weighted_L2_norm σ f → has_weighted_L2_norm σ g →
    @inner ℂ _ _ f g = C * ∫ τ : ℝ,
      starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
      mellinTransform (g : ℝ → ℂ) (σ + I * τ) := by
  -- Get the constant from mellin_parseval_formula
  obtain ⟨C, hC_pos, hC_formula⟩ := mellin_parseval_formula σ

  use C
  constructor
  · -- C > 0 from mellin_parseval_formula
    exact hC_pos

  · -- For all f, g with the L² conditions, prove the identity
    intro f g hf_L2 hg_L2

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
          have hfpg_L2 : has_weighted_L2_norm σ (f + g) := by
            -- The sum of L² functions is L²
            sorry
          have hfmg_L2 : has_weighted_L2_norm σ (f - g) := by
            -- The difference of L² functions is L²
            sorry
          have hfig_L2 : has_weighted_L2_norm σ (f + Complex.I • g) := by
            -- Linear combinations of L² functions are L²
            sorry
          have hfmig_L2 : has_weighted_L2_norm σ (f - Complex.I • g) := by
            -- Linear combinations of L² functions are L²
            sorry

          -- Apply hC_formula to each combined function
          have eq1 := hC_formula (f + g) hfpg_L2
          have eq2 := hC_formula (f - g) hfmg_L2
          have eq3 := hC_formula (f + Complex.I • g) hfig_L2
          have eq4 := hC_formula (f - Complex.I • g) hfmig_L2

          -- The equations give us the norms in terms of integrals
          -- We need to substitute these into our expression
          -- For now, we leave this as sorry as it requires careful manipulation
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
