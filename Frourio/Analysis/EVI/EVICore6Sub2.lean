import Frourio.Analysis.EVI.EVICore0
import Frourio.Analysis.EVI.EVICore6Sub1
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Semicontinuous
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Frourio

open Filter Topology Metric

section UniformizationLemmas

variable {φ : ℝ → ℝ} {s r : ℝ}

/-- The quotient function q(y,h) = (φ(s + (y + h)) - φ(s + y)) / h for h > 0 -/
noncomputable def quotient_function (φ : ℝ → ℝ) (s y h : ℝ) : ℝ :=
  (φ (s + (y + h)) - φ (s + y)) / h

/-- Upper semicontinuity condition for the quotient function at h = 0 -/
def upper_semicontinuous_at_zero (φ : ℝ → ℝ) (s : ℝ) (y₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ α > 0, ∃ β > 0, ∀ y h,
    |y - y₀| < α → 0 < h → h < β → quotient_function φ s y h < ε

/-- **Lemma U1**: Parametric right-ε–δ uniformization at a base point
    Given upper semicontinuity and Dini conditions near w, we get uniform bounds. -/
lemma lemma_U1_parametric_uniformization
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y h,
      |y - w| < ρ_w → 0 < h → h < δ_w →
      quotient_function φ s y h ≤ ε := by
  -- For each y₀ near w, get local bounds from Dini condition and upper semicontinuity
  have h_local : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r/4 →
      ∃ α > 0, ∃ β > 0, ∀ y h,
        |y - y₀| < α → 0 < h → h < β → quotient_function φ s y h ≤ ε := by
    intros y₀ hy₀ hy₀_near
    -- From Dini condition at y₀
    have hDini_y₀ := hDini y₀ hy₀
    -- Apply EVISub1's result to get δ for this specific y₀
    obtain ⟨δ_y₀, hδ_y₀_pos, hδ_y₀_prop⟩ :=
      local_control_from_DiniUpperE_right_clean (s + y₀) hDini_y₀ ε hε
    -- From upper semicontinuity at y₀
    obtain ⟨α_y₀, hα_y₀_pos, β_y₀, hβ_y₀_pos, hUSC_y₀⟩ := hUSC y₀ hy₀ hy₀_near (ε/2) (by linarith)
    -- Combine to get the bounds
    use min α_y₀ (r/8), by simp [hα_y₀_pos, hr]
    use min β_y₀ δ_y₀, by simp [hβ_y₀_pos, hδ_y₀_pos]
    intros y h hy_near hh_pos hh_small
    -- Case 1: If y = y₀, apply Dini control directly
    -- Case 2: If y ≠ y₀, use upper semicontinuity
    -- Since |y - y₀| < min α_y₀ (r/8) ≤ α_y₀ and h < min β_y₀ δ_y₀ ≤ β_y₀
    have hy_close : |y - y₀| < α_y₀ := by
      have : min α_y₀ (r/8) ≤ α_y₀ := min_le_left _ _
      linarith [hy_near, this]
    have hh_bound : h < β_y₀ := by
      calc h < min β_y₀ δ_y₀ := hh_small
           _ ≤ β_y₀ := min_le_left _ _
    -- Apply upper semicontinuity result
    have h_usc := hUSC_y₀ y h hy_close hh_pos hh_bound
    -- h_usc gives us quotient_function φ s y h < ε/2 < ε
    linarith [h_usc]

  -- Use compactness to extract uniform bounds
  -- Consider a small closed ball around w
  let K := {y : ℝ | |y - w| ≤ r/8 ∧ y ∈ Set.Icc 0 r}
  have hK_compact : IsCompact K := by
    -- K is a closed and bounded subset of ℝ, hence compact
    -- First show K is closed
    have hK_closed : IsClosed K := by
      have h1 : IsClosed {y : ℝ | |y - w| ≤ r/8} := by
        -- This is a closed ball in the real line
        have : Continuous (fun y => |y - w|) := by
          apply Continuous.comp continuous_abs
          apply Continuous.sub continuous_id continuous_const
        exact isClosed_le this continuous_const
      have h2 : IsClosed (Set.Icc (0:ℝ) r) := isClosed_Icc
      exact IsClosed.inter h1 h2
    -- K is bounded since it's contained in [0, r]
    have hK_bounded : Bornology.IsBounded K := by
      -- K is a subset of the bounded interval [0, r]
      have h_subset : K ⊆ Set.Icc 0 r := fun y hy => hy.2
      exact Bornology.IsBounded.subset (Metric.isBounded_Icc 0 r) h_subset
    -- In ℝ, closed and bounded implies compact
    -- Use the fact that K is a subset of a compact interval
    have hK_subset : K ⊆ Set.Icc (w - r/4) (w + r) := by
      intro y hy
      simp [Set.mem_Icc]
      have hy_interval : y ∈ Set.Icc 0 r := hy.2
      have hy_near : |y - w| ≤ r/8 := hy.1
      simp [Set.mem_Icc] at hy_interval
      constructor
      · have : w - r/8 ≤ y := by linarith [abs_sub_le_iff.mp hy_near]
        linarith
      · have : y ≤ w + r/8 := by linarith [abs_sub_le_iff.mp hy_near]
        linarith [hy_interval.2]
    exact IsCompact.of_isClosed_subset isCompact_Icc hK_closed hK_subset

  -- Cover K by the neighborhoods from h_local
  have h_cover : ∀ y ∈ K, ∃ α > 0, ∃ β > 0, ∀ y' h,
      |y' - y| < α → 0 < h → h < β → quotient_function φ s y' h ≤ ε := by
    intros y hy
    apply h_local
    · exact hy.2
    · have : |y - w| ≤ r/8 := hy.1
      linarith

  -- Extract uniform bounds using the fact that w ∈ K
  -- First verify w ∈ K
  have hw_in_K : w ∈ K := by
    constructor
    · norm_num
      exact le_of_lt (by linarith [hr] : 0 < r/8)
    · exact hw

  -- Since h_cover gives us local bounds for each point in K,
  -- and w ∈ K, we can use the bounds at w
  obtain ⟨α_w, hα_w_pos, β_w, hβ_w_pos, h_w_control⟩ := h_cover w hw_in_K

  -- Choose ρ_w = α_w/2 and δ_w = β_w
  use min (α_w/2) (r/16)
  constructor
  · exact lt_min (half_pos hα_w_pos) (by linarith [hr] : 0 < r/16)
  use β_w
  constructor
  · exact hβ_w_pos

  intros y h hy_near hh_pos hh_small

  -- Since |y - w| < min(α_w/2, r/16) ≤ α_w/2, we have y close to w
  -- and we can apply the local control at w
  have hy_close_to_w : |y - w| < α_w := by
    have : min (α_w/2) (r/16) ≤ α_w/2 := min_le_left _ _
    linarith [hy_near, this]

  exact h_w_control y h hy_close_to_w hh_pos hh_small

/-- **Lemma U2**: Directed two-point control from U1
    From uniform bounds on the quotient, get the two-point estimate. -/
lemma lemma_U2_directed_two_point
    {w : ℝ} {ρ_w δ_w ε : ℝ}
    (h_uniform : ∀ y h, |y - w| < ρ_w → 0 < h → h < δ_w → quotient_function φ s y h ≤ ε) :
    ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      |y - w| < ρ_w → |z - w| < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) := by
  intros y z hy hz hyz hy_near hz_near hdiff

  by_cases h_eq : y = z
  · rw [h_eq]
    simp
  · -- If y < z, apply the uniform bound
    have h_pos : 0 < z - y := by
      exact sub_pos.mpr (lt_of_le_of_ne hyz h_eq)

    -- Set h = z - y
    let h := z - y

    -- Apply h_uniform with y and h
    have h_bound : quotient_function φ s y h ≤ ε := by
      apply h_uniform
      · exact hy_near
      · exact h_pos
      · exact hdiff

    -- Unfold the definition to get the result
    unfold quotient_function at h_bound

    -- Note that y + h = y + (z - y) = z
    have h_eq_z : y + h = z := by
      simp only [h]
      ring
    rw [h_eq_z] at h_bound

    -- Now h_bound says: (φ (s + z) - φ (s + y)) / (z - y) ≤ ε
    -- Multiply both sides by (z - y) which is positive
    calc φ (s + z) - φ (s + y)
        = (z - y) * ((φ (s + z) - φ (s + y)) / (z - y)) := by field_simp [ne_of_gt h_pos]
      _ ≤ (z - y) * ε := mul_le_mul_of_nonneg_left h_bound (le_of_lt h_pos)
      _ = ε * (z - y) := mul_comm (z - y) ε

/-- **Lemma U3**: Metric form equivalence
    On ℝ, |y - w| < ρ is equivalent to dist y w < ρ. -/
lemma lemma_U3_metric_form (y w ρ : ℝ) :
    |y - w| < ρ ↔ dist y w < ρ := by
  rw [Real.dist_eq]

/-- For y ≤ z, dist y z = z - y -/
lemma dist_eq_sub_of_le' {y z : ℝ} (h : y ≤ z) : dist y z = z - y := by
  rw [Real.dist_eq]
  rw [abs_sub_comm]
  exact abs_of_nonneg (sub_nonneg.mpr h)

/-- **Main Theorem**: Directed two-point local control with uniform bounds
    Combining U1, U2, and U3 to get the desired control around w. -/
theorem directed_two_point_local_uniform
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      dist y w < ρ_w → dist z w < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) := by
  -- Apply U1 to get uniform bounds
  obtain ⟨ρ_w, hρ_pos, δ_w, hδ_pos, h_uniform⟩ :=
    lemma_U1_parametric_uniformization hw hr hDini hUSC ε hε

  use ρ_w, hρ_pos, δ_w, hδ_pos

  intros y z hy hz hyz hy_near hz_near hdiff

  -- Apply U2 (which expects absolute value form)
  -- lemma_U3_metric_form says |y - w| < ρ ↔ dist y w < ρ
  have hy_abs : |y - w| < ρ_w := (lemma_U3_metric_form y w ρ_w).mpr hy_near
  have hz_abs : |z - w| < ρ_w := (lemma_U3_metric_form z w ρ_w).mpr hz_near
  exact lemma_U2_directed_two_point h_uniform y z hy hz hyz hy_abs hz_abs hdiff

/-- Alternative version using absolute values directly -/
theorem directed_two_point_local_abs
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      |y - w| < ρ_w → |z - w| < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) := by
  -- Get the metric version
  obtain ⟨ρ_w, hρ_pos, δ_w, hδ_pos, h_control⟩ :=
    directed_two_point_local_uniform hw hr hDini hUSC ε hε

  use ρ_w, hρ_pos, δ_w, hδ_pos

  intros y z hy hz hyz hy_near hz_near hdiff

  -- Convert to metric form and apply
  apply h_control y z hy hz hyz
  · rw [← lemma_U3_metric_form]; exact hy_near
  · rw [← lemma_U3_metric_form]; exact hz_near
  · exact hdiff

end UniformizationLemmas

end Frourio
