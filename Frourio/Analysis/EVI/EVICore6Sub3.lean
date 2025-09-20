import Frourio.Analysis.EVI.EVICore0
import Frourio.Analysis.EVI.EVICore6Sub1
import Frourio.Analysis.EVI.EVICore6Sub2
import Frourio.Analysis.Lebesgue.OrientedLebesgue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Frourio

open Filter Topology Metric

section CompactUniformization

variable {φ : ℝ → ℝ} {s r ε : ℝ}

/-- **Step 1 - Lemma R0**: Right ε–δ from Dini
    If DiniUpperE φ t ≤ 0 and ε > 0, then there exists δ > 0 such that
    for all 0 < h < δ, we have φ(t+h) - φ(t) ≤ ε·h. -/
theorem right_epsilon_delta_at_point (t : ℝ)
    (hDini : DiniUpperE φ t ≤ 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → φ (t + h) - φ t ≤ ε * h :=
  -- Direct application of the result from EVISub1
  local_control_from_DiniUpperE_right_clean t hDini ε hε

/-- **Step 2 - Lemma U1**: Uniformization near w
    Given R0 at each point near w and upper semicontinuity of the quotient function,
    we get uniform bounds near w. -/
theorem uniformization_near_center
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y h,
      |y - w| < ρ_w → 0 < h → h < δ_w →
      quotient_function φ s y h ≤ ε :=
  -- Direct application of the result from EVISub2
  lemma_U1_parametric_uniformization hw hr hDini hUSC ε hε

/-- **Step 3 - Lemma U2**: Directed two-point control
    From uniform bounds on the quotient, get the two-point estimate. -/
theorem directed_two_point_control_from_uniformization
    {w : ℝ} {ρ_w δ_w : ℝ}
    (h_uniform : ∀ y h, |y - w| < ρ_w → 0 < h → h < δ_w →
      quotient_function φ s y h ≤ ε) :
    ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      |y - w| < ρ_w → |z - w| < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) :=
  -- Direct application of the result from EVISub2
  lemma_U2_directed_two_point h_uniform

/-- Metric bridge: Convert between absolute value and distance -/
lemma metric_bridge (y w ρ : ℝ) : |y - w| < ρ ↔ dist y w < ρ :=
  lemma_U3_metric_form y w ρ

/-- For y ≤ z, dist y z = z - y -/
lemma dist_eq_diff_for_ordered {y z : ℝ} (h : y ≤ z) : dist y z = z - y :=
  dist_eq_sub_of_le' h

/-- **Step 4 - Lemma L1**: Lebesgue-uniform small-interval control -/
theorem lebesgue_uniform_small_interval
    (hr : 0 < r)
    (h_local : ∀ w ∈ Set.Icc 0 r, ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      dist y w < ρ_w → dist z w < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) :=
  -- Apply the Lebesgue number lemma from OrientedLebesgue
  oriented_uniform_small_interval_control hr h_local

/-- **Main Theorem**: Complete Lebesgue number for directed two-point cover
    Combining all steps to provide the complete solution. -/
theorem lebesgue_number_for_directed_cover_complete
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) := by
  -- Step 1-3: For each w, get local control using uniformization
  have h_local : ∀ w ∈ Set.Icc 0 r, ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      dist y w < ρ_w → dist z w < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) := by
    intro w hw
    -- Apply uniformization near w (Steps 1-2)
    obtain ⟨ρ_w, hρ_pos, δ_w, hδ_pos, h_uniform⟩ :=
      uniformization_near_center hw hr hDini (hUSC w hw) hε
    -- Convert to directed two-point control (Step 3)
    use ρ_w, hρ_pos, δ_w, hδ_pos
    intros y z hy hz hyz hy_near hz_near hdiff
    -- Convert from metric to absolute value form
    have hy_abs : |y - w| < ρ_w := (metric_bridge y w ρ_w).mpr hy_near
    have hz_abs : |z - w| < ρ_w := (metric_bridge z w ρ_w).mpr hz_near
    -- Apply directed two-point control
    exact directed_two_point_control_from_uniformization h_uniform
      y z hy hz hyz hy_abs hz_abs hdiff

  -- Step 4: Apply Lebesgue number lemma to get uniform L
  exact lebesgue_uniform_small_interval hr h_local

/-- Alternative formulation matching EVICore6's signature exactly -/
theorem lebesgue_number_for_directed_cover_fixed
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) :=
  lebesgue_number_for_directed_cover_complete hDini hUSC hε hr

end CompactUniformization

end Frourio
