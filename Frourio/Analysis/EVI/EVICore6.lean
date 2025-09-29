import Frourio.Analysis.EVI.EVICore0
import Frourio.Analysis.EVI.EVICore1
import Frourio.Analysis.EVI.EVICore6Sub1
import Frourio.Analysis.EVI.EVICore6Sub2
import Frourio.Analysis.EVI.EVICore6Sub3
import Frourio.Analysis.EVI.EVICore6Sub4
import Frourio.Analysis.Lebesgue.OrientedLebesgue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Frourio

open Filter Topology

section DirectedTwoPointTheory

variable {φ : ℝ → ℝ} {s r : ℝ} {ε : ℝ}

/-- **Lemma A**: Local control from right-sided Dini upper derivative.
    If `DiniUpperE φ t ≤ 0` and `ε > 0`, then there exists `δ > 0` such that
    for all `0 < h < δ`, we have `φ(t+h) - φ(t) ≤ ε h`. -/
theorem local_control_from_DiniUpperE_right
    (t : ℝ) (hDini : DiniUpperE φ t ≤ 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → φ (t + h) - φ t ≤ ε * h :=
  -- Use the clean implementation from EVISub1
  local_control_from_DiniUpperE_right_clean t hDini ε hε

/-- Version of directed_two_point_local with upper semicontinuity hypothesis -/
theorem directed_two_point_local_with_usc
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      |y - w| < ρ_w → |z - w| < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) :=
  -- Direct application of the theorem from EVISub2
  directed_two_point_local_abs hw hr hDini hUSC ε hε

/-- The directed product space K = {(y,z) ∈ I×I | y ≤ z} with max metric -/
def DirectedProductSpace (r : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ Set.Icc 0 r ∧ p.2 ∈ Set.Icc 0 r ∧ p.1 ≤ p.2}

/-- Max metric on the product space -/
def maxDist (p q : ℝ × ℝ) : ℝ := max |p.1 - q.1| |p.2 - q.2|

/-- **Complete version of Lemma C**: Lebesgue number with upper semicontinuity hypothesis.
    This is the correct formulation with all necessary hypotheses. -/
theorem lebesgue_number_for_directed_cover_with_usc
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) :=
  -- Direct application of the complete theorem from EVISub3
  lebesgue_number_for_directed_cover_complete hDini hUSC hε hr

/-- **Complete version of Proposition D** with upper semicontinuity hypothesis -/
theorem uniform_small_interval_control_with_usc
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) :=
  lebesgue_number_for_directed_cover_with_usc hDini hUSC hε hr

/-- **Corollary**: Global evaluation via finite chain composition (with USC).
    Using partition and telescoping sum, we get φ(s+r) ≤ φ(s) + εr. -/
theorem global_evaluation_from_partition_with_usc
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    φ (s + r) ≤ φ s + ε * r := by
  -- Get the uniform control with Lebesgue number L using upper semicontinuity
  obtain ⟨L, hL_pos, hL_control⟩ := uniform_small_interval_control_with_usc hDini hUSC hε hr
  -- Apply the theorem from EVISub4
  exact global_evaluation_via_partition hL_control hr hL_pos

/-- Complete version with upper semicontinuity hypothesis -/
theorem nonincreasing_of_DiniUpperE_nonpos_right_with_usc
    (hDini : ∀ t, DiniUpperE φ t ≤ 0)
    (hUSC : ∀ s : ℝ, ∀ r > 0, ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀) :
    ∀ s t, s ≤ t → φ t ≤ φ s := by
  intros s t hst
  by_cases h : s = t
  · rw [h]
  · have hst_strict : s < t := lt_of_le_of_ne hst h
    let r := t - s
    have hr_pos : 0 < r := by simp [r]; exact hst_strict
    have : ∀ ε > 0, φ t ≤ φ s + ε * r := by
      intro ε hε
      have hDini_shifted : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0 := by
        intros u hu
        exact hDini (s + u)
      -- Apply the upper semicontinuity hypothesis for the interval [0, r]
      have hUSC_shifted : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
        |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀ := by
        intros w hw y₀ hy₀ h_near
        -- Direct application of hUSC with the specific s and r
        exact hUSC s r hr_pos w hw y₀ hy₀ h_near
      have h_eval := global_evaluation_from_partition_with_usc hDini_shifted hUSC_shifted hε hr_pos
      convert h_eval using 1
      simp [r]
    -- Take limit as ε → 0
    have h_limit : φ t ≤ φ s := by
      by_contra h_neg
      push_neg at h_neg
      let δ := (φ t - φ s) / (2 * r)
      have hδ_pos : 0 < δ := by
        simp [δ]
        have : 0 < φ t - φ s := sub_pos.mpr h_neg
        exact div_pos this (mul_pos (by norm_num : (0 : ℝ) < 2) hr_pos)
      have h_contr := this δ hδ_pos
      have : φ t ≤ φ s + δ * r := h_contr
      have : φ t ≤ φ s + (φ t - φ s) / 2 := by
        convert this using 1
        simp [δ]
        field_simp
        ring
      linarith
    exact h_limit

end DirectedTwoPointTheory

end Frourio
