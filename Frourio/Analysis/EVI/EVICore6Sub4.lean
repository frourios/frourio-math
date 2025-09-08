import Frourio.Analysis.EVI.EVICore0
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Partition Telescoping and Uniform Small-Interval Bounds

This file implements the lemmas from paper8.md for removing the sorries in
`global_evaluation_from_partition` in EVICore6.lean.

## Main results

* `find_fine_partition`: Lemma P0 - Find a partition with step size < L
* `partition_geometry_range`: Lemma P1 - Partition points are in [0,r]
* `partition_geometry_monotone`: Lemma P1 - Partition is monotone with equal steps
* `telescoping_identity`: Lemma T1 - Telescoping sum identity
* `per_segment_bound`: Lemma U1 - Bound on each segment from uniform control
* `sum_per_segment_bounds`: Lemma S1 - Sum of per-segment bounds
* `global_evaluation_via_partition`: Main proposition - Global bound from partition

-/

namespace Frourio

section PartitionTelescoping

variable {φ : ℝ → ℝ} {s r ε L : ℝ}

/-- The i-th point of the equi-partition of [0,r] with N parts -/
noncomputable def partition_point (r : ℝ) (N : ℕ) (i : ℕ) : ℝ := (i : ℝ) * r / N

/-- The shifted partition point S_i = s + t_i -/
noncomputable def shifted_partition_point (s r : ℝ) (N : ℕ) (i : ℕ) : ℝ :=
  s + partition_point r N i

/-- **Lemma P0**: Find a fine partition
    If r > 0 and L > 0, then there exists N ∈ ℕ, N ≥ 1, such that r/N < L. -/
theorem find_fine_partition (hr : 0 < r) (hL : 0 < L) :
    ∃ N : ℕ, 0 < N ∧ r / (N : ℝ) < L := by
  -- Take N = ⌈r/L⌉ + 1
  use ⌈r / L⌉₊ + 1
  constructor
  · simp
  · have h_ceil : (⌈r / L⌉₊ : ℝ) ≥ r / L := Nat.le_ceil _
    have h_pos : 0 < ((⌈r / L⌉₊ + 1) : ℝ) := by
      have : (0 : ℝ) < ⌈r / L⌉₊ := by
        rw [Nat.cast_pos]
        exact Nat.ceil_pos.mpr (div_pos hr hL)
      linarith
    calc r / (↑(⌈r / L⌉₊ + 1))
        < r / (r / L) := by
          apply div_lt_div_of_pos_left hr
          · exact div_pos hr hL
          · have : r / L < ↑(⌈r / L⌉₊ + 1) := by
              have h1 : ⌈r / L⌉₊ < r / L + 1 := Nat.ceil_lt_add_one (le_of_lt (div_pos hr hL))
              simp only [Nat.cast_add, Nat.cast_one]
              linarith [h_ceil, h1]
            exact this
      _ = L := by field_simp

/-- **Lemma P1 (Range)**: Partition points are in [0,r]
    For all i = 0,...,N, we have 0 ≤ t_i ≤ r. -/
theorem partition_geometry_range (r : ℝ) (N : ℕ) (hN : 0 < N) (hr : 0 ≤ r) (i : ℕ) (hi : i ≤ N) :
    0 ≤ partition_point r N i ∧ partition_point r N i ≤ r := by
  unfold partition_point
  constructor
  · apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg i) hr
    · exact Nat.cast_nonneg N
  · calc partition_point r N i = (i : ℝ) * r / N := rfl
        _ ≤ (N : ℝ) * r / N := by
            apply div_le_div_of_nonneg_right
            · apply mul_le_mul_of_nonneg_right
              · exact Nat.cast_le.mpr hi
              · exact hr
            · exact Nat.cast_nonneg N
        _ = r := by
            have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
            field_simp [this]

/-- **Lemma P1 (Monotone)**: Partition is monotone with equal steps
    For all i = 0,...,N-1, we have t_i ≤ t_{i+1} and t_{i+1} - t_i = r/N. -/
theorem partition_geometry_monotone (r : ℝ) (N : ℕ) (hr : 0 ≤ r)
    (i : ℕ) :
    partition_point r N i ≤ partition_point r N (i + 1) ∧
    partition_point r N (i + 1) - partition_point r N i = r / N := by
  unfold partition_point
  constructor
  · -- Show t_i ≤ t_{i+1}
    apply div_le_div_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right
      · norm_cast
        exact Nat.le_succ i
      · exact hr
    · exact Nat.cast_nonneg N
  · -- Show t_{i+1} - t_i = r/N
    have : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by simp only [Nat.cast_add, Nat.cast_one]
    rw [this]
    ring

/-- Helper lemma: Pure telescoping identity -/
private lemma telescoping_sum_helper (f : ℕ → ℝ) (n : ℕ) :
    (Finset.range n).sum (fun i => f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [ih]
    ring

/-- **Lemma T1**: Telescoping identity
    For any function g : ℝ → ℝ and S_i := s + t_i,
    ∑_{i=0}^{N-1} (g(S_{i+1}) - g(S_i)) = g(S_N) - g(S_0) = g(s + r) - g(s). -/
theorem telescoping_identity (g : ℝ → ℝ) (s r : ℝ) (N : ℕ) (hN : 0 < N) :
    (Finset.range N).sum (fun i => g (shifted_partition_point s r N (i + 1)) -
                                   g (shifted_partition_point s r N i)) =
    g (s + r) - g s := by
  -- Direct proof using telescoping
  have h1 : g (shifted_partition_point s r N N) = g (s + r) := by
    unfold shifted_partition_point partition_point
    have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
    calc g (s + (N : ℝ) * r / N) = g (s + ((N : ℝ) * r / N)) := rfl
        _ = g (s + r) := by field_simp [hN_ne]
  have h2 : g (shifted_partition_point s r N 0) = g s := by
    unfold shifted_partition_point partition_point
    simp
  -- The sum telescopes
  -- We use the fact that this is a telescoping sum where consecutive terms cancel
  calc (Finset.range N).sum (fun i =>
         g (shifted_partition_point s r N (i + 1)) - g (shifted_partition_point s r N i))
      = g (shifted_partition_point s r N N) - g (shifted_partition_point s r N 0) := by
          -- Apply the telescoping helper lemma
          exact telescoping_sum_helper (fun i => g (shifted_partition_point s r N i)) N
    _ = g (s + r) - g s := by rw [h1, h2]

/-- **Lemma U1**: Per-segment bound from uniform control
    Assume the uniform small-interval control on [0,r] with parameter L.
    If N ≥ 1 and r/N < L, then for all i = 0,...,N-1,
    φ(s + t_{i+1}) - φ(s + t_i) ≤ ε(t_{i+1} - t_i) = ε(r/N). -/
theorem per_segment_bound
    (h_control : ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
                   φ (s + z) - φ (s + y) ≤ ε * (z - y))
    (N : ℕ) (hN : 0 < N) (hr : 0 < r) (hL : r / N < L) (i : ℕ) (hi : i < N) :
    φ (shifted_partition_point s r N (i + 1)) - φ (shifted_partition_point s r N i) ≤
    ε * (r / N) := by
  unfold shifted_partition_point
  -- Apply h_control with y = t_i and z = t_{i+1}
  have h_apply := h_control (partition_point r N i) (partition_point r N (i + 1))
  -- Verify the conditions
  have h_yi : partition_point r N i ∈ Set.Icc 0 r := by
    apply Set.mem_Icc.mpr
    exact partition_geometry_range r N hN (le_of_lt hr) i (le_of_lt hi)
  have h_zi : partition_point r N (i + 1) ∈ Set.Icc 0 r := by
    apply Set.mem_Icc.mpr
    exact partition_geometry_range r N hN (le_of_lt hr) (i + 1) (Nat.succ_le_of_lt hi)
  have h_le : partition_point r N i ≤ partition_point r N (i + 1) := by
    exact (partition_geometry_monotone r N (le_of_lt hr) i).1
  have h_diff : partition_point r N (i + 1) - partition_point r N i < L := by
    rw [(partition_geometry_monotone r N (le_of_lt hr) i).2]
    exact hL
  -- Apply the control
  have h_bound := h_apply h_yi h_zi h_le h_diff
  -- Simplify using the fact that t_{i+1} - t_i = r/N
  rw [(partition_geometry_monotone r N (le_of_lt hr) i).2] at h_bound
  exact h_bound

/-- **Lemma S1**: Summing per-segment bounds
    Under the hypotheses of U1,
    ∑_{i=0}^{N-1} (φ(s + t_{i+1}) - φ(s + t_i)) ≤ ε ∑_{i=0}^{N-1} (t_{i+1} - t_i) = εr. -/
theorem sum_per_segment_bounds
    (h_control : ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
                   φ (s + z) - φ (s + y) ≤ ε * (z - y))
    (N : ℕ) (hN : 0 < N) (hr : 0 < r) (hL : r / N < L) :
    (Finset.range N).sum (fun i =>
      φ (shifted_partition_point s r N (i + 1)) - φ (shifted_partition_point s r N i)) ≤
    ε * r := by
  -- Apply per_segment_bound to each term
  have h_bound : ∀ i ∈ Finset.range N,
      φ (shifted_partition_point s r N (i + 1)) - φ (shifted_partition_point s r N i) ≤
      ε * (r / N) := by
    intros i hi
    simp only [Finset.mem_range] at hi
    exact per_segment_bound h_control N hN hr hL i hi
  -- Sum the bounds
  calc (Finset.range N).sum (fun i =>
         φ (shifted_partition_point s r N (i + 1)) - φ (shifted_partition_point s r N i))
      ≤ (Finset.range N).sum (fun i => ε * (r / N)) := by
          apply Finset.sum_le_sum
          exact h_bound
    _ = N * (ε * (r / N)) := by simp [Finset.sum_const, Finset.card_range]
    _ = ε * r := by
        have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
        field_simp [hN_ne]

/-- **Main Proposition**: Global evaluation via partition
    Assume the uniform small-interval control on [0,r] with constant L > 0.
    Pick N ≥ 1 with r/N < L. Then φ(s + r) ≤ φ(s) + εr. -/
theorem global_evaluation_via_partition
    (h_control : ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
                   φ (s + z) - φ (s + y) ≤ ε * (z - y))
    (hr : 0 < r) (hL : 0 < L) :
    φ (s + r) ≤ φ s + ε * r := by
  -- Find a fine partition
  obtain ⟨N, hN_pos, hN_fine⟩ := find_fine_partition hr hL
  -- Apply telescoping identity
  have h_telescope := telescoping_identity φ s r N hN_pos
  -- Apply sum of per-segment bounds
  have h_sum_bound := sum_per_segment_bounds h_control N hN_pos hr hN_fine
  -- Combine
  have h_diff : φ (s + r) - φ s ≤ ε * r := by
    calc φ (s + r) - φ s
        = (Finset.range N).sum (fun i =>
            φ (shifted_partition_point s r N (i + 1)) - φ (shifted_partition_point s r N i)) :=
          by rw [← h_telescope]
      _ ≤ ε * r := h_sum_bound
  -- Rearrange
  linarith [h_diff]

end PartitionTelescoping

end Frourio
