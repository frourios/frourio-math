import Frourio.Analysis.EVI.EVICore0
import Frourio.Analysis.EVI.Lebesgue.Lebesgue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

/-!
# Oriented (Directed) Lebesgue Number Lemmas

This file implements the oriented versions of the Lebesgue number lemma for
two-point local control. These lemmas handle the
case where we have directional constraints (y ≤ z) in addition to distance bounds.

## Main definitions

* `OrientedProductSpace`: The space K = {(y,z) ∈ I×I | y ≤ z}

## Main results

* `oriented_lebesgue_from_two_point_local`: Lebesgue number for oriented two-point cover
* `oriented_uniform_small_interval_control`: Uniform control on small oriented intervals
* `dist_eq_sub_of_le`: In ℝ, if y ≤ z then dist y z = z - y
-/

namespace Frourio

open Filter Topology Metric

section OrientedLebesgue

variable {φ : ℝ → ℝ} {s r ε : ℝ}

/-- **L1 Helper**: For a two-point set {y,z} in a metric space,
    HasSmallDiam {y,z} L iff dist y z < L -/
lemma two_point_hasSmallDiam_iff {X : Type*} [PseudoMetricSpace X] {y z : X} {L : ℝ}
    (hL : 0 < L) : HasSmallDiam ({y, z} : Set X) L ↔ dist y z < L := by
  constructor
  · intro h
    exact h y z (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · intro hdist
    intros u v hu hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rw [dist_self]; exact hL
    · exact hdist
    · rw [dist_comm]; exact hdist
    · rw [dist_self]; exact hL

/-- **Lemma L1**: Two-Point Lebesgue Number Lemma
    Given a subset form Lebesgue lemma, we can derive a two-point version
    that directly gives membership instead of subset inclusion -/
lemma two_point_lebesgue {ι : Type*} [Nonempty ι] {K : Set ℝ}
    (hK : IsCompact K) {U : ι → Set ℝ} (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ L > 0, ∀ y z, y ∈ K → z ∈ K → dist y z < L →
      ∃ i, y ∈ U i ∧ z ∈ U i := by
  -- Get Lebesgue number from the existing lemma
  obtain ⟨L, hL_pos, hLeb⟩ := lebesgue_number_exists hK hU hcover
  use L, hL_pos
  intros y z hy hz hdist
  -- Apply subset form to the two-point set
  let A : Set ℝ := {y, z}
  have hA_sub : A ⊆ K := by
    intro t ht
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hy
    · exact hz
  have hA_small : HasSmallDiam A L := by
    intros u v hu hv
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rw [dist_self]; exact hL_pos
    · exact hdist
    · rw [dist_comm]; exact hdist
    · rw [dist_self]; exact hL_pos
  -- Get the index i such that A ⊆ U i
  obtain ⟨i, hAin⟩ := hLeb.2 A hA_sub hA_small
  -- Extract memberships
  use i
  constructor
  · exact hAin (Set.mem_insert _ _)
  · exact hAin (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The oriented product space K = {(y,z) ∈ I×I | y ≤ z} -/
def OrientedProductSpace (r : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ Set.Icc 0 r ∧ p.2 ∈ Set.Icc 0 r ∧ p.1 ≤ p.2}

/-- **Additional Lemma 3**: In ℝ, if y ≤ z then dist y z = z - y -/
lemma dist_eq_sub_of_le {y z : ℝ} (h : y ≤ z) : dist y z = z - y := by
  rw [dist_comm, Real.dist_eq]
  exact abs_of_nonneg (sub_nonneg.mpr h)

/-- **Additional Lemma 1**: Oriented Lebesgue from Two-Point Local Control
    Given oriented two-point local control, there exists a Lebesgue number L > 0
    such that any pair (y,z) with y ≤ z and dist y z < L is contained in some
    local control neighborhood. -/
theorem oriented_lebesgue_from_two_point_local
    (hr : 0 < r)
    (h_local : ∀ w ∈ Set.Icc 0 r, ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      dist y w < ρ_w → dist z w < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → dist y z < L →
      ∃ w ∈ Set.Icc 0 r, ∃ δ_w > 0,
        dist y w < δ_w ∧ dist z w < δ_w ∧
        φ (s + z) - φ (s + y) ≤ ε * (z - y) := by
  classical
  -- Extract local radii and length bounds at each w
  choose ρ hρ_pos δ hδ_pos h_control using h_local
  -- Define index type and an open cover of the interval I = [0,r]
  let ι := {w : ℝ // w ∈ Set.Icc 0 r}
  let radius : ι → ℝ := fun i => min (ρ i.1 i.2 / 2) (δ i.1 i.2 / 2)
  have hrad_pos : ∀ i : ι, 0 < radius i := by
    intro i
    have h1 : 0 < ρ i.1 i.2 / 2 := by
      have := hρ_pos i.1 i.2; linarith
    have h2 : 0 < δ i.1 i.2 / 2 := by
      have := hδ_pos i.1 i.2; linarith
    exact lt_min_iff.mpr ⟨h1, h2⟩
  let U : ι → Set ℝ := fun i => Metric.ball i.1 (radius i)
  have hUopen : ∀ i, IsOpen (U i) := fun _ => isOpen_ball
  -- Cover: every x ∈ I lies in its own ball centered at x
  have hcover : Set.Icc 0 r ⊆ ⋃ i : ι, U i := by
    intro x hx
    refine Set.mem_iUnion.mpr ?_
    refine ⟨⟨x, hx⟩, ?_⟩
    have : 0 < radius ⟨x, hx⟩ := hrad_pos ⟨x, hx⟩
    simp [U, Metric.mem_ball, dist_self, this]
  -- Apply two-point Lebesgue lemma directly
  haveI : Nonempty ι := ⟨⟨0, by simp [Set.mem_Icc, le_of_lt hr]⟩⟩
  obtain ⟨L, hLpos, hLeb⟩ := two_point_lebesgue isCompact_Icc hUopen hcover
  refine ⟨L, hLpos, ?_⟩
  intro y z hy hz hyz hdist
  -- Apply two-point lemma to get both y and z in some U i
  obtain ⟨i, hy_in_U, hz_in_U⟩ := hLeb y z hy hz hdist
  -- Extract that y,z are in ball(i.1, radius i)
  have hy_in : dist y i.1 < radius i := by simp [U, Metric.mem_ball] at hy_in_U; exact hy_in_U
  have hz_in : dist z i.1 < radius i := by simp [U, Metric.mem_ball] at hz_in_U; exact hz_in_U
  -- Define witnesses
  refine ⟨i.1, i.2, min (ρ i.1 i.2) (δ i.1 i.2), ?_, ?_, ?_, ?_⟩
  · -- positivity of δ_w
    have hρ : 0 < ρ i.1 i.2 := hρ_pos i.1 i.2
    have hδ : 0 < δ i.1 i.2 := hδ_pos i.1 i.2
    exact lt_min hρ hδ
  · -- dist y w < δ_w
    have : radius i ≤ min (ρ i.1 i.2) (δ i.1 i.2) := by
      have hρ_half : ρ i.1 i.2 / 2 ≤ ρ i.1 i.2 := by
        have := hρ_pos i.1 i.2
        linarith
      have hδ_half : δ i.1 i.2 / 2 ≤ δ i.1 i.2 := by
        have := hδ_pos i.1 i.2
        linarith
      exact min_le_min hρ_half hδ_half
    exact lt_of_lt_of_le hy_in this
  · -- dist z w < δ_w
    have : radius i ≤ min (ρ i.1 i.2) (δ i.1 i.2) := by
      have hρ_half : ρ i.1 i.2 / 2 ≤ ρ i.1 i.2 := by
        have := hρ_pos i.1 i.2
        linarith
      have hδ_half : δ i.1 i.2 / 2 ≤ δ i.1 i.2 := by
        have := hδ_pos i.1 i.2
        linarith
      exact min_le_min hρ_half hδ_half
    exact lt_of_lt_of_le hz_in this
  · -- Apply local control at center w = i.1
    -- First, show the premises of h_control
    have hy_lt_rhalf : dist y i.1 < ρ i.1 i.2 / 2 :=
      lt_of_lt_of_le hy_in (min_le_left _ _)
    have hz_lt_rhalf : dist z i.1 < ρ i.1 i.2 / 2 :=
      lt_of_lt_of_le hz_in (min_le_left _ _)
    have hhalf_lt_ρ : ρ i.1 i.2 / 2 < ρ i.1 i.2 := by
      have := hρ_pos i.1 i.2; linarith
    have hdist_yw : dist y i.1 < ρ i.1 i.2 := lt_trans hy_lt_rhalf hhalf_lt_ρ
    have hdist_zw : dist z i.1 < ρ i.1 i.2 := lt_trans hz_lt_rhalf hhalf_lt_ρ
    -- Length bound: z - y < δ i.1 i.2
    have hdist_yz_lt : dist y z < (radius i) + (radius i) := by
      have h1 : dist y z ≤ dist y i.1 + dist i.1 z := dist_triangle y i.1 z
      have h2 : dist i.1 z = dist z i.1 := dist_comm i.1 z
      rw [h2] at h1
      exact lt_of_le_of_lt h1 (add_lt_add hy_in hz_in)
    have hsum_le_delta : (radius i) + (radius i) ≤ δ i.1 i.2 := by
      have hr_le : radius i ≤ δ i.1 i.2 / 2 := min_le_right _ _
      have hsum : (radius i) + (radius i) ≤ δ i.1 i.2 / 2 + δ i.1 i.2 / 2 := add_le_add hr_le hr_le
      have hadd : δ i.1 i.2 / 2 + δ i.1 i.2 / 2 ≤ δ i.1 i.2 := by linarith
      exact le_trans hsum hadd
    have hlen : z - y < δ i.1 i.2 := by
      have : z - y < (radius i) + (radius i) := by
        simp only [dist_eq_sub_of_le hyz] at hdist_yz_lt; exact hdist_yz_lt
      exact lt_of_lt_of_le this hsum_le_delta
    -- Now apply the local inequality
    exact h_control i.1 i.2 y z hy hz hyz hdist_yw hdist_zw hlen

/-- **Additional Lemma 2**: Oriented Uniform Small-Interval Control
    A corollary that directly gives uniform control on small oriented intervals. -/
theorem oriented_uniform_small_interval_control
    (hr : 0 < r)
    (h_local : ∀ w ∈ Set.Icc 0 r, ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      dist y w < ρ_w → dist z w < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) := by
  -- Get the Lebesgue number from the previous theorem
  obtain ⟨L, hL_pos, hL_prop⟩ := oriented_lebesgue_from_two_point_local hr h_local

  use L, hL_pos
  intros y z hy hz hyz hdiff

  -- Convert z - y < L to dist y z < L using the 1D bridge lemma
  have hdist : dist y z < L := by
    rw [dist_eq_sub_of_le hyz]
    exact hdiff

  -- Apply the Lebesgue property
  obtain ⟨w, hw, δ_w, hδ_w_pos, _, _, h_ineq⟩ := hL_prop y z hy hz hyz hdist

  exact h_ineq

end OrientedLebesgue

end Frourio
