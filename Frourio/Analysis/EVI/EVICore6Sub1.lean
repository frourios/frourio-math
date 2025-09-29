import Frourio.Analysis.EVI.EVICore0
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
# Right-Hand Dini Upper Derivative: ε–δ Extraction and Filter Lemmas

This file implements the minimal analytic lemmas needed for robust proofs of
local control from right-hand Dini upper derivatives.

## Main results

* `lemma_R1_eventually_le_from_limsup`: Eventually ≤ from limsup ≤
* `lemma_R2_right_filter_extraction`: Right-filter ε–δ extraction
* `lemma_R3_ereal_coercion`: EReal coercion simplification (references to Mathlib)
* `lemma_R4_multiply_positive`: Multiply by a positive increment
* `right_epsilon_delta_from_dini_nonpos`: Main corollary combining all lemmas

-/

namespace Frourio

open Filter Topology

section RightDiniLemmas

variable {φ : ℝ → ℝ} {t : ℝ}

/-- **Lemma R1**: Eventually-≤ from limsup ≤
    If limsup f l ≤ c, then for every η > 0, eventually f x ≤ c + η. -/
lemma lemma_R1_eventually_le_from_limsup {α : Type*} {f : α → ℝ} {l : Filter α} {c : ℝ}
    (h : limsup (fun x => (f x : EReal)) l ≤ (c : EReal)) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x in l, f x ≤ c + η := by
  -- Since c < c + η, we have limsup f l < c + η
  have h_lt : limsup (fun x => (f x : EReal)) l < ((c + η) : EReal) := by
    calc limsup (fun x => (f x : EReal)) l
        ≤ (c : EReal) := h
      _ < ((c + η) : EReal) := by
          have : c < c + η := by linarith
          exact EReal.coe_lt_coe_iff.mpr this

  -- By the standard lemma, if limsup < a then eventually f < a
  have h_eventually_lt := Filter.eventually_lt_of_limsup_lt h_lt

  -- Convert from eventually < to eventually ≤
  filter_upwards [h_eventually_lt] with x hx
  -- hx : (f x : EReal) < ((c + η) : EReal)
  -- Convert back to ℝ
  have hx_real : f x < c + η := by
    rw [← EReal.coe_lt_coe_iff]
    exact hx
  exact le_of_lt hx_real

/-- Specialized version with c = 0 for Dini applications -/
lemma lemma_R1_nonpos_special {α : Type*} {f : α → ℝ} {l : Filter α}
    (h : limsup (fun x => (f x : EReal)) l ≤ (0 : EReal)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in l, f x ≤ ε := by
  have := lemma_R1_eventually_le_from_limsup h ε hε
  simp at this
  exact this

/-- **Lemma R2**: Right-filter ε–δ extraction
    If P holds eventually in nhdsWithin 0 (0,+∞), then there exists δ > 0
    such that P h holds for all 0 < h < δ. -/
lemma lemma_R2_right_filter_extraction {P : ℝ → Prop}
    (h : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), P h) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → P h := by
  -- Convert from filter to existence of δ
  simp only [Filter.eventually_iff_exists_mem] at h
  obtain ⟨S, hS_mem, hS_prop⟩ := h
  -- S is in nhdsWithin 0 (Set.Ioi 0), so it contains a neighborhood
  rw [Metric.mem_nhdsWithin_iff] at hS_mem
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := hS_mem
  use δ, hδ_pos
  intros h hh_pos hh_lt
  apply hS_prop
  apply hδ_ball
  constructor
  · simp [Metric.mem_ball, abs_of_pos hh_pos]
    exact hh_lt
  · exact hh_pos

/-- **Lemma R3a**: EReal coercion for < -/
lemma lemma_R3a_coe_lt (x y : ℝ) : (x : EReal) < (y : EReal) ↔ x < y :=
  EReal.coe_lt_coe_iff

/-- **Lemma R3b**: EReal coercion for ≤ -/
lemma lemma_R3b_coe_le (x y : ℝ) : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  EReal.coe_le_coe_iff

/-- **Lemma R4**: Multiply by a positive increment
    If h > 0 and q(h) ≤ ε, then φ(t+h) - φ(t) ≤ ε·h. -/
lemma lemma_R4_multiply_positive {φ : ℝ → ℝ} {t h ε : ℝ} (hh_pos : 0 < h)
    (hq : (φ (t + h) - φ t) / h ≤ ε) :
    φ (t + h) - φ t ≤ ε * h := by
  -- φ(t+h) - φ(t) = h · q(h) by definition
  have h_eq : φ (t + h) - φ t = h * ((φ (t + h) - φ t) / h) := by
    field_simp [ne_of_gt hh_pos]

  -- Apply the inequality
  rw [h_eq]
  calc h * ((φ (t + h) - φ t) / h)
      ≤ h * ε := mul_le_mul_of_nonneg_left hq (le_of_lt hh_pos)
    _ = ε * h := mul_comm h ε

/-- **Corollary**: Right ε–δ from DiniUpperE ≤ 0
    Given DiniUpperE φ t ≤ 0 and ε > 0, there exists δ > 0 such that
    for all 0 < h < δ, we have φ(t+h) - φ(t) ≤ ε·h. -/
theorem right_epsilon_delta_from_dini_nonpos
    (hDini : DiniUpperE φ t ≤ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → φ (t + h) - φ t ≤ ε * h := by
  -- Define the quotient function
  let q := fun h : ℝ => (φ (t + h) - φ t) / h

  -- DiniUpperE is the limsup of q along the right filter
  unfold DiniUpperE at hDini

  -- Apply R1 to get eventual bound
  have h_eventually : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), q h ≤ ε := by
    exact lemma_R1_nonpos_special hDini ε hε

  -- Apply R2 to extract δ
  obtain ⟨δ, hδ_pos, hδ_prop⟩ := lemma_R2_right_filter_extraction h_eventually

  use δ, hδ_pos
  intros h hh_pos hh_lt

  -- Get q(h) ≤ ε
  have hq : q h ≤ ε := hδ_prop h hh_pos hh_lt

  -- Apply R4 to get the final result
  exact lemma_R4_multiply_positive hh_pos hq

/-- Convenience wrapper that matches the signature in EVICore6 -/
theorem local_control_from_DiniUpperE_right_clean
    (t : ℝ) (hDini : DiniUpperE φ t ≤ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → φ (t + h) - φ t ≤ ε * h :=
  right_epsilon_delta_from_dini_nonpos hDini ε hε

end RightDiniLemmas

end Frourio
