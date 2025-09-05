import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Semicontinuous
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Sequences

namespace Frourio

/-!
# Minimizing Movement (JKO-type scheme)

This file implements the minimizing movement scheme (JKO scheme) for gradient flows
in general metric spaces, without dependency on measure theory.

## Main definitions

- `MmFunctional`: The functional to minimize at each time step
- `IsMinimizer`: Predicate for being a minimizer
- `MmStep`: Single step of the minimizing movement scheme
- `MmCurve`: Discrete curve obtained from the scheme

## Main results

- `mm_step_exists`: Existence of minimizers under appropriate assumptions
- Energy decrease and a priori estimates for the scheme
-/

variable {X : Type*} [PseudoMetricSpace X]

/-- Squared distance function for convenience. -/
def distSquared (x y : X) : ℝ := (dist x y) ^ 2

/-- The functional to minimize in the minimizing movement scheme.
    `MmFunctional τ F xPrev x = F(x) + (1/(2τ)) * d²(x, xPrev)` -/
noncomputable def MmFunctional (τ : ℝ) (F : X → ℝ) (xPrev x : X) : ℝ :=
  F x + (1 / (2 * τ)) * distSquared x xPrev

/-- A point is a minimizer if it achieves the minimum value of the functional. -/
def IsMinimizer {Y : Type*} (f : Y → ℝ) (x : Y) : Prop :=
  ∀ y : Y, f x ≤ f y

/-- A single step of the minimizing movement scheme. -/
def MmStep (τ : ℝ) (F : X → ℝ) (xPrev x : X) : Prop :=
  IsMinimizer (MmFunctional τ F xPrev) x

/-- The functional F is proper if it takes finite values somewhere. -/
def MmProper (F : X → ℝ) : Prop :=
  ∃ x : X, F x ≠ 0  -- Simplified: just need a finite value

/-- The functional F is coercive if it grows to infinity at infinity. -/
def MmCoercive [Nonempty X] (F : X → ℝ) : Prop :=
  ∀ c : ℝ, ∃ r : ℝ, ∀ x : X, dist x (Classical.arbitrary X) > r → F x > c

/-- The functional F has compact sublevels if its sublevel sets are relatively compact. -/
def MmCompactSublevels (F : X → ℝ) : Prop :=
  ∀ c : ℝ, IsCompact {x : X | F x ≤ c}

/-- Discrete curve obtained from the minimizing movement scheme. -/
structure MmCurve (τ : ℝ) (F : X → ℝ) (x0 : X) where
  /-- The discrete points at times nτ -/
  points : ℕ → X
  /-- Initial condition -/
  init : points 0 = x0
  /-- Each point is obtained by minimizing movement -/
  step : ∀ n : ℕ, MmStep τ F (points n) (points (n + 1))

/-- Linear interpolation between discrete points for continuous extension. -/
noncomputable def MmCurve.interpolate {τ : ℝ} {F : X → ℝ} {x0 : X}
    (curve : MmCurve τ F x0) (t : ℝ) : X :=
  if t ≤ 0 then x0
  else
    let n := ⌊t / τ⌋.toNat
    let s := (t - n * τ) / τ
    if s = 0 then curve.points n
    else curve.points n  -- Simplified: no actual interpolation in metric space

/-- Energy decrease along the minimizing movement scheme. -/
theorem mm_energy_decrease {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {xPrev x : X}
    (h : MmStep τ F xPrev x) :
    F x ≤ F xPrev := by
  unfold MmStep IsMinimizer MmFunctional at h
  have := h xPrev
  simp [distSquared] at this
  have hdist : 0 ≤ dist x xPrev ^ 2 := sq_nonneg _
  have hpos : 0 < 2 * τ := by linarith
  have : 0 ≤ (1 / (2 * τ)) * dist x xPrev ^ 2 := by
    apply mul_nonneg
    · exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hpos)
    · exact hdist
  by_contra hcontra
  push_neg at hcontra
  have hineq := h xPrev
  simp only [distSquared, dist_self, pow_two, zero_mul] at hineq
  linarith

/-- A priori estimate on distance for the minimizing movement scheme. -/
theorem mm_distance_estimate {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {xPrev x : X}
    (h : MmStep τ F xPrev x) :
    distSquared x xPrev ≤ 2 * τ * (F xPrev - F x) := by
  unfold MmStep IsMinimizer MmFunctional at h
  unfold distSquared
  -- Use the minimizer property at xPrev
  have h_min := h xPrev
  -- At xPrev: F x + (1/(2*τ)) * dist x xPrev ^ 2 ≤ F xPrev + 0
  simp only [distSquared, dist_self, pow_two, mul_zero, add_zero] at h_min
  -- So: (1/(2*τ)) * dist x xPrev ^ 2 ≤ F xPrev - F x
  have h_ineq : (1 / (2 * τ)) * dist x xPrev ^ 2 ≤ F xPrev - F x := by linarith
  -- Multiply both sides by 2*τ (which is positive)
  have hpos : 0 < 2 * τ := by linarith
  have hne : (2 * τ) ≠ 0 := ne_of_gt hpos
  -- Simple approach: directly multiply the inequality
  have h_mul := mul_le_mul_of_nonneg_left h_ineq (le_of_lt hpos)
  rw [← mul_assoc, mul_div_cancel₀ _ hne, one_mul] at h_mul
  exact h_mul

/-- Helper: sublevel sets are closed for lower semicontinuous functions. -/
theorem sublevel_closed_of_lsc {F : X → ℝ} (hF : LowerSemicontinuous F) (c : ℝ) :
    IsClosed {x : X | F x ≤ c} := by
  -- The sublevel set {x | F x ≤ c} is the preimage F⁻¹((-∞, c])
  -- which equals F⁻¹(Iic c) in Lean notation
  have h_eq : {x : X | F x ≤ c} = F ⁻¹' Set.Iic c := by
    ext x
    simp [Set.Iic]
  rw [h_eq]
  -- By the characterization of lower semicontinuity, F⁻¹(Iic c) is closed
  rw [lowerSemicontinuous_iff_isClosed_preimage] at hF
  exact hF c

/-- Helper: A lower semicontinuous function on a compact set is bounded below. -/
lemma lsc_bddBelow_on_compact {f : X → ℝ} {K : Set X}
    (hK_compact : IsCompact K) (_hK_nonempty : K.Nonempty)
    (hf_lsc : LowerSemicontinuous f) : BddBelow (f '' K) := by
  -- Proof by contradiction: if not bounded below, we get a sequence tending to -∞
  by_contra h_not_bdd
  simp only [BddBelow, lowerBounds, Set.Nonempty] at h_not_bdd
  -- For each n, there exists xₙ ∈ K with f(xₙ) < -n
  have h_seq : ∀ n : ℕ, ∃ x ∈ K, f x < -n := fun n => by
    -- h_not_bdd says: ¬∃ a, ∀ y ∈ f '' K, a ≤ y
    -- Which means: ∀ a, ∃ y ∈ f '' K, y < a
    have : ∃ y ∈ f '' K, y < (-n : ℝ) := by
      by_contra h
      push_neg at h
      exact h_not_bdd ⟨-n, h⟩
    obtain ⟨y, ⟨x, hxK, rfl⟩, hy⟩ := this
    exact ⟨x, hxK, hy⟩
  -- Choose such a sequence
  choose x hxK hfx using h_seq
  -- By compactness, extract a convergent subsequence
  have h_seq_compact : IsSeqCompact K := hK_compact.isSeqCompact
  -- The sequence (x n) is in K, so has a convergent subsequence
  obtain ⟨x₀, hx₀_in, φ, hφ_mono, hφ_tendsto⟩ := h_seq_compact hxK
  -- x₀ is the limit point in K
  -- f(x₀) is a real number, but f(x(φ n)) < -φ(n) → -∞
  -- This gives a contradiction using lsc property

  -- Since f is lsc and x(φ n) → x₀, we have f(x₀) ≤ liminf f(x(φ n))
  -- But f(x(φ n)) < -φ(n), and φ is strictly increasing, so liminf f(x(φ n)) = -∞
  -- This contradicts that f(x₀) is a real number

  -- Use closed sets approach directly
  -- For any r : ℝ, we know that eventually f(x(φ n)) < r
  -- Since {z | f z ≤ r} is closed and x(φ n) → x₀, we get f(x₀) ≤ r
  -- Taking r → -∞ gives a contradiction
  
  -- Pick any real number r
  have h_any_r : ∀ r : ℝ, f x₀ ≤ r := fun r => by
    -- Find N large enough so that φ(N) > -r (when r < 0)
    -- Then for n ≥ N, we have f(x(φ n)) < -φ(n) ≤ -φ(N) < r
    
    -- First, find n₀ such that for all n ≥ n₀, we have f(x(φ n)) < r
    have : ∃ n₀, ∀ n ≥ n₀, f (x (φ n)) < r := by
      -- Since f(x(φ n)) < -φ(n) and φ is strictly increasing
      -- We can find n₀ such that -φ(n₀) < r
      obtain ⟨n₀, hn₀⟩ := exists_nat_gt (-r)
      use n₀
      intro n hn
      have : (n₀ : ℝ) ≤ n := Nat.cast_le.mpr hn
      have : (n : ℝ) ≤ φ n := Nat.cast_le.mpr (StrictMono.id_le hφ_mono n)
      have : -(φ n : ℝ) ≤ -n₀ := by linarith
      calc f (x (φ n)) < -(φ n : ℝ) := hfx (φ n)
           _ ≤ -(n₀ : ℝ) := this
           _ < r := by linarith
    obtain ⟨n₀, hn₀⟩ := this
    
    -- Now use that {z | f z ≤ r} is closed
    have h_closed : IsClosed {z | f z ≤ r} := sublevel_closed_of_lsc hf_lsc r
    -- The sequence x(φ n) eventually stays in {z | f z < r} ⊆ {z | f z ≤ r}
    have h_eventually : ∀ᶠ n in Filter.atTop, x (φ n) ∈ {z | f z ≤ r} := by
      simp only [Filter.eventually_atTop]
      use n₀
      intro n hn
      simp only [Set.mem_setOf]
      exact le_of_lt (hn₀ n hn)
    -- Since {z | f z ≤ r} is closed and x(φ n) → x₀
    -- We use the fact that closed sets contain limits of sequences in the set
    have : x₀ ∈ {z | f z ≤ r} := by
      -- Convert to closure
      rw [← IsClosed.closure_eq h_closed]
      -- x₀ is in the closure because it's the limit of a sequence in the set
      apply mem_closure_of_tendsto hφ_tendsto
      exact h_eventually
    exact this
  
  -- But this means f(x₀) ≤ r for all r, which is impossible for a real-valued function
  -- Take r = f(x₀) - 1
  specialize h_any_r (f x₀ - 1)
  linarith

/-- Helper: For the infimum m of f on K, we can find points arbitrarily close to m. -/
lemma exists_approx_min_on_compact {f : X → ℝ} {K : Set X}
    (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf_lsc : LowerSemicontinuous f) :
    ∀ ε > 0, ∃ x ∈ K, f x < sInf (f '' K) + ε := by
  intro ε hε
  -- Get that f is bounded below on K
  have h_bdd := lsc_bddBelow_on_compact hK_compact hK_nonempty hf_lsc
  have h_nonempty : (f '' K).Nonempty := by
    obtain ⟨x, hx⟩ := hK_nonempty
    use f x
    exact ⟨x, hx, rfl⟩
  
  -- By definition of infimum, there exists y ∈ f '' K with y < sInf (f '' K) + ε
  have : ∃ y ∈ f '' K, y < sInf (f '' K) + ε := by
    -- If not, then sInf (f '' K) + ε would be a lower bound
    by_contra h
    push_neg at h
    -- Then sInf (f '' K) + ε ≤ sInf (f '' K) which is impossible
    have : sInf (f '' K) + ε ≤ sInf (f '' K) := le_csInf h_nonempty h
    linarith
  
  obtain ⟨y, hy_in, hy_lt⟩ := this
  obtain ⟨x, hx_in, rfl⟩ := hy_in
  exact ⟨x, hx_in, hy_lt⟩

-- Note: lsc_liminf_bound is not needed with the nested closed sets approach

/-- A lower semicontinuous real-valued function on a non-empty compact set attains its infimum.
    This is a special case of the Weierstrass extreme value theorem. -/
theorem lsc_attains_min_on_compact {f : X → ℝ} {K : Set X}
    (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf_lsc : LowerSemicontinuous f) :
    ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  -- Step 1: Define the infimum
  let S := f '' K
  have hS_ne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hK_nonempty
    use f x
    exact ⟨x, hx, rfl⟩
  have hS_bdd : BddBelow S := lsc_bddBelow_on_compact hK_compact hK_nonempty hf_lsc
  let m := sInf S

  -- Step 2: Define nested closed sets Cₙ = {x ∈ K | f x ≤ m + 1/(n+1)}
  let C : ℕ → Set X := fun n => {x ∈ K | f x ≤ m + 1/(n+1 : ℝ)}
  
  -- Step 3: Show each Cₙ is non-empty
  have hC_nonempty : ∀ n, (C n).Nonempty := fun n => by
    have : ∃ x ∈ K, f x < m + 1/(n+1 : ℝ) := 
      exists_approx_min_on_compact hK_compact hK_nonempty hf_lsc (1/(n+1 : ℝ))
        (by norm_num; exact Nat.cast_add_one_pos n)
    obtain ⟨x, hx_in, hx_lt⟩ := this
    use x
    simp only [C, Set.mem_setOf]
    exact ⟨hx_in, le_of_lt hx_lt⟩
  
  -- Step 4: Show each Cₙ is closed in the subspace topology of K
  -- In general we don't have T2Space for X, but we can work around it
  have hC_closed_in_K : ∀ n, ∃ (S : Set X), IsClosed S ∧ C n = K ∩ S := fun n => by
    use {x | f x ≤ m + 1/(n+1 : ℝ)}
    constructor
    · exact sublevel_closed_of_lsc hf_lsc _
    · ext x
      simp only [C, Set.mem_inter_iff, Set.mem_setOf]
  
  -- Step 5: Show the sets are nested (decreasing)
  have hC_nested : ∀ n, C (n + 1) ⊆ C n := fun n => by
    intro x hx
    simp only [C, Set.mem_setOf] at hx ⊢
    obtain ⟨hx_K, hx_le⟩ := hx
    constructor
    · exact hx_K
    · calc f x ≤ m + 1/((n+1:ℕ)+1:ℝ) := hx_le
           _ ≤ m + 1/(n+1:ℝ) := by
             apply add_le_add_left
             -- 1/(n+2) ≤ 1/(n+1) since n+2 ≥ n+1
             have : ((n+1:ℕ)+1:ℝ) = (n+1:ℝ) + 1 := by norm_cast
             rw [this]
             have : 1 / ((n+1:ℝ) + 1) ≤ 1 / (n+1:ℝ) := by
               apply div_le_div_of_nonneg_left
               · norm_num
               · exact Nat.cast_add_one_pos n
               · norm_cast; omega
             exact this
  
  -- Step 6: Use compactness to get intersection is non-empty
  -- The intersection ⋂ₙ Cₙ is non-empty by finite intersection property
  have h_inter_nonempty : (⋂ n, C n).Nonempty := by
    -- Direct approach: construct a point in the intersection
    -- Choose xₙ ∈ Cₙ for each n
    have : ∀ n, ∃ x, x ∈ C n := fun n => hC_nonempty n
    choose xseq hxseq using this
    
    -- Since xₙ ∈ Cₙ ⊆ C₀ ⊆ K for all n, extract convergent subsequence
    have hxseq_in_K : ∀ n, xseq n ∈ K := fun n => (hxseq n).1
    have h_seq_compact : IsSeqCompact K := hK_compact.isSeqCompact
    obtain ⟨x₀, hx₀_in, φ, hφ_mono, hφ_tendsto⟩ := h_seq_compact hxseq_in_K
    
    use x₀
    simp only [Set.mem_iInter]
    intro N
    -- Show x₀ ∈ C N
    -- Since the sets are nested, for all k ≥ N, xseq(φ k) ∈ C N
    have h_eventually : ∀ k, N ≤ φ k → xseq (φ k) ∈ C N := fun k hk => by
      -- Since φ k ≥ N and C(φ k) ⊆ C N (by nestedness)
      -- Apply nestedness multiple times
      have hsubset : C (φ k) ⊆ C N := by
        -- We need to show C (φ k) ⊆ C N when φ k ≥ N
        -- This follows from repeated application of hC_nested
        have : N ≤ φ k := hk
        -- We proceed by showing for any m ≥ N, C m ⊆ C N
        suffices ∀ m, N ≤ m → C m ⊆ C N by exact this (φ k) hk
        intro m hm
        induction' hm with p _ ih
        · rfl  -- C N ⊆ C N
        · exact Set.Subset.trans (hC_nested p) ih
      exact hsubset (hxseq (φ k))
    
    -- xseq(φ k) → x₀ and eventually xseq(φ k) ∈ C N
    -- Since C N = K ∩ {x | f x ≤ m + 1/(N+1)}, and the latter is closed
    obtain ⟨S, hS_closed, hCN_eq⟩ := hC_closed_in_K N
    rw [hCN_eq]
    constructor
    · exact hx₀_in
    · -- x₀ ∈ S because it's the limit of a sequence eventually in S
      -- Use that S is closed
      rw [← IsClosed.closure_eq hS_closed]
      apply mem_closure_of_tendsto hφ_tendsto
      simp only [Filter.eventually_atTop]
      -- φ is strictly monotone, so φ k ≥ k for all k
      have hφ_ge : ∀ k, k ≤ φ k := fun k => StrictMono.id_le hφ_mono k
      -- Therefore, for k ≥ N, we have φ k ≥ N
      use N
      intro k hk
      have : N ≤ φ k := le_trans hk (hφ_ge k)
      have hev := h_eventually k this
      -- hev : xseq (φ k) ∈ C N
      -- We know C N = K ∩ S, so xseq (φ k) ∈ S
      rw [hCN_eq] at hev
      simp only [Function.comp_apply]
      exact hev.2
  
  -- Step 7: Any point in the intersection achieves the minimum
  obtain ⟨x₀, hx₀⟩ := h_inter_nonempty
  simp only [Set.mem_iInter, C, Set.mem_setOf] at hx₀
  
  -- x₀ ∈ K and f(x₀) ≤ m + 1/(n+1) for all n
  have hx₀_in : x₀ ∈ K := (hx₀ 0).1
  have hx₀_le : ∀ n : ℕ, f x₀ ≤ m + 1/(n+1 : ℝ) := fun n => (hx₀ n).2
  
  -- Therefore f(x₀) ≤ m
  have h_le : f x₀ ≤ m := by
    by_contra h
    push_neg at h
    -- If f x₀ > m, choose n large enough so that 1/(n+1) < f x₀ - m
    have : ∃ n : ℕ, 1/(n+1 : ℝ) < f x₀ - m := by
      have h_pos : 0 < f x₀ - m := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (f x₀ - m))
      use n
      have : (n : ℝ) + 1 > 1 / (f x₀ - m) := by linarith
      -- From (n : ℝ) + 1 > 1 / (f x₀ - m), we get 1 / ((n : ℝ) + 1) < f x₀ - m
      -- From (n : ℝ) + 1 > 1 / (f x₀ - m) and f x₀ - m > 0, we get
      -- (n + 1) * (f x₀ - m) > 1, hence f x₀ - m > 1/(n+1)
      have : 1 < (n + 1) * (f x₀ - m) := by
        calc 1 = (f x₀ - m) * (1 / (f x₀ - m)) := by field_simp
             _ < (f x₀ - m) * (n + 1) := by
               apply mul_lt_mul_of_pos_left this h_pos
             _ = (n + 1) * (f x₀ - m) := by ring
      -- From 1 < (n+1) * (f x₀ - m), divide both sides by (n+1) to get 1/(n+1) < f x₀ - m
      -- From 1 < (f x₀ - m) * (n+1), divide by (n+1) to get 1/(n+1) < f x₀ - m
      rw [mul_comm] at this
      -- We have 1 < (n+1) * (f x₀ - m), so 1/(n+1) < f x₀ - m  
      have h1 : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
      -- From 1 < (n+1) * (f x₀ - m), we get 1/(n+1) < f x₀ - m
      -- by dividing both sides by (n+1) > 0
      have h_div : 1 / ((n : ℝ) + 1) < f x₀ - m := by
        calc 1 / ((n : ℝ) + 1) 
            = 1 / ((n : ℝ) + 1) * 1 := by ring
          _ < 1 / ((n : ℝ) + 1) * ((n : ℝ) + 1) * (f x₀ - m) := by
              rw [mul_assoc]
              rw [mul_comm] at this
              -- Now we have: 1 < (n+1) * (f x₀ - m)
              apply mul_lt_mul_of_pos_left this
              exact div_pos one_pos h1
          _ = (f x₀ - m) := by field_simp
      exact h_div
    obtain ⟨n, hn⟩ := this
    have := hx₀_le n
    linarith
  
  -- Also f(x₀) ≥ m since m is the infimum
  have h_ge : m ≤ f x₀ := csInf_le hS_bdd ⟨x₀, hx₀_in, rfl⟩
  
  -- Therefore f(x₀) = m
  have h_eq : f x₀ = m := le_antisymm h_le h_ge
  
  -- Now show x₀ is a minimizer
  use x₀, hx₀_in
  intro y hy
  rw [h_eq]
  exact csInf_le hS_bdd ⟨y, hy, rfl⟩

/-- Existence of minimizers for the minimizing movement step. -/
theorem mm_step_exists {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {xPrev : X}
    (hF_lsc : LowerSemicontinuous F) (hF_proper : MmProper F)
    (hF_compact : MmCompactSublevels F) :
    ∃ x : X, MmStep τ F xPrev x := by
  -- Define the functional to minimize
  let G := MmFunctional τ F xPrev

  -- Step 1: G is lower semicontinuous (sum of lsc function and continuous function)
  have hG_lsc : LowerSemicontinuous G := by
    -- G(x) = F(x) + (1/(2τ)) * distSquared(x, xPrev)
    -- F is lsc by assumption, and x ↦ distSquared(x, xPrev) is continuous
    have h_dist : Continuous (fun x => dist x xPrev) := by
      simpa using continuous_id.dist continuous_const
    have h_d2_cont : Continuous (fun x => distSquared x xPrev) := by
      unfold distSquared
      exact h_dist.pow 2
    have h_scaled_cont : Continuous (fun x => (1 / (2 * τ)) * distSquared x xPrev) := by
      exact continuous_const.mul h_d2_cont
    -- Sum of lsc and continuous is lsc
    change LowerSemicontinuous (fun x => F x + (1 / (2 * τ)) * distSquared x xPrev)
    exact hF_lsc.add h_scaled_cont.lowerSemicontinuous

  -- Step 2: Find a non-empty compact sublevel set
  -- Take any finite value of F (exists by Proper assumption)
  obtain ⟨x0, hx0⟩ := hF_proper

  -- Consider the value c = G(x0) = F(x0) + 0 = F(x0) (since we can choose x0 = xPrev if needed)
  -- Actually, let's use c = F(xPrev) + 1 to ensure non-emptiness
  let c := F xPrev + 1

  -- The sublevel set {x | G(x) ≤ c} is non-empty (contains xPrev)
  have h_nonempty : (Set.Nonempty {x : X | G x ≤ c}) := by
    use xPrev
    change MmFunctional τ F xPrev xPrev ≤ c
    simp only [MmFunctional, distSquared, dist_self, pow_two, mul_zero, add_zero]
    change F xPrev ≤ F xPrev + 1
    linarith

  -- Step 3: Show this sublevel set is compact
  -- We need to relate it to a sublevel set of F
  have h_sublevel_compact : IsCompact {x : X | G x ≤ c} := by
    -- For any x with G(x) ≤ c, we have F(x) ≤ c (since the distance term is non-negative)
    have h_subset : {x : X | G x ≤ c} ⊆ {x : X | F x ≤ c} := by
      intro x hx
      change MmFunctional τ F xPrev x ≤ c at hx
      simp only [MmFunctional] at hx
      have h_nonneg : 0 ≤ (1 / (2 * τ)) * distSquared x xPrev := by
        apply mul_nonneg
        · have hpos : 0 < 2 * τ := by linarith
          exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hpos)
        · unfold distSquared
          exact sq_nonneg _
      -- From hx: F x + (1/(2τ)) * distSquared x xPrev ≤ c = F xPrev + 1
      -- Since the distance term is non-negative, F x ≤ F xPrev + 1
      calc F x ≤ F x + (1 / (2 * τ)) * distSquared x xPrev := by linarith [h_nonneg]
           _ ≤ c := hx
           _ = F xPrev + 1 := rfl
    -- The set {x | F x ≤ c} is compact by assumption
    have h_F_compact := hF_compact c
    -- A closed subset of a compact set is compact
    have h_closed := sublevel_closed_of_lsc hG_lsc c
    exact IsCompact.of_isClosed_subset h_F_compact h_closed h_subset

  -- Step 4: Use the fact that a lower semicontinuous function on a non-empty compact set
  -- attains its minimum. We use IsCompact.exists_isMinOn from mathlib.

  -- First, we need to show that G is continuous on the compact set (for the theorem)
  -- Since G is lower semicontinuous, we need a stronger condition
  -- Actually, we can use the lsc version directly with our helper theorem
  obtain ⟨xmin, hxmin_in, hxmin_min⟩ :=
    lsc_attains_min_on_compact h_sublevel_compact h_nonempty hG_lsc

  -- Step 5: This minimum on the sublevel set is actually a global minimum
  use xmin
  unfold MmStep IsMinimizer
  intro y
  by_cases hy : G y ≤ c
  · -- If G(y) ≤ c, then xmin minimizes over this set
    exact hxmin_min y hy
  · -- If G(y) > c, then G(xmin) ≤ c < G(y)
    push_neg at hy
    have h1 : G xmin ≤ c := hxmin_in
    linarith

/-- Energy dissipation inequality for a discrete curve. -/
theorem mm_curve_energy_dissipation {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {x0 : X}
    (curve : MmCurve τ F x0) (n : ℕ) :
    F (curve.points n) ≤ F x0 := by
  induction n with
  | zero =>
    simp [curve.init]
  | succ n ih =>
    have := mm_energy_decrease hτ (curve.step n)
    linarith

/-- Sum of squared distances is bounded by initial energy difference. -/
theorem mm_curve_distance_sum {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {x0 : X}
    (curve : MmCurve τ F x0) (N : ℕ) :
    (Finset.range N).sum (fun n => distSquared (curve.points (n + 1)) (curve.points n)) ≤
    2 * τ * (F x0 - F (curve.points N)) := by
  induction N with
  | zero =>
    simp only [curve.init, sub_self, mul_zero]
    rfl
  | succ N ih =>
    have hstep := mm_distance_estimate hτ (curve.step N)
    have henergy := mm_energy_decrease hτ (curve.step N)
    simp [Finset.sum_range_succ]
    calc _ + distSquared (curve.points (N + 1)) (curve.points N)
        ≤ 2 * τ * (F x0 - F (curve.points N)) +
          2 * τ * (F (curve.points N) - F (curve.points (N + 1))) := add_le_add ih hstep
        _ = 2 * τ * (F x0 - F (curve.points (N + 1))) := by ring

end Frourio
