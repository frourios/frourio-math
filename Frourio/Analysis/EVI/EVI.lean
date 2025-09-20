import Frourio.Analysis.EVI.EVICore5
import Frourio.Analysis.EVI.EVICore6
import Frourio.Analysis.Lebesgue.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Tactic

namespace Frourio

open scoped BigOperators
open Finset

/-! Monotonicity lemmas from Dini derivatives -/

section DiniMonotonicity

-- L1: Eventually extraction from EReal limsup (simplified)
/-- If the limsup of a function is ≤ 0, then for any ε > 0,
    the function is eventually ≤ ε -/
lemma limsup_nonpos_eventually_le {α : Type*} (u : α → ℝ) (l : Filter α) (ε : ℝ) (hε : 0 < ε) :
    Filter.limsup (fun x => (u x : EReal)) l ≤ (0 : EReal) →
    ∀ᶠ x in l, u x ≤ ε := by
  intro h
  -- From `limsup ≤ 0 < ε`, get `limsup < ε`.
  have hlt : Filter.limsup (fun x => (u x : EReal)) l < (ε : EReal) :=
    lt_of_le_of_lt h (by
      -- Cast `0 < ε` to `EReal`.
      exact_mod_cast hε : (0 : EReal) < (ε : EReal))
  -- Standard fact: `limsup f < a` implies `eventually (f < a)`.
  have hev : ∀ᶠ x in l, (u x : EReal) < (ε : EReal) :=
    Filter.eventually_lt_of_limsup_lt hlt
  -- Turn strict `<` into `≤` and remove the coercions.
  refine hev.mono ?_
  intro x hx
  have hxR : u x < ε := by simpa using hx
  exact le_of_lt hxR

-- L2: Local control (ε-δ) lemma (simplified)
/-- If DiniUpperE φ t ≤ 0 and ε > 0, then there exists δ > 0 such that
    for all h with 0 < h < δ, we have (φ(t+h) - φ(t))/h ≤ ε -/
lemma local_control_from_DiniUpperE
  (φ : ℝ → ℝ) (t : ℝ) (ε : ℝ) (hε : 0 < ε) (h_dini : DiniUpperE φ t ≤ 0) :
    ∃ δ > 0, ∀ h, 0 < h ∧ h < δ → (φ (t + h) - φ t) / h ≤ ε := by
  -- Work with the right-neighborhood filter at 0.
  set l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  -- Real difference quotient.
  set u : ℝ → ℝ := fun h => (φ (t + h) - φ t) / h
  -- From `DiniUpperE φ t ≤ 0`, get eventual bound `u ≤ ε` on `l` using L1.
  have hlim : Filter.limsup (fun h : ℝ => ((u h : ℝ) : EReal)) l ≤ (0 : EReal) := by
    simpa [DiniUpperE, l, u]
      using (h_dini : DiniUpperE φ t ≤ 0)
  have hev : ∀ᶠ h in l, u h ≤ ε :=
    limsup_nonpos_eventually_le (u := u) (l := l) ε hε hlim
  -- Turn the eventual statement on `nhdsWithin 0 (Ioi 0)` into an explicit `δ`.
  -- Unpack membership in the infimum filter.
  have hset : {x : ℝ | u x ≤ ε} ∈ l := hev
  rcases (Filter.mem_inf_iff).1 (by simpa [l] using hset) with
    ⟨U, hU_nhds, V, hV_pr, hUV⟩
  -- `hV_pr : V ∈ 𝓟 (Set.Ioi 0)` means `Ioi 0 ⊆ V`.
  have hV_sup : Set.Ioi (0 : ℝ) ⊆ V := by simpa using hV_pr
  -- Choose a small ball around 0 contained in `U`.
  rcases (Metric.mem_nhds_iff).1 hU_nhds with ⟨δ, hδpos, hball⟩
  refine ⟨δ, hδpos, ?_⟩
  intro h hh
  have hpos : 0 < h := hh.1
  have hlt : h < δ := hh.2
  -- Then `h` lies in the ball and in `Ioi 0`.
  have h_in_ball : h ∈ Metric.ball (0 : ℝ) δ := by
    -- `dist h 0 = |h|` on ℝ.
    simpa [Real.dist_eq, abs_of_nonneg (le_of_lt hpos)] using hlt
  have hU : h ∈ U := hball h_in_ball
  have hV : h ∈ V := hV_sup (by exact hpos)
  have hinUV : h ∈ U ∩ V := ⟨hU, hV⟩
  have : h ∈ {x : ℝ | u x ≤ ε} := by simpa [hUV] using hinUV
  simpa [u] using this

/-- Pure telescoping identity on ℝ: `∑_{i=0}^{n-1} (t (i+1) - t i) = t n - t 0`. -/
lemma telescoping_sum_real (t : ℕ → ℝ) :
  ∀ n : ℕ, ∑ i ∈ range n, (t (i+1) - t i) = t n - t 0 := by
  classical
  intro n
  induction' n with n ih
  · simp
  · rw [range_succ, sum_insert (Finset.notMem_range_self), ih]
    ring

/-- If each short subinterval `(t i, t (i+1))` satisfies the incremental bound, then
summing gives the bound on the whole union. -/
lemma sum_bound_from_stepwise
  (φ : ℝ → ℝ) (s ε : ℝ) {N : ℕ} (t : ℕ → ℝ)
  (hstep :
    ∀ i < N, φ (s + t (i + 1)) - φ (s + t i) ≤ ε * (t (i + 1) - t i)) :
  (∑ i ∈ Finset.range N, (φ (s + t (i+1)) - φ (s + t i)))
    ≤ ε * (∑ i ∈ Finset.range N, (t (i+1) - t i)) := by
  classical
  have h_ineq : ∀ i ∈ Finset.range N,
    φ (s + t (i+1)) - φ (s + t i) ≤ ε * (t (i+1) - t i) := by
    intros i hi
    exact hstep i (Finset.mem_range.mp hi)
  calc ∑ i ∈ Finset.range N, (φ (s + t (i+1)) - φ (s + t i))
      ≤ ∑ i ∈ Finset.range N, ε * (t (i+1) - t i) := by
        exact Finset.sum_le_sum h_ineq
    _ = ε * (∑ i ∈ Finset.range N, (t (i+1) - t i)) := by
        rw [← Finset.mul_sum]

/-- Global composition from a *uniform* small-interval control. -/
lemma global_from_uniform_small_interval_control
  (φ : ℝ → ℝ) (s r ε : ℝ) (hr_pos : 0 < r)
  (hL : ∃ L > 0, ∀ ⦃y z⦄, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)) :
  φ (s + r) ≤ φ s + ε * r := by
  classical
  rcases hL with ⟨L, hLpos, hloc⟩
  -- choose N so that r/N < L
  obtain ⟨N, hNgt⟩ := exists_nat_gt (r / L)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < (N : ℝ) := lt_trans (div_pos hr_pos hLpos) hNgt
    exact Nat.cast_pos.mp this
  -- partition step
  set h := r / (N : ℝ) with hh
  have h_nonneg : 0 ≤ h := by
    exact div_nonneg (le_of_lt hr_pos) (by exact_mod_cast (le_of_lt hNpos))
  have hlt : h < L := by
    have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
    -- We need to show h = r/N < L
    -- From hNgt: r/L < N, we get r < N*L by multiplying by L
    -- Then dividing by N gives r/N < L
    rw [hh]
    have step1 : r < (N : ℝ) * L := by
      calc r = (r / L) * L := by field_simp [ne_of_gt hLpos]
           _ < (N : ℝ) * L := mul_lt_mul_of_pos_right hNgt hLpos
    -- Now we show r / N < L using field_simp
    have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hNposR
    have : r / (N : ℝ) < L := by
      have h_ineq : r < L * (N : ℝ) := by linarith [step1]
      calc r / (N : ℝ) = r * (1 / (N : ℝ)) := by rw [div_eq_mul_one_div]
           _ < L * (N : ℝ) * (1 / (N : ℝ)) := by
               exact mul_lt_mul_of_pos_right h_ineq (by simp [hNposR])
           _ = L := by field_simp [hN_ne]
    exact this
  -- grid
  let t : ℕ → ℝ := fun i => (i : ℝ) * h
  have t0 : t 0 = 0 := by simp [t]
  have tN : t N = r := by
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hNpos)
    simp [t, hh, mul_comm, mul_assoc, div_eq_mul_inv, hN0]
  -- stepwise bound via `hloc`
  have step_bound :
    ∀ i < N, φ (s + t (i+1)) - φ (s + t i) ≤ ε * (t (i+1) - t i) := by
    intro i hi
    -- membership
    have hy_in : t i ∈ Set.Icc (0:ℝ) r := by
      refine ⟨?_, ?_⟩
      · exact mul_nonneg (by exact_mod_cast (Nat.cast_nonneg i)) h_nonneg
      · have : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_of_lt hi)
        have : (i : ℝ) * h ≤ (N : ℝ) * h := mul_le_mul_of_nonneg_right this h_nonneg
        simpa [t, tN] using this
    have hz_in : t (i+1) ∈ Set.Icc (0:ℝ) r := by
      refine ⟨?_, ?_⟩
      · exact mul_nonneg (by exact_mod_cast (Nat.cast_nonneg (i+1))) h_nonneg
      · have : ((i+1 : ℝ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hi)
        have : ((i+1 : ℝ)) * h ≤ (N : ℝ) * h := mul_le_mul_of_nonneg_right this h_nonneg
        simpa [t, tN] using this
    have hyz : t i ≤ t (i+1) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_succ i)) h_nonneg
    have hlen : (t (i+1) - t i) < L := by
      have : (t (i+1) - t i) = h := by simp [t]; ring
      simpa [this] using hlt
    -- apply local uniform bound
    have := hloc (y := t i) (z := t (i+1)) hy_in hz_in hyz hlen
    simpa [t] using this
  -- sum and telescope
  have sum_left :
    ∑ i ∈ range N, (φ (s + t (i+1)) - φ (s + t i))
      ≤ ε * (∑ i ∈ range N, (t (i+1) - t i)) :=
    sum_bound_from_stepwise φ s ε t step_bound
  have tele_left :
    ∑ i ∈ range N, (φ (s + t (i+1)) - φ (s + t i)) = φ (s + r) - φ s := by
    trans (φ (s + t N) - φ (s + t 0))
    · exact telescoping_sum_real (fun i => φ (s + t i)) N
    · simp [tN, t0]
  have tele_right :
    ∑ i ∈ range N, (t (i+1) - t i) = r := by
    simpa [t0, tN] using telescoping_sum_real t N
  have main_ineq : φ (s + r) - φ s ≤ ε * r := by
    calc φ (s + r) - φ s = ∑ i ∈ range N, (φ (s + t (i+1)) - φ (s + t i)) := by rw [← tele_left]
         _ ≤ ε * (∑ i ∈ range N, (t (i+1) - t i)) := sum_left
         _ = ε * r := by rw [tele_right]
  linarith

/-- Core finite-chain composition, assuming *ball-local* two-point control.
(`lebesgue_property_from_two_point_local`). -/
theorem finite_chain_composition_core
  (φ : ℝ → ℝ) (s r ε : ℝ) (hr_pos : 0 < r) (hε_pos : 0 < ε)
  (two_point_ball_local :
    ∀ w ∈ Set.Icc 0 r, ∃ ρw > 0, ∃ δw > 0,
      ∀ u ∈ Set.Icc 0 r, ∀ v ∈ Set.Icc 0 r,
        dist u w < ρw → dist v w < ρw →
        φ (s + v) - φ (s + u) ≤ ε * (v - u)) :
  φ (s + r) ≤ φ s + ε * r := by
  classical
  -- get uniform small-interval control via Lebesgue
  obtain ⟨L, hLpos, hunif⟩ :=
    Frourio.lebesgue_property_from_two_point_local
      (φ := φ) (s := s) (r := r) (ε := ε) hr_pos hε_pos two_point_ball_local
  -- specialize to oriented segments y ≤ z
  have hL :
    ∃ L > 0, ∀ ⦃y z⦄, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y) := by
    refine ⟨L, hLpos, ?_⟩
    intro y z hy hz hyz hlen
    have hdist : dist y z < L := by
      -- since y ≤ z and z - y < L, use dist y z = |z - y| = z - y
      have : 0 ≤ z - y := sub_nonneg.mpr hyz
      rw [dist_comm, Real.dist_eq, abs_of_nonneg this]
      exact hlen
    rcases hunif y hy z hz hdist with ⟨w, hw, δw, hδpos, hyw, hzw, hineq⟩
    -- discard witnesses; we only need the inequality
    exact hineq
  -- globalize
  exact global_from_uniform_small_interval_control φ s r ε hr_pos hL

/-- Correct version with upper semicontinuity hypothesis -/
lemma finite_chain_composition_with_usc (φ : ℝ → ℝ) (s r ε : ℝ) (hr_pos : 0 < r)
  (hε_pos : 0 < ε) (h_dini_all : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
  (h_usc : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
    |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀) :
    φ (s + r) ≤ φ s + ε * r := by
  -- Direct application of the theorem from EVICore6
  exact global_evaluation_from_partition_with_usc h_dini_all h_usc hε_pos hr_pos

-- L4: ε→0 limit taking
/-- If for all ε > 0 we have f ≤ g + ε*c where c ≥ 0, then f ≤ g -/
lemma limit_epsilon_to_zero (f g c : ℝ) (hc : 0 ≤ c) (h : ∀ ε > 0, f ≤ g + ε * c) : f ≤ g := by
  -- Take ε → 0 limit
  by_contra h_not
  push_neg at h_not
  -- So g < f, choose ε = (f - g)/(2c) if c > 0, or ε = 1 if c = 0
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · -- Case c = 0
    simp at h
    have := h 1 (by norm_num)
    linarith
  · -- Case c > 0
    let ε := (f - g) / (2 * c)
    have hε_pos : 0 < ε := by
      simp [ε]; apply div_pos <;> linarith
    have := h ε hε_pos
    -- We have f ≤ g + (f - g)/(2c) * c = g + (f - g)/2
    -- So 2f ≤ 2g + (f - g) = f + g, hence f ≤ g
    simp [ε] at this
    field_simp at this
    linarith

lemma shifted_function_nonincreasing_with_usc
  (φ : ℝ → ℝ) (s : ℝ) (h_dini_shifted : ∀ u ≥ 0, DiniUpperE (fun τ => φ (s + τ) - φ s) u ≤ 0)
  (h_usc : ∀ t > 0, ∀ w ∈ Set.Icc 0 t, ∀ y₀ ∈ Set.Icc 0 t,
    |y₀ - w| < t / 4 → upper_semicontinuous_at_zero φ s y₀) :
    ∀ t ≥ 0, φ (s + t) ≤ φ s := by
  intro t ht
  let ψ := fun τ => φ (s + τ) - φ s
  -- Note: ψ(0) = 0, so we need to show ψ(t) ≤ 0
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp
  · -- Apply the USC version
    have h_dini_interval : ∀ u ∈ Set.Icc 0 t, DiniUpperE ψ (0 + u) ≤ 0 := by
      intro u hu
      simp only [zero_add]
      have : DiniUpperE ψ u = DiniUpperE (fun τ => φ (s + τ) - φ s) u := rfl
      exact h_dini_shifted u hu.1
    -- Need to transform h_usc for ψ
    have h_usc_ψ : ∀ w ∈ Set.Icc 0 t, ∀ y₀ ∈ Set.Icc 0 t,
      |y₀ - w| < t / 4 → upper_semicontinuous_at_zero ψ 0 y₀ := by
      -- Transport USC from φ to ψ using equality of quotient functions.
      -- For ψ(τ) = φ(s+τ) - φ(s), the quotient_function coincides:
      --   ((ψ (y+h) - ψ y) / h) = ((φ (s+y+h) - φ (s+y)) / h).
      -- Hence, any USC witness for φ at (s, y₀) is also a USC witness for ψ at (0, y₀).
      intros w hw y₀ hy₀ hdist
      -- Unfold the target predicate and reuse the witness from h_usc.
      intro ε hε
      -- Get USC parameters for φ at (s, y₀).
      rcases h_usc t ht_pos w hw y₀ hy₀ hdist ε hε with ⟨α, hαpos, β, hβpos, hφ⟩
      refine ⟨α, hαpos, β, hβpos, ?_⟩
      intro y h hy_near hpos hlt
      -- Apply the USC bound for φ and rewrite it to ψ via the quotient identity.
      have hineq : (φ (s + (y + h)) - φ (s + y)) / h < ε :=
        hφ y h hy_near hpos hlt
      have hrewrite :
          quotient_function ψ 0 y h
            = (φ (s + (y + h)) - φ (s + y)) / h := by
        unfold quotient_function ψ
        simp only [zero_add]
        ring_nf
      have : quotient_function ψ 0 y h < ε := by simpa [hrewrite] using hineq
      exact this
    -- Use finite_chain_composition_with_usc
    have h_eps : ∀ ε > 0, ψ t ≤ ε * t := by
      intro ε hε
      have := finite_chain_composition_with_usc ψ 0 t ε ht_pos hε h_dini_interval h_usc_ψ
      simpa [ψ] using this
    -- Let ε → 0
    have ht0 : 0 ≤ t := le_of_lt ht_pos
    have : ψ t ≤ 0 :=
      limit_epsilon_to_zero (ψ t) 0 t ht0 (by
        intro ε hε; simpa using (h_eps ε hε))
    -- Conclude
    have : φ (s + t) - φ s ≤ 0 := by simpa [ψ] using this
    simpa using sub_nonpos.mp this

/-- Main monotonicity theorem with upper semicontinuity: if DiniUpperE is non-positive
    everywhere and the function satisfies upper semicontinuity conditions,
    then the function is non-increasing -/
theorem nonincreasing_of_DiniUpperE_nonpos_with_usc (φ : ℝ → ℝ)
    (hD : ∀ u, DiniUpperE φ u ≤ 0)
    (h_usc : ∀ s t, s < t → ∀ w ∈ Set.Icc 0 (t - s), ∀ y₀ ∈ Set.Icc 0 (t - s),
      |y₀ - w| < (t - s) / 4 → upper_semicontinuous_at_zero φ s y₀) :
    ∀ s t, s ≤ t → φ t ≤ φ s := by
  intro s t hst
  rcases eq_or_lt_of_le hst with rfl | hst_lt
  · rfl
  · -- Use shifted_function_nonincreasing_with_usc
    have h_shifted : ∀ u ≥ 0, DiniUpperE (fun τ => φ (s + τ) - φ s) u ≤ 0 := by
      intro u hu
      -- The Dini upper derivative of the shifted function
      simp only [DiniUpperE]
      -- We need to show the limsup is ≤ 0
      -- First, simplify the expression arithmetically
      have simp_expr : ∀ h,
        (φ (s + (u + h)) - φ s - (φ (s + u) - φ s)) = φ (s + u + h) - φ (s + u) := by
        intro h
        ring_nf
      -- The goal is about limsup of a coerced expression
      -- We simplify using the fact that the expressions are equal
      suffices h_suff : Filter.limsup (fun h => ((φ (s + u + h) - φ (s + u)) / h : EReal))
                          (nhdsWithin 0 (Set.Ioi 0)) ≤ 0 by
        convert h_suff using 2
        ext h
        rw [simp_expr h]
        simp only [EReal.coe_div, EReal.coe_sub]
      -- Now this is DiniUpperE φ (s + u)
      have eq_dini : Filter.limsup (fun h => ((φ (s + u + h) - φ (s + u)) / h : EReal))
                       (nhdsWithin 0 (Set.Ioi 0)) = DiniUpperE φ (s + u) := by
        rfl
      rw [eq_dini]
      exact hD (s + u)
    -- Apply the theorem for the specific interval [s, t]
    have h_usc_interval : ∀ r > 0, ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀ := by
      intro r hr w hw y₀ hy₀ hdist
      -- Need to adjust the domains
      have hw' : w ∈ Set.Icc 0 (s + r - s) := by simp; exact hw
      have hy₀' : y₀ ∈ Set.Icc 0 (s + r - s) := by simp; exact hy₀
      have hdist' : |y₀ - w| < (s + r - s) / 4 := by simp; exact hdist
      exact h_usc s (s + r) (by linarith) w hw' y₀ hy₀' hdist'
    -- Apply to get φ(s + (t - s)) ≤ φ(s)
    have result := shifted_function_nonincreasing_with_usc φ s h_shifted h_usc_interval
      (t - s) (by linarith)
    -- Simplify s + (t - s) = t
    convert result using 2
    ring

end DiniMonotonicity

/-!
Generic predicate-level bridges between an abstract energy-dissipation
predicate `P : (X → ℝ) → (ℝ → X) → Prop` and the EVI predicate. These are
kept abstract here to avoid import cycles with `PLFACore` where `EDE` is
defined; users can specialize `P` to `EDE` on the PLFA side.
-/

section GenericBridges
variable {X : Type*} [PseudoMetricSpace X]

/-- Forward bridge: from an abstract predicate `P F ρ` to the EVI predicate for `F`.
Specialize `P` to `EDE` on the PLFA side to obtain `EDE → EVI`. -/
def EVIBridgeForward (P : (X → ℝ) → (ℝ → X) → Prop)
  (F : X → ℝ) (lam : ℝ) : Prop :=
  ∀ ρ : ℝ → X, P F ρ → IsEVISolution ({ E := F, lam := lam } : EVIProblem X) ρ

/-- Backward bridge: from the EVI predicate for `F` to an abstract predicate `P F ρ`.
Specialize `P` to `EDE` on the PLFA side to obtain `EVI → EDE`. -/
def EVIBridgeBackward (P : (X → ℝ) → (ℝ → X) → Prop)
  (F : X → ℝ) (lam : ℝ) : Prop :=
  ∀ ρ : ℝ → X, IsEVISolution ({ E := F, lam := lam } : EVIProblem X) ρ → P F ρ

/-- Equivalence bridge: `P F ρ` holds iff the EVI predicate holds for `F`. -/
def EVIEquivBridge (P : (X → ℝ) → (ℝ → X) → Prop)
  (F : X → ℝ) (lam : ℝ) : Prop :=
  EVIBridgeForward P F lam ∧ EVIBridgeBackward P F lam

end GenericBridges

/-! Geodesic uniform evaluation (two‑EVI input) -/

section GeodesicUniform
variable {X : Type*} [PseudoMetricSpace X]

/-- Geodesic-uniform evaluation predicate used by two‑EVI assumptions.
It provides, uniformly for all error levels `η`, a bridge from squared‑distance
contraction to linear‑distance contraction. This matches the role geodesic
regularity plays in AGS-type arguments and is sufficient for the with‑error
pipeline in this phase. -/
def GeodesicUniformEval (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∀ η : ℝ, HbridgeWithError P u v η

/-- Convenience: extract a bridge at a given error level from
`GeodesicUniformEval`. -/
theorem geodesicUniform_to_bridge {P : EVIProblem X} {u v : ℝ → X}
  (G : GeodesicUniformEval P u v) : ∀ η : ℝ, HbridgeWithError P u v η :=
G

end GeodesicUniform

end Frourio
