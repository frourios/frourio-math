import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Frourio

open MeasureTheory

/-!
# Exponential Decay Lemmas

This file contains lemmas about exponential decay that are used in the RH criterion proof.
These are standard results from real analysis about the behavior of exp(-x²) as x → ∞.
-/

/-- The key property: exp(-cx²) → 0 faster than any polynomial as x → ∞ -/
theorem exp_neg_sq_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => Real.exp (-c * (n : ℝ)^2)) Filter.atTop (nhds 0) := by
  have h_pow :
      Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)
  have h_nat_pow :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)^2) Filter.atTop Filter.atTop :=
    h_pow.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h_const_mul :
      Filter.Tendsto (fun n : ℕ => c * (n : ℝ)^2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop' hc h_nat_pow
  have h_comp := Real.tendsto_exp_neg_atTop_nhds_zero.comp h_const_mul
  convert h_comp using 1
  ext n
  simp [Function.comp, neg_mul]

lemma tendsto_comp {α : Type*} {β : Type*} {γ : Type*} {f : α → β} {g : β → γ} {x : Filter α}
  {y : Filter β} {z : Filter γ} (hg : Filter.Tendsto g y z) (hf : Filter.Tendsto f x y) :
  Filter.Tendsto (g ∘ f) x z := hg.comp hf

/-- For any ε > 0, there exists N such that for all n ≥ N,
    4 * exp(-π ε² (n+1)²) < ε.
    This captures the super-exponential decay of the Gaussian function. -/
theorem exponential_decay_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      4 * Real.exp (-Real.pi * ε^2 * (n + 1)^2) < ε := by
  classical
  have h_tendsto :
      Filter.Tendsto
        (fun n : ℕ => 4 * Real.exp (-Real.pi * ε^2 * (n + 1 : ℝ)^2))
        Filter.atTop (nhds 0) := by
    have h_coeff : 0 < Real.pi * ε^2 := by
      have h_sq : 0 < ε^2 := by
        simpa using sq_pos_of_ne_zero (by exact ne_of_gt hε)
      exact mul_pos Real.pi_pos h_sq
    have h_base :=
      exp_neg_sq_tendsto_zero (Real.pi * ε^2) h_coeff
    have h_succ :
        Filter.Tendsto Nat.succ Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro m
      refine Filter.eventually_atTop.2 ?_
      refine ⟨m, ?_⟩
      intro n hn
      exact le_trans (Nat.le_succ _) (Nat.succ_le_succ hn)
    have h_shift :
        Filter.Tendsto
          (fun n : ℕ =>
            Real.exp (-Real.pi * ε^2 * ((Nat.succ n : ℝ)^2)))
          Filter.atTop (nhds 0) := by
      have h_comp := h_base.comp h_succ
      convert h_comp using 1
      ext n
      simp [Function.comp, Nat.cast_succ]
    have h_shift' :
        Filter.Tendsto
          (fun n : ℕ =>
            Real.exp (-Real.pi * ε^2 * (n + 1 : ℝ)^2))
          Filter.atTop (nhds 0) := by
      simpa [Nat.cast_add, Nat.cast_one, pow_two, add_comm, add_left_comm, add_assoc]
        using h_shift
    have h_mul := h_shift'.const_mul (4 : ℝ)
    simpa using h_mul
  have h_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        4 * Real.exp (-Real.pi * ε^2 * (n + 1 : ℝ)^2) < ε := by
    have h_const :
        Filter.Tendsto (fun _ : ℕ => ε) Filter.atTop (nhds ε) :=
      tendsto_const_nhds
    have h_limit : (0 : ℝ) < ε := hε
    exact (Filter.Tendsto.eventually_lt h_tendsto h_const h_limit)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
  refine ⟨N, ?_⟩
  intro n hn
  exact hN n hn

/-- Alternative formulation controlling the reciprocal width parameter δ.
    For sufficiently small positive δ, the Gaussian tail becomes smaller than ε. -/
theorem exponential_decay_bound_reciprocal (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      4 * Real.exp (-Real.pi * ε^2 / δ^2) < ε := by
  classical
  obtain ⟨N, hN⟩ := exponential_decay_bound ε hε
  let δ0 : ℝ := 1 / (N + 1 : ℝ)
  have hδ0_pos : 0 < δ0 := by
    have : 0 < (N + 1 : ℝ) := by exact_mod_cast Nat.succ_pos N
    exact one_div_pos.mpr this
  refine ⟨δ0, hδ0_pos, ?_⟩
  intro δ hδ_pos hδ_le
  have h_base : 4 * Real.exp (-Real.pi * ε^2 / δ0^2) < ε := by
    have hN0 : 4 * Real.exp (-Real.pi * ε^2 * (N + 1 : ℝ)^2) < ε := hN N (le_rfl)
    simpa [δ0, pow_two, div_eq_mul_inv] using hN0
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hδ0_nonneg : 0 ≤ δ0 := le_of_lt hδ0_pos
  have h_sq : δ^2 ≤ δ0^2 := by
    have := mul_le_mul hδ_le hδ_le hδ_nonneg hδ0_nonneg
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
  have h_inv_sq : 1 / δ0^2 ≤ 1 / δ^2 :=
    one_div_le_one_div_of_le (pow_pos hδ_pos 2) h_sq
  have h_const_nonneg : 0 ≤ Real.pi * ε^2 :=
    mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg ε)
  have h_mul := mul_le_mul_of_nonneg_left h_inv_sq h_const_nonneg
  have h_arg : -Real.pi * ε^2 / δ^2 ≤ -Real.pi * ε^2 / δ0^2 := by
    have h_neg := neg_le_neg h_mul
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_neg
  have h_le : 4 * Real.exp (-Real.pi * ε^2 / δ^2) ≤
      4 * Real.exp (-Real.pi * ε^2 / δ0^2) := by
    have h_exp := Real.exp_le_exp.mpr h_arg
    exact mul_le_mul_of_nonneg_left h_exp (by norm_num : 0 ≤ (4 : ℝ))
  exact lt_of_le_of_lt h_le h_base

/-- For Gaussian decay with parameter depending on 1/(n+1) -/
theorem gaussian_tail_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      let δ := 1 / (n + 1 : ℝ)
      4 * Real.exp (-Real.pi * ε^2 / δ^2) < ε := by
  classical
  obtain ⟨N, hN⟩ := exponential_decay_bound ε hε
  refine ⟨N, ?_⟩
  intro n hn
  dsimp
  have h := hN n hn
  simpa [pow_two, div_eq_mul_inv, inv_pow, mul_comm, mul_left_comm, mul_assoc]
    using h

/-- General exponential bound: for any A > 0 and B > 0,
    A * exp(-B * n²) eventually becomes smaller than any ε > 0 -/
theorem general_exponential_bound (A B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      A * Real.exp (-B * (n : ℝ)^2) < ε := by
  classical
  have h_tendsto :
      Filter.Tendsto
        (fun n : ℕ => A * Real.exp (-B * (n : ℝ)^2)) Filter.atTop (nhds 0) := by
    have base := exp_neg_sq_tendsto_zero B hB
    simpa [mul_comm] using base.const_mul A
  have h_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        A * Real.exp (-B * (n : ℝ)^2) < ε := by
    have h_const :
        Filter.Tendsto (fun _ : ℕ => ε) Filter.atTop (nhds ε) :=
      tendsto_const_nhds
    exact (Filter.Tendsto.eventually_lt h_tendsto h_const hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
  refine ⟨N, ?_⟩
  intro n hn
  exact hN n hn

/-- Integral bound for Gaussian tails outside an interval.
For a Gaussian centered at τ₀ with width parameter (n+1)⁻¹,
the L² mass of the tail outside {τ | |τ - τ₀| ≤ ε} decays
exponentially in n. This is crucial for proving concentration
of Mellin traces at golden lattice points. -/
lemma gaussian_tail_bound_integral (τ₀ : ℝ) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∫ τ in {τ | |τ - τ₀| > ε}, Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
      ≤ C * Real.exp (-ε^2 * (n + 1 : ℝ)^2) := by
  sorry

end Frourio
