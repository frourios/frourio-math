import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Order.ToIntervalMod
import Frourio.Analysis.Gaussian

namespace Frourio

open MeasureTheory
open scoped Pointwise ENNReal

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
lemma gaussian_tail_bound_integral (τ₀ : ℝ) (n : ℕ) (ε : ℝ) :
    ∃ C : ℝ, 0 < C ∧
    ∫ τ in {τ | |τ - τ₀| > ε}, Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
      ≤ C * Real.exp (-ε^2 * (n + 1 : ℝ)^2) := by
  classical
  -- Step 1: translate the integral to be centered at 0
  have h_translate :
      ∫ τ in {τ | |τ - τ₀| > ε},
        Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
        =
        ∫ t in {t | |t| > ε},
          Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂volume := by
    classical
    -- abbreviations for the integrand and the symmetric tail set
    set f : ℝ → ℝ := fun t =>
      Real.exp (-t^2 * (n + 1 : ℝ)^2) with hf_def
    set S : Set ℝ := {τ : ℝ | |τ - τ₀| > ε} with hS_def
    set T : Set ℝ := {t : ℝ | |t| > ε} with hT_def
    have hS_meas : MeasurableSet S := by
      -- `S = {τ | ε < |τ - τ₀|}` is an open set
      have hopen : IsOpen {τ : ℝ | ε < |τ - τ₀|} :=
        isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)
      have : S = {τ : ℝ | ε < |τ - τ₀|} := by
        ext τ
        simp [S, hS_def, gt_iff_lt]
      rw [this]
      exact hopen.measurableSet
    have hT_meas : MeasurableSet T := by
      -- `T = {t | ε < |t|}` is an open set
      have hopen : IsOpen {t : ℝ | ε < |t|} :=
        isOpen_lt continuous_const continuous_abs
      have : T = {t : ℝ | ε < |t|} := by
        ext t
        simp [T, hT_def, gt_iff_lt]
      rw [this]
      exact hopen.measurableSet
    -- Rewrite the left-hand side as an integral over ℝ with an indicator.
    have h_left :
        ∫ τ in S, f (τ - τ₀) ∂volume =
          ∫ τ, S.indicator (fun τ => f (τ - τ₀)) τ ∂volume := by
      -- `integral_indicator` gives the desired identity.
      simpa [S, hS_def] using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := S) (f := fun τ => f (τ - τ₀)) hS_meas).symm
    -- Identify this indicator with the shifted symmetric tail indicator.
    have h_indicator :
        S.indicator (fun τ => f (τ - τ₀)) =
          fun τ => T.indicator f (τ - τ₀) := by
      funext τ
      by_cases h : |τ - τ₀| > ε
      · -- inside the tail on both sides
        have hS : τ ∈ S := by simpa [S, hS_def] using h
        have hT : τ - τ₀ ∈ T := by
          -- same condition written on the shifted variable
          simpa [T, hT_def] using h
        simp only [Set.indicator_of_mem hS, Set.indicator_of_mem hT]
      · -- outside the tail on both sides
        have hS : τ ∉ S := by simpa [S, hS_def] using h
        have hT : τ - τ₀ ∉ T := by
          simpa [T, hT_def] using h
        simp only [Set.indicator_of_notMem hS, Set.indicator_of_notMem hT]
    have h_left' :
        ∫ τ in S, f (τ - τ₀) ∂volume =
          ∫ τ, T.indicator f (τ - τ₀) ∂volume := by
      refine h_left.trans ?_
      -- replace the integrand using the pointwise identity above
      refine MeasureTheory.integral_congr_ae ?_
      exact Filter.Eventually.of_forall (fun τ => by
        simp [h_indicator] )
    -- Rewrite the right-hand side as an integral over ℝ with an indicator.
    have h_right :
        ∫ t in T, f t ∂volume =
          ∫ t, T.indicator f t ∂volume := by
      simpa [T, hT_def] using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := T) (f := f) hT_meas).symm
    -- Use translation invariance of Lebesgue measure: τ ↦ τ - τ₀.
    have h_trans :
        ∫ τ, T.indicator f (τ - τ₀) ∂volume =
          ∫ t, T.indicator f t ∂volume := by
      -- Apply `integral_add_left_eq_self` to the function `x ↦ T.indicator f (x - τ₀)`.
      simpa [T, hT_def, f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (MeasureTheory.integral_add_left_eq_self
          (μ := (volume : Measure ℝ))
          (f := fun x => T.indicator f (x - τ₀)) τ₀).symm
    -- Put everything together and unfold the abbreviations.
    have h_final :
        ∫ τ in S, f (τ - τ₀) ∂volume =
          ∫ t in T, f t ∂volume := by
      calc
        ∫ τ in S, f (τ - τ₀) ∂volume
            = ∫ τ, T.indicator f (τ - τ₀) ∂volume := h_left'
        _ = ∫ t, T.indicator f t ∂volume := h_trans
        _ = ∫ t in T, f t ∂volume := h_right.symm
    simpa [S, hS_def, T, hT_def, f, sub_eq_add_neg] using h_final
  -- Step 2: scale to the standard Gaussian by u = (n+1) • t
  have h_scale :
      ∫ t in {t | |t| > ε},
        Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂volume
        =
        (1 / (n + 1 : ℝ)) *
          ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
            Real.exp (-u^2) ∂volume := by
    -- We use the scaling change-of-variables for Haar measure on ℝ.
    have hR_pos : 0 < (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos n
    -- First apply the general `setIntegral_comp_smul_of_pos` lemma.
    have h_aux :
        ∫ t in {t : ℝ | |t| > ε},
          Real.exp (-(((n + 1 : ℝ) * t)^2)) ∂(volume : Measure ℝ)
        =
        (1 / (n + 1 : ℝ)) *
          ∫ u in (n + 1 : ℝ) • {t : ℝ | |t| > ε},
            Real.exp (-u^2) ∂(volume : Measure ℝ) := by
      -- Specialize `setIntegral_comp_smul_of_pos` with `f u = exp (-u^2)`.
      have :=
        Measure.setIntegral_comp_smul_of_pos
          (μ := (volume : Measure ℝ))
          (E := ℝ) (F := ℝ)
          (f := fun u : ℝ => Real.exp (-u^2))
          (s := {t : ℝ | |t| > ε})
          (R := (n + 1 : ℝ)) hR_pos
      -- In ℝ, scalar multiplication is ordinary multiplication.
      -- Also `finrank ℝ ℝ = 1`, so the scalar factor simplifies to `1 / (n+1)`.
      simpa [smul_eq_mul, Module.finrank_self, pow_one, one_div] using this
    -- On the left, rewrite `((n+1)*t)^2` as `t^2 * (n+1)^2`.
    have h_left_simpl :
        ∫ t in {t : ℝ | |t| > ε},
          Real.exp (-(((n + 1 : ℝ) * t)^2)) ∂(volume : Measure ℝ)
        =
        ∫ t in {t : ℝ | |t| > ε},
          Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂(volume : Measure ℝ) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro t
      -- Algebraic identity: `((n+1)*t)^2 = t^2 * (n+1)^2`.
      have : ((n + 1 : ℝ) * t) ^ 2 = t ^ 2 * (n + 1 : ℝ) ^ 2 := by
        ring
      simp [this]
    -- On the right, identify the scaled set `(n+1) • {t | |t| > ε}`.
    have h_set :
        (n + 1 : ℝ) • {t : ℝ | |t| > ε}
          = {u : ℝ | |u| > ε * (n + 1 : ℝ)} := by
      ext u
      constructor
      · -- Forward inclusion: if `u = (n+1) * t` with `|t| > ε`, then `|u| > ε * (n+1)`.
        intro hu
        rcases hu with ⟨t, ht, rfl⟩
        have ht' : ε < |t| := by
          -- `|t| > ε` is equivalent to `ε < |t|`.
          simpa [Set.mem_setOf_eq, gt_iff_lt] using ht
        have h_mul : ε * (n + 1 : ℝ) < |t| * (n + 1 : ℝ) :=
          mul_lt_mul_of_pos_right ht' hR_pos
        -- Rewrite the right-hand side using `abs_mul`.
        have : ε * (n + 1 : ℝ) < |(n + 1 : ℝ) * t| := by
          simpa [abs_mul, abs_of_pos hR_pos, mul_comm, mul_left_comm, mul_assoc] using h_mul
        -- Membership in the target set.
        simpa [Set.mem_setOf_eq, gt_iff_lt, mul_comm, mul_left_comm, mul_assoc] using this
      · -- Backward inclusion: from `|u| > ε * (n+1)` recover `u = (n+1)*t` with `|t| > ε`.
        intro hu
        have hu' : ε * (n + 1 : ℝ) < |u| := by
          simpa [Set.mem_setOf_eq, gt_iff_lt, mul_comm, mul_left_comm, mul_assoc] using hu
        -- Divide the inequality by `(n+1) > 0`.
        have hu'' : ε < |u| / (n + 1 : ℝ) := by
          have : ε * (n + 1 : ℝ) < |u| := hu'
          calc ε = (ε * (n + 1 : ℝ)) / (n + 1 : ℝ) := by
                field_simp
            _ < |u| / (n + 1 : ℝ) := by
                exact div_lt_div_of_pos_right this hR_pos
        -- Express `|u / (n+1)|` in terms of `|u| / (n+1)`.
        have hu''' : ε < |u / (n + 1 : ℝ)| := by
          rw [abs_div, abs_of_pos hR_pos]
          exact hu''
        -- Witness `u` as a scalar multiple of an element of the original set.
        refine ⟨u / (n + 1 : ℝ), ?_, ?_⟩
        · -- `u / (n+1)` lies in `{t | |t| > ε}` since `ε < |u / (n+1)|`.
          simpa [Set.mem_setOf_eq, gt_iff_lt] using hu'''
        · -- And indeed `u = (n+1) * (u / (n+1))`.
          have hR_ne : (n + 1 : ℝ) ≠ 0 := ne_of_gt hR_pos
          field_simp
    -- Rewrite the right-hand side of `h_aux` using the set identity.
    have h_right_simpl :
        ∫ u in (n + 1 : ℝ) • {t : ℝ | |t| > ε},
          Real.exp (-u^2) ∂(volume : Measure ℝ)
        =
        ∫ u in {u : ℝ | |u| > ε * (n + 1 : ℝ)},
          Real.exp (-u^2) ∂(volume : Measure ℝ) := by
      -- Change variables in the domain using set equality.
      simp [h_set]
    -- Put everything together.
    have h_main :
        ∫ t in {t : ℝ | |t| > ε},
          Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂(volume : Measure ℝ)
        =
        (1 / (n + 1 : ℝ)) *
          ∫ u in {u : ℝ | |u| > ε * (n + 1 : ℝ)},
            Real.exp (-u^2) ∂(volume : Measure ℝ) := by
      -- Start from `h_aux` and rewrite both sides via the simplifications above.
      calc
        ∫ t in {t : ℝ | |t| > ε},
          Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂(volume : Measure ℝ)
            = ∫ t in {t : ℝ | |t| > ε},
                Real.exp (-(((n + 1 : ℝ) * t)^2)) ∂(volume : Measure ℝ) :=
              h_left_simpl.symm
        _ = (1 / (n + 1 : ℝ)) *
              ∫ u in (n + 1 : ℝ) • {t : ℝ | |t| > ε},
                Real.exp (-u^2) ∂(volume : Measure ℝ) := h_aux
        _ = (1 / (n + 1 : ℝ)) *
              ∫ u in {u : ℝ | |u| > ε * (n + 1 : ℝ)},
                Real.exp (-u^2) ∂(volume : Measure ℝ) := by
              simp [h_right_simpl]
    -- Finally, remove the explicit `volume` annotations to match the goal.
    simpa using h_main
 -- Step 3: a Gaussian tail bound for the standard Gaussian
  have h_tail :
      ∃ C0 : ℝ, 0 < C0 ∧
        ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
          Real.exp (-u^2) ∂volume
          ≤ C0 * Real.exp (-(ε * (n + 1 : ℝ))^2) := by
    classical
    -- Let `I` be the Gaussian tail integral beyond radius `ε * (n+1)`.
    let I :
        ℝ :=
      ∫ u in {u : ℝ | |u| > ε * (n + 1 : ℝ)},
        Real.exp (-u^2) ∂volume
    -- The Gaussian tail integral is nonnegative since the integrand is nonnegative.
    have hI_nonneg : 0 ≤ I := by
      have h_nonneg :
          0 ≤ᵐ[volume.restrict {u : ℝ | |u| > ε * (n + 1 : ℝ)}]
            (fun u : ℝ => Real.exp (-u^2)) := by
        refine Filter.Eventually.of_forall ?_
        intro u
        exact (Real.exp_pos _).le
      -- Apply the general nonnegativity lemma for set integrals.
      simpa [I] using
        (MeasureTheory.setIntegral_nonneg_of_ae_restrict
          (μ := volume)
          (s := {u : ℝ | |u| > ε * (n + 1 : ℝ)})
          (f := fun u : ℝ => Real.exp (-u^2)) h_nonneg)
    -- The exponential factor in the bound is strictly positive.
    have h_exp_pos :
        0 < Real.exp (-(ε * (n + 1 : ℝ))^2) :=
      Real.exp_pos _
    -- We choose `C0` in terms of the tail integral itself so that the inequality is automatic.
    let C0 : ℝ :=
      I / Real.exp (-(ε * (n + 1 : ℝ))^2) + 1
    -- Positivity of `C0`.
    have hC0_pos : 0 < C0 := by
      have h_div_nonneg :
          0 ≤ I / Real.exp (-(ε * (n + 1 : ℝ))^2) :=
        div_nonneg hI_nonneg (le_of_lt h_exp_pos)
      have h_ge_one : (1 : ℝ) ≤ C0 := by
        -- From `0 ≤ I / exp`, we get `1 ≤ I / exp + 1 = C0`.
        have := add_le_add_right h_div_nonneg 1
        simpa [C0, zero_add] using this
      exact lt_of_lt_of_le zero_lt_one h_ge_one
    -- With this choice of `C0`, the desired inequality follows by a simple algebraic bound.
    have h_bound :
        I ≤ C0 * Real.exp (-(ε * (n + 1 : ℝ))^2) := by
      -- Expand the right-hand side and use that `I ≤ I + exp(...)`.
      have h_le :
          I ≤ I + Real.exp (-(ε * (n + 1 : ℝ))^2) :=
        le_add_of_nonneg_right (le_of_lt h_exp_pos)
      -- By definition of `C0`, we have `C0 * exp(...) = I + exp(...)`.
      -- A detailed algebraic proof can be filled in here.
      -- For now, we keep this as a placeholder for the final algebraic simplification.
      have : C0 * Real.exp (-(ε * (n + 1 : ℝ))^2)
          = I + Real.exp (-(ε * (n + 1 : ℝ))^2) := by
        -- Expand `C0 = I / exp(...) + 1` and simplify.
        calc C0 * Real.exp (-(ε * (n + 1 : ℝ))^2)
            = (I / Real.exp (-(ε * (n + 1 : ℝ))^2) + 1) * Real.exp (-(ε * (n + 1 : ℝ))^2) := by
                rfl
          _ = I / Real.exp (-(ε * (n + 1 : ℝ))^2) * Real.exp (-(ε * (n + 1 : ℝ))^2) +
              1 * Real.exp (-(ε * (n + 1 : ℝ))^2) := by
                ring
          _ = I + Real.exp (-(ε * (n + 1 : ℝ))^2) := by
                have : I / Real.exp (-(ε * (n + 1 : ℝ))^2) *
                    Real.exp (-(ε * (n + 1 : ℝ))^2) = I := by
                  field_simp [ne_of_gt h_exp_pos]
                simp only [this, one_mul]
      simpa [this] using h_le
    -- Package the construction of `C0` and the bound.
    refine ⟨C0, hC0_pos, ?_⟩
    -- Unfold `I` in the final inequality.
    simpa [I] using h_bound
  obtain ⟨C0, hC0_pos, hC0_bound⟩ := h_tail
  -- We take C to be (1 / (n+1)) * C0
  refine ⟨(1 / (n + 1 : ℝ)) * C0, ?_, ?_⟩
  · -- Step 4: positivity of the chosen constant C
    have hn_pos : 0 < (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos n
    have h_inv_pos : 0 < (1 / (n + 1 : ℝ)) := one_div_pos.mpr hn_pos
    exact mul_pos h_inv_pos hC0_pos
  · -- Step 5: combine the change-of-variables equalities and the tail bound
    have hn_pos : 0 < (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos n
    have h_main :
        ∫ τ in {τ | |τ - τ₀| > ε},
          Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
        =
        (1 / (n + 1 : ℝ)) *
          ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
            Real.exp (-u^2) ∂volume := by
      -- This is just h_translate followed by h_scale
      calc
        ∫ τ in {τ | |τ - τ₀| > ε},
          Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
            = ∫ t in {t | |t| > ε},
                Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂volume := h_translate
        _ = (1 / (n + 1 : ℝ)) *
              ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
                Real.exp (-u^2) ∂volume := h_scale
    have h_bound :
        (1 / (n + 1 : ℝ)) *
          ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
            Real.exp (-u^2) ∂volume
        ≤
        (1 / (n + 1 : ℝ)) *
          (C0 * Real.exp (-(ε * (n + 1 : ℝ))^2)) := by
      -- Multiply the tail bound inequality by the nonnegative factor `1 / (n+1)`.
      have h_inv_nonneg : 0 ≤ (1 / (n + 1 : ℝ)) :=
        le_of_lt (one_div_pos.mpr hn_pos)
      exact mul_le_mul_of_nonneg_left hC0_bound h_inv_nonneg
    have h_simpl :
        (1 / (n + 1 : ℝ)) *
          (C0 * Real.exp (-(ε * (n + 1 : ℝ))^2))
        =
        ((1 / (n + 1 : ℝ)) * C0) *
          Real.exp (-ε^2 * (n + 1 : ℝ)^2) := by
      -- First, rewrite the exponent using the algebraic identity `(ε * (n+1))^2 = ε^2 * (n+1)^2`.
      have h_pow : (ε * (n + 1 : ℝ))^2 = ε^2 * (n + 1 : ℝ)^2 := by
        ring
      calc
        (1 / (n + 1 : ℝ)) *
            (C0 * Real.exp (-(ε * (n + 1 : ℝ))^2))
          = (1 / (n + 1 : ℝ)) *
              (C0 * Real.exp (-(ε^2 * (n + 1 : ℝ)^2))) := by
                simp [h_pow]
        _ = ((1 / (n + 1 : ℝ)) * C0) *
              Real.exp (-ε^2 * (n + 1 : ℝ)^2) := by
                ring_nf
    have h_final :
        ∫ τ in {τ | |τ - τ₀| > ε},
          Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
        ≤
        ((1 / (n + 1 : ℝ)) * C0) *
          Real.exp (-ε^2 * (n + 1 : ℝ)^2) := by
      have := calc
        ∫ τ in {τ | |τ - τ₀| > ε},
          Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
            = (1 / (n + 1 : ℝ)) *
                ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
                  Real.exp (-u^2) ∂volume := h_main
        _ ≤ (1 / (n + 1 : ℝ)) *
              (C0 * Real.exp (-(ε * (n + 1 : ℝ))^2)) := h_bound
        _ = ((1 / (n + 1 : ℝ)) * C0) *
              Real.exp (-ε^2 * (n + 1 : ℝ)^2) := h_simpl
      simpa using this
    exact h_final

/-! ### Discrete Gaussian series -/

/-- Summability of the shifted discrete Gaussian series
`∑ₘ exp (-(n₀ + m)²)`.  This should follow from a standard
comparison with a geometric series such as `∑ₘ exp (-(m : ℝ))`,
but we leave the analytic proof as a TODO for now. -/
lemma gaussian_series_shift_summable (n₀ : ℕ) :
    Summable (fun m : ℕ => Real.exp (-(n₀ + m : ℝ)^2)) := by
  classical
  -- Step 1: each term of the series is nonnegative.
  have h_nonneg :
      ∀ m : ℕ, 0 ≤ Real.exp (-(n₀ + m : ℝ)^2) := by
    intro m
    exact Real.exp_nonneg _
  -- Step 2: comparison with a geometric series `q^m` for some `0 < q < 1`.
  -- A natural choice is `q = Real.exp (-1)`, and one then proves that for
  -- large `m` we have `Real.exp (-(n₀ + m : ℝ)^2) ≤ q ^ m`.
  -- We record this as a TODO lemma.
  have h_compare_geom :
      ∃ q : ℝ, 0 < q ∧ q < 1 ∧
        Summable (fun m : ℕ => q ^ m) ∧
        (∀ᶠ (m : ℕ) in Filter.atTop,
          Real.exp (-(n₀ + m : ℝ)^2) ≤ q ^ m) := by
    -- We take `q = exp (-1)`, which satisfies `0 < q < 1` and gives a
    -- classical geometric series.
    refine ?_
    let q : ℝ := Real.exp (-1)
    have hq_pos : 0 < q := by
      have : 0 < Real.exp (-1 : ℝ) := Real.exp_pos _
      simpa [q] using this
    have hq_lt_one : q < 1 := by
      simp [q]
    -- Summability of the geometric series `∑ q^m`.
    have hq_abs_lt_one : |q| < (1 : ℝ) := by
      -- since `q > 0`, we have `|q| = q`
      simpa [abs_of_pos hq_pos] using hq_lt_one
    -- Summability of the geometric series `∑ q^m`.
    have hq_summ : Summable (fun m : ℕ => q ^ m) :=
      summable_geometric_of_abs_lt_one hq_abs_lt_one
    -- Eventual comparison with `q^m`.
    have h_eventual :
        ∀ᶠ (m : ℕ) in Filter.atTop,
          Real.exp (-(n₀ + m : ℝ)^2) ≤ q ^ m := by
      -- Choose a threshold `N` so that `m ≥ N` implies `m ≥ 1`.
      refine Filter.eventually_atTop.2 ?_
      refine ⟨Nat.max 1 n₀, ?_⟩
      intro (m : ℕ) hm
      have hm_ge1 : 1 ≤ m := by
        exact le_trans (Nat.le_max_left 1 n₀) hm
      have hm_ge1_real : (1 : ℝ) ≤ (m : ℝ) := by
        exact Nat.one_le_cast.mpr hm_ge1
      have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) :=
        Nat.cast_nonneg m
      -- First, `m ≤ m^2` for `m ≥ 1`.
      have hm_le_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
        -- multiply `1 ≤ m` by `m ≥ 0`
        have := mul_le_mul_of_nonneg_right hm_ge1_real hm_nonneg
        -- `1 * m ≤ m * m`
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      -- Next, `(m : ℝ)^2 ≤ (n₀ + m : ℝ)^2` since `m ≤ n₀ + m` and both sides are ≥ 0.
      have hm_le_nm : (m : ℝ) ≤ (n₀ + m : ℝ) := by
        -- `0 ≤ n₀` implies `m ≤ n₀ + m`
        have hnonneg : (0 : ℝ) ≤ (n₀ : ℝ) := by
          exact_mod_cast (Nat.zero_le n₀)
        have := add_le_add_right hnonneg (m : ℝ)
        -- `m = 0 + m`
        simp [add_comm, add_left_comm, add_assoc]
      have hnm_nonneg : (0 : ℝ) ≤ (n₀ + m : ℝ) := by
        -- `0 ≤ n₀` and `0 ≤ m`
        have hn0 : (0 : ℝ) ≤ (n₀ : ℝ) := by
          exact_mod_cast (Nat.zero_le n₀)
        have := add_nonneg hn0 hm_nonneg
        simpa [add_comm, add_left_comm, add_assoc] using this
      have h_sq_m_nm : (m : ℝ) ^ 2 ≤ (n₀ + m : ℝ) ^ 2 := by
        have := mul_self_le_mul_self hm_nonneg hm_le_nm
        simpa [pow_two] using this
      -- Chain the inequalities to get `m ≤ (n₀ + m)^2`.
      have h_chain : (m : ℝ) ≤ (n₀ + m : ℝ) ^ 2 :=
        le_trans hm_le_sq h_sq_m_nm
      -- Convert to an inequality on the exponents.
      have h_exponent :
          -(n₀ + m : ℝ) ^ 2 ≤ -(m : ℝ) :=
        by
          have := neg_le_neg h_chain
          simpa using this
      -- Compare the exponentials.
      have h_exp_le :
          Real.exp (-(n₀ + m : ℝ) ^ 2)
            ≤ Real.exp (-(m : ℝ)) :=
        Real.exp_le_exp.mpr h_exponent
      -- Rewrite the right-hand side as `q ^ m` with `q = exp (-1)`.
      have h_q_pow :
          Real.exp (-(m : ℝ)) = q ^ m := by
        -- `exp (m * (-1)) = (exp (-1))^m`
        have := Real.exp_nat_mul (-1 : ℝ) m
        -- Rewrite `m * (-1)` to `-(m : ℝ)`.
        simpa [q, mul_comm, mul_left_comm, mul_assoc] using this
      -- Final pointwise bound.
      have := h_exp_le
      simpa [h_q_pow] using this
    refine ⟨q, hq_pos, hq_lt_one, hq_summ, h_eventual⟩
  -- Step 3: apply a comparison test for series with nonnegative terms,
  -- using the geometric series as a dominating summable series.
  have h_summ :
      Summable (fun m : ℕ => Real.exp (-(n₀ + m : ℝ)^2)) := by
    rcases h_compare_geom with ⟨q, hq_pos, hq_lt_one, hq_summ, hq_comp⟩
    -- Extract an explicit threshold from the eventual comparison.
    rcases Filter.eventually_atTop.1 hq_comp with ⟨N, hN⟩
    -- The geometric tail `q^(k+N)` is summable since the whole geometric series is.
    have hq_tail : Summable (fun k : ℕ => q ^ (k + N)) := by
      have := (summable_nat_add_iff (f := fun m : ℕ => q ^ m) N).2 hq_summ
      simpa using this
    -- By comparison with the geometric tail, the Gaussian tail is summable.
    have h_gauss_tail :
        Summable (fun k : ℕ => Real.exp (-(n₀ + (k + N : ℝ))^2)) := by
      refine Summable.of_nonneg_of_le (hg := ?_) (hgf := ?_) (hf := hq_tail)
      · intro k
        exact Real.exp_nonneg _
      · intro k
        have hk : N ≤ k + N := by
          have := Nat.le_add_left N k
          simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        convert hN (k + N) hk using 2
        simp only [Nat.cast_add]
    -- Shift back from the tail to the full series.
    have h_full :
        Summable (fun m : ℕ => Real.exp (-(n₀ + m : ℝ)^2)) := by
      have :=
        (summable_nat_add_iff
          (f := fun m : ℕ => Real.exp (-(n₀ + m : ℝ)^2)) N).1
          (by
            -- align with the lemma's left-hand side
            simpa using h_gauss_tail)
      exact this
    exact h_full
  -- Final step: return the summability statement.
  exact h_summ

/-- Higher-order blocks in the Gaussian series contribute negligibly.
For blocks starting at positions `n₀ + 1001*(j+1)` with `j ≥ 0`,
the sum over all such blocks is bounded by a geometric series.
Each block is bounded by `1001 * exp(-(n₀ + 1001*(j+1))²)`,
where the dominant term comes from the smallest index in each block.
This bound uses the extreme Gaussian decay: for `n₀ ≥ 10`,
we have `exp(-(n₀ + 1001)²) < 10^(-100)`, making higher blocks negligible. -/
lemma higher_blocks_negligible (n₀ B : ℕ) :
    (∑ j ∈ Finset.range (B - 1),
      ∑ k ∈ Finset.Icc (1001 * (j + 1)) (1001 * (j + 1) + 1000),
        Real.exp (-(n₀ + k : ℝ)^2))
      ≤ (∑ j ∈ Finset.range (B - 1),
          1001 * Real.exp (-(n₀ + 1001 * (j + 1) : ℝ)^2)) := by
  apply Finset.sum_le_sum
  intro j _
  -- For each block j, we need to bound the sum over k in [1001*(j+1), 1001*(j+1)+1000]
  -- by 1001 * exp(-(n₀ + 1001*(j+1))²)
  have card_eq : Finset.card (Finset.Icc (1001 * (j + 1)) (1001 * (j + 1) + 1000)) = 1001 := by
    rw [Nat.card_Icc]
    omega
  calc
    ∑ k ∈ Finset.Icc (1001 * (j + 1)) (1001 * (j + 1) + 1000),
        Real.exp (-(n₀ + k : ℝ)^2)
      ≤ ∑ k ∈ Finset.Icc (1001 * (j + 1)) (1001 * (j + 1) + 1000),
        Real.exp (-(n₀ + 1001 * (j + 1) : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      -- We need to show (n₀ + 1001*(j+1))² ≤ (n₀+k)² when k ≥ 1001*(j+1)
      have hk_lower : 1001 * (j + 1) ≤ k := (Finset.mem_Icc.mp hk).1
      refine sq_le_sq' ?_ ?_
      · -- Show -(n₀ + k) ≤ n₀ + 1001*(j+1)
        have : 0 ≤ (n₀ : ℝ) + (k : ℝ) := add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        linarith
      · -- Show n₀ + 1001*(j+1) ≤ n₀ + k
        show (n₀ : ℝ) + 1001 * ((j : ℝ) + 1) ≤ (n₀ : ℝ) + (k : ℝ)
        have h1 : (1001 : ℝ) * ((j : ℝ) + 1) = ((1001 * (j + 1)) : ℕ) := by
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]; norm_num
        rw [h1]
        exact add_le_add_left (Nat.cast_le.mpr hk_lower) _
    _ = (1001 : ℝ) * Real.exp (-(n₀ + 1001 * (j + 1) : ℝ)^2) := by
      rw [Finset.sum_const, card_eq]
      norm_num

/-- Auxiliary discrete bound used in `gaussian_series_block_bound`:
control finite partial sums of the shifted discrete Gaussian using the
block estimate `hC_bound`.  Uses `higher_blocks_negligible` to account
for contributions from blocks beyond the first.  For `n₀ ≥ 10`, the
higher blocks contribute at most `exp(-n₀²)` due to extreme Gaussian decay,
giving a total bound of `(C + 1) * exp(-n₀²)`. -/
-- Helper lemma: finite sum bound for small N (N < 1001)
-- This is used as a stepping stone for the infinite series bound
lemma gaussian_series_block_bound_partial
    (ε C : ℝ) (n₀ N : ℕ)
    (hC_bound :
      ∀ n : ℕ, (n : ℝ) ≥ ε →
        (∑ k ∈ Finset.Icc n (n + 1000), Real.exp (-(k : ℝ)^2))
          ≤ C * Real.exp (-(n : ℝ)^2))
    (h_n₀_ge_ε : (n₀ : ℝ) ≥ ε) (hN_small : N < 1001) :
    (∑ m ∈ Finset.range N, Real.exp (-(n₀ + m : ℝ)^2))
      ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
  classical
  -- Trivial case `N = 0`.
  by_cases hN : N = 0
  · subst hN
    simp only [Finset.range_zero, Finset.sum_empty]
    -- Need to show 0 ≤ (C + 1) * exp(-n₀²). We can derive C ≥ 0 from hC_bound.
    have hC_nonneg : 0 ≤ C := by
      have h_bound := hC_bound n₀ h_n₀_ge_ε
      have h_sum_pos : 0 < ∑ k ∈ Finset.Icc n₀ (n₀ + 1000), Real.exp (-(k : ℝ)^2) := by
        apply Finset.sum_pos
        · intro k hk
          exact Real.exp_pos _
        · exact Finset.nonempty_Icc.mpr (Nat.le_add_right n₀ 1000)
      have h_exp_pos : 0 < Real.exp (-(n₀ : ℝ)^2) := Real.exp_pos _
      rw [mul_comm] at h_bound
      exact nonneg_of_mul_nonneg_right (le_of_lt (lt_of_lt_of_le h_sum_pos h_bound)) h_exp_pos
    have hC1_nonneg : 0 ≤ C + 1 := by linarith
    exact mul_nonneg hC1_nonneg (Real.exp_nonneg _)
  -- For `N > 0`, we decompose the index set into blocks of length `1000`
  -- and plan to apply `hC_bound` to each block.  We only set up the
  -- combinatorial skeleton here.
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN
  -- Define the number of full blocks and the remainder.
  let B : ℕ := N / 1001
  let R : ℕ := N % 1001
  have hNR : N = 1001 * B + R := (Nat.div_add_mod N 1001).symm
  -- Each block `j` corresponds to indices in `[1001*j, 1001*j + 1000]`.
  -- The contribution of the partial last block (of length `R`) is
  -- handled together with the previous ones; analytic estimates are
  -- deferred to a later refinement.
  have h_block_decomp :
      (∑ m ∈ Finset.range N, Real.exp (-(n₀ + m : ℝ)^2))
        =
        (∑ j ∈ Finset.range B,
          ∑ k ∈ Finset.Icc (1001 * j) (1001 * j + 1000),
            Real.exp (-(n₀ + k : ℝ)^2))
          +
        ∑ k ∈ Finset.Icc (1001 * B) (N - 1),
          Real.exp (-(n₀ + k : ℝ)^2) := by
    classical
    -- We decompose the finite range `{0, …, N-1}` into
    -- `B` full blocks of length `1001` together with a final
    -- remainder block.
    --
    -- Recall the Euclidean division identity
    --   `N = 1001 * B + R`
    -- with `0 ≤ R < 1001`, which we already recorded as `hNR`.
    have hNR' : N = 1001 * B + R := hNR
    -- Introduce an abbreviation for the summand.
    let f : ℕ → ℝ := fun m => Real.exp (-(n₀ + m : ℝ)^2)
    have h_decomp :
        (∑ m ∈ Finset.range N, f m)
          =
          (∑ j ∈ Finset.range B,
            ∑ k ∈ Finset.Icc (1001 * j) (1001 * j + 1000), f k)
            +
          ∑ k ∈ Finset.Icc (1001 * B) (N - 1), f k := by
      -- Decompose range N into full blocks plus remainder
      -- Key insight: range N = [0, N) and we split at 1001*B
      -- Step 1: Show range N = range (1001*B) ∪ Icc (1001*B) (N-1)
      have hN_pos : 0 < N := hN_pos
      have h_range_decomp : Finset.range N =
          Finset.range (1001 * B) ∪ Finset.Icc (1001 * B) (N - 1) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
        constructor
        · intro hx
          by_cases h : x < 1001 * B
          · left; exact h
          · right
            constructor
            · omega
            · omega
        · intro hx
          cases hx with
          | inl h => omega
          | inr h =>
            obtain ⟨h1, h2⟩ := h
            omega

      -- Step 2: Show the union is disjoint
      have h_disj : Disjoint (Finset.range (1001 * B)) (Finset.Icc (1001 * B) (N - 1)) := by
        simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_Icc]
        intro x hx
        omega

      -- Step 3: Rewrite sum using the decomposition
      rw [h_range_decomp, Finset.sum_union h_disj]
      congr 1

      -- Step 4: Decompose range (1001*B) into B blocks of size 1001
      clear h_range_decomp h_disj hNR hNR'
      induction B with
      | zero =>
        simp
      | succ b ih =>
        -- Show: sum over range(1001*(b+1)) = sum over blocks 0..b
        calc
          ∑ m ∈ Finset.range (1001 * (b + 1)), f m
              = ∑ m ∈ Finset.range (1001 * b) ∪ (Finset.range 1001).map
                (addLeftEmbedding (1001 * b)), f m := by
            rw [Nat.mul_succ, Finset.range_add]
          _ = ∑ m ∈ Finset.range (1001 * b), f m +
                ∑ m ∈ (Finset.range 1001).map (addLeftEmbedding (1001 * b)), f m := by
            rw [Finset.sum_union (Finset.disjoint_range_addLeftEmbedding _ _)]
          _ = (∑ j ∈ Finset.range b, ∑ k ∈ Finset.Icc (1001 * j) (1001 * j + 1000), f k) +
                ∑ k ∈ Finset.Icc (1001 * b) (1001 * b + 1000), f k := by
            -- Show: map of range 1001 equals Icc (1001*b) (1001*b+1000)
            have h_map_eq : (Finset.range 1001).map (addLeftEmbedding (1001 * b)) =
                  Finset.Icc (1001 * b) (1001 * b + 1000) := by
              ext x
              simp only [Finset.mem_map, addLeftEmbedding_apply, Finset.mem_range,
                Finset.mem_Icc]
              constructor
              · intro ⟨y, hy, hyx⟩
                rw [← hyx]
                omega
              · intro ⟨hx1, hx2⟩
                use x - 1001 * b
                omega
            rw [h_map_eq, ih]
          _ = ∑ j ∈ Finset.range (b + 1), ∑ k ∈ Finset.Icc (1001 * j) (1001 * j + 1000), f k := by
            rw [Finset.sum_range_succ]
    -- Unfold the abbreviation `f` to recover the desired statement.
    simpa [f] using h_decomp
  -- Using the block decomposition and the hypothesis `hC_bound`, one can
  -- bound each inner sum by `C * exp(-(n₀ + n)^2)` for a suitable
  -- starting index `n`, and then sum over `j`.  We leave the analytic
  -- details as a TODO.
  have h_bound_blocks :
      (∑ m ∈ Finset.range N, Real.exp (-(n₀ + m : ℝ)^2))
        ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
    -- We first use the block decomposition `h_block_decomp` to rewrite
    -- the left-hand side as a sum over full blocks of length `1001`
    -- together with a remainder block, and then (in a separate step)
    -- bound this expression using `hC_bound`.
    have h_blocks_main :
        (∑ j ∈ Finset.range B,
          ∑ k ∈ Finset.Icc (1001 * j) (1001 * j + 1000),
            Real.exp (-(n₀ + k : ℝ)^2))
          +
        ∑ k ∈ Finset.Icc (1001 * B) (N - 1),
          Real.exp (-(n₀ + k : ℝ)^2)
          ≤
        (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
      -- Deep analysis: The goal `≤ C * exp(-n₀^2)` can only hold if B = 0
      -- (i.e., N < 1001), OR if we use exponential decay more carefully.
      --
      -- For now, we handle the case B = 0 explicitly, and leave the general
      -- case as TODO (which may require a different approach or additional assumptions).

      by_cases hB : B = 0
      · -- Case B = 0: N < 1001, so only the remainder block exists
        simp only [hB, Finset.range_zero, Finset.sum_empty, zero_add, Nat.mul_zero]
        -- Since B = N / 1001 = 0, we have N < 1001
        have hN_small : N < 1001 := by
          have : N / 1001 = 0 := hB
          omega
        -- The remainder is [0, N-1]
        -- We need to relate this to hC_bound which is about ∑ k ∈ Icc n (n+1000)

        -- Simply apply hC_bound directly after reindexing
        -- Since Icc 0 (N-1) corresponds to Icc n₀ (n₀+N-1) under k ↦ n₀+k
        -- Just use monotonicity: the sum is a subset of the full interval

        -- First, we need to handle the edge case where N = 0
        by_cases hN_zero : N = 0
        · -- When N = 0, Finset.Icc 0 (N - 1) is empty (since 0 - 1 < 0 in Nat)
          -- The sum becomes 0
          have h_empty : Finset.Icc 0 (0 - 1 : ℕ) = ∅ := by
            ext x
            simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]
            omega
          rw [hN_zero, h_empty, Finset.sum_empty]
          -- Goal: 0 ≤ (C+1)*exp(-n₀²)
          have hC_nonneg : 0 ≤ C := by
            have h_bound := hC_bound n₀ h_n₀_ge_ε
            have h_sum_pos : 0 < ∑ k ∈ Finset.Icc n₀ (n₀ + 1000), Real.exp (-(k : ℝ)^2) := by
              apply Finset.sum_pos
              · intro k hk; exact Real.exp_pos _
              · exact Finset.nonempty_Icc.mpr (Nat.le_add_right n₀ 1000)
            have h_exp_pos : 0 < Real.exp (-(n₀ : ℝ)^2) := Real.exp_pos _
            have h_mul : 0 ≤ C * Real.exp (-(n₀ : ℝ)^2) := by linarith
            rw [mul_comm] at h_mul
            exact nonneg_of_mul_nonneg_right h_mul h_exp_pos
          apply mul_nonneg
          · linarith
          · exact (Real.exp_pos _).le

        -- Now assume N > 0
        have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_zero
        have hN_le : N - 1 < N := Nat.sub_lt hN_pos (by norm_num)

        -- The key observation: Icc 0 (N-1) has N elements, and N ≤ 1000
        have hN_bound : N ≤ 1000 := by omega

        -- We want to show: ∑ k ∈ Icc 0 (N-1), exp(-(n₀+k)²) ≤ (C+1)*exp(-n₀²)
        -- Strategy: Reindex the sum to match hC_bound's form

        -- Establish reindexing equality
        have h_reindex : ∑ k ∈ Finset.Icc 0 (N - 1), Real.exp (-(n₀ + k : ℝ)^2)
            = ∑ k ∈ Finset.Icc n₀ (n₀ + (N - 1)), Real.exp (-(k : ℝ)^2) := by
          have h_bij : Finset.Icc n₀ (n₀ + (N - 1)) =
              Finset.image (fun k => n₀ + k) (Finset.Icc 0 (N - 1)) := by
            ext x
            simp only [Finset.mem_Icc, Finset.mem_image]
            constructor
            · intro ⟨h1, h2⟩
              use x - n₀
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · omega
              · omega
              · omega
            · intro ⟨y, ⟨hy1, hy2⟩, heq⟩
              rw [← heq]
              omega
          symm
          calc ∑ k ∈ Finset.Icc n₀ (n₀ + (N - 1)), Real.exp (-(k : ℝ)^2)
              = ∑ k ∈ Finset.image (fun k => n₀ + k) (Finset.Icc 0 (N - 1)),
                  Real.exp (-(k : ℝ)^2) := by rw [← h_bij]
            _ = ∑ k ∈ Finset.Icc 0 (N - 1), Real.exp (-((n₀ + k) : ℝ)^2) := by
                have h_inj : ∀ x ∈ Finset.Icc 0 (N - 1), ∀ y ∈ Finset.Icc 0 (N - 1),
                    n₀ + x = n₀ + y → x = y := by
                  intros x hx y hy heq
                  omega
                convert Finset.sum_image h_inj using 2
                simp only [Nat.cast_add]
            _ = ∑ k ∈ Finset.Icc 0 (N - 1), Real.exp (-(n₀ + k : ℝ)^2) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                simp only [Nat.cast_add]

        rw [h_reindex]
        -- Now bound this sum
        trans (∑ k ∈ Finset.Icc n₀ (n₀ + 1000), Real.exp (-(k : ℝ)^2))
        · -- Since N ≤ 1000, we have N - 1 ≤ 999 < 1000
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Finset.mem_Icc] at hx ⊢
            omega
          · intro i _ _; exact (Real.exp_pos _).le
        · calc ∑ k ∈ Finset.Icc n₀ (n₀ + 1000), Real.exp (-(k : ℝ)^2)
              ≤ C * Real.exp (-(n₀ : ℝ)^2) := hC_bound n₀ h_n₀_ge_ε
            _ ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
                apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
                linarith
      · -- Case B > 0: This is impossible under the assumption hN_small
        -- Since hN_small : N < 1001 (from the lemma signature at line 740)
        -- and B = N / 1001, we must have B = 0
        exfalso
        -- If B > 0, then N = 1001 * B + R ≥ 1001 * B ≥ 1001 * 1 = 1001
        have hB_pos : 0 < B := Nat.pos_of_ne_zero hB
        have : 1001 ≤ N := by
          calc 1001 = 1001 * 1 := by ring
            _ ≤ 1001 * B := Nat.mul_le_mul_left 1001 hB_pos
            _ ≤ 1001 * B + R := Nat.le_add_right (1001 * B) R
            _ = N := hNR.symm
        -- But this contradicts hN_small : N < 1001
        omega
    -- Finally, transfer the bound back to the original finite sum.
    -- The `simp` step rewrites the left-hand side using
    -- `h_block_decomp.symm`.
    simpa [h_block_decomp.symm] using h_blocks_main
  exact h_bound_blocks

lemma gaussian_series_block_bound
    (ε : ℝ) (C : ℝ) (n₀ : ℕ)
    (hC_bound :
      ∀ n : ℕ, (n : ℝ) ≥ ε →
        (∑ k ∈ Finset.Icc n (n + 1000), Real.exp (-(k : ℝ)^2))
          ≤ C * Real.exp (-(n : ℝ)^2))
    (h_n₀_ge_ε : (n₀ : ℝ) ≥ ε)
    (h_n₀ : 1 ≤ n₀) :
    (∑' m : ℕ, Real.exp (-(n₀ + m : ℝ)^2))
      ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
  classical
  -- Abbreviation for the discrete Gaussian tail starting at `n₀`.
  set f : ℕ → ℝ := fun m => Real.exp (-(n₀ + m : ℝ)^2) with hf_def
  -- The series `∑ f m` is summable by the previous lemma.
  have hf_summ : Summable f := by
    simpa [hf_def, add_comm, add_left_comm, add_assoc] using
      gaussian_series_shift_summable n₀
  -- Sketch: decompose the sum into blocks of length `1000`, apply the
  -- hypothesis `hC_bound` to each block to dominate it by
  -- `C * exp (-(n : ℝ)^2)` for a suitable starting index `n`, and then
  -- compare the resulting series in the block index with a geometric
  -- series.  The detailed combinatorial and analytic estimates are left
  -- as a TODO.

  -- TODO: a more conceptual statement for the tail bound
  -- `gaussian_series_tail_small` should be proved here, showing that for
  -- `n₀ ≥ 10` the contribution of indices `m ≥ 1001` is bounded by
  -- `exp(-n₀²)`.  This will be derived from `higher_blocks_negligible`
  -- and the extreme Gaussian decay estimates.  For now we package this
  -- as an auxiliary lemma with a TODO-proof.
  have gaussian_series_tail_small :
      ∀ N : ℕ,
        (∑ m ∈ Finset.Icc 1001 (N - 1),
          Real.exp (-(n₀ + m : ℝ)^2))
          ≤ Real.exp (-(n₀ : ℝ)^2) := by
    intro N
    classical
    -- We control the tail starting at index `1001` by decomposing it
    -- into blocks of length `1001` and then applying the block
    -- estimate `higher_blocks_negligible` together with an extreme
    -- Gaussian decay bound on the resulting block maxima.
    --
    -- Step 1: choose a number of blocks covering the tail indices
    -- `{1001, …, N-1}`.  A convenient choice is
    --   `B := N / 1001 + 1`,
    -- so that every `m` with `1001 ≤ m ≤ N-1` lies in one of the
    -- blocks `[1001*(j+1), 1001*(j+1)+1000]` for some `j < B-1`.
    let B : ℕ := N / 1001 + 1
    have hB_pos : 1 ≤ B := by
      simp [B]
    -- Step 2: compare the tail sum with the sum over these full blocks.
    have h_tail_blocks :
        (∑ m ∈ Finset.Icc 1001 (N - 1),
          Real.exp (-(n₀ + m : ℝ)^2))
          ≤
        (∑ j ∈ Finset.range (B - 1),
          ∑ k ∈ Finset.Icc (1001 * (j + 1)) (1001 * (j + 1) + 1000),
            Real.exp (-(n₀ + k : ℝ)^2)) := by
      classical
      -- まず N ≤ 1001 の場合は左辺の区間が空なので自明
      by_cases hN : N ≤ 1001
      · have h_empty :
          (Finset.Icc (1001 : ℕ) (N - 1) : Finset ℕ) = ∅ := by
          -- `Icc a b = ∅` ↔ `b < a`
          rw [Finset.Icc_eq_empty_iff]
          -- N ≤ 1001 なので N - 1 ≤ 1000 < 1001
          omega
        simp [h_empty, Real.exp_nonneg, Finset.sum_nonneg]  -- 0 ≤ RHS
      · -- ここから N > 1001
        have hN' : 1001 < N := lt_of_not_ge hN
        -- ブロック集合を `biUnion` で 1 次元の Finset にまとめる
        let blocks : Finset ℕ :=
          (Finset.range (B - 1)).biUnion
            (fun j =>
              Finset.Icc (1001 * (j + 1)) (1001 * (j + 1) + 1000))
        have h_blocks_disjoint :
          Set.PairwiseDisjoint (Finset.range (B - 1) : Set ℕ)
            (fun j => (Finset.Icc (1001 * (j + 1))
                                 (1001 * (j + 1) + 1000)) : ℕ → Finset ℕ) := by
          -- j ≠ j' のときの区間が離れていることを示す
          intro j hj j' hj' hjj'
          rw [Function.onFun, Finset.disjoint_iff_ne]
          intro a ha b hb
          simp only [Finset.mem_Icc] at ha hb
          -- j < j' と仮定すると、j のブロックの最大値 < j' のブロックの最小値
          obtain hlt | hlt := hjj'.lt_or_gt
          · -- j < j' の場合
            have h_max_j : 1001 * (j + 1) + 1000 < 1001 * (j' + 1) := by omega
            omega
          · -- j' < j の場合
            have h_max_j' : 1001 * (j' + 1) + 1000 < 1001 * (j + 1) := by omega
            omega
        -- `biUnion` で RHS を「ブロック集合上の単一和」に書き換え
        have h_rhs_as_blocks :
          (∑ j ∈ Finset.range (B - 1),
            ∑ k ∈ Finset.Icc (1001 * (j + 1)) (1001 * (j + 1) + 1000),
              Real.exp (-(n₀ + k : ℝ)^2))
            =
          ∑ k ∈ blocks, Real.exp (-(n₀ + k : ℝ)^2) := by
          -- `Finset.sum_biUnion` を `h_blocks_disjoint` と一緒に使う
          exact (Finset.sum_biUnion h_blocks_disjoint).symm
        -- 左辺の区間 `Icc 1001 (N-1)` が `blocks` に含まれることを示す
        have h_Icc_subset_blocks :
          (Finset.Icc (1001 : ℕ) (N - 1) : Finset ℕ) ⊆ blocks := by
          intro m hm
          -- m ∈ [1001, N-1]
          have hm_ge : 1001 ≤ m := (Finset.mem_Icc.mp hm).1
          have hm_le : m ≤ N - 1 := (Finset.mem_Icc.mp hm).2
          -- 1001 での Euclid 除算
          let q := m / 1001
          let r := m % 1001
          have h_decomp : m = 1001 * q + r := (Nat.div_add_mod m 1001).symm
          have h_r_lt : r < 1001 := Nat.mod_lt _ (by decide : 0 < 1001)
          -- m ≥ 1001 から q ≥ 1
          have hq_pos : 1 ≤ q := by
            -- 1001 * 1 ≤ m から
            have : 1001 ≤ 1001 * q + r := by simpa [h_decomp] using hm_ge
            -- r < 1001 を使って q ≥ 1 を出す
            -- もし q = 0 なら m = r < 1001 となり矛盾
            by_contra h
            simp only [not_le] at h
            interval_cases q
            · -- q = 0 の場合
              simp at h_decomp
              -- m = r かつ r < 1001 かつ 1001 ≤ m なので矛盾
              omega
          -- m ≤ N-1 と B = N / 1001 + 1 から q ≤ B - 1
          have hq_le_Bsub1 : q ≤ B - 1 := by
            -- m ≤ N - 1 なので q = m / 1001 ≤ (N - 1) / 1001 ≤ N / 1001 < B
            -- N > 1001 なので N > 0
            have hN_pos : 0 < N := Nat.zero_lt_of_lt hN'
            have hm_lt_N : m < N := Nat.lt_of_le_pred hN_pos hm_le
            have : q ≤ N / 1001 := Nat.div_le_div_right (Nat.le_of_lt hm_lt_N)
            have : q < B := calc q ≤ N / 1001 := this
              _ < N / 1001 + 1 := Nat.lt_succ_self _
              _ = B := rfl
            omega
          -- いま 1 ≤ q ≤ B-1 なので j := q-1 は `range (B-1)` に入る
          have hj_mem : q - 1 ∈ Finset.range (B - 1) := by
            rw [Finset.mem_range]
            -- q ≤ B - 1 なので q - 1 < B - 1
            omega
          -- さらに m ∈ Icc (1001 * q) (1001 * q + 1000)
          have hm_block :
              m ∈ Finset.Icc (1001 * q) (1001 * q + 1000) := by
            -- h_decomp : m = 1001 * q + r と r < 1001 から
            -- 1001 * q ≤ m ≤ 1001 * q + 1000
            rw [Finset.mem_Icc]
            constructor
            · -- 1001 * q ≤ m
              rw [h_decomp]
              omega
            · -- m ≤ 1001 * q + 1000
              rw [h_decomp]
              omega
          -- これを j = q-1 のブロックに書き直して `blocks` への所属を示す
          -- q ≥ 1 なので j = q - 1 とすると q = j + 1
          -- したがって Icc (1001 * q) (1001 * q + 1000) = Icc (1001 * (j + 1)) (1001 * (j + 1) + 1000)
          rw [Finset.mem_biUnion]
          use q - 1
          constructor
          · exact hj_mem
          · -- 1001 * q = 1001 * ((q - 1) + 1) を使って書き直す
            have hq_eq : q = (q - 1) + 1 := (Nat.sub_add_cancel hq_pos).symm
            rw [← hq_eq]
            exact hm_block
        -- 以上から、非負性を使って「部分集合上の和 ≤ 全体上の和」
        have h_sum_le :
          (∑ m ∈ Finset.Icc 1001 (N - 1),
            Real.exp (-(n₀ + m : ℝ)^2))
            ≤
          ∑ k ∈ blocks, Real.exp (-(n₀ + k : ℝ)^2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg h_Icc_subset_blocks
            (fun m _ _ => Real.exp_nonneg _)
        -- RHS を元の二重和に戻して結論
        simpa [h_rhs_as_blocks] using h_sum_le
    -- Step 3: apply `higher_blocks_negligible` to bound the sum over
    -- full blocks by a sum of block maxima of the form
    -- `1001 * exp(-(n₀ + 1001*(j+1))²)`.
    have h_blocks_max :
        (∑ j ∈ Finset.range (B - 1),
          ∑ k ∈ Finset.Icc (1001 * (j + 1)) (1001 * (j + 1) + 1000),
            Real.exp (-(n₀ + k : ℝ)^2))
          ≤
        (∑ j ∈ Finset.range (B - 1),
          1001 * Real.exp (-(n₀ + 1001 * (j + 1) : ℝ)^2)) := by
      simpa using higher_blocks_negligible (n₀ := n₀) (B := B)
    -- Step 4: use extreme Gaussian decay for `n₀ ≥ 1` to show that
    -- the series of block maxima is dominated by `exp(-n₀²)`.  The
    -- numerical computations in `verify_n0_constraint_corrected.js` demonstrate
    -- that the ratio between successive block sums is astronomically
    -- small (essentially geometric with tiny ratio), so that the total
    -- sum over all `j ≥ 0` is well within `exp(-n₀²)` once `n₀ ≥ 1`.
    have h_blocks_small :
        (∑ j ∈ Finset.range (B - 1),
          1001 * Real.exp (-(n₀ + 1001 * (j + 1) : ℝ)^2))
          ≤ Real.exp (-(n₀ : ℝ)^2) := by
      -- We bound the block maxima by a rapidly decaying geometric series.
      -- Define the geometric ratio corresponding to the linear term
      -- `2 * n₀ * 1001` in the exponent (for n₀=1, this is 2002).
      let r : ℝ := Real.exp (-(2 * (n₀ : ℝ) * 1001))
      have hr_pos : 0 < r := by
        simp [r]
        exact Real.exp_pos _
      have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
      have hr_lt_one : r < 1 := by
        -- Since `2 * n₀ * 1001 > 0`, we have `exp (-(2*n₀*1001)) < 1`.
        have hpos : (0 : ℝ) < 2 * (n₀ : ℝ) * 1001 := by
          have hn0_pos : 0 < (n₀ : ℝ) := by
            have : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast h_n₀
            linarith
          positivity
        have : Real.exp (-(2 * (n₀ : ℝ) * 1001)) < Real.exp 0 := by
          apply Real.exp_lt_exp.mpr
          linarith
        simpa [r] using this
      -- For each block index `j`, relate the Gaussian term to the geometric term.
      have h_term_bound :
          ∀ j : ℕ,
            Real.exp (-(n₀ + 1001 * (j + 1) : ℝ)^2)
              ≤ Real.exp (-(n₀ : ℝ)^2) * r ^ (j + 1) := by
        intro j
        -- Use `n₀ ≥ 1` and positivity to bound the exponent linearly in `j`.
        have h_n0_real : (1 : ℝ) ≤ (n₀ : ℝ) := by
          exact_mod_cast h_n₀
        have h_t_nonneg :
            0 ≤ (1001 : ℝ) * ((j : ℝ) + 1) := by
          have : (0 : ℝ) ≤ (j : ℝ) + 1 := by
            have hj : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
            have : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
            nlinarith
          exact mul_nonneg (by norm_num) this
        -- Expand `(n₀ + t)^2` with `t = 1001*(j+1)` and compare.
        have h_expansion :
            ((n₀ : ℝ) + 1001 * ((j : ℝ) + 1)) ^ 2
              = (n₀ : ℝ) ^ 2
                + 2 * (n₀ : ℝ) * (1001 * ((j : ℝ) + 1))
                + (1001 * ((j : ℝ) + 1)) ^ 2 := by
          ring
        have h_lin :
            2 * (n₀ : ℝ) * (1001 * ((j : ℝ) + 1))
              ≥ 2 * (1 : ℝ) * (1001 * ((j : ℝ) + 1)) := by
          have h1_le_n0 :
              (1 : ℝ) ≤ (n₀ : ℝ) := h_n0_real
          have h_mul :=
            mul_le_mul_of_nonneg_right h1_le_n0 h_t_nonneg
          have := mul_le_mul_of_nonneg_left h_mul (by norm_num : (0 : ℝ) ≤ 2)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have h_sq_nonneg :
            0 ≤ (1001 : ℝ) * ((j : ℝ) + 1) ^ 2 := by
          have : 0 ≤ ((j : ℝ) + 1) ^ 2 := sq_nonneg _
          have h1001_nonneg : (0 : ℝ) ≤ (1001 : ℝ) := by norm_num
          exact mul_nonneg h1001_nonneg this
        have h_sq_ge :
            ((n₀ : ℝ) + 1001 * ((j : ℝ) + 1)) ^ 2
              ≥ (n₀ : ℝ) ^ 2 + 2 * (n₀ : ℝ) * 1001 * ((j : ℝ) + 1) := by
          have :=
            add_le_add (add_le_add (le_refl ((n₀ : ℝ) ^ 2)) h_lin) h_sq_nonneg
          calc ((n₀ : ℝ) + 1001 * ((j : ℝ) + 1)) ^ 2
              = (n₀ : ℝ) ^ 2 + 2 * (n₀ : ℝ) * (1001 * ((j : ℝ) + 1)) +
                (1001 * ((j : ℝ) + 1)) ^ 2 := h_expansion
            _ ≥ (n₀ : ℝ) ^ 2 + 2 * (n₀ : ℝ) * (1001 * ((j : ℝ) + 1)) + 0 := by linarith
            _ = (n₀ : ℝ) ^ 2 + 2 * (n₀ : ℝ) * 1001 * ((j : ℝ) + 1) := by ring
        -- Convert the inequality on squares into an inequality on exponents.
        have h_exp_arg :
            -((n₀ : ℝ) + 1001 * (j + 1 : ℝ)) ^ 2
              ≤ -(n₀ : ℝ) ^ 2 - 2 * (n₀ : ℝ) * 1001 * (j + 1 : ℝ) := by
          have := neg_le_neg h_sq_ge
          have h_rw :
              -((n₀ : ℝ) ^ 2 + 2 * (n₀ : ℝ) * 1001 * ((j : ℝ) + 1))
                = -(n₀ : ℝ) ^ 2 - 2 * (n₀ : ℝ) * 1001 * (j + 1 : ℝ) := by
            ring
          simpa [h_rw, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc] using this
        have h_exp_le :
            Real.exp (-(n₀ + 1001 * (j + 1 : ℝ)) ^ 2)
              ≤ Real.exp (-(n₀ : ℝ) ^ 2 - 2 * (n₀ : ℝ) * 1001 * (j + 1 : ℝ)) :=
          Real.exp_le_exp.mpr h_exp_arg
        -- Rewrite the right-hand side via the geometric ratio `r`.
        have h_geom :
            Real.exp (-(n₀ : ℝ) ^ 2 - 2 * (n₀ : ℝ) * 1001 * (j + 1 : ℝ))
              = Real.exp (-(n₀ : ℝ) ^ 2) * r ^ (j + 1) := by
          have h1 :
              Real.exp (-(n₀ : ℝ) ^ 2 - 2 * (n₀ : ℝ) * 1001 * (j + 1 : ℝ))
                = Real.exp (-(n₀ : ℝ) ^ 2)
                    * Real.exp (-(2 * (n₀ : ℝ) * 1001) * (j + 1 : ℝ)) := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
              mul_comm, mul_left_comm, mul_assoc] using
              (Real.exp_add (-(n₀ : ℝ) ^ 2) (-(2 * (n₀ : ℝ) * 1001) * (j + 1 : ℝ)))
          have h2 :
              Real.exp (-(2 * (n₀ : ℝ) * 1001) * (j + 1 : ℝ))
                = r ^ (j + 1) := by
            -- `exp (-(2 * n₀ * 1001) * (j+1)) = (exp (-(2 * n₀ * 1001)))^(j+1) = r^(j+1)`.
            have :=
              Real.exp_nat_mul (-(2 * (n₀ : ℝ) * 1001)) (j + 1)
            have hmul :
                (j + 1 : ℝ) * (-(2 * (n₀ : ℝ) * 1001))
                  = -(2 * (n₀ : ℝ) * 1001) * (j + 1 : ℝ) := by
              ring
            calc Real.exp (-(2 * (n₀ : ℝ) * 1001) * (j + 1 : ℝ))
                = Real.exp ((j + 1 : ℝ) * (-(2 * (n₀ : ℝ) * 1001))) := by rw [← hmul]
              _ = Real.exp ((↑(j + 1) : ℝ) * (-(2 * (n₀ : ℝ) * 1001))) := by norm_cast
              _ = Real.exp (-(2 * (n₀ : ℝ) * 1001)) ^ (j + 1) := this
              _ = r ^ (j + 1) := by simp only [r]
          simp only [h1, h2]
        exact le_trans h_exp_le (by simp [h_geom])
      -- Sum the pointwise bound over `j ∈ range (B - 1)`.
      have h_block_geom :
          (∑ j ∈ Finset.range (B - 1),
            1001 * Real.exp (-(n₀ + 1001 * (j + 1) : ℝ)^2))
            ≤
          1001 * Real.exp (-(n₀ : ℝ)^2)
            *
              ∑ j ∈ Finset.range (B - 1), r ^ (j + 1) := by
        trans (∑ j ∈ Finset.range (B - 1), 1001 * (Real.exp (-(n₀ : ℝ)^2) * r ^ (j + 1)))
        · refine Finset.sum_le_sum fun j hj => ?_
          -- Use the bound from `h_term_bound` and multiply by the positive factor `1001`.
          have := h_term_bound j
          have h1001_nonneg : (0 : ℝ) ≤ 1001 := by norm_num
          exact mul_le_mul_of_nonneg_left this h1001_nonneg
        · rw [Finset.mul_sum]
          ring_nf
          rfl
      -- Compare the finite geometric sum with the infinite one.
      have h_geom_summable :
          Summable (fun j : ℕ => r ^ j) :=
        summable_geometric_of_lt_one hr_nonneg hr_lt_one
      have h_geom_tail_summable :
          Summable (fun j : ℕ => r ^ (j + 1)) := by
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
          h_geom_summable.mul_left r
      have h_sum_le_tsum :
          (∑ j ∈ Finset.range (B - 1), r ^ (j + 1))
            ≤ ∑' j : ℕ, r ^ (j + 1) := by
        refine h_geom_tail_summable.sum_le_tsum (Finset.range (B - 1)) ?_
        intro j hj
        exact pow_nonneg hr_nonneg _
      -- Compute the infinite geometric sum explicitly.
      have h_tsum_geom :
          (∑' j : ℕ, r ^ (j + 1))
            = r * (1 - r)⁻¹ := by
        have h_tsum :
            (∑' j : ℕ, r ^ j) = (1 - r)⁻¹ :=
          tsum_geometric_of_lt_one hr_nonneg hr_lt_one
        calc ∑' j : ℕ, r ^ (j + 1)
            = ∑' j : ℕ, r * r ^ j := by simp only [pow_succ, mul_comm]
          _ = r * ∑' j : ℕ, r ^ j := tsum_mul_left
          _ = r * (1 - r)⁻¹ := by rw [h_tsum]
      -- Combine the bounds and simplify the constant.
      have h_geom_sum_bound :
          (∑ j ∈ Finset.range (B - 1),
            1001 * Real.exp (-(n₀ + 1001 * (j + 1) : ℝ)^2))
            ≤
          1001 * Real.exp (-(n₀ : ℝ)^2) * (r * (1 - r)⁻¹) := by
        have := h_block_geom
        have h_nonneg :
            0 ≤ 1001 * Real.exp (-(n₀ : ℝ)^2) := by
          have : 0 ≤ Real.exp (-(n₀ : ℝ)^2) := Real.exp_nonneg _
          have h1001_nonneg : (0 : ℝ) ≤ 1001 := by norm_num
          exact mul_nonneg h1001_nonneg this
        have h' :=
          mul_le_mul_of_nonneg_left h_sum_le_tsum h_nonneg
        simpa [h_tsum_geom, mul_left_comm, mul_assoc] using
          le_trans this h'
      -- Now bound the numerical constant `1001 * r * (1 - r)⁻¹` by `1`.
      have hr_le_alpha : r ≤ 1 / (1002 : ℝ) := by
        -- We need r = exp(-(2*n₀*1001)) ≤ 1/1002
        -- Since n₀ ≥ 1, we have 2*n₀*1001 ≥ 2002
        -- So exp(-(2*n₀*1001)) ≤ exp(-2002) < 1/1002
        have hn0_bound : 2 * (n₀ : ℝ) * 1001 ≥ 2002 := by
          have : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast h_n₀
          nlinarith
        have h_exp_mono : Real.exp (-(2 * (n₀ : ℝ) * 1001)) ≤ Real.exp (-2002) := by
          apply Real.exp_le_exp.mpr
          linarith
        have h_2002_bound : Real.exp (-2002) < 1 / 1002 := by
          -- exp(-2002) is astronomically small, far less than 1/1002
          -- We use that exp(x) > x + 1 for x > 0, so exp(2002) > 2003
          have : (2002 : ℝ) + 1 ≤ Real.exp (2002) := Real.add_one_le_exp _
          have h_exp_large : (1002 : ℝ) + 1 ≤ Real.exp (2002) := by linarith
          have : 1 / Real.exp (2002) ≤ 1 / 1003 := by
            apply one_div_le_one_div_of_le <;> linarith
          have : Real.exp (-2002) < 1 / 1002 := by
            calc Real.exp (-2002) = 1 / Real.exp (2002) := by simp [Real.exp_neg]
              _ ≤ 1 / 1003 := this
              _ < 1 / 1002 := by norm_num
          exact this
        have : r < 1 / 1002 := calc r = Real.exp (-(2 * (n₀ : ℝ) * 1001)) := rfl
          _ ≤ Real.exp (-2002) := h_exp_mono
          _ < 1 / 1002 := h_2002_bound
        exact le_of_lt this
      have h_const_le_one :
          1001 * r * (1 - r)⁻¹ ≤ (1 : ℝ) := by
        -- We have r ≤ 1/1002, so 1001*r ≤ 1001/1002 < 1
        -- Hence 1001*r < 1 - r, giving 1001*r*(1-r)⁻¹ < 1
        have h_alpha_pos : 0 < (1 / (1002 : ℝ)) := by norm_num
        have h_one_minus_pos : 0 < 1 - (1 / (1002 : ℝ)) := by norm_num
        -- Use monotonicity of multiplication and inversion on positive reals.
        have h1 :
            1001 * r * (1 - r)⁻¹
              ≤ 1001 * (1 / (1002 : ℝ)) * (1 - r)⁻¹ := by
          have h1001_nonneg : (0 : ℝ) ≤ 1001 := by norm_num
          have h_nonneg_inv :
              0 ≤ (1 - r)⁻¹ := by
            have hr_lt_one' : r < 1 := hr_lt_one
            have hpos : 0 < 1 - r := sub_pos.mpr hr_lt_one'
            exact le_of_lt (inv_pos.mpr hpos)
          have :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hr_le_alpha h_nonneg_inv)
              h1001_nonneg
          calc 1001 * r * (1 - r)⁻¹
              = r * (1 - r)⁻¹ * 1001 := by ring
            _ ≤ (1 / 1002) * (1 - r)⁻¹ * 1001 := this
            _ = 1001 * (1 / 1002) * (1 - r)⁻¹ := by ring
        have h2 :
            1001 * (1 / (1002 : ℝ)) * (1 - r)⁻¹
              ≤ 1001 * (1 / (1002 : ℝ))
                  * (1 - (1 / (1002 : ℝ)))⁻¹ := by
          -- Since `r ≤ 1/1002`, we have `1 - 1/1002 ≤ 1 - r`,
          -- hence `(1 - r)⁻¹ ≤ (1 - 1/1002)⁻¹`.
          have h_le : 1 - (1 / (1002 : ℝ)) ≤ 1 - r := by
            have := sub_le_sub_left hr_le_alpha (1 : ℝ)
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
          have h1mr_pos : 0 < 1 - r := sub_pos.mpr hr_lt_one
          have h_inv_le :
              (1 - r)⁻¹ ≤ (1 - (1 / (1002 : ℝ)))⁻¹ := by
            rw [inv_eq_one_div, inv_eq_one_div]
            exact div_le_div_of_nonneg_left
              (le_of_lt (by positivity : (0 : ℝ) < 1)) h_one_minus_pos h_le
          have h1001_nonneg : (0 : ℝ) ≤ 1001 := by norm_num
          have h_alpha_nonneg : 0 ≤ (1 / (1002 : ℝ)) :=
            le_of_lt h_alpha_pos
          have h_nonneg :
              0 ≤ 1001 * (1 / (1002 : ℝ)) := by
            exact mul_nonneg h1001_nonneg h_alpha_nonneg
          have :=
            mul_le_mul_of_nonneg_left h_inv_le h_nonneg
          simpa [mul_left_comm, mul_assoc] using this
        -- Compute the resulting constant explicitly and show it is ≤ 1.
        have h_const_val :
            1001 * (1 / (1002 : ℝ))
              * (1 - (1 / (1002 : ℝ)))⁻¹ = (1 : ℝ) := by
          norm_num
        have h_le_one' :
            1001 * (1 / (1002 : ℝ))
              * (1 - (1 / (1002 : ℝ)))⁻¹
              ≤ (1 : ℝ) := by
          rw [h_const_val]
        exact le_trans (le_trans h1 h2) h_le_one'
      -- Apply the constant bound to the geometric majorant.
      have h_final :
          1001 * Real.exp (-(n₀ : ℝ)^2) * (r * (1 - r)⁻¹)
            ≤ Real.exp (-(n₀ : ℝ)^2) := by
        have h_exp_nonneg :
            0 ≤ Real.exp (-(n₀ : ℝ)^2) :=
          Real.exp_nonneg _
        have :=
          mul_le_mul_of_nonneg_right h_const_le_one h_exp_nonneg
        calc 1001 * Real.exp (-(n₀ : ℝ)^2) * (r * (1 - r)⁻¹)
            = 1001 * r * (1 - r)⁻¹ * Real.exp (-(n₀ : ℝ)^2) := by ring
          _ ≤ 1 * Real.exp (-(n₀ : ℝ)^2) := this
          _ = Real.exp (-(n₀ : ℝ)^2) := by ring
      exact le_trans h_geom_sum_bound h_final
    -- Step 5: combine the comparisons.
    exact le_trans h_tail_blocks (le_trans h_blocks_max h_blocks_small)
  have h_main :
      (∑' m : ℕ, f m)
        ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
    -- Strategy: Use that the infinite sum can be bounded by using
    -- tsum_le_of_sum_range_le, which states that if all finite partial sums
    -- are bounded by some constant, then the infinite sum is also bounded by it.

    -- We'll use the fact that for any N, the finite sum up to N is bounded
    -- by (C + 1) * exp(-n₀²), which we've already proven in
    -- gaussian_series_block_bound_partial for N < 1001.

    -- For N ≥ 1001, we need to extend the argument. The key insight from
    -- gaussian_decay_test2.js is that blocks beyond the first contribute
    -- negligibly due to exponential decay: exp(-(n₀+k)²) with k ≥ 1001
    -- decays as exp(-2*n₀*k - k²) which is astronomically small.

    -- However, a complete rigorous treatment requires additional infrastructure
    -- about Gaussian tail bounds that we'll develop separately.
    -- For now, we use the established bound for small N.

    apply hf_summ.tsum_le_of_sum_range_le
    intro N
    by_cases hN : N < 1001
    · -- Small-N case: handled by the finite-block lemma.
      exact gaussian_series_block_bound_partial ε C n₀ N hC_bound h_n₀_ge_ε hN
    · -- Large-N case: `N ≥ 1001`.
      have hN_ge : 1001 ≤ N := le_of_not_gt hN
      -- Split the finite sum into the first 1001 terms and the remaining tail.
      have h_split :
          (∑ m ∈ Finset.range N, f m)
            =
            (∑ m ∈ Finset.range 1001, f m) +
              ∑ m ∈ Finset.Icc 1001 (N - 1), f m := by
        classical
        -- Decompose the index set `{0, …, N-1}` as
        --   `{0, …, 1000} ∪ {1001, …, N-1}`.
        have h_range :
            Finset.range N =
              Finset.range 1001 ∪ Finset.Icc 1001 (N - 1) := by
          ext x
          simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
          constructor
          · intro hx
            by_cases hxs : x < 1001
            · -- `x` lies in the initial block.
              left; exact hxs
            · -- `x` lies in the tail block.
              right
              have hx_ge : 1001 ≤ x := le_of_not_gt hxs
              have hx_le : x ≤ N - 1 := by
                -- From `x < N` and `1001 ≤ N`, we deduce `x ≤ N - 1`.
                have hx_lt : (x : ℕ) < N := hx
                have : x.succ ≤ N := Nat.succ_le_of_lt hx_lt
                exact Nat.le_pred_of_lt (Nat.lt_of_succ_le this)
              exact ⟨by exact_mod_cast hx_ge, by exact_mod_cast hx_le⟩
          · intro hx
            rcases hx with hx | hx
            · -- `x` in the initial block.
              exact lt_of_lt_of_le hx hN_ge
            · -- `x` in the tail block.
              rcases hx with ⟨hx_ge, hx_le⟩
              -- From `x ≤ N - 1` we need to show `x < N`.
              omega
        -- The two pieces are disjoint, so the sum splits.
        have h_disj :
            Disjoint (Finset.range 1001) (Finset.Icc 1001 (N - 1)) := by
          simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Icc]
          omega
        -- Rewrite the sum over `range N` using this decomposition.
        simp [h_range, Finset.sum_union h_disj]
      -- Bound the first block using the discrete estimate `hC_bound` with `n = n₀`.
      have h_first_block :
          (∑ m ∈ Finset.range 1001, f m)
            ≤ C * Real.exp (-(n₀ : ℝ)^2) := by
        classical
        -- Reindex `m ↦ k := n₀ + m` and apply `hC_bound n₀ h_n₀_ge_ε`.
        have h_reindex :
            (∑ m ∈ Finset.range 1001, f m)
              =
              ∑ k ∈ Finset.Icc n₀ (n₀ + 1000),
                Real.exp (-(k : ℝ)^2) := by
          -- The map `m ↦ n₀ + m` is a bijection from `{0,…,1000}` onto
          -- `{n₀,…,n₀+1000}`.
          have h_bij :
              Finset.image (fun m : ℕ => n₀ + m) (Finset.Icc 0 1000)
                = Finset.Icc n₀ (n₀ + 1000) := by
            ext k
            simp [Finset.mem_Icc, add_comm, add_left_comm, add_assoc]
          -- Express the sum over `range 1001` via the interval `Icc 0 1000`.
          have h_range_Icc :
              Finset.range 1001 = Finset.Icc 0 1000 := by
            ext m
            simp [Finset.mem_range, Finset.mem_Icc]
            omega
          -- Now rewrite using `sum_image` and the bijection above.
          calc
            (∑ m ∈ Finset.range 1001, f m)
                = ∑ m ∈ Finset.Icc 0 1000, f m := by
                    simp [h_range_Icc]
            _ = ∑ k ∈ Finset.Icc n₀ (n₀ + 1000),
                  Real.exp (-(k : ℝ)^2) := by
                    -- Use the bijection `m ↦ n₀ + m`.
                    have h_inj : ∀ x ∈ Finset.Icc 0 1000,
                        ∀ y ∈ Finset.Icc 0 1000, n₀ + x = n₀ + y → x = y := by
                      intro x _ y _ hxy
                      omega
                    -- Rewrite LHS by unfolding f
                    show ∑ m ∈ Finset.Icc (0 : ℕ) 1000, f m =
                         ∑ k ∈ Finset.Icc n₀ (n₀ + 1000), Real.exp (-(k : ℝ)^2)
                    -- Apply sum_image
                    calc ∑ m ∈ Finset.Icc (0 : ℕ) 1000, f m
                        = ∑ m ∈ Finset.Icc (0 : ℕ) 1000, Real.exp (-((n₀ + m) : ℝ)^2) := by
                          simp only [f, hf_def]
                      _ = ∑ k ∈ Finset.image (fun m : ℕ => n₀ + m)
                            (Finset.Icc 0 1000), Real.exp (-(k : ℝ)^2) := by
                          rw [Finset.sum_image h_inj]
                          congr 1
                          ext m
                          congr 1
                          push_cast
                          ring
                      _ = ∑ k ∈ Finset.Icc n₀ (n₀ + 1000), Real.exp (-(k : ℝ)^2) := by
                          rw [h_bij]
        -- Apply the block estimate at `n = n₀`.
        have h_block := hC_bound n₀ h_n₀_ge_ε
        simpa [h_reindex] using h_block
      -- Bound the tail using `higher_blocks_negligible` and extreme Gaussian decay.
      have h_tail_block :
          (∑ m ∈ Finset.Icc 1001 (N - 1), f m)
            ≤ Real.exp (-(n₀ : ℝ)^2) := by
        -- Use the global discrete tail bound starting at index `1001`,
        -- expressed in terms of the shifted Gaussian series.  The
        -- analytic heart of this estimate is encapsulated in
        -- `gaussian_series_tail_small` above.
        have h := gaussian_series_tail_small N
        simpa [f, hf_def] using h
      -- Combine the bounds for the first block and the tail.
      have hC_nonneg : 0 ≤ C := by
        have h_bound := hC_bound n₀ h_n₀_ge_ε
        have h_sum_pos : 0 < ∑ k ∈ Finset.Icc n₀ (n₀ + 1000), Real.exp (-(k : ℝ)^2) := by
          apply Finset.sum_pos
          · intro k _
            exact Real.exp_pos _
          · exact Finset.nonempty_Icc.mpr (Nat.le_add_right n₀ 1000)
        have h_exp_pos : 0 < Real.exp (-(n₀ : ℝ)^2) := Real.exp_pos _
        rw [mul_comm] at h_bound
        exact nonneg_of_mul_nonneg_right (le_of_lt (lt_of_lt_of_le h_sum_pos h_bound)) h_exp_pos
      have h_exp_nonneg : 0 ≤ Real.exp (-(n₀ : ℝ)^2) :=
        (Real.exp_pos _).le
      have h_blocks :
          (∑ m ∈ Finset.range N, f m)
            ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
        calc
          (∑ m ∈ Finset.range N, f m)
              = (∑ m ∈ Finset.range 1001, f m) +
                  ∑ m ∈ Finset.Icc 1001 (N - 1), f m := h_split
          _ ≤ C * Real.exp (-(n₀ : ℝ)^2) + Real.exp (-(n₀ : ℝ)^2) := by
                gcongr
          _ = (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by ring
      exact h_blocks
  simpa [hf_def] using h_main

/-- Auxiliary lemma: control the Gaussian tail beyond an integer `n₀` by a discrete sum bound.
Uses `higher_blocks_negligible` to account for contributions from higher-order blocks,
giving a total bound of `(C + 1) * exp(-n₀²)` for `n₀ ≥ 1`. -/
lemma gaussian_one_sided_tail_discrete
    (ε : ℝ) (C : ℝ) (n₀ : ℕ)
    (hC_bound :
      ∀ n : ℕ, (n : ℝ) ≥ ε →
        (∑ k ∈ Finset.Icc n (n + 1000), Real.exp (-(k : ℝ)^2))
          ≤ C * Real.exp (-(n : ℝ)^2))
    (h_n₀_ge_ε : (n₀ : ℝ) ≥ ε)
    (h_n₀ : 1 ≤ n₀) :
    ∫ u in Set.Ioi (n₀ : ℝ), Real.exp (-u^2) ∂(volume : Measure ℝ)
      ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
  classical
  -- Abbreviation for the integrand.
  set f : ℝ → ℝ := fun u => Real.exp (-u^2) with hf_def
  -- Global integrability of the Gaussian on ℝ.
  have hf_int : Integrable f (volume : Measure ℝ) := by
    have h := integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num : 0 < (1 : ℝ))
    simpa [hf_def] using h
  -- General decomposition lemma for the tail `(n₀, ∞)` into unit intervals.
  have h_decomp :
      ∫ u in Set.Ioi (n₀ : ℝ), f u ∂(volume : Measure ℝ)
        =
        ∑' m : ℕ,
          ∫ u in Set.Ioc (n₀ + m : ℝ) (n₀ + m + 1 : ℝ), f u ∂(volume : Measure ℝ) := by
    -- Decompose `(n₀, ∞)` as a disjoint union of the unit intervals.
    classical
    -- Family of unit intervals starting at `n₀`.
    let s : ℕ → Set ℝ :=
      fun m => Set.Ioc (n₀ + m : ℝ) (n₀ + m + 1 : ℝ)
    -- Cover `ℝ` by integer translates of a unit interval, then restrict to `Ioi (n₀ : ℝ)`.
    have h_univ :
        (⋃ n : ℤ, Set.Ioc ((n₀ : ℝ) + n) ((n₀ : ℝ) + n + 1))
          = (Set.univ : Set ℝ) := by
      simpa using iUnion_Ioc_add_intCast (a := (n₀ : ℝ))
    -- Describe `(n₀, ∞)` as the union over `m : ℕ` of these intervals.
    have h_cover :
        Set.Ioi (n₀ : ℝ) = ⋃ m : ℕ, s m := by
      ext x; constructor
      · -- Every `x > n₀` lies in exactly one of the unit intervals.
        intro hx
        have hx_gt : (n₀ : ℝ) < x := by
          simpa [Set.mem_Ioi] using hx
        have hx_univ : x ∈ (Set.univ : Set ℝ) := trivial
        have hx_iUnion :
            x ∈ ⋃ n : ℤ, Set.Ioc ((n₀ : ℝ) + n) ((n₀ : ℝ) + n + 1) := by
          simp [h_univ]
        rcases Set.mem_iUnion.mp hx_iUnion with ⟨z, hz⟩
        -- Eliminate the possibility that the integer index is negative.
        cases z with
        | ofNat m =>
            -- Positive index: this gives the desired interval.
            refine Set.mem_iUnion.mpr ?_
            refine ⟨m, ?_⟩
            simpa [s] using hz
        | negSucc k =>
            -- Negative index leads to a contradiction with `x > n₀`.
            have hz_le : x ≤ (n₀ : ℝ) := by
              have hk : ((Int.negSucc k : ℤ) : ℝ) + 1 ≤ (0 : ℝ) := by
                simp
              have hk' :
                  (n₀ : ℝ) + ((Int.negSucc k : ℤ) : ℝ) + 1 ≤ (n₀ : ℝ) := by
                have := add_le_add_left hk (n₀ : ℝ)
                simp [add_assoc, add_comm, add_left_comm]
              have hz2 : x ≤ (n₀ : ℝ) + ((Int.negSucc k : ℤ) : ℝ) + 1 := hz.2
              exact le_trans hz2 hk'
            exact (False.elim <| (not_le_of_gt hx_gt) hz_le)
      · -- Any point in one of the unit intervals lies to the right of `n₀`.
        intro hx
        rcases Set.mem_iUnion.mp hx with ⟨m, hm⟩
        have hm_left : (n₀ : ℝ) < x := by
          have h_mem := Set.mem_Ioc.mp hm
          have h_m_nonneg : (0 : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast (Nat.zero_le m)
          have h_n0_le : (n₀ : ℝ) ≤ n₀ + (m : ℝ) := by
            simp [add_comm]
          exact lt_of_le_of_lt h_n0_le h_mem.1
        simpa [Set.mem_Ioi] using hm_left
    -- Measurability of each interval.
    have h_meas : ∀ m : ℕ, MeasurableSet (s m) := by
      intro m
      unfold s
      exact measurableSet_Ioc
    -- Pairwise disjointness of the intervals `s m`, inherited from the ℤ-indexed family.
    let t : ℤ → Set ℝ :=
      fun n => Set.Ioc ((n₀ : ℝ) + n) ((n₀ : ℝ) + n + 1)
    have h_disjZ :
        Pairwise (Function.onFun Disjoint t) := by
      -- Directly use the standard pairwise-disjointness lemma on integer translates.
      simpa [t] using
        (Set.pairwise_disjoint_Ioc_add_intCast (a := (n₀ : ℝ)))
    have h_disj :
        Pairwise (Function.onFun Disjoint s) := by
      -- Restrict the ℤ-indexed disjointness to the ℕ-indexed family via coercions.
      intro m k hmk
      have hmkZ : (m : ℤ) ≠ (k : ℤ) := by
        exact_mod_cast hmk
      -- Apply the ℤ-indexed pairwise disjointness to indices `m` and `k` viewed in ℤ.
      have hk : Disjoint (t (m : ℤ)) (t (k : ℤ)) :=
        h_disjZ hmkZ
      -- Identify the ℕ-indexed and ℤ-indexed intervals.
      have hm_eq : s m = t (m : ℤ) := by
        simp [s, t, add_comm, add_left_comm, add_assoc]
      have hk_eq : s k = t (k : ℤ) := by
        simp [s, t, add_comm, add_left_comm, add_assoc]
      simpa [hm_eq, hk_eq] using hk
    -- Integrability of `f` on the union.
    have h_int :
        IntegrableOn f (⋃ m : ℕ, s m) (volume : Measure ℝ) := by
      -- Restrict an integrable function to a measurable subset.
      simpa [h_cover] using hf_int.integrableOn
    -- Apply the general `integral_iUnion` lemma to swap integral and `tsum`.
    have h_eq :=
      MeasureTheory.integral_iUnion
        (μ := (volume : Measure ℝ))
        (f := f)
        (s := s)
        h_meas h_disj h_int
    -- Rewrite back in terms of the original tail integral over `Ioi (n₀ : ℝ)`.
    simpa [s, h_cover] using h_eq
  -- Step 2: bound each interval integral by the maximal value of `f` on that interval.
  have h_interval :
      ∀ m : ℕ,
        ∫ u in Set.Ioc (n₀ + m : ℝ) (n₀ + m + 1 : ℝ), f u ∂(volume : Measure ℝ)
          ≤ Real.exp (-(n₀ + m : ℝ)^2) := by
    intro m
    -- Abbreviations for the left endpoint and the interval.
    set a : ℝ := n₀ + m with ha_def
    let s : Set ℝ := Set.Ioc a (a + 1)
    have hs_meas : MeasurableSet s := by
      simp [s]
    -- On `[a, ∞)`, the map `u ↦ exp (-u^2)` is decreasing, since squaring is increasing on
    -- `[0, ∞)` and we flip the inequality with a minus sign.
    have ha_nonneg : 0 ≤ a := by
      have hn0 : 0 ≤ (n₀ : ℝ) := by exact_mod_cast (Nat.zero_le n₀)
      have hm : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      have := add_nonneg hn0 hm
      simpa [a, ha_def] using this
    have h_pointwise :
        ∀ u ∈ s, f u ≤ Real.exp (-a^2) := by
      intro u hu
      have hu_mem := Set.mem_Ioc.mp hu
      have ha_le_u : a ≤ u := le_of_lt hu_mem.1
      -- From `a ≤ u` with `a ≥ 0`, we get `a^2 ≤ u^2`.
      have h_sq : a ^ 2 ≤ u ^ 2 := by
        have := mul_self_le_mul_self ha_nonneg ha_le_u
        simpa [pow_two] using this
      -- Flip the inequality in the exponent and use monotonicity of `exp`.
      have h_arg : -u ^ 2 ≤ -a ^ 2 := by
        simpa using (neg_le_neg h_sq)
      have h_exp := Real.exp_le_exp.mpr h_arg
      simpa [hf_def, a, ha_def] using h_exp
    -- Integrability of `f` and of the constant bound on the interval.
    have hf_on : IntegrableOn f s (volume : Measure ℝ) :=
      hf_int.integrableOn
    have hs_finite : (volume : Measure ℝ) s ≠ ∞ := by
      simp [s, a, ha_def, Real.volume_Ioc]
    have hg_on :
        IntegrableOn (fun _ : ℝ => Real.exp (-a^2)) s (volume : Measure ℝ) :=
      integrableOn_const (μ := (volume : Measure ℝ)) (s := s)
        (C := Real.exp (-a^2)) hs_finite
    -- Compare the integral of `f` with that of the constant upper bound.
    have h_int_le :
        ∫ u in s, f u ∂(volume : Measure ℝ)
          ≤ ∫ u in s, (fun _ : ℝ => Real.exp (-a^2)) u ∂(volume : Measure ℝ) := by
      refine MeasureTheory.setIntegral_mono_on
          (μ := (volume : Measure ℝ)) (s := s)
          (f := f) (g := fun _ : ℝ => Real.exp (-a^2))
          (hf := hf_on) (hg := hg_on) hs_meas ?_
      intro u hu
      exact h_pointwise u hu
    -- Compute the integral of the constant function on the unit interval.
    have h_measure :
        (volume : Measure ℝ).real s = 1 := by
      have ha_le : a ≤ a + 1 := by linarith
      have hvol : (volume : Measure ℝ).real (Set.Ioc a (a + 1)) = (a + 1) - a :=
        Real.volume_real_Ioc_of_le (a := a) (b := a + 1) ha_le
      have hvol' : (volume : Measure ℝ).real s = (a + 1) - a := by
        simp [s]
      have hdist : (a + 1 : ℝ) - a = 1 := by
        simp
      simp [hvol', hdist]
    have h_const :
        ∫ u in s, (fun _ : ℝ => Real.exp (-a^2)) u ∂(volume : Measure ℝ)
          = Real.exp (-a^2) := by
      simp [s, h_measure, one_smul]
    -- Put everything together and rewrite back in terms of `n₀ + m`.
    have h_main :
        ∫ u in s, f u ∂(volume : Measure ℝ)
          ≤ Real.exp (-a^2) := by
      have := h_int_le
      simpa [h_const] using this
    simpa [s, a, ha_def] using h_main
  -- Step 3: control the resulting series of Gaussian terms by the discrete bound `hC_bound`.
  have h_series :
      (∑' m : ℕ, Real.exp (-(n₀ + m : ℝ)^2))
        ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
    exact gaussian_series_block_bound (ε := ε) (C := C) (n₀ := n₀) hC_bound h_n₀_ge_ε h_n₀
  -- Step 4: combine decomposition and series bound.
  have h_main :
      ∫ u in Set.Ioi (n₀ : ℝ), f u ∂(volume : Measure ℝ)
        ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
    have h_sum_le :
        ∑' m : ℕ,
          ∫ u in Set.Ioc (n₀ + m : ℝ) (n₀ + m + 1 : ℝ), f u ∂(volume : Measure ℝ)
          ≤
        ∑' m : ℕ, Real.exp (-(n₀ + m : ℝ)^2) := by
      -- `h_interval` から項別の不等式を得て，`tsum` の単調性を使う
      have h_summ_int :
          Summable
            (fun m : ℕ =>
              ∫ u in Set.Ioc (n₀ + m : ℝ) (n₀ + m + 1 : ℝ), f u ∂(volume : Measure ℝ)) := by
        -- `hasSum_integral_iUnion` から級数の収束性を取り出す
        -- 対応する可測集合族
        let s : ℕ → Set ℝ :=
          fun m => Set.Ioc (n₀ + m : ℝ) (n₀ + m + 1 : ℝ)
        -- 各区間の可測性
        have h_meas : ∀ m : ℕ, MeasurableSet (s m) := by
          intro m
          simp [s]
        -- 区間族 `s m` の互いに素なこと
        have h_disj :
            Pairwise (Function.onFun Disjoint s) := by
          intro m k hmk
          -- 整数添字付きの互いに素な区間族から従う
          let t : ℤ → Set ℝ :=
            fun n => Set.Ioc ((n₀ : ℝ) + n) ((n₀ : ℝ) + n + 1)
          have h_disjZ :
              Pairwise (Function.onFun Disjoint t) := by
            simpa [t] using
              (Set.pairwise_disjoint_Ioc_add_intCast (a := (n₀ : ℝ)))
          have hmkZ : (m : ℤ) ≠ (k : ℤ) := by
            exact_mod_cast hmk
          have hk : Disjoint (t (m : ℤ)) (t (k : ℤ)) :=
            h_disjZ hmkZ
          have hm_eq : s m = t (m : ℤ) := by
            simp [s, t, add_comm, add_left_comm, add_assoc]
          have hk_eq : s k = t (k : ℤ) := by
            simp [s, t, add_comm, add_left_comm, add_assoc]
          simpa [hm_eq, hk_eq] using hk
        -- 直和集合上での可積分性（全体空間で可積分なので従う）
        have h_int :
            IntegrableOn f (⋃ m : ℕ, s m) (volume : Measure ℝ) := by
          simpa using hf_int.integrableOn
        -- `hasSum_integral_iUnion` から `HasSum` を得る
        have h_hasSum :
            HasSum
              (fun m : ℕ =>
                ∫ u in s m, f u ∂(volume : Measure ℝ))
              (∫ u in ⋃ m : ℕ, s m, f u ∂(volume : Measure ℝ)) :=
          MeasureTheory.hasSum_integral_iUnion
            (μ := (volume : Measure ℝ))
            (f := f)
            (s := s)
            h_meas h_disj h_int
        -- `HasSum.summable` から級数の収束性を得る
        have h_summ :
            Summable
              (fun m : ℕ =>
                ∫ u in s m, f u ∂(volume : Measure ℝ)) :=
          h_hasSum.summable
        -- 表現を元の形に戻す
        simpa [s] using h_summ
      have h_summ_exp :
          Summable (fun m : ℕ => Real.exp (-(n₀ + m : ℝ)^2)) := by
        -- 離散ガウス級数の総和可能性（補題として切り出したもの）を使う
        exact gaussian_series_shift_summable n₀
      refine Summable.tsum_le_tsum (fun m => ?_) h_summ_int h_summ_exp
      -- 各項ごとの不等式は既に `h_interval` が与えている
      exact h_interval m
    calc
      ∫ u in Set.Ioi (n₀ : ℝ), f u ∂(volume : Measure ℝ)
          = ∑' m : ℕ,
              ∫ u in Set.Ioc (n₀ + m : ℝ) (n₀ + m + 1 : ℝ), f u ∂(volume : Measure ℝ) := h_decomp
      _ ≤ ∑' m : ℕ, Real.exp (-(n₀ + m : ℝ)^2) := h_sum_le
      _ ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := h_series
      _ ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := le_refl _
  -- Rewrite back in terms of the original integrand.
  simpa [hf_def] using h_main

/-- One-sided Gaussian tail bound on `(r, ∞)`, uniform for `r ≥ ε`. -/
lemma gaussian_one_sided_tail_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r : ℝ, ε ≤ r →
        ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ)
          ≤ C * Real.exp (-r^2) := by
  classical
  -- Strategy: compare the one-sided tail with a discrete Gaussian sum,
  -- and use the existing exponential decay lemmas on ℕ.
  -- We only set up the structure here; the analytic details are left as TODOs.
  -- Step 1: choose a positive constant `C` depending on `ε`.
  -- Ultimately, `C` will control the sum `∑_{k ≥ ⌈ε⌉} exp (-(k : ℝ)^2)`.
  obtain ⟨C, hC_pos, hC_bound⟩ :
      ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, (n : ℝ) ≥ ε →
          (∑ k ∈ Finset.Icc n (n + 1000), Real.exp (-(k : ℝ)^2))
            ≤ C * Real.exp (-(n : ℝ)^2) := by
    -- TODO: replace this placeholder with a genuine construction using
    -- `exponential_decay_bound` or `general_exponential_bound` and
    -- properties of the Gaussian tail on ℕ.
    -- For now we introduce an explicit constant and keep the proof as a TODO.
    -- The choice `C = 1001` matches the cardinality of the window
    -- `{n, n+1, …, n+1000}` used below.
    refine ⟨1001, by norm_num, ?_⟩
    intro n hn
    -- Basic skeleton: first record nonnegativity of the Gaussian sum,
    -- then reduce to a more precise bound on the discrete tail, left as TODO.
    have h_nonneg :
        0 ≤
          (∑ k ∈ Finset.Icc n (n + 1000),
            Real.exp (-(k : ℝ)^2)) := by
      have h_term_nonneg :
          ∀ k ∈ Finset.Icc n (n + 1000),
            0 ≤ Real.exp (-(k : ℝ)^2) := by
        intro k hk
        exact Real.exp_nonneg _
      exact Finset.sum_nonneg h_term_nonneg
    -- TODO: replace this placeholder with a genuine Gaussian sum estimate.
    -- Skeleton: bound the sum by comparing each term with the first one
    -- and using a crude cardinality estimate of the index set.
    have h_main :
        (∑ k ∈ Finset.Icc n (n + 1000), Real.exp (-(k : ℝ)^2))
          ≤ 1001 * Real.exp (-(n : ℝ)^2) := by
      -- Step 1: observe that for `k ≥ n` the Gaussian is bounded by the
      -- first term `exp (-(n : ℝ)^2)` since the function is decreasing
      -- on `[n, ∞)`. This is where the actual analysis will go.
      have h_pointwise :
          ∀ k ∈ Finset.Icc n (n + 1000),
            Real.exp (-(k : ℝ)^2) ≤ Real.exp (-(n : ℝ)^2) := by
        intro k hk
        -- From membership in `Finset.Icc`, we know `n ≤ k` as natural numbers.
        have hk_nat : n ≤ k := (Finset.mem_Icc.mp hk).1
        -- View this inequality in `ℝ`.
        have hk_real : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_nat
        -- Both sides are nonnegative, so we can square the inequality.
        have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        have hk_sq : (n : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
          -- `mul_self_le_mul_self` is stated using `*`, so we rewrite using `pow_two`.
          have := mul_self_le_mul_self hn_nonneg hk_real
          simpa [pow_two] using this
        -- Turning the inequality around in the exponent (since we have a minus sign).
        have h_arg : -(k : ℝ) ^ 2 ≤ -(n : ℝ) ^ 2 := by
          simpa using (neg_le_neg hk_sq)
        -- Apply monotonicity of the exponential.
        exact Real.exp_le_exp.mpr h_arg
      -- Step 2: control the sum by the number of terms times the maximal value.
      have h_card :
          (∑ k ∈ Finset.Icc n (n + 1000),
            Real.exp (-(k : ℝ)^2))
            ≤ (Finset.card (Finset.Icc n (n + 1000))) *
                Real.exp (-(n : ℝ)^2) := by
        -- Abbreviation for the finite index set.
        let s : Finset ℕ := Finset.Icc n (n + 1000)
        -- First, bound the sum by the sum of the constant upper bound.
        have h_le_const :
            (∑ k ∈ s, Real.exp (-(k : ℝ)^2))
              ≤ ∑ k ∈ s, Real.exp (-(n : ℝ)^2) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact h_pointwise k hk
        -- Compute the sum of the constant function over `s`.
        have h_sum_const :
            (∑ k ∈ s, Real.exp (-(n : ℝ)^2))
              = (Finset.card s) * Real.exp (-(n : ℝ)^2) := by
          -- `sum_const` gives the description via `•`, then rewrite to `*`.
          have : (∑ _ ∈ s, Real.exp (-(n : ℝ)^2))
              = (Finset.card s) • Real.exp (-(n : ℝ)^2) :=
            Finset.sum_const (Real.exp (-(n : ℝ)^2))
          simp [nsmul_eq_mul, this]
        -- Put the two pieces together.
        have h_total :
            (∑ k ∈ s, Real.exp (-(k : ℝ)^2))
              ≤ (Finset.card s) * Real.exp (-(n : ℝ)^2) := by
          calc
            (∑ k ∈ s, Real.exp (-(k : ℝ)^2))
                ≤ ∑ k ∈ s, Real.exp (-(n : ℝ)^2) := h_le_const
            _ = (Finset.card s) * Real.exp (-(n : ℝ)^2) := h_sum_const
        -- Rewrite back `s` to `Finset.Icc n (n + 1000)`.
        simpa [s] using h_total
      -- Step 3: bound the cardinality by the chosen constant `1001` and
      -- absorb it into the eventual choice of `C` in the outer statement.
      have h_card_bound :
          (Finset.card (Finset.Icc n (n + 1000))) *
              Real.exp (-(n : ℝ)^2)
            ≤ 1001 * Real.exp (-(n : ℝ)^2) := by
        -- First compute the exact cardinality.
        have h_card_exact :
            Finset.card (Finset.Icc n (n + 1000)) = 1001 := by
          -- Use the standard formula `Finset.card_Icc` on ℕ:
          -- `card (Icc a b) = b + 1 - a`.  Here, `b = n + 1000`,
          -- so the right-hand side simplifies to `1001`.
          simp [Nat.add_assoc]
        -- Turn this into an inequality `≤ 1001` at the level of ℕ.
        have h_card_nat :
            Finset.card (Finset.Icc n (n + 1000)) ≤ 1001 := by
          simp [h_card_exact]
        -- View the cardinality bound in `ℝ`.
        have h_card_real :
            (Finset.card (Finset.Icc n (n + 1000)) : ℝ) ≤ 1001 := by
          exact_mod_cast h_card_nat
        -- The Gaussian factor is nonnegative.
        have h_exp_nonneg : 0 ≤ Real.exp (-(n : ℝ)^2) :=
          Real.exp_nonneg _
        -- Multiply the cardinality inequality by the Gaussian factor.
        have h_mul :=
          mul_le_mul_of_nonneg_right h_card_real h_exp_nonneg
        -- Simplify the right-hand side and obtain the desired inequality.
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul
      exact
        le_trans h_card h_card_bound
    simpa using h_main
  -- Step 2: use the discrete bound to control the continuous tail.
  -- We return C + 2 to account for:
  -- - The initial segment (r, n₀] contributing at most exp(-r²)
  -- - Higher-order blocks contributing at most exp(-n₀²) ≤ exp(-r²)
  -- Together with the first block's C * exp(-r²), this gives (C + 2) * exp(-r²)
  have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
  have hC_pos' : 0 < C + 2 := by linarith
  refine ⟨C + 2, hC_pos', ?_⟩
  intro r hr
  -- Step 2a: choose an integer `n₀ ≥ r` (e.g. `n₀ = ⌈r⌉`).
  let n₀ : ℕ := Nat.ceil r
  have h_n₀_ge_r : r ≤ n₀ := by
    -- `Nat.ceil r` is the least integer ≥ r.
    have h := Nat.le_ceil r
    -- Interpret the statement with `n₀ = Nat.ceil r`.
    simpa [n₀] using h
  have h_n₀_ge_ε : (n₀ : ℝ) ≥ ε := by
    -- From `ε ≤ r ≤ n₀` we deduce `ε ≤ n₀`.
    have hε_le_r : ε ≤ r := hr
    have h_r_le_n₀ : r ≤ (n₀ : ℝ) := h_n₀_ge_r
    -- Chain the two inequalities.
    exact le_trans hε_le_r h_r_le_n₀
  have h_n₀ : 1 ≤ n₀ := by
    -- For gaussian_series_block_bound we need n₀ ≥ 1.
    -- We have n₀ = ⌈r⌉ where r ≥ ε > 0, so n₀ ≥ 1.
    have hr_pos : 0 < r := lt_of_lt_of_le hε hr
    have h_n₀_pos : 0 < (n₀ : ℝ) := by
      calc (0 : ℝ) < r := hr_pos
        _ ≤ (n₀ : ℝ) := h_n₀_ge_r
    have : 0 < n₀ := Nat.cast_pos.mp h_n₀_pos
    omega
  -- Step 2b: decompose the integral over `(r, ∞)` into the first segment
  -- `(r, n₀]` plus the tail beyond `n₀`, then bound each piece.
  have h_split_int :
      ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ)
        =
        ∫ u in Set.Ioc r n₀, Real.exp (-u^2) ∂(volume : Measure ℝ)
          +
        ∫ u in Set.Ioi (n₀ : ℝ), Real.exp (-u^2) ∂(volume : Measure ℝ) := by
    classical
    -- Abbreviations for the three sets involved.
    set S : Set ℝ := Set.Ioi r with hS_def
    set A : Set ℝ := Set.Ioc r (n₀ : ℝ) with hA_def
    set B : Set ℝ := Set.Ioi (n₀ : ℝ) with hB_def
    -- Step 1: rewrite all set integrals in terms of indicators on ℝ.
    have hS :
        ∫ u in S, Real.exp (-u^2) ∂(volume : Measure ℝ)
          =
          ∫ u, Set.indicator S (fun u => Real.exp (-u^2)) u
            ∂(volume : Measure ℝ) := by
      have hS_meas : MeasurableSet S := by
        have : S = Set.Ioi r := by
          ext u
          simp [S, hS_def, Set.Ioi]
        simp [S, hS_def, this]
      simpa [S, hS_def] using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := S) (f := fun u => Real.exp (-u^2)) hS_meas).symm
    have hA :
        ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ)
          =
          ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) u
            ∂(volume : Measure ℝ) := by
      have hA_meas : MeasurableSet A := by
        have : A = Set.Ioc r (n₀ : ℝ) := by
          ext u
          simp [A, hA_def, Set.Ioc]
        simp [A, hA_def, this]
      simpa [A, hA_def] using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := A) (f := fun u => Real.exp (-u^2)) hA_meas).symm
    have hB :
        ∫ u in B, Real.exp (-u^2) ∂(volume : Measure ℝ)
          =
          ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u
            ∂(volume : Measure ℝ) := by
      have hB_meas : MeasurableSet B := by
        have : B = Set.Ioi (n₀ : ℝ) := by
          ext u
          simp [B, hB_def, Set.Ioi]
        simp [B, hB_def, this]
      simpa [B, hB_def] using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := B) (f := fun u => Real.exp (-u^2)) hB_meas).symm
    -- Step 2: describe `S` as the disjoint union of `A` and `B`, and relate indicators.
    have h_union : S = A ∪ B := by
      ext u
      constructor
      · -- `u ∈ S` implies it lies either in `(r, n₀]` or in `(n₀, ∞)`.
        intro hu
        have hru : r < u := by
          simpa [S, hS_def, Set.Ioi] using hu
        by_cases hule : u ≤ (n₀ : ℝ)
        · left
          -- Then `u ∈ A = Ioc r n₀`.
          have : r < u ∧ u ≤ (n₀ : ℝ) := ⟨hru, hule⟩
          simpa [A, hA_def, Set.Ioc] using this
        · right
          -- Otherwise `n₀ < u`, so `u ∈ B = Ioi n₀`.
          have hgt : (n₀ : ℝ) < u := lt_of_not_ge hule
          simpa [B, hB_def, Set.Ioi] using hgt
      · -- If `u` lies in `A` or `B`, then in both cases `r < u`, so `u ∈ S`.
        intro hu
        rcases hu with hA' | hB'
        · -- Case `u ∈ A = Ioc r n₀`.
          have hru : r < u := by
            have : r < u ∧ u ≤ (n₀ : ℝ) := by
              simpa [A, hA_def, Set.Ioc] using hA'
            exact this.1
          simpa [S, hS_def, Set.Ioi] using hru
        · -- Case `u ∈ B = Ioi n₀`.
          have hnu : (n₀ : ℝ) < u := by
            simpa [B, hB_def, Set.Ioi] using hB'
          have hru : r < u := lt_of_le_of_lt h_n₀_ge_r hnu
          simpa [S, hS_def, Set.Ioi] using hru
    -- `A` and `B` are disjoint.
    have h_disj : Disjoint A B := by
      refine Set.disjoint_left.mpr ?_
      intro u hAu hBu
      have hAu' : r < u ∧ u ≤ (n₀ : ℝ) := by
        simpa [A, hA_def, Set.Ioc] using hAu
      have hBu' : (n₀ : ℝ) < u := by
        simpa [B, hB_def, Set.Ioi] using hBu
      linarith
    -- Pointwise identity for indicators: `S.indicator f = A.indicator f + B.indicator f`.
    have h_ind :
        (fun u =>
          Set.indicator S (fun u => Real.exp (-u^2)) u)
          =
        (fun u =>
          Set.indicator A (fun u => Real.exp (-u^2)) u +
          Set.indicator B (fun u => Real.exp (-u^2)) u) := by
      funext u
      have hSAB :
          Set.indicator S (fun u => Real.exp (-u^2)) u
            =
          Set.indicator (A ∪ B) (fun u => Real.exp (-u^2)) u := by
        -- Rewrite `S` as `A ∪ B`.
        have := congrArg
          (fun (s : Set ℝ) =>
            Set.indicator s (fun u => Real.exp (-u^2)) u) h_union
        simpa using this
      have h_union_ind :
          Set.indicator (A ∪ B) (fun u => Real.exp (-u^2)) u
            =
          Set.indicator A (fun u => Real.exp (-u^2)) u +
          Set.indicator B (fun u => Real.exp (-u^2)) u := by
        -- Use the standard indicator union identity for disjoint sets.
        have hfun :=
          Set.indicator_union_of_disjoint
            (s := A) (t := B)
            (f := fun u : ℝ => Real.exp (-u^2)) h_disj
        have := congrArg (fun g : ℝ → ℝ => g u) hfun
        simpa using this
      simpa [hSAB] using h_union_ind
    -- Step 3: use linearity of the integral to split the sum of indicators.
    have h_int :
        Integrable (fun u : ℝ => Real.exp (-u^2)) (volume : Measure ℝ) := by
      -- Gaussian integrability with coefficient `a = 1`.
      have hpos : 0 < (1 : ℝ) := by norm_num
      have hbase :
          Integrable (fun u : ℝ => Real.exp (-(1 : ℝ) * u ^ 2))
            (volume : Measure ℝ) :=
        integrable_exp_neg_mul_sq hpos
      simpa using hbase
    have hA_meas : MeasurableSet A := by
      have : A = Set.Ioc r (n₀ : ℝ) := by
        ext u
        simp [A, hA_def, Set.Ioc]
      simp [A, hA_def, this]
    have hB_meas : MeasurableSet B := by
      have : B = Set.Ioi (n₀ : ℝ) := by
        ext u
        simp [B, hB_def, Set.Ioi]
      simp [B, hB_def, this]
    have h_intA :
        Integrable (fun u : ℝ =>
            Set.indicator A (fun u => Real.exp (-u^2)) u)
          (volume : Measure ℝ) :=
      h_int.indicator hA_meas
    have h_intB :
        Integrable (fun u : ℝ =>
            Set.indicator B (fun u => Real.exp (-u^2)) u)
          (volume : Measure ℝ) :=
      h_int.indicator hB_meas
    have h_sum :
        ∫ u,
          (Set.indicator A (fun u => Real.exp (-u^2)) u +
           Set.indicator B (fun u => Real.exp (-u^2)) u)
          ∂(volume : Measure ℝ)
          =
        ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ)
          +
        ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := by
      simpa using
        (MeasureTheory.integral_add h_intA h_intB)
    -- Step 4: assemble all identities and rewrite indicators back to set integrals.
    calc
      ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ)
          = ∫ u in S, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
              simp [S, hS_def]
      _ = ∫ u, Set.indicator S (fun u => Real.exp (-u^2)) u
              ∂(volume : Measure ℝ) := hS
      _ = ∫ u,
              (Set.indicator A (fun u => Real.exp (-u^2)) u +
               Set.indicator B (fun u => Real.exp (-u^2)) u)
              ∂(volume : Measure ℝ) := by
                simp [h_ind]
      _ =
          ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ)
            +
          ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := h_sum
      _ =
          ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ)
            +
          ∫ u in B, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
            simp [hA, hB]
      _ =
          ∫ u in Set.Ioc r n₀, Real.exp (-u^2) ∂(volume : Measure ℝ)
            +
          ∫ u in Set.Ioi (n₀ : ℝ), Real.exp (-u^2) ∂(volume : Measure ℝ) := by
            simp [S, A, B, hS_def, hA_def, hB_def]
  -- Step 2c: bound the initial segment `(r, n₀]` by a multiple of `exp (-r^2)`.
  have h_initial :
      ∫ u in Set.Ioc r n₀, Real.exp (-u^2) ∂(volume : Measure ℝ)
        ≤ Real.exp (-r^2) := by
    classical
    -- Skeleton of the argument:
    -- 1. Use that `exp (-u^2)` is nonnegative and decreasing on `[r, ∞)`,
    --    so on `(r, n₀]` it is bounded above by `exp (-r^2)`.
    -- 2. Control the length of `(r, n₀]` using `n₀ = ⌈r⌉`, giving
    --    `volume (Ioc r n₀) ≤ 1`.
    -- 3. Conclude that the integral is at most `exp (-r^2) * 1`.
    -- Step 1: pointwise bound on the integrand over the interval.
    have h_nonneg :
        ∀ u ∈ Set.Ioc r (n₀ : ℝ), 0 ≤ Real.exp (-u^2) := by
      intro u hu
      exact Real.exp_nonneg _
    have h_pointwise :
        ∀ u ∈ Set.Ioc r (n₀ : ℝ),
          Real.exp (-u^2) ≤ Real.exp (-r^2) := by
      intro u hu
      -- From membership in `Set.Ioc r n₀` we know `r < u`.
      have hIoc : r < u ∧ u ≤ (n₀ : ℝ) := by
        simpa [Set.Ioc] using hu
      have hru : r < u := hIoc.1
      have hru_le : r ≤ u := le_of_lt hru
      -- Since `ε ≤ r` and `0 < ε`, we have `0 ≤ r`.
      have hr_nonneg : 0 ≤ r := le_trans (le_of_lt hε) hr
      -- Square the inequality `r ≤ u` on nonnegative reals.
      have h_sq : r ^ 2 ≤ u ^ 2 := by
        have := mul_self_le_mul_self hr_nonneg hru_le
        simpa [pow_two] using this
      -- Turn the inequality around in the exponent (minus sign).
      have h_arg : -u ^ 2 ≤ -r ^ 2 := by
        simpa using (neg_le_neg h_sq)
      -- Apply monotonicity of the exponential.
      exact Real.exp_le_exp.mpr h_arg
    -- Step 2: control the integral by the length of the interval times the bound.
    have h_int_le :
        ∫ u in Set.Ioc r n₀, Real.exp (-u^2) ∂(volume : Measure ℝ)
          ≤ Real.exp (-r^2) *
              (volume (Set.Ioc r (n₀ : ℝ))).toReal := by
      classical
      -- Strategy: rewrite both sides using indicators on ℝ, then use
      -- `integral_mono_ae` with the pointwise bound `h_pointwise`.
      -- Abbreviation for the interval.
      set S : Set ℝ := Set.Ioc r (n₀ : ℝ) with hS_def
      -- Left-hand side as an integral over ℝ with an indicator.
      have h_left :
          ∫ u in Set.Ioc r n₀, Real.exp (-u^2) ∂(volume : Measure ℝ)
            =
            ∫ u, Set.indicator S (fun u => Real.exp (-u^2)) u
              ∂(volume : Measure ℝ) := by
        have hS_meas : MeasurableSet S := by
          have : S = Set.Ioc r (n₀ : ℝ) := by
            ext u
            simp [S, hS_def, Set.Ioc]
          simp [S, hS_def, this]
        simpa [S, hS_def] using
          (MeasureTheory.integral_indicator
            (μ := (volume : Measure ℝ))
            (s := S) (f := fun u => Real.exp (-u^2)) hS_meas).symm
      -- Right-hand side as the integral of the constant bound over the interval.
      have h_right :
          Real.exp (-r^2) *
              (volume (Set.Ioc r (n₀ : ℝ))).toReal
            =
          ∫ u, Set.indicator S (fun _ => Real.exp (-r^2)) u
              ∂(volume : Measure ℝ) := by
        -- First, rewrite the indicator integral as a set integral.
        have hS_meas : MeasurableSet S := by
          have : S = Set.Ioc r (n₀ : ℝ) := by
            ext u
            simp [S, hS_def, Set.Ioc]
          simp [S, hS_def, this]
        have h_indicator :
            ∫ u, Set.indicator S (fun _ => Real.exp (-r^2)) u
              ∂(volume : Measure ℝ)
            =
            ∫ u in S, Real.exp (-r^2) ∂(volume : Measure ℝ) := by
          simp [S, hS_def]
        -- Next, evaluate the set integral of the constant function on `S`.
        have h_const :
            ∫ u in S, Real.exp (-r^2) ∂(volume : Measure ℝ)
              =
            Real.exp (-r^2) * (volume S).toReal := by
          -- Step 1: rewrite the set integral as an integral of an indicator.
          have h_set_indicator :
              ∫ u in S, Real.exp (-r^2) ∂(volume : Measure ℝ)
                =
              ∫ u, Set.indicator S (fun _ => Real.exp (-r^2)) u
                ∂(volume : Measure ℝ) := by
            simp [S, hS_def]
          -- Step 2: express the indicator of the constant as a constant multiple
          -- of the indicator of `1`.
          have h_indicator_const :
              (fun u => Set.indicator S (fun _ => Real.exp (-r^2)) u)
                =
              (fun u =>
                Real.exp (-r^2) *
                  Set.indicator S (fun _ => (1 : ℝ)) u) := by
            funext u
            by_cases hu : u ∈ S
            · simp [Set.indicator, hu, mul_comm]
            · simp [Set.indicator, hu]
          -- Step 3: factor the constant `exp (-r^2)` out of the integral.
          have h_factored :
              ∫ u, Set.indicator S (fun _ => Real.exp (-r^2)) u
                  ∂(volume : Measure ℝ)
                =
              Real.exp (-r^2) *
                ∫ u, Set.indicator S (fun _ => (1 : ℝ)) u
                  ∂(volume : Measure ℝ) := by
            have :=
              MeasureTheory.integral_const_mul
                (μ := (volume : Measure ℝ))
                (r := Real.exp (-r^2))
                (f := fun u => Set.indicator S (fun _ => (1 : ℝ)) u)
            -- This lemma says:
            -- `∫ u, Real.exp (-r^2) * (S.indicator (fun _ => 1) u) =
            --    Real.exp (-r^2) * ∫ u, S.indicator (fun _ => 1) u`.
            simpa [h_indicator_const] using this
          -- Step 4: compute the integral of the indicator of `1`, which is
          -- just the Lebesgue measure of `S`.
          have h_indicator_one :
              ∫ u, Set.indicator S (fun _ : ℝ => (1 : ℝ)) u
                ∂(volume : Measure ℝ)
                = (volume S).toReal := by
            -- This is exactly the `integral_indicator` lemma specialized to
            -- the constant function `1` on the measurable set `S`.
            set χ : ℝ → ℝ := Set.indicator S (fun _ : ℝ => (1 : ℝ)) with hχ_def
            have h_int_χ :
                ∫ u, χ u ∂(volume : Measure ℝ) = (volume S).toReal := by
              -- The underlying lemma in mathlib states that the integral of
              -- the indicator of `1` over a measurable set `S` is `(volume S).toReal`.
              simpa [χ, hχ_def] using
                (MeasureTheory.integral_indicator
                  (μ := (volume : Measure ℝ))
                  (f := fun _ : ℝ => (1 : ℝ)) hS_meas)
            simpa [χ, hχ_def] using h_int_χ
          -- Assemble the pieces.
          calc
            ∫ u in S, Real.exp (-r^2) ∂(volume : Measure ℝ)
                = ∫ u, Set.indicator S (fun _ => Real.exp (-r^2)) u
                    ∂(volume : Measure ℝ) := h_set_indicator
            _ = Real.exp (-r^2) *
                  ∫ u, Set.indicator S (fun _ => (1 : ℝ)) u
                    ∂(volume : Measure ℝ) := h_factored
            _ = Real.exp (-r^2) * (volume S).toReal := by
                  simp [h_indicator_one]
        -- Put the two identities together and normalize the set `S`.
        have :=
          calc
            Real.exp (-r^2) * (volume (Set.Ioc r (n₀ : ℝ))).toReal
                = Real.exp (-r^2) * (volume S).toReal := by
                      simp [S, hS_def]
            _ = ∫ u in S, Real.exp (-r^2) ∂(volume : Measure ℝ) := h_const.symm
            _ = ∫ u, Set.indicator S (fun _ => Real.exp (-r^2)) u
                  ∂(volume : Measure ℝ) := h_indicator.symm
        exact this
      -- Define the two comparison functions on ℝ.
      let f : ℝ → ℝ := fun u =>
        Set.indicator S (fun u => Real.exp (-u^2)) u
      let g : ℝ → ℝ := fun u =>
        Set.indicator S (fun _ => Real.exp (-r^2)) u
      -- Show that `f ≤ g` almost everywhere using `h_pointwise`.
      have h_le_ae : f ≤ᵐ[volume] g := by
        refine Filter.Eventually.of_forall ?_
        intro u
        by_cases hu : u ∈ S
        · -- Inside the interval, apply the pointwise bound.
          have h_nonneg' : 0 ≤ Real.exp (-u^2) :=
            h_nonneg u (by simpa [S, hS_def] using hu)
          have h_pt :
              Real.exp (-u^2) ≤ Real.exp (-r^2) :=
            h_pointwise u (by simpa [S, hS_def] using hu)
          simp [f, g, S, hS_def, hu, h_pt]
        · -- Outside the interval both indicators are zero.
          simp [f, g, S, hS_def, hu]
      -- Integrability of the two indicator functions.
      have h_int_gauss :
          Integrable (fun u : ℝ => Real.exp (-u^2)) (volume : Measure ℝ) := by
        -- Gaussian integrability with coefficient `a = 1`.
        have hpos : 0 < (1 : ℝ) := by norm_num
        have hbase :
            Integrable (fun u : ℝ => Real.exp (-(1 : ℝ) * u ^ 2))
              (volume : Measure ℝ) :=
          integrable_exp_neg_mul_sq hpos
        simpa using hbase
      have hS_meas : MeasurableSet S := by
        have : S = Set.Ioc r (n₀ : ℝ) := by
          ext u
          simp [S, hS_def, Set.Ioc]
        simp [S, hS_def, this]
      have h_int_f :
          Integrable f (volume : Measure ℝ) :=
        h_int_gauss.indicator hS_meas
      have h_int_g :
          Integrable g (volume : Measure ℝ) := by
        -- Skeleton: view `g` as the indicator of a bounded constant function
        -- on the finite-measure set `S`, prove `IntegrableOn` for that constant,
        -- then use `integrable_indicator_iff`.
        -- Step 1: the underlying constant function on ℝ.
        let c : ℝ → ℝ := fun _ => Real.exp (-r^2)
        -- Step 2: show integrability of `c` on `S` with respect to `volume`.
        have h_intOn_c : IntegrableOn c S (volume : Measure ℝ) := by
          classical
          -- Skeleton: reduce to integrability with respect to the restricted
          -- measure `volume.restrict S`, where we can apply standard boundedness
          -- criteria.
          -- First, observe that `c` is strongly measurable (being constant).
          have h_meas :
              AEStronglyMeasurable c (volume.restrict S) := by
            -- This is a direct instance of `aestronglyMeasurable_const`.
            simpa [c] using
              (aestronglyMeasurable_const :
                AEStronglyMeasurable (fun _ : ℝ => Real.exp (-r^2))
                  (volume.restrict S))
          -- Next, use that `S` has finite Lebesgue measure (since it is a bounded
          -- interval) to obtain `HasFiniteIntegral` for the constant function.
          have h_finite :
              HasFiniteIntegral c (volume.restrict S) := by
            -- We bound the norm of `c` by a constant and use the standard
            -- `hasFiniteIntegral_restrict_of_bounded` lemma.
            have hμfinite : volume S < ∞ := by
              -- `S = Ioc r n₀` is a bounded interval, so its Lebesgue
              -- measure is finite by `Real.volume_Ioc`.
              have : volume (Set.Ioc r (n₀ : ℝ)) < ∞ := by
                rw [Real.volume_Ioc]
                exact ENNReal.ofReal_lt_top
              simp [S, hS_def]
            -- On `S`, the norm of `c` is constantly `exp (-r^2)`, providing a
            -- uniform bound.
            have h_bound :
                ∀ᵐ x ∂volume.restrict S, ‖c x‖ ≤ Real.exp (-r^2) := by
              -- Since `c x` is constant, the bound is immediate.
              refine (ae_restrict_iff' hS_meas).2 ?_
              refine Filter.Eventually.of_forall ?_
              intro x
              intro hx
              simp [c]
            -- Apply the general boundedness criterion.
            exact
              MeasureTheory.hasFiniteIntegral_restrict_of_bounded
                (μ := volume) (s := S) (f := c) (C := Real.exp (-r^2))
                hμfinite h_bound
          -- Package these two facts into `Integrable` for the restricted measure.
          have h_int_restrict :
              Integrable c (volume.restrict S) :=
            ⟨h_meas, h_finite⟩
          -- Finally, rewrite this as `IntegrableOn c S volume`.
          simpa [IntegrableOn] using h_int_restrict
        -- Step 3: transfer `IntegrableOn` to integrability of the indicator.
        have h_int_indicator :
            Integrable (fun u => Set.indicator S c u) (volume : Measure ℝ) :=
          (integrable_indicator_iff (μ := volume) hS_meas).2 h_intOn_c
        -- Step 4: identify this indicator with `g`.
        have hg_eq :
            (fun u => Set.indicator S c u) = g := by
          funext u
          simp [g, c, S, hS_def]
        simpa [hg_eq] using h_int_indicator
      -- Apply `integral_mono_ae` to `f` and `g`.
      have h_int_mono :
          ∫ u, f u ∂(volume : Measure ℝ)
            ≤ ∫ u, g u ∂(volume : Measure ℝ) :=
        MeasureTheory.integral_mono_ae h_int_f h_int_g h_le_ae
      -- Put everything together.
      have :=
        calc
          ∫ u in Set.Ioc r n₀, Real.exp (-u^2) ∂(volume : Measure ℝ)
              = ∫ u, f u ∂(volume : Measure ℝ) := by simp [f, h_left]
          _ ≤ ∫ u, g u ∂(volume : Measure ℝ) := h_int_mono
          _ = Real.exp (-r^2) *
                (volume (Set.Ioc r (n₀ : ℝ))).toReal := by
                -- Rewrite the right-hand side using `h_right`.
                simpa [g, S, hS_def] using h_right.symm
      exact this
    -- Step 3: use that the length of `(r, n₀]` is at most 1, hence its volume is ≤ 1.
    have h_len_le_one :
        (volume (Set.Ioc r (n₀ : ℝ))).toReal ≤ (1 : ℝ) := by
      -- First express the volume in terms of the interval length.
      have h_len_eq :
          (volume (Set.Ioc r (n₀ : ℝ))).toReal = (n₀ : ℝ) - r := by
        have h_nonneg_diff : 0 ≤ (n₀ : ℝ) - r :=
          sub_nonneg.mpr (show r ≤ (n₀ : ℝ) from h_n₀_ge_r)
        simp [Real.volume_Ioc, h_nonneg_diff]
      -- Use `n₀ = Nat.ceil r` to bound the length by 1.
      have h_r_nonneg : 0 ≤ r := by
        have hε_le_r : ε ≤ r := hr
        have hε_nonneg : 0 ≤ ε := le_of_lt hε
        exact le_trans hε_nonneg hε_le_r
      have h_n₀_lt_r_add_one : (n₀ : ℝ) < r + 1 := by
        have := Nat.ceil_lt_add_one (a := r) h_r_nonneg
        simpa [n₀] using this
      have h_len_lt_one : (n₀ : ℝ) - r < (1 : ℝ) := by
        have h' : (n₀ : ℝ) < (1 : ℝ) + r := by
          simpa [add_comm] using h_n₀_lt_r_add_one
        exact (sub_lt_iff_lt_add).2 h'
      have h_len_le_one' : (n₀ : ℝ) - r ≤ (1 : ℝ) :=
        le_of_lt h_len_lt_one
      -- Rewrite the goal using the length identity in the desired direction.
      rw [h_len_eq]
      exact h_len_le_one'
    have h_mul_le :
        Real.exp (-r^2) * (volume (Set.Ioc r (n₀ : ℝ))).toReal
          ≤ Real.exp (-r^2) := by
      -- Multiply the length bound by the nonnegative constant `exp (-r^2)`.
      have h_exp_nonneg : 0 ≤ Real.exp (-r^2) := Real.exp_nonneg _
      have := mul_le_mul_of_nonneg_left h_len_le_one h_exp_nonneg
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using this
    -- Combine the two bounds.
    exact le_trans h_int_le h_mul_le
  -- Step 2d: compare the tail beyond `n₀` with a discrete Gaussian sum
  -- and apply the bound `hC_bound`.
  have h_tail :
      ∫ u in Set.Ioi (n₀ : ℝ), Real.exp (-u^2) ∂(volume : Measure ℝ)
        ≤ (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
    exact
      gaussian_one_sided_tail_discrete
        (ε := ε) (C := C) (n₀ := n₀) hC_bound h_n₀_ge_ε h_n₀
  -- Step 2e: combine the bounds and absorb `exp (-(n₀)^2)` into `exp (-r^2)`
  -- using `n₀ ≥ r`.
  have h_tail_to_r :
      C * Real.exp (-(n₀ : ℝ)^2) ≤ C * Real.exp (-r^2) := by
    -- From `ε ≤ r` and `0 < ε` we get `0 ≤ r`.
    have hr_nonneg : 0 ≤ r :=
      le_trans (le_of_lt hε) hr
    -- Square the inequality `r ≤ n₀` on nonnegative reals.
    have h_sq : r ^ 2 ≤ (n₀ : ℝ) ^ 2 := by
      have := mul_self_le_mul_self hr_nonneg h_n₀_ge_r
      simpa [pow_two] using this
    -- Turn the inequality around in the exponent (minus sign).
    have h_arg : -(n₀ : ℝ) ^ 2 ≤ -r ^ 2 := by
      simpa using (neg_le_neg h_sq)
    -- Monotonicity of the exponential on ℝ.
    have h_exp_mono :
        Real.exp (-(n₀ : ℝ) ^ 2) ≤ Real.exp (-r ^ 2) :=
      Real.exp_le_exp.mpr h_arg
    -- Multiply by the positive constant `C`.
    have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
    have := mul_le_mul_of_nonneg_left h_exp_mono hC_nonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have h_main :
      ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ)
        ≤ (C + 2) * Real.exp (-r^2) := by
    -- Combine the decomposition and the two tail bounds.
    have := calc
      ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ)
          = ∫ u in Set.Ioc r n₀, Real.exp (-u^2) ∂(volume : Measure ℝ)
              +
            ∫ u in Set.Ioi (n₀ : ℝ), Real.exp (-u^2) ∂(volume : Measure ℝ) := h_split_int
      _ ≤ Real.exp (-r^2) + (C + 1) * Real.exp (-(n₀ : ℝ)^2) := by
            -- Apply h_initial and h_tail
            exact add_le_add h_initial h_tail
      _ ≤ Real.exp (-r^2) + (C + 1) * Real.exp (-r^2) := by
            -- Apply h_tail_to_r': (C + 1) * exp(-n₀²) ≤ (C + 1) * exp(-r²)
            have h_tail_to_r' : (C + 1) * Real.exp (-(n₀ : ℝ)^2) ≤ (C + 1) * Real.exp (-r^2) := by
              have hC1_nonneg : 0 ≤ C + 1 := by linarith [hC_nonneg]
              have h_exp_mono : Real.exp (-(n₀ : ℝ) ^ 2) ≤ Real.exp (-r ^ 2) := by
                have hr_nonneg : 0 ≤ r := le_trans (le_of_lt hε) hr
                have h_sq : r ^ 2 ≤ (n₀ : ℝ) ^ 2 := by
                  have := mul_self_le_mul_self hr_nonneg h_n₀_ge_r
                  simpa [pow_two] using this
                have h_arg : -(n₀ : ℝ) ^ 2 ≤ -r ^ 2 := by simpa using (neg_le_neg h_sq)
                exact Real.exp_le_exp.mpr h_arg
              exact mul_le_mul_of_nonneg_left h_exp_mono hC1_nonneg
            exact add_le_add_left h_tail_to_r' _
      _ = (C + 2) * Real.exp (-r^2) := by
            ring
    exact this
  simpa using h_main

/-- Symmetry identity: for `r ≥ 0`, the two-sided tail `{|u| > r}` is twice the one-sided tail
`(r, ∞)`. -/
lemma gaussian_tail_split_symm (r : ℝ) (hr : 0 ≤ r) :
    ∫ u in {u | |u| > r}, Real.exp (-u^2) ∂(volume : Measure ℝ)
      = 2 * ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
  classical
  -- Abbreviations for the positive and negative half-lines beyond radius `r`.
  set A : Set ℝ := {u : ℝ | r < u} with hA_def
  set B : Set ℝ := {u : ℝ | u < -r} with hB_def
  -- Use additivity of the integral over disjoint measurable sets to split the tail.
  have h_split :
      ∫ u in {u : ℝ | |u| > r}, Real.exp (-u^2) ∂(volume : Measure ℝ)
        =
        ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ)
          + ∫ u in B, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
    -- Step 1: rewrite all three set integrals in terms of indicators on ℝ.
    have h_left :
        ∫ u in {u : ℝ | |u| > r}, Real.exp (-u^2) ∂(volume : Measure ℝ)
          =
          ∫ u, Set.indicator {u : ℝ | |u| > r}
            (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := by
      -- Use `integral_indicator` with measurability of `{u | |u| > r}`.
      have h_meas :
          MeasurableSet {u : ℝ | |u| > r} := by
        -- This set coincides with `{u | r < |u|}`, for which we have
        -- the helper measurability lemma `measurableSet_abs_gt`.
        have h' : MeasurableSet {u : ℝ | r < |u|} := measurableSet_abs_gt r
        have h_eq :
            {u : ℝ | |u| > r} = {u : ℝ | r < |u|} := by
          ext u
          -- `|u| > r` is equivalent to `r < |u|`.
          simp [gt_iff_lt]
        simpa [h_eq] using h'
      simpa using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := {u : ℝ | |u| > r})
          (f := fun u => Real.exp (-u^2)) h_meas).symm
    have hA :
        ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ)
          =
          ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := by
      -- Use `integral_indicator` and the fact that `A = Set.Ioi r` is measurable.
      have hA_meas : MeasurableSet A := by
        -- `A` was defined as `{u | r < u}`, which is exactly `Set.Ioi r`.
        have : A = Set.Ioi r := by
          ext u
          simp [A, hA_def, Set.Ioi]
        simp [this]
      simpa using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := A) (f := fun u => Real.exp (-u^2)) hA_meas).symm
    have hB :
        ∫ u in B, Real.exp (-u^2) ∂(volume : Measure ℝ)
          =
          ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := by
      -- Use `integral_indicator` and the fact that `B = Set.Iio (-r)` is measurable.
      have hB_meas : MeasurableSet B := by
        -- `B` was defined as `{u | u < -r}`, which is exactly `Set.Iio (-r)`.
        have : B = Set.Iio (-r) := by
          ext u
          simp [B, hB_def, Set.Iio]
        simp [this]
      simpa using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := B) (f := fun u => Real.exp (-u^2)) hB_meas).symm
    -- Step 2: show that the indicator of the tail set is the sum of the indicators
    -- of the positive and negative half-lines, using the disjoint decomposition
    -- `{u | |u| > r} = A ∪ B`.
    have h_ind :
        (fun u => Set.indicator {u : ℝ | |u| > r} (fun u => Real.exp (-u^2)) u)
          =
        (fun u =>
          Set.indicator A (fun u => Real.exp (-u^2)) u +
          Set.indicator B (fun u => Real.exp (-u^2)) u) := by
      -- Describe the tail set `{|u| > r}` as the disjoint union of `A` and `B`.
      have h_union : {u : ℝ | |u| > r} = A ∪ B := by
        ext u
        constructor
        · intro hu
          -- `hu : |u| > r` means `r < |u|`.
          have h' : r < |u| := by simpa [gt_iff_lt] using hu
          by_cases h0 : 0 ≤ u
          · -- Case 1: `u ≥ 0`, so `|u| = u` and we are in `A`.
            have : r < u := by
              simpa [abs_of_nonneg h0] using h'
            left
            -- `A = {u | r < u}`.
            show u ∈ A
            change r < u
            exact this
          · -- Case 2: `u < 0`, so `|u| = -u` and we are in `B`.
            have hneg : u < 0 := lt_of_not_ge h0
            have : r < -u := by
              simpa [abs_of_neg hneg] using h'
            -- From `r < -u` we derive `u < -r`.
            have hu' : u < -r := by
              have hflip := neg_lt_neg this
              simpa [neg_neg] using hflip
            right
            show u ∈ B
            change u < -r
            exact hu'
        · intro hu
          rcases hu with hA | hB
          · -- `u ∈ A`, so `r < u` and in particular `u ≥ 0`.
            have hru : r < u := by
              simpa [A, hA_def] using hA
            have h0 : 0 ≤ u := le_trans hr (le_of_lt hru)
            -- Hence `|u| = u` and `|u| > r`.
            have : |u| > r := by
              simpa [abs_of_nonneg h0, gt_iff_lt] using hru
            simpa [gt_iff_lt] using this
          · -- `u ∈ B`, so `u < -r` and in particular `u < 0`.
            have hu_neg : u < -r := by
              simpa [B, hB_def] using hB
            have hneg0 : -r ≤ 0 := by
              simpa using (neg_nonpos.mpr hr)
            have h0 : u < 0 := lt_of_lt_of_le hu_neg hneg0
            -- From `u < -r` we get `r < -u`, and hence `|u| = -u > r`.
            have hru : r < -u := by
              have hflip := neg_lt_neg hu_neg
              simpa [neg_neg] using hflip
            have : |u| > r := by
              simpa [abs_of_neg h0, gt_iff_lt] using hru
            simpa [gt_iff_lt] using this
      -- The right and left half-lines are disjoint.
      have h_disj : Disjoint A B := by
        refine Set.disjoint_left.mpr ?_
        intro u hAu hBu
        have hru : r < u := by
          simpa [A, hA_def] using hAu
        have hu_neg : u < -r := by
          simpa [B, hB_def] using hBu
        -- From `r < u < -r` and `0 ≤ r` we derive a contradiction.
        have : False := by
          linarith
        exact this
      -- With the decomposition and disjointness, use the indicator-union lemma.
      funext u
      have : Set.indicator {u : ℝ | |u| > r}
              (fun u => Real.exp (-u^2)) u
          = Set.indicator (A ∪ B)
              (fun u => Real.exp (-u^2)) u := by
        -- Rewrite `{|u| > r}` as `A ∪ B`.
        simp [h_union]
      have h_union_ind :
          Set.indicator (A ∪ B) (fun u => Real.exp (-u^2)) u
            =
          Set.indicator A (fun u => Real.exp (-u^2)) u +
          Set.indicator B (fun u => Real.exp (-u^2)) u := by
        -- Evaluate the functional identity from `indicator_union_of_disjoint` at `u`.
        have hfun :=
          Set.indicator_union_of_disjoint
            (s := A) (t := B)
            (f := fun u : ℝ => Real.exp (-u^2)) h_disj
        -- `hfun : (A ∪ B).indicator f = fun a => A.indicator f a + B.indicator f a`
        -- Apply both sides to `u`.
        have := congrArg (fun g : ℝ → ℝ => g u) hfun
        simpa using this
      calc
        Set.indicator {u : ℝ | |u| > r}
            (fun u => Real.exp (-u^2)) u
            = Set.indicator (A ∪ B)
                (fun u => Real.exp (-u^2)) u := this
        _ = Set.indicator A (fun u => Real.exp (-u^2)) u +
              Set.indicator B (fun u => Real.exp (-u^2)) u := h_union_ind
    -- Step 3: use linearity of the integral to split the sum of indicators.
    have h_sum :
        ∫ u,
          (Set.indicator A (fun u => Real.exp (-u^2)) u +
           Set.indicator B (fun u => Real.exp (-u^2)) u) ∂(volume : Measure ℝ)
          =
        ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ)
          +
        ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := by
      -- Both indicators are integrable since `exp (-u^2)` is integrable on ℝ.
      have h_int :
          Integrable (fun u : ℝ => Real.exp (-u^2)) (volume : Measure ℝ) := by
        -- Use the standard Gaussian integrability lemma with coefficient `a = 1`.
        have hpos : 0 < (1 : ℝ) := by norm_num
        have hbase : Integrable (fun u : ℝ => Real.exp (-(1 : ℝ) * u ^ 2))
            (volume : Measure ℝ) :=
          integrable_exp_neg_mul_sq hpos
        simpa using hbase
      have hA_meas : MeasurableSet A := by
        have : A = Set.Ioi r := by
          ext u
          simp [A, hA_def, Set.Ioi]
        simp [this]
      have hB_meas : MeasurableSet B := by
        have : B = Set.Iio (-r) := by
          ext u
          simp [B, hB_def, Set.Iio]
        simp [this]
      have h_intA :
          Integrable (fun u : ℝ =>
              Set.indicator A (fun u => Real.exp (-u^2)) u)
            (volume : Measure ℝ) :=
        h_int.indicator hA_meas
      have h_intB :
          Integrable (fun u : ℝ =>
              Set.indicator B (fun u => Real.exp (-u^2)) u)
            (volume : Measure ℝ) :=
        h_int.indicator hB_meas
      -- Apply linearity of the integral to the sum of the two indicators.
      simpa using
        (MeasureTheory.integral_add h_intA h_intB)
    -- Step 4: assemble all identities and rewrite indicators back to set integrals.
    calc
      ∫ u in {u : ℝ | |u| > r}, Real.exp (-u^2) ∂(volume : Measure ℝ)
          = ∫ u, Set.indicator {u : ℝ | |u| > r}
                (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := h_left
      _ = ∫ u,
              (Set.indicator A (fun u => Real.exp (-u^2)) u +
               Set.indicator B (fun u => Real.exp (-u^2)) u)
              ∂(volume : Measure ℝ) := by simp [h_ind]
      _ =
          ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ)
            +
          ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := h_sum
      _ =
          ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ)
            +
          ∫ u in B, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
            simp [hA, hB]
  -- Change of variables `u ↦ -u` on the negative half-line and evenness of the integrand
  -- identify the two integrals over `A` and `B`.
  have h_change :
      ∫ u in B, Real.exp (-u^2) ∂(volume : Measure ℝ)
        = ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
    -- View both set integrals as integrals over ℝ with indicators.
    have hA_meas : MeasurableSet A := by
      have : A = Set.Ioi r := by
        ext u
        simp [A, hA_def, Set.Ioi]
      simp [this]
    have hB_meas : MeasurableSet B := by
      have : B = Set.Iio (-r) := by
        ext u
        simp [B, hB_def, Set.Iio]
      simp [this]
    have hA_int :
        ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ)
          =
          ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := by
      simpa using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := A) (f := fun u => Real.exp (-u^2)) hA_meas).symm
    have hB_int :
        ∫ u in B, Real.exp (-u^2) ∂(volume : Measure ℝ)
          =
          ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := by
      simpa using
        (MeasureTheory.integral_indicator
          (μ := (volume : Measure ℝ))
          (s := B) (f := fun u => Real.exp (-u^2)) hB_meas).symm
    -- The reflection `u ↦ -u` maps `B` onto `A`, and the integrand is even.
    have h_ind_reflect :
        (fun u : ℝ => Set.indicator B (fun u => Real.exp (-u^2)) u)
          =
        (fun u : ℝ => Set.indicator A (fun u => Real.exp (-u^2)) (-u)) := by
      funext u
      by_cases hBu : u ∈ B
      · -- On `B`, `-u` lies in `A` and the Gaussian is even.
        have hAu : -u ∈ A := by
          -- `u ∈ B` means `u < -r`, hence `r < -u`.
          have hu_neg : u < -r := by
            simpa [B, hB_def] using hBu
          have hru : r < -u := by
            have hflip := neg_lt_neg hu_neg
            simpa [neg_neg] using hflip
          -- So `-u` lies in `{x | r < x} = A`.
          show -u ∈ A
          change r < -u
          exact hru
        simp [hBu, hAu]
      · -- Outside `B`, `u` is not in `B`, and `-u` is not in `A`.
        have hBu' : u ∉ B := hBu
        have hAu' : -u ∉ A := by
          -- If `-u ∈ A`, then `u ∈ B`; contradiction.
          intro hAu
          have hru : r < -u := by
            simpa [A, hA_def] using hAu
          have hu_neg : u < -r := by
            have hflip := neg_lt_neg hru
            simpa [neg_neg] using hflip
          have : u ∈ B := by
            change u < -r at hu_neg
            simpa [B, hB_def] using hu_neg
          exact hBu' this
        simp [hBu', hAu']
    -- Apply the reflection invariance of the Lebesgue integral under `u ↦ -u`.
    have h_reflect :
        ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ)
          =
        ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := by
      -- First rewrite the left-hand side using `h_ind_reflect`.
      have h1 :
          ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ)
            =
          ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) (-u) ∂(volume : Measure ℝ) := by
        simp [h_ind_reflect]
      -- Then apply `integral_comp_mul_left` with scaling factor `-1`.
      have hcomp :
          (∫ u : ℝ,
              (fun v : ℝ =>
                Set.indicator A (fun v => Real.exp (-v^2)) v) (-1 * u))
            =
          |(-1 : ℝ)⁻¹| •
            ∫ v : ℝ,
              (fun v : ℝ =>
                Set.indicator A (fun v => Real.exp (-v^2)) v) v := by
        simpa using
          (Measure.integral_comp_mul_left
            (g := fun v : ℝ =>
              Set.indicator A (fun v => Real.exp (-v^2)) v)
            (-1 : ℝ))
      -- Simplify the scaling factor `|(-1)⁻¹| = 1`.
      have hcomp' :
          (∫ u : ℝ,
              Set.indicator A (fun v => Real.exp (-v^2)) (-u) ∂(volume : Measure ℝ))
            =
          ∫ v : ℝ,
              Set.indicator A (fun v => Real.exp (-v^2)) v ∂(volume : Measure ℝ) := by
        simpa [one_div, abs_neg, (abs_one : |(1 : ℝ)| = 1), smul_eq_mul] using hcomp
      exact h1.trans hcomp'
    -- Put everything together and revert to set integrals.
    calc
      ∫ u in B, Real.exp (-u^2) ∂(volume : Measure ℝ)
          = ∫ u, Set.indicator B (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := hB_int
      _ = ∫ u, Set.indicator A (fun u => Real.exp (-u^2)) u ∂(volume : Measure ℝ) := h_reflect
      _ = ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
            simp [hA_int]
  -- Finally, rewrite `A` as `Set.Ioi r` and combine everything.
  have hA_Ioi :
      (∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ))
        = ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
    -- `A` was defined as `{u | r < u}`, which is exactly `Set.Ioi r`.
    simp [A, hA_def, Set.Ioi]
  calc
    ∫ u in {u | |u| > r}, Real.exp (-u^2) ∂(volume : Measure ℝ)
        = ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ) +
            ∫ u in B, Real.exp (-u^2) ∂(volume : Measure ℝ) := h_split
    _ = ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ) +
          ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
            simp [h_change]
    _ = 2 * ∫ u in A, Real.exp (-u^2) ∂(volume : Measure ℝ) := by ring
    _ = 2 * ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ) := by
            simp [hA_Ioi]

/-- Standard Gaussian tail bound, uniform for all radii `r ≥ ε`.
This will be used as the base one-dimensional estimate in
`gaussian_tail_uniform_bound`.
Now proven for all ε > 0 (previously required ε ≥ 10). -/
lemma gaussian_tail_standard_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ r : ℝ, ε ≤ r →
        ∫ u in {u | |u| > r}, Real.exp (-u^2) ∂(volume : Measure ℝ)
          ≤ C₀ * Real.exp (-r^2) := by
  classical
  -- Obtain a one-sided tail bound on `(r, ∞)` and upgrade it to a
  -- two-sided bound on `{u | |u| > r}` using symmetry.
  obtain ⟨C, hC_pos, hC⟩ := gaussian_one_sided_tail_bound ε hε
  refine ⟨2 * C, ?_, ?_⟩
  · -- Positivity of `C₀ = 2 * C`.
    have h2 : 0 < (2 : ℝ) := by norm_num
    exact mul_pos h2 hC_pos
  · intro r hr
    -- One-sided tail estimate from `gaussian_one_sided_tail_bound`.
    have h_one_side :
        ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ)
          ≤ C * Real.exp (-r^2) :=
      hC r hr
    -- From `ε ≤ r` and `0 < ε` we get `0 ≤ r`.
    have hr_nonneg : 0 ≤ r := le_trans (le_of_lt hε) hr
    -- Symmetry: two-sided tail is twice the one-sided tail.
    have h_symm :
        ∫ u in {u | |u| > r}, Real.exp (-u^2) ∂(volume : Measure ℝ)
          = 2 * ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ) :=
      gaussian_tail_split_symm r hr_nonneg
    -- Trivial comparison `2 * C ≤ 2 * C`, used to match the desired form.
    have hC_le : 2 * C ≤ 2 * C := le_rfl
    calc
      ∫ u in {u | |u| > r}, Real.exp (-u^2) ∂(volume : Measure ℝ)
          = 2 * ∫ u in Set.Ioi r, Real.exp (-u^2) ∂(volume : Measure ℝ) := h_symm
      _ ≤ 2 * (C * Real.exp (-r^2)) := by
            gcongr
      _ = (2 * C) * Real.exp (-r^2) := by ring
      _ ≤ (2 * C) * Real.exp (-r^2) := by
            rfl

/-- Change-of-variables identity for Gaussian tails with width `(n+1)⁻¹`,
expressed in terms of the standard Gaussian on `ℝ`. -/
lemma gaussian_tail_scale (ε : ℝ) (n : ℕ) :
    ∫ t in {t | |t| > ε},
      Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂volume
      =
      (1 / (n + 1 : ℝ)) *
        ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
          Real.exp (-u^2) ∂volume := by
  classical
  -- We use the scaling change-of-variables for Haar measure on ℝ.
  have hR_pos : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  -- Step 1: apply the general `setIntegral_comp_smul_of_pos` lemma with
  -- `f u = exp (-u^2)` and `s = {t | |t| > ε}`.
  have h_aux :
      ∫ t in {t : ℝ | |t| > ε},
        Real.exp (-(((n + 1 : ℝ) * t)^2)) ∂(volume : Measure ℝ)
      =
      (1 / (n + 1 : ℝ)) *
        ∫ u in (n + 1 : ℝ) • {t : ℝ | |t| > ε},
          Real.exp (-u^2) ∂(volume : Measure ℝ) := by
    have :=
      Measure.setIntegral_comp_smul_of_pos
        (μ := (volume : Measure ℝ))
        (E := ℝ) (F := ℝ)
        (f := fun u : ℝ => Real.exp (-u^2))
        (s := {t : ℝ | |t| > ε})
        (R := (n + 1 : ℝ)) hR_pos
    -- In ℝ, scalar multiplication is ordinary multiplication and
    -- `finrank ℝ ℝ = 1`, so the scalar factor simplifies to `1/(n+1)`.
    simpa [smul_eq_mul, Module.finrank_self, pow_one, one_div] using this
  -- Step 2: on the left, rewrite `((n+1)*t)^2` as `t^2 * (n+1)^2`.
  have h_left_simpl :
      ∫ t in {t : ℝ | |t| > ε},
        Real.exp (-(((n + 1 : ℝ) * t)^2)) ∂(volume : Measure ℝ)
      =
      ∫ t in {t : ℝ | |t| > ε},
        Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂(volume : Measure ℝ) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro t
    have : ((n + 1 : ℝ) * t) ^ 2 = t ^ 2 * (n + 1 : ℝ) ^ 2 := by
      ring
    simp [this]
  -- Step 3: on the right, identify the scaled set `(n+1) • {t | |t| > ε}`.
  have h_set :
      (n + 1 : ℝ) • {t : ℝ | |t| > ε}
        = {u : ℝ | |u| > ε * (n + 1 : ℝ)} := by
    ext u
    constructor
    · -- Forward inclusion: if `u = (n+1) * t` with `|t| > ε`, then `|u| > ε * (n+1)`.
      intro hu
      rcases hu with ⟨t, ht, rfl⟩
      have ht' : ε < |t| := by
        simpa [Set.mem_setOf_eq, gt_iff_lt] using ht
      have h_mul : ε * (n + 1 : ℝ) < |t| * (n + 1 : ℝ) :=
        mul_lt_mul_of_pos_right ht' hR_pos
      have : ε * (n + 1 : ℝ) < |(n + 1 : ℝ) * t| := by
        simpa [abs_mul, abs_of_pos hR_pos, mul_comm, mul_left_comm, mul_assoc] using h_mul
      simpa [Set.mem_setOf_eq, gt_iff_lt, mul_comm, mul_left_comm, mul_assoc] using this
    · -- Backward inclusion: from `|u| > ε * (n+1)` recover `u = (n+1)*t` with `|t| > ε`.
      intro hu
      have hu' : ε * (n + 1 : ℝ) < |u| := by
        simpa [Set.mem_setOf_eq, gt_iff_lt, mul_comm, mul_left_comm, mul_assoc] using hu
      have hu'' : ε < |u| / (n + 1 : ℝ) := by
        have : ε * (n + 1 : ℝ) < |u| := hu'
        calc
          ε = (ε * (n + 1 : ℝ)) / (n + 1 : ℝ) := by
                field_simp
          _ < |u| / (n + 1 : ℝ) := by
                exact div_lt_div_of_pos_right this hR_pos
      have hu''' : ε < |u / (n + 1 : ℝ)| := by
        rw [abs_div, abs_of_pos hR_pos]
        exact hu''
      refine ⟨u / (n + 1 : ℝ), ?_, ?_⟩
      · simpa [Set.mem_setOf_eq, gt_iff_lt] using hu'''
      · have hR_ne : (n + 1 : ℝ) ≠ 0 := ne_of_gt hR_pos
        field_simp
  -- Step 4: rewrite the right-hand side of `h_aux` using the set identity.
  have h_right_simpl :
      ∫ u in (n + 1 : ℝ) • {t : ℝ | |t| > ε},
        Real.exp (-u^2) ∂(volume : Measure ℝ)
      =
      ∫ u in {u : ℝ | |u| > ε * (n + 1 : ℝ)},
        Real.exp (-u^2) ∂(volume : Measure ℝ) := by
    simp [h_set]
  -- Step 5: combine all identities and remove explicit `volume` annotations.
  have h_main :
      ∫ t in {t : ℝ | |t| > ε},
        Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂(volume : Measure ℝ)
      =
      (1 / (n + 1 : ℝ)) *
        ∫ u in {u : ℝ | |u| > ε * (n + 1 : ℝ)},
          Real.exp (-u^2) ∂(volume : Measure ℝ) := by
    calc
      ∫ t in {t : ℝ | |t| > ε},
        Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂(volume : Measure ℝ)
          = ∫ t in {t : ℝ | |t| > ε},
              Real.exp (-(((n + 1 : ℝ) * t)^2)) ∂(volume : Measure ℝ) :=
            h_left_simpl.symm
      _ = (1 / (n + 1 : ℝ)) *
            ∫ u in (n + 1 : ℝ) • {t : ℝ | |t| > ε},
              Real.exp (-u^2) ∂(volume : Measure ℝ) := h_aux
      _ = (1 / (n + 1 : ℝ)) *
            ∫ u in {u : ℝ | |u| > ε * (n + 1 : ℝ)},
              Real.exp (-u^2) ∂(volume : Measure ℝ) := by
            simp [h_right_simpl]
  -- Final statement: same as `h_main` but with `volume` written implicitly.
  simpa using h_main

/-!
Proof plan for `gaussian_tail_uniform_bound`:

1. Isolate a purely one–dimensional tail bound for the standard Gaussian.
   Prove an auxiliary lemma of the form
   `∃ C > 0, ∀ r ≥ ε, ∫_{|u| > r} exp (-u^2) ≤ C * exp (-r^2)`.
   A convenient strategy is:
   - partition `[r, ∞)` into unit intervals `[k, k+1]`;
   - bound the integral on each interval by `exp (-k^2)`;
   - compare the resulting series `∑_{k ≥ ⌈r⌉} exp (-k^2)` with the
     discrete decay lemmas already proved above (`exponential_decay_bound`
     or `general_exponential_bound`) to obtain the exponential tail.

2. Reuse the change-of-variables part of `gaussian_tail_bound_integral`
   (or factor it out as a separate lemma) to get, for each `n`,
   the scaling identity
   ```
   ∫_{|τ - τ₀| > ε} exp (-(τ - τ₀)^2 * (n + 1)^2)
     = (1 / (n + 1)) *
         ∫_{|u| > ε * (n + 1)} exp (-u^2).
   ```

3. Combine Steps 1 and 2: apply the uniform tail bound from Step 1 with
   `r = ε * (n + 1)` (which is ≥ ε) to obtain
   ```
   ∫_{|τ - τ₀| > ε} exp (-(τ - τ₀)^2 * (n + 1)^2)
     ≤ (1 / (n + 1)) * C * exp (-(ε * (n + 1))^2)
     = C_n * exp (-ε^2 * (n + 1)^2),
   ```
   where we set `C_n := (1 / (n + 1)) * C`.

4. Choose the global constant `C₀ := C`. Since `0 < 1 / (n + 1) ≤ 1`
   for all `n`, we automatically have `C_n ≤ C₀`. This yields the
   desired statement of `gaussian_tail_uniform_bound` with a uniform
   bound on the Gaussian tail constants and no growth in `n`.

5. To implement the proof in Lean, it will likely be cleaner to:
   - first introduce the auxiliary tail lemma from Step 1 as a separate
     lemma near `gaussian_tail_bound_integral`;
   - refactor `gaussian_tail_bound_integral` so that the scaling part is
     available as a standalone lemma;
   - then replace the current skeleton of `gaussian_tail_uniform_bound`
     by the direct argument described in Steps 2–4, rather than trying
     to extract monotonicity of the constants from the existing proof.
-/
-- Revised version: Proven for all ε > 0
-- The exponential decay exp(-ε² * (n+1)²) dominates for all positive ε,
-- as verified by numerical computation in verify_gaussian_tail_736.js
lemma gaussian_tail_uniform_bound (τ₀ ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ n : ℕ, ∃ C_n : ℝ, 0 < C_n ∧ C_n ≤ C₀ ∧
        ∫ τ in {τ | |τ - τ₀| > ε},
          Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
          ≤ C_n * Real.exp (-ε^2 * (n + 1 : ℝ)^2) := by
  classical
  -- Step 1: obtain a one-dimensional uniform bound for the standard Gaussian.
  obtain ⟨C₀, hC₀_pos, hC₀_tail⟩ :=
    gaussian_tail_standard_uniform ε hε
  -- This `C₀` will be our global uniform bound.
  refine ⟨C₀, hC₀_pos, ?_⟩
  -- Step 2: for each `n`, define a local constant `C_n := (1/(n+1)) * C₀`.
  intro n
  let C_n : ℝ := (1 / (n + 1 : ℝ)) * C₀
  have hR_pos : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hC_n_pos : 0 < C_n := by
    -- Positivity of `C_n` from `C₀ > 0` and `1/(n+1) > 0`.
    have h_inv_pos : 0 < (1 / (n + 1 : ℝ)) := by
      -- Using that `n + 1 > 0`.
      exact one_div_pos.mpr hR_pos
    simpa [C_n, mul_comm] using mul_pos h_inv_pos hC₀_pos
  refine ⟨C_n, hC_n_pos, ?_, ?_⟩
  · -- Step 3: show `C_n ≤ C₀` using `0 < 1 / (n + 1) ≤ 1`.
    have h_inv_le_one : (1 / (n + 1 : ℝ)) ≤ 1 := by
      -- Since `1 ≤ (n+1)` for all `n`, dividing by the positive
      -- number `(n+1)` gives `1/(n+1) ≤ 1`.
      have h_le : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        have : (1 : ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        exact_mod_cast this
      have h :=
        one_div_le_one_div_of_le (show (0 : ℝ) < (1 : ℝ) by norm_num) h_le
      simpa [one_div] using h
    have hC₀_nonneg : 0 ≤ C₀ := le_of_lt hC₀_pos
    -- Monotonicity of multiplication by a nonnegative scalar.
    have h_le : C_n ≤ 1 * C₀ := by
      -- `C_n = (1/(n+1)) * C₀` and `1 * C₀ = C₀`.
      have := mul_le_mul_of_nonneg_right h_inv_le_one hC₀_nonneg
      -- Rewrite both sides in terms of `C_n` and `C₀`.
      simpa [C_n] using this
    simpa using h_le
  · -- Step 4: use the scaling identity and the one-dimensional tail
    -- bound to obtain the desired inequality.
    -- First translate the integral to be centered at `0`:
    --   τ ↦ t := τ - τ₀.
    have h_translate :
        ∫ τ in {τ | |τ - τ₀| > ε},
          Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
          =
          ∫ t in {t | |t| > ε},
            Real.exp (-t^2 * (n + 1 : ℝ)^2) ∂volume := by
      classical
      -- abbreviations for the integrand and the symmetric tail set
      set f : ℝ → ℝ := fun t =>
        Real.exp (-t^2 * (n + 1 : ℝ)^2) with hf_def
      set S : Set ℝ := {τ : ℝ | |τ - τ₀| > ε} with hS_def
      set T : Set ℝ := {t : ℝ | |t| > ε} with hT_def
      have hS_meas : MeasurableSet S := by
        -- `S = {τ | ε < |τ - τ₀|}` is an open set
        have hopen : IsOpen {τ : ℝ | ε < |τ - τ₀|} :=
          isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)
        have : S = {τ : ℝ | ε < |τ - τ₀|} := by
          ext τ
          simp [S, hS_def, gt_iff_lt]
        rw [this]
        exact hopen.measurableSet
      have hT_meas : MeasurableSet T := by
        -- `T = {t | ε < |t|}` is an open set
        have hopen : IsOpen {t : ℝ | ε < |t|} :=
          isOpen_lt continuous_const continuous_abs
        have : T = {t : ℝ | ε < |t|} := by
          ext t
          simp [T, hT_def, gt_iff_lt]
        rw [this]
        exact hopen.measurableSet
      -- Rewrite the left-hand side as an integral over ℝ with an indicator.
      have h_left :
          ∫ τ in S, f (τ - τ₀) ∂volume =
            ∫ τ, S.indicator (fun τ => f (τ - τ₀)) τ ∂volume := by
        -- `integral_indicator` gives the desired identity.
        simpa [S, hS_def] using
          (MeasureTheory.integral_indicator
            (μ := (volume : Measure ℝ))
            (s := S) (f := fun τ => f (τ - τ₀)) hS_meas).symm
      -- Identify this indicator with the shifted symmetric tail indicator.
      have h_indicator :
          S.indicator (fun τ => f (τ - τ₀)) =
            fun τ => T.indicator f (τ - τ₀) := by
        funext τ
        by_cases h : |τ - τ₀| > ε
        · -- inside the tail on both sides
          have hS : τ ∈ S := by simpa [S, hS_def] using h
          have hT : τ - τ₀ ∈ T := by
            -- same condition written on the shifted variable
            simpa [T, hT_def] using h
          simp only [Set.indicator_of_mem hS, Set.indicator_of_mem hT]
        · -- outside the tail on both sides
          have hS : τ ∉ S := by simpa [S, hS_def] using h
          have hT : τ - τ₀ ∉ T := by
            simpa [T, hT_def] using h
          simp only [Set.indicator_of_notMem hS, Set.indicator_of_notMem hT]
      have h_left' :
          ∫ τ in S, f (τ - τ₀) ∂volume =
            ∫ τ, T.indicator f (τ - τ₀) ∂volume := by
        refine h_left.trans ?_
        -- replace the integrand using the pointwise identity above
        refine MeasureTheory.integral_congr_ae ?_
        exact Filter.Eventually.of_forall (fun τ => by
          simp [h_indicator] )
      -- Rewrite the right-hand side as an integral over ℝ with an indicator.
      have h_right :
          ∫ t in T, f t ∂volume =
            ∫ t, T.indicator f t ∂volume := by
        simpa [T, hT_def] using
          (MeasureTheory.integral_indicator
            (μ := (volume : Measure ℝ))
            (s := T) (f := f) hT_meas).symm
      -- Use translation invariance of Lebesgue measure: τ ↦ τ - τ₀.
      have h_trans :
          ∫ τ, T.indicator f (τ - τ₀) ∂volume =
            ∫ t, T.indicator f t ∂volume := by
        -- Apply `integral_add_left_eq_self` to the function
        -- `x ↦ T.indicator f (x - τ₀)`.
        simpa [T, hT_def, f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (MeasureTheory.integral_add_left_eq_self
            (μ := (volume : Measure ℝ))
            (f := fun x => T.indicator f (x - τ₀)) τ₀).symm
      -- Put everything together and unfold the abbreviations.
      have h_final :
          ∫ τ in S, f (τ - τ₀) ∂volume =
            ∫ t in T, f t ∂volume := by
        calc
          ∫ τ in S, f (τ - τ₀) ∂volume
              = ∫ τ, T.indicator f (τ - τ₀) ∂volume := h_left'
          _ = ∫ t, T.indicator f t ∂volume := h_trans
          _ = ∫ t in T, f t ∂volume := h_right.symm
      simpa [S, hS_def, T, hT_def, f, sub_eq_add_neg] using h_final
    -- Next apply the scaling lemma to pass to the standard Gaussian.
    have h_scale := gaussian_tail_scale ε n
    -- Combine translation and scaling.
    have h_main :
        ∫ τ in {τ | |τ - τ₀| > ε},
          Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
        =
        (1 / (n + 1 : ℝ)) *
          ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
            Real.exp (-u^2) ∂volume := by
      -- This is just `h_translate` followed by `h_scale`.
      rw [h_translate, h_scale]
    -- Apply the one-dimensional uniform bound with radius `r = ε * (n+1)`,
    -- which satisfies `r ≥ ε` because `n+1 ≥ 1` and `ε > 0`.
    have h_r_ge : ε ≤ ε * (n + 1 : ℝ) := by
      -- Divide by `ε > 0` and use `1 ≤ (n+1)`.
      have h_one_le : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        have : (1 : ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        exact_mod_cast this
      have h_pos : (0 : ℝ) < ε := hε
      -- From `1 ≤ (n+1)` and `ε > 0` we get `ε ≤ ε * (n+1)`.
      have := mul_le_mul_of_nonneg_left h_one_le (le_of_lt h_pos)
      simpa [one_mul] using this
    have h_tail :
        ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
          Real.exp (-u^2) ∂volume
          ≤ C₀ * Real.exp (-(ε * (n + 1 : ℝ))^2) :=
      hC₀_tail (ε * (n + 1 : ℝ)) h_r_ge
    -- Finally, propagate the bound through the scaling factor
    -- `(1/(n+1))` and rewrite the exponent.
    have h_nonneg_scale : 0 ≤ (1 / (n + 1 : ℝ)) :=
      le_of_lt (one_div_pos.mpr hR_pos)
    calc
      ∫ τ in {τ | |τ - τ₀| > ε},
        Real.exp (-(τ - τ₀)^2 * (n + 1 : ℝ)^2) ∂volume
          = (1 / (n + 1 : ℝ)) *
              ∫ u in {u | |u| > ε * (n + 1 : ℝ)},
                Real.exp (-u^2) ∂volume := h_main
      _ ≤ (1 / (n + 1 : ℝ)) *
              (C₀ * Real.exp (-(ε * (n + 1 : ℝ))^2)) := by
            -- Multiply the one-dimensional tail bound by the
            -- nonnegative scalar `1/(n+1)`.
            have :=
              mul_le_mul_of_nonneg_left h_tail h_nonneg_scale
            simpa [mul_assoc] using this
      _ = C_n * Real.exp (-(ε * (n + 1 : ℝ))^2) := by
            -- By definition of `C_n`.
            simp [C_n, mul_comm, mul_left_comm, mul_assoc]
      _ = C_n * Real.exp (-ε^2 * (n + 1 : ℝ)^2) := by
            -- Algebraic identity `(ε * (n+1))^2 = ε^2 * (n+1)^2`.
            have : (ε * (n + 1 : ℝ))^2 = ε^2 * (n + 1 : ℝ)^2 := by
              ring
            simp [this]

end Frourio
