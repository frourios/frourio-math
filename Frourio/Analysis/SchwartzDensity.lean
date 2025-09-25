import Frourio.Analysis.MellinBasic
import Frourio.Analysis.HilbertSpaceCore
import Frourio.Analysis.SchwartzDensityCore
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Measure Real Complex SchwartzMap intervalIntegral
open scoped ENNReal Topology ComplexConjugate

namespace Frourio

section SchwartzDensity

/-- Bound for the eLpNorm of a Schwartz function on the unit interval (0,1] -/
lemma eLpNorm_bound_on_unit_interval {σ : ℝ} (hσ : 1 / 2 < σ)
    (f : SchwartzMap ℝ ℂ) (M : ℝ)
    (hM_bound : (∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar) ^
    (1 / 2 : ℝ) ≤ ENNReal.ofReal M) :
    eLpNorm (fun x => if x ∈ Set.Ioc 0 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
    ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 f * M) := by
  -- Near 0: use boundedness from the fact that Schwartz functions are bounded
  -- and the weight is integrable on (0,1]
  sorry -- Use boundedness and weight integrability

/-- Splitting the eLpNorm of a function on (0,∞) into (0,1] and (1,∞) parts -/
lemma eLpNorm_split_at_one {σ : ℝ} (f : SchwartzMap ℝ ℂ) :
    eLpNorm (fun x => if x > 0 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
    eLpNorm (fun x => if x ∈ Set.Ioc 0 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) +
    eLpNorm (fun x => if x ∈ Set.Ioi 1 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
  -- This follows from the triangle inequality for eLpNorm
  -- since (0,∞) = (0,1] ∪ (1,∞)
  sorry -- Triangle inequality for eLpNorm

/-- The weight function has finite L² norm for σ > 1/2 -/
lemma weight_function_L2_bound {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ M : ℝ, 0 < M ∧
    (∫⁻ x, ENNReal.ofReal (x ^ (2 * σ - 1)) ∂mulHaar) ^ (1/2 : ℝ) ≤ ENNReal.ofReal M := by
  -- The L^2 norm of the weight function is finite for σ > 1/2
  -- This follows from the integrability of x^(2σ-1) on (0,∞) when 2σ - 1 > -1
  sorry -- Technical bound on weight function

/-- The embedding is continuous with respect to appropriate Schwartz seminorms for σ > 1/2 -/
lemma schwartzToHσ_continuous {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ (k₁ k₂ : ℕ) (C : ℝ), 0 < C ∧
    ∀ f : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ f‖ ≤ C * SchwartzMap.seminorm ℝ k₁ k₂ f := by
  -- For σ > 1/2, the weight x^(2σ-2) is integrable near 0
  -- The seminorms k₁, k₂ need to control the behavior at infinity
  -- k₁ controls polynomial growth, k₂ controls smoothness

  -- Choose seminorm parameters: k₁ for polynomial decay, k₂ = 0 for just function values
  let k₁ : ℕ := ⌊4 * σ + 2⌋₊  -- Ensure enough decay at infinity
  let k₂ : ℕ := 0              -- Only need function values, not derivatives

  -- Define the constant C based on the weight integral bounds
  obtain ⟨M, hM_pos, hM_bound⟩ := weight_function_L2_bound hσ
  use k₁, k₂, M + 1
  constructor
  · linarith [hM_pos]
  · intro f
    -- Estimate the Hilbert space norm
    rw [schwartzToHσ]
    -- Use the fact that ‖MemLp.toLp f hf‖ = ENNReal.toReal (eLpNorm f p μ)
    rw [norm_toLp_eq_toReal_eLpNorm hσ f]

    -- Show that ENNReal.toReal of a bound gives the desired inequality
    suffices h_eLp : eLpNorm (fun x => if x > 0 then f x else 0) 2
        (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
        ENNReal.ofReal ((M + 1) * SchwartzMap.seminorm ℝ k₁ k₂ f) by
      have h_nonneg : 0 ≤ (M + 1) * SchwartzMap.seminorm ℝ k₁ k₂ f := by
        apply mul_nonneg
        · linarith [hM_pos]
        · exact apply_nonneg (SchwartzMap.seminorm ℝ k₁ k₂) f
      exact ENNReal.toReal_le_of_le_ofReal h_nonneg h_eLp

    -- The L^2 norm with weight can be bounded by Schwartz seminorms
    -- Split the integral into (0,1] and (1,∞)
    have h_split := @eLpNorm_split_at_one σ f

    -- Bound each part using Schwartz properties
    have h_bound1 := eLpNorm_bound_on_unit_interval hσ f M hM_bound

    have h_k₁_large : σ + 1 / 2 ≤ (k₁ : ℝ) := by
      have h_aux : (4 * σ + 2 : ℝ) < (k₁ : ℝ) + 1 := by
        simpa [k₁, add_comm, add_left_comm, add_assoc] using
          (Nat.lt_floor_add_one (4 * σ + 2))
      have h_floor : (4 * σ + 1 : ℝ) < (k₁ : ℝ) := by
        have := h_aux
        linarith
      have hσ_bound : σ + 1 / 2 ≤ 4 * σ + 1 := by
        linarith [hσ]
      exact (le_of_lt (lt_of_le_of_lt hσ_bound h_floor))
    have h_bound2 := eLpNorm_bound_on_tail (σ := σ) (k₁ := k₁) h_k₁_large f

    -- Combine bounds
    have h_seminorm_mono : SchwartzMap.seminorm ℝ 0 0 f ≤ SchwartzMap.seminorm ℝ k₁ k₂ f := by
        -- Seminorms are monotonic in their indices
        sorry

    -- Complete the bound combination
    -- Use triangle inequality and the bounds we've established
    -- Combine the bounds using the splitting and individual estimates
    have h_final : eLpNorm (fun x => if x > 0 then f x else 0) 2
          (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) ≤
        ENNReal.ofReal ((M + 1) * SchwartzMap.seminorm ℝ k₁ k₂ f) := by
      -- Apply splitting inequality then individual bounds
      have step1 := le_trans h_split (add_le_add h_bound1 h_bound2)
      -- Use seminorm monotonicity to get the final bound
      sorry -- Complete the seminorm bound combination
    exact h_final

/-- Schwartz functions are dense in Hσ for σ > 1/2 -/
theorem schwartz_dense_in_Hσ {σ : ℝ} (hσ : 1 / 2 < σ) :
    DenseRange (schwartzToHσ hσ) := by
  -- Use the characterization: a subspace is dense iff its closure equals the whole space
  rw [denseRange_iff_closure_range]
  -- Show that closure of range equals the whole space
  rw [Set.eq_univ_iff_forall]
  intro f
  -- For any f ∈ Hσ, we can approximate it arbitrarily well by Schwartz functions
  -- Use the characterization: f ∈ closure S ↔ ∀ ε > 0, ∃ s ∈ S, dist f s < ε
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Need to find a Schwartz function φ such that dist f (schwartzToHσ hσ φ) < ε
  -- Strategy: First approximate f by a compactly supported smooth function,
  -- then extend it to a Schwartz function

  -- Step 1: Use the density of compactly supported smooth functions in L²
  -- For this, we use the fact that C_c^∞ functions are dense in L² spaces
  have h_smooth_dense : ∃ (g : ℝ → ℂ)
      (hg_mem : MemLp g 2 (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))),
      HasCompactSupport g ∧ ContDiff ℝ ⊤ g ∧ dist f (hg_mem.toLp g) < ε / 2 := by
    -- Use the density of smooth compactly supported functions in weighted L² spaces
    -- First, we note that for σ > 1/2, the weight function x^(2σ-1) is locally integrable
    have h_weight_integrable : LocallyIntegrableOn
        (fun x : ℝ => x ^ (2 * σ - 1 : ℝ)) (Set.Ioi 0) mulHaar := by
      -- For now, use sorry for the locally integrable property
      -- This can be proven using the fact that x^(2σ-1) is continuous on (0,∞) and σ > 1/2
      sorry

    -- Use the standard density result for weighted L² spaces
    -- This follows from mollification and truncation arguments
    sorry -- Apply density theorem for weighted L² spaces

  obtain ⟨g, hg_mem, hg_compact, hg_smooth, hg_close⟩ := h_smooth_dense

  -- Step 2: Extend g to a Schwartz function
  -- Since g has compact support and is smooth, it's already a Schwartz function
  -- We just need to construct the SchwartzMap structure

  -- First verify that smooth compactly supported functions are Schwartz
  have hg_schwartz : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    intro k n
    -- Since g has compact support, say in [-R, R], and is smooth
    -- The bound is simply 0 outside [-R, R] and finite inside
    sorry -- Bound using compact support

  -- Construct the Schwartz function from g
  -- Note: SchwartzMap requires ContDiff ℝ (↑⊤) but we have ContDiff ℝ ⊤
  -- These are the same, but we need to handle the type difference
  let φ : SchwartzMap ℝ ℂ := {
    toFun := g
    smooth' := by
      -- Use the fact that ContDiff ℝ ⊤ g implies smoothness
      sorry -- Type conversion for smoothness
    decay' := hg_schwartz
  }

  -- Step 3: Show that schwartzToHσ hσ φ approximates f
  -- We need to show ∃ y ∈ Set.range (schwartzToHσ hσ), dist f y < ε
  use schwartzToHσ hσ φ
  refine ⟨?_, ?_⟩
  · -- Show that schwartzToHσ hσ φ is in the range
    use φ
  · -- Show the distance bound
    sorry -- Show dist f (schwartzToHσ hσ φ) < ε using hg_close

/-- For any f ∈ Hσ and ε > 0, there exists a Schwartz function approximating f for σ > 1/2 -/
lemma exists_schwartz_approximation {σ : ℝ} (hσ : 1 / 2 < σ) (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ φ - f‖ < ε := by
  have h_dense := schwartz_dense_in_Hσ hσ
  rw [DenseRange] at h_dense
  have hf_in_closure := h_dense.closure_eq ▸ Set.mem_univ f
  rw [Metric.mem_closure_iff] at hf_in_closure
  obtain ⟨g, hg_range, hg_close⟩ := hf_in_closure ε hε
  obtain ⟨φ, rfl⟩ := hg_range
  use φ
  rw [dist_eq_norm] at hg_close
  rw [←norm_sub_rev]
  exact hg_close

/-- Schwartz approximation with a.e. convergence for σ > 1/2 -/
lemma schwartz_ae_dense {σ : ℝ} (hσ : 1 / 2 < σ) (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ φ - f‖ < ε ∧
    (schwartzToHσ hσ φ : ℝ → ℂ) =ᵐ[mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))]
      (fun x => if x > 0 then φ x else 0) := by
  obtain ⟨φ, hφ⟩ := exists_schwartz_approximation hσ f ε hε
  use φ
  constructor
  · exact hφ
  · exact schwartzToHσ_ae_eq hσ φ

end SchwartzDensity

end Frourio
