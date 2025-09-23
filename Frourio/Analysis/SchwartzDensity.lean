import Frourio.Analysis.MellinBasic
import Frourio.Analysis.HilbertSpaceCore
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
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory Measure Real Complex SchwartzMap
open scoped ENNReal Topology ComplexConjugate

namespace Frourio

section SchwartzDensity

/-- Schwartz functions restricted to (0,∞) belong to Hσ for σ > 1/2 -/
lemma schwartz_mem_Hσ {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => if x > 0 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
  -- For σ > 1/2, the weight x^(2σ-2) ensures integrability near 0
  -- A Schwartz function has rapid decay, so the integral converges at infinity
  -- For σ ≤ 1/2, the integral diverges near 0 even for Schwartz functions
  sorry -- Detailed proof requires showing integrability with weight

/-- The embedding of Schwartz functions into Hσ for σ > 1/2 -/
noncomputable def schwartzToHσ {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) : Hσ σ :=
  MemLp.toLp (fun x => if x > 0 then f x else 0) (schwartz_mem_Hσ hσ f)

/-- The embedding is linear for σ > 1/2 -/
lemma schwartzToHσ_linear {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∀ (a : ℂ) (f g : SchwartzMap ℝ ℂ),
    schwartzToHσ hσ (a • f + g) = a • schwartzToHσ hσ f + schwartzToHσ hσ g := by
  sorry -- Prove linearity using properties of toLp

/-- The embedding is continuous with respect to appropriate Schwartz seminorms for σ > 1/2 -/
lemma schwartzToHσ_continuous {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ (k₁ k₂ : ℕ) (C : ℝ), 0 < C ∧
    ∀ f : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ f‖ ≤ C * SchwartzMap.seminorm ℝ k₁ k₂ f := by
  -- For σ > 1/2, the weight x^(2σ-2) is integrable near 0
  -- The seminorms k₁, k₂ need to control the behavior at infinity
  -- k₁ controls polynomial growth, k₂ controls smoothness
  sorry -- Prove continuity using appropriate Schwartz seminorms

/-- Schwartz functions are dense in Hσ for σ > 1/2 -/
theorem schwartz_dense_in_Hσ {σ : ℝ} (hσ : 1 / 2 < σ) :
    DenseRange (schwartzToHσ hσ) := by
  -- Strategy:
  -- 1. Start with an arbitrary f ∈ Hσ
  -- 2. Use simple function approximation (exists_simple_func_approximation in HilbertSpaceCore)
  -- 3. Approximate simple functions with smooth compactly supported functions
  -- 4. Smooth compactly supported functions can be approximated by Schwartz functions
  sorry -- Complete proof requires several technical steps

/-- For any f ∈ Hσ, schwartzToHσ hσ φ and the truncated φ agree a.e. for σ > 1/2 -/
lemma schwartzToHσ_ae_eq {σ : ℝ} (hσ : 1 / 2 < σ) (φ : SchwartzMap ℝ ℂ) :
    (schwartzToHσ hσ φ : ℝ → ℂ) =ᵐ[mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))]
      (fun x => if x > 0 then φ x else 0) := by
  -- This follows from the definition of MemLp.toLp
  sorry -- Use MemLp.coeFn_toLp

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
