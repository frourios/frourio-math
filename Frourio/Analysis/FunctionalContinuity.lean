import Frourio.Analysis.GammaConvergence
import Frourio.Zeta.Kernel
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Semicontinuous

namespace Frourio

open MeasureTheory Filter Topology

/-!
# Continuity of Energy Functionals

This file establishes the continuity properties of energy functionals
that appear in the RH criterion and Γ-convergence theory.
-/

-- Make this file work with any ZetaLineAPI instance, not just the default one
variable [ZetaLineAPI]

/-- If the norm is bounded by C, then the squared norm is bounded by C^2 -/
lemma norm_sq_le_of_norm_le {x : ℂ} {C : ℝ} (h : ‖x‖ ≤ C) : ‖x‖ ^ 2 ≤ C ^ 2 := by
  -- Since ‖x‖ ≤ C and norms are non-negative, we can square both sides
  -- We use sq_le_sq' which states: a^2 ≤ b^2 ↔ -b ≤ a ∧ a ≤ b
  apply sq_le_sq'
  · -- Show -C ≤ ‖x‖
    have h_norm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
    have h_C_nonneg : 0 ≤ C := le_trans h_norm_nonneg h
    linarith
  · -- Show ‖x‖ ≤ C
    exact h

/-- For any fixed radius, there exists a bound on the zeta function -/
lemma zeta_bounded_on_radius (R₀ : ℝ) : ∃ C₀ : ℝ,
    ∀ τ : ℝ, |τ| ≤ R₀ → ‖ZetaLineAPI.zeta_on_line τ‖ ≤ C₀ := by
  -- This follows directly from ZetaLineAPI.loc_bounded
  exact ZetaLineAPI.loc_bounded R₀

end Frourio
