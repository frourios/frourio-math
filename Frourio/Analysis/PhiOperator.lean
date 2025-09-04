import Frourio.Analysis.MellinTransform

namespace Frourio

/-!
Phi-operator (statement wrappers)

This module wraps Mellin-side statements for the Φ-difference operator into
assumption packs and exposes lightweight theorems for reuse from FG8.
-/

/-- Assumption pack for Φ-operator symbolization and norm bound along `H_σ`. -/
structure PhiOperatorAssumptions (Λ σ : ℝ) : Prop where
  (op_bound : op_norm_bound Λ σ)
  (symbolization : ∀ f : ℝ → ℂ, ∀ s : ℂ, phi_diff_symbolization Λ f s)

/-- Wrapper: obtain the operator-norm bound statement from the pack. -/
theorem phi_operator_norm_bound_of (Λ σ : ℝ)
  (A : PhiOperatorAssumptions Λ σ) : op_norm_bound Λ σ :=
  A.op_bound

/-- Wrapper: obtain the Mellin-side symbolization statement from the pack. -/
theorem phi_operator_symbolization_of (Λ σ : ℝ)
  (A : PhiOperatorAssumptions Λ σ) :
  ∀ f : ℝ → ℂ, ∀ s : ℂ, phi_diff_symbolization Λ f s :=
  A.symbolization

end Frourio

