import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Frourio.Geometry.FGCore
import Frourio.Analysis.EVI
import Frourio.Analysis.FrourioFunctional
import Frourio.Analysis.PLFA
import Frourio.Analysis.DoobTransform

/-!
# Gradient-Flow Framework: statements and data glue

This module bundles FG core data with the functional layer and exposes
statement-level predicates for the FG8 equivalences and bounds:
PLFA = EDE = EVI = JKO, effective lambda lower bounds, two-EVI with force,
tensorization (min rule placeholder), and a multi-scale effective lambda.

The goal here is to fix API shapes that connect existing components;
heavy analytic proofs will be added in later phases.
-/

namespace Frourio

open scoped BigOperators

section X
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- FG8 data pack: core FG data, a functional with coupling, external
budget constants and parameters controlling Doob degradation and symbol sizes. -/
structure GradientFlowSystem (X : Type*) [PseudoMetricSpace X] [MeasurableSpace X] where
  (base : FGData X)
  (func : FrourioFunctional X)
  (Ssup : ℝ)      -- proxy for ‖S_m‖_∞
  (XiNorm : ℝ)    -- proxy for ‖Ξ_m‖
  (budget : ConstantBudget)
  (eps : ℝ)       -- Doob degradation ε

/-- Equivalence packaging (PLFA = EDE = EVI = JKO) at statement level using
the functional `F = Ent + γ·Dσm` and effective parameter `λ_BE = λ - 2ε`. -/
def gradient_flow_equiv (S : GradientFlowSystem X) : Prop :=
  plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)

/-- Equivalence theorem (wrapper): if the packaged equivalence holds for
`F := Ent + γ·Dσm` and `λ_BE := λ - 2ε`, then the gradient-flow equivalence holds. -/
theorem gradient_flow_equiv_of_pack (S : GradientFlowSystem X)
  (G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  gradient_flow_equiv S :=
  G

/-- Effective lambda lower bound statement: there exists `λ_eff` satisfying the
budgeted inequality with Doob-corrected parameter. -/
def lambda_eff_lower_bound (S : GradientFlowSystem X) : Prop :=
  ∃ lamEff : ℝ, lambdaEffLowerBound S.func S.budget S.base.lam S.eps lamEff S.Ssup S.XiNorm

/-- Lower bound theorem (wrapper): a provided inequality instantiates the
`lambda_eff_lower_bound` statement. -/
theorem lambda_eff_lower_bound_of (S : GradientFlowSystem X)
  {lamEff : ℝ}
  (h : lambdaEffLowerBound S.func S.budget S.base.lam S.eps lamEff S.Ssup S.XiNorm) :
  lambda_eff_lower_bound S :=
by
  exact ⟨lamEff, h⟩

/-- Effective lambda lower bound derived from Doob assumptions and m-point
zero-order bounds. Uses the constructive inequality from the analysis layer. -/
theorem lambda_eff_lower_bound_from_doob
  (S : GradientFlowSystem X)
  (h : X → ℝ) (D : Diffusion X) (H : DoobAssumptions h D)
  (hM : MPointZeroOrderBound S.Ssup S.XiNorm)
  (hB : BudgetNonneg S.budget)
  (hγ : 0 ≤ S.func.gamma) :
  lambda_eff_lower_bound S :=
by
  -- Instantiate the constructive analysis-layer theorem and package the witness.
  rcases lambdaEffLowerBound_construct_from_doobAssumptions_mpoint S.func S.budget h D H
      S.base.lam S.eps S.Ssup S.XiNorm hM hB hγ with ⟨lamEff, hLE⟩
  exact ⟨lamEff, hLE⟩

/-- Two-EVI with external forcing: packaged via the analysis-layer predicate. -/
def two_evi_with_force (S : GradientFlowSystem X) : Prop :=
  ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v

/-- two-EVI with force theorem (wrapper): pass through an analysis-layer result. -/
theorem two_evi_with_force_of (S : GradientFlowSystem X)
  (H : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  two_evi_with_force S :=
  H

end X

section Xsuite
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- Integrated gradient-flow suite: bundles the equivalence package,
the lambda_eff lower bound, and the two-EVI with force into a single statement. -/
theorem gradient_flow_suite
  (S : GradientFlowSystem X)
  (G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (lamEff : ℝ)
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps lamEff S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S := by
  refine And.intro (gradient_flow_equiv_of_pack S G) ?hrest
  refine And.intro
    (lambda_eff_lower_bound_of S (lamEff := lamEff) hLam)
    (two_evi_with_force_of S Htwo)

end Xsuite

/-- Minimal tensorization predicate (placeholder with nontrivial content):
requires coercivity surrogates and nonnegative coupling for both factors. -/
def tensorization_min_rule {X Y : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y]
  (S₁ : GradientFlowSystem X) (S₂ : GradientFlowSystem Y) : Prop :=
  K1prime S₁.func ∧ K1prime S₂.func ∧ 0 ≤ S₁.func.gamma ∧ 0 ≤ S₂.func.gamma

/-- Multi-scale effective lambda helper: product of single-scale factors over
`j : Fin m`. -/
noncomputable def effective_lambda_multiscale {m : ℕ}
  (α κ Λ : Fin m → ℝ) (k : Fin m → ℤ) (lam : ℝ) : ℝ :=
  lam * ∏ j : Fin m,
    Real.exp (((κ j - 2 * α j) * (k j : ℝ)) * Real.log (Λ j))

/-- Alias used in the design notes. -/
noncomputable abbrev effectiveLambdaVec {m : ℕ}
  (α κ Λ : Fin m → ℝ) (k : Fin m → ℤ) (lam : ℝ) : ℝ :=
  effective_lambda_multiscale α κ Λ k lam

/-- Multi-scale rule statement: for any base parameter `λ`, there exists an
effective parameter obtained by the product formula. -/
def multiscale_lambda_rule {m : ℕ} (Λ α κ : Fin m → ℝ) (k : Fin m → ℤ) : Prop :=
  ∀ lam : ℝ, ∃ lamEff : ℝ, lamEff = effective_lambda_multiscale α κ Λ k lam

/-- Trivial constructor for the multiscale effective-λ rule: choose the
right-hand side as the witness. -/
theorem multiscale_lambda_rule_thm {m : ℕ}
  (Λ α κ : Fin m → ℝ) (k : Fin m → ℤ) :
  multiscale_lambda_rule Λ α κ k :=
by
  intro lam; exact ⟨effective_lambda_multiscale α κ Λ k lam, rfl⟩

end Frourio
