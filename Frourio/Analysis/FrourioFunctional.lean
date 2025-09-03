import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace Frourio

/-!
FG8 A1: Functional layer (PLFA/EDE/EVI/JKO bridge skeleton)

This module introduces a lightweight functional container and constants
to connect the FG8 framework with the existing analysis layer. The goal
is to keep the API proof-light (no sorry/axiom) while exposing the key
quantities and inequalities used later: the base entropy `Ent`, the
Mellin-side term `Dsigmam`, a coupling parameter `gamma`, and the Doob
corrected parameter `lambdaBE = λ - 2 ε`. We also provide a parameterized
lower-bound predicate for the effective contraction rate.

References: design/13.md (FG8 §0–1)
-/

/-- Core functional container for FG8. -/
structure FrourioFunctional (X : Type*) [PseudoMetricSpace X] where
  (Ent : X → ℝ)
  (Dsigmam : X → ℝ)
  (gamma : ℝ)

/-- Combined functional `F(x) = Ent x + gamma * Dsigmam x`. -/
noncomputable def FrourioFunctional.F {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : X → ℝ :=
  fun x => A.Ent x + A.gamma * A.Dsigmam x

/-- Narrow-continuity surrogate (K1′, minimalist nontrivial form):
we require a uniform lower bound for `Dsigmam` (coercivity proxy).
This avoids a vacuous `True` while staying assumption-light. -/
def K1prime {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : Prop :=
  ∃ C : ℝ, ∀ x : X, A.Dsigmam x ≥ -C

/-- Geodesic-affinity surrogate (K4^m, minimalist nontrivial form):
we assume nonnegativity of the coupling parameter `gamma`.
This encodes that the extra term does not invert convexity trends. -/
def K4m {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : Prop := 0 ≤ A.gamma

/-- Doob-corrected parameter: `λ_BE = λ - 2 ε`. -/
def lambdaBE (lam eps : ℝ) : ℝ := lam - 2 * eps

/-- Budget constants entering the effective-rate bound. -/
structure ConstantBudget where
  (cStar : ℝ)
  (cD : ℝ)

/-- Lower bound predicate for the effective contraction rate `λ_eff`.
Parameters `Ssup` and `XiNorm` act as proxies for `‖S_m‖_∞` and `‖Ξ_m‖`.

  λ_eff ≥ (λ - 2 ε) - γ · (cStar · Ssup^2 + cD · XiNorm)
-/
def lambdaEffLowerBound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (lam eps lamEff Ssup XiNorm : ℝ) : Prop :=
  lamEff ≥ lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)

end Frourio
