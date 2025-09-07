import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Frourio.Analysis.KTransform
import Frourio.Analysis.DoobTransform
import Frourio.Analysis.PLFA.PLFA
import Frourio.Analysis.Slope

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

/-- Build a `FrourioFunctional` from an entropy `Ent`, a K-transform `K`,
and a parameter `gamma`, using the `DsigmamFromK` interface with a supplied
sup-norm proxy `Ssup`. -/
noncomputable def FrourioFunctional.ofK {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) : FrourioFunctional X :=
{ Ent := Ent, Dsigmam := DsigmamFromK K Ssup, gamma := gamma }

/-- Narrow-continuity surrogate (K1′, minimalist nontrivial form):
we require a uniform lower bound for `Dsigmam` (coercivity proxy). -/
def K1prime {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : Prop :=
  ∃ C : ℝ, ∀ x : X, A.Dsigmam x ≥ -C

/-- Geodesic-affinity surrogate (K4^m, minimalist nontrivial form):
we assume nonnegativity of the coupling parameter `gamma`.
This encodes that the extra term does not invert convexity trends. -/
def K4m {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : Prop := 0 ≤ A.gamma

/-- If the K-transform has a uniform lower bound at `s = 0` by `-C0` and the
scale `Ssup` is nonnegative, then the derived `Dσm(x) = Ssup · K.map x 0` is
bounded below by `-(Ssup · C0)`. Hence the `K1′` surrogate holds for the
functional built from `K`. -/
theorem k1prime_ofK_from_uniform_lower_bound {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup C0 : ℝ)
  (hS : 0 ≤ Ssup) (hLB : UniformLowerBoundAtZero K C0) :
  K1prime (FrourioFunctional.ofK Ent K gamma Ssup) :=
by
  refine ⟨Ssup * C0, ?_⟩
  intro x
  dsimp [FrourioFunctional.ofK, DsigmamFromK]
  have h' : -C0 ≤ K.map x 0 := by simpa using (hLB x)
  have hineq' : Ssup * (-C0) ≤ Ssup * K.map x 0 :=
    mul_le_mul_of_nonneg_left h' hS
  -- rewrite `Ssup * (-C0)` as `-(Ssup * C0)` and flip to a `≥`-shaped bound
  have : -(Ssup * C0) ≤ Ssup * K.map x 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_neg, neg_mul] using hineq'
  simpa [ge_iff_le] using this

/-- Numeric lower bound for `F = Ent + γ · Dσm` built from a `KTransform` with
uniform kernel lower bound at `s = 0`. If `γ ≥ 0` and `Ssup ≥ 0`, then

  F(x) ≥ Ent(x) - γ · (Ssup · C0).

This inequality is used as a coercivity proxy downstream. -/
theorem F_lower_bound_of_ofK {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup C0 : ℝ)
  (hγ : 0 ≤ gamma) (hS : 0 ≤ Ssup) (hLB : UniformLowerBoundAtZero K C0) :
  ∀ x : X,
    FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x
      ≥ Ent x - gamma * (Ssup * C0) :=
by
  intro x
  dsimp [FrourioFunctional.F, FrourioFunctional.ofK, DsigmamFromK]
  -- `Ent x + γ Ssup K.map x 0 ≥ Ent x + γ Ssup (-C0)`
  have hK : -C0 ≤ K.map x 0 := by simpa using (hLB x)
  have hmul : gamma * (Ssup * (-C0)) ≤ gamma * (Ssup * K.map x 0) := by
    have hS' : 0 ≤ Ssup := hS
    have hγS : 0 ≤ gamma * Ssup := mul_nonneg hγ hS'
    have hSmul : Ssup * (-C0) ≤ Ssup * K.map x 0 :=
      mul_le_mul_of_nonneg_left hK hS'
    exact mul_le_mul_of_nonneg_left hSmul hγ
  have : Ent x + gamma * (Ssup * K.map x 0)
            ≥ Ent x + gamma * (Ssup * (-C0)) := by
    exact add_le_add_left hmul (Ent x)
  -- Rewrite the RHS to the target shape.
  have : Ent x + gamma * (Ssup * K.map x 0)
            ≥ Ent x - gamma * (Ssup * C0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_neg, neg_mul, sub_eq_add_neg]
      using this
  exact this

/-- Convenience: if `Ent` and the kernel admit global lower bounds and `γ,Ssup ≥ 0`,
then the combined functional satisfies the (placeholder) coercivity predicate. -/
theorem ofK_coercive_from_bounds {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup CEnt : ℝ)
  (_hEntLB : ∀ x : X, Ent x ≥ -CEnt) :
  Coercive (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  -- Provide the per-point slack with `c = 0`.
  intro x; exact ⟨0, by norm_num, by simp⟩

/- Promote K-side predicates to a statement-level slope bound builder.
   (moved below after slope-based predicates are introduced).
   Given (K1′), (K4^m), and nonnegativity of the proxies, we produce the
   `StrongSlopeUpperBound_pred` for the functional built from `K`. The analytic
   content is deferred; this wraps the dependency shape used downstream. -/

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

/-- Theoremized form: wrap a provided inequality as the `lambdaEffLowerBound` fact. -/
theorem lambdaEffLowerBound_thm {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  {lam eps lamEff Ssup XiNorm : ℝ}
  (h : lamEff ≥ lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)) :
  lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm :=
  h

def MPointZeroOrderBound (Ssup XiNorm : ℝ) : Prop := 0 ≤ Ssup ∧ 0 ≤ XiNorm

def BudgetNonneg (budget : ConstantBudget) : Prop := 0 ≤ budget.cStar ∧ 0 ≤ budget.cD

-- Earlier scalar Doob-CD shift placeholders have been removed in favor of
-- DoobAssumptions-based variants below.

/-- Variant using the concrete Doob assumptions pack. This theorem connects
`DoobAssumptions` to the λ_eff lower bound generation in the same
placeholder spirit: analytic content is deferred to a provided inequality
`hChoice`, while the Doob assumptions are carried explicitly in the
signature to match the review action. -/
theorem lambdaEffLowerBound_from_doobAssumptions_mpoint {X : Type*}
  [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (h : X → ℝ) (D : Diffusion X) (_H : DoobAssumptions h D)
  (lam eps lamEff Ssup XiNorm : ℝ)
  (_hM : MPointZeroOrderBound Ssup XiNorm)
  (_hB : BudgetNonneg budget)
  (_hγ : 0 ≤ A.gamma)
  (hChoice : lamEff ≥
      lambdaBE lam eps
        - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)) :
  lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm :=
  lambdaEffLowerBound_thm A budget hChoice

/-- Constructive variant using `DoobAssumptions`: produce an explicit
`lamEff` witnessing the lower bound, given m-point zero-order bounds and
budget nonnegativity. The Doob CD-shift is tracked via `DoobAssumptions`
but not quantitatively used at this phase. -/
theorem lambdaEffLowerBound_construct_from_doobAssumptions_mpoint {X : Type*}
  [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (h : X → ℝ) (D : Diffusion X) (_H : DoobAssumptions h D)
  (lam eps Ssup XiNorm : ℝ)
  (_hM : MPointZeroOrderBound Ssup XiNorm)
  (_hB : BudgetNonneg budget)
  (_hγ : 0 ≤ A.gamma) :
  ∃ lamEff : ℝ, lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm :=
by
  -- Choose the canonical RHS value as `lamEff`.
  refine ⟨lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm), ?_⟩
  exact le_of_eq rfl

/-
Abstract slope interface, designed to be replaceable by the descending slope
in later phases (AGS). We keep a zero‑slope default to preserve current proofs,
and provide an explicit slope predicate parametrized by a slope specification.
-/

/-- A slope specification: assigns a numerical slope to a functional at a point. -/
structure SlopeSpec (X : Type*) [PseudoMetricSpace X] where
  (slope : (X → ℝ) → X → ℝ)

/-- Default (dummy) slope specification used at this phase: always 0. -/
noncomputable def zeroSlopeSpec (X : Type*) [PseudoMetricSpace X] : SlopeSpec X :=
  ⟨fun _ _ => 0⟩

/-- Implemented slope specification using the descending slope. -/
noncomputable def descendingSlopeSpec (X : Type*) [PseudoMetricSpace X] : SlopeSpec X :=
  ⟨fun F x => Frourio.descendingSlope F x⟩

/-- Legacy slope alias (kept for existing code); uses the zero slope. -/
noncomputable def slope {X : Type*} [PseudoMetricSpace X]
  (G : X → ℝ) (x : X) : ℝ := (zeroSlopeSpec X).slope G x

/-- Predicate for a strong upper bound on the slope of `F = Ent + γ·Dσm`:
  |∂F|(x) ≤ |∂Ent|(x) + γ · (cStar · Ssup^2 + cD · XiNorm)
Kept abstract via the `slope` helper. -/
def StrongSlopeUpperBound_pred {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ) : Prop :=
  ∀ x : X,
    slope (FrourioFunctional.F A) x
      ≤ slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)

/-- Parametric strong slope upper bound using an abstract slope specification. -/
def StrongSlopeUpperBound_with {X : Type*} [PseudoMetricSpace X]
  (S : SlopeSpec X) (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ) : Prop :=
  ∀ x : X,
    S.slope (FrourioFunctional.F A) x
      ≤ S.slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)

/-- Default strong slope upper bound using the implemented descending slope. -/
def StrongSlopeUpperBound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ) : Prop :=
  StrongSlopeUpperBound_with (descendingSlopeSpec X) A budget Ssup XiNorm

/-- The legacy predicate `StrongSlopeUpperBound_pred` is the `StrongSlopeUpperBound_with`
for the default zero slope. -/
theorem strongSlope_with_zero_equiv {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ) :
  StrongSlopeUpperBound_pred A budget Ssup XiNorm
    ↔ StrongSlopeUpperBound_with (zeroSlopeSpec X) A budget Ssup XiNorm :=
by
  constructor <;> intro H x
  · simpa [StrongSlopeUpperBound_with, slope, zeroSlopeSpec]
      using (H x)
  · simpa [StrongSlopeUpperBound_pred, slope, zeroSlopeSpec]
      using (H x)

/-- Theoremized strong slope upper bound (wrapper from the predicate). -/
theorem slope_strong_upper_bound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ)
  (H : StrongSlopeUpperBound_pred A budget Ssup XiNorm) :
  ∀ x : X,
    slope (FrourioFunctional.F A) x
      ≤ slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
  H

/-- Parametric version: theoremized strong slope upper bound using a slope spec. -/
theorem slope_strong_upper_bound_with {X : Type*} [PseudoMetricSpace X]
  (S : SlopeSpec X) (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ)
  (H : StrongSlopeUpperBound_with S A budget Ssup XiNorm) :
  ∀ x : X,
    S.slope (FrourioFunctional.F A) x
      ≤ S.slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
  H

/-- Wrapper: theoremized strong slope upper bound in the default (descending slope) route. -/
theorem slope_strong_upper_bound_default {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ)
  (H : StrongSlopeUpperBound A budget Ssup XiNorm) :
  ∀ x : X,
    (descendingSlopeSpec X).slope (FrourioFunctional.F A) x
      ≤ (descendingSlopeSpec X).slope A.Ent x
        + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
  H

/-- A trivial slope upper bound using the dummy slope = 0 and nonnegativity. -/
theorem slope_upper_bound_trivial {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ)
  (hB : BudgetNonneg budget) (hγ : 0 ≤ A.gamma) (hS : 0 ≤ Ssup) (hX : 0 ≤ XiNorm) :
  StrongSlopeUpperBound_pred A budget Ssup XiNorm :=
by
  intro x
  -- Left-hand side is 0 by the `slope` definition.
  simp [slope, zeroSlopeSpec]
  -- We need to show `0 ≤ slope Ent x + γ * (...)`, which follows from nonnegativity.
  have hS2 : 0 ≤ Ssup ^ (2 : ℕ) := by simpa using pow_nonneg hS (2 : ℕ)
  have hterm1 : 0 ≤ budget.cStar * Ssup ^ (2 : ℕ) :=
    mul_nonneg hB.1 hS2
  have hterm2 : 0 ≤ budget.cD * XiNorm := mul_nonneg hB.2 hX
  have hsum : 0 ≤ budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm :=
    add_nonneg hterm1 hterm2
  have hγsum : 0 ≤ A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
    mul_nonneg hγ hsum
  -- `slope A.Ent x = 0` by definition, so the target is exactly `0 ≤ γ * (...)`.
  simpa [slope, zeroSlopeSpec] using hγsum

end Frourio
