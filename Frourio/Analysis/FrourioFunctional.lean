import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Frourio.Analysis.KTransform
import Frourio.Analysis.DoobTransform
import Frourio.Analysis.PLFA

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

/-- Specialization of `k1prime_ofK_from_uniform_lower_bound` to the 1D basic
model, which satisfies the uniform lower bound for `C0 = 0`. -/
theorem k1prime_for_F_of_basic1D
  (Ent : ℝ → ℝ) (gamma Ssup : ℝ) (hS : 0 ≤ Ssup) :
  K1prime (FrourioFunctional.ofK Ent (KTransform.basic1D) gamma Ssup) :=
by
  have hLB := UniformLowerBoundAtZero_basic1D
  simpa using (k1prime_ofK_from_uniform_lower_bound Ent (KTransform.basic1D) gamma Ssup 0 hS hLB)

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

/-- Explicit lambda-eff lower bound using the explicit Doob CD shift.
Assume `D` has `CD(λ,∞)` and a Doob weight `h` satisfies the Hessian bound
`∇² log h ≤ ε g`. Then, for nonnegative proxies and coupling, we obtain the
budgeted inequality with the effective parameter chosen as `λ_eff = λ - 2ε`.

This theorem tracks the Doob assumptions and the Hessian bound in its
signature; the numerical inequality follows from nonnegativity. -/
theorem lambdaEffLowerBound_from_doob_explicit_mpoint {X : Type*}
  [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (h : X → ℝ) (D : Diffusion X) (H : DoobAssumptions h D)
  (lam eps Ssup XiNorm : ℝ)
  (Hhess : HessianLogBound h D eps) (hCD : HasCD D lam)
  (hM : MPointZeroOrderBound Ssup XiNorm)
  (hB : BudgetNonneg budget)
  (hγ : 0 ≤ A.gamma) :
  lambdaEffLowerBound A budget lam eps (lambdaBE lam eps) Ssup XiNorm :=
by
  -- Track the explicit Doob CD shift at the type level.
  have _ := cd_parameter_shift_explicit h D H eps Hhess (lam := lam) hCD
  -- Show `λ - 2ε ≥ (λ - 2ε) - γ * (c⋆ S^2 + cD Ξ)` from nonnegativity.
  -- First, the budgeted bracket is nonnegative.
  have hS2 : 0 ≤ Ssup ^ (2 : ℕ) := by simpa using pow_nonneg hM.1 (2 : ℕ)
  have hterm1 : 0 ≤ budget.cStar * Ssup ^ (2 : ℕ) := mul_nonneg hB.1 hS2
  have hterm2 : 0 ≤ budget.cD * XiNorm := mul_nonneg hB.2 hM.2
  have hsum : 0 ≤ budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm :=
    add_nonneg hterm1 hterm2
  have hγsum : 0 ≤ A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
    mul_nonneg hγ hsum
  -- Use `a - b ≤ a` for `b ≥ 0`, with `a = λ - 2ε` and `b = γ * (...)`.
  have hineq : lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)
                ≤ lambdaBE lam eps := by
    -- `a - b ≤ a` iff `a ≤ a + b`, which holds for `b ≥ 0`.
    have := hγsum
    exact (sub_le_iff_le_add').mpr (by
      have : 0 ≤ A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) := this
      -- `a ≤ a + b` for `b ≥ 0`.
      simpa using (le_add_of_nonneg_right this : lambdaBE lam eps ≤ lambdaBE lam eps
        + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)))
  -- Repackage as the target `λ_eff ≥ (λ - 2ε) - γ * (...)` with `λ_eff = λ - 2ε`.
  exact hineq

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

/-- Abstract (placeholder) slope of a functional at a point. In later phases this
will be replaced by a metric slope/descending slope. Kept numeric to state
strong upper bounds algebraically. -/
noncomputable def slope {X : Type*} [PseudoMetricSpace X]
  (_G : X → ℝ) (_x : X) : ℝ := 0

/-- Predicate for a strong upper bound on the slope of `F = Ent + γ·Dσm`:
  |∂F|(x) ≤ |∂Ent|(x) + γ · (cStar · Ssup^2 + cD · XiNorm)
Kept abstract via the `slope` helper. -/
def StrongSlopeUpperBound_pred {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ) : Prop :=
  ∀ x : X,
    slope (FrourioFunctional.F A) x
      ≤ slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)

/-- Theoremized strong slope upper bound (wrapper from the predicate). -/
theorem slope_strong_upper_bound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ)
  (H : StrongSlopeUpperBound_pred A budget Ssup XiNorm) :
  ∀ x : X,
    slope (FrourioFunctional.F A) x
      ≤ slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
  H

/-- Promote K-side predicates to a statement-level slope bound builder.
Given (K1′), (K4^m), and nonnegativity of the proxies, we produce the
`StrongSlopeUpperBound_pred` for the functional built from `K`. The analytic
content is deferred; this wraps the dependency shape used downstream. -/
def StrongSlopeFromK_flags {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma : ℝ)
  (budget : ConstantBudget) (Ssup XiNorm : ℝ) : Prop :=
  (K1primeK K ∧ K4mK K ∧ 0 ≤ Ssup ∧ 0 ≤ XiNorm ∧ 0 ≤ gamma) →
    StrongSlopeUpperBound_pred (FrourioFunctional.ofK Ent K gamma Ssup) budget Ssup XiNorm

/-- Wrapper theorem: apply a provided `StrongSlopeFromK_flags` builder to
obtain the strong slope upper bound predicate. -/
theorem slope_strong_upper_bound_from_K {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma : ℝ)
  (budget : ConstantBudget) (Ssup XiNorm : ℝ)
  (H : StrongSlopeFromK_flags Ent K gamma budget Ssup XiNorm)
  (_hK1 : K1primeK K) (_hK4 : K4mK K) (hS : 0 ≤ Ssup) (hX : 0 ≤ XiNorm) (hγ : 0 ≤ gamma) :
  StrongSlopeUpperBound_pred (FrourioFunctional.ofK Ent K gamma Ssup) budget Ssup XiNorm :=
by
  exact H ⟨_hK1, _hK4, hS, hX, hγ⟩

/-- A trivial slope upper bound using the dummy slope = 0 and nonnegativity. -/
theorem slope_upper_bound_trivial {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ)
  (hB : BudgetNonneg budget) (hγ : 0 ≤ A.gamma) (hS : 0 ≤ Ssup) (hX : 0 ≤ XiNorm) :
  StrongSlopeUpperBound_pred A budget Ssup XiNorm :=
by
  intro x
  -- Left-hand side is 0 by the `slope` definition.
  simp [slope]
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
  simpa [slope] using hγsum

/-- Concrete builder: from K-side flags and nonnegativity, produce a strong
upper bound on the slope of `F := Ent + γ·Dσm` using the trivial inequality. -/
theorem slope_strong_upper_bound_from_K_trivial {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma : ℝ)
  (budget : ConstantBudget) (Ssup XiNorm : ℝ)
  (_hK1 : K1primeK K) (_hK4 : K4mK K)
  (hS : 0 ≤ Ssup) (hX : 0 ≤ XiNorm) (hγ : 0 ≤ gamma)
  (hB : BudgetNonneg budget) :
  StrongSlopeUpperBound_pred (FrourioFunctional.ofK Ent K gamma Ssup) budget Ssup XiNorm :=
by
  -- Ignore `hK1`, `hK4` at this phase and use the trivial slope upper bound.
  exact slope_upper_bound_trivial (FrourioFunctional.ofK Ent K gamma Ssup)
    budget Ssup XiNorm hB (by simpa using hγ) hS hX

/-
Bridging to PLFA analytic flags for `F := Ent + γ·Dσm`.
We keep these lightweight: PLFA’s flags are Prop-valued placeholders,
so we expose builders that consume K-side assumptions and return the
corresponding flags for `F`.
-/

/-- Half-convexity flag for `F` from nonnegative coupling (placeholder). -/
theorem halfConvex_flag_for_F {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (lamEff : ℝ) (_hγ : 0 ≤ A.gamma) :
  HalfConvex (FrourioFunctional.F A) lamEff :=
by
  -- `HalfConvex` is a placeholder (`True`) at this phase.
  change True; exact trivial

/-- Strong-upper-bound flag for `F` from a strong slope upper bound predicate. -/
theorem strongUpperBound_flag_for_F {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ)
  (_H : StrongSlopeUpperBound_pred A budget Ssup XiNorm) :
  StrongUpperBound (FrourioFunctional.F A) :=
by
  -- `StrongUpperBound` is a placeholder (`True`) at this phase.
  change True; exact trivial

/-- Properness flag for `F` under the K1′ coercivity surrogate of `Dσm` (placeholder). -/
theorem proper_flag_for_F {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : Proper (FrourioFunctional.F A) := by
  change True; exact trivial

/-- Lower semicontinuity flag for `F` (placeholder builder). -/
theorem lsc_flag_for_F {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : LowerSemicontinuous (FrourioFunctional.F A) := by
  change True; exact trivial

/-- Coercivity flag for `F` from the K1′ surrogate (placeholder builder). -/
theorem coercive_flag_for_F {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : Coercive (FrourioFunctional.F A) := by
  change True; exact trivial

/-- JKO stability flag for `F` (placeholder builder). -/
theorem jkoStable_flag_for_F {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : JKOStable (FrourioFunctional.F A) := by
  change True; exact trivial

/-- Aggregate: build PLFA analytic flags for `F := Ent + γ·Dσm` from K-side inputs. -/
-- (moved above to avoid forward reference)

theorem analytic_flags_for_F_from_K {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma : ℝ)
  (budget : ConstantBudget) (Ssup XiNorm lamEff : ℝ)
  (_hK1 : K1primeK K) (_hK4 : K4mK K) (hS : 0 ≤ Ssup) (hX : 0 ≤ XiNorm) (hγ : 0 ≤ gamma)
  (hB : BudgetNonneg budget) :
  AnalyticFlags (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff :=
by
  -- Construct the functional and discharge all component flags via placeholders.
  let A := FrourioFunctional.ofK Ent K gamma Ssup
  refine ⟨?proper, ?lsc, ?coercive, ?hc, ?sub, ?jko⟩
  · exact proper_flag_for_F A
  · exact lsc_flag_for_F A
  · exact coercive_flag_for_F A
  · exact halfConvex_flag_for_F A lamEff (by simpa using hγ)
  · -- Strong upper bound via a trivial slope inequality using nonnegativity.
    exact strongUpperBound_flag_for_F A budget Ssup XiNorm
      (slope_upper_bound_trivial A budget Ssup XiNorm hB
        (by simpa using hγ) hS hX)
  · exact jkoStable_flag_for_F A

/-- Convenience: build analytic flags for `F` using the 1D basic K-transform
model and nonnegativity assumptions. -/
theorem analytic_flags_for_F_from_basic1D
  (Ent : ℝ → ℝ) (gamma : ℝ)
  (budget : ConstantBudget) (Ssup XiNorm lamEff : ℝ)
  (hS : 0 ≤ Ssup) (hX : 0 ≤ XiNorm) (hγ : 0 ≤ gamma)
  (hB : BudgetNonneg budget) :
  AnalyticFlags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent (KTransform.basic1D) gamma Ssup))
    lamEff :=
by
  refine analytic_flags_for_F_from_K Ent (KTransform.basic1D) gamma budget Ssup XiNorm lamEff
    (K1prime_basic1D) (K4mK_basic1D) hS hX hγ hB

end Frourio
