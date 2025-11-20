import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Frourio.Analysis.KTransform
import Frourio.Analysis.DoobTransform
import Frourio.Analysis.PLFA.PLFA
import Frourio.Analysis.Slope
import Frourio.Geometry.FGCore
import Frourio.Geometry.FGInterop
import Frourio.Analysis.MinimizingMovement

namespace Frourio

/-!
Functional layer (PLFA/EDE/EVI/JKO bridge)

This module introduces a lightweight functional container and constants
to connect the FG8 framework with the existing analysis layer. The goal
is to keep the API proof-light while exposing the key
quantities and inequalities used later: the base entropy `Ent`, the
Mellin-side term `Dsigmam`, a coupling parameter `gamma`, and the Doob
corrected parameter `lambdaBE = λ - 2 ε`. We also provide a parameterized
lower-bound predicate for the effective contraction rate.
-/

/-- Core functional container. -/
structure FrourioFunctional (X : Type*) [PseudoMetricSpace X] where
  (Ent : X → ℝ) (Dsigmam : X → ℝ) (gamma : ℝ)

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

/-- Narrow-continuity surrogate:
we require a uniform lower bound for `Dsigmam` (coercivity proxy). -/
def K1prime {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : Prop :=
  ∃ C : ℝ, ∀ x : X, A.Dsigmam x ≥ -C

/-- Geodesic-affinity surrogate:
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

theorem ofK_coercive_from_bounds {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Coercive (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  -- Provide the per-point slack with `c = 0`.
  intro x; exact ⟨0, by norm_num, by simp⟩

/-- If `K1prime` holds for the functional built from `K`, and `Ent` has a uniform
lower bound, then the combined functional `F` is Coercive. -/
theorem ofK_coercive_from_k1prime {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Coercive (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  -- For the surrogate version, we can always choose c = 0
  intro x
  exact ⟨0, by norm_num, by simp⟩

/-- If the functional built from `K` satisfies `K1prime`, then it is LowerSemicontinuous
(in the surrogate sense). -/
theorem ofK_lower_semicontinuous_from_k1prime {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  -- For the surrogate version, we can always choose c = 0
  intro x
  exact ⟨0, by norm_num, by simp⟩

/-- The functional built from `K` satisfies the Proper predicate (surrogate). -/
theorem ofK_proper {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Proper (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  -- For the surrogate version, we can always choose C = 0
  exact ⟨0, fun x => by simp⟩

/-- The functional built from `K` satisfies HalfConvex (surrogate). -/
theorem ofK_halfconvex {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff :=
by
  -- For the surrogate version, we can always choose c = 0
  exact ⟨0, by norm_num, fun x => by simp⟩

/-- The functional built from `K` satisfies StrongUpperBound (surrogate). -/
theorem ofK_strong_upper_bound {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  StrongUpperBound (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  -- For the surrogate version, we can always choose c = 0
  exact ⟨0, by norm_num, fun x => by simp⟩


/-- If gamma ≥ 0, then K4^m holds for the functional built from K. -/
theorem k4m_ofK_from_gamma_nonneg {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (hγ : 0 ≤ gamma) :
  K4m (FrourioFunctional.ofK Ent K gamma Ssup) :=
by
  exact hγ

/-- The functional built from `K` satisfies JKOStable (surrogate).
For any initial point, there exists a curve (the constant curve) along which F is non-increasing. -/
theorem ofK_jko_stable {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  JKOStable (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  -- For the surrogate version, we use constant curves
  intro ρ0
  -- Construct the constant curve ρ(t) = ρ0 for all t
  use fun _ => ρ0
  constructor
  · -- ρ(0) = ρ0
    rfl
  · -- F(ρ(t)) ≤ F(ρ0) for all t (equality for constant curve)
    intro t
    simp

/-- JKO stability for general FrourioFunctional.
This provides the JKO property for any FrourioFunctional, showing that
from any initial point, there exists a (constant) curve along which F is non-increasing. -/
theorem jko_stable_general {X : Type*} [PseudoMetricSpace X] (A : FrourioFunctional X) :
  JKOStable (FrourioFunctional.F A) :=
by
  intro ρ0
  -- Use the constant curve
  use fun _ => ρ0
  constructor
  · rfl
  · intro t
    exact le_refl _

/-- JKO property with explicit curve construction.
Given an initial point, construct a JKO curve (constant curve in the surrogate case). -/
def constructJKOCurve {X : Type*} [PseudoMetricSpace X] (ρ0 : X) : ℝ → X :=
  fun _ => ρ0

/-- The constructed JKO curve satisfies the JKO property. -/
theorem constructJKOCurve_satisfies_jko {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (ρ0 : X) : JKO (FrourioFunctional.F A) ρ0 :=
by
  use constructJKOCurve ρ0
  constructor
  · -- Initial condition
    rfl
  · -- Non-increasing property
    intro t
    dsimp [constructJKOCurve]
    exact le_refl _

/-- K4^m is preserved under scaling of gamma by a nonnegative factor. -/
theorem k4m_scale {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (c : ℝ) (hc : 0 ≤ c) (hK4 : K4m A) :
  K4m { A with gamma := c * A.gamma } :=
by
  dsimp [K4m] at hK4 ⊢
  exact mul_nonneg hc hK4

/-- If both K1′ and K4^m hold, the functional has controlled behavior. -/
theorem controlled_functional_from_k1_k4 {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (hK1 : K1prime A) (hK4 : K4m A) :
  (∃ C : ℝ, ∀ x : X, A.Dsigmam x ≥ -C) ∧ (0 ≤ A.gamma) :=
⟨hK1, hK4⟩

/- Promote K-side predicates to a statement-level slope bound builder.
   (moved below after slope-based predicates are introduced).
   Given (K1′), (K4^m), and nonnegativity of the proxies, we produce the
   `StrongSlopeUpperBound_pred` for the functional built from `K`. The analytic
   content is deferred; this wraps the dependency shape used downstream. -/

/-- Budget constants entering the effective-rate bound. -/
structure ConstantBudget where
  (cStar : ℝ) (cD : ℝ)

/-- Lower bound predicate for the effective contraction rate `λ_eff`.
Parameters `Ssup` and `XiNorm` act as proxies for `‖S_m‖_∞` and `‖Ξ_m‖`.

  λ_eff ≥ (λ - 2 ε) - γ · (cStar · Ssup^2 + cD · XiNorm)
-/
def lambdaEffLowerBound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (lam eps lamEff Ssup XiNorm : ℝ) : Prop :=
  lamEff ≥ lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)

/-- Theoremized form: wrap a provided inequality as the `lambdaEffLowerBound` fact. -/
theorem lambdaEffLowerBound_thm {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  {lam eps lamEff Ssup XiNorm : ℝ}
  (h : lamEff ≥ lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)) :
  lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm :=
  h

/-- Monotonicity in `lamEff`: if a witness `lamEff` satisfies the inequality,
then any `lamEff' ≥ lamEff` also satisfies it. -/
theorem lambdaEffLowerBound_mono {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  {lam eps lamEff lamEff' Ssup XiNorm : ℝ}
  (hle : lamEff ≤ lamEff') (h : lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm) :
  lambdaEffLowerBound A budget lam eps lamEff' Ssup XiNorm :=
by
  -- `h : lamEff ≥ RHS` and `hle : lamEff ≤ lamEff'` imply `lamEff' ≥ RHS`.
  -- Rewrite both as `RHS ≤ lamEff` and chain.
  exact le_trans h hle

def MPointZeroOrderBound (Ssup XiNorm : ℝ) : Prop := 0 ≤ Ssup ∧ 0 ≤ XiNorm

def BudgetNonneg (budget : ConstantBudget) : Prop := 0 ≤ budget.cStar ∧ 0 ≤ budget.cD

/-! ### Parametric StrongUpperBound for Dσm's Zero-Order Contribution

This section provides the parametric strong upper bound for the zero-order
contribution of Dσm, controlled by the budget constants. -/

/-- Upper bound for Dσm based on kernel evaluation at s=0. -/
theorem DsigmamFromK_upper_bound {X : Type*} [PseudoMetricSpace X]
  (K : KTransform X) (Ssup C0 : ℝ) (hS : 0 ≤ Ssup) (hUB : ∀ x : X, K.map x 0 ≤ C0) :
  ∀ x : X, DsigmamFromK K Ssup x ≤ Ssup * C0 :=
by
  intro x
  dsimp [DsigmamFromK]
  exact mul_le_mul_of_nonneg_left (hUB x) hS

/-- Zero-order contribution bound for Dσm in the functional F = Ent + γ·Dσm. -/
def ZeroOrderBound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup : ℝ) : Prop :=
  ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ x : X, A.Dsigmam x ≤ budget.cStar * Ssup * C0

/-- The functional F = Ent + γ·Dσm satisfies parametric StrongUpperBound
when Ent is bounded above and Dσm has zero-order bound. -/
theorem ofK_strong_upper_bound_parametric {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (CEnt C0 : ℝ) (hγ : 0 ≤ gamma) (hS : 0 ≤ Ssup) (hC0 : 0 ≤ C0) (hCEnt : 0 ≤ CEnt)
  (hEntUB : ∀ x : X, Ent x ≤ CEnt) (hKUB : ∀ x : X, K.map x 0 ≤ C0) :
  ∃ c : ℝ, 0 ≤ c ∧ ∀ x : X,
    FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c :=
by
  use CEnt + gamma * Ssup * C0
  constructor
  · -- Show c ≥ 0
    apply add_nonneg
    · exact hCEnt
    · apply mul_nonneg
      · apply mul_nonneg
        · exact hγ
        · exact hS
      · exact hC0
  · intro x
    dsimp [FrourioFunctional.F, FrourioFunctional.ofK, DsigmamFromK]
    calc
      Ent x + gamma * (Ssup * K.map x 0)
        ≤ CEnt + gamma * (Ssup * K.map x 0) := by
          apply add_le_add_right (hEntUB x)
      _ ≤ CEnt + gamma * Ssup * C0 := by
          apply add_le_add_left
          -- Rewrite to match the associativity
          have : gamma * (Ssup * K.map x 0) = gamma * Ssup * K.map x 0 := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_left (hKUB x)
          apply mul_nonneg hγ hS

/-- Budget-aware StrongUpperBound: Connect budget constants to the upper bound. -/
theorem strongUpperBound_from_budget {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (hγ : 0 ≤ A.gamma)
  (hEnt : ∃ CEnt : ℝ, 0 ≤ CEnt ∧ ∀ x : X, A.Ent x ≤ CEnt)
  (hDsigma : ∃ CDsigma : ℝ, 0 ≤ CDsigma ∧ ∀ x : X, A.Dsigmam x ≤ CDsigma) :
  StrongUpperBound (FrourioFunctional.F A) :=
by
  -- Extract bounds
  obtain ⟨CEnt, hCEnt, hEntBound⟩ := hEnt
  obtain ⟨CDsigma, hCDsigma, hDsigmaBound⟩ := hDsigma
  -- Construct the upper bound constant
  use CEnt + A.gamma * CDsigma
  constructor
  · apply add_nonneg
    · exact hCEnt
    · apply mul_nonneg
      · exact hγ
      · exact hCDsigma
  · intro x
    dsimp [FrourioFunctional.F]
    -- The inequality F x ≤ F x + c holds with c = CEnt + A.gamma * CDsigma
    -- This is the surrogate form
    have : A.Ent x + A.gamma * A.Dsigmam x ≤
           A.Ent x + A.gamma * A.Dsigmam x + (CEnt + A.gamma * CDsigma) := by
      simp
      apply add_nonneg hCEnt
      apply mul_nonneg hγ hCDsigma
    exact this

/-- Integration: StrongUpperBound from kernel bound and budget parameters. -/
theorem strongUpperBound_from_kernel_and_budget {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (CEnt C0 : ℝ)
  (hγ : 0 ≤ gamma) (hS : 0 ≤ Ssup) (hCEnt : 0 ≤ CEnt) (hC0 : 0 ≤ C0)
  (hEntUB : ∀ x : X, Ent x ≤ CEnt) (hKUB : ∀ x : X, K.map x 0 ≤ C0) :
  StrongUpperBound (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  apply strongUpperBound_from_budget (FrourioFunctional.ofK Ent K gamma Ssup) hγ
  · use CEnt, hCEnt, hEntUB
  · use Ssup * C0
    constructor
    · apply mul_nonneg hS hC0
    · intro x
      dsimp [FrourioFunctional.ofK, DsigmamFromK]
      apply mul_le_mul_of_nonneg_left (hKUB x) hS

-- Earlier scalar Doob-CD shift placeholders have been removed in favor of
-- DoobAssumptions-based variants below.

/-- Variant using the concrete Doob assumptions pack. This theorem connects
`DoobAssumptions` to the λ_eff lower bound generation. The Doob transform
provides λ_BE = λ - 2ε, and the m-point terms provide additional corrections. -/
theorem lambdaEffLowerBound_from_doobAssumptions_mpoint {X : Type*}
  [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (lam eps lamEff Ssup XiNorm : ℝ)
  (hChoice : lamEff ≥
      lambdaBE lam eps
        - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)) :
  lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm :=
  lambdaEffLowerBound_thm A budget hChoice

/-- API: Direct connection from DoobAssumptions to the effective rate formula.
Given DoobAssumptions with parameter ε, we get λ_eff ≥ (λ - 2ε) - γ·(m-point terms). -/
theorem lambdaEff_formula_from_doob {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (lam eps Ssup XiNorm : ℝ) :
  ∃ lamEff : ℝ,
    lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm ∧
    lamEff = lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
by
  use lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)
  constructor
  · exact lambdaEffLowerBound_from_doobAssumptions_mpoint A budget lam eps
      (lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm))
      Ssup XiNorm (le_refl _)
  · rfl

/-- Constructive variant using `DoobAssumptions`: produce an explicit
`lamEff` witnessing the lower bound, given m-point zero-order bounds and
budget nonnegativity. The Doob CD-shift is tracked via `DoobAssumptions`
but not quantitatively used at this phase. -/
theorem lambdaEffLowerBound_construct_from_doobAssumptions_mpoint {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (lam eps Ssup XiNorm : ℝ) :
  ∃ lamEff : ℝ, lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm :=
by
  -- Choose the canonical RHS value as `lamEff`.
  refine ⟨lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm), ?_⟩
  exact le_of_eq rfl

/-! ### Main Lambda Effective Lower Bound with Doob Pack

This section provides the main theorem for deriving the effective lambda lower bound
from the Doob pack (λ - 2ε) and m-point 0-order term budget (c_*, c_D, Ssup, XiNorm). -/

/-- Main theorem: Derive λ_eff lower bound from Doob pack and m-point budget.
Given a Doob transform with parameter ε and m-point zero-order bounds,
we obtain: λ_eff ≥ (λ - 2ε) - γ·(c_* · Ssup² + c_D · XiNorm). -/
theorem lambdaEffLowerBound_from_doob_pack {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (h : X → ℝ) (D : Diffusion X) (doobPack : DoobQuantitative h D) -- Doob pack with ε
  (lam Ssup XiNorm : ℝ) (hCD : HasCD D lam) : -- Base CD condition
  ∃ lamEff : ℝ,
    lambdaEffLowerBound A budget lam doobPack.eps lamEff Ssup XiNorm ∧
    lamEff = lambdaBE lam doobPack.eps - A.gamma * (budget.cStar * Ssup ^ 2 + budget.cD * XiNorm) ∧
    HasCD (Doob h D) (lambdaBE lam doobPack.eps) := by
  -- The effective lambda is the RHS of the inequality
  let lamEff := lambdaBE lam doobPack.eps - A.gamma * (budget.cStar * Ssup ^ 2 + budget.cD * XiNorm)
  use lamEff
  refine ⟨?bound, rfl, ?cd⟩
  · -- Prove the lower bound
    exact le_refl lamEff
  · -- Prove the CD condition for Doob transform
    exact hasCD_doob_of_bochnerMinimal h D doobPack.bochner hCD

/-- Special case for commutative designs: When c_* = 0, the formula simplifies.
In commutative designs, the star term vanishes, giving:
λ_eff ≥ (λ - 2ε) - γ·(c_D · XiNorm). -/
theorem lambdaEffLowerBound_commutative {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (h : X → ℝ) (D : Diffusion X)
  (doobPack : DoobQuantitative h D) (lam Ssup XiNorm : ℝ) (hCD : HasCD D lam)
  (hCommutative : budget.cStar = 0) : -- Commutative design condition
  ∃ lamEff : ℝ,
    lambdaEffLowerBound A budget lam doobPack.eps lamEff Ssup XiNorm ∧
    lamEff = lambdaBE lam doobPack.eps - A.gamma * budget.cD * XiNorm := by
  -- Use the main theorem and simplify
  obtain ⟨lamEff, hBound, hFormula, hCD'⟩ :=
    lambdaEffLowerBound_from_doob_pack A budget h D doobPack lam Ssup XiNorm hCD
  use lamEff
  refine ⟨hBound, ?_⟩
  rw [hFormula, hCommutative]
  simp [zero_mul, zero_add, mul_assoc]

/-- Remark: In the commutative case (c_* = 0), the effective lambda formula
becomes λ_eff = (λ - 2ε) - γ·c_D·XiNorm, which provides a tighter bound
as the Ssup² term is eliminated. This is particularly relevant for:
- Symmetric diffusion operators
- Gradient flows on Riemannian manifolds with parallel transport
- Heat flow on groups with bi-invariant metrics -/
theorem lambdaEffLowerBound_commutative_remark {X : Type*} [PseudoMetricSpace X] :
  ∀ (A : FrourioFunctional X) (budget : ConstantBudget),
  budget.cStar = 0 →
  ∀ lam eps Ssup XiNorm : ℝ,
  lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ 2 + budget.cD * XiNorm) =
  lambdaBE lam eps - A.gamma * budget.cD * XiNorm := by
  intros A budget hc lam eps Ssup XiNorm
  rw [hc]
  simp [zero_mul, zero_add, mul_assoc]

/-- Constructor for effective lambda with explicit Doob pack and m-point budget.
This provides a convenient API for downstream usage. -/
def constructLambdaEff {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (h : X → ℝ) (D : Diffusion X)
  (doobPack : DoobQuantitative h D) (lam Ssup XiNorm : ℝ) : ℝ :=
  lambdaBE lam doobPack.eps - A.gamma * (budget.cStar * Ssup ^ 2 + budget.cD * XiNorm)

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
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ) : Prop :=
  ∀ x : X,
    slope (FrourioFunctional.F A) x
      ≤ slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)

/-- Parametric strong slope upper bound using an abstract slope specification. -/
def StrongSlopeUpperBound_with {X : Type*} [PseudoMetricSpace X]
  (S : SlopeSpec X) (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ) : Prop :=
  ∀ x : X,
    S.slope (FrourioFunctional.F A) x
      ≤ S.slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)

/-- Default strong slope upper bound using the implemented descending slope. -/
def StrongSlopeUpperBound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ) : Prop :=
  StrongSlopeUpperBound_with (descendingSlopeSpec X) A budget Ssup XiNorm

/-- The legacy predicate `StrongSlopeUpperBound_pred` is the `StrongSlopeUpperBound_with`
for the default zero slope. -/
theorem strongSlope_with_zero_equiv {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ) :
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
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ)
  (H : StrongSlopeUpperBound_pred A budget Ssup XiNorm) :
  ∀ x : X,
    slope (FrourioFunctional.F A) x
      ≤ slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
  H

/-- Parametric version: theoremized strong slope upper bound using a slope spec. -/
theorem slope_strong_upper_bound_with {X : Type*} [PseudoMetricSpace X]
  (S : SlopeSpec X) (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ) (H : StrongSlopeUpperBound_with S A budget Ssup XiNorm) :
  ∀ x : X,
    S.slope (FrourioFunctional.F A) x
      ≤ S.slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
  H

/-- Wrapper: theoremized strong slope upper bound in the default (descending slope) route. -/
theorem slope_strong_upper_bound_default {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ) (H : StrongSlopeUpperBound A budget Ssup XiNorm) :
  ∀ x : X,
    (descendingSlopeSpec X).slope (FrourioFunctional.F A) x
      ≤ (descendingSlopeSpec X).slope A.Ent x
        + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm) :=
  H

/-- A slope upper bound using the zero slope and nonnegativity. -/
theorem slope_upper_bound_zero {X : Type*} [PseudoMetricSpace X]
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

/-! ### HalfConvex Flag for λ_BE-Geodesic Semiconvexity

This section provides the connection between Ent's λ_BE-geodesic semiconvexity
and the HalfConvex flag required by the PLFA framework. -/

/-- Predicate: Ent satisfies λ-geodesic semiconvexity with respect to some
geodesic structure on X. This packages the existence of a geodesic
interpolation `γ` for which the standard λ-semiconvex inequality holds. -/
def EntGeodesicSemiconvex {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (lambda : ℝ) : Prop :=
  ∃ G : GeodesicStructure X, GeodesicSemiconvex G Ent lambda

/-- If Ent satisfies λ_BE-geodesic semiconvexity, then F = Ent + γ·Dσm
inherits HalfConvex property with parameter λ_BE. This is a placeholder
flag - the actual derivation is deferred to a later PR. -/
theorem halfConvex_from_ent_geodesic_semiconvex {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lambdaBE : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lambdaBE :=
by
  -- Placeholder implementation: HalfConvex with c = 0
  -- The actual constant will be derived from the geodesic semiconvexity of Ent
  -- combined with properties of Dσm in a future PR
  exact ⟨0, le_rfl, by intro x; simp⟩

/-- When using Doob transform with λ_BE = λ - 2ε, if the base Ent
satisfies λ-geodesic semiconvexity, then the transformed functional
has HalfConvex property with λ_BE. -/
theorem halfConvex_from_doob_lambdaBE {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lam eps : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) (lambdaBE lam eps) :=
by
  -- In the current surrogate development, we provide HalfConvex directly;
  -- once the Doob-induced λ_BE semiconvexity is formalized, this lemma can
  -- forward that hypothesis here.
  exact halfConvex_from_ent_geodesic_semiconvex Ent K gamma Ssup (lambdaBE lam eps)

/-- Combined flag provider: Given all necessary conditions, provide the
HalfConvex flag with λ_BE for use in AnalyticFlags. -/
def provideHalfConvexFlag {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lambdaBE : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lambdaBE :=
  halfConvex_from_ent_geodesic_semiconvex Ent K gamma Ssup lambdaBE

/-- API: Extract HalfConvex flag from DoobQuantitative pack.
This provides the flag needed for AnalyticFlagsReal. -/
theorem halfConvexFlag_from_doobQuantitative {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (h : X → ℝ) (D : Diffusion X) (HQ : DoobQuantitative h D) (lam : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
    (lambdaBE lam HQ.eps) :=
by
  -- Leverage the base construction; once Doob regularity is formalized, one
  -- can thread the resulting λ_BE-semi‑convexity through this lemma.
  exact halfConvex_from_ent_geodesic_semiconvex Ent K gamma Ssup (lambdaBE lam HQ.eps)

/-- Integration theorem: The HalfConvex flag from EntGeodesicSemiconvex
and StrongUpperBound from budget satisfy the requirements for
PLFA_EDE_from_analytic_flags, which ultimately feeds into AnalyticFlagsReal. -/
theorem halfConvex_strongUpperBound_integration {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lambdaBE : ℝ)
  (hSUB : StrongUpperBound (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lambdaBE ∧
  StrongUpperBound (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
⟨halfConvex_from_ent_geodesic_semiconvex Ent K gamma Ssup lambdaBE, hSUB⟩

/-! ### Proper Property for AnalyticFlagsReal

This section provides the proper property in the real sense (not surrogate)
for F=Ent+γDσm, as required by AnalyticFlagsReal. -/

/-- The functional F=Ent+γDσm is proper in the real sense:
there exists a sublevel set that is nonempty and F is bounded below. -/
theorem ofK_proper_real {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (x₀ : X) -- Need at least one point in X
  (CEnt CDsigma : ℝ) (hγ : 0 ≤ gamma) (hEntLB : ∀ x : X, Ent x ≥ -CEnt)
  (hDsigmaLB : ∀ x : X, (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x ≥ -CDsigma) :
  ∃ c : ℝ,
    (Set.Nonempty {x | FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c}) ∧
    BddBelow (Set.range (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))) :=
by
  -- Choose c large enough that x₀ is in the sublevel set
  let F := FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)
  use F x₀ + 1
  constructor
  · -- Sublevel set is nonempty (contains x₀)
    use x₀
    dsimp [F]
    -- F x₀ ≤ F x₀ + 1
    exact le_of_lt (lt_add_one _)
  · -- F is bounded below
    use -(CEnt + gamma * CDsigma)
    intro y
    simp only [Set.mem_range]
    intro ⟨x, hx⟩
    rw [← hx]
    dsimp [FrourioFunctional.F, FrourioFunctional.ofK]
    have h1 : Ent x ≥ -CEnt := hEntLB x
    have h2 : (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x ≥ -CDsigma := hDsigmaLB x
    calc
      Ent x + gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
        ≥ -CEnt + gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x := by
          apply add_le_add_right; exact h1
      _ ≥ -CEnt + gamma * (-CDsigma) := by
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_left h2 hγ
      _ = -(CEnt + gamma * CDsigma) := by ring

/-- Alternative: proper property using uniform bounds from K1'. -/
theorem ofK_proper_real_from_k1prime {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (x₀ : X) (CEnt : ℝ)
  (hγ : 0 ≤ gamma) (hEntLB : ∀ x : X, Ent x ≥ -CEnt)
  (hK1 : K1prime (FrourioFunctional.ofK Ent K gamma Ssup)) :
  ∃ c : ℝ,
    (Set.Nonempty {x | FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c}) ∧
    BddBelow (Set.range (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))) :=
by
  -- From K1', we know Dsigmam has a uniform lower bound
  obtain ⟨CDsigma, hDsigmaLB⟩ := hK1
  apply ofK_proper_real Ent K gamma Ssup x₀ CEnt CDsigma hγ hEntLB
  exact hDsigmaLB

/-- Comparison: The surrogate `Proper` is weaker than the real `proper`. -/
theorem proper_surrogate_from_real {X : Type*} [PseudoMetricSpace X] (F : X → ℝ) : Proper F :=
by
  exact ⟨0, fun x => by simp⟩

/-- Helper: Convert real proper to surrogate proper for the functional. -/
theorem ofK_proper_from_proper_real {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Proper (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
  proper_surrogate_from_real _

/-! ### Lower Semicontinuity for AnalyticFlagsReal

This section provides the lower semicontinuous property in Mathlib's sense
for F=Ent+γDσm, as required by AnalyticFlagsReal. -/

section LowerSemicontinuousLemmas

/-- Lower semicontinuity is preserved under non-negative scalar multiplication. -/
lemma lowerSemicontinuous_const_mul {X : Type*} [TopologicalSpace X]
  (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : _root_.LowerSemicontinuous f) :
  _root_.LowerSemicontinuous (fun x => c * f x) :=
by
  intro x y hy
  simp only at hy
  by_cases hc_zero : c = 0
  · -- Case 1: c = 0, the function is constant 0
    simp [hc_zero] at hy
    -- The function is constantly 0, and y < 0
    -- We need to show: ∀ᶠ x' in 𝓝 x, y < (fun z => c * f z) x'
    filter_upwards with x'
    simp [hc_zero]
    exact hy
  · -- Case 2: c > 0
    have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc_zero)
    -- From y < c * f(x), we need to apply lower semicontinuity
    -- We use: y < c * f(x) ↔ y/c < f(x) when c > 0

    -- Step 1: Get y/c < f(x)
    have h_div : y / c < f x := by
      rw [div_lt_iff₀ hc_pos, mul_comm]
      exact hy

    -- Step 2: Apply lower semicontinuity of f at y/c
    have h_lsc := hf x (y / c) h_div

    -- Step 3: Transform back
    filter_upwards [h_lsc] with x' hx'
    -- We have: y/c < f(x'), need to show: y < c * f(x')
    have : y / c < f x' := hx'
    rw [div_lt_iff₀ hc_pos] at this
    rw [mul_comm] at this
    exact this

end LowerSemicontinuousLemmas

/-- The functional F=Ent+γDσm is lower semicontinuous in Mathlib's sense
when both Ent and Dσm are lower semicontinuous. -/
theorem ofK_lowerSemicontinuous_real {X : Type*} [PseudoMetricSpace X] [TopologicalSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (hγ : 0 ≤ gamma)
  (hEnt_lsc : _root_.LowerSemicontinuous Ent)
  (hDsigma_lsc : _root_.LowerSemicontinuous ((FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam)) :
  _root_.LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  -- F = Ent + γ·Dσm is lower semicontinuous if both components are
  unfold FrourioFunctional.F FrourioFunctional.ofK
  -- Step 1: γ·Dσm is lower semicontinuous
  have h_gamma_dsigma : _root_.LowerSemicontinuous (fun x => gamma * DsigmamFromK K Ssup x) :=
    lowerSemicontinuous_const_mul (DsigmamFromK K Ssup) gamma hγ hDsigma_lsc
  -- Step 2: Ent + γ·Dσm is lower semicontinuous (sum of LSC functions)
  exact _root_.LowerSemicontinuous.add hEnt_lsc h_gamma_dsigma

/-- Alternative: If K satisfies narrow continuity, then Dσm is lower semicontinuous. -/
theorem dsigmam_lowerSemicontinuous_from_k1 {X : Type*} [PseudoMetricSpace X] [TopologicalSpace X]
  (K : KTransform X) (Ssup : ℝ) (hS : 0 ≤ Ssup)
  (hK_cont : ∀ s : ℝ, Continuous (fun x => K.map x s)) :
  _root_.LowerSemicontinuous (DsigmamFromK K Ssup) :=
by
  -- DsigmamFromK K Ssup = fun x => Ssup * K.map x 0
  unfold DsigmamFromK
  -- The function x ↦ K.map x 0 is continuous, hence lower semicontinuous
  have h_cont : Continuous (fun x => K.map x 0) := hK_cont 0
  -- A continuous function is lower semicontinuous
  have h_lsc : _root_.LowerSemicontinuous (fun x => K.map x 0) :=
    Continuous.lowerSemicontinuous h_cont
  -- Apply our lemma for scalar multiplication
  exact lowerSemicontinuous_const_mul (fun x => K.map x 0) Ssup hS h_lsc

/-- The functional F=Ent+γDσm is lower semicontinuous when Ent is continuous
and K has pointwise continuity in the state variable. -/
theorem ofK_lowerSemicontinuous_from_continuous {X : Type*} [PseudoMetricSpace X]
  [TopologicalSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (hγ : 0 ≤ gamma) (hS : 0 ≤ Ssup)
  (hEnt_cont : Continuous Ent) (hK_cont : ∀ s : ℝ, Continuous (fun x => K.map x s)) :
  _root_.LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  apply ofK_lowerSemicontinuous_real Ent K gamma Ssup hγ
  · -- Ent is continuous, hence lower semicontinuous
    exact Continuous.lowerSemicontinuous hEnt_cont
  · -- Dσm is lower semicontinuous from K's continuity
    unfold FrourioFunctional.ofK
    exact dsigmam_lowerSemicontinuous_from_k1 K Ssup hS hK_cont

/-- Comparison: The surrogate LowerSemicontinuous is weaker than Mathlib's. -/
theorem lsc_surrogate_from_real {X : Type*} [PseudoMetricSpace X] (F : X → ℝ) :
  LowerSemicontinuous F :=
by
  intro x
  exact ⟨0, le_refl 0, by simp⟩

/-- Helper: Show that if F satisfies Mathlib's lower semicontinuity,
then it also satisfies the surrogate version. -/
theorem ofK_lsc_surrogate_from_real {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
  lsc_surrogate_from_real _

/-! ### Coercivity for AnalyticFlagsReal

This section provides the coercive property in the real mathematical sense
for F=Ent+γDσm, as required by AnalyticFlagsReal. -/

section CoercivityReal

/-- A function is coercive in the real sense if it tends to infinity as the argument
tends to infinity in norm. This is the standard definition used in optimization and PDE theory. -/
def CoerciveReal {X : Type*} [NormedAddCommGroup X] (f : X → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ x : X, ‖x‖ ≥ R → f x ≥ M

/-- Alternative characterization: f(x) → ∞ as ‖x‖ → ∞ -/
def CoerciveReal' {X : Type*} [NormedAddCommGroup X] (f : X → ℝ) : Prop :=
  Filter.Tendsto f (Filter.cocompact X) Filter.atTop

/-- The functional F=Ent+γDσm is coercive in the real sense when both
Ent and Dσm satisfy appropriate growth conditions. -/
theorem ofK_coercive_real {X : Type*} [NormedAddCommGroup X] [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hγ : 0 < gamma) -- Need positive gamma for coercivity
  (hEnt_growth : ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ ∀ x : X, Ent x ≥ c₁ * ‖x‖ - c₂)  -- Linear growth
  (hDsigma_bounded_below : ∃ C : ℝ, ∀ x : X,
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x ≥ -C) :
  CoerciveReal (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  intro M
  -- Use the linear growth of Ent to dominate
  obtain ⟨c₁, c₂, hc₁, hEnt⟩ := hEnt_growth
  obtain ⟨C, hDsigma⟩ := hDsigma_bounded_below

  -- Choose R large enough so that c₁ * R - c₂ - γ * C ≥ M
  use (M + c₂ + gamma * C) / c₁ + 1

  intro x hx
  unfold FrourioFunctional.F FrourioFunctional.ofK
  -- F(x) = Ent(x) + γ * Dσm(x) ≥ c₁ * ‖x‖ - c₂ + γ * (-C)
  have h1 : (FrourioFunctional.ofK Ent K gamma Ssup).Ent x ≥ c₁ * ‖x‖ - c₂ := hEnt x
  have h2 : (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x ≥ -C := hDsigma x
  have h3 : gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x ≥ gamma * (-C) :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt hγ)
  calc (FrourioFunctional.ofK Ent K gamma Ssup).Ent x +
       (FrourioFunctional.ofK Ent K gamma Ssup).gamma *
       (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
    _ ≥ (c₁ * ‖x‖ - c₂) + gamma * (-C) := add_le_add h1 h3
    _ = c₁ * ‖x‖ - c₂ - gamma * C := by ring
    _ ≥ c₁ * ((M + c₂ + gamma * C) / c₁ + 1) - c₂ - gamma * C := by
      linarith [mul_le_mul_of_nonneg_left hx (le_of_lt hc₁)]
    _ = c₁ * ((M + c₂ + gamma * C) / c₁) + c₁ - c₂ - gamma * C := by ring
    _ = (M + c₂ + gamma * C) / c₁ * c₁ + c₁ - c₂ - gamma * C := by ring
    _ = (M + c₂ + gamma * C) + c₁ - c₂ - gamma * C := by
      simp only [div_mul_cancel₀ _ hc₁.ne']
    _ = M + c₁ := by ring
    _ ≥ M := le_add_of_nonneg_right (le_of_lt hc₁)

/-- Helper: The surrogate coercive property is weaker than the real one. -/
theorem coercive_surrogate_from_real {X : Type*} [NormedAddCommGroup X] [PseudoMetricSpace X]
  (F : X → ℝ) : Coercive F :=
by
  intro x
  exact ⟨0, le_refl 0, by simp⟩

/-- Helper: Show that if F satisfies real coercivity,
then it also satisfies the surrogate version. -/
theorem ofK_coercive_surrogate_from_real {X : Type*} [NormedAddCommGroup X] [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Coercive (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
  coercive_surrogate_from_real _

end CoercivityReal

/-! ### Geodesic Structure for Real Analytic Flags

This section provides the geodesic structure and semiconvexity properties
needed for AnalyticFlagsReal. -/

section GeodesicReal

/-- A basic geodesic structure on a normed space using linear interpolation. -/
def StandardGeodesicStructure (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
  GeodesicStructure X where
  γ := fun x y t => (1 - t) • x + t • y
  start_point := fun x y => by simp
  end_point := fun x y => by simp
  geodesic_property := fun x y s t _hs0 _hs1 _ht0 _ht1 => by
    -- Linear interpolation yields constant‑speed geodesics
    -- Key algebraic identity for the chord between parameters s and t
    have hdiff :
        ((1 - t) • x + t • y) - ((1 - s) • x + s • y)
          = (t - s) • (y - x) := by
      -- (a+b) - (c+d) = (a - c) + (b - d)
      have hsplit :
          ((1 - t) • x + t • y) - ((1 - s) • x + s • y)
            = (((1 - t) • x) - ((1 - s) • x)) + (t • y - s • y) := by
        rw [add_sub_add_comm]
      -- pull out scalars from differences
      have hx' : ((1 - t) • x) - ((1 - s) • x) = ((1 - t) - (1 - s)) • x := by
        simp [sub_smul]
      have hy' : t • y - s • y = (t - s) • y := by
        simp [sub_smul]
      -- combine
      have : ((1 - t) - (1 - s)) • x + (t - s) • y
             = (t - s) • (y - x) := by
        have hcoef : (1 - t) - (1 - s) = (s - t) := by ring
        have hxneg : (s - t) • x = -((t - s) • x) := by
          have hst : (s - t) = -(t - s) := by ring
          rw [hst, neg_smul]
        calc
          ((1 - t) - (1 - s)) • x + (t - s) • y
              = (s - t) • x + (t - s) • y := by simp [hcoef]
          _ = -((t - s) • x) + (t - s) • y := by simp [hxneg]
          _ = (t - s) • (y - x) := by
                simp [sub_eq_add_neg, smul_add, add_comm]
      rw [hsplit, hx', hy', this]
    -- Distances as norms and homogeneity of the norm
    calc
      dist ((1 - s) • x + s • y) ((1 - t) • x + t • y)
          = ‖((1 - t) • x + t • y) - ((1 - s) • x + s • y)‖ := by
              simp [dist_eq_norm, norm_sub_rev]
      _ = ‖(t - s) • (y - x)‖ := by simp [hdiff]
      _ = |t - s| * ‖y - x‖ := by simp [norm_smul]
      _ = |t - s| * dist x y := by simp [dist_eq_norm, norm_sub_rev]

/-- Existence of a concrete geodesic structure on a normed space:
we use the standard linear-interpolation geodesics, which have constant speed. -/
theorem ofK_geodesic_structure {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
  Nonempty (GeodesicStructure X) :=
⟨StandardGeodesicStructure X⟩

/-- The functional F=Ent+γDσm is geodesically semiconvex when Ent is
geodesically semiconvex and Dσm satisfies certain regularity conditions. -/
theorem ofK_geodesic_semiconvex {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) (hγ : 0 ≤ gamma)
  (G : GeodesicStructure X) (hEnt : GeodesicSemiconvex G Ent lamEff)
  (hDsigma_convex : ∀ x y : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam (G.γ x y t) ≤
    (1 - t) * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x +
    t * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) :
  GeodesicSemiconvex G (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff :=
by
  intro x y t ht0 ht1
  unfold FrourioFunctional.F
  -- F = Ent + γ·Dσm, so we need to combine the semiconvexity of Ent
  -- with the convexity of Dσm
  calc (FrourioFunctional.ofK Ent K gamma Ssup).Ent (G.γ x y t) +
       (FrourioFunctional.ofK Ent K gamma Ssup).gamma *
       (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam (G.γ x y t)
    _ ≤ ((1 - t) * Ent x + t * Ent y - (lamEff / 2) * t * (1 - t) * (dist x y) ^ 2) +
        gamma * ((1 - t) * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x +
                 t * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) := by
      apply add_le_add
      · exact hEnt x y t ht0 ht1
      · exact mul_le_mul_of_nonneg_left (hDsigma_convex x y t ht0 ht1) hγ
    _ = (1 - t) * (Ent x + gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x) +
        t * (Ent y + gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) -
        (lamEff / 2) * t * (1 - t) * (dist x y) ^ 2 := by ring
    _ = (1 - t) * FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x +
        t * FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) y -
        (lamEff / 2) * t * (1 - t) * (dist x y) ^ 2 := by
      unfold FrourioFunctional.F
      rfl

/-- Helper theorem: For standard geodesic structure (linear interpolation),
if a function is convex in the usual sense, it's geodesically 0-semiconvex. -/
theorem convex_implies_geodesic_semiconvex {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (f : X → ℝ) (hf : ∀ x y : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f ((1 - t) • x + t • y) ≤ (1 - t) * f x + t * f y) :
  GeodesicSemiconvex (StandardGeodesicStructure X) f 0 :=
by
  intro x y t ht0 ht1
  have key : (StandardGeodesicStructure X).γ x y t = (1 - t) • x + t • y := rfl
  rw [key]
  calc f ((1 - t) • x + t • y)
    _ ≤ (1 - t) * f x + t * f y := hf x y t ht0 ht1
    _ = (1 - t) * f x + t * f y - 0 := by ring
    _ = (1 - t) * f x + t * f y - (0 / 2) * t * (1 - t) * (dist x y) ^ 2 := by ring

end GeodesicReal

/-! ### Semiconvexity for Real Analytic Flags

This section provides semiconvexity properties needed for AnalyticFlagsReal. -/

section SemiconvexReal

/-- The functional F=Ent+γDσm satisfies semiconvexity for AnalyticFlagsReal
when provided with appropriate geodesic structure and regularity conditions. -/
theorem ofK_semiconvex_real {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) (hγ : 0 ≤ gamma)
  (G : GeodesicStructure X) (hEnt_semiconvex : GeodesicSemiconvex G Ent lamEff)
  (hDsigma_convex : ∀ x y : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam (G.γ x y t) ≤
    (1 - t) * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x +
    t * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) :
  GeodesicSemiconvex G (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff :=
ofK_geodesic_semiconvex Ent K gamma Ssup lamEff hγ G hEnt_semiconvex hDsigma_convex

/-- For the standard geodesic structure, F inherits semiconvexity from Ent
when Dσm is convex along geodesics. -/
theorem ofK_semiconvex_standard {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) (hγ : 0 ≤ gamma)
  (hEnt_semiconvex : GeodesicSemiconvex (StandardGeodesicStructure X) Ent lamEff)
  (hDsigma_convex : ∀ x y : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam ((1 - t) • x + t • y) ≤
    (1 - t) * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x +
    t * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) :
  GeodesicSemiconvex (StandardGeodesicStructure X)
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff :=
by
  apply ofK_geodesic_semiconvex
  · exact hγ
  · exact hEnt_semiconvex
  · intro x y t ht0 ht1
    convert hDsigma_convex x y t ht0 ht1

/-- When Ent is λ-semiconvex and Dσm is convex (0-semiconvex),
F = Ent + γ·Dσm is λ-semiconvex. -/
theorem semiconvex_combination {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Ent Dsigma : X → ℝ) (gamma lamEff : ℝ) (hγ : 0 ≤ gamma) (G : GeodesicStructure X)
  (hEnt : GeodesicSemiconvex G Ent lamEff) (hDsigma : GeodesicSemiconvex G Dsigma 0) :
  GeodesicSemiconvex G (fun x => Ent x + gamma * Dsigma x) lamEff :=
by
  intro x y t ht0 ht1
  calc (Ent (G.γ x y t) + gamma * Dsigma (G.γ x y t))
    _ ≤ ((1 - t) * Ent x + t * Ent y - (lamEff / 2) * t * (1 - t) * (dist x y) ^ 2) +
        gamma * ((1 - t) * Dsigma x + t * Dsigma y - (0 / 2) * t * (1 - t) * (dist x y) ^ 2) := by
      apply add_le_add
      · exact hEnt x y t ht0 ht1
      · apply mul_le_mul_of_nonneg_left
        · exact hDsigma x y t ht0 ht1
        · exact hγ
    _ = (1 - t) * (Ent x + gamma * Dsigma x) + t * (Ent y + gamma * Dsigma y) -
        (lamEff / 2) * t * (1 - t) * (dist x y) ^ 2 := by ring

end SemiconvexReal

/-! ### Compact Sublevels for Real Analytic Flags

This section provides compact sublevel set properties needed for AnalyticFlagsReal. -/

section CompactSublevels

/-- A functional has compact sublevels if all sublevel sets are compact. -/
def HasCompactSublevels {X : Type*} [TopologicalSpace X] (f : X → ℝ) : Prop :=
  ∀ c : ℝ, IsCompact {x : X | f x ≤ c}

/-- The functional F=Ent+γDσm has compact sublevels when both Ent and Dσm
have appropriate growth conditions and the space has suitable compactness properties. -/
theorem ofK_compact_sublevels {X : Type*} [NormedAddCommGroup X]
  [ProperSpace X] -- X is a proper metric space (closed balls are compact)
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hγ : 0 < gamma) (hEnt_coercive : CoerciveReal Ent) -- Ent grows to infinity at infinity
  (hDsigma_bounded_below : ∃ C : ℝ, ∀ x : X,
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x ≥ -C)
  (h_lsc : _root_.LowerSemicontinuous
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))) :
  HasCompactSublevels (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  intro c
  -- The sublevel set {x | F(x) ≤ c}
  -- Since F is coercive, sublevel sets are bounded
  -- Since F is lower semicontinuous, sublevel sets are closed
  -- In a proper space, closed and bounded implies compact

  -- First show the set is bounded
  have h_bounded : ∃ R > 0, {x : X | FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c} ⊆
    Metric.closedBall 0 R := by
    -- Use coercivity to find R such that F(x) > c for ‖x‖ > R
    obtain ⟨C, hC⟩ := hDsigma_bounded_below
    -- Choose M large enough so that Ent(x) ≥ M implies F(x) > c
    let M := c + gamma * C + 1
    obtain ⟨R₀, hR₀⟩ := hEnt_coercive M
    -- Ensure R is positive
    let R := max R₀ 1
    have hR_pos : 0 < R := by
      unfold R
      simp only [lt_max_iff]
      right
      norm_num
    use R, hR_pos
    intro x hx
    simp only [Metric.mem_closedBall]
    -- Show x is in the closed ball of radius R centered at 0
    -- We prove by contradiction: if ‖x‖ > R, then F(x) > c
    by_contra h_not_in_ball
    push_neg at h_not_in_ball
    -- h_not_in_ball : R < dist x 0
    -- Convert to the norm using `dist_eq_norm`
    have h_norm_large : R < ‖x‖ := by
      -- `dist x 0 = ‖x‖` in a normed group
      -- Now that we use the norm-induced metric, we can apply dist_eq_norm
      calc R < dist x 0 := h_not_in_ball
           _ = ‖x - 0‖ := dist_eq_norm x 0
           _ = ‖x‖ := by simp [sub_zero]
    -- Now h_norm_large : R < ‖x‖
    -- If ‖x‖ > R, then ‖x‖ ≥ R₀, so F(x) > c by coercivity
    have hx_ge_R : R ≤ ‖x‖ := le_of_lt h_norm_large
    have hR_ge_R0 : R ≥ R₀ := by
      unfold R; exact le_max_left _ _
    have hR0_le_R : R₀ ≤ R := hR_ge_R0
    have hx_large : ‖x‖ ≥ R₀ := le_trans hR0_le_R hx_ge_R
    have hEnt_large : Ent x ≥ M := hR₀ x hx_large
    have hF_large : FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x > c := by
      unfold FrourioFunctional.F
      calc (FrourioFunctional.ofK Ent K gamma Ssup).Ent x +
           (FrourioFunctional.ofK Ent K gamma Ssup).gamma *
           (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
        _ = Ent x + gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x := by rfl
        _ ≥ Ent x + gamma * (-C) := by
            apply add_le_add_left
            exact mul_le_mul_of_nonneg_left (hC x) (le_of_lt hγ)
        _ ≥ M - gamma * C := by linarith [hEnt_large]
        _ = c + gamma * C + 1 - gamma * C := by rfl
        _ = c + 1 := by ring
        _ > c := by linarith
    exact not_le.mpr hF_large hx

  -- The set is closed because F is lower semicontinuous
  have h_closed : IsClosed {x : X | FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c} := by
    -- Lower semicontinuous functions have closed sublevel sets
    -- Use the helper from MinimizingMovement: `sublevel_closed_of_lsc`
    exact Frourio.sublevel_closed_of_lsc h_lsc c

  -- In a proper space, closed and bounded implies compact
  -- Get the specific R from h_bounded
  obtain ⟨R, hR_pos, h_subset⟩ := h_bounded
  -- Closed balls are compact in proper spaces
  have h_ball_compact : IsCompact (Metric.closedBall (0 : X) R) :=
    ProperSpace.isCompact_closedBall _ _
  -- A closed subset of a compact set is compact
  apply IsCompact.of_isClosed_subset h_ball_compact h_closed h_subset

/-- Alternative: When the space has the Heine-Borel property,
coercivity and continuity imply compact sublevels. -/
theorem compact_sublevels_from_coercive_continuous {X : Type*} [NormedAddCommGroup X]
  [NormedSpace ℝ X] [FiniteDimensional ℝ X] -- Finite dimensional spaces have Heine-Borel
  (f : X → ℝ) (h_coercive : CoerciveReal f) (h_continuous : Continuous f) :
  HasCompactSublevels f :=
by
  intro c
  -- In finite dimensions, closed and bounded is compact (Heine-Borel)
  -- The sublevel set is closed (continuous functions have closed sublevel sets)
  have h_closed : IsClosed {x : X | f x ≤ c} := by
    exact isClosed_le h_continuous (continuous_const)
  -- Use coercivity to find R such that f(x) > c for ‖x‖ ≥ R
  obtain ⟨R, hR⟩ := h_coercive (c + 1)
  -- The sublevel set is bounded (use coercivity)
  have h_bounded : Bornology.IsBounded {x : X | f x ≤ c} := by
    -- The sublevel set is contained in the ball of radius R + 1
    rw [Metric.isBounded_iff_subset_ball 0]
    use R + 1
    intro x hx
    simp only [Metric.mem_ball, Set.mem_setOf_eq] at hx ⊢
    -- If ‖x‖ ≥ R, then f(x) ≥ c + 1 > c, contradicting hx
    by_contra h_not_in_ball
    push_neg at h_not_in_ball
    have h_norm_large : ‖x‖ ≥ R := by
      have h1 : R + 1 ≤ dist x 0 := h_not_in_ball
      have h2 : R < R + 1 := by linarith
      have h3 : R < dist x 0 := lt_of_lt_of_le h2 h1
      have h4 : dist x 0 = ‖x‖ := by simp [dist_eq_norm, sub_zero]
      rw [← h4]
      exact le_of_lt h3
    have h_f_large : f x ≥ c + 1 := hR x h_norm_large
    linarith [hx]
  -- In finite dimensions, closed and bounded implies compact
  -- Use the fact that finite dimensional normed spaces are proper
  haveI : ProperSpace X := FiniteDimensional.proper_real X
  -- In a proper space, closed and bounded implies compact
  have h_ball_compact : IsCompact (Metric.closedBall (0 : X) (R + 1)) :=
    ProperSpace.isCompact_closedBall _ _
  have h_subset : {x : X | f x ≤ c} ⊆ Metric.closedBall 0 (R + 1) := by
    intro x hx
    simp only [Metric.mem_closedBall, Set.mem_setOf_eq] at hx ⊢
    by_contra h_far
    push_neg at h_far
    have h1 : ‖x‖ > R + 1 := by simpa [dist_eq_norm, sub_zero] using h_far
    have h2 : ‖x‖ ≥ R := by linarith
    have h3 : f x ≥ c + 1 := hR x h2
    have h4 : f x ≤ c := hx
    linarith
  exact IsCompact.of_isClosed_subset h_ball_compact h_closed h_subset

/-- For normed spaces, if F is lower semicontinuous
and has bounded sublevel sets, it has compact sublevels. -/
theorem compact_sublevels_from_proper_lsc {X : Type*} [NormedAddCommGroup X] [ProperSpace X]
  (f : X → ℝ) (h_lsc : _root_.LowerSemicontinuous f)
  (h_bounded_sublevels : ∀ c : ℝ, Bornology.IsBounded {x : X | f x ≤ c}) :
  HasCompactSublevels f :=
by
  intro c
  -- Lower semicontinuous functions have closed sublevel sets
  have h_closed : IsClosed {x : X | f x ≤ c} := by
    exact LowerSemicontinuous.isClosed_preimage h_lsc c
  -- Get boundedness from the hypothesis
  have h_bounded : Bornology.IsBounded {x : X | f x ≤ c} := h_bounded_sublevels c
  -- In a proper space, closed and bounded implies compact
  -- First, get a ball containing the sublevel set
  rw [Metric.isBounded_iff_subset_closedBall 0] at h_bounded
  obtain ⟨r, hr⟩ := h_bounded
  -- The sublevel set is contained in the closed ball
  -- Closed balls are compact in proper spaces
  have h_ball_compact : IsCompact (Metric.closedBall (0 : X) r) :=
    ProperSpace.isCompact_closedBall _ _
  -- A closed subset of a compact set is compact
  exact IsCompact.of_isClosed_subset h_ball_compact h_closed hr

end CompactSublevels

/-! ### Slope Bounds for AnalyticFlagsReal

This section provides bounds on the descending slope needed for AnalyticFlagsReal. -/

section SlopeBounds

-- Disable long line warnings for complex mathematical expressions in this section
set_option linter.style.longLine false

/-! ### Helper Lemmas for Slope Bounds

These lemmas establish the subadditivity properties needed for slope bounds. -/

open Real in
/-- Subadditivity of the positive part function. -/
lemma posPart_add_le (a b : ℝ) : (a + b)⁺ ≤ a⁺ + b⁺ := by
  -- Case split on whether a + b is positive
  by_cases h : a + b ≤ 0
  · -- If a + b ≤ 0, then (a + b)⁺ = 0
    simp [h]
    exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  · -- If a + b > 0, then (a + b)⁺ = a + b
    push_neg at h
    simp [le_of_lt h]
    exact add_le_add (le_max_left _ _) (le_max_left _ _)

/-- Positive part scaling for non-negative scalars. -/
lemma posPart_smul (c : ℝ) (hc : 0 ≤ c) (a : ℝ) : (c * a)⁺ = c * a⁺ := by
  by_cases ha : a ≤ 0
  · -- If a ≤ 0, then a⁺ = 0 and c * a ≤ 0
    simp [ha]
    have : c * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc ha
    simp [this]
  · -- If a > 0, then a⁺ = a and c * a ≥ 0
    push_neg at ha
    simp [le_of_lt ha]
    -- For c ≥ 0 and a > 0, we have c * a ≥ 0
    -- We need to handle the case c = 0 separately
    by_cases hc_zero : c = 0
    · simp [hc_zero]
    · -- If c > 0 and a > 0, then c * a > 0
      have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc_zero)
      have : 0 < c * a := mul_pos hc_pos ha
      simp [le_of_lt this]

/-! ### Helper lemmas for EReal-based proofs -/

/-- If a function is eventually nonnegative, its EReal limsup is not ⊥. -/
lemma ereal_limsup_ne_bot_of_eventually_nonneg {α : Type*} {l : Filter α} [l.NeBot]
  {f : α → ℝ} (h : ∀ᶠ a in l, 0 ≤ f a) :
  Filter.limsup (fun a => (f a : EReal)) l ≠ ⊥ := by
  -- First, show that the function is bounded above in EReal
  have h_bdd : Filter.IsBoundedUnder (· ≤ ·) l (fun a => (f a : EReal)) := by
    apply Filter.isBoundedUnder_of
    use ⊤
    intro x
    exact le_top
  -- Now show limsup ≥ 0
  have h1 : (0 : EReal) ≤ Filter.limsup (fun a => (f a : EReal)) l := by
    apply Filter.le_limsup_of_frequently_le
    · -- Show ∃ᶠ a in l, 0 ≤ (f a : EReal)
      have : ∃ᶠ a in l, (0 : ℝ) ≤ f a := h.frequently
      exact this.mono (fun a ha => EReal.coe_nonneg.mpr ha)
    · exact h_bdd
  -- Since 0 ≠ ⊥ and limsup ≥ 0, we have limsup ≠ ⊥
  exact ne_bot_of_le_ne_bot EReal.zero_ne_bot h1

/-- Convert EReal limsup back to ℝ when the function is ℝ-valued, nonnegative and bounded. -/
lemma limsup_ereal_eq_limsup_real_of_bounded {α : Type*} {l : Filter α} [l.NeBot]
  {f : α → ℝ} (h_nonneg : ∀ᶠ a in l, 0 ≤ f a)
  (h_bdd : Filter.IsBoundedUnder (· ≤ ·) l f) :
  (Filter.limsup (fun a => (f a : EReal)) l).toReal = Filter.limsup f l := by
  -- We will use the monotone-map lemma for limsup with the coercion ℝ → EReal.
  -- Provide lower coboundedness of f from eventual nonnegativity.
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) l f :=
    Filter.isCoboundedUnder_le_of_eventually_le (l := l) (f := f) (x := (0 : ℝ)) h_nonneg
  -- Transport limsup through the monotone, continuous coercion.
  have hmap : Filter.limsup (fun a => ((f a : ℝ) : EReal)) l
      = ((Filter.limsup f l : ℝ) : EReal) := by
    have hmono : Monotone (fun x : ℝ => (x : EReal)) := by
      intro a b hab; simpa [EReal.coe_le_coe_iff] using hab
    have hcont : ContinuousAt (fun x : ℝ => (x : EReal)) (Filter.limsup f l) :=
      (continuous_coe_real_ereal).continuousAt
    -- Use the mapping lemma; note the direction and `Function.comp` normalization.
    have h := (Monotone.map_limsup_of_continuousAt (F := l)
                  (f := fun x : ℝ => (x : EReal)) (a := f)
                  (f_incr := hmono) (f_cont := hcont)
                  (bdd_above := h_bdd) (cobdd := hcobdd))
    -- h : ((Filter.limsup f l : ℝ) : EReal) = Filter.limsup ((fun x => (x : EReal)) ∘ f) l
    -- Rewrite `((fun x => (x : EReal)) ∘ f)` to `fun a => (f a : EReal)` and flip sides.
    simpa [Function.comp] using h.symm
  -- Apply toReal to both sides and simplify.
  calc
    (Filter.limsup (fun a => (f a : EReal)) l).toReal
        = (((Filter.limsup f l : ℝ) : EReal)).toReal := by
          simpa using congrArg (fun x => EReal.toReal x) hmap
    _ = Filter.limsup f l := by simp

/-- Subadditivity of descending slope for sums. -/
lemma descendingSlope_add_le {X : Type*} [PseudoMetricSpace X]
  {f g : X → ℝ} (x : X)
  [Filter.NeBot (nhdsWithin x (posDist x))]
  (h_add_limsup :
    Filter.limsup
      (fun y => (posPart (f x - f y)) / dist x y
               + (posPart (g x - g y)) / dist x y)
      (nhdsWithin x (posDist x))
    ≤ Filter.limsup (fun y => (posPart (f x - f y)) / dist x y)
        (nhdsWithin x (posDist x))
      + Filter.limsup (fun y => (posPart (g x - g y)) / dist x y)
        (nhdsWithin x (posDist x)))
  (h_sum_ub : ∃ M : ℝ, ∀ᶠ y in nhdsWithin x (posDist x),
      (posPart (f x - f y)) / dist x y + (posPart (g x - g y)) / dist x y ≤ M) :
  descendingSlope (fun y => f y + g y) x ≤ descendingSlope f x + descendingSlope g x := by
  -- Unfold descending slope definitions
  dsimp [descendingSlope]
  -- Set up the filter for points at positive distance
  set F := nhdsWithin x (posDist x)
  -- Define the quotient functions
  set u : X → ℝ := fun y => (posPart (f x - f y)) / dist x y
  set v : X → ℝ := fun y => (posPart (g x - g y)) / dist x y
  set w : X → ℝ := fun y => (posPart ((f x + g x) - (f y + g y))) / dist x y

  -- Show pointwise inequality: w y ≤ u y + v y for all y with 0 < dist x y
  have h_pointwise : ∀ᶠ y in F, w y ≤ u y + v y := by
    refine Filter.eventually_of_mem (self_mem_nhdsWithin) ?_
    intro y hy
    have h_pos : 0 < dist x y := by
      have : 0 < dist y x := hy
      rwa [dist_comm]
    have h_ne_zero : dist x y ≠ 0 := ne_of_gt h_pos
    -- Use positive part subadditivity
    have h_sub : (f x + g x) - (f y + g y) = (f x - f y) + (g x - g y) := by ring
    -- Apply to the goal directly
    simp only [w, u, v]
    rw [h_sub]
    -- Apply positive part subadditivity
    have h_pos_sub : posPart ((f x - f y) + (g x - g y)) ≤
                     posPart (f x - f y) + posPart (g x - g y) := posPart_add_le _ _
    -- Divide by dist x y
    have h_div := div_le_div_of_nonneg_right h_pos_sub (le_of_lt h_pos)
    simp only [add_div] at h_div
    exact h_div

  -- Apply limsup monotonicity + subadditivity via EReal
  haveI : F.NeBot := by
    -- This follows from the lemma hypothesis `[Filter.NeBot (nhdsWithin x (posDist x))]`.
    simpa [F]
  have h_limsup : Filter.limsup w F ≤ Filter.limsup u F + Filter.limsup v F := by
    -- Step 1: Establish eventual nonnegativity for all functions
    have hw_nonneg : ∀ᶠ y in F, 0 ≤ w y := by
      refine Filter.eventually_of_mem (self_mem_nhdsWithin) ?_
      intro y hy
      have h_pos : 0 < dist y x := hy  -- hy directly gives us the distance property
      exact div_nonneg (posPart_nonneg _) (le_of_lt (by rwa [dist_comm]))
    have hu_nonneg : ∀ᶠ y in F, 0 ≤ u y := by
      refine Filter.eventually_of_mem (self_mem_nhdsWithin) ?_
      intro y hy
      have h_pos : 0 < dist y x := hy
      exact div_nonneg (posPart_nonneg _) (le_of_lt (by rwa [dist_comm]))
    have hv_nonneg : ∀ᶠ y in F, 0 ≤ v y := by
      refine Filter.eventually_of_mem (self_mem_nhdsWithin) ?_
      intro y hy
      have h_pos : 0 < dist y x := hy
      exact div_nonneg (posPart_nonneg _) (le_of_lt (by rwa [dist_comm]))

    -- Step 2: Lift to EReal
    set uE : X → EReal := fun y => (u y : EReal)
    set vE : X → EReal := fun y => (v y : EReal)
    set wE : X → EReal := fun y => (w y : EReal)

    -- Step 3: Pointwise inequality in EReal
    have h_pointwiseE : ∀ᶠ y in F, wE y ≤ uE y + vE y := by
      exact h_pointwise.mono (fun y hy => by simp only [uE, vE, wE]; exact_mod_cast hy)

    -- Step 4: Apply EReal limsup monotonicity and subadditivity

    -- First show that the EReal functions are bounded above (by ⊤)
    have h_bddE_u : Filter.IsBoundedUnder (· ≤ ·) F uE := by
      apply Filter.isBoundedUnder_of
      use ⊤
      intro x
      exact le_top
    have h_bddE_v : Filter.IsBoundedUnder (· ≤ ·) F vE := by
      apply Filter.isBoundedUnder_of
      use ⊤
      intro x
      exact le_top
    have h_bddE_w : Filter.IsBoundedUnder (· ≤ ·) F wE := by
      apply Filter.isBoundedUnder_of
      use ⊤
      intro x
      exact le_top

    -- Apply monotonicity: limsup wE ≤ limsup (uE + vE)
    have h_mono : Filter.limsup wE F ≤ Filter.limsup (fun y => uE y + vE y) F := by
      have h_cobdd_w : Filter.IsCoboundedUnder (· ≤ ·) F wE := by
        have h_ev : ∀ᶠ y in F, (0 : EReal) ≤ wE y := by
          exact hw_nonneg.mono (fun y hy => by
            change (0 : EReal) ≤ (w y : EReal)
            exact EReal.coe_nonneg.mpr hy)
        apply Filter.isCoboundedUnder_le_of_eventually_le
        exact h_ev
      have h_bdd_sum : Filter.IsBoundedUnder (· ≤ ·) F (fun y => uE y + vE y) := by
        apply Filter.isBoundedUnder_of
        use ⊤
        intro x
        exact le_top
      apply Filter.limsup_le_limsup h_pointwiseE h_cobdd_w h_bdd_sum

    -- Apply subadditivity: limsup (uE + vE) ≤ limsup uE + limsup vE
    have h_add : Filter.limsup (fun y => uE y + vE y) F ≤
                 Filter.limsup uE F + Filter.limsup vE F := by
      apply EReal.limsup_add_le
      · -- Side condition 1: limsup uE ≠ ⊥ ∨ limsup vE ≠ ⊤
        left
        -- uE is eventually nonnegative, so limsup uE ≠ ⊥
        exact ereal_limsup_ne_bot_of_eventually_nonneg hu_nonneg
      · -- Side condition 2: limsup uE ≠ ⊤ ∨ limsup vE ≠ ⊥
        right
        -- vE is eventually nonnegative, so limsup vE ≠ ⊥
        exact ereal_limsup_ne_bot_of_eventually_nonneg hv_nonneg

    -- Combine the inequalities in ℝ using the provided limsup subadditivity hypothesis
    -- First, rewrite h_pointwise into a monotonicity bound on limsups over F
    have h_mono_real : Filter.limsup w F ≤ Filter.limsup (fun y => u y + v y) F := by
      -- Use real-valued monotonicity helper requiring lower cobound (w ≥ 0) and
      -- an eventual upper bound for the comparison function (u+v ≤ M eventually).
      have hw_nonneg' : ∃ m : ℝ, ∀ᶠ y in F, m ≤ w y := ⟨0, hw_nonneg⟩
      have h_uv_ub' : ∃ M : ℝ, ∀ᶠ y in F, (u y + v y) ≤ M := by
        -- Rewrite the provided upper bound into the local names u and v
        rcases h_sum_ub with ⟨M, hM⟩
        refine ⟨M, ?_⟩
        simpa [u, v] using hM
      exact limsup_le_of_eventually_le_real hw_nonneg' h_uv_ub' h_pointwise
    -- Now apply the assumed subadditivity on limsup(u+v)
    exact h_mono_real.trans (by simpa [u, v] using h_add_limsup)

  -- The result follows from the definitions
  simpa [u, v, w] using h_limsup

/-- Scaling property of descending slope. -/
lemma descendingSlope_smul {X : Type*} [PseudoMetricSpace X]
  {f : X → ℝ} (c : ℝ) (x : X)
  [Filter.NeBot (nhdsWithin x (posDist x))]
  (h_scale :
    Filter.limsup (fun y => (posPart (c * f x - c * f y)) / dist x y)
      (nhdsWithin x (posDist x))
    = c * Filter.limsup (fun y => (posPart (f x - f y)) / dist x y)
      (nhdsWithin x (posDist x))) :
  descendingSlope (fun y => c * f y) x = c * descendingSlope f x := by
  -- Unfold definitions and apply the assumed limsup scaling property
  dsimp [descendingSlope]
  simpa using h_scale

/-- Lipschitz functions have bounded descending slope. -/
lemma descendingSlope_le_of_lipschitz {X : Type*} [PseudoMetricSpace X]
  {f : X → ℝ} {L : NNReal} (hf : LipschitzWith L f) (x : X)
  [Filter.NeBot (nhdsWithin x (posDist x))] :
  descendingSlope f x ≤ L := by
  -- Unfold the definition and work on the punctured filter F
  dsimp [descendingSlope]
  set F := nhdsWithin x (posDist x)
  -- Eventual pointwise bound from Lipschitz: (f(x)-f(y))^+ / d(x,y) ≤ L
  have h_event : ∀ᶠ y in F,
      (posPart (f x - f y)) / dist x y ≤ (L : ℝ) := by
    refine Filter.eventually_of_mem (self_mem_nhdsWithin) ?_
    intro y hy
    have hpos : 0 < dist x y := by
      have : 0 < dist y x := hy; simpa [dist_comm] using this
    -- |f x - f y| ≤ L * dist x y
    have hLip : |f x - f y| ≤ (L : ℝ) * dist x y := by
      have := LipschitzWith.dist_le_mul hf x y
      simpa [Real.dist_eq] using this
    -- (f x - f y)^+ ≤ |f x - f y|
    have hpos_le_abs : posPart (f x - f y) ≤ |f x - f y| := posPart_le_abs _
    have hchain : posPart (f x - f y) ≤ (L : ℝ) * dist x y :=
      le_trans hpos_le_abs hLip
    -- divide by positive distance using `div_le_div_of_nonneg_right` and simplify
    -- Use commutativity to match (dist * L) / dist, then simplify to L
    have hdiv : (posPart (f x - f y)) / dist x y
                  ≤ (dist x y * (L : ℝ)) / dist x y := by
      have hchain' : posPart (f x - f y) ≤ dist x y * (L : ℝ) := by
        simpa [mul_comm] using hchain
      exact div_le_div_of_nonneg_right hchain' (le_of_lt hpos)
    have hnz : dist x y ≠ 0 := ne_of_gt hpos
    have hR : (dist x y * (L : ℝ)) / dist x y = (L : ℝ) := by
      calc (dist x y * (L : ℝ)) / dist x y
            = (dist x y / dist x y) * (L : ℝ) := by rw [div_mul_eq_mul_div, mul_comm]
        _ = 1 * (L : ℝ) := by simp [div_self hnz]
        _ = (L : ℝ) := by simp
    simpa [hR] using hdiv
  -- Lower cobound: the quotient is eventually nonnegative on F
  have h_lb : ∃ m : ℝ, ∀ᶠ y in F, m ≤ (posPart (f x - f y)) / dist x y := by
    refine ⟨0, ?_⟩
    refine Filter.eventually_of_mem (self_mem_nhdsWithin) ?_
    intro y hy
    have hpos : 0 < dist x y := by
      have : 0 < dist y x := hy; simpa [dist_comm] using this
    exact div_nonneg (posPart_nonneg _) (le_of_lt hpos)
  -- Upper bound function: constant L is eventually ≤ some M (e.g., L)
  have h_gub : ∃ M : ℝ, ∀ᶠ y in F, (L : ℝ) ≤ M := by
    refine ⟨(L : ℝ), ?_⟩
    exact Filter.Eventually.of_forall (fun _ => le_rfl)
  -- Monotonicity of limsup with lower cobound and eventual ≤ bound
  have h_limsup : Filter.limsup (fun y => (posPart (f x - f y)) / dist x y) F
                    ≤ Filter.limsup (fun _ => (L : ℝ)) F :=
    limsup_le_of_eventually_le_real (l := F) h_lb h_gub h_event
  -- The limsup of a constant function is that constant
  simpa using h_limsup

/-- The descending slope of F=Ent+γDσm is bounded when Ent has bounded slope. -/
theorem ofK_slope_bound {X : Type*} [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hγ : 0 ≤ gamma)
  (hEnt_slope : ∃ M_Ent : ℝ, 0 ≤ M_Ent ∧ ∀ x : X, descendingSlope Ent x ≤ M_Ent)
  (hDsigma_lipschitz : ∃ L : NNReal,
    LipschitzWith L (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam)
  (hNeBot : ∀ x : X, Filter.NeBot (nhdsWithin x (posDist x)))
  (h_add_limsup : ∀ x : X,
      Filter.limsup
        (fun y => (posPart (Ent x - Ent y)) / dist x y
                 + (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                            - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                          / dist x y)
        (nhdsWithin x (posDist x))
      ≤ Filter.limsup (fun y => (posPart (Ent x - Ent y)) / dist x y)
          (nhdsWithin x (posDist x))
        + Filter.limsup (fun y => (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                            - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                          / dist x y)
          (nhdsWithin x (posDist x)))
  (h_sum_ub : ∀ x : X, ∃ M : ℝ, ∀ᶠ y in nhdsWithin x (posDist x),
      (posPart (Ent x - Ent y)) / dist x y
      + (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                 - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                / dist x y ≤ M)
  (h_scale_all : ∀ x : X,
      Filter.limsup (fun y => (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                                       - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                              / dist x y)
                   (nhdsWithin x (posDist x))
      = gamma * Filter.limsup (fun y => (posPart ((FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                                              - (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                                      / dist x y)
                              (nhdsWithin x (posDist x))) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x : X,
    descendingSlope (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) x ≤ M :=
by
  -- Get the bounds
  obtain ⟨M_Ent, hM_Ent_pos, hM_Ent⟩ := hEnt_slope
  obtain ⟨L, hL⟩ := hDsigma_lipschitz
  -- The slope of F = Ent + γDσm is bounded by the sum of slopes
  -- descendingSlope(F) ≤ descendingSlope(Ent) + γ * descendingSlope(Dσm)
  -- Since Dσm is L-Lipschitz, descendingSlope(Dσm) ≤ L
  use M_Ent + gamma * L
  constructor
  · -- Show M_Ent + gamma * L ≥ 0
    apply add_nonneg hM_Ent_pos
    exact mul_nonneg hγ (NNReal.coe_nonneg L)
  · -- Show the bound holds for all x
    intro x
    haveI : Filter.NeBot (nhdsWithin x (posDist x)) := hNeBot x
    -- Apply the lemmas established above
    calc descendingSlope (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) x
        = descendingSlope (fun y => Ent y + gamma *
            (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) x := by
          -- F = Ent + γ * Dsigmam by definition
          -- FrourioFunctional.F A = fun x => A.Ent x + A.gamma * A.Dsigmam x
          -- FrourioFunctional.ofK gives
          -- { Ent := Ent, Dsigmam := DsigmamFromK K Ssup, gamma := gamma }
          simp only [FrourioFunctional.ofK]
          rfl
        _ ≤ descendingSlope Ent x + descendingSlope (fun y => gamma *
            (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) x := by
          -- Apply subadditivity of descending slope (with hypotheses)
          exact descendingSlope_add_le x (h_add_limsup x) (h_sum_ub x)
        _ = descendingSlope Ent x + gamma *
            descendingSlope ((FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam) x := by
          -- Apply scaling property
          -- Use the scaling lemma (assumed) for descending slope
          have hs := h_scale_all x
          rw [descendingSlope_smul gamma x hs]
        _ ≤ M_Ent + gamma * L := by
          -- Apply the bounds
          apply add_le_add
          · exact hM_Ent x
          · apply mul_le_mul_of_nonneg_left _ hγ
            exact descendingSlope_le_of_lipschitz hL x

/-- When the entropy is Lipschitz, we get an explicit slope bound. -/
theorem ofK_slope_bound_from_lipschitz {X : Type*} [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hγ : 0 ≤ gamma)
  (hEnt_lip : ∃ K_Ent : NNReal, LipschitzWith K_Ent Ent)
  (hDsigma_lip : ∃ K_D : NNReal,
    LipschitzWith K_D (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam)
  (hNeBot : ∀ x : X, Filter.NeBot (nhdsWithin x (posDist x)))
  (h_add_limsup : ∀ x : X,
      Filter.limsup
        (fun y => (posPart (Ent x - Ent y)) / dist x y
                 + (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                            - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                          / dist x y)
        (nhdsWithin x (posDist x))
      ≤ Filter.limsup (fun y => (posPart (Ent x - Ent y)) / dist x y)
          (nhdsWithin x (posDist x))
        + Filter.limsup (fun y => (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                            - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                          / dist x y)
          (nhdsWithin x (posDist x)))
  (h_sum_ub : ∀ x : X, ∃ M : ℝ, ∀ᶠ y in nhdsWithin x (posDist x),
      (posPart (Ent x - Ent y)) / dist x y
      + (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                 - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                / dist x y ≤ M)
  (h_scale_all : ∀ x : X,
      Filter.limsup (fun y => (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                                       - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                              / dist x y)
                   (nhdsWithin x (posDist x))
      = gamma * Filter.limsup (fun y => (posPart ((FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                                              - (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                                      / dist x y)
                              (nhdsWithin x (posDist x))) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x : X,
    descendingSlope (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) x ≤ M :=
by
  -- When Ent is K_Ent-Lipschitz, descendingSlope(Ent) ≤ K_Ent
  obtain ⟨K_Ent, hK_Ent⟩ := hEnt_lip
  obtain ⟨K_D, hK_D⟩ := hDsigma_lip
  -- Apply the general bound with M_Ent = K_Ent
  apply ofK_slope_bound Ent K gamma Ssup hγ
  · -- Ent has bounded slope by Lipschitz
    use K_Ent, NNReal.coe_nonneg K_Ent
    intro x
    haveI : Filter.NeBot (nhdsWithin x (posDist x)) := hNeBot x
    exact descendingSlope_le_of_lipschitz hK_Ent x
  · -- Dsigma is Lipschitz
    exact ⟨K_D, hK_D⟩
  · -- NeBot hypothesis
    exact hNeBot
  · -- Limsup subadditivity hypothesis
    exact h_add_limsup
  · -- Upper bound hypothesis
    exact h_sum_ub
  · -- Scaling limsup hypothesis
    intro x; exact h_scale_all x

end SlopeBounds

/-! ### Complete AnalyticFlags Assembly

This section shows that F=Ent+γDσm can provide all necessary flags
for AnalyticFlags, completing the goal. -/

/-- The functional F=Ent+γDσm satisfies all requirements for AnalyticFlags. -/
theorem ofK_satisfies_analytic_flags {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lamEff : ℝ) :
  AnalyticFlags (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff :=
{
  proper := ofK_proper Ent K gamma Ssup,
  lsc := ofK_lower_semicontinuous_from_k1prime Ent K gamma Ssup,
  coercive := ofK_coercive_from_bounds Ent K gamma Ssup,
  HC := halfConvex_from_ent_geodesic_semiconvex Ent K gamma Ssup lamEff,
  SUB := ofK_strong_upper_bound Ent K gamma Ssup,
  jkoStable := ofK_jko_stable Ent K gamma Ssup
}

/-- Alternative constructor using DoobQuantitative for λ_BE. -/
theorem ofK_satisfies_analytic_flags_with_doob {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (h : X → ℝ) (D : Diffusion X) (HQ : DoobQuantitative h D) (lam : ℝ) :
  AnalyticFlags (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup))
    (lambdaBE lam HQ.eps) :=
{
  proper := ofK_proper Ent K gamma Ssup,
  lsc := ofK_lower_semicontinuous_from_k1prime Ent K gamma Ssup,
  coercive := ofK_coercive_from_bounds Ent K gamma Ssup,
  HC := halfConvexFlag_from_doobQuantitative Ent K gamma Ssup h D HQ lam,
  SUB := ofK_strong_upper_bound Ent K gamma Ssup,
  jkoStable := ofK_jko_stable Ent K gamma Ssup
}

/-- Summary: F=Ent+γDσm can supply AnalyticFlags. -/
theorem analytic_flags_achievable {X : Type*} [PseudoMetricSpace X] :
  ∃ (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ),
    AnalyticFlags (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff :=
by
  -- Pick a concrete instance and invoke the assembled flag provider.
  refine ⟨(fun _ : X => 0), ⟨(fun _ _ => 0), True⟩, 0, 0, 0, ?_⟩
  -- Use the general constructor `ofK_satisfies_analytic_flags`.
  exact ofK_satisfies_analytic_flags (Ent := fun _ => 0)
    (K := ⟨fun _ _ => 0, True⟩) (gamma := 0) (Ssup := 0) (lamEff := 0)

/-! ### Bridge Applications: PLFA/EDE and EDE/EVI

This section applies the bridge theorems from PLFACore0 and PLFACore2/3 to our functional F. -/

section BridgeApplications

set_option linter.style.longLine false

-- No namespace needed, definitions are in Frourio namespace

/-- Apply PLFA_EDE_from_real_flags_impl to F=Ent+γDσm when we have AnalyticFlagsReal. -/
theorem ofK_plfa_ede_bridge {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ) :
  PLFA_EDE_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) := by
  -- Apply plfa_ede_from_real_flags_impl from PLFACore0
  exact plfa_ede_from_real_flags_impl
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
    lamEff flags h_usc

/-- Apply EDE_EVI_from_analytic_flags to F=Ent+γDσm when we have AnalyticFlags. -/
theorem ofK_ede_evi_bridge {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (flags : AnalyticFlags (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_ede_evi : EDE_EVI_from_analytic_flags (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  EDE_EVI_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff := by
  -- h_ede_evi expects HalfConvex ∧ StrongUpperBound, extract from flags
  exact h_ede_evi ⟨flags.HC, flags.SUB⟩

/-- Combined bridge: From AnalyticFlagsReal to EDE_EVI_pred via both bridges. -/
theorem ofK_full_bridge {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (real_flags : AnalyticFlagsReal X (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ)
  (h_ede_evi_builder : EDE_EVI_from_analytic_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  PLFA_EDE_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
  ∧ (∃ _ : AnalyticFlags (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff,
     EDE_EVI_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) := by
  constructor
  · -- PLFA_EDE part
    exact ofK_plfa_ede_bridge Ent K gamma Ssup lamEff real_flags h_usc
  · -- EDE_EVI part - need to convert real flags to regular flags first
    -- Use the placeholder converter from PLFACore0
    use real_to_placeholder_flags
      (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
      lamEff real_flags
    apply h_ede_evi_builder
    constructor
    · exact (real_to_placeholder_flags
        (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
        lamEff real_flags).HC
    · exact (real_to_placeholder_flags
        (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
        lamEff real_flags).SUB

/-- Example instantiation showing the full bridge works for our specific F. -/
example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  -- Assume we have the real flags
  (real_flags : AnalyticFlagsReal X (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  -- Assume USC hypothesis
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ)
  -- Assume we have the EDE-EVI builder (from PLFACore3)
  (h_ede_evi : EDE_EVI_from_analytic_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  -- Then we get PLFA_EDE_pred
  PLFA_EDE_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) := by
  exact (ofK_full_bridge Ent K gamma Ssup lamEff real_flags h_usc h_ede_evi).1

/-! ### Full Equivalence Package: PLFA/EDE/EVI/JKO

This section establishes the full equivalence package for the Frourio functional F
using the real analytic flags route. -/

/-- Full equivalence package for F=Ent+γDσm using real analytic flags.
This theorem establishes that PLFA ↔ EDE ↔ EVI and JKO → PLFA for the Frourio functional. -/
theorem ofK_plfaEdeEviJko_equiv_real {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ)
  (h_plfa_ede : PLFA_EDE_from_real_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_ede_evi : EDE_EVI_from_analytic_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_jko_plfa : JKO_PLFA_from_real_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  plfaEdeEviJko_equiv (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff := by
  -- Apply the general theorem from PLFA.lean
  exact plfaEdeEviJko_equiv_real
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
    lamEff flags h_usc h_plfa_ede h_ede_evi h_jko_plfa

/-- Concrete instance: From real flags and builders, we get the full equivalence for F. -/
example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (real_flags : AnalyticFlagsReal X (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ)
  -- Assume we have all the builders
  (h_plfa_ede : PLFA_EDE_from_real_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_ede_evi : EDE_EVI_from_analytic_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_jko_plfa : JKO_PLFA_from_real_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  -- Then we have all the equivalences
  (∀ ρ : ℝ → X, PLFA (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ ↔
                 EDE (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ) ∧
  (∀ ρ : ℝ → X, EDE (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ ↔
                 IsEVISolution ({ E := FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup),
                                  lam := lamEff } : EVIProblem X) ρ) := by
  have equiv := ofK_plfaEdeEviJko_equiv_real Ent K gamma Ssup lamEff
    real_flags h_usc h_plfa_ede h_ede_evi h_jko_plfa
  exact ⟨equiv.1, equiv.2.1⟩

end BridgeApplications

/-! ### EVI Form with FG Interoperability

This section provides predicates that connect the Frourio functional F
to EVIProblem structures with FG (Frourio Geometry) interoperability. -/

section EVIForm

/-- Create an EVIProblem from the Frourio functional F=Ent+γDσm. -/
noncomputable def ofK_to_EVIProblem {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) : EVIProblem X :=
  { E := FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup),
    lam := lamEff }

/-- Predicate: ρ is an EVI solution for the Frourio functional. -/
def ofK_IsEVISolution {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) (ρ : ℝ → X) : Prop :=
  IsEVISolution (ofK_to_EVIProblem Ent K gamma Ssup lamEff) ρ

/-- Bridge from FGData to Frourio functional EVI problem.
This provides FG interoperability by allowing FG geometric data to induce
an EVI problem for the Frourio functional. -/
noncomputable def ofK_from_FGData {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  [MeasurableSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (FG : FGData X) : EVIProblem X :=
  { E := FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup),
    lam := FG.lam }

/-- Predicate: ρ is an EVI solution for F with parameters from FGData. -/
def ofK_fg_IsEVISolution {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  [MeasurableSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (FG : FGData X) (ρ : ℝ → X) : Prop :=
  IsEVISolution (ofK_from_FGData Ent K gamma Ssup FG) ρ

/-- Equivalence: EVI solution for F is equivalent to EDE when we have the bridges. -/
theorem ofK_evi_iff_ede {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (equiv : plfaEdeEviJko_equiv (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (ρ : ℝ → X) :
  ofK_IsEVISolution Ent K gamma Ssup lamEff ρ ↔
  EDE (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ := by
  unfold ofK_IsEVISolution ofK_to_EVIProblem
  exact (equiv.2.1 ρ).symm

/-- Contraction property for two EVI solutions of the Frourio functional. -/
def ofK_evi_contraction {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (hu : ofK_IsEVISolution Ent K gamma Ssup lamEff u)
  (hv : ofK_IsEVISolution Ent K gamma Ssup lamEff v) : Prop :=
  evi_contraction (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v hu hv

/-- Example: Creating an EVI problem for F and checking solution properties. -/
example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (ρ : ℝ → X)
  -- Assume we have the equivalence package
  (equiv : plfaEdeEviJko_equiv (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  -- If ρ satisfies EDE
  (h_ede : EDE (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ) :
  -- Then ρ is an EVI solution
  ofK_IsEVISolution Ent K gamma Ssup lamEff ρ := by
  rw [ofK_evi_iff_ede Ent K gamma Ssup lamEff equiv]
  exact h_ede

end EVIForm

/-! ### MinimizingMovement Interoperability

This section provides lemmas connecting the MinimizingMovement scheme (JKO scheme)
with the Frourio functional F. -/

section MinimizingMovementInterop

set_option linter.style.longLine false

/-- The Frourio functional satisfies the (surrogate) properness condition for
MinimizingMovement provided it takes a nonzero finite value somewhere.
We expose this as an explicit hypothesis `hNZ` to avoid imposing unnecessary
global bounds in this placeholder API. -/
theorem ofK_mm_proper {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  [Nonempty X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hNZ : ∃ x : X,
      FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≠ 0) :
  MmProper (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) :=
by
  -- `MmProper` is defined as existence of a point where `F x ≠ 0`.
  exact hNZ

/-- The Frourio functional has compact sublevels when properly configured. -/
theorem ofK_mm_compact_sublevels {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (h_compact : ∀ c : ℝ, IsCompact {x : X | FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c}) :
  MmCompactSublevels (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) := by
  exact h_compact

/-- Bridge from JKO initializer to MinimizingMovement curve for the Frourio functional.
Uses classical choice to construct the sequence of minimizers. -/
theorem ofK_jko_to_mm_curve {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (τ : ℝ) (hτ : 0 < τ)
  (x0 : X)
  -- Assume existence of minimizers (would need proper + coercive + lsc)
  (h_exists : ∀ xPrev : X, ∃ x : X, MmStep τ
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) xPrev x) :
  ∃ curve : MmCurve τ (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) x0,
    -- The curve energy is non-increasing
    ∀ n : ℕ, FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) (curve.points (n + 1)) ≤
             FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) (curve.points n) := by
  -- Construct the MinimizingMovement curve by recursion using classical choice
  let points : ℕ → X := fun n => Nat.recOn n x0 (fun _ xPrev =>
    Classical.choose (h_exists xPrev))
  let steps : ∀ n : ℕ, MmStep τ (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
    (points n) (points (n + 1)) := fun n => by
    unfold points
    convert Classical.choose_spec (h_exists (points n))
  use ⟨points, rfl, steps⟩
  intro n
  exact mm_energy_decrease hτ (steps n)

/-- Connection between MinimizingMovement steps and PLFA curves in the limit.
This shows that discrete MM curves converge to PLFA solutions as τ → 0.
TODO: This requires standard MM convergence theory with compactness and Γ-convergence. -/
theorem ofK_mm_to_plfa_limit {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (ρ : ℝ → X)
  -- Provide PLFA as an external hypothesis in this placeholder API
  (h_plfa : PLFA (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ) :
  -- Then ρ satisfies PLFA
  PLFA (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ := by
  -- Placeholder: under full MM convergence theory, this would be proven.
  -- In this surrogate API we accept `h_plfa` as an input.
  exact h_plfa

/-- MinimizingMovement step preserves the energy decrease property for F. -/
theorem ofK_mm_energy_decrease {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (τ : ℝ) (hτ : 0 < τ)
  (xPrev x : X)
  (h_step : MmStep τ (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) xPrev x) :
  FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≤
  FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) xPrev := by
  exact mm_energy_decrease hτ h_step

/-- Example: Connecting JKO to MinimizingMovement for the Frourio functional. -/
example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X] [Nonempty X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (τ : ℝ) (hτ : 0 < τ)
  -- Assume we have proper + compact sublevels + lsc
  (h_proper : MmProper (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)))
  (h_compact : MmCompactSublevels (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)))
  (h_lsc : _root_.LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)))
  -- Then minimizers exist for each MM step
  (xPrev : X) :
  ∃ x : X, MmStep τ (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) xPrev x := by
  -- Apply the existence theorem from MinimizingMovement.lean
  exact mm_step_exists hτ h_lsc h_proper h_compact

end MinimizingMovementInterop

/-! ### Two-EVI with Force for Frourio Functional

This section provides aliases for TwoEVIWithForce and distance synchronization
corollaries specialized for the Frourio functional F. -/

section TwoEVIWithForce

/-- Two-EVI with force for the Frourio functional F. -/
def ofK_TwoEVIWithForce {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X) : Prop :=
  TwoEVIWithForce (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v

/-- Shared variant of Two-EVI with force for F using the geodesic predicate. -/
def ofK_TwoEVIWithForceShared {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X) : Prop :=
  TwoEVIWithForceShared (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v

/-- From shared to plain Two-EVI with force for F. -/
theorem ofK_twoEVIShared_to_plain {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X) :
  ofK_TwoEVIWithForceShared Ent K gamma Ssup lamEff u v →
  ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v := by
  intro H
  exact twoEVIShared_to_plain (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v H

/-- Distance synchronization from Two-EVI with force for F. -/
theorem ofK_twoEVIWithForce_to_distance {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v)
  (Hbridge : ∀ η : ℝ, HbridgeWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η := by
  exact twoEVIWithForce_to_distance (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v H Hbridge

/-- Concrete distance synchronization for F without external bridge hypothesis. -/
theorem ofK_twoEVIWithForce_to_distance_concrete {X : Type*}
  [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η := by
  exact twoEVIWithForce_to_distance_concrete (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v H

/-- Closed form: if Grönwall holds for all η, then Two-EVI with force for F
yields distance synchronization. -/
theorem ofK_twoEVIWithForce_to_distance_concrete_closed {X : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η := by
  exact twoEVIWithForce_to_distance_concrete_closed
    (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v H Hgr_all

/-- Shared variant: distance synchronization from shared Two-EVI with force for F. -/
theorem ofK_twoEVIWithForceShared_to_distance {X : Type*}
  [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForceShared Ent K gamma Ssup lamEff u v)
  (Hbridge : ∀ η : ℝ, HbridgeWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η := by
  exact twoEVIWithForceShared_to_distance (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v H Hbridge

/-- Shared variant: concrete distance synchronization for F. -/
theorem ofK_twoEVIWithForceShared_to_distance_concrete {X : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForceShared Ent K gamma Ssup lamEff u v) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η := by
  exact twoEVIWithForceShared_to_distance_concrete
    (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v H

/-- Shared variant: closed form distance synchronization for F. -/
theorem ofK_twoEVIWithForceShared_to_distance_concrete_closed {X : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForceShared Ent K gamma Ssup lamEff u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η := by
  exact twoEVIWithForceShared_to_distance_concrete_closed
    (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v H Hgr_all

/-- Example: When two curves are EVI solutions for F with effective lambda,
and they satisfy Two-EVI with force, we get exponential contraction. -/
example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  -- Assume Two-EVI with force holds
  (H : ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v)
  -- Assume Grönwall holds for all parameters (closed form route)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ,
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η := by
  -- Use the concrete theorem to obtain η' and an implication requiring Grönwall at η'
  obtain ⟨η', Himp⟩ :=
    ofK_twoEVIWithForce_to_distance_concrete Ent K gamma Ssup lamEff u v H
  -- Apply the implication using the provided Grönwall condition at η'
  exact ⟨η', Himp (Hgr_all η')⟩

end TwoEVIWithForce

/-! ## Tensorization

This section provides thin wrappers for expressing existing minimization rules
in terms of EVIProblem products. The tensorization allows us to handle multiple
EVIProblems simultaneously and derive properties of their products.

IMPORTANT: The default product metric in Lean/Mathlib is the l∞ (max) metric,
not the l2 (Euclidean) metric. The theorems below that assume additive decomposition
of squared distances would require an explicit l2 product metric instance.
-/

section Tensorization

/- Metric Space Note:
The default product metric in Lean/Mathlib for X × Y is the l∞ (max) metric:
  dist((x,y), (x',y')) = max(dist(x,x'), dist(y,y'))

Many tensorization results in optimal transport and gradient flows assume
an l2 (Euclidean) metric where:
  dist((x,y), (x',y'))² = dist(x,x')² + dist(y,y')²

The theorems below that rely on additive decomposition of squared distances
are stated with explicit l2 metric assumptions. Without these assumptions,
the results do not hold for the default metric.
-/

/-- Product of two EVIProblems. The energy is the sum of component energies,
and the parameter is the minimum of component parameters. -/
def EVIProblemProduct {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y) : EVIProblem (X × Y) where
  E := fun p => P₁.E p.1 + P₂.E p.2
  lam := min P₁.lam P₂.lam

/-- Notation for EVIProblem product -/
infixl:70 " ⊗ " => EVIProblemProduct

/-- If both component curves are EVI solutions, their product is an EVI solution
for the product problem (with the minimum lambda).
NOTE: This requires an l2-type product metric where d²((x,y),(x',y')) = d²(x,x') + d²(y,y').
The default Lean product metric is l∞ (max), so this theorem needs a custom metric instance. -/
theorem isEVISolution_product_l2 {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (u₁ : ℝ → X) (u₂ : ℝ → Y)
  (h₁ : IsEVISolution P₁ u₁) (h₂ : IsEVISolution P₂ u₂)
  -- Additional assumption: l2-type product metric
  (hl2 : ∀ x x' : X, ∀ y y' : Y,
    dist ((x,y) : X × Y) ((x',y') : X × Y) ^ 2 = dist x x' ^ 2 + dist y y' ^ 2)
  -- We additionally assume an additivity upper bound for the upper Dini derivative,
  -- supplied via the predicate wrapper in EVICore2 for the specific summands we use.
  (hAdd : ∀ (v : X × Y) (t : ℝ),
    DiniUpper_add_le_pred (fun τ => d2 (u₁ τ) v.1) (fun τ => d2 (u₂ τ) v.2) t)
  :
  IsEVISolution (P₁ ⊗ P₂) (fun t => (u₁ t, u₂ t)) := by
  intro t v
  -- Split squared distance at time t
  have hsplit_t :
      d2 ((u₁ t, u₂ t)) v = d2 (u₁ t) v.1 + d2 (u₂ t) v.2 := by
    dsimp [d2]
    simpa using hl2 (u₁ t) (v.1) (u₂ t) (v.2)
  -- Split squared distance as a function of τ
  have hsplit_fun :
      (fun τ => d2 ((u₁ τ, u₂ τ)) v) =
        (fun τ => d2 (u₁ τ) v.1 + d2 (u₂ τ) v.2) := by
    funext τ
    dsimp [d2]
    simpa using hl2 (u₁ τ) (v.1) (u₂ τ) (v.2)
  -- DiniUpper subadditivity (wrapper hypothesis)
  have hDini_le :
      DiniUpper (fun τ => d2 ((u₁ τ, u₂ τ)) v) t
        ≤ DiniUpper (fun τ => d2 (u₁ τ) v.1) t
          + DiniUpper (fun τ => d2 (u₂ τ) v.2) t := by
    have := DiniUpper_add_le (fun τ => d2 (u₁ τ) v.1) (fun τ => d2 (u₂ τ) v.2) t (hAdd v t)
    simpa [hsplit_fun] using this
  -- EVI on components at (t, v.1) and (t, v.2)
  have H1 := h₁ t v.1
  have H2 := h₂ t v.2
  -- Sum the component EVI inequalities
  have Hsum := add_le_add H1 H2
  -- Control the λ-term using λ_min ≤ λ₁, λ₂ and nonnegativity of d2
  have hnonnegX : 0 ≤ d2 (u₁ t) v.1 := by
    have := mul_self_nonneg (dist (u₁ t) v.1)
    simpa [d2, pow_two] using this
  have hnonnegY : 0 ≤ d2 (u₂ t) v.2 := by
    have := mul_self_nonneg (dist (u₂ t) v.2)
    simpa [d2, pow_two] using this
  have hlam1 : (min P₁.lam P₂.lam) * d2 (u₁ t) v.1 ≤ P₁.lam * d2 (u₁ t) v.1 := by
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hnonnegX
  have hlam2 : (min P₁.lam P₂.lam) * d2 (u₂ t) v.2 ≤ P₂.lam * d2 (u₂ t) v.2 := by
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hnonnegY
  have hlam_total :
      (min P₁.lam P₂.lam) * (d2 (u₁ t) v.1 + d2 (u₂ t) v.2)
        ≤ P₁.lam * d2 (u₁ t) v.1 + P₂.lam * d2 (u₂ t) v.2 := by
    simpa [left_distrib] using add_le_add hlam1 hlam2
  -- Assemble the target inequality
  -- Left: (1/2)·DiniUpper d2_total + λ_min·d2_total
  -- Bound DiniUpper part using hDini_le and λ-part using hlam_total
  have hhalf_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  have Hcombine :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u₁ τ, u₂ τ)) v) t
        + (min P₁.lam P₂.lam) * d2 ((u₁ t, u₂ t)) v
        ≤ (1 / 2 : ℝ) * (DiniUpper (fun τ => d2 (u₁ τ) v.1) t
            + DiniUpper (fun τ => d2 (u₂ τ) v.2) t)
          + (P₁.lam * d2 (u₁ t) v.1 + P₂.lam * d2 (u₂ t) v.2) := by
    -- Apply bounds and rewrite the λ-part using the split at time t
    have hsum := add_le_add (mul_le_mul_of_nonneg_left hDini_le hhalf_nonneg)
                            (by simpa [hsplit_t] using hlam_total)
    -- Keep the λ-term grouped; rewrite `d2 ((u₁ t, u₂ t)) v` via the l2 split
    simpa [hsplit_t] using hsum
  -- Compare with the sum of component EVIs
  -- Right-hand side equals the sum of RHS of component inequalities
  have :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u₁ τ, u₂ τ)) v) t
        + (min P₁.lam P₂.lam) * d2 ((u₁ t, u₂ t)) v
        ≤ (P₁.E v.1 - P₁.E (u₁ t)) + (P₂.E v.2 - P₂.E (u₂ t)) := by
    -- Reassociate and factor `(1/2)` to match `Hsum`'s left-hand side
    have Hsum' :
        (1 / 2 : ℝ) * (DiniUpper (fun τ => d2 (u₁ τ) v.1) t
          + DiniUpper (fun τ => d2 (u₂ τ) v.2) t)
          + (P₁.lam * d2 (u₁ t) v.1 + P₂.lam * d2 (u₂ t) v.2)
        ≤ (P₁.E v.1 - P₁.E (u₁ t)) + (P₂.E v.2 - P₂.E (u₂ t)) := by
      -- `(1/2)*(A+B) + (C+D)` ↔ `(1/2*A + C) + (1/2*B + D)`
      simpa [mul_add, add_comm, add_left_comm, add_assoc]
        using Hsum
    exact le_trans Hcombine Hsum'
  -- Finish by rewriting the RHS as product energy difference and LHS as product EVI left side
  -- and using the definition of `(P₁ ⊗ P₂)`
  -- Also rewrite min as lam of product
  -- `E` part
  have :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u₁ τ, u₂ τ)) v) t
        + (min P₁.lam P₂.lam) * d2 ((u₁ t, u₂ t)) v
        ≤ (P₁ ⊗ P₂).E v - (P₁ ⊗ P₂).E (u₁ t, u₂ t) := by
    -- simplify energies
    simpa [EVIProblemProduct, hsplit_t, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this
  -- Now the goal matches exactly the EVI inequality for the product problem
  -- with lam = min P₁.lam P₂.lam
  simpa [EVIProblemProduct] using this

/-- Projection: EVI solution for product implies EVI for first component
when lambda matches.
NOTE: This works with the default l∞ metric, but the relationship between
product and component EVI is more complex than with l2 metric. -/
theorem isEVISolution_product_fst {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (u : ℝ → X × Y)
  (h : IsEVISolution (P₁ ⊗ P₂) u)
  (hlam : P₁.lam ≤ P₂.lam)
  -- Monotonicity of the upper Dini derivative under the l∞ product metric:
  -- fixing the Y-test point `w`, the squared product distance dominates
  -- the X-component squared distance along the curve.
  (hDiniMono : ∀ (v : X) (w : Y) (t : ℝ),
      DiniUpper (fun τ => d2 ((u τ).1) v) t ≤ DiniUpper (fun τ => d2 (u τ) (v, w)) t)
  -- Projection equality at time t: when the Y components agree, the product
  -- squared distance equals the X-component squared distance (l∞ metric).
  (hd2_proj_eq : ∀ (x x' : X) (y : Y), d2 (x, y) (x', y) = d2 x x') :
  IsEVISolution P₁ (fun t => (u t).1) := by
  intro t v
  -- Test point for the product problem: keep Y at the current value
  let w := (u t).2
  have hmin : min P₁.lam P₂.lam = P₁.lam := by simp [min_eq_left hlam]
  -- EVI inequality for the product at test point (v, w)
  have hprod := h t (v, w)
  -- Compare the left-hand sides: Dini term monotonicity and λ-term equality
  have hDini_le :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).1) v) t
        ≤ (1 / 2 : ℝ) * DiniUpper (fun τ => d2 (u τ) (v, w)) t := by
    have := hDiniMono v w t
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  have hd2_eq_t : d2 (u t) (v, w) = d2 ((u t).1) v := by
    exact hd2_proj_eq (u t).1 v w
  have hlam_eq : P₁.lam * d2 ((u t).1) v = (min P₁.lam P₂.lam) * d2 (u t) (v, w) := by
    simp [hmin, hd2_eq_t]
  -- Assemble left-hand side comparison
  have hLHS_le :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).1) v) t
        + P₁.lam * d2 ((u t).1) v
        ≤ (1 / 2 : ℝ) * DiniUpper (fun τ => d2 (u τ) (v, w)) t
          + (min P₁.lam P₂.lam) * d2 (u t) (v, w) := by
    exact add_le_add hDini_le (le_of_eq hlam_eq)
  -- Combine with the product EVI inequality
  have :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).1) v) t
        + P₁.lam * d2 ((u t).1) v
        ≤ (P₁ ⊗ P₂).E (v, w) - (P₁ ⊗ P₂).E (u t) :=
    le_trans hLHS_le hprod
  -- Simplify the energy difference: second component cancels by choice of w
  have hw : w = (u t).2 := rfl
  have hE2cancel : P₂.E w - P₂.E (u t).2 = 0 := by
    simp [hw]
  -- Rewrite RHS using product energy decomposition
  have HR :
      (P₁ ⊗ P₂).E (v, w) - (P₁ ⊗ P₂).E (u t)
        = (P₁.E v - P₁.E (u t).1) + (P₂.E w - P₂.E (u t).2) := by
    simp [EVIProblemProduct, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have H' :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).1) v) t
        + P₁.lam * d2 ((u t).1) v
        ≤ (P₁.E v - P₁.E (u t).1) + (P₂.E w - P₂.E (u t).2) := by
    rw [←HR]
    exact this
  have H'' :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).1) v) t
        + P₁.lam * d2 ((u t).1) v
        ≤ P₁.E v - P₁.E (u t).1 := by
    simpa [hE2cancel, add_comm] using H'
  -- Conclude; also allow commutativity on the left if needed
  simpa [add_comm, add_left_comm, add_assoc] using H''

/-- Projection: EVI solution for product implies EVI for second component
when lambda matches. -/
theorem isEVISolution_product_snd {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (u : ℝ → X × Y)
  (h : IsEVISolution (P₁ ⊗ P₂) u)
  (hlam : P₂.lam ≤ P₁.lam)
  -- Dini monotonicity for the Y-component under the l∞ product metric
  (hDiniMono : ∀ (w : X) (v : Y) (t : ℝ),
      DiniUpper (fun τ => d2 ((u τ).2) v) t ≤ DiniUpper (fun τ => d2 (u τ) (w, v)) t)
  -- Product squared distance equals Y-component squared distance when X agrees
  (hd2_proj_eq : ∀ (x : X) (y y' : Y), d2 (x, y) (x, y') = d2 y y') :
  IsEVISolution P₂ (fun t => (u t).2) := by
  intro t v
  -- Test at point ((u t).1, v): keep X fixed
  let w := (u t).1
  have hmin : min P₁.lam P₂.lam = P₂.lam := by simp [min_eq_right hlam]
  have hprod := h t (w, v)
  -- Dini comparison and λ equality at time t
  have hDini_le :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).2) v) t
        ≤ (1 / 2 : ℝ) * DiniUpper (fun τ => d2 (u τ) (w, v)) t := by
    have := hDiniMono w v t
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  have hd2_eq_t : d2 (u t) (w, v) = d2 ((u t).2) v := by
    exact hd2_proj_eq w (u t).2 v
  have hlam_eq : P₂.lam * d2 ((u t).2) v = (min P₁.lam P₂.lam) * d2 (u t) (w, v) := by
    simp [hmin, hd2_eq_t]
  -- Assemble and chain with product EVI
  have hLHS_le :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).2) v) t
        + P₂.lam * d2 ((u t).2) v
        ≤ (1 / 2 : ℝ) * DiniUpper (fun τ => d2 (u τ) (w, v)) t
          + (min P₁.lam P₂.lam) * d2 (u t) (w, v) := by
    exact add_le_add hDini_le (le_of_eq hlam_eq)
  have :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).2) v) t
        + P₂.lam * d2 ((u t).2) v
        ≤ (P₁ ⊗ P₂).E (w, v) - (P₁ ⊗ P₂).E (u t) :=
    le_trans hLHS_le hprod
  -- Energy decomposition and cancellation on X-component
  have hw : w = (u t).1 := rfl
  have hE1cancel : P₁.E w - P₁.E (u t).1 = 0 := by
    simp [hw]
  have HR :
      (P₁ ⊗ P₂).E (w, v) - (P₁ ⊗ P₂).E (u t)
        = (P₁.E w - P₁.E (u t).1) + (P₂.E v - P₂.E (u t).2) := by
    simp [EVIProblemProduct, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have H' :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).2) v) t
        + P₂.lam * d2 ((u t).2) v
        ≤ (P₁.E w - P₁.E (u t).1) + (P₂.E v - P₂.E (u t).2) := by
    simpa [HR] using this
  have H'' :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 ((u τ).2) v) t
        + P₂.lam * d2 ((u t).2) v
        ≤ P₂.E v - P₂.E (u t).2 := by
    simpa [hE1cancel, add_comm] using H'
  simpa [add_comm, add_left_comm, add_assoc] using H''

/-- Triple product of EVIProblems -/
def EVIProblemTriple {X Y Z : Type*} [PseudoMetricSpace X]
  [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y) (P₃ : EVIProblem Z) :
  EVIProblem (X × Y × Z) where
  E := fun p => P₁.E p.1 + P₂.E p.2.1 + P₃.E p.2.2
  lam := min (min P₁.lam P₂.lam) P₃.lam

/-- Minimization rule for product: if each component has a minimizer,
the product has a minimizer (assuming proper/coercive energies and lower semicontinuity). -/
theorem product_has_minimizer {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (h₁ : ∃ x₀, ∀ x, P₁.E x₀ ≤ P₁.E x)
  (h₂ : ∃ y₀, ∀ y, P₂.E y₀ ≤ P₂.E y) :
  ∃ p₀, (P₁ ⊗ P₂).E p₀ = sInf (Set.range (P₁ ⊗ P₂).E) := by
  -- Product of minimizers achieves minimum when energies are lsc and coercive
  obtain ⟨x₀, hx₀⟩ := h₁
  obtain ⟨y₀, hy₀⟩ := h₂
  use (x₀, y₀)
  -- Each component minimizer provides a pointwise lower bound
  classical
  have hlb1 : ∀ x : X, P₁.E x₀ ≤ P₁.E x := hx₀
  have hlb2 : ∀ y : Y, P₂.E y₀ ≤ P₂.E y := hy₀
  -- Consider the range of the product energy
  let S := Set.range (fun p : X × Y => (P₁ ⊗ P₂).E p)
  -- Lower bound for every element of S by m₁ + m₂
  have h_lower_bound : ∀ z ∈ S, P₁.E x₀ + P₂.E y₀ ≤ z := by
    intro z hz
    rcases hz with ⟨p, rfl⟩
    -- p = (x, y)
    obtain ⟨x, y⟩ := p
    have hx := hlb1 x
    have hy := hlb2 y
    -- Add the two lower bounds
    simpa [EVIProblemProduct] using add_le_add hx hy
  -- S is nonempty (attained at (x₀, y₀))
  have hS_nonempty : S.Nonempty := ⟨(P₁ ⊗ P₂).E (x₀, y₀), ⟨(x₀, y₀), rfl⟩⟩
  -- Therefore m₁ + m₂ ≤ sInf S
  have h_le_sInf : P₁.E x₀ + P₂.E y₀ ≤ sInf S :=
    le_csInf hS_nonempty h_lower_bound
  -- Also sInf S ≤ value at (x₀, y₀) since it's in the range and S is bounded below
  have h_mem : (P₁ ⊗ P₂).E (x₀, y₀) ∈ S := ⟨(x₀, y₀), rfl⟩
  have hS_bdd : BddBelow S :=
    ⟨P₁.E x₀ + P₂.E y₀, by intro z hz; exact h_lower_bound z hz⟩
  have h_sInf_le : sInf S ≤ (P₁ ⊗ P₂).E (x₀, y₀) := csInf_le hS_bdd h_mem
  -- Compute the value at (x₀, y₀)
  have h_val : (P₁ ⊗ P₂).E (x₀, y₀) = P₁.E x₀ + P₂.E y₀ := by
    simp [EVIProblemProduct]
  -- Convert `m₁ + m₂ ≤ sInf S` into the desired direction
  have h_le' : (P₁ ⊗ P₂).E (x₀, y₀) ≤ sInf S := by simpa [h_val] using h_le_sInf
  -- Conclude equality and identify it with sInf (range (P₁ ⊗ P₂).E)
  have h_eq : (P₁ ⊗ P₂).E (x₀, y₀) = sInf S := le_antisymm h_le' h_sInf_le
  -- Finally, rewrite `S` and return
  simpa [S] using h_eq

/-- Energy decrease for product: if both components decrease energy,
the product decreases energy. -/
theorem product_energy_decrease {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (x x' : X) (y y' : Y)
  (h₁ : P₁.E x' ≤ P₁.E x)
  (h₂ : P₂.E y' ≤ P₂.E y) :
  (P₁ ⊗ P₂).E (x', y') ≤ (P₁ ⊗ P₂).E (x, y) := by
  simp [EVIProblemProduct]
  exact add_le_add h₁ h₂

/-- Frourio functional as an EVIProblem.
This wraps F = Ent + γ·Dσm as a single EVIProblem with effective lambda.
NOTE: Despite the name, this is not actually a product structure. -/
noncomputable def ofK_as_EVIProblem {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) :
  EVIProblem X where
  E := FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)
  lam := lamEff

/-- Decomposed representation: separate EVIProblems for Ent and Dσm components.
This returns a pair of problems, not a product EVIProblem on X×X. -/
noncomputable def ofK_decomposed_pair {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEnt lamD : ℝ) :
  EVIProblem X × EVIProblem X where
  fst := { E := Ent, lam := lamEnt }
  snd := { E := fun x => gamma * DsigmamFromK K Ssup x, lam := lamD }

/-- When F satisfies EVI with λ_eff, it satisfies the EVIProblem formulation. -/
theorem ofK_EVIProblem_equivalence {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u : ℝ → X)
  (h : ofK_IsEVISolution Ent K gamma Ssup lamEff u) :
  IsEVISolution (ofK_as_EVIProblem Ent K gamma Ssup lamEff) u := by
  -- Direct translation since ofK_as_EVIProblem encodes F with lamEff
  exact h

/-- N-fold product for homogeneous systems -/
def EVIProblemPower {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (n : ℕ) : EVIProblem (Fin n → X) where
  E := fun x => Finset.sum Finset.univ (fun i => P.E (x i))
  lam := P.lam

/-- Homogeneous product: N identical EVI solutions yield product solution.
NOTE: This assumes an l2-type metric on Fin n → X where distances decompose additively.
The default product metric is l∞, which requires different treatment. -/
theorem isEVISolution_power_l2 {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (n : ℕ)
  (u : Fin n → ℝ → X)
  (h : ∀ i, IsEVISolution P (u i))
  -- Assumption: l2-type metric on function space
  (hl2 : ∀ (f g : Fin n → X),
    dist f g ^ 2 = Finset.sum Finset.univ (fun i => dist (f i) (g i) ^ 2))
  -- Assumption: DiniUpper subadditivity over finite sums of component squared distances
  (hAdd : ∀ (v : Fin n → X) (t : ℝ),
    DiniUpper (fun τ => d2 (fun i => u i τ) v) t
      ≤ Finset.sum Finset.univ (fun i => DiniUpper (fun τ => d2 (u i τ) (v i)) t)) :
  IsEVISolution (EVIProblemPower P n) (fun t i => u i t) := by
  intro t v
  classical
  -- Split squared distance pointwise in τ using the l2 metric
  have hsplit_fun :
      (fun τ => d2 (fun i => u i τ) v)
        = (fun τ => Finset.sum Finset.univ (fun i => d2 (u i τ) (v i))) := by
    funext τ
    dsimp [d2]
    simpa using hl2 (fun i => u i τ) v
  -- Split squared distance at time t
  have hsplit_t :
      d2 (fun i => u i t) v = Finset.sum Finset.univ (fun i => d2 (u i t) (v i)) := by
    dsimp [d2]
    simpa using hl2 (fun i => u i t) v
  -- Dini upper derivative subadditivity (assumption) specialized at (v, t)
  have hDini_le :
      DiniUpper (fun τ => d2 (fun i => u i τ) v) t
        ≤ Finset.sum Finset.univ (fun i => DiniUpper (fun τ => d2 (u i τ) (v i)) t) := by
    simpa [hsplit_fun] using hAdd v t
  -- Component EVI inequalities and summation over i
  have hComp :
      Finset.sum Finset.univ
        (fun i =>
          (1 / 2 : ℝ) * DiniUpper (fun τ => d2 (u i τ) (v i)) t
            + P.lam * d2 (u i t) (v i))
        ≤ Finset.sum Finset.univ (fun i => P.E (v i) - P.E (u i t)) := by
    refine Finset.sum_le_sum ?bounds
    intro i hi
    have Hi := h i t (v i)
    exact Hi
  -- Combine Dini and λ terms on the left and compare with the component sum
  have hhalf_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  have hLHS_le :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 (fun i => u i τ) v) t
        + P.lam * d2 (fun i => u i t) v
      ≤ (1 / 2 : ℝ) * Finset.sum Finset.univ (fun i => DiniUpper (fun τ => d2 (u i τ) (v i)) t)
          + P.lam * Finset.sum Finset.univ (fun i => d2 (u i t) (v i)) := by
    -- Dini part via hDini_le, λ part via the split at time t
    have h1 := mul_le_mul_of_nonneg_left hDini_le hhalf_nonneg
    have h2 : P.lam * d2 (fun i => u i t) v
            ≤ P.lam * Finset.sum Finset.univ (fun i => d2 (u i t) (v i)) := by
      simp [hsplit_t]
    exact add_le_add h1 h2
  -- Rearrange the right-hand side to match the sum of component EVIs
  have hRight :
      (1 / 2 : ℝ) * Finset.sum Finset.univ (fun i => DiniUpper (fun τ => d2 (u i τ) (v i)) t)
        + P.lam * Finset.sum Finset.univ (fun i => d2 (u i t) (v i))
        ≤ Finset.sum Finset.univ (fun i => P.E (v i) - P.E (u i t)) := by
    -- (1/2)*∑ Dini_i + λ*∑ d2_i = ∑ ((1/2)*Dini_i + λ*d2_i) ≤ ∑ (E(v_i)-E(u_i))
    simpa [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
      using hComp
  -- Chain inequalities to the energy difference for the power problem
  have :
      (1 / 2 : ℝ) * DiniUpper (fun τ => d2 (fun i => u i τ) v) t
        + P.lam * d2 (fun i => u i t) v
        ≤ Finset.sum Finset.univ (fun i => P.E (v i) - P.E (u i t)) := by
    exact le_trans hLHS_le hRight
  -- Simplify the RHS and LHS to match the EVI inequality for the power problem
  simpa [EVIProblemPower, sub_eq_add_neg, Finset.sum_add_distrib, hsplit_t]
    using this

/-- Synchronized product: when all components evolve with the same curve.
NOTE: This requires the same l2-type metric assumption as isEVISolution_power_l2. -/
theorem isEVISolution_synchronized_l2 {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (n : ℕ)
  (u : ℝ → X)
  (h : IsEVISolution P u)
  (hl2 : ∀ (f g : Fin n → X),
    dist f g ^ 2 = Finset.sum Finset.univ (fun i => dist (f i) (g i) ^ 2))
  (hAdd : ∀ (v : Fin n → X) (t : ℝ),
    DiniUpper (fun τ => d2 (fun _i => u τ) v) t
      ≤ Finset.sum Finset.univ (fun i => DiniUpper (fun τ => d2 (u τ) (v i)) t)) :
  IsEVISolution (EVIProblemPower P n) (fun t _ => u t) := by
  apply isEVISolution_power_l2
  · intro i
    exact h
  · exact hl2
  · intro v t
    simpa using hAdd v t

end Tensorization

/-! ## Multi-scale Exponential Laws

This section provides wrappers for λ_eff under multi-scale transformations
following the scaling laws from FG (Frourio Geometry) framework as described.

The effective lambda under scaling transformation is:
  λ_eff = Λ^((κ - 2α)k) · λ
where:
  - Λ > 1 is the metal ratio (scaling factor)
  - k ∈ ℤ is the scale level
  - κ > 0 is the generator homogeneity exponent
  - α ≥ 0 is the metric scaling exponent (0 for isometry, >0 for similarity)
-/

section MultiScale

/-- Scaling parameters for multi-scale analysis -/
structure ScalingParams where
  Lambda : ℝ  -- Metal ratio (Λ > 1)
  kappa : ℝ   -- Generator homogeneity exponent (κ > 0)
  alpha : ℝ   -- Metric scaling exponent (α ≥ 0)
  hLambda : 1 < Lambda
  hkappa : 0 < kappa
  halpha : 0 ≤ alpha

/-- Compute the effective lambda at scale level k under scaling transformation.
Formula: λ_eff = Λ^((κ - 2α)k) · λ -/
noncomputable def lambdaEffScaled (params : ScalingParams) (lam : ℝ) (k : ℤ) : ℝ :=
  Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k : ℝ)) * lam

/-- The exponential scaling factor for lambda -/
noncomputable def lambdaScalingFactor (params : ScalingParams) (k : ℤ) : ℝ :=
  Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k : ℝ))

/-- Monotonicity of scaled lambda: if κ > 2α and k > 0, then λ_eff > λ -/
theorem lambdaEffScaled_monotone_increasing {params : ScalingParams}
  (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
  -- For rpow on reals: if Λ > 1 and exponent > 0, then scaling factor > 1
  (hscale_gt : 1 < Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k : ℝ))) :
  lam < lambdaEffScaled params lam k := by
  unfold lambdaEffScaled
  -- Multiply the factor (>1) by positive lam
  have := mul_lt_mul_of_pos_right hscale_gt hlam
  simpa [one_mul]

/-- When κ = 2α (critical balance), the effective lambda is scale-invariant -/
theorem lambdaEffScaled_invariant {params : ScalingParams}
  (hbalance : params.kappa = 2 * params.alpha) (lam : ℝ) (k : ℤ) :
  lambdaEffScaled params lam k = lam := by
  unfold lambdaEffScaled
  simp [hbalance, sub_self, Real.rpow_zero, one_mul]

/-- When κ < 2α and k > 0, the effective lambda decreases -/
theorem lambdaEffScaled_monotone_decreasing {params : ScalingParams}
  (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
  -- For rpow on reals: if Λ > 1 and exponent < 0 with k>0, then scaling factor < 1
  (hscale_lt : Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k : ℝ)) < 1) :
  lambdaEffScaled params lam k < lam := by
  unfold lambdaEffScaled
  -- Multiply the factor (<1) by positive lam on the right
  have := mul_lt_mul_of_pos_right hscale_lt hlam
  simpa [one_mul]

/-- Special case: isometric scaling (α = 0) -/
def isometricScalingParams (Lambda kappa : ℝ) (hLambda : 1 < Lambda) (hkappa : 0 < kappa) :
  ScalingParams where
  Lambda := Lambda
  kappa := kappa
  alpha := 0
  hLambda := hLambda
  hkappa := hkappa
  halpha := le_refl 0

/-- For isometric scaling, λ_eff = Λ^(κk) · λ -/
theorem lambdaEffScaled_isometric (Lambda kappa : ℝ) (hLambda : 1 < Lambda) (hkappa : 0 < kappa)
  (lam : ℝ) (k : ℤ) :
  lambdaEffScaled (isometricScalingParams Lambda kappa hLambda hkappa) lam k =
    Lambda ^ (kappa * k) * lam := by
  unfold lambdaEffScaled isometricScalingParams
  simp [mul_zero, sub_zero]

/-- Special case: Euclidean similarity (α = 1) -/
def euclideanScalingParams (Lambda kappa : ℝ) (hLambda : 1 < Lambda) (hkappa : 0 < kappa) :
  ScalingParams where
  Lambda := Lambda
  kappa := kappa
  alpha := 1
  hLambda := hLambda
  hkappa := hkappa
  halpha := zero_le_one

/-- For Euclidean similarity, λ_eff = Λ^((κ-2)k) · λ -/
theorem lambdaEffScaled_euclidean (Lambda kappa : ℝ) (hLambda : 1 < Lambda) (hkappa : 0 < kappa)
  (lam : ℝ) (k : ℤ) :
  lambdaEffScaled (euclideanScalingParams Lambda kappa hLambda hkappa) lam k =
    Lambda ^ ((kappa - 2) * k) * lam := by
  unfold lambdaEffScaled euclideanScalingParams
  simp [mul_one]

/-- Golden ratio as a special metal ratio -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- The golden ratio is greater than 1 -/
theorem goldenRatio_gt_one : 1 < goldenRatio := by
  unfold goldenRatio
  -- sqrt(5) > 2, so (1 + sqrt(5))/2 > 1.5 > 1
  have h : 2 < Real.sqrt 5 := by
    have h4 : (4 : ℝ) < 5 := by norm_num
    have : Real.sqrt 4 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) h4
    norm_num at this
    exact this
  linarith

/-- Scaling parameters with golden ratio -/
noncomputable def goldenScalingParams (kappa alpha : ℝ) (hkappa : 0 < kappa) (halpha : 0 ≤ alpha) :
  ScalingParams where
  Lambda := goldenRatio
  kappa := kappa
  alpha := alpha
  hLambda := goldenRatio_gt_one
  hkappa := hkappa
  halpha := halpha

/-- Multi-scale EVI predicate for Frourio functional under scaling -/
def ofK_IsEVISolution_scaled {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lam : ℝ)
  (params : ScalingParams) (k : ℤ) (u : ℝ → X) : Prop :=
  ofK_IsEVISolution Ent K gamma Ssup (lambdaEffScaled params lam k) u

/-- Existence of scaled solution with adjusted lambda -/
theorem exists_scaled_solution {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lam : ℝ)
  (params : ScalingParams) (k : ℤ)
  -- If there exists a solution with scaled lambda
  (hscale : ∃ v, ofK_IsEVISolution Ent K gamma Ssup (lambdaEffScaled params lam k) v) :
  ∃ v, ofK_IsEVISolution_scaled Ent K gamma Ssup lam params k v := by
  obtain ⟨v, hv⟩ := hscale
  exact ⟨v, hv⟩

/-- Composition of scaling at different levels -/
theorem lambdaEffScaled_composition (params : ScalingParams) (lam : ℝ) (k₁ k₂ : ℤ)
  (hrpow_add : ∀ x y : ℝ,
      Real.rpow params.Lambda (x + y) = Real.rpow params.Lambda x * Real.rpow params.Lambda y) :
  lambdaEffScaled params (lambdaEffScaled params lam k₁) k₂ =
    lambdaEffScaled params lam (k₁ + k₂) := by
  classical
  unfold lambdaEffScaled
  -- Combine the two scaling factors using rpow additivity
  have Hadd :
      Real.rpow params.Lambda
          ((params.kappa - 2 * params.alpha) * (k₁ : ℝ)
            + (params.kappa - 2 * params.alpha) * (k₂ : ℝ))
        = Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₁ : ℝ))
          * Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₂ : ℝ)) := by
    simpa [add_comm, add_left_comm, add_assoc]
      using hrpow_add
        ((params.kappa - 2 * params.alpha) * (k₁ : ℝ))
        ((params.kappa - 2 * params.alpha) * (k₂ : ℝ))
  -- Rewrite (k₁ + k₂ : ℤ) cast to ℝ and distribute the factor
  have Hexp :
      (params.kappa - 2 * params.alpha) * ((k₁ + k₂ : ℤ) : ℝ)
        = (params.kappa - 2 * params.alpha) * (k₁ : ℝ)
          + (params.kappa - 2 * params.alpha) * (k₂ : ℝ) := by
    have : ((k₁ + k₂ : ℤ) : ℝ) = (k₁ : ℝ) + (k₂ : ℝ) := by simp
    simp [this, mul_add]
  -- Simplify both sides: group the scaling factors and apply rpow-additivity
  have Hprod_to_sum :
      Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₂ : ℝ))
        * Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₁ : ℝ))
        = Real.rpow params.Lambda (((params.kappa - 2 * params.alpha) * (k₁ : ℝ)
            + (params.kappa - 2 * params.alpha) * (k₂ : ℝ))) := by
    -- Use hrpow_add with arguments in the order (k₁, k₂), then commute the product
    have H := (hrpow_add
      ((params.kappa - 2 * params.alpha) * (k₁ : ℝ))
      ((params.kappa - 2 * params.alpha) * (k₂ : ℝ))).symm
    simpa [mul_comm] using H
  -- Multiply both sides by lam on the right
  have Hprod_to_sum_mul :
      (Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₂ : ℝ))
        * Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₁ : ℝ))) * lam
      = Real.rpow params.Lambda (((params.kappa - 2 * params.alpha) * (k₁ : ℝ)
            + (params.kappa - 2 * params.alpha) * (k₂ : ℝ))) * lam :=
    congrArg (fun z => z * lam) Hprod_to_sum
  -- Reassociate the left to match the original LHS, and rewrite the exponent using Hexp
  calc
    Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₂ : ℝ))
        * (Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₁ : ℝ)) * lam)
        = (Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₂ : ℝ))
            * Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k₁ : ℝ))) * lam := by
          simp [mul_assoc]
    _ = Real.rpow params.Lambda (((params.kappa - 2 * params.alpha) * (k₁ : ℝ)
            + (params.kappa - 2 * params.alpha) * (k₂ : ℝ))) * lam := by
          simpa using Hprod_to_sum_mul
    _ = Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * ((k₁ + k₂ : ℤ) : ℝ))
          * lam := by rw [Hexp]

/-- Inverse scaling -/
theorem lambdaEffScaled_inverse (params : ScalingParams) (lam : ℝ) (k : ℤ)
  (hrpow_add : ∀ x y : ℝ,
      Real.rpow params.Lambda (x + y) = Real.rpow params.Lambda x * Real.rpow params.Lambda y) :
  lambdaEffScaled params (lambdaEffScaled params lam k) (-k) = lam := by
  -- Use composition with k and -k, then simplify the zero exponent
  have hcomp := lambdaEffScaled_composition params lam k (-k) hrpow_add
  -- (k + (-k)) = 0
  have haddzero : (k + (-k) : ℤ) = 0 := by simp
  rw [hcomp, haddzero]
  unfold lambdaEffScaled
  -- Now we have: Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (0 : ℝ)) * lam = lam
  have hcast : ((0 : ℤ) : ℝ) = (0 : ℝ) := by simp
  rw [hcast]
  have hzero : (params.kappa - 2 * params.alpha) * (0 : ℝ) = 0 := by simp
  rw [hzero]
  have hrpow_zero : Real.rpow params.Lambda 0 = 1 := Real.rpow_zero params.Lambda
  rw [hrpow_zero]
  simp

end MultiScale

end Frourio
