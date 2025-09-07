import Frourio.Algebra.Properties
import Frourio.Algebra.StructureSequence
import Frourio.Algebra.CrossedProduct
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Frourio.Analysis.PLFA.PLFA
import Frourio.Analysis.MinimizingMovement
import Frourio.Analysis.FrourioFunctional
import Frourio.Analysis.DoobTransform
import Frourio.Geometry.GradientFlowFramework
import Frourio.Geometry.FGTheorems.FGTheorems

namespace Frourio

/-- 黄金比の基本性質 -/
lemma golden_ratio_property : φ^2 = φ + 1 := by
  -- φ = (1 + √5)/2 を用いた計算
  have hmul := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) 5)
  -- rewrite to exponent form for easier substitution
  have hsq : (Real.sqrt 5)^2 = (5 : ℝ) := by
    calc
      (Real.sqrt 5)^2 = (Real.sqrt 5) * (Real.sqrt 5) := by simp [pow_two]
      _ = (5 : ℝ) := hmul
  have h1 : φ^2 = ((1 + Real.sqrt 5)^2) / 4 := by
    have htmp : ((1 + Real.sqrt 5) / 2)^2 = ((1 + Real.sqrt 5)^2) / 4 := by
      ring
    simpa [φ] using htmp
  have h2 : φ + 1 = (3 + Real.sqrt 5) / 2 := by
    have htmp : (1 + Real.sqrt 5) / 2 + 1 = (3 + Real.sqrt 5) / 2 := by
      ring
    simpa [φ] using htmp
  calc
    φ^2
        = ((1 + Real.sqrt 5)^2) / 4 := h1
    _   = (1 + 2 * Real.sqrt 5 + (Real.sqrt 5)^2) / 4 := by ring
    _   = (1 + 2 * Real.sqrt 5 + 5) / 4 := by simp [hsq]
    _   = (6 + 2 * Real.sqrt 5) / 4 := by ring
    _   = (3 + Real.sqrt 5) / 2 := by ring
    _   = φ + 1 := by simp [h2]

/-- 黄金比は正 -/
lemma phi_pos : 0 < φ := by
  -- φ = (1 + √5) / 2 > 0
  have h₁ : 0 < 1 + Real.sqrt 5 := by
    have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  have h₂ : 0 < (2 : ℝ) := by norm_num
  have : 0 < (1 + Real.sqrt 5) / 2 := div_pos h₁ h₂
  simpa [φ] using this

/-- 黄金比の逆数：φ⁻¹ = φ - 1 -/
lemma phi_inv : φ⁻¹ = φ - 1 := by
  have hφ : φ ^ 2 = φ + 1 := golden_ratio_property
  have hne : φ ≠ 0 := ne_of_gt phi_pos
  -- φ*(φ-1) = 1
  have hmul : φ * (φ - 1) = 1 := by
    have h' : φ * φ = φ + 1 := by simpa [pow_two] using hφ
    calc
      φ * (φ - 1) = φ * φ - φ := by ring
      _ = (φ + 1) - φ := by simp [h']
      _ = 1 := by simp
  -- (φ-1) = φ⁻¹
  have hmul' : (φ - 1) * φ = 1 := by simpa [mul_comm] using hmul
  have : (φ - 1) * φ * φ⁻¹ = 1 * φ⁻¹ := congrArg (fun t => t * φ⁻¹) hmul'
  have : (φ - 1) = φ⁻¹ := by simp [hne] at this; simpa using this
  simp [this]

/-- 具体例：S_1(φ) = φ - 1/φ -/
example : S φ (1 : ℤ) = φ - 1 / φ := by
  simp [Frourio.S_one]

/-- 具体例：S_1(φ) = 1 -/
example : S φ (1 : ℤ) = 1 := by
  calc
    S φ (1 : ℤ) = φ - 1 / φ := by simp [Frourio.S_one]
    _ = φ - φ⁻¹ := by simp [one_div]
    _ = φ - (φ - 1) := by simp [phi_inv]
    _ = 1 := by ring

/-- 具体例：S_2(φ) = φ -/
lemma S_phi_two : S φ (2 : ℤ) = 2 * φ - 1 := by
  -- S φ 2 = φ^2 - (φ⁻¹)^2
  have hcalc : S φ (2 : ℤ) = φ ^ 2 - (φ⁻¹) ^ 2 := by
    simp [S, zpow_ofNat, zpow_neg]
  -- φ^2 = φ + 1, φ⁻¹ = φ - 1
  have : S φ (2 : ℤ) = (φ + 1) - (φ - 1) ^ 2 := by
    simp [hcalc, golden_ratio_property, phi_inv]
  -- (φ - 1)^2 = 2 - φ を経由して計算
  have hsq : (φ - 1) ^ 2 = 2 - φ := by
    have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
    calc
      (φ - 1) ^ 2 = φ ^ 2 - 2 * φ + 1 := by ring
      _ = (φ + 1) - 2 * φ + 1 := by simp [hφ2]
      _ = 2 - φ := by ring
  calc
    S φ (2 : ℤ) = (φ + 1) - (φ - 1) ^ 2 := this
    _ = φ + 1 - (2 - φ) := by simp [hsq]
    _ = 2 * φ - 1 := by ring

/-- 黄金Frourio作用素のMellin記号 -/
noncomputable def goldenMellinSymbol (s : ℂ) : ℂ :=
  mellinSymbol GoldenFrourioOperator s

/-- 3点Frourio作用素の例 -/
noncomputable def ThreePointExample (δ : ℝ) (hδ : 0 < δ) : FrourioOperator 3 :=
  { α := fun _ => (1 : ℂ)
  , χ := fun _ => Sign.pos
  , Λ := fun i => δ ^ (i.1 + 1)
  , Λ_pos := by
      intro i
      -- pow_pos は自然数乗に対して正の値を保つ
      exact pow_pos hδ (i.1 + 1)
  }

/-- 交叉積の自明作用における簡単な計算例（m=2, Λ=φ）。 -/
example :
    CrossedProduct.mul (trivialZmAction ℝ 2)
      { base := φ, scales := fun _ => (0 : ℤ) }
      { base := 1, scales := fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0 }
      =
      { base := φ, scales := fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0 } := by
  -- 自明作用では base は通常の積、scales は加法
  have hzero : (fun _ : Fin 2 => (0 : ℤ)) = (0 : Fin 2 → ℤ) := rfl
  simp [CrossedProduct.mul, trivialZmAction, φ, hzero]

end Frourio

/-!
Basic 1D example: from an initial value to JKO, then to EDE and EVI.

We take `X := ℝ`, the energy `F := fun _ => 0`, and `λ_eff := 0`.
For a constant curve `ρ t = ρ0`, JKO and EDE are immediate, and EVI holds
trivially since the squared distance to any fixed `v` is constant in time.
-/

namespace FrourioExamples

open Frourio

section Basic1D
variable (ρ0 : ℝ)

noncomputable def F : ℝ → ℝ := fun _ => 0
noncomputable def lamEff : ℝ := 0

noncomputable def rho : ℝ → ℝ := fun _t => ρ0

/-- JKO witness: the constant curve at `ρ0`. -/
theorem basic1D_JKO : JKO F ρ0 := by
  refine ⟨rho ρ0, rfl, ?_⟩
  intro t; simp [F]

/-- EDE holds for the constant curve and constant energy. -/
theorem basic1D_EDE : EDE F (rho ρ0) := by
  intro t
  have h : DiniUpperE (fun _ => (0 : ℝ)) t = (0 : EReal) := by
    -- forward difference quotient is identically 0
    simp [Frourio.DiniUpperE]
  -- conclude `0 ≤ 0`
  simp [F, h]

/-- EVI holds for the constant curve when `λ_eff = 0`. -/
theorem basic1D_EVI :
  IsEVISolution ({ E := F, lam := lamEff } : EVIProblem ℝ) (rho ρ0) := by
  intro t v
  -- The squared distance to `v` is constant along a constant curve.
  have hDu : DiniUpper (fun τ => d2 ((rho ρ0) τ) v) t = 0 := by
    simp [Frourio.DiniUpper, rho, d2]
  have hconst : DiniUpper (fun _ => d2 ρ0 v) t = 0 := by
    simp [Frourio.DiniUpper, d2]
  -- Plug into the EVI inequality with zero energy and zero λ.
  simp [F, lamEff, rho, hconst]

/-- Integrated existence: from `ρ0`, there exists a curve realizing JKO, EDE, EVI. -/
theorem basic1D_chain :
  ∃ ρ : ℝ → ℝ, ρ 0 = ρ0 ∧ JKO F ρ0 ∧ EDE F ρ ∧
    IsEVISolution ({ E := F, lam := lamEff } : EVIProblem ℝ) ρ := by
  refine ⟨rho ρ0, rfl, ?_, ?_, ?_⟩
  · exact basic1D_JKO ρ0
  · exact basic1D_EDE ρ0
  · exact basic1D_EVI ρ0

end Basic1D

end FrourioExamples

/-!
Quadratic energy example on ℝ: closed‑form MM step and a chain to EVI via a
package equivalence. This showcases the MM functional with `F(x) = (1/2) x^2`.
-/

namespace FrourioExamplesQuadratic

open Frourio

section Quadratic
variable (τ xPrev : ℝ)

/-- Quadratic energy `F(x) = (1/2) x^2`. -/
noncomputable def Fq : ℝ → ℝ := fun x => (1 / 2) * x ^ (2 : ℕ)

/-- Closed‑form MM minimizer for the quadratic energy on ℝ:
`x* = xPrev / (1 + τ)` minimizes `F(x) + (1/(2τ))‖x − xPrev‖^2` when `τ > 0`. -/
theorem quadratic_mm_step_closed_form (hτ : 0 < τ) :
  MmStep τ (Fq) xPrev (xPrev / (1 + τ)) := by
  -- Unfold definitions and complete the square.
  unfold MmStep IsMinimizer MmFunctional
  intro y
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have h1τ : 1 + τ ≠ 0 := by
    have : 0 < 1 + τ := by linarith
    exact ne_of_gt this
  -- Rewrite the distance square on ℝ.
  have hdist : distSquared y xPrev
      = (y - xPrev) ^ (2 : ℕ) := by
    dsimp [distSquared]
    -- `dist y xPrev = |y - xPrev|` on ℝ and `|·|^2 = (·)^2`.
    have habsSq : (|y - xPrev| : ℝ) ^ (2 : ℕ) = (y - xPrev) ^ (2 : ℕ) := by
      -- `|a|^2 = a^2` as `|a|*|a| = a*a` via `abs_mul_self`.
      simp [pow_two]
    simp [Real.dist_eq, habsSq]
  -- Define the candidate minimizer.
  set xStar : ℝ := xPrev / (1 + τ)
  -- Similar rewrite for `distSquared xStar xPrev`.
  have hdistStar : distSquared xStar xPrev = (xStar - xPrev) ^ (2 : ℕ) := by
    dsimp [distSquared]
    have habsSq : (|xStar - xPrev| : ℝ) ^ (2 : ℕ) = (xStar - xPrev) ^ (2 : ℕ) := by
      simp [pow_two]
    simp [Real.dist_eq, habsSq]
  -- Show the completing‑the‑square identity: f(y) = f(x*) + c · (y − x*)^2.
  have hcs :
      (Fq y) + (1 / (2 * τ)) * distSquared y xPrev
        = (Fq xStar) + (1 / (2 * τ)) * distSquared xStar xPrev
          + ((τ + 1) / (2 * τ)) * (y - xStar) ^ (2 : ℕ) := by
    -- Expand both sides as polynomials in y and compare.
    dsimp [Fq]
    -- Replace `distSquared` by a pure square.
    simp [hdist, hdistStar, pow_two, xStar]
    -- Clear denominators and normalize.
    -- `field_simp` uses the nonzero facts for τ and (1+τ).
    field_simp [hτ0, h1τ]; ring
  -- From the identity, deduce the minimizer property since the square term ≥ 0.
  have hnonneg : 0 ≤ ((τ + 1) / (2 * τ)) * (y - xStar) ^ (2 : ℕ) := by
    have hc : 0 ≤ ((τ + 1) / (2 * τ)) := by
      have : 0 < (τ + 1) / (2 * τ) := by
        have hpos : 0 < 2 * τ := by nlinarith
        have : 0 < (τ + 1) := by linarith
        exact div_pos this hpos
      exact le_of_lt this
    have hsq : 0 ≤ (y - xStar) ^ (2 : ℕ) := by
      have : 0 ≤ (y - xStar) ^ 2 := by exact pow_two_nonneg (y - xStar)
      simpa using this
    exact mul_nonneg hc hsq
  -- Conclude `f(x*) ≤ f(y)`.
  -- Turn the identity into the desired inequality `f(x*) ≤ f(y)`.
  -- Rearranged form of `hcs` to match the goal shape.
  have hcs' :
      (Fq xStar)
        + (((τ + 1) / (2 * τ)) * (y - xStar) ^ (2 : ℕ)
            + (1 / (2 * τ)) * distSquared xStar xPrev)
      = (Fq y) + (1 / (2 * τ)) * distSquared y xPrev := by
    simpa [add_comm, add_left_comm, add_assoc] using hcs.symm
  calc
    (Fq xStar) + (1 / (2 * τ)) * distSquared xStar xPrev
        ≤ (Fq xStar) + (1 / (2 * τ)) * distSquared xStar xPrev
            + ((τ + 1) / (2 * τ)) * (y - xStar) ^ (2 : ℕ) :=
      le_add_of_nonneg_right hnonneg
    _ = (Fq xStar)
          + (((τ + 1) / (2 * τ)) * (y - xStar) ^ (2 : ℕ)
              + (1 / (2 * τ)) * distSquared xStar xPrev) := by
      ring
    _ = (Fq y) + (1 / (2 * τ)) * distSquared y xPrev := hcs'

/-- Trivial JKO witness for the quadratic energy: the constant curve. -/
theorem quadratic_JKO (x0 : ℝ) : JKO (Fq) x0 := by
  refine ⟨fun _ => x0, rfl, ?_⟩
  intro t; simp [Fq]

/-- With a packaged `PLFA = EDE = EVI = JKO` equivalence for `Fq`, a JKO initializer
produces an EVI solution (example chain). -/
theorem chain_quadratic_to_EVI (lamEff : ℝ)
  (G : Frourio.plfaEdeEviJko_equiv (Fq) lamEff)
  (x0 : ℝ) :
  ∃ ρ : ℝ → ℝ, ρ 0 = x0 ∧ IsEVISolution ({ E := Fq, lam := lamEff } : EVIProblem ℝ) ρ :=
by
  -- Use the generic `jko_to_evi` from the analysis layer with the trivial JKO witness.
  -- Use implicit `τ, xPrev` from the section for `quadratic_JKO`.
  exact Frourio.jko_to_evi (F := Fq) lamEff G x0 (quadratic_JKO x0)

end Quadratic

end FrourioExamplesQuadratic

/-!
FG8-style examples: demonstrate how to apply the integrated suite,
effective-λ lower bound, and two‑EVI with force wrappers added in
FGTheorems. These are statement-level demos parameterized by the
corresponding assumptions.
-/

namespace FrourioExamplesFG8

open Frourio

section FG8Demos
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

variable (S : GradientFlowSystem X)

/-- Demo: Run the integrated gradient-flow suite via the real-route auto wrapper.
Supply real analytic flags for `F := Ent + γ·Dσm`, an EDE⇔EVI builder on
analytic flags, an effective-λ lower-bound witness, and a two‑EVI with
force hypothesis. -/
theorem demo_flow_suite_real_auto
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HedeEvi_builder : EDE_EVI_from_analytic_flags
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  exact Frourio.flow_suite_from_real_flags_auto S flags HedeEvi_builder hLam Htwo

/-- Demo: Construct `λ_eff` lower bound from Doob+m‑point hypotheses using
the FG-level convenience wrapper. -/
theorem demo_lambda_eff_from_doob
  (h : X → ℝ) (D : Diffusion X) (H : DoobAssumptions h D)
  (hM : MPointZeroOrderBound S.Ssup S.XiNorm)
  (hB : BudgetNonneg S.budget)
  (hg : 0 ≤ S.func.gamma) :
  lambda_eff_lower S :=
by
  exact Frourio.lambda_eff_lower_from_doob S h D H hM hB hg

/-- Demo: From `two_evi_with_force S`, obtain a distance synchronization with error
for any pair of curves `u, v` via the concrete Grönwall route. -/
theorem demo_twoEVI_concrete
  (Htwo : two_evi_with_force S) (u v : ℝ → X) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred S.base.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v η :=
by
  exact Frourio.two_evi_with_force_to_distance_concrete S Htwo u v

/-- Demo (closed form): if the Grönwall predicate holds for all `η`, then obtain
an error parameter with a distance synchronization bound. -/
theorem demo_twoEVI_concrete_closed
  (Htwo : two_evi_with_force S) (u v : ℝ → X)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred S.base.lam η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v η :=
by
  exact Frourio.two_evi_with_force_to_distance_concrete_closed S Htwo u v Hgr_all

end FG8Demos

end FrourioExamplesFG8
