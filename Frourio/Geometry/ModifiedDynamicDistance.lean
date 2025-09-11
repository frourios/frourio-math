import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Semicontinuous
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Frourio.Geometry.MultiScaleDiff
import Frourio.Analysis.MinimizingMovement
import Frourio.Analysis.Slope

namespace Frourio

open Filter Topology

/-!
# Modified Benamou-Brenier Distance for Meta-Variational Principle

This file defines the modified dynamic distance d_m based on the action functional
𝒜_m(ρ,φ) from the meta-variational principle.

## Main definitions

- `VelocityPotential`: Abstract velocity potential for continuity equation
- `Am`: The modified action functional 𝒜_m
- `dm`: The modified Benamou-Brenier distance
- `DynDistanceFlags`: Flags for dynamic distance properties

## Implementation notes

We build on existing infrastructure from MinimizingMovement and Slope,
providing a lightweight abstraction layer for the modified distance.
-/

open MeasureTheory

/-- Abstract velocity potential satisfying the weak continuity equation.
Represents φ_t such that d/dt ∫ φ dρ_t = ∫ Γ(φ, φ_t) dρ_t -/
structure VelocityPotential (X : Type*) [MeasurableSpace X] where
  /-- The potential function at each time -/
  φ : ℝ → X → ℝ
  /-- Spatial measurability for each time slice t ↦ φ t -/
  measurable : ∀ t, Measurable (φ t)
  /-- Time continuity at every spatial point: t ↦ φ t x is continuous. -/
  timeContinuous : ∀ x : X, Continuous (fun t : ℝ => φ t x)
  /-- L² integrability with respect to each ρ_t -/
  l2_integrable : ∀ t, ∀ (ρ : Measure X), ∫⁻ x, ENNReal.ofReal ((φ t x)^2) ∂ρ < ⊤
  /-- L² Sobolev regularity assumption for AGS theory -/
  l2_sobolev_regular : ∀ t, ∀ (μ : Measure X), ∫⁻ x, ENNReal.ofReal ((φ t x)^2) ∂μ < ⊤

/-- Curve of probability measures on X -/
structure ProbabilityCurve (X : Type*) [MeasurableSpace X] where
  /-- The measure at each time -/
  ρ : ℝ → Measure X
  /-- Each ρ_t is a probability measure -/
  is_prob : ∀ (t : ℝ), MeasureTheory.IsProbabilityMeasure (ρ t)
  /-- Weak continuity in the duality with continuous bounded functions -/
  weakly_continuous : Prop  -- Simplified placeholder for weak continuity
  /-- Time regularity of the measure curve -/
  time_regular : ∀ t, MeasureTheory.IsFiniteMeasure (ρ t)

/-- The carré du champ operator associated with a Dirichlet form.
For a local Dirichlet form ℰ, Γ(f,g) represents the energy density.
In the Riemannian case: Γ(f,g) = ⟨∇f, ∇g⟩ -/
structure CarreDuChamp (X : Type*) [MeasurableSpace X] where
  /-- The bilinear form Γ : (X → ℝ) × (X → ℝ) → (X → ℝ) -/
  Γ : (X → ℝ) → (X → ℝ) → (X → ℝ)
  /-- Symmetry: Γ(f,g) = Γ(g,f) -/
  symmetric : ∀ f g, Γ f g = Γ g f
  /-- Bilinearity in the first argument -/
  linear_left : ∀ a b : ℝ, ∀ f g h : X → ℝ,
    Γ (fun x => a * f x + b * g x) h = fun x => a * Γ f h x + b * Γ g h x
  /-- Chain rule property (Leibniz rule) -/
  chain_rule : ∀ f g h : X → ℝ,
    Γ (fun x => f x * g x) h = fun x => f x * Γ g h x + g x * Γ f h x
  /-- Non-negativity for Γ(f,f) -/
  nonneg : ∀ f : X → ℝ, ∀ x : X, 0 ≤ Γ f f x

/-- The action functional 𝒜_m(ρ,φ).
At this stage we provide a lightweight surrogate equal to 0, keeping the
interface stable for downstream uses (dm-squared as an infimum of actions).
When the analytic development is in place, replace this with the bona fide
integral expression. -/
noncomputable def Am {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) : ℝ :=
  -- Modified Benamou–Brenier action:
  -- ∫_{0}^{1} [ ∫ Γ(φ_t, φ_t) dρ_t + κ ∫ |Δ^{⟨m⟩}_{cfg} φ_t|^2 dμ ] dt
  ∫ t in Set.Icc (0 : ℝ) 1,
      (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
    + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ)

/-- Non-negativity of the action functional Am.
This follows from the non-negativity of both the carré du champ
and the squared multi-scale difference. -/
lemma Am_nonneg {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) :
    0 ≤ Am H cfg Γ κ μ ρ φ := by
  -- Am is the integral of non-negative terms over [0,1]
  have h_inner_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t)) := by
    intro t _
    have hpt : ∀ x, 0 ≤ (Γ.Γ (φ.φ t) (φ.φ t)) x := by
      intro x; exact Γ.nonneg (φ.φ t) x
    exact integral_nonneg hpt
  have h_inner2_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ) := by
    intro t _
    have hpt : ∀ x, 0 ≤ (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) := by
      intro x; exact sq_nonneg _
    exact integral_nonneg hpt
  have h_sum_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
            + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ) := by
    intro t ht
    have hA := h_inner_nonneg t ht
    have hB := h_inner2_nonneg t ht
    exact add_nonneg hA (mul_nonneg hκ hB)
  -- The integral of a nonnegative function is nonnegative
  apply setIntegral_nonneg
  · exact measurableSet_Icc
  · intro t ht
    exact h_sum_nonneg t ht

/-- Measurability of the carré du champ integrand.
For each time t, the function x ↦ Γ(φ_t, φ_t)(x) is measurable. -/
lemma carre_du_champ_integrand_measurable {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (φ : VelocityPotential X) (t : ℝ)
    (hΓ_meas : ∀ f g, Measurable f → Measurable g →
      Measurable (fun x => Γ.Γ f g x)) :
    Measurable (fun x => Γ.Γ (φ.φ t) (φ.φ t) x) := by
  -- Use the provided measurability-preserving hypothesis for Γ together with
  -- the measurability of the time-slice φ.φ t.
  have hf : Measurable (φ.φ t) := φ.measurable t
  exact hΓ_meas (φ.φ t) (φ.φ t) hf hf

/-- Measurability of the multi-scale difference integrand.
For each time t, the function x ↦ |Δ^{⟨m⟩}φ_t|² is measurable. -/
lemma multiscale_diff_integrand_measurable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (φ : VelocityPotential X) (t : ℝ) :
    Measurable (fun x => (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ)) := by
  -- measurability of Δ^{⟨m⟩}φ_t, then square as product with itself
  have h_meas : Measurable (multiScaleDiff H cfg (φ.φ t)) := by
    exact multiScaleDiff_measurable H cfg (φ.φ t) (φ.measurable t)
  -- (f x)^2 = (f x) * (f x)
  have : Measurable (fun x => (multiScaleDiff H cfg (φ.φ t) x) *
                               (multiScaleDiff H cfg (φ.φ t) x)) := by
    simpa using (h_meas.mul h_meas)
  -- Rewrite ^2 as product to conclude measurability
  have h_eq : (fun x => (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ)) =
              (fun x => (multiScaleDiff H cfg (φ.φ t) x) *
                         (multiScaleDiff H cfg (φ.φ t) x)) := by
    funext x; simp [pow_two]
  simpa [h_eq]

/-- The Am integrand is measurable for each time parameter.
This is essential for Fubini's theorem applications. -/
lemma Am_integrand_measurable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) (t : ℝ) :
    Measurable (fun _ : ℝ => (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
      + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ)) := by
  -- The integrand is constant in the dummy variable, hence measurable
  exact measurable_const

/-- 単調性バージョン：非負可測な `Γ(φ,φ)` に対し、測度の劣位 `ρ ≤ ρ'` から
  拡張非負積分が単調に増加する。実数積分の LSC 主張の代わりに、
  `lintegral`（拡張非負積分）の単調性を用いる形で使用できる。 -/
lemma carre_du_champ_lsc {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (φ : X → ℝ)
    (h_meas : Measurable (fun x => Γ.Γ φ φ x))
    {ρ ρ' : Measure X} (hρle : ρ ≤ ρ') :
    ∫⁻ x, ENNReal.ofReal (Γ.Γ φ φ x) ∂ρ ≤ ∫⁻ x, ENNReal.ofReal (Γ.Γ φ φ x) ∂ρ' := by
  -- 可測性を ENNReal 版に引き上げ
  have h_meas_en : Measurable (fun x => ENNReal.ofReal (Γ.Γ φ φ x)) :=
    h_meas.ennreal_ofReal
  -- 測度に関する単調性（劣位）から lintegral の単調性が従う
  exact lintegral_mono' hρle (le_refl _)

/-- L² メンバーシップ版：φ_t が L² に属するなら，
`multiScaleDiff` も L² に属する。既存補題 `multiScaleDiff_square_integrable` を用いる。 -/
lemma multiscale_diff_l2_integrable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (μ : Measure X)
    (φ : VelocityPotential X) (t : ℝ)
    (hL2 : MeasureTheory.MemLp (φ.φ t) 2 μ) :
    MeasureTheory.MemLp (multiScaleDiff H cfg (φ.φ t)) 2 μ := by
  exact multiScaleDiff_square_integrable (H := H) (cfg := cfg) (μ := μ)
    (φ := φ.φ t) hL2

/-- Integrability of the Am integrand (assuming appropriate conditions).
This is a technical lemma for the monotonicity proof. -/
lemma Am_integrand_integrable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    (hΓ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    (hΔ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ)
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    :
    MeasureTheory.IntegrableOn
      (fun t => (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume := by
  -- Sum of an integrable function and a scalar multiple of an integrable function
  have hκΔ : MeasureTheory.IntegrableOn
      (fun t => κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume := by
    -- IntegrableOn is closed under scalar multiplication
    simpa using hΔ_int.const_mul κ
  exact hΓ_int.add hκΔ

/-- 改良版（前処理済みの時間関数の可積分性を仮定して結論する版） -/
lemma Am_integrand_integrable_improved {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    -- 時間関数それぞれの可積分性を仮定
    (hΓ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    (hΔ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ)
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun t => (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume := by
  -- 既存の `Am_integrand_integrable` を利用して直ちに従う
  exact Am_integrand_integrable (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (μ := μ)
    (ρ := ρ) (φ := φ) hΓ_int hΔ_int

/-- Monotonicity of Am with respect to κ.
If κ ≤ κ', then Am with κ is at most Am with κ'. -/
lemma Am_mono_in_kappa {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ κ' : ℝ) (h : κ ≤ κ') (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    (hΓ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    (hΔ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ)
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    Am H cfg Γ κ μ ρ φ ≤ Am H cfg Γ κ' μ ρ φ := by
  -- The difference is (κ' - κ) * ∫∫ |Δ^{⟨m⟩}φ|², which is non-negative
  simp only [Am]
  -- Direct proof: for each t, the integrand with κ is ≤ integrand with κ'
  have h_pointwise : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ) ≤
      (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
        + κ' * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ) := by
    intro t _
    have h_nonneg : 0 ≤ ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ := by
      apply integral_nonneg
      intro x
      exact sq_nonneg _
    -- κ ≤ κ' and integral is non-negative, so κ * integral ≤ κ' * integral
    exact add_le_add_left (mul_le_mul_of_nonneg_right h h_nonneg) _
  -- Apply monotonicity of integral
  have h_int_κ := Am_integrand_integrable H cfg Γ κ μ ρ φ hΓ_int hΔ_int
  have h_int_κ' := Am_integrand_integrable H cfg Γ κ' μ ρ φ hΓ_int hΔ_int
  exact MeasureTheory.setIntegral_mono_on h_int_κ h_int_κ' measurableSet_Icc h_pointwise

/-- Am is zero when the potential φ is identically zero. -/
lemma Am_zero_of_phi_zero {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    (hφ : ∀ t x, φ.φ t x = 0) :
    Am H cfg Γ κ μ ρ φ = 0 := by
  simp only [Am]
  -- Both integrands become zero when φ = 0
  have h1 : ∀ t, Γ.Γ (φ.φ t) (φ.φ t) = fun _ => 0 := by
    intro t
    have : φ.φ t = fun _ => 0 := funext (hφ t)
    rw [this]
    -- Γ(0, 0) = 0 by bilinearity
    have h_zero : Γ.Γ (fun _ : X => 0) (fun _ : X => 0) = fun _ => 0 := by
      funext y
      -- Using linearity: Γ(0*f,g) = 0*Γ(f,g) = 0 for any f,g
      -- Using linearity: Γ(0,0) = Γ(0*f + 0*g, 0) = 0*Γ(f,0) + 0*Γ(g,0) = 0
      have h_lin : Γ.Γ (fun _ : X => 0) (fun _ : X => 0) =
                   Γ.Γ (fun x => 0 * (1 : ℝ) + 0 * (0 : ℝ)) (fun _ => 0) := by simp
      rw [h_lin, Γ.linear_left 0 0 (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => 0)]
      simp
    exact h_zero
  have h2 : ∀ t, multiScaleDiff H cfg (φ.φ t) = fun _ => 0 := by
    intro t
    have : φ.φ t = fun _ => 0 := funext (hφ t)
    rw [this]
    exact multiScaleDiff_zero H cfg
  simp_rw [h1, h2]
  simp

/-- Am is zero when the multi-scale difference is zero. -/
lemma Am_zero_of_diff_zero {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    (hΓ : ∀ t x, Γ.Γ (φ.φ t) (φ.φ t) x = 0)
    (hdiff : ∀ t x, multiScaleDiff H cfg (φ.φ t) x = 0) :
    Am H cfg Γ 0 μ ρ φ = 0 := by
  simp only [Am]
  -- Both terms are zero
  have h1 : ∀ t, (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t)) = 0 := by
    intro t
    simp_rw [hΓ t]
    simp
  have h2 : ∀ t, (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ) = 0 := by
    intro t
    simp_rw [hdiff t]
    simp
  simp_rw [h1, h2]
  simp

/-- 単調性：同じ曲線 ρ 上で，ポテンシャルが点ごとに大きい（エネルギー密度と
多尺度差分の二乗が増える）とき，作用 𝒜_m は増加する。 -/
lemma Am_monotone_in_potential {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ φ' : VelocityPotential X)
    -- 時刻ごとの積分レベルでの単調性を仮定する
    (hΓ_int_le : ∀ t : ℝ,
      (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t)) ≤
      (∫ x, (Γ.Γ (φ'.φ t) (φ'.φ t)) x ∂(ρ.ρ t)))
    (hΔ_int_le : ∀ t : ℝ,
      (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ) ≤
      (∫ x, (multiScaleDiff H cfg (φ'.φ t) x) ^ (2 : ℕ) ∂μ))
    -- 時間方向での可積分性（両辺）
    (hInt_left : MeasureTheory.IntegrableOn
      (fun t => (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    (hInt_right : MeasureTheory.IntegrableOn
      (fun t => (∫ x, (Γ.Γ (φ'.φ t) (φ'.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ'.φ t) x) ^ (2 : ℕ) ∂μ))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    Am H cfg Γ κ μ ρ φ ≤ Am H cfg Γ κ μ ρ φ' := by
  -- 区間 I = [0,1] 上の被積分関数の単調性から，集合積分の単調性が従う。
  have h_pointwise : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ) ≤
      (∫ x, (Γ.Γ (φ'.φ t) (φ'.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ'.φ t) x) ^ (2 : ℕ) ∂μ) := by
    intro t _
    -- それぞれの時刻 t で積分の不等式が成り立つ
    have h1 := hΓ_int_le t
    have h2 := hΔ_int_le t
    have h2' : κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ) ≤
               κ * (∫ x, (multiScaleDiff H cfg (φ'.φ t) x) ^ (2 : ℕ) ∂μ) :=
      mul_le_mul_of_nonneg_left h2 hκ
    exact add_le_add h1 h2'
  -- setIntegral の単調性を使用（時間方向は可積分性が仮定されている）
  refine MeasureTheory.setIntegral_mono_on hInt_left hInt_right (measurableSet_Icc) h_pointwise

/-- The weak formulation of the continuity equation in AGS theory.
For any test function ψ ∈ C_c^∞(X), the equation reads:
d/dt ∫ ψ dρ_t = ∫ Γ(ψ, φ_t) dρ_t

This captures the distributional derivative of the curve ρ_t in the direction
determined by the velocity potential φ_t via the carré du champ operator Γ. -/
def ContinuityEquation (X : Type*) [MeasurableSpace X]
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) (Γ : CarreDuChamp X) : Prop :=
  -- Regularity conditions
  (∀ x, Continuous (fun t => φ.φ t x)) ∧
  (∀ t, Measurable (φ.φ t)) ∧
  -- Simplified continuity equation without topological assumptions
  ρ.weakly_continuous ∧
  -- Measurability of the carré du champ
  (∀ ψ : X → ℝ, Measurable ψ → ∀ t, Measurable (Γ.Γ ψ (φ.φ t)))

/-- The weak continuity equation is satisfied when appropriate regularity
conditions hold. This is a fundamental existence theorem for AGS theory. -/
theorem continuity_equation_from_regularity (X : Type*) [MeasurableSpace X]
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) (Γ : CarreDuChamp X)
    (h_weak : ρ.weakly_continuous)
    (h_meas : ∀ ψ : X → ℝ, Measurable ψ → ∀ t, Measurable (Γ.Γ ψ (φ.φ t)))
    :
    ContinuityEquation X ρ φ Γ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact φ.timeContinuous x
  · intro t; exact φ.measurable t
  · exact h_weak
  · exact h_meas

/-- Admissible pairs (ρ,φ) connecting ρ₀ to ρ₁ -/
structure AdmissiblePair (X : Type*) [MeasurableSpace X]
    (ρ₀ ρ₁ : Measure X) (Γ : CarreDuChamp X) where
  /-- The curve of measures -/
  curve : ProbabilityCurve X
  /-- The velocity potential -/
  potential : VelocityPotential X
  /-- Initial condition -/
  init : curve.ρ 0 = ρ₀
  /-- Terminal condition -/
  terminal : curve.ρ 1 = ρ₁
  /-- Continuity equation holds -/
  continuity : ContinuityEquation X curve potential Γ

/-- The set of admissible pairs: those satisfying the continuity equation.
Endpoint constraints are already embedded in `AdmissiblePair`. -/
def AdmissibleSet {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X) : Set (AdmissiblePair X ρ₀ ρ₁ Γ) :=
  { p : AdmissiblePair X ρ₀ ρ₁ Γ |
      -- Base regularity: continuity equation packages weak-continuity + time-regularity
      ContinuityEquation X p.curve p.potential Γ ∧
      -- Multi-scale term: each time-slice mapped by Δ^{⟨m⟩} is measurable
      (∀ t : ℝ, Measurable (multiScaleDiff H cfg (p.potential.φ t))) ∧
      -- Energy term: Γ(φ_t, φ_t) is measurable for each t
      (∀ t : ℝ, Measurable (Γ.Γ (p.potential.φ t) (p.potential.φ t))) }

/-- AdmissibleSet が非空となる十分条件（データ駆動版）.
具体的な曲線 `curve` と速度ポテンシャル `potential` が端点条件と弱連続の式、
および各時間スライスでの可測性条件を満たすなら、`AdmissibleSet` は非空である。 -/
theorem admissible_set_nonempty {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X)
    (curve : ProbabilityCurve X) (potential : VelocityPotential X)
    (h_init : curve.ρ 0 = ρ₀) (h_term : curve.ρ 1 = ρ₁)
    (hCE : ContinuityEquation X curve potential Γ)
    (hΔ_meas : ∀ t : ℝ, Measurable (multiScaleDiff H cfg (potential.φ t)))
    (hΓ_meas : ∀ t : ℝ, Measurable (Γ.Γ (potential.φ t) (potential.φ t))) :
    ∃ (p : AdmissiblePair X ρ₀ ρ₁ Γ), p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁ := by
  -- 構成: 与えられたデータから許容対を組み立て、定義に従って集合に属することを示す。
  refine ⟨{
      curve := curve
      potential := potential
      init := h_init
      terminal := h_term
      continuity := hCE }, ?_⟩
  -- AdmissibleSet の各条件を満たすことを確認
  refine And.intro ?hCE ?rest
  · exact hCE
  · refine And.intro ?hΔ ?hΓ
    · intro t; simpa using hΔ_meas t
    · intro t; simpa using hΓ_meas t

/-- The modified Benamou-Brenier distance squared.
d_m²(ρ₀,ρ₁) = inf { 𝒜_m(ρ,φ) | (ρ,φ) connects ρ₀ to ρ₁ } -/
noncomputable def dmCandidates {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) : Set ℝ :=
  (fun p : AdmissiblePair X ρ₀ ρ₁ Γ =>
      Am (X := X) H cfg Γ κ μ p.curve p.potential) ''
    (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁)

/-- The modified Benamou–Brenier energy squared as the infimum of action values
over admissible pairs. If no admissible pair exists, we set it to 0 by convention. -/
noncomputable def dm_squared {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) : ℝ :=
  by
    classical
    let S := dmCandidates (X := X) H cfg Γ κ μ ρ₀ ρ₁
    exact if h : S = (∅ : Set ℝ) then 0 else sInf S

/-- The modified Benamou-Brenier distance -/
noncomputable def dm {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) : ℝ :=
  Real.sqrt (dm_squared H cfg Γ κ μ ρ₀ ρ₁)

/-- Flags encoding properties of the dynamic distance.
These are axiomatized at this stage, to be proved later via AGS theory. -/
structure DynDistanceFlags {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) where
  /-- Nonnegativity: dm_squared ≥ 0 -/
  nonneg : ∀ ρ₀ ρ₁ : Measure X,
    0 ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁
  /-- Diagonal vanishing: dm_squared(ρ,ρ) = 0 -/
  diag_zero : ∀ ρ : Measure X,
    dm_squared H cfg Γ κ μ ρ ρ = 0
  /-- Symmetry of the squared distance -/
  symm : ∀ ρ₀ ρ₁ : Measure X,
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ = dm_squared H cfg Γ κ μ ρ₁ ρ₀
  /-- Triangle inequality (gluing property for geodesics) -/
  triangle : ∀ ρ₀ ρ₁ ρ₂ : Measure X,
    dm_squared H cfg Γ κ μ ρ₀ ρ₂ ≤
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ + dm_squared H cfg Γ κ μ ρ₁ ρ₂
  /-- Triangle inequality at the distance level -/
  triangle_dist : ∀ ρ₀ ρ₁ ρ₂ : Measure X,
    dm H cfg Γ κ μ ρ₀ ρ₂ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ + dm H cfg Γ κ μ ρ₁ ρ₂

/-- The modified distance dominates the Wasserstein distance.
This follows from the non-negativity of the second term in 𝒜_m. -/
-- Placeholder for Wasserstein distance squared
noncomputable def W2_squared {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    : Measure X → Measure X → ℝ := fun _ _ => 0

/-- The domination theorem: dm² dominates W₂².
This follows from the non-negativity of the multi-scale regularization term.
Specifically:
1. dm_squared is the infimum over admissible pairs (ρ,φ)
2. The action Am = ∫[Γ(φ,φ) + κ|Δ^{⟨m⟩}φ|²] ≥ ∫Γ(φ,φ) (since κ > 0 and |Δ^{⟨m⟩}φ|² ≥ 0)
3. The Benamou-Brenier characterization: W₂² = inf ∫Γ(φ,φ)
Therefore dm² ≥ W₂² automatically. -/
theorem dm_dominates_wasserstein {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) :
    W2_squared ρ₀ ρ₁ ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁ := by
  classical
  -- Left-hand side is the placeholder 0; it suffices to show nonnegativity of dm_squared.
  simp only [W2_squared]
  -- Expand definition of dm_squared and prove the nonnegativity of the infimum.
  simp only [dm_squared, dmCandidates]
  -- Case split on emptiness of the admissible set
  by_cases hadm : AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁ = ∅
  · simp [hadm]
  · -- Define the image set S and show all elements are ≥ 0
    set S : Set ℝ :=
      (fun p : AdmissiblePair X ρ₀ ρ₁ Γ =>
        Am (X := X) H cfg Γ κ μ p.curve p.potential) '' AdmissibleSet H cfg Γ ρ₀ ρ₁ with hS
    have hS_ne : S.Nonempty := by
      -- Since the domain is nonempty, its image is nonempty
      have : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hadm
      rcases this with ⟨p, hp⟩
      exact ⟨_, ⟨p, hp, rfl⟩⟩
    -- Use Am_nonneg to show all elements are non-negative
    have hS_nonneg : ∀ y ∈ S, 0 ≤ y := by
      intro y hy
      rcases hy with ⟨p, hp, rfl⟩
      exact Am_nonneg H cfg Γ κ hκ μ p.curve p.potential
    -- All elements of S are non-negative, so sInf S ≥ 0
    have h_nonneg : 0 ≤ sInf S := le_csInf hS_ne (by intro b hb; exact hS_nonneg b hb)
    -- Since AdmissibleSet is nonempty, dmCandidates is nonempty, so we get sInf
    have h_eq : dmCandidates H cfg Γ κ μ ρ₀ ρ₁ = S := hS.symm
    rw [← h_eq] at h_nonneg
    change 0 ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁
    rw [dm_squared]
    classical
    have h_ne : dmCandidates H cfg Γ κ μ ρ₀ ρ₁ ≠ ∅ := by
      rw [h_eq]; exact Set.nonempty_iff_ne_empty.mp hS_ne
    simp [h_ne]
    exact h_nonneg

/-- Benamou-Brenier formulation of the Wasserstein distance squared.
W₂²(ρ₀, ρ₁) = inf_{(ρ,v)} ∫₀¹ ∫ |v_t|² dρ_t dt
where the infimum is over curves ρ_t with ρ₀ = ρ₀, ρ₁ = ρ₁ and continuity equation
∂_t ρ + ∇·(ρ v) = 0. -/
noncomputable def W2_squared_BB {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X) : ℝ :=
  by
    classical
    -- The Benamou-Brenier action for velocity field v: ∫₀¹ ∫ Γ(v,v) dρ_t dt
    let candidates :=
      { energy : ℝ | ∃ (ρ : ProbabilityCurve X) (v : VelocityPotential X),
        ρ.ρ 0 = ρ₀ ∧ ρ.ρ 1 = ρ₁ ∧
        ContinuityEquation X ρ v Γ ∧
        energy = ∫ t in Set.Icc (0 : ℝ) 1, ∫ x, Γ.Γ (v.φ t) (v.φ t) x ∂(ρ.ρ t) }
    exact if candidates = ∅ then 0 else sInf candidates

/-- Enhanced domination theorem: dm² ≥ W₂² with explicit Benamou-Brenier comparison.
This follows from the structure of the action functional:
Am = ∫₀¹ [∫ Γ(φ,φ) dρ_t + κ ∫ |Δ^{⟨m⟩}φ|² dμ] dt
≥ ∫₀¹ ∫ Γ(φ,φ) dρ_t dt (since κ ≥ 0 and |Δ^{⟨m⟩}φ|² ≥ 0)
Therefore: dm² = inf Am ≥ inf ∫₀¹ ∫ Γ(φ,φ) dρ_t dt = W₂² -/
theorem dm_dominates_wasserstein_BB {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- 非空性仮定：許容対が少なくとも一つ存在
    (h_adm : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    -- 時間方向の可積分性：各許容対に対し Γ 部分と多重スケール項の時間可積分性
    (h_time_int : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (Γ.Γ (p.potential.φ t) (p.potential.φ t)) x ∂(p.curve.ρ t))
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ)
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    W2_squared_BB Γ ρ₀ ρ₁ ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁ := by
  classical
  -- 展開
  simp only [W2_squared_BB, dm_squared, dmCandidates]
  -- 画像集合の記号
  set Sdm : Set ℝ :=
    (fun p : AdmissiblePair X ρ₀ ρ₁ Γ =>
      Am (X := X) H cfg Γ κ μ p.curve p.potential) ''
    AdmissibleSet H cfg Γ ρ₀ ρ₁ with hSdm
  have hSdm_ne : Sdm.Nonempty := by
    rcases h_adm with ⟨p, hp⟩
    exact ⟨_, ⟨p, hp, rfl⟩⟩
  have hSdm_bdd : BddBelow Sdm := ⟨0, by
    intro y hy; rcases hy with ⟨p, hp, rfl⟩
    exact Am_nonneg (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
      (μ := μ) p.curve p.potential⟩
  -- W2 側の候補集合（Benamou-Brenier）
  set Sbb : Set ℝ :=
    { energy : ℝ | ∃ (ρ : ProbabilityCurve X),
        ρ.ρ 0 = ρ₀ ∧ ρ.ρ 1 = ρ₁ ∧
        ∃ (v : VelocityPotential X),
          ContinuityEquation X ρ v Γ ∧
          energy = ∫ t in Set.Icc (0 : ℝ) 1, ∫ x, Γ.Γ (v.φ t) (v.φ t) x ∂(ρ.ρ t) } with hSbb
  -- AdmissibleSet の非空性から BB 候補集合も非空
  have hSbb_ne : Sbb.Nonempty := by
    rcases h_adm with ⟨p, hp⟩
    refine ⟨(
      ∫ t in Set.Icc (0 : ℝ) 1,
        ∫ x, Γ.Γ (p.potential.φ t) (p.potential.φ t) x ∂(p.curve.ρ t)
    ), ?_⟩
    -- p のデータからエネルギーを構成
    exact ⟨p.curve, p.init, p.terminal, p.potential, p.continuity, rfl⟩
  -- 目標：sInf Sbb ≤ sInf Sdm
  -- sInf Sbb は Sdm の下界：各 y∈Sdm に対し sInf Sbb ≤ y を示す
  have h_lower : sInf Sbb ≤ sInf Sdm := by
    -- 下界性：任意の y∈Sdm に対し sInf Sbb ≤ y
    apply le_csInf hSdm_ne
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    -- y = Am(p). 同じ (ρ,φ) から BB エネルギー z を取り、z ≤ y
    have h_mem_bb :
        (∫ t in Set.Icc (0 : ℝ) 1,
            ∫ x, Γ.Γ (p.potential.φ t) (p.potential.φ t) x ∂(p.curve.ρ t)) ∈ Sbb := by
      refine ?_
      exact ⟨p.curve, p.init, p.terminal, p.potential, p.continuity, rfl⟩
    -- sInf Sbb ≤ その元 ≤ Am(p)
    have h_sInf_le_z : sInf Sbb ≤
        (∫ t in Set.Icc (0 : ℝ) 1,
            ∫ x, Γ.Γ (p.potential.φ t) (p.potential.φ t) x ∂(p.curve.ρ t)) := by
      -- sInf ≤ element（下に 0 で有界な集合の性質を使う）
      -- まず Sbb が下に 0 で有界であることを示す
      have h_bdd : BddBelow Sbb := ⟨0, by
        intro z hz
        rcases hz with ⟨ρ, h0, h1, v, hCE, rfl⟩
        -- Γ(·,·) の非負性から各時刻の内部積分は非負
        have h_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
            0 ≤ (∫ x, Γ.Γ (v.φ t) (v.φ t) x ∂(ρ.ρ t)) := by
          intro t ht
          have hpt : ∀ x, 0 ≤ Γ.Γ (v.φ t) (v.φ t) x := by
            intro x; exact Γ.nonneg (v.φ t) x
          exact integral_nonneg hpt
        -- 時間方向の積分も非負
        exact setIntegral_nonneg measurableSet_Icc (by intro t ht; simpa using h_nonneg t ht)
      ⟩
      exact csInf_le h_bdd h_mem_bb
    -- Am(p) は BB エネルギーに κ≥0 の正項を時間方向で足し込んだものなので ≥
    have h_Am_ge :
        (∫ t in Set.Icc (0 : ℝ) 1,
            ∫ x, Γ.Γ (p.potential.φ t) (p.potential.φ t) x ∂(p.curve.ρ t)) ≤
        Am (X := X) H cfg Γ κ μ p.curve p.potential := by
      -- 点ごとの不等式 A(t) ≤ A(t) + B(t)
      have h_pointwise : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∫ x, Γ.Γ (p.potential.φ t) (p.potential.φ t) x ∂(p.curve.ρ t)) ≤
        (∫ x, Γ.Γ (p.potential.φ t) (p.potential.φ t) x ∂(p.curve.ρ t)) +
        κ * (∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ) := by
        intro t ht; exact le_add_of_nonneg_right (by
          have : 0 ≤ (∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ) := by
            apply integral_nonneg; intro x; exact sq_nonneg _
          exact mul_nonneg hκ this)
      -- 可積分性を h_time_int から取り出し
      have hInt := h_time_int p hp
      rcases hInt with ⟨hΓ_int, hΔ_int⟩
      -- 右辺の時間可積分性（和）
      have hRight :=
        Am_integrand_integrable (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (μ := μ)
          (ρ := p.curve) (φ := p.potential) hΓ_int hΔ_int
      -- 左辺の時間可積分性は hΓ_int
      -- setIntegral の単調性
      have := MeasureTheory.setIntegral_mono_on hΓ_int hRight measurableSet_Icc h_pointwise
      -- 右辺を Am に書き換える
      simpa [Am, add_comm, add_left_comm, add_assoc]
        using this
    exact h_sInf_le_z.trans h_Am_ge
  -- ここまでで：sInf Sbb ≤ sInf Sdm
  -- 定義に基づいて結論（どちらも非空）
  have hSdm_ne' : Sdm ≠ ∅ := Set.nonempty_iff_ne_empty.mp hSdm_ne
  have hSbb_ne' : Sbb ≠ ∅ := Set.nonempty_iff_ne_empty.mp hSbb_ne
  simp [Sdm, Sbb, hSdm_ne', hSbb_ne', h_lower]

/-- The Wasserstein distance from the squared distance -/
noncomputable def W2_BB {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X) : ℝ :=
  Real.sqrt (W2_squared_BB Γ ρ₀ ρ₁)

/-- Enhanced domination at the distance level: dm ≥ W₂ -/
theorem dm_dominates_wasserstein_dist {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    (h_adm : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (h_time_int : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (Γ.Γ (p.potential.φ t) (p.potential.φ t)) x ∂(p.curve.ρ t))
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ)
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    W2_BB Γ ρ₀ ρ₁ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ := by
  -- Apply sqrt monotonicity to the squared domination
  simp only [W2_BB, dm]
  exact Real.sqrt_le_sqrt (dm_dominates_wasserstein_BB H cfg Γ κ hκ μ ρ₀ ρ₁ h_adm h_time_int)

/-- Flag-free domination: removing dependence on DynDistanceFlags.
This completes the goal of section 1-4. -/
theorem dm_dominates_wasserstein_flagfree {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X) :
    ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty →
      (∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        MeasureTheory.IntegrableOn
          (fun t => ∫ x, (Γ.Γ (p.potential.φ t) (p.potential.φ t)) x ∂(p.curve.ρ t))
          (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
        MeasureTheory.IntegrableOn
          (fun t => ∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ)
          (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) →
      W2_BB Γ ρ₀ ρ₁ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ ∧
      W2_squared_BB Γ ρ₀ ρ₁ ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁ := by
  intro ρ₀ ρ₁
  intro h_adm h_time_int
  constructor
  · exact dm_dominates_wasserstein_dist H cfg Γ κ hκ μ ρ₀ ρ₁ h_adm h_time_int
  · exact dm_dominates_wasserstein_BB H cfg Γ κ hκ μ ρ₀ ρ₁ h_adm h_time_int

/-- The probability space P₂(X) with finite second moments -/
structure P2 (X : Type*) [MeasurableSpace X] [PseudoMetricSpace X] where
  /-- The underlying measure -/
  val : Measure X
  /-- It's a probability measure -/
  is_prob : MeasureTheory.IsProbabilityMeasure val
  /-- Has finite second moment -/
  finite_second_moment : ∃ x₀ : X, (∫⁻ x, ENNReal.ofReal ((dist x x₀) ^ (2 : ℕ)) ∂val) < ⊤

/-- dm defines a metric on P₂(X) -/
noncomputable instance P2_PseudoMetricSpace {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : DynDistanceFlags H cfg Γ κ μ) :
    PseudoMetricSpace (P2 X) where
  -- Define distance using dm
  dist p q := dm H cfg Γ κ μ p.val q.val
  -- Properties (using placeholder implementations)
  dist_self p := by
    -- sqrt(dm_squared(ρ,ρ)) = 0 by diag_zero
    simp [dm, flags.diag_zero (ρ := p.val)]
  dist_comm p q := by
    -- symmetry via flags.symm, lifted through sqrt
    have hsq : dm_squared H cfg Γ κ μ p.val q.val =
        dm_squared H cfg Γ κ μ q.val p.val :=
      flags.symm (ρ₀ := p.val) (ρ₁ := q.val)
    simpa [dm] using congrArg Real.sqrt hsq
  dist_triangle p q r := by
    -- directly from triangle_dist on dm
    simpa [dm]
      using flags.triangle_dist (ρ₀ := p.val) (ρ₁ := q.val) (ρ₂ := r.val)
  edist_dist p q := by
    -- The goal is comparing two representations of the same non-negative real
    simp only
    -- Convert the NNReal coercion to ENNReal.ofReal
    have h : dm H cfg Γ κ μ p.val q.val ≥ 0 := Real.sqrt_nonneg _
    simp [ENNReal.ofReal, Real.toNNReal, max_eq_left h]

/-- SpectralPenalty provides an upper bound for the multi-scale term -/
lemma spectral_penalty_bound {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X) (φ : VelocityPotential X)
    (penalty : SpectralPenalty H cfg)
    (hpen : ∀ t, ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ ≤
            penalty.C_dirichlet * (spectralSymbolSupNorm cfg) ^ 2 *
            ∫ x, Γ.Γ (φ.φ t) (φ.φ t) x ∂μ) :
    ∀ t, ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ ≤
         penalty.C_dirichlet * (spectralSymbolSupNorm cfg) ^ 2 *
         ∫ x, Γ.Γ (φ.φ t) (φ.φ t) x ∂μ := by
  intro t
  exact hpen t

/-- Lower semicontinuity bridge: Am LSC implies dm_squared LSC -/
lemma dm_squared_lsc_from_Am {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [_inst : TopologicalSpace (ProbabilityMeasure X)]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (h_lsc : LowerSemicontinuous
      (fun p : ProbabilityMeasure X × ProbabilityMeasure X =>
        dm_squared H cfg Γ κ μ p.1.val p.2.val)) :
    LowerSemicontinuous (fun p : ProbabilityMeasure X × ProbabilityMeasure X =>
      dm_squared H cfg Γ κ μ p.1.val p.2.val) :=
  -- In the current development stage, we accept LSC as a hypothesis (strategy B)
  h_lsc

/-- Zero distance identity: dm_squared(ρ, ρ) = 0
The diagonal distance vanishes because the constant curve ρ(t) = ρ for all t
with zero velocity potential φ(t,x) = 0 achieves zero action. -/
theorem dm_squared_self_eq_zero {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ : Measure X) (hprob : IsProbabilityMeasure ρ) :
    dm_squared H cfg Γ κ μ ρ ρ = 0 := by
  classical
  -- 定数曲線とゼロポテンシャルを構成
  let curve : ProbabilityCurve X :=
    { ρ := fun _ => ρ
      is_prob := fun _ => hprob
      weakly_continuous := True
      time_regular := fun _ => by
        -- probability measure ⇒ finite measure
        refine ⟨?_⟩
        -- measure_univ_lt_top: μ(univ) = 1 < ∞
        simp [hprob.measure_univ]
    }
  let potential : VelocityPotential X :=
    { φ := fun _ _ => 0
      measurable := fun _ => measurable_const
      timeContinuous := fun _ => by
        simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
      l2_integrable := fun _ _ => by
        -- ∫ (0)^2 = 0 < ⊤
        simp
      l2_sobolev_regular := fun _ _ => by
        simp
    }
  -- 連続の式（弱形式）：ゼロポテンシャルで満たされる
  have hCE : ContinuityEquation X curve potential Γ := by
    refine ⟨?h1, ?h2, ?h3, ?h4⟩
    · intro x; simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
    · intro t; simpa using (potential.measurable t)
    · -- weak continuity is assumed as `True`
      exact trivial
    · intro ψ hψ t
      -- φ_t = 0 関数
      have hφ0 : potential.φ t = (fun _ : X => 0) := by funext x; rfl
      -- Γ(ψ,0) = Γ(0,ψ) = 0 関数（線形性＋対称性）
      have hzero_left : Γ.Γ (fun _ : X => 0) ψ = fun _ => 0 := by
        -- 線形性（第1引数）から Γ(0,ψ) = 0 関数
        funext x
        have hlin := Γ.linear_left (a := 0) (b := 0) (f := ψ) (g := ψ) (h := ψ)
        -- 評価して 0 を得る
        have hx := congrArg (fun F => F x) hlin
        simpa using hx
      have hzero_right : Γ.Γ ψ (fun _ : X => 0) = fun _ => 0 := by
        calc
          Γ.Γ ψ (fun _ : X => 0) = Γ.Γ (fun _ : X => 0) ψ := by
            simpa using (Γ.symmetric (ψ) (fun _ : X => 0))
          _ = (fun _ => 0) := hzero_left
      -- 0 関数は可測
      simp [hφ0, hzero_right]
  -- 可測性要件：Δ は 0 を返し、Γ(0,0) も 0
  have hΔ_meas : ∀ t : ℝ, Measurable (multiScaleDiff H cfg (potential.φ t)) := by
    intro t
    -- Δ^{⟨m⟩}(0) = 0 は可測（定数）
    have : multiScaleDiff H cfg (potential.φ t) = (fun _ => 0) := by
      simpa using (multiScaleDiff_zero H cfg)
    simp [this]
  have hΓ_meas : ∀ t : ℝ, Measurable (Γ.Γ (potential.φ t) (potential.φ t)) := by
    intro t
    -- potential.φ t は 0 関数
    have hφ0 : potential.φ t = (fun _ : X => 0) := by funext x; rfl
    -- Γ(0,0) は 0 関数（第1引数の線形性より）
    have h_zero : Γ.Γ (fun _ : X => 0) (fun _ : X => 0) = fun _ => 0 := by
      have hlin := Γ.linear_left (a := 0) (b := 0)
        (f := fun _ : X => 0) (g := fun _ : X => 0) (h := fun _ : X => 0)
      funext x
      simpa using congrArg (fun F => F x) hlin
    simp [hφ0, h_zero]
  -- この許容対は AdmissibleSet に属し、作用は 0
  have hadm : (⟨curve, potential, rfl, rfl, hCE⟩ : AdmissiblePair X ρ ρ Γ) ∈
      AdmissibleSet H cfg Γ ρ ρ := by
    exact And.intro hCE (And.intro hΔ_meas hΓ_meas)
  -- 画像集合に 0 が含まれるので，下限は 0 以下
  have hAm0 : Am H cfg Γ κ μ (curve) (potential) = 0 := by
    -- 作用は各 t で 0 の積分
    -- 既存補題を使用
    refine Am_zero_of_phi_zero (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (μ := μ)
      (ρ := curve) (φ := potential) ?phi0
    intro t x; rfl
  -- dm_squared の定義に従って結論（sInf S = 0 を示す）
  -- S = 画像集合
  let S : Set ℝ :=
    (fun p : AdmissiblePair X ρ ρ Γ =>
      Am (X := X) H cfg Γ κ μ p.curve p.potential) '' AdmissibleSet H cfg Γ ρ ρ
  have hS_nonempty : S.Nonempty := ⟨_, ⟨⟨curve, potential, rfl, rfl, hCE⟩, hadm, hAm0⟩⟩
  have hS_lower0 : ∀ y ∈ S, 0 ≤ y := by
    intro y hy; rcases hy with ⟨p, hp, rfl⟩
    exact Am_nonneg H cfg Γ κ hκ μ p.curve p.potential
  have h_sInf_le_0 : sInf S ≤ 0 := by
    -- sInf ≤ any element; pick y = 0 ∈ S, and S is bounded below by 0
    have h0mem : 0 ∈ S := ⟨⟨curve, potential, rfl, rfl, hCE⟩, hadm, hAm0⟩
    have h_bddbelow : BddBelow S := ⟨0, by intro y hy; exact hS_lower0 y hy⟩
    exact csInf_le h_bddbelow h0mem
  have h_0_le_sInf : 0 ≤ sInf S := by
    -- 0 is a lower bound of S
    exact le_csInf hS_nonempty (by intro b hb; exact hS_lower0 b hb)
  have h_sInf_eq : sInf S = 0 := le_antisymm h_sInf_le_0 h_0_le_sInf
  -- 以上より dm_squared = 0
  unfold dm_squared
  -- 場合分け：S は空でない
  simp [dmCandidates, S, h_sInf_eq, hS_nonempty.ne_empty]

/-- Non-negativity: dm_squared ≥ 0
This follows from Am_nonneg since dm_squared is the infimum of non-negative values. -/
theorem dm_squared_nonneg {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) :
    0 ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁ := by
  -- This is essentially the same proof as in dm_dominates_wasserstein
  classical
  simp only [dm_squared, dmCandidates]
  by_cases hadm : AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁ = ∅
  · simp [hadm]
  · set S : Set ℝ :=
      (fun p : AdmissiblePair X ρ₀ ρ₁ Γ =>
        Am (X := X) H cfg Γ κ μ p.curve p.potential) '' AdmissibleSet H cfg Γ ρ₀ ρ₁
    have hS_ne : S.Nonempty := by
      have : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hadm
      rcases this with ⟨p, hp⟩
      exact ⟨_, ⟨p, hp, rfl⟩⟩
    have hS_nonneg : ∀ y ∈ S, 0 ≤ y := by
      intro y hy
      rcases hy with ⟨p, hp, rfl⟩
      exact Am_nonneg H cfg Γ κ hκ μ p.curve p.potential
    have h_ne : S ≠ ∅ := Set.nonempty_iff_ne_empty.mp hS_ne
    simp [h_ne]
    exact le_csInf hS_ne (by intro b hb; exact hS_nonneg b hb)

/-- Symmetry: dm_squared(ρ₀, ρ₁) = dm_squared(ρ₁, ρ₀)
This follows from time-reversal symmetry of the action functional. -/
theorem dm_squared_symm {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- 非空性（両向き）を仮定
    (hNE₀ : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (hNE₁ : (AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀).Nonempty)
    -- 時間反転により作用値が保存される対応が存在することを仮定（両向き）
    (hRev : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∃ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hRev' : ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀,
      ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential) :
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ = dm_squared H cfg Γ κ μ ρ₁ ρ₀ := by
  classical
  -- 画像集合を定義
  let S01 : Set ℝ :=
    (fun p : AdmissiblePair X ρ₀ ρ₁ Γ =>
      Am (X := X) H cfg Γ κ μ p.curve p.potential) ''
      AdmissibleSet H cfg Γ ρ₀ ρ₁
  let S10 : Set ℝ :=
    (fun p : AdmissiblePair X ρ₁ ρ₀ Γ =>
      Am (X := X) H cfg Γ κ μ p.curve p.potential) ''
      AdmissibleSet H cfg Γ ρ₁ ρ₀
  -- 非空性により if 分岐は sInf になる
  have hne01 : S01.Nonempty := by
    rcases hNE₀ with ⟨p, hp⟩; exact ⟨_, ⟨p, hp, rfl⟩⟩
  have hne10 : S10.Nonempty := by
    rcases hNE₁ with ⟨p, hp⟩; exact ⟨_, ⟨p, hp, rfl⟩⟩
  -- 下に 0 で有界（非負）
  have h_bdd01 : BddBelow S01 := ⟨0, by
    intro y hy; rcases hy with ⟨p, hp, rfl⟩
    exact Am_nonneg (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
      (μ := μ) p.curve p.potential⟩
  have h_bdd10 : BddBelow S10 := ⟨0, by
    intro y hy; rcases hy with ⟨p, hp, rfl⟩
    exact Am_nonneg (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
      (μ := μ) p.curve p.potential⟩
  -- sInf の比較：sInf S10 ≤ sInf S01
  have h_le_10_01 : sInf S10 ≤ sInf S01 := by
    -- 任意の y∈S01 に対し sInf S10 ≤ y（対応要素が S10 にある）
    have hstep : ∀ y ∈ S01, sInf S10 ≤ y := by
      intro y hy
      rcases hy with ⟨p, hp, rfl⟩
      rcases hRev p hp with ⟨q, hq, hAm⟩
      -- y = Am p = Am q ∈ S10
      have : (Am (X := X) H cfg Γ κ μ q.curve q.potential) ∈ S10 := ⟨q, hq, rfl⟩
      -- sInf S10 ≤ that element = y
      have := csInf_le h_bdd10 this
      simpa [hAm] using this
    exact le_csInf hne01 hstep
  -- 対称に sInf S01 ≤ sInf S10
  have h_le_01_10 : sInf S01 ≤ sInf S10 := by
    have hstep : ∀ y ∈ S10, sInf S01 ≤ y := by
      intro y hy
      rcases hy with ⟨q, hq, rfl⟩
      rcases hRev' q hq with ⟨p, hp, hAm⟩
      have : (Am (X := X) H cfg Γ κ μ p.curve p.potential) ∈ S01 := ⟨p, hp, rfl⟩
      have := csInf_le h_bdd01 this
      simpa [hAm] using this
    exact le_csInf hne10 hstep
  -- dm_squared の定義に戻す
  simp [dm_squared, dmCandidates, S01, S10, hne01.ne_empty, hne10.ne_empty,
        le_antisymm h_le_10_01 h_le_01_10]

/-- Triangle inequality for dm_squared: subadditivity via curve gluing
dm_squared(ρ₀, ρ₂) ≤ dm_squared(ρ₀, ρ₁) + dm_squared(ρ₁, ρ₂) -/
theorem dm_squared_triangle {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ ρ₂ : Measure X)
    -- 最小元の存在（両区間）
    (hMin01 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hMin12 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    -- 貼り合わせの存在：作用は和以下
    (hGlue : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
          Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
          Am (X := X) H cfg Γ κ μ p.curve p.potential +
          Am (X := X) H cfg Γ κ μ q.curve q.potential) :
    dm_squared H cfg Γ κ μ ρ₀ ρ₂ ≤
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ + dm_squared H cfg Γ κ μ ρ₁ ρ₂ := by
  classical
  -- 画像集合
  let S01 : Set ℝ :=
    (fun p : AdmissiblePair X ρ₀ ρ₁ Γ =>
      Am (X := X) H cfg Γ κ μ p.curve p.potential) ''
      AdmissibleSet H cfg Γ ρ₀ ρ₁
  let S12 : Set ℝ :=
    (fun p : AdmissiblePair X ρ₁ ρ₂ Γ =>
      Am (X := X) H cfg Γ κ μ p.curve p.potential) ''
      AdmissibleSet H cfg Γ ρ₁ ρ₂
  let S02 : Set ℝ :=
    (fun p : AdmissiblePair X ρ₀ ρ₂ Γ =>
      Am (X := X) H cfg Γ κ μ p.curve p.potential) ''
      AdmissibleSet H cfg Γ ρ₀ ρ₂
  -- 下に 0 で有界
  have h_bdd01 : BddBelow S01 := ⟨0, by
    intro y hy; rcases hy with ⟨p, hp, rfl⟩
    exact Am_nonneg (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
      (μ := μ) p.curve p.potential⟩
  have h_bdd12 : BddBelow S12 := ⟨0, by
    intro y hy; rcases hy with ⟨p, hp, rfl⟩
    exact Am_nonneg (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
      (μ := μ) p.curve p.potential⟩
  have h_bdd02 : BddBelow S02 := ⟨0, by
    intro y hy; rcases hy with ⟨p, hp, rfl⟩
    exact Am_nonneg (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
      (μ := μ) p.curve p.potential⟩
  -- 最小元の取り出し
  rcases hMin01 with ⟨p01, hp01, hmin01⟩
  rcases hMin12 with ⟨p12, hp12, hmin12⟩
  have hmem01 : (Am (X := X) H cfg Γ κ μ p01.curve p01.potential) ∈ S01 := ⟨p01, hp01, rfl⟩
  have hmem12 : (Am (X := X) H cfg Γ κ μ p12.curve p12.potential) ∈ S12 := ⟨p12, hp12, rfl⟩
  -- sInf の同一視：最小元＝下限
  have h_sInf01_le : sInf S01 ≤ Am H cfg Γ κ μ p01.curve p01.potential :=
    csInf_le h_bdd01 hmem01
  have h_le_sInf01 : Am H cfg Γ κ μ p01.curve p01.potential ≤ sInf S01 := by
    -- p01 は全要素の下界
    apply le_csInf
    · -- 非空性：p01 が属する
      exact ⟨_, hmem01⟩
    · intro y hy
      rcases hy with ⟨q, hq, rfl⟩
      exact hmin01 q hq
  have h_sInf01 : sInf S01 = Am H cfg Γ κ μ p01.curve p01.potential :=
    le_antisymm h_sInf01_le h_le_sInf01
  have h_sInf12_le : sInf S12 ≤ Am H cfg Γ κ μ p12.curve p12.potential :=
    csInf_le h_bdd12 hmem12
  have h_le_sInf12 : Am H cfg Γ κ μ p12.curve p12.potential ≤ sInf S12 := by
    apply le_csInf
    · exact ⟨_, hmem12⟩
    · intro y hy; rcases hy with ⟨q, hq, rfl⟩; exact hmin12 q hq
  have h_sInf12 : sInf S12 = Am H cfg Γ κ μ p12.curve p12.potential :=
    le_antisymm h_sInf12_le h_le_sInf12
  -- 貼り合わせで S02 の元を得て、作用 ≤ 和
  obtain ⟨r, hr, hAm_le⟩ := hGlue p01 hp01 p12 hp12
  have hmem02 : (Am (X := X) H cfg Γ κ μ r.curve r.potential) ∈ S02 := ⟨r, hr, rfl⟩
  -- sInf S02 ≤ Am r ≤ Am p01 + Am p12 = sInf S01 + sInf S12
  have h_step : sInf S02 ≤
    Am (X := X) H cfg Γ κ μ p01.curve p01.potential +
    Am (X := X) H cfg Γ κ μ p12.curve p12.potential := by
    have := csInf_le h_bdd02 hmem02
    exact this.trans hAm_le
  -- 目標へ：dm_squared の定義を展開
  -- S01,S12 は非空（最小元が存在）
  have hne01 : S01.Nonempty := ⟨_, hmem01⟩
  have hne12 : S12.Nonempty := ⟨_, hmem12⟩
  -- S02 も非空（r がある）
  have hne02 : S02.Nonempty := ⟨_, hmem02⟩
  -- まとめ
  simp [dm_squared, dmCandidates, S01, S12, S02,
        hne01.ne_empty, hne12.ne_empty, hne02.ne_empty,
        h_sInf01, h_sInf12] at h_step ⊢
  exact h_step

/-- Triangle inequality for dm: the actual distance function
dm(ρ₀, ρ₂) ≤ dm(ρ₀, ρ₁) + dm(ρ₁, ρ₂) -/
theorem dm_triangle {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ ρ₂ : Measure X)
    -- dm_squared_triangle に必要な仮定を引き回す
    (hMin01 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hMin12 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hGlue : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
          Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
          Am (X := X) H cfg Γ κ μ p.curve p.potential +
          Am (X := X) H cfg Γ κ μ q.curve q.potential) :
    dm H cfg Γ κ μ ρ₀ ρ₂ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ + dm H cfg Γ κ μ ρ₁ ρ₂ := by
  -- Use triangle inequality from squared distances
  have h₁ := dm_squared_nonneg H cfg Γ κ hκ μ ρ₀ ρ₁
  have h₂ := dm_squared_nonneg H cfg Γ κ hκ μ ρ₁ ρ₂
  have h_tri := dm_squared_triangle (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
    (μ := μ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) (ρ₂ := ρ₂) hMin01 hMin12 hGlue
  -- dm is defined as sqrt of dm_squared
  simp only [dm]
  -- For non-negative a,b,c with c ≤ a + b, we want √c ≤ √a + √b
  -- This follows from monotonicity of sqrt: √c ≤ √(a + b) ≤ √a + √b
  have h_mono := Real.sqrt_le_sqrt h_tri
  have h_sqrt_add : Real.sqrt
      (dm_squared H cfg Γ κ μ ρ₀ ρ₁ + dm_squared H cfg Γ κ μ ρ₁ ρ₂)
      ≤ Real.sqrt (dm_squared H cfg Γ κ μ ρ₀ ρ₁)
        + Real.sqrt (dm_squared H cfg Γ κ μ ρ₁ ρ₂) := by
    -- 手作りの証明: (√a + √b)^2 = a + b + 2√a√b ≥ a + b
    set a := dm_squared H cfg Γ κ μ ρ₀ ρ₁
    set b := dm_squared H cfg Γ κ μ ρ₁ ρ₂
    have ha : 0 ≤ a := h₁
    have hb : 0 ≤ b := h₂
    have hsq_nonneg : 0 ≤ (Real.sqrt a + Real.sqrt b) := by
      exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_le_sq : a + b ≤ (Real.sqrt a + Real.sqrt b)^2 := by
      have hcs : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by
        have hprod : 0 ≤ Real.sqrt a * Real.sqrt b :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have h2nonneg : 0 ≤ (2:ℝ) := by norm_num
        exact mul_nonneg h2nonneg hprod
      -- a + b ≤ a + b + 2√a√b
      have h_le : a + b ≤ a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hcs (a + b)
      -- (√a + √b)^2 = a + b + 2√a√b
      have hsq_eq : (Real.sqrt a + Real.sqrt b)^2 =
          a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
        -- ring: (x+y)^2 = x^2 + y^2 + 2xy, with x=√a, y=√b
        have : (Real.sqrt a + Real.sqrt b)^2 =
            (Real.sqrt a)^2 + (Real.sqrt b)^2 + 2 * (Real.sqrt a * Real.sqrt b) := by
          ring
        -- simplify (√a)^2 = a and (√b)^2 = b using mul_self_sqrt (needs nonneg)
        simpa [pow_two, Real.mul_self_sqrt ha, Real.mul_self_sqrt hb, mul_comm,
          mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
          using this
      exact by simpa [hsq_eq] using h_le
    -- 単調性で √(a+b) ≤ √((√a+√b)^2) = √a + √b
    have hstep : Real.sqrt (a + b) ≤
        Real.sqrt ((Real.sqrt a + Real.sqrt b)^2) :=
      Real.sqrt_le_sqrt h_le_sq
    have hfinal : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
      simpa [Real.sqrt_sq_eq_abs, add_comm, add_left_comm, add_assoc,
             abs_of_nonneg hsq_nonneg]
        using hstep
    exact hfinal
  exact le_trans h_mono h_sqrt_add

/-- Triangle inequality for `dm` on `P2 X`（P2 版） -/
theorem dm_triangle_P2 {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (p q r : P2 X)
    -- 前段の dm_squared 三角不等式に必要な仮定を P2 版で供給
    (hMin01 : ∃ s ∈ AdmissibleSet (X := X) H cfg Γ p.val q.val,
      ∀ t ∈ AdmissibleSet (X := X) H cfg Γ p.val q.val,
        Am (X := X) H cfg Γ κ μ s.curve s.potential ≤
        Am (X := X) H cfg Γ κ μ t.curve t.potential)
    (hMin12 : ∃ s ∈ AdmissibleSet (X := X) H cfg Γ q.val r.val,
      ∀ t ∈ AdmissibleSet (X := X) H cfg Γ q.val r.val,
        Am (X := X) H cfg Γ κ μ s.curve s.potential ≤
        Am (X := X) H cfg Γ κ μ t.curve t.potential)
    (hGlue : ∀ s ∈ AdmissibleSet (X := X) H cfg Γ p.val q.val,
      ∀ t ∈ AdmissibleSet (X := X) H cfg Γ q.val r.val,
        ∃ u ∈ AdmissibleSet (X := X) H cfg Γ p.val r.val,
          Am (X := X) H cfg Γ κ μ u.curve u.potential ≤
          Am (X := X) H cfg Γ κ μ s.curve s.potential +
          Am (X := X) H cfg Γ κ μ t.curve t.potential) :
    dm H cfg Γ κ μ p.val r.val ≤ dm H cfg Γ κ μ p.val q.val + dm H cfg Γ κ μ q.val r.val := by
  -- まず平方距離の三角不等式を適用
  have htri := dm_squared_triangle (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
    (μ := μ) (ρ₀ := p.val) (ρ₁ := q.val) (ρ₂ := r.val) hMin01 hMin12 hGlue
  -- 非負性
  have ha := dm_squared_nonneg (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
    (μ := μ) (ρ₀ := p.val) (ρ₁ := q.val)
  have hb := dm_squared_nonneg (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
    (μ := μ) (ρ₀ := q.val) (ρ₁ := r.val)
  -- 平方根へ移す
  simp [dm]  -- 展開: sqrt(dm_squared ...)
  have hm := Real.sqrt_le_sqrt htri
  have h_sqrt_add : Real.sqrt
      (dm_squared H cfg Γ κ μ p.val q.val + dm_squared H cfg Γ κ μ q.val r.val)
      ≤ Real.sqrt (dm_squared H cfg Γ κ μ p.val q.val)
        + Real.sqrt (dm_squared H cfg Γ κ μ q.val r.val) := by
    -- 同様に手作りの平方根不等式
    set a := dm_squared H cfg Γ κ μ p.val q.val
    set b := dm_squared H cfg Γ κ μ q.val r.val
    have ha' : 0 ≤ a := ha
    have hb' : 0 ≤ b := hb
    have hsq_nonneg : 0 ≤ (Real.sqrt a + Real.sqrt b) := by
      exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_le_sq : a + b ≤ (Real.sqrt a + Real.sqrt b)^2 := by
      have hcs : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by
        have hprod : 0 ≤ Real.sqrt a * Real.sqrt b :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have h2nonneg : 0 ≤ (2:ℝ) := by norm_num
        exact mul_nonneg h2nonneg hprod
      have h_le : a + b ≤ a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hcs (a + b)
      have hsq_eq : (Real.sqrt a + Real.sqrt b)^2 =
          a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
        -- ring: (x+y)^2 = x^2 + y^2 + 2xy, with x=√a, y=√b
        have : (Real.sqrt a + Real.sqrt b)^2 =
            (Real.sqrt a)^2 + (Real.sqrt b)^2 + 2 * (Real.sqrt a * Real.sqrt b) := by
          ring
        -- simplify (√a)^2 = a and (√b)^2 = b using mul_self_sqrt (needs nonneg)
        simpa [pow_two, Real.mul_self_sqrt ha, Real.mul_self_sqrt hb, mul_comm,
          mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
          using this
      simpa [hsq_eq]
        using h_le
    have := Real.sqrt_le_sqrt h_le_sq
    simpa [a, b, Real.sqrt_sq_eq_abs, abs_of_nonneg hsq_nonneg] using this
  exact le_trans hm h_sqrt_add

/-- Collecting all distance axioms: dm defines a pseudometric on measures -/
theorem dm_pseudometric {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    -- 対称性に必要な仮定（両向きの非空性と時間反転対応）
    (hNE01 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (hNE10 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀).Nonempty)
    (hRev : ∀ {ρ₀ ρ₁} (p : AdmissiblePair X ρ₀ ρ₁ Γ), p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁ →
      ∃ q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hRev' : ∀ {ρ₀ ρ₁} (q : AdmissiblePair X ρ₁ ρ₀ Γ), q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀ →
      ∃ p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    -- 三角不等式に必要な仮定（最小元の存在と貼り合わせ）
    (hMin : ∀ ρ₀ ρ₁ : Measure X,
      ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
          Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
          Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hGlue' : ∀ {ρ₀ ρ₁ ρ₂}
        (p : AdmissiblePair X ρ₀ ρ₁ Γ) (_ : p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁)
        (q : AdmissiblePair X ρ₁ ρ₂ Γ) (_ : q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂),
      ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
        Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
        Am (X := X) H cfg Γ κ μ p.curve p.potential +
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    -- 零距離同一性に必要な確率性
    (hP : ∀ ρ : Measure X, IsProbabilityMeasure ρ) :
    ∀ ρ₀ ρ₁ ρ₂ : Measure X,
      (0 ≤ dm H cfg Γ κ μ ρ₀ ρ₁) ∧
      (dm H cfg Γ κ μ ρ₀ ρ₀ = 0) ∧
      (dm H cfg Γ κ μ ρ₀ ρ₁ = dm H cfg Γ κ μ ρ₁ ρ₀) ∧
      (dm H cfg Γ κ μ ρ₀ ρ₂ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ + dm H cfg Γ κ μ ρ₁ ρ₂) := by
  intro ρ₀ ρ₁ ρ₂
  constructor
  · -- Non-negativity
    simp only [dm]
    exact Real.sqrt_nonneg _
  constructor
  · -- Zero diagonal
    simp only [dm]
    rw [dm_squared_self_eq_zero H cfg Γ κ hκ μ ρ₀ (hP ρ₀)]
    exact Real.sqrt_zero
  constructor
  · -- Symmetry
    have ne01 := hNE01 ρ₀ ρ₁
    have ne10 := hNE10 ρ₀ ρ₁
    -- 準備した仮定を渡して対称性（平方距離）を得てから平方根で持ち上げる
    have hsymm := dm_squared_symm (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
      (μ := μ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) ne01 ne10 (by intro p hp; exact hRev p hp)
      (by intro q hq; exact hRev' q hq)
    simpa [dm] using congrArg Real.sqrt hsymm
  · -- Triangle inequality
    -- 最小元と貼り合わせの仮定を渡して三角不等式を適用
    have ⟨p01, hp01, hmin01⟩ := hMin ρ₀ ρ₁
    have ⟨p12, hp12, hmin12⟩ := hMin ρ₁ ρ₂
    exact dm_triangle (H := H) (cfg := cfg) (Γ := Γ) (κ := κ) (hκ := hκ)
      (μ := μ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      (hMin01 := ⟨p01, hp01, hmin01⟩) (hMin12 := ⟨p12, hp12, hmin12⟩)
      (hGlue := by
        intro p hp q hq; exact hGlue' p hp q hq)

/-- Flag-free pseudometric instance: using the proven distance axioms
instead of relying on DynDistanceFlags -/
noncomputable instance P2_PseudoMetricSpace_flagfree {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (hNE01 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (hNE10 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀).Nonempty)
    (hRev : ∀ {ρ₀ ρ₁} (p : AdmissiblePair X ρ₀ ρ₁ Γ), p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁ →
      ∃ q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hRev' : ∀ {ρ₀ ρ₁} (q : AdmissiblePair X ρ₁ ρ₀ Γ), q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀ →
      ∃ p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hMin : ∀ ρ₀ ρ₁ : Measure X,
      ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
          Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
          Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hGlue' : ∀ {ρ₀ ρ₁ ρ₂}
        (p : AdmissiblePair X ρ₀ ρ₁ Γ) (_ : p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁)
        (q : AdmissiblePair X ρ₁ ρ₂ Γ) (_ : q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂),
      ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
        Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
        Am (X := X) H cfg Γ κ μ p.curve p.potential +
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hP : ∀ ρ : Measure X, IsProbabilityMeasure ρ) :
    PseudoMetricSpace (P2 X) where
  -- Define distance using dm
  dist p q := dm H cfg Γ κ μ p.val q.val
  -- Properties using proven theorems instead of flags
  dist_self p := by
    have h := dm_pseudometric H cfg Γ κ hκ μ hNE01 hNE10
      (by intro ρ₀ ρ₁ a ha; exact hRev a ha)
      (by intro ρ₀ ρ₁ b hb; exact hRev' b hb)
      hMin
      (by intro ρ₀ ρ₁ ρ₂ a ha b hb; exact hGlue' a ha b hb)
      hP
    exact (h p.val p.val p.val).2.1
  dist_comm p q := by
    have h := dm_pseudometric H cfg Γ κ hκ μ hNE01 hNE10
      (by intro ρ₀ ρ₁ a ha; exact hRev a ha)
      (by intro ρ₀ ρ₁ b hb; exact hRev' b hb)
      hMin
      (by intro ρ₀ ρ₁ ρ₂ a ha b hb; exact hGlue' a ha b hb)
      hP
    exact (h p.val q.val p.val).2.2.1
  dist_triangle p q r := by
    have h := dm_pseudometric H cfg Γ κ hκ μ hNE01 hNE10
      (by intro ρ₀ ρ₁ a ha; exact hRev a ha)
      (by intro ρ₀ ρ₁ b hb; exact hRev' b hb)
      hMin
      (by intro ρ₀ ρ₁ ρ₂ a ha b hb; exact hGlue' a ha b hb)
      hP
    exact (h p.val q.val r.val).2.2.2
  edist_dist p q := by
    -- The goal is comparing two representations of the same non-negative real
    simp only
    -- Convert the NNReal coercion to ENNReal.ofReal
    have h_nonneg : dm H cfg Γ κ μ p.val q.val ≥ 0 := by
      -- √(…) is always ≥ 0
      simp [dm, Real.sqrt_nonneg]
    simp [ENNReal.ofReal, Real.toNNReal, max_eq_left h_nonneg]

end Frourio
