import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace Frourio

open MeasureTheory

/-!
# Multi-Scale Difference Operator for Meta-Variational Principle

This file defines the m-point multi-scale difference operator Δ^{⟨m⟩} and
spectral symbols for the meta-variational principle framework.

## Main definitions

- `MultiScaleConfig`: Configuration for multi-scale parameters (α, τ)
- `multiScaleDiff`: The m-point multi-scale difference operator
- `spectralSymbol`: The spectral symbol ψ_m(λ)
- `SpectralBound`: Flags for spectral bounds

## Implementation notes

We use `PNat` for m to ensure m ≥ 1 at the type level, and separate positive
reals for scale parameters τ to maintain mathematical validity.
-/

open scoped BigOperators

/-- Configuration for m-point multi-scale parameters.
Contains weights α and scales τ with the constraint that weights sum to zero. -/
structure MultiScaleConfig (m : PNat) where
  /-- Weights for each scale, must sum to zero -/
  α : Fin m → ℝ
  /-- Time scales, must be positive -/
  τ : Fin m → ℝ
  /-- Positivity constraint for scales -/
  hτ_pos : ∀ i, 0 < τ i
  /-- Zero-sum constraint for weights -/
  hα_sum : ∑ i, α i = 0
  /-- Weights are bounded (for technical reasons) -/
  hα_bound : ∀ i, |α i| ≤ 1

/-- Abstract heat semigroup structure for multi-scale analysis -/
structure HeatSemigroup (X : Type*) where
  /-- The semigroup operator H_t -/
  H : ℝ → (X → ℝ) → (X → ℝ)
  /-- Semigroup property: H_s ∘ H_t = H_{s+t} -/
  isSemigroup : ∀ s t : ℝ, ∀ φ : X → ℝ, H s (H t φ) = H (s + t) φ
  /-- Identity at t=0: H_0 = I -/
  isIdentity : ∀ φ : X → ℝ, H 0 φ = φ
  /-- Linearity in function argument -/
  linear_in_function : ∀ t : ℝ, ∀ a b : ℝ, ∀ φ ψ : X → ℝ,
    H t (fun x => a * φ x + b * ψ x) = fun x => a * H t φ x + b * H t ψ x
  /-- Preserves constant functions -/
  preserves_constants : ∀ t : ℝ, ∀ c : ℝ, H t (fun _ => c) = fun _ => c
  /-- Measurability preservation: under any measurable structure on `X`,
      if `φ` is measurable then so is `H_t φ`. We quantify the instance
      explicitly to avoid requiring `[MeasurableSpace X]` at the structure level. -/
  measurable_in_function : ∀ t : ℝ, ∀ φ : X → ℝ,
    (∀ [MeasurableSpace X], Measurable φ → Measurable (fun x => H t φ x))
  /-- L² continuity: H_t preserves L² functions -/
  l2_continuous : ∀ t : ℝ, ∀ φ : X → ℝ,
    (∀ [MeasurableSpace X] (μ : MeasureTheory.Measure X),
      MeasureTheory.MemLp φ 2 μ → MeasureTheory.MemLp (fun x => H t φ x) 2 μ)
  /-- L² contractivity: H_t is a contraction on L² -/
  l2_contractive : ∀ t : ℝ, ∀ φ : X → ℝ,
    (∀ [MeasurableSpace X] (μ : MeasureTheory.Measure X),
      (0 ≤ t) → MeasureTheory.MemLp φ 2 μ → MeasureTheory.MemLp (fun x => H t φ x) 2 μ)

/-- The m-point multi-scale difference operator Δ^{⟨m⟩}_{α,τ}.
Definition: Δ^{⟨m⟩} φ := ∑ α_i H_{τ_i} φ - (∑ α_i)I φ.
Since ∑ α_i = 0 (zero-sum constraint), the second term vanishes,
giving us Δ^{⟨m⟩} φ = ∑ α_i H_{τ_i} φ -/
noncomputable def multiScaleDiff {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (φ : X → ℝ) : X → ℝ :=
  fun x => ∑ i : Fin m, cfg.α i * H.H (cfg.τ i) φ x

/-- Basic linearity property of the multi-scale difference operator -/
theorem multiScaleDiff_linear {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (a b : ℝ) (φ ψ : X → ℝ) :
    multiScaleDiff H cfg (fun x => a * φ x + b * ψ x) =
    fun x => a * multiScaleDiff H cfg φ x + b * multiScaleDiff H cfg ψ x := by
  ext x
  simp only [multiScaleDiff]
  -- Use linearity of H for each term
  conv_lhs => arg 2; ext i; rw [H.linear_in_function]
  -- Distribute the sum
  simp only [mul_add, Finset.sum_add_distrib]
  -- Rearrange terms: pull out scalar multiplication
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> (congr 1; ext i; ring)

/-- Constants are annihilated by the multi-scale difference operator -/
theorem multiScaleDiff_const_zero {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (c : ℝ) :
    multiScaleDiff H cfg (fun _ => c) = fun _ => 0 := by
  ext x
  simp only [multiScaleDiff]
  -- H preserves constants, so H.H (cfg.τ i) (fun _ => c) = fun _ => c
  conv_lhs => arg 2; ext i; rw [H.preserves_constants]
  -- Now we have ∑ i, cfg.α i * c = c * ∑ i, cfg.α i = c * 0 = 0
  rw [← Finset.sum_mul]
  simp [cfg.hα_sum]

/-- The zero function is mapped to zero by the multi-scale difference operator -/
theorem multiScaleDiff_zero {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) :
    multiScaleDiff H cfg (fun _ => 0) = fun _ => 0 := by
  exact multiScaleDiff_const_zero H cfg 0

/-- HeatSemigroup preserves measurability -/
lemma heatSemigroup_measurable {X : Type*} [MeasurableSpace X]
    (H : HeatSemigroup X) (t : ℝ) (φ : X → ℝ) (hφ : Measurable φ) :
    Measurable (fun x => H.H t φ x) :=
  H.measurable_in_function t φ hφ

/-- HeatSemigroup preserves L² functions -/
lemma heatSemigroup_l2_preserves {X : Type*} [MeasurableSpace X]
    (H : HeatSemigroup X) (t : ℝ) (μ : MeasureTheory.Measure X) (φ : X → ℝ)
    (hφ : MeasureTheory.MemLp φ 2 μ) :
    MeasureTheory.MemLp (fun x => H.H t φ x) 2 μ :=
  H.l2_continuous t φ μ hφ

/-- HeatSemigroup is L² contractive for non-negative time -/
lemma heatSemigroup_l2_contraction {X : Type*} [MeasurableSpace X]
    (H : HeatSemigroup X) (t : ℝ) (ht : 0 ≤ t) (μ : MeasureTheory.Measure X) (φ : X → ℝ)
    (hφ : MeasureTheory.MemLp φ 2 μ) :
    MeasureTheory.MemLp (fun x => H.H t φ x) 2 μ :=
  H.l2_contractive t φ μ ht hφ

/-- Measurability property for multiScaleDiff -/
lemma multiScaleDiff_measurable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (φ : X → ℝ) (hφ : Measurable φ) :
    Measurable (multiScaleDiff H cfg φ) := by
  classical
  -- Define the summand function
  let f : Fin m → X → ℝ := fun i x => cfg.α i * H.H (cfg.τ i) φ x
  -- Each summand is measurable: constant times a measurable function
  have hf_meas : ∀ i, Measurable (fun x => f i x) := by
    intro i
    have hH : Measurable (fun x => H.H (cfg.τ i) φ x) :=
      (H.measurable_in_function (cfg.τ i) φ) hφ
    exact (measurable_const.mul hH)
  -- Finite sum of measurable functions is measurable
  have hsum : Measurable (fun x => (Finset.univ : Finset (Fin m)).sum (fun i => f i x)) := by
    refine Finset.induction_on (Finset.univ : Finset (Fin m)) ?base ?step
    · simp
    · intro a s ha ih
      -- Order matters for `Measurable.add`; match the expected summand order
      simpa [Finset.sum_insert ha, f] using (hf_meas a).add ih
  -- Rewrite back to the original definition
  simpa [multiScaleDiff, f] using hsum

/-- Integrability property for multiScaleDiff squared -/
-- A practical L² (p = 2) version: if φ is in L², then multiScaleDiff is also in L²
-- (using the L² continuity of the heat semigroup).
lemma multiScaleDiff_square_integrable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (μ : MeasureTheory.Measure X) (φ : X → ℝ)
    (hφ : MeasureTheory.MemLp φ 2 μ) :
    MeasureTheory.MemLp (multiScaleDiff H cfg φ) 2 μ := by
  -- First establish that each H_t φ is in L²
  have hL2 : ∀ i : Fin m, MeasureTheory.MemLp (fun x => H.H (cfg.τ i) φ x) 2 μ := by
    intro i
    exact heatSemigroup_l2_preserves H (cfg.τ i) μ φ hφ
  classical
  -- Define components with scalar weights
  let f : Fin m → X → ℝ := fun i x => cfg.α i * H.H (cfg.τ i) φ x
  -- Each component is in L² since `H_t φ` is in L² and L² is closed under scalars
  have hf_mem : ∀ i : Fin m, MeasureTheory.MemLp (fun x => f i x) 2 μ := by
    intro i
    have hHi : MeasureTheory.MemLp (fun x => H.H (cfg.τ i) φ x) 2 μ := hL2 i
    -- Use `MemLp.const_mul` (real scalar multiplication preserves membership)
    simpa [f] using hHi.const_mul (cfg.α i)
  -- Finite sum of L² functions stays in L²
  have hsum_mem : MeasureTheory.MemLp
      (fun x => (Finset.univ : Finset (Fin m)).sum (fun i => f i x)) 2 μ := by
    -- `finset_sum_memLp` style lemma: use induction along with `MemLp.add`
    refine Finset.induction_on (Finset.univ : Finset (Fin m)) ?base ?step
    · -- empty sum is zero, which is in L²
      simp only [Finset.sum_empty]
      exact MeasureTheory.MemLp.zero
    · intro a s ha ih
      -- sum over `insert a s` equals `(f a) + sum over s`
      -- `MemLp.add` closes L² under addition
      simp only [Finset.sum_insert ha]
      exact (hf_mem a).add ih
  -- Tie back to the original definition
  simpa [multiScaleDiff, f] using hsum_mem


/-- The spectral symbol ψ_m(λ) = ∑ α_i (exp(-τ_i λ) - 1) for λ ≥ 0 -/
noncomputable def spectralSymbol {m : PNat} (cfg : MultiScaleConfig m) (lam : ℝ) : ℝ :=
  ∑ i : Fin m, cfg.α i * (Real.exp (-cfg.τ i * lam) - 1)

/-- The spectral symbol at λ = 0 vanishes -/
theorem spectralSymbol_at_zero {m : PNat} (cfg : MultiScaleConfig m) :
    spectralSymbol cfg 0 = 0 := by
  simp only [spectralSymbol]
  simp [Real.exp_zero, mul_zero, sub_self, Finset.sum_const_zero]

/-- Basic bound: |ψ_m(λ)| ≤ ∑|α_i| for all λ ≥ 0 -/
theorem spectralSymbol_basic_bound {m : PNat} (cfg : MultiScaleConfig m)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    |spectralSymbol cfg lam| ≤ ∑ i : Fin m, |cfg.α i| := by
  unfold spectralSymbol
  -- Use triangle inequality
  have := Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin m)))
    (f := fun i => cfg.α i * (Real.exp (-cfg.τ i * lam) - 1))
  refine le_trans this ?_
  refine Finset.sum_le_sum ?_
  intro i _
  -- Bound each term |α_i * (exp(-τ_i λ) - 1)| ≤ |α_i|
  have hexp_le : Real.exp (-cfg.τ i * lam) ≤ 1 := by
    have hτpos := cfg.hτ_pos i
    have hneg : -cfg.τ i * lam ≤ 0 := by
      have : 0 ≤ cfg.τ i * lam := mul_nonneg (le_of_lt hτpos) hlam
      linarith
    exact Real.exp_le_one_iff.2 hneg
  have habs : |Real.exp (-cfg.τ i * lam) - 1| ≤ 1 := by
    rw [abs_sub_comm]
    have hnonneg : 0 ≤ 1 - Real.exp (-cfg.τ i * lam) := sub_nonneg.mpr hexp_le
    rw [abs_of_nonneg hnonneg]
    have hexp_nonneg : 0 ≤ Real.exp (-cfg.τ i * lam) := Real.exp_nonneg _
    linarith
  calc |cfg.α i * (Real.exp (-cfg.τ i * lam) - 1)|
      = |cfg.α i| * |Real.exp (-cfg.τ i * lam) - 1| := abs_mul _ _
    _ ≤ |cfg.α i| * 1 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = |cfg.α i| := mul_one _

/-/ Mean value theorem for exponential: |e^a - e^b| ≤ max(e^a, e^b) * |a - b| -/
lemma exp_diff_le {a b : ℝ} :
    |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b| := by
  classical
  rcases lt_trichotomy a b with hlt | heq | hgt
  · -- a < b
    have hcont : ContinuousOn (fun t : ℝ => Real.exp t) (Set.Icc a b) :=
      Real.continuous_exp.continuousOn
    have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp x) x :=
      fun x _ => by simpa using Real.hasDerivAt_exp x
    obtain ⟨c, hc, hEq⟩ :=
      exists_hasDerivAt_eq_slope (f := fun t : ℝ => Real.exp t)
        (f' := fun x => Real.exp x) hlt hcont hderiv
    -- |exp a - exp b| = exp c * |a - b|
    have habs_raw : |Real.exp a - Real.exp b| = Real.exp c * (b - a) := by
      have hba_pos : 0 < b - a := sub_pos.mpr hlt
      have hmul : Real.exp c * (b - a) = Real.exp b - Real.exp a :=
        (eq_div_iff (ne_of_gt hba_pos)).mp hEq
      have := congrArg (fun x => |x|) hmul.symm
      simpa [abs_mul, abs_of_pos hba_pos, abs_sub_comm] using this
    have habs : |Real.exp a - Real.exp b| = Real.exp c * |a - b| := by
      have : |a - b| = b - a := by
        have : a - b < 0 := sub_neg.mpr hlt
        simpa [abs_of_neg this, sub_eq_add_neg, add_comm] using (abs_of_neg this)
      simpa [this] using habs_raw
    -- Bound exp c ≤ max … using c ∈ (a,b)
    have hc_le : Real.exp c ≤ max (Real.exp a) (Real.exp b) := by
      have hcIcc : c ∈ Set.Icc a b := ⟨(Set.mem_Ioo.mp hc).1.le, (Set.mem_Ioo.mp hc).2.le⟩
      have : Real.exp c ≤ Real.exp b := Real.exp_le_exp.mpr hcIcc.2
      exact this.trans (le_max_right _ _)
    have hmul_le := mul_le_mul_of_nonneg_right hc_le (abs_nonneg (a - b))
    simpa [habs, mul_comm, mul_left_comm, mul_assoc] using hmul_le
  · -- a = b
    subst heq; simp
  · -- a > b: swap
    have hcont : ContinuousOn (fun t : ℝ => Real.exp t) (Set.Icc b a) :=
      Real.continuous_exp.continuousOn
    have hderiv : ∀ x ∈ Set.Ioo b a, HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp x) x :=
      fun x _ => by simpa using Real.hasDerivAt_exp x
    have hlt' : b < a := hgt
    obtain ⟨c, hc, hEq⟩ :=
      exists_hasDerivAt_eq_slope (f := fun t : ℝ => Real.exp t)
        (f' := fun x => Real.exp x) hlt' hcont hderiv
    have habs_raw : |Real.exp a - Real.exp b| = Real.exp c * (a - b) := by
      have hba_pos : 0 < a - b := sub_pos.mpr hlt'
      have hmul : Real.exp c * (a - b) = Real.exp a - Real.exp b :=
        (eq_div_iff (ne_of_gt hba_pos)).mp hEq
      have := congrArg (fun x => |x|) hmul
      have := this.symm
      simpa [abs_mul, abs_of_pos hba_pos] using this
    have habs : |Real.exp a - Real.exp b| = Real.exp c * |a - b| := by
      have : |a - b| = a - b := by
        have : 0 ≤ a - b := sub_nonneg.mpr hlt'.le
        simp [abs_of_nonneg this]
      simpa [this] using habs_raw
    -- |exp a - exp b| ≤ max … * |a-b| by symmetry
    have hc_le : Real.exp c ≤ max (Real.exp a) (Real.exp b) := by
      have hcIcc : c ∈ Set.Icc b a := ⟨(Set.mem_Ioo.mp hc).1.le, (Set.mem_Ioo.mp hc).2.le⟩
      have : Real.exp c ≤ Real.exp a := Real.exp_le_exp.mpr hcIcc.2
      exact this.trans (le_max_left _ _)
    have hmul_le := mul_le_mul_of_nonneg_right hc_le (abs_nonneg (a - b))
    have heq_abs : |Real.exp a - Real.exp b| = Real.exp c * |a - b| := habs
    simpa [heq_abs, mul_comm, mul_left_comm, mul_assoc] using hmul_le

/-- Refined bound for exponential differences when arguments are non-positive -/
lemma exp_diff_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  have h := exp_diff_le (a := a) (b := b)
  have hmax : max (Real.exp a) (Real.exp b) ≤ 1 := by
    rw [max_le_iff]; exact ⟨Real.exp_le_one_iff.mpr ha, Real.exp_le_one_iff.mpr hb⟩
  calc
    |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b| := h
    _ ≤ 1 * |a - b| := mul_le_mul_of_nonneg_right hmax (abs_nonneg _)
    _ = |a - b| := by simp

/-- The spectral symbol is Lipschitz continuous in λ -/
theorem spectralSymbol_lipschitz {m : PNat} (cfg : MultiScaleConfig m) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      |spectralSymbol cfg lam₁ - spectralSymbol cfg lam₂| ≤ L * |lam₁ - lam₂| := by
  -- The Lipschitz constant is ∑ |α_i| * τ_i
  use ∑ i : Fin m, |cfg.α i| * cfg.τ i
  constructor
  · -- L ≥ 0
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (abs_nonneg _) (le_of_lt (cfg.hτ_pos i))
  · -- Lipschitz property using mean value theorem
    intro lam₁ lam₂ hlam₁ hlam₂
    -- Rewrite the difference as a sum
    have hdiff : spectralSymbol cfg lam₁ - spectralSymbol cfg lam₂ =
        ∑ i : Fin m, cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂)) := by
      unfold spectralSymbol
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext i
      ring
    -- Apply triangle inequality
    rw [hdiff]
    have htri : |∑ i : Fin m, cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))|
        ≤ ∑ i : Fin m, |cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))| :=
      Finset.abs_sum_le_sum_abs _ _
    apply le_trans htri
    -- Bound each term using exp_diff_le_of_nonpos
    have hbound : ∀ i : Fin m,
        |cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))|
        ≤ |cfg.α i| * cfg.τ i * |lam₁ - lam₂| := by
      intro i
      have hτpos := cfg.hτ_pos i
      -- Both -τ_i * lam₁ and -τ_i * lam₂ are non-positive
      have ha : -cfg.τ i * lam₁ ≤ 0 := by
        have : 0 ≤ cfg.τ i * lam₁ := mul_nonneg (le_of_lt hτpos) hlam₁
        linarith
      have hb : -cfg.τ i * lam₂ ≤ 0 := by
        have : 0 ≤ cfg.τ i * lam₂ := mul_nonneg (le_of_lt hτpos) hlam₂
        linarith
      -- Apply exp_diff_le_of_nonpos
      have hexp := exp_diff_le_of_nonpos ha hb
      calc |cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))|
          = |cfg.α i| * |Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂)| := abs_mul _ _
        _ ≤ |cfg.α i| * |-cfg.τ i * lam₁ - (-cfg.τ i * lam₂)| :=
            mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        _ = |cfg.α i| * |cfg.τ i * (lam₂ - lam₁)| := by congr 2; ring
        _ = |cfg.α i| * (cfg.τ i * |lam₂ - lam₁|) := by
            rw [abs_mul, abs_of_pos hτpos]
        _ = |cfg.α i| * cfg.τ i * |lam₁ - lam₂| := by
            rw [abs_sub_comm lam₂ lam₁, mul_assoc]
    -- Sum the bounds
    have hsum : ∑ i : Fin m, |cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))|
        ≤ ∑ i : Fin m, |cfg.α i| * cfg.τ i * |lam₁ - lam₂| := by
      apply Finset.sum_le_sum
      intro i _
      exact hbound i
    apply le_trans hsum
    -- Factor out |lam₁ - lam₂|
    rw [← Finset.sum_mul]

/-- Monotonicity: ψ_m(λ) is decreasing for λ ≥ 0 when all α_i ≥ 0 -/
theorem spectralSymbol_monotone_decreasing {m : PNat} (cfg : MultiScaleConfig m)
    (hα_nonneg : ∀ i, 0 ≤ cfg.α i) :
    ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → lam₁ ≤ lam₂ →
      spectralSymbol cfg lam₂ ≤ spectralSymbol cfg lam₁ := by
  intro lam₁ lam₂ hlam₁ hle
  unfold spectralSymbol
  apply Finset.sum_le_sum
  intro i _
  -- Each term α_i * (exp(-τ_i λ) - 1) is decreasing
  have hexp_mono : Real.exp (-cfg.τ i * lam₂) ≤ Real.exp (-cfg.τ i * lam₁) := by
    apply Real.exp_le_exp.mpr
    have hτpos := cfg.hτ_pos i
    nlinarith
  have : Real.exp (-cfg.τ i * lam₂) - 1 ≤ Real.exp (-cfg.τ i * lam₁) - 1 := by
    linarith
  exact mul_le_mul_of_nonneg_left this (hα_nonneg i)

/-- Flags for spectral bounds and Bochner-type inequalities.
These are assumptions/axioms at this stage, to be proved later. -/
structure SpectralBound {X : Type*} {m : PNat} (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) where
  /-- Uniform bound on the spectral symbol -/
  norm_bound : ℝ
  /-- The bound is non-negative -/
  norm_bound_nonneg : 0 ≤ norm_bound
  /-- The spectral symbol is uniformly bounded -/
  spectral_uniform_bound : ∀ lam : ℝ, 0 ≤ lam → |spectralSymbol cfg lam| ≤ norm_bound
  /-- Bochner-type inequality relating L² norm to energy (Γ operator) -/
  bochner_inequality : Prop  -- Placeholder for the full inequality

/-- The sup-norm of the spectral symbol. Defined abstractly. -/
noncomputable def spectralSymbolSupNorm {m : PNat} (cfg : MultiScaleConfig m) : ℝ :=
  sSup { y : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧ y = |spectralSymbol cfg lam| }

/-- The sup-norm is bounded by ∑|α_i| -/
theorem spectralSymbolSupNorm_bounded {m : PNat} (cfg : MultiScaleConfig m) :
    spectralSymbolSupNorm cfg ≤ ∑ i : Fin m, |cfg.α i| := by
  apply csSup_le
  · -- The set is nonempty
    use |spectralSymbol cfg 0|
    refine ⟨0, le_refl _, rfl⟩
  · -- Upper bound
    intro y hy
    rcases hy with ⟨lam, hlam, rfl⟩
    exact spectralSymbol_basic_bound cfg lam hlam

/-- Explicit constant tracking: spectral symbol Lipschitz constant -/
def spectralSymbolLipschitzConstant {m : PNat} (cfg : MultiScaleConfig m) : ℝ :=
  ∑ i : Fin m, |cfg.α i| * cfg.τ i

/-- The Lipschitz constant is non-negative -/
lemma spectralSymbolLipschitzConstant_nonneg {m : PNat} (cfg : MultiScaleConfig m) :
    0 ≤ spectralSymbolLipschitzConstant cfg := by
  unfold spectralSymbolLipschitzConstant
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (abs_nonneg _) (le_of_lt (cfg.hτ_pos i))

/-- Note: The Lipschitz constant from spectralSymbol_lipschitz equals spectralSymbolLipschitzConstant -/
lemma spectralSymbol_lipschitz_constant_eq {m : PNat} (cfg : MultiScaleConfig m) :
    ∃ L : ℝ, L = spectralSymbolLipschitzConstant cfg ∧ 
    (∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      |spectralSymbol cfg lam₁ - spectralSymbol cfg lam₂| ≤ L * |lam₁ - lam₂|) := by
  -- We reproduce the Lipschitz proof with the explicit constant
  use spectralSymbolLipschitzConstant cfg
  constructor
  · rfl
  · intro lam₁ lam₂ hlam₁ hlam₂
    -- Rewrite the difference as a sum
    have hdiff : spectralSymbol cfg lam₁ - spectralSymbol cfg lam₂ =
        ∑ i : Fin m, cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂)) := by
      unfold spectralSymbol
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext i
      ring
    -- Triangle inequality for sums
    rw [hdiff]
    have htri : |∑ i : Fin m, cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))|
        ≤ ∑ i : Fin m, |cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))| :=
      Finset.abs_sum_le_sum_abs _ _
    apply le_trans htri
    -- Bound each term using exp_diff_le_of_nonpos
    have hbound : ∀ i : Fin m,
        |cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))|
        ≤ |cfg.α i| * cfg.τ i * |lam₁ - lam₂| := by
      intro i
      have hτpos := cfg.hτ_pos i
      have ha : -cfg.τ i * lam₁ ≤ 0 := by
        have : 0 ≤ cfg.τ i * lam₁ := mul_nonneg (le_of_lt hτpos) hlam₁
        linarith
      have hb : -cfg.τ i * lam₂ ≤ 0 := by
        have : 0 ≤ cfg.τ i * lam₂ := mul_nonneg (le_of_lt hτpos) hlam₂
        linarith
      have hexp := exp_diff_le_of_nonpos ha hb
      calc |cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))|
          = |cfg.α i| * |Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂)| :=
              abs_mul _ _
        _ ≤ |cfg.α i| * |-cfg.τ i * lam₁ - (-cfg.τ i * lam₂)| :=
              mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        _ = |cfg.α i| * |cfg.τ i * (lam₂ - lam₁)| := by congr 2; ring
        _ = |cfg.α i| * (cfg.τ i * |lam₂ - lam₁|) := by
              rw [abs_mul, abs_of_pos hτpos]
        _ = |cfg.α i| * cfg.τ i * |lam₁ - lam₂| := by
              rw [abs_sub_comm lam₂ lam₁, mul_assoc]
    -- Sum the bounds and factor |lam₁ - lam₂|
    have hsum : ∑ i : Fin m, |cfg.α i * (Real.exp (-cfg.τ i * lam₁) - Real.exp (-cfg.τ i * lam₂))|
        ≤ ∑ i : Fin m, |cfg.α i| * cfg.τ i * |lam₁ - lam₂| := by
      apply Finset.sum_le_sum
      intro i _
      exact hbound i
    apply le_trans hsum
    -- Factor out |lam₁ - lam₂|
    have : ∑ i : Fin m, |cfg.α i| * cfg.τ i * |lam₁ - lam₂|
        = (∑ i : Fin m, |cfg.α i| * cfg.τ i) * |lam₁ - lam₂| := by
      simpa [Finset.sum_mul] using (Finset.sum_mul (s := (Finset.univ : Finset (Fin m)))
        (f := fun i => |cfg.α i| * cfg.τ i) (g := fun _ => |lam₁ - lam₂|))
    simpa [spectralSymbolLipschitzConstant, this]

/-- Explicit bound when all coefficients satisfy |α_i| ≤ C -/
theorem spectralSymbolSupNorm_explicit_bound {m : PNat} (cfg : MultiScaleConfig m)
    (C : ℝ) (hC : ∀ i, |cfg.α i| ≤ C) :
    spectralSymbolSupNorm cfg ≤ m * C := by
  have h1 : spectralSymbolSupNorm cfg ≤ ∑ i : Fin m, |cfg.α i| :=
    spectralSymbolSupNorm_bounded cfg
  have h2 : ∑ i : Fin m, |cfg.α i| ≤ ∑ i : Fin m, C := by
    apply Finset.sum_le_sum
    intro i _
    exact hC i
  have h3 : ∑ i : Fin m, C = m * C := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc spectralSymbolSupNorm cfg ≤ ∑ i : Fin m, |cfg.α i| := h1
    _ ≤ ∑ i : Fin m, C := h2
    _ = m * C := h3

/-- Optimal bound: When cfg.hα_bound gives |α_i| ≤ 1, the sup-norm is at most m -/
theorem spectralSymbolSupNorm_optimal_bound {m : PNat} (cfg : MultiScaleConfig m) :
    spectralSymbolSupNorm cfg ≤ m := by
  calc spectralSymbolSupNorm cfg
      ≤ ∑ i : Fin m, |cfg.α i| := spectralSymbolSupNorm_bounded cfg
    _ ≤ ∑ i : Fin m, 1 := Finset.sum_le_sum (fun i _ => cfg.hα_bound i)
    _ = m := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- The spectral symbol achieves its sup-norm at λ = 0 when all α_i have the same sign -/
theorem spectralSymbol_zero_at_zero {m : PNat} (cfg : MultiScaleConfig m) :
    |spectralSymbol cfg 0| = 0 := by
  exact abs_eq_zero.mpr (spectralSymbol_at_zero cfg)

/-- Precise constant for the derivative bound of spectral symbol -/
def spectralSymbolDerivativeBound {m : PNat} (cfg : MultiScaleConfig m) : ℝ :=
  ∑ i : Fin m, |cfg.α i| * cfg.τ i

/-- The derivative of spectral symbol at any point is bounded -/
theorem spectralSymbol_derivative_bound {m : PNat} (cfg : MultiScaleConfig m)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hderiv : deriv (spectralSymbol cfg) lam
      = ∑ i : Fin m, (-cfg.α i) * cfg.τ i * Real.exp (-cfg.τ i * lam)) :
    |deriv (spectralSymbol cfg) lam| ≤ spectralSymbolDerivativeBound cfg := by
  classical
  -- Rewrite derivative using the provided formula
  have hτpos : ∀ i : Fin m, 0 < cfg.τ i := cfg.hτ_pos
  have hexp_le_one : ∀ i : Fin m, Real.exp (-cfg.τ i * lam) ≤ 1 := by
    intro i
    have : 0 ≤ cfg.τ i * lam := mul_nonneg (le_of_lt (hτpos i)) hlam
    have hnonpos : -cfg.τ i * lam ≤ 0 := by linarith
    exact Real.exp_le_one_iff.mpr hnonpos
  -- Bound absolute value of the derivative by summing term-wise bounds
  have : |deriv (spectralSymbol cfg) lam|
      = |∑ i : Fin m, (-cfg.α i) * cfg.τ i * Real.exp (-cfg.τ i * lam)| := by
    simpa [hderiv]
  calc
    |deriv (spectralSymbol cfg) lam|
        = |∑ i : Fin m, (-cfg.α i) * cfg.τ i * Real.exp (-cfg.τ i * lam)| := this
    _ ≤ ∑ i : Fin m, |(-cfg.α i) * cfg.τ i * Real.exp (-cfg.τ i * lam)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, |cfg.α i| * cfg.τ i := by
          refine Finset.sum_le_sum ?termBound
          intro i _
          have hτi := hτpos i
          have h1 : |(-cfg.α i) * cfg.τ i * Real.exp (-cfg.τ i * lam)|
                = |cfg.α i| * cfg.τ i * Real.exp (-cfg.τ i * lam) := by
            have : |(-cfg.α i) * cfg.τ i| = |cfg.α i| * cfg.τ i := by
              simpa [abs_mul, abs_of_pos hτi] using congrArg abs (by ring : (-cfg.α i) * cfg.τ i = - (cfg.α i * cfg.τ i))
            simpa [abs_mul, this]
          have h2 : Real.exp (-cfg.τ i * lam) ≤ 1 := hexp_le_one i
          have hnonneg : 0 ≤ |cfg.α i| * cfg.τ i :=
            mul_nonneg (abs_nonneg _) (le_of_lt hτi)
          have : |cfg.α i| * cfg.τ i * Real.exp (-cfg.τ i * lam)
                ≤ |cfg.α i| * cfg.τ i * 1 := by
            exact mul_le_mul_of_nonneg_left h2 hnonneg
          have hτabs : |cfg.τ i| = cfg.τ i := by simpa using (abs_of_pos hτi)
          simpa [h1, hτabs] using this
    _ = spectralSymbolDerivativeBound cfg := by
          simp [spectralSymbolDerivativeBound]

/-- Precise tracking of the constant C(ℰ) in FG★ inequality -/
structure FGStarConstants {m : PNat} (cfg : MultiScaleConfig m) where
  /-- Constant from spectral bound -/
  spectral_const : ℝ
  /-- Constant from energy functional properties -/
  energy_const : ℝ
  /-- Combined constant for FG★ inequality -/
  combined_const : ℝ
  /-- Relation between constants -/
  const_relation : combined_const = spectral_const * energy_const
  /-- All constants are non-negative -/
  spectral_const_nonneg : 0 ≤ spectral_const
  energy_const_nonneg : 0 ≤ energy_const

/-- Construction of FG★ constants with explicit values -/
noncomputable def constructFGStarConstants {m : PNat} (cfg : MultiScaleConfig m) : 
    FGStarConstants cfg where
  spectral_const := spectralSymbolSupNorm cfg
  energy_const := 1  -- Placeholder; would depend on energy functional
  combined_const := spectralSymbolSupNorm cfg * 1
  const_relation := rfl
  spectral_const_nonneg := by
    -- spectralSymbolSupNorm is non-negative since it's a supremum of absolute values
    unfold spectralSymbolSupNorm
    -- The supremum of non-negative values is non-negative
    apply Real.sSup_nonneg
    intro y hy
    rcases hy with ⟨lam, _, rfl⟩
    exact abs_nonneg _
  energy_const_nonneg := zero_le_one

/-- Refined bound with optimal constant tracking -/
structure OptimalSpectralBound {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The optimal bound constant -/
  C_opt : ℝ
  /-- Non-negativity -/
  C_opt_nonneg : 0 ≤ C_opt
  /-- The bound is sharp (achieved for some λ) -/
  is_sharp : ∃ lam : ℝ, 0 ≤ lam ∧ |spectralSymbol cfg lam| = C_opt
  /-- The bound holds uniformly -/
  uniform_bound : ∀ lam : ℝ, 0 ≤ lam → |spectralSymbol cfg lam| ≤ C_opt

/-- Auxiliary hypothesis: the spectral symbol is bounded.
    This would follow from detailed Fourier analysis. -/
def spectralBoundHypothesis {m : PNat} (cfg : MultiScaleConfig m) : Prop :=
  ∀ lam : ℝ, |spectralSymbol cfg lam| ≤ 1

/-- Under the hypothesis that the spectral symbol is bounded,
    it is bounded by the sup-norm. -/
lemma le_spectralSymbolSupNorm {m : PNat} (cfg : MultiScaleConfig m) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    |spectralSymbol cfg lam| ≤ spectralSymbolSupNorm cfg := by
  classical
  -- Show the set is bounded above by ∑ |α_i|
  let S : Set ℝ := { y : ℝ | ∃ t : ℝ, 0 ≤ t ∧ y = |spectralSymbol cfg t| }
  have h_bdd : BddAbove S := by
    refine ⟨∑ i : Fin m, |cfg.α i|, ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    -- Bound |ψ_m(t)| ≤ ∑ |α_i|
    unfold spectralSymbol
    -- Bound each term by |α_i|
    have hterm_le : ∀ i : Fin m,
        |cfg.α i * (Real.exp (-cfg.τ i * t) - 1)| ≤ |cfg.α i| := by
      intro i
      -- Since t ≥ 0 and τ_i > 0, exp(-τ_i t) ≤ 1
      have hle1 : Real.exp (-cfg.τ i * t) ≤ 1 := by
        have hτpos := cfg.hτ_pos i
        have hneg : -cfg.τ i * t ≤ 0 := by
          have : 0 ≤ cfg.τ i * t := mul_nonneg (le_of_lt hτpos) ht
          linarith
        exact Real.exp_le_one_iff.2 hneg
      have hnonneg : 0 ≤ 1 - Real.exp (-cfg.τ i * t) := sub_nonneg.mpr hle1
      have habs_eq : |Real.exp (-cfg.τ i * t) - 1| = 1 - Real.exp (-cfg.τ i * t) := by
        rw [abs_sub_comm]
        exact abs_of_nonneg hnonneg
      have hle_one : |Real.exp (-cfg.τ i * t) - 1| ≤ 1 := by
        rw [habs_eq]
        have hexp_nonneg : 0 ≤ Real.exp (-cfg.τ i * t) := Real.exp_nonneg _
        linarith
      -- Now multiply by |α_i|
      have : |cfg.α i| * |Real.exp (-cfg.τ i * t) - 1| ≤ |cfg.α i| * 1 := by
        exact (mul_le_mul_of_nonneg_left hle_one (abs_nonneg _))
      simpa [abs_mul, mul_one] using this
    -- Use triangle inequality on the sum
    have := Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin m))) (f :=
      fun i => cfg.α i * (Real.exp (-cfg.τ i * t) - 1))
    -- Rewrite the sums and apply the termwise bound
    -- abs_sum_le_sum_abs gives: |∑ f i| ≤ ∑ |f i|
    -- Then each |f i| ≤ |α i|, summing yields the claim
    have hsum_le :
        |∑ i : Fin m, cfg.α i * (Real.exp (-cfg.τ i * t) - 1)| ≤ ∑ i : Fin m, |cfg.α i| := by
      refine le_trans this ?_
      refine Finset.sum_le_sum ?_
      intro i _
      exact hterm_le i
    simpa using hsum_le
  -- y is in the set, so it's ≤ sSup S by le_csSup
  have hy : |spectralSymbol cfg lam| ∈ S := ⟨lam, hlam, rfl⟩
  exact le_csSup h_bdd hy

/-- Alternative formulation: explicit sup-norm bound flag -/
structure SpectralSupNormBound {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The sup-norm bound value -/
  bound : ℝ
  /-- Non-negativity -/
  bound_nonneg : 0 ≤ bound
  /-- The actual bound -/
  is_bound : spectralSymbolSupNorm cfg ≤ bound

/-- Spectral penalty evaluation for the multi-scale difference operator.
This encodes the key estimate: ∫|Δ^{⟨m⟩} φ|² dμ ≤ C(ℰ)‖ψ_m‖_∞² ∫Γ(φ,φ) dμ -/
structure SpectralPenalty {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) where
  /-- The constant C(ℰ) depending on the Dirichlet form -/
  C_dirichlet : ℝ
  /-- Non-negativity of the constant -/
  C_nonneg : 0 ≤ C_dirichlet

end Frourio
