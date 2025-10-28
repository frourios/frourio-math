import Frourio.Analysis.SchwartzDensityLp.ConvolutionTheory
import Frourio.Analysis.SchwartzDensityLp.SchwartzDensityLpCore
import Frourio.Analysis.YoungInequality.YoungInequality
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Approximate Identity and Mollifier Convergence

This file establishes the convergence properties of convolution with
approximate identities (mollifiers), which are crucial for the Schwartz
density theorem.

## Main results

- `mollifier_converges_continuous`: For continuous f with compact support,
  ‖f - f * ψ_η‖_∞ → 0 as η → 0
- `mollifier_converges_Lp`: For f ∈ Lp with compact support,
  ‖f - f * ψ_η‖_p → 0 as η → 0
- `mollifier_converges_L1_compactSupport`: L¹ convergence (used in paper)
- `mollifier_converges_L2_compactSupport`: L² convergence (used in paper)

## References

- Folland, Real Analysis, Proposition 8.14
- papers/schwartz_density_constructive_analysis.md, Lemma 4.5
- papers/schwartz_density_constructive_analysis.md, Section 4.2

## Key definitions

An approximate identity (mollifier family) is a sequence {ψ_η}_{η>0} where:
1. ψ_η(x) = η^(-n) ψ(x/η) for some ψ ∈ C∞_c
2. ∫ ψ = 1 (normalization)
3. ψ ≥ 0 (positivity)
4. supp(ψ) ⊆ B_1 (compact support)

As η → 0, ψ_η "concentrates" near 0 and approximates the Dirac delta function.

-/

open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology

variable {n : ℕ}

section ApproximateIdentityDefinition

/--
**Approximate identity (mollifier) structure.**

A function ψ is a mollifier if it is smooth, compactly supported,
normalized, and non-negative.
-/
structure IsApproximateIdentity (ψ : (Fin n → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ
  compact_support : HasCompactSupport ψ
  normalized : ∫ x, ψ x = 1
  nonneg : ∀ x, 0 ≤ ψ x
  support_subset : tsupport ψ ⊆ Metric.closedBall (0 : Fin n → ℝ) 1

/--
**Scaled mollifier ψ_η.**

ψ_η(x) = η^(-n) ψ(x/η)
-/
noncomputable def scaledMollifier (ψ : (Fin n → ℝ) → ℝ) (η : ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)

end ApproximateIdentityDefinition

section UniformContinuityLemmas

/--
**Uniform continuity on compact sets.**

For f continuous with compact support, f is uniformly continuous.
-/
lemma uniformly_continuous_of_compactSupport
    (f : (Fin n → ℝ) → ℂ)
    (hf_cont : Continuous f)
    (hf_compact : HasCompactSupport f) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y,
      ‖x - y‖ < δ → ‖f x - f y‖ < ε := by
  classical
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := (Metric.uniformContinuous_iff.mp
    (hf_compact.uniformContinuous_of_continuous hf_cont)) ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro x y hxy
  have hxy' : dist x y < δ := by simpa [dist_eq_norm] using hxy
  have hε' : dist (f x) (f y) < ε := hδ hxy'
  simpa [dist_eq_norm] using hε'

lemma eventually_tail_indicator_toReal_bound
    (φ : 𝓢((Fin n → ℝ), ℂ))
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (δ : ℝ)
    (coreSet : Set (Fin n → ℝ))
    (h_core_volume_lt_top : volume coreSet < ⊤)
    (h_tail_indicator_eventually_one :
      ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
        eLpNorm
            (fun x =>
              Set.indicator coreSetᶜ
                (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
            1 volume
          ≤ ENNReal.ofReal δ)
    (h_tail_indicator_eLpNorm_ne_top :
      ∀ y : Fin n → ℝ,
        eLpNorm
            (fun x =>
              Set.indicator coreSetᶜ
                (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
            p volume ≠ ∞)
    (h_tail_indicator_bound :
      ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
        eLpNorm
            (fun x =>
              Set.indicator coreSetᶜ
                (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
            p volume
          ≤
            (volume coreSet) ^ (1 / p.toReal)
              * ENNReal.ofReal (δ / 2)) :
    ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
      (eLpNorm
          (fun x =>
            Set.indicator coreSetᶜ
              (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
          p volume).toReal
        ≤
          ((volume coreSet) ^ (1 / p.toReal) * ENNReal.ofReal (δ / 2)).toReal := by
  classical
  refine
    (h_tail_indicator_eventually_one.and
        ((Filter.Eventually.of_forall fun y =>
            h_tail_indicator_eLpNorm_ne_top y).and
          h_tail_indicator_bound)).mono ?_
  intro y hy
  rcases hy with ⟨-, hy⟩
  rcases hy with ⟨hy_fin, hy_bound⟩
  have hp_pos : (0 : ℝ≥0∞) < p := lt_of_lt_of_le (by simp) hp
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have hp_toReal_pos : 0 < p.toReal :=
    ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have h_exp_nonneg : 0 ≤ 1 / p.toReal := by
    have h_nonneg : 0 ≤ p.toReal := hp_toReal_pos.le
    have h_inv_nonneg := inv_nonneg.mpr h_nonneg
    simp [one_div]
  have h_pow_ne_top :
      (volume coreSet) ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg
      (ne_of_lt h_core_volume_lt_top)
  have h_mul_ne_top :
      (volume coreSet) ^ (1 / p.toReal) * ENNReal.ofReal (δ / 2) ≠ ∞ :=
    ENNReal.mul_ne_top h_pow_ne_top (by simp)
  have :=
    (ENNReal.toReal_le_toReal hy_fin h_mul_ne_top).mpr hy_bound
  simpa using this

end UniformContinuityLemmas
