import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Frourio.Analysis.SchwartzDensityLp.ConvolutionTheory
import Frourio.Analysis.SchwartzDensityLp.SchwartzDensityLpCore
import Frourio.Analysis.SchwartzDensityLp.YoungInequality

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

lemma core_indicator_eLpNorm_bound
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    {coreSet : Set (Fin n → ℝ)}
    (h_core_meas : MeasurableSet coreSet)
    (h_core_volume_lt_top : volume coreSet < ⊤)
    {g : (Fin n → ℝ) → ℂ} {δ : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (h_bound :
      ∀ᵐ x ∂volume.restrict coreSet, ‖g x‖ ≤ δ) :
  eLpNorm (fun x => Set.indicator coreSet g x) p volume
    ≤ (volume coreSet) ^ (1 / p.toReal) * ENNReal.ofReal δ := by
  sorry

lemma tail_indicator_eLpNorm_bound
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    {tailSet : Set (Fin n → ℝ)} (h_tail_meas : MeasurableSet tailSet)
    {g : (Fin n → ℝ) → ℂ} (hg_mem : MemLp g p volume)
    {δ : ℝ} (hδ_nonneg : 0 ≤ δ)
    (h_tail :
      ∫⁻ x, ‖g x‖ₑ ∂(volume.restrict tailSet)
        ≤ ENNReal.ofReal δ) :
  eLpNorm (fun x => Set.indicator tailSet g x) p volume
    ≤ ENNReal.ofReal δ := by
  sorry

set_option maxHeartbeats 1000000 in
-- Increase heartbeats to accommodate the long proof search below.
lemma translation_tendsto_of_schwartz
    (φ : 𝓢((Fin n → ℝ), ℂ))
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞) :
    Filter.Tendsto
      (fun y : Fin n → ℝ =>
        eLpNorm (fun x => (φ : (Fin n → ℝ) → ℂ) (x - y) - φ x) p volume)
      (𝓝 (0 : Fin n → ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  classical
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro ε hε
  by_cases hε_top : ε = ⊤
  · refine Filter.Eventually.of_forall ?_
    intro y
    simp [hε_top]
  have hε_lt_top : ε < ⊤ := lt_of_le_of_ne le_top hε_top
  have hε_toReal_pos : 0 < ε.toReal :=
    ENNReal.toReal_pos (by exact ne_of_gt hε) hε_top
  set δ : ℝ := ε.toReal / 2 with hδ_def
  have hδ_pos : 0 < δ := by
    have : (0 : ℝ) < 2 := by norm_num
    simpa [hδ_def] using div_pos hε_toReal_pos this
  have hδ_lt_ε_toReal : δ < ε.toReal := by
    simpa [hδ_def] using half_lt_self hε_toReal_pos
  have hδ_lt : ENNReal.ofReal δ < ε := by
    have : ENNReal.ofReal δ < ENNReal.ofReal ε.toReal :=
      (ENNReal.ofReal_lt_ofReal_iff hε_toReal_pos).2 hδ_lt_ε_toReal
    simpa [ENNReal.ofReal_toReal, hε_top] using this
  have hδ_half_pos : 0 < δ / 2 := by simpa using half_pos hδ_pos
  have hδ_half_lt_δ : ENNReal.ofReal (δ / 2) < ENNReal.ofReal δ :=
    (ENNReal.ofReal_lt_ofReal_iff hδ_pos).2 (half_lt_self hδ_pos)
  have hδ_half_lt : ENNReal.ofReal (δ / 2) < ε :=
    lt_of_lt_of_le hδ_half_lt_δ hδ_lt.le
  let Φ : (Fin n → ℝ) → ℝ≥0∞ :=
    fun y => eLpNorm (fun x => (φ : (Fin n → ℝ) → ℂ) (x - y) - φ x) p volume
  have hΦ0 : Φ 0 = 0 := by
    simp [Φ]
  have hφ_mem : MemLp (fun x => (φ : (Fin n → ℝ) → ℂ) x) p volume := by
    simpa using (SchwartzMap.memLp (φ) (p := p) (μ := volume))
  have hφ_mem_one : MemLp (fun x => (φ : (Fin n → ℝ) → ℂ) x) 1 volume := by
    simpa using (SchwartzMap.memLp (φ) (p := (1 : ℝ≥0∞)) (μ := volume))
  obtain ⟨R₀, hR₀_pos, h_tail₀⟩ :=
    integrable_tail_small
      (f := fun x => (φ : (Fin n → ℝ) → ℂ) x)
      (hf := hφ_mem_one)
      (ε := δ / 2) hδ_half_pos
  set R : ℝ := 2 * R₀ with hR_def
  have hR_pos : 0 < R := by
    have hpos : 0 < (2 : ℝ) := by norm_num
    simpa [hR_def] using (mul_pos hpos hR₀_pos)
  have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
  have hR₀_le_R : R₀ ≤ R := by
    have h_diff : R - R₀ = R₀ := by
      simp [hR_def, two_mul, sub_eq_add_neg]
    have h_nonneg : 0 ≤ R - R₀ := by
      simpa [h_diff] using (le_of_lt hR₀_pos : 0 ≤ R₀)
    simpa [sub_eq_add_neg] using (sub_nonneg.mp h_nonneg)
  have hφ_integrable : Integrable (fun x => (φ : (Fin n → ℝ) → ℂ) x) volume :=
    (memLp_one_iff_integrable).1 hφ_mem_one
  have hφ_norm_integrable : Integrable (fun x => ‖(φ : (Fin n → ℝ) → ℂ) x‖) volume :=
    hφ_integrable.norm
  have h_tail_integrable₀ :
      Integrable (fun x => ‖(φ : (Fin n → ℝ) → ℂ) x‖)
        (volume.restrict {x | R₀ ≤ ‖x‖}) :=
    hφ_norm_integrable.restrict (s := {x | R₀ ≤ ‖x‖})
  have h_tail_bound :
      ∫ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ ∂(volume.restrict {x | R ≤ ‖x‖})
        < δ / 2 := by
    classical
    have h_nonneg : ∀ x, 0 ≤ ‖(φ : (Fin n → ℝ) → ℂ) x‖ :=
      fun x => norm_nonneg _
    have :=
      tail_bound_mono
        (F := fun x : (Fin n → ℝ) => ‖(φ : (Fin n → ℝ) → ℂ) x‖)
        (R₁ := R₀) (R₂ := R) (ε := δ / 2)
        (hR := hR₀_le_R) (h_nonneg := h_nonneg)
        (h_int := h_tail_integrable₀)
        (h_bound := h_tail₀)
    simpa using this
  let tailSet : Set (Fin n → ℝ) := {x | R ≤ ‖x‖}
  have h_tail_meas : MeasurableSet tailSet :=
    by
      classical
      simpa [tailSet] using measurable_set_norm_ge (n := n) (R := R)
  have hφ_cont : Continuous fun x => (φ : (Fin n → ℝ) → ℂ) x :=
    SchwartzMap.continuous φ
  have hφ_aemeas_volume :
      AEMeasurable (fun x => (φ : (Fin n → ℝ) → ℂ) x) volume :=
    hφ_cont.aemeasurable
  have hφ_tail_aemeas :
      AEMeasurable (fun x => (φ : (Fin n → ℝ) → ℂ) x)
        (volume.restrict tailSet) :=
    hφ_aemeas_volume.mono_measure
      (Measure.restrict_le_self (μ := volume) (s := tailSet))
  have hφ_trans_cont :
      ∀ y : Fin n → ℝ,
        Continuous fun x => (φ : (Fin n → ℝ) → ℂ) (x - y) := by
    intro y
    have h_sub : Continuous fun x : (Fin n → ℝ) => x - y := by
      simpa [sub_eq_add_neg]
        using
          (continuous_id.add
              (continuous_const : Continuous fun _ : (Fin n → ℝ) => (-y)))
    exact hφ_cont.comp h_sub
  have hφ_trans_aemeas :
      ∀ y : Fin n → ℝ,
        AEMeasurable
          (fun x => (φ : (Fin n → ℝ) → ℂ) (x - y)) volume := by
    intro y
    exact (hφ_trans_cont y).aemeasurable
  have hφ_trans_tail_aemeas :
      ∀ y : Fin n → ℝ,
        AEMeasurable
          (fun x => (φ : (Fin n → ℝ) → ℂ) (x - y))
          (volume.restrict tailSet) := by
    intro y
    exact (hφ_trans_aemeas y).mono_measure
      (Measure.restrict_le_self (μ := volume) (s := tailSet))
  have h_tail_lintegral_bound :
      ∀ y : Fin n → ℝ,
        ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) (x - y) - φ x‖ₑ
            ∂(volume.restrict tailSet)
          ≤
            ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) (x - y)‖ₑ
                ∂(volume.restrict tailSet)
              + ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ
                ∂(volume.restrict tailSet) :=
    by
      intro y
      classical
      have :=
        lintegral_tail_enorm_sub_le
          (f := fun x => (φ : (Fin n → ℝ) → ℂ) (x - y))
          (φ := fun x => (φ : (Fin n → ℝ) → ℂ) x)
          (R := R)
          (hφ := hφ_tail_aemeas)
      simpa [tailSet] using this
  have h_tail_integrable :
      Integrable (fun x => (φ : (Fin n → ℝ) → ℂ) x)
        (volume.restrict tailSet) :=
    hφ_integrable.restrict (s := tailSet)
  have h_tail_nonneg :
      0 ≤ᵐ[volume.restrict tailSet]
        fun x => ‖(φ : (Fin n → ℝ) → ℂ) x‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  have h_tail_lintegral :
      ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ ∂(volume.restrict tailSet)
        = ENNReal.ofReal
            (∫ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ ∂(volume.restrict tailSet)) :=
    by
      classical
      simpa using
        (lintegral_enorm_of_nonneg
            (μ := volume.restrict tailSet)
            (f := fun x : (Fin n → ℝ) =>
              ‖(φ : (Fin n → ℝ) → ℂ) x‖)
            (fun _ => norm_nonneg _)).trans
          ((ofReal_integral_eq_lintegral_ofReal
              (μ := volume.restrict tailSet)
              (f := fun x : (Fin n → ℝ) =>
                ‖(φ : (Fin n → ℝ) → ℂ) x‖)
              h_tail_integrable.norm h_tail_nonneg).symm)
  have h_tail_le :
      ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ ∂(volume.restrict tailSet)
        ≤ ENNReal.ofReal (δ / 2) := by
    have h_real_le :
        ∫ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ ∂(volume.restrict tailSet)
          ≤ δ / 2 := le_of_lt h_tail_bound
    have := ENNReal.ofReal_le_ofReal h_real_le
    simpa [h_tail_lintegral] using this
  have h_tail_subset :
      ∀ {y : Fin n → ℝ}, ‖y‖ ≤ R₀ →
        tailSet ⊆ {x : (Fin n → ℝ) | R₀ ≤ ‖x - y‖} := by
    intro y hy x hx
    have hR₀_le : R₀ ≤ R - ‖y‖ := by
      have h_le := sub_le_sub_left hy R
      have hR_sub : R - R₀ = R₀ := by
        simp [hR_def, two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      simpa [hR_sub] using h_le
    have hx_norm : R ≤ ‖x‖ := by
      simpa [tailSet] using hx
    have h_triangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using norm_add_le (x - y) y
    have h_sub : ‖x‖ - ‖y‖ ≤ ‖x - y‖ :=
      (sub_le_iff_le_add).2 h_triangle
    have hR_minus_le : R - ‖y‖ ≤ ‖x - y‖ := by
      have h_aux : R - ‖y‖ ≤ ‖x‖ - ‖y‖ :=
        by simpa using sub_le_sub_right hx_norm ‖y‖
      exact h_aux.trans h_sub
    exact hR₀_le.trans hR_minus_le
  set tailSet₀ : Set (Fin n → ℝ) := {x | R₀ ≤ ‖x‖}
  have h_tail_meas₀ : MeasurableSet tailSet₀ := by
    classical
    simpa [tailSet₀] using measurable_set_norm_ge (n := n) (R := R₀)
  have h_tail_nonneg₀ :
      0 ≤ᵐ[volume.restrict tailSet₀]
        fun x => ‖(φ : (Fin n → ℝ) → ℂ) x‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  have h_tail_lintegrable₀ :
      Integrable (fun x => (φ : (Fin n → ℝ) → ℂ) x)
        (volume.restrict tailSet₀) :=
    hφ_integrable.restrict (s := tailSet₀)
  have h_tail_norm_integrable₀ :
      Integrable (fun x => ‖(φ : (Fin n → ℝ) → ℂ) x‖)
        (volume.restrict tailSet₀) :=
    h_tail_lintegrable₀.norm
  have h_tail_lintegral₀ :
      ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ ∂(volume.restrict tailSet₀)
        = ENNReal.ofReal
            (∫ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ ∂(volume.restrict tailSet₀)) :=
    by
      classical
      simpa [tailSet₀]
        using
          (lintegral_enorm_of_nonneg
              (μ := volume.restrict tailSet₀)
              (f := fun x : (Fin n → ℝ) =>
                ‖(φ : (Fin n → ℝ) → ℂ) x‖)
              (fun _ => norm_nonneg _)).trans
            ((ofReal_integral_eq_lintegral_ofReal
                (μ := volume.restrict tailSet₀)
                (f := fun x : (Fin n → ℝ) =>‖(φ : (Fin n → ℝ) → ℂ) x‖)
                h_tail_norm_integrable₀ h_tail_nonneg₀).symm)
  have h_tail_le₀ :
      ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ ∂(volume.restrict tailSet₀)
        ≤ ENNReal.ofReal (δ / 2) :=
    by
      have h_real_le :
          ∫ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ ∂(volume.restrict tailSet₀)
            ≤ δ / 2 := (le_of_lt h_tail₀)
      have := ENNReal.ofReal_le_ofReal h_real_le
      simpa [h_tail_lintegral₀] using this
  clear h_tail_lintegrable₀ h_tail_norm_integrable₀
  have h_tail_shift_le :
      ∀ {y : Fin n → ℝ}, ‖y‖ ≤ R₀ →
        ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) (x - y)‖ₑ ∂(volume.restrict tailSet)
          ≤ ENNReal.ofReal (δ / 2) := by
    intro y hy
    classical
    let tailSetShift : Set (Fin n → ℝ) := {z | z + y ∈ tailSet}
    have h_meas_add :
        Measurable fun z : (Fin n → ℝ) => z + y :=
      (continuous_id.add continuous_const).measurable
    have h_meas_sub :
        Measurable fun z : (Fin n → ℝ) => z - y := by
      simpa [sub_eq_add_neg]
        using (continuous_id.add (continuous_const : Continuous fun _ => (-y))).measurable
    have h_tailShift_meas : MeasurableSet tailSetShift := by
      simpa [tailSetShift, Set.preimage, Set.mem_setOf_eq]
        using h_meas_add h_tail_meas
    have h_tailShift_subset : tailSetShift ⊆ tailSet₀ := by
      intro z hz
      have hz_tail : z + y ∈ tailSet := hz
      have hz_norm := h_tail_subset (y := y) hy hz_tail
      simpa [tailSetShift, tailSet₀, Set.mem_setOf_eq, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hz_norm
    have h_map_eq :
        Measure.map (fun x : (Fin n → ℝ) => x - y)
            (volume.restrict tailSet)
          = volume.restrict tailSetShift := by
      refine Measure.ext (fun s hs => ?_)
      have h_map_apply :
          Measure.map (fun x : (Fin n → ℝ) => x - y)
              (volume.restrict tailSet) s
            = volume (((fun x => x - y) ⁻¹' s) ∩ tailSet) := by
        simp [Measure.map_apply, h_meas_sub, Measure.restrict_apply,
          hs, h_tail_meas]
      have h_restrict :
          volume.restrict tailSetShift s
            = volume (tailSetShift ∩ s) := by
        simp [Measure.restrict_apply, hs, h_tailShift_meas, Set.inter_comm]
      have h_volume_eq :
          volume (((fun x => x - y) ⁻¹' s) ∩ tailSet)
            = volume (tailSetShift ∩ s) := by
        have h_preimage :
            (fun z : (Fin n → ℝ) => z + y) ⁻¹'
                (tailSet ∩ {x : (Fin n → ℝ) | x - y ∈ s})
              = tailSetShift ∩ s := by
          ext z; constructor <;> intro hz
          · rcases hz with ⟨hz_tail, hz_s⟩
            have hz_s' : z ∈ s := by
              simpa [sub_eq_add_neg]
                using hz_s
            exact ⟨by simpa [tailSetShift] using hz_tail, hz_s'⟩
          · rcases hz with ⟨hz_shift, hz_s⟩
            have hz_tail : z + y ∈ tailSet := by
              simpa [tailSetShift] using hz_shift
            refine ⟨hz_tail, ?_⟩
            simpa [sub_eq_add_neg] using hz_s
        have h_meas_aux :
            MeasurableSet
              (tailSet ∩ {x : (Fin n → ℝ) | x - y ∈ s}) := by
          refine h_tail_meas.inter ?_
          have :
              (fun x : (Fin n → ℝ) => x - y) ⁻¹' s
                = {x : (Fin n → ℝ) | x - y ∈ s} := by rfl
          simpa [this] using h_meas_sub hs
        have h_map_self :=
          congrArg (fun μ => μ
              (tailSet ∩ {x : (Fin n → ℝ) | x - y ∈ s}))
            (map_add_right_eq_self (μ := volume) y)
        have h_map_apply₂ :
            Measure.map (fun z : (Fin n → ℝ) => z + y) volume
                (tailSet ∩ {x : (Fin n → ℝ) | x - y ∈ s})
              = volume ((fun z : (Fin n → ℝ) => z + y) ⁻¹'
                  (tailSet ∩ {x : (Fin n → ℝ) | x - y ∈ s})) :=
          by
            exact Measure.map_apply (μ := volume) h_meas_add h_meas_aux
        have h_eq :
            volume (tailSetShift ∩ s)
              = volume (tailSet ∩ {x : (Fin n → ℝ) | x - y ∈ s}) := by
          simpa [h_map_apply₂, h_preimage] using h_map_self
        have h_inter :
            ((fun x : (Fin n → ℝ) => x - y) ⁻¹' s) ∩ tailSet
              = tailSet ∩ {x : (Fin n → ℝ) | x - y ∈ s} := by
          ext z
          constructor <;> intro hz
          · rcases hz with ⟨hz_pre, hz_tail⟩
            have hz' : z - y ∈ s := by
              simpa [Set.mem_preimage] using hz_pre
            refine ⟨hz_tail, ?_⟩
            simpa [Set.mem_setOf_eq] using hz'
          · rcases hz with ⟨hz_tail, hz_pre⟩
            have hz' : z - y ∈ s := by
              simpa [Set.mem_setOf_eq] using hz_pre
            refine ⟨?_, hz_tail⟩
            simpa [Set.mem_preimage] using hz'
        simpa [h_inter] using h_eq.symm
      have h_measure_eq :
          Measure.map (fun x : (Fin n → ℝ) => x - y)
              (volume.restrict tailSet) s
            = volume.restrict tailSetShift s := by
        calc
          Measure.map (fun x : (Fin n → ℝ) => x - y)
              (volume.restrict tailSet) s
              = volume (((fun x : (Fin n → ℝ) => x - y) ⁻¹' s) ∩ tailSet) :=
                by simp [h_map_apply]
          _ = volume (tailSetShift ∩ s) := h_volume_eq
          _ = volume.restrict tailSetShift s :=
                h_restrict.symm
      exact h_measure_eq
    have hφ_norm_real :
        AEMeasurable
          (fun x : (Fin n → ℝ) =>
            ‖(φ : (Fin n → ℝ) → ℂ) x‖)
          (volume.restrict tailSetShift) :=
      (hφ_cont.norm.aemeasurable).mono_measure
        (Measure.restrict_le_self (μ := volume) (s := tailSetShift))
    have hφ_norm_meas :
        AEMeasurable
          (fun x : (Fin n → ℝ) =>
            ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ)
          (volume.restrict tailSetShift) := by
      simpa using hφ_norm_real.ennreal_ofReal
    have hφ_norm_meas_map :
        AEMeasurable
          (fun x : (Fin n → ℝ) =>
            ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ)
          (Measure.map (fun x : (Fin n → ℝ) => x - y)
            (volume.restrict tailSet)) := by
      simpa [h_map_eq] using hφ_norm_meas
    have h_shift_aemeas :
        AEMeasurable (fun x : (Fin n → ℝ) => x - y)
          (volume.restrict tailSet) :=
      h_meas_sub.aemeasurable
    have h_lintegral_eq :
        ∫⁻ x,
            ‖(φ : (Fin n → ℝ) → ℂ) (x - y)‖ₑ
              ∂(volume.restrict tailSet)
          =
            ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ
              ∂(volume.restrict tailSetShift) := by
      have :=
        (lintegral_map' hφ_norm_meas_map h_shift_aemeas).symm
      simpa [h_map_eq]
        using this
    have h_shift_subset : tailSetShift ⊆ tailSet₀ :=
      h_tailShift_subset
    have h_lintegral_le :
        ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ
            ∂(volume.restrict tailSetShift)
          ≤ ENNReal.ofReal (δ / 2) := by
      have :=
        lintegral_mono_set (μ := volume)
          (f := fun x : (Fin n → ℝ) =>
            ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ)
          (s := tailSetShift) (t := tailSet₀)
          h_shift_subset
      have := this.trans h_tail_le₀
      simpa [Measure.restrict_restrict, h_tailShift_meas] using this
    have h_lintegral_shift :=
      h_lintegral_eq ▸ h_lintegral_le
    exact h_lintegral_shift
  have h_tail_total :
      ∀ {y : Fin n → ℝ}, ‖y‖ ≤ R₀ →
        ∫⁻ x, ‖(φ : (Fin n → ℝ) → ℂ) (x - y)‖ₑ
            ∂(volume.restrict tailSet)
          ≤ ENNReal.ofReal (δ / 2) :=
    h_tail_shift_le
  clear h_tail_shift_le
  -- Control the tail contribution of the translated function.
  have h_tail_translate :
      ∀ {y : Fin n → ℝ}, ‖y‖ ≤ R₀ →
        ∫⁻ x,
            ‖(φ : (Fin n → ℝ) → ℂ) (x - y) - φ x‖ₑ
              ∂(volume.restrict tailSet)
          ≤ ENNReal.ofReal δ := by
    intro y hy
    have h_bound := h_tail_lintegral_bound y
    have h₁ := h_tail_total hy
    have h₂ := h_tail_le
    have h_nonneg : 0 ≤ δ / 2 := le_of_lt hδ_half_pos
    have h_sum :
        (∫⁻ (x : Fin n → ℝ) in tailSet, ‖(φ : (Fin n → ℝ) → ℂ) (x - y)‖ₑ)
            + ∫⁻ (x : Fin n → ℝ) in tailSet, ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ
          ≤ ENNReal.ofReal δ := by
      calc
        (∫⁻ (x : Fin n → ℝ) in tailSet,
              ‖(φ : (Fin n → ℝ) → ℂ) (x - y)‖ₑ)
              + ∫⁻ (x : Fin n → ℝ) in tailSet, ‖(φ : (Fin n → ℝ) → ℂ) x‖ₑ
            ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
              add_le_add h₁ h₂
        _ = ENNReal.ofReal (δ / 2 + δ / 2) := by
              simpa using (ENNReal.ofReal_add h_nonneg h_nonneg).symm
        _ = ENNReal.ofReal δ := by
              simp [add_halves]
    exact h_bound.trans h_sum
  -- Control the tail contribution uniformly in a neighborhood of the origin.
  have h_tail_eventually :
      ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
        ∫⁻ (x : Fin n → ℝ) in tailSet,
            ‖(φ : (Fin n → ℝ) → ℂ) (x - y) - φ x‖ₑ
          ≤ ENNReal.ofReal δ := by
    have h_small :
        ∀ᶠ y in 𝓝 (0 : Fin n → ℝ), ‖y‖ < R₀ := by
      simpa [Metric.ball, dist_eq_norm, sub_eq_add_neg]
        using Metric.ball_mem_nhds (0 : Fin n → ℝ) hR₀_pos
    refine h_small.mono ?_
    intro y hy
    have hy_le : ‖y‖ ≤ R₀ := le_of_lt hy
    exact h_tail_translate hy_le
  -- Control the integrand on the inner core uniformly using uniform continuity.
  set coreSet : Set (Fin n → ℝ) :=
      Metric.closedBall (0 : Fin n → ℝ) R with h_core_def
  set coreSetPlus : Set (Fin n → ℝ) :=
      Metric.closedBall (0 : Fin n → ℝ) (R + 1) with h_corePlus_def
  have h_core_subset : coreSet ⊆ coreSetPlus := by
    intro x hx
    have hx_norm_le : ‖x‖ ≤ R := by
      simpa [coreSet, h_core_def, dist_eq_norm]
        using Metric.mem_closedBall.mp hx
    have hR_le : R ≤ R + 1 := by linarith
    have hx_norm_le' : ‖x‖ ≤ R + 1 := le_trans hx_norm_le hR_le
    exact Metric.mem_closedBall.mpr
      (by simpa [coreSetPlus, h_corePlus_def, dist_eq_norm] using hx_norm_le')
  have h_corePlus_compact : IsCompact coreSetPlus := by
    simpa [coreSetPlus, h_corePlus_def]
      using isCompact_closedBall (0 : Fin n → ℝ) (R + 1)
  have hφ_cont_on :
      ContinuousOn (fun x : Fin n → ℝ => (φ : (Fin n → ℝ) → ℂ) x) coreSetPlus :=
    (SchwartzMap.continuous φ).continuousOn
  have h_corePlus_uc :
      UniformContinuousOn
        (fun x : Fin n → ℝ => (φ : (Fin n → ℝ) → ℂ) x) coreSetPlus :=
    h_corePlus_compact.uniformContinuousOn_of_continuous hφ_cont_on
  have h_core_uniform :
      ∀ ε > 0, ∃ δ₁ > 0, ∀ y : Fin n → ℝ,
        ‖y‖ < δ₁ →
          ∀ x ∈ coreSet,
            ‖(φ : (Fin n → ℝ) → ℂ) (x - y) - φ x‖ < ε := by
    classical
    intro ε hε
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
      Metric.uniformContinuousOn_iff.mp h_corePlus_uc ε hε
    refine ⟨min δ₁ 1, lt_min hδ₁_pos zero_lt_one, ?_⟩
    intro y hy x hx_core
    have hy_lt_δ₁ : ‖y‖ < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
    have hy_lt_one : ‖y‖ < (1 : ℝ) := lt_of_lt_of_le hy (min_le_right _ _)
    have hy_le_one : ‖y‖ ≤ (1 : ℝ) := le_of_lt hy_lt_one
    have hx_mem_plus : x ∈ coreSetPlus := h_core_subset hx_core
    have hx_norm_le : ‖x‖ ≤ R := by
      simpa [coreSet, h_core_def, dist_eq_norm]
        using Metric.mem_closedBall.mp hx_core
    have hx_minus_mem_plus : x - y ∈ coreSetPlus := by
      have hx_minus_le : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := by
        simpa [sub_eq_add_neg] using norm_add_le x (-y)
      have hx_sum_le : ‖x‖ + ‖y‖ ≤ R + 1 := by
        have := add_le_add hx_norm_le hy_le_one
        simpa using this
      have hx_bound : ‖x - y‖ ≤ R + 1 := le_trans hx_minus_le hx_sum_le
      exact Metric.mem_closedBall.mpr
        (by simpa [coreSetPlus, h_corePlus_def, dist_eq_norm] using hx_bound)
    have hdist_lt : dist x (x - y) < δ₁ := by
      simpa [dist_eq_norm, sub_eq_add_neg] using hy_lt_δ₁
    have h_apply := hδ₁ x hx_mem_plus (x - y) hx_minus_mem_plus hdist_lt
    have hnorm_lt' :
        ‖(φ : (Fin n → ℝ) → ℂ) x - φ (x - y)‖ < ε := by
      simpa [dist_eq_norm, sub_eq_add_neg] using h_apply
    have hnorm_lt :
        ‖(φ : (Fin n → ℝ) → ℂ) (x - y) - φ x‖ < ε := by
      simpa [norm_sub_rev] using hnorm_lt'
    exact hnorm_lt
  have h_core_eventually :
      ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
        ∀ x ∈ coreSet,
          ‖(φ : (Fin n → ℝ) → ℂ) (x - y) - φ x‖ ≤ δ / 2 := by
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
      h_core_uniform (δ / 2) (half_pos hδ_pos)
    refine (Metric.eventually_nhds_iff).2 ?_
    refine ⟨δ₁, hδ₁_pos, ?_⟩
    intro y hy x hx_core
    have hy_norm : ‖y‖ < δ₁ := by simpa [dist_eq_norm] using hy
    have hy_bound := hδ₁ y hy_norm x hx_core
    exact (le_of_lt hy_bound)
  have h_core_meas : MeasurableSet coreSet := by
    simpa [coreSet, h_core_def]
      using
        (Metric.isClosed_closedBall :
          IsClosed (Metric.closedBall (0 : Fin n → ℝ) R)).measurableSet
  have h_core_volume_lt_top : volume coreSet < ⊤ := by
    simpa [coreSet, h_core_def]
      using
        (MeasureTheory.measure_closedBall_lt_top
          (x := (0 : Fin n → ℝ)) (r := R))
  have h_core_indicator_eventually :
      ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
        eLpNorm
            (fun x =>
              Set.indicator coreSet
                (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
            p volume
          ≤
            (volume coreSet) ^ (1 / p.toReal) * ENNReal.ofReal (δ / 2) := by
    have h_core_volume_ne_top : volume coreSet ≠ ∞ :=
      ne_of_lt h_core_volume_lt_top
    refine h_core_eventually.mono ?_
    intro y hy
    have hy_all :
        ∀ᵐ x ∂volume,
          x ∈ coreSet →
            ‖(φ : (Fin n → ℝ) → ℂ) (x - y) - φ x‖ ≤ δ / 2 :=
      Filter.Eventually.of_forall fun x hx => hy x hx
    have hy_ae :
        ∀ᵐ x ∂volume.restrict coreSet,
          ‖(φ : (Fin n → ℝ) → ℂ) (x - y) - φ x‖ ≤ δ / 2 :=
      (MeasureTheory.ae_restrict_iff' h_core_meas).2 hy_all
    have h_indicator_eq :
        eLpNorm
            (fun x =>
              Set.indicator coreSet
                (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
            p volume
          =
            eLpNorm (fun x => (φ : (Fin n → ℝ) → ℂ) (x - y) - φ x)
              p (volume.restrict coreSet) := by
      simpa [coreSet, h_core_def, sub_eq_add_neg]
        using
          (eLpNorm_indicator_eq_eLpNorm_restrict
            (μ := volume) (s := coreSet)
            (f := fun x => (φ : (Fin n → ℝ) → ℂ) (x - y) - φ x)
            h_core_meas)
    have h_le :=
      (eLpNorm_le_of_ae_bound
          (μ := volume.restrict coreSet) (p := p)
          (f := fun x => (φ : (Fin n → ℝ) → ℂ) (x - y) - φ x)
          hy_ae)
    have h_measure_eq :
        volume.restrict coreSet Set.univ = volume coreSet := by
      simp [Measure.restrict_apply, h_core_meas]
    simpa [h_indicator_eq, h_measure_eq]
      using h_le
  -- Control the contribution of the core ball by combining the previous bounds.
  have h_split_eventually :
      ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
        Φ y ≤
          eLpNorm
              (fun x =>
                Set.indicator coreSet
                  (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
              p volume
            +
              eLpNorm
                (fun x =>
                  Set.indicator coreSetᶜ
                    (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
                p volume := by
    refine Filter.Eventually.of_forall ?_
    intro y
    classical
    set g : (Fin n → ℝ) → ℂ :=
      fun x => (φ : (Fin n → ℝ) → ℂ) (x - y) - φ x
    have hg_meas : AEMeasurable g volume :=
      (hφ_trans_aemeas y).sub hφ_aemeas_volume
    have h_core_compl_meas : MeasurableSet coreSetᶜ :=
      h_core_meas.compl
    have h_core_indicator_meas :
        AEStronglyMeasurable (fun x => Set.indicator coreSet g x) volume :=
      (hg_meas.indicator h_core_meas).aestronglyMeasurable
    have h_tail_indicator_meas :
        AEStronglyMeasurable (fun x => Set.indicator coreSetᶜ g x) volume :=
      (hg_meas.indicator h_core_compl_meas).aestronglyMeasurable
    have h_add_le :=
      eLpNorm_add_le (μ := volume) (p := p)
        h_core_indicator_meas h_tail_indicator_meas hp
    have h_sum_decomp :
        eLpNorm g p volume
          ≤
            eLpNorm (fun x => Set.indicator coreSet g x) p volume
              +
                eLpNorm
                  (fun x =>
                    Set.indicator coreSetᶜ g x) p volume := by
      have h_decomp :
          (fun x =>
              Set.indicator coreSet g x
                + Set.indicator coreSetᶜ g x)
            = g := by
        funext x
        classical
        by_cases hx : x ∈ coreSet
        · have hx_compl : x ∉ coreSetᶜ := by
            simpa [Set.mem_compl] using hx
          simp [g, hx, hx_compl]
        · have hx_compl : x ∈ coreSetᶜ := by
            simpa [Set.mem_compl] using hx
          simp [g, hx, hx_compl]
      simpa [g, h_decomp]
        using h_add_le
    simpa [Φ, g]
      using h_sum_decomp
  have h_core_tail_split :
      ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
        Φ y ≤
          (volume coreSet) ^ (1 / p.toReal) * ENNReal.ofReal (δ / 2)
            +
              eLpNorm
                (fun x =>
                  Set.indicator coreSetᶜ
                    (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
                p volume := by
    refine (h_core_indicator_eventually.and h_split_eventually).mono ?_
    intro y hy
    rcases hy with ⟨hy_core, hy_split⟩
    have h_add_bound :
        eLpNorm
            (fun x =>
              Set.indicator coreSet
                (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
            p volume
          +
            eLpNorm
              (fun x =>
                Set.indicator coreSetᶜ
                  (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
              p volume
          ≤
            (volume coreSet) ^ (1 / p.toReal) * ENNReal.ofReal (δ / 2)
              +
                eLpNorm
                  (fun x =>
                    Set.indicator coreSetᶜ
                      (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
                  p volume := by
      exact add_le_add_right hy_core _
    exact hy_split.trans h_add_bound
  have h_tail_indicator_eventually_one :
      ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
        eLpNorm
            (fun x =>
              Set.indicator coreSetᶜ
                (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
            1 volume
          ≤ ENNReal.ofReal δ := by
    refine h_tail_eventually.mono ?_
    intro y hy
    classical
    set g : (Fin n → ℝ) → ℂ :=
      fun x => (φ : (Fin n → ℝ) → ℂ) (x - y) - φ x
    have h_core_subset_tail : coreSetᶜ ⊆ tailSet := by
      intro x hx
      have hx_not_le : ¬ dist x (0 : Fin n → ℝ) ≤ R :=
        by simpa [coreSet, h_core_def, dist_eq_norm] using hx
      have hx_norm_gt : R < ‖x‖ := by
        have hx_lt := lt_of_not_ge hx_not_le
        simpa [dist_eq_norm] using hx_lt
      have hx_norm_ge : R ≤ ‖x‖ := le_of_lt hx_norm_gt
      change R ≤ ‖x‖
      exact hx_norm_ge
    have h_indicator_eq :
        eLpNorm (fun x => Set.indicator coreSetᶜ g x) 1 volume
          =
            ∫⁻ x, ‖g x‖ₑ ∂(volume.restrict coreSetᶜ) := by
      have h_meas : MeasurableSet coreSetᶜ := h_core_meas.compl
      have h_eLp :=
        eLpNorm_indicator_eq_eLpNorm_restrict
          (μ := volume) (p := (1 : ℝ≥0∞))
          (s := coreSetᶜ) (f := g) h_meas
      have h_lintegral :
          eLpNorm g 1 (volume.restrict coreSetᶜ)
            = ∫⁻ x, ‖g x‖ₑ ∂(volume.restrict coreSetᶜ) := by
        simp [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      simp [h_eLp, h_lintegral]
    have h_core_le :
        ∫⁻ x, ‖g x‖ₑ ∂(volume.restrict coreSetᶜ)
          ≤ ENNReal.ofReal δ := by
      have h_mono :=
        lintegral_mono_set (μ := volume)
          (f := fun x : (Fin n → ℝ) => ‖g x‖ₑ)
          (s := coreSetᶜ) (t := tailSet) h_core_subset_tail
      exact h_mono.trans hy
    simpa [h_indicator_eq]
      using h_core_le
  have h_tail_indicator_memLp :
      ∀ y : Fin n → ℝ,
        MemLp
          (fun x =>
            Set.indicator coreSetᶜ
              (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
          p volume := by
    intro y
    classical
    set g : (Fin n → ℝ) → ℂ :=
      fun x => (φ : (Fin n → ℝ) → ℂ) (x - y) - φ x
    have h_pres :
        MeasurePreserving (fun x : (Fin n → ℝ) => x - y) volume volume := by
      simpa [sub_eq_add_neg]
        using
          (measurePreserving_add_right (μ := volume)
            (-y : Fin n → ℝ))
    have h_shift_mem :
        MemLp (fun x : (Fin n → ℝ) => (φ : (Fin n → ℝ) → ℂ) (x - y)) p volume :=
      hφ_mem.comp_measurePreserving h_pres
    have hg_mem : MemLp g p volume :=
      h_shift_mem.sub hφ_mem
    have h_core_compl_meas : MeasurableSet coreSetᶜ := h_core_meas.compl
    change
        MemLp (fun x => Set.indicator coreSetᶜ g x) p volume
    exact
      (MemLp.indicator (μ := volume) (p := p) (s := coreSetᶜ)
        h_core_compl_meas hg_mem)
  have h_tail_indicator_eLpNorm_ne_top :
      ∀ y : Fin n → ℝ,
        eLpNorm
            (fun x =>
              Set.indicator coreSetᶜ
                (fun z => (φ : (Fin n → ℝ) → ℂ) (z - y) - φ z) x)
            p volume ≠ ∞ := by
    intro y
    exact (h_tail_indicator_memLp y).eLpNorm_ne_top
  sorry

/--
**Translation in Lp converges to identity.**

For f ∈ Lp, ‖τ_y f - f‖_p → 0 as y → 0, where (τ_y f)(x) = f(x - y).

This is a key ingredient in the approximation identity proof.
-/
lemma translation_continuous_Lp
    (f : (Fin n → ℝ) → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (hf : MemLp f p volume) :
    ∀ ε > 0, ∃ δ > 0, ∀ y,
      ‖y‖ < δ →
      eLpNorm (fun x => f (x - y) - f x) p volume < ENNReal.ofReal ε := by
  classical
  let Φ := fun y : (Fin n → ℝ) =>
    eLpNorm (fun x => f (x - y) - f x) p volume
  have hΦ0 : Φ 0 = 0 := by
    simp [Φ]
  have h_tendsto : Filter.Tendsto Φ (𝓝 (0 : Fin n → ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    classical
    refine ENNReal.tendsto_nhds_zero.2 ?_
    intro ε hε
    by_cases hε_top : ε = ⊤
    · refine Filter.Eventually.of_forall ?_
      intro y
      simp [Φ, hε_top]
    · have hε_lt_top : ε < ⊤ := lt_of_le_of_ne le_top hε_top
      have hε_toReal_pos : 0 < ε.toReal := by
        refine ENNReal.toReal_pos (by exact ne_of_gt hε) hε_top
      set δ : ℝ := ε.toReal / 3 with hδ_def
      have hδ_pos : 0 < δ := by
        have hthree : (0 : ℝ) < 3 := by norm_num
        simpa [hδ_def] using (div_pos hε_toReal_pos hthree)
      obtain ⟨φ, hφ⟩ := schwartz_dense_Lp (p := p) (hp := hp)
        (hp_ne_top := hp_ne_top) f hf (ε := δ) hδ_pos
      have hφ_mem : MemLp (fun x => φ x) p volume := by
        simpa using (SchwartzMap.memLp (φ) (p := p) (μ := volume))
      have hφ_tendsto :
          Filter.Tendsto
            (fun y : Fin n → ℝ =>
              eLpNorm (fun x => φ (x - y) - φ x) p volume)
            (𝓝 (0 : Fin n → ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
        simpa using
          translation_tendsto_of_schwartz (φ := φ) (p := p) (hp := hp)
            (hp_ne_top := hp_ne_top)
      have hΦ_le :
          ∀ y : Fin n → ℝ,
            Φ y ≤
              eLpNorm (fun x => f (x - y) - φ (x - y)) p volume
                + eLpNorm (fun x => φ (x - y) - φ x) p volume
                + eLpNorm (fun x => f x - φ x) p volume := by
        intro y
        classical
        set g1 : (Fin n → ℝ) → ℂ := fun x => f (x - y) - φ (x - y)
        set g2 : (Fin n → ℝ) → ℂ := fun x => φ (x - y) - φ x
        set g3 : (Fin n → ℝ) → ℂ := fun x => φ x - f x
        have h_pres :
            MeasurePreserving (fun x : (Fin n → ℝ) => x - y) volume volume := by
          simpa [sub_eq_add_neg]
            using
              (measurePreserving_add_right (μ := volume)
                (-y : Fin n → ℝ))
        have hf_shift_mem := hf.comp_measurePreserving h_pres
        have hφ_shift_mem := hφ_mem.comp_measurePreserving h_pres
        have hf_shift_aesm :
            AEStronglyMeasurable (fun x : (Fin n → ℝ) => f (x - y)) volume :=
          hf_shift_mem.aestronglyMeasurable
        have hφ_shift_aesm :
            AEStronglyMeasurable (fun x : (Fin n → ℝ) => φ (x - y)) volume :=
          hφ_shift_mem.aestronglyMeasurable
        have hg1_meas : AEStronglyMeasurable g1 volume :=
          hf_shift_aesm.sub hφ_shift_aesm
        have hg2_meas : AEStronglyMeasurable g2 volume :=
          hφ_shift_aesm.sub hφ_mem.aestronglyMeasurable
        have hg3_meas : AEStronglyMeasurable g3 volume :=
          hφ_mem.aestronglyMeasurable.sub hf.aestronglyMeasurable
        have hsum_meas :
            AEStronglyMeasurable (fun x => g2 x + g3 x) volume :=
          hg2_meas.add hg3_meas
        have h_triangle₁ :
            eLpNorm (fun x => g1 x + (g2 x + g3 x)) p volume
              ≤
                eLpNorm g1 p volume
                  + eLpNorm (fun x => g2 x + g3 x) p volume :=
          eLpNorm_add_le (μ := volume) (p := p) hg1_meas hsum_meas hp
        have h_triangle₂ :
            eLpNorm (fun x => g2 x + g3 x) p volume
              ≤ eLpNorm g2 p volume + eLpNorm g3 p volume :=
          eLpNorm_add_le (μ := volume) (p := p) hg2_meas hg3_meas hp
        have hΦ_eq :
            Φ y
              = eLpNorm (fun x => g1 x + (g2 x + g3 x)) p volume := by
          simp [Φ, g1, g2, g3, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        have h_bound :
            Φ y
              ≤
                eLpNorm g1 p volume
                  + (eLpNorm g2 p volume + eLpNorm g3 p volume) := by
          have h_le :=
            calc
              Φ y
                  = eLpNorm (fun x => g1 x + (g2 x + g3 x)) p volume := hΦ_eq
              _ ≤
                  eLpNorm g1 p volume
                    + eLpNorm (fun x => g2 x + g3 x) p volume := h_triangle₁
              _ ≤
                  eLpNorm g1 p volume
                    + (eLpNorm g2 p volume + eLpNorm g3 p volume) :=
                    add_le_add_left h_triangle₂ _
          exact h_le
        have h_sub_comm :
            eLpNorm g3 p volume
              = eLpNorm (fun x => f x - φ x) p volume := by
          simpa [g3]
            using
              (eLpNorm_sub_comm (μ := volume) (p := p)
                (f := fun x : (Fin n → ℝ) => φ x)
                (g := fun x : (Fin n → ℝ) => f x))
        have h_bound' :
            Φ y
              ≤
                eLpNorm g1 p volume
                  + (eLpNorm g2 p volume
                    + eLpNorm (fun x => f x - φ x) p volume) := by
          simpa [h_sub_comm] using h_bound
        have h_bound'' :
            Φ y
              ≤
                eLpNorm (fun x => f (x - y) - φ (x - y)) p volume
                  + eLpNorm (fun x => φ (x - y) - φ x) p volume
                  + eLpNorm (fun x => f x - φ x) p volume := by
          simpa [g1, g2, g3, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
            using h_bound'
        exact h_bound''
      have hf_sub_aesm :
          AEStronglyMeasurable (fun x => f x - φ x) volume :=
        hf.aestronglyMeasurable.sub hφ_mem.aestronglyMeasurable
      have h_translate_eq :
          ∀ y : Fin n → ℝ,
            eLpNorm (fun x => f (x - y) - φ (x - y)) p volume
              = eLpNorm (fun x => f x - φ x) p volume := by
        intro y
        have hζ :=
          eLpNorm_comp_add_right
            (μ := volume)
            (G := Fin n → ℝ)
            (E := ℂ)
            (f := fun x => f x - φ x)
            (y := -y)
            (p := p)
            hf_sub_aesm
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hζ
      have h_target_small :
          (0 : ℝ≥0∞) ∈ Set.Iio (ENNReal.ofReal δ) := by
        have h_pos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := by
          simpa using ENNReal.ofReal_pos.mpr hδ_pos
        simpa [Set.mem_Iio] using h_pos
      have hφ_eventually_small :
          ∀ᶠ y in 𝓝 (0 : Fin n → ℝ),
            eLpNorm (fun x => φ (x - y) - φ x) p volume
              < ENNReal.ofReal δ :=
        (hφ_tendsto.eventually
          (IsOpen.mem_nhds isOpen_Iio h_target_small))
      have hΦ_eventually_lt :
          ∀ᶠ y in 𝓝 (0 : Fin n → ℝ), Φ y < ε := by
        refine hφ_eventually_small.mono ?_
        intro y hy
        have hΦ_bound := hΦ_le y
        have hA_lt :
            eLpNorm (fun x => f (x - y) - φ (x - y)) p volume
              < ENNReal.ofReal δ := by
          simpa [h_translate_eq y] using hφ
        have hC_lt :
            eLpNorm (fun x => f x - φ x) p volume
              < ENNReal.ofReal δ := hφ
        have hAB_lt :
            eLpNorm (fun x => f (x - y) - φ (x - y)) p volume
                + eLpNorm (fun x => φ (x - y) - φ x) p volume
              < ENNReal.ofReal δ + ENNReal.ofReal δ :=
          ENNReal.add_lt_add hA_lt hy
        have h_upper_lt :
            eLpNorm (fun x => f (x - y) - φ (x - y)) p volume
                + eLpNorm (fun x => φ (x - y) - φ x) p volume
                + eLpNorm (fun x => f x - φ x) p volume
              < ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ := by
          have h_total := ENNReal.add_lt_add hAB_lt hC_lt
          simpa [add_comm, add_left_comm, add_assoc]
            using h_total
        have hΦ_lt :
            Φ y < ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ :=
          lt_of_le_of_lt hΦ_bound h_upper_lt
        have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
        have h_sum_eq :
            ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ
              = ENNReal.ofReal (δ + δ + δ) := by
          simp [ENNReal.ofReal_add, hδ_nonneg, add_comm, add_left_comm,
            add_assoc]
        have h_three_eq : ENNReal.ofReal (δ + δ + δ) = ε := by
          have h_three : δ + δ + δ = ε.toReal := by
            have h_mul : 3 * δ = ε.toReal := by
              simp [hδ_def, div_eq_mul_inv, mul_comm, mul_left_comm,
                mul_assoc]
            have h_sum : δ + δ + δ = 3 * δ := by ring
            simpa [h_sum] using h_mul
          simp [h_three, hε_top]
        have hΦ_lt' : Φ y < ε := by
          simpa [h_sum_eq, h_three_eq] using hΦ_lt
        exact hΦ_lt'
      have hΦ_eventually_le :
          ∀ᶠ y in 𝓝 (0 : Fin n → ℝ), Φ y ≤ ε :=
        hΦ_eventually_lt.mono (fun _ hy => le_of_lt hy)
      exact hΦ_eventually_le
  intro ε hε
  have h_eventually :
      ∀ᶠ y in 𝓝 (0 : Fin n → ℝ), Φ y < ENNReal.ofReal ε := by
    have h_target : ∀ᶠ z in 𝓝 (0 : ℝ≥0∞), z < ENNReal.ofReal ε := by
      have h_mem : (0 : ℝ≥0∞) ∈ Set.Iio (ENNReal.ofReal ε) := by
        have h_pos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := by
          simpa using ENNReal.ofReal_pos.mpr hε
        simpa [Set.mem_Iio] using h_pos
      exact IsOpen.mem_nhds isOpen_Iio h_mem
    exact h_tendsto.eventually h_target
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    (Metric.eventually_nhds_iff).1 h_eventually
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy
  have hy' : dist y (0 : (Fin n → ℝ)) < δ := by
    simpa [dist_eq_norm] using hy
  have := hδ hy'
  simpa [Φ, dist_eq_norm] using this

end UniformContinuityLemmas

section ConvergenceContinuous

/--
**Mollifier convergence for continuous functions.**

For f continuous with compact support and ψ an approximate identity:
  ‖f - f * ψ_η‖_∞ → 0 as η → 0
-/
theorem mollifier_converges_continuous
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hf_cont : Continuous f)
    (hf_compact : HasCompactSupport f)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      ∀ x, ‖f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)‖ < ε := by
  sorry

end ConvergenceContinuous

section ConvergenceLp

/--
**Mollifier convergence in Lp (general result).**

For f ∈ Lp with 1 ≤ p < ∞ and ψ an approximate identity:
  ‖f - f * ψ_η‖_p → 0 as η → 0
-/
theorem mollifier_converges_Lp
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    (hf : MemLp f p volume)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      eLpNorm (fun x => f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)) p volume <
        ENNReal.ofReal ε := by
  sorry

/--
**Mollifier convergence in L¹ for compact support functions.**

This is the result used in the paper's proof (Section 4.2).
Corresponds to h_g_conv_bound for L¹.
-/
theorem mollifier_converges_L1_compactSupport
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hf : Integrable f volume)
    (hf_compact : HasCompactSupport f)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      eLpNorm (fun x => f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)) 1 volume <
        ENNReal.ofReal ε := by
  classical
  have hf_memLp : MemLp f 1 volume :=
    (memLp_one_iff_integrable (μ := volume)).2 hf
  have h_one_le_one : (1 : ℝ≥0∞) ≤ (1 : ℝ≥0∞) := by rfl
  have h_one_ne_top : (1 : ℝ≥0∞) ≠ ∞ := by norm_num
  simpa using
    mollifier_converges_Lp f ψ (1 : ℝ≥0∞) h_one_le_one h_one_ne_top hf_memLp hψ

/--
**Mollifier convergence in L² for compact support functions.**

L² version of the above.
Corresponds to h_g_conv_bound for L².
-/
theorem mollifier_converges_L2_compactSupport
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 volume)
    (hf_compact : HasCompactSupport f)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      eLpNorm (fun x => f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)) 2 volume <
        ENNReal.ofReal ε := by
  classical
  have h_one_two : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  simpa using
    mollifier_converges_Lp f ψ (2 : ℝ≥0∞) h_one_two h_two_ne_top hf hψ

end ConvergenceLp
