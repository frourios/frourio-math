import Frourio.Analysis.SchwartzDensityLp.ConvolutionTheory
import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
import Frourio.Analysis.SchwartzDensityLp.YoungInequalityCore
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Young's Inequality for Convolution

This file provides Young's inequality for convolution in Lp spaces.

## Main results

- `young_convolution_inequality`: The main Young's inequality
- `young_L1_L1`: Special case: ‖f * g‖₁ ≤ ‖f‖₁ · ‖g‖₁
- `young_L1_L2`: Special case: ‖f * g‖₂ ≤ ‖f‖₂ · ‖g‖₁
- `convolution_diff_bound_L1`: Used in the paper's proof (Step 3)
- `convolution_diff_bound_L2`: L² version

## References

- Folland, Real Analysis, Theorem 8.8
- papers/schwartz_density_constructive_analysis.md, Section 3.2, Lemma 3.9
- papers/schwartz_density_constructive_analysis.md, Section 4.2, Step 3

## Technical notes

Young's inequality states that for 1 ≤ p, q, r ≤ ∞ with 1/p + 1/q = 1 + 1/r:
  ‖f * g‖_r ≤ ‖f‖_p · ‖g‖_q

For the Schwartz density theorem, we primarily need:
1. p = q = 1, r = 1: ‖f * g‖₁ ≤ ‖f‖₁ · ‖g‖₁
2. p = 2, q = 1, r = 2: ‖f * g‖₂ ≤ ‖f‖₂ · ‖g‖₁

-/

open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff

variable {n : ℕ}

section YoungGeneral

/--
**Young's inequality for convolution (general form).**

For 1 ≤ p, q, r ≤ ∞ with 1/p + 1/q = 1 + 1/r:
  ‖f * g‖_r ≤ ‖f‖_p · ‖g‖_q
-/
theorem young_convolution_inequality
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) r volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
  classical

  -- Young's inequality proof strategy:
  --
  -- Key idea: Use Hölder's inequality and Minkowski's integral inequality
  --
  -- Step 1: For each x, estimate |∫ f(x-y) g(y) dy|
  -- Using Hölder: |∫ f(x-y) g(y) dy| ≤ (∫ |f(x-y)|^p' dy)^(1/p') · (∫ |g(y)|^q' dy)^(1/q')
  -- where 1/p' + 1/q' = 1
  --
  -- Step 2: Take L^r norm over x and apply Minkowski's integral inequality
  --
  -- The difficulty is that we need to relate the exponents p', q', r
  -- to the original p, q, r via the condition 1/p + 1/q = 1 + 1/r

  -- First, establish basic properties
  have hf_ae : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hg_ae : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  have hf_lt_top : eLpNorm f p volume < ⊤ := hf.eLpNorm_lt_top
  have hg_lt_top : eLpNorm g q volume < ⊤ := hg.eLpNorm_lt_top
  have hf_ne_top : eLpNorm f p volume ≠ ∞ := ne_of_lt hf_lt_top
  have hg_ne_top : eLpNorm g q volume ≠ ∞ := ne_of_lt hg_lt_top
  -- Basic positivity facts about the exponents.
  have hp_pos : (0 : ℝ≥0∞) < p := zero_lt_one.trans_le hp
  have hq_pos : (0 : ℝ≥0∞) < q := zero_lt_one.trans_le hq
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
  have hp_inv_ne_top : 1 / p ≠ ⊤ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hp_ne_zero)
  have hq_inv_ne_top : 1 / q ≠ ⊤ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hq_ne_zero)
  have hsum_ne_top : 1 / p + 1 / q ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hp_inv_ne_top, hq_inv_ne_top⟩
  have hr_ne_zero : r ≠ 0 := by
    intro hr_zero
    have h_rhs : 1 + 1 / r = ⊤ := by
      simp [hr_zero]
    have : 1 / p + 1 / q = ⊤ := by
      calc
        1 / p + 1 / q = 1 + 1 / r := hpqr
        _ = ⊤ := h_rhs
    exact hsum_ne_top this
  have hr_inv_ne_top : 1 / r ≠ ⊤ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hr_ne_zero)
  -- Package the convolution integrand and the convolution itself for reuse.
  set kernel := fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2) * g p.2 with hkernel_def
  set conv := fun x : (Fin n → ℝ) => ∫ y, f (x - y) * g y with hconv_def

  -- Re-express the goal in terms of the named convolution.
  suffices h_goal :
      MemLp conv r volume ∧
        eLpNorm conv r volume ≤
          eLpNorm f p volume * eLpNorm g q volume by
    simpa [conv, hconv_def] using h_goal

  have hf_aemeas : AEMeasurable f volume := hf_ae.aemeasurable
  have hg_aemeas : AEMeasurable g volume := hg_ae.aemeasurable
  have h_sub_qmp :
      Measure.QuasiMeasurePreserving
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2)
          (volume.prod volume) volume := by
    have h_measPres :
        MeasurePreserving
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 - p.2, p.2))
            (volume.prod volume) (volume.prod volume) :=
      measurePreserving_sub_prod (μ := volume) (ν := volume)
    have h_fst_qmp :
        Measure.QuasiMeasurePreserving
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1)
            (volume.prod volume) volume :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)
    have h_comp :=
      h_fst_qmp.comp h_measPres.quasiMeasurePreserving
    simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
      using h_comp
  have hf_prod_aemeas :
      AEMeasurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2))
        (volume.prod volume) :=
    hf_aemeas.comp_quasiMeasurePreserving h_sub_qmp
  have hg_prod_aemeas :
      AEMeasurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g p.2)
        (volume.prod volume) :=
    hg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hkernel_aemeas :
      AEMeasurable kernel (volume.prod volume) := by
    have := hf_prod_aemeas.mul hg_prod_aemeas
    simpa [kernel, hkernel_def, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hkernel_meas :
      AEStronglyMeasurable kernel (volume.prod volume) :=
    hkernel_aemeas.aestronglyMeasurable
  have hf_norm : MemLp (fun x => ‖f x‖) p volume := hf.norm
  have hg_norm : MemLp (fun x => ‖g x‖) q volume := hg.norm

  -- When `r = ⊤`, the exponent relation forces `p` and `q` to be conjugate.
  have h_conjugate_of_top : r = ⊤ → ENNReal.HolderConjugate p q := by
    intro hr_top
    have hpq_one : 1 / p + 1 / q = 1 := by simpa [hr_top] using hpqr
    exact young_exponent_inf_case hp hq hpq_one

  by_cases hr_top : r = ⊤
  · have h_conjugate : ENNReal.HolderConjugate p q := h_conjugate_of_top hr_top
    haveI : ENNReal.HolderConjugate p q := h_conjugate
    have hpq_one : 1 / p + 1 / q = 1 := by simpa [hr_top] using hpqr
    have hpq : IsConjugateExponent p q := by
      classical
      have h_inv_q : 1 / q = 1 - 1 / p :=
        ENNReal.eq_sub_of_add_eq' (by simp : (1 : ℝ≥0∞) ≠ ∞)
          (by simpa [add_comm] using hpq_one)
      have h_inv_p : 1 / p = 1 - 1 / q :=
        ENNReal.eq_sub_of_add_eq' (by simp : (1 : ℝ≥0∞) ≠ ∞) hpq_one
      by_cases hp_one : p = 1
      · subst hp_one
        have h_inv_zero : 1 / q = 0 := by
          simpa [one_div, inv_one, sub_self] using h_inv_q
        have hq_top : q = ⊤ :=
          ENNReal.inv_eq_zero.mp (by simpa [one_div] using h_inv_zero)
        exact Or.inl ⟨rfl, hq_top⟩
      · have hp_ne_one : p ≠ 1 := hp_one
        by_cases hp_top : p = ⊤
        · subst hp_top
          have h_inv : 1 / q = 1 := by
            simpa [one_div, ENNReal.inv_top, zero_add] using hpq_one
          have hq_one : q = 1 := by
            have h_inv' : q⁻¹ = 1 := by simpa [one_div] using h_inv
            exact ENNReal.inv_eq_one.mp h_inv'
          exact Or.inr <| Or.inl ⟨rfl, hq_one⟩
        · have hp_ne_top : p ≠ ∞ := hp_top
          have hq_ne_top : q ≠ ∞ := by
            intro hq_top
            have h_inv : 1 / p = 1 := by
              simpa [hq_top, one_div, ENNReal.inv_top, add_comm] using hpq_one
            have h_inv' : p⁻¹ = 1 := by simpa [one_div] using h_inv
            have hp_one : p = 1 := by
              exact ENNReal.inv_eq_one.mp h_inv'
            exact hp_ne_one hp_one
          have hq_ne_one : q ≠ 1 := by
            intro hq_one
            have h_inv_zero : 1 / p = 0 := by
              simpa [hq_one, one_div, inv_one, sub_self] using h_inv_p
            have h_inv_zero' : p⁻¹ = 0 := by simpa [one_div] using h_inv_zero
            have hp_top : p = ⊤ := ENNReal.inv_eq_zero.mp h_inv_zero'
            exact hp_ne_top hp_top
          have hp_lt_top : p < ⊤ := lt_of_le_of_ne le_top hp_ne_top
          have hq_lt_top : q < ⊤ := lt_of_le_of_ne le_top hq_ne_top
          have hp_gt_one : 1 < p := lt_of_le_of_ne hp (by simpa [eq_comm] using hp_ne_one)
          have hq_gt_one : 1 < q := lt_of_le_of_ne hq (by simpa [eq_comm] using hq_ne_one)
          exact Or.inr <| Or.inr ⟨hp_gt_one, hp_lt_top, hq_gt_one, hq_lt_top, hpq_one⟩
    have h_holder_convolution :
        ∀ x, Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) volume ∧
          ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂volume
              ≤ (eLpNorm f p volume).toReal * (eLpNorm g q volume).toReal := by
      intro x
      classical
      let μ : Measure (Fin n → ℝ) := volume
      haveI : μ.IsNegInvariant := by
        refine ⟨?_⟩
        set T :=
          (-1 : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
        have h_det_eq :
            LinearMap.det T =
              (-1 : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
          simpa [T]
            using
              (LinearMap.det_smul (-1 : ℝ)
                (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
        have h_abs_det :
            abs (LinearMap.det T) = (1 : ℝ) := by
          simp [h_det_eq]
        have h_det_ne_zero : LinearMap.det T ≠ 0 := by
          have h_abs_ne : abs (LinearMap.det T) ≠ 0 := by
            simp [h_abs_det]
          exact abs_ne_zero.mp h_abs_ne
        have h_map_aux :=
          Real.map_linearMap_volume_pi_eq_smul_volume_pi
            (f := T) h_det_ne_zero
        have h_abs_inv : abs ((LinearMap.det T)⁻¹) = (1 : ℝ) := by
          have := abs_inv (LinearMap.det T)
          simpa [h_abs_det, h_det_ne_zero]
            using this
        have h_scalar :
            ENNReal.ofReal (abs ((LinearMap.det T)⁻¹)) = (1 : ℝ≥0∞) := by
          simp [h_abs_inv]
        have h_map_aux' :
            Measure.map (fun y : (Fin n → ℝ) => -y) μ
              = ENNReal.ofReal (abs ((LinearMap.det T)⁻¹)) • μ := by
          simpa [T, LinearMap.smul_apply, Pi.smul_apply]
            using h_map_aux
        have h_map :
            Measure.map (fun y : (Fin n → ℝ) => -y) μ = μ := by
          simpa [h_scalar] using h_map_aux'
        have h_map_neg :
            Measure.map (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) μ = μ := by
          simpa [Neg.neg] using h_map
        have h_neg_eq :
            Measure.neg (μ := μ) = μ := by
          simpa [Measure.neg]
            using h_map_neg
        exact h_neg_eq
      simpa using
        holder_inequality_convolution (μ := volume) (p := p) (q := q)
          (f := fun z => ‖f z‖) (g := fun z => ‖g z‖)
          hpq hf_norm hg_norm x
    have h_conv_meas : AEStronglyMeasurable conv volume := by
      simpa [conv, hconv_def, kernel, hkernel_def] using
        (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := volume) (ν := volume) (f := kernel) hkernel_meas)
    set C :=
      (eLpNorm f p volume).toReal * (eLpNorm g q volume).toReal with hC_def
    have h_conv_pointwise : ∀ x, ‖conv x‖ ≤ C := by
      intro x
      have h_norm_le :
          ‖∫ y, f (x - y) * g y ∂volume‖
              ≤ ∫ y, ‖f (x - y) * g y‖ ∂volume :=
        norm_integral_le_integral_norm (μ := volume)
          (f := fun y => f (x - y) * g y)
      have h_bound :
          ∫ y, ‖f (x - y) * g y‖ ∂volume ≤ C := by
        simpa [C, norm_mul] using (h_holder_convolution x).2
      have h_le : ‖conv x‖ ≤ ∫ y, ‖f (x - y) * g y‖ ∂volume := by
        simpa [conv, hconv_def] using h_norm_le
      exact h_le.trans h_bound
    have h_conv_bound :
        ∀ᵐ x ∂volume, ‖conv x‖ ≤ C :=
      Filter.Eventually.of_forall h_conv_pointwise
    have h_memLp : MemLp conv ∞ volume :=
      memLp_top_of_bound h_conv_meas (C := C) h_conv_bound
    have h_bound_en :
        (fun x => (‖conv x‖ₑ : ℝ≥0∞)) ≤ᵐ[volume]
          fun _ => ENNReal.ofReal C := by
      refine h_conv_bound.mono ?_
      intro x hx
      have hx' : ENNReal.ofReal ‖conv x‖ ≤ ENNReal.ofReal C :=
        ENNReal.ofReal_le_ofReal hx
      simpa using hx'
    have h_essSup_le :
        essSup (fun x => (‖conv x‖ₑ : ℝ≥0∞)) volume ≤ ENNReal.ofReal C := by
      refine essSup_le_of_ae_le (μ := volume) (f := fun x => (‖conv x‖ₑ : ℝ≥0∞))
          (c := ENNReal.ofReal C) ?_
      simpa using h_bound_en
    have h_eLpNorm_le_top :
        eLpNorm conv ∞ volume ≤ ENNReal.ofReal C := by
      simpa [eLpNorm, eLpNorm_exponent_top, conv, hconv_def] using h_essSup_le
    have hf_ofReal :
        ENNReal.ofReal (eLpNorm f p volume).toReal = eLpNorm f p volume := by
      simpa using ENNReal.ofReal_toReal hf_ne_top
    have hg_ofReal :
        ENNReal.ofReal (eLpNorm g q volume).toReal = eLpNorm g q volume := by
      simpa using ENNReal.ofReal_toReal hg_ne_top
    have hf_toReal_nonneg :
        0 ≤ (eLpNorm f p volume).toReal := ENNReal.toReal_nonneg
    have hg_toReal_nonneg :
        0 ≤ (eLpNorm g q volume).toReal := ENNReal.toReal_nonneg
    have h_rhs_eq :
        ENNReal.ofReal C =
            eLpNorm f p volume * eLpNorm g q volume := by
      have h_mul :
          ENNReal.ofReal C =
              ENNReal.ofReal (eLpNorm f p volume).toReal *
                ENNReal.ofReal (eLpNorm g q volume).toReal := by
        simp [C, ENNReal.ofReal_mul, hf_toReal_nonneg, hg_toReal_nonneg]
      simpa [hf_ofReal, hg_ofReal, mul_comm, mul_left_comm, mul_assoc]
        using h_mul
    have h_memLp_r : MemLp conv r volume := by
      simpa [hr_top] using h_memLp
    have h_eLpNorm_le :
        eLpNorm conv r volume ≤ ENNReal.ofReal C := by
      simpa [hr_top] using h_eLpNorm_le_top
    refine ⟨h_memLp_r, ?_⟩
    calc
      eLpNorm conv r volume ≤ ENNReal.ofReal C := h_eLpNorm_le
      _ = eLpNorm f p volume * eLpNorm g q volume := h_rhs_eq
  · have hr_ne_top : r ≠ ⊤ := hr_top
    -- TODO: handle the finite exponent case `r ≠ ⊤`
    sorry

end YoungGeneral

section SpecialCases

/--
**Young's inequality for L¹ × L¹ → L¹.**

‖f * g‖₁ ≤ ‖f‖₁ · ‖g‖₁

This is used throughout the paper for bounding L¹ errors.
-/
theorem young_L1_L1
    (f g : (Fin n → ℝ) → ℂ)
    (hf : Integrable f volume)
    (hg : Integrable g volume) :
    Integrable (fun x => ∫ y, f (x - y) * g y) volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) 1 volume ≤
      eLpNorm f 1 volume * eLpNorm g 1 volume := by
  -- For L¹ × L¹ → L¹, this is the simplest case
  -- The proof uses Fubini and the basic triangle inequality

  have hf_ae : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hg_ae : AEStronglyMeasurable g volume := hg.aestronglyMeasurable

  constructor
  · -- Prove integrability of the convolution
    -- TODO: fill in the actual proof.
    sorry

  · -- Prove the inequality
    -- TODO: fill in the actual proof.
    sorry -- The inequality is essentially proven in the integrability part

/--
**Young's inequality for L² × L¹ → L².**

‖f * g‖₂ ≤ ‖f‖₂ · ‖g‖₁

This is used throughout the paper for bounding L² errors.
-/
theorem young_L2_L1
    (f g : (Fin n → ℝ) → ℂ)
    (hf : MemLp f 2 volume)
    (hg : Integrable g volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) 2 volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) 2 volume ≤
      eLpNorm f 2 volume * eLpNorm g 1 volume := by
  sorry

end SpecialCases

section NormalizedMollifier

/--
**Convolution with normalized mollifier preserves Lp norm bound.**

If ψ is a normalized mollifier (∫ ψ = 1, ψ ≥ 0), then:
  ‖f * ψ‖_p ≤ ‖f‖_p

This is a consequence of Young's inequality with ‖ψ‖₁ = 1.
-/
theorem convolution_normalized_mollifier_bound
    (f ψ : (Fin n → ℝ) → ℝ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hf : MemLp f p volume)
    (hψ_int : Integrable ψ volume)
    (hψ_norm : ∫ x, ψ x = 1)
    (hψ_nonneg : ∀ x, 0 ≤ ψ x) :
    eLpNorm (fun x => ∫ y, f (x - y) * ψ y) p volume ≤
      eLpNorm f p volume := by
  sorry

end NormalizedMollifier

section ConvolutionDifferenceBounds

/--
**Bound on difference of convolutions (L¹ case).**

‖(g - f₀) * ψ‖₁ ≤ ‖g - f₀‖₁ · ‖ψ‖₁

This is used in the paper's Section 4.2, Step 3 (II-c).
Corresponds to h_conv_diff_bound in the code.
-/
theorem convolution_diff_bound_L1
    (f₁ f₂ ψ : (Fin n → ℝ) → ℂ)
    (hf₁ : Integrable f₁ volume)
    (hf₂ : Integrable f₂ volume)
    (hψ : Integrable ψ volume) :
    eLpNorm (fun x =>
      (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 1 volume ≤
      eLpNorm (fun x => f₁ x - f₂ x) 1 volume * eLpNorm ψ 1 volume := by
  sorry

/--
**Bound on difference of convolutions with a normalized mollifier (L¹ case).**

If ψ is a non-negative mollifier with unit mass, convolution with the scaled
ψ does not increase the L¹ distance between two functions.
-/
theorem mollifier_convolution_diff_L1
    (g f₀ : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hg : Integrable g volume)
    (hf₀ : Integrable f₀ volume)
    (hψ_compact : HasCompactSupport ψ)
    (hψ_nonneg : ∀ x, 0 ≤ ψ x)
    (hψ_int : ∫ x, ψ x = 1) :
    ∀ η : ℝ, 0 < η → η < 1 →
      eLpNorm (fun x =>
        (∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) -
        (∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)))
        1 volume ≤
      eLpNorm (fun x => g x - f₀ x) 1 volume := by
  sorry

/--
**Bound on difference of convolutions (L² case).**

‖(g - f₀) * ψ‖₂ ≤ ‖g - f₀‖₂ · ‖ψ‖₁

L² version of the above, used for L² error bounds.
-/
theorem convolution_diff_bound_L2
    (f₁ f₂ ψ : (Fin n → ℝ) → ℂ)
    (hf₁ : MemLp f₁ 2 volume)
    (hf₂ : MemLp f₂ 2 volume)
    (hψ : Integrable ψ volume) :
    eLpNorm (fun x =>
      (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 2 volume ≤
      eLpNorm (fun x => f₁ x - f₂ x) 2 volume * eLpNorm ψ 1 volume := by
  sorry

end ConvolutionDifferenceBounds

section MollifierProperties

/--
**Scaled mollifier has L¹ norm = 1.**

If ∫ ψ = 1, then ∫ ψ_η = 1 where ψ_η(x) = η^(-n) ψ(x/η).
-/
theorem scaled_mollifier_integral_one
    (ψ : (Fin n → ℝ) → ℝ)
    (η : ℝ)
    (hη : 0 < η)
    (hψ_int : Integrable ψ volume)
    (hψ_norm : ∫ x, ψ x = 1) :
    ∫ (x : Fin n → ℝ), (η^(-(n : ℝ)) * ψ (fun i => x i / η)) = 1 := by
  sorry

/--
**Scaled mollifier L¹ norm bound.**

For the scaled mollifier ψ_η with ∫ ψ = 1, we have ‖ψ_η‖₁ = 1.
-/
theorem scaled_mollifier_L1_norm_one
    (ψ : (Fin n → ℝ) → ℝ)
    (η : ℝ)
    (hη : 0 < η)
    (hψ_int : Integrable ψ volume)
    (hψ_norm : ∫ x, ψ x = 1)
    (hψ_nonneg : ∀ x, 0 ≤ ψ x) :
    eLpNorm (fun (x : Fin n → ℝ) => η^(-(n : ℝ)) * ψ (fun i => x i / η)) 1 volume =
      ENNReal.ofReal 1 := by
  sorry

end MollifierProperties
