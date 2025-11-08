import Frourio.Analysis.SchwartzDensityLp.ConvolutionTheory
import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
import Frourio.Analysis.SchwartzDensityLp.TonelliTheorem
import Frourio.Analysis.YoungInequality.YoungInequalityCore3
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic

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
  have h_conv_meas : AEStronglyMeasurable conv volume := by
    simpa [conv, hconv_def, kernel, hkernel_def] using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := volume) (ν := volume) (f := kernel) hkernel_meas)

  haveI : (volume : Measure (Fin n → ℝ)).IsNegInvariant := by
    classical
    let μ : Measure (Fin n → ℝ) := volume
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
    have h_abs_det : abs (LinearMap.det T) = (1 : ℝ) := by
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
      simpa [Measure.neg] using h_map_neg
    simpa [μ] using h_neg_eq

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
      simpa using
        holder_inequality_convolution (μ := volume) (p := p) (q := q)
          (f := fun z => ‖f z‖) (g := fun z => ‖g z‖)
          hpq hf_norm hg_norm x
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
    have h_conv_bound :
        eLpNorm conv r volume ≤
          eLpNorm f p volume * eLpNorm g q volume := by
      simpa [conv, hconv_def]
        using
          eLpNorm_convolution_le_mul
            (μ := volume) (f := f) (g := g)
            (p := p) (q := q) (r := r)
            hp hq hpqr hr_ne_top hf hg
    have h_rhs_lt_top :
        eLpNorm f p volume * eLpNorm g q volume < ⊤ :=
      ENNReal.mul_lt_top hf_lt_top hg_lt_top
    have h_conv_lt_top : eLpNorm conv r volume < ⊤ :=
      lt_of_le_of_lt h_conv_bound h_rhs_lt_top
    have h_memLp_r : MemLp conv r volume := by
      refine ⟨h_conv_meas, ?_⟩
      simpa [conv, hconv_def] using h_conv_lt_top
    refine ⟨h_memLp_r, ?_⟩
    simpa [conv, hconv_def] using h_conv_bound

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
    classical
    have hf1 : MemLp f 1 volume := (memLp_one_iff_integrable (μ := volume)).2 hf
    have hg1 : MemLp g 1 volume := (memLp_one_iff_integrable (μ := volume)).2 hg
    have h :=
      young_convolution_inequality (f := f) (g := g) (p := (1 : ℝ≥0∞))
        (q := (1 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
        (hp := by simp) (hq := by simp) (hpqr := by simp) hf1 hg1
    have h_mem : MemLp (fun x => ∫ y, f (x - y) * g y) 1 volume := h.1
    exact (memLp_one_iff_integrable (μ := volume)).1 h_mem

  · -- Prove the inequality
    classical
    have hf1 : MemLp f 1 volume := (memLp_one_iff_integrable (μ := volume)).2 hf
    have hg1 : MemLp g 1 volume := (memLp_one_iff_integrable (μ := volume)).2 hg
    have h :=
      young_convolution_inequality (f := f) (g := g) (p := (1 : ℝ≥0∞))
        (q := (1 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
        (hp := by simp) (hq := by simp) (hpqr := by simp) hf1 hg1
    simpa using h.2

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
  classical
  have hg1 : MemLp g 1 volume := (memLp_one_iff_integrable (μ := volume)).2 hg
  have h :=
    young_convolution_inequality (f := f) (g := g)
      (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
      (hp := by norm_num) (hq := by simp)
      (hpqr := by simp [one_div, add_comm, add_left_comm, add_assoc])
      hf hg1
  simpa using h

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
  classical
  -- Cast to complex and apply Young with q = 1, r = p, then use ‖ψ‖₁ = 1.
  -- Define complex-valued copies.
  set fC : (Fin n → ℝ) → ℂ := fun x => (f x : ℂ)
  set ψC : (Fin n → ℝ) → ℂ := fun x => (ψ x : ℂ)

  -- Lp-membership for the complex copy follows from measurability and norm equality.
  have hfC : MemLp fC p volume := by
    -- a.e.-strong measurability transfers along `Complex.ofReal` via `comp_aemeasurable`.
    have hfC_meas : AEStronglyMeasurable fC volume :=
      (Complex.measurable_ofReal.comp_aemeasurable
      (hf.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
    -- eLpNorm is preserved since norms agree pointwise.
    have hf_eLp_eq : eLpNorm fC p volume = eLpNorm f p volume :=
      eLpNorm_congr_norm_ae (μ := volume) (p := p)
        (Filter.Eventually.of_forall (fun x => by simp [fC, Real.norm_eq_abs]))
    -- Assemble `MemLp` from measurability and finiteness of the `eLpNorm`.
    refine ⟨hfC_meas, ?_⟩
    simpa [hf_eLp_eq] using hf.eLpNorm_lt_top

  have hψ1 : MemLp ψC 1 volume := by
    -- From integrability of ψ.
    have : Integrable ψC volume := hψ_int.ofReal
    simpa using (memLp_one_iff_integrable (μ := volume)).2 this

  -- Apply Young with q = 1, r = p.
  have hYoung :=
    young_convolution_inequality (f := fC) (g := ψC)
      (p := p) (q := (1 : ℝ≥0∞)) (r := p)
      (hp := hp) (hq := by simp)
      (hpqr := by simp [one_div, add_comm, add_left_comm, add_assoc])
      hfC hψ1

  -- Compute ‖ψ‖₁ = 1 in `ℝ≥0∞`.
  have hψ_L1_val : eLpNorm ψC 1 volume = (1 : ℝ≥0∞) := by
    -- eLpNorm at p = 1 is the lintegral of the ennreal norm; simplify to |ψ|.
    have h_enorm_abs :
        ∫⁻ x, ‖ψC x‖ₑ ∂volume = ∫⁻ x, ENNReal.ofReal |ψ x| ∂volume := by
      have hpt : (fun x => ‖ψC x‖ₑ) = fun x => ENNReal.ofReal |ψ x| := by
        funext x
        simpa [ψC, Real.norm_eq_abs] using (ofReal_norm_eq_enorm ((ψ x : ℂ))).symm
      simp [hpt]
    have h_abs_int : Integrable (fun x => |ψ x|) volume := hψ_int.abs
    have h_abs_nonneg : 0 ≤ᵐ[volume] fun x => |ψ x| :=
      Filter.Eventually.of_forall (fun x => by simp)
    have h_ofReal_abs :
        ENNReal.ofReal (∫ x, |ψ x| ∂volume)
          = ∫⁻ x, ENNReal.ofReal |ψ x| ∂volume :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_abs_int h_abs_nonneg
    have h_eLp_eq_ofReal :
        eLpNorm ψC 1 volume = ENNReal.ofReal (∫ x, |ψ x| ∂volume) := by
      have : eLpNorm ψC 1 volume = ∫⁻ x, ‖ψC x‖ₑ ∂volume := by
        simp [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      calc eLpNorm ψC 1 volume
            = ∫⁻ x, ‖ψC x‖ₑ ∂volume := by simp [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        _ = ∫⁻ x, ENNReal.ofReal |ψ x| ∂volume := h_enorm_abs
        _ = ENNReal.ofReal (∫ x, |ψ x| ∂volume) := (h_ofReal_abs).symm
    -- Since ψ ≥ 0 a.e., |ψ| = ψ a.e., so the integrals are equal.
    have h_abs_eq : ∀ᵐ x ∂volume, |ψ x| = ψ x :=
      Filter.Eventually.of_forall (fun x => by simp [abs_of_nonneg (hψ_nonneg x)])
    have h_abs_integral_eq : ∫ x, |ψ x| ∂volume = ∫ x, ψ x ∂volume := by
      -- Both sides are integrable, so we can use `integral_congr_ae`.
      have _ : Integrable (fun x => |ψ x|) volume := hψ_int.abs
      exact integral_congr_ae h_abs_eq
    -- Conclude using the normalization ∫ ψ = 1.
    have : eLpNorm ψC 1 volume = ENNReal.ofReal (∫ x, ψ x ∂volume) := by
      simpa [h_abs_integral_eq] using h_eLp_eq_ofReal
    simp [this, hψ_norm]

  -- Identify the complex Lp norms with the real ones by pointwise norm equality.
  have hf_eq : eLpNorm fC p volume = eLpNorm f p volume := by
    refine eLpNorm_congr_norm_ae (μ := volume) (p := p) ?_
    exact Filter.Eventually.of_forall (fun x => by simp [fC, Real.norm_eq_abs])
  have hconv_eq :
      eLpNorm (fun x => ∫ y, fC (x - y) * ψC y) p volume =
        eLpNorm (fun x => ∫ y, f (x - y) * ψ y) p volume := by
    -- Pointwise equality of norms via integral_ofReal, no integrability preconditions needed.
    refine eLpNorm_congr_norm_ae (μ := volume) (p := p) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have h_int_eq :
        (∫ y, fC (x - y) * ψC y ∂volume)
          = (∫ y, (Complex.ofReal (f (x - y) * ψ y)) ∂volume) := by
      have : (fun y => fC (x - y) * ψC y)
          = fun y => Complex.ofReal (f (x - y) * ψ y) := by
        funext y; simp [fC, ψC, sub_eq_add_neg]
      simp [this]
    have :
        ‖(∫ y, fC (x - y) * ψC y ∂volume)‖
          = ‖(∫ y, f (x - y) * ψ y ∂volume : ℝ)‖ := by
      simpa [h_int_eq, Real.norm_eq_abs]
        using congrArg (fun z : ℂ => ‖z‖)
          (integral_ofReal (f := fun y => f (x - y) * ψ y))
    simp [this]

  -- Transport the Young bound to the real-valued convolution and use ‖ψ‖₁ = 1.
  have h_bound :
      eLpNorm (fun x => ∫ y, f (x - y) * ψ y) p volume ≤
        eLpNorm f p volume * eLpNorm ψC 1 volume := by
    simpa [hconv_eq, hf_eq]
      using hYoung.2

  -- Conclude using ‖ψ‖₁ = 1.
  simpa [hψ_L1_val, one_mul]
    using h_bound

end NormalizedMollifier

section MollifierProperties

/--
Transport `AEMeasurable` across a positive scalar multiple of a measure.
If `f` is a.e.-measurable w.r.t. `μ`, then it is also a.e.-measurable w.r.t. `c • μ`.
This simple helper is used to avoid threading measurability through `map` equalities.
-/
lemma aemeasurable_smul_measure_of_aemeasurable
    {α : Type*} [MeasurableSpace α]
    (f : α → ℝ≥0∞) (μ : Measure α) (c : ℝ≥0∞)
    (hf : AEMeasurable f μ) : AEMeasurable f (c • μ) := by
  classical
  rcases hf with ⟨g, hg_meas, hfg⟩
  refine ⟨g, hg_meas, ?_⟩
  -- Transfer the a.e. equality along the scalar multiple of the measure.
  -- If μ {x | f x ≠ g x} = 0 then (c • μ) {x | f x ≠ g x} = 0.
  -- Extract the null set statement from the a.e. equality
  have h_zero : μ {x | f x ≠ g x} = 0 := (ae_iff).1 hfg
  -- Scale the measure: null sets remain null for `c • μ`
  have h_zero' : (c • μ) {x | f x ≠ g x} = 0 := by
    -- Avoid `simp` turning equality into a disjunction via `mul_eq_zero`.
    -- Directly rewrite using `Measure.smul_apply` and `h_zero`.
    simp [Measure.smul_apply, h_zero]
  -- Turn the null-set statement back into an a.e. equality for `c • μ`.
  exact (ae_iff).2 h_zero'

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
  classical
  -- Define the linear scaling map g(x) = (1/η) • x
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => (1 / η : ℝ) • x with hg_def
  have hg_meas : Measurable g := by
    simpa [hg_def] using (continuous_const_smul (1 / η : ℝ)).measurable

  -- Pushforward of Lebesgue measure under g is a scalar multiple via the Jacobian determinant
  have h_map_scale :
      Measure.map g volume
        = ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
    -- This is the standard formula for linear change of variables on ℝ^n
    simpa [g, hg_def]
      using Real.map_linearMap_volume_pi_eq_smul_volume_pi
        (f := ( (1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ))
        (by
          -- Show det ≠ 0 using η ≠ 0
          have hne : (1 / η : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hη)
          have hdet :
              LinearMap.det
                  ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
                = (1 / η : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
            simp
          have hpow2 : (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
            pow_ne_zero (Module.finrank ℝ (Fin n → ℝ)) hne
          simpa [hdet] using hpow2)

  -- Change of variables for the real integral of ψ ∘ g using the map description.
  -- We express ∫ ψ(g x) d(volume x) in terms of ∫ ψ d(volume).
  have h_change_integral :
      ∫ x, ψ (g x) =
        (ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))).toReal
          * ∫ y, ψ y := by
    -- Use the mapping property of the integral and the pushforward identity.
    -- First, obtain integrability of ψ w.r.t. the pushforward measure.
    have hg_aemeas : AEMeasurable g volume := hg_meas.aemeasurable
    have hc_ne_top :
        ENNReal.ofReal (abs ((LinearMap.det
          ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) ≠ ∞ := by
      simp
    have hψ_memLp : MemLp ψ 1 volume :=
      (memLp_one_iff_integrable (μ := volume)).2 hψ_int
    have hψ_memLp_map : MemLp ψ 1 (Measure.map g volume) := by
      -- Transfer along the measure identity `h_map_scale`.
      simpa [h_map_scale]
        using hψ_memLp.smul_measure hc_ne_top
    have hψ_int_map : Integrable ψ (Measure.map g volume) :=
      (memLp_one_iff_integrable (μ := Measure.map g volume)).1 hψ_memLp_map
    -- Apply the integral mapping property, then substitute the measure identity.
    have h_map :
        ∫ y, ψ y ∂(Measure.map g volume) = ∫ x, ψ (g x) ∂volume := by
      simpa using
        (MeasureTheory.integral_map (μ := volume)
          (hg_aemeas)
          (hψ_int_map.aestronglyMeasurable))
    have h_smul :
        ∫ y, ψ y ∂(Measure.map g volume)
          = (ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))).toReal
              * ∫ y, ψ y := by
      -- Evaluate the integral under the smul measure using `integral_smul_measure`.
      simp [h_map_scale, integral_smul_measure, mul_comm, mul_left_comm, mul_assoc]
    -- Rearrange to the desired orientation: ∫ ψ∘g dμ = c * ∫ ψ dμ.
    exact h_map.symm.trans h_smul

  -- Compute the determinant factor: for g = (1/η)•id, we get toReal = η^n.
  have h_det_toReal :
      (ENNReal.ofReal (abs ((LinearMap.det
          ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))).toReal
        = η ^ (n : ℝ) := by
    -- Compute the determinant and simplify the absolute inverse using η > 0.
    have hdet :
        LinearMap.det ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
          = (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) := by
      simp
    have hfinrank : (Module.finrank ℝ (Fin n → ℝ)) = n := by
      simp
    have hpow_pos : 0 < ((1 / η : ℝ) ^ n) := by
      have hpos : 0 < (1 / η : ℝ) := by simpa [one_div] using (inv_pos.mpr hη)
      exact pow_pos hpos n
    have h_abs_inv_nonneg : 0 ≤ (((1 / η : ℝ) ^ n)⁻¹) := (le_of_lt (inv_pos.mpr hpow_pos))
    have h_pow_inv : ((1 / η : ℝ) ^ n)⁻¹ = η ^ n := by
      simp [one_div, inv_inv]
    have h_abs_eq :
        abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)
          = η ^ n := by
      calc
        abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)
            = abs (((1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)))⁻¹) := by
                simp [hdet]
        _   = abs (((1 / η : ℝ) ^ n)⁻¹) := by simp [hfinrank]
        _   = (((1 / η : ℝ) ^ n)⁻¹) := abs_of_nonneg h_abs_inv_nonneg
        _   = η ^ n := h_pow_inv
    have h_toReal_ofReal :
        (ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))).toReal
          = abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹) := by
      simp
    have h_eta_pos_for_rpow : 0 < η := hη
    have h_abs_eta : abs η = η := abs_of_pos hη
    calc
      (ENNReal.ofReal (abs ((LinearMap.det
          ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))).toReal
          = abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹) :=
            h_toReal_ofReal
      _ = (η ^ n : ℝ) := h_abs_eq
      _ = η ^ (n : ℝ) := by
            rw [← Real.rpow_natCast]

  -- Pull out the constant η^{-n} from the integral
  have h_pull_const :
      ∫ x, η^(-(n : ℝ)) * ψ (g x) = η^(-(n : ℝ)) * ∫ x, ψ (g x) := by
    -- Use the linearity of the integral for scalar multiplication
    -- together with integrability of ψ ∘ g (which follows from hψ_int).
    -- A suitable lemma is `integral_const_mul`.
    simpa using
      (MeasureTheory.integral_const_mul
        (μ := volume)
        (r := η^(-(n : ℝ)))
        (f := fun x : (Fin n → ℝ) => ψ (g x)))

  -- Align the argument `ψ (fun i => x i / η)` with `ψ (g x)` and finish.
  have h_rewrite :
      (fun x : (Fin n → ℝ) => η^(-(n : ℝ)) * ψ (fun i => x i / η))
        = fun x => η^(-(n : ℝ)) * ψ (g x) := by
    -- Pointwise, g x = fun i => x i / η
    funext x
    have hx : (η⁻¹ : ℝ) • x = fun i => x i * η⁻¹ := by
      funext i; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    simp [hg_def, one_div, div_eq_mul_inv, hx, mul_comm, mul_left_comm, mul_assoc]

  -- Combine all steps in a short calculation.
  calc
    ∫ (x : Fin n → ℝ), (η^(-(n : ℝ)) * ψ (fun i => x i / η))
        = ∫ x, η^(-(n : ℝ)) * ψ (g x) := by
              rw [h_rewrite]
    _ = η^(-(n : ℝ)) * ∫ x, ψ (g x) := h_pull_const
    _ = η^(-(n : ℝ)) * ((ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))).toReal
          * ∫ y, ψ y) := by rw [h_change_integral]
    _ = (η^(-(n : ℝ)) * η ^ (n : ℝ)) * ∫ y, ψ y := by
          rw [h_det_toReal]
          ring
    _ = 1 * ∫ y, ψ y := by
          -- η^{-n} * η^{n} = 1
          -- Use real-power arithmetic (η > 0 ensures no sign issues)
          have : η^(-(n : ℝ)) * η^(n : ℝ) = (1 : ℝ) := by
            -- Use rpow_add with (-n) + n = 0
            have h_add := Real.rpow_add hη (-(n : ℝ)) (n : ℝ)
            have hsum : (-(n : ℝ)) + (n : ℝ) = 0 := by simp
            have : η^(-(n : ℝ)) * η^(n : ℝ) = (η : ℝ) ^ (0 : ℝ) := by
              simpa [hsum] using h_add.symm
            simpa [Real.rpow_zero] using this
          rw [this]
    _ = 1 := by rw [hψ_norm, one_mul]

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
  classical
  -- Define the scaled mollifier and the scaling map.
  set ψη : (Fin n → ℝ) → ℝ :=
    fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η) with hψη_def
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => (1 / η : ℝ) • x with hg_def

  -- Basic measurability for the scaling map
  have hg_meas : Measurable g := by
    simpa [hg_def] using (continuous_const_smul (1 / η : ℝ)).measurable

  -- Pointwise positivity of ψη due to ψ ≥ 0 and η > 0.
  have hψη_nonneg : ∀ x, 0 ≤ ψη x := by
    intro x
    have hx_arg : (η⁻¹ : ℝ) • x = fun i => x i * η⁻¹ := by
      funext i
      simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    have hψ_nonneg_at : 0 ≤ ψ (g x) := hψ_nonneg (g x)
    have hηpos : 0 ≤ η^(-(n : ℝ)) := by
      have : 0 < η^(-(n : ℝ)) := by
        simpa using Real.rpow_pos_of_pos hη (-(n : ℝ))
      exact this.le
    -- Align ψ (g x) with ψ (fun i => x i / η) using hx_arg
    simpa [hψη_def, hg_def, one_div, div_eq_mul_inv, hx_arg, mul_comm, mul_left_comm, mul_assoc]
      using mul_nonneg hηpos hψ_nonneg_at

  -- Rewrite the L¹ seminorm as a nonnegative lintegral and factor out the constant η^{-n}.
  have h_step1 :
      eLpNorm ψη 1 volume
        = ENNReal.ofReal (η^(-(n : ℝ))) *
            ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume := by
    -- Start from the L¹ formula for `eLpNorm` and rewrite the integrand.
    have hη_nonneg : 0 ≤ η^(-(n : ℝ)) := by
      have : 0 < η^(-(n : ℝ)) := by simpa using Real.rpow_pos_of_pos hη (-(n : ℝ))
      exact this.le
    have h_enorm_eq :
        ∀ᵐ x ∂volume,
          (‖ψη x‖ₑ : ℝ≥0∞)
            = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (ψ (g x)) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have hψgx_nonneg : 0 ≤ ψ (g x) := hψ_nonneg (g x)
      -- Align arguments: (η⁻¹) • x = fun i => x i * η⁻¹
      have hx_arg : (η⁻¹ : ℝ) • x = fun i => x i * η⁻¹ := by
        funext i; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
      calc
        (‖ψη x‖ₑ : ℝ≥0∞)
            = ENNReal.ofReal ‖ψη x‖ := (ofReal_norm_eq_enorm (ψη x)).symm
        _   = ENNReal.ofReal (ψη x) := by
              simp [Real.norm_eq_abs, abs_of_nonneg (hψη_nonneg x)]
        _   = ENNReal.ofReal (η^(-(n : ℝ)) * ψ (g x)) := by
              simp [hψη_def, hg_def, one_div, div_eq_mul_inv, hx_arg,
                mul_comm, mul_left_comm, mul_assoc]
        _   = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (ψ (g x)) := by
              -- Use `ENNReal.ofReal_mul` (one nonneg proof argument) and specify `p`, `q`.
              simpa [mul_comm, mul_left_comm, mul_assoc]
                using (ENNReal.ofReal_mul
                  (p := η^(-(n : ℝ))) (q := ψ (g x)) hη_nonneg)
    -- Pull the constant out of the lintegral using the `c ≠ ∞` variant.
    have h_c_ne_top : ENNReal.ofReal (η^(-(n : ℝ))) ≠ ∞ := by simp
    calc
      eLpNorm ψη 1 volume
          = ∫⁻ x, ‖ψη x‖ₑ ∂volume := by
                simp [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      _   = ∫⁻ x, ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (ψ (g x)) ∂volume := by
                simpa using lintegral_congr_ae h_enorm_eq
      _   = ENNReal.ofReal (η^(-(n : ℝ))) * ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume := by
                simpa [mul_comm, mul_left_comm, mul_assoc]
                  using
                    (lintegral_const_mul' (μ := volume)
                      (ENNReal.ofReal (η^(-(n : ℝ))))
                      (fun x : (Fin n → ℝ) => ENNReal.ofReal (ψ (g x)))
                      h_c_ne_top)

  -- Compute the pushforward of Lebesgue measure under the linear scaling map x ↦ (1/η)·x.
  have h_map_scale :
      Measure.map g volume
        = ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
    -- This is a standard Jacobian formula for linear maps on ℝ^n.
    simpa [g, hg_def]
      using Real.map_linearMap_volume_pi_eq_smul_volume_pi
        (f := ( (1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ))
        (by
          -- Show det ≠ 0 via the explicit determinant formula and η ≠ 0.
          have hne : (1 / η : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hη)
          have hdet :
              LinearMap.det
                  ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
                = (1 / η : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
            simp
          have hpow2 : (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
            pow_ne_zero (Module.finrank ℝ (Fin n → ℝ)) hne
          simpa [hdet] using hpow2)
  -- Change variables: express the lintegral of ψ ∘ g via the pushforward measure.
  have h_change :
      ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume
        = ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
            * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
    -- Build AEMeasurable for the integrand under the pushforward measure.
    have hψ_aemeas : AEMeasurable ψ volume :=
      hψ_int.aestronglyMeasurable.aemeasurable
    have h_ofReal_aemeas_map :
        AEMeasurable (fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y))
          (Measure.map g volume) := by
      -- Use the helper to transport a.e.-measurability across the scalar multiple
      -- given by `h_map_scale`.
      have h_ofReal_aemeas_vol :
          AEMeasurable (fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y)) volume :=
        hψ_aemeas.ennreal_ofReal
      -- `Measure.map g volume = c • volume` where `c = ofReal |det g|⁻¹`.
      -- Hence a.e.-measurability transfers from `volume` to `Measure.map g volume`.
      simpa [h_map_scale]
        using aemeasurable_smul_measure_of_aemeasurable
          (f := fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y))
          (μ := volume)
          (c := ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
          h_ofReal_aemeas_vol
    -- Change of variables for lintegral via `lintegral_map'`.
    have h_map_eq :=
      lintegral_map' (μ := volume)
        (f := fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y))
        (g := g) h_ofReal_aemeas_map
        (aemeasurable_id'.comp_measurable hg_meas)
    -- Pull out the scaling factor from the pushforward measure using `lintegral_smul_measure`.
    have h_pull_const :
        ∫⁻ y, ENNReal.ofReal (ψ y) ∂(Measure.map g volume)
          = ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
              * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
      simp [h_map_scale, lintegral_smul_measure, mul_comm, mul_left_comm, mul_assoc]
    simpa [h_map_eq] using h_pull_const

  -- Convert the remaining lintegral to a real integral using nonnegativity of ψ.
  have hψ_nonneg_ae : 0 ≤ᵐ[volume] fun y => ψ y :=
    Filter.Eventually.of_forall hψ_nonneg
  have hψ_lintegral :
      ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume
        = ENNReal.ofReal (∫ y, ψ y ∂volume) := by
    -- Use the standard bridge between lintegral and integral for nonnegative integrable ψ.
    simpa using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψ_int hψ_nonneg_ae).symm

  have h_det_simp :
      ENNReal.ofReal (abs ((LinearMap.det
          ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
        = ENNReal.ofReal (η ^ (n : ℝ)) := by
    -- Evaluate the determinant and simplify using η > 0.
    have hdet :
        LinearMap.det ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
          = (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) := by
      simp
    have hfinrank : (Module.finrank ℝ (Fin n → ℝ)) = n := by
      simp
    -- Since η > 0, ((1/η)^n)⁻¹ = η^n and is nonnegative, so its absolute value equals itself.
    have h_pow_inv : ((1 / η : ℝ) ^ n)⁻¹ = η ^ n := by
      -- Use (a^n)⁻¹ = (a⁻¹)^n with a = 1/η and (1/η)⁻¹ = η.
      simp [one_div, inv_inv]
    have h_nonneg : 0 ≤ ((1 / η : ℝ) ^ n)⁻¹ := by
      -- Positivity from η > 0.
      have hpos : 0 < (1 / η : ℝ) := by
        simpa [one_div] using (inv_pos.mpr hη)
      exact inv_nonneg.mpr (le_of_lt (pow_pos hpos n))
    have h_abs_eq : abs (((1 / η : ℝ) ^ n)⁻¹) = ((1 / η : ℝ) ^ n)⁻¹ :=
      abs_of_nonneg h_nonneg
    -- Translate nat-power to real-power.
    have h_nat_to_real : (η ^ n : ℝ) = η ^ (n : ℝ) := by
      simp
    -- Conclude.
    calc
      ENNReal.ofReal (abs ((LinearMap.det
          ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
          = ENNReal.ofReal (abs (((1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ))) )⁻¹) := by
            simp [hdet]
      _ = ENNReal.ofReal (abs (((1 / η : ℝ) ^ n)⁻¹)) := by simp [hfinrank]
      _ = ENNReal.ofReal (((1 / η : ℝ) ^ n)⁻¹) := by simp [abs_of_pos hη]
      _ = ENNReal.ofReal (η ^ n) := by simp [h_pow_inv]
      _ = ENNReal.ofReal (((η : ℝ) ^ (n : ℝ))) := by
        -- Avoid `simp` looping by using a directed rewrite.
        exact congrArg ENNReal.ofReal h_nat_to_real

  -- Combine all equalities and simplify using ∫ ψ = 1 and rpow rules.
  have h_prod :
      ENNReal.ofReal (η^(-(n : ℝ)))
        * (ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
        = ENNReal.ofReal 1 := by
    -- Use multiplicativity of ofReal and rpow addition.
    have hη_pos_real : 0 ≤ η^(-(n : ℝ)) :=
      (Real.rpow_pos_of_pos hη (-(n : ℝ))).le
    have hη_pow_pos : 0 ≤ η ^ (n : ℝ) :=
      (Real.rpow_pos_of_pos hη (n : ℝ)).le
    have h_mul_ofReal :
        ENNReal.ofReal (η^(-(n : ℝ)) * η ^ (n : ℝ))
          = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (η ^ (n : ℝ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using (ENNReal.ofReal_mul (p := η^(-(n : ℝ))) (q := η ^ (n : ℝ)) hη_pos_real)
    -- Simplify the product inside ofReal using rpow_add.
    have h_rpow : η^(-(n : ℝ)) * η ^ (n : ℝ) = (η : ℝ) ^ (0 : ℝ) := by
      have h_add := Real.rpow_add hη (-(n : ℝ)) (n : ℝ)
      -- x^(a+b) = x^a * x^b ⇒ x^a * x^b = x^(a+b)
      -- Here a = -n, b = n, so a + b = 0.
      have hsum : (-(n : ℝ)) + (n : ℝ) = 0 := by simp
      simpa [hsum, Real.rpow_zero] using h_add.symm
    -- Conclude the product equals 1.
    have h_one : ENNReal.ofReal ((η : ℝ) ^ (0 : ℝ)) = ENNReal.ofReal 1 := by
      simp
    calc
      ENNReal.ofReal (η^(-(n : ℝ)))
          * ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
          = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (η ^ (n : ℝ)) := by
                simp [abs_of_pos hη]
      _ = ENNReal.ofReal (η^(-(n : ℝ)) * η ^ (n : ℝ)) := by
                -- Use the earlier multiplicativity lemma tailored to rpow terms.
                simpa using h_mul_ofReal.symm
      _ = ENNReal.ofReal ((η : ℝ) ^ (0 : ℝ)) := by
        simpa using h_rpow
      _ = ENNReal.ofReal 1 := h_one

  -- Final assembly: start from `h_step1`, apply the change-of-variables `h_change`,
  -- convert the remaining lintegral using `hψ_lintegral`, and simplify with `hψ_norm`.
  calc
    eLpNorm ψη 1 volume
        = ENNReal.ofReal (η^(-(n : ℝ))) *
            ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume := h_step1
    _ = (ENNReal.ofReal (η^(-(n : ℝ))) *
            ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
            * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            congrArg (fun z => ENNReal.ofReal (η^(-(n : ℝ))) * z) h_change
    _ = ENNReal.ofReal 1 * ENNReal.ofReal (∫ y, ψ y ∂volume) := by
          -- First, multiply the constant factor equality `h_prod` by the lintegral.
          have hconst_mul :
              (ENNReal.ofReal (η^(-(n : ℝ))) *
                ENNReal.ofReal (abs ((LinearMap.det
                  ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
                * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume
                = ENNReal.ofReal 1 * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              congrArg (fun c => c * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume) h_prod
          -- Then convert the lintegral using `hψ_lintegral`.
          simpa [hψ_lintegral] using hconst_mul
    _ = ENNReal.ofReal 1 := by simp [hψ_norm]

end MollifierProperties

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
  classical
  -- Step 1: rewrite the difference of convolutions as the convolution of the difference.
  have hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * ψ y) volume := by
    have h_kernel :=
      convolution_kernel_integrable (μ := volume)
        (f := f₁) (g := ψ) hf₁ hψ
    have h := Integrable.prod_right_ae (μ := volume) (ν := volume) h_kernel
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * ψ y) volume := by
    have h_kernel :=
      convolution_kernel_integrable (μ := volume)
        (f := f₂) (g := ψ) hf₂ hψ
    have h := Integrable.prod_right_ae (μ := volume) (ν := volume) h_kernel
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have h_sub_ae := convolution_sub (f₁ := f₁) (f₂ := f₂) (g := ψ) hconv₁ hconv₂

  -- Step 2: use ae-equality to replace the L¹ norm by the convolution of the difference.
  have h_eq_eLp :
      eLpNorm (fun x =>
        (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 1 volume
        = eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 1 volume := by
    -- note the equality in `convolution_sub` has the opposite orientation
    simpa using
      eLpNorm_congr_ae (μ := volume) (p := (1 : ℝ≥0∞)) h_sub_ae.symm

  -- Step 3: apply Young (L¹×L¹→L¹) to the convolution of the difference with ψ.
  have hdiff_int : Integrable (fun x => f₁ x - f₂ x) volume := hf₁.sub hf₂
  have hdiff_mem : MemLp (fun x => f₁ x - f₂ x) 1 volume :=
    (memLp_one_iff_integrable (μ := volume)).2 hdiff_int
  have hψ_mem : MemLp ψ 1 volume :=
    (memLp_one_iff_integrable (μ := volume)).2 hψ
  have h_young :=
    young_convolution_inequality
      (f := fun x => f₁ x - f₂ x) (g := ψ)
      (p := (1 : ℝ≥0∞)) (q := (1 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (hp := by simp) (hq := by simp) (hpqr := by simp)
      hdiff_mem hψ_mem

  -- Step 4: assemble the estimate.
  have :
      eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 1 volume ≤
        eLpNorm (fun x => f₁ x - f₂ x) 1 volume * eLpNorm ψ 1 volume := by
    simpa using h_young.2
  simpa [h_eq_eLp] using this

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
    (hψ_nonneg : ∀ x, 0 ≤ ψ x)
    (hψ_int : ∫ x, ψ x = 1) :
    ∀ η : ℝ, 0 < η → η < 1 →
      eLpNorm (fun x =>
        (∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) -
        (∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)))
        1 volume ≤
      eLpNorm (fun x => g x - f₀ x) 1 volume := by
  classical
  intro η hη_pos _hη_lt_one
  -- Define the scaled mollifier (real and complex versions).
  set ψηR : (Fin n → ℝ) → ℝ :=
    fun y => η^(-(n : ℝ)) * ψ (fun i => y i / η) with hψηR_def
  set ψηC : (Fin n → ℝ) → ℂ := fun y => (ψηR y : ℝ) with hψηC_def

  -- L¹ norm of the scaled mollifier equals 1.
  -- First, obtain integrability of ψ from the normalization assumption.
  have hψ_integrable : Integrable ψ volume := by
    classical
    by_contra hnot
    have h0 : ∫ x, ψ x ∂volume = 0 := by
      simp [MeasureTheory.integral_undef hnot]  -- integral is 0 if not integrable
    have : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = ∫ x, ψ x ∂volume := by simpa using hψ_int.symm
        _ = 0 := h0
    exact one_ne_zero this
  have hψηR_L1 : eLpNorm ψηR 1 volume = ENNReal.ofReal 1 := by
    simpa [hψηR_def]
      using scaled_mollifier_L1_norm_one (ψ := ψ) (η := η)
        hη_pos hψ_integrable hψ_int hψ_nonneg
  -- Transfer the L¹ norm equality to the complex-valued version.
  have hψηC_L1 : eLpNorm ψηC 1 volume = ENNReal.ofReal 1 := by
    have h_eq : eLpNorm ψηC 1 volume = eLpNorm ψηR 1 volume := by
      refine eLpNorm_congr_norm_ae (μ := volume) (p := (1 : ℝ≥0∞)) ?_
      exact Filter.Eventually.of_forall (fun x => by
        simp [ψηC, hψηC_def, Real.norm_eq_abs])
    simpa [h_eq] using hψηR_L1

  -- Obtain integrability of the complex scaled mollifier from its finite L¹ norm.
  have hψηC_meas : AEStronglyMeasurable ψηC volume := by
    -- Build AEMeasurable for the real scaled mollifier, then lift to complex via ofReal.
    have hψ_meas : AEMeasurable ψ volume :=
      hψ_integrable.aestronglyMeasurable.aemeasurable
    have h_scale_meas : Measurable fun y : (Fin n → ℝ) => (1 / η : ℝ) • y :=
      (continuous_const_smul (1 / η : ℝ)).measurable
    -- Compute the pushforward of volume under scaling and derive quasi-measure-preserving.
    have h_map_scale :
        Measure.map (fun y : (Fin n → ℝ) => (1 / η : ℝ) • y) volume
          = ENNReal.ofReal (abs ((LinearMap.det
                ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
      simpa
        using Real.map_linearMap_volume_pi_eq_smul_volume_pi
          (f := ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))))
          (by
            have hne : (1 / η : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hη_pos)
            have hdet :
                LinearMap.det
                    ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
                  = (1 / η : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
              simp
            have hpow2 : (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
              pow_ne_zero (Module.finrank ℝ (Fin n → ℝ)) hne
            simpa [hdet] using hpow2)
    have h_scale_qmp :
        Measure.QuasiMeasurePreserving (fun y : (Fin n → ℝ) => (1 / η : ℝ) • y)
          volume volume := by
      refine ⟨h_scale_meas, ?_⟩
      have h_le :
          Measure.map (fun y : (Fin n → ℝ) => (1 / η : ℝ) • y) volume ≤
            ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
        simpa [h_map_scale] using (le_of_eq h_map_scale)
      exact Measure.absolutelyContinuous_of_le_smul h_le
    -- Compose along the quasi-measure-preserving scaling map.
    have h_comp : AEMeasurable (fun y => ψ ((1 / η) • y)) volume :=
      hψ_meas.comp_quasiMeasurePreserving h_scale_qmp
    have h_c_meas : AEMeasurable (fun _ : (Fin n → ℝ) => η^(-(n : ℝ))) volume :=
      (measurable_const : Measurable fun _ : (Fin n → ℝ) => η^(-(n : ℝ))).aemeasurable
    -- Rewrite the argument `η⁻¹ • x` to the coordinate form `fun i => x i / η`.
    have h_arg_eq_inv :
        (fun x : (Fin n → ℝ) => ψ (η⁻¹ • x))
          = (fun x : (Fin n → ℝ) => ψ (fun i => x i / η)) := by
      funext x
      have : (η⁻¹ : ℝ) • x = (fun i => x i * η⁻¹) := by
        funext i; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
      simp [div_eq_mul_inv, this]
    have h_comp' : AEMeasurable (fun y : (Fin n → ℝ) => ψ ((1 / η) • y)) volume := by
      simpa [one_div] using h_comp
    have h_comp2 : AEMeasurable (fun y : (Fin n → ℝ) => ψ (fun i => y i / η)) volume := by
      -- Convert `((1/η) • y)` to `(η⁻¹ • y)` and then rewrite by coordinates.
      have h_comp'' : AEMeasurable (fun y : (Fin n → ℝ) => ψ (η⁻¹ • y)) volume := by
        simpa [one_div] using h_comp'
      simpa [h_arg_eq_inv] using h_comp''
    have hψηR_ae : AEMeasurable ψηR volume := by
      simpa [ψηR, hψηR_def] using h_c_meas.mul h_comp2
    have hψηR_sm : AEStronglyMeasurable ψηR volume := hψηR_ae.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp_aemeasurable hψηR_sm.aemeasurable).aestronglyMeasurable

  have hψηC_int : Integrable ψηC volume := by
    -- From measurability and the finite L¹ norm we get membership in L¹, hence integrable.
    have h_lt_top : eLpNorm ψηC 1 volume < (⊤ : ℝ≥0∞) := by
      simp [hψηC_L1]
    have h_mem : MemLp ψηC 1 volume := ⟨hψηC_meas, h_lt_top⟩
    simpa using (memLp_one_iff_integrable (μ := volume)).1 h_mem

  -- Apply the L¹ convolution difference bound with the scaled mollifier.
  have h_bound :=
    convolution_diff_bound_L1 (f₁ := g) (f₂ := f₀)
      (ψ := ψηC) hg hf₀ hψηC_int

  -- Replace the multiplier by 1 using the computed L¹ norm.
  have hψηC_L1_one : eLpNorm ψηC 1 volume = (1 : ℝ≥0∞) := by
    simpa using hψηC_L1.trans (by simp)

  have h_form_total :
      (fun x =>
        (∫ y, g (x - y) * (↑(ψηR y) : ℂ)) - ∫ y, f₀ (x - y) * (↑(ψηR y) : ℂ))
        = (fun x =>
            (∫ y, g (x - y) * (((↑η : ℂ) ^ n)⁻¹ * ↑(ψ (fun i => y i / η)))) -
              ∫ y, f₀ (x - y) * (((↑η : ℂ) ^ n)⁻¹ * ↑(ψ (fun i => y i / η)))) := by
    funext x
    simp [ψηR, hψηR_def, one_div, div_eq_mul_inv,
          Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
          Real.rpow_neg (le_of_lt hη_pos), Real.rpow_natCast,
          mul_comm, mul_left_comm, mul_assoc]
  -- Apply the bound after rewriting both convolution terms inside the difference.
  simpa [ψηC, hψηC_def, hψηC_L1_one, one_mul, h_form_total]
    using h_bound

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
  classical
  -- Lebesgue measure on ℝ^n is neg-invariant; provide the instance locally for this section.
  haveI : (volume : Measure (Fin n → ℝ)).IsNegInvariant := by
    classical
    let μ : Measure (Fin n → ℝ) := volume
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
    have h_abs_det : abs (LinearMap.det T) = (1 : ℝ) := by
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
      simpa [Measure.neg] using h_map_neg
    simpa [μ] using h_neg_eq
  -- Step 1: establish a.e. integrability of the two convolution integrands
  have hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * ψ y) volume := by
    simpa using
      (MeasureTheory.convolution_fiber_integrable_L2_L1
        (μ := volume) (f := f₁) (g := ψ) hf₁ hψ)
  have hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * ψ y) volume := by
    simpa using
      (MeasureTheory.convolution_fiber_integrable_L2_L1
        (μ := volume) (f := f₂) (g := ψ) hf₂ hψ)

  -- Step 2: rewrite the difference of convolutions as the convolution of the difference
  have h_sub_ae := convolution_sub (f₁ := f₁) (f₂ := f₂) (g := ψ) hconv₁ hconv₂
  have h_eq_eLp :
      eLpNorm (fun x =>
        (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 2 volume
        = eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 2 volume := by
    simpa using eLpNorm_congr_ae (μ := volume) (p := (2 : ℝ≥0∞)) h_sub_ae.symm

  -- Step 3: apply Young's inequality in the L² × L¹ → L² form
  have hdiff_mem : MemLp (fun x => f₁ x - f₂ x) 2 volume := hf₁.sub hf₂
  have hYoung :=
    young_L2_L1 (f := fun x => f₁ x - f₂ x) (g := ψ) (hf := hdiff_mem) (hg := hψ)
  have h_bound :
      eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 2 volume ≤
        eLpNorm (fun x => f₁ x - f₂ x) 2 volume * eLpNorm ψ 1 volume := by
    simpa using hYoung.2

  -- Step 4: assemble the estimate using the a.e. equality
  simpa [h_eq_eLp] using h_bound

end ConvolutionDifferenceBounds
