import Frourio.Analysis.HolderInequality.HolderInequalityCore
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section HolderNormalized

/-- Normalized function's power equality -/
lemma holder_equality_normalized_pow
    (f : α → ℝ) (norm_f : ℝ) (pr : ℝ)
    (hnorm_f_pos : 0 < norm_f)
    (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (fun x => (f x / norm_f) ^ pr) =ᵐ[μ] fun x => (norm_f⁻¹) ^ pr * (f x ^ pr) := by
  have hnorm_inv_nonneg : 0 ≤ norm_f⁻¹ := inv_nonneg.mpr hnorm_f_pos.le
  refine hf_nonneg.mono ?_
  intro x hx
  have hx_mul : (f x / norm_f) ^ pr = f x ^ pr * norm_f⁻¹ ^ pr := by
    simpa [div_eq_mul_inv, mul_comm]
      using Real.mul_rpow (x := f x) (y := norm_f⁻¹) (z := pr) hx hnorm_inv_nonneg
  have hx_mul' : (f x / norm_f) ^ pr = norm_f⁻¹ ^ pr * f x ^ pr := by
    simpa [mul_comm, mul_left_comm] using hx_mul
  simpa using hx_mul'

/-- Normalized function's power is integrable -/
lemma holder_equality_normalized_pow_integrable
    (p : ℝ≥0∞) (f : α → ℝ) (norm_f : ℝ) (pr : ℝ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : MemLp f p μ)
    (hnorm_f_pos : 0 < norm_f)
    (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hpr : pr = p.toReal) :
    Integrable (fun x => (f x / norm_f) ^ pr) μ := by
  classical
  have hf_norm_pow : Integrable (fun x => ‖f x‖ ^ pr) μ := by
    simpa [hpr] using hf.integrable_norm_rpow hp_ne_zero hp_ne_top
  have hnorm_eq :
      (fun x => ‖f x‖ ^ pr) =ᵐ[μ] fun x => f x ^ pr :=
    hf_nonneg.mono fun x hx => by
      have hnorm : ‖f x‖ = f x := by
        simp [Real.norm_eq_abs, abs_of_nonneg hx]
      simp [hnorm]
  have hf_pow_integrable : Integrable (fun x => f x ^ pr) μ :=
    hf_norm_pow.congr hnorm_eq
  have h_const_mul : Integrable (fun x => (norm_f⁻¹) ^ pr * (f x ^ pr)) μ :=
    Integrable.const_mul hf_pow_integrable ((norm_f⁻¹) ^ pr)
  have h_eq :=
    holder_equality_normalized_pow f norm_f pr hnorm_f_pos hf_nonneg
  exact (h_const_mul.congr h_eq.symm)

/-- Normalized function's power is nonnegative -/
lemma holder_equality_normalized_pow_nonneg
    (f : α → ℝ) (norm_f : ℝ) (pr : ℝ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    (hnorm_f_pos : 0 < norm_f) :
    0 ≤ᵐ[μ] fun x => (f x / norm_f) ^ pr := by
  refine hf_pos.mono ?_
  intro x hx
  have hx_div : 0 < f x / norm_f := div_pos hx hnorm_f_pos
  exact Real.rpow_nonneg (le_of_lt hx_div) _

/-- Integral of function's power equals norm's power -/
lemma holder_equality_integral_pow
    (p : ℝ≥0∞) (f : α → ℝ) (pr : ℝ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : MemLp f p μ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    (hpr : pr = p.toReal) :
    ∫ x, f x ^ pr ∂μ = (eLpNorm f p μ).toReal ^ pr := by
  classical
  have hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x := hf_pos.mono fun _ hx => le_of_lt hx
  have hpr_pos : 0 < pr := by
    have := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    simpa [hpr] using this
  have hpr_nonneg : 0 ≤ pr := hpr_pos.le
  have hf_norm_pow : Integrable (fun x => ‖f x‖ ^ pr) μ := by
    simpa [hpr] using hf.integrable_norm_rpow hp_ne_zero hp_ne_top
  have hf_pow_eq : (fun x => ‖f x‖ ^ pr) =ᵐ[μ] fun x => f x ^ pr :=
    hf_pos.mono fun x hx => by
      have hx_nonneg : 0 ≤ f x := le_of_lt hx
      have hnorm : ‖f x‖ = f x := by
        simp [Real.norm_eq_abs, abs_of_pos hx]
      simp [hnorm]
  have hf_pow_integrable : Integrable (fun x => f x ^ pr) μ :=
    hf_norm_pow.congr hf_pow_eq
  have hf_pow_nonneg : 0 ≤ᵐ[μ] fun x => f x ^ pr :=
    hf_nonneg.mono fun x hx => Real.rpow_nonneg hx _
  have h_ofReal_integral :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_pow_integrable hf_pow_nonneg
  have h_integrand_eq :
      (fun x => ENNReal.ofReal (f x ^ pr)) =ᵐ[μ] fun x => ‖f x‖ₑ ^ pr :=
    hf_nonneg.mono fun x hx => by
      have hnorm : ‖f x‖ = f x := by
        have hx_pos : 0 ≤ f x := hx
        simp [Real.norm_eq_abs, abs_of_nonneg hx_pos]
      have h_enorm : ENNReal.ofReal (f x) = ‖f x‖ₑ := by
        simpa [hnorm, Real.norm_eq_abs, abs_of_nonneg hx] using
          (ofReal_norm_eq_enorm (f x))
      have h_rpow := ENNReal.ofReal_rpow_of_nonneg hx hpr_nonneg
      simpa [h_enorm] using h_rpow.symm
  have h_eLpNorm_eq : eLpNorm f p μ = eLpNorm' f pr μ := by
    simpa [hpr] using eLpNorm_eq_eLpNorm' (μ := μ) (p := p) (f := f) hp_ne_zero hp_ne_top
  have h_lintegral :
      ∫⁻ x, ENNReal.ofReal (f x ^ pr) ∂μ = (eLpNorm f p μ) ^ pr := by
    calc
      ∫⁻ x, ENNReal.ofReal (f x ^ pr) ∂μ
          = ∫⁻ x, ‖f x‖ₑ ^ pr ∂μ := lintegral_congr_ae h_integrand_eq
      _ = eLpNorm' f pr μ ^ pr :=
        lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr_pos
      _ = (eLpNorm f p μ) ^ pr := by
        simp [h_eLpNorm_eq]
  have h_ofReal_eq : ENNReal.ofReal (∫ x, f x ^ pr ∂μ) = (eLpNorm f p μ) ^ pr :=
    h_ofReal_integral.trans h_lintegral
  have h_integral_nonneg : 0 ≤ ∫ x, f x ^ pr ∂μ :=
    integral_nonneg_of_ae hf_pow_nonneg
  have h_final := congrArg ENNReal.toReal h_ofReal_eq
  simpa [ENNReal.toReal_ofReal, h_integral_nonneg, ENNReal.toReal_rpow] using h_final

/-- Integral of normalized function's power equals 1 -/
lemma holder_equality_normalized_integral
    (p : ℝ≥0∞) (f : α → ℝ) (norm_f : ℝ) (pr : ℝ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : MemLp f p μ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    (hnorm_f : norm_f = (eLpNorm f p μ).toReal)
    (hnorm_f_pos : 0 < norm_f)
    (hpr : pr = p.toReal) :
    ∫ x, (f x / norm_f) ^ pr ∂μ = 1 := by
  classical
  have hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x := hf_pos.mono fun _ hx => le_of_lt hx
  have h_norm_ne_zero : norm_f ≠ 0 := ne_of_gt hnorm_f_pos
  have hnorm_inv_nonneg : 0 ≤ norm_f⁻¹ := inv_nonneg.mpr hnorm_f_pos.le
  have hnorm_nonneg : 0 ≤ norm_f := hnorm_f_pos.le
  have h_pow_eq :=
    holder_equality_normalized_pow f norm_f pr hnorm_f_pos hf_nonneg
  have h_norm_pow_integrable :=
    holder_equality_normalized_pow_integrable p f norm_f pr hp_ne_zero hp_ne_top hf hnorm_f_pos
      hf_nonneg hpr
  have hf_norm_pow : Integrable (fun x => ‖f x‖ ^ pr) μ := by
    simpa [hpr] using hf.integrable_norm_rpow hp_ne_zero hp_ne_top
  have hf_pow_eq : (fun x => ‖f x‖ ^ pr) =ᵐ[μ] fun x => f x ^ pr :=
    hf_pos.mono fun x hx => by
      have hx_nonneg : 0 ≤ f x := le_of_lt hx
      have hnorm : ‖f x‖ = f x := by
        simp [Real.norm_eq_abs, abs_of_pos hx]
      simp [hnorm]
  have hf_pow_integrable : Integrable (fun x => f x ^ pr) μ :=
    hf_norm_pow.congr hf_pow_eq
  have h_integral_eq :
      ∫ x, (f x / norm_f) ^ pr ∂μ = ∫ x, (norm_f⁻¹) ^ pr * (f x ^ pr) ∂μ :=
    integral_congr_ae h_pow_eq
  have h_const_mul :
      ∫ x, (norm_f⁻¹) ^ pr * (f x ^ pr) ∂μ =
        (norm_f⁻¹) ^ pr * ∫ x, f x ^ pr ∂μ := by
    simpa using integral_const_mul ((norm_f⁻¹) ^ pr) (fun x => f x ^ pr)
  have h_integral_pow :=
    holder_equality_integral_pow p f pr hp_ne_zero hp_ne_top hf hf_pos hpr
  have h_eq_one :
      (norm_f⁻¹) ^ pr * (eLpNorm f p μ).toReal ^ pr = 1 := by
    have h_norm_pow_ne_zero : norm_f ^ pr ≠ 0 := by
      have h_pos : 0 < norm_f ^ pr := Real.rpow_pos_of_pos hnorm_f_pos pr
      exact ne_of_gt h_pos
    have h_inv : (norm_f⁻¹) ^ pr = (norm_f ^ pr)⁻¹ := Real.inv_rpow hnorm_nonneg pr
    have h_prod : (norm_f⁻¹) ^ pr * norm_f ^ pr = 1 := by
      simp [h_inv, h_norm_pow_ne_zero]
    simpa [hnorm_f] using h_prod
  calc
    ∫ x, (f x / norm_f) ^ pr ∂μ
        = (norm_f⁻¹) ^ pr * ∫ x, f x ^ pr ∂μ := by
          simpa [h_const_mul] using h_integral_eq
    _ = (norm_f⁻¹) ^ pr * ((eLpNorm f p μ).toReal ^ pr) := by simp [h_integral_pow]
    _ = 1 := h_eq_one

/-- Product of normalized functions is integrable -/
lemma holder_equality_prod_integrable
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f g : α → ℝ) (norm_f norm_g : ℝ)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hnorm_f_pos : 0 < norm_f) (hnorm_g_pos : 0 < norm_g) :
    Integrable (fun x => (f x / norm_f) * (g x / norm_g)) μ := by
  classical
  set f_norm : α → ℝ := fun x => f x / norm_f with hf_norm_def
  set g_norm : α → ℝ := fun x => g x / norm_g with hg_norm_def
  have hnorm_f_ne_zero : norm_f ≠ 0 := ne_of_gt hnorm_f_pos
  have hnorm_g_ne_zero : norm_g ≠ 0 := ne_of_gt hnorm_g_pos
  have hf_norm_mem : MemLp f_norm p μ := by
    simpa [f_norm, div_eq_mul_inv, mul_comm, hnorm_f_ne_zero] using hf.const_mul norm_f⁻¹
  have hg_norm_mem : MemLp g_norm q μ := by
    simpa [g_norm, div_eq_mul_inv, mul_comm, hnorm_g_ne_zero] using hg.const_mul norm_g⁻¹
  obtain ⟨h_integrable_norm, _⟩ :=
    holder_inequality (μ := μ) (p := p) (q := q) hpq f_norm g_norm hf_norm_mem hg_norm_mem
  have h_meas : AEStronglyMeasurable (fun x => f_norm x * g_norm x) μ :=
    hf_norm_mem.aestronglyMeasurable.mul hg_norm_mem.aestronglyMeasurable
  have h_fin_norm : HasFiniteIntegral (fun x => ‖f_norm x * g_norm x‖) μ := by
    simpa [f_norm, g_norm, Real.norm_eq_abs, abs_mul] using h_integrable_norm.hasFiniteIntegral
  have h_fin : HasFiniteIntegral (fun x => f_norm x * g_norm x) μ :=
    (hasFiniteIntegral_norm_iff (fun x => f_norm x * g_norm x)).1 h_fin_norm
  have h_integrable_prod : Integrable (fun x => f_norm x * g_norm x) μ := ⟨h_meas, h_fin⟩
  simpa [f_norm, g_norm, hf_norm_def, hg_norm_def, hnorm_f_ne_zero, hnorm_g_ne_zero] using
    h_integrable_prod

/-- Integral of product of normalized functions equals 1 -/
lemma holder_equality_prod_integral
    (f g : α → ℝ) (norm_f norm_g : ℝ) (hnorm_f_pos : 0 < norm_f) (hnorm_g_pos : 0 < norm_g)
    (h_eq : ∫ x, f x * g x ∂μ = norm_f * norm_g) :
    ∫ x, (f x / norm_f) * (g x / norm_g) ∂μ = 1 := by
  classical
  have hnorm_f_ne_zero : norm_f ≠ 0 := ne_of_gt hnorm_f_pos
  have hnorm_g_ne_zero : norm_g ≠ 0 := ne_of_gt hnorm_g_pos
  calc
    ∫ x, (f x / norm_f) * (g x / norm_g) ∂μ
        = ∫ x, (norm_f⁻¹ * norm_g⁻¹) * (f x * g x) ∂μ := by
          simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = (norm_f⁻¹ * norm_g⁻¹) * ∫ x, f x * g x ∂μ :=
      integral_const_mul (norm_f⁻¹ * norm_g⁻¹) (fun x => f x * g x)
    _ = (norm_f * norm_g) * (norm_f⁻¹ * norm_g⁻¹) := by
      simp [h_eq, mul_comm, mul_left_comm, mul_assoc]
    _ = 1 := by
      have h_mul : (norm_f * norm_g) * (norm_f⁻¹ * norm_g⁻¹)
          = (norm_f * norm_f⁻¹) * (norm_g * norm_g⁻¹) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      simp [h_mul, hnorm_f_ne_zero, hnorm_g_ne_zero]

/-- Young's inequality difference is nonnegative -/
lemma holder_equality_young_diff_nonneg
    (f g : α → ℝ) (norm_f norm_g : ℝ) (pr qr : ℝ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hg_pos : ∀ᵐ x ∂μ, 0 < g x)
    (hnorm_f_pos : 0 < norm_f) (hnorm_g_pos : 0 < norm_g)
    (hpq_real : Real.HolderConjugate pr qr) :
    0 ≤ᵐ[μ] fun x =>
      (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
      (f x / norm_f) * (g x / norm_g) := by
  classical
  have hnorm_f_ne_zero : norm_f ≠ 0 := ne_of_gt hnorm_f_pos
  have hnorm_g_ne_zero : norm_g ≠ 0 := ne_of_gt hnorm_g_pos
  refine (hf_pos.and hg_pos).mono ?_
  intro x hx
  have hxA_pos : 0 < f x / norm_f := div_pos hx.1 hnorm_f_pos
  have hxB_pos : 0 < g x / norm_g := div_pos hx.2 hnorm_g_pos
  have hxA_nonneg : 0 ≤ f x / norm_f := hxA_pos.le
  have hxB_nonneg : 0 ≤ g x / norm_g := hxB_pos.le
  have h_young :=
    Real.young_inequality_of_nonneg hxA_nonneg hxB_nonneg hpq_real
  have h_sub_nonneg :
      0 ≤ (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
            (f x / norm_f) * (g x / norm_g) :=
    sub_nonneg.mpr h_young
  simpa [div_eq_mul_inv]

/-- Young's inequality difference is integrable -/
lemma holder_equality_young_diff_integrable
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f g : α → ℝ) (norm_f norm_g : ℝ) (pr qr : ℝ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hq_ne_zero : q ≠ 0) (hq_ne_top : q ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hnorm_f_pos : 0 < norm_f) (hnorm_g_pos : 0 < norm_g)
    (hpr : pr = p.toReal) (hqr : qr = q.toReal) :
    Integrable (fun x =>
      (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
      (f x / norm_f) * (g x / norm_g)) μ := by
  classical
  have hnorm_f_ne_zero : norm_f ≠ 0 := ne_of_gt hnorm_f_pos
  have hnorm_g_ne_zero : norm_g ≠ 0 := ne_of_gt hnorm_g_pos
  set f_norm : α → ℝ := fun x => f x / norm_f with hf_norm_def
  set g_norm : α → ℝ := fun x => g x / norm_g with hg_norm_def
  have hf_norm_mem : MemLp f_norm p μ := by
    simpa [f_norm, div_eq_mul_inv, mul_comm, hnorm_f_ne_zero] using hf.const_mul norm_f⁻¹
  have hg_norm_mem : MemLp g_norm q μ := by
    simpa [g_norm, div_eq_mul_inv, mul_comm, hnorm_g_ne_zero] using hg.const_mul norm_g⁻¹
  have hpr_pos : 0 < pr := by
    have := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    simpa [hpr] using this
  have hqr_pos : 0 < qr := by
    have := ENNReal.toReal_pos hq_ne_zero hq_ne_top
    simpa [hqr] using this
  have hpr_nonneg : 0 ≤ pr := hpr_pos.le
  have hqr_nonneg : 0 ≤ qr := hqr_pos.le
  have hf_norm_pow_norm_integrable : Integrable (fun x => ‖f_norm x‖ ^ pr) μ := by
    simpa [hpr] using hf_norm_mem.integrable_norm_rpow hp_ne_zero hp_ne_top
  have hg_norm_pow_norm_integrable : Integrable (fun x => ‖g_norm x‖ ^ qr) μ := by
    simpa [hqr] using hg_norm_mem.integrable_norm_rpow hq_ne_zero hq_ne_top
  have hf_norm_pow_meas : AEStronglyMeasurable (fun x => f_norm x ^ pr) μ := by
    exact (Real.continuous_rpow_const hpr_nonneg).comp_aestronglyMeasurable
      hf_norm_mem.aestronglyMeasurable
  have hg_norm_pow_meas : AEStronglyMeasurable (fun x => g_norm x ^ qr) μ := by
    exact (Real.continuous_rpow_const hqr_nonneg).comp_aestronglyMeasurable
      hg_norm_mem.aestronglyMeasurable
  have hf_norm_pow_le :
      ∀ᵐ x ∂μ, ‖f_norm x ^ pr‖ ≤ ‖f_norm x‖ ^ pr :=
    Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using Real.abs_rpow_le_abs_rpow (f_norm x) pr
  have hg_norm_pow_le :
      ∀ᵐ x ∂μ, ‖g_norm x ^ qr‖ ≤ ‖g_norm x‖ ^ qr :=
    Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using Real.abs_rpow_le_abs_rpow (g_norm x) qr
  have hf_norm_pow_integrable : Integrable (fun x => f_norm x ^ pr) μ :=
    Integrable.mono' hf_norm_pow_norm_integrable hf_norm_pow_meas hf_norm_pow_le
  have hg_norm_pow_integrable : Integrable (fun x => g_norm x ^ qr) μ :=
    Integrable.mono' hg_norm_pow_norm_integrable hg_norm_pow_meas hg_norm_pow_le
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hqr_ne_zero : qr ≠ 0 := ne_of_gt hqr_pos
  have h_norm_pow_integrable : Integrable (fun x => f_norm x ^ pr / pr) μ := by
    simpa [div_eq_mul_inv, mul_comm, hpr_ne_zero] using
      (hf_norm_pow_integrable.const_mul (pr⁻¹))
  have h_norm_pow_integrable' : Integrable (fun x => g_norm x ^ qr / qr) μ := by
    simpa [div_eq_mul_inv, mul_comm, hqr_ne_zero] using
      (hg_norm_pow_integrable.const_mul (qr⁻¹))
  have h_prod_integrable : Integrable (fun x => f_norm x * g_norm x) μ :=
    holder_equality_prod_integrable p q hpq f g norm_f norm_g hf hg hnorm_f_pos hnorm_g_pos
  have h_sum_integrable : Integrable
      (fun x => f_norm x ^ pr / pr + g_norm x ^ qr / qr - f_norm x * g_norm x) μ := by
    have := (h_norm_pow_integrable.add h_norm_pow_integrable').sub h_prod_integrable
    simpa [sub_eq_add_neg] using this
  simpa [f_norm, g_norm, hf_norm_def, hg_norm_def, div_eq_mul_inv, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      h_sum_integrable

/-- Young's inequality difference integral equals zero -/
lemma holder_equality_young_diff_integral_zero
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f g : α → ℝ) (norm_f norm_g : ℝ) (pr qr : ℝ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top' : p ≠ ∞)
    (hq_ne_zero : q ≠ 0) (hq_ne_top' : q ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hg_pos : ∀ᵐ x ∂μ, 0 < g x)
    (hnorm_f_pos : 0 < norm_f) (hnorm_g_pos : 0 < norm_g)
    (hpr : pr = p.toReal) (hqr : qr = q.toReal)
    (hpr_pos : 0 < pr) (hqr_pos : 0 < qr)
    (h_int_f : ∫ x, (f x / norm_f) ^ pr ∂μ = 1)
    (h_int_g : ∫ x, (g x / norm_g) ^ qr ∂μ = 1)
    (h_int_fg : ∫ x, (f x / norm_f) * (g x / norm_g) ∂μ = 1)
    (hpq_real : Real.HolderConjugate pr qr) :
    ∫ x, (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
      (f x / norm_f) * (g x / norm_g) ∂μ = 0 := by
  classical
  have hnorm_f_ne_zero : norm_f ≠ 0 := ne_of_gt hnorm_f_pos
  have hnorm_g_ne_zero : norm_g ≠ 0 := ne_of_gt hnorm_g_pos
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hqr_ne_zero : qr ≠ 0 := ne_of_gt hqr_pos
  have hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x := hf_pos.mono fun _ hx => le_of_lt hx
  have hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ g x := hg_pos.mono fun _ hx => le_of_lt hx
  have hf_norm_pow_integrable :
      Integrable (fun x => (f x / norm_f) ^ pr) μ :=
    holder_equality_normalized_pow_integrable p f norm_f pr hp_ne_zero hp_ne_top' hf
      hnorm_f_pos hf_nonneg hpr
  have hg_norm_pow_integrable :
      Integrable (fun x => (g x / norm_g) ^ qr) μ :=
    holder_equality_normalized_pow_integrable q g norm_g qr hq_ne_zero hq_ne_top' hg
      hnorm_g_pos hg_nonneg hqr
  have h_prod_integrable : Integrable
      (fun x => (f x / norm_f) * (g x / norm_g)) μ :=
    holder_equality_prod_integrable p q hpq f g norm_f norm_g hf hg hnorm_f_pos hnorm_g_pos
  set A := fun x => (f x / norm_f) ^ pr / pr
  set B := fun x => (g x / norm_g) ^ qr / qr
  set C := fun x => (f x / norm_f) * (g x / norm_g)
  have hA_integrable : Integrable A μ := by
    simpa [A, div_eq_mul_inv, mul_comm]
      using hf_norm_pow_integrable.const_mul (pr⁻¹)
  have hB_integrable : Integrable B μ := by
    simpa [B, div_eq_mul_inv, mul_comm]
      using hg_norm_pow_integrable.const_mul (qr⁻¹)
  have h_sum_integrable : Integrable (fun x => A x + B x) μ :=
    hA_integrable.add hB_integrable
  have h_int_A_aux : ∫ x, A x ∂μ
      = (∫ x, (f x / norm_f) ^ pr ∂μ) * pr⁻¹ := by
    simpa [A, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using
        (integral_mul_const (μ := μ) (r := pr⁻¹)
          (f := fun x => (f x / norm_f) ^ pr))
  have h_int_B_aux : ∫ x, B x ∂μ
      = (∫ x, (g x / norm_g) ^ qr ∂μ) * qr⁻¹ := by
    simpa [B, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using
        (integral_mul_const (μ := μ) (r := qr⁻¹)
          (f := fun x => (g x / norm_g) ^ qr))
  have h_int_A : ∫ x, A x ∂μ = 1 / pr := by
    simpa [h_int_f, one_div, mul_comm] using h_int_A_aux
  have h_int_B : ∫ x, B x ∂μ = 1 / qr := by
    simpa [h_int_g, one_div, mul_comm] using h_int_B_aux
  have h_int_C : ∫ x, C x ∂μ = 1 := by
    simpa [C]
      using h_int_fg
  have h_integral_sum : ∫ x, A x + B x ∂μ = ∫ x, A x ∂μ + ∫ x, B x ∂μ :=
    integral_add hA_integrable hB_integrable
  have h_integral_total :
      ∫ x, A x + B x - C x ∂μ = ∫ x, A x + B x ∂μ - ∫ x, C x ∂μ :=
    integral_sub h_sum_integrable h_prod_integrable
  have h_result : ∫ x, A x + B x - C x ∂μ = (1 / pr + 1 / qr) - 1 := by
    calc
      ∫ x, A x + B x - C x ∂μ
          = ∫ x, A x + B x ∂μ - ∫ x, C x ∂μ := by
              simpa using h_integral_total
      _ = (∫ x, A x ∂μ + ∫ x, B x ∂μ) - ∫ x, C x ∂μ := by
              simpa using h_integral_sum
      _ = (1 / pr + 1 / qr) - 1 := by
              simp [h_int_A, h_int_B, h_int_C, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have h_inv_sum_inv : pr⁻¹ + qr⁻¹ = 1 := (Real.holderConjugate_iff.mp hpq_real).2
  have h_diff_zero_inv : pr⁻¹ + qr⁻¹ - 1 = 0 := by
    calc
      pr⁻¹ + qr⁻¹ - 1 = (1 : ℝ) - 1 := by
        simp [h_inv_sum_inv]
      _ = 0 := sub_self _
  have h_diff_zero : 1 / pr + 1 / qr - 1 = 0 := by
    simpa [one_div] using h_diff_zero_inv
  have h_final : ∫ x, A x + B x - C x ∂μ = 0 := h_result.trans h_diff_zero
  simpa [A, B, C, sub_eq_add_neg] using h_final

/-- Young's inequality difference is almost everywhere zero -/
lemma holder_equality_young_diff_zero
    (f g : α → ℝ) (norm_f norm_g : ℝ) (pr qr : ℝ)
    (h_nonneg : 0 ≤ᵐ[μ] fun x =>
      (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
      (f x / norm_f) * (g x / norm_g))
    (h_integrable : Integrable (fun x =>
      (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
      (f x / norm_f) * (g x / norm_g)) μ)
    (h_integral_zero : ∫ x, (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
      (f x / norm_f) * (g x / norm_g) ∂μ = 0) :
    (fun x => (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
      (f x / norm_f) * (g x / norm_g)) =ᵐ[μ] fun _ => (0 : ℝ) := by
  classical
  set Φ : α → ℝ :=
    fun x =>
      (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
        (f x / norm_f) * (g x / norm_g)
  have h_integrable' : Integrable Φ μ := by
    simpa [Φ, sub_eq_add_neg] using h_integrable
  have h_nonneg' : 0 ≤ᵐ[μ] Φ :=
    (h_nonneg.mono fun x hx => by simpa [Φ, sub_eq_add_neg] using hx)
  have h_integral_zero' : ∫ x, Φ x ∂μ = 0 :=
    by simpa [Φ, sub_eq_add_neg] using h_integral_zero
  have h_ofReal_integral :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_integrable' h_nonneg'
  have h_lintegral_zero : ∫⁻ x, ENNReal.ofReal (Φ x) ∂μ = 0 := by
    simpa [h_integral_zero'] using h_ofReal_integral.symm
  have h_aemeas : AEMeasurable (fun x => ENNReal.ofReal (Φ x)) μ :=
    (h_integrable'.aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have h_ofReal_zero :
      (fun x => ENNReal.ofReal (Φ x)) =ᵐ[μ] fun _ => (0 : ℝ≥0∞) :=
    (lintegral_eq_zero_iff' h_aemeas).1 h_lintegral_zero
  have h_ae_zero : Φ =ᵐ[μ] fun _ => 0 := by
    filter_upwards [h_ofReal_zero, h_nonneg'] with x hzero hnonneg
    have hx_le : Φ x ≤ 0 :=
      (ENNReal.ofReal_eq_zero.1 (by simpa using hzero))
    have hx_ge : 0 ≤ Φ x := hnonneg
    exact le_antisymm hx_le hx_ge
  simpa [Φ, sub_eq_add_neg]

/-- Conjugate exponents sum in real numbers -/
lemma conjugate_exponent_toReal_sum
    (p q : ℝ≥0∞) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hq_ne_zero : q ≠ 0) (hq_ne_top : q ≠ ∞) (hpq_sum : 1 / p + 1 / q = 1) :
    p.toReal⁻¹ + q.toReal⁻¹ = 1 := by
  have hp_inv_ne_top : 1 / p ≠ ∞ := by
    simp [one_div, hp_ne_zero]
  have hq_inv_ne_top : 1 / q ≠ ∞ := by
    simp [one_div, hq_ne_zero]
  have hp_inv_ne_top' : p⁻¹ ≠ ∞ := by simpa [one_div] using hp_inv_ne_top
  have hq_inv_ne_top' : q⁻¹ ≠ ∞ := by simpa [one_div] using hq_inv_ne_top
  have hpq_sum_inv : p⁻¹ + q⁻¹ = 1 := by simpa [one_div] using hpq_sum
  have hsum_toReal := congrArg ENNReal.toReal hpq_sum_inv
  have hsum_eq : (p⁻¹).toReal + (q⁻¹).toReal = 1 := by
    have h_lhs : (p⁻¹ + q⁻¹).toReal = (p⁻¹).toReal + (q⁻¹).toReal :=
      ENNReal.toReal_add hp_inv_ne_top' hq_inv_ne_top'
    have h_rhs : (1 : ℝ≥0∞).toReal = 1 := by simp
    simpa [h_lhs, h_rhs] using hsum_toReal
  have h_inv_p : (p⁻¹).toReal = p.toReal⁻¹ := by
    have hp_fin : p ≠ ∞ := hp_ne_top
    simp [one_div, ENNReal.toReal_inv, hp_ne_zero, hp_fin]
  have h_inv_q : (q⁻¹).toReal = q.toReal⁻¹ := by
    have hq_fin : q ≠ ∞ := hq_ne_top
    simp [one_div, ENNReal.toReal_inv, hq_ne_zero, hq_fin]
  simpa [h_inv_p, h_inv_q] using hsum_eq

lemma isConjugateExponent.real_holderConjugate_toReal
    {p q : ℝ≥0∞} (hpq : IsConjugateExponent p q)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (hq_ne_zero : q ≠ 0) (hq_ne_top : q ≠ ∞) :
    Real.HolderConjugate p.toReal q.toReal := by
  classical
  rcases hpq with hpq | hpq | hpq
  · rcases hpq with ⟨hp_eq, hq_eq⟩
    cases hq_ne_top (by simp [hq_eq])
  · rcases hpq with ⟨hp_eq, hq_eq⟩
    cases hp_ne_top (by simp [hp_eq])
  · rcases hpq with ⟨hp_gt_one, hp_lt_top, hq_gt_one, hq_lt_top, hpq_sum⟩
    have hp_real : 1 < p.toReal := by
      have := (ENNReal.toReal_lt_toReal (by simp) (by simpa using hp_ne_top)).2 hp_gt_one
      simpa using this
    have hq_real : 1 < q.toReal := by
      have := (ENNReal.toReal_lt_toReal (by simp) (by simpa using hq_ne_top)).2 hq_gt_one
      simpa using this
    have h_sum_inv :=
      conjugate_exponent_toReal_sum p q hp_ne_zero hp_ne_top hq_ne_zero hq_ne_top hpq_sum
    exact (Real.holderConjugate_iff).2 ⟨hp_real, by simpa using h_sum_inv⟩

/-- Young's equality auxiliary lemma -/
lemma holder_equality_young_eq_aux
    (pr qr : ℝ)
    (hpr_pos : 0 < pr) (hqr_pos : 0 < qr)
    (hpq_sum : 1 / pr + 1 / qr = 1) :
    ∀ {a b : ℝ}, 0 < a → 0 < b →
      a ^ pr / pr + b ^ qr / qr = a * b → a ^ pr = b ^ qr := by
  classical
  intro a b ha hb h_eq
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hqr_ne_zero : qr ≠ 0 := ne_of_gt hqr_pos
  have w_pos : 0 < 1 / pr := one_div_pos.mpr hpr_pos
  set w : ℝ := 1 / pr
  have hpq_sum' : 1 / pr + 1 / qr = 1 := by
    simpa [w] using hpq_sum
  have one_sub_w_eq : 1 - w = 1 / qr := by
    have : 1 / qr = 1 - 1 / pr := (eq_sub_iff_add_eq').2 hpq_sum'
    simpa [w] using this.symm
  have h_inv_eq_qr : 1 - pr⁻¹ = qr⁻¹ := by
    have : 1 - 1 / pr = 1 / qr := by simpa [w] using one_sub_w_eq
    simpa [one_div] using this
  have hpr_gt_one : 1 < pr := by
    have hrepr : 1 / pr = 1 - 1 / qr :=
      (eq_sub_iff_add_eq').2 <| by simpa [add_comm] using hpq_sum'
    have hlt : 1 / pr < 1 / (1 : ℝ) := by
      have hpos : 0 < 1 / qr := one_div_pos.mpr hqr_pos
      have := sub_lt_self (1 : ℝ) hpos
      simpa [hrepr] using this
    have := lt_of_one_div_lt_one_div hpr_pos hlt
    simpa using this
  have hw_lt_one : w < 1 := by
    have hlt := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 1) hpr_gt_one
    simpa [w] using hlt
  have one_sub_w_pos : 0 < 1 - w := sub_pos.mpr hw_lt_one
  set x : ℝ := a ^ pr
  set y : ℝ := b ^ qr
  have hx_pos : 0 < x := Real.rpow_pos_of_pos ha _
  have hy_pos : 0 < y := Real.rpow_pos_of_pos hb _
  have ha_nonneg : 0 ≤ a := le_of_lt ha
  have hb_nonneg : 0 ≤ b := le_of_lt hb
  have hx_pow : x ^ w = a := by
    have := Real.rpow_rpow_inv ha_nonneg (by simpa using hpr_ne_zero)
    simpa [x, w] using this
  have hy_pow : y ^ (1 - w) = b := by
    have hy := Real.rpow_rpow_inv hb_nonneg (by simpa using hqr_ne_zero)
    convert hy using 1 with
    · simp [y, one_sub_w_eq, one_div]
  have hw_mul_eq : w * x + (1 - w) * y = x ^ w * y ^ (1 - w) := by
    have h_left : w * x + (1 - w) * y = a ^ pr / pr + b ^ qr / qr := by
      simp [w, one_sub_w_eq, x, y, div_eq_mul_inv, mul_comm, mul_left_comm, add_comm, add_left_comm,
        h_inv_eq_qr]
    have h_right : x ^ w * y ^ (1 - w) = a * b := by
      simp [x, y, hx_pow, hy_pow]
    simpa [h_right] using h_left.trans h_eq
  let weights : Fin 2 → ℝ := ![w, 1 - w]
  let values : Fin 2 → ℝ := ![x, y]
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ weights i := by
    intro i hi
    fin_cases i <;> simp [weights, w_pos.le, one_sub_w_pos.le]
  have hw_sum : ∑ i ∈ (Finset.univ : Finset (Fin 2)), weights i = 1 := by
    simp [weights, Fin.sum_univ_two]
  have hz_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ values i := by
    intro i hi
    fin_cases i <;> simp [values, hx_pos.le, hy_pos.le]
  have h_geom_arith :
      ∏ i ∈ (Finset.univ : Finset (Fin 2)), values i ^ weights i =
        ∑ i ∈ (Finset.univ : Finset (Fin 2)), weights i * values i := by
    simpa [values, weights, Fin.prod_univ_two, Fin.sum_univ_two]
      using hw_mul_eq.symm
  have h_condition :=
    (Real.geom_mean_eq_arith_mean_weighted_iff
        (s := (Finset.univ : Finset (Fin 2))) (w := weights) (z := values)
        hw_nonneg hw_sum hz_nonneg).1 h_geom_arith
  have hw_ne_zero : weights 0 ≠ 0 := by
    simp [weights, ne_of_gt w_pos]
  have h_one_sub_w_ne_zero : weights 1 ≠ 0 := by
    simp [weights, ne_of_gt one_sub_w_pos]
  have hx_eq := h_condition 0 (by simp) hw_ne_zero
  have hy_eq := h_condition 1 (by simp) h_one_sub_w_ne_zero
  have hx_eq' : x = w * x + (1 - w) * y := by
    simpa [values, weights, Fin.sum_univ_two] using hx_eq
  have hy_eq' : y = w * x + (1 - w) * y := by
    simpa [values, weights, Fin.sum_univ_two] using hy_eq
  have hxy : x = y := by
    have := hx_eq'.trans hy_eq'.symm
    simpa using this
  simpa [x, y]

/-- Normalized functions' powers are equal almost everywhere -/
lemma holder_equality_normalized_eq
    (p q : ℝ≥0∞)
    (hpq_sum : 1 / p + 1 / q = (1 : ℝ≥0∞))
    (f g : α → ℝ) (norm_f norm_g : ℝ) (pr qr : ℝ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top' : p ≠ ∞)
    (hq_ne_zero : q ≠ 0) (hq_ne_top' : q ≠ ∞)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hg_pos : ∀ᵐ x ∂μ, 0 < g x)
    (hnorm_f_pos : 0 < norm_f) (hnorm_g_pos : 0 < norm_g)
    (hpr : pr = p.toReal) (hqr : qr = q.toReal)
    (hpr_pos : 0 < pr) (hqr_pos : 0 < qr)
    (h_diff_zero : (fun x => (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
      (f x / norm_f) * (g x / norm_g)) =ᵐ[μ] fun _ => (0 : ℝ)) :
    (fun x => (f x / norm_f) ^ pr) =ᵐ[μ] fun x => (g x / norm_g) ^ qr := by
  classical
  have h_inv_sum_toReal :=
    conjugate_exponent_toReal_sum p q hp_ne_zero hp_ne_top' hq_ne_zero hq_ne_top' hpq_sum
  have h_sum_inv : pr⁻¹ + qr⁻¹ = 1 := by
    simpa [hpr, hqr] using h_inv_sum_toReal
  have h_sum_real : 1 / pr + 1 / qr = 1 := by simpa [one_div] using h_sum_inv
  have h_pow_eq : ∀ᵐ x ∂μ, (f x / norm_f) ^ pr = (g x / norm_g) ^ qr := by
    filter_upwards [hf_pos, hg_pos, h_diff_zero] with x hf_pos_x hg_pos_x h_zero
    have ha_pos : 0 < f x / norm_f :=
      div_pos hf_pos_x hnorm_f_pos
    have hb_pos : 0 < g x / norm_g :=
      div_pos hg_pos_x hnorm_g_pos
    have h_eq :
        (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr =
          (f x / norm_f) * (g x / norm_g) := by
      have h_zero' :
          (f x / norm_f) ^ pr / pr + (g x / norm_g) ^ qr / qr -
              (f x / norm_f) * (g x / norm_g) = 0 := by
        simpa using h_zero
      exact sub_eq_zero.mp h_zero'
    have :=
      holder_equality_young_eq_aux pr qr hpr_pos hqr_pos h_sum_real
        (a := f x / norm_f) (b := g x / norm_g) ha_pos hb_pos h_eq
    simpa using this
  simpa using h_pow_eq

/-- Original functions' powers are proportional -/
lemma holder_equality_proportional
    (f g : α → ℝ) (norm_f norm_g : ℝ) (pr qr : ℝ) (c : ℝ)
    (hc_def : c = norm_f ^ pr / norm_g ^ qr)
    (hnorm_f_pos : 0 < norm_f) (hnorm_g_pos : 0 < norm_g)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hg_pos : ∀ᵐ x ∂μ, 0 < g x)
    (h_norm_eq : (fun x => (f x / norm_f) ^ pr) =ᵐ[μ] fun x => (g x / norm_g) ^ qr) :
    (fun x => (f x) ^ pr) =ᵐ[μ] fun x => c * (g x) ^ qr := by
  classical
  have h_result : ∀ᵐ x ∂μ, (f x) ^ pr = c * (g x) ^ qr := by
    filter_upwards [h_norm_eq, hf_pos, hg_pos] with x hx_eq hf_pos_x hg_pos_x
    have hf_nonneg : 0 ≤ f x := le_of_lt hf_pos_x
    have hg_nonneg : 0 ≤ g x := le_of_lt hg_pos_x
    have hnorm_f_nonneg : 0 ≤ norm_f := hnorm_f_pos.le
    have hnorm_g_nonneg : 0 ≤ norm_g := hnorm_g_pos.le
    have hx_frac_eq : (f x) ^ pr / norm_f ^ pr = (g x) ^ qr / norm_g ^ qr := by
      simpa [Real.div_rpow hf_nonneg hnorm_f_nonneg, Real.div_rpow hg_nonneg hnorm_g_nonneg]
        using hx_eq
    have hnorm_f_pow_ne_zero : norm_f ^ pr ≠ 0 :=
      (Real.rpow_pos_of_pos hnorm_f_pos pr).ne'
    have h_left : (f x) ^ pr = (f x) ^ pr / norm_f ^ pr * norm_f ^ pr := by
      have h : (f x) ^ pr / norm_f ^ pr * norm_f ^ pr = (f x) ^ pr := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hnorm_f_pow_ne_zero]
      simpa using h.symm
    have h_right : (f x) ^ pr / norm_f ^ pr * norm_f ^ pr =
        (g x) ^ qr / norm_g ^ qr * norm_f ^ pr := by
      have h := congrArg (fun t => t * norm_f ^ pr) hx_frac_eq
      simpa [mul_comm, mul_left_comm, mul_assoc, hnorm_f_pow_ne_zero]
        using h
    have hx_mul : (f x) ^ pr = (g x) ^ qr / norm_g ^ qr * norm_f ^ pr :=
      h_left.trans h_right
    simpa [hc_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hx_mul
  simpa using h_result

/--
**Hölder's inequality attains equality.**

Equality holds in Hölder's inequality when f^p and g^q are proportional.
-/
theorem holder_equality_condition
    (p q : ℝ≥0∞)
    (hp : 1 < p) (hp_top : p < ∞)
    (hpq : IsConjugateExponent p q)
    (f : α → ℝ) (g : α → ℝ)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ)
    (hμ_pos : μ Set.univ ≠ 0)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    (hg_pos : ∀ᵐ x ∂μ, 0 < g x)
    (h_eq : ∫ x, f x * g x ∂μ =
            (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal) :
    ∃ (c : ℝ), 0 < c ∧ (fun x => (f x) ^ p.toReal) =ᵐ[μ]
               (fun x => c * (g x) ^ q.toReal) := by
  classical
  have h_conj :
      ∃ (hq : 1 < q) (hq_top : q < ∞), 1 / p + 1 / q = (1 : ℝ≥0∞) := by
    rcases hpq with h|h|h
    · rcases h with ⟨hp_eq, _⟩
      have : ¬(1 < (1 : ℝ≥0∞)) := by simp
      exact (this (by simp [hp_eq] at hp)).elim
    · rcases h with ⟨hp_eq, _⟩
      have : ¬((∞ : ℝ≥0∞) < ∞) := by simp
      exact (this (by simp [hp_eq] at hp_top)).elim
    · rcases h with ⟨_, _, hq, hq_top, hpq_sum⟩
      exact ⟨hq, hq_top, hpq_sum⟩
  rcases h_conj with ⟨hq, hq_top, hpq_sum⟩
  set pr := p.toReal with hpr
  set qr := q.toReal with hqr
  have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
  have hq_ne_top : q ≠ ∞ := ne_of_lt hq_top
  have hp_pos' : 0 < p := zero_lt_one.trans hp
  have hq_pos' : 0 < q := zero_lt_one.trans hq
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos'
  have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos'
  have pr_pos : 0 < pr := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have qr_pos : 0 < qr := ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have pr_nonneg : 0 ≤ pr := pr_pos.le
  have qr_nonneg : 0 ≤ qr := qr_pos.le
  have h_holder :=
    holder_inequality (μ := μ) (p := p) (q := q) hpq f g hf hg
  obtain ⟨h_integrable, h_le⟩ := h_holder
  have h_mul_pos : 0 ≤ᵐ[μ] fun x => f x * g x :=
    (hf_pos.and hg_pos).mono fun x hx =>
      mul_nonneg (le_of_lt hx.1) (le_of_lt hx.2)
  have h_abs_eq :
      (fun x => |f x * g x|) =ᵐ[μ] fun x => f x * g x :=
    (hf_pos.and hg_pos).mono fun x hx => by
      have hx_nonneg : 0 ≤ f x * g x :=
        mul_nonneg (le_of_lt hx.1) (le_of_lt hx.2)
      simp [hx_nonneg, Real.norm_eq_abs]
  have h_abs_norm_eq :
      ∫ x, |f x * g x| ∂μ = ∫ x, f x * g x ∂μ :=
    integral_congr_ae h_abs_eq
  have h_nonneg_int : 0 ≤ ∫ x, f x * g x ∂μ :=
    integral_nonneg_of_ae h_mul_pos
  have h_norm_eq :
      ∫ x, ‖f x‖ * ‖g x‖ ∂μ = ∫ x, f x * g x ∂μ := by
    have h_norm_abs :
        (fun x => ‖f x‖ * ‖g x‖) =ᵐ[μ] fun x => |f x * g x| :=
      Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs, abs_mul]
    calc
      ∫ x, ‖f x‖ * ‖g x‖ ∂μ
          = ∫ x, |f x * g x| ∂μ := integral_congr_ae h_norm_abs
      _ = ∫ x, f x * g x ∂μ := h_abs_norm_eq
  have h_equality :
      ∫ x, |f x| * |g x| ∂μ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
    have h_abs_norm :
        ∫ x, |f x| * |g x| ∂μ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      simp [Real.norm_eq_abs, abs_mul, mul_comm, mul_left_comm, mul_assoc]
    have h_norm :
        ∫ x, ‖f x‖ * ‖g x‖ ∂μ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal :=
      h_norm_eq.trans h_eq
    exact h_abs_norm.trans h_norm
  have h_le' :
      ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal :=
    h_le
  have h_eq_holder :
      ∫ x, |f x| * |g x| ∂μ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal :=
    h_equality
  have h_norm_pos_f : 0 < (eLpNorm f p μ).toReal :=
    eLpNorm_toReal_pos_of_ae_pos (μ := μ) (p := p) (f := f) hp hf hf_pos hμ_pos
  have h_norm_pos_g : 0 < (eLpNorm g q μ).toReal :=
    eLpNorm_toReal_pos_of_ae_pos (μ := μ) (p := q) (f := g) hq hg hg_pos hμ_pos
  set norm_f := (eLpNorm f p μ).toReal with hnorm_f
  set norm_g := (eLpNorm g q μ).toReal with hnorm_g
  have norm_f_pos : 0 < norm_f := by simpa [norm_f, hnorm_f] using h_norm_pos_f
  have norm_g_pos : 0 < norm_g := by simpa [norm_g, hnorm_g] using h_norm_pos_g
  have norm_f_nonneg : 0 ≤ norm_f := norm_f_pos.le
  have norm_g_nonneg : 0 ≤ norm_g := norm_g_pos.le
  set c : ℝ := norm_f ^ pr / norm_g ^ qr with hc_def
  have hc_pos : 0 < c := by
    have hnum_pos : 0 < norm_f ^ pr := Real.rpow_pos_of_pos norm_f_pos _
    have hden_pos : 0 < norm_g ^ qr := Real.rpow_pos_of_pos norm_g_pos _
    have hden_ne_zero : norm_g ^ qr ≠ 0 := ne_of_gt hden_pos
    exact div_pos hnum_pos hden_pos
  refine ⟨c, hc_pos, ?_⟩
  classical
  have norm_f_ne_zero : norm_f ≠ 0 := ne_of_gt norm_f_pos
  have norm_g_ne_zero : norm_g ≠ 0 := ne_of_gt norm_g_pos
  set f_norm : α → ℝ := fun x => f x / norm_f with hf_norm_def
  set g_norm : α → ℝ := fun x => g x / norm_g with hg_norm_def
  have hf_norm_mem : MemLp f_norm p μ := by
    simpa [f_norm, div_eq_mul_inv, mul_comm] using hf.const_mul norm_f⁻¹
  have hg_norm_mem : MemLp g_norm q μ := by
    simpa [g_norm, div_eq_mul_inv, mul_comm] using hg.const_mul norm_g⁻¹
  have hf_norm_pos : ∀ᵐ x ∂μ, 0 < f_norm x :=
    hf_pos.mono fun x hx => by
      have := div_pos hx norm_f_pos
      simpa [f_norm, div_eq_mul_inv]
  have hg_norm_pos : ∀ᵐ x ∂μ, 0 < g_norm x :=
    hg_pos.mono fun x hx => by
      have := div_pos hx norm_g_pos
      simpa [g_norm, div_eq_mul_inv]
  have hf_norm_nonneg : 0 ≤ᵐ[μ] fun x => f_norm x := hf_norm_pos.mono fun _ hx => hx.le
  have hg_norm_nonneg : 0 ≤ᵐ[μ] fun x => g_norm x := hg_norm_pos.mono fun _ hx => hx.le
  have hf_abs_eq :
      (fun x => ‖f x‖ ^ pr) =ᵐ[μ] fun x => (f x) ^ pr :=
    hf_pos.mono fun x hx => by
      have hx_nonneg : 0 ≤ f x := le_of_lt hx
      have hnorm : ‖f x‖ = f x := by
        simp [Real.norm_eq_abs, abs_of_pos hx]
      simp [hnorm]
  have hg_abs_eq :
      (fun x => ‖g x‖ ^ qr) =ᵐ[μ] fun x => (g x) ^ qr :=
    hg_pos.mono fun x hx => by
      have hx_nonneg : 0 ≤ g x := le_of_lt hx
      have hnorm : ‖g x‖ = g x := by
        simp [Real.norm_eq_abs, abs_of_pos hx]
      simp [hnorm]
  have hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x := hf_pos.mono fun _ hx => le_of_lt hx
  have hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ g x := hg_pos.mono fun _ hx => le_of_lt hx
  have hf_pow_integrable : Integrable (fun x => f x ^ pr) μ :=
    (hf.integrable_norm_rpow hp_ne_zero hp_ne_top).congr hf_abs_eq
  have hg_pow_integrable : Integrable (fun x => g x ^ qr) μ :=
    (hg.integrable_norm_rpow hq_ne_zero hq_ne_top).congr hg_abs_eq
  have hf_norm_pow_eq :
      (fun x => f_norm x ^ pr)
        =ᵐ[μ] fun x => (norm_f⁻¹) ^ pr * (f x ^ pr) :=
    holder_equality_normalized_pow f norm_f pr norm_f_pos hf_nonneg
  have hg_norm_pow_eq :
      (fun x => g_norm x ^ qr)
        =ᵐ[μ] fun x => (norm_g⁻¹) ^ qr * (g x ^ qr) :=
    holder_equality_normalized_pow g norm_g qr norm_g_pos hg_nonneg
  have hf_norm_pow_integrable : Integrable (fun x => f_norm x ^ pr) μ :=
    holder_equality_normalized_pow_integrable p f norm_f pr hp_ne_zero hp_ne_top hf norm_f_pos
      hf_nonneg rfl
  have hg_norm_pow_integrable : Integrable (fun x => g_norm x ^ qr) μ :=
    holder_equality_normalized_pow_integrable q g norm_g qr hq_ne_zero hq_ne_top hg norm_g_pos
      hg_nonneg rfl
  have hf_norm_pow_nonneg :
      0 ≤ᵐ[μ] fun x => f_norm x ^ pr :=
    holder_equality_normalized_pow_nonneg f norm_f pr hf_pos norm_f_pos
  have hg_norm_pow_nonneg :
      0 ≤ᵐ[μ] fun x => g_norm x ^ qr :=
    holder_equality_normalized_pow_nonneg g norm_g qr hg_pos norm_g_pos
  have hf_integral_aux : ∫ x, f x ^ pr ∂μ = norm_f ^ pr :=
    holder_equality_integral_pow p f pr hp_ne_zero hp_ne_top hf hf_pos rfl
  have hg_integral_aux : ∫ x, g x ^ qr ∂μ = norm_g ^ qr :=
    holder_equality_integral_pow q g qr hq_ne_zero hq_ne_top hg hg_pos rfl
  have h_integral_f_norm_pow : ∫ x, f_norm x ^ pr ∂μ = 1 :=
    holder_equality_normalized_integral
      p f norm_f pr hp_ne_zero hp_ne_top hf hf_pos rfl norm_f_pos rfl
  have h_integral_g_norm_pow : ∫ x, g_norm x ^ qr ∂μ = 1 :=
    holder_equality_normalized_integral
      q g norm_g qr hq_ne_zero hq_ne_top hg hg_pos rfl norm_g_pos rfl
  have h_prod_integrable : Integrable (fun x => f_norm x * g_norm x) μ :=
    holder_equality_prod_integrable p q hpq f g norm_f norm_g hf hg norm_f_pos norm_g_pos
  have hpq_real : Real.HolderConjugate pr qr := by
    have hp_ne_top : p ≠ ∞ := hp_ne_top
    have hq_ne_top : q ≠ ∞ := hq_ne_top
    have hp_ne_zero' : p ≠ 0 := hp_ne_zero
    have hq_ne_zero' : q ≠ 0 := hq_ne_zero
    have := isConjugateExponent.real_holderConjugate_toReal
      hpq hp_ne_zero' hp_ne_top hq_ne_zero' hq_ne_top
    simpa [pr, hpr, qr, hqr] using this
  have h_prod_eq :
      (fun x => f_norm x * g_norm x)
        =ᵐ[μ] fun x => (norm_f⁻¹ * norm_g⁻¹) * (f x * g x) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [f_norm, g_norm, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have h_integral_fg_norm : ∫ x, f_norm x * g_norm x ∂μ = 1 :=
    holder_equality_prod_integral f g norm_f norm_g norm_f_pos norm_g_pos h_eq
  have h_diff_nonneg :
      0 ≤ᵐ[μ]
        fun x =>
          f_norm x ^ pr / pr + g_norm x ^ qr / qr - f_norm x * g_norm x :=
    holder_equality_young_diff_nonneg f g norm_f norm_g pr qr
      hf_pos hg_pos norm_f_pos norm_g_pos hpq_real
  have h_diff_integrable : Integrable
      (fun x => f_norm x ^ pr / pr + g_norm x ^ qr / qr - f_norm x * g_norm x) μ :=
    holder_equality_young_diff_integrable p q hpq f g norm_f norm_g pr qr
      hp_ne_zero hp_ne_top hq_ne_zero hq_ne_top hf hg norm_f_pos norm_g_pos rfl rfl
  have h_diff_integral_zero :
      ∫ x, f_norm x ^ pr / pr + g_norm x ^ qr / qr - f_norm x * g_norm x ∂μ = 0 :=
    holder_equality_young_diff_integral_zero
      p q hpq f g norm_f norm_g pr qr hp_ne_zero hp_ne_top hq_ne_zero hq_ne_top
      hf hg hf_pos hg_pos norm_f_pos norm_g_pos rfl rfl pr_pos qr_pos
      h_integral_f_norm_pow h_integral_g_norm_pow h_integral_fg_norm hpq_real
  have h_diff_zero :
      (fun x => f_norm x ^ pr / pr + g_norm x ^ qr / qr - f_norm x * g_norm x)
        =ᵐ[μ] fun _ => (0 : ℝ) :=
    holder_equality_young_diff_zero f g norm_f norm_g pr qr
      h_diff_nonneg h_diff_integrable h_diff_integral_zero
  have hpq_sum_real_inv : pr⁻¹ + qr⁻¹ = 1 := by
    simpa [pr, hpr, qr, hqr]
      using conjugate_exponent_toReal_sum p q hp_ne_zero hp_ne_top hq_ne_zero hq_ne_top hpq_sum
  have hpq_sum_real : 1 / pr + 1 / qr = 1 := by
    simpa [one_div] using hpq_sum_real_inv
  have young_eq_aux :
      ∀ {a b : ℝ}, 0 < a → 0 < b →
        a ^ pr / pr + b ^ qr / qr = a * b → a ^ pr = b ^ qr :=
    fun {a b} ha hb h_eq' =>
      holder_equality_young_eq_aux pr qr pr_pos qr_pos hpq_sum_real ha hb h_eq'
  have h_norm_eq_aeme :
      (fun x => f_norm x ^ pr) =ᵐ[μ] fun x => g_norm x ^ qr :=
    holder_equality_normalized_eq p q hpq_sum
      f g norm_f norm_g pr qr hp_ne_zero hp_ne_top hq_ne_zero hq_ne_top
      hf_pos hg_pos norm_f_pos norm_g_pos rfl rfl pr_pos qr_pos h_diff_zero
  have h_goal :
      (fun x => f x ^ pr) =ᵐ[μ] fun x => c * g x ^ qr :=
    holder_equality_proportional f g norm_f norm_g pr qr c rfl
      norm_f_pos norm_g_pos hf_pos hg_pos h_norm_eq_aeme
  -- Final scaling back to original statement
  exact h_goal

end HolderNormalized

section AuxiliaryLemmas

/--
**Conjugate exponent computation.**

Compute the conjugate exponent explicitly from p.
-/
theorem conjugate_exponent_formula
    (p : ℝ≥0∞)
    (hp : 1 < p) (hp_top : p < ∞) :
    ∃ q : ℝ≥0∞, IsConjugateExponent p q ∧
    q = ENNReal.ofReal (p.toReal / (p.toReal - 1)) := by
  classical
  have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
  set pr := p.toReal with hpr
  have hpr_gt_one : 1 < pr := by
    have := (ENNReal.toReal_lt_toReal (by simp) hp_ne_top).2 hp
    simpa [hpr] using this
  have hpr_pos : 0 < pr := zero_lt_one.trans hpr_gt_one
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hpr_sub_pos : 0 < pr - 1 := sub_pos.2 hpr_gt_one
  have hpr_sub_ne_zero : pr - 1 ≠ 0 := ne_of_gt hpr_sub_pos
  set qrReal := pr / (pr - 1) with hqrReal
  set q : ℝ≥0∞ := ENNReal.ofReal qrReal with hq
  have hq_ne_top : q ≠ ∞ := by simp [hq]
  have hq_pos_real : 0 < qrReal := div_pos hpr_pos hpr_sub_pos
  have hq_real_gt_one : 1 < qrReal := by
    have hdiff : qrReal - 1 = 1 / (pr - 1) := by
      field_simp [hqrReal, hpr_ne_zero, hpr_sub_ne_zero]
    have hpos' : 0 < qrReal - 1 := by
      have h := one_div_pos.2 hpr_sub_pos
      exact hdiff.symm ▸ h
    exact sub_pos.mp hpos'
  have hq_gt_one : 1 < q := by
    have h := (ENNReal.ofReal_lt_ofReal_iff hq_pos_real).2 hq_real_gt_one
    simpa [hq] using h
  have hq_lt_top : q < ∞ := by simp [hq]
  have hp_ofReal : ENNReal.ofReal pr = p := by
    simp [hp_ne_top, hpr]
  have hp_inv : p⁻¹ = ENNReal.ofReal (1 / pr) := by
    have := (ENNReal.ofReal_inv_of_pos hpr_pos).symm
    simpa [hp_ofReal, one_div] using this
  have hq_inv : q⁻¹ = ENNReal.ofReal (1 / qrReal) := by
    have := (ENNReal.ofReal_inv_of_pos hq_pos_real).symm
    simpa [hq, one_div] using this
  have hsum_real : 1 / pr + 1 / qrReal = 1 := by
    field_simp [hqrReal, hpr_ne_zero, hpr_sub_ne_zero]
  have hsum_real_inv : pr⁻¹ + qrReal⁻¹ = 1 := by simpa [one_div] using hsum_real
  have hsum : 1 / p + 1 / q = 1 := by
    have h1 : 0 ≤ 1 / pr := by positivity
    have h2 : 0 ≤ 1 / qrReal := by positivity
    calc
      1 / p + 1 / q = p⁻¹ + q⁻¹ := by simp [one_div]
      _ = ENNReal.ofReal (1 / pr) + ENNReal.ofReal (1 / qrReal) := by simp [hp_inv, hq_inv]
      _ = ENNReal.ofReal (1 / pr + 1 / qrReal) := (ENNReal.ofReal_add h1 h2).symm
      _ = ENNReal.ofReal 1 := by simp [hsum_real_inv]
      _ = 1 := by simp
  refine ⟨q, ?_, by simp [hq, hpr, hqrReal]⟩
  refine Or.inr ?_
  refine Or.inr ?_
  exact ⟨hp, hp_top, hq_gt_one, hq_lt_top, hsum⟩

/--
**Self-conjugate property.**

p = 2 is its own conjugate exponent.
-/
theorem conjugate_exponent_two : IsConjugateExponent 2 2 := by
  classical
  have htop : (2 : ℝ≥0∞) < ∞ := (lt_top_iff_ne_top.mpr (by simp))
  obtain ⟨q, hq, hq_eq⟩ := conjugate_exponent_formula (p := (2 : ℝ≥0∞))
    (hp := by norm_num) (hp_top := htop)
  have hq_two : q = (2 : ℝ≥0∞) := by
    have hsimp : (2 : ℝ) / (2 - 1) = (2 : ℝ) := by norm_num
    have hq_eq' : q = ENNReal.ofReal ((2 : ℝ) / (2 - 1)) := by
      simpa using hq_eq
    have hq_ofReal : q = ENNReal.ofReal (2 : ℝ) := by simpa [hsimp] using hq_eq'
    simpa using hq_ofReal
  simpa [hq_two] using hq

/--
**Monotonicity in Hölder's inequality.**

If ‖f₁‖_p ≤ ‖f₂‖_p and ‖g₁‖_q ≤ ‖g₂‖_q, then the Hölder bound increases.
-/
theorem holder_monotone
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f₁ f₂ : α → ℝ) (g₁ g₂ : α → ℝ)
    (hf₁ : MemLp f₁ p μ) (hf₂ : MemLp f₂ p μ)
    (hg₁ : MemLp g₁ q μ) (hg₂ : MemLp g₂ q μ)
    (hf : ∀ᵐ x ∂μ, |f₁ x| ≤ |f₂ x|)
    (hg : ∀ᵐ x ∂μ, |g₁ x| ≤ |g₂ x|) :
    ∫ x, |f₁ x * g₁ x| ∂μ ≤ ∫ x, |f₂ x * g₂ x| ∂μ := by
  classical
  have hint₁ := memLp_mul_of_memLp_conjugate (μ := μ) p q hpq f₁ g₁ hf₁ hg₁
  have hint₂ := memLp_mul_of_memLp_conjugate (μ := μ) p q hpq f₂ g₂ hf₂ hg₂
  have hint_abs₁ : Integrable (fun x => |f₁ x * g₁ x|) μ := hint₁.abs
  have hint_abs₂ : Integrable (fun x => |f₂ x * g₂ x|) μ := hint₂.abs
  have h_mono : ∀ᵐ x ∂μ, |f₁ x * g₁ x| ≤ |f₂ x * g₂ x| := by
    filter_upwards [hf, hg] with x hfx hgx
    have h1 : |f₁ x| * |g₁ x| ≤ |f₂ x| * |g₁ x| :=
      mul_le_mul_of_nonneg_right hfx (abs_nonneg _)
    have h2 : |f₂ x| * |g₁ x| ≤ |f₂ x| * |g₂ x| :=
      mul_le_mul_of_nonneg_left hgx (abs_nonneg _)
    have h_comb : |f₁ x| * |g₁ x| ≤ |f₂ x| * |g₂ x| := le_trans h1 h2
    simpa [abs_mul] using h_comb
  have :=
    MeasureTheory.integral_mono_ae hint_abs₁ hint_abs₂ h_mono
  simpa using this

end AuxiliaryLemmas
