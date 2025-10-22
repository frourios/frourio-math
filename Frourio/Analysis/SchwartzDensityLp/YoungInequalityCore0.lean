import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
import Frourio.Analysis.SchwartzDensityLp.FubiniSection
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Measure.Haar.Basic

noncomputable section

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter

variable {G α : Type*}

section ConvolutionMeasurability

variable [MeasurableSpace G] [AddCommGroup G]
variable {μ : Measure G} [SFinite μ]

/--
**Almost everywhere strong measurability of convolution.**
-/
lemma aestronglyMeasurable_convolution
    (f g : G → ℂ)
    (h_kernel : Integrable (fun p : G × G => f (p.1 - p.2) * g p.2) (μ.prod μ))
    (h_fiber : ∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ) :
    AEStronglyMeasurable (fun x => ∫ y, f (x - y) * g y ∂μ) μ := by
  classical
  -- Record the fibrewise integrability information in a form suited for product notation.
  have h_fiber' :
      ∀ᵐ x ∂μ, Integrable (fun y => (fun p : G × G => f (p.1 - p.2) * g p.2) (x, y)) μ :=
    h_fiber
  -- The convolution kernel is a.e.-strongly measurable thanks to integrability.
  have h_kernel_meas :
      AEStronglyMeasurable (fun p : G × G => f (p.1 - p.2) * g p.2) (μ.prod μ) :=
    h_kernel.aestronglyMeasurable
  -- Apply the Fubini-type measurability lemma to the inner integral.
  have h_int_meas :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μ) (ν := μ) (E := ℂ) h_kernel_meas
  -- Unfold the integrand to reach the desired statement.
  simpa using h_int_meas

end ConvolutionMeasurability

section ExponentArithmetic

variable {p q r : ℝ≥0∞}

/--
**Exponent arithmetic for Young's relation in the finite case.**
-/
lemma young_exponent_relation
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hp_fin : p ≠ ∞) (hq_fin : q ≠ ∞) (hr_fin : r ≠ ∞) :
    ENNReal.toReal r =
      (ENNReal.toReal p * ENNReal.toReal q) /
        (ENNReal.toReal p + ENNReal.toReal q -
          ENNReal.toReal p * ENNReal.toReal q) := by
  classical
  set pr := ENNReal.toReal p with hpr
  set qr := ENNReal.toReal q with hqr
  set rr := ENNReal.toReal r with hrr
  have h_pos_one : (0 : ℝ≥0∞) < 1 := by simp
  have hp_pos₀ : (0 : ℝ≥0∞) < p := lt_of_lt_of_le h_pos_one hp
  have hq_pos₀ : (0 : ℝ≥0∞) < q := lt_of_lt_of_le h_pos_one hq
  have hr_pos₀ : (0 : ℝ≥0∞) < r := lt_of_lt_of_le h_pos_one hr
  have hp_ne_zero' : p ≠ 0 := ne_of_gt hp_pos₀
  have hq_ne_zero' : q ≠ 0 := ne_of_gt hq_pos₀
  have hr_ne_zero' : r ≠ 0 := ne_of_gt hr_pos₀
  have hp_pos : 0 < pr := ENNReal.toReal_pos hp_ne_zero' hp_fin
  have hq_pos : 0 < qr := ENNReal.toReal_pos hq_ne_zero' hq_fin
  have hr_pos : 0 < rr := ENNReal.toReal_pos hr_ne_zero' hr_fin
  have hp_ne_zero : pr ≠ 0 := ne_of_gt hp_pos
  have hq_ne_zero : qr ≠ 0 := ne_of_gt hq_pos
  have hr_ne_zero : rr ≠ 0 := ne_of_gt hr_pos
  have hp_inv_ne_top : p⁻¹ ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hp_ne_zero')
  have hq_inv_ne_top : q⁻¹ ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hq_ne_zero')
  have hr_inv_ne_top : r⁻¹ ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hr_ne_zero')
  have hp_inv_toReal : (p⁻¹).toReal = 1 / pr :=
    by simp [hpr, one_div, ENNReal.toReal_inv, hp_ne_zero', hp_fin]
  have hq_inv_toReal : (q⁻¹).toReal = 1 / qr :=
    by simp [hqr, one_div, ENNReal.toReal_inv, hq_ne_zero', hq_fin]
  have hr_inv_toReal : (r⁻¹).toReal = 1 / rr :=
    by simp [hrr, one_div, ENNReal.toReal_inv, hr_ne_zero', hr_fin]
  have h_left_toReal :
      ((p⁻¹ + q⁻¹).toReal) = (p⁻¹).toReal + (q⁻¹).toReal := by
    simpa [one_div] using ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top
  have h_right_toReal :
      ((1 + r⁻¹).toReal) = 1 + (r⁻¹).toReal := by
    simpa [one_div] using ENNReal.toReal_add (by simp) hr_inv_ne_top
  have hpqr' : p⁻¹ + q⁻¹ = 1 + r⁻¹ := by simpa [one_div] using hpqr
  have h_toReal := congrArg ENNReal.toReal hpqr'
  have h_real : 1 / pr + 1 / qr = 1 + 1 / rr := by
    have h := h_toReal
    have h_one : (1 : ℝ≥0∞).toReal = 1 := by simp
    have h' : (p⁻¹).toReal + (q⁻¹).toReal = 1 + (r⁻¹).toReal := by
      simpa [h_left_toReal, h_right_toReal, h_one] using h
    simpa [hp_inv_toReal, hq_inv_toReal, hr_inv_toReal] using h'
  have h_prod_ne_zero : pr * qr ≠ 0 := mul_ne_zero hp_ne_zero hq_ne_zero
  have h_mul_eq : rr * (pr + qr) = rr * (pr * qr) + pr * qr := by
    have h := congrArg (fun t : ℝ => t * (pr * qr * rr)) h_real
    have hx : pr⁻¹ * (pr * qr * rr) = qr * rr := by
      calc
        pr⁻¹ * (pr * qr * rr)
            = (pr⁻¹ * (pr * qr)) * rr := by
              simp [mul_assoc]
        _ = ((pr⁻¹ * pr) * qr) * rr := by
              simp [mul_assoc]
        _ = ((pr⁻¹ * pr) * qr) * rr := by rfl
        _ = (1 * qr) * rr := by simp [hp_ne_zero]
        _ = qr * rr := by simp [mul_assoc]
    have hy : qr⁻¹ * (pr * qr * rr) = pr * rr := by
      calc
        qr⁻¹ * (pr * qr * rr)
            = qr⁻¹ * (pr * (qr * rr)) := by
              simp [mul_assoc]
        _ = (qr⁻¹ * pr) * (qr * rr) := by
              simp [mul_assoc]
        _ = (pr * qr⁻¹) * (qr * rr) := by simp [mul_comm]
        _ = pr * (qr⁻¹ * (qr * rr)) := by simp [mul_assoc]
        _ = pr * ((qr⁻¹ * qr) * rr) := by simp [mul_assoc]
        _ = pr * (1 * rr) := by simp [hq_ne_zero]
        _ = pr * rr := by simp
    have hz : rr⁻¹ * (pr * qr * rr) = pr * qr := by
      calc
        rr⁻¹ * (pr * qr * rr)
            = (rr⁻¹ * (pr * qr)) * rr := by
              simp [mul_assoc]
        _ = (rr⁻¹ * rr) * (pr * qr) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
        _ = (1 : ℝ) * (pr * qr) := by simp [hr_ne_zero]
        _ = pr * qr := by simp
    have h_left :
        ((1 / pr + 1 / qr) * (pr * qr * rr)) = pr * rr + qr * rr := by
      calc
        ((1 / pr + 1 / qr) * (pr * qr * rr))
            = (1 / pr) * (pr * qr * rr) + (1 / qr) * (pr * qr * rr) := by
              simp [add_mul]
        _ = pr⁻¹ * (pr * qr * rr) + qr⁻¹ * (pr * qr * rr) := by
              simp [one_div]
        _ = qr * rr + pr * rr := by
              simp [hx, hy]
        _ = pr * rr + qr * rr := by
              simp [add_comm]
    have h_right :
        ((1 + 1 / rr) * (pr * qr * rr)) = rr * (pr * qr) + pr * qr := by
      calc
        ((1 + 1 / rr) * (pr * qr * rr))
            = (pr * qr * rr) + (1 / rr) * (pr * qr * rr) := by
              simp [add_mul]
        _ = pr * qr * rr + rr⁻¹ * (pr * qr * rr) := by
              simp [one_div]
        _ = pr * qr * rr + pr * qr := by
              simp [hz]
        _ = (pr * qr) * rr + pr * qr := by
              simp [mul_assoc]
        _ = rr * (pr * qr) + pr * qr := by
              simp [mul_comm, mul_left_comm, mul_assoc]
    have h_simp : pr * rr + qr * rr = rr * (pr * qr) + pr * qr := by
      calc
        pr * rr + qr * rr
            = ((1 / pr + 1 / qr) * (pr * qr * rr)) := by
              simpa using h_left.symm
        _ = ((1 + 1 / rr) * (pr * qr * rr)) := h
        _ = rr * (pr * qr) + pr * qr := by
              simpa using h_right
    simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using h_simp
  have h_cross : rr * (pr + qr - pr * qr) = pr * qr := by
    have h_diff := congrArg (fun t : ℝ => t - rr * (pr * qr)) h_mul_eq
    simpa [mul_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
      mul_comm, mul_left_comm, mul_assoc] using h_diff
  have h_den_ne_zero : pr + qr - pr * qr ≠ 0 := by
    intro hzero
    have : pr * qr = 0 := by simpa [hzero] using h_cross
    exact h_prod_ne_zero this
  have h_rr_eq : rr = pr * qr / (pr + qr - pr * qr) := by
    refine (eq_div_iff_mul_eq h_den_ne_zero).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_cross
  simpa [hrr, hpr, hqr] using h_rr_eq

/--
**Exponent arithmetic for Young's relation in the infinite case.**
-/
lemma young_exponent_inf_case
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 1 / p + 1 / q = 1) :
    ENNReal.HolderConjugate p q := by
  classical
  by_cases hp_top : p = ∞
  · have hq_one : q = 1 := by
      have h_inv : q⁻¹ = 1 := by
        simpa [hp_top, one_div, ENNReal.inv_top, zero_add] using hpq
      exact ENNReal.inv_eq_one.mp h_inv
    simpa [hp_top, hq_one] using ENNReal.HolderConjugate.top_one
  have hp_fin : p ≠ ∞ := hp_top
  by_cases hq_top : q = ∞
  · have hp_one : p = 1 := by
      have h_inv : p⁻¹ = 1 := by
        simpa [hq_top, one_div, ENNReal.inv_top, add_comm] using hpq
      exact ENNReal.inv_eq_one.mp h_inv
    simpa [hp_one, hq_top] using ENNReal.HolderConjugate.one_top
  have hq_fin : q ≠ ∞ := hq_top
  have hp_pos₀ : (0 : ℝ≥0∞) < p := zero_lt_one.trans_le hp
  have hq_pos₀ : (0 : ℝ≥0∞) < q := zero_lt_one.trans_le hq
  have hp_ne_zero' : p ≠ 0 := ne_of_gt hp_pos₀
  have hq_ne_zero' : q ≠ 0 := ne_of_gt hq_pos₀
  set pr := p.toReal with hpr
  set qr := q.toReal with hqr
  have hp_pos : 0 < pr := ENNReal.toReal_pos hp_ne_zero' hp_fin
  have hq_pos : 0 < qr := ENNReal.toReal_pos hq_ne_zero' hq_fin
  have hp_inv_ne_top : (1 / p) ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hp_ne_zero')
  have hq_inv_ne_top : (1 / q) ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hq_ne_zero')
  have hp_inv_toReal : (1 / p).toReal = 1 / pr :=
    by simp [hpr, one_div, ENNReal.toReal_inv, hp_ne_zero', hp_fin]
  have hq_inv_toReal : (1 / q).toReal = 1 / qr :=
    by simp [hqr, one_div, ENNReal.toReal_inv, hq_ne_zero', hq_fin]
  have h_left_toReal :
      ((p⁻¹ + q⁻¹).toReal) = (p⁻¹).toReal + (q⁻¹).toReal := by
    simpa [one_div] using ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top
  have hpq_inv : p⁻¹ + q⁻¹ = 1 := by simpa [one_div] using hpq
  have h_toReal := congrArg ENNReal.toReal hpq_inv
  have h_real : pr⁻¹ + qr⁻¹ = 1 := by
    have h := h_toReal
    have h_one : (1 : ℝ≥0∞).toReal = 1 := by simp
    have h' : (p⁻¹).toReal + (q⁻¹).toReal = 1 := by
      simpa [h_left_toReal, h_one] using h
    have h'' : 1 / pr + 1 / qr = 1 := by
      simpa [hp_inv_toReal, hq_inv_toReal] using h'
    simpa [one_div] using h''
  have hp_ne_zero : pr ≠ 0 := ne_of_gt hp_pos
  have hq_ne_zero : qr ≠ 0 := ne_of_gt hq_pos
  have h_inv_pr : 1 / pr = 1 - 1 / qr :=
    (eq_sub_iff_add_eq').2 <| by
      simpa [one_div, add_comm, add_left_comm, add_assoc] using h_real
  have h_inv_qr : 1 / qr = 1 - 1 / pr :=
    (eq_sub_iff_add_eq').2 <| by
      simpa [one_div, add_comm, add_left_comm, add_assoc] using h_real
  have h_inv_qr_pos : 0 < 1 / qr := one_div_pos.2 hq_pos
  have h_inv_pr_pos : 0 < 1 / pr := one_div_pos.2 hp_pos
  have h_inv_pr_lt_one : 1 / pr < 1 := by
    simpa [h_inv_pr] using sub_lt_self (1 : ℝ) h_inv_qr_pos
  have h_inv_qr_lt_one : 1 / qr < 1 := by
    simpa [h_inv_qr] using sub_lt_self (1 : ℝ) h_inv_pr_pos
  have hp_real_gt_one : 1 < pr := by
    have := mul_lt_mul_of_pos_right h_inv_pr_lt_one hp_pos
    simpa [one_div, hp_ne_zero, mul_comm, mul_left_comm, mul_assoc] using this
  have hq_real_gt_one : 1 < qr := by
    have := mul_lt_mul_of_pos_right h_inv_qr_lt_one hq_pos
    simpa [one_div, hq_ne_zero, mul_comm, mul_left_comm, mul_assoc] using this
  have hpq_real : pr.HolderConjugate qr :=
    (Real.holderConjugate_iff).2 ⟨hp_real_gt_one, by simpa [one_div] using h_real⟩
  exact ENNReal.HolderConjugate.of_toReal hpq_real

end ExponentArithmetic

section ConvolutionAuxiliary

variable {G : Type*}
variable [MeasurableSpace G]
variable (μ : Measure G) [SFinite μ]

/--
Auxiliary finite-measure version of `convolution_memLp_of_memLp`.  This lemma will be proved in the
next steps and then used to deduce the general s-finite case via exhaustion by finite measures.
-/
lemma integrable_abs_mul_eLpNorm_of_memLp
    [IsFiniteMeasure μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (f g : G → ℂ) (p q : ℝ≥0∞) (hq : 1 ≤ q) (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun y => ‖g y‖ * (eLpNorm (fun x => f (x + -y)) p μ).toReal) μ := by
  classical
  have hf_meas : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  set C := (eLpNorm f p μ).toReal with hC_def
  have h_translate_toReal :
      ∀ y : G, (eLpNorm (fun x => f (x + -y)) p μ).toReal = C := by
    intro y
    have h_norm : eLpNorm (fun x => f (x + -y)) p μ = eLpNorm f p μ := by
      simpa using eLpNorm_comp_add_right (μ := μ) (f := f) (y := -y) (p := p) hf_meas
    simp [C, hC_def, h_norm]
  have hg_L1 : MemLp g 1 μ := hg.mono_exponent (p := (1 : ℝ≥0∞)) (q := q) hq
  have hg_int : Integrable g μ := (memLp_one_iff_integrable).1 hg_L1
  have hg_norm_int : Integrable (fun y => ‖g y‖) μ := hg_int.norm
  have h_const : Integrable (fun y => ‖g y‖ * C) μ := hg_norm_int.mul_const C
  simpa [h_translate_toReal] using h_const

lemma minkowski_inequality_convolution_complex
    [IsFiniteMeasure μ] [NormedAddCommGroup G]
    (f g : G → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    (h_meas : AEStronglyMeasurable
      (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ))
    (h_prod : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ))
    (h_int : ∀ᵐ y ∂μ, Integrable (fun x => f (x - y) * g y) μ)
    (h_memLp : ∀ᵐ y ∂μ, MemLp (fun x => f (x - y) * g y) p μ)
    (h_norm : Integrable
      (fun y => ‖g y‖ * (eLpNorm (fun x => f (x - y)) p μ).toReal) μ) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) p μ ≤
      ENNReal.ofReal (∫ y, ‖g y‖ * (eLpNorm (fun x => f (x - y)) p μ).toReal ∂μ) := by
  classical
  have h_scaling :
      ∀ y : G,
        eLpNorm (fun x => f (x - y) * g y) p μ =
          ENNReal.ofReal ‖g y‖ * eLpNorm (fun x => f (x - y)) p μ := by
    intro y
    have h_smul :
        (fun x => f (x - y) * g y) = fun x => (g y) • f (x - y) := by
      funext x
      simp [mul_comm, smul_eq_mul, sub_eq_add_neg]
    simpa [h_smul] using
      eLpNorm_const_smul (μ := μ) (p := p) (c := g y) (f := fun x => f (x - y))
  have h_pointwise :
      (fun y => (eLpNorm (fun x => f (x - y) * g y) p μ).toReal) =ᵐ[μ]
        fun y => ‖g y‖ * (eLpNorm (fun x => f (x - y)) p μ).toReal := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have h_eq := h_scaling y
    have h_toReal := congrArg ENNReal.toReal h_eq
    have h_nonneg : 0 ≤ ‖g y‖ := norm_nonneg _
    simpa [ENNReal.toReal_ofReal_mul, h_nonneg]
      using h_toReal
  have h_norm_toReal :
      Integrable (fun y => (eLpNorm (fun x => f (x - y) * g y) p μ).toReal) μ :=
    h_norm.congr <| by
      simpa using h_pointwise.symm
  have h_minkowski :=
    minkowski_integral_inequality (μ := μ) (ν := μ) (p := p)
      hp hp_ne_top (fun x y => f (x - y) * g y)
      h_meas h_prod h_int h_memLp h_norm_toReal
  have h_integral_eq :
      (∫ y, (eLpNorm (fun x => f (x - y) * g y) p μ).toReal ∂μ)
        = ∫ y, ‖g y‖ * (eLpNorm (fun x => f (x - y)) p μ).toReal ∂μ :=
    integral_congr_ae h_pointwise
  simpa [h_integral_eq]
    using h_minkowski

lemma convolution_memLp_of_memLp_finiteMeasure
    [IsFiniteMeasure μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (f g : G → ℂ) (q r : ℝ≥0∞) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hr_ne_top : r ≠ ∞) (hf_r : MemLp f r μ) (hg : MemLp g q μ) :
    MemLp (fun x => ∫ y, f (x - y) * g y ∂μ) r μ := by
  classical
  have h_kernel_meas :
      AEStronglyMeasurable
        (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) :=
    convolution_kernel_aestronglyMeasurable (μ := μ)
      (f := f) (g := g) hf_r.aestronglyMeasurable hg.aestronglyMeasurable
  have h_kernel_int :
      Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) :=
    convolution_kernel_integrable_of_memLp
      (μ := μ) (p := r) (q := q) hr hq hf_r hg
  have h_fiber_int :
      ∀ᵐ y ∂μ, Integrable (fun x => f (x - y) * g y) μ :=
    convolution_kernel_fiber_integrable_of_memLp
      (μ := μ) (p := r) (q := q) hr hq hf_r hg
  have h_fiber_int' :
      ∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ := by
    have h := Integrable.prod_right_ae (μ := μ) (ν := μ) h_kernel_int
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have h_fiber_mem :
      ∀ᵐ y ∂μ, MemLp (fun x => f (x - y) * g y) r μ :=
    convolution_kernel_fiber_memLp_of_memLp (μ := μ)
      (p := r) (q := q) hf_r hg
  have h_norm_aux :=
    integrable_abs_mul_eLpNorm_of_memLp (μ := μ)
      (f := f) (g := g) (p := r) (q := q) hq hf_r hg
  have h_norm :
      Integrable (fun y => ‖g y‖ * (eLpNorm (fun x => f (x - y)) r μ).toReal) μ := by
    refine h_norm_aux.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    have h_translate :
        eLpNorm (fun x => f (x - y)) r μ =
          eLpNorm (fun x => f (x + -y)) r μ := by
      simp [sub_eq_add_neg]
    simp [h_translate, sub_eq_add_neg]
  let convAdd : G → ℂ := fun x => ∫ y, f (x + -y) * g y ∂μ
  have h_conv_meas' : AEStronglyMeasurable convAdd μ := by
    have :=
      aestronglyMeasurable_convolution (μ := μ)
        (f := f) (g := g) h_kernel_int h_fiber_int'
    simpa [convAdd, sub_eq_add_neg] using this
  have h_minkowski := by
    have :=
      minkowski_inequality_convolution_complex (μ := μ)
        (f := f) (g := g) (p := r)
        hr hr_ne_top h_kernel_meas h_kernel_int h_fiber_int h_fiber_mem h_norm
    simpa [convAdd, sub_eq_add_neg] using this
  have h_conv_lt_top' : eLpNorm convAdd r μ < ∞ := by
    refine lt_of_le_of_lt h_minkowski ?_
    simp
  have h_conv_meas : AEStronglyMeasurable (fun x => ∫ y, f (x - y) * g y ∂μ) μ := by
    simpa [sub_eq_add_neg] using
      aestronglyMeasurable_convolution (μ := μ)
        (f := f) (g := g) h_kernel_int h_fiber_int'
  have h_conv_lt_top :
      eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) r μ < ∞ := by
    simpa [convAdd, sub_eq_add_neg] using h_conv_lt_top'
  exact ⟨h_conv_meas, h_conv_lt_top⟩

lemma sfiniteSeq_partial_le_smul
    (μ : Measure G) [SFinite μ] :
    ∀ N,
      (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k)
        ≤ ((N + 1 : ℝ≥0∞) • μ) := by
  classical
  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
  let μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k
  have hμpartial :
      ∀ N, μpartial N ≤ ((N + 1 : ℝ≥0∞) • μ) := by
    intro N s hs
    classical
    intro hμ
    have hle :=
      Finset.sum_le_card_nsmul (Finset.range (N + 1)) (fun k => μn k s) (μ s)
        (by
          intro k hk
          have hineq : μn k ≤ μ := by
            simpa [μn] using (MeasureTheory.sfiniteSeq_le (μ := μ) k)
          exact (hineq s).trans (by simp))
    have hbound :
        ∑ k ∈ Finset.range (N + 1), (μn k) s ≤ (↑N + 1) * μ s := by
      simpa [Finset.card_range, Nat.succ_eq_add_one, nsmul_eq_mul, mul_comm] using hle
    have hμpartial_le_mul : μpartial N s ≤ (↑N + 1) * μ s := by
      simpa [μpartial] using hbound
    have hμ_eq : (↑N + 1 : ℝ≥0∞) * μ s = (↑hs : ℝ≥0∞) := hμ
    have hμpartial_le_hs : μpartial N s ≤ (↑hs : ℝ≥0∞) := by
      simpa [hμ_eq] using hμpartial_le_mul
    have hμpartial_lt_top : μpartial N s < ∞ :=
      lt_of_le_of_lt hμpartial_le_hs (by simp)
    have hμpartial_ne_top : μpartial N s ≠ ∞ := ne_of_lt hμpartial_lt_top
    have hhs_ne_top : (↑hs : ℝ≥0∞) ≠ ∞ := by simp
    refine ⟨(μpartial N s).toNNReal, ?_, ?_⟩
    · simp [hμpartial_ne_top]
    · have := (ENNReal.toNNReal_le_toNNReal hμpartial_ne_top hhs_ne_top).2
        hμpartial_le_hs
      simpa using this
  intro N
  simpa [μpartial] using hμpartial N

lemma sfiniteSeq_partial_tendsto
    (μ : Measure G) [SFinite μ] :
    ∀ ⦃s : Set G⦄, MeasurableSet s →
      Tendsto
        (fun N =>
          (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k) s)
        atTop
        (𝓝 (μ s)) := by
  classical
  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
  have hμ_sum : Measure.sum μn = μ := MeasureTheory.sum_sfiniteSeq μ
  let μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k
  intro s hs
  have h_sum_eval := congrArg (fun ν : Measure G => ν s) hμ_sum
  have hμ_tsum : ∑' n, μn n s = μ s := by
    simpa [Measure.sum_apply _ hs, μn] using h_sum_eval
  have h_seq :
      Tendsto (fun N => μpartial N s) atTop (𝓝 (∑' n, μn n s)) := by
    simpa [μpartial, Measure.finset_sum_apply, Nat.succ_eq_add_one]
      using
        (ENNReal.tendsto_nat_tsum (fun n => μn n s)).comp (tendsto_add_atTop_nat 1)
  simpa [μpartial, hμ_tsum]
    using h_seq

lemma sfiniteSeq_partial_prod_le_smul
    (μ : Measure G) [SFinite μ] :
    ∀ N,
      (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k).prod
          (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k)
        ≤ (((N + 1 : ℝ≥0∞) * (N + 1 : ℝ≥0∞)) • (μ.prod μ)) := by
  classical
  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
  let μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k
  have hμpartial_le_smul := sfiniteSeq_partial_le_smul (μ := μ)
  intro N
  classical
  set c : ℝ≥0∞ := (N + 1 : ℝ≥0∞)
  have hμ_le : μpartial N ≤ c • μ := by
    simpa [μpartial, μn, c] using hμpartial_le_smul N
  refine fun s => ?_
  classical
  set S := toMeasurable (μ.prod μ) s with hS_def
  have hS_meas : MeasurableSet S := measurableSet_toMeasurable _ _
  have hs_subset : s ⊆ S := by
    simpa [S] using subset_toMeasurable (μ.prod μ) s
  have h_goal :
      (μpartial N).prod (μpartial N) S ≤ ((c * c) • (μ.prod μ)) S := by
    have h_prod_apply_partial :
        (μpartial N).prod (μpartial N) S =
          ∫⁻ x, μpartial N (Prod.mk x ⁻¹' S) ∂ μpartial N :=
      Measure.prod_apply (μ := μpartial N) (ν := μpartial N) hS_meas
    have h_prod_apply :
        (μ.prod μ) S = ∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μ :=
      Measure.prod_apply (μ := μ) (ν := μ) hS_meas
    have h_pointwise :
        (fun x => μpartial N (Prod.mk x ⁻¹' S)) ≤
          fun x => c * μ (Prod.mk x ⁻¹' S) := by
      intro x
      have := hμ_le (Prod.mk x ⁻¹' S)
      simpa [c, Measure.smul_apply] using this
    have h_step1 :
        (∫⁻ x, μpartial N (Prod.mk x ⁻¹' S) ∂ μpartial N)
          ≤ ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ μpartial N :=
      lintegral_mono h_pointwise
    have h_step2 :
        ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ μpartial N ≤
          ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ (c • μ) :=
      lintegral_mono' hμ_le fun _ => le_rfl
    have h_step4 :
        ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ μ =
          c * ∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μ :=
      lintegral_const_mul c (measurable_measure_prodMk_left hS_meas)
    calc
      (μpartial N).prod (μpartial N) S
          = ∫⁻ x, μpartial N (Prod.mk x ⁻¹' S) ∂ μpartial N :=
        h_prod_apply_partial
      _ ≤ ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ μpartial N := h_step1
      _ ≤ ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ (c • μ) := h_step2
      _ = c * ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ μ := by
        simp [lintegral_smul_measure, mul_comm, mul_left_comm, mul_assoc]
      _ = c * (c * ∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μ) := by
        simp [h_step4, mul_comm, mul_left_comm, mul_assoc]
      _ = (c * c) * (μ.prod μ) S := by
        simp [h_prod_apply, mul_comm, mul_left_comm, mul_assoc]
      _ = ((c * c) • (μ.prod μ)) S := by
        simp [Measure.smul_apply, mul_comm, mul_left_comm, mul_assoc]
  have h_total :
      (μpartial N).prod (μpartial N) s ≤ ((c * c) • (μ.prod μ)) S :=
    (measure_mono (μ := (μpartial N).prod (μpartial N)) hs_subset).trans h_goal
  simpa [μpartial, μn, c, S, Measure.smul_apply, measure_toMeasurable,
    mul_comm, mul_left_comm, mul_assoc]
    using h_total

lemma sfiniteSeq_partial_translate_norm_bound
    (μ : Measure G) [SFinite μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {r : ℝ≥0∞}
    (f : G → ℂ)
    (μpartial : ℕ → Measure G)
    (hf : MemLp f r μ)
    (h_le : ∀ N, μpartial N ≤ ((N + 1 : ℝ≥0∞) • μ)) :
    ∀ N y,
      eLpNorm (fun x => f (x - y)) r (μpartial N)
        ≤ ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ := by
  classical
  intro N y
  have h_le' :=
    eLpNorm_mono_measure
      (f := fun x => f (x - y))
      (μ := ((N + 1 : ℝ≥0∞) • μ))
      (ν := μpartial N)
      (p := r)
      (h_le N)
  have h_smul :=
    eLpNorm_smul_measure_of_ne_zero
      (μ := μ)
      (p := r)
      (f := fun x => f (x - y))
      (c := (N + 1 : ℝ≥0∞))
      (by
        have h_pos : (0 : ℝ≥0∞) < (N + 1 : ℝ≥0∞) := by
          exact_mod_cast (Nat.succ_pos N)
        exact ne_of_gt h_pos)
  have h_translate :=
    eLpNorm_comp_add_right
      (μ := μ) (f := f) (p := r) (y := -y) hf.aestronglyMeasurable
  have h_step := h_le'.trans (le_of_eq h_smul)
  simpa [smul_eq_mul, sub_eq_add_neg,
    h_translate, mul_comm, mul_left_comm, mul_assoc]
    using h_step

lemma sfiniteSeq_partial_integrable_norm_mul
    (μ : Measure G) [SFinite μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {r : ℝ≥0∞}
    (hr : 1 ≤ r) (hr_ne_top : r ≠ ∞)
    (f g : G → ℂ)
    (μpartial : ℕ → Measure G)
    (hf : MemLp f r μ)
    (hg_partial_int : ∀ N, Integrable g (μpartial N))
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (hμpartial_prod_ac : ∀ N, (μpartial N).prod (μpartial N) ≪ μ.prod μ)
    (h_translate_norm_bound_toReal :
      ∀ N y,
        (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ≤
          ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal) :
    ∀ N,
      Integrable
        (fun y => ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal)
        (μpartial N) := by
  classical
  intro N
  set C :=
      ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal with hC_def
  have h_C_nonneg : 0 ≤ C := by
    have h_nonneg :
        0 ≤ (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ).toReal :=
      ENNReal.toReal_nonneg
    simpa [hC_def] using h_nonneg
  have h_bound :
      ∀ y,
        ‖‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal‖ ≤
          ‖g y‖ * C := by
    intro y
    have h_toReal_nonneg :
        0 ≤ (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal :=
      ENNReal.toReal_nonneg
    have h_mul_nonneg :
        0 ≤ ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal :=
      mul_nonneg (norm_nonneg _) h_toReal_nonneg
    have h_upper := h_translate_norm_bound_toReal N y
    have h_mul_upper :
        ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ≤
          ‖g y‖ * C :=
      mul_le_mul_of_nonneg_left h_upper (norm_nonneg _)
    have h_abs_eq :
        ‖‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal‖ =
          ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
      simp [abs_of_nonneg h_mul_nonneg]
    have h_rhs_nonneg : 0 ≤ ‖g y‖ * C :=
      mul_nonneg (norm_nonneg _) h_C_nonneg
    simpa [h_abs_eq, abs_of_nonneg h_rhs_nonneg] using h_mul_upper
  have h_bound_integrable :
      Integrable (fun y => ‖g y‖ * C) (μpartial N) := by
    simpa [hC_def, mul_comm, mul_left_comm, mul_assoc]
      using ((hg_partial_int N).norm.mul_const C)
  refine (h_bound_integrable.mono' ?_ ?_)
  · classical
    have hf_meas : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
    set f₀ := hf_meas.mk f with hf₀_def
    have hf₀_meas : StronglyMeasurable f₀ := hf_meas.stronglyMeasurable_mk
    have hf₀_ae_eq : f =ᵐ[μ] f₀ := hf_meas.ae_eq_mk
    have hf₀_ae_eq_prod :
        (fun q : G × G => f (q.1 - q.2))
          =ᵐ[μ.prod μ]
          fun q : G × G => f₀ (q.1 - q.2) := by
      have h_sub_qmp :
          Measure.QuasiMeasurePreserving (fun z : G × G => z.1 - z.2)
            (μ.prod μ) μ := by
        have h_measPres :
            MeasurePreserving (fun z : G × G => (z.1 - z.2, z.2))
              (μ.prod μ) (μ.prod μ) :=
          measurePreserving_sub_prod (μ := μ) (ν := μ)
        have h_fst :
            Measure.QuasiMeasurePreserving (fun z : G × G => z.1)
              (μ.prod μ) μ :=
          MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
        simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
          using h_fst.comp h_measPres.quasiMeasurePreserving
      exact h_sub_qmp.ae_eq_comp hf₀_ae_eq
    have hf₀_ae_eq_prod_partial :
        (fun q : G × G => f (q.1 - q.2))
          =ᵐ[(μpartial N).prod (μpartial N)]
          fun q : G × G => f₀ (q.1 - q.2) :=
      (hμpartial_prod_ac N) hf₀_ae_eq_prod
    have hf₀_ae_eq_prod_partial_uncurry :
        Function.uncurry (fun x y => f (x - y))
          =ᵐ[(μpartial N).prod (μpartial N)]
          Function.uncurry (fun x y => f₀ (x - y)) := by
      simpa [Function.uncurry] using hf₀_ae_eq_prod_partial
    have hf₀_ae_eq_prod_partial_uncurry_swap :
        Function.uncurry (fun y x => f (x - y))
          =ᵐ[(μpartial N).prod (μpartial N)]
          Function.uncurry (fun y x => f₀ (x - y)) := by
      have h_comp :=
        (Measure.measurePreserving_swap
            (μ := μpartial N) (ν := μpartial N)).quasiMeasurePreserving.ae_eq_comp
          hf₀_ae_eq_prod_partial_uncurry
      simpa [Function.comp, Function.uncurry, Prod.swap, sub_eq_add_neg]
        using h_comp
    have h_kernel_ae :
        ∀ᵐ y ∂ μpartial N,
          (fun x => f (x - y)) =ᵐ[μpartial N] fun x => f₀ (x - y) := by
      have h_curry :=
        Measure.ae_ae_eq_curry_of_prod
          (μ := μpartial N) (ν := μpartial N)
          hf₀_ae_eq_prod_partial_uncurry_swap
      refine h_curry.mono ?_
      intro y hy
      simpa [Function.curry, sub_eq_add_neg] using hy
    have h_eLp_ae :
        ∀ᵐ y ∂ μpartial N,
          eLpNorm (fun x => f (x - y)) r (μpartial N) =
            eLpNorm (fun x => f₀ (x - y)) r (μpartial N) :=
      h_kernel_ae.mono fun _ hy => eLpNorm_congr_ae hy
    have h_eLp_toReal_ae :
        (fun y =>
            (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal)
          =ᵐ[μpartial N]
          fun y =>
            (eLpNorm (fun x => f₀ (x - y)) r (μpartial N)).toReal :=
      h_eLp_ae.mono fun _ hy => by simp [hy]
    haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
    have h_sub_meas :
        Measurable fun z : G × G => z.1 - z.2 :=
      measurable_fst.sub measurable_snd
    have hF_sm :
        StronglyMeasurable (fun z : G × G => f₀ (z.1 - z.2)) :=
      hf₀_meas.comp_measurable h_sub_meas
    have h_integrand_aemeasurable :
        AEMeasurable
          (fun z : G × G => (‖f₀ (z.1 - z.2)‖ₑ) ^ r.toReal)
          ((μpartial N).prod (μpartial N)) := by
      simpa using (hF_sm.aemeasurable.enorm.pow_const r.toReal)
    have h_lintegral_aemeasurable :
        AEMeasurable
          (fun y =>
            ∫⁻ x, (‖f₀ (x - y)‖ₑ) ^ r.toReal ∂ μpartial N)
          (μpartial N) :=
      h_integrand_aemeasurable.lintegral_prod_left'
    have hr_pos : (0 : ℝ≥0∞) < r := lt_of_lt_of_le (by simp) hr
    have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
    have h_eLp_aemeasurable :
        AEMeasurable
          (fun y => eLpNorm (fun x => f₀ (x - y)) r (μpartial N))
          (μpartial N) := by
      have h_pow_meas : Measurable fun t : ℝ≥0∞ => t ^ (1 / r.toReal) :=
        (measurable_id.pow_const (1 / r.toReal))
      have := h_pow_meas.comp_aemeasurable h_lintegral_aemeasurable
      refine this.congr ?_
      refine Filter.Eventually.of_forall ?_
      intro y
      simp [eLpNorm_eq_lintegral_rpow_enorm (μ := μpartial N)
        (f := fun x => f₀ (x - y)) hr_ne_zero hr_ne_top]
    have h_eLp_toReal_meas :
        AEStronglyMeasurable
          (fun y =>
            (eLpNorm (fun x => f₀ (x - y)) r (μpartial N)).toReal)
          (μpartial N) :=
      (h_eLp_aemeasurable.ennreal_toReal).aestronglyMeasurable
    have hg_norm_meas :
        AEStronglyMeasurable (fun y => ‖g y‖) (μpartial N) :=
      (hg_partial_int N).aestronglyMeasurable.norm
    have h_prod_meas_aux :
        AEStronglyMeasurable
          (fun y =>
            ‖g y‖ * (eLpNorm (fun x => f₀ (x - y)) r (μpartial N)).toReal)
          (μpartial N) :=
      hg_norm_meas.mul h_eLp_toReal_meas
    rcases h_prod_meas_aux with ⟨φ, hφ_meas, hφ_ae⟩
    refine ⟨φ, hφ_meas, ?_⟩
    have h_prod_ae :
        (fun y =>
            ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal)
          =ᵐ[μpartial N]
          fun y =>
            ‖g y‖ * (eLpNorm (fun x => f₀ (x - y)) r (μpartial N)).toReal :=
      h_eLp_toReal_ae.mono fun _ hy => by simp [hy]
    exact h_prod_ae.trans hφ_ae
  · refine (Filter.Eventually.of_forall ?_)
    intro y
    simpa using h_bound y

lemma sfiniteSeq_partial_integral_norm_mul_le
    (μ : Measure G) [SFinite μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    {r : ℝ≥0∞}
    (f g : G → ℂ)
    (μpartial : ℕ → Measure G)
    (hg_partial_int : ∀ N, Integrable g (μpartial N))
    (h_norm_partial :
      ∀ N,
        Integrable
          (fun y => ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal)
          (μpartial N))
    (h_translate_norm_bound_toReal :
      ∀ N y,
        (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ≤
          ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal) :
    ∀ N,
      ∫ y, ‖g y‖ *
          (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N ≤
        ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal *
          ∫ y, ‖g y‖ ∂ μpartial N := by
  classical
  intro N
  set C :=
      ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal with hC_def
  have hC_nonneg : 0 ≤ C := by
    have h_nonneg :
        0 ≤ (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ).toReal :=
      ENNReal.toReal_nonneg
    simpa [hC_def] using h_nonneg
  have h_pointwise :
      ∀ y,
        ‖g y‖ *
            (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ≤
          ‖g y‖ * C := by
    intro y
    have h_upper := h_translate_norm_bound_toReal N y
    have h_mul_upper :=
      mul_le_mul_of_nonneg_left h_upper (norm_nonneg (g y))
    simpa [hC_def] using h_mul_upper
  have h_integrand_int := h_norm_partial N
  have h_const_int :
      Integrable (fun y => ‖g y‖ * C) (μpartial N) := by
    have := (hg_partial_int N).norm.mul_const C
    simpa [hC_def, mul_comm, mul_left_comm, mul_assoc]
      using this
  have h_le :=
    integral_mono_ae
      h_integrand_int
      h_const_int
      (Filter.Eventually.of_forall h_pointwise)
  have h_const_eval :
      ∫ y, ‖g y‖ * C ∂ μpartial N
        = C * ∫ y, ‖g y‖ ∂ μpartial N := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (integral_mul_const (μ := μpartial N) (r := C) (f := fun y => ‖g y‖))
  have h_result :
      ∫ y, ‖g y‖ *
          (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N ≤
        C * ∫ y, ‖g y‖ ∂ μpartial N := by
    simpa [h_const_eval]
      using h_le
  simpa [hC_def] using h_result

lemma convolution_partial_minkowski_bound
    (ν : Measure G) [IsFiniteMeasure ν] [NormedAddCommGroup G]
    {r : ℝ≥0∞}
    (hr : 1 ≤ r) (hr_ne_top : r ≠ ∞)
    (f g : G → ℂ)
    (h_kernel_meas :
      AEStronglyMeasurable
        (fun q : G × G => f (q.1 - q.2) * g q.2) (ν.prod ν))
    (h_kernel_int :
      Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (ν.prod ν))
    (h_fiber_int : ∀ᵐ y ∂ν, Integrable (fun x => f (x - y) * g y) ν)
    (h_fiber_mem : ∀ᵐ y ∂ν, MemLp (fun x => f (x - y) * g y) r ν)
    (h_scaling :
      ∀ y : G,
        eLpNorm (fun x => f (x - y) * g y) r ν =
          ENNReal.ofReal ‖g y‖ * eLpNorm (fun x => f (x - y)) r ν)
    (h_norm_integrable :
      Integrable (fun y => ‖g y‖ * (eLpNorm (fun x => f (x - y)) r ν).toReal) ν) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂ν) r ν ≤
      ENNReal.ofReal
        (∫ y, ‖g y‖ * (eLpNorm (fun x => f (x - y)) r ν).toReal ∂ν) := by
  classical
  have h_pointwise :
      (fun y =>
          (eLpNorm (fun x => f (x - y) * g y) r ν).toReal)
        =ᵐ[ν]
        fun y =>
          ‖g y‖ * (eLpNorm (fun x => f (x - y)) r ν).toReal := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have h_eq := h_scaling y
    have h_toReal := congrArg ENNReal.toReal h_eq
    have h_nonneg : 0 ≤ ‖g y‖ := norm_nonneg _
    simpa [ENNReal.toReal_ofReal_mul, h_nonneg] using h_toReal
  have h_norm_toReal :
      Integrable
        (fun y => (eLpNorm (fun x => f (x - y) * g y) r ν).toReal) ν := by
    refine h_norm_integrable.congr ?_
    simpa using h_pointwise.symm
  have h_minkowski :=
    minkowski_integral_inequality
      (μ := ν) (ν := ν) (p := r)
      hr hr_ne_top (fun x y => f (x - y) * g y)
      h_kernel_meas h_kernel_int h_fiber_int h_fiber_mem h_norm_toReal
  have h_integral_eq :
      (∫ y,
          (eLpNorm (fun x => f (x - y) * g y) r ν).toReal ∂ν)
        = ∫ y,
            ‖g y‖ * (eLpNorm (fun x => f (x - y)) r ν).toReal ∂ν :=
    integral_congr_ae h_pointwise
  simpa [h_integral_eq]
    using h_minkowski

lemma convPartial_minkowski_bound
    (μpartial : ℕ → Measure G) [NormedAddCommGroup G]
    (f g : G → ℂ)
    (r : ℝ≥0∞)
    (convPartial : ℕ → G → ℂ)
    (h_convPartial :
      ∀ N, convPartial N = fun x => ∫ y, f (x - y) * g y ∂ μpartial N)
    (hr : 1 ≤ r) (hr_ne_top : r ≠ ∞)
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (h_kernel_meas_partial :
      ∀ N,
        AEStronglyMeasurable
          (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)))
    (h_kernel_int_partial :
      ∀ N,
        Integrable (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)))
    (h_kernel_fiber_int_partial :
      ∀ N,
        ∀ᵐ y ∂ μpartial N, Integrable (fun x => f (x - y) * g y) (μpartial N))
    (h_kernel_fiber_mem_partial :
      ∀ N,
        ∀ᵐ y ∂ μpartial N,
          MemLp (fun x => f (x - y) * g y) r (μpartial N))
    (h_norm_partial :
      ∀ N,
        Integrable (fun y =>
            ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal)
          (μpartial N)) :
    ∀ N,
      eLpNorm (convPartial N) r (μpartial N) ≤
        ENNReal.ofReal
          (∫ y,
              ‖g y‖ *
                (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N) := by
  classical
  intro N
  haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
  have h_scaling :
      ∀ y : G,
        eLpNorm (fun x => f (x - y) * g y) r (μpartial N) =
          ENNReal.ofReal ‖g y‖ *
            eLpNorm (fun x => f (x - y)) r (μpartial N) := by
    intro y
    have h_smul :
        (fun x : G => f (x - y) * g y) =
          fun x : G => (g y) • f (x - y) := by
      funext x
      simp [mul_comm, smul_eq_mul, sub_eq_add_neg]
    simpa [h_smul] using
      eLpNorm_const_smul (μ := μpartial N) (p := r)
        (c := g y) (f := fun x => f (x - y))
  have h_bound :=
    convolution_partial_minkowski_bound
      (ν := μpartial N) (r := r)
      (hr := hr) (hr_ne_top := hr_ne_top)
      (f := f) (g := g)
      (h_kernel_meas := h_kernel_meas_partial N)
      (h_kernel_int := h_kernel_int_partial N)
      (h_fiber_int := h_kernel_fiber_int_partial N)
      (h_fiber_mem := h_kernel_fiber_mem_partial N)
      (h_scaling := h_scaling)
      (h_norm_integrable := h_norm_partial N)
  simpa [h_convPartial N]
    using h_bound

lemma convPartial_bound
    [NormedAddCommGroup G] (μ : Measure G) (μpartial : ℕ → Measure G)
    (f g : G → ℂ) (r : ℝ≥0∞)
    (convPartial : ℕ → G → ℂ)
    (h_minkowski_partial :
      ∀ N,
        eLpNorm (convPartial N) r (μpartial N) ≤
          ENNReal.ofReal
            (∫ y,
                ‖g y‖ *
                  (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal
                ∂ μpartial N))
    (h_norm_partial_le :
      ∀ N,
        ∫ y,
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal
              ∂ μpartial N ≤
          ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal *
            ∫ y, ‖g y‖ ∂ μpartial N) :
    ∀ N,
      eLpNorm (convPartial N) r (μpartial N) ≤
        ENNReal.ofReal
          ((((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal) *
            ∫ y, ‖g y‖ ∂ μpartial N) := by
  classical
  intro N
  have h_mink := h_minkowski_partial N
  have h_le := h_norm_partial_le N
  set C :=
      ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal
    with hC_def
  have h_ofReal_le :
      ENNReal.ofReal
          (∫ y,
              ‖g y‖ *
                (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal
              ∂ μpartial N)
        ≤ ENNReal.ofReal (C * ∫ y, ‖g y‖ ∂ μpartial N) := by
    refine ENNReal.ofReal_le_ofReal ?_
    simpa [hC_def, mul_comm, mul_left_comm, mul_assoc] using h_le
  exact h_mink.trans <| by
    simpa [hC_def, mul_comm, mul_left_comm, mul_assoc]
      using h_ofReal_le

lemma convPartial_succ_eq
    [NormedAddCommGroup G] (μ : Measure G) (μpartial μn : ℕ → Measure G)
    (f g : G → ℂ)
    (convPartial convPiece : ℕ → G → ℂ)
    (h_convPartial :
      ∀ N, convPartial N = fun x => ∫ y, f (x - y) * g y ∂ μpartial N)
    (h_convPiece :
      ∀ N, convPiece N = fun x => ∫ y, f (x - y) * g y ∂ μn N)
    (hμpartial_succ : ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1))
    (h_kernel_fiber_int_partial_measure :
      ∀ N, ∀ᵐ x ∂ μ, Integrable (fun y => f (x - y) * g y) (μpartial N))
    (h_kernel_fiber_int_piece :
      ∀ N, ∀ᵐ x ∂ μ, Integrable (fun y => f (x - y) * g y) (μn N)) :
    ∀ N,
      convPartial (N + 1)
        =ᵐ[μ]
          fun x => convPartial N x + convPiece (N + 1) x := by
  classical
  intro N
  have h_int_succ := h_kernel_fiber_int_partial_measure (N + 1)
  have h_int_prev := h_kernel_fiber_int_partial_measure N
  have h_int_piece := h_kernel_fiber_int_piece (N + 1)
  refine (h_int_succ.and (h_int_prev.and h_int_piece)).mono ?_
  intro x hx
  rcases hx with ⟨hx_succ, hx_rest⟩
  rcases hx_rest with ⟨hx_prev, hx_piece⟩
  have h_measure := hμpartial_succ N
  have h_integral_add :
      ∫ y, f (x - y) * g y ∂ μpartial (N + 1)
        = ∫ y, f (x - y) * g y ∂ μpartial N
            + ∫ y, f (x - y) * g y ∂ μn (N + 1) := by
    simpa [h_measure, Nat.succ_eq_add_one]
      using MeasureTheory.integral_add_measure hx_prev hx_piece
  simp [h_convPartial (N + 1), h_convPartial N, h_convPiece (N + 1),
    h_integral_add, Nat.succ_eq_add_one]

lemma convPartial_sum_eq
    [NormedAddCommGroup G] (μ : Measure G) (μpartial μn : ℕ → Measure G)
    (f g : G → ℂ)
    (convPartial convPiece : ℕ → G → ℂ)
    (h_convPartial :
      ∀ N, convPartial N = fun x => ∫ y, f (x - y) * g y ∂ μpartial N)
    (h_convPiece :
      ∀ N, convPiece N = fun x => ∫ y, f (x - y) * g y ∂ μn N)
    (hμpartial_zero : μpartial 0 = μn 0)
    (hμpartial_succ : ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1))
    (h_kernel_fiber_int_partial_measure :
      ∀ N, ∀ᵐ x ∂ μ, Integrable (fun y => f (x - y) * g y) (μpartial N))
    (h_kernel_fiber_int_piece :
      ∀ N, ∀ᵐ x ∂ μ, Integrable (fun y => f (x - y) * g y) (μn N)) :
    ∀ N,
      convPartial N
        =ᵐ[μ]
          fun x => ∑ k ∈ Finset.range (N + 1), convPiece k x := by
  classical
  intro N
  induction' N with N hN
  · refine Filter.Eventually.of_forall ?_
    intro x
    simp [h_convPartial, h_convPiece, hμpartial_zero]
  · have h_succ :=
      convPartial_succ_eq
        (μ := μ)
        (μpartial := μpartial)
        (μn := μn)
        (f := f)
        (g := g)
        (convPartial := convPartial)
        (convPiece := convPiece)
        (h_convPartial := h_convPartial)
        (h_convPiece := h_convPiece)
        (hμpartial_succ := hμpartial_succ)
        (h_kernel_fiber_int_partial_measure :=
          h_kernel_fiber_int_partial_measure)
        (h_kernel_fiber_int_piece := h_kernel_fiber_int_piece)
        N
    refine h_succ.trans ?_
    refine hN.mono ?_
    intro x hx
    have hx' :
        convPartial N x + convPiece (N + 1) x =
          (∑ k ∈ Finset.range (N + 1), convPiece k x) + convPiece (N + 1) x := by
      simp [hx]
    have hx'' :
        (∑ k ∈ Finset.range (N + 1), convPiece k x) + convPiece (N + 1) x =
          ∑ k ∈ Finset.range (N + 1 + 1), convPiece k x := by
      simp [Finset.sum_range_succ, Nat.succ_eq_add_one, add_comm,
        add_left_comm, add_assoc]
    exact hx'.trans hx''

lemma sfiniteSeq_prod_le
    (μ : Measure G) [SFinite μ] :
    ∀ n, (MeasureTheory.sfiniteSeq μ n).prod (MeasureTheory.sfiniteSeq μ n) ≤ μ.prod μ := by
  classical
  set μn := MeasureTheory.sfiniteSeq μ
  have hμn_le : ∀ n, μn n ≤ μ := fun n =>
    by simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n
  intro n
  refine fun s => ?_
  classical
  set S := toMeasurable (μ.prod μ) s with hS_def
  have hS_meas : MeasurableSet S := measurableSet_toMeasurable _ _
  have hs_subset : s ⊆ S := by
    simpa [S] using subset_toMeasurable (μ.prod μ) s
  have h_prod_apply_piece :
      (μn n).prod (μn n) S =
        ∫⁻ x, μn n (Prod.mk x ⁻¹' S) ∂ μn n :=
    Measure.prod_apply (μ := μn n) (ν := μn n) hS_meas
  have h_prod_apply :
      (μ.prod μ) S = ∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μ :=
    Measure.prod_apply (μ := μ) (ν := μ) hS_meas
  have h_pointwise :
      (fun x => μn n (Prod.mk x ⁻¹' S)) ≤
        fun x => μ (Prod.mk x ⁻¹' S) := by
    intro x
    exact hμn_le n (Prod.mk x ⁻¹' S)
  have h_step1 :
      (∫⁻ x, μn n (Prod.mk x ⁻¹' S) ∂ μn n)
        ≤ ∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μn n :=
    lintegral_mono h_pointwise
  have h_step2 :
      (∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μn n)
        ≤ ∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μ :=
    lintegral_mono' (hμn_le n) fun _ => le_rfl
  have h_goal :
      (μn n).prod (μn n) S ≤ (μ.prod μ) S := by
    have h_chain := h_step1.trans h_step2
    simpa [h_prod_apply_piece, h_prod_apply] using h_chain
  have h_total :
      (μn n).prod (μn n) s ≤ (μ.prod μ) S :=
    (measure_mono (μ := (μn n).prod (μn n)) hs_subset).trans h_goal
  simpa [μn, S, measure_toMeasurable] using h_total

lemma sfiniteSeq_piece_integrable_norm_mul
    (μ : Measure G) [SFinite μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {r : ℝ≥0∞}
    (hr : 1 ≤ r) (hr_ne_top : r ≠ ∞)
    (f g : G → ℂ)
    (μn : ℕ → Measure G)
    (hf_r : MemLp f r μ)
    (hg_piece_int : ∀ n, Integrable g (μn n))
    (hμn_fin : ∀ n, IsFiniteMeasure (μn n))
    (hμn_prod_ac : ∀ n, (μn n).prod (μn n) ≪ μ.prod μ)
    (h_translate_norm_bound_toReal_piece :
      ∀ n y,
        (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ≤
          (eLpNorm f r μ).toReal) :
    ∀ n,
      Integrable
        (fun y => ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μn n)).toReal)
        (μn n) := by
  classical
  intro n
  haveI := hμn_fin n
  set C := (eLpNorm f r μ).toReal with hC_def
  have hC_nonneg : 0 ≤ C := by
    have h_nonneg : 0 ≤ (eLpNorm f r μ).toReal := ENNReal.toReal_nonneg
    simp [hC_def]
  have h_bound :
      ∀ y,
        ‖‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μn n)).toReal‖ ≤
          ‖g y‖ * C := by
    intro y
    have h_toReal_nonneg :
        0 ≤ (eLpNorm (fun x => f (x - y)) r (μn n)).toReal :=
      ENNReal.toReal_nonneg
    have h_mul_nonneg :
        0 ≤ ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μn n)).toReal :=
      mul_nonneg (norm_nonneg _) h_toReal_nonneg
    have h_upper := h_translate_norm_bound_toReal_piece n y
    have h_mul_upper := mul_le_mul_of_nonneg_left h_upper (norm_nonneg (g y))
    have h_abs_eq :
        ‖‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μn n)).toReal‖ =
          ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μn n)).toReal := by
      simp [abs_of_nonneg h_mul_nonneg]
    have h_rhs_nonneg : 0 ≤ ‖g y‖ * C :=
      mul_nonneg (norm_nonneg _) hC_nonneg
    simpa [h_abs_eq, abs_of_nonneg h_rhs_nonneg, hC_def]
      using h_mul_upper
  have h_bound_integrable :
      Integrable (fun y => ‖g y‖ * C) (μn n) := by
    have := (hg_piece_int n).norm.mul_const C
    simpa [hC_def, mul_comm, mul_left_comm, mul_assoc] using this
  have hf_meas : AEStronglyMeasurable f μ := hf_r.aestronglyMeasurable
  set f₀ := hf_meas.mk f with hf₀_def
  have hf₀_meas : StronglyMeasurable f₀ := hf_meas.stronglyMeasurable_mk
  have hf₀_ae_eq : f =ᵐ[μ] f₀ := hf_meas.ae_eq_mk
  have hf₀_ae_eq_prod :
      (fun q : G × G => f (q.1 - q.2))
        =ᵐ[μ.prod μ]
        fun q : G × G => f₀ (q.1 - q.2) := by
    have h_sub_qmp :
        Measure.QuasiMeasurePreserving (fun z : G × G => z.1 - z.2)
          (μ.prod μ) μ := by
      have h_measPres :
          MeasurePreserving (fun z : G × G => (z.1 - z.2, z.2))
            (μ.prod μ) (μ.prod μ) :=
        measurePreserving_sub_prod (μ := μ) (ν := μ)
      have h_fst :
          Measure.QuasiMeasurePreserving (fun z : G × G => z.1)
            (μ.prod μ) μ :=
        MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
      simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
        using h_fst.comp h_measPres.quasiMeasurePreserving
    exact h_sub_qmp.ae_eq_comp hf₀_ae_eq
  have hf₀_ae_eq_prod_piece :
      (fun q : G × G => f (q.1 - q.2))
        =ᵐ[(μn n).prod (μn n)]
        fun q : G × G => f₀ (q.1 - q.2) :=
    (hμn_prod_ac n) hf₀_ae_eq_prod
  have hf₀_ae_eq_prod_piece_uncurry :
      Function.uncurry (fun x y => f (x - y))
        =ᵐ[(μn n).prod (μn n)]
        Function.uncurry (fun x y => f₀ (x - y)) := by
    simpa [Function.uncurry] using hf₀_ae_eq_prod_piece
  have hf₀_ae_eq_prod_piece_uncurry_swap :
      Function.uncurry (fun y x => f (x - y))
        =ᵐ[(μn n).prod (μn n)]
        Function.uncurry (fun y x => f₀ (x - y)) := by
    have h_comp :=
      (Measure.measurePreserving_swap
          (μ := μn n) (ν := μn n)).quasiMeasurePreserving.ae_eq_comp
        hf₀_ae_eq_prod_piece_uncurry
    simpa [Function.comp, Function.uncurry, Prod.swap, sub_eq_add_neg]
      using h_comp
  have h_kernel_ae_piece :
      ∀ᵐ y ∂ μn n,
        (fun x => f (x - y)) =ᵐ[μn n] fun x => f₀ (x - y) := by
    have h_curry :=
      Measure.ae_ae_eq_curry_of_prod
        (μ := μn n) (ν := μn n)
        hf₀_ae_eq_prod_piece_uncurry_swap
    refine h_curry.mono ?_
    intro y hy
    simpa [Function.curry, sub_eq_add_neg] using hy
  have h_eLp_ae_piece :
      ∀ᵐ y ∂ μn n,
        eLpNorm (fun x => f (x - y)) r (μn n) =
          eLpNorm (fun x => f₀ (x - y)) r (μn n) :=
    h_kernel_ae_piece.mono fun _ hy => eLpNorm_congr_ae hy
  have h_eLp_toReal_ae_piece :
      (fun y =>
          (eLpNorm (fun x => f (x - y)) r (μn n)).toReal)
        =ᵐ[μn n]
        fun y =>
          (eLpNorm (fun x => f₀ (x - y)) r (μn n)).toReal :=
    h_eLp_ae_piece.mono fun _ hy => by simp [hy]
  have h_sub_meas :
      Measurable fun z : G × G => z.1 - z.2 :=
    measurable_fst.sub measurable_snd
  have hF_sm :
      StronglyMeasurable (fun z : G × G => f₀ (z.1 - z.2)) :=
    hf₀_meas.comp_measurable h_sub_meas
  have h_integrand_aemeasurable_piece :
      AEMeasurable
        (fun z : G × G => (‖f₀ (z.1 - z.2)‖ₑ) ^ r.toReal)
        ((μn n).prod (μn n)) := by
    simpa using (hF_sm.aemeasurable.enorm.pow_const r.toReal)
  have h_lintegral_aemeasurable_piece :
      AEMeasurable
        (fun y =>
          ∫⁻ x, (‖f₀ (x - y)‖ₑ) ^ r.toReal ∂ μn n)
        (μn n) :=
    h_integrand_aemeasurable_piece.lintegral_prod_left'
  have hr_pos : (0 : ℝ≥0∞) < r := lt_of_lt_of_le (by simp) hr
  have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
  have h_eLp_aemeasurable_piece :
      AEMeasurable
        (fun y => eLpNorm (fun x => f₀ (x - y)) r (μn n))
        (μn n) := by
    have h_pow_meas : Measurable fun t : ℝ≥0∞ => t ^ (1 / r.toReal) :=
      (measurable_id.pow_const (1 / r.toReal))
    have := h_pow_meas.comp_aemeasurable h_lintegral_aemeasurable_piece
    refine this.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    simp [eLpNorm_eq_lintegral_rpow_enorm (μ := μn n)
      (f := fun x => f₀ (x - y)) hr_ne_zero hr_ne_top]
  have h_eLp_toReal_meas_piece :
      AEStronglyMeasurable
        (fun y =>
          (eLpNorm (fun x => f₀ (x - y)) r (μn n)).toReal)
        (μn n) :=
    (h_eLp_aemeasurable_piece.ennreal_toReal).aestronglyMeasurable
  have hg_norm_meas_piece :
      AEStronglyMeasurable (fun y => ‖g y‖) (μn n) :=
    (hg_piece_int n).aestronglyMeasurable.norm
  have h_prod_meas_piece :
      AEStronglyMeasurable
        (fun y =>
          ‖g y‖ *
            (eLpNorm (fun x => f₀ (x - y)) r (μn n)).toReal)
        (μn n) :=
    hg_norm_meas_piece.mul h_eLp_toReal_meas_piece
  rcases h_prod_meas_piece with ⟨φ, hφ_meas, hφ_ae⟩
  refine (h_bound_integrable.mono' ?_ ?_)
  · refine ⟨φ, hφ_meas, ?_⟩
    have h_prod_ae_piece :
        (fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μn n)).toReal)
          =ᵐ[μn n]
          fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f₀ (x - y)) r (μn n)).toReal :=
      h_eLp_toReal_ae_piece.mono fun _ hy => by simp [hy]
    exact h_prod_ae_piece.trans hφ_ae
  · exact Filter.Eventually.of_forall h_bound

lemma sfiniteSeq_piece_minkowski_bound
    (μ : Measure G) [SFinite μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    {r : ℝ≥0∞}
    (hr : 1 ≤ r) (hr_ne_top : r ≠ ∞)
    (f g : G → ℂ)
    (μn : ℕ → Measure G)
    (convPiece : ℕ → G → ℂ)
    (hμn_fin : ∀ n, IsFiniteMeasure (μn n))
    (h_kernel_meas_piece :
      ∀ n,
        AEStronglyMeasurable
          (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μn n).prod (μn n)))
    (h_kernel_int_piece :
      ∀ n,
        Integrable (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μn n).prod (μn n)))
    (h_kernel_fiber_int_piece_left :
      ∀ n, ∀ᵐ y ∂ μn n,
          Integrable (fun x => f (x - y) * g y) (μn n))
    (h_kernel_fiber_mem_piece :
      ∀ n, ∀ᵐ y ∂ μn n,
          MemLp (fun x => f (x - y) * g y) r (μn n))
    (h_norm_piece :
      ∀ n,
        Integrable
          (fun y =>
              (eLpNorm (fun x => f (x - y) * g y) r (μn n)).toReal)
          (μn n))
    (h_pointwise :
      ∀ n,
        (fun y =>
            (eLpNorm (fun x => f (x - y) * g y) r (μn n)).toReal)
          =ᵐ[μn n]
          fun y =>
            ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μn n)).toReal)
    (h_convPiece_def :
      ∀ n,
        convPiece n = fun x => ∫ y, f (x - y) * g y ∂ μn n) :
    ∀ n,
      eLpNorm (convPiece n) r (μn n) ≤
        ENNReal.ofReal
          (∫ y, ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ∂ μn n) := by
  classical
  intro n
  haveI := hμn_fin n
  have h_scaling :
      ∀ y : G,
        eLpNorm (fun x => f (x - y) * g y) r (μn n) =
          ENNReal.ofReal ‖g y‖ *
            eLpNorm (fun x => f (x - y)) r (μn n) := by
    intro y
    have h_smul :
        (fun x : G => f (x - y) * g y) =
          fun x : G => (g y) • f (x - y) := by
      funext x
      simp [mul_comm, smul_eq_mul, sub_eq_add_neg]
    simpa [h_smul] using
      eLpNorm_const_smul (μ := μn n) (p := r)
        (c := g y) (f := fun x => f (x - y))
  have h_pointwise' := h_pointwise n
  have h_norm_toReal_piece := h_norm_piece n
  have h_minkowski :=
    minkowski_integral_inequality
      (μ := μn n) (ν := μn n) (p := r)
      hr hr_ne_top (fun x y => f (x - y) * g y)
      (h_kernel_meas_piece n) (h_kernel_int_piece n)
      (h_kernel_fiber_int_piece_left n) (h_kernel_fiber_mem_piece n)
      h_norm_toReal_piece
  have h_integral_eq_piece :
      (∫ y,
          (eLpNorm (fun x => f (x - y) * g y) r (μn n)).toReal ∂ μn n)
        = ∫ y, ‖g y‖ *
            (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ∂ μn n :=
    integral_congr_ae h_pointwise'
  simpa [h_convPiece_def n, h_integral_eq_piece]
    using h_minkowski

lemma sfiniteSeq_partial_integral_norm
    (g : G → ℂ)
    (μpartial μn : ℕ → Measure G)
    (hμpartial_zero : μpartial 0 = μn 0)
    (hμpartial_succ : ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1))
    (hg_partial_int : ∀ N, Integrable g (μpartial N))
    (hg_piece_int : ∀ n, Integrable g (μn n)) :
    ∀ N,
      ∫ y, ‖g y‖ ∂ μpartial N
        = ∑ k ∈ Finset.range (N + 1), ∫ y, ‖g y‖ ∂ μn k := by
  classical
  intro N
  induction' N with N hN
  · simp [hμpartial_zero]
  · have h_add := hμpartial_succ N
    have h_int_partial : Integrable (fun y => ‖g y‖) (μpartial N) :=
      (hg_partial_int N).norm
    have h_int_piece : Integrable (fun y => ‖g y‖) (μn (N + 1)) :=
      (hg_piece_int (N + 1)).norm
    have h_integral_add :
        ∫ y, ‖g y‖ ∂ μpartial (N + 1)
          = ∫ y, ‖g y‖ ∂ μpartial N
              + ∫ y, ‖g y‖ ∂ μn (N + 1) := by
      simpa [h_add, Nat.succ_eq_add_one]
        using
          (MeasureTheory.integral_add_measure
            (μ := μpartial N) (ν := μn (N + 1))
            (f := fun y => ‖g y‖)
            h_int_partial h_int_piece)
    calc
      ∫ y, ‖g y‖ ∂ μpartial (N + 1)
          = ∫ y, ‖g y‖ ∂ μpartial N
              + ∫ y, ‖g y‖ ∂ μn (N + 1) := h_integral_add
      _ = (∑ k ∈ Finset.range (N + 1), ∫ y, ‖g y‖ ∂ μn k)
              + ∫ y, ‖g y‖ ∂ μn (N + 1) := by
            simpa [Nat.succ_eq_add_one] using hN
      _ = ∑ k ∈ Finset.range (N + 1 + 1), ∫ y, ‖g y‖ ∂ μn k := by
            simp [Finset.sum_range_succ, Nat.succ_eq_add_one, add_comm,
              add_left_comm, add_assoc]

lemma sfiniteSeq_partial_le_measure
    (μ : Measure G)
    (μn μpartial : ℕ → Measure G)
    (hμ_sum : Measure.sum μn = μ)
    (hμpartial_def :
      ∀ N, μpartial N = ∑ k ∈ Finset.range (N + 1), μn k) :
    ∀ N, μpartial N ≤ μ := by
  classical
  intro N s hs
  intro hμ
  have h_sum_eval := congrArg (fun ν : Measure G => ν s) hμ_sum.symm
  have hμ_tsum : μ s = ∑' n, μn n s :=
    by simpa [Measure.sum_apply_of_countable μn s] using h_sum_eval
  have h_tsum_value : ∑' n, μn n s = (↑hs : ℝ≥0∞) := by
    simpa [hμ] using hμ_tsum.symm
  have h_partial : μpartial N s = ∑ k ∈ Finset.range (N + 1), μn k s := by
    simp [hμpartial_def N]
  have h_sum_le :
      (∑ k ∈ Finset.range (N + 1), μn k s) ≤ (↑hs : ℝ≥0∞) := by
    have h_finset :=
      ENNReal.sum_le_tsum
        (s := Finset.range (N + 1))
        (f := fun k : ℕ => μn k s)
    simpa [h_tsum_value] using h_finset
  have hμpartial_le' : μpartial N s ≤ (↑hs : ℝ≥0∞) := by
    simpa [h_partial] using h_sum_le
  have hμpartial_lt_top : μpartial N s < ∞ :=
    lt_of_le_of_lt hμpartial_le' (by simp)
  have hμpartial_ne_top : μpartial N s ≠ ∞ := ne_of_lt hμpartial_lt_top
  have hhs_ne_top : (↑hs : ℝ≥0∞) ≠ ∞ := by simp
  refine ⟨(μpartial N s).toNNReal, ?_, ?_⟩
  · simp [hμpartial_ne_top]
  · have :=
      (ENNReal.toNNReal_le_toNNReal hμpartial_ne_top hhs_ne_top).2 hμpartial_le'
    simpa using this

lemma sfiniteSeq_piece_norm_le
    [NormedAddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ]
    {r : ℝ≥0∞}
    (f g : G → ℂ)
    (μn : ℕ → Measure G)
    (hg_piece_int : ∀ n, Integrable g (μn n))
    (h_norm_piece :
      ∀ n,
        Integrable
          (fun y => ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μn n)).toReal)
          (μn n))
    (h_translate_norm_bound_toReal_piece :
      ∀ n y,
        (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ≤
          (eLpNorm f r μ).toReal) :
    ∀ n,
      ∫ y, ‖g y‖ *
            (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ∂ μn n ≤
        (eLpNorm f r μ).toReal * ∫ y, ‖g y‖ ∂ μn n := by
  classical
  intro n
  set C := (eLpNorm f r μ).toReal with hC_def
  have hC_nonneg : 0 ≤ C := by
    have h_nonneg : 0 ≤ (eLpNorm f r μ).toReal := ENNReal.toReal_nonneg
    simp [hC_def]
  have h_pointwise :
      ∀ y,
        ‖g y‖ *
            (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ≤
          ‖g y‖ * C := by
    intro y
    have h_upper := h_translate_norm_bound_toReal_piece n y
    have h_nonneg : 0 ≤ ‖g y‖ := norm_nonneg _
    have h_mul_upper := mul_le_mul_of_nonneg_left h_upper h_nonneg
    simpa [hC_def, mul_comm, mul_left_comm, mul_assoc]
      using h_mul_upper
  have h_integrand_int := h_norm_piece n
  have h_const_int :
      Integrable (fun y => ‖g y‖ * C) (μn n) := by
    have := (hg_piece_int n).norm.mul_const C
    simpa [hC_def, mul_comm, mul_left_comm, mul_assoc]
      using this
  have h_le :=
    integral_mono_ae
      h_integrand_int
      h_const_int
      (Filter.Eventually.of_forall h_pointwise)
  have h_const_eval₁ :
      ∫ y, ‖g y‖ * C ∂ μn n =
        (∫ y, ‖g y‖ ∂ μn n) * C := by
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using
        (integral_mul_const (μ := μn n) (r := C)
          (f := fun y => ‖g y‖))
  have h_const_eval :
      ∫ y, ‖g y‖ * C ∂ μn n =
        C * ∫ y, ‖g y‖ ∂ μn n := by
    calc
      _ = (∫ y, ‖g y‖ ∂ μn n) * C := h_const_eval₁
      _ = C * ∫ y, ‖g y‖ ∂ μn n := by
        simp [mul_comm, mul_left_comm, mul_assoc]
  have h_le' :
      ∫ y, ‖g y‖ *
            (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ∂ μn n ≤
        C * ∫ y, ‖g y‖ ∂ μn n := by
    calc
      _ ≤ ∫ y, ‖g y‖ * C ∂ μn n := h_le
      _ = (∫ y, ‖g y‖ ∂ μn n) * C := h_const_eval₁
      _ = C * ∫ y, ‖g y‖ ∂ μn n := by
        simp [mul_comm, mul_left_comm, mul_assoc]
  simpa [hC_def, h_const_eval, mul_comm, mul_left_comm, mul_assoc]
    using h_le'

lemma sfiniteSeq_piece_conv_bound
    (μ : Measure G) [NormedAddCommGroup G] [SFinite μ]
    {r : ℝ≥0∞}
    (f g : G → ℂ)
    (μn : ℕ → Measure G)
    (convPiece : ℕ → G → ℂ)
    (h_minkowski_piece :
      ∀ n,
        eLpNorm (convPiece n) r (μn n) ≤
          ENNReal.ofReal
            (∫ y, ‖g y‖ *
                (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ∂ μn n))
    (h_norm_piece_le :
      ∀ n,
        ∫ y, ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ∂ μn n ≤
          (eLpNorm f r μ).toReal * ∫ y, ‖g y‖ ∂ μn n) :
    ∀ n,
      eLpNorm (convPiece n) r (μn n) ≤
        ENNReal.ofReal
          ((eLpNorm f r μ).toReal * ∫ y, ‖g y‖ ∂ μn n) := by
  intro n
  have h_mink := h_minkowski_piece n
  have h_le := h_norm_piece_le n
  have h_rhs_nonneg :
      0 ≤ (eLpNorm f r μ).toReal * ∫ y, ‖g y‖ ∂ μn n := by
    have h_nonneg₁ : 0 ≤ (eLpNorm f r μ).toReal := ENNReal.toReal_nonneg
    have h_nonneg₂ : 0 ≤ ∫ y, ‖g y‖ ∂ μn n := by
      have h_nonneg_fun : 0 ≤ᵐ[μn n] fun y => ‖g y‖ :=
        Filter.Eventually.of_forall fun _ => norm_nonneg _
      exact integral_nonneg_of_ae h_nonneg_fun
    exact mul_nonneg h_nonneg₁ h_nonneg₂
  have h_ofReal :
      ENNReal.ofReal
          (∫ y, ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ∂ μn n)
        ≤ ENNReal.ofReal
          ((eLpNorm f r μ).toReal * ∫ y, ‖g y‖ ∂ μn n) :=
      (ENNReal.ofReal_le_ofReal_iff h_rhs_nonneg).2 h_le
  exact h_mink.trans h_ofReal

lemma sfiniteSeq_convPartial_tendsto
    [NormedAddCommGroup G] (μ : Measure G) [SFinite μ]
    (f g : G → ℂ)
    (μn μpartial : ℕ → Measure G)
    (convPartial convPiece : ℕ → G → ℂ)
    (conv : G → ℂ)
    (hμ_sum : Measure.sum μn = μ)
    (hμpartial_zero : μpartial 0 = μn 0)
    (hμpartial_succ : ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1))
    (hμpartial_le_smul : ∀ N, μpartial N ≤ ((N + 1 : ℝ≥0∞) • μ))
    (hμn_le : ∀ n, μn n ≤ μ)
    (h_convPartial_def :
      ∀ N, convPartial N = fun x => ∫ y, f (x - y) * g y ∂ μpartial N)
    (h_convPiece_def :
      ∀ n, convPiece n = fun x => ∫ y, f (x - y) * g y ∂ μn n)
    (h_conv_def : conv = fun x => ∫ y, f (x - y) * g y ∂ μ)
    (h_kernel_fiber_int_mu :
      ∀ᵐ x ∂ μ, Integrable (fun y => f (x - y) * g y) μ) :
    ∀ᵐ x ∂ μ, Tendsto (fun N => convPartial N x) atTop (𝓝 (conv x)) := by
  classical
  refine h_kernel_fiber_int_mu.mono ?_
  intro x hx_int
  have hx_convPartial_def :
      ∀ N,
        convPartial N x = ∫ y, f (x - y) * g y ∂ μpartial N := fun N => by
    simp [h_convPartial_def N]
  have hx_convPiece_def :
      ∀ n,
        convPiece n x = ∫ y, f (x - y) * g y ∂ μn n := fun n => by
    simp [h_convPiece_def n]
  have hx_conv_def' : conv x = ∫ y, f (x - y) * g y ∂ μ := by
    simp [h_conv_def]
  let hxFun : G → ℂ := fun y => f (x - y) * g y
  have hx_int_partial : ∀ N, Integrable hxFun (μpartial N) := by
    intro N
    refine hx_int.of_measure_le_smul (μ := μ) (μ' := μpartial N)
        (c := (Nat.succ N : ℝ≥0∞)) ?_ ?_
    · simp
    · simpa using hμpartial_le_smul N
  have hx_int_piece : ∀ n, Integrable hxFun (μn n) := by
    intro n
    refine hx_int.of_measure_le_smul (μ := μ) (μ' := μn n)
        (c := (1 : ℝ≥0∞)) ?_ ?_
    · simp
    · simpa [one_smul] using hμn_le n
  have hx_convPartial_succ :
      ∀ N,
        convPartial (N + 1) x =
          convPartial N x + convPiece (N + 1) x := by
    intro N
    have h_measure := hμpartial_succ N
    have h_add :=
      MeasureTheory.integral_add_measure
        (μ := μpartial N) (ν := μn (N + 1))
        (f := hxFun)
        (hx_int_partial N)
        (hx_int_piece (N + 1))
    simpa [hx_convPartial_def, hx_convPiece_def, hxFun, h_measure,
      Nat.succ_eq_add_one]
      using h_add
  have hx_convPartial_sum :
      ∀ N,
        convPartial N x =
          ∑ k ∈ Finset.range (N + 1), convPiece k x := by
    intro N
    induction' N with N hN
    · have hμ := hμpartial_zero
      simp [hx_convPartial_def, hx_convPiece_def, Finset.range_one, hμ]
    · have h_step := hx_convPartial_succ N
      simpa [Finset.sum_range_succ, Nat.succ_eq_add_one, add_comm,
        add_left_comm, add_assoc, hN]
        using h_step
  have hx_norm_piece_bound :
      ∀ n, ‖convPiece n x‖ ≤ ∫ y, ‖hxFun y‖ ∂ μn n := by
    intro n
    have hx_bound :=
      norm_integral_le_integral_norm (μ := μn n) (f := hxFun)
    simpa [hx_convPiece_def, hxFun]
      using hx_bound
  have hx_norm_hasSum :
      HasSum (fun n => ∫ y, ‖hxFun y‖ ∂ μn n)
        (∫ y, ‖hxFun y‖ ∂ μ) := by
    have hx_norm_integrable : Integrable (fun y : G => ‖hxFun y‖) μ := hx_int.norm
    have hx_norm_integrable_sum :
        Integrable (fun y : G => ‖hxFun y‖) (Measure.sum μn) := by
      simpa [hμ_sum] using hx_norm_integrable
    simpa [hμ_sum]
      using
        (MeasureTheory.hasSum_integral_measure
          (μ := μn)
          (f := fun y : G => (‖hxFun y‖ : ℝ))
          (hf := hx_norm_integrable_sum))
  have hx_abs_summable :
      Summable fun n => ‖convPiece n x‖ :=
    (Summable.of_nonneg_of_le (fun _ => by positivity)
        hx_norm_piece_bound hx_norm_hasSum.summable)
  have hx_summable : Summable fun n => convPiece n x :=
    hx_abs_summable.of_norm
  have hx_tsum_eq :
      (∑' n, convPiece n x) = conv x := by
    have hx_integrable_sum : Integrable hxFun (Measure.sum μn) := by
      simpa [hμ_sum] using hx_int
    have hx_hasSum_measure :=
      MeasureTheory.hasSum_integral_measure
        (μ := μn) (f := hxFun) (hf := hx_integrable_sum)
    have hx_tsum := hx_hasSum_measure.tsum_eq
    have hx_tsum_value :
        (∑' n, convPiece n x) = ∫ y, hxFun y ∂ Measure.sum μn := by
      simpa [hx_convPiece_def, hxFun] using hx_tsum
    have hx_tsum_to_mu :
        (∑' n, convPiece n x) = ∫ y, hxFun y ∂ μ := by
      simpa [hμ_sum] using hx_tsum_value
    simpa [hx_conv_def', hxFun] using hx_tsum_to_mu
  have hx_hasSum : HasSum (fun n => convPiece n x) (conv x) := by
    simpa [hx_tsum_eq] using hx_summable.hasSum
  have hx_tendsto_range :
      Tendsto (fun N => ∑ k ∈ Finset.range N, convPiece k x)
        atTop (𝓝 (conv x)) :=
    hx_hasSum.tendsto_sum_nat
  have hx_tendsto_succ :
      Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), convPiece k x)
        atTop (𝓝 (conv x)) :=
    hx_tendsto_range.comp (tendsto_add_atTop_nat 1)
  have hx_eventually_eq :
      (fun N => ∑ k ∈ Finset.range (N + 1), convPiece k x)
        =ᶠ[atTop]
          fun N => convPartial N x :=
    Filter.Eventually.of_forall fun N => (hx_convPartial_sum N).symm
  exact hx_tendsto_succ.congr' hx_eventually_eq

lemma sfiniteSeq_convPartial_aestronglyMeasurable
    [NormedAddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ]
    (f g : G → ℂ)
    (μpartial : ℕ → Measure G)
    (convPartial : ℕ → G → ℂ)
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (hμpartial_le_smul : ∀ N, μpartial N ≤ ((N + 1 : ℝ≥0∞) • μ))
    (h_kernel_meas :
      AEStronglyMeasurable
        (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ))
    (h_convPartial_def :
      ∀ N, convPartial N = fun x => ∫ y, f (x - y) * g y ∂ μpartial N) :
    ∀ N, AEStronglyMeasurable (convPartial N) μ := by
  classical
  intro N
  haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
  set c : ℝ≥0∞ := (N + 1 : ℝ≥0∞)
  have h_prod_le : μ.prod (μpartial N) ≤ c • (μ.prod μ) := by
    intro s
    classical
    set S := toMeasurable (μ.prod μ) s with hS_def
    have hS_meas : MeasurableSet S := measurableSet_toMeasurable _ _
    have hs_subset : s ⊆ S := by
      simpa [S] using subset_toMeasurable (μ.prod μ) s
    have h_meas_eq : (c • (μ.prod μ)) S = (c • (μ.prod μ)) s := by
      simp [Measure.smul_apply, S, measure_toMeasurable, c, mul_comm,
        mul_left_comm, mul_assoc]
    have h_prod_le_S :
        (μ.prod (μpartial N)) S ≤ (c • (μ.prod μ)) S := by
      have h_prod_apply :
          (μ.prod (μpartial N)) S =
            ∫⁻ x, μpartial N (Prod.mk x ⁻¹' S) ∂ μ :=
        Measure.prod_apply (μ := μ) (ν := μpartial N) hS_meas
      have h_prod_apply' :
          (μ.prod μ) S = ∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μ :=
        Measure.prod_apply (μ := μ) (ν := μ) hS_meas
      have h_pointwise :
          (fun x => μpartial N (Prod.mk x ⁻¹' S)) ≤
            fun x => c * μ (Prod.mk x ⁻¹' S) := by
        intro x
        have h_le := (hμpartial_le_smul N) (Prod.mk x ⁻¹' S)
        simpa [Measure.smul_apply, c, mul_comm, mul_left_comm, mul_assoc]
          using h_le
      have h_integral_le :
          (∫⁻ x, μpartial N (Prod.mk x ⁻¹' S) ∂ μ)
            ≤ ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ μ :=
        lintegral_mono h_pointwise
      have h_const_mul :
          ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ μ =
            c * ∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μ :=
        lintegral_const_mul c (measurable_measure_prodMk_left hS_meas)
      calc
        (μ.prod (μpartial N)) S
            = ∫⁻ x, μpartial N (Prod.mk x ⁻¹' S) ∂ μ := h_prod_apply
        _ ≤ ∫⁻ x, c * μ (Prod.mk x ⁻¹' S) ∂ μ := h_integral_le
        _ = c * ∫⁻ x, μ (Prod.mk x ⁻¹' S) ∂ μ := h_const_mul
        _ = (c • (μ.prod μ)) S := by
          simp [Measure.smul_apply, h_prod_apply', c, mul_comm, mul_left_comm,
            mul_assoc]
    have h_prod_le_s : (μ.prod (μpartial N)) s ≤ (c • (μ.prod μ)) s := by
      calc
        (μ.prod (μpartial N)) s
            ≤ (μ.prod (μpartial N)) S := by
              exact measure_mono hs_subset
        _ ≤ (c • (μ.prod μ)) S := h_prod_le_S
        _ = (c • (μ.prod μ)) s := h_meas_eq
    simpa [c] using h_prod_le_s
  have h_prod_ac : μ.prod (μpartial N) ≪ μ.prod μ :=
    Measure.absolutelyContinuous_of_le_smul h_prod_le
  have h_kernel_meas' :
      AEStronglyMeasurable
        (fun q : G × G => f (q.1 - q.2) * g q.2)
        (μ.prod (μpartial N)) :=
    h_kernel_meas.mono_ac h_prod_ac
  have h_meas :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μ)
      (ν := μpartial N)
      (f := fun q : G × G => f (q.1 - q.2) * g q.2)
      h_kernel_meas'
  simpa [h_convPartial_def N]
    using h_meas

lemma sfiniteSeq_lintegral_norm_tendsto
    [NormedAddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ]
    (g : G → ℂ)
    (μn μpartial : ℕ → Measure G)
    (hμ_sum : Measure.sum μn = μ)
    (h_lintegral_norm_partial :
      ∀ N,
        ∫⁻ y, ‖g y‖ₑ ∂ μpartial N
          = ∑ k ∈ Finset.range (N + 1), ∫⁻ y, ‖g y‖ₑ ∂ μn k) :
    Tendsto (fun N => ∫⁻ y, ‖g y‖ₑ ∂ μpartial N) atTop
      (𝓝 (∫⁻ y, ‖g y‖ₑ ∂ μ)) := by
  classical
  let gNorm : G → ℝ≥0∞ := fun y => ‖g y‖ₑ
  have h_lintegral_norm_sum :
      (∑' n, ∫⁻ y, gNorm y ∂ μn n) = ∫⁻ y, gNorm y ∂ μ := by
    classical
    simpa [hμ_sum]
      using
        (MeasureTheory.lintegral_sum_measure
          (μ := μn)
          (f := fun y : G => gNorm y)).symm
  have h_series_tendsto :
      Tendsto
        (fun N => ∑ k ∈ Finset.range (N + 1), ∫⁻ y, gNorm y ∂ μn k)
        atTop
        (𝓝 (∑' n, ∫⁻ y, gNorm y ∂ μn n)) :=
    (ENNReal.tendsto_nat_tsum
      (f := fun n => ∫⁻ y, gNorm y ∂ μn n)).comp
        (tendsto_add_atTop_nat 1)
  have h_eval' :
      (fun N => ∑ k ∈ Finset.range (N + 1), ∫⁻ y, gNorm y ∂ μn k)
        = fun N => ∫⁻ y, gNorm y ∂ μpartial N := by
    funext N
    exact (h_lintegral_norm_partial N).symm
  have h_series_tendsto_int :
      Tendsto (fun N => ∫⁻ y, gNorm y ∂ μpartial N) atTop
        (𝓝 (∑' n, ∫⁻ y, gNorm y ∂ μn n)) := by
    exact h_eval' ▸ h_series_tendsto
  have h_target :
      (𝓝 (∑' n, ∫⁻ y, gNorm y ∂ μn n))
        = 𝓝 (∫⁻ y, gNorm y ∂ μ) := by
    change
        𝓝 (∑' n, ∫⁻ y, ‖g y‖ₑ ∂ μn n)
          = 𝓝 (∫⁻ y, ‖g y‖ₑ ∂ μ)
    exact congrArg (fun t => 𝓝 t) h_lintegral_norm_sum
  have h_series_tendsto_final :
      Tendsto (fun N => ∫⁻ y, gNorm y ∂ μpartial N) atTop
        (𝓝 (∫⁻ y, gNorm y ∂ μ)) := by
    exact h_target ▸ h_series_tendsto_int
  change
      Tendsto (fun N => ∫⁻ y, ‖g y‖ₑ ∂ μpartial N) atTop
        (𝓝 (∫⁻ y, ‖g y‖ₑ ∂ μ))
  exact h_series_tendsto_final

lemma sfiniteSeq_convPartial_integral_tendsto
    [NormedAddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ]
    (r : ℝ≥0∞)
    (μn μpartial : ℕ → Measure G)
    (convPartial : ℕ → G → ℂ)
    (h_lintegral_convPartial_partial_sum :
      ∀ N M,
        ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μpartial M
          = ∑ k ∈ Finset.range (M + 1),
              ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn k)
    (h_lintegral_convPartial_sum :
      ∀ N,
        (∑' k, ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn k)
          = ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ) :
    ∀ N,
      Tendsto
        (fun M => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μpartial M)
        atTop
        (𝓝 (∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ)) := by
  intro N
  classical
  have h_series_tendsto :
      Tendsto
        (fun M =>
          ∑ k ∈ Finset.range (M + 1),
            ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn k)
        atTop
        (𝓝
          (∑' k,
            ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn k)) := by
    exact
      (ENNReal.tendsto_nat_tsum
        (f := fun k => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn k)).comp
        (tendsto_add_atTop_nat 1)
  have h_eval :
      (fun M => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μpartial M)
        = fun M =>
            ∑ k ∈ Finset.range (M + 1),
              ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn k := by
    funext M
    exact h_lintegral_convPartial_partial_sum N M
  have h_eval' :
      (∑' k, ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn k)
        = ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ :=
    h_lintegral_convPartial_sum N
  simpa [h_eval, h_eval'] using h_series_tendsto

lemma integrable_norm_convolution_kernel_section
    (μ : Measure G) [NormedAddCommGroup G] [SFinite μ] (f g : G → ℂ)
    (h_kernel_int : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)) :
    ∀ᵐ x ∂μ, Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ := by
  classical
  have h_norm_int := h_kernel_int.norm
  have h_norm_eq :
      (fun q : G × G => ‖f (q.1 - q.2) * g q.2‖)
        = fun q : G × G => ‖f (q.1 - q.2)‖ * ‖g q.2‖ := by
    ext q
    simp [norm_mul]
  rw [h_norm_eq] at h_norm_int
  simpa using Integrable.prod_right_ae (μ := μ) (ν := μ) h_norm_int

lemma integral_norm_mul_mono
    (μ₁ μ₂ : Measure G) [NormedAddCommGroup G] [IsFiniteMeasure μ₁]
    (f g : G → ℂ) (x : G) (hμ : μ₁ ≤ μ₂)
    (h_int_μ₂ : Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ₂) :
    ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ₁ ≤ ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ₂ := by
  -- The integrand is nonnegative
  have h_nonneg : ∀ᵐ y ∂μ₂, 0 ≤ ‖f (x - y)‖ * ‖g y‖ :=
    ae_of_all μ₂ fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- Apply integral_mono_measure directly
  exact integral_mono_measure hμ h_nonneg h_int_μ₂

end ConvolutionAuxiliary
