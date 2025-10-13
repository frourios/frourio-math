import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
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
variable [NormedAddCommGroup G] [MeasurableSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]
variable (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]

/--
Auxiliary finite-measure version of `convolution_memLp_of_memLp`.  This lemma will be proved in the
next steps and then used to deduce the general s-finite case via exhaustion by finite measures.
-/
lemma integrable_abs_mul_eLpNorm_of_memLp
    [IsFiniteMeasure μ]
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
    [IsFiniteMeasure μ]
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
    [IsFiniteMeasure μ]
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

lemma convolution_memLp_of_memLp
    (f g : G → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hf_r : MemLp f r μ) (hg : MemLp g q μ) :
    MemLp (fun x => ∫ y, f (x - y) * g y ∂μ) r μ := by
  -- Plan: localize to the exhausting sequence of finite-measure subsets given by the s-finite Haar
  -- measure, apply the finite-measure version of the argument on each restriction using
  -- Minkowski plus Hölder, and then pass to the limit via monotone convergence to recover the
  -- global `MemLp` membership.
  classical
  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
  have hμn_fin : ∀ n, IsFiniteMeasure (μn n) := fun n => inferInstance
  have hμ_sum : Measure.sum μn = μ := MeasureTheory.sum_sfiniteSeq μ
  have hf_n : ∀ n, MemLp f p (μn n) := fun n =>
    hf.of_measure_le_smul (μ' := μn n) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n)
  have hg_n : ∀ n, MemLp g q (μn n) := fun n =>
    hg.of_measure_le_smul (μ' := μn n) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n)
  let μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k
  have hμpartial_succ : ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1) := by
    intro N
    classical
    simp [μpartial, Nat.succ_eq_add_one, Finset.range_succ, add_comm, add_left_comm, add_assoc]
  have hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N) := by
    intro N
    classical
    refine Nat.rec ?base ?step N
    · simpa [μpartial] using hμn_fin 0
    · intro k hk
      have hk_add : IsFiniteMeasure (μpartial k + μn (k + 1)) := by infer_instance
      simpa [hμpartial_succ, Nat.succ_eq_add_one] using hk_add
  have hμpartial_le_succ : ∀ N, μpartial N ≤ μpartial (N + 1) := by
    intro N s
    classical
    have hnonneg : 0 ≤ μn (N + 1) s := bot_le
    simp [hμpartial_succ, Nat.succ_eq_add_one, Measure.add_apply]
  have hμpartial_mono : Monotone μpartial :=
    monotone_nat_of_le_succ hμpartial_le_succ
  have hμpartial_le_smul : ∀ N, μpartial N ≤ ((N + 1 : ℝ≥0∞) • μ) := by
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
    · have := (ENNReal.toNNReal_le_toNNReal hμpartial_ne_top hhs_ne_top).2 hμpartial_le_hs
      simpa using this
  have hf_partial : ∀ N, MemLp f p (μpartial N) := by
    intro N
    refine hf.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have hf_r_partial : ∀ N, MemLp f r (μpartial N) := by
    intro N
    refine hf_r.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have hg_partial : ∀ N, MemLp g q (μpartial N) := by
    intro N
    refine hg.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have hμpartial_tendsto :
      ∀ ⦃s : Set G⦄, MeasurableSet s →
        Tendsto (fun N => μpartial N s) atTop (𝓝 (μ s)) := by
    intro s hs
    classical
    have h_sum_eval := congrArg (fun ν : Measure G => ν s) hμ_sum
    have hμ_tsum : ∑' n, μn n s = μ s := by
      simpa [Measure.sum_apply _ hs] using h_sum_eval
    have h_seq :
        Tendsto (fun N => μpartial N s) atTop (𝓝 (∑' n, μn n s)) := by
      simpa [μpartial, Measure.finset_sum_apply, Nat.succ_eq_add_one] using
        (ENNReal.tendsto_nat_tsum (fun n => μn n s)).comp (tendsto_add_atTop_nat 1)
    simpa [hμ_tsum] using h_seq
  -- Remaining steps: for each `n`, apply the finite measure argument with measure `μn n`; then
  -- use `Measure.sum` decomposition `μ = Measure.sum μn` to pass to the limit and conclude the
  -- desired membership.
  have hμpartial_tendsto_univ :
      Tendsto (fun N => μpartial N Set.univ) atTop (𝓝 (μ Set.univ)) :=
    hμpartial_tendsto MeasurableSet.univ
  set convPartial : ℕ → G → ℂ := fun N x => ∫ y, f (x - y) * g y ∂μpartial N
  have hconvPartial_tendsto_measure := hμpartial_tendsto_univ
  sorry

/--
Norm inequality for convolution in the finite-exponent Young regime. This refines the membership
lemma above by providing the optimal multiplicative bound on the `L^r` norm.
-/
lemma eLpNorm_convolution_le_mul
    (f g : G → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) r μ ≤
      eLpNorm f p μ * eLpNorm g q μ := by
  sorry

end ConvolutionAuxiliary
