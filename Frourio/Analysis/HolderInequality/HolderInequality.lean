import Frourio.Analysis.HolderInequality.HolderInequalityCore
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory ENNReal NNReal
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section HolderNormalized

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
  have hf_pow_integrable : Integrable (fun x => f x ^ pr) μ :=
    (hf.integrable_norm_rpow hp_ne_zero hp_ne_top).congr hf_abs_eq
  have hg_pow_integrable : Integrable (fun x => g x ^ qr) μ :=
    (hg.integrable_norm_rpow hq_ne_zero hq_ne_top).congr hg_abs_eq
  have hf_norm_pow_eq :
      (fun x => f_norm x ^ pr)
        =ᵐ[μ] fun x => (norm_f⁻¹) ^ pr * (f x ^ pr) := by
    sorry
  have hg_norm_pow_eq :
      (fun x => g_norm x ^ qr)
        =ᵐ[μ] fun x => (norm_g⁻¹) ^ qr * (g x ^ qr) := by
    sorry
  have hf_norm_pow_integrable : Integrable (fun x => f_norm x ^ pr) μ := by
    sorry
  have hg_norm_pow_integrable : Integrable (fun x => g_norm x ^ qr) μ := by
    sorry
  have hf_norm_pow_nonneg :
      0 ≤ᵐ[μ] fun x => f_norm x ^ pr := by
    sorry
  have hg_norm_pow_nonneg :
      0 ≤ᵐ[μ] fun x => g_norm x ^ qr := by
    sorry
  have hf_integral_aux : ∫ x, f x ^ pr ∂μ = norm_f ^ pr := by
    sorry
  have hg_integral_aux : ∫ x, g x ^ qr ∂μ = norm_g ^ qr := by
    sorry
  have h_integral_f_norm_pow : ∫ x, f_norm x ^ pr ∂μ = 1 := by
    sorry
  have h_integral_g_norm_pow : ∫ x, g_norm x ^ qr ∂μ = 1 := by
    sorry
  have h_prod_integrable : Integrable (fun x => f_norm x * g_norm x) μ := by
    sorry
  have h_prod_eq :
      (fun x => f_norm x * g_norm x)
        =ᵐ[μ] fun x => (norm_f⁻¹ * norm_g⁻¹) * (f x * g x) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [f_norm, g_norm, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have h_integral_fg_norm : ∫ x, f_norm x * g_norm x ∂μ = 1 := by
    sorry
  have h_diff_nonneg :
      0 ≤ᵐ[μ]
        fun x =>
          f_norm x ^ pr / pr + g_norm x ^ qr / qr - f_norm x * g_norm x := by
    sorry
  have h_diff_integrable : Integrable
      (fun x => f_norm x ^ pr / pr + g_norm x ^ qr / qr - f_norm x * g_norm x) μ := by
    sorry
  have h_diff_integral_zero :
      ∫ x, f_norm x ^ pr / pr + g_norm x ^ qr / qr - f_norm x * g_norm x ∂μ = 0 := by
    sorry
  have h_diff_zero :
      (fun x => f_norm x ^ pr / pr + g_norm x ^ qr / qr - f_norm x * g_norm x)
        =ᵐ[μ] fun _ => (0 : ℝ) := by
    sorry
  have young_eq_aux :
      ∀ {a b : ℝ}, 0 < a → 0 < b →
        a ^ pr / pr + b ^ qr / qr = a * b → a ^ pr = b ^ qr := by
    intro a b ha hb h_eq'
    sorry
  have h_norm_eq_aeme :
      (fun x => f_norm x ^ pr) =ᵐ[μ] fun x => g_norm x ^ qr := by
    sorry
  have h_goal :
      (fun x => f x ^ pr) =ᵐ[μ] fun x => c * g x ^ qr := by
    sorry
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
  sorry

/--
**Self-conjugate property.**

p = 2 is its own conjugate exponent.
-/
theorem conjugate_exponent_two :
    IsConjugateExponent 2 2 := by
  sorry

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
  sorry

end AuxiliaryLemmas
