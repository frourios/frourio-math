import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Hölder's Inequality

This file contains Hölder's inequality and related results for L^p spaces.

Hölder's inequality is a fundamental inequality in analysis that bounds the
integral of a product of functions in terms of their L^p norms. For conjugate
exponents p and q (where 1/p + 1/q = 1), it states:

  ∫ |f · g| dμ ≤ ‖f‖_{L^p} · ‖g‖_{L^q}

This inequality is crucial for:
- Proving Minkowski's inequality
- Establishing duality in L^p spaces
- Young's inequality for convolution
- Various interpolation results

## Main results

- `holder_inequality`: The main Hölder inequality for conjugate exponents
- `holder_inequality_ennreal`: Version with extended non-negative reals
- `holder_inequality_infty`: Special case when p = ∞ (q = 1)
- `holder_inequality_one`: Special case when p = 1 (q = ∞)
- `holder_conjugate_exponent`: Definition and properties of conjugate exponents

## References

- Folland, Real Analysis: Modern Techniques and Their Applications, Section 6.2
- Rudin, Real and Complex Analysis, Chapter 3
- Lieb & Loss, Analysis, Section 2.3

## Implementation notes

The proof strategy depends on the exponents:
1. For p = 1, q = ∞: Direct from essential supremum bound
2. For p = ∞, q = 1: Symmetric to case 1
3. For 1 < p < ∞: Use Young's inequality for products ab ≤ a^p/p + b^q/q
4. Apply to normalized functions and integrate

-/

open MeasureTheory ENNReal NNReal
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section ConjugateExponent

/--
**Conjugate exponent relation.**

For 1 ≤ p ≤ ∞, the conjugate exponent q satisfies 1/p + 1/q = 1.
-/
def IsConjugateExponent (p q : ℝ≥0∞) : Prop :=
  (p = 1 ∧ q = ∞) ∨ (p = ∞ ∧ q = 1) ∨
  (1 < p ∧ p < ∞ ∧ 1 < q ∧ q < ∞ ∧ 1 / p + 1 / q = 1)

/--
**Conjugate exponent is unique.**

If p and q are conjugate exponents, then q is uniquely determined by p.
-/
theorem conjugate_exponent_unique
    {p q₁ q₂ : ℝ≥0∞}
    (h₁ : IsConjugateExponent p q₁)
    (h₂ : IsConjugateExponent p q₂) :
    q₁ = q₂ := by
  classical
  rcases h₁ with h₁ | h₁
  · rcases h₁ with ⟨hp, hq₁⟩
    subst hp
    have hq₂ : q₂ = ∞ := by simpa [IsConjugateExponent] using h₂
    simp [hq₁, hq₂]
  · rcases h₁ with h₁ | h₁
    · rcases h₁ with ⟨hp, hq₁⟩
      subst hp
      have hq₂ : q₂ = 1 := by simpa [IsConjugateExponent] using h₂
      simp [hq₁, hq₂]
    · rcases h₁ with ⟨hp, hp_top, hq₁, hq₁_top, hpq₁⟩
      rcases h₂ with h₂ | h₂
      · rcases h₂ with ⟨hp_eq, _⟩
        have : False := by simp [hp_eq] at hp
        exact this.elim
      · rcases h₂ with h₂ | h₂
        · rcases h₂ with ⟨hp_eq, _⟩
          have : False := by simp [hp_eq] at hp_top
          exact this.elim
        · rcases h₂ with ⟨_, _, hq₂, hq₂_top, hpq₂⟩
          have hp_ne_zero : p ≠ 0 := by
            intro hp_zero
            have : False := by simp [hp_zero] at hp
            exact this.elim
          have hp_inv_ne_top : 1 / p ≠ ∞ := by
            simpa [one_div] using (ENNReal.inv_ne_top).2 hp_ne_zero
          have h_sum : 1 / p + 1 / q₁ = 1 / p + 1 / q₂ := by
            calc
              1 / p + 1 / q₁ = 1 := hpq₁
              _ = 1 / p + 1 / q₂ := by simpa [eq_comm] using hpq₂
          have h_inv_eq : 1 / q₁ = 1 / q₂ :=
            WithTop.add_left_cancel (α := ℝ≥0) hp_inv_ne_top h_sum
          have := congrArg (fun x : ℝ≥0∞ => x⁻¹) h_inv_eq
          simpa [one_div] using this

/--
**Conjugate relation is symmetric.**

If p and q are conjugate exponents, then so are q and p.
-/
theorem conjugate_exponent_symm
    {p q : ℝ≥0∞}
    (h : IsConjugateExponent p q) :
    IsConjugateExponent q p := by
  classical
  rcases h with h | h | h
  · rcases h with ⟨hp, hq⟩
    exact Or.inr <| Or.inl ⟨hq, hp⟩
  · rcases h with ⟨hp, hq⟩
    exact Or.inl ⟨hq, hp⟩
  · rcases h with ⟨hp, hp_top, hq, hq_top, hpq⟩
    refine Or.inr <| Or.inr ⟨hq, hq_top, hp, hp_top, ?_⟩
    simpa [add_comm] using hpq

/--
**Exponent bounds for conjugate exponents.**

If p and q are conjugate with 1 < p < ∞, then 1 < q < ∞.
-/
theorem conjugate_exponent_bounds
    {p q : ℝ≥0∞}
    (h : IsConjugateExponent p q)
    (hp : 1 < p) (hp_top : p < ∞) :
    1 < q ∧ q < ∞ := by
  classical
  rcases h with h | h | h
  · rcases h with ⟨hp_eq, _⟩
    have : False := by simp [hp_eq] at hp
    exact this.elim
  · rcases h with ⟨hp_eq, _⟩
    have : False := by simp [hp_eq] at hp_top
    exact this.elim
  · rcases h with ⟨_, _, hq, hq_top, _⟩
    exact ⟨hq, hq_top⟩

end ConjugateExponent

section HolderBasic

/--
**Hölder's inequality (basic form for p = 1, q = ∞).**

For any measurable functions f and g:
  ∫ |f · g| dμ ≤ ‖f‖_{L^1} · ‖g‖_{L^∞}
-/
theorem holder_inequality_one_infty
    (f : α → E) (g : α → F)
    (hf : Integrable f μ)
    (hg_ae : AEStronglyMeasurable g μ)
    (hg_bound : ∃ C, ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (∫ x, ‖f x‖ ∂μ) * (sInf {C | ∀ᵐ x ∂μ, ‖g x‖ ≤ C}) := by
  classical
  by_cases hμ : μ = 0
  · simp [hμ]
  set S := {C : ℝ | ∀ᵐ x ∂μ, ‖g x‖ ≤ C} with hS
  have hS_nonempty : S.Nonempty :=
    let ⟨C, hC⟩ := hg_bound
    ⟨max C 0, hC.mono fun x hx => hx.trans <| le_max_left _ _⟩
  have hf_norm : Integrable (fun x => ‖f x‖) μ := hf.norm
  set A := ∫ x, ‖f x‖ * ‖g x‖ ∂μ with hA
  set a := ∫ x, ‖f x‖ ∂μ with ha
  have ha_nonneg : 0 ≤ a := by
    have : ∀ x, 0 ≤ ‖f x‖ := fun x => norm_nonneg _
    simpa [ha] using integral_nonneg this
  have holder_with_bound : ∀ {C : ℝ}, C ∈ S → A ≤ a * C := by
    intro C hC
    have hC_ae : ∀ᵐ x ∂μ, ‖g x‖ ≤ C := hC
    have hC_nonneg : 0 ≤ C :=
      by
        have hμ_univ_ne : μ (Set.univ : Set α) ≠ 0 :=
          by simpa [Measure.measure_univ_eq_zero] using hμ
        by_contra hCneg
        have hCneg' : C < 0 := lt_of_not_ge hCneg
        have hμset : μ {x | C < ‖g x‖} = 0 := by
          simpa [not_le] using (ae_iff).1 hC_ae
        have hset : {x | C < ‖g x‖} = (Set.univ : Set α) := by
          classical
          ext x
          have hx : C < ‖g x‖ := lt_of_lt_of_le hCneg' (norm_nonneg _)
          simp [hx]
        exact hμ_univ_ne <| by simpa [hset] using hμset
    have h_mul_le : (fun x => ‖f x‖ * ‖g x‖) ≤ᵐ[μ] fun x => C * ‖f x‖ :=
      hC_ae.mono fun x hx =>
        by
          have hfx : 0 ≤ ‖f x‖ := norm_nonneg _
          have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C :=
            (mul_le_mul_of_nonneg_left hx hfx : _)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have h_mul_abs : ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ C * ‖f x‖ :=
      hC_ae.mono fun x hx =>
        by
          have hfx : 0 ≤ ‖f x‖ := norm_nonneg _
          have hgx : 0 ≤ ‖g x‖ := norm_nonneg _
          have h_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ := mul_nonneg hfx hgx
          have h_rhs_nonneg : 0 ≤ C * ‖f x‖ := mul_nonneg hC_nonneg hfx
          have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C :=
            (mul_le_mul_of_nonneg_left hx hfx : _)
          simpa [Real.norm_of_nonneg h_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
            mul_comm, mul_left_comm, mul_assoc] using this
    have h_mul_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
      (hf_norm.aestronglyMeasurable.mul hg_ae.norm)
    have h_const_int : Integrable (fun x => C * ‖f x‖) μ := hf_norm.const_mul C
    have h_mul_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
      Integrable.mono' h_const_int h_mul_meas h_mul_abs
    have h_integral_le := integral_mono_ae h_mul_int h_const_int h_mul_le
    have h_integral_const : ∫ x, C * ‖f x‖ ∂μ = C * a := by
      simpa [ha, mul_comm] using
        integral_const_mul (μ := μ) (r := C) (f := fun x => ‖f x‖)
    have : A ≤ C * a := by
      simpa [A, h_integral_const] using h_integral_le
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have h_eps : ∀ {ε : ℝ}, 0 < ε → A ≤ a * (sInf S + ε) := by
    intro ε hε
    obtain ⟨C, hC_mem, hC_lt⟩ := Real.lt_sInf_add_pos hS_nonempty hε
    have hAC : A ≤ a * C := holder_with_bound hC_mem
    have h_le : C ≤ sInf S + ε := le_of_lt hC_lt
    have h_order : a * C ≤ a * (sInf S + ε) :=
      mul_le_mul_of_nonneg_left h_le ha_nonneg
    exact hAC.trans h_order
  have hA_nonneg : 0 ≤ A :=
    by
      have : ∀ x, 0 ≤ ‖f x‖ * ‖g x‖ :=
        fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
      simpa [A] using integral_nonneg this
  have h_final : A ≤ a * sInf S := by
    by_cases ha_zero : a = 0
    · obtain ⟨C₀, hC₀⟩ := hS_nonempty
      have hA_le_zero : A ≤ 0 := by
        simpa [ha_zero] using holder_with_bound hC₀
      have hA_eq_zero : A = 0 :=
        le_antisymm hA_le_zero hA_nonneg
      simp [hA_eq_zero, ha_zero]
    · have ha_ne : a ≠ 0 := ha_zero
      have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by simpa [eq_comm] using ha_ne)
      have h_eps' : ∀ {ε : ℝ}, 0 < ε → A ≤ a * sInf S + ε := by
        intro ε hε
        have hδpos : 0 < ε / a := div_pos hε ha_pos
        have hmain := h_eps hδpos
        have hmul : a * (sInf S + ε / a) = a * sInf S + ε := by
          simp [mul_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, ha_ne]
        simpa [hmul, mul_comm, mul_left_comm, mul_assoc] using hmain
      have h_lt : ∀ {ε : ℝ}, 0 < ε → A < a * sInf S + ε := by
        intro ε hε
        have hhalf : 0 < ε / 2 := half_pos hε
        have hineq := h_eps' hhalf
        have hlt : a * sInf S + ε / 2 < a * sInf S + ε := by
          have := half_lt_self hε
          exact add_lt_add_left this _
        exact lt_of_le_of_lt hineq hlt
      exact (le_iff_forall_pos_lt_add).2 fun ε hε => h_lt hε
  simpa [A, a, S, mul_comm, mul_left_comm, mul_assoc] using h_final

/--
**Hölder's inequality (basic form for p = ∞, q = 1).**

This is the symmetric case of `holder_inequality_one_infty`.
-/
theorem holder_inequality_infty_one
    (f : α → E) (g : α → F)
    (hf_ae : AEStronglyMeasurable f μ)
    (hf_bound : ∃ C, ∀ᵐ x ∂μ, ‖f x‖ ≤ C)
    (hg : Integrable g μ) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (sInf {C | ∀ᵐ x ∂μ, ‖f x‖ ≤ C}) * (∫ x, ‖g x‖ ∂μ) := by
  classical
  have h :=
    holder_inequality_one_infty (μ := μ) (E := F) (F := E)
      (f := g) (g := f) hg hf_ae hf_bound
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/--
**Young's inequality for products.**

For conjugate exponents p and q with 1 < p < ∞, and non-negative a, b:
  a · b ≤ a^p / p + b^q / q
-/
theorem young_inequality
    {p q : ℝ}
    (hp : 1 < p)
    (hpq : 1 / p + 1 / q = 1)
    {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ a ^ p / p + b ^ q / q := by
  have h_conj : p.HolderConjugate q :=
    (Real.holderConjugate_iff).2 ⟨hp, by simpa [one_div] using hpq⟩
  exact Real.young_inequality_of_nonneg ha hb h_conj

end HolderBasic

section HolderGeneral

/--
**Hölder's inequality (general form with eLpNorm).**

For conjugate exponents 1 ≤ p, q ≤ ∞ with 1/p + 1/q = 1:
  ∫ |f · g| dμ ≤ ‖f‖_{L^p(μ)} · ‖g‖_{L^q(μ)}
-/
theorem holder_inequality
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f : α → E) (g : α → F)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (fun x => ‖f x‖ * ‖g x‖) μ ∧
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  classical
  rcases hpq with hpq | hpq | hpq
  · rcases hpq with ⟨hp, hq⟩
    subst hp; subst hq
    -- Case `p = 1`, `q = ∞`
    have hf_int : Integrable f μ := by
      simpa [memLp_one_iff_integrable] using hf
    obtain ⟨hg_meas, hg_fin⟩ := hg
    have hg_bound : ∃ C, ∀ᵐ x ∂μ, ‖g x‖ ≤ C := by
      have hg_ne_top' : eLpNorm g ∞ μ ≠ ∞ := ne_of_lt hg_fin
      have hg_ne_top : eLpNormEssSup g μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hg_ne_top'
      refine ⟨(eLpNorm g ∞ μ).toReal, ?_⟩
      refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => g x)).mono ?_
      intro x hx
      have hx' : ENNReal.ofReal ‖g x‖ ≤ eLpNormEssSup g μ := by
        simpa [ofReal_norm_eq_enorm] using hx
      have := (ENNReal.ofReal_le_iff_le_toReal hg_ne_top).mp hx'
      simpa [eLpNorm, eLpNorm_exponent_top] using this
    have hg_ae : AEStronglyMeasurable g μ := hg_meas
    have :=
      holder_inequality_one_infty (μ := μ) (f := f) (g := g) hf_int hg_ae hg_bound
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hg_bound
      set C₀ := max C 0
      have hC₀_nonneg : 0 ≤ C₀ := le_max_right _ _
      have hC₀_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C₀ :=
        hC.mono fun x hx => le_max_of_le_left hx
      have h_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_int.aestronglyMeasurable.norm.mul hg_ae.norm)
      have h_dom : ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ C₀ * ‖f x‖ :=
        hC₀_bound.mono fun x hx =>
          by
            have hf_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg : 0 ≤ ‖g x‖ := norm_nonneg _
            have hmul_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ := mul_nonneg hf_nonneg hg_nonneg
            have h_rhs_nonneg : 0 ≤ C₀ * ‖f x‖ := mul_nonneg hC₀_nonneg hf_nonneg
            have hmul_le : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C₀ :=
              (mul_le_mul_of_nonneg_left hx hf_nonneg : _)
            simpa [Real.norm_of_nonneg hmul_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using hmul_le
      have h_majorant : Integrable (fun x => C₀ * ‖f x‖) μ :=
        (hf_int.norm.const_mul C₀)
      exact Integrable.mono' h_majorant h_meas h_dom
    · classical
      -- Express the L¹ norm of `f` via `eLpNorm`.
      have hf_norm : Integrable (fun x => ‖f x‖) μ := hf_int.norm
      have hf_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ :=
        Filter.Eventually.of_forall fun _ => norm_nonneg _
      have hf_lintegral :
          ∫⁻ x, ENNReal.ofReal (‖f x‖) ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := by
        simpa using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_norm hf_nonneg).symm
      have hf_eLpNorm :
          eLpNorm f 1 μ = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := by
        simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm, ofReal_norm_eq_enorm]
          using hf_lintegral
      have hf_toReal :
          (eLpNorm f 1 μ).toReal = ∫ x, ‖f x‖ ∂μ := by
        have h_nonneg : 0 ≤ ∫ x, ‖f x‖ ∂μ :=
          integral_nonneg fun _ => norm_nonneg _
        have := congrArg ENNReal.toReal hf_eLpNorm
        simpa [h_nonneg, ENNReal.toReal_ofReal] using this
      -- Obtain the essential supremum bound for `g` with the precise constant.
      have hg_ne_top' : eLpNorm g ∞ μ ≠ ∞ := ne_of_lt hg_fin
      have hg_ne_top : eLpNormEssSup g μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hg_ne_top'
      set K := (eLpNorm g ∞ μ).toReal with hK
      have hK_nonneg : 0 ≤ K := by
        simp [K]
      have hK_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ K := by
        refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => g x)).mono ?_
        intro x hx
        have hx' : ENNReal.ofReal ‖g x‖ ≤ eLpNormEssSup g μ := by
          simpa [ofReal_norm_eq_enorm] using hx
        have := (ENNReal.ofReal_le_iff_le_toReal hg_ne_top).mp hx'
        simpa [K, eLpNorm, eLpNorm_exponent_top] using this
      -- Compare the product with the majorant `K * ‖f x‖`.
      have hf_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_int.aestronglyMeasurable.norm.mul hg_ae.norm)
      have h_mul_le :
          (fun x => ‖f x‖ * ‖g x‖) ≤ᵐ[μ] fun x => K * ‖f x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hf_nonneg' : 0 ≤ ‖f x‖ := norm_nonneg _
            have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * K :=
              (mul_le_mul_of_nonneg_left hx hf_nonneg' : _)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have h_mul_abs :
          ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ K * ‖f x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hf_nonneg' : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg' : 0 ≤ ‖g x‖ := norm_nonneg _
            have h_prod_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ :=
              mul_nonneg hf_nonneg' hg_nonneg'
            have h_rhs_nonneg : 0 ≤ K * ‖f x‖ := mul_nonneg hK_nonneg hf_nonneg'
            have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * K :=
              (mul_le_mul_of_nonneg_left hx hf_nonneg' : _)
            simpa [Real.norm_of_nonneg h_prod_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using this
      have h_majorant : Integrable (fun x => K * ‖f x‖) μ :=
        hf_norm.const_mul K
      have h_prod_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
        Integrable.mono' h_majorant hf_meas h_mul_abs
      have h_integral_le :=
        integral_mono_ae h_prod_int h_majorant h_mul_le
      have h_integral_const :
          ∫ x, K * ‖f x‖ ∂μ = K * ∫ x, ‖f x‖ ∂μ := by
        simpa [mul_comm] using
          integral_const_mul (μ := μ) (r := K) (f := fun x => ‖f x‖)
      have h_main :
          ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ K * ∫ x, ‖f x‖ ∂μ := by
        simpa [h_integral_const] using h_integral_le
      simpa [hf_toReal, K, mul_comm, mul_left_comm, mul_assoc] using h_main
  · rcases hpq with ⟨hp, hq⟩
    subst hp; subst hq
    -- Case `p = ∞`, `q = 1`
    have hg_int : Integrable g μ := by
      simpa [memLp_one_iff_integrable] using hg
    obtain ⟨hf_meas, hf_fin⟩ := hf
    have hf_bound : ∃ C, ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
      have hf_ne_top' : eLpNorm f ∞ μ ≠ ∞ := ne_of_lt hf_fin
      have hf_ne_top : eLpNormEssSup f μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hf_ne_top'
      refine ⟨(eLpNorm f ∞ μ).toReal, ?_⟩
      refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => f x)).mono ?_
      intro x hx
      have hx' : ENNReal.ofReal ‖f x‖ ≤ eLpNormEssSup f μ := by
        simpa [ofReal_norm_eq_enorm] using hx
      have := (ENNReal.ofReal_le_iff_le_toReal hf_ne_top).mp hx'
      simpa [eLpNorm, eLpNorm_exponent_top] using this
    have hf_ae : AEStronglyMeasurable f μ := hf_meas
    have :=
      holder_inequality_infty_one (μ := μ) (f := f) (g := g) hf_ae hf_bound hg_int
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hf_bound
      set C₀ := max C 0
      have hC₀_nonneg : 0 ≤ C₀ := le_max_right _ _
      have hC₀_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C₀ :=
        hC.mono fun x hx => le_max_of_le_left hx
      have hg_meas : AEStronglyMeasurable g μ := hg_int.aestronglyMeasurable
      have h_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_ae.norm.mul hg_meas.norm)
      have h_dom : ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ C₀ * ‖g x‖ :=
        hC₀_bound.mono fun x hx =>
          by
            have hf_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg : 0 ≤ ‖g x‖ := norm_nonneg _
            have h_prod_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ := mul_nonneg hf_nonneg hg_nonneg
            have h_rhs_nonneg : 0 ≤ C₀ * ‖g x‖ := mul_nonneg hC₀_nonneg hg_nonneg
            have h_mul_le : ‖f x‖ * ‖g x‖ ≤ C₀ * ‖g x‖ :=
              (mul_le_mul_of_nonneg_right hx hg_nonneg : _)
            simpa [Real.norm_of_nonneg h_prod_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using h_mul_le
      have h_majorant : Integrable (fun x => C₀ * ‖g x‖) μ :=
        hg_int.norm.const_mul C₀
      exact Integrable.mono' h_majorant h_meas h_dom
    · classical
      -- Express the L¹ norm of `g` via `eLpNorm`.
      have hg_norm : Integrable (fun x => ‖g x‖) μ := hg_int.norm
      have hg_nonneg : 0 ≤ᵐ[μ] fun x => ‖g x‖ :=
        Filter.Eventually.of_forall fun _ => norm_nonneg _
      have hg_lintegral :
          ∫⁻ x, ENNReal.ofReal (‖g x‖) ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ∂μ) := by
        simpa using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_norm hg_nonneg).symm
      have hg_eLpNorm :
          eLpNorm g 1 μ = ENNReal.ofReal (∫ x, ‖g x‖ ∂μ) := by
        simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm, ofReal_norm_eq_enorm]
          using hg_lintegral
      have hg_toReal :
          (eLpNorm g 1 μ).toReal = ∫ x, ‖g x‖ ∂μ := by
        have h_nonneg : 0 ≤ ∫ x, ‖g x‖ ∂μ :=
          integral_nonneg fun _ => norm_nonneg _
        have := congrArg ENNReal.toReal hg_eLpNorm
        simpa [h_nonneg, ENNReal.toReal_ofReal] using this
      -- Obtain the essential supremum bound for `f` with the precise constant.
      have hf_ne_top' : eLpNorm f ∞ μ ≠ ∞ := ne_of_lt hf_fin
      have hf_ne_top : eLpNormEssSup f μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hf_ne_top'
      set K := (eLpNorm f ∞ μ).toReal with hK
      have hK_nonneg : 0 ≤ K := by
        simp [K]
      have hK_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ K := by
        refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => f x)).mono ?_
        intro x hx
        have hx' : ENNReal.ofReal ‖f x‖ ≤ eLpNormEssSup f μ := by
          simpa [ofReal_norm_eq_enorm] using hx
        have := (ENNReal.ofReal_le_iff_le_toReal hf_ne_top).mp hx'
        simpa [K, eLpNorm, eLpNorm_exponent_top] using this
      -- Compare the product with the majorant `K * ‖g x‖`.
      have hg_meas : AEStronglyMeasurable g μ := hg_int.aestronglyMeasurable
      have h_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_ae.norm.mul hg_meas.norm)
      have h_mul_le :
          (fun x => ‖f x‖ * ‖g x‖) ≤ᵐ[μ] fun x => K * ‖g x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hg_nonneg' : 0 ≤ ‖g x‖ := norm_nonneg _
            have : ‖f x‖ * ‖g x‖ ≤ K * ‖g x‖ :=
              (mul_le_mul_of_nonneg_right hx hg_nonneg' : _)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have h_mul_abs :
          ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ K * ‖g x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hf_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg' : 0 ≤ ‖g x‖ := norm_nonneg _
            have h_prod_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ :=
              mul_nonneg hf_nonneg hg_nonneg'
            have h_rhs_nonneg : 0 ≤ K * ‖g x‖ :=
              mul_nonneg hK_nonneg hg_nonneg'
            have : ‖f x‖ * ‖g x‖ ≤ K * ‖g x‖ :=
              (mul_le_mul_of_nonneg_right hx hg_nonneg' : _)
            simpa [Real.norm_of_nonneg h_prod_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using this
      have h_majorant : Integrable (fun x => K * ‖g x‖) μ :=
        hg_norm.const_mul K
      have h_prod_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
        Integrable.mono' h_majorant h_meas h_mul_abs
      have h_integral_le :=
        integral_mono_ae h_prod_int h_majorant h_mul_le
      have h_integral_const :
          ∫ x, K * ‖g x‖ ∂μ = K * ∫ x, ‖g x‖ ∂μ := by
        simpa [mul_comm] using
          integral_const_mul (μ := μ) (r := K) (f := fun x => ‖g x‖)
      have h_main :
          ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ K * ∫ x, ‖g x‖ ∂μ := by
        simpa [h_integral_const] using h_integral_le
      simpa [hg_toReal, K, mul_comm, mul_left_comm, mul_assoc] using h_main
  · rcases hpq with ⟨hp, hp_top, hq, hq_top, hpq'⟩
    -- Case `1 < p, q < ∞`
    set pr := p.toReal with hpr
    set qr := q.toReal with hqr
    have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
    have hq_ne_top : q ≠ ∞ := ne_of_lt hq_top
    have hp_pos : 0 < p :=
      lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ 1 by simp) hp
    have hq_pos : 0 < q :=
      lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ 1 by simp) hq
    have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
    have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
    have hp_real_gt_one : 1 < pr := by
      have h₁ : (1 : ℝ≥0∞) ≠ ∞ := by simp
      have := (ENNReal.toReal_lt_toReal h₁ hp_ne_top).2 hp
      simpa [hpr] using this
    have hq_real_gt_one : 1 < qr := by
      have h₁ : (1 : ℝ≥0∞) ≠ ∞ := by simp
      have := (ENNReal.toReal_lt_toReal h₁ hq_ne_top).2 hq
      simpa [hqr] using this
    have pr_pos : 0 < pr := zero_lt_one.trans hp_real_gt_one
    have qr_pos : 0 < qr := zero_lt_one.trans hq_real_gt_one
    have pr_nonneg : 0 ≤ pr := pr_pos.le
    have qr_nonneg : 0 ≤ qr := qr_pos.le
    have hp_inv_ne_top : 1 / p ≠ ∞ := by
      simpa [one_div] using (ENNReal.inv_ne_top).2 hp_ne_zero
    have hq_inv_ne_top : 1 / q ≠ ∞ := by
      simpa [one_div] using (ENNReal.inv_ne_top).2 hq_ne_zero
    have hp_inv_toReal : (1 / p).toReal = 1 / pr := by
      simp [one_div, hpr, ENNReal.toReal_inv]
    have hq_inv_toReal : (1 / q).toReal = 1 / qr := by
      simp [one_div, hqr, ENNReal.toReal_inv]
    have hpq_real_sum : 1 / pr + 1 / qr = 1 := by
      have h := congrArg ENNReal.toReal hpq'
      have hsum_symm : (1 / p).toReal + (1 / q).toReal = (1 / p + 1 / q).toReal :=
        (ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top).symm
      have h_toReal_add : (1 / p).toReal + (1 / q).toReal = 1 :=
        hsum_symm.trans h
      simpa [hp_inv_toReal, hq_inv_toReal] using h_toReal_add
    have hpq_real_sum' : pr⁻¹ + qr⁻¹ = 1 := by
      simpa [one_div] using hpq_real_sum
    have hpq_real : pr.HolderConjugate qr :=
      (Real.holderConjugate_iff).2 ⟨hp_real_gt_one, hpq_real_sum'⟩
    have hp_ofReal : ENNReal.ofReal pr = p := by
      simp [hpr, hp_ne_top]
    have hq_ofReal : ENNReal.ofReal qr = q := by
      simp [hqr, hq_ne_top]
    have hf_norm : MemLp (fun x => ‖f x‖) p μ := hf.norm
    have hg_norm : MemLp (fun x => ‖g x‖) q μ := hg.norm
    have hf_norm_real : MemLp (fun x => ‖f x‖) (ENNReal.ofReal pr) μ := by
      simpa [hp_ofReal] using hf_norm
    have hg_norm_real : MemLp (fun x => ‖g x‖) (ENNReal.ofReal qr) μ := by
      simpa [hq_ofReal] using hg_norm
    have hf_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    have hg_nonneg : 0 ≤ᵐ[μ] fun x => ‖g x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    have hf_pow_integrable : Integrable (fun x => ‖f x‖ ^ pr) μ :=
      hf.integrable_norm_rpow hp_ne_zero hp_ne_top
    have hg_pow_integrable : Integrable (fun x => ‖g x‖ ^ qr) μ :=
      hg.integrable_norm_rpow hq_ne_zero hq_ne_top
    have hf_pow_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ ^ pr :=
      Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hg_pow_nonneg : 0 ≤ᵐ[μ] fun x => ‖g x‖ ^ qr :=
      Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _
    haveI : ENNReal.HolderConjugate p q :=
      ⟨by simpa [one_div] using hpq'⟩
    have h_prod_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ := by
      simpa [Pi.mul_apply] using
        (MemLp.integrable_mul (p := p) (q := q) hf_norm hg_norm)
    have hf_lintegral :
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ pr) ∂μ =
            ENNReal.ofReal (∫ x, ‖f x‖ ^ pr ∂μ) := by
      simpa using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_pow_integrable
            hf_pow_nonneg).symm
    have hg_lintegral :
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ qr) ∂μ =
            ENNReal.ofReal (∫ x, ‖g x‖ ^ qr ∂μ) := by
      simpa using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_pow_integrable
            hg_pow_nonneg).symm
    have hf_integral_eq :
        ∫⁻ x, ‖f x‖ₑ ^ pr ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ pr ∂μ) := by
      have h :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_pow_integrable
            hf_pow_nonneg).symm
      have hfun :
          (fun x => ENNReal.ofReal (‖f x‖ ^ pr)) = fun x => ‖f x‖ₑ ^ pr := by
        funext x
        simpa [ofReal_norm_eq_enorm]
          using (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) pr_nonneg).symm
      simpa [hfun] using h
    have hg_integral_eq :
        ∫⁻ x, ‖g x‖ₑ ^ qr ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ qr ∂μ) := by
      have h :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_pow_integrable
            hg_pow_nonneg).symm
      have hfun :
          (fun x => ENNReal.ofReal (‖g x‖ ^ qr)) = fun x => ‖g x‖ₑ ^ qr := by
        funext x
        simpa [ofReal_norm_eq_enorm]
          using (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) qr_nonneg).symm
      simpa [hfun] using h
    set Af := ∫⁻ x, ‖f x‖ₑ ^ pr ∂μ with hAf
    set Ag := ∫⁻ x, ‖g x‖ₑ ^ qr ∂μ with hAg
    have hAf_eq : Af = ENNReal.ofReal (∫ x, ‖f x‖ ^ pr ∂μ) := by
      simpa [hAf] using hf_integral_eq
    have hAg_eq : Ag = ENNReal.ofReal (∫ x, ‖g x‖ ^ qr ∂μ) := by
      simpa [hAg] using hg_integral_eq
    have hAf_ne_top : Af ≠ ∞ := by
      simp [hAf_eq]
    have hAg_ne_top : Ag ≠ ∞ := by
      simp [hAg_eq]
    have hf_integral_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ pr ∂μ :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hAf_toReal : Af.toReal = ∫ x, ‖f x‖ ^ pr ∂μ := by
      have := congrArg ENNReal.toReal hAf_eq
      simpa [hf_integral_nonneg, ENNReal.toReal_ofReal] using this
    have hg_integral_nonneg : 0 ≤ ∫ x, ‖g x‖ ^ qr ∂μ :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hAg_toReal : Ag.toReal = ∫ x, ‖g x‖ ^ qr ∂μ := by
      have := congrArg ENNReal.toReal hAg_eq
      simpa [hg_integral_nonneg, ENNReal.toReal_ofReal] using this
    have hf_norm_rpow : (∫ x, ‖f x‖ ^ pr ∂μ) ^ (1 / pr) =
        (eLpNorm f p μ).toReal := by
      have hf_eLpNorm :=
        eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := f) hp_ne_zero hp_ne_top
      have h := congrArg ENNReal.toReal hf_eLpNorm
      have h_power : (Af ^ (1 / pr)).toReal = Af.toReal ^ (1 / pr) := by
        simpa using (ENNReal.toReal_rpow Af (1 / pr)).symm
      have h_main : (Af ^ (1 / pr)).toReal = (eLpNorm f p μ).toReal := by
        simpa [hAf] using h.symm
      have h_lhs : (Af ^ (1 / pr)).toReal =
          (∫ x, ‖f x‖ ^ pr ∂μ) ^ (1 / pr) := by
        simpa [hAf_toReal] using h_power
      exact h_lhs.symm.trans h_main
    have hg_norm_rpow : (∫ x, ‖g x‖ ^ qr ∂μ) ^ (1 / qr) =
        (eLpNorm g q μ).toReal := by
      have hg_eLpNorm :=
        eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := g) hq_ne_zero hq_ne_top
      have h := congrArg ENNReal.toReal hg_eLpNorm
      have h_power : (Ag ^ (1 / qr)).toReal = Ag.toReal ^ (1 / qr) := by
        simpa using (ENNReal.toReal_rpow Ag (1 / qr)).symm
      have h_main : (Ag ^ (1 / qr)).toReal = (eLpNorm g q μ).toReal := by
        simpa [hAg] using h.symm
      have h_lhs : (Ag ^ (1 / qr)).toReal =
          (∫ x, ‖g x‖ ^ qr ∂μ) ^ (1 / qr) := by
        simpa [hAg_toReal] using h_power
      exact h_lhs.symm.trans h_main
    have hf_norm_rpow_inv : (∫ x, ‖f x‖ ^ pr ∂μ) ^ pr⁻¹ =
        (eLpNorm f p μ).toReal := by
      simpa [one_div] using hf_norm_rpow
    have hg_norm_rpow_inv : (∫ x, ‖g x‖ ^ qr ∂μ) ^ qr⁻¹ =
        (eLpNorm g q μ).toReal := by
      simpa [one_div] using hg_norm_rpow
    have h_main :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := pr) (q := qr)
        hpq_real hf_nonneg hg_nonneg hf_norm_real hg_norm_real
    have h_final :
        ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
          (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
      simpa [hf_norm_rpow_inv, hg_norm_rpow_inv] using h_main
    exact ⟨h_prod_int, h_final⟩

/--
**Hölder's inequality (ENNReal version).**

This version assumes we are in the genuine Hölder regime `1 < p, q < ∞` and works with
lintegrals of non-negative extended real-valued functions.
-/
theorem holder_inequality_ennreal
    (p q : ℝ≥0∞) (hpq : IsConjugateExponent p q) (hp : 1 < p) (hp_top : p < ∞)
    (f : α → ℝ≥0∞) (g : α → ℝ≥0∞) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ x, f x * g x ∂μ ≤ (∫⁻ x, f x ^ p.toReal ∂μ) ^ (1 / p.toReal) *
      (∫⁻ x, g x ^ q.toReal ∂μ) ^ (1 / q.toReal) := by
  classical
  rcases hpq with h|h|h
  · rcases h with ⟨hp_eq, _⟩
    have : ¬1 < (1 : ℝ≥0∞) := by simp
    exact (this (by simp [hp_eq] at hp)).elim
  · rcases h with ⟨hp_eq, _⟩
    have : ¬((∞ : ℝ≥0∞) < ∞) := by simp
    exact (this (by simp [hp_eq] at hp_top)).elim
  rcases h with ⟨hp', hp'_top, hq, hq_top, hpq_sum⟩
  have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
  have hq_ne_top : q ≠ ∞ := ne_of_lt hq_top
  have hp_pos' : 0 < p := lt_of_le_of_lt (by simp : (0 : ℝ≥0∞) ≤ 1) hp
  have hq_pos' : 0 < q := lt_of_le_of_lt (by simp : (0 : ℝ≥0∞) ≤ 1) hq
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos'
  have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos'
  set pr := p.toReal with hpr
  set qr := q.toReal with hqr
  have hp_real_gt_one : 1 < pr := by
    have h_one_ne_top : (1 : ℝ≥0∞) ≠ ∞ := by simp
    have := (ENNReal.toReal_lt_toReal h_one_ne_top hp_ne_top).2 hp
    simpa [hpr] using this
  have hq_real_gt_one : 1 < qr := by
    have h_one_ne_top : (1 : ℝ≥0∞) ≠ ∞ := by simp
    have := (ENNReal.toReal_lt_toReal h_one_ne_top hq_ne_top).2 hq
    simpa [hqr] using this
  have hp_inv_ne_top : 1 / p ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top).2 hp_ne_zero
  have hq_inv_ne_top : 1 / q ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top).2 hq_ne_zero
  have hp_inv_toReal : (1 / p).toReal = 1 / pr := by
    simp [one_div, hpr, ENNReal.toReal_inv, hp_ne_zero, hp_ne_top]
  have hq_inv_toReal : (1 / q).toReal = 1 / qr := by
    simp [one_div, hqr, ENNReal.toReal_inv, hq_ne_zero, hq_ne_top]
  have hpq_real_sum : pr⁻¹ + qr⁻¹ = 1 := by
    have h := congrArg ENNReal.toReal hpq_sum
    have hsum := ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top
    have h_one : (1 : ℝ≥0∞).toReal = 1 := by simp
    have h_toReal_sum : (1 / p + 1 / q).toReal = 1 := by
      simpa [hsum, h_one] using h
    have h_toReal_sum' : 1 / pr + 1 / qr = (1 / p + 1 / q).toReal := by
      simpa [one_div, hp_inv_toReal, hq_inv_toReal] using hsum.symm
    have : 1 / pr + 1 / qr = 1 := h_toReal_sum'.trans h_toReal_sum
    simpa [one_div] using this
  have hpq_real : pr.HolderConjugate qr :=
    (Real.holderConjugate_iff).2 ⟨hp_real_gt_one, hpq_real_sum⟩
  have h_holder :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ) (p := pr) (q := qr)
      hpq_real hf hg
  simpa [hpr, hqr] using h_holder

/--
**Hölder's inequality with explicit exponents.**

Version where the conjugate relation is given as a hypothesis rather than
using the IsConjugateExponent predicate.
-/
theorem holder_inequality_explicit
    (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hp_top : p ≠ ∞ ∨ q = 1)
    (hq_top : q ≠ ∞ ∨ p = 1)
    (hpq : 1 / p + 1 / q = 1)
    (f : α → E) (g : α → F)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (fun x => ‖f x‖ * ‖g x‖) μ ∧
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  classical
  have h_inv_q : 1 / q = 1 - 1 / p :=
    ENNReal.eq_sub_of_add_eq' (by simp : (1 : ℝ≥0∞) ≠ ∞)
      (by simpa [add_comm] using hpq)
  have h_inv_p : 1 / p = 1 - 1 / q :=
    ENNReal.eq_sub_of_add_eq' (by simp : (1 : ℝ≥0∞) ≠ ∞) hpq
  by_cases hp_one : p = 1
  · have hq_inv_zero : q⁻¹ = 0 := by
      have : 1 / q = 0 := by simpa [hp_one] using h_inv_q
      simpa [one_div] using this
    have hq_eq_top : q = ∞ := ENNReal.inv_eq_zero.mp hq_inv_zero
    have h_conj : IsConjugateExponent p q := Or.inl ⟨hp_one, hq_eq_top⟩
    exact holder_inequality (μ := μ) (p := p) (q := q) h_conj f g hf hg
  have hp_ne_one : p ≠ 1 := hp_one
  by_cases hq_one : q = 1
  · have hp_inv_zero : p⁻¹ = 0 := by
      have : 1 / p = 0 := by simpa [hq_one] using h_inv_p
      simpa [one_div] using this
    have hp_eq_top : p = ∞ := ENNReal.inv_eq_zero.mp hp_inv_zero
    have h_conj : IsConjugateExponent p q := Or.inr <| Or.inl ⟨hp_eq_top, hq_one⟩
    exact holder_inequality (μ := μ) (p := p) (q := q) h_conj f g hf hg
  have hq_ne_one : q ≠ 1 := hq_one
  have hp_ne_top : p ≠ ∞ :=
    hp_top.elim id fun h => False.elim (hq_ne_one h)
  have hq_ne_top : q ≠ ∞ :=
    hq_top.elim id fun h => False.elim (hp_ne_one h)
  have hp_lt_one : 1 < p := lt_of_le_of_ne hp (by simpa [eq_comm] using hp_ne_one)
  have hq_lt_one : 1 < q := lt_of_le_of_ne hq (by simpa [eq_comm] using hq_ne_one)
  have hp_lt_top : p < ∞ := lt_of_le_of_ne le_top (by simpa [eq_comm] using hp_ne_top)
  have hq_lt_top : q < ∞ := lt_of_le_of_ne le_top (by simpa [eq_comm] using hq_ne_top)
  have h_conj : IsConjugateExponent p q :=
    Or.inr <| Or.inr ⟨hp_lt_one, hp_lt_top, hq_lt_one, hq_lt_top, hpq⟩
  exact holder_inequality (μ := μ) (p := p) (q := q) h_conj f g hf hg

/--
**Hölder's inequality phrased with extended nonnegative reals.**

This version allows the exponents `p` and `q` to take the value `∞` and expresses the
conclusion directly on lintegrals of norms.
-/
lemma holder_inequality_lintegral_norm
    {μ : Measure α} {f g : α → ℂ} {p q : ℝ≥0∞} {α : Type*} [MeasurableSpace α]
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 1 / p + 1 / q = 1)
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ∫⁻ x, (‖f x‖ₑ * ‖g x‖ₑ) ∂μ ≤
      eLpNorm f p μ * eLpNorm g q μ := by
  classical
  -- Deduce the auxiliary hypotheses required by the explicit Hölder inequality.
  have hp_top : p ≠ ∞ ∨ q = 1 := by
    by_cases hp_inf : p = ∞
    · right
      have h_inv : 1 / q = 1 := by
        simpa [hp_inf, one_div, ENNReal.inv_eq_zero] using hpq
      simpa [one_div] using h_inv
    · exact Or.inl hp_inf
  have hq_top : q ≠ ∞ ∨ p = 1 := by
    by_cases hq_inf : q = ∞
    · right
      have h_inv : 1 / p = 1 := by
        simpa [hq_inf, one_div, ENNReal.inv_eq_zero, add_comm] using hpq
      simpa [one_div] using h_inv
    · exact Or.inl hq_inf
  -- Apply the explicit Hölder inequality for Bochner integrals.
  obtain ⟨h_int, h_le⟩ :=
    holder_inequality_explicit (μ := μ) (p := p) (q := q)
      hp hq hp_top hq_top hpq f g hf hg
  -- Express the lintegral in terms of the Bochner integral.
  have h_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ * ‖g x‖ :=
    Filter.Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h_lintegral :
      ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ =
        ENNReal.ofReal (∫ x, ‖f x‖ * ‖g x‖ ∂μ) := by
    have h_ofReal :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg).symm
    have h_integrand :
        (fun x => ENNReal.ofReal (‖f x‖ * ‖g x‖)) =
          fun x => ‖f x‖ₑ * ‖g x‖ₑ := by
      ext x
      simp [ENNReal.ofReal_mul, ofReal_norm_eq_enorm, norm_nonneg]
    simpa [h_integrand]
      using h_ofReal
  -- Convert the real inequality to the desired ENNReal inequality.
  have h_ofReal_le :
      ENNReal.ofReal (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤
        ENNReal.ofReal ((eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal) := by
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).2 h_le
  have hf_fin : eLpNorm f p μ ≠ ∞ := hf.eLpNorm_ne_top
  have hg_fin : eLpNorm g q μ ≠ ∞ := hg.eLpNorm_ne_top
  have h_rhs :
      ENNReal.ofReal ((eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal)
        = eLpNorm f p μ * eLpNorm g q μ := by
    have hf_nonneg : 0 ≤ (eLpNorm f p μ).toReal := ENNReal.toReal_nonneg
    have hg_nonneg : 0 ≤ (eLpNorm g q μ).toReal := ENNReal.toReal_nonneg
    simp [ENNReal.ofReal_mul, hf_nonneg, hg_nonneg,
      ENNReal.ofReal_toReal hf_fin, ENNReal.ofReal_toReal hg_fin]
  calc
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ
        = ENNReal.ofReal (∫ x, ‖f x‖ * ‖g x‖ ∂μ) := h_lintegral
    _ ≤ ENNReal.ofReal ((eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal) := h_ofReal_le
    _ = eLpNorm f p μ * eLpNorm g q μ := h_rhs

end HolderGeneral

section HolderApplications

/--
**Hölder's inequality for L^p membership.**

If f ∈ L^p and g ∈ L^q with conjugate exponents, then fg ∈ L^1.
-/
theorem memLp_mul_of_memLp_conjugate
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f : α → ℝ) (g : α → ℝ)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (fun x => f x * g x) μ := by
  classical
  obtain ⟨h_int, -⟩ :=
    holder_inequality (μ := μ) (p := p) (q := q) hpq f g hf hg
  refine ⟨hf.aestronglyMeasurable.mul hg.aestronglyMeasurable, ?_⟩
  have h_finite : HasFiniteIntegral (fun x => ‖f x‖ * ‖g x‖) μ :=
    h_int.hasFiniteIntegral
  have h_finite' : HasFiniteIntegral (fun x => f x * g x) μ :=
    h_finite.congr' <|
      (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs, abs_mul])
  simpa using h_finite'

/--
**Hölder's inequality for convolution integrands.**

Specialized version useful for proving Young's inequality.
-/
theorem holder_inequality_convolution
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f g : G → ℝ)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ)
    (x : G) :
    Integrable (fun y => |f (x - y)| * |g y|) μ ∧
    ∫ y, |f (x - y)| * |g y| ∂μ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  classical
  -- Translation and negation of the second argument.
  have h_sub : MeasurePreserving (fun y : G => y - x) μ μ :=
    ⟨Measurable.sub measurable_id (measurable_const (a := x)),
      by simp [sub_eq_add_neg, map_add_right_eq_self]⟩
  have h_neg : MeasurePreserving (fun y : G => -y) μ μ :=
    Measure.measurePreserving_neg μ
  have h_comp : MeasurePreserving (fun y : G => -(y - x)) μ μ :=
    h_neg.comp h_sub
  -- Precomposition keeps `MemLp` under this measure-preserving map.
  have hf_shift : MemLp (fun y => f (-(y - x))) p μ :=
    hf.comp_measurePreserving h_comp
  -- Apply Hölder's inequality to the shifted functions.
  obtain ⟨h_int, h_bound⟩ :=
    holder_inequality (μ := μ) (p := p) (q := q) hpq
      (fun y => f (-(y - x))) g hf_shift hg
  -- Translation preserves the Lᵖ norm.
  have hf_norm_eq :
      eLpNorm (fun y => f (-(y - x))) p μ = eLpNorm f p μ :=
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable h_comp
  -- Prepare an a.e. equality between the absolute-value products.
  have h_abs_eq :
      (fun y => |f (-(y - x))| * |g y|) =ᵐ[μ]
        fun y => |f (x - y)| * |g y| :=
    Filter.Eventually.of_forall fun y => by simp [neg_sub]
  refine ⟨?_, ?_⟩
  · -- Integrability statement passes along the equality.
    have h_int_abs :
        Integrable (fun y => |f (-(y - x))| * |g y|) μ := by
      simpa [Real.norm_eq_abs] using h_int
    exact Integrable.congr h_int_abs h_abs_eq
  · -- Rewrite the inequality using the identified norm equality.
    have h_bound' : ∫ y, ‖f (-(y - x))‖ * ‖g y‖ ∂μ ≤
        (eLpNorm (fun y => f (-(y - x))) p μ).toReal * (eLpNorm g q μ).toReal := by
      simpa [Real.norm_eq_abs] using h_bound
    calc ∫ y, |f (x - y)| * |g y| ∂μ
        = ∫ y, |f (-(y - x))| * |g y| ∂μ := (integral_congr_ae h_abs_eq).symm
      _ = ∫ y, ‖f (-(y - x))‖ * ‖g y‖ ∂μ := by simp [Real.norm_eq_abs]
      _ ≤ (eLpNorm (fun y => f (-(y - x))) p μ).toReal * (eLpNorm g q μ).toReal := h_bound'
      _ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by rw [hf_norm_eq]

lemma reverse_holder_witness_memLp
    (p q : ℝ≥0∞)
    (hp : 1 < p) (hp_top : p < ∞)
    (hpq : IsConjugateExponent p q)
    (f : α → ℝ)
    (hf : MemLp f p μ)
    [IsFiniteMeasure μ] :
    MemLp (fun x => ‖f x‖ ^ (p.toReal - 1)) q μ := by
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
  have hp_pos : 0 < p := zero_lt_one.trans hp
  have hq_pos : 0 < q := zero_lt_one.trans hq
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
  have pr_pos : 0 < pr := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have qr_pos : 0 < qr := ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have pr_nonneg : 0 ≤ pr := pr_pos.le
  have qr_nonneg : 0 ≤ qr := qr_pos.le
  have hp_real_gt_one : 1 < pr := by
    have h_one_ne_top : (1 : ℝ≥0∞) ≠ ∞ := by simp
    have := (ENNReal.toReal_lt_toReal h_one_ne_top hp_ne_top).2 hp
    simpa [hpr] using this
  have hq_real_gt_one : 1 < qr := by
    have h_one_ne_top : (1 : ℝ≥0∞) ≠ ∞ := by simp
    have := (ENNReal.toReal_lt_toReal h_one_ne_top hq_ne_top).2 hq
    simpa [hqr] using this
  have expo_nonneg : 0 ≤ pr - 1 := sub_nonneg.mpr hp_real_gt_one.le
  have hp_inv_ne_top : 1 / p ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top).2 hp_ne_zero
  have hq_inv_ne_top : 1 / q ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top).2 hq_ne_zero
  have hp_inv_toReal : (1 / p).toReal = 1 / pr := by
    simp [one_div, hpr, ENNReal.toReal_inv, hp_ne_zero, hp_ne_top]
  have hq_inv_toReal : (1 / q).toReal = 1 / qr := by
    simp [one_div, hqr, ENNReal.toReal_inv, hq_ne_zero, hq_ne_top]
  have hpq_real_sum : 1 / pr + 1 / qr = 1 := by
    have h := congrArg ENNReal.toReal hpq_sum
    have hsum_symm :=
      (ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top).symm
    have h_toReal_add :
        (1 / p).toReal + (1 / q).toReal = 1 := by
      rw [hsum_symm, h]
      simp
    simpa [hp_inv_toReal, hq_inv_toReal] using h_toReal_add
  have pr_ne_zero : pr ≠ 0 := ne_of_gt pr_pos
  have qr_ne_zero : qr ≠ 0 := ne_of_gt qr_pos
  have h_mul : pr * qr = pr + qr := by
    have h := hpq_real_sum
    field_simp [pr_ne_zero, qr_ne_zero] at h
    simpa [mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc] using h.symm
  have h_exponent : (pr - 1) * qr = pr := by
    calc
      (pr - 1) * qr = pr * qr - qr := by ring
      _ = (pr + qr) - qr := by simp [h_mul]
      _ = pr := by simp
  have h_ratio : pr / qr = pr - 1 := by
    have h_div : pr - 1 = pr / qr :=
      (eq_div_iff_mul_eq qr_ne_zero).2 <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_exponent
    simpa using h_div.symm
  set pq := p / q with hpq_def
  have hpq_ne_zero : pq ≠ 0 := by
    intro hpq_zero
    have : p / q = 0 := by simpa [hpq_def] using hpq_zero
    have hcases : p = 0 ∨ q = ∞ := (ENNReal.div_eq_zero_iff).mp this
    cases hcases with
    | inl hp_zero => exact hp_ne_zero hp_zero
    | inr hq_top' => exact hq_ne_top hq_top'
  have hpq_ne_top : pq ≠ ∞ :=
    ENNReal.div_ne_top hp_ne_top hq_ne_zero
  have hpq_toReal : pq.toReal = pr - 1 := by
    have h_toReal : pq.toReal = pr / qr := by
      simp [hpq_def, hpr, hqr, ENNReal.toReal_div]
    simpa [h_ratio] using h_toReal
  have h_ratio' : pr / (pr - 1) = qr := by
    have hsub : pr - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp_real_gt_one)
    have := congrArg (fun t : ℝ => t / (pr - 1)) h_exponent
    simpa [hsub, mul_comm, mul_left_comm, mul_assoc, div_mul_eq_mul_div, mul_div_cancel_left,
      div_eq_mul_inv] using this.symm
  have hq_mul : q * (p / q) = p := ENNReal.mul_div_cancel hq_ne_zero hq_ne_top
  have hpq_div : p / pq = q := by
    calc
      p / pq = p / (p / q) := by simp [hpq_def]
      _ = (q * (p / q)) / (p / q) := by simp [hpq_def, hq_mul]
      _ = q := by
        have := ENNReal.mul_div_mul_right (a := q) (b := 1) (c := pq) hpq_ne_zero hpq_ne_top
        simpa [hpq_def] using this
  have h_mem :
      MemLp (fun x => ‖f x‖ ^ (pr - 1)) q μ := by
    have h_base :=
      (memLp_norm_rpow_iff (μ := μ) (p := p) (q := pq)
        hf.aestronglyMeasurable hpq_ne_zero hpq_ne_top).2 hf
    simpa [Real.norm_eq_abs, ← hpq_def, hpq_toReal, hpq_div, ← hpr, ← hqr, h_ratio] using h_base
  exact h_mem

lemma reverse_holder_integral_eq
    (p q : ℝ≥0∞)
    (hp : 1 < p) (hp_top : p < ∞)
    (hpq : IsConjugateExponent p q)
    (f : α → ℝ)
    (hf : MemLp f p μ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    [IsFiniteMeasure μ] :
    ∫ x, f x * (‖f x‖ ^ (p.toReal - 1)) ∂μ = (eLpNorm f p μ).toReal ^ p.toReal := by
  classical
  set pr := p.toReal with hpr
  have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
  have hp_pos : 0 < p := zero_lt_one.trans hp
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have pr_pos : 0 < pr := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have pr_ne_zero : pr ≠ 0 := ne_of_gt pr_pos
  have pr_nonneg : 0 ≤ pr := pr_pos.le
  set g₀ := fun x => ‖f x‖ ^ (pr - 1) with hg₀
  have hg_mem_aux :=
    reverse_holder_witness_memLp (p := p) (q := q) hp hp_top hpq f hf
  have hg_mem : MemLp g₀ q μ := by simpa [g₀, hpr] using hg_mem_aux
  have h_integrand_eq :
      (fun x => f x * g₀ x) =ᵐ[μ] fun x => ‖f x‖ ^ pr := by
    refine hf_pos.mono ?_
    intro x hx
    have hnorm : ‖f x‖ = f x := by
      simp [Real.norm_eq_abs, abs_of_pos hx]
    have hnorm_pos : 0 < ‖f x‖ := by simpa [hnorm]
    have hsum : 1 + (pr - 1) = pr := by ring
    calc
      f x * g₀ x = f x * (‖f x‖ ^ (pr - 1)) := by simp [g₀]
      _ = ‖f x‖ * (‖f x‖ ^ (pr - 1)) := by simp [hnorm]
      _ = ‖f x‖ ^ (1 : ℝ) * (‖f x‖ ^ (pr - 1)) := by simp [Real.rpow_one]
      _ = ‖f x‖ ^ pr := by
        simpa [hsum] using (Real.rpow_add hnorm_pos 1 (pr - 1)).symm
  have h_integral_eq :
      ∫ x, f x * g₀ x ∂μ = ∫ x, ‖f x‖ ^ pr ∂μ :=
    integral_congr_ae h_integrand_eq
  set A := ∫ x, ‖f x‖ ^ pr ∂μ with hA
  have hA_nonneg : 0 ≤ A :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  set norm := (eLpNorm f p μ).toReal with hnorm
  have norm_nonneg : 0 ≤ norm := by
    simp [norm]
  have h_eLpNorm :
      eLpNorm f p μ = ENNReal.ofReal (A ^ pr⁻¹) := by
    have :=
      MemLp.eLpNorm_eq_integral_rpow_norm (μ := μ) (f := f) hp_ne_zero hp_ne_top hf
    simpa [hA, hpr] using this
  have h_norm_eq : norm = A ^ pr⁻¹ := by
    have h := congrArg ENNReal.toReal h_eLpNorm
    have hA_pow_nonneg : 0 ≤ A ^ pr⁻¹ := Real.rpow_nonneg hA_nonneg _
    have h_toReal : (ENNReal.ofReal (A ^ pr⁻¹)).toReal = A ^ pr⁻¹ :=
      by simp [hA_pow_nonneg]
    simpa [norm, h_toReal] using h
  have hpow : (A ^ pr⁻¹) ^ pr = A := by
    have hmul : pr⁻¹ * pr = 1 := by
      field_simp [pr_ne_zero]
    have hpow_aux := Real.rpow_mul hA_nonneg pr⁻¹ pr
    have hpow_aux' : A = (A ^ pr⁻¹) ^ pr := by
      simpa [hmul, Real.rpow_one] using hpow_aux
    exact hpow_aux'.symm
  have h_norm_pow : norm ^ pr = A := by
    simpa [norm, h_norm_eq] using hpow
  calc
    ∫ x, f x * (‖f x‖ ^ (p.toReal - 1)) ∂μ
        = A := by simpa [g₀, hA, hpr] using h_integral_eq
    _ = (eLpNorm f p μ).toReal ^ p.toReal := by
      simpa [norm, hA, hpr] using h_norm_pow.symm

/--
**Reverse Hölder inequality.**

Under certain conditions, a reverse inequality holds.
-/
theorem reverse_holder_inequality
    (p q : ℝ≥0∞)
    (hp : 1 < p) (hp_top : p < ∞)
    (hpq : IsConjugateExponent p q)
    (f : α → ℝ)
    (hf : MemLp f p μ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    [IsFiniteMeasure μ] :
    ∃ g, MemLp g q μ ∧
      (∫ x, f x * g x ∂μ) = (eLpNorm f p μ).toReal := by
  classical
  set norm := (eLpNorm f p μ).toReal with hnorm_def
  have norm_nonneg : 0 ≤ norm := by simp [norm, hnorm_def]
  let g₀ : α → ℝ := fun x => ‖f x‖ ^ (p.toReal - 1)
  have hg₀_mem : MemLp g₀ q μ := by
    simpa [g₀] using
      reverse_holder_witness_memLp (p := p) (q := q) hp hp_top hpq f hf
  have h_integral_base :
      ∫ x, f x * g₀ x ∂μ = norm ^ p.toReal := by
    simpa [g₀, norm, hnorm_def] using
      reverse_holder_integral_eq (p := p) (q := q) hp hp_top hpq f hf hf_pos
  by_cases hnorm_zero : norm = 0
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · simp
    · simp [norm, hnorm_def, hnorm_zero]
  · have norm_pos : 0 < norm := lt_of_le_of_ne norm_nonneg (by simpa [eq_comm] using hnorm_zero)
    let c : ℝ := norm ^ (1 - p.toReal)
    have hc_nonneg : 0 ≤ c := Real.rpow_nonneg norm_nonneg _
    let g : α → ℝ := fun x => c * g₀ x
    have hg_mem : MemLp g q μ := by
      simpa [g] using hg₀_mem.const_mul c
    have h_integral_const :
        ∫ x, f x * (‖f x‖ ^ (p.toReal - 1) * c) ∂μ
          = c * (∫ x, f x * g₀ x ∂μ) := by
      simpa [g₀, c, mul_comm, mul_left_comm, mul_assoc, Real.norm_eq_abs]
        using (integral_const_mul (μ := μ) (r := c) (f := fun x => f x * g₀ x))
    have h_integral_const' :
        ∫ x, f x * (‖f x‖ ^ (p.toReal - 1) * c) ∂μ
          = c * (norm ^ p.toReal) := by
      simpa [h_integral_base] using h_integral_const
    have h_integral : ∫ x, f x * g x ∂μ = c * (norm ^ p.toReal) := by
      simpa [g, g₀, c, mul_comm, mul_left_comm, mul_assoc]
        using h_integral_const'
    have h_pow : c * (norm ^ p.toReal) = norm := by
      have h := (Real.rpow_add norm_pos (1 - p.toReal) (p.toReal)).symm
      have h_exponent : (1 - p.toReal) + p.toReal = 1 := by ring
      simpa [g₀, c, h_exponent, Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using h
    refine ⟨g, hg_mem, ?_⟩
    simp [h_integral, h_pow]

end HolderApplications

section HolderNormalized

/--
**Hölder's inequality for normalized functions.**

If ‖f‖_p = ‖g‖_q = 1, then ∫ |f · g| ≤ 1.
-/
theorem holder_inequality_normalized
    (p q : ℝ≥0∞) (hpq : IsConjugateExponent p q) (f : α → ℝ) (g : α → ℝ) (hf : MemLp f p μ)
    (hg : MemLp g q μ) (hf_norm : eLpNorm f p μ = 1) (hg_norm : eLpNorm g q μ = 1) :
    ∫ x, |f x * g x| ∂μ ≤ 1 := by
  classical
  obtain ⟨-, h_bound⟩ :=
    holder_inequality (μ := μ) (p := p) (q := q) hpq f g hf hg
  have h_abs_eq :
      (fun x => |f x * g x|) =ᵐ[μ] fun x => ‖f x‖ * ‖g x‖ :=
    Filter.Eventually.of_forall fun x => by
      simp [Real.norm_eq_abs, abs_mul, mul_comm, mul_left_comm, mul_assoc]
  have h_integral_eq :
      ∫ x, |f x * g x| ∂μ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ :=
    integral_congr_ae h_abs_eq
  have hf_norm_toReal : (eLpNorm f p μ).toReal = 1 := by
    simp [hf_norm]
  have hg_norm_toReal : (eLpNorm g q μ).toReal = 1 := by
    simp [hg_norm]
  calc
    ∫ x, |f x * g x| ∂μ
        = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := h_integral_eq
    _ ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := h_bound
    _ = 1 * 1 := by simp [hf_norm_toReal, hg_norm_toReal]
    _ = 1 := by simp

lemma eLpNorm_toReal_pos_of_ae_pos
    (p : ℝ≥0∞) (hp : 1 < p) (f : α → ℝ) (hf : MemLp f p μ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hμ_pos : μ Set.univ ≠ 0) :
    0 < (eLpNorm f p μ).toReal := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    exact ne_of_gt <| (zero_lt_one.trans hp)
  have h_nonneg : 0 ≤ (eLpNorm f p μ).toReal := ENNReal.toReal_nonneg
  have h_ne : (eLpNorm f p μ).toReal ≠ 0 := by
    intro hzero
    have hnorm_ne_top : eLpNorm f p μ ≠ ∞ := ne_of_lt hf.2
    have hzero_cases := (ENNReal.toReal_eq_zero_iff (eLpNorm f p μ)).mp hzero
    have hnorm_zero : eLpNorm f p μ = 0 := by
      rcases hzero_cases with hzero' | htop
      · exact hzero'
      · exact (hnorm_ne_top htop).elim
    have hf_zero : f =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff (μ := μ) (f := f) (p := p) hf.1 hp_ne_zero).1 hnorm_zero
    have hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0 :=
      hf_pos.mono fun x hx => ne_of_gt hx
    have hf_false : (∀ᵐ x ∂μ, False) :=
      (hf_ne_zero.and hf_zero).mono fun x hx => (hx.1 hx.2)
    have hf_false' : μ Set.univ = 0 := by
      have : μ {x | ¬False} = 0 := ae_iff.mp hf_false
      simp only [not_false_eq_true, Set.setOf_true] at this
      exact this
    exact (hμ_pos hf_false')
  exact lt_of_le_of_ne h_nonneg (by simpa [eq_comm] using h_ne)

end HolderNormalized

theorem holder_integral_norm_mul_le
    [SFinite μ]
    {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 1 / p + 1 / q = 1)
    (f g : α → E)
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  classical
  -- One of `p`, `q` must be finite unless the other exponent equals `1`.
  have hp_top : p ≠ ∞ ∨ q = 1 := by
    by_cases hp_inf : p = ∞
    · have h_inv : 1 / q = 1 := by simpa [hp_inf, one_div] using hpq
      have hq_eq_one : q = 1 := by
        have := congrArg (fun x : ℝ≥0∞ => x⁻¹) h_inv
        simpa using this
      exact Or.inr hq_eq_one
    · exact Or.inl hp_inf
  have hq_top : q ≠ ∞ ∨ p = 1 := by
    by_cases hq_inf : q = ∞
    · have h_inv : 1 / p = 1 := by simpa [hq_inf, one_div] using hpq
      have hp_eq_one : p = 1 := by
        have := congrArg (fun x : ℝ≥0∞ => x⁻¹) h_inv
        simpa using this
      exact Or.inr hp_eq_one
    · exact Or.inl hq_inf
  -- Apply the explicit Hölder inequality with these structural facts.
  obtain ⟨_, h_bound⟩ :=
    holder_inequality_explicit
      (μ := μ) (p := p) (q := q)
      hp hq hp_top hq_top hpq f g hf hg
  exact h_bound
