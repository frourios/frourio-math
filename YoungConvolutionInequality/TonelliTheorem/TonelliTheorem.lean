import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import YoungConvolutionInequality.FubiniSection.FubiniSection
import YoungConvolutionInequality.HolderInequality.HolderInequalityCore

/-!
# Tonelli's Theorem for Convolution Kernels

This file provides the necessary Tonelli/Fubini theorem statements and signatures
required for implementing `integrable_norm_convolution_kernel_section`.

The key challenge in `integrable_norm_convolution_kernel_section` is going from
a.e. integrability to pointwise integrability. This file provides the foundational
theorems needed to bridge this gap.

## Main Results

- `tonelli_nonneg_section`: Tonelli's theorem for nonnegative functions
- `lintegral_prod_eq_lintegral_iterated`: Explicit form of Fubini/Tonelli
- `ae_integrable_from_product_integrable`: Extract a.e. integrability from product
- `integrable_section_at_point_of_continuous`: Conditional version using continuity
-/

open MeasureTheory
open scoped ENNReal

variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}

namespace MeasureTheory

section TonelliForConvolution

/-! ## Tonelli's Theorem for Nonnegative Functions

These are the core statements of Tonelli's theorem that we need for the convolution case.
-/

variable [SFinite μ]

/--
**Tonelli's Theorem: Integral Equality on Product Measures**

For a measurable nonnegative function on a product space,
the double integral equals the iterated integral (in any order).

This is the fundamental statement: If f : G × G → ℝ≥0∞ is measurable and nonnegative,
then: ∫⁻ (x,y), f (x,y) ∂(μ.prod μ) = ∫⁻ x, ∫⁻ y, f (x,y) ∂μ ∂μ
-/
theorem tonelli_nonneg_prod_eq_iterated
    (f : G × G → ℝ≥0∞)
    (hf_meas : Measurable f) :
    ∫⁻ p, f p ∂(μ.prod μ) = ∫⁻ x, ∫⁻ y, f (x, y) ∂μ ∂μ := by
  simpa using lintegral_prod (μ := μ) (ν := μ) f hf_meas.aemeasurable

/--
**Section Finiteness from Product Finiteness (Tonelli Consequence)**

If ∫⁻ (x,y), f (x,y) ∂(μ.prod μ) < ∞ where f is measurable and nonnegative,
then for a.e. x, we have ∫⁻ y, f (x,y) ∂μ < ∞.

This is the key consequence of Tonelli for our application.
-/
theorem tonelli_ae_section_lt_top
    {f : G × G → ℝ≥0∞}
    (hf_meas : Measurable f)
    (hf_int : ∫⁻ p, f p ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f (x, y) ∂μ < ∞ := by
  classical
  have h_prod_eq := tonelli_nonneg_prod_eq_iterated (μ := μ) f hf_meas
  rw [h_prod_eq] at hf_int
  have h_meas_section : Measurable fun x => ∫⁻ y, f (x, y) ∂μ :=
    Measurable.lintegral_prod_right' hf_meas
  exact ae_lt_top h_meas_section (ne_of_lt hf_int)

/--
**Tonelli for Norm Products (Nonnegative)**

For measurable nonnegative functions `f, g : G → ℝ≥0∞`,
if `∫⁻ (x, y), f x * g y ∂(μ.prod μ) < ∞`,
then for a.e. `x`, `∫⁻ y, f x * g y ∂μ < ∞`.
-/
theorem tonelli_product_ae_section_lt_top
    {f g : G → ℝ≥0∞}
    (hf_meas : Measurable f)
    (hg_meas : Measurable g)
    (hf_int : ∫⁻ x, f x ∂μ < ∞)
    (hg_int : ∫⁻ y, g y ∂μ < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f x * g y ∂μ < ∞ := by
  have h_prod_meas :
      Measurable fun p : G × G => f p.1 * g p.2 :=
    (hf_meas.comp measurable_fst).mul (hg_meas.comp measurable_snd)
  have h_prod_eq :
      ∫⁻ p : G × G, f p.1 * g p.2 ∂(μ.prod μ)
        = (∫⁻ x, f x ∂μ) * (∫⁻ y, g y ∂μ) := by
    simpa using
      lintegral_prod_mul (μ := μ) (ν := μ)
        (f := f) (g := g)
        hf_meas.aemeasurable hg_meas.aemeasurable
  have h_prod_int :
      ∫⁻ p : G × G, f p.1 * g p.2 ∂(μ.prod μ) < ∞ := by
    simpa [h_prod_eq] using ENNReal.mul_lt_top hf_int hg_int
  exact tonelli_ae_section_lt_top (μ := μ) h_prod_meas h_prod_int

end TonelliForConvolution

section ConvolutionKernelIntegrability

/-! ## Tonelli for Convolution Kernels

These theorems apply Tonelli directly to the convolution kernel case.
-/

variable [AddCommGroup G]

/--
**Tonelli for Norm Convolution Kernels (Key Application)**

For f, g : G → ℂ and measurable norms,
if (x,y) ↦ f(x - y) * g(y) is integrable on μ.prod μ,
then for a.e. x, y ↦ ‖f(x - y)‖ * ‖g(y)‖ is integrable on μ.

This theorem bridges from the product-level assumption to the section-level conclusion.
-/
theorem tonelli_norm_convolution_section_ae
    {f g : G → ℂ} [SFinite μ]
    (h_kernel_int : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)) :
    ∀ᵐ x ∂μ, Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ := by
  classical
  have h_sections :
      ∀ᵐ x ∂μ, Integrable (fun y : G => f (x - y) * g y) μ :=
    (Integrable.prod_right_ae (μ := μ) (ν := μ) h_kernel_int)
  refine h_sections.mono ?_
  intro x hx
  simpa [norm_mul] using hx.norm

/--
**Tonelli for Real-Valued Convolution Kernels**

For f, g : G → ℝ and nonnegative values,
if (x,y) ↦ f(x - y) * g(y) has finite double integral,
then for a.e. x, the section has finite integral.
-/
theorem tonelli_real_convolution_section_ae
    {f g : G → ℝ} [MeasurableSub₂ G] [SFinite μ]
    (hf_meas : Measurable f)
    (hg_meas : Measurable g)
    (h_kernel_int : ∫⁻ p, ENNReal.ofReal (|f (p.1 - p.2)| * |g p.2|) ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, ENNReal.ofReal (|f (x - y)| * |g y|) ∂μ < ∞ := by
  classical
  set F : G × G → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (|f (p.1 - p.2)| * |g p.2|)
  have hF_meas : Measurable F := by
    have hf_comp : Measurable fun p : G × G => f (p.1 - p.2) :=
      hf_meas.comp measurable_sub
    have hf_abs : Measurable fun p : G × G => |f (p.1 - p.2)| :=
      (continuous_abs.measurable.comp hf_comp)
    have hg_comp : Measurable fun p : G × G => g p.2 :=
      hg_meas.comp measurable_snd
    have hg_abs : Measurable fun p : G × G => |g p.2| :=
      (continuous_abs.measurable.comp hg_comp)
    have h_mul :
        Measurable fun p : G × G => |f (p.1 - p.2)| * |g p.2| :=
      hf_abs.mul hg_abs
    exact ENNReal.measurable_ofReal.comp h_mul
  simpa [F] using
    tonelli_ae_section_lt_top (μ := μ) (f := F) hF_meas h_kernel_int

end ConvolutionKernelIntegrability

section TonelliProductDecomposition

/-! ## Tonelli's Theorem: Product Decomposition

Finer-grained versions of Tonelli that separate the roles of f and g.
-/

variable [AddCommGroup G]

/--
**Tonelli: Separate Factors**

For f, g : G → ℂ with appropriate boundedness and a translation-invariant measure μ,
∫⁻ (x,y), ‖f(x-y) * g(y)‖ ∂(μ.prod μ)
  ≤ (∫⁻ x, ‖f x‖ ∂μ) * (∫⁻ y, ‖g y‖ ∂μ)

when these integrals are finite.
-/
theorem tonelli_norm_product_bound
    {f g : G → ℂ}
    [MeasurableAdd₂ G]
    [MeasurableNeg G]
    [μ.IsAddRightInvariant]
    [SFinite μ]
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ)
    (hf_int : ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ < ∞)
    (hg_int : ∫⁻ y, ENNReal.ofReal ‖g y‖ ∂μ < ∞) :
    ∫⁻ p, ENNReal.ofReal ‖f (p.1 - p.2) * g p.2‖ ∂(μ.prod μ) < ∞ := by
  classical
  -- Package the absolute values as ℝ≥0∞-valued functions.
  set Af : G → ℝ≥0∞ := fun x => ENNReal.ofReal ‖f x‖
  set Ag : G → ℝ≥0∞ := fun y => ENNReal.ofReal ‖g y‖
  have hAf_aemeas : AEMeasurable Af μ := by
    simpa [Af] using (hf_meas.norm.aemeasurable.ennreal_ofReal)
  have hAg_aemeas : AEMeasurable Ag μ := by
    simpa [Ag] using (hg_meas.norm.aemeasurable.ennreal_ofReal)
  have hAf_lt_top : (∫⁻ x, Af x ∂μ) < ∞ := by simpa [Af] using hf_int
  have hAg_lt_top : (∫⁻ y, Ag y ∂μ) < ∞ := by simpa [Ag] using hg_int
  -- Pointwise rewrite of the kernel in terms of Af and Ag.
  have h_kernel_eq :
      (fun p : G × G =>
        ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖))
        = fun p : G × G => Af (p.1 - p.2) * Ag p.2 := by
    funext p
    simp [Af, Ag, ENNReal.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
  -- Measurability data for the composed kernels.
  have hAg_prod_aemeas :
      AEMeasurable (fun q : G × G => Ag q.2) (μ.prod μ) :=
    hAg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have h_prod_aemeas :
      AEMeasurable (fun q : G × G => Af q.1 * Ag q.2) (μ.prod μ) :=
    (hAf_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))).mul
        hAg_prod_aemeas
  -- Change of variables via the measure-preserving shear.
  set τ : G × G → G × G := fun q => (q.1 - q.2, q.2)
  have h_pres : MeasurePreserving τ (μ.prod μ) (μ.prod μ) :=
    measurePreserving_sub_prod (μ := μ) (ν := μ)
  have h_map : Measure.map τ (μ.prod μ) = μ.prod μ := h_pres.map_eq
  have h_change :
      ∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ)
        = ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ) := by
    have h_meas_map :
        AEMeasurable (fun q : G × G => Af q.1 * Ag q.2)
          (Measure.map τ (μ.prod μ)) := by
      simpa [h_map] using h_prod_aemeas
    have h_comp :=
      lintegral_map' h_meas_map
        (aemeasurable_id'.comp_measurable h_pres.measurable)
    have h_eval :
        ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ q, Af (τ q).1 * Ag (τ q).2 ∂(μ.prod μ) := by
      simpa [τ, h_map] using h_comp
    simpa [τ] using h_eval.symm
  -- Evaluate the remaining product integral via Tonelli.
  have h_tonelli :
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    have h_split :=
      MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
        (f := fun q : G × G => Af q.1 * Ag q.2) h_prod_aemeas
    have h_inner :
        ∀ x, ∫⁻ y, Af x * Ag y ∂μ = Af x * ∫⁻ y, Ag y ∂μ := by
      intro x
      simpa using
        lintegral_const_mul'' (μ := μ) (r := Af x) (f := Ag) hAg_aemeas
    have h_outer :
        ∫⁻ x, Af x * ∫⁻ y, Ag y ∂μ ∂μ
          = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := by
      simpa [mul_comm] using
        lintegral_mul_const'' (μ := μ)
          (r := ∫⁻ y, Ag y ∂μ) (f := Af) hAf_aemeas
    calc
      ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ x, ∫⁻ y, Af x * Ag y ∂μ ∂μ := by
              simpa [Function.uncurry] using h_split
      _ = ∫⁻ x, Af x * ∫⁻ y, Ag y ∂μ ∂μ := by
              simp [h_inner]
      _ = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := h_outer
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by simp [mul_comm]
  -- Assemble the pieces.
  have h_kernel_eval :
      ∫⁻ p : G × G,
          ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖) ∂(μ.prod μ)
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    calc
      ∫⁻ p, ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖) ∂(μ.prod μ)
          = ∫⁻ p, Af (p.1 - p.2) * Ag p.2 ∂(μ.prod μ) := by
              simp [h_kernel_eq]
      _ = ∫⁻ p, Af p.1 * Ag p.2 ∂(μ.prod μ) := h_change
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := h_tonelli
  have h_kernel_eval' :
      ∫⁻ p : G × G, ENNReal.ofReal ‖f (p.1 - p.2) * g p.2‖ ∂(μ.prod μ)
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    simpa [Af, Ag, norm_mul, ENNReal.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
      using h_kernel_eval
  have h_fin : (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) < ∞ :=
    ENNReal.mul_lt_top hAf_lt_top hAg_lt_top
  have h_prod_fin :
      ∫⁻ p : G × G,
          ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖) ∂(μ.prod μ) < ∞ := by
    simpa [h_kernel_eval] using h_fin
  have h_kernel_fin :
      ∫⁻ p : G × G, ENNReal.ofReal ‖f (p.1 - p.2) * g p.2‖ ∂(μ.prod μ) < ∞ := by
    simpa [Af, Ag, norm_mul, ENNReal.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
      using h_prod_fin
  exact h_kernel_fin

end TonelliProductDecomposition

section AEMeasurableTonelli

/-!
Auxiliary a.e.-finiteness lemmas for ℝ≥0∞-valued kernels assuming only
`AEMeasurable` on the product space. Proofs will be supplied where used.
-/

/--
From product finiteness for an `AEMeasurable` nonnegative kernel on `μ.prod μ`,
deduce that for a.e. `x`, the section `y ↦ f (x, y)` has finite lintegral.
-/
theorem tonelli_ae_section_lt_top_of_aemeasurable_left
    [SFinite μ]
    {f : G × G → ℝ≥0∞}
    (hf_aemeas : AEMeasurable f (μ.prod μ))
    (hf_int : ∫⁻ p, f p ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f (x, y) ∂μ < ∞ := by
  classical
  -- Choose a measurable representative of f on μ.prod μ.
  set f0 : G × G → ℝ≥0∞ := hf_aemeas.mk f with hf0_def
  have hf0_meas : Measurable f0 := hf_aemeas.measurable_mk
  have hf_ae_eq : f =ᵐ[μ.prod μ] f0 := hf_aemeas.ae_eq_mk
  -- Transfer product finiteness along the a.e. equality.
  have hf0_int : ∫⁻ p, f0 p ∂(μ.prod μ) < ∞ := by
    have h_eq := lintegral_congr_ae hf_ae_eq
    simpa [h_eq] using hf_int
  -- Apply the measurable Tonelli consequence to f0.
  have h_left : ∀ᵐ x ∂μ, ∫⁻ y, f0 (x, y) ∂μ < ∞ :=
    tonelli_ae_section_lt_top (μ := μ) (f := f0) hf0_meas hf0_int
  -- Relate sections of f and f0 via the product a.e. equality.
  have h_curry :
      ∀ᵐ x ∂μ, (fun y => f (x, y)) =ᵐ[μ] fun y => f0 (x, y) :=
    Measure.ae_ae_eq_curry_of_prod (μ := μ) (ν := μ) hf_ae_eq
  have h_eq_int :
      ∀ᵐ x ∂μ, ∫⁻ y, f (x, y) ∂μ = ∫⁻ y, f0 (x, y) ∂μ := by
    refine h_curry.mono ?_
    intro x hx
    simpa using lintegral_congr_ae hx
  -- Conclude finiteness for f by equality with the finite sections of f0.
  refine (h_eq_int.and h_left).mono ?_
  intro x hx
  rcases hx with ⟨h_eq, h_lt⟩
  simpa [h_eq] using h_lt

/--
Symmetric version: from product finiteness for an `AEMeasurable` nonnegative kernel,
deduce that for a.e. `y`, the section `x ↦ f (x, y)` has finite lintegral.
-/
theorem tonelli_ae_section_lt_top_of_aemeasurable_right
    [SFinite μ]
    {f : G × G → ℝ≥0∞}
    (hf_aemeas : AEMeasurable f (μ.prod μ))
    (hf_int : ∫⁻ p, f p ∂(μ.prod μ) < ∞) :
    ∀ᵐ y ∂μ, ∫⁻ x, f (x, y) ∂μ < ∞ := by
  classical
  -- Measurable representative on μ.prod μ
  set f0 : G × G → ℝ≥0∞ := hf_aemeas.mk f with hf0_def
  have hf0_meas : Measurable f0 := hf_aemeas.measurable_mk
  have hf_ae_eq : f =ᵐ[μ.prod μ] f0 := hf_aemeas.ae_eq_mk
  -- Product finiteness transfers along the a.e. equality.
  have hf0_int : ∫⁻ p, f0 p ∂(μ.prod μ) < ∞ := by
    have h_eq := lintegral_congr_ae hf_ae_eq
    simpa [h_eq] using hf_int
  -- Consider the swapped kernel and apply the measurable Tonelli consequence to it.
  set fSwap : G × G → ℝ≥0∞ := fun q => f0 (q.2, q.1) with hfSwap_def
  have h_swap_pres :
      MeasurePreserving (fun q : G × G => Prod.swap q) (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hfSwap_meas : Measurable fSwap :=
    hf0_meas.comp h_swap_pres.measurable
  have h_map_eq : Measure.map Prod.swap (μ.prod μ) = μ.prod μ := h_swap_pres.map_eq
  have hf0_aemeas_map :
      AEMeasurable f0 (Measure.map Prod.swap (μ.prod μ)) := by
    simpa [h_map_eq] using hf0_meas.aemeasurable
  have h_map :=
    lintegral_map' hf0_aemeas_map
      (aemeasurable_id'.comp_measurable h_swap_pres.measurable)
  have hfSwap_int : ∫⁻ p, fSwap p ∂(μ.prod μ) < ∞ := by
    -- From change of variables: ∫ f0 ∘ swap d(μ×μ) = ∫ f0 d(μ×μ)
    have h_eval :
        ∫⁻ p, f0 p ∂(μ.prod μ) = ∫⁻ p, fSwap p ∂(μ.prod μ) := by
      -- `h_map` gives: ∫ f0 d(map swap (μ×μ)) = ∫ f0 ∘ swap d(μ×μ)
      -- Use map_eq to rewrite the LHS.
      simpa [fSwap, hfSwap_def, h_map_eq]
        using h_map
    -- Conclude finiteness for the swapped kernel.
    simpa [h_eval] using hf0_int
  -- Tonelli on the swapped kernel gives finiteness of the swapped sections.
  have h_right_swap : ∀ᵐ y ∂μ, ∫⁻ x, fSwap (y, x) ∂μ < ∞ :=
    tonelli_ae_section_lt_top (μ := μ) (f := fSwap) hfSwap_meas hfSwap_int
  -- Identify fSwap (y, x) with f0 (x, y).
  have h_right0 : ∀ᵐ y ∂μ, ∫⁻ x, f0 (x, y) ∂μ < ∞ := by
    refine h_right_swap.mono ?_
    intro y hy
    simpa [fSwap, hfSwap_def]
      using hy
  -- Relate sections of f and f0 via the product a.e. equality, using swap to get y-fibres.
  have h_swap_eq :
      (fun q : G × G => f (q.2, q.1)) =ᵐ[μ.prod μ]
        fun q => f0 (q.2, q.1) := by
    have h_comp :=
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae_eq_comp
        hf_ae_eq
    simpa [Function.comp, Prod.swap] using h_comp
  have h_curry :
      ∀ᵐ y ∂μ, (fun x => f (x, y)) =ᵐ[μ] fun x => f0 (x, y) := by
    have h := Measure.ae_ae_eq_curry_of_prod (μ := μ) (ν := μ) h_swap_eq
    refine h.mono ?_
    intro y hy
    simpa [Function.curry, Prod.swap] using hy
  have h_eq_int :
      ∀ᵐ y ∂μ, ∫⁻ x, f (x, y) ∂μ = ∫⁻ x, f0 (x, y) ∂μ := by
    refine h_curry.mono ?_
    intro y hy
    simpa using lintegral_congr_ae hy
  -- Conclude finiteness for f by equality with the finite sections of f0.
  refine (h_eq_int.and h_right0).mono ?_
  intro y hy
  rcases hy with ⟨h_eq, h_lt⟩
  simpa [h_eq] using h_lt

end AEMeasurableTonelli

/-
Additional Tonelli/Fubini helper lemmas for real-valued kernels.
These provide signatures (without proofs) for bridging from ENNReal-valued
Tonelli statements to Bochner integrability of real-valued sections and
their outer integrals. The detailed proofs will be supplied where needed.
-/

/--
From product finiteness for an `AEMeasurable` nonnegative real-valued kernel on `μ.prod μ`,
deduce that for a.e. `x`, the section `y ↦ H (x, y)` is Bochner integrable (as an ℝ-valued
function).
-/
lemma ae_integrable_left_of_lintegral_ofReal_lt_top
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    {H : G × G → ℝ}
    (hH_nonneg : ∀ p, 0 ≤ H p)
    (hH_aemeas : AEMeasurable H (μ.prod μ))
    (hH_int :
      ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, Integrable (fun y => H (x, y)) μ := by
  classical
  -- Step 1: apply the ℝ≥0∞-valued Tonelli consequence to the kernel `ofReal ∘ H`.
  have hH_ofReal_aemeas :
      AEMeasurable (fun p : G × G => ENNReal.ofReal (H p)) (μ.prod μ) :=
    hH_aemeas.ennreal_ofReal
  have h_section_lt_top :
      ∀ᵐ x ∂μ, ∫⁻ y, ENNReal.ofReal (H (x, y)) ∂μ < ∞ :=
    tonelli_ae_section_lt_top_of_aemeasurable_left
      (μ := μ) (f := fun p : G × G => ENNReal.ofReal (H p))
      hH_ofReal_aemeas hH_int
  -- Step 1a: a.e. strong measurability of the sections x ↦ H (x, ·).
  have h_section_aesm :
      ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => H (x, y)) μ := by
    -- Extract a measurable representative H' of H on μ.prod μ.
    rcases hH_aemeas with ⟨H', hH'_meas, hH_eq⟩
    -- From H = H' a.e. on μ.prod μ, deduce a.e. equality on almost every fibre.
    have h_section_ae :
        ∀ᵐ x ∂μ, (fun y => H' (x, y)) =ᵐ[μ] fun y => H (x, y) := by
      have h_curry :
          ∀ᵐ x ∂μ, (fun y => H (x, y)) =ᵐ[μ] fun y => H' (x, y) :=
        Measure.ae_ae_eq_curry_of_prod (μ := μ) (ν := μ) hH_eq
      refine h_curry.mono ?_
      intro x hx
      simpa using hx.symm
    -- Sections of the measurable representative are measurable.
    have hH'_section_meas :
        ∀ x, Measurable fun y => H' (x, y) := fun x =>
      hH'_meas.comp (measurable_const.prodMk measurable_id)
    -- Package measurability and a.e. equality into AEStronglyMeasurable for H(x, ·).
    refine h_section_ae.mono ?_
    intro x hx
    exact (hH'_section_meas x).aestronglyMeasurable.congr hx
  -- Step 2: from finiteness of the `ofReal` lintegral and nonnegativity,
  -- deduce Bochner integrability of the real-valued sections.
  refine (h_section_lt_top.and h_section_aesm).mono ?_
  intro x hx
  rcases hx with ⟨hx, hx_aesm⟩
  -- Rewrite the integrand using `‖H (x, y)‖ = H (x, y)` (since `H ≥ 0`).
  have h_eq :
      (fun y => ENNReal.ofReal (H (x, y))) =
        fun y => ENNReal.ofReal ‖H (x, y)‖ := by
    funext y
    have h_nonneg : 0 ≤ H (x, y) := hH_nonneg (x, y)
    have h_abs : |H (x, y)| = H (x, y) := abs_of_nonneg h_nonneg
    simp [Real.norm_eq_abs, h_abs]
  have hx_norm :
      ∫⁻ y, ENNReal.ofReal ‖H (x, y)‖ ∂μ < ∞ := by
    simpa [h_eq] using hx
  -- Use the standard Bochner criterion for integrability via the lintegral of the norm.
  -- Integrable is AEStronglyMeasurable ∧ HasFiniteIntegral
  have hx_hasFinite : HasFiniteIntegral (fun y => H (x, y)) μ := by
    -- HasFiniteIntegral means ∫⁻ y, ‖H (x, y)‖ₑ ∂μ < ⊤
    have h_enorm_eq : (fun y => ‖H (x, y)‖ₑ) = fun y => ENNReal.ofReal ‖H (x, y)‖ := by
      funext y
      exact (ofReal_norm_eq_enorm (H (x, y))).symm
    simpa [HasFiniteIntegral, h_enorm_eq] using hx_norm
  exact ⟨hx_aesm, hx_hasFinite⟩

/--
From product finiteness for an `AEMeasurable` nonnegative real-valued kernel on `μ.prod μ`,
deduce that the outer integral `x ↦ ∫ y, H (x, y) dμ` is Bochner integrable on `μ`.
-/
lemma integrable_left_integral_of_lintegral_ofReal_lt_top
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    {H : G × G → ℝ}
    (hH_nonneg : ∀ p, 0 ≤ H p)
    (hH_aemeas : AEMeasurable H (μ.prod μ))
    (hH_int :
      ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) < ∞) :
    Integrable (fun x => ∫ y, H (x, y) ∂μ) μ := by
  classical
  -- First, upgrade to Bochner integrability of H on the product space.
  have hH_eq_ofReal_norm :
      (fun p : G × G => ENNReal.ofReal (H p)) =
        fun p => ENNReal.ofReal ‖H p‖ := by
    funext p
    have h_nonneg : 0 ≤ H p := hH_nonneg p
    have h_abs : |H p| = H p := abs_of_nonneg h_nonneg
    simp [h_abs, Real.norm_eq_abs]
  have hH_norm_int :
      ∫⁻ p, ENNReal.ofReal ‖H p‖ ∂(μ.prod μ) < ∞ := by
    simpa [hH_eq_ofReal_norm] using hH_int
  have hH_meas : AEStronglyMeasurable H (μ.prod μ) :=
    hH_aemeas.aestronglyMeasurable
  have hH_hasFinite : HasFiniteIntegral H (μ.prod μ) := by
    -- Translate the finiteness of the ofReal-lintegral into HasFiniteIntegral.
    have h_enorm_eq :
        (fun p : G × G => ‖H p‖ₑ)
          = fun p => ENNReal.ofReal ‖H p‖ := by
      funext p
      exact (ofReal_norm_eq_enorm (H p)).symm
    simpa [HasFiniteIntegral, h_enorm_eq] using hH_norm_int
  have hH_int_prod : Integrable H (μ.prod μ) :=
    ⟨hH_meas, hH_hasFinite⟩
  -- Use the product integrability to control the fibrewise integrals.
  have h_prod_info :=
    (integrable_prod_iff (μ := μ) (ν := μ)
        (f := H) hH_meas).mp hH_int_prod
  have h_section_int :
      ∀ᵐ x ∂μ, Integrable (fun y => H (x, y)) μ := by
    simpa using h_prod_info.1
  have h_majorant_int :
      Integrable (fun x => ∫ y, ‖H (x, y)‖ ∂μ) μ := by
    simpa using h_prod_info.2
  -- Measurability of the outer integral x ↦ ∫ H (x, y) dμ.
  have h_integral_meas :
      AEStronglyMeasurable (fun x => ∫ y, H (x, y) ∂μ) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := μ) (f := H) hH_meas)
  have h_norm_meas :
      AEStronglyMeasurable (fun x => ‖∫ y, H (x, y) ∂μ‖) μ :=
    h_integral_meas.norm
  -- Pointwise bound: norm of the fibrewise integral is dominated by the integral of norms.
  have h_pointwise :
      (fun x => ‖∫ y, H (x, y) ∂μ‖)
        ≤ᵐ[μ] fun x => ∫ y, ‖H (x, y)‖ ∂μ := by
    refine h_section_int.mono ?_
    intro x hx
    have hx_bound :=
      norm_integral_le_integral_norm (μ := μ) (f := fun y => H (x, y))
    simpa using hx_bound
  -- Basic integrability of the norm of the outer integral.
  have h_norm_integrable :
      Integrable (fun x => ‖∫ y, H (x, y) ∂μ‖) μ := by
    refine Integrable.mono' h_majorant_int h_norm_meas ?_
    simpa using h_pointwise
  -- Package as integrability of the real-valued function x ↦ ∫ H (x, y) dμ.
  set Gfun : G → ℝ := fun x => ∫ y, H (x, y) ∂μ with hG_def
  have hG_meas : AEStronglyMeasurable Gfun μ := h_integral_meas
  have hG_hasFinite : HasFiniteIntegral Gfun μ := by
    -- From integrability of the norm of Gfun, deduce finiteness for Gfun itself.
    have h_fin_norm : HasFiniteIntegral (fun x => ‖Gfun x‖) μ :=
      h_norm_integrable.hasFiniteIntegral
    simpa [Gfun, HasFiniteIntegral] using h_fin_norm
  exact ⟨hG_meas, hG_hasFinite⟩

/-!
## L²×L¹ Convolution: Fiberwise Integrability

We record a lemma signature stating that if `f ∈ L²(μ)` and `g ∈ L¹(μ)`, then for almost every
`x`, the section `y ↦ f (x - y) * g y` is integrable. The proof combines Tonelli/Fubini with
the Cauchy–Schwarz inequality applied to the finite measure with density `|g|`.
-/

/-- Fiberwise integrability for L²×L¹ convolution kernels. -/
theorem convolution_fiber_integrable_L2_L1
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (f g : G → ℂ)
    (hf : MemLp f 2 μ) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ := by
  classical
  -- Weighted finite measure ν with density ‖g‖ₑ.
  set ν : Measure G := μ.withDensity (fun y => ‖g y‖ₑ) with hν_def
  -- Step 1: L²(ν) control of y ↦ f (x - y) for a.e. x.
  -- This follows from Tonelli on the nonnegative kernel
  --   (x, y) ↦ ‖f (x - y)‖ₑ^2 · ‖g y‖ₑ,
  -- together with the L²(μ) control of f and L¹(μ) control of g.
  have hL2_ae : ∀ᵐ x ∂μ, MemLp (fun y => f (x - y)) 2 ν := by
    -- Build ℝ≥0∞-valued factors Af, Ag.
    set Af : G → ℝ≥0∞ := fun z => ‖f z‖ₑ ^ (2 : ℝ) with hAf_def
    set Ag : G → ℝ≥0∞ := fun y => ‖g y‖ₑ with hAg_def
    have hf_meas : AEMeasurable (fun z => ‖f z‖ₑ) μ := hf.aestronglyMeasurable.enorm
    have hAf_meas : AEMeasurable Af μ := by
      simpa [Af, hAf_def] using hf_meas.pow_const (2 : ℝ)
    have hg_meas : AEMeasurable (fun y => ‖g y‖ₑ) μ := hg.aestronglyMeasurable.enorm
    have hAg_meas : AEMeasurable Ag μ := by simpa [Ag, hAg_def] using hg_meas
    -- Finiteness of the separated integrals
    have hAf_lt_top : (∫⁻ z, Af z ∂μ) < ∞ := by
      -- From `hf : MemLp f 2 μ` via the characterization by lintegral of the r-power of ‖f‖ₑ
      have :=
        lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := μ)
            (p := (2 : ℝ≥0∞)) (f := f)
            two_ne_zero ENNReal.ofNat_ne_top hf.eLpNorm_lt_top
      simpa [Af, hAf_def, ENNReal.toReal_ofNat] using this
    have hAg_lt_top : (∫⁻ y, Ag y ∂μ) < ∞ := by
      -- From integrability of g
      simpa [Ag, hAg_def, HasFiniteIntegral] using hg.hasFiniteIntegral
    -- Define the nonnegative kernel on the product space.
    set H : G × G → ℝ≥0∞ := fun q => Af (q.1 - q.2) * Ag q.2 with hH_def
    -- A.E.-measurability of H on μ × μ.
    have h_sub_qmp :
        Measure.QuasiMeasurePreserving (fun q : G × G => q.1 - q.2)
          (μ.prod μ) μ := by
      have h_sub_prod :
          MeasurePreserving (fun q : G × G => (q.1 - q.2, q.2))
            (μ.prod μ) (μ.prod μ) :=
        measurePreserving_sub_prod (μ := μ) (ν := μ)
      have h_fst_qmp :
          Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
            (μ.prod μ) μ :=
        MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
      have h_comp := h_fst_qmp.comp h_sub_prod.quasiMeasurePreserving
      simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm] using h_comp
    have hAf_comp_aemeas :
        AEMeasurable (fun q : G × G => Af (q.1 - q.2)) (μ.prod μ) :=
      hAf_meas.comp_quasiMeasurePreserving h_sub_qmp
    have hAg_comp_aemeas :
        AEMeasurable (fun q : G × G => Ag q.2) (μ.prod μ) :=
      hAg_meas.comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
    have hH_aemeas : AEMeasurable H (μ.prod μ) :=
      (hAf_comp_aemeas.mul hAg_comp_aemeas)
    -- Compute the product lintegral via the shear change of variables and Tonelli.
    have h_change :
        ∫⁻ q : G × G, H q ∂(μ.prod μ)
          = ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ) := by
      -- Use the measure-preserving shear τ(q) = (q.1 - q.2, q.2)
      set τ : G × G → G × G := fun q => (q.1 - q.2, q.2)
      have h_pres : MeasurePreserving τ (μ.prod μ) (μ.prod μ) :=
        measurePreserving_sub_prod (μ := μ) (ν := μ)
      have h_map : Measure.map τ (μ.prod μ) = μ.prod μ := h_pres.map_eq
      have h_prod_aemeas :
          AEMeasurable (fun q : G × G => Af q.1 * Ag q.2) (μ.prod μ) :=
        (hAf_meas.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))).mul
          (hAg_meas.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)))
      have h_prod_map :
          AEMeasurable (fun q : G × G => Af q.1 * Ag q.2)
            (Measure.map τ (μ.prod μ)) := by
        simpa [h_map] using h_prod_aemeas
      have h_map_eq :=
        lintegral_map' h_prod_map (aemeasurable_id'.comp_measurable h_pres.measurable)
      have h_eval :
          ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
            = ∫⁻ q, Af (τ q).1 * Ag (τ q).2 ∂(μ.prod μ) := by
        simpa [τ, h_map] using h_map_eq
      have hH_eval :
          (fun q : G × G => Af (τ q).1 * Ag (τ q).2) = H := by
        funext q; simp [H, τ, hH_def]
      simpa [hH_eval] using h_eval.symm
    have h_split :
        ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = (∫⁻ z, Af z ∂μ) * (∫⁻ y, Ag y ∂μ) := by
      -- Tonelli on the separated kernel Af(x)·Ag(y).
      have h_prod_aemeas :
          AEMeasurable (fun q : G × G => Af q.1 * Ag q.2) (μ.prod μ) :=
        (hAf_meas.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))).mul
          (hAg_meas.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)))
      have h_tonelli :=
        MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
          (f := fun q : G × G => Af q.1 * Ag q.2) h_prod_aemeas
      have h_inner :
          ∀ x, ∫⁻ y, Af x * Ag y ∂μ = Af x * ∫⁻ y, Ag y ∂μ := by
        intro x; simpa using lintegral_const_mul'' (μ := μ) (r := Af x) (f := Ag) hAg_meas
      have h_outer :
          ∫⁻ x, Af x * ∫⁻ y, Ag y ∂μ ∂μ
            = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := by
        simpa [mul_comm]
          using lintegral_mul_const'' (μ := μ) (r := ∫⁻ y, Ag y ∂μ) (f := Af) hAf_meas
      calc
        ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
            = ∫⁻ x, ∫⁻ y, Af x * Ag y ∂μ ∂μ := by
                simpa [Function.uncurry] using h_tonelli
        _ = ∫⁻ x, Af x * ∫⁻ y, Ag y ∂μ ∂μ := by
                simp [h_inner]
        _ = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := h_outer
        _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by simp [mul_comm]
    have h_prod_lt_top : ∫⁻ q : G × G, H q ∂(μ.prod μ) < ∞ := by
      have := ENNReal.mul_lt_top hAf_lt_top hAg_lt_top
      simpa [h_change, h_split] using this
    -- Tonelli consequence: for a.e. x, the y-section has finite lintegral.
    have h_section_fin : ∀ᵐ x ∂μ, ∫⁻ y, H (x, y) ∂μ < ∞ :=
      tonelli_ae_section_lt_top_of_aemeasurable_left
        (μ := μ) (f := H) hH_aemeas h_prod_lt_top
    -- Identify the section integral with the L²(ν) seminorm of y ↦ f (x − y).
    -- Also record measurability for MemLp.
    have hν_ac : ν ≪ μ := by
      -- withDensity is absolutely continuous with respect to the base measure
      simpa [hν_def] using withDensity_absolutelyContinuous (μ := μ)
        (f := fun y => ‖g y‖ₑ)
    -- For a fixed x, measurability of y ↦ f (x - y) under μ then lift to ν.
    have h_meas_x : ∀ x, AEStronglyMeasurable (fun y => f (x - y)) ν := by
      intro x
      -- y ↦ x - y is measurable
      have h_sub_meas : Measurable (fun y : G => x - y) := by
        have : (fun y : G => x - y) = (fun y => x + (-y)) := by
          ext y; simp [sub_eq_add_neg]
        simpa [this] using (measurable_const.add measurable_neg)
      -- Get a strongly measurable representative of f
      obtain ⟨f0, hf0_strong, hf_ae⟩ := hf.aestronglyMeasurable
      -- f0 ∘ (x - ·) is strongly measurable
      have hf0_comp : StronglyMeasurable (fun y => f0 (x - y)) :=
        hf0_strong.comp_measurable h_sub_meas
      -- f (x - ·) =ᵐ[μ] f0 (x - ·)
      have h_ae_comp : (fun y => f (x - y)) =ᵐ[μ] (fun y => f0 (x - y)) := by
        -- Use measure preservation: y ↦ x - y preserves μ
        have h_mp : MeasurePreserving (fun y : G => x - y) μ μ := by
          -- x - y = -(y - x), and both transformations preserve μ
          have h1 : (fun y : G => x - y) = Neg.neg ∘ (fun y => y - x) := by
            ext y; simp [Function.comp, sub_eq_add_neg, add_comm]
          -- y - x is measure-preserving (right invariance)
          have h_sub_right : MeasurePreserving (fun y : G => y - x) μ μ :=
            measurePreserving_sub_right μ x
          -- Need to show that Neg.neg is also measure-preserving
          -- For an abelian group with right-invariant measure, neg preserves the measure
          have h_neg : MeasurePreserving (Neg.neg : G → G) μ μ :=
            Measure.measurePreserving_neg (μ := μ)
          rw [h1]
          exact h_neg.comp h_sub_right
        exact h_mp.quasiMeasurePreserving.ae_eq_comp hf_ae
      -- Package into AEStronglyMeasurable on μ, then transfer to ν
      have h_aestrong_μ : AEStronglyMeasurable (fun y => f (x - y)) μ :=
        ⟨fun y => f0 (x - y), hf0_comp, h_ae_comp⟩
      exact h_aestrong_μ.mono_ac hν_ac
    -- Conclude MemLp from the finite weighted lintegral and measurability.
    refine h_section_fin.mono ?_
    intro x hx
    -- Expand withDensity to match the weighted section integral.
    have h_expand :
        ∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) ∂ν
          = ∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) * ‖g y‖ₑ ∂μ := by
      -- use the standard expansion lemma for withDensity (a.e. measurable versions)
      -- We need a.e. measurability on μ for the integrand
      -- Since ν = μ.withDensity, and withDensity is absolutely continuous w.r.t. μ,
      -- we have μ ≪ ν is FALSE, but the reverse ν ≪ μ holds (hν_ac)
      -- However, we need the a.e. measurability on μ, not ν
      -- So we construct it directly from h_aestrong_μ earlier in the proof
      have h_aestrong_μ : AEStronglyMeasurable (fun y => f (x - y)) μ := by
        -- Reconstruct the a.e. strong measurability on μ
        have h_sub_meas : Measurable (fun y : G => x - y) := by
          have : (fun y : G => x - y) = (fun y => x + (-y)) := by ext; simp [sub_eq_add_neg]
          rw [this]
          exact measurable_const.add measurable_neg
        obtain ⟨f0, hf0, hf_ae⟩ := hf.aestronglyMeasurable
        have hf0_comp : StronglyMeasurable (fun y => f0 (x - y)) :=
          hf0.comp_measurable h_sub_meas
        have h_ae_comp : (fun y => f (x - y)) =ᵐ[μ] (fun y => f0 (x - y)) := by
          -- Use measure preservation: y ↦ x - y preserves μ
          have h_mp : MeasurePreserving (fun y : G => x - y) μ μ := by
            -- x - y = -(y - x), and both transformations preserve μ
            have h1 : (fun y : G => x - y) = Neg.neg ∘ (fun y => y - x) := by
              ext y; simp [Function.comp, sub_eq_add_neg, add_comm]
            -- y - x is measure-preserving (right invariance)
            have h_sub_right : MeasurePreserving (fun y : G => y - x) μ μ :=
              measurePreserving_sub_right μ x
            -- Negation is measure-preserving under IsNegInvariant
            have h_neg : MeasurePreserving (Neg.neg : G → G) μ μ :=
              Measure.measurePreserving_neg (μ := μ)
            rw [h1]
            exact h_neg.comp h_sub_right
          exact h_mp.quasiMeasurePreserving.ae_eq_comp hf_ae
        exact ⟨fun y => f0 (x - y), hf0_comp, h_ae_comp⟩
      have hf_pow_ae_μ : AEMeasurable (fun y => (‖f (x - y)‖ₑ) ^ (2 : ℝ)) μ :=
        h_aestrong_μ.enorm.pow_const (2 : ℝ)
      have hg_ae : AEMeasurable (fun y => ‖g y‖ₑ) μ := hg_meas
      have h :=
        lintegral_withDensity_eq_lintegral_mul₀ (μ := μ)
          (f := fun y => ‖g y‖ₑ) hg_ae
          (g := fun y => (‖f (x - y)‖ₑ) ^ (2 : ℝ)) hf_pow_ae_μ
      simpa [ν, hν_def, mul_comm] using h
    -- Now H (x, y) = Af (x - y) * Ag y by definition.
    have hH_section : ∫⁻ y, H (x, y) ∂μ
        = ∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) * ‖g y‖ₑ ∂μ := by
      simp [H, hH_def, Af, hAf_def, Ag, hAg_def]
    -- Package into `MemLp`.
    refine ⟨h_meas_x x, ?_⟩
    -- Compare the weighted L² seminorm with the finite section lintegral from Tonelli.
    have : ∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) ∂ν < ∞ := by
      rw [h_expand, ← hH_section]
      exact hx
    -- Turn it into `eLpNorm < ∞`.
    -- Use the characterization `eLpNorm_eq_lintegral_rpow_enorm` with p = 2.
    have h_eq :
        eLpNorm (fun y => f (x - y)) 2 ν
          = (∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
      simpa [one_div, ENNReal.toReal_ofNat]
        using (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
                (μ := ν) (f := fun y => f (x - y))
                (p := (2 : ℝ≥0∞)) two_ne_zero ENNReal.ofNat_ne_top)
    -- From finiteness of the inside lintegral, deduce `eLpNorm < ∞`.
    have h_lt_top : eLpNorm (fun y => f (x - y)) 2 ν < ∞ := by
      -- If the inner lintegral is finite, then its positive r-power is finite.
      refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (μ := ν) (p := (2 : ℝ≥0∞)) (f := fun y => f (x - y))
        (hp_ne_zero := two_ne_zero) (hp_ne_top := ENNReal.ofNat_ne_top)).2 ?_
      simpa using this
    exact h_lt_top
  -- Step 2: Cauchy–Schwarz on (G, ν) for each fibre x.
  -- Since ν is finite (by hg), we have 1 ∈ L²(ν). Combining with hL2_ae gives
  --   ∫ ‖f (x - ·)‖ dν < ∞
  -- hence ∫ ‖f (x - y)‖ · ‖g y‖ dμ(y) < ∞.
  -- First, establish that ν is a finite measure
  have hν_finite : IsFiniteMeasure ν := by
    -- ν = μ.withDensity (fun y => ‖g y‖ₑ)
    -- Since g is integrable, ∫⁻ y, ‖g y‖ₑ ∂μ < ∞
    rw [hν_def]
    have h_int : ∫⁻ y, ‖g y‖ₑ ∂μ < ∞ := by
      simpa [HasFiniteIntegral] using hg.hasFiniteIntegral
    have h_ne_top : ∫⁻ y, ‖g y‖ₑ ∂μ ≠ ⊤ := ne_of_lt h_int
    exact MeasureTheory.isFiniteMeasure_withDensity h_ne_top
  have h_int_norm_ae : ∀ᵐ x ∂μ, Integrable (fun y => ‖f (x - y)‖) ν := by
    -- Deduce L¹(ν) from L²(ν) via exponent monotonicity, then take norms.
    refine hL2_ae.mono ?_
    intro x hx
    haveI : IsFiniteMeasure ν := hν_finite
    have hx_L1 : MemLp (fun y => f (x - y)) 1 ν :=
      hx.mono_exponent (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)
    have hx_int : Integrable (fun y => f (x - y)) ν :=
      (memLp_one_iff_integrable (μ := ν)).1 hx_L1
    exact hx_int.norm
  -- Step 3: Pull back from ν to μ via withDensity and conclude integrability
  -- of the complex-valued section y ↦ f (x - y) * g y on μ.
  refine h_int_norm_ae.mono ?_
  intro x hx
  -- `hx` gives ∫ ‖f (x - ·)‖ dν < ∞
  -- By definition of ν = μ.withDensity ‖g‖ₑ, this means ∫ ‖f (x - y)‖ · ‖g y‖ dμ(y) < ∞
  -- We need to show Integrable (fun y => f (x - y) * g y) μ

  -- First, expand the integral over ν to an integral over μ
  have h_expand : ∫⁻ y, ‖f (x - y)‖ₑ ∂ν = ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂μ := by
    rw [hν_def]
    have h_aemeas_f : AEMeasurable (fun y => ‖f (x - y)‖ₑ) μ := by
      have h_aestrong : AEStronglyMeasurable (fun y => f (x - y)) μ := by
        have h_sub_meas : Measurable (fun y : G => x - y) := by
          have : (fun y : G => x - y) = (fun y => x + (-y)) := by ext; simp [sub_eq_add_neg]
          simpa [this] using (measurable_const.add measurable_neg)
        obtain ⟨f0, hf0, hf_ae⟩ := hf.aestronglyMeasurable
        have hf0_comp : StronglyMeasurable (fun y => f0 (x - y)) :=
          hf0.comp_measurable h_sub_meas
        have h_ae_comp : (fun y => f (x - y)) =ᵐ[μ] (fun y => f0 (x - y)) := by
          have h_mp : MeasurePreserving (fun y : G => x - y) μ μ := by
            have h1 : (fun y : G => x - y) = Neg.neg ∘ (fun y => y - x) := by
              ext y; simp [Function.comp, sub_eq_add_neg, add_comm]
            have h_sub_right : MeasurePreserving (fun y : G => y - x) μ μ :=
              measurePreserving_sub_right μ x
            have h_neg : MeasurePreserving (Neg.neg : G → G) μ μ :=
              Measure.measurePreserving_neg (μ := μ)
            rw [h1]
            exact h_neg.comp h_sub_right
          exact h_mp.quasiMeasurePreserving.ae_eq_comp hf_ae
        exact ⟨fun y => f0 (x - y), hf0_comp, h_ae_comp⟩
      exact h_aestrong.enorm
    have h_aemeas_g : AEMeasurable (fun y => ‖g y‖ₑ) μ := hg.aestronglyMeasurable.enorm
    have h_eq := lintegral_withDensity_eq_lintegral_mul₀ (μ := μ) h_aemeas_g h_aemeas_f
    simpa [mul_comm] using h_eq

  -- From hx, we have ∫⁻ y, ‖f (x - y)‖ₑ ∂ν < ∞
  have h_int_prod : ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂μ < ∞ := by
    rw [← h_expand]
    -- hx : Integrable (fun y => ‖f (x - y)‖) ν
    -- Need to convert to ∫⁻ y, ‖f (x - y)‖ₑ ∂ν < ∞
    have : HasFiniteIntegral (fun y => ‖f (x - y)‖) ν := hx.hasFiniteIntegral
    simpa [HasFiniteIntegral] using this

  -- Now show that f (x - y) * g y is integrable
  -- We have ‖f (x - y) * g y‖ = ‖f (x - y)‖ * ‖g y‖
  have h_aestrong_prod : AEStronglyMeasurable (fun y => f (x - y) * g y) μ := by
    have h_aestrong_f : AEStronglyMeasurable (fun y => f (x - y)) μ := by
      have h_sub_meas : Measurable (fun y : G => x - y) := by
        have : (fun y : G => x - y) = (fun y => x + (-y)) := by ext; simp [sub_eq_add_neg]
        simpa [this] using (measurable_const.add measurable_neg)
      obtain ⟨f0, hf0, hf_ae⟩ := hf.aestronglyMeasurable
      have hf0_comp : StronglyMeasurable (fun y => f0 (x - y)) :=
        hf0.comp_measurable h_sub_meas
      have h_ae_comp : (fun y => f (x - y)) =ᵐ[μ] (fun y => f0 (x - y)) := by
        have h_mp : MeasurePreserving (fun y : G => x - y) μ μ := by
          have h1 : (fun y : G => x - y) = Neg.neg ∘ (fun y => y - x) := by
            ext y; simp [Function.comp, sub_eq_add_neg, add_comm]
          have h_sub_right : MeasurePreserving (fun y : G => y - x) μ μ :=
            measurePreserving_sub_right μ x
          have h_neg : MeasurePreserving (Neg.neg : G → G) μ μ :=
            Measure.measurePreserving_neg (μ := μ)
          rw [h1]
          exact h_neg.comp h_sub_right
        exact h_mp.quasiMeasurePreserving.ae_eq_comp hf_ae
      exact ⟨fun y => f0 (x - y), hf0_comp, h_ae_comp⟩
    exact h_aestrong_f.mul hg.aestronglyMeasurable

  have h_norm_eq : (fun y => ‖f (x - y) * g y‖ₑ) = (fun y => ‖f (x - y)‖ₑ * ‖g y‖ₑ) := by
    ext y
    simp [nnnorm_mul]

  refine ⟨h_aestrong_prod, ?_⟩
  simpa [HasFiniteIntegral, h_norm_eq] using h_int_prod

end MeasureTheory
