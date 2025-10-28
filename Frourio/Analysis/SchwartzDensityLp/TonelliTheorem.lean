import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Arithmetic
import Frourio.Analysis.SchwartzDensityLp.FubiniSection
import Frourio.Analysis.HolderInequality.HolderInequalityCore
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

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

end MeasureTheory
