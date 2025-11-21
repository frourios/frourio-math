import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fubini Theory for Sections

This file develops theory for extracting section integrability from product measure integrability.

## Main Results

- `integrable_section_of_integrable_prod`: If a function is integrable on a product measure,
  then for a.e. point in the first factor, the section is integrable on the second factor.

- `integrable_section_at_point`: Under suitable conditions (e.g., continuity or additional
  structure), we can extract section integrability at a specific point, not just a.e.

## Key Definitions

- Sections of functions on product spaces
- Measurability properties of sections

## Implementation Notes

The main challenge is going from "for a.e. x" to "for all x" or "for a specific x".
This generally requires additional assumptions like:
- Continuity of the function
- Additional regularity of the measures
- Density arguments

## References

- Rudin, "Real and Complex Analysis", Chapter on Product Measures
- Folland, "Real Analysis", Section on Fubini's Theorem
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

variable {α β E : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]
variable [NormedAddCommGroup E]
variable {μ : Measure α} {ν : Measure β}

namespace MeasureTheory

section IntegrableSection

/-- The left section of a function f : α × β → E at a point a : α is the function
    y ↦ f (a, y) on β. -/
def leftSection (f : α × β → E) (a : α) : β → E := fun b => f (a, b)

variable [SFinite ν]

/--
**Fubini's Theorem for Sections (a.e. version)**

If a function is integrable on a product measure μ.prod ν, then for almost every point a in α,
the section b ↦ f (a, b) is integrable on ν.

This is a consequence of Fubini's theorem and Tonelli's theorem.
-/
theorem integrable_section_of_integrable_prod
    {f : α × β → E} [SFinite μ]
    (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ a ∂μ, Integrable (leftSection f a) ν := by
  simpa [leftSection] using hf.prod_right_ae

/--
**Variant for real-valued functions**

For nonnegative measurable functions on a product space, if the double integral is finite,
then for a.e. x, the section integral is finite.
-/
theorem ae_integrable_section_of_lintegral_lt_top
    {f : α × β → ℝ≥0∞}
    (hf_meas : Measurable f)
    (hf_int : ∫⁻ p, f p ∂(μ.prod ν) < ∞) :
    ∀ᵐ a ∂μ, ∫⁻ b, f (a, b) ∂ν < ∞ := by
  classical
  have h_meas_section :
      Measurable fun a => ∫⁻ b, f (a, b) ∂ν :=
    (Measurable.lintegral_prod_right' hf_meas)
  have h_section_lt :
      ∫⁻ a, ∫⁻ b, f (a, b) ∂ν ∂μ < ∞ := by
    have h_prod := lintegral_prod (μ:=μ) (ν:=ν) f hf_meas.aemeasurable
    simpa [h_prod] using hf_int
  have h_section_ne :
      ∫⁻ a, ∫⁻ b, f (a, b) ∂ν ∂μ ≠ ∞ := ne_of_lt h_section_lt
  exact ae_lt_top h_meas_section h_section_ne

/--
For nonnegative real-valued functions, if integrable on product, then sections are integrable a.e.
-/
theorem integrable_section_of_integrable_prod_nonneg
    {f : α × β → ℝ} [SFinite μ]
    (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ a ∂μ, Integrable (fun b => f (a, b)) ν := by
  simpa [leftSection] using
    (integrable_section_of_integrable_prod (μ:=μ) (ν:=ν) (f:=f) hf)

end IntegrableSection

section ConvolutionKernel

variable {G : Type*} [AddCommGroup G]
variable [MeasurableSpace G]
variable (μ : Measure G)

/--
**Section integrability for convolution kernels**

For convolution-type kernels of the form (x, y) ↦ f(x - y) * g(y),
if the product is integrable on μ.prod μ, then for a.e. x,
the section y ↦ f(x - y) * g(y) is integrable.
-/
theorem integrable_convolution_section_ae
    {f g : G → ℂ} [SFinite μ]
    (h_kernel_int : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)) :
    ∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ := by
  simpa [leftSection] using
    (integrable_section_of_integrable_prod
      (μ:=μ) (ν:=μ)
      (f:=fun q : G × G => f (q.1 - q.2) * g q.2)
      h_kernel_int)

/--
**Section integrability for norm of convolution kernels**

For the norm version: if ‖f(x - y) * g(y)‖ is integrable on the product,
then for a.e. x, the section is integrable.
-/
theorem integrable_norm_convolution_section_ae
    {f g : G → ℂ} [SFinite μ]
    (h_kernel_int : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)) :
    ∀ᵐ x ∂μ, Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ := by
  have h_norm_int := h_kernel_int.norm
  have h_eq : (fun q : G × G => ‖f (q.1 - q.2) * g q.2‖)
            = (fun q : G × G => ‖f (q.1 - q.2)‖ * ‖g q.2‖) := by
    ext q
    exact norm_mul _ _
  have h_norm_int' :
      Integrable (fun q : G × G => ‖f (q.1 - q.2)‖ * ‖g q.2‖) (μ.prod μ) := by
    simpa [h_eq] using h_norm_int
  -- Apply the real-valued section integrability lemma
  simpa [leftSection] using
    (integrable_section_of_integrable_prod_nonneg
      (μ:=μ) (ν:=μ)
      (f:=fun q : G × G => ‖f (q.1 - q.2)‖ * ‖g q.2‖)
      h_norm_int')

/--
**Strong version: section integrability at a specific point**

To deduce a pointwise statement we assume that the fibrewise convolution
`y ↦ f (x - y) * g y` is already integrable (e.g. because we control the section by
continuity, decay, or membership in some `Lp`).  This is enough to conclude that the
normed kernel is integrable as well.
-/
theorem integrable_norm_convolution_section_at_point
    {f g : G → ℂ}
    (x : G)
    (h_section_int : Integrable (fun y => f (x - y) * g y) μ) :
    Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ := by
  have h_norm : Integrable (fun y => ‖f (x - y) * g y‖) μ := h_section_int.norm
  have h_eq :
      (fun y => ‖f (x - y) * g y‖)
        = fun y => ‖f (x - y)‖ * ‖g y‖ := by
    funext y; exact norm_mul _ _
  simpa [h_eq] using h_norm

end ConvolutionKernel

end MeasureTheory
