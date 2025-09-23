import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz

/-!
# Fourier–Plancherel infrastructure on `ℝ`

This file prepares the ingredients required for the Fourier–Plancherel theorem on the real
line.  The goal is to express the Fourier integral in the more familiar `e^{-2π i x ξ}` form and to
record basic properties (measurability, integrability, norm preservation of the kernel) that are
frequently used when extending the Fourier transform from Schwartz functions to the `L²` setting.

The actual isometry statement is postponed to a later stage; here we progressively organise the
supporting lemmas so that subsequent files can invoke them without having to unfold the Fourier
kernel repeatedly.
-/

noncomputable section

open scoped FourierTransform RealInnerProductSpace

namespace Frourio

open MeasureTheory Complex Real SchwartzMap

/-- Fourier kernel on `ℝ`, written explicitly as `exp(-2π i t ξ)`. -/
def fourierKernel (ξ t : ℝ) : ℂ :=
  Complex.exp (Complex.ofReal (-(2 * π * ξ * t)) * Complex.I)

@[simp] lemma fourierKernel_zero_left (t : ℝ) : fourierKernel 0 t = 1 := by
  simp [fourierKernel]

@[simp] lemma fourierKernel_zero_right (ξ : ℝ) : fourierKernel ξ 0 = 1 := by
  simp [fourierKernel]

lemma fourierKernel_norm (ξ t : ℝ) : ‖fourierKernel ξ t‖ = 1 := by
  have hre : (Complex.ofReal (-(2 * π * ξ * t)) * Complex.I).re = 0 := by simp
  simp [fourierKernel, Complex.norm_exp]

lemma fourierKernel_mul_eq (ξ t : ℝ) (z : ℂ) :
    fourierKernel ξ t * z = ((Real.fourierChar (-(t * ξ))) : Circle) • z := by
  simp [fourierKernel, Circle.smul_def, Real.fourierChar_apply, mul_comm, mul_left_comm,
    mul_assoc]

lemma fourierKernel_eq_char (ξ t : ℝ) :
    fourierKernel ξ t = ((Real.fourierChar (-(t * ξ))) : ℂ) := by
  simp [fourierKernel, Real.fourierChar_apply, mul_comm, mul_left_comm, mul_assoc]

lemma fourierKernel_mul_norm (ξ t : ℝ) (z : ℂ) :
    ‖fourierKernel ξ t * z‖ = ‖z‖ := by
  simp [fourierKernel_norm ξ t]

section integrability

open scoped Topology

lemma integrable_fourierKernel_mul_iff {f : ℝ → ℂ} (ξ : ℝ) :
    Integrable (fun t => fourierKernel ξ t * f t) ↔ Integrable f := by
  classical
  have h := Real.fourierIntegral_convergent_iff (μ := volume)
      (f := fun t : ℝ => f t) (w := ξ)
  have hchar : (fun t : ℝ => ((Real.fourierChar (-(ξ * t))) : Circle) • f t)
      = fun t : ℝ => fourierKernel ξ t * f t := by
    funext t
    have hcomm : ((Real.fourierChar (-(ξ * t))) : ℂ)
        = ((Real.fourierChar (-(t * ξ))) : ℂ) := by simp [mul_comm]
    simp [fourierKernel_mul_eq, Circle.smul_def, hcomm]
  constructor
  · intro hf
    have hf' : Integrable (fun t : ℝ => ((Real.fourierChar (-(ξ * t))) : Circle) • f t) := by
      simpa [hchar] using hf
    exact h.mp hf'
  · intro hf
    have hf' := h.mpr hf
    simpa [hchar] using hf'

lemma integrable_fourierKernel_mul {f : ℝ → ℂ} (ξ : ℝ) (hf : Integrable f) :
    Integrable (fun t => fourierKernel ξ t * f t) :=
  (integrable_fourierKernel_mul_iff (f := f) ξ).2 hf

end integrability

/-- The Fourier integral expressed via the explicit kernel. -/
def fourierIntegral (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ t : ℝ, fourierKernel ξ t * f t

lemma fourierIntegral_eq_real (f : ℝ → ℂ) (ξ : ℝ) :
    Real.fourierIntegral f ξ = fourierIntegral f ξ := by
  classical
  simp [fourierIntegral, Real.fourierIntegral_real_eq, Circle.smul_def,
    fourierKernel_eq_char, mul_comm]

lemma norm_fourierIntegral_le (f : ℝ → ℂ) (ξ : ℝ) :
    ‖fourierIntegral f ξ‖ ≤ ∫ t : ℝ, ‖f t‖ := by
  have := norm_integral_le_integral_norm (μ := volume)
      (f := fun t : ℝ => fourierKernel ξ t * f t)
  have hnorm : (fun t : ℝ => ‖fourierKernel ξ t‖ * ‖f t‖) = fun t : ℝ => ‖f t‖ := by
    funext t; simp [fourierKernel_norm ξ t]
  simpa [fourierIntegral, hnorm]

/-- Equality of squared norms of the integrand, used repeatedly when working with
`L²` functions. -/
lemma integrand_norm_sq (ξ t : ℝ) (f : ℝ → ℂ) :
    ‖fourierKernel ξ t * f t‖ ^ 2 = ‖f t‖ ^ 2 := by
  simp [pow_two, fourierKernel_norm ξ t, mul_comm]

/-- Helper lemma for rewriting the pointwise value of the Fourier integral in terms of the
explicit kernel. -/
lemma fourierIntegral_apply (f : ℝ → ℂ) (ξ : ℝ) :
    fourierIntegral f ξ = ∫ t : ℝ, fourierKernel ξ t * f t := rfl

/-- Pointwise boundedness for the explicit kernel formulation. -/
lemma fourierIntegral_abs_le (f : ℝ → ℂ) (ξ : ℝ) :
    ‖fourierIntegral f ξ‖ ≤ ∫ t : ℝ, ‖f t‖ :=
  norm_fourierIntegral_le f ξ

/-! ### Behaviour on Schwartz functions -/

namespace Schwartz

/-- Multiplying a Schwartz function by the Fourier kernel keeps it integrable. -/
lemma integrable_fourierKernel_mul (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    Integrable (fun t : ℝ => fourierKernel ξ t * f t) := by
  classical
  refine Frourio.integrable_fourierKernel_mul ξ ?_
  simpa using f.integrable

/-- Identify our explicit kernel formulation with mathlib's Fourier transform on Schwartz
functions. -/
lemma fourierIntegral_eq_fourierTransform (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    fourierIntegral (fun t : ℝ => f t) ξ =
      (fourierTransformCLE ℝ f) ξ := by
  classical
  calc
    fourierIntegral (fun t : ℝ => f t) ξ
        = Real.fourierIntegral (fun t : ℝ => f t) ξ := by
            simpa using (fourierIntegral_eq_real (fun t : ℝ => f t) ξ).symm
    _ = (fourierTransformCLE ℝ f) ξ := by
            simp [fourierTransformCLE_apply]

end Schwartz

/-!
### Towards Fourier–Plancherel

The lemmas collected above allow us to treat the Fourier transform in its classical exponential
form inside `L²` developments.  The remaining step – extending the transform to a unitary map on
`L²(ℝ)` – will rely on the density of Schwartz functions together with the continuity of the
Fourier transform; this part is deferred to future work.
-/

/-- Skeleton of the Fourier–Plancherel theorem:
`‖f‖_{L²} = (1 / (2π)) * ‖𝓕 f‖_{L²}` for sufficiently nice functions.

The current lemma serves as a placeholder documenting the intended statement and the normalising
constant.  The actual proof will be supplied once the necessary extension machinery has been fully
formalised. -/
lemma fourier_plancherel_placeholder
    (f : ℝ → ℂ) (hf : Integrable f) :
    ∫ t : ℝ, ‖f t‖ ^ 2 = (1 / (2 * Real.pi)) * ∫ ξ : ℝ, ‖fourierIntegral f ξ‖ ^ 2 := by
  -- TODO: develop the full Fourier–Plancherel machinery and replace this placeholder with the
  -- genuine isometry statement proved for Schwartz functions and extended to `L²` by density.
  sorry

end Frourio
