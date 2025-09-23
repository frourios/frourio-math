import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Frourio.Analysis.GaussianFourierTransform

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

open MeasureTheory Filter Complex Real SchwartzMap

open scoped ComplexConjugate

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

lemma fourierKernel_conj (ξ t : ℝ) :
    conj (fourierKernel ξ t) = fourierKernel (-ξ) t := by
  classical
  have hnorm := fourierKernel_norm ξ t
  have hnonzero : fourierKernel ξ t ≠ 0 := by
    have : ‖fourierKernel ξ t‖ ≠ 0 := by
      simp [hnorm]
    intro hzero
    apply this
    simp [hzero]
  have hinv : fourierKernel (-ξ) t = (fourierKernel ξ t)⁻¹ := by
    unfold fourierKernel
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Complex.exp_neg (Complex.ofReal (-(2 * π * ξ * t)) * Complex.I))
  have hunit : fourierKernel ξ t * conj (fourierKernel ξ t) = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  have hconj_inv : conj (fourierKernel ξ t) = (fourierKernel ξ t)⁻¹ := by
    have := congrArg (fun z => z * (fourierKernel ξ t)⁻¹) hunit
    simpa [hnonzero, mul_comm, mul_left_comm, mul_assoc] using this
  simpa [hinv]

lemma fourierKernel_neg (ξ t : ℝ) : fourierKernel (-ξ) t = conj (fourierKernel ξ t) := by
  simp [fourierKernel_conj]

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

lemma integrable_conj_of_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ) :
    Integrable (fun t => conj (f t)) μ := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable, ?_⟩
  have hnorm : ∀ᵐ t ∂μ, ‖f t‖ = ‖conj (f t)‖ :=
    Filter.Eventually.of_forall fun _ => by simp
  exact hf.hasFiniteIntegral.congr' hnorm

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

lemma fourierIntegral_conj {f : ℝ → ℂ} (_hf : Integrable f) (ξ : ℝ) :
    conj (fourierIntegral f ξ) =
      fourierIntegral (fun t => conj (f t)) (-ξ) := by
  classical
  have h :=
    (integral_conj (μ := volume) (f := fun t : ℝ => fourierKernel ξ t * f t)).symm
  have hpoint :
      (fun t : ℝ => (starRingEnd ℂ) (fourierKernel ξ t) * (starRingEnd ℂ) (f t))
        = fun t : ℝ => fourierKernel (-ξ) t * conj (f t) := by
    funext t
    simp [fourierKernel_conj]
  have h' :
      conj (∫ t : ℝ, fourierKernel ξ t * f t) =
        ∫ t : ℝ, fourierKernel (-ξ) t * conj (f t) := by
    simpa [hpoint]
      using h
  simpa [fourierIntegral] using h'

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

/-- Conjugating a Schwartz function before applying the Fourier integral is the same as
conjugating the transform and negating the frequency. -/
lemma fourierIntegral_conj_eq_neg (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    fourierIntegral (fun t : ℝ => conj (f t)) ξ =
      conj (fourierIntegral (fun t : ℝ => f t) (-ξ)) := by
  classical
  have hf : Integrable (fun t : ℝ => f t) := f.integrable
  have h := fourierIntegral_conj (f := fun t : ℝ => f t) hf (-ξ)
  -- `h` rewrites the conjugated transform; rearrange the equality.
  simpa using h.symm

/-- Real-notation variant of `fourierIntegral_conj_eq_neg`. -/
lemma fourierIntegral_conj_eq_neg_real (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    Real.fourierIntegral (fun t : ℝ => conj (f t)) ξ =
      conj (Real.fourierIntegral (fun t : ℝ => f t) (-ξ)) := by
  classical
  simpa [fourierIntegral_eq_real (fun t : ℝ => conj (f t)) ξ,
    fourierIntegral_eq_real (fun t : ℝ => f t) (-ξ)]
    using fourierIntegral_conj_eq_neg (f := f) ξ

lemma integrable_fourierIntegral (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => fourierIntegral (fun t : ℝ => f t) ξ) := by
  classical
  simpa [fourierIntegral_eq_fourierTransform] using
    (fourierTransformCLE ℝ f).integrable

/-- The Fourier transform of a Schwartz function remains integrable after negating the frequency.
-/
lemma integrable_fourierIntegral_neg (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => fourierIntegral (fun t : ℝ => f t) (-ξ)) := by
  classical
  have h := integrable_fourierIntegral f
  have :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable h
  simpa [Function.comp] using this

/-- The conjugate of the Fourier transform of a Schwartz function is integrable. -/
lemma integrable_conj_fourierIntegral (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => conj (fourierIntegral (fun t : ℝ => f t) ξ)) := by
  classical
  exact integrable_conj_of_integrable (integrable_fourierIntegral f)

/-- The conjugated Fourier transform as a function. -/
def conjFourierTransform (f : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  fun ξ : ℝ => conj (fourierIntegral (fun t : ℝ => f t) ξ)

/-- The Fourier integral of the conjugated Fourier transform. -/
def doubleFourierTransform (f : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  fourierIntegral (conjFourierTransform f)

/-- Taking the Fourier integral of the conjugated Fourier transform recovers the conjugate. -/
lemma fourierIntegral_conj_fourierIntegral (f : SchwartzMap ℝ ℂ) :
    doubleFourierTransform f = fun t : ℝ => conj (f t) := by
  classical
  -- Basic integrability facts for `f` and its transforms.
  have hf : Integrable (fun t : ℝ => f t) := f.integrable
  have h_conj_f : Integrable (fun t : ℝ => conj (f t)) :=
    integrable_conj_of_integrable hf
  have hF : Integrable (fun ξ : ℝ => fourierIntegral (fun t : ℝ => f t) ξ) :=
    integrable_fourierIntegral f
  have hF_conj : Integrable (conjFourierTransform f) :=
    integrable_conj_fourierIntegral f
  have hF_neg : Integrable (fun ξ : ℝ => fourierIntegral (fun t : ℝ => f t) (-ξ)) :=
    integrable_fourierIntegral_neg f
  -- Deduce integrability of the Fourier transform of the conjugate function via the previous lemma.
  have h_fourier_conj : Integrable (𝓕 (fun t : ℝ => conj (f t))) := by
    have h1 := integrable_conj_of_integrable hF_neg
    have h2 : (fun ξ : ℝ => fourierIntegral (fun t : ℝ => conj (f t)) ξ) =
              (fun ξ : ℝ => 𝓕 (fun t : ℝ => conj (f t)) ξ) := by
      funext ξ
      exact (fourierIntegral_eq_real (fun t : ℝ => conj (f t)) ξ).symm
    simpa [fourierIntegral_conj_eq_neg, ← h2] using h1
  -- Express the conjugated transform as the inverse Fourier transform of the conjugated function.
  have h_inv_fun_real :
      (fun ξ : ℝ => conj (Real.fourierIntegral (fun t : ℝ => f t) ξ))
        = Real.fourierIntegralInv (fun t : ℝ => conj (f t)) := by
    funext ξ
    simpa [fourierIntegralInv_eq_fourierIntegral_neg]
      using (fourierIntegral_conj_eq_neg_real (f := f) (-ξ)).symm
  -- Continuity of the conjugated Schwartz function.
  have h_cont : Continuous fun t : ℝ => conj (f t) :=
    Complex.continuous_conj.comp f.continuous
  -- Apply Fourier inversion to the conjugated function.
  have h_inversion :=
    Continuous.fourier_inversion h_cont h_conj_f h_fourier_conj
  -- Function evaluation
  funext t
  -- Transfer the identity to the standard Fourier integral using the commutation lemma.
  have h_comm := fourierIntegralInv_comm (fun t : ℝ => conj (f t))
  have h_comm_t := congrArg (fun g => g t) h_comm
  have h_inversion_t := congrArg (fun g => g t) h_inversion
  have h_eval := h_comm_t.trans h_inversion_t
  -- Replace the intermediate inverse transform by the conjugated Fourier transform.
  have h_conjFT_eq : 𝓕 (conjFourierTransform f) =
      𝓕 (fun ξ : ℝ => conj (𝓕 (fun t : ℝ => f t) ξ)) := by
    congr
    funext ξ
    simp [conjFourierTransform, fourierIntegral_eq_real]
  have h_eval' :
      𝓕 (conjFourierTransform f) t = conj (f t) := by
    rw [h_conjFT_eq]
    simpa [h_inv_fun_real.symm] using h_eval
  -- Translate the statement back to our explicit kernel formulation.
  simpa [doubleFourierTransform, fourierIntegral_eq_real] using h_eval'

end Schwartz

/-!
### Towards Fourier–Plancherel

The lemmas collected above allow us to treat the Fourier transform in its classical exponential
form inside `L²` developments.  The remaining step – extending the transform to a unitary map on
`L²(ℝ)` – will rely on the density of Schwartz functions together with the continuity of the
Fourier transform; this part is deferred to future work.
-/

/-- Fourier–Plancherel theorem for Schwartz functions written with the explicit kernel
`exp (-2π i ξ t)`.

With this normalisation the Fourier transform is an isometry on `L²`, so no additional constant
appears in the equality. -/
lemma fourier_plancherel (f : SchwartzMap ℝ ℂ) :
    ∫ t : ℝ, ‖f t‖ ^ 2 = ∫ ξ : ℝ, ‖fourierIntegral (fun t : ℝ => f t) ξ‖ ^ 2 := by
  classical
  -- Shorthand for the Fourier transform of `f`.
  set F : ℝ → ℂ := fun ξ => Real.fourierIntegral (fun t : ℝ => f t) ξ
  -- All integrability assertions required by the self-adjointness lemma.
  have hf : Integrable (fun t : ℝ => f t) := f.integrable
  have hF : Integrable F := by
    simpa [F, fourierIntegral_eq_real] using Schwartz.integrable_fourierIntegral f
  have hF_conj : Integrable (fun ξ : ℝ => conj (F ξ)) := by
    simpa [F, fourierIntegral_eq_real] using Schwartz.integrable_conj_fourierIntegral f
  -- Self-adjointness of the Fourier transform written with the explicit kernel.
  have h_selfAdj :=
    VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
      (L := innerₗ ℝ) (f := fun t : ℝ => f t)
      (g := fun ξ : ℝ => conj (F ξ))
      Real.continuous_fourierChar
      (by continuity) hf hF_conj
  -- Rewrite the result in a more concrete form.
  have h_eq' :
      ∫ ξ : ℝ, F ξ * conj (F ξ)
        = ∫ t : ℝ, f t *
            Real.fourierIntegral (fun ξ : ℝ => conj (F ξ)) t := by
    simpa [F, smul_eq_mul] using h_selfAdj
  have h_fourier_conj :
      Real.fourierIntegral (fun ξ : ℝ => conj (F ξ)) = fun t : ℝ => conj (f t) := by
    have h_main := Schwartz.fourierIntegral_conj_fourierIntegral f
    have h_conv : Schwartz.doubleFourierTransform f =
                  Real.fourierIntegral (Schwartz.conjFourierTransform f) := by
      simp [Schwartz.doubleFourierTransform]
      funext t
      exact (fourierIntegral_eq_real (Schwartz.conjFourierTransform f) t).symm
    have h_conj_conv : Schwartz.conjFourierTransform f =
                       fun ξ : ℝ => conj (F ξ) := by
      funext ξ
      simp [Schwartz.conjFourierTransform, F, fourierIntegral_eq_real]
    rw [h_conv, h_conj_conv] at h_main
    exact h_main
  have h_eq : ∫ ξ : ℝ, F ξ * conj (F ξ) = ∫ t : ℝ, f t * conj (f t) := by
    simpa [h_fourier_conj] using h_eq'
  -- Identify both sides with the corresponding squared norms.
  have h_left :
      (fun ξ : ℝ => F ξ * conj (F ξ)) = fun ξ : ℝ => (‖F ξ‖ ^ 2 : ℂ) := by
    funext ξ
    simp [F, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two]
  have h_right :
      (fun t : ℝ => f t * conj (f t)) = fun t : ℝ => (‖f t‖ ^ 2 : ℂ) := by
    funext t
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two]
  -- Translate the complex-valued identity into the desired real statement.
  have h_complex : ∫ ξ : ℝ, (‖F ξ‖ ^ 2 : ℂ) = ∫ t : ℝ, (‖f t‖ ^ 2 : ℂ) := by
    simpa [← h_left, ← h_right] using h_eq
  -- Convert the complex equality to real equality
  have h_real : ∫ ξ : ℝ, ‖F ξ‖ ^ 2 = ∫ t : ℝ, ‖f t‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [← integral_ofReal', ← integral_ofReal']
    convert h_complex
    · simp
    · simp
  simpa [F, fourierIntegral_eq_real] using h_real.symm

end Frourio
