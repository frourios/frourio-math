import Frourio.Analysis.GaussianFourierTransform
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Topology.UniformSpace.UniformEmbedding

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

lemma fourierKernel_neg_div_two_pi (τ t : ℝ) :
    fourierKernel (-τ / (2 * Real.pi)) t = Complex.exp (Complex.I * τ * t) := by
  have hpi : (2 * Real.pi) ≠ 0 := by
    have : (2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero this Real.pi_ne_zero
  have hscale :
      (2 * Real.pi) * (-τ / (2 * Real.pi)) = -τ := by
    have h₂π : (2 * Real.pi) ≠ 0 := hpi
    have hπ : (Real.pi) ≠ 0 := Real.pi_ne_zero
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, h₂π, hπ]
  have hmul :
      -(2 * Real.pi * (-τ / (2 * Real.pi)) * t) = τ * t := by
    have := congrArg (fun x : ℝ => -(x * t)) hscale
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hmul' : Complex.ofReal (τ * t) * Complex.I = Complex.I * τ * t := by
    simp [Complex.ofReal_mul, mul_comm, mul_left_comm]
  simp only [fourierKernel, hmul]
  rw [hmul']

lemma integral_fourierIntegral_rescale_sq (g : ℝ → ℂ) :
    (∫ τ : ℝ, ‖fourierIntegral g (-τ / (2 * Real.pi))‖ ^ 2) =
      (2 * Real.pi) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 := by
  have h :=
    (Measure.integral_comp_mul_left
        (a := -1 / (2 * Real.pi))
        (g := fun ξ : ℝ => ‖fourierIntegral g ξ‖ ^ 2))
  have h_inv : (-1 / (2 * Real.pi))⁻¹ = -(2 * Real.pi) := by
    have : (2 * Real.pi) ≠ 0 := by
      have : (2 : ℝ) ≠ 0 := by norm_num
      exact mul_ne_zero this Real.pi_ne_zero
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have h_abs : |(-1 / (2 * Real.pi))⁻¹| = 2 * Real.pi := by
    have hpos : 0 ≤ 2 * Real.pi := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg this Real.pi_pos.le
    simp [h_inv, abs_neg, abs_of_nonneg hpos]
  have h_smul :
      (|(-1 / (2 * Real.pi))⁻¹| : ℝ)
        • ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 =
          (2 * Real.pi) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 := by
    rw [smul_eq_mul, h_abs]
  have h_simplified :
      (∫ τ : ℝ, ‖fourierIntegral g ((-1) / (2 * Real.pi) * τ)‖ ^ 2)
        = (2 * Real.pi) * ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 := by
    rw [← h_smul]
    exact h
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using h_simplified

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

lemma fourierIntegral_smul (c : ℂ) {f : ℝ → ℂ}
    (_hf : Integrable f) (ξ : ℝ) :
    fourierIntegral (fun t : ℝ => c * f t) ξ
      = c * fourierIntegral f ξ := by
  classical
  calc
    fourierIntegral (fun t : ℝ => c * f t) ξ
        = ∫ t : ℝ, fourierKernel ξ t * (c * f t) := rfl
    _ = ∫ t : ℝ, c • (fourierKernel ξ t * f t) := by
          simp [smul_eq_mul, mul_comm, mul_left_comm]
    _ = c • ∫ t : ℝ, fourierKernel ξ t * f t :=
          (MeasureTheory.integral_smul (μ := volume)
            (c := c) (f := fun t : ℝ => fourierKernel ξ t * f t))
    _ = c * fourierIntegral f ξ := by
          simp [fourierIntegral, smul_eq_mul]

lemma fourierIntegral_add {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    fourierIntegral (fun t : ℝ => f t + g t) ξ
      = fourierIntegral f ξ + fourierIntegral g ξ := by
  classical
  have hf_mul : Integrable (fun t : ℝ => fourierKernel ξ t * f t) :=
    integrable_fourierKernel_mul ξ hf
  have hg_mul : Integrable (fun t : ℝ => fourierKernel ξ t * g t) :=
    integrable_fourierKernel_mul ξ hg
  have h := MeasureTheory.integral_add hf_mul hg_mul
  simpa [fourierIntegral, mul_add, add_comm, add_left_comm, add_assoc]
    using h

lemma fourierIntegral_sub {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    fourierIntegral (fun t : ℝ => f t - g t) ξ
      = fourierIntegral f ξ - fourierIntegral g ξ := by
  classical
  have hg_neg : Integrable (fun t : ℝ => -g t) := hg.neg
  have h_add :=
    fourierIntegral_add (f := f) (g := fun t : ℝ => -g t)
      hf hg_neg ξ
  have h_neg :=
    fourierIntegral_smul (-1 : ℂ) (f := g) hg ξ
  have h_neg' : fourierIntegral (fun t : ℝ => -g t) ξ
      = -fourierIntegral g ξ := by
    simpa [smul_eq_mul] using h_neg
  simpa [sub_eq_add_neg, h_neg'] using h_add

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
  have hneg :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp
      h.aestronglyMeasurable
  simpa [Function.comp] using (hneg.2 h)

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
  -- Rewrite the inversion identity in terms of the explicit conjugated transform.
  have h_eval_real :
      Real.fourierIntegral (conjFourierTransform f) t = conj (f t) := by
    simpa [conjFourierTransform, h_inv_fun_real.symm, fourierIntegral_eq_real]
      using h_eval
  -- Translate the statement back to our explicit kernel formulation.
  have h_eval_fourier :
      fourierIntegral (conjFourierTransform f) t = conj (f t) := by
    simpa [fourierIntegral_eq_real] using h_eval_real
  simpa [doubleFourierTransform] using h_eval_fourier

/-- Smooth compactly supported functions can be approximated by Schwartz functions in L²(ℝ) -/
lemma schwartz_approximates_smooth_compactly_supported (g : ℝ → ℂ)
    (hg_compact : HasCompactSupport g) (hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (ε : ℝ) (hε_pos : ε > 0) :
    ∃ φ : SchwartzMap ℝ ℂ, eLpNorm (g - (φ : ℝ → ℂ)) 2 volume < ENNReal.ofReal ε := by
  classical
  -- Show that every derivative of `g` is bounded by taking the maximum on the compact support.
  have hg_schwartz : ∀ k n : ℕ, ∃ C : ℝ,
      ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    intro k n
    classical
    set K := tsupport g with hK_def
    have hK_compact : IsCompact K := by
      simpa [hK_def] using hg_compact
    set h : ℝ → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖
    have h_nonneg : ∀ x, 0 ≤ h x := by
      intro x
      exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    have hK_subset : tsupport (iteratedFDeriv ℝ n g) ⊆ K := by
      simpa [hK_def] using
        (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := g) (n := n))
    by_cases h_support_empty :
        tsupport (iteratedFDeriv ℝ n g) = (∅ : Set ℝ)
    · refine ⟨0, ?_⟩
      intro x
      have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := by
        simp [h_support_empty]
      have hx_zero : iteratedFDeriv ℝ n g x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      simp [hx_zero]
    · have h_support_nonempty :
          (tsupport (iteratedFDeriv ℝ n g)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr (by simpa using h_support_empty)
      obtain ⟨x₀, hx₀_support⟩ := h_support_nonempty
      have hx₀K : x₀ ∈ K := hK_subset hx₀_support
      have h_pow_cont : Continuous fun x : ℝ => ‖x‖ ^ k :=
        (continuous_norm : Continuous fun x : ℝ => ‖x‖).pow _
      have h_iter_cont :
          Continuous fun x : ℝ => iteratedFDeriv ℝ n g x :=
        (hg_smooth.continuous_iteratedFDeriv (hm := by
          exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))))
      have h_cont : Continuous h := h_pow_cont.mul (h_iter_cont.norm)
      have h_image_compact : IsCompact (h '' K) := hK_compact.image h_cont
      have h_image_nonempty : (h '' K).Nonempty := ⟨h x₀, ⟨x₀, hx₀K, rfl⟩⟩
      obtain ⟨C, hC_isGreatest⟩ :=
        h_image_compact.exists_isGreatest h_image_nonempty
      obtain ⟨⟨xC, hxC_K, rfl⟩, hC_max⟩ := hC_isGreatest
      refine ⟨h xC, ?_⟩
      intro x
      by_cases hxK : x ∈ K
      · have hx_mem : h x ∈ h '' K := ⟨x, hxK, rfl⟩
        exact hC_max hx_mem
      · have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := fun hx => hxK (hK_subset hx)
        have hx_zero : iteratedFDeriv ℝ n g x = 0 :=
          image_eq_zero_of_notMem_tsupport hx_not
        have h_nonneg_xC : 0 ≤ h xC := h_nonneg xC
        have hx_val : h x = 0 := by simp [h, hx_zero]
        have hx_le : h x ≤ h xC := by simpa [hx_val] using h_nonneg_xC
        simpa [h] using hx_le
  -- Construct the Schwartz function associated to `g`.
  let φ : SchwartzMap ℝ ℂ := ⟨g, hg_smooth, hg_schwartz⟩
  have h_diff_zero : g - (φ : ℝ → ℂ) = (fun _ => 0 : ℝ → ℂ) := by
    funext x
    change g x - g x = 0
    simp
  have h_eLp_zero :
      eLpNorm (g - (φ : ℝ → ℂ)) 2 volume = 0 := by
    simp [h_diff_zero]
  refine ⟨φ, ?_⟩
  have hε_pos' : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε_pos
  simpa [h_eLp_zero] using hε_pos'

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

/-!
### L² Fourier transform surjectivity

The following lemmas establish that the L² Fourier transform is surjective,
which is needed to construct the unitary equivalence on `Lp ℂ 2 volume`.
-/

/-- The range of a linear isometry between complete spaces is closed. -/
lemma LinearIsometry.range_closed
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace E] (U : E →ₗᵢ[ℂ] F) :
    IsClosed (Set.range U) := by
  -- Strategy: Use Isometry.isClosedEmbedding from mathlib
  -- An isometry from a complete emetric space is a closed embedding
  -- A closed embedding has closed range

  -- Apply Isometry.isClosedEmbedding to get that U is a closed embedding
  have h_closed_emb : Topology.IsClosedEmbedding (U : E → F) := by
    -- This requires showing U.isometry (which we have from LinearIsometry)
    -- and CompleteSpace E (which we have as hypothesis)
    exact U.isometry.isClosedEmbedding

  -- A closed embedding has closed range
  exact h_closed_emb.isClosed_range

/-- If a subset of a topological space is both dense and closed, it equals the whole space. -/
lemma dense_closed_eq_univ {α : Type*} [TopologicalSpace α]
    {s : Set α} (h_dense : Dense s) (h_closed : IsClosed s) :
    s = Set.univ := by
  have h_closure_univ : closure s = (Set.univ : Set α) := Dense.closure_eq h_dense
  have h_closure_eq : closure s = s := h_closed.closure_eq
  simpa [h_closure_eq] using h_closure_univ

/-- A linear isometry from a complete space to itself with dense range is surjective.
This follows from the fact that isometries have closed range in complete spaces. -/
lemma LinearIsometry.surjective_of_dense_range
    {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (U : E →ₗᵢ[ℂ] E) (h_dense : Dense (Set.range U)) :
    Function.Surjective U := by
  -- Strategy: show `range U` is closed, hence closed ∧ dense ⇒ `range U = univ`,
  -- then any `y : E` lies in the range and has a preimage.
  intro y
  -- The range is closed for an isometry with complete domain/codomain.
  have h_closed : IsClosed (Set.range U) :=
    LinearIsometry.range_closed (E := E) (F := E) U
  -- Closed and dense subset equals the whole space.
  have h_univ : Set.range U = Set.univ :=
    dense_closed_eq_univ (α := E) (s := Set.range U) h_dense h_closed
  -- Conclude surjectivity: every `y` belongs to the range, so `∃ x, U x = y`.
  have hy : y ∈ Set.range U := by
    simp [h_univ]
  rcases hy with ⟨x, rfl⟩
  exact ⟨x, rfl⟩

end Frourio
