import Frourio.Analysis.Gaussian
import Frourio.Analysis.ZakMellin
import Frourio.Analysis.GaussianContourShiftReal
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Data.ENNReal.Basic

/-!
# Gaussian Moments and Fourier Properties

This file contains lemmas about moments of Gaussian functions and their Fourier transforms,
specifically supporting the frame condition proof in `exists_golden_peak_proof`.
-/

namespace Frourio

noncomputable section

open Real Complex MeasureTheory Measure FourierTransform ENNReal

variable {δ : ℝ} (hδ : 0 < δ)

-- Canonical L² witness for the normalized Gaussian, to avoid `.val`
def normalizedGaussianLp (δ : ℝ) (hδ : 0 < δ) : Lp ℂ 2 (volume : Measure ℝ) :=
  Classical.choose (build_normalized_gaussian δ hδ)

/--
A helper lemma showing that A / √δ * δ = A * √δ for positive δ.
This simplifies the algebraic manipulation in the Gaussian Fourier transform proof.
-/
lemma div_sqrt_mul_delta {A : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    A / ↑(Real.sqrt δ) * ↑δ = A * ↑(Real.sqrt δ) := by
  set s : ℂ := (↑(Real.sqrt δ) : ℂ)
  have hs_ne : s ≠ 0 := by
    have hsqrt_pos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    simp [s, Complex.ofReal_eq_zero, (ne_of_gt hsqrt_pos)]
  have hs_sq : (↑δ : ℂ) = s * s := by
    have : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt (le_of_lt hδ)
    simpa [s, Complex.ofReal_mul] using congrArg Complex.ofReal this.symm
  calc
    A / s * (↑δ : ℂ)
        = A / s * (s * s) := by simp [hs_sq]
    _ = A * s⁻¹ * (s * s) := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = (A * s⁻¹ * s) * s := by
      simp [mul_assoc]
    _ = (A * (s⁻¹ * s)) * s := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (A * 1) * s := by
      simp [hs_ne]
    _ = A * s := by simp

/--
Helper lemma: δ² * δ⁻² = 1 in complex numbers
-/
lemma delta_sq_inv_sq {δ : ℝ} (hδ : 0 < δ) :
    ((↑δ : ℂ) * ↑δ) * ((↑δ)⁻¹ * (↑δ)⁻¹) = 1 := by
  -- Rewrite as (δ² * δ⁻²)
  rw [← sq, ← sq]
  -- Now we have δ² * (δ⁻¹)²
  -- Use the fact that (x⁻¹)² = (x²)⁻¹
  have inv_sq : ((↑δ : ℂ)⁻¹)^2 = ((↑δ : ℂ)^2)⁻¹ := by
    rw [sq, sq]
    -- Now we have: (δ⁻¹ * δ⁻¹) = (δ * δ)⁻¹
    rw [mul_inv]
  rw [inv_sq]
  -- Now we have δ² * (δ²)⁻¹ = 1
  have mul_inv : (↑δ : ℂ)^2 * ((↑δ : ℂ)^2)⁻¹ = 1 := by
    have h : (↑δ : ℂ)^2 ≠ 0 := by
      apply pow_ne_zero
      simp [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hδ
    exact mul_inv_cancel₀ h
  exact mul_inv

/--
Helper lemma for completing the square calculation.
Shows that -π/δ² * (t + I*δ²*ξ)² + π/δ² * (-1) * (δ²)² * ξ² = -π/δ² * (t + I*δ²*ξ)² - π*δ²*ξ²
-/
lemma complete_square_simplify {δ : ℝ} (hδ : 0 < δ) (ξ t : ℝ) :
    -↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2 + ↑π / ↑δ^2 * (-1) * (↑δ^2)^2 * ↑ξ^2 =
    -↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2 := by
  -- Show that π / δ^2 * (-1) * (δ^2)^2 * ξ^2 = -π * δ^2 * ξ^2
  have ne_zero : (↑δ : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hδ
  -- The key equality: π/δ² * (-1) * δ⁴ * ξ² = -π * δ² * ξ²
  field_simp [ne_zero]
  ring

/--
Complete the square in the exponent appearing in Gaussian integrals.
This is the algebraic identity
`-π/δ² * t² - 2π I ξ t = -π/δ² (t + I δ² ξ)² - π δ² ξ²` over the complex numbers.
-/
lemma gaussian_exponent_complete_square {δ : ℝ} (hδ : 0 < δ) (ξ t : ℝ) :
    -↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t =
    -↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2 := by
  -- Expand and regroup using the auxiliary simplification lemma
  calc
    -↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t
        = -↑π / ↑δ^2 * (↑t^2 + 2 * ↑t * I * ↑δ^2 * ↑ξ + (I * ↑δ^2 * ↑ξ)^2) +
            ↑π / ↑δ^2 * (I * ↑δ^2 * ↑ξ)^2 := by
          have ne_zero : (↑δ : ℂ) ≠ 0 := by
            simp only [ne_eq, Complex.ofReal_eq_zero]
            exact ne_of_gt hδ
          field_simp [ne_zero]
          ring
    _ = -↑π / ↑δ^2 * (↑t^2 + 2 * ↑t * I * ↑δ^2 * ↑ξ + (I * ↑δ^2 * ↑ξ)^2) +
            ↑π / ↑δ^2 * (-1) * (↑δ^2)^2 * ↑ξ^2 := by
          have : (I * ↑δ^2 * ↑ξ)^2 = I^2 * (↑δ^2)^2 * ↑ξ^2 := by ring
          rw [this, Complex.I_sq]
          ring
    _ = -↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2 := by
          have : (↑t + I * ↑δ^2 * ↑ξ)^2 = ↑t^2 + 2 * ↑t * I * ↑δ^2 * ↑ξ +
              (I * ↑δ^2 * ↑ξ)^2 := by ring
          rw [← this]
          exact complete_square_simplify hδ ξ t

/--
Complex contour shift for Gaussian integrals.
For a Gaussian function, shifting the integration contour by a purely imaginary constant
doesn't change the integral value. This is a consequence of Cauchy's theorem for entire functions
with sufficient decay.
-/
lemma complex_gaussian_contour_shift {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
  simpa using gaussian_contour_shift_real hδ ξ


/--
Helper lemma for integral_ofReal with specific type signatures.
-/
@[simp]
lemma integral_ofReal' {f : ℝ → ℝ} :
    (∫ x : ℝ, ↑(f x) : ℂ) = ↑(∫ x : ℝ, f x) := by
  exact integral_ofReal

/--
Standard complex Gaussian integral.
The integral of exp(-π/δ² * s²) over ℝ equals δ.
This is the complex version of the standard Gaussian integral formula.
-/
lemma gaussian_integral_complex {δ : ℝ} (hδ : 0 < δ) :
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) = ↑δ := by
  -- First, convert the complex exponential to real exponential
  have : ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) =
         ∫ s : ℝ, ↑(Real.exp (-π / δ^2 * s^2)) := by
    congr 1
    ext s
    have h : (-↑π / ↑δ^2 * ↑s^2 : ℂ) = ↑(-π / δ^2 * s^2) := by
      push_cast
      ring
    rw [h, Complex.ofReal_exp]
  rw [this]

  -- Now we have ∫ (s : ℝ), ↑(Real.exp (-π / δ^2 * s^2))
  -- This equals ↑(∫ (s : ℝ), Real.exp (-π / δ^2 * s^2))
  rw [integral_ofReal']

  -- Apply the standard Gaussian integral formula
  have gaussian_formula : ∫ s : ℝ, Real.exp (-π / δ^2 * s^2) = δ := by
    -- Use the standard Gaussian integral: ∫ exp(-ax²) dx = √(π/a)
    -- With a = π/δ², we get √(π/(π/δ²)) = √(δ²) = δ
    have h_pos : 0 < π / δ^2 := by
      apply div_pos Real.pi_pos
      exact sq_pos_of_pos hδ

    convert integral_gaussian (π / δ^2) using 2
    -- The standard formula gives √(π/a) = √(π/(π/δ²)) = √(δ²) = δ
    · ext x
      simp only [neg_div, neg_mul]
    · have : π / (π / δ ^ 2) = δ ^ 2 := by
        field_simp
      rw [this, Real.sqrt_sq (le_of_lt hδ)]

  exact_mod_cast gaussian_formula

/--
Shifted Gaussian integral formula.
The integral of exp(-π/δ²(t + Iδ²ξ)²) over ℝ equals δ.
This represents a Gaussian shifted by a pure imaginary amount.
-/
lemma shifted_gaussian_integral {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ t : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2) = ↑δ := by
  have hshift := complex_gaussian_contour_shift hδ ξ
  have hgauss := gaussian_integral_complex hδ
  simpa using hshift.trans hgauss


/--
Complex shifted Gaussian integral formula.
The integral of exp(-π/δ²(t + Iδ²ξ)²) over ℝ equals δ.
-/
lemma complex_shifted_gaussian_integral {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ t : ℝ, Complex.exp (-π / δ^2 * (t + I * δ^2 * ξ)^2) = δ := by
  -- Expand the square (t + I * δ^2 * ξ)^2
  have expand_sq : ∀ t : ℝ, (↑t + I * ↑δ^2 * ↑ξ)^2 =
                            ↑t^2 + 2 * ↑t * I * ↑δ^2 * ↑ξ - (↑δ^2)^2 * ↑ξ^2 := by
    intro t
    have : (↑t + I * ↑δ^2 * ↑ξ)^2 = ↑t^2 + 2 * ↑t * I * ↑δ^2 * ↑ξ + (I * ↑δ^2 * ↑ξ)^2 := by ring
    rw [this]
    have I_sq : I^2 = -1 := Complex.I_sq
    rw [show (I * ↑δ^2 * ↑ξ)^2 = I^2 * (↑δ^2)^2 * ↑ξ^2 by ring]
    rw [I_sq]
    ring

  -- Rewrite the integral using the expansion
  conv_lhs =>
    arg 2
    intro t
    rw [show -↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2 =
             -↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t + ↑π * ↑δ^2 * ↑ξ^2 by
      rw [expand_sq t]
      have ne_zero : (↑δ : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact ne_of_gt hδ
      field_simp [ne_zero]
      ring]

  -- Split the exponential: exp(a + b + c) = exp(a) * exp(b) * exp(c)
  conv_lhs =>
    arg 2
    intro t
    rw [show Complex.exp (-↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t + ↑π * ↑δ^2 * ↑ξ^2) =
        Complex.exp (-↑π / ↑δ^2 * ↑t^2) * Complex.exp (-2 * ↑π * I * ↑ξ * ↑t) *
          Complex.exp (↑π * ↑δ^2 * ↑ξ^2) by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring]

  -- Factor out the constant exp(π * δ^2 * ξ^2)
  rw [show (∫ t : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑t^2) *
                     Complex.exp (-2 * ↑π * I * ↑ξ * ↑t) *
                     Complex.exp (↑π * ↑δ^2 * ↑ξ^2)) =
           Complex.exp (↑π * ↑δ^2 * ↑ξ^2) *
           (∫ t : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑t^2) * Complex.exp (-2 * ↑π * I * ↑ξ * ↑t)) by
    rw [← integral_const_mul]
    congr 1
    ext t
    ring]

  -- Apply the Gaussian Fourier transform formula
  have gaussian_fourier :
      ∫ t : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑t^2) * Complex.exp (-2 * ↑π * I * ↑ξ * ↑t) =
      ↑δ * Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) := by
    -- Combine the exponentials
    have combine : ∀ t : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑t^2) * Complex.exp (-2 * ↑π * I * ↑ξ * ↑t) =
                            Complex.exp (-↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t) := by
      intro t
      rw [← Complex.exp_add]
      congr 1
      ring

    simp_rw [combine]

    -- Complete the square in the exponent
    have complete_square : ∀ t : ℝ, -↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t =
                                    -↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2 := by
      intro t
      simpa using gaussian_exponent_complete_square hδ ξ t

    simp_rw [complete_square]

    -- Split the exponential again
    have split : ∀ t : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2) =
        Complex.exp (-↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2) * Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) := by
      intro t
      rw [← Complex.exp_add]
      congr 1
      ring

    simp_rw [split]

    -- Factor out the constant
    rw [integral_mul_const]

    -- Apply the shifted Gaussian integral formula
    rw [shifted_gaussian_integral hδ ξ]

  rw [gaussian_fourier]
  -- Simplify: exp(π * δ^2 * ξ^2) * (δ * exp(-π * δ^2 * ξ^2)) = δ
  rw [show Complex.exp (↑π * ↑δ^2 * ↑ξ^2) * (↑δ * Complex.exp (-↑π * ↑δ^2 * ↑ξ^2)) =
           ↑δ * (Complex.exp (↑π * ↑δ^2 * ↑ξ^2) * Complex.exp (-↑π * ↑δ^2 * ↑ξ^2)) by ring]
  have cancel : Complex.exp (↑π * ↑δ^2 * ↑ξ^2) * Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [cancel, mul_one]

/--
The Fourier transform of a Gaussian with real exponential form.
This variant uses Real.exp with coercion to complex numbers.
-/
lemma gaussian_fourier_real_exp {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ t : ℝ, Complex.exp (↑(-2 * π * ξ * t) * I) * ↑(Real.exp (-Real.pi * t^2 / δ^2)) =
    δ * Complex.exp (-π * δ^2 * ξ^2) := by
  -- Convert Real.exp to Complex.exp
  have h1 : ∫ t : ℝ, Complex.exp (↑(-2 * π * ξ * t) * I) * ↑(Real.exp (-Real.pi * t^2 / δ^2)) =
      ∫ t : ℝ, Complex.exp (↑(-2 * π * ξ * t) * I) * Complex.exp (↑(-Real.pi * t^2 / δ^2)) := by
    congr 1
    ext t
    simp only [Complex.ofReal_exp]
  rw [h1]

  -- Rewrite the exponents as complex multiples
  have h2 : ∫ t : ℝ, Complex.exp (↑(-2 * π * ξ * t) * I) * Complex.exp (↑(-Real.pi * t^2 / δ^2)) =
            ∫ t : ℝ, Complex.exp (-2 * ↑π * I * ↑ξ * ↑t) *
              Complex.exp (-(↑π * ↑t ^ 2 / ↑δ ^ 2)) := by
    congr 1
    ext t
    have ht : -(↑π * ↑t ^ 2) / ↑δ ^ 2 = -(↑π * ↑t ^ 2 / ↑δ ^ 2) := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simp [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_pow,
      mul_comm, mul_left_comm, mul_assoc, ht]
  rw [h2]
  -- Combine the exponentials into a single exponential
  have h3_fun :
      (fun t : ℝ =>
        Complex.exp (-2 * ↑π * I * ↑ξ * ↑t) * Complex.exp (-(↑π * ↑t ^ 2 / ↑δ ^ 2))) =
      fun t : ℝ => Complex.exp (-2 * ↑π * I * ↑ξ * ↑t - ↑π * ↑t ^ 2 / ↑δ ^ 2) := by
    ext t
    simp [Complex.exp_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have h3 : ∫ t : ℝ, Complex.exp (-2 * ↑π * I * ↑ξ * ↑t) * Complex.exp (-(↑π * ↑t ^ 2 / ↑δ ^ 2)) =
            ∫ t : ℝ, Complex.exp (-2 * ↑π * I * ↑ξ * ↑t - ↑π * ↑t ^ 2 / ↑δ ^ 2) := by
    simp [h3_fun, Complex.exp_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  rw [h3]

  -- Complete the square inside the exponent
  have h4 :
      ∫ t : ℝ, Complex.exp (-2 * ↑π * I * ↑ξ * ↑t - ↑π * ↑t ^ 2 / ↑δ ^ 2) =
        ∫ t : ℝ,
          Complex.exp (-↑π / ↑δ ^ 2 * (↑t + I * ↑δ ^ 2 * ↑ξ) ^ 2 - ↑π * ↑δ ^ 2 * ↑ξ ^ 2) := by
    congr 1
    ext t
    have exponent_eq :
        -2 * ↑π * I * ↑ξ * ↑t - ↑π * ↑t ^ 2 / ↑δ ^ 2 =
          -↑π / ↑δ ^ 2 * ↑t ^ 2 - 2 * ↑π * I * ↑ξ * ↑t := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc]
    have square := gaussian_exponent_complete_square hδ ξ t
    have h_start :
        Complex.exp (-2 * ↑π * I * ↑ξ * ↑t - ↑π * ↑t ^ 2 / ↑δ ^ 2) =
          Complex.exp (-(2 * ↑π * I * ↑ξ * ↑t) + -(↑π * ↑t ^ 2 / ↑δ ^ 2)) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have eq_add :
        -(2 * ↑π * I * ↑ξ * ↑t) + -(↑π * ↑t ^ 2 / ↑δ ^ 2) =
          -(2 * ↑π * I * ↑ξ * ↑t) + -↑π / ↑δ ^ 2 * ↑t ^ 2 := by
      have :
          -(2 * ↑π * I * ↑ξ * ↑t) + -(↑π * ↑t ^ 2 / ↑δ ^ 2) =
            -↑π / ↑δ ^ 2 * ↑t ^ 2 + -(2 * ↑π * I * ↑ξ * ↑t) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using exponent_eq
      simpa [add_comm, add_left_comm, add_assoc] using this
    have h_eq1 :
        Complex.exp (-(2 * ↑π * I * ↑ξ * ↑t) + -(↑π * ↑t ^ 2 / ↑δ ^ 2)) =
          Complex.exp (-(2 * ↑π * I * ↑ξ * ↑t) + -↑π / ↑δ ^ 2 * ↑t ^ 2) := by
      simpa using congrArg Complex.exp eq_add
    have eq_square :
        -(2 * ↑π * I * ↑ξ * ↑t) + -↑π / ↑δ ^ 2 * ↑t ^ 2 =
          -↑π / ↑δ ^ 2 * (↑t + I * ↑δ ^ 2 * ↑ξ) ^ 2 + -(↑π * ↑δ ^ 2 * ↑ξ ^ 2) := by
      have :
          -↑π / ↑δ ^ 2 * ↑t ^ 2 + -(2 * ↑π * I * ↑ξ * ↑t) =
            -↑π / ↑δ ^ 2 * (↑t + I * ↑δ ^ 2 * ↑ξ) ^ 2 - ↑π * ↑δ ^ 2 * ↑ξ ^ 2 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using square
      simpa [add_comm, add_left_comm, add_assoc] using this
    have h_eq2 :
        Complex.exp (-(2 * ↑π * I * ↑ξ * ↑t) + -↑π / ↑δ ^ 2 * ↑t ^ 2) =
          Complex.exp (-↑π / ↑δ ^ 2 * (↑t + I * ↑δ ^ 2 * ↑ξ) ^ 2 - ↑π * ↑δ ^ 2 * ↑ξ ^ 2) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using congrArg Complex.exp eq_square
    exact h_start.trans (h_eq1.trans h_eq2)
  rw [h4]

  -- Split the exponential into a product
  have h5 :
      ∫ t : ℝ, Complex.exp (-↑π / ↑δ ^ 2 * (↑t + I * ↑δ ^ 2 * ↑ξ) ^ 2 - ↑π * ↑δ ^ 2 * ↑ξ ^ 2) =
        ∫ t : ℝ,
          Complex.exp (-↑π / ↑δ ^ 2 * (↑t + I * ↑δ ^ 2 * ↑ξ) ^ 2) *
            Complex.exp (-↑π * ↑δ ^ 2 * ↑ξ ^ 2) := by
    congr 1
    ext t
    simp [Complex.exp_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  rw [h5]

  -- Factor out the constant term from the integral
  have h6 : ∫ t : ℝ, Complex.exp (-↑π / ↑δ ^ 2 * (↑t + I * ↑δ ^ 2 * ↑ξ) ^ 2) *
            Complex.exp (-↑π * ↑δ ^ 2 * ↑ξ ^ 2) =
      Complex.exp (-↑π * ↑δ ^ 2 * ↑ξ ^ 2) *
        ∫ t : ℝ, Complex.exp (-↑π / ↑δ ^ 2 * (↑t + I * ↑δ ^ 2 * ↑ξ) ^ 2) := by
    simp [mul_comm, mul_left_comm, mul_assoc, integral_mul_const]
  rw [h6]

  -- Evaluate the Gaussian integral with imaginary shift
  have h7 := shifted_gaussian_integral hδ ξ
  rw [h7]

  -- Simplify the remaining expression
  have hξ : Complex.exp (-↑π * ↑δ ^ 2 * ↑ξ ^ 2) = Complex.exp (-π * δ^2 * ξ^2) := by
    simp [Complex.ofReal_mul, Complex.ofReal_pow]
  simp [hξ, mul_comm]

/--
Explicit formula for the Fourier transform of a normalized Gaussian.
The Fourier transform of a Gaussian is another Gaussian with reciprocal width.
-/
lemma gaussian_fourier_transform {δ : ℝ} (hδ : 0 < δ) :
    fourierIntegral (((normalizedGaussianLp δ hδ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) =
    fun (ξ : ℝ) => ((2 : ℂ)^((1 : ℂ)/4) * sqrt δ) * Complex.exp (-π * δ^2 * ξ^2) := by
  classical
  -- Unfold the definition of normalizedGaussianLp
  unfold normalizedGaussianLp
  -- Get the normalized Gaussian from build_normalized_gaussian
  set g := Classical.choose (build_normalized_gaussian δ hδ)
  -- Apply properties of the chosen normalized Gaussian
  have hg_prop := Classical.choose_spec (build_normalized_gaussian δ hδ)
  -- Extract the norm and almost everywhere properties
  obtain ⟨hg_norm, hg_ae⟩ := hg_prop
  -- We need to show the Fourier transform equals the target function
  ext ξ
  -- The coercion of g is the normalized Gaussian function
  have hg_eq : (g : ℝ → ℂ) = (normalizedGaussianLp δ hδ : ℝ → ℂ) := rfl
  -- Use the almost everywhere equality for the Gaussian
  have hg_form : ∀ᵐ t, (g : ℝ → ℂ) t =
      ((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ : ℝ) * (Real.exp (-Real.pi * t^2 / δ^2) : ℂ) := hg_ae
  -- Compute the Fourier transform at point ξ
  simp only [fourierIntegral]
  -- Unfold the Fourier integral definition for our specific function
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (↑↑(normalizedGaussianLp δ hδ)) ξ =
    2 ^ (1 / 4) * ↑√δ * cexp (-↑π * ↑δ ^ 2 * ↑ξ ^ 2)
  -- Use the definition of normalizedGaussianLp
  have : (normalizedGaussianLp δ hδ : ℝ → ℂ) = (g : ℝ → ℂ) := by
    simp only [normalizedGaussianLp]
    rfl
  rw [this]
  -- Use the almost everywhere equality to substitute the explicit form
  have integral_eq : VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (↑↑g) ξ =
      ∫ t, Complex.exp (↑(-2 * π * ξ * t) * I) *
        (((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ : ℝ) * (Real.exp (-Real.pi * t^2 / δ^2) : ℂ)) := by
    -- Apply the almost everywhere equality in the integral
    -- The Fourier integral is defined as this integral
    simp only [VectorFourier.fourierIntegral]
    -- Use the fact that g equals the Gaussian almost everywhere
    apply integral_congr_ae
    filter_upwards [hg_form] with t ht
    rw [ht]
    -- Need to show: 𝐞(-inner ℝ ξ t) • (gaussian) = exp(-2πiξt) * gaussian
    simp only [innerₗ_apply, real_inner_comm]
    -- After simplification, inner t ξ = t * ξ in ℝ
    simp only [RCLike.inner_apply, conj_trivial]
    -- 𝐞 x is e^(2πix) and we have 𝐞(-ξ*t) • f = e^(-2πiξt) * f
    -- Circle scalar multiplication is just multiplication after coercion: c • x = (↑c : ℂ) * x
    rw [show ∀ (c : Circle) (x : ℂ), c • x = (↑c : ℂ) * x from fun _ _ => rfl]
    congr 1
    -- Show that 𝐞(-ξ * t) = exp(-2πi * ξ * t)
    simp only [Real.fourierChar_apply]
    congr 1
    ring_nf
  rw [integral_eq]
  -- Factor out the constant from the integral
  have factor_const : ∫ t, Complex.exp (↑(-2 * π * ξ * t) * I) *
      (((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ : ℝ) * (Real.exp (-Real.pi * t^2 / δ^2) : ℂ)) =
      ((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ : ℝ) *
      ∫ t, Complex.exp (↑(-2 * π * ξ * t) * I) * (Real.exp (-Real.pi * t^2 / δ^2) : ℂ) := by
    simp only [mul_assoc, mul_comm (Complex.exp _), mul_assoc]
    rw [← integral_const_mul]
  rw [factor_const]
  -- Apply the Fourier transform formula for Gaussian
  have gaussian_ft := gaussian_fourier_real_exp hδ ξ
  rw [gaussian_ft]
  -- Simplify the expression: (2^(1/4) / √δ) * δ * exp(-π δ² ξ²) = 2^(1/4) * √δ * exp(-π δ² ξ²)
  simp only [mul_assoc]
  -- We need to show: (2^(1/4) / √δ) * (δ * exp) = 2^(1/4) * √δ * exp
  -- This follows from the algebraic identity: (A / √δ) * δ = A * √δ
  -- The key algebraic simplification: (2^(1/4) / √δ) * δ = 2^(1/4) * √δ
  -- First prove that (2^(1/4) / √δ) * δ = 2^(1/4) * √δ as complex numbers
  have h_alg : (↑((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ) : ℂ) * (↑δ : ℂ) =
               ((2 : ℂ)^(1/4 : ℂ)) * (↑(Real.sqrt δ) : ℂ) := by
    rw [Complex.ofReal_div]
    rw [div_sqrt_mul_delta hδ]
    rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) < 2).le]
    -- Goal: 2 ^ ↑(1 / 4) * ↑√δ = 2 ^ (1 / 4) * ↑√δ
    congr 1
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  -- Now apply this to the full expression with the exponential
  rw [← mul_assoc, h_alg, mul_assoc]

end

end Frourio
