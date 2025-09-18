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
  -- We need to show: (A / √δ) * δ = A * √δ
  -- Multiply both sides by √δ to get: A * δ = A * √δ * √δ = A * δ
  have hsqrt_ne : (↑(Real.sqrt δ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr hδ).ne'
  field_simp [hsqrt_ne]
  -- Now we need to show: A * δ = A * (√δ * √δ)
  congr 1
  -- Show: δ = (√δ)^2
  rw [pow_two]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← sq, Real.sq_sqrt hδ.le]

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
Complex contour shift for Gaussian integrals.
For a Gaussian function, shifting the integration contour by a purely imaginary constant
doesn't change the integral value. This is a consequence of Cauchy's theorem for entire functions
with sufficient decay.
-/
lemma complex_gaussian_contour_shift {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
  -- The proof requires showing that shifting the contour of integration
  -- by a purely imaginary constant doesn't change the value of the integral

  -- Step 1: Expand (a + I·δ²·ξ)²
  have expand : ∀ a : ℝ, (↑a + I * ↑δ^2 * ↑ξ)^2 =
                         ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2 := by
    intro a
    calc (↑a + I * ↑δ^2 * ↑ξ)^2
        = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ + (I * ↑δ^2 * ↑ξ)^2 := by ring
        _ = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ + I^2 * ↑δ^4 * ↑ξ^2 := by ring
        _ = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2 := by
          simp only [Complex.I_sq]
          ring

  -- Step 2: Rewrite the integral using the expansion
  conv_lhs =>
    arg 2
    intro a
    rw [expand a]

  -- Step 3: Simplify the exponent
  have simplify_exp : ∀ a : ℝ,
      -↑π / ↑δ^2 * (↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2) =
      -↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a + ↑π * ↑δ^2 * ↑ξ^2 := by
    intro a
    have ne_zero : (↑δ : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hδ
    field_simp [ne_zero]
    ring

  simp_rw [simplify_exp]

  -- Step 4: Split the exponential
  have split : ∀ a : ℝ,
      Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a + ↑π * ↑δ^2 * ↑ξ^2) =
      Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
      Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) *
      Complex.exp (↑π * ↑δ^2 * ↑ξ^2) := by
    intro a
    rw [← Complex.exp_add, ← Complex.exp_add]
    ring_nf

  simp_rw [split]

  -- Step 5: Factor out the constant exp(π * δ² * ξ²)
  have factor : (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                          Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) *
                          Complex.exp (↑π * ↑δ^2 * ↑ξ^2)) =
                Complex.exp (↑π * ↑δ^2 * ↑ξ^2) *
                (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                         Complex.exp (-2 * ↑π * I * ↑ξ * ↑a)) := by
    have : ∀ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                     Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) *
                     Complex.exp (↑π * ↑δ^2 * ↑ξ^2) =
                     Complex.exp (↑π * ↑δ^2 * ↑ξ^2) *
                     (Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                      Complex.exp (-2 * ↑π * I * ↑ξ * ↑a)) := by
      intro a
      ring
    simp_rw [this]
    rw [← integral_const_mul]

  rw [factor]

  -- Step 6: The key step - showing the oscillating integral equals the Gaussian integral
  -- The integral ∫ exp(-π/δ²a²) * exp(-2πIξa) da should equal exp(-πδ²ξ²) * ∫ exp(-π/δ²s²) ds
  -- This would complete the proof by showing:
  -- exp(πδ²ξ²) * [exp(-πδ²ξ²) * ∫ exp(-π/δ²s²) ds] = ∫ exp(-π/δ²s²) ds

  -- We need to show that:
  -- exp(πδ²ξ²) * ∫ exp(-π/δ²a²) * exp(-2πIξa) da = ∫ exp(-π/δ²s²) ds

  -- Step 6a: Combine the exponentials in the integral
  have combine_exp : (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                               Complex.exp (-2 * ↑π * I * ↑ξ * ↑a)) =
                     (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a)) := by
    congr 1
    ext a
    rw [← Complex.exp_add]
    congr 1
    ring

  rw [combine_exp]

  -- Step 6b: Complete the square in reverse
  -- We need to show: -π/δ²a² - 2πIξa = -π/δ²(a + Iδ²ξ)² - πδ²ξ²
  have reverse_complete_sq : ∀ a : ℝ,
      -↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a =
      -↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2 := by
    intro a
    -- Add and subtract πδ²ξ²
    -- We already proved this is the complete square formula
    -- Use the same expansion as before
    conv_rhs => rw [expand a]
    have ne_zero : (↑δ : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hδ
    field_simp [ne_zero]
    ring

  simp_rw [reverse_complete_sq]

  -- Step 6c: Split the exponential again
  have split_again : ∀ a : ℝ,
      Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2) =
      Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) *
      Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) := by
    intro a
    rw [← Complex.exp_add]
    ring_nf

  simp_rw [split_again]

  -- Step 6d: Factor out exp(-πδ²ξ²)
  rw [← integral_const_mul]

  -- Step 6e: Now we have:
  -- exp(πδ²ξ²) * [exp(-πδ²ξ²) * ∫ exp(-π/δ²(a + Iδ²ξ)²) da] = ∫ exp(-π/δ²s²) ds

  -- Rearrange the integral
  have rearrange : (∫ a : ℝ, Complex.exp (↑π * ↑δ^2 * ↑ξ^2) *
                             (Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) *
                              Complex.exp (-↑π * ↑δ^2 * ↑ξ^2))) =
                   (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2)) := by
    congr 1
    ext a
    -- Goal: exp(π·δ²·ξ²) * (exp(...) * exp(-π·δ²·ξ²)) = exp(...)
    -- This simplifies since exp(π·δ²·ξ²) * exp(-π·δ²·ξ²) = 1
    rw [mul_assoc]
    rw [mul_comm (Complex.exp _) (Complex.exp (-↑π * ↑δ^2 * ↑ξ^2))]
    rw [← mul_assoc]
    rw [← Complex.exp_add]
    ring_nf
    simp

  rw [rearrange]

  -- Step 6f: The final step requires showing:
  -- ∫ exp(-π/δ²(a + Iδ²ξ)²) da = ∫ exp(-π/δ²s²) ds
  -- This is the contour shift property for Gaussian integrals

  -- We need to show that shifting the integration variable by a purely imaginary constant
  -- doesn't change the value of the Gaussian integral

  -- Method 1: Direct substitution (would require complex change of variables)
  -- Let t = a + Iδ²ξ, but since a is real and Iδ²ξ is purely imaginary,
  -- this is a horizontal shift in the complex plane

  -- Method 2: Use analyticity of the Gaussian
  -- The function f(z) = exp(-π/δ²·z²) is entire (analytic everywhere)
  -- and decays rapidly as |z| → ∞

  -- Method 3: Parametrize the contours
  -- Contour 1: γ₁(a) = a for a ∈ ℝ
  -- Contour 2: γ₂(a) = a + Iδ²ξ for a ∈ ℝ

  -- By Cauchy's theorem, for an entire function with sufficient decay,
  -- the integral over any horizontal line is the same

  -- Since we're integrating exp(-π/δ²(a + Iδ²ξ)²) over real a,
  -- this is equivalent to integrating exp(-π/δ²t²) over the line t = a + Iδ²ξ

  -- The key insight is that we can deform the contour from ℝ to ℝ + Iδ²ξ
  -- without crossing any singularities (since exp is entire)

  -- Formal proof would require:
  have contour_independence :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by

    -- Step 1: Expand the squared term (a + Iδ²ξ)²
    have expand_integral :
      ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
      ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2)) := by
      congr 1
      ext a
      congr 2
      rw [expand a]

    rw [expand_integral]

    -- Step 2: Distribute -π/δ² into the sum
    have distribute :
      ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2)) =
      ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a + ↑π * ↑δ^2 * ↑ξ^2) := by
      congr 1
      ext a
      congr 1
      have ne_zero : (↑δ : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact ne_of_gt hδ
      field_simp [ne_zero]
      ring

    rw [distribute]

    -- Step 3: Split the exponential
    have split_exp_integral :
      ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a + ↑π * ↑δ^2 * ↑ξ^2) =
      ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
               Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) *
               Complex.exp (↑π * ↑δ^2 * ↑ξ^2) := by
      congr 1
      ext a
      rw [← Complex.exp_add, ← Complex.exp_add]
      ring_nf

    rw [split_exp_integral]

    -- Step 4: Factor out the constant exp(πδ²ξ²)
    have factor_const :
      ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
               Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) *
               Complex.exp (↑π * ↑δ^2 * ↑ξ^2) =
      Complex.exp (↑π * ↑δ^2 * ↑ξ^2) *
      ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
               Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) := by
      -- Move the constant outside
      have : ∀ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                       Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) *
                       Complex.exp (↑π * ↑δ^2 * ↑ξ^2) =
                       Complex.exp (↑π * ↑δ^2 * ↑ξ^2) *
                       (Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                        Complex.exp (-2 * ↑π * I * ↑ξ * ↑a)) := by
        intro a
        ring
      simp_rw [this]
      rw [← integral_const_mul]

    rw [factor_const]

    -- Step 5: The key step - Fourier transform of Gaussian
    -- We need: ∫ exp(-π/δ²·a²) * exp(-2πIξa) da = exp(-πδ²ξ²) * ∫ exp(-π/δ²·s²) ds

    -- This is equivalent to showing that the Fourier transform of
    -- f(a) = exp(-π/δ²·a²) evaluated at frequency ξ is exp(-πδ²ξ²) * δ

    have fourier_gaussian :
      ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) * Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) =
      Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) * ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
      -- This is the Fourier transform of a Gaussian
      -- The Fourier transform of exp(-πa²/δ²) at frequency ξ is δ·exp(-πδ²ξ²)

      -- Step 1: Combine the exponentials in the integrand
      have combine_integrands :
        (fun a : ℝ => Complex.exp (-↑π / ↑δ^2 * ↑a^2) * Complex.exp (-2 * ↑π * I * ↑ξ * ↑a)) =
        (fun a : ℝ => Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a)) := by
        ext a
        rw [← Complex.exp_add]
        congr 1
        ring

      simp_rw [combine_integrands]

      -- Step 2: Complete the square in the exponent
      -- We want to write -π/δ²·a² - 2πIξa in the form -π/δ²·(a + c)² + d
      have complete_sq_exponent : ∀ a : ℝ,
        -↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a =
        -↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2 := by
        intro a
        -- This is the same completion of square we did before
        have expand_sq : (↑a + I * ↑δ^2 * ↑ξ)^2 =
                        ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2 := by
          calc (↑a + I * ↑δ^2 * ↑ξ)^2
              = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ + (I * ↑δ^2 * ↑ξ)^2 := by ring
              _ = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ + I^2 * ↑δ^4 * ↑ξ^2 := by ring
              _ = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2 := by
                simp only [Complex.I_sq]
                ring

        conv_rhs => rw [expand_sq]
        have ne_zero : (↑δ : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact ne_of_gt hδ
        field_simp [ne_zero]
        ring

      simp_rw [complete_sq_exponent]

      -- Step 3: Split the exponential
      have split_completed :
        (fun a : ℝ => Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2)) =
        (fun a : ℝ => Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) *
                      Complex.exp (-↑π * ↑δ^2 * ↑ξ^2)) := by
        ext a
        rw [← Complex.exp_add]
        ring_nf

      simp_rw [split_completed]

      -- Step 4: Factor out the constant
      rw [← integral_const_mul]
      rw [mul_comm]

      -- Step 5: Apply the contour shift
      -- We need: ∫ exp(-π/δ²·(a + Iδ²ξ)²) da = ∫ exp(-π/δ²·s²) ds
      -- This is because shifting by a purely imaginary constant doesn't change the integral

      -- The goal is now to show:
      -- exp(-πδ²ξ²) * ∫ exp(-π/δ²·(a + Iδ²ξ)²) da = exp(-πδ²ξ²) * ∫ exp(-π/δ²·s²) ds

      -- We'll apply the contour shift property
      have shift_contour :
        ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
        ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
        -- This is the contour shift property we established earlier
        -- The integral of a Gaussian over a horizontal line in the complex plane
        -- is the same as the integral over the real axis
        exact gaussian_contour_shift_real hδ ξ

      -- First normalize the expression order
      have normalize_order :
        (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + ↑ξ * (I * ↑δ^2))^2) *
          Complex.exp (-↑π * ↑δ^2 * ↑ξ^2)) =
        (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) *
          Complex.exp (-↑π * ↑δ^2 * ↑ξ^2)) := by
        congr 1
        ext a
        congr 2
        congr 1
        congr 1
        ring

      rw [normalize_order]

      -- Factor out the constant exp(-πδ²ξ²) from the integral
      have factor_exp :
        (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) *
          Complex.exp (-↑π * ↑δ^2 * ↑ξ^2)) =
        Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) * (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 *
          (↑a + I * ↑δ^2 * ↑ξ)^2)) := by
        rw [← integral_const_mul]
        congr 1
        ext a
        ring

      rw [factor_exp, shift_contour]

      -- Now we need to show the RHS equals what we have
      rw [integral_const_mul]

    rw [fourier_gaussian]

    -- Step 6: Cancel exp(πδ²ξ²) * exp(-πδ²ξ²) = 1
    rw [← mul_assoc]
    rw [show Complex.exp (↑π * ↑δ^2 * ↑ξ^2) * Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) = 1 by
      rw [← Complex.exp_add]
      simp]
    rw [one_mul]

  exact contour_independence

/--
Contour shift lemma for Gaussian integrals.
The integral of exp(-π/δ²(t + Iδ²ξ)²) over ℝ equals the integral of exp(-π/δ²s²).
This is a key result from complex analysis (Cauchy's theorem).
-/
lemma gaussian_contour_shift {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
  -- Step 1: Expand the square (a + I * δ² * ξ)²
  have expand : ∀ a : ℝ, (↑a + I * ↑δ^2 * ↑ξ)^2 =
                         ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2 := by
    intro a
    calc (↑a + I * ↑δ^2 * ↑ξ)^2
        = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ + (I * ↑δ^2 * ↑ξ)^2 := by ring
        _ = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ + I^2 * ↑δ^4 * ↑ξ^2 := by ring
        _ = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2 := by
          simp only [Complex.I_sq]
          ring

  -- Step 2: Apply the expansion to the integral
  conv_lhs =>
    arg 2
    intro a
    rw [expand a]

  -- Step 3: Simplify the exponent
  have simplify : ∀ a : ℝ, -↑π / ↑δ^2 * (↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2) =
                           -↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a + ↑π * ↑δ^2 * ↑ξ^2 := by
    intro a
    have ne_zero : (↑δ : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hδ
    field_simp [ne_zero]
    ring

  simp_rw [simplify]

  -- Step 4: Split the exponential exp(a + b + c) = exp(a) * exp(b) * exp(c)
  have split : ∀ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a + ↑π * ↑δ^2 * ↑ξ^2) =
                        Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                        Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) *
                        Complex.exp (↑π * ↑δ^2 * ↑ξ^2) := by
    intro a
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring

  simp_rw [split]

  -- Step 5: Factor out the constant exp(π * δ² * ξ²)
  have factor_const : (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                                Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) *
                                Complex.exp (↑π * ↑δ^2 * ↑ξ^2)) =
                      Complex.exp (↑π * ↑δ^2 * ↑ξ^2) *
                      (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                               Complex.exp (-2 * ↑π * I * ↑ξ * ↑a)) := by
    -- Since exp(π * δ² * ξ²) is constant with respect to a
    have : ∀ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                     Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) *
                     Complex.exp (↑π * ↑δ^2 * ↑ξ^2) =
                     Complex.exp (↑π * ↑δ^2 * ↑ξ^2) *
                     (Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                      Complex.exp (-2 * ↑π * I * ↑ξ * ↑a)) := by
      intro a
      ring
    simp_rw [this]
    rw [← integral_const_mul]

  rw [factor_const]

  -- Step 6: The key step - the oscillating integral
  -- ∫ exp(-π/δ² * a²) * exp(-2πIξa) da = exp(-π * δ² * ξ²) * ∫ exp(-π/δ² * s²) ds
  -- This requires showing that the Fourier transform of a Gaussian is a Gaussian
  have key_identity : (∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                                 Complex.exp (-2 * ↑π * I * ↑ξ * ↑a)) =
                       Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) *
                       (∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2)) := by
    -- This is the Fourier transform of a Gaussian
    -- We need to complete the square in the exponent

    -- Step 1: Combine the exponentials
    have combine : ∀ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) *
                            Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) =
                            Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a) := by
      intro a
      rw [← Complex.exp_add]
      congr 1
      ring

    simp_rw [combine]

    -- Step 2: Complete the square
    -- -π/δ² * a² - 2πIξa = -π/δ² * (a + Iδ²ξ)² - πδ²ξ²
    have complete_sq : ∀ a : ℝ, -↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a =
                                -↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2 := by
      intro a
      -- Expand (a + Iδ²ξ)²
      have expand_sq : (↑a + I * ↑δ^2 * ↑ξ)^2 =
                       ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2 := by
        calc (↑a + I * ↑δ^2 * ↑ξ)^2
            = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ + (I * ↑δ^2 * ↑ξ)^2 := by ring
            _ = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ + I^2 * ↑δ^4 * ↑ξ^2 := by ring
            _ = ↑a^2 + 2 * ↑a * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2 := by
              simp only [Complex.I_sq]
              ring

      have ne_zero : (↑δ : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact ne_of_gt hδ

      -- We'll show this by direct expansion
      -- (a + I·δ²·ξ)² = a² + 2·a·I·δ²·ξ - δ⁴·ξ²
      -- So -π/δ² · (a + I·δ²·ξ)² = -π/δ² · a² - 2π·I·ξ·a + π·δ²·ξ²

      -- We need to show: LHS = RHS
      -- Start by expanding the RHS
      conv_rhs => rw [expand_sq]
      -- Now simplify
      field_simp [ne_zero]
      ring

    simp_rw [complete_sq]

    -- Step 3: Split the exponential
    have split_exp : ∀ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2) =
                              Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) *
                              Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) := by
      intro a
      rw [← Complex.exp_add]
      ring_nf

    simp_rw [split_exp]

    -- Step 4: Factor out the constant
    rw [integral_mul_const]
    rw [mul_comm]
    congr 1
    exact gaussian_contour_shift_real hδ ξ

  rw [key_identity]

  -- Step 7: Simplify exp(π * δ² * ξ²) * exp(-π * δ² * ξ²) = 1
  simp only [← mul_assoc]
  rw [show Complex.exp (↑π * ↑δ^2 * ↑ξ^2) * Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) = 1 by
    rw [← Complex.exp_add]
    simp]
  simp

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
  -- The key insight: shifting a Gaussian by a pure imaginary amount doesn't change its integral
  -- This is because exp(-a(t + ib)²) = exp(-at²) * exp(-2iabt) * exp(ab²)
  -- and the oscillating term exp(-2iabt) doesn't affect the integral over ℝ

  -- Step 1: Make a change of variables s = t + I*δ²*ξ
  -- This shifts the contour of integration in the complex plane
  have contour_shift : ∫ t : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2) =
                       ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
    -- For a real Gaussian with imaginary shift, we can expand the square and separate terms
    -- (t + iα)² = t² + 2iαt - α², so exp(-c(t + iα)²) = exp(-ct²) * exp(-2icαt) * exp(cα²)
    -- The integral of exp(-ct²) * exp(-2icαt) over ℝ equals exp(cα²) * ∫exp(-cs²)ds
    -- by completing the square in reverse

    -- First, let's work with the expanded form
    have expand : ∀ t : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2) =
                          Complex.exp (-↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t) *
                          Complex.exp (↑π * ↑δ^2 * ↑ξ^2) := by
      intro t
      -- We'll show: -π/δ² * (t + I*δ²*ξ)² = -π/δ² * t² - 2π*I*ξ*t + π*δ²*ξ²

      -- First, expand the square
      have sq_exp : (↑t + I * ↑δ^2 * ↑ξ)^2 = ↑t^2 + 2 * ↑t * I * ↑δ^2 * ↑ξ + (I * ↑δ^2 * ↑ξ)^2 := by
        ring

      -- Simplify I² = -1
      have I_sq : (I * ↑δ^2 * ↑ξ)^2 = -↑δ^4 * ↑ξ^2 := by
        calc (I * ↑δ^2 * ↑ξ)^2
            = I^2 * (↑δ^2)^2 * ↑ξ^2 := by ring
            _ = (-1 : ℂ) * ↑δ^4 * ↑ξ^2 := by
              simp only [Complex.I_sq]
              ring
            _ = -↑δ^4 * ↑ξ^2 := by ring

      -- Now compute the full expression
      calc Complex.exp (-↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2)
          = Complex.exp (-↑π / ↑δ^2 * (↑t^2 + 2 * ↑t * I * ↑δ^2 * ↑ξ + (I * ↑δ^2 * ↑ξ)^2)) := by
            rw [sq_exp]
          _ = Complex.exp (-↑π / ↑δ^2 * (↑t^2 + 2 * ↑t * I * ↑δ^2 * ↑ξ - ↑δ^4 * ↑ξ^2)) := by
            congr 1
            congr 1
            rw [I_sq]
            ring
          _ = Complex.exp (-↑π / ↑δ^2 * ↑t^2 - ↑π / ↑δ^2 *
              (2 * ↑t * I * ↑δ^2 * ↑ξ) + ↑π / ↑δ^2 * ↑δ^4 * ↑ξ^2) := by
            congr 1
            ring
          _ = Complex.exp (-↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t + ↑π * ↑δ^2 * ↑ξ^2) := by
            congr 1
            -- Simplify the exponent: -π/δ² * (2 * t * I * δ² * ξ) = -2 * π * I * ξ * t
            -- and π/δ² * δ⁴ * ξ² = π * δ² * ξ²
            have ne_zero : (↑δ : ℂ) ≠ 0 := by
              simp only [ne_eq, Complex.ofReal_eq_zero]
              exact ne_of_gt hδ
            simp only [div_eq_inv_mul]
            field_simp [ne_zero]
          _ = Complex.exp (-↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t) *
              Complex.exp (↑π * ↑δ^2 * ↑ξ^2) := by
            rw [← Complex.exp_add]

    simp_rw [expand]

    -- Now we have: ∫ exp(-π/δ²·t²) * exp(-2πiξt) * exp(πδ²ξ²) dt
    rw [integral_mul_const]

    -- We need to show: exp(πδ²ξ²) * ∫ exp(-π/δ²·t²) * exp(-2πiξt) dt = ∫ exp(-π/δ²·s²) ds
    -- The integral ∫ exp(-π/δ²·t²) * exp(-2πiξt) dt = δ * exp(-πδ²ξ²)
    -- Therefore: exp(πδ²ξ²) * δ * exp(-πδ²ξ²) = δ
    -- And ∫ exp(-π/δ²·s²) ds = δ

    -- Use the fact that exp(x) * exp(-x) = 1
    have cancel : Complex.exp (↑π * ↑δ^2 * ↑ξ^2) * Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) = 1 := by
      rw [← Complex.exp_add]
      simp

    -- We need to show: exp(πδ²ξ²) * ∫ exp(-π/δ²·t²) * exp(-2πiξt) dt = ∫ exp(-π/δ²·s²) ds

    -- Use the fact that we already expanded the expression
    calc (∫ (a : ℝ), Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a)) *
                    Complex.exp (↑π * ↑δ^2 * ↑ξ^2)
        = ∫ (a : ℝ), Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π * I * ↑ξ * ↑a) *
                     Complex.exp (↑π * ↑δ^2 * ↑ξ^2) := by
          rw [← integral_mul_const]
        _ = ∫ (a : ℝ), Complex.exp (-↑π / ↑δ^2 * ↑a^2 - 2 * ↑π *
            I * ↑ξ * ↑a + ↑π * ↑δ^2 * ↑ξ^2) := by
          congr 1
          funext a
          rw [← Complex.exp_add]
        _ = ∫ (a : ℝ), Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) := by
          congr 1
          funext a
          -- Show that the exponents are equal
          congr 1
          -- Use field_simp to handle the division
          have ne_zero : (↑δ : ℂ) ≠ 0 := by
            simp only [ne_eq, Complex.ofReal_eq_zero]
            exact ne_of_gt hδ
          field_simp [ne_zero]
          -- Expand and simplify
          ring_nf
          -- Simplify I² = -1
          simp only [I_sq]
          ring
        _ = ∫ (s : ℝ), Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
          -- Apply the contour shift lemma
          exact gaussian_contour_shift hδ ξ

  -- Step 2: Apply the standard Gaussian integral formula
  rw [contour_shift]

  exact gaussian_integral_complex hδ

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
      -- Expand (t + I * δ^2 * ξ)^2
      calc -↑π / ↑δ^2 * ↑t^2 - 2 * ↑π * I * ↑ξ * ↑t
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
  -- Combine the exponentials
  have h2 : ∫ t : ℝ, Complex.exp (↑(-2 * π * ξ * t) * I) * Complex.exp (↑(-Real.pi * t^2 / δ^2)) =
            ∫ t : ℝ, Complex.exp (↑(-2 * π * ξ * t) * I + ↑(-Real.pi * t^2 / δ^2)) := by
    congr 1
    ext t
    rw [Complex.exp_add]
  rw [h2]
  -- Apply the Gaussian Fourier transform formula
  -- Convert to standard Gaussian Fourier transform form
  have h3 : ∫ t : ℝ, Complex.exp (↑(-2 * π * ξ * t) * I + ↑(-Real.pi * t^2 / δ^2)) =
            ∫ t : ℝ, Complex.exp (-2 * π * I * ξ * t - π * t^2 / δ^2) := by
    congr 1
    ext t
    congr 1
    -- Show the equality by simplifying both sides
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_pow]
    ring_nf
    -- Now we need to show -(↑2 * ↑π * ↑ξ * ↑t * I) = -(↑π * ↑ξ * ↑t * I * 2)
    -- This follows from commutativity of multiplication
    congr 2
    -- Goal: ↑2 * ↑π * ↑ξ * ↑t * I = ↑π * ↑ξ * ↑t * I * 2
    -- Rearrange using associativity and commutativity
    simp only [mul_comm, mul_assoc, mul_left_comm]
    -- Now we have: I * (↑ξ * (↑t * (↑π * ↑2))) = I * (↑ξ * (↑t * (↑π * 2)))
    -- We need to show ↑2 = 2 as complex numbers
    norm_num
  rw [h3]
  have h4 : ∫ t : ℝ, Complex.exp (-2 * π * I * ξ * t - π * t^2 / δ^2) =
            ∫ t : ℝ, Complex.exp (-π / δ^2 * (t + I * δ^2 * ξ)^2 - π * δ^2 * ξ^2) := by
    congr 1
    ext t
    congr 1
    -- Show that -2πIξt - πt²/δ² = -π/δ²(t + Iδ²ξ)² - πδ²ξ²
    -- Factor out -π/δ² from the left side
    have left_factor : -2 * ↑π * I * ↑ξ * ↑t - ↑π * ↑t^2 / ↑δ^2 =
                       -↑π / ↑δ^2 * (↑t^2 + 2 * ↑δ^2 * I * ↑ξ * ↑t) := by
      field_simp
      ring_nf
      -- Now we need to show: -(t * (I * (ξ * 2))) = -(t * I * ξ * (δ * δ * (δ⁻¹ * δ⁻¹)) * 2)
      -- This simplifies since δ * δ * (δ⁻¹ * δ⁻¹) = 1
      congr 1
      -- Convert δ^2 * (δ⁻¹)^2 to δ * δ * (δ⁻¹ * δ⁻¹)
      simp only [pow_two]
      -- Now we have: -(t * I * ξ * 2) = -(t * I * ξ * (δ * δ) * ((δ⁻¹) * (δ⁻¹)) * 2)
      -- Rewrite the right side to show (δ * δ) * ((δ⁻¹) * (δ⁻¹)) = 1
      rw [mul_assoc (↑t * I * ↑ξ), mul_assoc, delta_sq_inv_sq hδ, mul_one]
      -- Now we just need to show -(t * I * (ξ * 2)) = -(t * I * ξ * 2)
      ring
    rw [left_factor]
    -- Complete the square: t² + 2δ²Iξt = (t + δ²Iξ)² - (δ²Iξ)²
    have complete : ↑t^2 + 2 * ↑δ^2 * I * ↑ξ * ↑t = (↑t + I * ↑δ^2 * ↑ξ)^2 - (I * ↑δ^2 * ↑ξ)^2 := by
      ring
    rw [complete]
    -- Distribute -π/δ²
    simp only [mul_sub]
    -- Simplify (Iδ²ξ)² = I²δ⁴ξ² = -δ⁴ξ²
    have I_sq : (I * ↑δ^2 * ↑ξ)^2 = -(↑δ^4 * ↑ξ^2) := by
      simp only [sq]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [I_sq]
    -- Simplify the algebra
    field_simp
  rw [h4]
  -- Split the exponential: exp(-π/δ²(t + Iδ²ξ)² - πδ²ξ²) = exp(-π/δ²(t + Iδ²ξ)²) * exp(-πδ²ξ²)
  have h5 : ∫ t : ℝ, Complex.exp (-π / δ^2 * (t + I * δ^2 * ξ)^2 - π * δ^2 * ξ^2) =
      ∫ t : ℝ, Complex.exp (-π / δ^2 * (t + I * δ^2 * ξ)^2) * Complex.exp (-π * δ^2 * ξ^2) := by
    congr 1
    ext t
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [h5]
  -- Factor out the constant
  have h6 : ∫ t : ℝ, Complex.exp (-π / δ^2 * (t + I * δ^2 * ξ)^2) * Complex.exp (-π * δ^2 * ξ^2) =
      Complex.exp (-π * δ^2 * ξ^2) * ∫ t : ℝ, Complex.exp (-π / δ^2 * (t + I * δ^2 * ξ)^2) := by
    simp_rw [mul_comm (Complex.exp _) (Complex.exp (-π * δ^2 * ξ^2))]
    simp_rw [integral_const_mul]
  rw [h6]
  -- Apply Gaussian integral formula
  -- The integral ∫ exp(-π/δ²(t + Iδ²ξ)²) needs a change of variable
  have h7 := complex_shifted_gaussian_integral hδ ξ
  rw [h7]
  -- Simplify: exp(-πδ²ξ²) * δ = δ * exp(-πδ²ξ²) by commutativity
  rw [mul_comm]

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
