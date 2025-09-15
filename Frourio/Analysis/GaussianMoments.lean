import Frourio.Analysis.Gaussian
import Frourio.Analysis.ZakMellin
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

lemma normalizedGaussianLp_norm_one {δ : ℝ} (hδ : 0 < δ) :
    ‖normalizedGaussianLp δ hδ‖ = 1 := by
  unfold normalizedGaussianLp
  have h := Classical.choose_spec (build_normalized_gaussian δ hδ)
  exact h.1

/--
The second moment ∫ t² |w(t)|² dt is finite for normalized Gaussian windows.
This establishes time localization for the suitable_window condition.
-/
lemma gaussian_second_moment_finite {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ t : ℝ, ENNReal.ofReal (t^2 * ‖(((normalizedGaussianLp δ hδ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) t‖^2) ∂volume < ⊤ := by
  -- Use the fact that normalizedGaussianLp is defined as Classical.choose
  unfold normalizedGaussianLp
  -- Now we have the Classical.choose term directly
  -- The normalized Gaussian is w(t) = A * exp(-π t²/δ²) where A = 2^(1/4)/√δ
  -- So |w(t)|² = A² * exp(-2π t²/δ²)
  -- We need to show ∫ t² * A² * exp(-2π t²/δ²) dt < (⊤ : ℝ≥0∞)

  -- Get the specification for the chosen element
  let w := Classical.choose (build_normalized_gaussian δ hδ)
  have h_spec := Classical.choose_spec (build_normalized_gaussian δ hδ)
  -- From h_spec.2, we have a.e. pointwise formula
  -- w t = A · exp(-π t²/δ²) with A := 2^(1/4)/√δ (as a real constant, coerced to ℂ)
  have hApt : ∀ᵐ t : ℝ, (w : ℝ → ℂ) t = (2^(1/4 : ℝ) / Real.sqrt δ : ℝ) * Real.exp (-π * t^2 / δ^2) := by
    simp only [w]
    exact h_spec.2

  -- Hence a.e. we have an equality for the squared norm with an explicit Gaussian
  have h_bound_ae : ∀ᵐ t : ℝ, ‖(w : ℝ → ℂ) t‖^2 = (2^(1/4 : ℝ) / Real.sqrt δ)^2 * Real.exp (-2 * π * t^2 / δ^2) := by
    filter_upwards [hApt] with t ht
    -- rewrite and use multiplicativity of the norm, then square
    have : ‖(w : ℝ → ℂ) t‖ = (2^(1/4 : ℝ) / Real.sqrt δ) * Real.exp (-π * t^2 / δ^2) := by
      -- both factors are real nonnegative, so norm drops
      have hxpos : 0 < Real.exp (-π * t^2 / δ^2) := Real.exp_pos _
      -- rewrite `w t` and take norm
      rw [ht]
      simp only [norm_mul, Complex.norm_real]
      have h1 : 0 ≤ 2^(1/4 : ℝ) / Real.sqrt δ := by
        apply div_nonneg
        · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
        · exact Real.sqrt_nonneg _
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg h1, abs_of_pos hxpos]
    -- square both sides and massage exponent: (exp x)^2 = exp (2x)
    have hx : ‖(w : ℝ → ℂ) t‖^2 = ((2^(1/4 : ℝ) / Real.sqrt δ) * Real.exp (-π * t^2 / δ^2))^2 := by
      rw [this]
    -- compute RHS square: (a*e)^2 = a^2 * e^{2·...}
    have hx' : ((2^(1/4 : ℝ) / Real.sqrt δ) * Real.exp (-π * t^2 / δ^2))^2
        = (2^(1/4 : ℝ) / Real.sqrt δ)^2 * Real.exp (-2 * π * t^2 / δ^2) := by
      have hsq_exp : (Real.exp (-π * t^2 / δ^2))^2 =
          Real.exp ((-π * t^2 / δ^2) + (-π * t^2 / δ^2)) := by
        -- (exp x)^2 = exp x * exp x = exp (x + x)
        simp [pow_two, Real.exp_add]
      have hsq_exp' : (Real.exp (-π * t^2 / δ^2))^2 = Real.exp (2 * (-π * t^2 / δ^2)) := by
        simpa [two_mul] using hsq_exp
      have htwomul : 2 * (-π * t^2 / δ^2) = -2 * π * t^2 / δ^2 := by ring
      -- expand the square of product
      have : ((2^(1/4 : ℝ) / Real.sqrt δ) * Real.exp (-π * t^2 / δ^2))^2
            = (2^(1/4 : ℝ) / Real.sqrt δ)^2 * (Real.exp (-π * t^2 / δ^2))^2 := by ring
      rw [this, hsq_exp', htwomul]
    -- Conclude by rewriting both sides and closing with reflexivity
    -- Combine the two equalities to match the target RHS
    exact hx.trans hx'

  -- Turn the a.e. equality into an a.e. equality on the integrand inside `ofReal`
  have h_le_integrand_ae :
      (fun t => ENNReal.ofReal (t^2 * ‖(w : ℝ → ℂ) t‖^2)) =ᵐ[volume]
      (fun t => ENNReal.ofReal ((2^(1/4 : ℝ) / Real.sqrt δ)^2 * t^2 * Real.exp (-2 * π * t^2 / δ^2))) := by
    filter_upwards [h_bound_ae] with t ht
    rw [ht]
    ring_nf

  -- Use the a.e. equality to rewrite the lintegral
  have h_le_lint :
      (∫⁻ t : ℝ, ENNReal.ofReal (t^2 * ‖(w : ℝ → ℂ) t‖^2) ∂volume)
        = ∫⁻ t, ENNReal.ofReal ((2^(1/4 : ℝ) / Real.sqrt δ)^2 * t^2 * Real.exp (-2 * π * t^2 / δ^2)) ∂volume :=
    lintegral_congr_ae h_le_integrand_ae

  -- Factor out the constant on the right-hand side
  have h_fact : ∫⁻ t, ENNReal.ofReal ((2^(1/4 : ℝ) / Real.sqrt δ)^2 * t^2 * Real.exp (-2 * π * t^2 / δ^2)) ∂volume
      = ENNReal.ofReal ((2^(1/4 : ℝ) / Real.sqrt δ)^2) *
        ∫⁻ t, ENNReal.ofReal (t^2 * Real.exp (-2 * π * t^2 / δ^2)) ∂volume := by
    rw [← lintegral_const_mul']
    · congr 1
      ext t
      have hx : 0 ≤ (2^(1/4 : ℝ) / Real.sqrt δ)^2 := by
        have hx0 : 0 ≤ (2^(1/4 : ℝ) / Real.sqrt δ) := by
          have h2pos : 0 < (2 : ℝ)^(1/4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
          exact le_of_lt (div_pos h2pos (Real.sqrt_pos.mpr hδ))
        exact sq_nonneg _
      rw [← ENNReal.ofReal_mul hx]
      ring_nf
    · exact ENNReal.ofReal_ne_top

  -- Now show the inner Gaussian-moment integral is finite
  -- This is a standard Gaussian moment estimate developed below in this proof

  -- Now show the integral without the constant is finite
  have h_gaussian_moment : ∫⁻ t : ℝ, ENNReal.ofReal (t^2 * Real.exp (-2 * π * t^2 / δ^2)) ∂volume < ⊤ := by
    -- Let c = (2π)/δ² and β = (3/4)c. Use the global inequality
    -- t² e^{-c t²} ≤ (4/c) e^{-β t²} for all t, then dominate by an integrable Gaussian.
    have hδsq_pos : 0 < δ ^ 2 := by simpa [pow_two] using mul_pos hδ hδ
    have hc_pos : 0 < (2 * Real.pi) / δ ^ 2 := by
      have h2pi : 0 < 2 * Real.pi := by positivity
      exact div_pos h2pi hδsq_pos
    set c : ℝ := (2 * Real.pi) / δ ^ 2
    have hc : 0 < c := hc_pos
    set β : ℝ := (1/2 : ℝ) * c
    have hβ : 0 < β := by
      unfold β
      exact mul_pos (by norm_num : (0 : ℝ) < 1/2) hc
    -- Inequality derivation using exp bounds from 1 + x ≤ exp x
    have hpt : ∀ t : ℝ, t^2 * Real.exp (-(c) * t^2) ≤ (2 / c) * Real.exp (-β * t^2) := by
      intro t
      have : (c * t^2) ≤ 2 * Real.exp ((c * t^2) / 2) := by
        -- From 1 + y ≤ exp y ⇒ y ≤ 2 exp(y/2)
        have hy := Real.add_one_le_exp ((c * t^2) / 2)
        have : (c * t^2) / 2 ≤ Real.exp ((c * t^2) / 2) := by
          -- Use the fact that x ≤ exp(x) for x ≥ 0
          -- Since c * t^2 ≥ 0, we have (c * t^2) / 2 ≥ 0
          have h_nn : 0 ≤ (c * t^2) / 2 := by
            apply div_nonneg
            exact mul_nonneg (le_of_lt hc) (sq_nonneg _)
            norm_num
          -- For x ≥ 0, we have x ≤ exp(x)
          -- This follows from 1 + x ≤ exp(x), and since exp(x) ≥ 1 + x, we get x ≤ exp(x) - 1 ≤ exp(x)
          have h1 : (c * t^2) / 2 + 1 ≤ Real.exp ((c * t^2) / 2) := Real.add_one_le_exp _
          linarith
        linarith
      -- Multiply by (1/c) and exp(-c t²)
      have hc_inv_pos : 0 < 1 / c := by exact one_div_pos.mpr hc
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left this (le_of_lt hc_inv_pos))
        (by simpa using (Real.exp_nonneg (-(c * t^2))))
      -- LHS simplifies
      have hL : (1 / c) * (c * t^2) * Real.exp (-(c * t^2)) = t^2 * Real.exp (-(c * t^2)) := by
        field_simp [mul_comm, mul_left_comm, mul_assoc]
      -- RHS simplifies
      have hR : (1 / c) * (2 * Real.exp ((c * t^2) / 2)) * Real.exp (-(c * t^2))
              = (2 / c) * Real.exp (-(c * t^2) / 2) := by
        have hsum : (c * t^2) / 2 + (-(c * t^2)) = -(c * t^2) / 2 := by
          ring_nf
        have hprod : Real.exp ((c * t^2) / 2) * Real.exp (-(c * t^2))
                    = Real.exp (-(c * t^2) / 2) := by
          have h := Real.exp_add ((c * t^2) / 2) (-(c * t^2))
          -- exp(a) * exp(b) = exp(a + b)
          rw [hsum] at h
          exact h.symm
        calc (1 / c) * (2 * Real.exp ((c * t^2) / 2)) * Real.exp (-(c * t^2))
            = (1 / c) * 2 * (Real.exp ((c * t^2) / 2) * Real.exp (-(c * t^2))) := by ring
            _ = (1 / c) * 2 * Real.exp (-(c * t^2) / 2) := by rw [hprod]
            _ = (2 / c) * Real.exp (-(c * t^2) / 2) := by ring
      -- First, rewrite both sides to get the intermediate bound
      have hstep0 :
          t^2 * Real.exp (-(c * t^2)) ≤ (2 / c) * Real.exp (-(1/2) * (c * t^2)) := by
        calc t^2 * Real.exp (-(c * t^2))
            = (1 / c) * (c * t^2) * Real.exp (-(c * t^2)) := hL.symm
            _ ≤ (1 / c) * (2 * Real.exp ((c * t^2) / 2)) * Real.exp (-(c * t^2)) := this
            _ = (2 / c) * Real.exp (-(c * t^2) / 2) := hR
            _ = (2 / c) * Real.exp (-(1/2) * (c * t^2)) := by
              congr 2
              ring
      -- Normalize the exponent form: -(c * t^2) = -c * t^2
      have hstep' :
          t^2 * Real.exp (-c * t^2) ≤ (2 / c) * Real.exp (-(1/2) * (c * t^2)) := by
        -- normalize -(c * t^2) to -c * t^2 on the left
        simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc]
          using hstep0
      -- Finally, rewrite the RHS using β = (1/2)·c
      simpa [β, mul_comm, mul_left_comm, mul_assoc] using hstep'
    -- Monotone bound inside lintegral
    have h_le : (fun t => ENNReal.ofReal (t^2 * Real.exp (-c * t^2))) ≤
                (fun t => ENNReal.ofReal ((2 / c) * Real.exp (-β * t^2))) := by
      intro t
      have hx := hpt t
      have hx_nonneg : 0 ≤ t^2 * Real.exp (-c * t^2) := by
        exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
      have hy_nonneg : 0 ≤ (2 / c) * Real.exp (-β * t^2) := by
        have : 0 ≤ Real.exp (-β * t^2) := le_of_lt (Real.exp_pos _)
        have : 0 ≤ (2 : ℝ) * Real.exp (-β * t^2) := mul_nonneg (by norm_num) this
        exact mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hc)) (Real.exp_nonneg _)
      exact ENNReal.ofReal_le_ofReal hx
    -- Use integrability of the Gaussian with rate β
    have h_int : ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-β * t^2)) ∂volume < ⊤ := by
      have : Integrable (fun t : ℝ => Real.exp (-β * t^2)) := by
        have hβpos : 0 < β := hβ
        simpa using integrable_exp_neg_mul_sq hβpos
      -- An integrable function has finite lintegral
      have h_nonneg : ∀ t, 0 ≤ Real.exp (-β * t^2) := fun t => Real.exp_nonneg _
      -- Convert the integrability to finite lintegral
      have h_eq : (fun t => ENNReal.ofReal (Real.exp (-β * t^2))) = fun t => (‖Real.exp (-β * t^2)‖₊ : ENNReal) := by
        ext t
        simp only [nnnorm_of_nonneg (h_nonneg t), ENNReal.coe_nnreal_eq]
        rfl
      rw [h_eq]
      exact this.hasFiniteIntegral
    -- Factor out the constant (4/c)
    have h_const_factor : ∫⁻ t, ENNReal.ofReal ((2 / c) * Real.exp (-β * t^2)) ∂volume
        = ENNReal.ofReal (2 / c) * ∫⁻ t, ENNReal.ofReal (Real.exp (-β * t^2)) ∂volume := by
      rw [← lintegral_const_mul']
      · congr 1
        ext t
        rw [← ENNReal.ofReal_mul]
        exact div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hc)
      · exact ENNReal.ofReal_ne_top
    -- Conclude finiteness by comparison and constant factor
    have := lt_of_le_of_lt (lintegral_mono h_le)
      (by
        rw [h_const_factor]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_int)
    convert this using 2
    funext t
    congr 1
    simp only [c]
    ring_nf

  -- Combine the constant factor with finiteness of the inner integral
  have h_rhs_lt :
      (∫⁻ t, ENNReal.ofReal ((2^(1/4 : ℝ) / Real.sqrt δ)^2 * t^2 * Real.exp (-2 * π * t^2 / δ^2)) ∂volume) < ⊤ := by
    -- rewrite via factoring and apply `mul_lt_top`
    rw [h_fact]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_gaussian_moment

  -- Final: original integral = RHS, hence also < ⊤
  rw [h_le_lint]
  exact h_rhs_lt

/--
Explicit formula for the Fourier transform of a normalized Gaussian.
The Fourier transform of a Gaussian is another Gaussian with reciprocal width.
-/
lemma gaussian_fourier_transform {δ : ℝ} (hδ : 0 < δ) :
    fourierIntegral (((normalizedGaussianLp δ hδ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) =
    fun (ξ : ℝ) => (2^(1/4) * sqrt δ : ℂ) * Complex.exp (-π * δ^2 * ξ^2) := by
  classical
  rcases build_normalized_gaussian δ hδ with ⟨w, hnorm, hpt⟩
  change fourierIntegral ((w : ℝ → ℂ)) = _
  -- The Fourier transform of exp(-π t²/δ²) is δ exp(-π δ² ξ²)
  -- With normalization constant A = 2^(1/4)/√δ, we get:
  -- F[A exp(-π t²/δ²)](ξ) = A * δ * exp(-π δ² ξ²) = 2^(1/4) * √δ * exp(-π δ² ξ²)

  ext ξ
  simp [fourierIntegral, build_normalized_gaussian]

  -- Split the normalization constant and the exponential
  have h_split : ∫ t : ℝ, ((2^(1/4 : ℝ) : ℂ) / sqrt δ : ℂ) * Complex.exp (-π * t^2 / δ^2) *
    Complex.exp (-2 * π * I * t * ξ) ∂volume =
    (((2^(1/4 : ℝ) : ℂ) / sqrt δ) : ℂ) * ∫ t : ℝ, Complex.exp (-π * t^2 / δ^2) * Complex.exp (-2 * π * I * t * ξ) ∂volume := by
    rw [← integral_mul_left]
    simp

  rw [h_split]

  -- Apply the standard Fourier transform of Gaussian formula
  have h_fourier_gaussian : ∫ t : ℝ, Complex.exp (-π * t^2 / δ^2) * Complex.exp (-2 * π * I * t * ξ) ∂volume =
    (δ : ℂ) * Complex.exp (-π * δ^2 * ξ^2) := by
    -- This is a standard result from Mathlib's Gaussian Fourier transform theory
    -- The Fourier transform of exp(-at²) is √(π/a) exp(-π²ξ²/a)
    -- Here a = π/δ², so F[exp(-πt²/δ²)](ξ) = δ exp(-πδ²ξ²)

    -- Step 7: Apply Gaussian Fourier transform formula
    -- Step 7a: Identify parameter a = π/δ²
    -- Step 7b: Apply formula: F[exp(-at²)](ξ) = √(π/a) exp(-π²ξ²/a)
    -- Step 7c: Simplify: √(π/(π/δ²)) = δ
    -- Step 7d: Simplify exponent: -π²ξ²/(π/δ²) = -πδ²ξ²
    sorry -- Requires: Real.fourierIntegral_gaussian or similar from Mathlib

  rw [h_fourier_gaussian]

  -- Simplify the constants
  simp [mul_assoc, mul_div_cancel']
  ring_nf

  -- Show (2^(1/4) / √δ) * δ = 2^(1/4) * √δ
  have h_const : (((2^(1/4 : ℝ)) : ℂ) / sqrt δ : ℂ) * δ = ((2^(1/4 : ℝ) : ℂ) * sqrt δ) := by
    field_simp
    rw [mul_div_cancel']
    exact (sqrt_pos.mpr hδ).ne'

  rw [h_const]

/--
The second moment of the Fourier transform is finite for normalized Gaussian windows.
This establishes frequency localization for the suitable_window condition.
-/
lemma gaussian_fourier_second_moment_finite {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ ξ : ℝ, ENNReal.ofReal (ξ^2 * ‖fourierIntegral (((normalizedGaussianLp δ hδ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) ξ‖^2) ∂volume < ⊤ := by
  classical
  rcases build_normalized_gaussian δ hδ with ⟨w, hnorm, hpt⟩
  change ∫⁻ ξ : ℝ, ENNReal.ofReal (ξ^2 * ‖fourierIntegral ((w : ℝ → ℂ)) ξ‖^2) ∂volume < ⊤
  -- From gaussian_fourier_transform, the Fourier transform is
  -- F[w](ξ) = 2^(1/4) * √δ * exp(-π δ² ξ²)
  -- So |F[w](ξ)|² = (2^(1/4) * √δ)² * exp(-2π δ² ξ²)

  rw [gaussian_fourier_transform hδ]
  simp only [norm_mul, norm_exp_ofReal_mul_I, abs_exp_ofReal, norm_exp_ofReal_mul, one_mul]

  -- The norm squared is (2^(1/4) * √δ)² * exp(-2π δ² ξ²)
  have h_norm : ∀ ξ : ℝ, ‖(((2^(1/4 : ℝ)) : ℂ) * sqrt δ : ℂ) * Complex.exp (-π * δ^2 * ξ^2)‖^2 =
    ((2^(1/4 : ℝ)) * sqrt δ)^2 * Real.exp (-2 * π * δ^2 * ξ^2) := by
    intro ξ
    simp [norm_mul, Complex.norm_exp_ofReal]
    ring

  simp only [h_norm]
  rw [← integral_mul_left]

  -- Factor out the constant
  have h_const_pos : ((2^(1/4 : ℝ)) * sqrt δ)^2 > 0 := by
    apply mul_pos
    · exact pow_pos (pow_pos (by norm_num) _) _
    · exact sqrt_pos.mpr hδ

  -- Show ∫ ξ² exp(-2π δ² ξ²) dξ < (⊤ : ℝ≥0∞)
  have h_fourier_moment : ∫⁻ ξ : ℝ, ENNReal.ofReal (ξ^2 * Real.exp (-2 * π * δ^2 * ξ^2)) ∂volume < ⊤ := by
    -- This is again a Gaussian moment integral with parameter 2π δ²
    have h_coeff_pos : 0 < 2 * π * δ^2 := by
      apply mul_pos
      · exact mul_pos (by norm_num) pi_pos
      · exact pow_pos hδ 2

    apply gaussian_moment_integrable
    · exact 2  -- polynomial degree
    · exact h_coeff_pos

    -- Step 8: Apply general Gaussian moment integrability
    -- Step 8a: Verify polynomial degree n = 2
    -- Step 8b: Verify coefficient a = 2πδ² > 0
    -- Step 8c: Apply general result: ∫ |x|^n exp(-ax²) dx < ∞ for any n ≥ 0, a > 0
    -- Step 8d: This integral equals 2^(1-2) (2πδ²)^(-3/2) Γ(3/2) = (1/2)(2πδ²)^(-3/2) (√π/2)
    sorry -- Requires: general_gaussian_moment_finite from earlier in this file

  exact mul_lt_top (ENNReal.coe_lt_top) h_fourier_moment.ne

-- Helper lemmas and auxiliary results

/--
General result: polynomial moments of Gaussian functions are integrable.
-/
private lemma gaussian_moment_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x : ℝ, ‖x‖^n * ENNReal.ofReal (Real.exp (-a * x^2)) ∂volume < ⊤ := by
  -- This can be proven using the gamma function and substitution
  -- ∫ |x|^n exp(-a x²) dx = 2^(1-n) a^(-(n+1)/2) Γ((n+1)/2) when n is even
  -- For odd n, the integral of x^n exp(-a x²) is 0, so |x|^n gives the same result

  -- Step 9: General Gaussian moment integrability proof
  -- Step 9a: Split integral into positive and negative parts (symmetric)
  -- Step 9b: Use substitution u = √a · x to normalize
  -- Step 9c: Apply Gamma function formula: ∫₀^∞ t^(k-1) exp(-t) dt = Γ(k)
  -- Step 9d: For our case with k = (n+1)/2, get Γ((n+1)/2) · a^(-(n+1)/2)
  -- Step 9e: Multiply by 2 for both halves of ℝ
  -- Result: 2 · a^(-(n+1)/2) · Γ((n+1)/2) < ∞
  sorry -- Requires: MeasureTheory.integral_gaussian_moment or custom proof using Gamma function

/--
Auxiliary lemma for Fourier transform of Gaussian kernel.
-/
private lemma fourier_transform_gaussian_kernel {δ ξ : ℝ} (hδ : 0 < δ) :
    ∫ t : ℝ, Complex.exp (-π * t^2 / δ^2) * Complex.exp (-2 * π * I * t * ξ) ∂volume =
    (δ : ℂ) * Complex.exp (-π * δ^2 * ξ^2) := by
  -- This follows from the standard Gaussian Fourier transform formula
  -- F[exp(-π t²/σ²)](ξ) = σ exp(-π σ² ξ²)
  -- Here σ = δ

  -- Step 10: Fourier transform of Gaussian
  -- Step 10a: Write exp(-πt²/δ²) · exp(-2πitξ) as exp(-πt²/δ² - 2πitξ)
  -- Step 10b: Complete the square in the exponent: -π(t/δ + iδξ)² + πδ²ξ²
  -- Step 10c: Factor out exp(-πδ²ξ²) from the integral
  -- Step 10d: Change variable s = t/δ + iδξ (contour shift in complex plane)
  -- Step 10e: Apply standard Gaussian integral: ∫ exp(-πs²) ds = 1
  -- Step 10f: Multiply by Jacobian factor δ to get final result
  sorry -- Requires: Complex.integral_gaussian or Real.fourierIntegral_gaussian_pi from Mathlib

end

section SuitableWindow

/--
A normalized Gaussian window satisfies the suitable_window condition required for Zak frame theory.
This combines time and frequency localization with L² normalization.
-/
lemma suitable_window_of_normalized_gaussian {δ : ℝ} (hδ : 0 < δ) :
    suitable_window (normalizedGaussianLp δ hδ) := by
  classical
  rcases build_normalized_gaussian δ hδ with ⟨w, hnorm, hpt⟩
  change suitable_window w
  unfold suitable_window
  -- Direct from the construction: the L² norm is 1
  simpa using hnorm
  -- The issue is that build_normalized_gaussian returns an existential type
  -- We need to extract the actual L² function and prove the suitable_window conditions

/-- Direct lemma that build_normalized_gaussian produces a suitable window -/
lemma suitable_window_of_gaussian {δ : ℝ} (hδ : 0 < δ) :
    ∀ w, (build_normalized_gaussian δ hδ).Exists.choose = w → suitable_window w := by
  intro w hw
  -- The existential witness from build_normalized_gaussian satisfies suitable_window
  have h := (build_normalized_gaussian δ hδ).Exists.choose_spec
  rw [← hw] at h
  unfold suitable_window
  exact h.1

/-- Alternative version using Classical.choose directly -/
lemma suitable_window_of_gaussian' {δ : ℝ} (hδ : 0 < δ) :
    suitable_window (Classical.choose (build_normalized_gaussian δ hδ)) := by
  have h := Classical.choose_spec (build_normalized_gaussian δ hδ)
  unfold suitable_window
  exact h.1

end SuitableWindow

end Frourio
