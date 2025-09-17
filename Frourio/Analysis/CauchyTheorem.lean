import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Frourio.Analysis.Gaussian

/-!
# Cauchy's Theorem and Complex Contour Integration

This file contains signatures and basic results for Cauchy's theorem
and complex contour integration, particularly for applications to
Gaussian integrals and the Riemann Hypothesis proof.

## Main definitions and results

* `contour_integral_independent_of_path`: For holomorphic functions, the integral
  is independent of the path between two points
* `cauchy_theorem_rectangle`: Cauchy's theorem for rectangular contours
* `horizontal_shift_invariance`: Shifting integration by a purely imaginary constant
  doesn't change the value for rapidly decaying entire functions
* `gaussian_contour_shift_general`: General contour shift for Gaussian-like functions

## Implementation notes

These are primarily signatures that will be needed for the full proof.
The actual implementations require deep complex analysis theory.
-/

namespace Frourio

open Complex MeasureTheory Real Filter Topology

section CauchyTheorem

/--
Equality of parameterized rectangular contour and standard interval representation.
This lemma shows that the sum of parameterized integrals along a rectangular path
equals the standard Cauchy integral representation.
-/
lemma rectangular_contour_conversion (f : ℂ → ℂ) (z₀ z₁ z₂ : ℂ) :
    ((∫ x : ℝ in z₀.re..z₁.re, f (x + z₀.im * I)) +
     I • (∫ y : ℝ in z₀.im..z₂.im, f (z₁.re + y * I))) +
    (-(∫ x : ℝ in z₀.re..z₁.re, f (x + z₂.im * I))) +
    (-I • (∫ y : ℝ in z₀.im..z₂.im, f (z₀.re + y * I))) =
    (∫ x : ℝ in z₀.re..z₁.re, f (x + z₀.im * I)) -
    (∫ x : ℝ in z₀.re..z₁.re, f (x + z₂.im * I)) +
    I • (∫ y : ℝ in z₀.im..z₂.im, f (z₁.re + y * I)) -
    I • (∫ y : ℝ in z₀.im..z₂.im, f (z₀.re + y * I)) := by
  -- The left side is already in the form a + b + (-c) + (-d)
  -- The right side is in the form a - c + b - d
  -- These are algebraically equal: a + b + (-c) + (-d) = a - c + b - d

  -- Rearrange the left side using associativity and commutativity
  have h1 : ((∫ x : ℝ in z₀.re..z₁.re, f (x + z₀.im * I)) +
            I • (∫ y : ℝ in z₀.im..z₂.im, f (z₁.re + y * I))) +
           (-(∫ x : ℝ in z₀.re..z₁.re, f (x + z₂.im * I))) +
           (-I • (∫ y : ℝ in z₀.im..z₂.im, f (z₀.re + y * I))) =
           (∫ x : ℝ in z₀.re..z₁.re, f (x + z₀.im * I)) +
           (-(∫ x : ℝ in z₀.re..z₁.re, f (x + z₂.im * I))) +
           I • (∫ y : ℝ in z₀.im..z₂.im, f (z₁.re + y * I)) +
           (-I • (∫ y : ℝ in z₀.im..z₂.im, f (z₀.re + y * I))) := by
    ring

  -- Convert negations to subtractions
  have h2 : (∫ x : ℝ in z₀.re..z₁.re, f (x + z₀.im * I)) +
            (-(∫ x : ℝ in z₀.re..z₁.re, f (x + z₂.im * I))) +
            I • (∫ y : ℝ in z₀.im..z₂.im, f (z₁.re + y * I)) +
            (-I • (∫ y : ℝ in z₀.im..z₂.im, f (z₀.re + y * I))) =
            (∫ x : ℝ in z₀.re..z₁.re, f (x + z₀.im * I)) -
            (∫ x : ℝ in z₀.re..z₁.re, f (x + z₂.im * I)) +
            I • (∫ y : ℝ in z₀.im..z₂.im, f (z₁.re + y * I)) -
            I • (∫ y : ℝ in z₀.im..z₂.im, f (z₀.re + y * I)) := by
    -- This follows from the definition of subtraction: a + (-b) = a - b
    simp only [sub_eq_add_neg]
    -- Need to show -I • x = -(I • x)
    simp only [neg_smul]

  rw [h1, h2]

/--
The norm of a complex number x + yi equals √(x² + y²).
-/
lemma complex_norm_add_mul_I (x y : ℝ) :
    ‖(↑x : ℂ) + ↑y * I‖ = Real.sqrt (x^2 + y^2) := by
  -- Step 1: Express the complex number in terms of its real and imaginary parts
  have h_re : ((↑x : ℂ) + ↑y * I).re = x := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re]
  have h_im : ((↑x : ℂ) + ↑y * I).im = y := by
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im]
  -- Step 2: Apply the formula |z| = sqrt(re(z)² + im(z)²)
  -- The norm squared of a complex number equals re² + im²
  have norm_sq : ‖(↑x : ℂ) + ↑y * I‖^2 = x^2 + y^2 := by
    -- For complex numbers, ‖z‖² = |z|² = re(z)² + im(z)²
    -- First, expand the norm squared using the formula
    have norm_sq_formula : ∀ (z : ℂ), ‖z‖^2 = z.re^2 + z.im^2 := by
      intro z
      -- This is a fundamental property of complex numbers
      -- ‖a + bi‖² = a² + b²
      simpa [Complex.normSq, pow_two] using (Complex.normSq_eq_norm_sq z).symm
    -- Apply the formula to our specific complex number
    rw [norm_sq_formula]
    -- Substitute the real and imaginary parts
    rw [h_re, h_im]
  -- Taking square root of both sides gives the result
  have h : ‖(↑x : ℂ) + ↑y * I‖ = Real.sqrt (‖(↑x : ℂ) + ↑y * I‖^2) := by
    rw [Real.sqrt_sq]
    exact norm_nonneg _
  rw [h, norm_sq]

/--
A function with Gaussian decay is integrable along any horizontal line in the complex plane.
-/
lemma integrable_of_gaussian_decay_horizontal {f : ℂ → ℂ} {y : ℝ}
    (hf_entire : ∀ z, DifferentiableAt ℂ f z)
    (hf_decay : ∃ (A B : ℝ) (hA : 0 < A) (hB : 0 < B),
      ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (-B * ‖z‖^2)) :
    Integrable (fun x : ℝ => f (x + y * I)) := by
  -- Extract the decay constants
  obtain ⟨A, B, hA, hB, hdecay⟩ := hf_decay

  -- Use the decay bound to establish integrability
  -- We have ‖f(x + y₁*I)‖ ≤ A * exp(-B * ‖x + y₁*I‖²)
  -- Since ‖x + y₁*I‖² = x² + y₁², this gives us a Gaussian bound

  -- Apply integrability criterion using comparison with a Gaussian bound
  -- The function g(x) = A * exp(-B * y₁²) * exp(-B * x²) will serve as our integrable bound
  let g := fun x => A * Real.exp (-B * y^2) * Real.exp (-B * x^2)

  -- Show integrability using the bound
  have hg_integrable : Integrable g := by
    simp only [g]
    have h1 := integrable_exp_neg_mul_sq hB
    have h2 := h1.const_mul (A * Real.exp (-B * y^2))
    exact h2

  have hf_measurable : AEStronglyMeasurable (fun x : ℝ => f (↑x + ↑y * I)) volume := by
    apply Continuous.aestronglyMeasurable
    -- f is continuous everywhere as it's differentiable
    apply Continuous.comp
    · -- f is continuous
      apply continuous_iff_continuousAt.mpr
      intro z
      exact (hf_entire z).continuousAt
    · -- The map x ↦ x + y₁ * I is continuous
      exact continuous_ofReal.add continuous_const

  have h_bound : ∀ᵐ (x : ℝ) ∂volume, ‖f (↑x + ↑y * I)‖ ≤ g x := by
    apply ae_of_all
    intro x
    simp only [g]
    have h := hdecay (↑x + ↑y * I)
    calc ‖f (↑x + ↑y * I)‖
      ≤ A * Real.exp (-B * ‖↑x + ↑y * I‖^2) := h
      _ = A * Real.exp (-B * (x^2 + y^2)) := by
        congr 2
        -- Calculate ‖x + y₁*I‖² = x² + y₁²
        -- The norm squared of a + bi equals a² + b²
        have := complex_norm_add_mul_I x y
        rw [pow_two, this, mul_self_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
      _ = A * Real.exp (-B * y^2) * Real.exp (-B * x^2) := by
        have h : -B * (x^2 + y^2) = -B * y^2 + -B * x^2 := by ring
        rw [h, Real.exp_add]
        ring

  exact Integrable.mono' hg_integrable hf_measurable h_bound

lemma cauchy_rectangle_formula {f : ℂ → ℂ} {R : ℝ} {y₁ y₂ : ℝ}
    (hf_rect : DifferentiableOn ℂ f (Set.uIcc (-R) R ×ℂ Set.uIcc y₁ y₂)) :
    (∫ x in (-R:ℝ)..R, f (x + y₁ * I)) - (∫ x in (-R:ℝ)..R, f (x + y₂ * I)) =
    - (I • (∫ t in y₁..y₂, f (R + t * I)) - I • (∫ t in y₁..y₂, f (-R + t * I))) := by
  -- Define rectangle corners
  let z₀ : ℂ := ⟨-R, y₁⟩
  let z₁ : ℂ := ⟨R, y₂⟩

  -- Apply Cauchy's theorem from mathlib
  have cauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z₀ z₁ hf_rect

  -- Cauchy's theorem gives us (with z₀ = (-R, y₁) and z₁ = (R, y₂)):
  -- (∫ x in -R..R, f(x + y₁*I)) - (∫ x in -R..R, f(x + y₂*I))
  -- + I • (∫ t in y₁..y₂, f(R + t*I)) - I • (∫ t in y₁..y₂, f(-R + t*I)) = 0

  simp only [z₀, z₁] at cauchy

  -- From Cauchy's theorem, simplify the expression
  simp only [Complex.ofReal_neg] at cauchy

  -- Now cauchy states:
  -- (∫ x in -R..R, f(x + y₁*I)) - (∫ x in -R..R, f(x + y₂*I))
  -- + I • (∫ t in y₁..y₂, f(R + t*I)) - I • (∫ t in y₁..y₂, f(-R + t*I)) = 0

  -- Rearrange algebraically to get the desired form
  rw [eq_neg_iff_add_eq_zero]
  convert cauchy using 1
  -- Need to show equality after converting to appropriate form
  ring

lemma vertical_integral_bound_exp {a : ℂ} {R : ℝ} {y₁ y₂ : ℝ}
    (ha : 0 < a.re) (hy : y₁ ≤ y₂) :
    ∃ C : ℝ, ‖∫ t in y₁..y₂, Complex.exp (-a * (R + t * I)^2)‖ ≤
    Real.exp (-a.re * R^2) * C := by
  -- For f(z) = exp(-a * z²), we evaluate the integral along the vertical line
  -- z = R + t*I for t ∈ [y₁, y₂]

  -- Expand (R + t*I)² = R² + 2*R*t*I - t²
  have h_expand : ∀ t : ℝ, (R + t * I : ℂ)^2 = R^2 - t^2 + 2*R*t*I := by
    intro t
    simp only [sq, add_mul, mul_add, mul_comm I, mul_assoc, I_mul_I]
    ring

  -- So -a * (R + t*I)² = -a.re * (R² - t²) + 2*a.im*R*t - i*(a.im * (R² - t²) + 2*a.re*R*t)
  have h_exp_decomp : ∀ t : ℝ,
    -a * (R + t * I)^2 = ((-a.re * (R^2 - t^2) + 2*a.im*R*t) : ℂ)
                       + I * ((-a.im * (R^2 - t^2) - 2*a.re*R*t) : ℝ) := by
    intro t
    sorry -- Complex decomposition of -a * (R + t * I)^2

  -- The norm of exp(-a * (R + t*I)²) equals exp of the real part
  have h_norm : ∀ t : ℝ,
    ‖Complex.exp (-a * (R + t * I)^2)‖ = Real.exp (-a.re * (R^2 - t^2) + 2*a.im*R*t) := by
    intro t
    rw [h_exp_decomp]
    -- Use the fact that |exp(z)| = exp(Re(z))
    sorry -- Complex norm evaluation

  -- Factor out exp(-a.re * R²) from the bound
  have h_factor : ∀ t : ℝ,
    ‖Complex.exp (-a * (R + t * I)^2)‖ = Real.exp (-a.re * R^2) *
      Real.exp (a.re * t^2 + 2*a.im*R*t) := by
    intro t
    rw [h_norm]
    rw [← Real.exp_add]
    congr 1
    ring

  -- Define C as the integral of the remaining factor
  let C := |y₂ - y₁| * Real.exp (a.re * (max (y₁^2) (y₂^2)) + 2 * |a.im| * |R| * (max |y₁| |y₂|))

  use C

  -- Apply the bound using the factorization
  calc ‖∫ t in y₁..y₂, Complex.exp (-a * (R + t * I)^2)‖
    ≤ ∫ t in y₁..y₂, ‖Complex.exp (-a * (R + t * I)^2)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hy
    _ = ∫ t in y₁..y₂, Real.exp (-a.re * R^2) * Real.exp (a.re * t^2 + 2*a.im*R*t) := by
        congr 1
        ext t
        exact h_factor t
    _ = Real.exp (-a.re * R^2) * ∫ t in y₁..y₂, Real.exp (a.re * t^2 + 2*a.im*R*t) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ Real.exp (-a.re * R^2) * C := by
        gcongr
        -- The integral is bounded by |y₂ - y₁| times the max of the integrand
        sorry -- This requires bounding the integral by the maximum value times the interval length

lemma contour_limit_theorem {f : ℂ → ℂ} {y₁ y₂ : ℝ}
    (hf_integrable_y1 : Integrable (fun x : ℝ => f (x + y₁ * I)))
    (hf_integrable_y2 : Integrable (fun x : ℝ => f (x + y₂ * I)))
    (h_vert_vanish : ∀ ε > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R ≥ R₀,
      ‖I • (∫ t in y₁..y₂, f (R + t * I)) - I • (∫ t in y₁..y₂, f (-R + t * I))‖ < ε)
    (h_rect : ∀ R > (0 : ℝ),
      (∫ x in (-R:ℝ)..R, f (x + y₁ * I)) - (∫ x in (-R:ℝ)..R, f (x + y₂ * I)) =
      -(I • (∫ t in y₁..y₂, f (R + t * I)) - I • (∫ t in y₁..y₂, f (-R + t * I)))) :
    ∫ x : ℝ, f (x + y₁ * I) = ∫ x : ℝ, f (x + y₂ * I) := by
  -- Show that the difference of integrals equals zero
  have limit_eq : (∫ x : ℝ, f (x + y₁ * I)) - (∫ x : ℝ, f (x + y₂ * I)) = 0 := by
    classical
    let g : ℝ → ℂ := fun x => f (x + y₁ * I) - f (x + y₂ * I)
    have hg_integrable : Integrable g := hf_integrable_y1.sub hf_integrable_y2

    -- The finite integral converges to the improper integral
    have hg_tendsto :
        Tendsto (fun R : ℝ => ∫ x in (-R : ℝ)..R, g x) atTop
          (𝓝 (∫ x : ℝ, g x)) := by
      have :=
        intervalIntegral_tendsto_integral (μ := volume) (f := g)
          (a := fun R : ℝ => -R) (b := fun R : ℝ => R) hg_integrable
          tendsto_neg_atTop_atBot tendsto_id
      simpa using this

    -- The finite integral equals minus the vertical integrals by h_rect
    have h_rect_eq :
        (fun R : ℝ => ∫ x in (-R : ℝ)..R, g x) =ᶠ[Filter.atTop]
          (fun R : ℝ =>
            -(I • (∫ t in y₁..y₂, f (R + t * I)) -
              I • (∫ t in y₁..y₂, f (-R + t * I)))) := by
      refine (eventually_ge_atTop (1 : ℝ)).mono ?_
      intro R hRge1
      have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hRge1
      have hf1 :
          IntervalIntegrable (fun x : ℝ => f (x + y₁ * I)) volume (-R) R :=
        hf_integrable_y1.intervalIntegrable
      have hf2 :
          IntervalIntegrable (fun x : ℝ => f (x + y₂ * I)) volume (-R) R :=
        hf_integrable_y2.intervalIntegrable
      have h_sub :=
        intervalIntegral.integral_sub (μ := volume)
          (f := fun x : ℝ => f (x + y₁ * I))
          (g := fun x : ℝ => f (x + y₂ * I)) (a := (-R : ℝ)) (b := R) hf1 hf2
      have h_rect_R := h_rect R hRpos
      simp only [g]
      rw [h_sub, h_rect_R]

    -- The limit of the right side is the limit of g
    have h_right_tendsto :
        Tendsto (fun R : ℝ =>
            -(I • (∫ t in y₁..y₂, f (R + t * I)) -
              I • (∫ t in y₁..y₂, f (-R + t * I)))) atTop
          (𝓝 (∫ x : ℝ, g x)) := hg_tendsto.congr' h_rect_eq

    -- The vertical integrals vanish as R → ∞
    have h_vert_tendsto0 :
        Tendsto (fun R : ℝ =>
            I • (∫ t in y₁..y₂, f (R + t * I)) -
              I • (∫ t in y₁..y₂, f (-R + t * I))) atTop (𝓝 (0 : ℂ)) := by
      refine Metric.tendsto_atTop.2 ?_
      intro ε hε
      obtain ⟨R₀, hR₀_pos, hR₀⟩ := h_vert_vanish ε hε
      refine ⟨R₀, ?_⟩
      intro R hR
      have hnorm := hR₀ R hR
      simpa [dist_eq_norm] using hnorm

    -- Therefore, -(vertical integrals) also tends to 0
    have h_neg_vert_tendsto0 :
        Tendsto (fun R : ℝ =>
            -(I • (∫ t in y₁..y₂, f (R + t * I)) -
              I • (∫ t in y₁..y₂, f (-R + t * I)))) atTop (𝓝 (0 : ℂ)) := by
      refine Metric.tendsto_atTop.2 ?_
      intro ε hε
      obtain ⟨R₀, hR₀_pos, hR₀⟩ := h_vert_vanish ε hε
      refine ⟨R₀, ?_⟩
      intro R hR
      have hnorm := hR₀ R hR
      have :
          ‖-(I • (∫ t in y₁..y₂, f (R + t * I)) -
              I • (∫ t in y₁..y₂, f (-R + t * I)))‖ < ε := by
        rw [norm_neg]
        exact hnorm
      simpa [dist_eq_norm] using this

    -- By uniqueness of limits, ∫ g = 0
    have h_int_eq : ∫ x : ℝ, g x = 0 :=
      tendsto_nhds_unique h_right_tendsto h_neg_vert_tendsto0

    have h_sub := integral_sub hf_integrable_y1 hf_integrable_y2
    exact by
      simpa [g] using h_sub.symm.trans h_int_eq

  -- Conclude equality from limit_eq: diff = 0 implies equality
  exact sub_eq_zero.mp limit_eq

lemma gaussian_integrable_horizontal {a : ℂ} {y : ℝ} (ha : 0 < a.re) :
    Integrable (fun x : ℝ => Complex.exp (-a * (x + y * I)^2)) := by
  -- The Gaussian exp(-a(x+yi)²) satisfies the decay condition needed for horizontal_contour_shift
  -- We'll show integrability using the same approach as in horizontal_contour_shift

  -- Define the function
  let f := fun z => Complex.exp (-a * z^2)

  -- Verify f is entire
  have hf_entire : ∀ z, DifferentiableAt ℂ f z := by
    intro z
    simp [f]
    apply DifferentiableAt.cexp
    apply DifferentiableAt.neg
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.pow
    exact differentiableAt_id

  -- Establish Gaussian decay for f
  have hf_decay : ∃ (A B : ℝ) (hA : 0 < A) (hB : 0 < B),
      ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (-B * ‖z‖^2) := by
    -- For z = x + yi, we have z² = (x² - y²) + 2xyi
    -- So -a * z² = -a.re(x² - y²) + a.im·2xy - i(...)
    -- Thus |exp(-a * z²)| = exp(-a.re(x² - y²) + 2a.im·xy)

    -- We need to bound exp(-a.re(x² - y²) + 2a.im·xy) ≤ A * exp(-B(x² + y²))
    -- Using the inequality: 2|a.im·xy| ≤ |a.im|(x² + y²) for appropriate constants

    -- Choose B = a.re/2 (half the real part for safety)
    -- Choose A to compensate for the worst case of the imaginary part
    use Real.exp (|a.im|^2 / (2 * a.re)), a.re / 2, by {
      -- Show A > 0
      exact Real.exp_pos _
    }, by {
      -- Show B = a.re/2 > 0
      exact half_pos ha
    }

    intro z
    simp [f]
    -- Need to show: ‖exp(-a * z^2)‖ ≤ exp(|a.im|²/(2a.re)) * exp(-(a.re/2) * ‖z‖^2)

    -- This requires the inequality:
    -- exp(-a.re(x²-y²) + 2a.im·xy) ≤ exp(|a.im|²/(2a.re)) * exp(-(a.re/2)(x²+y²))
    -- Which follows from completing the square in the exponent
    sorry -- Detailed computation with completing the square

  -- Apply integrable_of_gaussian_decay_horizontal with y parameter
  have h_integrable : Integrable (fun x : ℝ => f (x + y * I)) :=
    integrable_of_gaussian_decay_horizontal (y := y) hf_entire hf_decay

  -- The function on the horizontal line y is exactly what we need
  convert h_integrable

/--
For entire functions with Gaussian decay, the integral over any horizontal line
has the same value. The decay condition automatically ensures integrability.
-/
theorem horizontal_contour_shift {f : ℂ → ℂ} {y₁ y₂ : ℝ}
    (hf_entire : ∀ z, DifferentiableAt ℂ f z)
    (hf_decay : ∃ (A B : ℝ) (_ : 0 < A) (_ : 0 < B),
      ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (-B * ‖z‖^2)) :
    ∫ x : ℝ, f (x + y₁ * I) = ∫ x : ℝ, f (x + y₂ * I) := by
  -- First derive integrability from the decay condition
  have hf_integrable_y1 :  Integrable (fun x : ℝ => f (x + y₁ * I)) :=
    integrable_of_gaussian_decay_horizontal hf_entire hf_decay

  have hf_integrable_y2 : Integrable (fun x : ℝ => f (x + y₂ * I)) :=
    integrable_of_gaussian_decay_horizontal hf_entire hf_decay

  -- Step 1: For any R > 0, apply Cauchy's theorem on rectangle using the lemma
  have rect_eq : ∀ R > 0,
    (∫ x in (-R:ℝ)..R, f (x + y₁ * I)) - (∫ x in (-R:ℝ)..R, f (x + y₂ * I)) =
    - (I • (∫ t in y₁..y₂, f (R + t * I)) - I • (∫ t in y₁..y₂, f (-R + t * I))) := by
    intro R hR
    -- Apply the lemma cauchy_rectangle_formula
    have hf_rect : DifferentiableOn ℂ f (Set.uIcc (-R) R ×ℂ Set.uIcc y₁ y₂) := by
      intro w _
      exact (hf_entire w).differentiableWithinAt
    exact cauchy_rectangle_formula hf_rect

  -- Step 2: Show vertical integrals vanish as R → ∞ due to decay
  -- We prove each vertical integral vanishes separately, then combine

  -- Extract decay constants from hf_decay
  obtain ⟨A, B, hA, hB, hdecay⟩ := hf_decay

  -- General lemma for vertical integral vanishing
  have vert_vanish_general : ∀ (sign : ℝ) (hsign : sign = 1 ∨ sign = -1), ∀ ε > (0 : ℝ),
    ∃ R₀ > (0 : ℝ), ∀ R ≥ R₀,
    ‖I • ∫ t in y₁..y₂, f ((sign * R : ℂ) + t * I)‖ < ε / 2 := by
    classical
    intro sign hsign ε hε
    obtain hsign_sq : sign^2 = (1 : ℝ) := by
      cases hsign with
      | inl h => simp [h]
      | inr h => simp [h]
    set const : ℝ := A * |y₂ - y₁| with hconst
    have hconst_nonneg : 0 ≤ const := by
      have hA_nonneg : 0 ≤ A := le_of_lt hA
      exact mul_nonneg hA_nonneg (abs_nonneg _)
    let C : ℝ → ℝ := fun R => A * Real.exp (-B * R^2)
    have h_integral_bound : ∀ R : ℝ,
        ‖I • ∫ t in y₁..y₂, f ((sign * R : ℂ) + t * I)‖ ≤ const * Real.exp (-B * R^2) := by
      intro R
      have h_pointwise : ∀ t : ℝ,
          ‖f ((sign * R : ℂ) + t * I)‖ ≤ C R := by
        intro t
        have h_decay := hdecay ((sign * R : ℂ) + t * I)
        have hsign_mul_sq : (sign * R)^2 = R^2 := by
          have := mul_pow sign R (2 : ℕ)
          simpa [pow_two, hsign_sq, mul_comm, mul_left_comm, mul_assoc] using this
        have hnorm_sq := complex_norm_add_mul_I (sign * R) t
        have hnorm_sq' := congrArg (fun x : ℝ => x ^ 2) hnorm_sq
        have hnonneg : 0 ≤ (sign * R)^2 + t^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
        have hnorm : ‖((sign * R : ℂ) + t * I)‖^2 = (sign * R)^2 + t^2 := by
          -- The issue is that (sign * R : ℂ) = ↑sign * ↑R, so the expressions differ
          -- Let's work with the expanded form directly
          have hcast : (sign * R : ℂ) = ↑sign * ↑R := by simp
          rw [hcast]
          -- Now we use the lemma about ↑(sign * R) + ↑t * I
          have : ‖↑sign * ↑R + ↑t * I‖ = ‖↑(sign * R) + ↑t * I‖ := by
            congr
            simp
          rw [this, pow_two, hnorm_sq]
          rw [mul_self_sqrt hnonneg]
        have hnorm' : ‖((sign * R : ℂ) + t * I)‖^2 = R^2 + t^2 := by
          simp [hnorm, hsign_mul_sq]
        have ht_nonneg : 0 ≤ t^2 := sq_nonneg t
        have hsum : R^2 ≤ R^2 + t^2 := le_add_of_nonneg_right ht_nonneg
        have hneg : -B ≤ 0 := neg_nonpos.mpr (le_of_lt hB)
        have hmul := mul_le_mul_of_nonpos_left hsum hneg
        have h_exp_le :
            Real.exp (-B * ‖((sign * R : ℂ) + t * I)‖^2) ≤ Real.exp (-B * R^2) := by
          simpa [hnorm'] using Real.exp_le_exp.mpr hmul
        have hA_nonneg : 0 ≤ A := le_of_lt hA
        exact h_decay.trans (mul_le_mul_of_nonneg_left h_exp_le hA_nonneg)
      have h_norm_integral :
          ‖∫ t in y₁..y₂, f ((sign * R : ℂ) + t * I)‖ ≤ C R * |y₂ - y₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro t _
        exact h_pointwise t
      have hnorm_smul :
          ‖I • ∫ t in y₁..y₂, f ((sign * R : ℂ) + t * I)‖ =
            ‖∫ t in y₁..y₂, f ((sign * R : ℂ) + t * I)‖ := by
        simp [Complex.norm_I]
      have := h_norm_integral
      calc
        ‖I • ∫ t in y₁..y₂, f ((sign * R : ℂ) + t * I)‖
            = ‖∫ t in y₁..y₂, f ((sign * R : ℂ) + t * I)‖ := hnorm_smul
        _ ≤ C R * |y₂ - y₁| := this
        _ = const * Real.exp (-B * R^2) := by
            simp [C, const, mul_comm, mul_left_comm, mul_assoc]
    by_cases hconst_zero : const = 0
    · refine ⟨1, by norm_num, ?_⟩
      intro R _
      have hε_pos : 0 < ε / 2 := half_pos hε
      have hnorm_zero : ‖I • ∫ t in y₁..y₂, f ((sign * R : ℂ) + t * I)‖ = 0 := by
        have hle : ‖I • ∫ t in y₁..y₂, f ((sign * R : ℂ) + t * I)‖ ≤ 0 := by
          simpa [hconst_zero] using h_integral_bound R
        exact le_antisymm hle (norm_nonneg _)
      rw [hnorm_zero]
      exact hε_pos
    · have hconst_pos : 0 < const := by
        have hA_pos : 0 < A := hA
        have hy_abs_ne : |y₂ - y₁| ≠ 0 := by
          intro hy_zero
          have : const = 0 := by simp [const, hy_zero]
          exact hconst_zero this
        have hy_abs_pos : 0 < |y₂ - y₁| := lt_of_le_of_ne' (abs_nonneg _) hy_abs_ne
        exact mul_pos hA_pos hy_abs_pos
      set δ : ℝ := ε / (2 * const) with hδ
      have hδ_pos : 0 < δ := by
        have hden_pos : 0 < 2 * const := mul_pos (show (0 : ℝ) < 2 by norm_num) hconst_pos
        simpa [δ, hδ] using div_pos hε hden_pos
      by_cases hδ_ge : 1 ≤ δ
      · refine ⟨1, by norm_num, ?_⟩
        intro R hR
        have hconst_le : const ≤ ε / 2 := by
          -- Since 1 ≤ δ = ε/(2*const), we have 2*const ≤ ε
          have hden_pos : 0 < 2 * const := mul_pos (show (0 : ℝ) < 2 by norm_num) hconst_pos
          rw [hδ] at hδ_ge
          have hconst_le' : 2 * const ≤ ε := by
            have : 1 * (2 * const) ≤ (ε / (2 * const)) * (2 * const) :=
              mul_le_mul_of_nonneg_right hδ_ge (le_of_lt hden_pos)
            rw [one_mul] at this
            rw [div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hden_pos), mul_one] at this
            exact this
          have htwo_pos : (0 : ℝ) < 2 := by norm_num
          rw [le_div_iff₀ htwo_pos]
          rw [mul_comm] at hconst_le'
          exact hconst_le'
        have hR_nonneg : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) hR
        have hR_sq_ge : 1 ≤ R^2 := by
          have htmp := mul_le_mul_of_nonneg_right hR hR_nonneg
          have : R ≤ R^2 := by
            rw [sq]
            simpa [mul_comm] using htmp
          exact le_trans hR this
        have hneg : -B ≤ 0 := neg_nonpos.mpr (le_of_lt hB)
        have h_exp_le : Real.exp (-B * R^2) ≤ Real.exp (-B) := by
          have := mul_le_mul_of_nonpos_left hR_sq_ge hneg
          simpa using Real.exp_le_exp.mpr this
        have h_exp_lt_one : Real.exp (-B) < 1 := by
          simpa [Real.exp_lt_one_iff] using (neg_lt_zero.mpr hB)
        have hprod_lt : const * Real.exp (-B * R^2) < const :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left h_exp_le (le_of_lt hconst_pos))
            (by simpa [mul_comm] using mul_lt_mul_of_pos_left h_exp_lt_one hconst_pos)
        have hnorm_le := h_integral_bound R
        have hconst_le' : const * Real.exp (-B * R^2) < ε / 2 :=
          lt_of_lt_of_le hprod_lt hconst_le
        exact lt_of_le_of_lt hnorm_le hconst_le'
      · have hδ_lt : δ < 1 := lt_of_not_ge hδ_ge
        have hlog_neg : Real.log δ < 0 := by
          have := Real.log_lt_log hδ_pos hδ_lt
          rwa [Real.log_one] at this
        set target : ℝ := (-Real.log δ + 1) / B with htarget
        have htarget_pos : 0 < target := by
          have hnum_pos : 0 < -Real.log δ + 1 :=
            add_pos_of_pos_of_nonneg (neg_pos.mpr hlog_neg) (by norm_num)
          exact div_pos hnum_pos hB
        let R₀ : ℝ := max 1 (Real.sqrt target)
        have hR₀_pos : 0 < R₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
        refine ⟨R₀, hR₀_pos, ?_⟩
        intro R hR
        have hR_ge_one : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
        have hR_nonneg : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) hR_ge_one
        have hR_ge_sqrt : Real.sqrt target ≤ R := le_trans (le_max_right _ _) hR
        have hsqrt_nonneg : 0 ≤ Real.sqrt target := Real.sqrt_nonneg _
        have h_abs_le : |Real.sqrt target| ≤ |R| := by
          simpa [abs_of_nonneg hsqrt_nonneg, abs_of_nonneg hR_nonneg] using hR_ge_sqrt
        have hsq := (sq_le_sq.2 h_abs_le)
        have htarget_nonneg : 0 ≤ target := le_of_lt htarget_pos
        have htarget_sq : target = (Real.sqrt target)^2 := by
          have := Real.mul_self_sqrt htarget_nonneg
          simpa [pow_two] using this.symm
        have htarget_le : target ≤ R^2 := by
          rw [htarget_sq]
          exact hsq
        have hmul_ge : -Real.log δ + 1 ≤ B * R^2 := by
          have hcalc : B * target = -Real.log δ + 1 := by
            have hB_ne : (B : ℝ) ≠ 0 := ne_of_gt hB
            rw [htarget, mul_comm B, div_mul_eq_mul_div, mul_div_assoc, div_self hB_ne, mul_one]
          have := mul_le_mul_of_nonneg_left htarget_le (le_of_lt hB)
          simpa [hcalc] using this
        have h_exp_le : Real.exp (-B * R^2) ≤ δ * Real.exp (-1) := by
          have hineq : -B * R^2 ≤ Real.log δ - 1 := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm] using
              (neg_le_neg hmul_ge)
          have := Real.exp_le_exp.mpr hineq
          rw [sub_eq_add_neg, Real.exp_add] at this
          rw [Real.exp_log hδ_pos] at this
          convert this using 2
        have hconst_ne : const ≠ 0 := ne_of_gt hconst_pos
        have hprod_le : const * Real.exp (-B * R^2) ≤ (ε / 2) * Real.exp (-1) := by
          have hfactor : const * δ = ε / 2 := by
            rw [hδ]
            field_simp
          calc const * Real.exp (-B * R^2)
            _ ≤ const * (δ * Real.exp (-1)) := mul_le_mul_of_nonneg_left h_exp_le hconst_nonneg
            _ = (const * δ) * Real.exp (-1) := by ring
            _ = (ε / 2) * Real.exp (-1) := by rw [hfactor]
        have hε_pos' : 0 < ε / 2 := half_pos hε
        have hlt_mul : (ε / 2) * Real.exp (-1) < ε / 2 := by
          rw [mul_comm]
          exact mul_lt_of_lt_one_left hε_pos' (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
        have hnorm_le := h_integral_bound R
        have hconst_lt : const * Real.exp (-B * R^2) < ε / 2 :=
          lt_of_le_of_lt hprod_le hlt_mul
        exact lt_of_le_of_lt hnorm_le hconst_lt

  -- Combine to show the difference vanishes
  have vert_vanish : ∀ ε > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R ≥ R₀,
    ‖I • (∫ t in y₁..y₂, f ((R : ℂ) + t * I)) - I • (∫ t in y₁..y₂, f ((-R : ℂ) + t * I))‖ < ε := by
    intro ε hε
    -- Get R₀ for both sides with ε using the general lemma
    obtain ⟨R₁, hR₁_pos, hR₁⟩ := vert_vanish_general 1 (Or.inl rfl) ε hε
    obtain ⟨R₂, hR₂_pos, hR₂⟩ := vert_vanish_general (-1) (Or.inr rfl) ε hε

    use max R₁ R₂
    constructor
    · exact lt_max_of_lt_left hR₁_pos
    · intro R hR
      -- Use triangle inequality
      calc ‖I • (∫ t in y₁..y₂, f (R + t * I)) - I • (∫ t in y₁..y₂, f (-R + t * I))‖
        = ‖I • ((∫ t in y₁..y₂, f (R + t * I)) - (∫ t in y₁..y₂, f (-R + t * I)))‖ := by
            rw [← smul_sub]
        _ = ‖(∫ t in y₁..y₂, f (R + t * I)) - (∫ t in y₁..y₂, f (-R + t * I))‖ := by
            rw [norm_smul, Complex.norm_I]
            simp only [one_mul]
        _ ≤ ‖∫ t in y₁..y₂, f (R + t * I)‖ + ‖∫ t in y₁..y₂, f (-R + t * I)‖ := norm_sub_le _ _
        _ = ‖I • ∫ t in y₁..y₂, f (R + t * I)‖ + ‖I • ∫ t in y₁..y₂, f (-R + t * I)‖ := by
            simp only [norm_smul, Complex.norm_I]
            ring
        _ < ε/2 + ε/2 := by
          apply add_lt_add
          · convert hR₁ R (le_trans (le_max_left _ _) hR) using 2
            simp [one_mul]
          · convert hR₂ R (le_trans (le_max_right _ _) hR) using 2
            simp
        _ = ε := add_halves ε

  -- Step 3: Take limit as R → ∞ using the lemma
  -- Apply contour_limit_theorem to conclude the equality
  exact contour_limit_theorem hf_integrable_y1 hf_integrable_y2 vert_vanish rect_eq

end CauchyTheorem

section RiemannLebesgue

/--
The Riemann-Lebesgue lemma: For an L¹ function f, its Fourier transform
vanishes at infinity.
-/
theorem riemann_lebesgue_lemma {f : ℝ → ℂ} (hf : Integrable f) :
    Filter.Tendsto (fun ξ : ℝ => ∫ x : ℝ, f x * Complex.exp (-2 * π * I * ↑ξ * ↑x))
    Filter.atTop (𝓝 0) := by
  sorry

/--
Special case for Gaussian times oscillating exponential.
This is useful for analyzing the Fourier transform of Gaussians.
-/
theorem gaussian_oscillating_integral {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑a^2) * Complex.exp (-2 * ↑π * I * ↑ξ * ↑a) =
    Complex.exp (-↑π * ↑δ^2 * ↑ξ^2) * ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
  sorry

end RiemannLebesgue

section ComplexIntegration

/--
Change of variables formula for complex integrals along the real line.
If φ : ℝ → ℂ is a smooth bijection preserving orientation, then
∫ f(z) dz = ∫ f(φ(t)) φ'(t) dt
-/
theorem complex_change_of_variables {f : ℂ → ℂ} {φ : ℝ → ℂ}
    (hf : ContinuousOn f (φ '' Set.univ))
    (hφ : Differentiable ℝ (fun t => (φ t).re) ∧ Differentiable ℝ (fun t => (φ t).im))
    (hφ_bij : Function.Bijective φ) :
    ∫ z : ℝ, f (z : ℂ) = ∫ t : ℝ, f (φ t) * deriv φ t := by
  sorry

/--
Integration by parts for complex functions on the real line.
-/
theorem complex_integration_by_parts {f g : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (h_decay : Filter.Tendsto (fun x => f x * g x) Filter.atTop (𝓝 0) ∧
               Filter.Tendsto (fun x => f x * g x) Filter.atBot (𝓝 0)) :
    ∫ x : ℝ, (deriv f x) * g x = - ∫ x : ℝ, f x * (deriv g x) := by
  sorry

end ComplexIntegration

end Frourio
