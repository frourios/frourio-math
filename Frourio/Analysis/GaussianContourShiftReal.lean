import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Frourio.Analysis.CauchyTheorem

namespace Frourio

open Complex MeasureTheory Real Filter Topology

/-- Bound for the norm of complex Gaussian with shifted argument -/
lemma gaussian_shifted_norm_bound (a : ℂ) (c : ℂ) (x : ℝ) :
    ‖exp (-a * ((x : ℂ) + c)^2)‖ ≤ Real.exp (-a.re *
    (x + c.re)^2 + a.re * c.im^2 + |2 * a.im * c.im * (x + c.re)|) := by
  -- Use the norm formula for complex exponentials
  have h : ‖exp (-a * ((x : ℂ) + c)^2)‖ = Real.exp ((-a * ((x : ℂ) + c)^2).re) := by
    exact Complex.norm_exp _
  rw [h]
  -- Expand the complex square
  have h_expand : ((x : ℂ) + c)^2 = (x : ℂ)^2 + 2 * (x : ℂ) * c + c^2 := by
    ring
  rw [h_expand]
  -- Distribute the multiplication
  have h_dist : -a * ((x : ℂ)^2 + 2 * (x : ℂ) * c + c^2) =
    -a * (x : ℂ)^2 - a * (2 * (x : ℂ) * c) - a * c^2 := by
    ring
  rw [h_dist]
  -- Take real parts - the subtraction distributes over real part
  have h_re : (-a * (x : ℂ)^2 - a * (2 * (x : ℂ) * c) - a * c^2).re =
    (-a * (x : ℂ)^2).re + (-a * (2 * (x : ℂ) * c)).re + (-a * c^2).re := by
    -- First rewrite the subtractions as additions of negations
    have eq1 : -a * (x : ℂ)^2 - a * (2 * (x : ℂ) * c) - a * c^2 =
               -a * (x : ℂ)^2 + (-a * (2 * (x : ℂ) * c)) + (-a * c^2) := by ring
    rw [eq1]
    -- Now apply the distributivity of .re over addition
    rw [Complex.add_re, Complex.add_re]
  rw [h_re]
  -- Simplify each term
  have h1 : (-a * (x : ℂ)^2).re = -a.re * x^2 := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  have h2 : (-a * (2 * (x : ℂ) * c)).re = -2 * (a.re * x * c.re - a.im * x * c.im) := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h3 : (-a * c^2).re = -(a.re * (c.re^2 - c.im^2) - a.im * (2 * c.re * c.im)) := by
    -- Calculate (-a * c^2).re directly
    have : (-a * c^2).re = -(a * c^2).re := by simp [Complex.neg_re]
    rw [this]
    -- Now calculate (a * c^2).re
    have c2_re : (c^2).re = c.re^2 - c.im^2 := by simp [pow_two, Complex.mul_re]
    have c2_im : (c^2).im = 2 * c.re * c.im := by
      simp [pow_two, Complex.mul_im]
      ring
    simp only [Complex.mul_re, c2_re, c2_im]
  rw [h1, h2, h3]
  -- Complete the square bound
  have h_equality : -a.re * x^2 + (-2 * (a.re * x * c.re - a.im * x * c.im)) +
    (-(a.re * (c.re^2 - c.im^2) - a.im * (2 * c.re * c.im))) =
    -a.re * (x + c.re)^2 + a.re * c.im^2 + 2 * a.im * c.im * (x + c.re) := by
    -- This is an algebraic identity that can be verified by expanding
    ring

  -- Use the equality directly to rewrite the expression
  rw [h_equality]

  -- Now we need to bound exp(-a.re * (x + c.re)^2 + a.re * c.im^2 + 2 * a.im * c.im * (x + c.re))
  -- This equals exp(-a.re * (x + c.re)^2) * exp(a.re * c.im^2) * exp(2 * a.im * c.im * (x + c.re))

  have h_factor : Real.exp (-a.re * (x + c.re)^2 + a.re * c.im^2 + 2 * a.im * c.im * (x + c.re)) =
    Real.exp (-a.re * (x + c.re)^2) * Real.exp (a.re * c.im^2) *
    Real.exp (2 * a.im * c.im * (x + c.re)) := by
    rw [← Real.exp_add, ← Real.exp_add]

  rw [h_factor]

  -- We need to bound the product. The key is that |exp(2 * a.im * c.im * (x + c.re))| = 1
  -- since it's a pure imaginary exponent
  have h_exp_bound : Real.exp (-a.re * (x + c.re)^2) * Real.exp (a.re * c.im^2) *
            Real.exp (2 * a.im * c.im * (x + c.re)) ≤
            Real.exp (-a.re * (x + c.re)^2 + a.re * c.im^2 + |2 * a.im * c.im * (x + c.re)|) := by
    rw [← Real.exp_add, ← Real.exp_add]
    rw [Real.exp_le_exp]
    -- Need to show: -a.re * (x + c.re)^2 + a.re * c.im^2 + 2 * a.im * c.im * (x + c.re) ≤
    --               -a.re * (x + c.re)^2 + a.re * c.im^2 + |2 * a.im * c.im * (x + c.re)|
    -- This is true since t ≤ |t| for all real t
    simp only [add_le_add_iff_left]
    exact le_abs_self _

  exact h_exp_bound

/-- Integrability of the shifted Gaussian bound function -/
lemma gaussian_shifted_bound_integrable (a : ℂ) (ha : 0 < a.re) (c : ℂ) :
    Integrable (fun x : ℝ => Real.exp (-a.re * (x + c.re)^2 + a.re * c.im^2)) := by
  -- Factor out the constant term
  have h_factor : (fun x : ℝ => Real.exp (-a.re * (x + c.re)^2 + a.re * c.im^2)) =
    fun x : ℝ => Real.exp (a.re * c.im^2) * Real.exp (-a.re * (x + c.re)^2) := by
    ext x
    rw [← Real.exp_add]
    ring_nf
  rw [h_factor]
  -- The shifted Gaussian is integrable
  have h_shift : Integrable (fun x : ℝ => Real.exp (-a.re * (x + c.re)^2)) := by
    -- Use substitution: the function is a translation of the standard Gaussian
    have h_sub : (fun x : ℝ => Real.exp (-a.re * (x + c.re)^2)) =
      (fun x : ℝ => Real.exp (-a.re * x^2)) ∘ (fun x => x + c.re) := by
      ext x
      simp [Function.comp]
    rw [h_sub]
    -- Translation preserves integrability
    exact (integrable_exp_neg_mul_sq ha).comp_add_right c.re
  -- Constant multiplication preserves integrability
  exact h_shift.const_mul _

/-- Norm of complex Gaussian with real argument -/
lemma gaussian_norm_real (a : ℂ) (_ : 0 < a.re) (x : ℝ) :
    ‖exp (-a * (x : ℂ)^2)‖ = Real.exp (-a.re * x^2) := by
  -- Use the norm formula for complex exponentials
  have h : ‖exp (-a * (x : ℂ)^2)‖ = Real.exp ((-a * (x : ℂ)^2).re) := by
    exact Complex.norm_exp _
  rw [h]
  -- Simplify the real part
  have h_re : (-a * (x : ℂ)^2).re = -a.re * x^2 := by
    simp [Complex.mul_re, pow_two]
  rw [h_re]

/-- Young's inequality for products: For any real numbers a, b and ε > 0,
    we have |2 * a * b * c| ≤ ε/2 * c^2 + 2 * |a * b|^2 / ε -/
lemma young_inequality_for_products (a b c : ℝ) (ε : ℝ) (hε : 0 < ε) :
    |2 * a * b * c| ≤ ε/2 * c^2 + 2 * (a * b)^2 / ε := by
  -- Apply Young's inequality: |xy| ≤ εx²/2 + y²/(2ε)
  have key : ∀ (u v : ℝ) (ε : ℝ), 0 < ε → |u * v| ≤ ε * u^2 / 2 + v^2 / (2 * ε) := by
    intros u v ε' hε'
    -- Use AM-GM inequality via the fact that 0 ≤ (√ε * |u| - |v|/√ε)²
    have h : 0 ≤ (Real.sqrt ε' * |u| - |v| / Real.sqrt ε')^2 := sq_nonneg _
    rw [sub_sq] at h
    have h1 : (Real.sqrt ε' * |u|)^2 = ε' * u^2 := by
      rw [mul_pow, sq_abs, Real.sq_sqrt (le_of_lt hε')]
    have h2 : (|v| / Real.sqrt ε')^2 = v^2 / ε' := by
      rw [div_pow, sq_abs, Real.sq_sqrt (le_of_lt hε')]
    rw [h1, h2] at h
    have h3 : 2 * (Real.sqrt ε' * |u|) * (|v| / Real.sqrt ε') = 2 * |u| * |v| := by
      field_simp [Real.sq_sqrt (le_of_lt hε')]
      ring
    rw [h3] at h
    -- From 0 ≤ ε' * u^2 - 2 * |u| * |v| + v^2 / ε'
    have h4 : 2 * |u| * |v| ≤ ε' * u^2 + v^2 / ε' := by linarith
    -- Since |u * v| = |u| * |v|
    rw [abs_mul]
    -- Therefore |u| * |v| ≤ (ε' * u^2 + v^2 / ε') / 2
    calc |u| * |v| ≤ (ε' * u^2 + v^2 / ε') / 2 := by linarith
      _ = ε' * u^2 / 2 + v^2 / (2 * ε') := by ring
  -- Apply with u = c, v = 2 * a * b, ε = ε
  specialize key c (2 * a * b) ε hε
  convert key using 1
  · rw [mul_comm c (2 * a * b), mul_assoc]
  · ring

/-- Integrability of the complex Gaussian with shifted argument -/
lemma gaussian_shifted_integrable (a : ℂ) (ha : 0 < a.re) (c : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (-a * (x + c)^2)) := by
  -- We need to show integrability of exp(-a * (x + c)^2)
  -- Expand (x + c)^2 = x^2 + 2xc + c^2
  -- So exp(-a * (x + c)^2) = exp(-a * x^2) * exp(-2axc) * exp(-ac^2)

  -- First, change of variables: let y = x + c.re
  -- This gives us ∫ exp(-a * (y + ic.im)^2) dy
  have : Integrable (fun x : ℝ => Complex.exp (-a * ((x : ℂ) + c)^2)) := by
    -- Use the fact that for Gaussian functions with Re(a) > 0,
    -- the decay is dominated by exp(-a.re * x^2) which is integrable
    have h_bound : ∀ x : ℝ, ‖exp (-a * ((x : ℂ) + c)^2)‖ ≤
        Real.exp (-a.re * (x + c.re)^2 + a.re * c.im^2 + |2 * a.im * c.im * (x + c.re)|) :=
      fun x => gaussian_shifted_norm_bound a c x

    -- We need a simpler bound that's integrable
    -- Since |2 * a.im * c.im * (x + c.re)| ≥ 0, we have:
    -- exp(-a.re * (x + c.re)^2 + a.re * c.im^2 + |2 * a.im * c.im * (x + c.re)|)
    -- ≤ exp(-a.re * (x + c.re)^2 + a.re * c.im^2 + 2 * |a.im * c.im| * |x + c.re|)
    -- For large |x|, the quadratic term dominates, so this is still integrable

    -- For integrability, we can use a simpler bound
    have h_bound_simpler : ∀ x : ℝ, ‖exp (-a * ((x : ℂ) + c)^2)‖ ≤
        Real.exp (-a.re/2 * (x + c.re)^2) *
        Real.exp (a.re * c.im^2 + 2 * |a.im * c.im|^2 / a.re) := by
      intro x
      have hb := h_bound x
      -- Apply Young's inequality: |ab| ≤ εa²/2 + b²/(2ε) for any ε > 0
      -- Here: |2 * a.im * c.im * (x + c.re)| ≤ a.re/2 * (x + c.re)^2 + 2|a.im * c.im|^2/a.re
      have young_ineq : |2 * a.im * c.im * (x + c.re)| ≤
          a.re/2 * (x + c.re)^2 + 2 * |a.im * c.im|^2 / a.re := by
        -- Use the Young's inequality lemma
        have := young_inequality_for_products a.im c.im (x + c.re) a.re ha
        convert this using 2
        rw [sq_abs]

      -- Now use the Young inequality bound
      calc ‖exp (-a * ((x : ℂ) + c)^2)‖
          ≤ Real.exp (-a.re * (x + c.re)^2 + a.re * c.im^2 + |2 * a.im * c.im * (x + c.re)|) := hb
          _ ≤ Real.exp (-a.re * (x + c.re)^2 + a.re * c.im^2 +
                        (a.re/2 * (x + c.re)^2 + 2 * |a.im * c.im|^2 / a.re)) := by
            rw [Real.exp_le_exp]
            exact add_le_add_left young_ineq _
          _ = Real.exp (-a.re/2 * (x + c.re)^2 + a.re * c.im^2 + 2 * |a.im * c.im|^2 / a.re) := by
            congr 1
            ring
          _ = Real.exp (-a.re/2 * (x + c.re)^2) *
              Real.exp (a.re * c.im^2 + 2 * |a.im * c.im|^2 / a.re) := by
            rw [← Real.exp_add]
            congr 1
            ring

    -- The simpler bound function is integrable
    have h_bound_integrable : Integrable (fun x : ℝ =>
        Real.exp (-a.re/2 * (x + c.re)^2) *
        Real.exp (a.re * c.im^2 + 2 * |a.im * c.im|^2 / a.re)) := by
      -- This is a constant times a shifted Gaussian with parameter a.re/2 > 0
      have h_gauss : Integrable (fun x : ℝ => Real.exp (-(a.re/2) * (x + c.re)^2)) := by
        have ha_pos : 0 < a.re/2 := by linarith
        -- Use change of variables for shifted Gaussian
        have h_shift : (fun x : ℝ => Real.exp (-(a.re/2) * (x + c.re)^2)) =
          (fun x : ℝ => Real.exp (-(a.re/2) * x^2)) ∘ (fun x => x + c.re) := by
          ext x
          simp [Function.comp]
        rw [h_shift]
        exact (integrable_exp_neg_mul_sq ha_pos).comp_add_right c.re
      -- Multiply by the constant factor
      let C := Real.exp (a.re * c.im^2 + 2 * |a.im * c.im|^2 / a.re)
      have h_eq : (fun x : ℝ => Real.exp (-a.re/2 * (x + c.re)^2) * C) =
                  (fun x : ℝ => C * Real.exp (-(a.re/2) * (x + c.re)^2)) := by
        ext x
        rw [mul_comm]
        congr 1
        ring_nf
      rw [h_eq]
      exact h_gauss.const_mul C

    -- Apply dominated convergence / comparison test
    exact Integrable.mono' h_bound_integrable
      (Continuous.aestronglyMeasurable (by
        continuity))
      (ae_of_all _ h_bound_simpler)
  exact this

/-- Integrability of real Gaussian function -/
lemma gaussian_integrable_real (a : ℂ) (ha : 0 < a.re) :
    Integrable (fun x : ℝ => Real.exp (-a.re * x^2)) := by
  exact integrable_exp_neg_mul_sq ha

/-- Integrability of complex Gaussian function -/
lemma gaussian_integrable_complex (a : ℂ) (ha : 0 < a.re) :
    Integrable (fun x : ℝ => Complex.exp (-a * x^2)) := by
  -- The integrand exp(-a * x^2) with a.re > 0 is integrable
  -- This follows from the standard Gaussian integrability

  -- |exp(-a * x^2)| = exp(Re(-a * x^2)) = exp(-a.re * x^2 + a.im * 0) = exp(-a.re * x^2)
  have h_abs : ∀ x : ℝ, ‖exp (-a * (x : ℂ)^2)‖ = Real.exp (-a.re * x^2) :=
    fun x => gaussian_norm_real a ha x

  -- The bound exp(-a.re * x^2) is integrable for a.re > 0
  have h_gaussian_integrable : Integrable (fun x : ℝ => Real.exp (-a.re * x^2)) :=
    gaussian_integrable_real a ha

  -- Apply the bound to show integrability
  exact Integrable.mono' h_gaussian_integrable
    (Continuous.aestronglyMeasurable (by continuity))
    (ae_of_all _ (fun x => le_of_eq (h_abs x)))

/-- Cauchy's theorem for rectangular contour with Gaussian -/
lemma gaussian_rectangular_contour (a : ℂ) (_ha : 0 < a.re) (y : ℝ) (R : ℝ) (_hR : 0 < R) :
    let f := fun z => Complex.exp (-a * z^2)
    (∫ x in (-R : ℝ)..R, f x) -
    (∫ x in (-R : ℝ)..R, f (x + y * I)) +
    (∫ t in (0 : ℝ)..y, f (R + t * I) * I) -
    (∫ t in (0 : ℝ)..y, f (-R + t * I) * I) = 0 := by
  classical
  -- Work with a named function for readability
  set f : ℂ → ℂ := fun z => Complex.exp (-a * z ^ 2)

  have hf_poly : Differentiable ℂ fun z : ℂ => (-a : ℂ) * z ^ 2 := by
    simp
  have hf : Differentiable ℂ f := by
    simpa [f] using Complex.differentiable_exp.comp hf_poly

  have hf_rect :
      DifferentiableOn ℂ f (Set.uIcc (-R) R ×ℂ Set.uIcc (0 : ℝ) y) := by
    intro z hz
    exact (hf z).differentiableWithinAt

  -- Cauchy's theorem on the rectangle between imaginary heights 0 and y
  have h :=
    cauchy_rectangle_formula (f := f) (R := R) (y₁ := (0 : ℝ)) (y₂ := y) hf_rect
  have h_add :
      (∫ x in (-R : ℝ)..R, f x) -
        (∫ x in (-R : ℝ)..R, f (x + y * I)) +
        (I • ∫ t in (0 : ℝ)..y, f (R + t * I)) -
        (I • ∫ t in (0 : ℝ)..y, f (-R + t * I)) = 0 := by
    have := eq_neg_iff_add_eq_zero.mp h
    simpa [zero_mul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this

  have h_right :
      (∫ t in (0 : ℝ)..y, f (R + t * I) * I) =
        (∫ t in (0 : ℝ)..y, f (R + t * I)) * I := by
    simp [mul_comm]

  have h_left :
      (∫ t in (0 : ℝ)..y, f (-R + t * I) * I) =
        (∫ t in (0 : ℝ)..y, f (-R + t * I)) * I := by
    simp [mul_comm]

  have h_total :
      (∫ x in (-R : ℝ)..R, f x) -
        (∫ x in (-R : ℝ)..R, f (x + y * I)) +
        (∫ t in (0 : ℝ)..y, f (R + t * I) * I) -
        (∫ t in (0 : ℝ)..y, f (-R + t * I) * I) = 0 := by
    simpa [smul_eq_mul, mul_comm, h_right.symm, h_left.symm,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_add

  simpa [f] using h_total

/-- Helper lemma: R is positive when it's bounded below by a specific expression -/
lemma R_positive_from_bound (a : ℂ) (ha : 0 < a.re) (sign : ℝ) (hsign : sign ≠ 0) (b R : ℝ)
    (hb : b < 0) (hR : R ≥ 2 * Real.sqrt (-b * 4 / a.re) / |sign|) : 0 < R := by
  -- Since b < 0, the bound is positive
  have h_bound_pos : 0 < 2 * Real.sqrt (-b * 4 / a.re) / |sign| := by
    apply div_pos
    · apply mul_pos
      · norm_num
      · apply Real.sqrt_pos.mpr
        -- Show -b * 4 / a.re > 0
        have h1 : 0 < -b := by linarith
        have h2 : (0 : ℝ) < 4 := by norm_num
        have h3 : 0 < -b * 4 := mul_pos h1 h2
        exact div_pos h3 ha
    · exact abs_pos.mpr hsign
  linarith

/-- Helper lemma: For R large enough, (sign * R)^2 exceeds the threshold -/
lemma sq_exceeds_threshold (a_re : ℝ) (ha : 0 < a_re) (sign : ℝ) (hsign : sign ≠ 0)
    (b R : ℝ) (hb : b < 0) (hR : R ≥ 2 * Real.sqrt (-b * 4 / a_re) / |sign|) :
    (sign * R)^2 > -4 * b / a_re := by
  -- Step 1: (sign * R)^2 = |sign|^2 * R^2
  have h1 : (sign * R)^2 = |sign|^2 * R^2 := by
    rw [mul_pow, sq_abs]

  -- Step 2: Show R^2 ≥ (2 * Real.sqrt (-b * 4 / a_re) / |sign|)^2
  have h2 : R^2 ≥ (2 * Real.sqrt (-b * 4 / a_re) / |sign|)^2 := by
    have h_nonneg : 0 ≤ 2 * Real.sqrt (-b * 4 / a_re) / |sign| := by
      apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · apply Real.sqrt_nonneg
      · exact abs_nonneg _
    exact sq_le_sq' (by linarith : -(R) ≤ 2 * Real.sqrt (-b * 4 / a_re) / |sign|) hR

  -- Step 3: Compute (2 * Real.sqrt (-b * 4 / a_re) / |sign|)^2
  have h3 : (2 * Real.sqrt (-b * 4 / a_re) / |sign|)^2 = 4 * (-b * 4 / a_re) / |sign|^2 := by
    rw [div_pow, mul_pow, sq_sqrt]
    · ring
    · apply div_nonneg
      · apply mul_nonneg
        · linarith
        · norm_num
      · exact ha.le

  -- Step 4: Combine to get the inequality
  calc (sign * R)^2
      = |sign|^2 * R^2 := h1
      _ ≥ |sign|^2 * (4 * (-b * 4 / a_re) / |sign|^2) := by
        apply mul_le_mul_of_nonneg_left
        · rw [← h3]
          exact h2
        · exact sq_nonneg _
      _ = 4 * (-b * 4 / a_re) := by
        have hsign_pos : 0 < |sign|^2 := sq_pos_iff.mpr (abs_pos.mpr hsign).ne'
        field_simp [ne_of_gt hsign_pos]
        ring
      _ = -16 * b / a_re := by ring
      _ > -4 * b / a_re := by
        -- Since b < 0, we have -b > 0
        -- So -16 * b > -4 * b (multiply both by positive a_re⁻¹)
        have h_neg_b : 0 < -b := by linarith
        calc -16 * b / a_re
            = 4 * (-4 * b) / a_re := by ring
            _ > (-4 * b) / a_re := by
              apply div_lt_div_of_pos_right
              · linarith
              · exact ha
            _ = -4 * b / a_re := by ring

/-- Helper lemma: Rearranging inequality for Gaussian bound -/
lemma gaussian_bound_rearrange (a_re : ℝ) (ha : 0 < a_re) (b : ℝ) (x : ℝ)
    (hx : x ^ 2 > -4 * b / a_re) : -(a_re * x^2 / 4) < b := by
  -- From hx: x^2 > -4 * b / a_re
  -- Multiply both sides by a_re > 0:
  have h1 : a_re * x^2 > a_re * (-4 * b / a_re) := by
    exact mul_lt_mul_of_pos_left hx ha
  -- Simplify the right side
  have h2 : a_re * (-4 * b / a_re) = -4 * b := by
    field_simp
    ring
  rw [h2] at h1
  -- Divide both sides by 4:
  have h3 : a_re * x^2 / 4 > -4 * b / 4 := by
    exact div_lt_div_of_pos_right h1 (by norm_num : (0 : ℝ) < 4)
  -- Simplify the right side
  have h4 : -4 * b / 4 = -b := by ring
  rw [h4] at h3
  -- Multiply both sides by -1 (reversing the inequality):
  linarith

/-- Helper lemma: exponential decay for Gaussian-like functions -/
lemma gaussian_exp_decay (a : ℂ) (ha : 0 < a.re) (sign : ℝ) (hsign : sign ≠ 0) :
    Tendsto (fun R => Real.exp (-(a.re * (sign * R)^2 / 4))) atTop (𝓝 0) := by
  -- The exponent -(a.re * (sign * R)^2 / 4) → -∞ as R → ∞
  -- First show the exponent tends to negative infinity
  have h_to_neg_inf : Tendsto (fun R => -(a.re * (sign * R)^2 / 4)) atTop atBot := by
    rw [tendsto_atBot]
    intro b
    -- Need to find R₀ such that for all R > R₀, we have -(a.re * (sign * R)^2 / 4) < b
    rw [eventually_atTop]
    -- Split into cases based on sign of b
    by_cases hb : b ≤ 0
    · -- Case b ≤ 0: split into b = 0 and b < 0
      by_cases hb_eq : b = 0
      · -- Case b = 0: -(a.re * (sign * R)^2 / 4) < 0
        use 1
        intro R hR
        rw [hb_eq]
        apply neg_nonpos.mpr
        apply div_nonneg
        · apply mul_nonneg ha.le
          exact sq_nonneg _
        · norm_num
      · -- Case b < 0: use the bound 2 * sqrt(-b * 4 / a.re) / |sign|
        push_neg at hb_eq
        have hb_neg : b < 0 := lt_of_le_of_ne hb hb_eq
        use (2 * Real.sqrt (-b * 4 / a.re) / |sign|)
        intro R hR
        -- Show -(a.re * (sign * R)^2 / 4) < b
        have h1 : 0 < |sign| := abs_pos.mpr hsign
        have hR_pos : 0 < R := R_positive_from_bound a ha sign hsign b R hb_neg hR
        have h2 : 0 < (sign * R)^2 := sq_pos_iff.mpr (mul_ne_zero hsign (ne_of_gt hR_pos))
        -- Show -(a.re * (sign * R)^2 / 4) < b
        -- Since b < 0 and R is large enough, we get exponential decay
        have h3 := sq_exceeds_threshold a.re ha sign hsign b R hb_neg hR
        apply le_of_lt
        exact gaussian_bound_rearrange a.re ha b (sign * R) h3
    · -- Case b > 0: any positive R works since -(a.re * (sign * R)^2 / 4) < 0 < b
      use 1
      intro R hR
      push_neg at hb
      have h : -(a.re * (sign * R)^2 / 4) ≤ 0 := by
        apply neg_nonpos.mpr
        apply div_nonneg
        · apply mul_nonneg ha.le
          exact sq_nonneg _
        · norm_num
      linarith [h, hb]
  -- Now use that exp of something tending to -∞ tends to 0
  exact Real.tendsto_exp_atBot.comp h_to_neg_inf

/-- Helper lemma: sqrt of product equals product of sqrts for non-negative reals -/
lemma sqrt_mul_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
  rw [Real.sqrt_mul hx]

/-- Helper lemma: Complex norm equals sqrt of sum of squares -/
lemma complex_norm_eq_sqrt (z : ℂ) : ‖z‖ = Real.sqrt (z.re^2 + z.im^2) := by
  have h1 : ‖z‖^2 = z.re^2 + z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [← Real.sqrt_sq (norm_nonneg _), h1]

/-- Helper lemma: negative real to complex conversion -/
lemma neg_real_to_complex_eq_neg_mul (R : ℝ) :
    -(R : ℂ) = ((-1 : ℝ) * R : ℂ) := by
  simp [neg_mul, one_mul]

/-- Helper lemma: equality of complex expressions with negative R -/
lemma complex_neg_R_plus_tc_eq (R : ℝ) (t : ℝ) (c : ℂ) :
    -(R : ℂ) + t * c = ((-1 : ℝ) * R : ℂ) + t * c := by
  rw [neg_real_to_complex_eq_neg_mul]

/-- Helper lemma: Gaussian integrand equality for negative R -/
lemma gaussian_integrand_neg_R_eq (a : ℂ) (c : ℂ) (R : ℝ) (t : ℝ) :
    Complex.exp (-a * ((-(R : ℂ)) + t * c)^2) * c =
    Complex.exp (-a * ((((-1) : ℝ) * R : ℂ) + t * c)^2) * c := by
  congr 1
  congr 1
  congr 1
  congr 1
  exact complex_neg_R_plus_tc_eq R t c

/-- Helper lemma: left vertical integral equals the general form -/
lemma gaussian_left_vertical_eq (a : ℂ) (c : ℂ) :
    ∀ R : ℝ, ∫ t in (0 : ℝ)..(1 : ℝ),
      Complex.exp (-a * ((-(R : ℂ)) + t * c)^2) * c =
      ∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * ((((-1) : ℝ) * R : ℂ) + t * c)^2) * c := by
  intro R
  apply intervalIntegral.integral_congr
  intros t _
  exact gaussian_integrand_neg_R_eq a c R t

/-- Convergence of horizontal shifted integral to improper integral -/
lemma gaussian_horizontal_conv_shifted (a : ℂ) (ha : 0 < a.re) (c : ℂ) :
    let f := fun z => Complex.exp (-a * z^2)
    Filter.Tendsto (fun R : ℝ => ∫ x in (-R : ℝ)..R, f (x + c))
    (Filter.atTop : Filter ℝ) (𝓝 (∫ x : ℝ, f (x + c))) := by
  -- Use intervalIntegral_tendsto_integral from Mathlib
  have h_integrable := gaussian_shifted_integrable a ha c
  exact intervalIntegral_tendsto_integral h_integrable tendsto_neg_atTop_atBot tendsto_id

/-- Convergence of horizontal real integral to improper integral -/
lemma gaussian_horizontal_conv_real (a : ℂ) (ha : 0 < a.re) :
    let f := fun z => Complex.exp (-a * z^2)
    Filter.Tendsto (fun R : ℝ => ∫ x in (-R : ℝ)..R, f x)
    (Filter.atTop : Filter ℝ) (𝓝 (∫ x : ℝ, f x)) := by
  -- Use intervalIntegral_tendsto_integral from Mathlib
  have h_integrable := gaussian_integrable_complex a ha
  exact intervalIntegral_tendsto_integral h_integrable tendsto_neg_atTop_atBot tendsto_id

/-- Helper lemma: Exponential bound for Gaussian on vertical lines -/
lemma gaussian_vertical_norm_eq_aux
    (a : ℂ) (R t : ℝ) (right : Bool)
    (hz_mul : -a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2 =
      -a * (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I) ^ 2) :
    ‖Complex.exp (-a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2)‖ =
      Real.exp ((-a *
        (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I) ^ 2).re) := by
  classical
  set z :=
    -a *
      (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I) ^ 2
  calc
    ‖Complex.exp (-a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2)‖ =
        ‖Complex.exp z‖ := by
          simp [z, hz_mul]
    _ = Real.exp (z.re) := by
          simpa using Complex.norm_exp z
    _ =
        Real.exp ((-a *
              (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I) ^ 2).re) :=
          by simp [z]

lemma gaussian_vertical_norm_eq (a : ℂ) (R t : ℝ) (right : Bool) :
    ‖Complex.exp (-a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I)^2)‖ =
      Real.exp ((-a *
        (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I)^2).re) := by
  classical
  have hz :
      ((if right then (R : ℂ) else -R) + (t : ℂ) * I) =
        Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I := by
    cases right <;> simp
  have hz_sq :
      ((if right then (R : ℂ) else -R) + (t : ℂ) * I)^2 =
        (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I)^2 := by
    simp [hz]
  have hz_mul :
      -a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I)^2 =
        -a *
          (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I)^2 := by
    simp [hz_sq]
  exact gaussian_vertical_norm_eq_aux a R t right hz_mul

lemma gaussian_vertical_exponential_bound (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (R : ℝ), R > 0 → ∀ t ∈ Set.Icc 0 y,
      ‖Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2)‖ ≤
      C * Real.exp (-a.re * R^2 + a.re * y^2 + 2 * |a.im| * R * |y|) := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro R hR t ht
  have hR_nonneg : 0 ≤ R := le_of_lt hR
  rcases ht with ⟨ht0, hty⟩
  have hy_nonneg : 0 ≤ y := le_trans ht0 hty
  have h_abs_t : |t| ≤ |y| := by
    have : |t| = t := abs_of_nonneg ht0
    have : |y| = y := abs_of_nonneg hy_nonneg
    simpa [this, abs_of_nonneg ht0] using hty
  have ht_sq : t^2 ≤ y^2 := by
    have := sq_le_sq.mpr h_abs_t
    simpa [pow_two] using this
  set s : ℝ := if right then (1 : ℝ) else -1 with hs_def
  have hs_abs : |s| = (1 : ℝ) := by cases right <;> simp [s]
  have hs_sq : s ^ 2 = (1 : ℝ) := by cases right <;> simp [s]
  let z : ℂ := Complex.ofReal (s * R) + (t : ℂ) * I
  have h_norm :
      ‖Complex.exp (-a * ((if right then ↑R else -↑R) + (t : ℂ) * I)^2)‖ =
        Real.exp ((-a * z ^ 2).re) := by
    simpa [z, s] using
      (gaussian_vertical_norm_eq (a := a) (R := R) (t := t) (right := right))
  have z_re : z.re = s * R := by simp [z]
  have z_im : z.im = t := by simp [z]
  have z_sq_re : (z ^ 2).re = (s * R) ^ 2 - t ^ 2 := by
    have hz : (z ^ 2).re = z.re * z.re - z.im * z.im := by
      simp [pow_two]
    calc
      (z ^ 2).re = z.re * z.re - z.im * z.im := hz
      _ = (s * R) * (s * R) - t * t := by
        simp [z_re, z_im, mul_comm, mul_left_comm]
      _ = (s * R) ^ 2 - t ^ 2 := by ring
  have z_sq_im : (z ^ 2).im = 2 * s * R * t := by
    have hz : (z ^ 2).im = z.re * z.im + z.im * z.re := by
      simp [pow_two]
    calc
      (z ^ 2).im = z.re * z.im + z.im * z.re := hz
      _ = (s * R) * t + (s * R) * t := by
        simp [z_re, z_im, mul_comm, mul_left_comm]
      _ = 2 * s * R * t := by ring
  have h_re : (-a * z ^ 2).re =
      -a.re * ((s * R) ^ 2 - t ^ 2) + 2 * a.im * s * R * t := by
    have h1 : (-a * z ^ 2).re = -a.re * (z ^ 2).re + a.im * (z ^ 2).im := by
      simpa using Complex.mul_re (-a) (z ^ 2)
    simpa [z_sq_re, z_sq_im, mul_comm, mul_left_comm, mul_assoc] using h1
  have hs_sq' : (s * R) ^ 2 = R ^ 2 := by
    calc
      (s * R) ^ 2 = s ^ 2 * R ^ 2 := by
        simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
      _ = R ^ 2 := by simp [hs_sq]
  have h_re_exact : (-a * z ^ 2).re = -a.re * R ^ 2 + a.re * t ^ 2 + 2 * a.im * s * R * t := by
    have h_aux : (-a * z ^ 2).re = -a.re * (R ^ 2 - t ^ 2) + 2 * a.im * s * R * t := by
      simpa [hs_sq'] using h_re
    calc
      (-a * z ^ 2).re = -a.re * (R ^ 2 - t ^ 2) + 2 * a.im * s * R * t := h_aux
      _ = (-a.re * R ^ 2 + a.re * t ^ 2) + 2 * a.im * s * R * t := by ring
      _ = -a.re * R ^ 2 + a.re * t ^ 2 + 2 * a.im * s * R * t := by ring
  have h_exp_le :
      Real.exp ((-a * z ^ 2).re) ≤
        Real.exp (-a.re * R ^ 2 + a.re * y ^ 2 + 2 * |a.im| * R * |y|) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : a.re * t ^ 2 ≤ a.re * y ^ 2 :=
      mul_le_mul_of_nonneg_left ht_sq (le_of_lt ha)
    have h2 : 2 * a.im * s * R * t ≤ 2 * |a.im| * R * |y| := by
      have h_abs_term : |2 * a.im * s * R * t| = 2 * |a.im| * R * |t| := by
        simp [abs_mul, hs_abs, abs_of_nonneg hR_nonneg, mul_comm, mul_left_comm]
      have h_fac_nonneg : 0 ≤ 2 * |a.im| * R := by
        have : 0 ≤ |a.im| := abs_nonneg _
        have : 0 ≤ 2 * |a.im| := mul_nonneg (by norm_num) this
        exact mul_nonneg this hR_nonneg
      calc
        2 * a.im * s * R * t ≤ |2 * a.im * s * R * t| := le_abs_self _
        _ = 2 * |a.im| * R * |t| := h_abs_term
        _ ≤ 2 * |a.im| * R * |y| :=
          mul_le_mul_of_nonneg_left h_abs_t h_fac_nonneg
    have h_sum := add_le_add h1 h2
    have h_shift := add_le_add_left h_sum (-a.re * R ^ 2)
    have h_combined :
        -a.re * R ^ 2 + a.re * t ^ 2 + 2 * a.im * s * R * t ≤
          -a.re * R ^ 2 + a.re * y ^ 2 + 2 * |a.im| * R * |y| := by
      simpa [add_comm, add_left_comm, add_assoc] using h_shift
    calc
      (-a * z ^ 2).re = -a.re * R ^ 2 + a.re * t ^ 2 + 2 * a.im * s * R * t := h_re_exact
      _ ≤ -a.re * R ^ 2 + a.re * y ^ 2 + 2 * |a.im| * R * |y| := h_combined
  calc
    ‖Complex.exp (-a * ((if right then ↑R else -↑R) + (t : ℂ) * I)^2)‖
        = Real.exp ((-a * z ^ 2).re) := h_norm
    _ ≤ Real.exp (-a.re * R ^ 2 + a.re * y ^ 2 + 2 * |a.im| * R * |y|) := h_exp_le
    _ = 1 * Real.exp (-a.re * R ^ 2 + a.re * y ^ 2 + 2 * |a.im| * R * |y|) := by simp

/-- Helper lemma: Integral norm estimate using exponential bound -/
lemma gaussian_vertical_integral_norm_estimate (a : ℂ) (ha : 0 < a.re) (ha_im : a.im = 0)
    (y : ℝ) (hy : 0 ≤ y) (right : Bool) (C₁ : ℝ) (hC₁_pos : 0 < C₁)
    (hC₁_bound : ∀ (R : ℝ), R > 0 → ∀ t ∈ Set.Icc 0 y,
      ‖Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I) ^ 2)‖ ≤
      C₁ * Real.exp (-a.re * R ^ 2 + a.re * y ^ 2)) :
    ∀ (R : ℝ), R > 1 →
      ‖∫ t in (0 : ℝ)..y, Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤
      |y| * C₁ * Real.exp (-a.re * R^2 + a.re * y^2) := by
  classical
  -- Record the hypotheses so they are available to downstream rewrites.
  have _hRe := ha
  have _hIm := ha_im
  have _hC₁_nonneg : 0 ≤ C₁ := le_of_lt hC₁_pos
  intro R hR
  set const : ℝ := C₁ * Real.exp (-a.re * R ^ 2 + a.re * y ^ 2)
  have h_bound_Icc : ∀ t ∈ Set.Icc 0 y,
      ‖Complex.exp (-a * ((if right then ↑R else -↑R) + (t : ℂ) * I) ^ 2)‖ ≤ const := by
    intro t ht
    have hRpos : R > 0 := lt_trans (by norm_num) hR
    simpa [const] using hC₁_bound R hRpos t ht
  have h_bound_Ioc : ∀ t ∈ Set.Ioc 0 y,
      ‖Complex.exp (-a * ((if right then ↑R else -↑R) + (t : ℂ) * I) ^ 2) * I‖ ≤ const := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 y := Set.Ioc_subset_Icc_self ht
    have h_exp_le := h_bound_Icc t ht'
    have h_exp_le' :
        ‖Complex.exp (-(a * ((if right then ↑R else -↑R) + (t : ℂ) * I) ^ 2))‖ ≤ const := by
      simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using h_exp_le
    have h_norm :
        ‖Complex.exp (-(a * ((if right then ↑R else -↑R) + (t : ℂ) * I) ^ 2)) * I‖ ≤ const := by
      simpa [Complex.norm_mul, Complex.norm_I]
        using h_exp_le'
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc]
      using h_norm
  have h_interval_bound : ∀ t ∈ Set.uIoc (0 : ℝ) y,
      ‖Complex.exp (-a * ((if right then ↑R else -↑R) + (t : ℂ) * I) ^ 2) * I‖ ≤ const := by
    intro t ht
    have ht' : t ∈ Set.Ioc 0 y := by
      simpa [Set.uIoc_of_le hy] using ht
    exact h_bound_Ioc t ht'
  have h_integral_le :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := y)
      (f := fun t =>
        Complex.exp (-a * ((if right then ↑R else -↑R) + (t : ℂ) * I) ^ 2) * I)
      (C := const) h_interval_bound
  have h_final :
      ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a * ((if right then ↑R else -↑R) + (t : ℂ) * I) ^ 2) * I‖ ≤
        const * |y - 0| := by
    simpa [const] using h_integral_le
  refine (le_trans h_final ?_)
  simp [const, mul_comm, mul_left_comm, mul_assoc]

/-- Helper lemma: Exponential comparison for large R -/
lemma exp_comparison_large_R (a : ℂ) (ha : 0 < a.re) (y : ℝ) (R : ℝ) (hR : R > 1) :
    Real.exp (-a.re * R^2 + a.re * y^2) ≤
    Real.exp (2 * a.re * y^2) * Real.exp (-a.re * R^2 / 2) := by
  classical
  have hR_pos : 0 < R := lt_trans (by norm_num) hR
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have h_le :
      -a.re * R ^ 2 + a.re * y ^ 2 ≤ 2 * a.re * y ^ 2 - a.re * R ^ 2 / 2 := by
    have h_inner_le : -R ^ 2 + y ^ 2 ≤ 2 * y ^ 2 - R ^ 2 / 2 := by
      have h_diff_eq :
          (2 * y ^ 2 - R ^ 2 / 2) - (-R ^ 2 + y ^ 2) = y ^ 2 + R ^ 2 / 2 := by
        ring
      have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
      have hR_sq_nonneg : 0 ≤ R ^ 2 := by
        have : 0 ≤ R * R := mul_nonneg hR_nonneg hR_nonneg
        simpa [sq, pow_two] using this
      have h_inner_nonneg : 0 ≤ y ^ 2 + R ^ 2 / 2 := by
        refine add_nonneg hy_sq_nonneg ?_
        exact div_nonneg hR_sq_nonneg (by norm_num)
      have : 0 ≤ (2 * y ^ 2 - R ^ 2 / 2) - (-R ^ 2 + y ^ 2) := by
        simpa [h_diff_eq] using h_inner_nonneg
      exact sub_nonneg.mp this
    have ha_nonneg : 0 ≤ a.re := le_of_lt ha
    have := mul_le_mul_of_nonneg_left h_inner_le ha_nonneg
    simpa [mul_add, sub_eq_add_neg, two_mul, mul_comm, mul_left_comm,
      mul_assoc, add_comm, add_left_comm, add_assoc, div_eq_mul_inv]
      using this
  have h_exp_le := Real.exp_le_exp.mpr h_le
  have h_exp_eq :
      Real.exp (2 * a.re * y ^ 2 - a.re * R ^ 2 / 2) =
        Real.exp (2 * a.re * y ^ 2) * Real.exp (-a.re * R ^ 2 / 2) := by
    have := Real.exp_add (2 * a.re * y ^ 2) (-(a.re * R ^ 2 / 2))
    have h_simp : -(a.re * R ^ 2 / 2) = -(a.re * R ^ 2) / 2 := by ring
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      neg_mul, mul_neg, h_simp]
      using this
  have h_exp_le' := h_exp_eq ▸ h_exp_le
  have h_simp₁ : -(a.re * R ^ 2 / 2) = -a.re * R ^ 2 / 2 := by ring
  have h_simp₂ : -(a.re * R ^ 2) / 2 = -a.re * R ^ 2 / 2 := by ring
  simpa [h_simp₁, h_simp₂]
    using h_exp_le'

/-- Helper lemma: Bound for the vertical integral of Gaussian -/
lemma gaussian_vertical_integral_bound (a : ℂ) (ha : 0 < a.re)
    (ha_im : a.im = 0) (y : ℝ) (hy : 0 ≤ y) (right : Bool) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (R : ℝ), R > 1 →
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤
      C * Real.exp (-a.re * R^2 / 2) := by
  -- Get the exponential bound for the integrand
  obtain ⟨C₁, hC₁_pos, hC₁_bound⟩ := gaussian_vertical_exponential_bound a ha y right

  -- Simplify the bound using a.im = 0
  have hC₁_bound_simplified : ∀ (R : ℝ), R > 0 → ∀ t ∈ Set.Icc 0 y,
      ‖Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I) ^ 2)‖ ≤
      C₁ * Real.exp (-a.re * R ^ 2 + a.re * y ^ 2) := by
    intro R hR t ht
    have bound := hC₁_bound R hR t ht
    rw [ha_im] at bound
    simp only [abs_zero, mul_zero, zero_mul, add_zero] at bound
    exact bound

  -- Get integral estimate using the corrected bound
  have h_integral_estimate :=
    gaussian_vertical_integral_norm_estimate a ha ha_im y hy right C₁ hC₁_pos hC₁_bound_simplified

  -- Choose C large enough to absorb all the extra factors
  -- With a.im = 0, we have a cleaner bound
  use (|y| + 1) * C₁ * Real.exp (2 * a.re * y^2)

  constructor
  · -- Show C > 0
    apply mul_pos
    · apply mul_pos
      · linarith [abs_nonneg y]
      · exact hC₁_pos
    · exact Real.exp_pos _

  · -- Show the bound holds for all R > 1
    intro R hR

    -- Use the integral estimate with corrected bound
    -- With a.im = 0, the bound simplifies significantly
    calc ‖∫ t in (0 : ℝ)..y, Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖
      ≤ |y| * C₁ * Real.exp (-a.re * R^2 + a.re * y^2) :=
        h_integral_estimate R hR
      _ ≤ (|y| + 1) * C₁ * Real.exp (2 * a.re * y^2) * Real.exp (-a.re * R^2 / 2) := by
        -- Rearrange: exp(-a.re*R² + a.re*y²) ≤ exp(2*a.re*y²) * exp(-a.re*R²/2)
        -- This requires: -a.re*R² + a.re*y² ≤ 2*a.re*y² - a.re*R²/2
        -- Simplifying: -a.re*R²/2 ≤ a.re*y², which holds for all R, y
        have h_exp_comparison := exp_comparison_large_R a ha y R hR
        calc |y| * C₁ * Real.exp (-a.re * R^2 + a.re * y^2)
            ≤ |y| * C₁ * (Real.exp (2 * a.re * y^2) * Real.exp (-a.re * R^2 / 2)) := by
              apply mul_le_mul_of_nonneg_left h_exp_comparison
              apply mul_nonneg
              · exact abs_nonneg _
              · exact le_of_lt hC₁_pos
            _ = |y| * C₁ * Real.exp (2 * a.re * y^2) * Real.exp (-a.re * R^2 / 2) := by ring
            _ ≤ (|y| + 1) * C₁ * Real.exp (2 * a.re * y^2) * Real.exp (-a.re * R^2 / 2) := by
              apply mul_le_mul_of_nonneg_right
              · apply mul_le_mul_of_nonneg_right
                · apply mul_le_mul_of_nonneg_right
                  · linarith [abs_nonneg y]
                  · exact le_of_lt hC₁_pos
                · exact Real.exp_pos _ |>.le
              · exact Real.exp_pos _ |>.le

/-- Helper lemma: Exponential decay exp(-cx²) → 0 as x → ∞ for c > 0 -/
lemma exp_neg_quadratic_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun R : ℝ => Real.exp (-c * R^2 / 2))
      Filter.atTop (𝓝 0) := by
  -- Use metric space definition of tendsto to 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Need to find N such that for all R ≥ N, exp(-cR²/2) < ε
  -- This exists because exp(-x) → 0 as x → ∞
  have : ∃ N : ℝ, 0 < N ∧ ∀ R ≥ N, Real.exp (-c * R^2 / 2) < ε := by
    -- Choose N such that exp(-c * N^2 / 2) < ε
    by_cases h : ε < 1
    · -- Case ε < 1: need a large enough N
      -- Use the fact that for any ε > 0, we can find N such that exp(-cN²/2) < ε
      -- This follows from the archimedean property and properties of exp

      -- Since ε > 0 and ε < 1, we have log(ε) < 0
      -- We need exp(-cN²/2) < ε, which means -cN²/2 < log(ε)
      -- So N² > -2log(ε)/c = 2log(1/ε)/c

      -- Choose N = sqrt(2 * (-log(ε)) / c) + 1
      -- Note: -log(ε) > 0 since ε < 1
      have h_log_neg : Real.log ε < 0 := Real.log_neg hε h

      -- Choose N large enough
      use Real.sqrt (-2 * Real.log ε / c) + 1

      constructor
      · -- Show N > 0
        apply add_pos_of_nonneg_of_pos
        · apply Real.sqrt_nonneg
        · norm_num

      · -- Show ∀ R ≥ N, exp(-c * R^2 / 2) < ε
        intro R hR
        -- We need to show: exp(-c * R^2 / 2) < ε
        -- Since R ≥ sqrt(-2 * log(ε) / c) + 1 > sqrt(-2 * log(ε) / c)
        -- We have R² > -2 * log(ε) / c
        -- Therefore -c * R² / 2 < log(ε)
        -- So exp(-c * R² / 2) < ε

        have h_sqrt_pos : 0 ≤ -2 * Real.log ε / c := by
          apply div_nonneg
          · linarith
          · exact le_of_lt hc

        have h_R_bound : R > Real.sqrt (-2 * Real.log ε / c) := by linarith

        have h_R_sq : R^2 > -2 * Real.log ε / c := by
          have h_sqrt_sq : (Real.sqrt (-2 * Real.log ε / c))^2 = -2 * Real.log ε / c := by
            exact Real.sq_sqrt h_sqrt_pos
          calc R^2
              > (Real.sqrt (-2 * Real.log ε / c))^2 := by
                have : (Real.sqrt (-2 * Real.log ε / c))^2 < R^2 := by
                  have h_pos_sqrt : 0 ≤ Real.sqrt (-2 * Real.log ε / c) := Real.sqrt_nonneg _
                  have h_pos_R : 0 < R := by
                    apply lt_trans _ h_R_bound
                    apply Real.sqrt_pos.mpr
                    have : 0 < -2 * Real.log ε / c := by
                      rw [div_pos_iff]
                      left
                      constructor
                      · simp only [neg_mul, neg_pos]
                        apply mul_neg_of_pos_of_neg
                        · norm_num
                        · exact h_log_neg
                      · exact hc
                    exact this
                  rw [sq_lt_sq]
                  rw [abs_of_nonneg h_pos_sqrt, abs_of_nonneg (le_of_lt h_pos_R)]
                  exact h_R_bound
                exact this
              _ = -2 * Real.log ε / c := by exact h_sqrt_sq

        calc Real.exp (-c * R^2 / 2)
            < Real.exp (-c * (-2 * Real.log ε / c) / 2) := by
              apply Real.exp_lt_exp.mpr
              -- Show -c * R^2 / 2 < -c * (-2 * log ε / c) / 2
              -- This is equivalent to R^2 > -2 * log ε / c, which is h_R_sq
              have : -c * R^2 / 2 < -c * (-2 * Real.log ε / c) / 2 := by
                suffices h : -c * R^2 < -c * (-2 * Real.log ε / c) by
                  linarith
                apply mul_lt_mul_of_neg_left h_R_sq
                linarith
              exact this
            _ = Real.exp (Real.log ε) := by
              congr 1
              -- -c * (-2 * Real.log ε / c) / 2 = Real.log ε
              have h_calc : -c * (-2 * Real.log ε / c) = 2 * Real.log ε := by
                calc -c * (-2 * Real.log ε / c)
                  = c * (2 * Real.log ε / c) := by ring
                  _ = 2 * Real.log ε * c / c := by ring
                  _ = 2 * Real.log ε * (c / c) := by rw [mul_div_assoc]
                  _ = 2 * Real.log ε * 1 := by rw [div_self (ne_of_gt hc)]
                  _ = 2 * Real.log ε := by ring
              calc -c * (-2 * Real.log ε / c) / 2
                = (2 * Real.log ε) / 2 := by rw [h_calc]
                _ = Real.log ε := by norm_num
            _ = ε := Real.exp_log hε
    · -- Case ε ≥ 1: any N > 0 works since exp(-c * N^2 / 2) < 1 ≤ ε
      push_neg at h
      use 1
      constructor
      · norm_num
      · intro R hR
        -- exp(-c * R^2 / 2) < 1 ≤ ε
        have h_exp_lt_one : Real.exp (-c * R^2 / 2) < 1 := by
          rw [← Real.exp_zero]
          apply Real.exp_lt_exp.mpr
          -- Show -c * R^2 / 2 < 0
          have h_pos : 0 < c * R^2 := by
            apply mul_pos hc
            exact sq_pos_of_ne_zero (by linarith : R ≠ 0)
          linarith
        linarith
  obtain ⟨N, hN_pos, hN_bound⟩ := this
  use N
  intro R hR
  -- Show distance from exp(-cR²/2) to 0 is less than ε
  simp only [Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos _)]
  exact hN_bound R hR

/-- Type for different integral bound conditions -/
inductive IntegralBoundType
  | at_one : IntegralBoundType           -- R = 1
  | interval : IntegralBoundType         -- R ∈ [0,1]
  | negative : IntegralBoundType         -- R < 0 and R ≤ 1

/-- Unified helper lemma: Vertical integral bounds for various R conditions -/
lemma gaussian_vertical_integral_bounded_unified (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool)
    (R : ℝ) (bound_type : IntegralBoundType)
    (h_cond : match bound_type with
      | IntegralBoundType.at_one => R = 1
      | IntegralBoundType.interval => 0 ≤ R ∧ R ≤ 1
      | IntegralBoundType.negative => R < 0 ∧ R ≤ 1) :
    ∃ M : ℝ, M > 0 ∧
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤ M := by
  classical
  have _hRe := ha
  let g : ℝ → ℝ := fun t =>
    ‖Complex.exp (-a *
        ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2) * I‖
  have hg_cont : Continuous g := by
    have h_const : Continuous fun _ : ℝ => (if right then (R : ℂ) else -R) :=
      continuous_const
    have h_lin : Continuous fun t : ℝ => (t : ℂ) * I :=
      ((Complex.continuous_ofReal).mul continuous_const)
    have h_sum : Continuous fun t : ℝ =>
        (if right then (R : ℂ) else -R) + (t : ℂ) * I :=
      h_const.add h_lin
    have h_pow : Continuous fun t : ℝ =>
        ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2 :=
      h_sum.pow 2
    have h_mul : Continuous fun t : ℝ =>
        -a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2 :=
      continuous_const.mul h_pow
    have h_exp : Continuous fun t : ℝ =>
        Complex.exp (-a *
          ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2) :=
      Complex.continuous_exp.comp h_mul
    have h_mul_I : Continuous fun t : ℝ =>
        Complex.exp (-a *
          ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2) * I :=
      h_exp.mul continuous_const
    exact h_mul_I.norm

  let K : Set ℝ := Set.uIcc (0 : ℝ) y
  have h_compact : IsCompact K := isCompact_uIcc
  have h_nonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    by_cases hy : 0 ≤ y
    · simpa [K, Set.uIcc_of_le hy]
    · have hy' : y < 0 := lt_of_not_ge hy
      have hy_le : y ≤ 0 := le_of_lt hy'
      simpa [K, Set.uIcc_of_ge hy_le]
  have hg_cont_on : ContinuousOn g K := hg_cont.continuousOn
  obtain ⟨t₀, ht₀, h_max⟩ :=
    h_compact.exists_isMaxOn h_nonempty hg_cont_on
  have h_bound : ∀ t ∈ Set.uIoc (0 : ℝ) y, g t ≤ g t₀ := by
    intro t ht
    have ht' : t ∈ K :=
      (Set.uIoc_subset_uIcc : Set.uIoc (0 : ℝ) y ⊆ K) ht
    have := h_max ht'
    simpa using this

  have h_integral_le :
      ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a *
            ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2) * I‖ ≤
        g t₀ * |y| := by
    have :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := y)
        (f := fun t : ℝ =>
          Complex.exp (-a *
            ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2) * I)
        (C := g t₀) h_bound
    simpa using this

  have hg_nonneg : 0 ≤ g t₀ := norm_nonneg _
  let M : ℝ := (g t₀ + 1) * (|y| + 1)
  have hM_pos : 0 < M :=
    mul_pos
      (add_pos_of_nonneg_of_pos hg_nonneg (by norm_num))
      (add_pos_of_nonneg_of_pos (abs_nonneg _) (by norm_num))
  have h_le_M : g t₀ * |y| ≤ M := by
    have h₁ : g t₀ * |y| ≤ g t₀ * (|y| + 1) := by
      refine mul_le_mul_of_nonneg_left ?_ hg_nonneg
      have : |y| ≤ |y| + 1 := by have := abs_nonneg y; linarith
      exact this
    have h₂ : g t₀ * (|y| + 1) ≤ (g t₀ + 1) * (|y| + 1) := by
      refine mul_le_mul_of_nonneg_right ?_ (add_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      have : g t₀ ≤ g t₀ + 1 := by linarith
      exact this
    exact le_trans h₁ h₂
  have h_goal :
      ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I) ^ 2) * I‖ ≤ M := by
    have := le_trans h_integral_le h_le_M
    simpa using this

  cases bound_type with
  | at_one =>
      cases h_cond
      exact ⟨M, hM_pos, h_goal⟩
  | interval =>
      rcases h_cond with ⟨_, _⟩
      exact ⟨M, hM_pos, h_goal⟩
  | negative =>
      rcases h_cond with ⟨_, _⟩
      exact ⟨M, hM_pos, h_goal⟩

/-- Unified helper lemma with C bound: For R = 1 with given C -/
lemma gaussian_vertical_integral_bounded_with_C (a : ℂ) (_ha : 0 < a.re) (y : ℝ) (right : Bool)
    (R : ℝ) (C : ℝ) (_hC_pos : 0 < C)
    (hC_bound : ∀ (R' : ℝ), R' > 1 → ‖∫ t in (0 : ℝ)..y,
      Complex.exp (-a * ((if right then ↑R' else -↑R') + ↑t * I) ^ 2) *
      I‖ ≤ C * Real.exp (-a.re * R' ^ 2 / 2))
    (hR : R = 1) :
    ‖∫ t in (0 : ℝ)..y,
      Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) *
      I‖ ≤ C * Real.exp (-a.re * R^2 / 2) := by
  classical
  subst hR
  let sReal : ℝ := if right then (1 : ℝ) else -1
  have h_if (R : ℝ) :
      Complex.ofReal (sReal * R) = (if right then (R : ℂ) else -R) := by
    cases right <;> simp [sReal]

  let integrand : ℝ → ℝ → ℂ := fun R t =>
    Complex.exp (-a * (Complex.ofReal (sReal * R) + (t : ℂ) * I) ^ 2) * I

  have h_linear : Continuous fun p : ℝ × ℝ => Complex.ofReal (sReal * p.1) := by
    have : Continuous fun p : ℝ × ℝ => sReal * p.1 :=
      (continuous_const.mul continuous_fst)
    exact Complex.continuous_ofReal.comp this

  have h_im : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) :=
    Complex.continuous_ofReal.comp continuous_snd

  have h_im_mul : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) * I :=
    h_im.mul continuous_const

  have h_sum : Continuous fun p : ℝ × ℝ =>
      Complex.ofReal (sReal * p.1) + (p.2 : ℂ) * I :=
    h_linear.add h_im_mul

  have h_pow : Continuous fun p : ℝ × ℝ =>
      (Complex.ofReal (sReal * p.1) + (p.2 : ℂ) * I) ^ 2 :=
    h_sum.pow 2

  have h_mul_const : Continuous fun p : ℝ × ℝ =>
      -a * (Complex.ofReal (sReal * p.1) + (p.2 : ℂ) * I) ^ 2 :=
    continuous_const.mul h_pow

  have h_integrand_cont : Continuous fun p : ℝ × ℝ => integrand p.1 p.2 := by
    have h_exp := Complex.continuous_exp.comp h_mul_const
    exact h_exp.mul continuous_const

  have h_integral_cont :
      Continuous fun R : ℝ => ∫ t in (0 : ℝ)..y, integrand R t := by
    have h :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume) (f := integrand)
        (by simpa [integrand, Function.uncurry] using h_integrand_cont)
        (0 : ℝ) y
    simpa [integrand] using h

  let F : ℝ → ℂ := fun R => ∫ t in (0 : ℝ)..y, integrand R t
  have hF_eq (R : ℝ) :
      F R = ∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2) * I := by
    simp [F, integrand, h_if]

  let fNorm : ℝ → ℝ := fun R => ‖F R‖
  have hf_cont : Continuous fNorm := (h_integral_cont.norm)

  let G : ℝ → ℝ := fun R : ℝ => C * Real.exp (-a.re * R ^ 2 / 2)
  have hG_cont : Continuous G := by
    have h_pow : Continuous fun R : ℝ => R ^ 2 := continuous_id.pow 2
    have h_mul1 : Continuous fun R : ℝ => (-a.re) * R ^ 2 :=
      continuous_const.mul h_pow
    have h_mul2 : Continuous fun R : ℝ => (-a.re) * R ^ 2 / 2 :=
      h_mul1.mul continuous_const
    exact continuous_const.mul (Real.continuous_exp.comp h_mul2)

  let seq : ℕ → ℝ := fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)
  have h_seq_gt : ∀ n : ℕ, seq n > 1 := by
    intro n
    have h_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have h_pos : 0 < (n : ℝ) + 1 := add_pos_of_nonneg_of_pos h_nonneg (by norm_num)
    have h_div_pos : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr h_pos
    have h := add_lt_add_left h_div_pos 1
    simpa [seq] using h

  have h_seq_tendsto : Tendsto seq atTop (𝓝 (1 : ℝ)) := by
    have h_inv := tendsto_one_div_add_atTop_nhds_zero_nat
    have h_const : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    simpa [seq] using h_const.add h_inv

  have h_f_le : ∀ n : ℕ, fNorm (seq n) ≤ G (seq n) := by
    intro n
    simpa [fNorm, F, integrand, G, h_if, seq]
      using hC_bound (seq n) (h_seq_gt n)

  have h_f_tendsto :
      Tendsto (fun n : ℕ => fNorm (seq n)) atTop (𝓝 (fNorm 1)) :=
    (hf_cont.tendsto 1).comp h_seq_tendsto

  have h_g_tendsto :
      Tendsto (fun n : ℕ => G (seq n)) atTop (𝓝 (G 1)) :=
    (hG_cont.tendsto 1).comp h_seq_tendsto

  have h_diff_nonneg : ∀ n : ℕ, 0 ≤ G (seq n) - fNorm (seq n) := by
    intro n
    exact sub_nonneg.mpr (h_f_le n)

  have h_diff_tendsto :
      Tendsto (fun n : ℕ => G (seq n) - fNorm (seq n)) atTop
          (𝓝 (G 1 - fNorm 1)) :=
    (h_g_tendsto.sub h_f_tendsto)

  have h_eventually :
      ∀ᶠ n in Filter.atTop,
        G (seq n) - fNorm (seq n) ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun n => by
      have : 0 ≤ G (seq n) - fNorm (seq n) := h_diff_nonneg n
      simpa [Set.mem_Ici] using this
  have h_limit_nonneg : 0 ≤ G 1 - fNorm 1 :=
    (isClosed_Ici.mem_of_tendsto h_diff_tendsto h_eventually)

  have h_le : fNorm 1 ≤ G 1 := sub_nonneg.mp h_limit_nonneg

  have h_exp_simp : G 1 = C * Real.exp (-a.re * (1 : ℝ) ^ 2 / 2) := by
    simp [G]

  have h_norm_eq : fNorm 1 =
      ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a * ((if right then (1 : ℂ) else -(1 : ℂ)) + ↑t * I) ^ 2) * I‖ := by
    simp [fNorm, F, integrand, h_if]

  have h_goal := h_le

  simpa [h_norm_eq, h_exp_simp]
    using h_goal

/-- Helper lemma: Vertical integral bound at R = 1 -/
lemma gaussian_vertical_integral_at_one (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool)
    (C : ℝ) (hC_pos : 0 < C)
    (hC_bound : ∀ (R : ℝ), R > 1 → ‖∫ t in (0 : ℝ)..y,
      Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I) ^ 2) *
      I‖ ≤ C * Real.exp (-a.re * R ^ 2 / 2)) :
    ‖∫ t in (0 : ℝ)..y,
      Complex.exp (-a * ((if right then (1:ℂ) else -(1:ℂ)) + ↑t * I)^2) *
      I‖ ≤ C * Real.exp (-a.re / 2) := by
  have h := gaussian_vertical_integral_bounded_with_C a ha y right 1 C hC_pos hC_bound rfl
  -- h gives us the bound with ↑1, we need it with (1:ℂ)
  simp only [one_pow, mul_one] at h
  exact h

/-- Type for different conditions on R that imply R² ≤ 1 -/
inductive SqLeOneCondition
  | nonneg_le : SqLeOneCondition    -- 0 ≤ R ≤ 1
  | abs_le : SqLeOneCondition        -- |R| ≤ 1
  | neg_le : SqLeOneCondition        -- R < 0 and R ≤ 1

/-- Unified lemma: Various conditions that imply R² ≤ 1 -/
lemma sq_le_one_unified (R : ℝ) (cond : SqLeOneCondition)
    (h : match cond with
      | SqLeOneCondition.nonneg_le => 0 ≤ R ∧ R ≤ 1
      | SqLeOneCondition.abs_le => |R| ≤ 1
      | SqLeOneCondition.neg_le => R < 0 ∧ R ≤ 1 ∧ -1 ≤ R) : R^2 ≤ 1 := by
  match cond with
  | SqLeOneCondition.nonneg_le =>
    obtain ⟨hR_nonneg, hR_le⟩ := h
    calc R^2 = R * R := by ring
      _ ≤ 1 * 1 := mul_le_mul hR_le hR_le hR_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      _ = 1 := by ring
  | SqLeOneCondition.abs_le =>
    have : R^2 = |R|^2 := by rw [sq_abs]
    rw [this]
    calc |R|^2 = |R| * |R| := by ring
      _ ≤ 1 * 1 := mul_le_mul h h (abs_nonneg R) (by norm_num : (0 : ℝ) ≤ 1)
      _ = 1 := by ring
  | SqLeOneCondition.neg_le =>
    obtain ⟨hR_neg, hR_le, hR_ge_neg⟩ := h
    -- Since -1 ≤ R < 0, we have |R| = -R ≤ 1
    have h_abs : |R| ≤ 1 := by
      rw [abs_of_neg hR_neg]
      linarith
    -- Use the abs_le case directly (not recursively)
    have : R^2 = |R|^2 := by rw [sq_abs]
    rw [this]
    calc |R|^2 = |R| * |R| := by ring
      _ ≤ 1 * 1 := mul_le_mul h_abs h_abs (abs_nonneg R) (by norm_num : (0 : ℝ) ≤ 1)
      _ = 1 := by ring

/-- Helper lemma: If R ≤ 1 and R ≥ 0, then R² ≤ 1 -/
lemma sq_le_one_of_le_one (R : ℝ) (hR : R ≤ 1) (hR_nonneg : 0 ≤ R) : R^2 ≤ 1 :=
  sq_le_one_unified R SqLeOneCondition.nonneg_le ⟨hR_nonneg, hR⟩

/-- Helper lemma: If |R| ≤ 1, then R² ≤ 1 -/
lemma sq_le_one_of_abs_le_one (R : ℝ) (hR : |R| ≤ 1) : R^2 ≤ 1 :=
  sq_le_one_unified R SqLeOneCondition.abs_le hR

/-- Helper lemma: If R < 0 and -1 ≤ R ≤ 1, then R² ≤ 1 -/
lemma sq_le_one_of_neg_le_one (R : ℝ) (hR_neg : R < 0) (hR_le : R ≤ 1)
    (hR_ge : -1 ≤ R) : R^2 ≤ 1 :=
  sq_le_one_unified R SqLeOneCondition.neg_le ⟨hR_neg, hR_le, hR_ge⟩

/-- Helper lemma: The vertical integral is bounded for R ∈ [0,1] -/
lemma gaussian_vertical_integral_bounded_on_interval (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool)
    (R : ℝ) (hR_le : R ≤ 1) (hR_ge : 0 ≤ R) :
    ∃ M : ℝ, M > 0 ∧
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤ M :=
  gaussian_vertical_integral_bounded_unified a ha y right R IntegralBoundType.interval
    ⟨hR_ge, hR_le⟩

/-- Helper lemma: The vertical integral is bounded for negative R with R ≤ 1 -/
lemma gaussian_vertical_integral_bounded_negative (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool)
    (R : ℝ) (hR_neg : R < 0) (hR_le : R ≤ 1) :
    ∃ M : ℝ, M > 0 ∧
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤ M :=
  gaussian_vertical_integral_bounded_unified a ha y right R IntegralBoundType.negative
    ⟨hR_neg, hR_le⟩

/-- Helper lemma: Gaussian vertical integral is continuous in R -/
lemma gaussian_vertical_integral_continuous (a : ℂ) (y : ℝ) (right : Bool) :
    ContinuousOn
      (fun R : ℝ => ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖)
      (Set.Icc 0 1) := by
  classical
  -- encode the direction `right` as a real multiplier
  let sReal : ℝ := if right then (1 : ℝ) else -1
  have h_if (R : ℝ) :
      Complex.ofReal (sReal * R) = (if right then (R : ℂ) else -R) := by
    cases right <;> simp [sReal]

  -- parametric integrand whose continuity in `(R, t)` is evident
  let integrand : ℝ → ℝ → ℂ := fun R t =>
    Complex.exp (-a * (Complex.ofReal (sReal * R) + (t : ℂ) * I) ^ 2) * I

  have h_linear : Continuous fun p : ℝ × ℝ => Complex.ofReal (sReal * p.1) := by
    have : Continuous fun p : ℝ × ℝ => sReal * p.1 :=
      continuous_const.mul continuous_fst
    exact Complex.continuous_ofReal.comp this

  have h_im : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) :=
    Complex.continuous_ofReal.comp continuous_snd

  have h_im_mul : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) * I :=
    h_im.mul continuous_const

  have h_sum : Continuous fun p : ℝ × ℝ =>
      Complex.ofReal (sReal * p.1) + (p.2 : ℂ) * I :=
    h_linear.add h_im_mul

  have h_pow : Continuous fun p : ℝ × ℝ =>
      (Complex.ofReal (sReal * p.1) + (p.2 : ℂ) * I) ^ 2 :=
    h_sum.pow 2

  have h_mul_const : Continuous fun p : ℝ × ℝ =>
      -a * (Complex.ofReal (sReal * p.1) + (p.2 : ℂ) * I) ^ 2 :=
    continuous_const.mul h_pow

  have h_integrand_cont : Continuous fun p : ℝ × ℝ => integrand p.1 p.2 := by
    have h_exp := Complex.continuous_exp.comp h_mul_const
    exact h_exp.mul continuous_const

  have h_integral_cont :
      Continuous fun R : ℝ => ∫ t in (0 : ℝ)..y, integrand R t := by
    have h :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume) (f := integrand)
        (by simpa [integrand, Function.uncurry] using h_integrand_cont)
        (0 : ℝ) y
    simpa [integrand] using h

  have h_norm_cont :
      Continuous fun R : ℝ => ‖∫ t in (0 : ℝ)..y, integrand R t‖ :=
    h_integral_cont.norm

  have h_norm_cont_on : ContinuousOn
      (fun R : ℝ => ‖∫ t in (0 : ℝ)..y, integrand R t‖) (Set.Icc 0 1) :=
    h_norm_cont.continuousOn

  simpa [integrand, h_if] using h_norm_cont_on

/-- Helper lemma: Continuous function on compact set attains maximum -/
lemma continuous_on_compact_attains_max {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {f : α → ℝ} (hf : Continuous f) (S : Set α)
    (hS_compact : IsCompact S) (hS_nonempty : S.Nonempty) :
    ∃ x₀ ∈ S, ∀ x ∈ S, f x ≤ f x₀ := by
  classical
  obtain ⟨x₀, hx₀S, hx₀⟩ :=
    hS_compact.exists_isMaxOn hS_nonempty (hf.continuousOn)
  refine ⟨x₀, hx₀S, ?_⟩
  intro x hx
  exact hx₀ hx

/-- Helper lemma: Maximum of gaussian vertical integral on [0,1] exists -/
lemma gaussian_vertical_integral_max_exists (a : ℂ) (y : ℝ) (right : Bool) :
    ∃ R_max ∈ Set.Icc (0:ℝ) 1,
      ∀ R ∈ Set.Icc (0:ℝ) 1,
        ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤
        ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a * ((if right then ↑R_max else -↑R_max) + ↑t * I)^2) * I‖ := by
  -- Apply extreme value theorem to the continuous function on compact set [0,1]
  have h_cont := gaussian_vertical_integral_continuous a y right
  have h_compact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  have h_nonempty : (Set.Icc (0:ℝ) 1).Nonempty := by
    use 0
    simp [Set.Icc]
  -- Apply the extreme value theorem to obtain a maximizer on `[0, 1]`
  obtain ⟨R₀, hR₀_mem, hR₀⟩ :=
    h_compact.exists_isMaxOn h_nonempty h_cont
  refine ⟨R₀, hR₀_mem, ?_⟩
  intro R hR
  exact hR₀ hR

/-- Helper lemma: If M is the maximum of the integral on [0,1], it bounds all values -/
lemma integral_bound_on_interval (a : ℂ) (y : ℝ) (right : Bool) (M : ℝ)
    (hM_is_max : ∃ R₀ ∈ Set.Icc (0 : ℝ) 1,
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R₀ else -↑R₀) + ↑t * I) ^ 2) * I‖ = M ∧
      ∀ R ∈ Set.Icc (0 : ℝ) 1,
        ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I) ^ 2) * I‖ ≤ M) :
    ∀ R ∈ Set.Icc (0:ℝ) 1,
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤ M := by
  -- This follows directly from the hypothesis that M is the maximum

  intro R hR_mem

  -- Extract the bound from the hypothesis
  obtain ⟨R₀, hR₀_mem, ⟨hR₀_eq, hbound⟩⟩ := hM_is_max

  -- Apply the bound directly
  exact hbound R hR_mem

/-- Helper lemma: For R ∈ [0, 1] we have |R| ≤ 1, even when considering negative extensions -/
lemma abs_le_one_of_in_interval (R : ℝ) (hR_lower : -1 ≤ R) (hR_upper : R ≤ 1) : |R| ≤ 1 := by
  -- If -1 ≤ R ≤ 1, then |R| ≤ 1
  rcases le_or_gt 0 R with hR_pos | hR_neg
  · -- Case: R ≥ 0
    simp [abs_of_nonneg hR_pos]
    exact hR_upper
  · -- Case: R < 0
    simp [abs_of_neg hR_neg]
    linarith

/-- Helper lemma: For 0 ≤ R^2 ≤ 1 and a.re > 0, we have exp(a.re/2 - a.re*R^2/2) ≥ 1 -/
lemma exp_ge_one_of_R_sq_le_one (a : ℂ) (ha : 0 < a.re) (R : ℝ) (h_R_sq : R ^ 2 ≤ 1) :
    1 ≤ Real.exp (a.re / 2 - a.re * R^2 / 2) := by
  have h_coeff_nonneg : 0 ≤ a.re / 2 :=
    div_nonneg (le_of_lt ha) (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
  have h_one_minus : 0 ≤ 1 - R^2 := sub_nonneg.mpr h_R_sq
  have h_nonneg_mul : 0 ≤ (a.re / 2) * (1 - R^2) :=
    mul_nonneg h_coeff_nonneg h_one_minus
  have h_eq : a.re / 2 - a.re * R^2 / 2 = (a.re / 2) * (1 - R^2) := by
    ring
  have h_nonneg : 0 ≤ a.re / 2 - a.re * R^2 / 2 := by
    simpa [h_eq] using h_nonneg_mul
  have h_exp : Real.exp 0 ≤ Real.exp (a.re / 2 - a.re * R^2 / 2) := by
    simpa using Real.exp_le_exp.mpr h_nonneg
  simpa [Real.exp_zero] using h_exp

/-- Helper lemma: Shows M_small + 1 ≤ C_small * exp(-a.re * R^2 / 2) when R^2 ≤ 1 -/
lemma small_bound_le_C_small_exp (a : ℂ) (ha : 0 < a.re) (R : ℝ) (h_R_sq : R ^ 2 ≤ 1)
    (M_small : ℝ) (hM_small_nonneg : 0 ≤ M_small) :
    M_small + 1 ≤ (M_small + 1) * Real.exp (a.re / 2) * Real.exp (-a.re * R^2 / 2) := by
  let C_small := (M_small + 1) * Real.exp (a.re / 2)
  have h_exp_combine :
      (M_small + 1) * Real.exp (a.re / 2) * Real.exp (-a.re * R^2 / 2) =
        (M_small + 1) * Real.exp (a.re / 2 - a.re * R^2 / 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h_exp_ge_one : 1 ≤ Real.exp (a.re / 2 - a.re * R^2 / 2) :=
    exp_ge_one_of_R_sq_le_one a ha R h_R_sq
  have h_nonneg_small : 0 ≤ M_small + 1 := by
    linarith [hM_small_nonneg]
  have h_result :=
    mul_le_mul_of_nonneg_left h_exp_ge_one h_nonneg_small
  rw [← h_exp_combine] at h_result
  simpa using h_result

/-- Helper lemma: The C from gaussian_vertical_integral_bound works for all R -/
lemma gaussian_vertical_integral_bounded_all (a : ℂ) (ha : 0 < a.re) (ha_im : a.im = 0)
    (y : ℝ) (hy : 0 ≤ y) (right : Bool) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (R : ℝ),
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤
      C * Real.exp (-a.re * R^2 / 2) := by
  classical
  obtain ⟨C_pos, hC_pos_pos, hC_pos_bound⟩ :=
    gaussian_vertical_integral_bound a ha ha_im y hy right
  obtain ⟨C_flip, hC_flip_pos, hC_flip_bound⟩ :=
    gaussian_vertical_integral_bound a ha ha_im y hy (!right)
  let F : Bool → ℝ → ℂ := fun r R =>
    ∫ t in (0 : ℝ)..y,
      Complex.exp (-a * ((if r then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2) * I
  have h_flip_norm : ∀ R : ℝ, ‖F right R‖ = ‖F (!right) (-R)‖ := by
    intro R
    cases right <;> simp [F]

  obtain ⟨R_pos, hR_pos_mem, hR_pos_bound⟩ :=
    gaussian_vertical_integral_max_exists (a := a) (y := y) (right := right)
  obtain ⟨R_neg, hR_neg_mem, hR_neg_bound⟩ :=
    gaussian_vertical_integral_max_exists (a := a) (y := y) (right := !right)

  let M_pos : ℝ := ‖F right R_pos‖
  have h_pos_bound : ∀ R ∈ Set.Icc (0 : ℝ) 1,
      ‖F right R‖ ≤ M_pos := by
    intro R hR
    simpa [F, M_pos] using hR_pos_bound R hR

  let M_neg : ℝ := ‖F (!right) R_neg‖
  have h_neg_bound : ∀ R ∈ Set.Icc (0 : ℝ) 1,
      ‖F (!right) R‖ ≤ M_neg := by
    intro R hR
    simpa [F, M_neg] using hR_neg_bound R hR

  let M_small : ℝ := max M_pos M_neg
  have hM_small_nonneg : 0 ≤ M_small :=
    (norm_nonneg _).trans (le_max_left _ _)

  let C_small : ℝ := (M_small + 1) * Real.exp (a.re / 2)
  have hC_small_pos : 0 < C_small :=
    mul_pos (by linarith [hM_small_nonneg]) (Real.exp_pos _)

  let C_large : ℝ := max C_pos C_flip
  have hC_large_pos : 0 < C_large :=
    lt_of_lt_of_le hC_pos_pos (le_max_left _ _)

  let C_total : ℝ := max C_small C_large
  have hC_total_pos : 0 < C_total :=
    lt_of_lt_of_le hC_small_pos (le_max_left _ _)

  refine ⟨C_total, hC_total_pos, ?_⟩
  intro R
  change
    ‖F right R‖ ≤ C_total * Real.exp (-a.re * R ^ 2 / 2)

  by_cases h_abs : |R| ≤ 1
  · obtain ⟨hR_lb, hR_ub⟩ := abs_le.mp h_abs
    have h_small_bound : ‖F right R‖ ≤ M_small := by
      by_cases hR_nonneg : 0 ≤ R
      · have hR_mem : R ∈ Set.Icc (0 : ℝ) 1 := ⟨hR_nonneg, hR_ub⟩
        have h_bound := h_pos_bound R hR_mem
        exact h_bound.trans (le_max_left _ _)
      · have hR_neg : R < 0 := lt_of_not_ge hR_nonneg
        have hR_le_zero : R ≤ 0 := le_of_lt hR_neg
        let R' := -R
        have hR'_mem : R' ∈ Set.Icc (0 : ℝ) 1 := by
          refine ⟨neg_nonneg.mpr hR_le_zero, ?_⟩
          simpa using neg_le_neg hR_lb
        have h_bound := h_neg_bound R' hR'_mem
        have h_bound' : ‖F right R‖ ≤ M_neg := by
          have h_rw := (h_flip_norm R).symm
          simpa [R', h_rw] using h_bound
        exact h_bound'.trans (le_max_right _ _)
    have h_R_sq_le : R ^ 2 ≤ (1 : ℝ) :=
      sq_le_one_of_abs_le_one R h_abs
    have h_coeff_nonneg : 0 ≤ a.re / 2 :=
      div_nonneg (le_of_lt ha) (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    have h_one_minus : 0 ≤ 1 - R ^ 2 := by
      simpa [sub_eq_add_neg] using sub_nonneg.mpr h_R_sq_le
    have h_exp_ge_one : 1 ≤ Real.exp (a.re / 2 - a.re * R ^ 2 / 2) :=
      exp_ge_one_of_R_sq_le_one a ha R h_R_sq_le
    have h_small_le : ‖F right R‖ ≤ M_small + 1 :=
      h_small_bound.trans (by linarith)
    have h_le_tail : M_small + 1 ≤ C_small * Real.exp (-a.re * R ^ 2 / 2) :=
      small_bound_le_C_small_exp a ha R h_R_sq_le M_small hM_small_nonneg
    have h_small :
        ‖F right R‖ ≤ C_small * Real.exp (-a.re * R ^ 2 / 2) :=
      h_small_le.trans h_le_tail
    have h_const_le : C_small ≤ C_total :=
      le_max_left _ _
    have h_exp_nonneg : 0 ≤ Real.exp (-a.re * R ^ 2 / 2) := (Real.exp_pos _).le
    exact h_small.trans
      (mul_le_mul_of_nonneg_right h_const_le h_exp_nonneg)

  · have h_abs_gt : 1 < |R| := lt_of_not_ge h_abs
    by_cases hR_pos : R > 1
    · have h_bound := hC_pos_bound R hR_pos
      have h_const_le : C_pos ≤ C_total :=
        le_trans (le_max_left _ _) (le_max_of_le_right (le_refl _))
      have h_exp_nonneg : 0 ≤ Real.exp (-a.re * R ^ 2 / 2) := (Real.exp_pos _).le
      exact h_bound.trans
        (mul_le_mul_of_nonneg_right h_const_le h_exp_nonneg)
    · have hR_le_one : R ≤ 1 := le_of_not_gt hR_pos
      have hR_lt_neg_one : R < -1 := by
        by_contra h
        have hR_ge_neg_one : R ≥ -1 := not_lt.mp h
        have h_abs_le : |R| ≤ 1 := abs_le.mpr ⟨hR_ge_neg_one, hR_le_one⟩
        exact (not_lt_of_ge h_abs_le h_abs_gt).elim
      have hR_flip : (-R) > 1 := by linarith
      have h_bound_flip := hC_flip_bound (-R) hR_flip
      have h_const_le : C_flip ≤ C_total :=
        le_trans (le_max_right _ _) (le_max_of_le_right (le_refl _))
      have h_exp_nonneg : 0 ≤ Real.exp (-a.re * R ^ 2 / 2) := (Real.exp_pos _).le
      have h_bound_neg :
          ‖F right R‖ ≤ C_flip * Real.exp (-a.re * R ^ 2 / 2) := by
        cases right <;> simpa [F, pow_two] using h_bound_flip
      exact h_bound_neg.trans
        (mul_le_mul_of_nonneg_right h_const_le h_exp_nonneg)

/-- Helper lemma: A single vertical integral of Gaussian vanishes as R → ∞
    If `right = true`, it's the right vertical integral (at x = R).
    If `right = false`, it's the left vertical integral (at x = -R). -/
lemma gaussian_vertical_integral_vanish_aux (a : ℂ) (ha : 0 < a.re) (ha_im : a.im = 0)
    (y : ℝ) (hy : 0 ≤ y) (right : Bool) :
    Filter.Tendsto
      (fun R : ℝ => ∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I)
      (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ)) := by
  -- The strategy: Show that |exp(-a(±R + ti)²)| decays exponentially in R

  -- Use the integral bound for all R
  have h_integral_bound := gaussian_vertical_integral_bounded_all a ha ha_im y hy right

  -- As R → ∞, exp(-a.re * R²/2) → 0 (since a.re > 0)
  have h_exp_vanish := exp_neg_quadratic_tendsto_zero a.re ha

  -- Combine the bounds to show the integral tends to 0
  obtain ⟨C, ⟨hC_pos, hC_bound⟩⟩ := h_integral_bound

  -- Use the squeeze theorem
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero
  · intro R
    exact norm_nonneg _
  · intro R
    exact hC_bound R
  · -- C * exp(-a.re * R²/2) → 0
    convert Filter.Tendsto.const_mul C h_exp_vanish
    simp only [mul_zero]

/-- Vertical integrals of Gaussian vanish as R → ∞ -/
lemma gaussian_vertical_integrals_vanish (a : ℂ) (ha : 0 < a.re)
    (ha_im : a.im = 0) (y : ℝ) (hy : 0 ≤ y) :
    let f := fun z => Complex.exp (-a * z^2)
    Filter.Tendsto
      (fun R : ℝ => (∫ t in (0 : ℝ)..y, f (↑R + ↑t * I) * I) -
                    (∫ t in (0 : ℝ)..y, f (-↑R + ↑t * I) * I))
      (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ)) := by
  -- The difference of two integrals converges to 0 if both converge to 0
  simp only

  -- Show that the right vertical integral vanishes (right = true)
  have h_right_vanish : Filter.Tendsto
    (fun R : ℝ => ∫ t in (0 : ℝ)..y, Complex.exp (-a * (↑R + ↑t * I)^2) * I)
    (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ)) := by
    have h := gaussian_vertical_integral_vanish_aux a ha ha_im y hy true
    simp only [if_true] at h
    exact h

  -- Show that the left vertical integral vanishes (right = false)
  have h_left_vanish : Filter.Tendsto
    (fun R : ℝ => ∫ t in (0 : ℝ)..y, Complex.exp (-a * (-↑R + ↑t * I)^2) * I)
    (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ)) := by
    have h := gaussian_vertical_integral_vanish_aux a ha ha_im y hy false
    simp only at h
    exact h

  -- The difference converges to 0 - 0 = 0
  convert Filter.Tendsto.sub h_right_vanish h_left_vanish using 1
  simp only [sub_zero]

/-- Limit of difference of integrals using rectangular contour -/
lemma gaussian_integral_diff_limit (a : ℂ) (y : ℝ) :
    let f := fun z => Complex.exp (-a * z^2)
    -- If the following limits exist:
    (Filter.Tendsto (fun R : ℝ => ∫ x in (-R : ℝ)..R, f ↑x)
      (Filter.atTop : Filter ℝ) (𝓝 (∫ x : ℝ, f ↑x))) →
    (Filter.Tendsto (fun R : ℝ => ∫ x in (-R : ℝ)..R, f (↑x + ↑y * I))
      (Filter.atTop : Filter ℝ) (𝓝 (∫ x : ℝ, f (↑x + ↑y * I)))) →
    -- And the rectangular contour equation holds
    (∀ R > (0 : ℝ), (∫ x in (-R : ℝ)..R, f ↑x) - (∫ x in (-R : ℝ)..R, f (↑x + ↑y * I)) =
                    -((∫ t in (0 : ℝ)..y, f (↑R + ↑t * I) * I) -
                      (∫ t in (0 : ℝ)..y, f (-↑R + ↑t * I) * I))) →
    -- And vertical integrals vanish
    (Filter.Tendsto (fun R : ℝ => (∫ t in (0 : ℝ)..y, f (↑R + ↑t * I) * I) -
                                  (∫ t in (0 : ℝ)..y, f (-↑R + ↑t * I) * I))
      (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ))) →
    -- Then the difference of improper integrals is zero
    (∫ x : ℝ, f ↑x) - (∫ x : ℝ, f (↑x + ↑y * I)) = 0 := by
  simp only
  intro h_conv_real h_conv_shifted h_rect h_vert_vanish

  -- Define the difference function
  let diff_R := fun R : ℝ => (∫ x in (-R : ℝ)..R, Complex.exp (-a * ↑x^2)) -
                             (∫ x in (-R : ℝ)..R, Complex.exp (-a * (↑x + ↑y * I)^2))
  let diff_limit := (∫ x : ℝ, Complex.exp (-a * ↑x^2)) -
                    (∫ x : ℝ, Complex.exp (-a * (↑x + ↑y * I)^2))

  -- The difference function converges to diff_limit
  have h_diff_conv : Filter.Tendsto diff_R Filter.atTop (𝓝 diff_limit) := by
    simp only [diff_R, diff_limit]
    apply Filter.Tendsto.sub h_conv_real h_conv_shifted

  -- By h_rect, diff_R equals negative of vertical integrals
  have h_eq : ∀ᶠ R in (Filter.atTop : Filter ℝ),
              diff_R R = -(((∫ t in (0 : ℝ)..y, Complex.exp (-a * (↑R + ↑t * I)^2) * I) -
                           (∫ t in (0 : ℝ)..y, Complex.exp (-a * (-↑R + ↑t * I)^2) * I))) := by
    rw [Filter.eventually_atTop]
    use 1
    intro R hR
    exact h_rect R (by linarith : 0 < R)

  -- The negative of vertical integrals tends to -0 = 0
  have h_neg_vert : Filter.Tendsto
                    (fun R : ℝ => -(((∫ t in (0 : ℝ)..y, Complex.exp (-a * (↑R + ↑t * I)^2) * I) -
                                    (∫ t in (0 : ℝ)..y, Complex.exp (-a * (-↑R + ↑t * I)^2) * I))))
                    (Filter.atTop : Filter ℝ) (𝓝 (-(0 : ℂ))) := by
    apply Filter.Tendsto.neg
    exact h_vert_vanish

  -- Since -(0) = 0
  have h_neg_zero : -(0 : ℂ) = 0 := neg_zero

  -- By uniqueness of limits, diff_limit = 0
  have h_unique : diff_limit = 0 := by
    -- diff_R converges to both diff_limit and 0
    have h_to_zero : Filter.Tendsto diff_R (Filter.atTop : Filter ℝ) (𝓝 0) := by
      rw [← h_neg_zero]
      -- Use h_eq to show diff_R eventually equals the negative of vertical integrals
      -- h_eq shows: diff_R = negative of vertical integrals (eventually)
      -- We need to reverse the equality for congr'
      have h_eq_symm : ∀ᶠ (R : ℝ) in (Filter.atTop : Filter ℝ),
          -(((∫ t in (0 : ℝ)..y, Complex.exp (-a * (↑R + ↑t * I)^2) * I) -
             (∫ t in (0 : ℝ)..y, Complex.exp (-a * (-↑R + ↑t * I)^2) * I))) = diff_R R := by
        filter_upwards [h_eq] with R hR
        exact hR.symm
      exact Filter.Tendsto.congr' h_eq_symm h_neg_vert
    -- By uniqueness of limits in Hausdorff spaces
    exact tendsto_nhds_unique h_diff_conv h_to_zero

  exact h_unique

/--
Special case: Gaussian contour shift.
The integral of a Gaussian function exp(-a(z+c)²) over a horizontal line
equals the integral over the real axis.
-/
theorem gaussian_contour_shift_general {a : ℂ} (ha : 0 < a.re)
    (ha_im : a.im = 0) (c : ℂ) (hc : c.re = 0) (hc_im : 0 ≤ c.im) :
    ∫ x : ℝ, Complex.exp (-a * (↑x + c)^2) = ∫ x : ℝ, Complex.exp (-a * ↑x^2) := by
  -- We'll use Cauchy's theorem on rectangular contours and take limits

  -- Define the function we're integrating
  let f := fun z => Complex.exp (-a * z^2)

  -- First, verify that f is entire (differentiable everywhere)
  have hf_entire : ∀ z, DifferentiableAt ℂ f z := by
    intro z
    simp [f]
    apply DifferentiableAt.cexp
    apply DifferentiableAt.neg
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.pow
    exact differentiableAt_id

  -- Show both integrals are well-defined (integrable)
  have h_integrable_shifted := gaussian_shifted_integrable a ha c
  have h_integrable_real := gaussian_integrable_complex a ha

  -- Key idea: Use change of variables and contour deformation
  -- For any R > 0, consider the rectangular contour with vertices at:
  -- -R, R, R + c, -R + c

  -- Since c.re = 0 (from hc), c is purely imaginary, so c = c.im * I
  -- Extract the imaginary part to use in gaussian_rectangular_contour
  have h_rect := fun R hR => gaussian_rectangular_contour a ha c.im R hR

  -- From the rectangular contour theorem, for any R > 0:
  -- (∫ x in -R..R, f x) - (∫ x in -R..R, f(x + c.im * I)) +
  -- (∫ t in 0..c.im, f(R + t*I)*I) - (∫ t in 0..c.im, f(-R + t*I)*I) = 0

  -- Rearranging:
  -- ∫ x in -R..R, f(x + c.im * I) = ∫ x in -R..R, f x + (vertical integrals)

  -- We need to show that as R → ∞:
  -- 1. ∫ x in -R..R, f x → ∫ x, f x
  -- 2. ∫ x in -R..R, f(x + c.im * I) → ∫ x, f(x + c.im * I)
  -- 3. The vertical integrals → 0

  -- First, since c.re = 0 and c = c.im * I, we have:
  have c_eq : c = ↑c.im * I := by
    -- Since c.re = 0, we have c = 0 + c.im * i = c.im * I
    apply Complex.ext
    · -- Real part
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      exact hc
    · -- Imaginary part
      simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

  -- The convergence of horizontal integrals
  have h_horiz_conv_real := gaussian_horizontal_conv_real a ha

  -- For the shifted integral, we need to show f(x + c) = f(x + c.im * I)
  -- First show that (↑c.im * I).im = c.im
  have im_calc : (↑c.im * I : ℂ).im = c.im := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

  have shifted_eq : ∀ x : ℝ, f (↑x + c) = f (↑x + ↑c.im * I) := by
    intro x
    simp only [f]
    -- We need to show: exp(-a * (↑x + c)^2) = exp(-a * (↑x + ↑c.im * I)^2)
    -- Since c = ↑c.im * I (from c_eq), we can rewrite the left side
    rw [c_eq]
    -- Now the goal is: exp(-a * (↑x + ↑c.im * I)^2) = exp(-a * (↑x + ↑(↑c.im * I).im * I)^2)
    -- Use im_calc: (↑c.im * I).im = c.im
    rw [im_calc]

  -- Now use this equality for the shifted convergence
  have h_horiz_conv_shifted : Filter.Tendsto (fun R : ℝ => ∫ x in (-R : ℝ)..R, f (↑x + c))
      (Filter.atTop : Filter ℝ) (𝓝 (∫ x : ℝ, f (↑x + c))) := by
    have h := gaussian_horizontal_conv_shifted a ha c
    exact h

  -- For vertical integrals vanishing, we need to show they tend to 0 as R → ∞
  -- The rectangular contour theorem gives us the relation between horizontal and vertical integrals

  -- From h_rect: for each R > 0,
  -- (∫ x in -R..R, f x) - (∫ x in -R..R, f(x + c.im * I)) =
  -- - ((∫ t in 0..c.im, f(R + t*I)*I) - (∫ t in 0..c.im, f(-R + t*I)*I))

  have h_rect_rearranged : ∀ R > (0 : ℝ),
    (∫ x in (-R : ℝ)..R, f ↑x) - (∫ x in (-R : ℝ)..R, f (↑x + ↑c.im * I)) =
    - ((∫ t in (0 : ℝ)..c.im, f (↑R + ↑t * I) * I) -
       (∫ t in (0 : ℝ)..c.im, f (-↑R + ↑t * I) * I)) := by
    intro R hR
    have eq := h_rect R hR
    simp only at eq
    -- The equation from h_rect is:
    -- (∫ x in -R..R, f x) - (∫ x in -R..R, f(x + c.im * I)) +
    -- (∫ t in 0..c.im, f(R + t*I)*I) - (∫ t in 0..c.im, f(-R + t*I)*I) = 0
    -- Rearranging algebraically:
    calc (∫ x in (-R : ℝ)..R, f ↑x) - (∫ x in (-R : ℝ)..R, f (↑x + ↑c.im * I))
        = 0 - ((∫ t in (0 : ℝ)..c.im, f (↑R + ↑t * I) * I) -
               (∫ t in (0 : ℝ)..c.im, f (-↑R + ↑t * I) * I)) := by
          rw [← eq]
          ring
      _ = - ((∫ t in (0 : ℝ)..c.im, f (↑R + ↑t * I) * I) -
             (∫ t in (0 : ℝ)..c.im, f (-↑R + ↑t * I) * I)) := by simp

  -- Now we need to show that the vertical integrals tend to 0
  -- Use the lemma about vertical integrals vanishing
  have h_vert_vanish : Filter.Tendsto
    (fun R : ℝ => (∫ t in (0 : ℝ)..c.im, f (↑R + ↑t * I) * I) -
                  (∫ t in (0 : ℝ)..c.im, f (-↑R + ↑t * I) * I))
    (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ)) :=
    gaussian_vertical_integrals_vanish a ha ha_im c.im hc_im

  -- Taking the limit R → ∞ in h_rect_rearranged
  -- Left side: (∫ x, f x) - (∫ x, f(x + c.im * I))
  -- Right side: - 0 = 0
  -- Therefore: ∫ x, f x = ∫ x, f(x + c.im * I)

  have h_limit : (∫ x : ℝ, f ↑x) - (∫ x : ℝ, f (↑x + ↑c.im * I)) = 0 := by
    -- Apply the limit lemma
    apply gaussian_integral_diff_limit a c.im
    -- 1. Real integral converges
    exact h_horiz_conv_real
    -- 2. Shifted integral converges (need to adapt h_horiz_conv_shifted)
    · have : Tendsto (fun R => ∫ x in (-R : ℝ)..R, f (↑x + ↑c.im * I))
             atTop (𝓝 (∫ x : ℝ, f (↑x + ↑c.im * I))) := by
        convert h_horiz_conv_shifted using 2
        · congr 1
          ext x
          exact (shifted_eq x).symm
        · congr 1
          ext x
          exact (shifted_eq x).symm
      exact this
    -- 3. Rectangular contour equation
    exact h_rect_rearranged
    -- 4. Vertical integrals vanish
    exact h_vert_vanish

  -- Finally, use shifted_eq to relate f(x + c.im * I) to f(x + c)
  calc ∫ x : ℝ, Complex.exp (-a * (↑x + c)^2)
      = ∫ x : ℝ, f (↑x + c) := by simp only [f]
    _ = ∫ x : ℝ, f (↑x + ↑c.im * I) := by
        congr 1
        ext x
        exact shifted_eq x
    _ = ∫ x : ℝ, f ↑x := by
        -- From h_limit: (∫ x, f x) - (∫ x, f(x + c.im * I)) = 0
        -- Therefore: ∫ x, f(x + c.im * I) = ∫ x, f x
        rw [sub_eq_zero] at h_limit
        exact h_limit.symm
    _ = ∫ x : ℝ, Complex.exp (-a * ↑x^2) := by simp only [f]

/-- Helper lemma: Real part of π/δ² is positive when δ > 0 -/
lemma pi_div_delta_sq_re_pos {δ : ℝ} (hδ : 0 < δ) : 0 < (↑π / ↑δ^2 : ℂ).re := by
  have hδ_sq_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hare_eq₀ : (↑π / ↑δ ^ 2 : ℂ) = Complex.ofReal (π / δ ^ 2) := by
    calc
      ↑π / ↑δ ^ 2
          = Complex.ofReal π / (Complex.ofReal δ) ^ 2 := rfl
      _ = Complex.ofReal π / Complex.ofReal (δ ^ 2) := by
            simp [pow_two, Complex.ofReal_mul]
      _ = Complex.ofReal (π / δ ^ 2) := by
            simp
  rw [hare_eq₀, Complex.ofReal_re]
  exact div_pos Real.pi_pos hδ_sq_pos

/-- Helper lemma: Imaginary part of π/δ² is zero -/
lemma pi_div_delta_sq_im_zero (δ : ℝ) : (↑π / ↑δ^2 : ℂ).im = 0 := by
  have : (↑π / ↑δ^2 : ℂ) = Complex.ofReal (π / δ^2) := by
    calc
      ↑π / ↑δ^2
          = Complex.ofReal π / (Complex.ofReal δ)^2 := rfl
      _ = Complex.ofReal π / Complex.ofReal (δ^2) := by
            simp [pow_two, Complex.ofReal_mul]
      _ = Complex.ofReal (π / δ^2) := by
            simp
  rw [this, Complex.ofReal_im]

/-- Helper lemma: Real part of I*δ²*ξ is zero -/
lemma i_delta_sq_xi_re_zero (δ ξ : ℝ) : (I * ↑(δ^2) * ↑ξ : ℂ).re = 0 := by
  -- Extremely detailed proof with multiple layers of abstraction

  -- Layer 1: Establish fundamental properties of complex coercion
  have coerce_prop_1 : ∀ (a b : ℝ), (↑(a * b) : ℂ) = (↑a : ℂ) * (↑b : ℂ) :=
    fun a b => Complex.ofReal_mul a b

  have coerce_prop_2 : ∀ (a : ℝ), (↑a : ℂ).re = a :=
    fun a => Complex.ofReal_re a

  have coerce_prop_3 : ∀ (a : ℝ), (↑a : ℂ).im = 0 :=
    fun a => Complex.ofReal_im a

  -- Layer 2: Establish properties of square operation
  have sq_decomp : δ^2 = δ * δ := sq δ

  have sq_cast_property : (↑(δ^2) : ℂ) = (↑(δ * δ) : ℂ) := by
    -- Extremely detailed proof to avoid any type issues
    have step1 : δ^2 = δ * δ := sq_decomp
    have step2 : ∀ (x y : ℝ), x = y → (↑x : ℂ) = (↑y : ℂ) := by
      intros x y h_eq
      rw [h_eq]
    have step3 : (↑(δ^2) : ℂ) = (↑(δ * δ) : ℂ) := step2 (δ^2) (δ * δ) step1
    exact step3

  -- Layer 3: Complex multiplication chain
  have complex_sq_expansion : (↑(δ^2) : ℂ) = (↑δ : ℂ) * (↑δ : ℂ) := by
    calc (↑(δ^2) : ℂ)
        = (↑(δ * δ) : ℂ) := sq_cast_property
        _ = (↑δ : ℂ) * (↑δ : ℂ) := coerce_prop_1 δ δ

  -- Layer 4: Associativity manipulation
  have assoc_form : I * ↑(δ^2) * ↑ξ = I * (↑(δ^2) * ↑ξ) := by
    rw [mul_assoc I (↑(δ^2) : ℂ) (↑ξ : ℂ)]

  -- Layer 5: Product analysis
  have prod_im_zero : (↑(δ^2) * ↑ξ : ℂ).im = 0 := by
    rw [Complex.mul_im]
    have h1 : (↑(δ^2) : ℂ).re = δ^2 := coerce_prop_2 (δ^2)
    have h2 : (↑(δ^2) : ℂ).im = 0 := coerce_prop_3 (δ^2)
    have h3 : (↑ξ : ℂ).re = ξ := coerce_prop_2 ξ
    have h4 : (↑ξ : ℂ).im = 0 := coerce_prop_3 ξ
    calc (↑(δ^2) : ℂ).re * (↑ξ : ℂ).im + (↑(δ^2) : ℂ).im * (↑ξ : ℂ).re
        = δ^2 * 0 + 0 * ξ := by rw [h1, h2, h3, h4]
        _ = 0 + 0 := by ring
        _ = 0 := by norm_num

  -- Layer 6: Complex I multiplication property
  have i_mul_prop : ∀ (z : ℂ), (I * z).re = -z.im := fun z => Complex.I_mul_re z

  -- Layer 7: Final calculation
  calc (I * ↑(δ^2) * ↑ξ : ℂ).re
      = (I * (↑(δ^2) * ↑ξ) : ℂ).re := by rw [assoc_form]
      _ = -(↑(δ^2) * ↑ξ : ℂ).im := i_mul_prop (↑(δ^2) * ↑ξ)
      _ = -0 := by rw [prod_im_zero]
      _ = 0 := by norm_num

/-- Helper lemma: Imaginary part of I*δ²*ξ equals δ²*ξ -/
lemma i_delta_sq_xi_im (δ ξ : ℝ) : (I * ↑(δ^2) * ↑ξ : ℂ).im = δ^2 * ξ := by
  -- Ultra-complex proof with exhaustive detail

  -- Foundation Layer: Complex number axioms
  have complex_axiom_re : ∀ (r : ℝ), (↑r : ℂ).re = r :=
    fun r => Complex.ofReal_re r
  have complex_axiom_im : ∀ (r : ℝ), (↑r : ℂ).im = 0 :=
    fun r => Complex.ofReal_im r
  have complex_axiom_mul : ∀ (a b : ℝ), (↑(a * b) : ℂ) = (↑a : ℂ) * (↑b : ℂ) :=
    fun a b => Complex.ofReal_mul a b

  -- Square decomposition layer
  have square_def : δ^2 = δ * δ := sq δ
  have square_complex_cast : (↑(δ^2) : ℂ) = (↑(δ * δ) : ℂ) := by
    -- Ultra-detailed proof to avoid any issues
    have h_eq : δ^2 = δ * δ := square_def
    have cast_eq : ∀ (a b : ℝ), a = b → (↑a : ℂ) = (↑b : ℂ) := by
      intros a b h_ab
      rw [h_ab]
    exact cast_eq (δ^2) (δ * δ) h_eq

  -- Complex square relationship
  have complex_square_rel : (↑(δ^2) : ℂ) = (↑δ : ℂ) * (↑δ : ℂ) := by
    rw [square_complex_cast]
    exact complex_axiom_mul δ δ

  -- Multiplication associativity layer
  have mul_assoc_specific : I * ↑(δ^2) * ↑ξ = I * (↑(δ^2) * ↑ξ) :=
    mul_assoc I (↑(δ^2) : ℂ) (↑ξ : ℂ)

  -- Product real part computation
  have product_real_part : (↑(δ^2) * ↑ξ : ℂ).re = δ^2 * ξ := by
    rw [Complex.mul_re]
    -- Detailed computation of each component
    have comp1 : (↑(δ^2) : ℂ).re = δ^2 := complex_axiom_re (δ^2)
    have comp2 : (↑(δ^2) : ℂ).im = 0 := complex_axiom_im (δ^2)
    have comp3 : (↑ξ : ℂ).re = ξ := complex_axiom_re ξ
    have comp4 : (↑ξ : ℂ).im = 0 := complex_axiom_im ξ

    calc (↑(δ^2) : ℂ).re * (↑ξ : ℂ).re - (↑(δ^2) : ℂ).im * (↑ξ : ℂ).im
        = δ^2 * ξ - 0 * 0 := by rw [comp1, comp2, comp3, comp4]
        _ = δ^2 * ξ - 0 := by ring
        _ = δ^2 * ξ := by norm_num

  -- Product imaginary part (for completeness)
  have product_imag_part : (↑(δ^2) * ↑ξ : ℂ).im = 0 := by
    rw [Complex.mul_im]
    have comp1 : (↑(δ^2) : ℂ).re = δ^2 := complex_axiom_re (δ^2)
    have comp2 : (↑(δ^2) : ℂ).im = 0 := complex_axiom_im (δ^2)
    have comp3 : (↑ξ : ℂ).re = ξ := complex_axiom_re ξ
    have comp4 : (↑ξ : ℂ).im = 0 := complex_axiom_im ξ

    calc (↑(δ^2) : ℂ).re * (↑ξ : ℂ).im + (↑(δ^2) : ℂ).im * (↑ξ : ℂ).re
        = δ^2 * 0 + 0 * ξ := by rw [comp1, comp2, comp3, comp4]
        _ = 0 + 0 := by ring
        _ = 0 := by norm_num

  -- Complex I multiplication imaginary part property
  have i_mul_im_property : ∀ (z : ℂ), (I * z).im = z.re :=
    fun z => Complex.I_mul_im z

  -- Final assembly
  calc (I * ↑(δ^2) * ↑ξ : ℂ).im
      = (I * (↑(δ^2) * ↑ξ) : ℂ).im := by rw [mul_assoc_specific]
      _ = (↑(δ^2) * ↑ξ : ℂ).re := i_mul_im_property (↑(δ^2) * ↑ξ)
      _ = δ^2 * ξ := product_real_part

/-- Helper lemma: Gaussian functions are integrable -/
lemma gaussian_integrable_basic (a : ℂ) (ha : 0 < a.re) :
    ∀ c : ℂ, Integrable (fun x : ℝ => Complex.exp (-a * (↑x + c)^2)) := by
  intro c
  simpa using gaussian_shifted_integrable a ha c

/-- Standard negation homeomorphism on ℝ -/
def neg_homeomorph : Homeomorph ℝ ℝ := {
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := fun x => by simp
  right_inv := fun x => by simp
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg
}

/-- Helper lemma: The standard negation homeomorphism preserves Lebesgue measure -/
lemma neg_homeomorph_measure_preserving :
    MeasureTheory.MeasurePreserving neg_homeomorph.toFun := by
  simpa [neg_homeomorph] using Measure.measurePreserving_neg (volume : Measure ℝ)

lemma integral_gaussian_neg_substitution (a : ℂ) (c : ℂ) :
    ∫ (x : ℝ), Complex.exp (-a * (↑x + c)^2) =
    ∫ (x : ℝ), Complex.exp (-a * (↑(-x) + c)^2) := by
  classical
  have h :=
    (neg_homeomorph_measure_preserving.integral_comp
        (neg_homeomorph.measurableEmbedding)
        (fun x : ℝ => Complex.exp (-a * ((x : ℂ) + c)^2)))
  -- `h` gives the equality with the integrals swapped; rewrite to the desired statement
  simpa [neg_homeomorph]
    using h.symm

/-- Helper lemma: Transform integral with shift to standard form -/
lemma gaussian_shift_transform (a_param : ℂ) (c_param : ℂ)
    (h_subst_left : ∫ (a : ℝ), Complex.exp (-a_param * (↑a + c_param) ^ 2) =
                     ∫ (u : ℝ), Complex.exp (-a_param * (↑(-u) + c_param) ^ 2))
    (h_simplified : ∫ (u : ℝ), Complex.exp (-a_param * (↑(-u) + c_param) ^ 2) =
                     ∫ (u : ℝ), Complex.exp (-a_param * (↑u - c_param) ^ 2))
    (h_expand : ∫ (u : ℝ), Complex.exp (-a_param * (↑u - c_param) ^ 2) =
                 ∫ (u : ℝ), Complex.exp (-a_param * ((↑u) ^ 2 - 2 * ↑u * c_param + c_param ^ 2)))
    (h_general : ∫ (u : ℝ), Complex.exp (-a_param * (↑u + (-c_param)) ^ 2) =
                  ∫ (s : ℝ), Complex.exp (-a_param * ↑s ^ 2)) :
    ∫ (a : ℝ), Complex.exp (-a_param * (↑a + c_param)^2) =
    ∫ (s : ℝ), Complex.exp (-a_param * ↑s^2) := by
  calc ∫ (a : ℝ), Complex.exp (-a_param * (↑a + c_param)^2)
      = ∫ (u : ℝ), Complex.exp (-a_param * (↑(-u) + c_param)^2) := h_subst_left
      _ = ∫ (u : ℝ), Complex.exp (-a_param * (↑u - c_param)^2) := h_simplified
      _ = ∫ (u : ℝ), Complex.exp (-a_param * ((↑u)^2 - 2 * ↑u * c_param + c_param^2)) := h_expand
      _ = ∫ (u : ℝ), Complex.exp (-a_param * (↑u + (-c_param))^2) := by
          -- Need to show (u - c_param)² = (u + (-c_param))²
          congr 1
          ext u
          congr 1
          congr 1
          ring
      _ = ∫ (s : ℝ), Complex.exp (-a_param * ↑s^2) := h_general

/-- Helper lemma: Connect parametric form to original form -/
lemma gaussian_parametric_to_original (δ ξ : ℝ)
    (a_param : ℂ) (c_param : ℂ)
    (h_a_def : a_param = ↑π / ↑δ ^ 2)
    (h_c_def : c_param = I * ↑δ ^ 2 * ↑ξ) :
    (∫ (a : ℝ), Complex.exp (-a_param * (↑a + c_param)^2) =
     ∫ (s : ℝ), Complex.exp (-a_param * ↑s^2)) ↔
    (∫ (a : ℝ), Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
     ∫ (s : ℝ), Complex.exp (-↑π / ↑δ^2 * ↑s^2)) := by
  rw [h_a_def, h_c_def]
  -- Both sides are the same after substitution
  constructor
  · intro h
    convert h using 2
    · ext a; congr 1; ring
    · ext s; congr 1; ring
  · intro h
    convert h using 2
    · ext a; congr 1; ring
    · ext s; congr 1; ring

/--
Helper lemma for handling the case when c.im < 0 in gaussian_contour_shift.
This lemma directly provides the needed equality with the correct variable names.
-/
lemma gaussian_shift_neg_case (δ ξ : ℝ) (hδ : 0 < δ) (hξ : ξ < 0) :
    ∫ (a : ℝ), Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ (s : ℝ), Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
  -- Set up parameters for the general theorem
  let a_param : ℂ := ↑π / ↑δ^2
  let c_param : ℂ := I * ↑δ^2 * ↑ξ

  -- Prove the required conditions
  have ha_re_pos : 0 < a_param.re := pi_div_delta_sq_re_pos hδ
  have ha_im : a_param.im = 0 := pi_div_delta_sq_im_zero δ
  have hc_re : c_param.re = 0 := by
    -- c_param = I * ↑δ^2 * ↑ξ, we need to show its real part is 0
    have equiv : c_param = I * ↑(δ^2) * ↑ξ := by
      simp only [c_param]
      -- Show that ↑δ^2 = ↑(δ^2)
      congr 2
      -- This is true by the definition of coercion
      have : (↑δ : ℂ)^2 = ↑(δ^2) := by
        rw [sq, sq]
        exact (Complex.ofReal_mul δ δ).symm
      exact this
    rw [equiv]
    exact i_delta_sq_xi_re_zero δ ξ

  have hc_im : c_param.im < 0 := by
    -- c_param = I * ↑δ^2 * ↑ξ, we need to show its imaginary part is negative
    have equiv : c_param = I * ↑(δ^2) * ↑ξ := by
      simp only [c_param]
      congr 2
      have : (↑δ : ℂ)^2 = ↑(δ^2) := by
        rw [sq, sq]
        exact (Complex.ofReal_mul δ δ).symm
      exact this
    rw [equiv]
    have h : (I * ↑(δ^2) * ↑ξ : ℂ).im = δ^2 * ξ := i_delta_sq_xi_im δ ξ
    rw [h]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hδ) hξ

  -- The theorem gaussian_contour_shift_general requires c.im ≥ 0,
  -- but we have c.im < 0. We use transformation to reduce to the positive case.

  -- Strategy: Use substitution u = -a to flip the imaginary part
  -- This transforms c_param to -c_param, making its imaginary part positive

  -- Step 1: Apply substitution u = -a in the left integral
  have h_subst_left : ∫ (a : ℝ), Complex.exp (-a_param * (↑a + c_param)^2) =
                       ∫ (u : ℝ), Complex.exp (-a_param * (↑(-u) + c_param)^2) := by
    -- Use change of variables for Lebesgue integrals
    -- The substitution u = -a has Jacobian = |-1| = 1

    -- First show the function is integrable
    have h_integrable : Integrable (fun a : ℝ => Complex.exp (-a_param * (↑a + c_param)^2)) :=
      gaussian_integrable_basic a_param ha_re_pos c_param

    -- Apply the substitution using the standard negation homeomorphism
    -- The measure is preserved under negation (Haar measure property)
    have h_measure_preserving : MeasureTheory.MeasurePreserving neg_homeomorph.toFun :=
      neg_homeomorph_measure_preserving

    -- Apply the change of variables theorem
    -- For negation, we can use the fact that ∫f(-x) = ∫f(x) for Lebesgue measure
    exact integral_gaussian_neg_substitution a_param c_param

  -- Step 2: Simplify the substituted integral
  have h_simplified : ∫ (u : ℝ), Complex.exp (-a_param * (↑(-u) + c_param)^2) =
                       ∫ (u : ℝ), Complex.exp (-a_param * (↑u - c_param)^2) := by
    congr 1
    ext u
    congr 1
    congr 1
    simp only [Complex.ofReal_neg]
    ring

  -- Step 3: Expand (u - c_param)² = u² - 2u*c_param + c_param²
  -- Note that c_param is purely imaginary (c_param.re = 0)
  have h_expand : ∫ (u : ℝ), Complex.exp (-a_param * (↑u - c_param)^2) =
                  ∫ (u : ℝ), Complex.exp (-a_param * ((↑u)^2 - 2 * ↑u * c_param + c_param^2)) := by
    congr 1
    ext u
    congr 1
    congr 1
    ring

  -- Step 4: Now we have -c_param which has positive imaginary part
  have hc_neg_param_im : 0 < (-c_param).im := by
    simp only [Complex.neg_im]
    exact neg_pos_of_neg hc_im

  have hc_neg_param_re : (-c_param).re = 0 := by
    simp only [Complex.neg_re]
    rw [hc_re]
    simp

  -- Step 5: Apply gaussian_contour_shift_general with -c_param
  have h_general := gaussian_contour_shift_general ha_re_pos ha_im (-c_param)
                    hc_neg_param_re (le_of_lt hc_neg_param_im)

  -- Step 6: Complete the proof
  -- We need to show: ∫ exp(-π/δ² * (a + I*δ²*ξ)²) = ∫ exp(-π/δ² * s²)
  -- From h_general, we have: ∫ exp(-a_param * (t + (-c_param))²) = ∫ exp(-a_param * t²)

  -- Transform h_simplified and h_expand to match h_general
  rw [← gaussian_parametric_to_original δ ξ a_param c_param rfl rfl]
  exact gaussian_shift_transform a_param c_param h_subst_left h_simplified h_expand h_general

/--
Specific version for our use case with real parameters.
This is the version needed for the Gaussian Fourier transform proof.
-/
theorem gaussian_contour_shift_real {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
  -- Handle both ξ ≥ 0 and ξ < 0 cases
  by_cases hξ : 0 ≤ ξ
  · -- Case ξ ≥ 0: Use gaussian_contour_shift_general directly
    -- Apply gaussian_contour_shift_general with a = π/δ² and c = I*δ²*ξ

    -- First, set up the parameters
    let a : ℂ := ↑π / ↑δ^2
    let c : ℂ := I * ↑δ^2 * ↑ξ

    -- Verify that a.re > 0
    have ha_re_pos : 0 < a.re := by
      have hδ_sq_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ
      have hare_eq₀ : (↑π / ↑δ ^ 2 : ℂ) = Complex.ofReal (π / δ ^ 2) := by
        calc
          ↑π / ↑δ ^ 2
              = Complex.ofReal π / (Complex.ofReal δ) ^ 2 := rfl
          _ = Complex.ofReal π / Complex.ofReal (δ ^ 2) := by
                simp [pow_two, Complex.ofReal_mul]
          _ = Complex.ofReal (π / δ ^ 2) := by
                simp
      have hare_eq : a.re = π / δ ^ 2 := by
        have h := congrArg Complex.re hare_eq₀
        have h' := h.trans (Complex.ofReal_re (π / δ ^ 2))
        simpa [a] using h'
      simpa [hare_eq] using div_pos Real.pi_pos hδ_sq_pos

    -- Derive a.im = 0 from the fact that a = Complex.ofReal (π / δ^2)
    have ha_im : a.im = 0 := by
      have hare_eq₀ : (↑π / ↑δ ^ 2 : ℂ) = Complex.ofReal (π / δ ^ 2) := by
        calc
          ↑π / ↑δ ^ 2
              = Complex.ofReal π / (Complex.ofReal δ) ^ 2 := rfl
          _ = Complex.ofReal π / Complex.ofReal (δ ^ 2) := by
                simp [pow_two, Complex.ofReal_mul]
          _ = Complex.ofReal (π / δ ^ 2) := by
                simp
      have h := congrArg Complex.im hare_eq₀
      have h' := h.trans (Complex.ofReal_im (π / δ ^ 2))
      simpa [a] using h'

    have hc_re : c.re = 0 := by
      -- c = I * ↑δ^2 * ↑ξ
      -- Since I = Complex.I has re = 0 and im = 1, and δ^2, ξ are real,
      -- we have c = (0 + i) * (δ^2 + 0i) * (ξ + 0i) = 0 + i*δ^2*ξ
      -- Therefore c.re = 0
      simp only [c, Complex.mul_re, Complex.I_re, Complex.I_im,
                 Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      -- The goal is now (0 - 1 * (↑δ ^ 2).im) * ξ = 0
      -- Since δ^2 is a real number, (↑δ ^ 2).im = 0
      have h : (↑(δ^2) : ℂ).im = 0 := Complex.ofReal_im _
      -- Now rewrite using h
      conv_lhs => rw [← h]
      simp

    -- Verify that c.im ≥ 0
    have hc_im : 0 ≤ c.im := by
      -- c = I * ↑δ^2 * ↑ξ
      -- Since I = Complex.I = ⟨0, 1⟩ and δ^2, ξ are real:
      -- c = (0 + i) * (δ^2 + 0i) * (ξ + 0i) = i * δ^2 * ξ = (0 + i*δ^2*ξ)
      -- Therefore c.im = δ^2 * ξ
      -- Need to convert between ↑δ^2 and ↑(δ^2)
      have h_eq : c = I * ↑(δ^2) * ↑ξ := by
        simp only [c]
        congr 2
        have : (↑δ : ℂ)^2 = ↑(δ^2) := by
          rw [sq, sq]
          exact (Complex.ofReal_mul δ δ).symm
        exact this
      rw [h_eq]
      have h_c_im := i_delta_sq_xi_im δ ξ
      rw [h_c_im]
      exact mul_nonneg (sq_nonneg δ) hξ

    -- Apply gaussian_contour_shift_general
    have h := gaussian_contour_shift_general ha_re_pos ha_im c hc_re hc_im

    -- Now we need to show that the integrals match the desired form
    convert h using 1
    · congr 1
      ext x
      -- Need to show: exp(-↑π / ↑δ^2 * (↑x + I * ↑δ^2 * ↑ξ)^2) = exp(-a * (↑x + c)^2)
      congr 1
      -- Need to show: -↑π / ↑δ^2 * (↑x + I * ↑δ^2 * ↑ξ)^2 = -a * (↑x + c)^2
      simp only [a, c]
      ring
    · congr 1
      ext s
      -- Need to show: exp(-↑π / ↑δ^2 * ↑s^2) = exp(-a * ↑s^2)
      congr 1
      -- Need to show: -↑π / ↑δ^2 * ↑s^2 = -a * ↑s^2
      simp only [a]
      ring
  · push_neg at hξ
    exact gaussian_shift_neg_case δ ξ hδ hξ

end Frourio
