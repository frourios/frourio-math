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
lemma gaussian_rectangular_contour (a : ℂ) (ha : 0 < a.re) (c : ℂ) (R : ℝ) (hR : 0 < R) :
    let f := fun z => Complex.exp (-a * z^2)
    (∫ x in (-R : ℝ)..R, f x) - (∫ x in (-R : ℝ)..R, f (x + c)) +
    (∫ t in (0 : ℝ)..(1 : ℝ), f ((R : ℂ) + t * c) * c) -
    (∫ t in (0 : ℝ)..(1 : ℝ), f (-(R : ℂ) + t * c) * c) = 0 := by
  simp only
  -- The parametrization needs to be adjusted
  -- We have integrals along:
  -- 1. bottom: from -R to R at height 0
  -- 2. top: from -R to R at height c.im
  -- 3. right: from 0 to c.im at x = R
  -- 4. left: from 0 to c.im at x = -R

  sorry -- Need to parametrize the contour correctly for cauchy_rectangle_formula

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

/-- Helper lemma: Asymptotic dominance for large R in the positive sign case -/
lemma large_R_dominance_pos (a : ℂ) (ha : 0 < a.re) (c : ℂ) (sign : ℝ) (R : ℝ) (t : ℝ)
    (hsign_pos : 0 < sign) (hR : max 1 (2 * ‖c‖ / |sign|) < R) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    -(a.re * sign * R * t * c.re * 2) + (-(a.re * sign ^ 2 * R ^ 2) - a.re * t ^ 2 * c.re ^ 2) +
    a.re * t ^ 2 * c.im ^ 2 + sign * R * t * a.im * c.im * 2 +
    t ^ 2 * c.re * a.im * c.im * 2 ≤
    a.re * sign ^ 2 * R ^ 2 * (-1 / 2) + a.re * ‖c‖ ^ 2 := by
  -- The proof strategy: show that when R > 2‖c‖/sign, we have sign*R > 2‖c‖
  -- This means (sign*R)^2 > 4‖c‖^2, so the negative term dominates

  -- We will show that all the extra terms can be bounded by a.re * (sign * R)^2 / 2
  -- when R is sufficiently large

  sorry

/-- Helper lemma: Asymptotic dominance for large R in the negative sign case -/
lemma large_R_dominance_neg (a : ℂ) (ha : 0 < a.re) (c : ℂ) (sign : ℝ) (R : ℝ) (t : ℝ)
    (hsign_neg : sign < 0) (hR : max 1 (2 * ‖c‖ / |sign|) < R) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    -(a.re * sign * R * t * c.re * 2) + (-(a.re * sign ^ 2 * R ^ 2) - a.re * t ^ 2 * c.re ^ 2) +
    a.re * t ^ 2 * c.im ^ 2 + sign * R * t * a.im * c.im * 2 +
    t ^ 2 * c.re * a.im * c.im * 2 ≤
    a.re * sign ^ 2 * R ^ 2 * (-1 / 2) + a.re * ‖c‖ ^ 2 := by
  -- The proof strategy for negative sign is similar to positive sign
  -- When sign < 0, we have |sign| = -sign, so R > 2‖c‖/|sign| means R > 2‖c‖/(-sign)
  -- This gives us -sign * R > 2‖c‖, and since sign^2 > 0, the negative term still dominates

  sorry

/-- Helper lemma: sum of real parts inequality -/
lemma complex_real_parts_sum_bound (a : ℂ) (ha : 0 < a.re) (c : ℂ) (sign : ℝ)
    (hsign : sign ≠ 0) (R : ℝ) (hR : max 1 (2 * ‖c‖ / |sign|) < R) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (c_norm_sq : c.re ^ 2 + c.im ^ 2 = ‖c‖ ^ 2) :
    (-(a * ((sign * R : ℂ) ^ 2))).re + (-(a * (2 * (sign * R : ℂ) * (t : ℂ) * c))).re +
    (-(a * ((t : ℂ) * c) ^ 2)).re ≤ -(a.re * (sign * R)^2) / 2 + a.re * ‖c‖^2 := by
  -- Split the sum and use negativity
  have expand : (-(a * ((sign * R : ℂ) ^ 2))).re + (-(a * (2 * (sign * R : ℂ) * (t : ℂ) * c))).re +
                (-(a * ((t : ℂ) * c) ^ 2)).re =
                -(a * ((sign * R : ℂ) ^ 2)).re - (a * (2 * (sign * R : ℂ) * (t : ℂ) * c)).re -
                (a * ((t : ℂ) * c) ^ 2).re := by
    simp only [neg_re]
    ring

  rw [expand]

  -- Calculate each real part
  have h1 : (a * ((sign * R : ℂ) ^ 2)).re = a.re * (sign * R)^2 := by
    rw [sq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, sq]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

  have h2 : (a * (2 * (sign * R : ℂ) * (t : ℂ) * c)).re =
            2 * sign * R * t * (a.re * c.re - a.im * c.im) := by
    -- Rewrite multiplication step by step
    have step1 : (2 * (sign * R : ℂ) * (t : ℂ) * c) = ((2 * sign * R * t : ℝ) : ℂ) * c := by
      simp only [Complex.ofReal_mul]
      norm_cast
      ring_nf
    rw [step1]
    -- Now compute (a * (↑(2 * sign * R * t) * c)).re
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    -- Simplify (↑(2 * sign * R * t) * c).im
    have aux : (↑(2 * sign * R * t) * c).im = (2 * sign * R * t) * c.im := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [aux]
    -- The goal should be 2 * sign * R * t * (a.re * c.re + a.im * c.im)
    ring

  have h3 : (a * ((t : ℂ) * c) ^ 2).re =
            a.re * t^2 * (c.re^2 - c.im^2) - a.im * t^2 * 2 * c.re * c.im := by
    simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    -- Expand ((t : ℂ) * c).re and ((t : ℂ) * c).im
    have tc_re : ((t : ℂ) * c).re = t * c.re :=
      by simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have tc_im : ((t : ℂ) * c).im = t * c.im :=
      by simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    simp [tc_re, tc_im]
    -- The goal is to prove equality
    ring_nf

  rw [h1, h2, h3]
  ring_nf

  -- Use the fact that t ∈ [0,1] to bound t^2
  have ht2 : t^2 ≤ t := by
    have h_t_nonneg : 0 ≤ t := ht.1
    have h_t_le_one : t ≤ 1 := ht.2
    calc t^2 = t * t := sq t
         _ ≤ t * 1 := mul_le_mul_of_nonneg_left h_t_le_one h_t_nonneg
         _ = t := mul_one t

  -- After substitution, we have:
  -- -a.re * (sign * R)^2 - 2 * sign * R * t * (a.re * c.re - a.im * c.im)
  --   - a.re * t^2 * (c.re^2 - c.im^2) - a.im * t^2 * 2 * c.re * c.im
  -- ≤ -a.re * (sign * R)^2 / 2 + a.re * ‖c‖^2

  -- The key is to use that R > 2 * ‖c‖ / |sign|
  have hR_pos : 0 < R := by
    calc 0 < 1 := one_pos
         _ ≤ max 1 (2 * ‖c‖ / |sign|) := le_max_left _ _
         _ < R := hR

  have hsign_ne_zero : sign ≠ 0 := hsign
  have habs_sign : 0 < |sign| := abs_pos.mpr hsign_ne_zero

  -- From hR: max 1 (2 * ‖c‖ / |sign|) < R, we get 2 * ‖c‖ < R * |sign|
  have hR_bound : 2 * ‖c‖ < R * |sign| := by
    have h : 2 * ‖c‖ / |sign| < R := calc
      2 * ‖c‖ / |sign| ≤ max 1 (2 * ‖c‖ / |sign|) := le_max_right 1 (2 * ‖c‖ / |sign|)
      _ < R := hR
    calc 2 * ‖c‖ = 2 * ‖c‖ / |sign| * |sign| := by
                     rw [div_mul_cancel₀ (2 * ‖c‖) (abs_ne_zero.mpr hsign_ne_zero)]
         _ < R * |sign| := mul_lt_mul_of_pos_right h habs_sign

  -- Goal: -(a.re * (sign * R) ^ 2) - 2 * sign * R * t * (a.re * c.re - a.im * c.im) -
  --       (a.re * t ^ 2 * (c.re ^ 2 - c.im ^ 2) - a.im * t ^ 2 * 2 * c.re * c.im) ≤
  --       -(a.re * (sign * R) ^ 2) / 2 + a.re * ‖c‖ ^ 2
  -- Strategy: Use the bound on R to show that the dominant negative term -(a.re * (sign * R)^2)
  -- provides enough margin to accommodate the other terms

  -- First, let's work with the case distinction on sign
  by_cases hsign_pos : 0 < sign
  · -- Case: sign > 0
    have hsign_eq : |sign| = sign := abs_of_pos hsign_pos
    rw [hsign_eq] at hR_bound

    -- The middle term has sign * R * t * (...) where sign > 0, R > 0, t ≥ 0
    -- We need to bound |a.re * c.re - a.im * c.im|
    have cs_bound2 : |a.re * c.re - a.im * c.im| ≤ 2 * ‖a‖ * ‖c‖ := by
      have h1 : |a.re * c.re - a.im * c.im| ≤ |a.re * c.re| + |a.im * c.im| := by
        have : a.re * c.re - a.im * c.im = a.re * c.re + (-(a.im * c.im)) := by ring
        rw [this]
        trans |a.re * c.re| + |-(a.im * c.im)|
        · exact abs_add _ _
        · simp [abs_neg]
      calc |a.re * c.re - a.im * c.im| ≤ |a.re * c.re| + |a.im * c.im| := h1
           _ = |a.re| * |c.re| + |a.im| * |c.im| := by simp [abs_mul]
           _ ≤ ‖a‖ * ‖c‖ + ‖a‖ * ‖c‖ := by {
               apply add_le_add
               · have h1 : |a.re| ≤ ‖a‖ := by
                   have hsq : |a.re|^2 ≤ ‖a‖^2 := by
                     have : ‖a‖^2 = a.re^2 + a.im^2 := by
                       rw [← Complex.normSq_eq_norm_sq, Complex.normSq]
                       simp [sq]
                     rw [this, sq_abs]
                     nlinarith [sq_nonneg a.im]
                   have hsqrt : Real.sqrt (|a.re|^2) ≤ Real.sqrt (‖a‖^2) := Real.sqrt_le_sqrt hsq
                   simp only [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt
                   exact hsqrt
                 have h2 : |c.re| ≤ ‖c‖ := by
                   have hsq : |c.re|^2 ≤ ‖c‖^2 := by
                     have : ‖c‖^2 = c.re^2 + c.im^2 := by
                       rw [← Complex.normSq_eq_norm_sq, Complex.normSq]
                       simp [sq]
                     rw [this, sq_abs]
                     nlinarith [sq_nonneg c.im]
                   have hsqrt : Real.sqrt (|c.re|^2) ≤ Real.sqrt (‖c‖^2) := Real.sqrt_le_sqrt hsq
                   simp only [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt
                   exact hsqrt
                 exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
               · have h1 : |a.im| ≤ ‖a‖ := by
                   have hsq : |a.im|^2 ≤ ‖a‖^2 := by
                     have : ‖a‖^2 = a.re^2 + a.im^2 := by
                       rw [← Complex.normSq_eq_norm_sq, Complex.normSq]
                       simp [sq]
                     rw [this, sq_abs]
                     nlinarith [sq_nonneg a.re]
                   have hsqrt : Real.sqrt (|a.im|^2) ≤ Real.sqrt (‖a‖^2) := Real.sqrt_le_sqrt hsq
                   simp only [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt
                   exact hsqrt
                 have h2 : |c.im| ≤ ‖c‖ := by
                   have hsq : |c.im|^2 ≤ ‖c‖^2 := by
                     have : ‖c‖^2 = c.re^2 + c.im^2 := by
                       rw [← Complex.normSq_eq_norm_sq, Complex.normSq]
                       simp [sq]
                     rw [this, sq_abs]
                     nlinarith [sq_nonneg c.re]
                   have hsqrt : Real.sqrt (|c.im|^2) ≤ Real.sqrt (‖c‖^2) := Real.sqrt_le_sqrt hsq
                   simp only [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt
                   exact hsqrt
                 exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
             }
           _ = 2 * ‖a‖ * ‖c‖ := by ring

    have middle_bound : |2 * sign * R * t * (a.re * c.re - a.im * c.im)| ≤
                        2 * sign * R * t * (2 * ‖a‖ * ‖c‖) := by
      calc |2 * sign * R * t * (a.re * c.re - a.im * c.im)|
          = 2 * sign * R * t * |a.re * c.re - a.im * c.im| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul]
            simp only [abs_two, abs_of_pos hsign_pos, abs_of_pos hR_pos, abs_of_nonneg ht.1]
          _ ≤ 2 * sign * R * t * (2 * ‖a‖ * ‖c‖) := by
            exact mul_le_mul_of_nonneg_left cs_bound2 (mul_nonneg
              (mul_nonneg (mul_nonneg two_pos.le hsign_pos.le) hR_pos.le) ht.1)

    -- Goal: prove the main inequality
    -- We need to show that the negative terms dominate when R is large
    -- The key insight is that -a.re * (sign * R)^2 provides the dominant negative contribution

    -- Since sign > 0 and R > 2‖c‖/sign, we have sign * R > 2‖c‖
    have hR_large : sign * R > 2 * ‖c‖ := by
      calc sign * R = R * sign := by ring
           _ > 2 * ‖c‖ := hR_bound

    -- The dominant term is -a.re * (sign * R)^2
    -- We need to show it provides enough negativity to offset other terms

    -- Combine all bounds: the middle term contributes at most 4 * sign * R * t * ‖a‖ * ‖c‖
    -- The last terms contribute at most a.re * t^2 * ‖c‖^2 (using bounds on c.re^2 - c.im^2)
    -- and a.im * t^2 * 2 * ‖c‖^2 (using bounds on c.re * c.im)

    -- Using t ≤ 1 and the fact that R is large compared to ‖c‖
    -- After rw [h1, h2, h3] and ring_nf, we have:
    -- Goal: -(a.re * (sign * R) ^ 2) - 2 * sign * R * t * (a.re * c.re - a.im * c.im) -
    --       (a.re * t ^ 2 * (c.re ^ 2 - c.im ^ 2) - a.im * t ^ 2 * 2 * c.re * c.im) ≤
    --       -(a.re * (sign * R) ^ 2) / 2 + a.re * ‖c‖ ^ 2

    -- Simplify: we need to show
    -- -(a.re * (sign * R) ^ 2) / 2 ≤ 2 * sign * R * t * (a.re * c.re - a.im * c.im) +
    --                                 a.re * t ^ 2 * (c.re ^ 2 - c.im ^ 2) -
    --                                 a.im * t ^ 2 * 2 * c.re * c.im + a.re * ‖c‖ ^ 2

    -- Use our bounds
    have term1_bound : 2 * sign * R * t * (a.re * c.re - a.im * c.im) ≤
                       2 * sign * R * t * (2 * ‖a‖ * ‖c‖) := by
      have h1 : 2 * sign * R * t * (a.re * c.re - a.im * c.im) ≤
                |2 * sign * R * t * (a.re * c.re - a.im * c.im)| := by
        exact le_abs_self _
      calc 2 * sign * R * t * (a.re * c.re - a.im * c.im)
           ≤ |2 * sign * R * t * (a.re * c.re - a.im * c.im)| := h1
           _ ≤ 2 * sign * R * t * (2 * ‖a‖ * ‖c‖) := middle_bound

    -- We need more detailed bounds on the remaining terms
    -- For the term a.re * t^2 * (c.re^2 - c.im^2):
    have term2_bound : a.re * t^2 * (c.re^2 - c.im^2) ≤ a.re * t * ‖c‖^2 := by
      have h1 : t^2 ≤ t := ht2
      have h2 : c.re^2 - c.im^2 ≤ ‖c‖^2 := by
        have : c.re^2 - c.im^2 ≤ c.re^2 + c.im^2 := by linarith [sq_nonneg c.im]
        calc c.re^2 - c.im^2 ≤ c.re^2 + c.im^2 := this
             _ = ‖c‖^2 := c_norm_sq
      by_cases hc_sign : 0 ≤ c.re^2 - c.im^2
      · -- Case: c.re^2 - c.im^2 ≥ 0
        calc a.re * t^2 * (c.re^2 - c.im^2)
             ≤ a.re * t * (c.re^2 - c.im^2) := by
               apply mul_le_mul_of_nonneg_right
               · exact mul_le_mul_of_nonneg_left h1 ha.le
               · exact hc_sign
             _ ≤ a.re * t * ‖c‖^2 := by
               apply mul_le_mul_of_nonneg_left h2
               exact mul_nonneg ha.le ht.1
      · -- Case: c.re^2 - c.im^2 < 0
        push_neg at hc_sign
        calc a.re * t^2 * (c.re^2 - c.im^2)
             ≤ 0 := by
               apply mul_nonpos_of_nonneg_of_nonpos
               · -- Show a.re * t^2 ≥ 0
                 exact mul_nonneg ha.le (sq_nonneg t)
               · exact le_of_lt hc_sign
             _ ≤ a.re * t * ‖c‖^2 := by
               apply mul_nonneg
               · exact mul_nonneg ha.le ht.1
               · exact sq_nonneg _

    -- Now we need to bound the term with a.im * t^2 * 2 * c.re * c.im
    -- The main goal is to show that the dominant term -a.re * (sign * R)^2 / 2
    -- is large enough to dominate all other terms when R is sufficiently large

    -- This requires showing that for large R (specifically R > 2 * ‖c‖ / sign):
    -- -a.re * (sign * R)^2 / 2 + all positive terms ≤ -a.re * (sign * R)^2 / 2 + a.re * ‖c‖^2

    exact large_R_dominance_pos a ha c sign R t hsign_pos hR ht
  · -- Case: sign < 0
    push_neg at hsign_pos
    have hsign_neg : sign < 0 := lt_of_le_of_ne hsign_pos hsign_ne_zero
    have hsign_eq : |sign| = -sign := abs_of_neg hsign_neg
    rw [hsign_eq] at hR_bound

    exact large_R_dominance_neg a ha c sign R t hsign_neg hR ht

/-- Helper lemma for bounding the real part of complex multiplication -/
lemma complex_mul_re_bound (a : ℂ) (ha : 0 < a.re) (c : ℂ) (sign : ℝ)
    (hsign : sign ≠ 0) (R : ℝ) (hR : max 1 (2 * ‖c‖ / |sign|) < R) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (-a * ((sign * R : ℂ) + t * c)^2).re ≤ -a.re * (sign * R)^2 / 2 + a.re * ‖c‖^2 := by
  -- Expand the square
  have sq_expand : ((sign * R : ℂ) + t * c)^2 =
      (sign * R)^2 + 2 * (sign * R) * t * c + (t * c)^2 := by ring

  -- Rewrite using the expansion
  rw [sq_expand]

  -- Distribute -a over the sum
  rw [mul_add, mul_add]

  -- The goal has the form (-a * (...)).re ≤ ...
  -- but after mul_add, it becomes (-a * ... + -a * ... + -a * ...).re
  -- So we need to handle this carefully

  -- Simplify to get the real part
  simp only [Complex.add_re, neg_mul]

  -- Step 1: Calculate the real part of each term
  -- First term: (-a * (sign * R)^2).re
  have term1_calc : ((-a) * ↑((sign * R)^2)).re = -a.re * (sign * R)^2 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, neg_re]
    ring

  -- Second term: (-a * 2 * (sign * R) * t * c).re
  have term2_calc : ((-a) * (2 * ↑(sign * R) * ↑t * c)).re =
      -2 * sign * R * t * a.re * c.re + 2 * sign * R * t * a.im * c.im := by
    -- Simplify step by step
    have h1 : (2 : ℂ) * ↑(sign * R) * ↑t * c = ↑(2 * sign * R * t) * c := by
      simp only [Complex.ofReal_mul]
      push_cast
      ring
    rw [h1]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, neg_re]
    have h2 : (↑(2 * sign * R * t) * c).im = (2 * sign * R * t) * c.im := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp only [h2]
    -- (-a).im = -a.im
    have h3 : (-a).im = -a.im := by simp [neg_im]
    simp only [h3]
    -- Now we have the correct form
    ring

  -- Third term: (-a * (t * c)^2).re
  have term3_calc : ((-a) * ((↑t : ℂ) * c)^2).re =
      -t^2 * a.re * (c.re^2 - c.im^2) + t^2 * 2 * a.im * c.re * c.im := by
    have h : ((↑t : ℂ) * c)^2 = ↑(t^2) * c^2 := by
      simp [mul_pow, Complex.ofReal_pow]
    rw [h]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, neg_re]
    have c2_re : (c^2).re = c.re^2 - c.im^2 := by simp [sq, Complex.mul_re]
    have c2_im : (c^2).im = 2 * c.re * c.im := by simp [sq, Complex.mul_im]; ring
    -- Use c2_re and c2_im
    simp only [c2_re, c2_im]
    -- Expand ((↑(t^2) : ℂ) * c^2).im
    have h_im : ((↑(t^2) : ℂ) * c^2).im = t^2 * (c^2).im := by
      simp only [Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp only [h_im, c2_im]
    -- (-a).im = -a.im
    have h_neg : (-a).im = -a.im := by simp [neg_im]
    rw [h_neg]
    ring

  -- Step 2: The goal simplifies to the calculated form
  -- After simp only [Complex.add_re, neg_mul], the LHS becomes sum of real parts
  -- which equals the sum we calculated above

  -- Step 3: Apply key bounds
  -- Extract bounds from hypothesis
  have ⟨t_lo, t_hi⟩ : 0 ≤ t ∧ t ≤ 1 := ⟨ht.1, ht.2⟩

  -- From R > max 1 (2 * ‖c‖ / |sign|), get R > 2 * ‖c‖ / |sign|
  have R_bound : 2 * ‖c‖ / |sign| < R := by
    calc 2 * ‖c‖ / |sign| ≤ max 1 (2 * ‖c‖ / |sign|) := le_max_right _ _
         _ < R := hR

  -- Convert to 2 * ‖c‖ < |sign| * R
  have R_bound' : 2 * ‖c‖ < |sign| * R := by
    rw [div_lt_iff₀ (abs_pos.mpr hsign)] at R_bound
    rw [mul_comm R |sign|] at R_bound
    exact R_bound

  -- Cauchy-Schwarz bound for inner product
  have cs_bound : |a.re * c.re + a.im * c.im| ≤ ‖a‖ * ‖c‖ := by
    -- |⟨(a.re, a.im), (c.re, c.im)⟩| ≤ ‖(a.re, a.im)‖ * ‖(c.re, c.im)‖
    -- Apply the Cauchy-Schwarz inequality for real inner products
    have cs_ineq : ∀ (x₁ x₂ y₁ y₂ : ℝ),
        (x₁ * y₁ + x₂ * y₂)^2 ≤ (x₁^2 + x₂^2) * (y₁^2 + y₂^2) := by
      intro x₁ x₂ y₁ y₂
      -- This follows from (x₁y₂ - x₂y₁)² ≥ 0
      have h : 0 ≤ (x₁ * y₂ - x₂ * y₁)^2 := sq_nonneg _
      linarith [sq_nonneg x₁, sq_nonneg x₂, sq_nonneg y₁, sq_nonneg y₂]
    -- Apply to our specific values
    have h1 : (a.re * c.re + a.im * c.im)^2 ≤ (a.re^2 + a.im^2) * (c.re^2 + c.im^2) :=
      cs_ineq a.re a.im c.re c.im
    -- Take square roots
    have h2 : |a.re * c.re + a.im * c.im| ≤ Real.sqrt ((a.re^2 + a.im^2) * (c.re^2 + c.im^2)) := by
      rw [← Real.sqrt_sq (abs_nonneg _), sq_abs]
      exact Real.sqrt_le_sqrt h1
    -- Convert to norm
    have h3 : Real.sqrt ((a.re^2 + a.im^2) * (c.re^2 + c.im^2)) =
              Real.sqrt (a.re^2 + a.im^2) * Real.sqrt (c.re^2 + c.im^2) :=
      sqrt_mul_of_nonneg (add_nonneg (sq_nonneg a.re) (sq_nonneg a.im))
    rw [h3] at h2
    -- Use norm definitions
    have ha_norm : Real.sqrt (a.re^2 + a.im^2) = ‖a‖ := by
      rw [← complex_norm_eq_sqrt]
    have hc_norm : Real.sqrt (c.re^2 + c.im^2) = ‖c‖ := by
      rw [← complex_norm_eq_sqrt]
    rw [ha_norm, hc_norm] at h2
    exact h2

  -- Use c.re^2 + c.im^2 = ‖c‖^2
  have c_norm_sq : c.re^2 + c.im^2 = ‖c‖^2 := by
    rw [← Complex.normSq_eq_norm_sq c]; simp [Complex.normSq, sq]

  -- Step 4: Main inequality chain
  exact complex_real_parts_sum_bound a ha c sign hsign R hR t ht c_norm_sq

/-- Helper lemma: bound on the real part of the exponential argument -/
lemma gaussian_exp_real_part_bound (a : ℂ) (ha : 0 < a.re) (c : ℂ) (sign : ℝ)
    (hsign : sign ≠ 0) (R : ℝ) (hR : max 1 (2 * ‖c‖ / |sign|) < R) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (-a * ((sign * R : ℂ) + t * c)^2).re ≤ -a.re * (sign * R)^2 / 2 + a.re * ‖c‖^2 := by
  -- Expand the square
  have sq_expand : ((sign * R : ℂ) + t * c)^2 =
      (sign * R)^2 + 2 * (sign * R) * t * c + (t * c)^2 := by ring

  -- Extract bounds from ht
  have ⟨t_lo, t_hi⟩ : 0 ≤ t ∧ t ≤ 1 := by exact ⟨ht.1, ht.2⟩

  -- Use Complex.normSq for ‖c‖^2
  have norm_c_sq : ‖c‖^2 = c.re^2 + c.im^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    unfold Complex.normSq
    simp [sq]

  -- Component bounds for |c.re| ≤ ‖c‖ and |c.im| ≤ ‖c‖
  have c_re_bound : |c.re| ≤ ‖c‖ := by
    have h1 : |c.re|^2 ≤ ‖c‖^2 := by
      rw [norm_c_sq, sq_abs]
      nlinarith [sq_nonneg c.im]
    have h2 : Real.sqrt (|c.re|^2) ≤ Real.sqrt (‖c‖^2) := Real.sqrt_le_sqrt h1
    simp only [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2
    exact h2

  have c_im_bound : |c.im| ≤ ‖c‖ := by
    have h1 : |c.im|^2 ≤ ‖c‖^2 := by
      rw [norm_c_sq, sq_abs]
      nlinarith [sq_nonneg c.re]
    have h2 : Real.sqrt (|c.im|^2) ≤ Real.sqrt (‖c‖^2) := Real.sqrt_le_sqrt h1
    simp only [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2
    exact h2

  -- Use the helper lemma
  exact complex_mul_re_bound a ha c sign hsign R hR t ht

/-- Helper lemma: vertical integral at x = sign * R vanishes as R → ∞ -/
lemma gaussian_vertical_integral_vanish (a : ℂ) (ha : 0 < a.re) (c : ℂ) (sign : ℝ)
    (hsign : sign ≠ 0) :
    Filter.Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..(1 : ℝ),
      Complex.exp (-a * ((sign * R : ℂ) + t * c)^2) * c)
    (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ)) := by
  -- Strategy: Show that the integral tends to 0 by bounding the integrand
  -- The key insight is that exp(-a * z²) decays exponentially for large |z|
  -- Since sign ≠ 0, we can show the integral vanishes
  rw [tendsto_zero_iff_norm_tendsto_zero]

  -- We need to bound the norm of the integral and show it tends to 0
  -- Key idea: For large R, exp(-a * ((sign*R) + t*c)²) decays exponentially

  -- First, establish that for sufficiently large R, we have a good decay bound
  have decay_bound : ∃ (C : ℝ), (0 : ℝ) < C ∧ ∀ᶠ (R : ℝ) in (atTop : Filter ℝ),
      ‖∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * (((sign * R) : ℂ) + t * c)^2) * c‖ ≤
      C * Real.exp (-(a.re * (sign * R)^2 / 4)) := by
    -- The constant C will depend on ‖c‖ and other terms
    by_cases hc : c = 0
    · -- If c = 0, the integral is 0
      use 1
      constructor
      · norm_num
      · simp only [hc, mul_zero]
        filter_upwards with R
        -- When c = 0, the integral is 0, so 0 ≤ 1 * exp(...)
        simp only [intervalIntegral.integral_zero, norm_zero]
        apply mul_nonneg
        · linarith
        · apply le_of_lt
          exact Real.exp_pos _

    -- For non-zero c
    use (2 * ‖c‖ * Real.exp (2 * a.re * ‖c‖^2))
    constructor
    · apply mul_pos
      apply mul_pos
      norm_num
      exact norm_pos_iff.mpr hc
      apply Real.exp_pos
    · filter_upwards [Filter.eventually_gt_atTop (max 1 (2 * ‖c‖ / |sign|))] with R hR
      -- Use integral bounds
      calc ‖∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * ((sign * R : ℂ) + t * c)^2) * c‖
          ≤ ∫ t in (0 : ℝ)..(1 : ℝ), ‖Complex.exp (-a * ((sign * R : ℂ) + t * c)^2) * c‖ := by
            have h_cont : Continuous (fun t : ℝ => Complex.exp (-a *
                ((sign * R : ℂ) + t * c)^2) * c) := by
              apply Continuous.mul
              · apply Complex.continuous_exp.comp
                -- -a * ((sign * R : ℂ) + t * c)^2 is continuous
                have : Continuous (fun t : ℝ => -a * ((sign * R : ℂ) + t * c)^2) := by
                  apply Continuous.mul
                  · exact continuous_const  -- -a is constant
                  · apply Continuous.pow
                    apply Continuous.add
                    · exact continuous_const  -- (sign * R : ℂ) is constant
                    · apply Continuous.mul
                      · -- t ↦ (t : ℂ) is continuous
                        have : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal
                        exact this
                      · exact continuous_const  -- c is constant
                exact this
              · exact continuous_const
            have h_int := h_cont.intervalIntegrable (μ := volume) 0 1
            apply intervalIntegral.norm_integral_le_integral_norm
            exact zero_le_one
          _ = ∫ t in (0 : ℝ)..(1 : ℝ), ‖Complex.exp (-a * ((sign * R : ℂ) + t * c)^2)‖ * ‖c‖ := by
            congr 1
            ext t
            rw [Complex.norm_mul]
          _ ≤ ‖c‖ * ∫ t in (0 : ℝ)..(1 : ℝ), Real.exp (-a.re *
              (sign * R)^2 / 2 + a.re * ‖c‖^2) := by
            -- First factor out ‖c‖ from the integral on the left side
            conv_lhs => rw [intervalIntegral.integral_mul_const]
            -- Now LHS is: (∫ t, ‖exp(...)‖) * ‖c‖
            rw [mul_comm]
            -- Now LHS is: ‖c‖ * (∫ t, ‖exp(...)‖)
            -- And RHS is: ‖c‖ * (∫ t, exp(...))
            gcongr

            -- Now we need to bound the integral of the norm of the exponential
            -- Use that ‖exp(z)‖ = exp(z.re) for any complex z
            apply intervalIntegral.integral_mono_on
            · -- Show 0 ≤ 1
              norm_num
            · -- Show integrability of the left side
              apply Continuous.intervalIntegrable
              apply Continuous.norm
              apply Complex.continuous_exp.comp
              apply Continuous.mul
              · exact continuous_const
              · apply Continuous.pow
                apply Continuous.add
                · exact continuous_const
                · apply Continuous.mul
                  · exact Complex.continuous_ofReal
                  · exact continuous_const
            · -- Show integrability of the right side (constant function)
              apply Continuous.intervalIntegrable
              exact continuous_const
            · -- Main inequality: pointwise bound
              intros t ht
              -- Use ‖exp(z)‖ = exp(z.re)
              rw [Complex.norm_exp]

              -- We need to bound Re(-a * ((sign * R : ℂ) + t * c)^2)
              -- For large R, the dominant term is -a.re * (sign * R)^2
              -- We can show the bound holds for all t ∈ [0,1]

              apply Real.exp_le_exp_of_le

              exact gaussian_exp_real_part_bound a ha c sign hsign R hR t ht
          _ ≤ 2 * ‖c‖ * Real.exp (2 * a.re * ‖c‖^2) * Real.exp (-(a.re * (sign * R)^2 / 4)) := by
            rw [intervalIntegral.integral_const]
            simp only [sub_zero, one_smul]
            -- Now we have: ‖c‖ * Real.exp (-a.re * (sign * R)^2 / 2 + a.re * ‖c‖^2)

            -- Split the exponential using exp(a + b) = exp(a) * exp(b)
            rw [Real.exp_add]
            -- Now we have: ‖c‖ * (exp(-a.re * (sign * R)^2 / 2) * exp(a.re * ‖c‖^2))

            -- Rearrange to match RHS structure
            calc ‖c‖ * (Real.exp (-a.re * (sign * R)^2 / 2) * Real.exp (a.re * ‖c‖^2))
                = (‖c‖ * Real.exp (-a.re * (sign * R)^2 / 2)) * Real.exp (a.re * ‖c‖^2) := by ring
              _ ≤ (‖c‖ * Real.exp (-(a.re * (sign * R)^2 / 4))) * Real.exp (2 * a.re * ‖c‖^2) := by
                gcongr
                · -- exp(-a.re * (sign * R)^2 / 2) ≤ exp(-(a.re * (sign * R)^2 / 4))
                  -- -a.re * (sign * R)^2 / 2 ≤ -a.re * (sign * R)^2 / 4
                  -- This is equivalent to -1/2 ≤ -1/4
                  have h1 : 0 < a.re * (sign * R)^2 := by
                    apply mul_pos ha
                    apply sq_pos_of_ne_zero
                    apply mul_ne_zero hsign
                    -- R > max 1 (2 * ‖c‖ / |sign|) ≥ 1 > 0
                    have : 1 ≤ max 1 (2 * ‖c‖ / |sign|) := le_max_left _ _
                    linarith
                  linarith
                · -- exp(a.re * ‖c‖^2) ≤ exp(2 * a.re * ‖c‖^2)
                  -- a.re * ‖c‖^2 ≤ 2 * a.re * ‖c‖^2
                  nlinarith [norm_nonneg c, ha]
              _ ≤ 2 * ‖c‖ * Real.exp (2 * a.re * ‖c‖^2) *
                  Real.exp (-(a.re * (sign * R)^2 / 4)) := by
                ring_nf
                -- Need to show: x ≤ x * 2 where x = ‖c‖ * exp(...) * exp(...)
                -- This is true since x > 0 and 1 ≤ 2
                have h_pos : 0 < ‖c‖ * Real.exp (a.re * sign ^ 2 * R ^ 2 *
                    (-1 / 4)) * Real.exp (‖c‖ ^ 2 * a.re * 2) := by
                  apply mul_pos
                  apply mul_pos
                  exact norm_pos_iff.mpr hc
                  apply Real.exp_pos
                  apply Real.exp_pos
                linarith

  -- Apply the decay bound to show convergence to 0
  rcases decay_bound with ⟨C, hC_pos, bound⟩

  -- We want to show norm of integral tends to 0
  -- We have: eventually, 0 ≤ norm ≤ C * exp(...)
  -- And C * exp(...) → 0

  -- Use the squeeze theorem
  have h_limit : Tendsto (fun R => C * Real.exp (-(a.re * (sign * R)^2 / 4))) atTop (𝓝 0) := by
    have exp_decay := gaussian_exp_decay a ha sign hsign
    convert Tendsto.const_mul C exp_decay using 1
    ext R
    ring_nf

  -- Apply squeeze theorem
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ => (0 : ℝ))
    (h := fun R => C * Real.exp (-(a.re * (sign * R)^2 / 4)))
  · exact tendsto_const_nhds
  · exact h_limit
  · -- Lower bound
    filter_upwards with R
    exact norm_nonneg _
  · -- Upper bound from decay_bound
    exact bound

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

/-- Vertical integrals vanish as R → ∞ for Gaussian -/
lemma gaussian_vertical_vanish (a : ℂ) (ha : 0 < a.re) (c : ℂ) :
    let f := fun z => Complex.exp (-a * z^2)
    Filter.Tendsto (fun R : ℝ =>
      (∫ t in (0 : ℝ)..(1 : ℝ), f ((R : ℂ) + t * c) * c) -
      (∫ t in (0 : ℝ)..(1 : ℝ), f (-(R : ℂ) + t * c) * c))
    (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ)) := by
  simp only
  -- The key is to show each vertical integral decays like exp(-a.re * R^2) as R → ∞
  -- We'll bound the norm of each integral and show they tend to 0

  -- First, we need to show that each integral tends to 0 independently
  have h_right : Filter.Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..(1 : ℝ),
      Complex.exp (-a * ((R : ℂ) + t * c)^2) * c)
    (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ)) := by
    have eq : ∀ R : ℝ, ∫ t in (0 : ℝ)..(1 : ℝ),
      Complex.exp (-a * ((R : ℂ) + t * c)^2) * c =
      ∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * (((1 : ℝ) * R : ℂ) + t * c)^2) * c := by
      intro R
      congr 2
      norm_cast
      rw [one_mul]
    convert gaussian_vertical_integral_vanish a ha c 1 (one_ne_zero) using 2
    exact eq _

  have h_left : Filter.Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..(1 : ℝ),
      Complex.exp (-a * ((-(R : ℂ)) + t * c)^2) * c)
    (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ)) := by
    simp_rw [gaussian_left_vertical_eq a c]
    have h_neg_one_ne_zero : (-1 : ℝ) ≠ 0 := by norm_num
    exact gaussian_vertical_integral_vanish a ha c (-1) h_neg_one_ne_zero

  -- The difference of two functions tending to 0 also tends to 0
  have h_zero : (0 : ℂ) - 0 = 0 := by simp
  rw [← h_zero]
  exact Filter.Tendsto.sub h_right h_left

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

/--
Special case: Gaussian contour shift.
The integral of a Gaussian function exp(-a(z+c)²) over a horizontal line
equals the integral over the real axis.
-/
theorem gaussian_contour_shift_general {a : ℂ} (ha : 0 < a.re) (c : ℂ) :
    ∫ x : ℝ, Complex.exp (-a * (x + c)^2) = ∫ x : ℝ, Complex.exp (-a * x^2) := by
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

  have h_rect := fun R hR => gaussian_rectangular_contour a ha c R hR
  have h_vert_vanish := gaussian_vertical_vanish a ha c

  -- The horizontal integrals converge to the improper integrals
  have h_horiz_conv_shifted := gaussian_horizontal_conv_shifted a ha c
  have h_horiz_conv_real := gaussian_horizontal_conv_real a ha

  -- Combine the limits to conclude
  -- From h_rect, taking R → ∞:
  -- (∫ x : ℝ, f x) - (∫ x : ℝ, f (x + c)) + 0 = 0
  -- Therefore: ∫ x : ℝ, f x = ∫ x : ℝ, f (x + c)

  -- But we need to show: ∫ x, exp(-a(x+c)²) = ∫ x, exp(-ax²)
  -- Note that exp(-a(x+c)²) = f(x+c), so we have exactly what we need

  simp only [f] at *

  -- First, establish that for each R, the equation h_rect gives us a relationship
  have h_rect_rearranged : ∀ R > (0 : ℝ),
    (∫ x in (-R : ℝ)..R, Complex.exp (-a * x^2)) -
    (∫ x in (-R : ℝ)..R, Complex.exp (-a * (x + c)^2)) =
    - ((∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * ((R : ℂ) + t * c)^2) * c) -
       (∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * (-(R : ℂ) + t * c)^2) * c)) := by
    intro R hR
    have eq := h_rect R hR
    -- Rearrange: a - b + c - d = 0 implies a - b = -(c - d)
    have : (∫ x in (-R : ℝ)..R, Complex.exp (-a * x^2)) -
           (∫ x in (-R : ℝ)..R, Complex.exp (-a * (x + c)^2)) +
           ((∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * ((R : ℂ) + t * c)^2) * c) -
            (∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * (-(R : ℂ) + t * c)^2) * c)) = 0 := by
      convert eq using 1
      ring
    have rearranged : (∫ x in (-R : ℝ)..R, Complex.exp (-a * x^2)) -
                  (∫ x in (-R : ℝ)..R, Complex.exp (-a * (x + c)^2)) =
                  - ((∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * ((R : ℂ) + t * c)^2) * c) -
                      (∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * (-(R : ℂ) + t * c)^2) * c)) := by
      have h := add_eq_zero_iff_eq_neg.mp this
      exact h
    exact rearranged

  -- Define the difference function for convenience
  let diff_fn := fun R : ℝ => (∫ x in (-R : ℝ)..R, Complex.exp (-a * x^2)) -
                              (∫ x in (-R : ℝ)..R, Complex.exp (-a * (x + c)^2))

  -- The difference converges to the difference of the improper integrals
  have h_diff_conv : Filter.Tendsto diff_fn (Filter.atTop : Filter ℝ)
    (𝓝 ((∫ x : ℝ, Complex.exp (-a * x^2)) - (∫ x : ℝ, Complex.exp (-a * (x + c)^2)))) := by
    simp only [diff_fn]
    apply Filter.Tendsto.sub h_horiz_conv_real h_horiz_conv_shifted

  -- The difference also equals the negative of the vertical integrals (from h_rect_rearranged)
  have h_diff_eq_vert : ∀ᶠ R in (Filter.atTop : Filter ℝ),
    diff_fn R = - ((∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * ((R : ℂ) + t * c)^2) * c) -
                   (∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * (-(R : ℂ) + t * c)^2) * c)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    exact h_rect_rearranged R hR

  -- The vertical integrals tend to 0, so their negative also tends to 0
  have h_neg_vert : Filter.Tendsto (fun R : ℝ =>
    - ((∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * ((R : ℂ) + t * c)^2) * c) -
       (∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * (-(R : ℂ) + t * c)^2) * c)))
    (Filter.atTop : Filter ℝ) (𝓝 (-(0 : ℂ))) := by
    apply Filter.Tendsto.neg
    exact h_vert_vanish

  -- Simplify: -(0) = 0
  have h_neg_zero : -(0 : ℂ) = 0 := by simp

  -- Use uniqueness of limits
  have h_unique : (∫ x : ℝ, Complex.exp (-a * x^2)) -
      (∫ x : ℝ, Complex.exp (-a * (x + c)^2)) = 0 := by
    -- The function diff_fn converges to both the difference of integrals and to 0
    -- First, show that diff_fn eventually equals the negative of vertical integrals
    have h_conv_rewrite : Filter.Tendsto diff_fn (Filter.atTop : Filter ℝ) (𝓝 0) := by
      -- Since diff_fn eventually equals the negative of vertical integrals,
      -- and the vertical integrals tend to 0, diff_fn also tends to 0
      -- First rewrite using h_neg_zero
      rw [← h_neg_zero]
      -- Now we want to show: Tendsto diff_fn atTop (𝓝 (-0))
      -- We know diff_fn eventually equals the negative of vertical integrals
      -- Create the symmetric version of h_diff_eq_vert
      have h_eq_symm : ∀ᶠ (R : ℝ) in (Filter.atTop : Filter ℝ),
        - ((∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * ((R : ℂ) + t * c)^2) * c) -
           (∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * (-(R : ℂ) + t * c)^2) * c)) = diff_fn R := by
        filter_upwards [h_diff_eq_vert] with (R : ℝ) hR
        exact hR.symm
      apply Filter.Tendsto.congr' h_eq_symm
      exact h_neg_vert
    -- By uniqueness of limits in Hausdorff spaces
    exact tendsto_nhds_unique h_diff_conv h_conv_rewrite

  -- From the difference being 0, we get equality
  have h_eq : ∫ x : ℝ, Complex.exp (-a * x^2) = ∫ x : ℝ, Complex.exp (-a * (x + c)^2) := by
    have : (∫ x : ℝ, Complex.exp (-a * x^2)) -
      (∫ x : ℝ, Complex.exp (-a * (x + c)^2)) = 0 := h_unique
    exact sub_eq_zero.mp this

  exact h_eq.symm

/--
Specific version for our use case with real parameters.
This is the version needed for the Gaussian Fourier transform proof.
-/
theorem gaussian_contour_shift_real {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) := by
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

  -- Apply gaussian_contour_shift_general
  have h := gaussian_contour_shift_general ha_re_pos c

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

end Frourio
