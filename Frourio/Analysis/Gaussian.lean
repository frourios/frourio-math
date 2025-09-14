import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Frourio

section GaussianHelpers

open MeasureTheory Real Complex
open scoped Real ENNReal

-- Small helper to keep rewriting light inside big proofs
private lemma norm_ofReal_exp_neg_mul_sq (a t : ℝ) :
    ‖(Real.exp (-(a * t ^ 2)) : ℂ)‖ = Real.exp (-(a * t ^ 2)) := by
  have hxpos : 0 < Real.exp (-(a * t ^ 2)) := Real.exp_pos _
  simp only [Complex.norm_real]
  exact abs_of_pos hxpos

-- Direct helper matching the complex Gaussian form
private lemma norm_cexp_neg_mul_sq (a t : ℝ) :
    ‖Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))‖ = Real.exp (-(a * t ^ 2)) := by
  -- rewrite the complex exponent of a real number into `ofReal (Real.exp ...)`
  have hz_real : -((a : ℂ) * (t : ℂ) ^ 2) = (-(a * t ^ 2) : ℂ) := by
    simp [pow_two]
  have hExp : Complex.exp (-((a : ℂ) * (t : ℂ) ^ 2))
        = (Real.exp (-(a * t ^ 2)) : ℂ) := by
    simpa [hz_real] using (Complex.ofReal_exp (-(a * t ^ 2))).symm
  -- take norms; rewrite to a real exponential inside `ofReal`, then drop the norm
  rw [hExp]
  simpa using norm_ofReal_exp_neg_mul_sq a t

-- Lightweight helper to avoid heavy `simp` chains
private lemma exp_sq_eq (x : ℝ) : Real.exp x * Real.exp x = Real.exp (x + x) := by
  simpa using (Real.exp_add x x).symm

-- L² membership characterization for complex exponential functions
private lemma memLp_two_iff_integrable_sq_complex (f : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable f (volume : Measure ℝ)) :
    MemLp f 2 (volume : Measure ℝ) ↔
    Integrable (fun t => ‖f t‖ ^ (2 : ℕ)) (volume : Measure ℝ) := by
  -- Use the real-valued version on ‖f‖
  have h_norm_meas : AEStronglyMeasurable (fun t => ‖f t‖) volume := hmeas.norm
  -- Apply the real-valued lemma to ‖f‖
  have key := memLp_two_iff_integrable_sq h_norm_meas
  -- Connect MemLp f with MemLp ‖f‖ using memLp_norm_iff
  have norm_equiv : MemLp f 2 volume ↔ MemLp (fun t => ‖f t‖) 2 volume := by
    constructor
    · intro h
      refine ⟨h_norm_meas, ?_⟩
      rw [eLpNorm_norm]
      exact h.2
    · intro h
      refine ⟨hmeas, ?_⟩
      rw [← eLpNorm_norm]
      exact h.2
  rw [norm_equiv]
  exact key

lemma gaussian_memLp (a : ℝ) (ha : 0 < a) :
    MemLp (fun t : ℝ => Real.exp (-a * t^2)) 2 (volume : Measure ℝ) := by
  -- measurability
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-a * t^2)) (volume : Measure ℝ) := by
    have ht2 : Measurable fun t : ℝ => t^2 := by
      simpa [pow_two] using (measurable_id.mul measurable_id)
    have hlin : Measurable fun t : ℝ => (-a) * t^2 :=
      (measurable_const.mul ht2)
    have : Measurable fun t : ℝ => Real.exp ((-a) * t^2) :=
      Real.measurable_exp.comp hlin
    exact this.aestronglyMeasurable
  -- snorm finiteness via integrability of the square
  have hInt_sq : Integrable (fun t : ℝ => ‖Real.exp (-a * t^2)‖ ^ (2 : ℝ)) (volume : Measure ℝ) := by
    -- since the function is nonnegative real, ‖·‖ = id, and square corresponds to doubling the rate
    -- use the standard Gaussian integrability for coefficient 2a
    have hInt : Integrable (fun t : ℝ => Real.exp (-(2 * a) * t^2)) (volume : Measure ℝ) := by
      -- mathlib: integrable of Gaussian with positive coefficient
      -- placeholder: rely on library lemma
      -- integrable_exp_neg_mul_sq: ∀ a>0, Integrable (fun t => exp (-a * t^2))
      -- apply it with a := 2a
      have hpos : 0 < 2 * a := by nlinarith
      exact
        (by
          -- Use the standard library lemma for Gaussian integrability
          simpa [mul_comm] using integrable_exp_neg_mul_sq hpos)
    -- identify the squared norm with the doubled-coefficient Gaussian
    have h_eq : (fun t : ℝ => ‖Real.exp (-a * t^2)‖ ^ (2 : ℝ))
        = fun t : ℝ => Real.exp (-(2 * a) * t^2) := by
      funext t
      have hxpos : 0 < Real.exp (-a * t^2) := Real.exp_pos _
      have hn : ‖Real.exp (-a * t^2)‖ = Real.exp (-a * t^2) := by
        simpa using (abs_of_pos hxpos)
      have hsq : ‖Real.exp (-a * t^2)‖ ^ (2 : ℝ)
            = (Real.exp (-a * t^2)) ^ 2 := by
        simpa [hn, Real.rpow_two]
      have : (Real.exp (-a * t^2)) ^ 2 = Real.exp (2 * (-a * t^2)) := by
        -- Avoid heavy `simp`; unfold square, combine exponents, then normalize
        calc
          (Real.exp (-a * t^2)) ^ 2
              = Real.exp (-a * t^2) * Real.exp (-a * t^2) := by
                simp [pow_two]
          _ = Real.exp ((-a * t^2) + (-a * t^2)) := by
                exact (exp_sq_eq (-a * t^2))
          _ = Real.exp (2 * (-a * t^2)) := by
                ring_nf
      have hc : 2 * (-a) = -(2 * a) := by ring
      simpa [hsq, mul_left_comm, mul_assoc, hc] using this
    -- normalize the integrand to `-(2*a) * t^2`, then rewrite via `h_eq`
    have hInt' : Integrable (fun t : ℝ => Real.exp (-(2 * a) * t^2)) (volume : Measure ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, two_mul] using hInt
    -- adjust RHS shape to match `hInt'`
    have h_eq' : (fun t : ℝ => ‖Real.exp (-a * t^2)‖ ^ (2 : ℝ))
        = fun t : ℝ => Real.exp (-(2 * a * t^2)) := by
      funext t
      have := congrArg (fun f : ℝ → ℝ => f t) h_eq
      simpa [mul_assoc, neg_mul] using this
    -- Convert `hInt'` to the desired integrand via the pointwise identity `h_eq'`.
    -- First normalize the RHS to `-(2*a) * t^2`, then apply `h_eq`.
    have hInt''0 : Integrable (fun t : ℝ => Real.exp (-(2 * a) * t^2)) (volume : Measure ℝ) := by
      simpa [mul_assoc] using hInt'
    -- Also useful: product-of-exps equals single exp with doubled coefficient
    have h_prod : (fun t : ℝ => Real.exp (-(a * (t * t))) * Real.exp (-(a * (t * t))))
        = fun t : ℝ => Real.exp (-(2 * (a * (t * t)))) := by
      funext t
      have := exp_sq_eq (-(a * (t * t)))
      -- `exp x * exp x = exp (x + x)` then simplify `x + x = 2 * x`
      simpa [two_mul, add_comm, add_left_comm, add_assoc, mul_add, mul_left_comm, mul_assoc] using this
    have hInt'' : Integrable (fun t : ℝ => ‖Real.exp (-a * t^2)‖ ^ (2 : ℝ)) (volume : Measure ℝ) := by
      -- Rewrite the squared norm to product, then to doubled exponent via `h_prod`
      have : Integrable (fun t : ℝ => Real.exp (-(2 * (a * (t * t))))) (volume : Measure ℝ) := by
        -- reshape `hInt''0` to match, harmonizing `t^2` with `t * t`
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hInt''0
      -- now convert to the goal via `h_eq` or directly via `h_prod` and `pow_two`
      simpa [pow_two, h_prod, mul_comm, mul_left_comm, mul_assoc] using this
    exact hInt''
  -- conclude MemLp for p = 2 via integrability of the square
  -- convert from integrability of ‖f‖^2 to integrability of f^2 for real nonnegative f
  have hInt_sq_pow : Integrable (fun t : ℝ => (Real.exp (-a * t^2)) ^ 2) (volume : Measure ℝ) := by
    have hpt : (fun t : ℝ => ‖Real.exp (-a * t^2)‖ ^ (2 : ℝ))
        = (fun t : ℝ => (Real.exp (-a * t^2)) ^ 2) := by
      funext t
      have hxpos : 0 < Real.exp (-a * t^2) := Real.exp_pos _
      -- For real-valued nonnegative, ‖x‖ = x; unfold the square
      simpa [Real.rpow_two, abs_of_pos hxpos]
    simpa [hpt] using hInt_sq
  refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
  exact hInt_sq_pow

lemma gaussian_memLpC_cexp (a : ℝ) (ha : 0 < a) :
    MemLp (fun t : ℝ => Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))) 2 (volume : Measure ℝ) := by
  -- measurability for the complex Gaussian
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))) (volume : Measure ℝ) := by
    have ht2 : Measurable fun t : ℝ => (t : ℂ) ^ 2 := by
      have : Measurable fun t : ℝ => (t : ℂ) := Complex.measurable_ofReal
      simpa [pow_two] using (this.mul this)
    have hlin : Measurable fun t : ℝ => -((a : ℂ) * (t : ℂ) ^ 2) := by
      simpa [neg_mul, pow_two, mul_comm, mul_left_comm, mul_assoc] using
        ((measurable_const.mul ht2)).neg
    simpa using (Complex.measurable_exp.comp hlin).aestronglyMeasurable
  -- Integrability of the squared norm reduces to real Gaussian with doubled rate
  have hInt_sq : Integrable (fun t : ℝ => ‖Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))‖ ^ (2 : ℕ)) (volume : Measure ℝ) := by
    -- pointwise rewrite of the norm to a real exponential, then square
    have h_eq : (fun t : ℝ => ‖Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))‖ ^ (2 : ℕ))
        = (fun t : ℝ => Real.exp (-(2 * a) * t^2)) := by
      funext t
      have hnorm : ‖Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))‖ = Real.exp (-(a * t^2)) := by
        simpa [pow_two] using norm_cexp_neg_mul_sq a t
      -- square the real value inside the norm with Nat exponent
      have : (‖Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))‖ : ℝ) ^ (2 : ℕ)
            = (Real.exp (-(a * t^2))) ^ 2 := by simpa [hnorm]
      -- combine exponent laws to get doubled coefficient
      have hsq : (Real.exp (-(a * t^2))) ^ 2
            = Real.exp (-(a * t^2) + -(a * t^2)) := by
        simpa [pow_two, exp_sq_eq]
      have hadd : Real.exp (-(a * t^2) + -(a * t^2))
            = Real.exp (-(2 * a) * t^2) := by
        have : (-(a * t^2) + -(a * t^2)) = -((2 * a) * t^2) := by
          ring_nf
        simpa [this]
      simpa [hsq, hadd]
    -- integrability of the RHS by standard Gaussian lemma
    have hpos : 0 < 2 * a := by nlinarith
    have hInt : Integrable (fun t : ℝ => Real.exp (-(2 * a) * t^2)) (volume : Measure ℝ) := by
      simpa [mul_comm] using integrable_exp_neg_mul_sq hpos
    simpa [h_eq] using hInt
  -- conclude MemLp at p=2 from measurability and integrability of the square
  exact (memLp_two_iff_integrable_sq_complex _ hmeas).mpr hInt_sq

-- Pointwise identity between the complex Gaussian and the coerced real exponential
private lemma cexp_neg_mul_sq_ofReal (a t : ℝ) :
    Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2)) = (Real.exp (-(a * t^2)) : ℂ) := by
  have hz_real : -((a : ℂ) * (t : ℂ) ^ 2) = (-(a * t ^ 2) : ℂ) := by
    simp [pow_two]
  calc
    Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))
        = Complex.exp ((-(a * t^2) : ℂ)) := by simpa [hz_real]
    _   = (Real.exp (-(a * t^2)) : ℂ) := by
          simpa using (Complex.ofReal_exp (-(a * t^2))).symm

lemma gaussian_memLpC (a : ℝ) (ha : 0 < a) :
    MemLp (fun t : ℝ => (Real.exp (-a * t^2) : ℂ)) 2 (volume : Measure ℝ) := by
  -- Use the complex Gaussian version and pointwise equality
  have hC : MemLp (fun t : ℝ => Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))) 2 (volume : Measure ℝ) :=
    gaussian_memLpC_cexp a ha
  -- Measurability of the target function
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (Real.exp (-a * t^2) : ℂ)) (volume : Measure ℝ) := by
    have ht2 : Measurable fun t : ℝ => t^2 := by
      simpa [pow_two] using (measurable_id.mul measurable_id)
    have hlin : Measurable fun t : ℝ => (-a) * t^2 := (measurable_const.mul ht2)
    have hR : Measurable fun t : ℝ => Real.exp ((-a) * t^2) := Real.measurable_exp.comp hlin
    have hC : Measurable fun x : ℝ => (x : ℂ) := by simpa using Complex.measurable_ofReal
    exact (hC.comp hR).aestronglyMeasurable
  -- Transfer integrability of the square via pointwise equality of norms
  have hInt_sqC : Integrable (fun t : ℝ => ‖Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))‖ ^ (2 : ℕ)) (volume : Measure ℝ) := by
    exact (memLp_two_iff_integrable_sq_complex _ (gaussian_memLpC_cexp a ha).aestronglyMeasurable).mp hC
  have hInt_sq_ofReal : Integrable (fun t : ℝ => ‖(Real.exp (-a * t^2) : ℂ)‖ ^ (2 : ℕ)) (volume : Measure ℝ) := by
    -- pointwise equality of squared norms
    have hEq : (fun t : ℝ => ‖(Real.exp (-a * t^2) : ℂ)‖ ^ (2 : ℕ))
        = (fun t : ℝ => ‖Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))‖ ^ (2 : ℕ)) := by
      funext t
      have h1 : (Real.exp (-a * t^2)) = Real.exp (-(a * t^2)) := by ring_nf
      have hnorm1 : ‖(Real.exp (-a * t^2) : ℂ)‖ = Real.exp (-(a * t^2)) := by
        simpa [h1] using norm_ofReal_exp_neg_mul_sq a t
      have hnorm2 : ‖Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))‖ = Real.exp (-(a * t^2)) := by
        simpa [pow_two] using norm_cexp_neg_mul_sq a t
      simp [hnorm1, hnorm2]
    simpa [hEq] using hInt_sqC
  -- conclude using the `p = 2` characterization
  exact (memLp_two_iff_integrable_sq_complex _ hmeas).mpr hInt_sq_ofReal

/-- 補題B: ガウスの L² ノルム計算に用いる積分評価。
`∫ ℝ exp(-2π t² / δ²) dt = δ / √2`（δ>0）。 -/
lemma gaussian_integral_scaled (δ : ℝ) (hδ : 0 < δ) :
    (∫ t : ℝ, Real.exp (- (2 * Real.pi) * t^2 / (δ^2)) ∂(volume : Measure ℝ))
      = δ / Real.sqrt 2 := by
  -- Rewrite the integrand to the standard `exp (-(a) * t^2)` form with `a := (2π)/δ^2`.
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hδsq_pos : 0 < δ^2 := by simpa [pow_two] using mul_pos hδ hδ
  have hpos : 0 < (2 * Real.pi) / δ^2 := by
    have : 0 < 2 * Real.pi := by
      have : (0 : ℝ) < 2 := by norm_num
      exact mul_pos this Real.pi_pos
    exact div_pos this hδsq_pos
  -- Use the closed form of the Gaussian integral at parameter `(2π)/δ^2`.
  have h_val :
      (∫ t : ℝ, Real.exp (-((2 * Real.pi) / δ^2) * t ^ 2) ∂(volume : Measure ℝ))
        = Real.sqrt (Real.pi / ((2 * Real.pi) / δ^2)) := by
    simpa using integral_gaussian ((2 * Real.pi) / δ^2)
  -- Put everything together and simplify the closed form to `δ / √2`.
  have h_int_eq :
      (∫ t : ℝ, Real.exp (-(2 * Real.pi) * t ^ 2 / δ ^ 2) ∂(volume : Measure ℝ))
        = Real.sqrt (Real.pi / ((2 * Real.pi) / δ ^ 2)) := by
    -- rearrange `(- (2π) * t^2) / δ^2` as `-((2π)/δ^2) * t^2` on the integrand
    simpa [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using h_val
  -- Arithmetic simplifications inside the square root
  have h_cancel : Real.pi / ((2 * Real.pi) / δ ^ 2)
        = δ ^ 2 / 2 := by
    -- a / (b / c) = a * c / b
    calc
      Real.pi / ((2 * Real.pi) / δ ^ 2)
          = (Real.pi * δ ^ 2) / (2 * Real.pi) := by
                simpa [div_mul_eq_mul_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
      _   = (δ ^ 2) * (Real.pi / (2 * Real.pi)) := by ring_nf
      _   = (δ ^ 2) * (1 / 2) := by
                have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
                have hstep : Real.pi / (2 * Real.pi) = (Real.pi / Real.pi) / 2 := by
                  -- a/(b*c) = (a/b)/c with a=π, b=π, c=2, then commute b*c
                  simpa [mul_comm] using (div_mul_eq_div_div Real.pi Real.pi 2)
                simpa [hstep, div_self hπ]
      _   = δ ^ 2 / 2 := by ring
  -- Conclude using `sqrt (δ^2 / 2) = |δ| / √2 = δ / √2` since δ > 0.
  have : Real.sqrt (Real.pi / ((2 * Real.pi) / δ ^ 2))
        = Real.sqrt (δ ^ 2 / 2) := by simpa [h_cancel]
  calc
    (∫ t : ℝ, Real.exp (-(2 * Real.pi) * t ^ 2 / δ ^ 2) ∂(volume : Measure ℝ))
        = Real.sqrt (Real.pi / ((2 * Real.pi) / δ ^ 2)) := h_int_eq
    _ = Real.sqrt (δ ^ 2 / 2) := this
    _ = Real.sqrt (δ ^ 2) / Real.sqrt 2 := by
          have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
          simpa [Real.sqrt_div, h2nonneg]
    _ = |δ| / Real.sqrt 2 := by simpa [pow_two] using congrArg (fun x => x / Real.sqrt 2) (Real.sqrt_sq_eq_abs δ)
    _ = δ / Real.sqrt 2 := by simpa [abs_of_pos hδ]

end GaussianHelpers

end Frourio
