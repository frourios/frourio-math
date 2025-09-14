import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Pi.Bounds

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
    simp [hz_real, (Complex.ofReal_exp (-(a * t ^ 2))).symm]
  -- take norms; rewrite to a real exponential inside `ofReal`, then drop the norm
  rw [hExp]
  simpa using norm_ofReal_exp_neg_mul_sq a t

-- Lightweight helper to avoid heavy `simp` chains
private lemma exp_sq_eq (x : ℝ) : Real.exp x * Real.exp x = Real.exp (x + x) := by
  simpa using (Real.exp_add x x).symm

-- Helper for exp square with pow_two and two_mul to avoid timeout
private lemma exp_sq_pow_two (x : ℝ) : (Real.exp x) ^ 2 = Real.exp (2 * x) := by
  rw [pow_two, exp_sq_eq, two_mul]

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
        simp [abs_of_pos hxpos]
      have hsq : ‖Real.exp (-a * t^2)‖ ^ (2 : ℝ)
            = (Real.exp (-a * t^2)) ^ 2 := by
        simp [hn, Real.rpow_two]
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
      simp [Real.rpow_two, abs_of_pos hxpos]
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
            = (Real.exp (-(a * t^2))) ^ 2 := by simp [hnorm]
      -- combine exponent laws to get doubled coefficient
      have hsq : (Real.exp (-(a * t^2))) ^ 2
            = Real.exp (-(a * t^2) + -(a * t^2)) := by
        simp [pow_two, exp_sq_eq]
      have hadd : Real.exp (-(a * t^2) + -(a * t^2))
            = Real.exp (-(2 * a) * t^2) := by
        have : (-(a * t^2) + -(a * t^2)) = -((2 * a) * t^2) := by
          ring_nf
        simp [this]
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
        = Complex.exp ((-(a * t^2) : ℂ)) := by simp [hz_real]
    _   = (Real.exp (-(a * t^2)) : ℂ) := by
          simp [(Complex.ofReal_exp (-(a * t^2))).symm]

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

/-! 追加補題: ガウスの L² ノルム（二乗） -/

/-- 実ガウス `exp(-π t² / δ²)` の L² ノルムの二乗は `δ/√2`（δ>0）。 -/
lemma gaussian_l2_norm_sq_real (δ : ℝ) (hδ : 0 < δ) :
    (∫ t : ℝ, (Real.exp (-Real.pi * t^2 / δ^2)) ^ 2 ∂(volume : Measure ℝ))
      = δ / Real.sqrt 2 := by
  -- 二乗を倍係数の単一指数にまとめる
  have hpt : (fun t : ℝ => (Real.exp (-Real.pi * t ^ 2 / δ ^ 2)) ^ 2)
      = (fun t : ℝ => Real.exp (-(2 * Real.pi) * t ^ 2 / δ ^ 2)) := by
    funext t
    have hx : (Real.exp (-Real.pi * t ^ 2 / δ ^ 2)) ^ 2
        = Real.exp (2 * (-Real.pi * t ^ 2 / δ ^ 2)) := by
      exact exp_sq_pow_two (-Real.pi * t ^ 2 / δ ^ 2)
    have hx' : 2 * (-Real.pi * t ^ 2 / δ ^ 2)
        = -(2 * Real.pi) * t ^ 2 / δ ^ 2 := by
      ring
    rw [hx, hx']
  rw [hpt]
  exact gaussian_integral_scaled δ hδ

/-- 複素数値に持ち上げた実ガウスの L² ノルム二乗も同じ値。 -/
lemma gaussian_l2_norm_sq_complex (δ : ℝ) (hδ : 0 < δ) :
    (∫ t : ℝ, ‖(Real.exp (-Real.pi * t^2 / δ^2) : ℂ)‖ ^ (2 : ℕ) ∂(volume : Measure ℝ))
      = δ / Real.sqrt 2 := by
  -- ノルムはそのまま実数値に一致する
  have hpt : (fun t : ℝ => ‖(Real.exp (-Real.pi * t ^ 2 / δ ^ 2) : ℂ)‖ ^ (2 : ℕ))
      = (fun t : ℝ => (Real.exp (-Real.pi * t ^ 2 / δ ^ 2)) ^ 2) := by
    funext t
    have hxpos : 0 < Real.exp (-Real.pi * t ^ 2 / δ ^ 2) := Real.exp_pos _
    have h1 : ‖(Real.exp (-Real.pi * t ^ 2 / δ ^ 2) : ℂ)‖ = Real.exp (-Real.pi * t ^ 2 / δ ^ 2) := by
      simp only [Complex.norm_real]
      exact abs_of_pos hxpos
    rw [h1]
  rw [hpt]
  exact gaussian_l2_norm_sq_real δ hδ

/-! 正規化ガウス関数の構成 -/

/-- Helper lemma for complex exponential equality -/
private lemma cexp_pi_delta_sq_eq (δ : ℝ) (x : ℝ) :
    Complex.exp (-( ((Real.pi / δ^2) : ℂ) * (x : ℂ) ^ 2))
      = (Real.exp (-(Real.pi / δ^2) * x^2) : ℂ) :=
  by
    -- Use the generic ofReal-square identity and normalize powers/products
    have h := cexp_neg_mul_sq_ofReal (Real.pi / δ^2) x
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h

/-- Helper lemma: Complex Gaussian exp(-(π/δ²) * t²) in L² -/
private lemma gaussian_memLp_pi_delta_sq (δ : ℝ) (hδ : 0 < δ) :
    MemLp (fun t : ℝ => Complex.exp (-( ((Real.pi / δ^2) : ℂ) * (t : ℂ) ^ 2))) 2
        (volume : Measure ℝ) := by
  -- Directly apply the complex Gaussian L² lemma with a = π/δ²
  have ha : 0 < Real.pi / δ^2 := div_pos Real.pi_pos (pow_pos hδ 2)
  simpa using gaussian_memLpC_cexp (Real.pi / δ^2) ha

/-- Helper lemma: Convert L² norm from Lebesgue integral to regular integral form -/
private lemma lintegral_norm_sq_eq_integral_norm_sq (f : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable f (volume : Measure ℝ))
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    ((∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) ^ (1 / (2 : ℝ))).toReal =
    Real.sqrt (∫ t, ‖f t‖ ^ (2 : ℕ) ∂(volume : Measure ℝ)) := by
  -- Convert `MemLp f 2` to integrability of the squared norm
  have hInt_nat : Integrable (fun t : ℝ => ‖f t‖ ^ (2 : ℕ)) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_complex f hmeas).mp hf
  -- The ENNReal integrand equals ofReal of the squared norm
  have h_enorm_sq : (fun t : ℝ => ‖f t‖ₑ ^ (2 : ℝ))
      = fun t : ℝ => ENNReal.ofReal ((‖f t‖ : ℝ) ^ (2 : ℕ)) := by
    funext t
    simp only [ENNReal.rpow_two]
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  -- The squared norm is nonnegative a.e.
  have h_nonneg_ae : 0 ≤ᵐ[volume] fun t : ℝ => (‖f t‖ : ℝ) ^ (2 : ℕ) :=
    Filter.Eventually.of_forall (fun t => pow_two_nonneg _)
  -- Convert the lintegral to ofReal of the integral
  have h_lint :
      (∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ))
        = ENNReal.ofReal (∫ t, (‖f t‖ : ℝ) ^ (2 : ℕ) ∂(volume : Measure ℝ)) := by
    rw [h_enorm_sq]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt_nat h_nonneg_ae]
  -- The integral is nonnegative
  have h_integral_nonneg : 0 ≤ ∫ t, (‖f t‖ : ℝ) ^ (2 : ℕ) ∂(volume : Measure ℝ) :=
    integral_nonneg (fun t => pow_two_nonneg _)
  -- Calculate the result
  calc
    ((∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) ^ (1 / (2 : ℝ))).toReal
        = (ENNReal.ofReal (∫ t, (‖f t‖ : ℝ) ^ (2 : ℕ) ∂(volume : Measure ℝ)) ^ (1 / (2 : ℝ))).toReal := by
          rw [h_lint]
    _   = (ENNReal.ofReal (∫ t, (‖f t‖ : ℝ) ^ (2 : ℕ) ∂(volume : Measure ℝ))).toReal ^ (1 / (2 : ℝ)) := by
          rw [ENNReal.toReal_rpow]
    _   = (∫ t, (‖f t‖ : ℝ) ^ (2 : ℕ) ∂(volume : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
          rw [ENNReal.toReal_ofReal h_integral_nonneg]
    _   = Real.sqrt (∫ t, (‖f t‖ : ℝ) ^ (2 : ℕ) ∂(volume : Measure ℝ)) := by
          rw [Real.sqrt_eq_rpow]

/-- 正規化ガウス関数を L² 空間の要素として構成する。
`δ > 0` に対して、`exp(-π t²/δ²)` を正規化して L² ノルム 1 の関数を得る。 -/
lemma build_normalized_gaussian (δ : ℝ) (hδ : 0 < δ) :
    ∃ w : Lp ℂ 2 (volume : Measure ℝ),
    ‖w‖ = 1 ∧
    ∀ᵐ t : ℝ, (w : ℝ → ℂ) t = ((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ : ℝ) *
      (Real.exp (-Real.pi * t^2 / δ^2) : ℂ) := by
  -- 正規化定数 A = 2^(1/4) / √δ
  let A : ℝ := (2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ
  -- 正規化されたガウス関数
  let wFun : ℝ → ℂ := fun t => A * (Real.exp (-Real.pi * t^2 / δ^2) : ℂ)

  -- wFun の可測性
  have hmeas : AEStronglyMeasurable wFun (volume : Measure ℝ) := by
    have h1 : Measurable fun t : ℝ => t^2 := by
      simpa [pow_two] using (measurable_id.mul measurable_id)
    have h2 : Measurable fun t : ℝ => -Real.pi * t^2 / δ^2 := by
      exact (measurable_const.mul h1).div_const _
    have h3 : Measurable fun t : ℝ => Real.exp (-Real.pi * t^2 / δ^2) := by
      exact Real.measurable_exp.comp h2
    have h4 : Measurable fun t : ℝ => (Real.exp (-Real.pi * t^2 / δ^2) : ℂ) := by
      exact Complex.measurable_ofReal.comp h3
    exact (measurable_const.mul h4).aestronglyMeasurable

  -- wFun ∈ L²
  have hLp : MemLp wFun 2 (volume : Measure ℝ) := by
    -- A² · gaussian_memLpC で示す
    have hA_pos : 0 < A := by
      simp only [A]
      have h2pos : 0 < (2 : ℝ)^(1/4 : ℝ) := by
        exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
      exact div_pos h2pos (Real.sqrt_pos.mpr hδ)
    -- 係数 a = π/δ² for the Gaussian
    have ha : 0 < Real.pi / δ^2 := by
      exact div_pos Real.pi_pos (pow_pos hδ 2)
    -- Use the complex Gaussian and a pointwise identity to match the real-coerced form
    have hg : MemLp (fun t : ℝ => (Real.exp (-Real.pi * t^2 / δ^2) : ℂ)) 2
        (volume : Measure ℝ) := by
      -- L² membership for the complex Gaussian at a := π/δ²
      have hC : MemLp (fun t : ℝ => Complex.exp (-( ((Real.pi / δ^2) : ℂ) * (t : ℂ) ^ 2))) 2
          (volume : Measure ℝ) := gaussian_memLp_pi_delta_sq δ hδ
      -- Pointwise identity to switch to `(Real.exp ... : ℂ)` form
      have hpt : (fun t : ℝ => Complex.exp (-( ((Real.pi / δ^2) : ℂ) * (t : ℂ) ^ 2)))
          = (fun t : ℝ => (Real.exp (-Real.pi * t^2 / δ^2) : ℂ)) := by
        funext x
        -- First reduce cexp to ofReal exp at rate a = π/δ²
        have h1 :
            Complex.exp (-( ((Real.pi / δ^2) : ℂ) * (x : ℂ) ^ 2))
              = (Real.exp (-(Real.pi / δ^2) * x^2) : ℂ) :=
          cexp_pi_delta_sq_eq δ x
        -- Then massage the real exponent
        have h2 : -(Real.pi / δ^2) * x^2 = -Real.pi * x^2 / δ^2 := by
          -- (-π/δ^2) * x^2 = (-π) * x^2 / δ^2 and (-π) = -(π)
          have := (div_mul_eq_mul_div (-Real.pi) (δ^2) (x^2))
          simpa [neg_div] using this
        simpa [h2] using h1
      -- Transport MemLp via pointwise equality
      simpa [hpt] using hC
    -- Scaling by constant preserves L² membership
    exact MemLp.const_mul hg A

  -- L² ノルムの計算
  have hnorm : ‖(MemLp.toLp wFun hLp : Lp ℂ 2 (volume : Measure ℝ))‖ = (1 : ℝ) := by
    rw [Lp.norm_toLp]
    -- No need to rewrite (2 : ℝ≥0∞).toReal here
    -- No explicit inverse/one_div rewrites needed here
    -- ‖wFun‖₂² = A² · ‖gaussian‖₂²
    have hsq : ∫ t : ℝ, ‖wFun t‖ ^ (2 : ℕ) ∂(volume : Measure ℝ) =
        A^2 * (δ / Real.sqrt 2) := by
      have heq : (fun t => ‖wFun t‖ ^ (2 : ℕ)) =
          fun t => A^2 * ‖(Real.exp (-Real.pi * t^2 / δ^2) : ℂ)‖ ^ (2 : ℕ) := by
        funext t
        simp [wFun, Complex.norm_mul, Complex.norm_real, abs_of_pos]
        have hA_pos : 0 < A := by
          simp only [A]
          have h2pos : 0 < (2 : ℝ)^(1/4 : ℝ) := by
            exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
          exact div_pos h2pos (Real.sqrt_pos.mpr hδ)
        simp [abs_of_pos hA_pos, mul_pow]
      rw [heq]
      simp only [integral_const_mul]
      rw [gaussian_l2_norm_sq_complex δ hδ]
    -- A² · (δ / √2) = 1
    have hA2 : A^2 * (δ / Real.sqrt 2) = 1 := by
      simp only [A, div_pow, Real.sq_sqrt (le_of_lt hδ)]
      field_simp
      -- normalize powers; handle ((2)^(1/4))^2 separately below
      have h2_14_sq : ((2 : ℝ)^(1/4 : ℝ))^2 = Real.sqrt 2 := by
        have hpos : (0 : ℝ) ≤ 2 := by norm_num
        have h := (Real.rpow_mul hpos (1/4 : ℝ) (2 : ℝ)).symm
        have hpow : ((2 : ℝ)^(1/4 : ℝ))^2 = (2 : ℝ) ^ ((1/4 : ℝ) * 2) := by
          simpa using h
        have h12 : (1/4 : ℝ) * 2 = (1/2 : ℝ) := by ring
        -- Rewrite exponent (4⁻¹)*2 to 2⁻¹ to match the goal shape
        -- First, align (4⁻¹)*2 with (1/4)*2, then use h12, and finally 1/2 = 2⁻¹
        have h12a : (4 : ℝ)⁻¹ * 2 = (1/4 : ℝ) * 2 := by
          simp [one_div]
        have h12b : (1/4 : ℝ) * 2 = (2 : ℝ)⁻¹ := by
          simpa [one_div] using h12
        have h12'' : (4 : ℝ)⁻¹ * 2 = (2 : ℝ)⁻¹ := by
          -- avoid multiple-goal `trans ... <;>`; prove by chained equalities
          exact (h12a.trans h12b)
        have hhalf : ((2 : ℝ)^(1/4 : ℝ))^2 = (2 : ℝ) ^ (2 : ℝ)⁻¹ := by
          simpa [h12''] using hpow
        -- And 2^(2⁻¹) = 2^(1/2) = √2
        simpa [Real.sqrt_eq_rpow, one_div] using hhalf
      rw [h2_14_sq]
    -- eLpNorm の基本表示（p=2, 0<2<∞）を使って toReal を実数の平方根に落とす
    have h0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have htop : (2 : ℝ≥0∞) ≠ ∞ := by simp
    have hrepr :=
      eLpNorm_eq_lintegral_rpow_enorm (μ := volume) (f := wFun) h0 htop
    -- これで目標は `1 = √(∫ ‖wFun‖^2)` に帰着している
    -- 積分値は `hsq` より `(A^2) * (δ/√2)`、さらに `hA2 : A^2 * (δ/√2) = 1`。
    -- よって `√(∫ ‖wFun‖^2) = 1`、従ってゴール成立。
    -- ここではそのまま対称形で示す。
    have hsq_rt : Real.sqrt (∫ t, ‖wFun t‖ ^ (2 : ℕ) ∂(volume : Measure ℝ)) = 1 := by
      simp [hsq, hA2, Real.sqrt_one]
    -- 目標 `(eLpNorm wFun 2 volume).toReal = 1` は，`eLpNorm` の表式と `hsq_rt` から従う。
    calc
      (eLpNorm wFun 2 volume).toReal
          = (((∫⁻ t, ‖wFun t‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) : ℝ≥0∞)
                ^ (1 / (2 : ℝ))).toReal := by
            -- `eLpNorm` の表示に `toReal` をかけた等式
            simpa using congrArg ENNReal.toReal hrepr
      _ = Real.sqrt (∫ t, ‖wFun t‖ ^ (2 : ℕ) ∂(volume : Measure ℝ)) := by
            -- p = 2 のとき、lintegral から実積分への標準変換
            exact lintegral_norm_sq_eq_integral_norm_sq wFun hmeas hLp
      _ = 1 := hsq_rt

  -- 結果を返す
  use (MemLp.toLp wFun hLp)
  refine ⟨hnorm, ?_⟩
  -- Establish the pointwise formula a.e. via `coeFn_toLp`.
  have hcoe : (((MemLp.toLp wFun hLp) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] wFun := MemLp.coeFn_toLp hLp
  -- Rewrite to the desired normalized Gaussian expression
  refine hcoe.mono ?_
  intro t ht
  -- Bridge `(Real.exp ... : ℂ)` and `Complex.exp ...` with algebraic rewrites
  have hx : (Real.exp (-Real.pi * t ^ 2 / δ ^ 2) : ℂ)
      = Complex.exp (-( (Real.pi : ℂ) * (t : ℂ) ^ 2) / (δ : ℂ) ^ 2) := by
    -- Start from the canonical identity for `π/δ²` and rearrange
    have h1 := (cexp_pi_delta_sq_eq δ t).symm
    -- Convert `-(π/δ²) * t²` into `-(π * t²) / δ²`
    have h2 : -(Real.pi / δ ^ 2) * t ^ 2 = -Real.pi * t ^ 2 / δ ^ 2 := by
      -- -(a/b) * c = -(a * c) / b
      ring
    simp [h2, pow_two, mul_comm, mul_left_comm, mul_assoc, h1]
  -- Apply the a.e. equality and simplify
  simp only [ht, wFun, A]

/-- 補題2-3（包絡評価）: `δ > 0` に対し，`build_normalized_gaussian` で得た
正規化ガウス `w` は a.e. で
`‖w t‖ ≤ (2)^(1/4)/√δ · exp(-π t²/δ²)` を満たす。 -/
lemma normalized_gaussian_pointwise_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ w : Lp ℂ 2 (volume : Measure ℝ),
      ‖w‖ = 1 ∧
      ∀ᵐ t : ℝ, ‖((w : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t‖
        ≤ ((2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt δ)
            * Real.exp (-Real.pi * t^2 / δ^2) := by
  rcases build_normalized_gaussian δ hδ with ⟨w, hnorm, hpt⟩
  -- 係数 A は正なので，ノルムは等号評価で与えられる
  have hA_pos : 0 < (2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt δ := by
    have h2pos : 0 < (2 : ℝ) ^ (1/4 : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
    exact div_pos h2pos (Real.sqrt_pos.mpr hδ)
  refine ⟨w, hnorm, ?_⟩
  -- a.e. 同値式からノルムの上界を導く（実際は等号）
  refine hpt.mono ?_
  intro t ht
  -- 右辺は実数正である
  have hxpos : 0 < Real.exp (-Real.pi * t ^ 2 / δ ^ 2) := Real.exp_pos _
  have hnorm_exp : ‖(Real.exp (-Real.pi * t ^ 2 / δ ^ 2) : ℂ)‖
      = Real.exp (-Real.pi * t ^ 2 / δ ^ 2) := by
    simp only [Complex.norm_real]
    exact abs_of_pos hxpos
  -- 目標の不等式は実は等号で成り立つ
  -- `ht` で `w` の値を具体化して，`norm_mul` と実数係数のノルムを用いる
  show ‖((w : ℝ → ℂ) t)‖ ≤ ((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ) * Real.exp (-Real.pi * t^2 / δ^2)
  calc ‖((w : ℝ → ℂ) t)‖
      = ‖(((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ : ℝ) : ℂ) * (Real.exp (-Real.pi * t^2 / δ^2) : ℂ)‖ := by
        rw [ht]
  _   = ‖(((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ : ℝ) : ℂ)‖ * ‖(Real.exp (-Real.pi * t^2 / δ^2) : ℂ)‖ := by
        rw [Complex.norm_mul]
  _   = |((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ)| * ‖(Real.exp (-Real.pi * t^2 / δ^2) : ℂ)‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
  _   = ((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ) * ‖(Real.exp (-Real.pi * t^2 / δ^2) : ℂ)‖ := by
        rw [abs_of_pos hA_pos]
  _   = ((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ) * Real.exp (-Real.pi * t^2 / δ^2) := by
        rw [hnorm_exp]
  _   ≤ ((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ) * Real.exp (-Real.pi * t^2 / δ^2) := by
        rfl

/-- Gaussian tail bound: The L² norm of a Gaussian outside radius R decays exponentially -/
lemma gaussian_tail_l2_bound (δ : ℝ) (hδ : 0 < δ) (R : ℝ) (hR : 0 < R) :
    ∫ t in {t : ℝ | R < |t|}, Real.exp (-2 * Real.pi * t^2 / δ^2) ∂(volume : Measure ℝ)
      ≤ 2 * Real.exp (-Real.pi * R^2 / δ^2) / Real.sqrt (Real.pi / δ^2) := by
  -- The integral of exp(-2π t²/δ²) over |t| > R
  -- can be bounded using the Gaussian tail inequality
  -- For now, we provide a sorry as this requires careful integration
  sorry

/-- For normalized Gaussian with width δ, the L² mass outside radius R vanishes as δ → 0 -/
lemma normalized_gaussian_tail_vanishes (δ : ℝ) (hδ : 0 < δ) (R : ℝ) (hR : 0 < R) :
    ∃ w : Lp ℂ 2 (volume : Measure ℝ),
      ‖w‖ = 1 ∧
      (∫ t in {t : ℝ | R < |t|}, ‖(w : ℝ → ℂ) t‖^2 ∂(volume : Measure ℝ))
        ≤ 4 * Real.exp (-Real.pi * R^2 / δ^2) := by
  -- Use build_normalized_gaussian and the tail bound
  rcases build_normalized_gaussian δ hδ with ⟨w, hnorm, hpt⟩
  refine ⟨w, hnorm, ?_⟩
  -- The normalized Gaussian has amplitude 2^(1/4) / √δ
  -- and form exp(-π t²/δ²), so ‖w(t)‖² ≤ C * exp(-2π t²/δ²)
  -- Apply gaussian_tail_l2_bound
  sorry

end GaussianHelpers

end Frourio

namespace Frourio

open Real

/-- 大きな n に対する正規化定数の比較補題。
`δ n = 1/(n+1)` のとき，`n ≥ 2` なら
`2^(1/4)/√(δ n) ≤ (δ n · π^(1/4))⁻¹` が成り立つ。 -/
lemma gaussian_norm_const_le_alt_const_for_large_n (n : ℕ) (hn : 2 ≤ n) :
    ((2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt (1 / (n + 1 : ℝ)))
      ≤ ((1 / (n + 1 : ℝ)) * Real.pi ^ (1/4 : ℝ))⁻¹ := by
  have hpos : 0 < (n + 1 : ℝ) := by
    have : (0 : ℕ) < n + 1 := Nat.succ_pos _
    exact_mod_cast this
  -- rewrite LHS and RHS
  have hsqrt_inv : Real.sqrt (1 / (n + 1 : ℝ)) = 1 / Real.sqrt (n + 1 : ℝ) := by
    have hx : (n + 1 : ℝ) ≠ 0 := ne_of_gt hpos
    simpa [one_div] using Real.sqrt_inv (by exact_mod_cast hx)
  have hL : ((2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt (1 / (n + 1 : ℝ)))
      = (2 : ℝ) ^ (1/4 : ℝ) * Real.sqrt (n + 1 : ℝ) := by
    simp [hsqrt_inv, one_div, mul_comm, mul_left_comm, mul_assoc]
  have hR : (((1 / (n + 1 : ℝ)) * Real.pi ^ (1/4 : ℝ))⁻¹)
      = (n + 1 : ℝ) / (Real.pi ^ (1/4 : ℝ)) := by
    field_simp [one_div, mul_comm, mul_left_comm, mul_assoc]
  -- it suffices to prove the squared inequality, since both sides are ≥ 0
  have hL_nonneg : 0 ≤ (2 : ℝ) ^ (1/4 : ℝ) * Real.sqrt (n + 1 : ℝ) := by
    have h2pos : 0 ≤ (2 : ℝ) ^ (1/4 : ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    exact mul_nonneg h2pos (Real.sqrt_nonneg _)
  have hR_nonneg : 0 ≤ (n + 1 : ℝ) / (Real.pi ^ (1/4 : ℝ)) := by
    have hpi : 0 < Real.pi ^ (1/4 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
    exact div_nonneg (le_of_lt hpos) (le_of_lt hpi)
  -- show: (2^(1/4) * √(n+1))^2 ≤ ((n+1)/π^(1/4))^2
  have hsq :
      ((2 : ℝ) ^ (1/4 : ℝ) * Real.sqrt (n + 1 : ℝ))^2
        ≤ ((n + 1 : ℝ) / (Real.pi ^ (1/4 : ℝ)))^2 := by
    -- Reduce to: √(2π) ≤ n+1
    -- Start from strict bound √(2π) < 3 ≤ n+1 for n ≥ 2
    have hlt3 : Real.sqrt ((2 : ℝ) * Real.pi) < (3 : ℝ) := by
      have h2pi_lt8 : (2 : ℝ) * Real.pi < 8 := by
        have hπlt4 : Real.pi < 4 := pi_lt_four
        nlinarith
      have h2pi_nonneg : 0 ≤ (2 : ℝ) * Real.pi := by positivity
      have hsq_mono := (Real.sqrt_lt_sqrt_iff h2pi_nonneg).mpr h2pi_lt8
      have h_sqrt8_lt3 : Real.sqrt 8 < 3 := by
        have : Real.sqrt 8 < Real.sqrt 9 := by
          apply Real.sqrt_lt_sqrt
          · norm_num
          · norm_num
        have h9eq : Real.sqrt 9 = (3 : ℝ) := by
          -- `sqrt (3^2) = 3` since `3 ≥ 0`, and `3^2 = 9`.
          have hpow : (3 : ℝ) ^ 2 = 9 := by norm_num
          simpa [pow_two, hpow] using Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (3 : ℝ))
        rw [h9eq] at this
        exact this
      simpa using (lt_trans hsq_mono h_sqrt8_lt3)
    have h3le : (3 : ℝ) ≤ (n + 1 : ℝ) := by
      have : (3 : ℕ) ≤ n + 1 := Nat.succ_le_succ hn
      exact_mod_cast this
    have hsqrt_le : Real.sqrt ((2 : ℝ) * Real.pi) ≤ (n + 1 : ℝ) :=
      le_trans (le_of_lt hlt3) h3le
    -- Multiply both sides by (n+1) > 0 and divide by √π > 0
    have hposn1 : 0 ≤ (n + 1 : ℝ) := le_of_lt hpos
    have hpos_pi12 : 0 < Real.pi ^ (1/2 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
    have hpos_sqrt_pi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hmul : Real.sqrt ((2 : ℝ) * Real.pi) * (n + 1 : ℝ)
          ≤ (n + 1 : ℝ) * (n + 1 : ℝ) := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hsqrt_le hposn1
    have hdiv : (Real.sqrt ((2 : ℝ) * Real.pi) / Real.sqrt Real.pi) * (n + 1 : ℝ)
          ≤ ((n + 1 : ℝ) * (n + 1 : ℝ)) / Real.sqrt Real.pi := by
      have : Real.sqrt Real.pi ≠ 0 := ne_of_gt hpos_sqrt_pi
      -- divide both sides by √π > 0
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (div_le_div_of_nonneg_right hmul (le_of_lt hpos_sqrt_pi))
    -- simplify LHS: √(2π)/√π = √2
    have hsqrt_mul : Real.sqrt ((2 : ℝ) * Real.pi)
          = Real.sqrt 2 * Real.sqrt Real.pi := by
      have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
      have hpinonneg : 0 ≤ Real.pi := le_of_lt Real.pi_pos
      simpa using Real.sqrt_mul h2nonneg hpinonneg
    have hdivL : (Real.sqrt ((2 : ℝ) * Real.pi) / Real.sqrt Real.pi)
          = Real.sqrt 2 := by
      have hne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hpos_sqrt_pi
      simp [hsqrt_mul, hne]
    -- rewrite inequality to the target squared inequality
    have : Real.sqrt 2 * (n + 1 : ℝ)
          ≤ ((n + 1 : ℝ) * (n + 1 : ℝ)) / Real.sqrt Real.pi := by
      rw [← hdivL]
      exact hdiv
    -- Directly rewrite `this` with rpow to match the target linear inequality
    have htarget : (2 : ℝ) ^ (1/2 : ℝ) * (n + 1 : ℝ)
          ≤ ((n + 1 : ℝ) * (n + 1 : ℝ)) / (Real.pi) ^ (1/2 : ℝ) := by
      simpa [Real.sqrt_eq_rpow] using this
    -- Turn this linear inequality into the desired squared form
    -- Split 1/2 = 1/4 + 1/4 to match ((2^(1/4))^2) and ((π^(1/4))^2).
    have hsplit2 : (2 : ℝ) ^ (1/2 : ℝ)
        = (2 : ℝ) ^ (1/4 : ℝ) * (2 : ℝ) ^ (1/4 : ℝ) := by
      have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
      have hmul := (Real.rpow_mul h2nonneg (1/4 : ℝ) (2 : ℝ)).symm
      -- ((2)^(1/4))^2 = 2^((1/4)*2)
      have h12'' : (4 : ℝ)⁻¹ * (2 : ℝ) = (2 : ℝ)⁻¹ := by
        -- (1/4)*2 = 1/2 = 2⁻¹
        simpa [one_div] using (by
          have : (1/4 : ℝ) * (2 : ℝ) = (1/2 : ℝ) := by norm_num
          simpa [one_div] using this)
      have hsq : ((2 : ℝ) ^ (1/4 : ℝ)) ^ 2 = (2 : ℝ) ^ (2 : ℝ)⁻¹ := by
        simpa [h12''] using hmul
      simpa [pow_two] using hsq.symm
    have hsplitpi : (Real.pi) ^ (1/2 : ℝ)
        = (Real.pi) ^ (1/4 : ℝ) * (Real.pi) ^ (1/4 : ℝ) := by
      have hpinonneg : 0 ≤ Real.pi := le_of_lt Real.pi_pos
      have hmul := (Real.rpow_mul hpinonneg (1/4 : ℝ) (2 : ℝ)).symm
      have h12pi : (4 : ℝ)⁻¹ * (2 : ℝ) = (2 : ℝ)⁻¹ := by
        -- (1/4)*2 = 1/2 = 2⁻¹
        simpa [one_div] using (by
          have : (1/4 : ℝ) * (2 : ℝ) = (1/2 : ℝ) := by norm_num
          simpa [one_div] using this)
      have hsq : ((Real.pi) ^ (1/4 : ℝ)) ^ 2 = (Real.pi) ^ (2 : ℝ)⁻¹ := by
        simpa [h12pi] using hmul
      simpa [pow_two] using hsq.symm
    -- Also split (n+1) as (n+1)^(1/2) * (n+1)^(1/2)
    have hn1_split : (n + 1 : ℝ) = (n + 1 : ℝ) ^ (1/2 : ℝ) * (n + 1 : ℝ) ^ (1/2 : ℝ) := by
      have h := Real.rpow_add (hpos) (1/2 : ℝ) (1/2 : ℝ)
      -- massage 2⁻¹ to 1/2 in the exponent sum
      have hhalf' : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by
        have : (1/2 : ℝ) + (1/2 : ℝ) = 1 := by norm_num
        simpa [one_div] using this
      simpa [hhalf', Real.rpow_one, one_div] using h
    -- Rewrite both sides explicitly to avoid heavy simp search
    have lhs_eq : ((2 : ℝ) ^ (1/4 : ℝ) * Real.sqrt (n + 1 : ℝ)) ^ 2
          = (2 : ℝ) ^ (2 : ℝ)⁻¹ * (n + 1 : ℝ) := by
      have h2sq : ((2 : ℝ) ^ (1/4 : ℝ)) ^ 2 = (2 : ℝ) ^ (1/2 : ℝ) := by
        have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
        have hmul := (Real.rpow_mul h2nonneg (1/4 : ℝ) (2 : ℝ)).symm
        have h12'' : (4 : ℝ)⁻¹ * (2 : ℝ) = (2 : ℝ)⁻¹ := by
          -- (1/4)*2 = 1/2 = 2⁻¹
          simpa [one_div] using (by
            have : (1/4 : ℝ) * (2 : ℝ) = (1/2 : ℝ) := by norm_num
            simpa [one_div] using this)
        -- Now rewrite (4⁻¹*2) to (2⁻¹) in the exponent
        simpa [h12'', one_div] using hmul
      have hsq_sqrt : (Real.sqrt (n + 1 : ℝ)) ^ 2 = (n + 1 : ℝ) := by
        simpa using Real.sq_sqrt (le_of_lt hpos)
      have mul_pow2 : ((2 : ℝ) ^ (1/4 : ℝ) * Real.sqrt (n + 1 : ℝ)) ^ 2
            = ((2 : ℝ) ^ (1/4 : ℝ)) ^ 2 * (Real.sqrt (n + 1 : ℝ)) ^ 2 := by
        simpa using (mul_pow ((2 : ℝ) ^ (1/4 : ℝ)) (Real.sqrt (n + 1 : ℝ)) (2 : ℕ))
      -- combine via transitivity to avoid simp recursion
      have h2sq' : ((2 : ℝ) ^ (1/4 : ℝ)) ^ 2 = (2 : ℝ) ^ (2 : ℝ)⁻¹ := by
        simpa [one_div] using h2sq
      have hstep : ((2 : ℝ) ^ (1/4 : ℝ)) ^ 2 * (Real.sqrt (n + 1 : ℝ)) ^ 2
            = (2 : ℝ) ^ (2 : ℝ)⁻¹ * (n + 1 : ℝ) := by
        rw [h2sq', hsq_sqrt]
      exact mul_pow2.trans hstep
    have rhs_eq : ((n + 1 : ℝ) / (Real.pi) ^ (1/4 : ℝ)) ^ 2
          = ((n + 1 : ℝ) * (n + 1 : ℝ)) / (Real.pi) ^ (2 : ℝ)⁻¹ := by
      -- expand the square of the quotient to a product, then simplify the denominator
      have div_pow2_prod : ((n + 1 : ℝ) / (Real.pi) ^ (1/4 : ℝ)) ^ 2
            = ((n + 1 : ℝ) * (n + 1 : ℝ)) / ((Real.pi) ^ (1/4 : ℝ) * (Real.pi) ^ (1/4 : ℝ)) := by
        -- (a/b)^2 = (a/b) * (a/b) = (a*a) / (b*b)
        simp [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      -- and (π^(1/4))*(π^(1/4)) = π^(1/2) = π^(2⁻¹)
      have hsplitpi12 : (Real.pi) ^ (1/4 : ℝ) * (Real.pi) ^ (1/4 : ℝ)
            = (Real.pi) ^ (2 : ℝ)⁻¹ := by
        have hhalf : (Real.pi) ^ (1/2 : ℝ) = (Real.pi) ^ ((2 : ℝ)⁻¹) := by
          simp [one_div]
        -- from earlier: π^(1/2) = π^(1/4) * π^(1/4)
        simpa [hhalf] using hsplitpi.symm
      -- Replace the denominator using congrArg to avoid simp shape issues
      have div_pow2_prod' : ((n + 1 : ℝ) / (Real.pi) ^ (1/4 : ℝ)) ^ 2
            = ((n + 1 : ℝ) * (n + 1 : ℝ)) / ((Real.pi) ^ (1/4 : ℝ) * (Real.pi) ^ (1/4 : ℝ)) :=
        div_pow2_prod
      -- Denominator equality from hsplitpi12
      let D1 := (Real.pi) ^ (1/4 : ℝ) * (Real.pi) ^ (1/4 : ℝ)
      let D2 := (Real.pi) ^ (2 : ℝ)⁻¹
      have hDen : ((n + 1 : ℝ) * (n + 1 : ℝ)) / D1
            = ((n + 1 : ℝ) * (n + 1 : ℝ)) / D2 := by
        simpa [D1, D2] using congrArg (fun x => ((n + 1 : ℝ) * (n + 1 : ℝ)) / x) hsplitpi12
      -- Conclude the desired equality by transitivity
      have : ((n + 1 : ℝ) / (Real.pi) ^ (1/4 : ℝ)) ^ 2
            = ((n + 1 : ℝ) * (n + 1 : ℝ)) / D2 := div_pow2_prod'.trans hDen
      simpa [D2] using this
    -- Convert the inequality using these identities via exponent normalization
    have hlin' : (2 : ℝ) ^ (2 : ℝ)⁻¹ * (n + 1 : ℝ)
          ≤ ((n + 1 : ℝ) * (n + 1 : ℝ)) / Real.pi ^ (2 : ℝ)⁻¹ := by
      -- rewrite 1/2 as 2⁻¹ on both sides
      simpa [one_div] using htarget
    -- Replace both sides by the squared forms using lhs_eq and rhs_eq
    have hgoal : ((2 : ℝ) ^ (1/4 : ℝ) * Real.sqrt (n + 1 : ℝ)) ^ 2
          ≤ ((n + 1 : ℝ) / (Real.pi) ^ (1/4 : ℝ)) ^ 2 := by
      -- convert both sides of the inequality
      convert hlin' using 1 <;> simp [lhs_eq, rhs_eq]
    exact hgoal
  -- From squared inequality and nonnegativity, deduce the desired inequality
  have habs :
      |(2 : ℝ) ^ (1/4 : ℝ) * Real.sqrt (n + 1 : ℝ)|
        ≤ |(n + 1 : ℝ) / (Real.pi ^ (1/4 : ℝ))| := by
    -- `sq_le_sq` gives equivalence between squares and absolute values
    exact sq_le_sq.mp hsq
  have hineq_linear :
      (2 : ℝ) ^ (1/4 : ℝ) * Real.sqrt (n + 1 : ℝ)
        ≤ (n + 1 : ℝ) / (Real.pi ^ (1/4 : ℝ)) := by
    rw [abs_of_nonneg hL_nonneg, abs_of_nonneg hR_nonneg] at habs
    exact habs
  rw [hL, hR]
  exact hineq_linear

end Frourio
