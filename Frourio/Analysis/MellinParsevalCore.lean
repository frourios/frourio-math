import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.SchwartzDensity.SchwartzDensity
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.HilbertSpaceCore
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Regular

set_option linter.style.multiGoal false

/-!
# Mellin-Parseval Identity and its Relation to Fourier-Parseval

This file establishes the explicit relationship between the Mellin-Plancherel formula
and the classical Fourier-Parseval identity through logarithmic change of variables.

## Main Results

- `mellin_to_fourier_change_of_variables`: The change of variables x = e^t transforms
  the Mellin transform to a Fourier transform on the additive group ℝ
- `parseval_identity_equivalence`: The Mellin-Plancherel formula is equivalent to
  the Fourier-Parseval identity under appropriate transformation
- `mellin_parseval_formula`: Explicit Parseval formula for Mellin transforms

## Implementation Notes

The key insight is that the multiplicative Haar measure dx/x on (0,∞) corresponds
to the Lebesgue measure dt on ℝ under the logarithmic change of variables x = e^t.
-/

open MeasureTheory Measure Real Complex
open scoped ENNReal Topology FourierTransform

namespace Frourio

section MellinFourierCorrespondence

/-- The logarithmic change of variables map -/
noncomputable def logMap : (Set.Ioi (0 : ℝ)) → ℝ := fun x => Real.log x.val

/-- The exponential change of variables map -/
noncomputable def expMap : ℝ → (Set.Ioi (0 : ℝ)) := fun t => ⟨Real.exp t, Real.exp_pos t⟩

/-- The logarithmic map is a measurable equivalence -/
noncomputable def logMap_measurableEquiv :
    MeasurableEquiv (Set.Ioi (0 : ℝ)) ℝ where
  toFun := logMap
  invFun := expMap
  left_inv := fun x => by
    simp [logMap, expMap]
    ext
    simp [Real.exp_log x.2]
  right_inv := fun t => by
    simp [logMap, expMap, Real.log_exp]
  measurable_toFun := by
    -- logMap is the composition of log with the inclusion map
    unfold logMap
    -- We need to show that fun x : Set.Ioi (0 : ℝ) => Real.log x.val is measurable
    -- This is the composition of Real.log with the coercion Subtype.val
    have h_val_measurable : Measurable (fun x : Set.Ioi (0 : ℝ) => x.val) := by
      exact measurable_subtype_coe
    have h_log_measurable : Measurable (fun x : ℝ => Real.log x) := by
      exact Real.measurable_log
    -- The composition of measurable functions is measurable
    exact h_log_measurable.comp h_val_measurable
  measurable_invFun := by
    -- expMap is the function that takes t to (exp(t), proof that exp(t) > 0)
    unfold expMap
    have h_exp_measurable : Measurable Real.exp := Real.measurable_exp
    -- For a subtype with a measurable predicate, the constructor is measurable
    -- when the underlying function is measurable
    refine Measurable.subtype_mk ?_
    exact h_exp_measurable

/-- The Mellin kernel x^(s-1) becomes e^((s-1)t) under logarithmic change -/
lemma mellin_kernel_transform (s : ℂ) (t : ℝ) :
    (Real.exp t : ℂ) ^ (s - 1) = Complex.exp ((s - 1) * t) := by
  -- Use the fact that for x > 0, x^s = exp(s * log x)
  -- Here x = exp(t), so log(exp(t)) = t
  have h_ne_zero : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)

  -- Use the definition of complex power: x^s = exp(s * log(x))
  rw [Complex.cpow_def_of_ne_zero h_ne_zero]

  -- Simplify: exp((s-1) * log(exp(t))) = exp((s-1) * t)
  congr 1

  -- We need to show: log(exp(t)) * (s - 1) = (s - 1) * t
  rw [mul_comm]
  congr 1

  -- Show that log(exp(t)) = t for real t
  -- First convert exp(t) to complex
  simp only [Complex.ofReal_exp]

  -- We need to show: Complex.log (Complex.exp (↑t)) = ↑t
  -- This is a fundamental identity for complex logarithms
  -- when the imaginary part of the argument is in (-π, π]

  -- For real t, we have Im(↑t) = 0, which is in the principal branch
  apply Complex.log_exp

  -- We need to show -π < Im(↑t) ∧ Im(↑t) ≤ π
  simp only [Complex.ofReal_im]
  · linarith [Real.pi_pos]
  · exact Real.pi_nonneg

/-- Change of variables lemma for Mellin transform: x = exp(t) -/
lemma mellin_change_of_variables (f : ℝ → ℂ) (s : ℂ) :
    ∫ x in Set.Ioi (0 : ℝ), f x * x ^ (s - 1) ∂volume =
    ∫ t : ℝ, f (Real.exp t) * (Real.exp t : ℂ) ^ (s - 1) * Real.exp t := by
  -- Under the change of variables x = exp(t):
  -- - The domain (0, ∞) maps to (-∞, ∞)
  -- - We have dx = exp(t) dt (the Jacobian)
  -- - x^(s-1) becomes (exp(t))^(s-1)
  -- - The integral becomes: ∫ f(exp(t)) * (exp(t))^(s-1) * exp(t) dt
  classical
  -- Package the Mellin integrand for convenience.
  set g : ℝ → ℂ := fun x => f x * (x : ℂ) ^ (s - 1)
  -- Apply the general real change-of-variables formula for the exponential map.
  have h_deriv :
      ∀ x ∈ (Set.univ : Set ℝ),
        HasFDerivWithinAt (fun t : ℝ => Real.exp t)
          (Real.exp x • (1 : ℝ →L[ℝ] ℝ)) Set.univ x := by
    intro x _
    -- Start from the standard derivative of `Real.exp` and rewrite the linear map
    have h :=
      ((Real.hasDerivAt_exp x).hasFDerivAt).hasFDerivWithinAt (s := (Set.univ : Set ℝ))
    -- Replace `smulRight` by scalar multiplication on the identity map
    convert h using 1
    refine ContinuousLinearMap.ext ?_
    intro y
    simp [ContinuousLinearMap.smulRight, smul_eq_mul, mul_comm]
  have h_inj :
      Set.InjOn (fun t : ℝ => Real.exp t) (Set.univ : Set ℝ) := by
    intro x _ y _ hxy
    exact Real.exp_injective hxy
  have h_range :
      (fun t : ℝ => Real.exp t) '' (Set.univ : Set ℝ) = Set.Ioi (0 : ℝ) := by
    simpa [Set.image_univ, Set.range] using Real.range_exp
  have h_change :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume)
      (s := (Set.univ : Set ℝ))
      (f := fun t : ℝ => Real.exp t)
      (f' := fun x : ℝ => Real.exp x • (1 : ℝ →L[ℝ] ℝ))
      (g := g)
      (hs := MeasurableSet.univ)
      (hf' := h_deriv)
      (hf := h_inj)
  -- Rewrite the change-of-variable identity into the desired form.
  have h_det :
      ∀ x : ℝ,
        |((Real.exp x) • (1 : ℝ →L[ℝ] ℝ)).det| = Real.exp x := by
    intro x
    have hdet : ((Real.exp x) • (1 : ℝ →L[ℝ] ℝ)).det = Real.exp x := by simp
    simp
  -- Simplify both sides to obtain the explicit change-of-variable statement.
  simpa [g, h_range, h_det, abs_of_pos (Real.exp_pos _), smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using h_change

/-- Under x = e^t, the Mellin transform becomes a Fourier-type transform -/
theorem mellin_to_fourier_change_of_variables
    (f : ℝ → ℂ) (s : ℂ) :
    mellinTransform f s = ∫ t : ℝ, f (Real.exp t) * Complex.exp (s * t) := by
  -- First, unfold the definition of mellinTransform
  unfold mellinTransform

  -- Apply the change of variables lemma
  rw [mellin_change_of_variables]

  -- Now we have ∫ t : ℝ, f (Real.exp t) * (Real.exp t : ℂ) ^ (s - 1) * Real.exp t
  -- The target has f(Real.exp t) * exp(s * t)

  -- Use mellin_kernel_transform to convert (Real.exp t)^(s-1) to exp((s-1)t)
  congr 1
  ext t
  rw [mellin_kernel_transform]

  -- Now we have f(exp(t)) * exp((s-1)t) * exp(t)
  -- We need to show this equals f(exp(t)) * exp(s*t)

  -- Let's compute: exp((s-1)t) * exp(t) = exp((s-1)t + t) = exp(st)
  have h_exp_combine : Complex.exp ((s - 1) * ↑t) * ↑(Real.exp t) = Complex.exp (s * ↑t) := by
    simp only [Complex.ofReal_exp]
    rw [← Complex.exp_add]
    congr 1
    ring

  -- Rewrite using h_exp_combine
  rw [mul_assoc, h_exp_combine]

/-- Change of variables formula for exponential transformation -/
lemma exp_image_measure_integral (E : Set ℝ) (hE : MeasurableSet E) :
    ∫⁻ x in Real.exp '' E, ENNReal.ofReal (1 / x) ∂volume =
    ∫⁻ t in E, ENNReal.ofReal (1 / Real.exp t) * ENNReal.ofReal (Real.exp t) ∂volume := by
  classical
  -- Apply the one-dimensional change-of-variables formula for the exponential map.
  have h_deriv : ∀ x ∈ E, HasDerivWithinAt Real.exp (Real.exp x) E x := by
    intro x _
    exact (Real.hasDerivAt_exp x).hasDerivWithinAt
  have h_inj : Set.InjOn Real.exp E := Real.exp_injective.injOn
  -- Use the general non-negative change-of-variables lemma.
  have h :=
    lintegral_image_eq_lintegral_abs_deriv_mul (s := E)
      (f := Real.exp) (f' := fun x => Real.exp x)
      hE h_deriv h_inj (fun x : ℝ => ENNReal.ofReal (1 / x))
  -- Simplify both sides using the positivity of the exponential function.
  simpa [abs_of_pos (Real.exp_pos _), mul_comm, mul_left_comm, mul_assoc]
    using h

/-- Simplification lemma: (1/exp(t)) * exp(t) = 1 in ENNReal -/
lemma ennreal_div_exp_mul_exp : ∀ t : ℝ,
    ENNReal.ofReal (1 / Real.exp t) * ENNReal.ofReal (Real.exp t) = 1 := by
  intro t
  -- This follows from the fact that (1/x) * x = 1 for x ≠ 0
  -- and Real.exp t is always nonzero
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have h_inv : ENNReal.ofReal (1 / Real.exp t)
      = (ENNReal.ofReal (Real.exp t))⁻¹ := by
    simpa [one_div] using ENNReal.ofReal_inv_of_pos hpos
  have h_ne_zero : ENNReal.ofReal (Real.exp t) ≠ 0 := by
    simpa [ENNReal.ofReal_ne_zero_iff] using hpos
  have h_ne_top : ENNReal.ofReal (Real.exp t) ≠ ∞ := ENNReal.ofReal_ne_top
  have h_eq :
      ENNReal.ofReal (1 / Real.exp t) * ENNReal.ofReal (Real.exp t)
        = (ENNReal.ofReal (Real.exp t))⁻¹ * ENNReal.ofReal (Real.exp t) :=
    congrArg (fun x : ℝ≥0∞ => x * ENNReal.ofReal (Real.exp t)) h_inv
  have h_cancel :
      (ENNReal.ofReal (Real.exp t))⁻¹ * ENNReal.ofReal (Real.exp t) = 1 := by
    simpa [mul_comm] using ENNReal.mul_inv_cancel h_ne_zero h_ne_top
  exact h_eq.trans h_cancel

/-- The multiplicative Haar measure corresponds to Lebesgue measure -/
lemma mulHaar_pushforward_log :
    ∃ (c : ℝ≥0∞), c ≠ 0 ∧ c ≠ ∞ ∧
    Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ))) = c • volume := by
  -- The measure dx/x on (0,∞) becomes dt on ℝ under x = e^t
  -- In fact, the constant c should be 1

  -- Recall that mulHaar has density 1/x with respect to volume on (0,∞)
  -- Under the change of variables x = e^t:
  -- - The domain (0,∞) maps to (-∞,∞) = ℝ
  -- - We have dx = e^t dt
  -- - The measure dx/x becomes (e^t dt)/e^t = dt

  -- So the pushforward of mulHaar under log is exactly the Lebesgue measure
  use 1

  constructor
  · -- Show that 1 ≠ 0
    norm_num

  constructor
  · -- Show that 1 ≠ ∞
    norm_num

  · -- Show that Measure.map Real.log (mulHaar.restrict (Set.Ioi 0)) = 1 • volume
    -- This follows from the change of variables formula

    -- First, simplify using the fact that mulHaar is already restricted
    -- mulHaar = (volume.withDensity (fun x => ENNReal.ofReal (1 / x))).restrict (Set.Ioi 0)
    -- So mulHaar.restrict (Set.Ioi 0) = mulHaar (idempotent)

    -- mulHaar is already defined as a restriction to (0,∞), so restricting again is idempotent
    have h_restrict : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by
      -- Unfold the definition of mulHaar
      unfold mulHaar
      rw [Measure.restrict_restrict (measurableSet_Ioi)]
      simp

    rw [h_restrict]

    -- Now we need to show: Measure.map Real.log mulHaar = volume
    -- This is the key property: the pushforward of dx/x under log is dt

    simp only [one_smul]

    -- We need to show that the pushforward equals volume
    -- This uses the fact that for any measurable set E ⊆ ℝ:
    -- (Measure.map Real.log mulHaar) E = mulHaar (Real.log ⁻¹' E ∩ Set.Ioi 0)
    -- = ∫ x in (Real.log ⁻¹' E ∩ Set.Ioi 0), 1/x dx
    -- Under x = e^t, this becomes ∫ t in E, dt = volume E

    -- Use measure equality by showing they agree on measurable sets
    ext E hE

    -- Calculate (Measure.map Real.log mulHaar) E
    rw [Measure.map_apply Real.measurable_log hE]

    -- Now we have mulHaar (Real.log ⁻¹' E)
    -- Since mulHaar is supported on (0,∞), we get mulHaar (Real.log ⁻¹' E ∩ Set.Ioi 0)

    -- The change of variables formula says:
    -- ∫ x in Real.log ⁻¹' E ∩ (0,∞), 1/x dx = ∫ t in E, dt
    -- because under x = e^t, dx/x = dt

    -- First, observe that Real.log ⁻¹' E ∩ Set.Ioi 0 = Real.exp '' E
    have h_preimage_eq_image : Real.log ⁻¹' E ∩ Set.Ioi (0 : ℝ) = Real.exp '' E := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_image]
      constructor
      · intro ⟨hlog, hpos⟩
        use Real.log x
        constructor
        · exact hlog
        · exact Real.exp_log hpos
      · intro ⟨t, ht, hx⟩
        rw [← hx]
        constructor
        · simp [Real.log_exp, ht]
        · exact Real.exp_pos t

    -- Now we need: mulHaar (Real.exp '' E) = volume E
    -- This follows from the change of variables formula for measures
    -- mulHaar has density 1/x, so mulHaar(A) = ∫ x in A, 1/x dx

    unfold mulHaar

    -- For a restricted measure, μ.restrict S (A) = μ (A ∩ S)
    -- We need to show Real.log ⁻¹' E is measurable
    have hE_preimage_measurable : MeasurableSet (Real.log ⁻¹' E) := by
      exact Real.measurable_log hE

    rw [Measure.restrict_apply hE_preimage_measurable]
    rw [h_preimage_eq_image]

    -- We need to show:
    -- (volume.withDensity (fun x => ENNReal.ofReal (1/x))) (Real.exp '' E) = volume E

    -- This is the key change of variables formula:
    -- ∫ x in Real.exp '' E, 1/x dx = ∫ t in E, dt
    -- Under x = exp(t), we have dx = exp(t) dt, so dx/x = dt

    -- The measure with density 1/x evaluated on Real.exp '' E
    rw [withDensity_apply']

    -- We need: ∫⁻ x in Real.exp '' E, ENNReal.ofReal (1/x) ∂volume = volume E

    -- Use change of variables: x = exp(t), so the integral becomes
    -- ∫⁻ t in E, ENNReal.ofReal (1/exp(t)) * exp(t) ∂volume
    -- = ∫⁻ t in E, 1 ∂volume = volume E

    -- First, show that Real.exp is a measurable equivalence when restricted properly
    have h_exp_measurable : Measurable Real.exp := Real.measurable_exp

    -- Apply the change of variables formula for exponential
    rw [exp_image_measure_integral E hE]

    -- Simplify using the fact that (1/exp(t)) * exp(t) = 1
    simp_rw [ennreal_div_exp_mul_exp]
    simp [lintegral_const, volume]

end MellinFourierCorrespondence

section ParsevalEquivalence

/-- The transformed function under logarithmic change -/
noncomputable def logPushforward (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => f (Real.exp t)

/-- The weight function for the transformed inner product -/
noncomputable def mellinWeight (σ : ℝ) : ℝ → ℝ :=
  fun t => Real.exp ((2 * σ - 1) * t)

/-- The Mellin transform at σ + iτ corresponds to weighted Fourier transform -/
theorem mellin_as_weighted_fourier (f : ℝ → ℂ) (σ τ : ℝ) :
    mellinTransform f (σ + I * τ) =
    ∫ t : ℝ, (logPushforward f) t * Complex.exp (σ * t) * Complex.exp (I * τ * t) := by
  -- Use the change of variables theorem directly
  rw [mellin_to_fourier_change_of_variables]

  -- Now we have: ∫ t : ℝ, f (Real.exp t) * Complex.exp ((σ + I * τ) * t)
  -- We need: ∫ t : ℝ, (logPushforward f) t * Complex.exp (σ * t) * Complex.exp (I * τ * t)

  -- First unfold logPushforward
  unfold logPushforward

  -- Now we need to show:
  -- f (Real.exp t) * Complex.exp ((σ + I * τ) * t) =
  -- f (Real.exp t) * Complex.exp (σ * t) * Complex.exp (I * τ * t)

  congr 1
  ext t

  -- Split the complex exponential using the property exp(a + b) = exp(a) * exp(b)
  have h_split : Complex.exp (((σ : ℂ) + I * τ) * t) =
                 Complex.exp ((σ : ℂ) * t) * Complex.exp (I * τ * t) := by
    rw [← Complex.exp_add]
    congr 1
    ring

  rw [h_split]

  -- This is just associativity of multiplication
  ring

/-- The polarization identity for complex inner products -/
lemma complex_polarization_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f g : E) :
    4 * @inner ℂ _ _ f g =
      ((‖f + g‖ ^ 2 : ℝ) : ℂ) - ((‖f - g‖ ^ 2 : ℝ) : ℂ) -
        Complex.I * ((‖f + Complex.I • g‖ ^ 2 : ℝ) : ℂ) +
          Complex.I * ((‖f - Complex.I • g‖ ^ 2 : ℝ) : ℂ) := by
  classical
  -- Apply the polarization identity for linear maps with the identity map.
  have h := inner_map_polarization'
      (T := (LinearMap.id : E →ₗ[ℂ] E)) (x := f) (y := g)
  -- Clear the denominator by multiplying through by 4.
  have h4 :
      (4 : ℂ) * @inner ℂ _ _ f g =
        @inner ℂ _ _ (f + g) (f + g) - @inner ℂ _ _ (f - g) (f - g) -
          Complex.I * @inner ℂ _ _ (f + Complex.I • g) (f + Complex.I • g) +
            Complex.I * @inner ℂ _ _ (f - Complex.I • g) (f - Complex.I • g) := by
    simpa [div_eq_mul_inv, LinearMap.id_apply, mul_comm, mul_left_comm, mul_assoc]
      using (congrArg (fun z : ℂ => (4 : ℂ) * z) h)
  -- Replace the inner products of a vector with itself by squared norms.
  have h_norms :
      (4 : ℂ) * @inner ℂ _ _ f g =
        (‖f + g‖ : ℂ)^2 - (‖f - g‖ : ℂ)^2 -
          Complex.I * (‖f + Complex.I • g‖ : ℂ)^2 +
            Complex.I * (‖f - Complex.I • g‖ : ℂ)^2 := by
    simpa [inner_self_eq_norm_sq_to_K] using h4
  -- Express the complex norms as coercions of real squares and rearrange.
  have h_final :
      (4 : ℂ) * @inner ℂ _ _ f g =
        Complex.ofReal (‖f + g‖ ^ 2) - Complex.ofReal (‖f - g‖ ^ 2) -
          Complex.I * Complex.ofReal (‖f + Complex.I • g‖ ^ 2) +
            Complex.I * Complex.ofReal (‖f - Complex.I • g‖ ^ 2) := by
    simpa [pow_two, Complex.ofReal_mul] using h_norms
  -- Interpret the result back in the desired form.
  simpa using h_final

/-- The Mellin transform relates to LogPull through change of variables -/
lemma mellin_logpull_relation (σ : ℝ) (f : Hσ σ) (τ : ℝ) :
    mellinTransform (f : ℝ → ℂ) (σ + I * τ) =
    ∫ t : ℝ, LogPull σ f t * Complex.exp (I * τ * t) * Complex.exp ((1/2 : ℝ) * t) := by
  have h_base :=
    mellin_as_weighted_fourier (f := (f : ℝ → ℂ)) (σ := σ) (τ := τ)
  have h_exp : ∀ t : ℝ,
      Complex.exp (σ * t)
        = (Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ) * Complex.exp ((1 / 2 : ℝ) * t) := by
    intro t
    have hσt :
        (σ : ℂ) * (t : ℂ)
          = ((σ - (1 / 2 : ℝ)) : ℂ) * (t : ℂ) + (1 / 2 : ℂ) * (t : ℂ) := by
      have hsum : σ * t = (σ - (1 / 2 : ℝ)) * t + (1 / 2 : ℝ) * t := by
        ring
      calc
        (σ : ℂ) * (t : ℂ)
            = Complex.ofReal σ * Complex.ofReal t := rfl
        _ = Complex.ofReal (σ * t) := by
                simp [Complex.ofReal_mul]
        _ = Complex.ofReal ((σ - (1 / 2 : ℝ)) * t + (1 / 2 : ℝ) * t) := by
                simp [hsum, add_comm]
        _ = ((σ - (1 / 2 : ℝ)) : ℂ) * (t : ℂ) + (1 / 2 : ℂ) * (t : ℂ) := by
                simp [Complex.ofReal_mul, Complex.ofReal_add, sub_eq_add_neg, add_comm]
    calc
      Complex.exp (σ * t)
          = Complex.exp ((σ : ℂ) * (t : ℂ)) := by
              simp
      _ = Complex.exp
            (((σ - (1 / 2 : ℝ)) : ℂ) * (t : ℂ) + (1 / 2 : ℂ) * (t : ℂ)) := by
              simp [hσt]
      _ = Complex.exp (((σ - (1 / 2 : ℝ)) : ℂ) * (t : ℂ))
              * Complex.exp ((1 / 2 : ℂ) * (t : ℂ)) := by
              simpa
                using
                  Complex.exp_add (((σ - (1 / 2 : ℝ)) : ℂ) * (t : ℂ))
                    ((1 / 2 : ℂ) * (t : ℂ))
      _ = (Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ)
              * Complex.exp ((1 / 2 : ℝ) * t) := by
              simp [Complex.ofReal_exp, sub_eq_add_neg]
  have h_integrand :
      (fun t : ℝ =>
        logPushforward (f : ℝ → ℂ) t * Complex.exp (σ * t) * Complex.exp (I * τ * t))
        =
        fun t : ℝ =>
          LogPull σ f t * Complex.exp (I * τ * t) * Complex.exp ((1 / 2 : ℝ) * t) := by
    funext t
    have h_exp_t := h_exp t
    simp [LogPull_apply, logPushforward, Hσ.toFun, h_exp_t, mul_comm, mul_left_comm,
      mul_assoc]
  simpa [h_integrand] using h_base

/-- Norm simplification for weighted LogPull -/
lemma norm_simplification_logpull (σ : ℝ) (f : Hσ σ) :
    ∫ t : ℝ, ‖LogPull σ f t * Complex.exp ((1/2 : ℝ) * t)‖^2 =
    ∫ t : ℝ, ‖LogPull σ f t‖^2 * Real.exp t := by
  -- We need to show: |LogPull σ f t * e^{t/2}|^2 = |LogPull σ f t|^2 * e^t
  -- This follows from:
  -- |z * e^{t/2}|^2 = |z|^2 * |e^{t/2}|^2 = |z|^2 * e^t
  -- since |e^{t/2}|^2 = e^{Re(t/2) * 2} = e^t for real t
  have h_pointwise :
      ∀ t : ℝ,
        ‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2 =
          ‖LogPull σ f t‖^2 * Real.exp t := by
    intro t
    have h_sq :=
      congrArg (fun r : ℝ => r ^ 2)
        (norm_mul (LogPull σ f t) (Complex.exp ((1 / 2 : ℝ) * t)))
    have h_norm_exp :
        ‖Complex.exp ((1 / 2 : ℝ) * t)‖ = Real.exp ((1 / 2 : ℝ) * t) := by
      have : (((1 / 2 : ℝ) * t : ℂ)).re = (1 / 2 : ℝ) * t := by
        simp
      simp [Complex.norm_exp]
    have h_exp_sq : Real.exp ((1 / 2 : ℝ) * t) ^ (2 : ℕ) = Real.exp t := by
      have hsum : (1 / 2 : ℝ) * t + (1 / 2 : ℝ) * t = t := by
        calc
          (1 / 2 : ℝ) * t + (1 / 2 : ℝ) * t
              = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) * t := by ring
          _ = (1 : ℝ) * t := by norm_num
          _ = t := by simp
      have hsum' : (2⁻¹ : ℝ) * t + (2⁻¹ : ℝ) * t = t := by
        simpa [one_div] using hsum
      calc
        Real.exp ((1 / 2 : ℝ) * t) ^ (2 : ℕ)
            = Real.exp ((1 / 2 : ℝ) * t) * Real.exp ((1 / 2 : ℝ) * t) := by
                simp [pow_two]
        _ = Real.exp ((1 / 2 : ℝ) * t + (1 / 2 : ℝ) * t) := by
                simpa using
                  (Real.exp_add ((1 / 2 : ℝ) * t) ((1 / 2 : ℝ) * t)).symm
        _ = Real.exp t := by
                simp [hsum', one_div]
    have h_rhs : (‖LogPull σ f t‖ * ‖Complex.exp ((1 / 2 : ℝ) * t)‖) ^ (2 : ℕ)
        = ‖LogPull σ f t‖ ^ (2 : ℕ) * Real.exp t := by
      have h_mul_pow :
          (‖LogPull σ f t‖ * Real.exp ((1 / 2 : ℝ) * t)) ^ (2 : ℕ)
            = ‖LogPull σ f t‖ ^ (2 : ℕ)
                * Real.exp ((1 / 2 : ℝ) * t) ^ (2 : ℕ) := by
        simpa using
          (mul_pow (‖LogPull σ f t‖) (Real.exp ((1 / 2 : ℝ) * t)) (2 : ℕ))
      have h_replace :
          (‖LogPull σ f t‖ * ‖Complex.exp ((1 / 2 : ℝ) * t)‖) ^ (2 : ℕ)
            = (‖LogPull σ f t‖ * Real.exp ((1 / 2 : ℝ) * t)) ^ (2 : ℕ) := by
        simp only [h_norm_exp]
      calc
        (‖LogPull σ f t‖ * ‖Complex.exp ((1 / 2 : ℝ) * t)‖) ^ (2 : ℕ)
            = (‖LogPull σ f t‖ * Real.exp ((1 / 2 : ℝ) * t)) ^ (2 : ℕ) := h_replace
        _ = ‖LogPull σ f t‖ ^ (2 : ℕ)
              * Real.exp ((1 / 2 : ℝ) * t) ^ (2 : ℕ) := h_mul_pow
        _ = ‖LogPull σ f t‖ ^ (2 : ℕ) * Real.exp t := by
              simp only [h_exp_sq]
    have h_final := h_sq.trans h_rhs
    simpa [pow_two] using h_final
  have h_pointwise_ae :
      (fun t : ℝ => ‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2)
        =ᵐ[volume]
        fun t : ℝ => ‖LogPull σ f t‖^2 * Real.exp t :=
    Filter.Eventually.of_forall h_pointwise
  simpa using integral_congr_ae h_pointwise_ae

/-- The L² norm of weighted LogPull equals the weighted L² norm of f,
    assuming the integral converges -/
lemma weighted_LogPull_integral_eq (σ : ℝ) (f : Hσ σ) :
    ∫⁻ t, ENNReal.ofReal (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2) ∂volume
    = ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖f x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume := by
  classical
  -- Package the pullback integrand that will be transported under log/exp.
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)

  -- Measurability needed for the change-of-variables lemma.
  have hg_meas : Measurable g := by
    have h_comp : Measurable fun t : ℝ => Hσ.toFun f (Real.exp t) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_norm : Measurable fun t : ℝ => ‖Hσ.toFun f (Real.exp t)‖ := h_comp.norm
    have h_sq : Measurable fun t : ℝ => ‖Hσ.toFun f (Real.exp t)‖^2 := by
      simpa [pow_two] using h_norm.mul h_norm
    exact (Measurable.ennreal_ofReal h_sq)

  -- Pointwise identification of the integrand on ℝ.
  have h_pointwise_real :
      ∀ t : ℝ,
        ‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2
          = ‖LogPull σ f t‖^2 * Real.exp t := by
    intro t
    have h_norm_exp :
        ‖Complex.exp ((1 / 2 : ℝ) * t)‖ = Real.exp ((1 / 2 : ℝ) * t) := by
      simpa using Complex.norm_exp ((1 / 2 : ℝ) * t : ℂ)
    have h_exp_sq : Real.exp ((1 / 2 : ℝ) * t) ^ 2 = Real.exp t := by
      have h_add : (2⁻¹ : ℝ) * t + (2⁻¹ : ℝ) * t = t := by
        have h : ((1 / 2 : ℝ) * t) + ((1 / 2 : ℝ) * t) = t := by ring
        simpa [one_div] using h
      calc
        Real.exp ((1 / 2 : ℝ) * t) ^ 2
            = Real.exp ((1 / 2 : ℝ) * t) * Real.exp ((1 / 2 : ℝ) * t) := by
                simp [pow_two]
        _ = Real.exp (((1 / 2 : ℝ) * t) + ((1 / 2 : ℝ) * t)) := by
                simpa using (Real.exp_add ((1 / 2 : ℝ) * t) ((1 / 2 : ℝ) * t)).symm
        _ = Real.exp t := by simp [one_div, h_add]
    have h_mul_pow :
        (‖LogPull σ f t‖ * Real.exp ((1 / 2 : ℝ) * t))^2
          = ‖LogPull σ f t‖^2 * Real.exp ((1 / 2 : ℝ) * t) ^ 2 := by
      simpa using
        (mul_pow (‖LogPull σ f t‖) (Real.exp ((1 / 2 : ℝ) * t)) (2 : ℕ))
    have h_sq :
        ‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2
          = (‖LogPull σ f t‖ * ‖Complex.exp ((1 / 2 : ℝ) * t)‖)^2 := by
      simp [pow_two]
    have h_sq' := h_sq
    -- Replace the norm of the exponential with the real exponential
    rw [h_norm_exp] at h_sq'
    have h_sq'' := h_sq'
    -- Use the multiplicative property of squares to separate the factors
    rw [h_mul_pow] at h_sq''
    have h_sq''' := h_sq''
    -- Convert the remaining exponential square into `Real.exp t`
    rw [h_exp_sq] at h_sq'''
    -- Combine the successive rewrites
    simpa using h_sq'''

  have h_pointwise :
      (fun t : ℝ =>
          ENNReal.ofReal (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2))
        =ᵐ[volume]
        fun t : ℝ =>
          g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) := by
    refine Filter.Eventually.of_forall ?_
    intro t
    have h_sq := h_pointwise_real t
    have h_logpull_sq := LogPull_norm_sq (σ := σ) (f := f) t
    have h_normsq_nonneg : 0 ≤ ‖Hσ.toFun f (Real.exp t)‖^2 := sq_nonneg _
    have h_exp_nonneg : 0 ≤ Real.exp ((2 * σ - 1) * t + t) := (Real.exp_pos _).le
    have h0 := congrArg ENNReal.ofReal h_sq
    have h_mul_logpull :=
      congrArg (fun r : ℝ => r * Real.exp t) h_logpull_sq
    have h1 := congrArg ENNReal.ofReal h_mul_logpull
    have h2 := congrArg ENNReal.ofReal
      (by
        have :
            (Real.exp ((2 * σ - 1) * t) * ‖Hσ.toFun f (Real.exp t)‖^2) * Real.exp t
              = ‖Hσ.toFun f (Real.exp t)‖^2 * Real.exp ((2 * σ - 1) * t + t) := by
          simp [mul_comm, mul_left_comm, Real.exp_add, add_comm]
        exact this)
    calc
      ENNReal.ofReal (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2)
          = ENNReal.ofReal (‖LogPull σ f t‖^2 * Real.exp t) := h0
      _ = ENNReal.ofReal
            ((Real.exp ((2 * σ - 1) * t) * ‖Hσ.toFun f (Real.exp t)‖^2)
              * Real.exp t) := h1
      _ = ENNReal.ofReal
            (‖Hσ.toFun f (Real.exp t)‖^2
              * Real.exp ((2 * σ - 1) * t + t)) := h2
      _ = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
            * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) := by
              simp [ENNReal.ofReal_mul, h_normsq_nonneg]
      _ = g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) := by
              simp [g]

  have h_left :
      ∫⁻ t, ENNReal.ofReal (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2)
          ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) ∂volume :=
    lintegral_congr_ae h_pointwise

  -- Change variables t ↦ log x to move the integral back to (0,∞).
  have h_change :
      ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) ∂volume
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume := by
    simpa using
      (lintegral_change_of_variables_exp (α := 2 * σ - 1) (f := g) hg_meas).symm

  -- Identify the transformed integrand with the weighted Hσ-integral.
  have h_rhs_restrict :
      ∫⁻ x in Set.Ioi (0 : ℝ),
          g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1))
          ∂(volume.restrict (Set.Ioi (0 : ℝ)))
        = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1))
          ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine lintegral_congr_ae ?_
    refine ((ae_restrict_iff' measurableSet_Ioi).2 ?_)
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx_pos : 0 < x := hx
    have hx_nonneg : 0 ≤ x := hx_pos.le
    have h_g : g (Real.log x) = ENNReal.ofReal (‖Hσ.toFun f x‖^2) := by
      simp [g, Real.exp_log hx_pos]
    have hx_pow_nonneg : 0 ≤ x ^ (2 * σ - 1) :=
      Real.rpow_nonneg hx_nonneg _
    have h_normsq_nonneg : 0 ≤ ‖Hσ.toFun f x‖^2 := sq_nonneg _
    calc
      g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1))
          = ENNReal.ofReal (‖Hσ.toFun f x‖^2)
              * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
                simp [h_g]
      _ = ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) := by
          simp [ENNReal.ofReal_mul, h_normsq_nonneg, mul_comm]

  have h_rhs :
      ∫⁻ x in Set.Ioi (0 : ℝ),
          g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume
        = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := by
    simpa using h_rhs_restrict

  -- Assemble the chain of equalities.
  calc
    ∫⁻ t, ENNReal.ofReal (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2)
        ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t + t)) ∂volume :=
          h_left
    _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume := h_change
    _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun f x‖^2 * x ^ (2 * σ - 1)) ∂volume := h_rhs
    _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖f x‖^2 * x ^ (2 * σ - 1)) ∂volume := by
              rfl

/-- Additional L² integrability condition for functions in Hσ σ -/
def has_weighted_L2_norm (σ : ℝ) (f : Hσ σ) : Prop :=
  (∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2 * x^(2*σ - 1)) ∂volume) < ⊤

/-- The weighted LogPull function is in L² under suitable conditions -/
lemma weighted_LogPull_memLp (σ : ℝ) (f : Hσ σ) (h_extra : has_weighted_L2_norm σ f) :
    MemLp (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) 2 volume := by
  have h_eq := weighted_LogPull_integral_eq σ f

  refine ⟨?_, ?_⟩
  · -- Measurability
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact LogPull_measurable σ f
    · apply Complex.measurable_exp.comp
      apply Measurable.mul
      · exact measurable_const
      · exact Complex.measurable_ofReal.comp measurable_id

  · -- Finiteness of L² norm
    -- We need to show: eLpNorm (weighted function) 2 volume < ⊤
    -- This is equivalent to showing the integral of |g|^2 is finite
    have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num

    rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
    simp only [ENNReal.toReal_ofNat, one_div]

    -- Now we need: (∫⁻ t, ‖g t‖ₑ ^ 2)^(1/2) < ⊤
    -- This holds iff ∫⁻ t, ‖g t‖ₑ ^ 2 < ⊤
    have h_exponent_nonneg : 0 ≤ (2 : ℝ)⁻¹ := by norm_num

    -- Show the base integral is finite using h_eq and h_extra
    have h_base_ne_top : (∫⁻ t, (‖LogPull σ f t * Complex.exp
        ((2⁻¹ : ℝ) * t)‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ≠ ⊤ := by
      -- The integral equals h_extra, which is finite
      have h_eq' : ∫⁻ t, (‖LogPull σ f t * Complex.exp ((2⁻¹ : ℝ) * t)‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂volume
          = ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2 * x^(2 * σ - 1)) ∂volume := by
        -- This is essentially h_eq with the right norm notation
        convert h_eq using 2
        funext t
        -- Show the norms are equal
        simp only [pow_two]
        -- Need to show: ‖g t‖ₑ^2 = ENNReal.ofReal (‖g t‖^2)
        -- where g t = LogPull σ f t * exp((1/2) * t)
        have h_norm_eq : (‖LogPull σ f t * Complex.exp ((2⁻¹ : ℝ) * t)‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
            = ENNReal.ofReal (‖LogPull σ f t * Complex.exp
              ((1 / 2 : ℝ) * t)‖ * ‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖) := by
          -- First show 2⁻¹ = 1/2
          have h_half : (2⁻¹ : ℝ) = 1 / 2 := by norm_num
          rw [h_half]
          have hz : 0 ≤ ‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖ := norm_nonneg _
          simp [pow_two]
        exact h_norm_eq
      rw [h_eq']
      exact ne_of_lt h_extra

    exact ENNReal.rpow_lt_top_of_nonneg h_exponent_nonneg h_base_ne_top

/-- Triangle inequality for eLpNorm differences -/
lemma eLpNorm_triangle_diff (f g h : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (hh : AEStronglyMeasurable h volume) :
    eLpNorm (f - h) 2 volume ≤ eLpNorm (f - g) 2 volume + eLpNorm (g - h) 2 volume := by
  -- Rewrite f - h as (f - g) + (g - h)
  have h_eq : f - h = (f - g) + (g - h) := by
    ext x
    simp [Pi.sub_apply, Pi.add_apply]
  rw [h_eq]
  -- Apply triangle inequality for addition
  exact eLpNorm_add_le (hf.sub hg) (hg.sub hh) (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-- Linearity of the Mellin transform (assuming convergence) -/
lemma mellin_transform_linear (σ : ℝ) (h k : Hσ σ) (c : ℂ) (s : ℂ)
    (hh_int : Integrable (fun t => h t * t ^ (s - 1)) (volume.restrict (Set.Ioi 0)))
    (hk_int : Integrable (fun t => k t * t ^ (s - 1)) (volume.restrict (Set.Ioi 0))) :
    mellinTransform ((h + c • k) : ℝ → ℂ) s =
      mellinTransform (h : ℝ → ℂ) s + c * mellinTransform (k : ℝ → ℂ) s := by
  -- The Mellin transform is linear in the function argument
  unfold mellinTransform

  -- Expand the left side
  have h_expand : ((h + c • k) : ℝ → ℂ) = fun t => h t + c * k t := by
    ext t
    simp [Pi.add_apply, Pi.smul_apply]

  rw [h_expand]

  -- Distribute multiplication
  have h_distrib : ∀ t, (h t + c * k t) * t ^ (s - 1) =
      h t * t ^ (s - 1) + c * (k t * t ^ (s - 1)) := by
    intro t
    ring

  simp_rw [h_distrib]

  -- Use linearity of integration
  rw [integral_add, integral_const_mul]
  · exact hh_int
  · exact Integrable.const_mul hk_int c

end ParsevalEquivalence

end Frourio
