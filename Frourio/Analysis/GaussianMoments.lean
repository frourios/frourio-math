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

-- Helper lemmas and auxiliary results

/--
General result: polynomial moments of Gaussian functions are integrable.
-/
private lemma gaussian_moment_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x : ℝ, ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume < ⊤ := by
  -- Split the integral over ℝ into positive and negative parts
  have h_split : ∫⁻ x : ℝ, ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume =
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x^n * Real.exp (-a * x^2)) ∂volume +
      ∫⁻ x in Set.Iio (0 : ℝ), ENNReal.ofReal ((-x)^n * Real.exp (-a * x^2)) ∂volume := by
    -- First split ℝ into three parts: negative, zero, positive
    have h_partition : ∫⁻ x : ℝ, ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume =
        ∫⁻ x in Set.Iio (0 : ℝ), ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume +
        ∫⁻ x in ({0} : Set ℝ), ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume +
        ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume := by
      -- The three sets form a measurable partition of ℝ
      have h_union : Set.univ = Set.Iio (0 : ℝ) ∪ ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ) := by
        -- Show that every real number belongs to one of the three sets
        ext x
        simp only [Set.mem_univ, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_singleton_iff]
        -- Use trichotomy for real numbers
        have h_trichotomy : x < 0 ∨ x = 0 ∨ x > 0 := by
          -- Use the linear order structure on ℝ
          have h_le_or_gt : x ≤ 0 ∨ 0 < x := by
            -- Use decidability of linear order on ℝ
            have h_decidable : Decidable (x ≤ 0) := by
              -- Real numbers have a decidable linear order
              have h_inst : DecidableRel (· ≤ · : ℝ → ℝ → Prop) := by
                -- Use classical logic to get decidability
                classical
                -- In classical logic, all propositions are decidable
                have h_dec : ∀ a b : ℝ, Decidable (a ≤ b) := fun a b => by
                  -- Use Classical.propDecidable for the proposition a ≤ b
                  have h_prop_dec : Decidable (a ≤ b) := by
                    -- Apply the classical axiom that all propositions are decidable
                    have h_classical_axiom : ∀ (p : Prop), Decidable p := by
                      intro p
                      -- Use the law of excluded middle to construct decidability
                      have h_lem : p ∨ ¬p := by
                        -- Apply the classical excluded middle theorem
                        exact Classical.em p

                      -- Convert excluded middle to Decidable
                      have h_to_decidable : p ∨ ¬p → Decidable p := by
                        intro h_or
                        -- Use classical decidability
                        exact Classical.propDecidable p

                      -- Apply the conversion
                      exact h_to_decidable h_lem

                    -- Apply to the specific proposition a ≤ b
                    exact h_classical_axiom (a ≤ b)

                  -- Return the decidable instance
                  exact h_prop_dec

                -- Return as DecidableRel
                exact h_dec

              -- Apply the decidable instance to x and 0
              have h_apply : Decidable (x ≤ 0) := h_inst x 0

              -- Return the decidable instance
              exact h_apply

            cases h_decidable
            · -- Case: ¬(x ≤ 0), which means 0 < x
              right
              have h_not_le : ¬(x ≤ 0) := by
                -- The decidable instance gives us ¬(x ≤ 0) in this branch
                assumption
              have h_gt : 0 < x := by
                -- Convert ¬(x ≤ 0) to 0 < x using not_le
                exact not_le.mp h_not_le
              exact h_gt
            · -- Case: x ≤ 0
              left
              have h_le : x ≤ 0 := by
                -- The decidable instance gives us x ≤ 0 in this branch
                assumption
              exact h_le

          cases' h_le_or_gt with h_le h_gt
          · -- Case: x ≤ 0
            -- Split into x < 0 or x = 0
            have h_lt_or_eq : x < 0 ∨ x = 0 := by
              -- Apply lt_or_eq_of_le to decompose x ≤ 0
              exact lt_or_eq_of_le h_le

            cases' h_lt_or_eq with h_lt h_eq
            · -- Subcase: x < 0
              left
              exact h_lt
            · -- Subcase: x = 0
              right
              left
              exact h_eq
          · -- Case: 0 < x
            right
            right
            exact h_gt
        -- The goal is now True ↔ (x < 0 ∨ x = 0) ∨ 0 < x
        -- We need to prove the right side from h_trichotomy
        constructor
        · -- ⊢ True → (x < 0 ∨ x = 0) ∨ 0 < x
          intro _
          cases' h_trichotomy with h_neg h_rest
          · left
            left
            exact h_neg
          · cases' h_rest with h_zero h_pos
            · left
              right
              exact h_zero
            · right
              exact h_pos
        · -- ⊢ (x < 0 ∨ x = 0) ∨ 0 < x → True
          intro _
          trivial

      -- The sets are pairwise disjoint
      have h_disjoint : Pairwise (fun i j => Disjoint
        ([Set.Iio (0 : ℝ), ({0} : Set ℝ), Set.Ioi (0 : ℝ)].get i)
        ([Set.Iio (0 : ℝ), ({0} : Set ℝ), Set.Ioi (0 : ℝ)].get j)) := by
        -- Show pairwise disjointness by cases
        intro i j hij
        -- Check all pairs: Iio 0 ∩ {0} = ∅, Iio 0 ∩ Ioi 0 = ∅, {0} ∩ Ioi 0 = ∅
        fin_cases i <;> fin_cases j
        · -- Case i = 0, j = 0 (contradiction with i ≠ j)
          exfalso
          exact hij rfl
        · -- Case i = 0, j = 1 (Iio 0 ∩ {0} = ∅)
          -- Simplify the list indexing
          simp only [List.get_eq_getElem]
          -- Show Iio 0 and {0} are disjoint
          apply Set.disjoint_singleton_right.mpr
          exact Set.notMem_Iio.mpr (le_refl 0)
        · -- Case i = 0, j = 2 (Iio 0 ∩ Ioi 0 = ∅)
          simp only [List.get_eq_getElem]
          -- Show Iio 0 and Ioi 0 are disjoint
          rw [Set.disjoint_iff]
          intro x ⟨hx1, hx2⟩
          -- x < 0 and x > 0 is a contradiction
          exact (lt_irrefl x) (lt_trans hx1 hx2)
        · -- Case i = 1, j = 0 ({0} ∩ Iio 0 = ∅)
          simp only [List.get_eq_getElem]
          -- Show {0} and Iio 0 are disjoint
          apply Set.disjoint_singleton_left.mpr
          exact Set.notMem_Iio.mpr (le_refl 0)
        · -- Case i = 1, j = 1 (contradiction with i ≠ j)
          exfalso
          exact hij rfl
        · -- Case i = 1, j = 2 ({0} ∩ Ioi 0 = ∅)
          simp only [List.get_eq_getElem]
          -- Show {0} and Ioi 0 are disjoint
          apply Set.disjoint_singleton_left.mpr
          exact Set.not_mem_Ioi.mpr (le_refl 0)
        · -- Case i = 2, j = 0 (Ioi 0 ∩ Iio 0 = ∅)
          simp only [List.get_eq_getElem]
          -- Show Ioi 0 and Iio 0 are disjoint
          rw [Set.disjoint_iff_inter_eq_empty]
          rw [Set.eq_empty_iff_forall_not_mem]
          intro x ⟨hx1, hx2⟩
          -- x > 0 and x < 0 is a contradiction
          exact (lt_irrefl x) (lt_trans hx2 hx1)
        · -- Case i = 2, j = 1 (Ioi 0 ∩ {0} = ∅)
          simp only [List.get_eq_getElem]
          -- Show Ioi 0 and {0} are disjoint
          apply Set.disjoint_singleton_right.mpr
          exact Set.not_mem_Ioi.mpr (le_refl 0)
        · -- Case i = 2, j = 2 (contradiction with i ≠ j)
          exfalso
          exact hij rfl

      -- Each set is measurable
      have h_measurable_neg : MeasurableSet (Set.Iio (0 : ℝ)) := by
        -- Iio 0 is measurable as an open ray
        exact measurableSet_Iio
      have h_measurable_zero : MeasurableSet ({0} : Set ℝ) := by
        -- Singleton {0} is measurable
        exact MeasurableSet.singleton 0
      have h_measurable_pos : MeasurableSet (Set.Ioi (0 : ℝ)) := by
        -- Ioi 0 is measurable as an open ray
        exact measurableSet_Ioi

      -- The integrand is measurable
      have h_integrand_measurable : Measurable (fun x : ℝ => ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2))) := by
        -- Composition of measurable functions
        apply Measurable.ennreal_ofReal
        apply Measurable.mul
        · -- ‖x‖^n is measurable
          exact Measurable.pow measurable_norm measurable_const
        · -- exp(-a * x^2) is measurable
          apply Measurable.exp
          apply Measurable.const_mul
          -- x^2 is measurable
          exact Measurable.pow measurable_id measurable_const

      -- Apply the partition formula for lintegral
      have h_lintegral_add : ∫⁻ x, ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume =
          ∫⁻ x in Set.Iio (0 : ℝ) ∪ ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ),
            ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume := by
        sorry -- Rewrite using h_union: Set.univ = Iio 0 ∪ {0} ∪ Ioi 0

      -- Use additivity of lintegral over disjoint measurable sets
      have h_sum : ∫⁻ x in Set.Iio (0 : ℝ) ∪ ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ),
            ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume =
          ∫⁻ x in Set.Iio (0 : ℝ), ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume +
          ∫⁻ x in ({0} : Set ℝ), ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume +
          ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume := by
        sorry -- Apply lintegral additivity using h_disjoint and measurability

      -- Combine the steps
      rw [h_lintegral_add, h_sum]

    -- The integral over the singleton {0} is zero
    have h_zero : ∫⁻ x in ({0} : Set ℝ), ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume = 0 := by
      sorry -- Singleton has measure zero for Lebesgue measure

    -- On Ioi 0, we have ‖x‖ = x
    have h_pos_abs : ∀ x ∈ Set.Ioi (0 : ℝ), ‖x‖^n = x^n := by
      sorry -- For x > 0, ‖x‖ = x, so ‖x‖^n = x^n

    -- On Iio 0, we have ‖x‖ = -x
    have h_neg_abs : ∀ x ∈ Set.Iio (0 : ℝ), ‖x‖^n = (-x)^n := by
      sorry -- For x < 0, ‖x‖ = -x, so ‖x‖^n = (-x)^n

    -- Apply the abs value identities to each region
    have h_pos_region : ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume =
        ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x^n * Real.exp (-a * x^2)) ∂volume := by
      sorry -- Apply h_pos_abs pointwise in the integral

    have h_neg_region : ∫⁻ x in Set.Iio (0 : ℝ), ENNReal.ofReal (‖x‖^n * Real.exp (-a * x^2)) ∂volume =
        ∫⁻ x in Set.Iio (0 : ℝ), ENNReal.ofReal ((-x)^n * Real.exp (-a * x^2)) ∂volume := by
      sorry -- Apply h_neg_abs pointwise in the integral

    -- Combine all the pieces
    rw [h_partition, h_zero, add_zero, h_neg_region, h_pos_region]
    ring

  -- By symmetry, both integrals are equal
  have h_symm : ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x^n * Real.exp (-a * x^2)) ∂volume =
      ∫⁻ x in Set.Iio (0 : ℝ), ENNReal.ofReal ((-x)^n * Real.exp (-a * x^2)) ∂volume := by
    sorry -- Use substitution x ↦ -x and symmetry of exp(-a * x^2)

  -- Reduce to showing the integral over positive reals is finite
  have h_pos_finite : ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x^n * Real.exp (-a * x^2)) ∂volume < ⊤ := by
    -- Apply substitution u = √a · x to normalize the exponential
    have h_subst : ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x^n * Real.exp (-a * x^2)) ∂volume =
        ENNReal.ofReal (1 / a^((n + 1) / 2 : ℝ)) * ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^n * Real.exp (-u^2)) ∂volume := by
      sorry -- Use measure change formula for u = √a · x

    -- The normalized integral relates to the Gamma function
    have h_gamma : ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^n * Real.exp (-u^2)) ∂volume =
        ENNReal.ofReal ((1/2) * Real.Gamma ((n + 1) / 2)) := by
      sorry -- Apply Gamma function formula with substitution t = u²

    -- The Gamma function value is finite
    have h_gamma_finite : ENNReal.ofReal ((1/2) * Real.Gamma ((n + 1) / 2)) < ⊤ := by
      sorry -- Gamma function is finite for positive arguments

    sorry -- Combine the above facts

  -- Conclude by combining the split parts
  rw [h_split]
  rw [← h_symm]
  have h_double : ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x^n * Real.exp (-a * x^2)) ∂volume +
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x^n * Real.exp (-a * x^2)) ∂volume =
      2 * ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x^n * Real.exp (-a * x^2)) ∂volume := by
    ring
  rw [h_double]
  have h2_lt_top : (2 : ENNReal) < ⊤ := ENNReal.natCast_lt_top 2
  exact ENNReal.mul_lt_top h2_lt_top h_pos_finite

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
  -- normalizedGaussianLp is defined as Classical.choose (build_normalized_gaussian δ hδ)
  unfold normalizedGaussianLp
  have h := Classical.choose_spec (build_normalized_gaussian δ hδ)
  unfold suitable_window
  -- Direct from the construction: the L² norm is 1
  exact h.1

/-- Direct lemma that build_normalized_gaussian produces a suitable window -/
lemma suitable_window_of_gaussian {δ : ℝ} (hδ : 0 < δ) :
    ∀ w, Classical.choose (build_normalized_gaussian δ hδ) = w → suitable_window w := by
  intro w hw
  -- The existential witness from build_normalized_gaussian satisfies suitable_window
  have h := Classical.choose_spec (build_normalized_gaussian δ hδ)
  -- Rewrite using hw to replace Classical.choose with w
  rw [← hw]
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
