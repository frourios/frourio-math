import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore4
import Frourio.Analysis.HilbertSpaceCore
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

open MeasureTheory Measure Real Complex Set
open scoped ENNReal Topology FourierTransform

namespace Frourio
open Schwartz

section ParsevalEquivalence

set_option maxHeartbeats 1000000 in
/-- The Mellin-Plancherel formula relates to Fourier-Parseval -/
theorem parseval_identity_equivalence (σ : ℝ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (f g : Hσ σ),
    -- Additional L² and integrability conditions needed for convergence
    has_weighted_L2_norm σ f →
    Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) →
    has_weighted_L2_norm σ g →
    Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t)) →
    @inner ℂ _ _ f g = C * ∫ τ : ℝ,
      starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
      mellinTransform (g : ℝ → ℂ) (σ + I * τ) := by
  -- Get the constant from mellin_parseval_formula
  obtain ⟨C, hC_pos, hC_formula⟩ := mellin_parseval_formula σ

  use C
  constructor
  · -- C > 0 from mellin_parseval_formula
    exact hC_pos

  · -- For all f, g with the L² conditions and integrability, prove the identity
    intro f g hf_L2 hf_int hg_L2 hg_int

    -- Use the polarization identity to express inner product in terms of norms
    have h_polarization := complex_polarization_identity f g

    -- We already have hf_L2 and hg_L2 as hypotheses
    -- We also have hC_formula from the outer obtain statement

    -- Apply the polarization identity to both sides
    -- Left side: 4 * inner f g = ‖f+g‖^2 - ‖f-g‖^2 - i*‖f+ig‖^2 + i*‖f-ig‖^2
    -- Right side: Each norm can be expressed using mellin_parseval_formula

    -- Step 1: Apply the norm formula from mellin_parseval_formula to each term
    have h_fp_norm := hC_formula (f + g)
    have h_fm_norm := hC_formula (f - g)
    have h_fi_norm := hC_formula (f + Complex.I • g)
    have h_fmi_norm := hC_formula (f - Complex.I • g)

    -- Step 2: The Mellin transform is linear, so we can expand each transform
    have h_mellin_linear := mellin_transform_linear σ

    -- Step 3: Apply polarization identity in the Mellin domain
    have h_mellin_polarization : ∀ τ : ℝ,
        let F := mellinTransform (f : ℝ → ℂ) (σ + I * τ)
        let G := mellinTransform (g : ℝ → ℂ) (σ + I * τ)
        ‖F + G‖ ^ 2 - ‖F - G‖ ^ 2 - Complex.I * ‖F + Complex.I * G‖ ^ 2 +
          Complex.I * ‖F - Complex.I * G‖ ^ 2 =
          4 * (starRingEnd ℂ F * G) := by
      intro τ
      exact mellin_polarization_pointwise
        (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
        (mellinTransform (g : ℝ → ℂ) (σ + I * τ))

    -- Step A: gather the four norm identities for f±g and f±I•g
    have h_fpL2 : has_weighted_L2_norm σ (f + g) :=
      has_weighted_L2_norm_add σ hf_L2 hg_L2
    have h_fmL2 : has_weighted_L2_norm σ (f - g) :=
      has_weighted_L2_norm_sub σ hf_L2 hg_L2
    have h_fiL2 : has_weighted_L2_norm σ (f + Complex.I • g) := by
      have : has_weighted_L2_norm σ (Complex.I • g) :=
        has_weighted_L2_norm_smul σ Complex.I hg_L2
      simpa [add_comm] using has_weighted_L2_norm_add σ hf_L2 this
    have h_fmiL2 : has_weighted_L2_norm σ (f - Complex.I • g) := by
      have : has_weighted_L2_norm σ (Complex.I • g) :=
        has_weighted_L2_norm_smul σ Complex.I hg_L2
      simpa [sub_eq_add_neg] using has_weighted_L2_norm_add σ hf_L2
        (has_weighted_L2_norm_smul σ (-1 : ℂ) this)

    -- Auxiliary: integrability of the weighted LogPull for the combinations.
    -- This follows by linearity and stability of Integrable under addition/scalar.
    have h_fpInt : Integrable
        (fun t => LogPull σ (f + g) t * Complex.exp ((1 / 2 : ℝ) * t)) :=
      LogPull_integrable_add σ f g hf_int hg_int
    have h_fmInt : Integrable
        (fun t => LogPull σ (f - g) t * Complex.exp ((1 / 2 : ℝ) * t)) :=
      LogPull_integrable_sub σ f g hf_int hg_int
    have h_fiInt : Integrable
        (fun t => LogPull σ (f + Complex.I • g) t * Complex.exp ((1 / 2 : ℝ) * t)) :=
      LogPull_integrable_add_smul σ f g Complex.I hf_int hg_int
    have h_fmiInt : Integrable
        (fun t => LogPull σ (f - Complex.I • g) t * Complex.exp ((1 / 2 : ℝ) * t)) :=
      LogPull_integrable_sub_smul σ f g Complex.I hf_int hg_int

    -- Apply the norm formula to each combination
    have h_fp := h_fp_norm h_fpL2 h_fpInt
    have h_fm := h_fm_norm h_fmL2 h_fmInt
    have h_fi := h_fi_norm h_fiL2 h_fiInt
    have h_fmi := h_fmi_norm h_fmiL2 h_fmiInt

    -- Convert the ENNReal equalities to real equalities using finiteness
    -- and then to complex numbers (via `Complex.ofReal`).
    have h_ofReal_fp :
        Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖((f + g : Hσ σ) : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume).toReal)
          = Complex.ofReal (C * ∫ τ : ℝ,
              ‖mellinTransform (((f + g : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) :=
      norm_squared_to_complex_add_sub σ C (f + g) hC_pos h_fp

    have h_ofReal_fm :
        Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖((f - g : Hσ σ) : ℝ → ℂ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume).toReal)
          = Complex.ofReal (C * ∫ τ : ℝ,
              ‖mellinTransform (((f - g : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) :=
      norm_squared_to_complex_add_sub σ C (f - g) hC_pos h_fm

    have h_ofReal_fi :
        Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖((f + Complex.I • g : Hσ σ) : ℝ → ℂ) x‖ ^ 2 *
                x ^ (2 * σ - 1)) ∂volume).toReal)
          = Complex.ofReal (C * ∫ τ : ℝ,
              ‖mellinTransform (((f + Complex.I • g : Hσ σ) : ℝ → ℂ))
                (σ + I * τ)‖ ^ 2 ∂volume) :=
      norm_squared_to_complex_add_sub σ C (f + Complex.I • g) hC_pos h_fi

    have h_ofReal_fmi :
        Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖((f - Complex.I • g : Hσ σ) : ℝ → ℂ) x‖ ^ 2 *
                x ^ (2 * σ - 1)) ∂volume).toReal)
          = Complex.ofReal (C * ∫ τ : ℝ,
              ‖mellinTransform (((f - Complex.I • g : Hσ σ) : ℝ → ℂ))
                (σ + I * τ)‖ ^ 2 ∂volume) :=
      norm_squared_to_complex_add_sub σ C (f - Complex.I • g) hC_pos h_fmi

    -- Substitute into the polarization identity for ⟪f,g⟫ and rearrange.
    have h_left := h_polarization
    -- Replace each squared norm with its Mellin-domain representation.
    -- Keep the original polarization identity form for now; translating
    -- each squared norm to Mellin-domain integrals will be handled later.
    have h_left' := h_left

    -- On the Mellin side, apply polarization pointwise and integrate.
    -- First, rewrite each term via linearity of Mellin transform.
    have h_lin₁ :
        (fun τ : ℝ =>
          ‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2)
          =
        (fun τ : ℝ =>
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
             + mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2) := by
        funext τ
        rw [mellinTransform_add]
        · exact mellin_integrable_of_weighted_L2 σ f τ hf_int
        · exact mellin_integrable_of_weighted_L2 σ g τ hg_int
    have h_lin₂ :
        (fun τ : ℝ =>
          ‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2)
          =
        (fun τ : ℝ =>
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
             - mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2) := by
      funext τ
      rw [mellinTransform_sub]
      · exact mellin_integrable_of_weighted_L2 σ f τ hf_int
      · exact mellin_integrable_of_weighted_L2 σ g τ hg_int
    have h_lin₃ :
        (fun τ : ℝ =>
          ‖mellinTransform (f + Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2)
          =
        (fun τ : ℝ =>
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
             + Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2) := by
      funext τ
      congr 1
      rw [mellinTransform_add, mellinTransform_smul]
      · exact mellin_integrable_of_weighted_L2 σ f τ hf_int
      · exact mellin_integrable_smul σ g Complex.I τ hg_int
    have h_lin₄ :
        (fun τ : ℝ =>
          ‖mellinTransform (f - Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2)
          =
        (fun τ : ℝ =>
          ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
             - Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2) := by
      funext τ
      congr 1
      rw [mellinTransform_sub, mellinTransform_smul]
      · exact mellin_integrable_of_weighted_L2 σ f τ hf_int
      · exact mellin_integrable_smul σ g Complex.I τ hg_int

    -- Use these to rewrite h_left' as an integral of the pointwise polarization identity.
    have h_right :
        Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)
          - Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)
          - Complex.I * Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (f + Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)
          + Complex.I * Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (f - Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)
        = C * ∫ τ : ℝ,
            4 * (starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
              * mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume := by
      -- Pull out C and integrate the pointwise polarization identity.
      -- The inner equality is exactly `h_mellin_polarization τ`.
      -- We rewrite the four integrands and then use linearity of the integral.
      have h_pol_ae :
          (fun τ : ℝ =>
            ((‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                + mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) : ℂ)
              - ((‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                - mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) : ℂ)
              - Complex.I *
                ((‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                  + Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) : ℂ)
              + Complex.I *
                ((‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                  - Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) : ℂ))
          =ᵐ[volume]
          (fun τ : ℝ => 4 *
            (starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
              * mellinTransform (g : ℝ → ℂ) (σ + I * τ))) := by
        refine Filter.Eventually.of_forall ?_
        intro τ
        simpa using h_mellin_polarization τ
      -- Now integrate both sides and multiply by C.
      -- Convert the outer `Complex.ofReal (C * ∫ ...)` into `C * Complex.ofReal (∫ ...)`.
      -- Then use linearity of integral and the previous `h_pol_ae`.
      have h_int_equal :
          Complex.ofReal (∫ τ : ℝ,
            (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                + mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                - mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.I * Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                + Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            + Complex.I * Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                - Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
          = ∫ τ : ℝ, 4 *
              (starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
                * mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume := by
        -- Introduce abbreviations for the four real-valued integrands
        set A : ℝ → ℝ :=
          fun τ => ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                     + mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2
        set B : ℝ → ℝ :=
          fun τ => ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                     - mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2
        set C1 : ℝ → ℝ :=
          fun τ => ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                     + Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2
        set C2 : ℝ → ℝ :=
          fun τ => ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                     - Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2

        -- Define the complex-valued combination appearing in the polarization identity
        set L : ℝ → ℂ :=
          fun τ => ((A τ : ℝ) : ℂ) - ((B τ : ℝ) : ℂ)
                      - Complex.I * ((C1 τ : ℝ) : ℂ)
                      + Complex.I * ((C2 τ : ℝ) : ℂ)

        -- Step 1: Integrate the pointwise polarization identity via congruence
        have h_int_congr : ∫ τ, L τ ∂volume
            = ∫ τ : ℝ, 4 * (starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ)))
                * mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ))) ∂volume := by
          -- Use a.e. equality of integrands to identify the integrals
          have h := integral_congr_ae (μ := volume) h_pol_ae
          simpa [L] using h

        -- Step 2: Expand the left integral using linearity and `integral_ofReal`
        have h_decompose :
            Complex.ofReal (∫ τ, A τ ∂volume)
              - Complex.ofReal (∫ τ, B τ ∂volume)
              - Complex.I * Complex.ofReal (∫ τ, C1 τ ∂volume)
              + Complex.I * Complex.ofReal (∫ τ, C2 τ ∂volume)
          = ∫ τ, L τ ∂volume := by
          -- This follows from linearity of the Bochner integral and
          -- the identity ∫ (fun τ => ((r τ : ℝ) : ℂ)) = Complex.ofReal (∫ r).
          -- We defer the routine integrability bookkeeping.
          have hA_ofReal : ∫ τ, ((A τ : ℝ) : ℂ) ∂volume
              = Complex.ofReal (∫ τ, A τ ∂volume) := by simp
          have hB_ofReal : ∫ τ, ((B τ : ℝ) : ℂ) ∂volume
              = Complex.ofReal (∫ τ, B τ ∂volume) := by simp
          have hC1_ofReal : ∫ τ, ((C1 τ : ℝ) : ℂ) ∂volume
              = Complex.ofReal (∫ τ, C1 τ ∂volume) := by simp
          have hC2_ofReal : ∫ τ, ((C2 τ : ℝ) : ℂ) ∂volume
              = Complex.ofReal (∫ τ, C2 τ ∂volume) := by simp

          -- Linearity to pull apart the combination
          have h_split :
              ∫ τ, L τ ∂volume
                = (∫ τ, ((A τ : ℝ) : ℂ) ∂volume)
                  - (∫ τ, ((B τ : ℝ) : ℂ) ∂volume)
                  - Complex.I * (∫ τ, ((C1 τ : ℝ) : ℂ) ∂volume)
                  + Complex.I * (∫ τ, ((C2 τ : ℝ) : ℂ) ∂volume) := by
            -- Use the integrability lemmas for each component
            have h_int_A : Integrable (fun τ => ((A τ : ℝ) : ℂ)) volume :=
              integrable_mellin_norm_sq_add σ f g hf_L2 hf_int hg_L2 hg_int
            have h_int_B : Integrable (fun τ => ((B τ : ℝ) : ℂ)) volume :=
              integrable_mellin_norm_sq_sub σ f g hf_L2 hf_int hg_L2 hg_int
            have h_int_C1 : Integrable (fun τ => ((C1 τ : ℝ) : ℂ)) volume :=
              integrable_mellin_norm_sq_add_I σ f g hf_L2 hf_int hg_L2 hg_int
            have h_int_C2 : Integrable (fun τ => ((C2 τ : ℝ) : ℂ)) volume :=
              integrable_mellin_norm_sq_sub_I σ f g hf_L2 hf_int hg_L2 hg_int

            exact integral_polarization_split A B C1 C2 h_int_A h_int_B h_int_C1 h_int_C2

          -- Replace each term by its `ofReal` integral
          have h_rhs :
            (∫ τ, ((A τ : ℝ) : ℂ) ∂volume)
              - (∫ τ, ((B τ : ℝ) : ℂ) ∂volume)
              - Complex.I * (∫ τ, ((C1 τ : ℝ) : ℂ) ∂volume)
              + Complex.I * (∫ τ, ((C2 τ : ℝ) : ℂ) ∂volume)
            = Complex.ofReal (∫ τ, A τ ∂volume)
              - Complex.ofReal (∫ τ, B τ ∂volume)
              - Complex.I * Complex.ofReal (∫ τ, C1 τ ∂volume)
              + Complex.I * Complex.ofReal (∫ τ, C2 τ ∂volume) := by
            -- Straight replacement using `h*_ofReal`
            simp [hA_ofReal, hB_ofReal, hC1_ofReal, hC2_ofReal]

          -- Conclude by chaining the two identities
          calc
            Complex.ofReal (∫ τ, A τ ∂volume)
              - Complex.ofReal (∫ τ, B τ ∂volume)
              - Complex.I * Complex.ofReal (∫ τ, C1 τ ∂volume)
              + Complex.I * Complex.ofReal (∫ τ, C2 τ ∂volume)
              = (∫ τ, ((A τ : ℝ) : ℂ) ∂volume)
                - (∫ τ, ((B τ : ℝ) : ℂ) ∂volume)
                - Complex.I * (∫ τ, ((C1 τ : ℝ) : ℂ) ∂volume)
                + Complex.I * (∫ τ, ((C2 τ : ℝ) : ℂ) ∂volume) := by
                  simp [hA_ofReal, hB_ofReal, hC1_ofReal, hC2_ofReal]
            _ = ∫ τ, L τ ∂volume := h_split.symm

        -- Step 3: Combine the two steps
        simpa [A, B, C1, C2, L]
          using h_decompose.trans h_int_congr
      -- Pull out the constant C from `ofReal (C * ∫ ...)`.
      -- Note: `Complex.ofReal (C * A) = C • Complex.ofReal A` and
      -- we can rewrite scalar multiplication as multiplication since `C : ℝ`.
      -- Putting all together:
      have h_pullC :
          Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform (f + g : ℝ → ℂ)
            (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform (f - g : ℝ → ℂ)
            (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.I * Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform
              (f + Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            + Complex.I * Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform
              (f - Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
          = C * (Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            - Complex.I * Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f + Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
            + Complex.I * Complex.ofReal (∫ τ : ℝ,
              (‖mellinTransform (f - Complex.I • g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)) := by
        -- Rewrite `Complex.ofReal (C * ·)` and factor out `(C : ℂ)`.
        -- Then commute factors and regroup by distributivity.
        -- Finally, coe back from `(C : ℂ)` to `C` on the right.
        have :
            Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform (f + g : ℝ → ℂ)
              (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
              - Complex.ofReal (C * ∫ τ : ℝ, (‖mellinTransform (f - g : ℝ → ℂ)
              (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
              - Complex.I * Complex.ofReal (C * ∫ τ : ℝ,
                (‖mellinTransform (f + Complex.I • g : ℝ → ℂ)
                  (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
              + Complex.I * Complex.ofReal (C * ∫ τ : ℝ,
                (‖mellinTransform (f - Complex.I • g : ℝ → ℂ)
                  (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
          = (C : ℂ) * (Complex.ofReal (∫ τ : ℝ,
                (‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
              - Complex.ofReal (∫ τ : ℝ,
                (‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
              - Complex.I * Complex.ofReal (∫ τ : ℝ,
                (‖mellinTransform (f + Complex.I • g : ℝ → ℂ)
                  (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
              + Complex.I * Complex.ofReal (∫ τ : ℝ,
                (‖mellinTransform (f - Complex.I • g : ℝ → ℂ)
                  (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)) := by
          -- Push `C` inside `ofReal` as a complex scalar and factor it out.
          -- Also commute it across `I` in the last two terms.
          simp [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc, mul_add, mul_sub,
            sub_eq_add_neg]
        simpa using this
      -- Combine the last two displays.
      calc
        Complex.ofReal (C * ∫ τ : ℝ,
            (‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
          - Complex.ofReal (C * ∫ τ : ℝ,
              (‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
          - Complex.I * Complex.ofReal (C * ∫ τ : ℝ,
              (‖mellinTransform (f + Complex.I • g : ℝ → ℂ)
                (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
          + Complex.I * Complex.ofReal (C * ∫ τ : ℝ,
              (‖mellinTransform (f - Complex.I • g : ℝ → ℂ)
                (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
          = C * (Complex.ofReal (∫ τ : ℝ,
                (‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
              - Complex.ofReal (∫ τ : ℝ,
                  (‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
              - Complex.I * Complex.ofReal (∫ τ : ℝ,
                  (‖mellinTransform (f + Complex.I • g : ℝ → ℂ)
                    (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
              + Complex.I * Complex.ofReal (∫ τ : ℝ,
                  (‖mellinTransform (f - Complex.I • g : ℝ → ℂ)
                    (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)) := h_pullC
        _ = C * ∫ τ : ℝ,
              4 * (starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
                * mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume := by
              -- h_int_equal gives us the result for separated transforms
              -- We need to relate mellinTransform (f + g) to mellinTransform f + mellinTransform g
              rw [show Complex.ofReal (∫ τ : ℝ,
                      (‖mellinTransform (f + g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
                    - Complex.ofReal (∫ τ : ℝ,
                        (‖mellinTransform (f - g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
                    - Complex.I * Complex.ofReal (∫ τ : ℝ,
                        (‖mellinTransform (f + Complex.I • g : ℝ → ℂ)
                          (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
                    + Complex.I * Complex.ofReal (∫ τ : ℝ,
                        (‖mellinTransform (f - Complex.I • g : ℝ → ℂ)
                          (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
                  = Complex.ofReal (∫ τ : ℝ,
                      (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                          + mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
                    - Complex.ofReal (∫ τ : ℝ,
                        (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                          - mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
                    - Complex.I * Complex.ofReal (∫ τ : ℝ,
                        (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                          + Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
                    + Complex.I * Complex.ofReal (∫ τ : ℝ,
                        (‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)
                          - Complex.I * mellinTransform (g : ℝ → ℂ) (σ + I * τ)‖ ^ 2 : ℝ) ∂volume)
                  from by
                    -- Rewrite each integral via linearity of Mellin transform on the integrand
                    -- using `h_lin₁` through `h_lin₄`.
                    simp [h_lin₁, h_lin₂, h_lin₃, h_lin₄]]
              rw [h_int_equal]

    sorry

/-- The Mellin transform preserves the L² structure up to normalization -/
theorem mellin_isometry_normalized (σ : ℝ) :
    ∃ (C : ℝ) (U : Hσ σ →L[ℂ] Lp ℂ 2 volume),
    C > 0 ∧ ∀ f : Hσ σ, ‖U f‖ = C * ‖f‖ ∧
    (U f : ℝ → ℂ) = fun τ : ℝ => mellinTransform (f : ℝ → ℂ) (σ + I * ↑τ) := by
  -- Construct the normalized Mellin transform operator
  sorry

end ParsevalEquivalence

section ClassicalParseval

/-- Connection between Mellin-Parseval and Fourier-Parseval -/
theorem mellin_fourier_parseval_connection (σ : ℝ) (f : Hσ σ) :
    let g := fun t => (f : ℝ → ℂ) (Real.exp t) * Complex.exp ((σ - (1/2)) * t)
    ∃ (hg : MemLp g 2 volume), ‖f‖ ^ 2 = ‖MemLp.toLp g hg‖ ^ 2 := by
  -- The weighted L² norm on (0,∞) with weight x^(2σ-1)
  -- equals the L² norm on ℝ after the transformation
  sorry

/-- The Mellin transform is unitarily equivalent to Fourier transform -/
theorem mellin_fourier_unitary_equivalence (σ : ℝ) :
    ∃ (V : Hσ σ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ)),
    ∀ (f : Hσ σ) (τ : ℝ),
    ∃ (c : ℂ), c ≠ 0 ∧ mellinTransform (f : ℝ → ℂ) (σ + I * τ) = c * (V f τ) := by
  -- The unitary equivalence via logarithmic change of variables
  sorry

end ClassicalParseval

section Applications

/-- Mellin convolution theorem via Parseval -/
theorem mellin_convolution_parseval (σ : ℝ) (f g : Hσ σ) :
    ∫ τ : ℝ, mellinTransform f (σ + I * τ) * starRingEnd ℂ (mellinTransform g (σ + I * τ)) =
    (2 * Real.pi) * ∫ x in Set.Ioi (0 : ℝ), (f x) *
    starRingEnd ℂ (g x) * (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := by
  -- This is the correct Mellin-Parseval identity for inner products
  -- ∫ M_f(σ+iτ) * conj(M_g(σ+iτ)) dτ = 2π * ∫ f(x) * conj(g(x)) * x^(2σ-1) dx
  -- Using starRingEnd ℂ for complex conjugation and proper complex exponentiation
  sorry

/-- Energy conservation in Mellin space -/
theorem mellin_energy_conservation (σ : ℝ) (f : Hσ σ) :
    ∫ x in Set.Ioi (0 : ℝ), ‖(f : ℝ → ℂ) x‖ ^ 2 * (x : ℝ) ^ (2 * σ - 1) ∂volume =
    (1 / (2 * Real.pi)) * ∫ τ : ℝ, ‖mellinTransform f (σ + I * τ)‖ ^ 2 := by
  -- Direct consequence of mellin_parseval_formula
  sorry

end Applications

end Frourio
