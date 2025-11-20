import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore2
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

/-- Integrability is preserved under scalar multiplication -/
lemma mellin_integrable_smul (σ : ℝ) (f : Hσ σ) (c : ℂ) (τ : ℝ)
    (hf_int : Integrable (fun t => LogPull σ f t)) :
    IntegrableOn (fun t : ℝ => (c • f : ℝ → ℂ) t * t ^ (σ + I * τ - 1)) (Set.Ioi 0) := by
  classical
  -- Start from the base integrability for `f` at `σ + i τ`.
  have h_base : IntegrableOn (fun t : ℝ => (f : ℝ → ℂ) t * t ^ (σ + I * τ - 1)) (Set.Ioi 0) :=
    mellin_integrable_of_weighted_L1 σ f τ hf_int
  -- View IntegrableOn as Integrable under the restricted measure.
  have h_base_int :
      Integrable (fun t : ℝ => (f : ℝ → ℂ) t * t ^ (σ + I * τ - 1))
        (volume.restrict (Set.Ioi 0)) := h_base
  -- Multiply by the constant `c`.
  have h_const :
      Integrable (fun t : ℝ => c * ((f : ℝ → ℂ) t * t ^ (σ + I * τ - 1)))
        (volume.restrict (Set.Ioi 0)) := h_base_int.const_mul c
  -- Identify the target integrand with the constant multiple.
  have h_ae :
      (fun t : ℝ => (c • (f : ℝ → ℂ)) t * t ^ (σ + I * τ - 1))
        =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ => c * ((f : ℝ → ℂ) t * t ^ (σ + I * τ - 1))) :=
    Filter.Eventually.of_forall (by
      intro t; simp [Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc])
  -- Conclude integrability for the smul integrand.
  exact (Integrable.congr h_const h_ae.symm)

/-- Integrability of the squared norm of a rescaled Fourier integral.
Given `gf` with Fourier integral in L², the rescaled function
`τ ↦ ‖fourierIntegral gf (-τ / (2π))‖²` is integrable. -/
lemma integrable_fourierIntegral_rescale_sq_norm
    (gf : ℝ → ℂ)
    (hFI_L2 : MemLp (fun ξ : ℝ => fourierIntegral gf ξ) 2 volume)
    (h_fourier_meas : AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gf ξ) volume)
    (h_comp_meas : AEStronglyMeasurable
        (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) volume) :
    Integrable (fun τ : ℝ => ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2) volume := by
  classical
  -- Step 1: use L²-membership of ξ ↦ fourierIntegral gf ξ to get
  -- integrability of its squared norm in ξ.
  have h_unscaled_int :
      Integrable (fun ξ : ℝ => ‖fourierIntegral gf ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (μ := volume)
      (f := fun ξ : ℝ => fourierIntegral gf ξ) h_fourier_meas).1 hFI_L2
  -- Step 2: establish a.e.-strong measurability for the squared norm after rescaling.
  have h_sq_meas : AEStronglyMeasurable
      (fun τ : ℝ => ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2) volume := by
    -- Measurability follows from h_comp_meas via norm and continuous pow.
    exact (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable
      (h_comp_meas.norm.aemeasurable)
  -- Step 3: reduce finiteness to the unscaled side via the rescaling identity
  -- ∫τ ‖FI(gf)(-τ/(2π))‖² = (2π) ∫ξ ‖FI(gf)(ξ)‖².
  -- Using h_unscaled_int, the RHS is finite, hence the LHS is finite as well.
  refine ⟨h_sq_meas, ?_⟩
  -- Nonnegativity of the integrand allows working with (real) integrals.
  have h_nonneg :
      (∀ τ : ℝ, 0 ≤ ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2) := by
    intro τ; simp
  -- Name the two integrals for clarity and apply the rescaling formula.
  set Iτ : ℝ := ∫ τ : ℝ, ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2 with hIτ
  set Iξ : ℝ := ∫ ξ : ℝ, ‖fourierIntegral gf ξ‖ ^ 2 with hIξ
  have h_rescale : Iτ = (2 * Real.pi) * Iξ := by
    rw [hIτ, hIξ]
    -- Align any potential `𝓕` notation (Real.fourierIntegral) with `fourierIntegral`.
    have h := integral_fourierIntegral_rescale_sq gf
    simp [fourierIntegral_eq_real] at h
    simpa using h
  -- Finiteness of the unscaled side from L²-membership.
  have h_unscaled_fin : HasFiniteIntegral (fun ξ : ℝ => ‖fourierIntegral gf ξ‖ ^ 2) :=
    h_unscaled_int.hasFiniteIntegral
  -- Convert finiteness across the rescaling identity to obtain the target.
  -- The right-hand side is finite; hence so is the left-hand side.
  -- Package as `HasFiniteIntegral` for the τ-integrand.

  -- 1) Work with nonnegativity to switch to `lintegral` via `hasFiniteIntegral_iff_ofReal`.
  -- 2) Use change of variables on the lintegral side to relate τ- and ξ-integrals.
  -- 3) Conclude from `h_unscaled_fin` (the ξ-side finiteness).

  -- Preparations: nonnegativity a.e. for both ξ- and τ-side functions.
  have h_nonneg_ae_τ :
      0 ≤ᵐ[volume] fun τ : ℝ => ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2 :=
    Filter.Eventually.of_forall (by intro τ; simp)
  have h_nonneg_ae_ξ :
      0 ≤ᵐ[volume] fun ξ : ℝ => ‖fourierIntegral gf ξ‖ ^ 2 :=
    Filter.Eventually.of_forall (by intro ξ; simp)

  -- Abbreviations for the two nonnegative functions.
  set Fτ : ℝ → ℝ := fun τ => ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2 with hFτ
  set Fξ : ℝ → ℝ := fun ξ => ‖fourierIntegral gf ξ‖ ^ 2 with hFξ

  -- Convert ξ-side `HasFiniteIntegral` to a `lintegral` bound.
  have h_lint_ξ_lt_top :
      (∫⁻ ξ : ℝ, ENNReal.ofReal (Fξ ξ) ∂volume) < ∞ := by
    -- direct from `h_unscaled_fin` using nonnegativity
    have := (hasFiniteIntegral_iff_ofReal (μ := volume)
      (f := fun ξ : ℝ => Fξ ξ) h_nonneg_ae_ξ).1 h_unscaled_fin
    simpa [Fξ, hFξ] using this

  -- Target: τ-side `HasFiniteIntegral` via the same equivalence.
  refine (hasFiniteIntegral_iff_ofReal (μ := volume)
      (f := fun τ : ℝ => Fτ τ) h_nonneg_ae_τ).2 ?_

  -- Change of variables on the lintegral side:
  -- One can show the exact scaling identity at the level of lintegrals:
  --   ∫⁻ τ, ofReal (Fτ τ) = ofReal (|(-1 / (2π))⁻¹|) * ∫⁻ ξ, ofReal (Fξ ξ),
  -- by applying the change of variables τ ↦ (-1 / (2π)) * τ.
  -- This is `lintegral_comp_mul_left`.
  have h_a_ne : ((-1 : ℝ) / (2 * Real.pi)) ≠ 0 := by
    have h2π : (2 * Real.pi) ≠ 0 := by
      have : (2 : ℝ) ≠ 0 := by norm_num
      exact mul_ne_zero this Real.pi_ne_zero
    have h₁ : (-1 : ℝ) ≠ 0 := by norm_num
    simpa [div_eq_mul_inv] using mul_ne_zero h₁ (inv_ne_zero h2π)
  have h_scale :
      (∫⁻ τ : ℝ, ENNReal.ofReal (Fτ τ) ∂volume)
        = (ENNReal.ofReal (|(-1 / (2 * Real.pi))⁻¹|)) *
            (∫⁻ ξ : ℝ, ENNReal.ofReal (Fξ ξ) ∂volume) := by
    -- AEMeasurability of the ξ-side ENNReal integrand under Lebesgue
    have hFξ_aesm : AEStronglyMeasurable (fun ξ : ℝ => Fξ ξ) volume :=
      h_unscaled_int.aestronglyMeasurable
    have hf_vol : AEMeasurable (fun ξ : ℝ => ENNReal.ofReal (Fξ ξ)) volume :=
      (hFξ_aesm.aemeasurable).ennreal_ofReal
    have := Measure.lintegral_comp_mul_left
        ((-1 : ℝ) / (2 * Real.pi)) h_a_ne (fun ξ : ℝ => ENNReal.ofReal (Fξ ξ)) hf_vol
    -- LHS becomes ∫ ofReal (Fξ ((-1)/(2π) * τ)) = ∫ ofReal (Fτ τ)
    -- by the definition of Fτ.
    simpa [Fτ, Fξ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using this

  -- Evaluate the absolute scaling constant |(-1 / (2π))⁻¹| = 2π.
  have h_abs :
      ENNReal.ofReal (|(-1 / (2 * Real.pi))⁻¹|) = ENNReal.ofReal (2 * Real.pi) := by
    have hpos : 0 ≤ 2 * Real.pi := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg this Real.pi_pos.le
    have h_inv : (-1 / (2 * Real.pi))⁻¹ = -(2 * Real.pi) := by
      have : (2 * Real.pi) ≠ 0 := by
        have : (2 : ℝ) ≠ 0 := by norm_num
        exact mul_ne_zero this Real.pi_ne_zero
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simp [h_inv, abs_neg, abs_of_nonneg hpos]

  -- Use the scaling identity to reduce finiteness to the ξ-side, which we have.
  have h_const_fin : ENNReal.ofReal (2 * Real.pi) < ∞ := by simp
  have :
      (∫⁻ τ : ℝ, ENNReal.ofReal (Fτ τ) ∂volume) < ∞ := by
    -- Combine `h_scale`, `h_abs`, and the finiteness of the ξ-side lintegral.
    rw [h_scale, h_abs]
    exact ENNReal.mul_lt_top h_const_fin h_lint_ξ_lt_top
  exact this

/-- Integrability of norm squared of sum of Mellin transforms -/
lemma integrable_mellin_norm_sq_add (σ : ℝ) (f g : Hσ σ)
    (hf_L2 : has_weighted_L2_norm σ f)
    (hf_int : Integrable (fun t => LogPull σ f t))
    (hg_L2 : has_weighted_L2_norm σ g)
    (hg_int : Integrable (fun t => LogPull σ g t)) :
    Integrable (fun τ : ℝ => ((‖mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ))
    + mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ))‖ ^ 2 : ℝ) : ℂ)) volume := by
  classical
  -- Abbreviations for the Mellin transforms of `f` and `g` along the line `σ + iτ`.
  set F : ℝ → ℂ :=
    fun τ => mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ)) with hF
  set G : ℝ → ℂ :=
    fun τ => mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ)) with hG

  -- Strong measurability of the target integrand.
  have h_meas_F : AEStronglyMeasurable F volume := by
    -- Express F via a Fourier integral of a measurable function and use
    -- `integral_prod_right'` to get a.e.-strong measurability.
    classical
    -- Define the auxiliary function for the Fourier side
    set gf : ℝ → ℂ := fun t => LogPull σ f t with hgf_def
    -- Measurability of `gf`
    have h_gf_meas : Measurable gf := by
      simpa [gf, hgf_def] using LogPull_measurable σ f
    -- Kernel measurability on the product space
    have h_kernel_meas : Measurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2) := by
      -- fourierKernel ξ t = exp(ofReal (-(2π) * ξ * t) * I)
      unfold fourierKernel
      apply Measurable.cexp
      apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * a.1 * a.2))
      apply Measurable.neg
      have : Measurable (fun a : ℝ × ℝ => a.1 * a.2) := by
        exact measurable_fst.mul measurable_snd
      convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
      ext a
      ring
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gf p.2)
          (volume.prod volume) := by
      -- Product measurability from kernel and gf composed with `snd`.
      have : Measurable (fun p : ℝ × ℝ => gf p.2) := h_gf_meas.comp measurable_snd
      exact (h_kernel_meas.mul this).aestronglyMeasurable
    -- Measurability of the Fourier integral map ξ ↦ ∫ fourierKernel ξ t * gf t dt
    have h_fourier_meas :
        AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gf ξ) volume := by
      simpa [fourierIntegral]
        using
          (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
            (μ := volume) (ν := volume)
            (f := fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gf p.2)
            h_integrand_meas)
    -- Compose with the linear change of variable τ ↦ -τ / (2π)
    have h_arg_meas : Measurable (fun τ : ℝ => -τ / (2 * Real.pi)) := by
      have : Measurable (fun τ : ℝ => ((-1) / (2 * Real.pi)) * τ) :=
        measurable_const.mul measurable_id
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this
    -- Identify F with the composed Fourier integral and conclude measurability.
    have hF_meas_aux :
        AEStronglyMeasurable
          (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) volume := by
      -- Prove measurability directly via `integral_prod_right'` with a rescaled kernel
      have h_kernel_scaled_meas :
          Measurable (fun p : ℝ × ℝ =>
            fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
        -- fourierKernel ξ t = exp(ofReal (-(2π) * ξ * t) * I)
        unfold fourierKernel
        -- Build the measurable argument of the complex exponential
        apply Measurable.cexp
        apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
        apply Measurable.neg
        have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
          apply Measurable.mul
          · apply Measurable.div_const
            exact measurable_fst.neg
          · exact measurable_snd
        convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
        ext a
        field_simp
        ring
      have h_integrand_meas' :
          AEStronglyMeasurable
            (fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
            (volume.prod volume) := by
        -- Product measurability from the scaled kernel and gf ∘ snd
        have : Measurable (fun p : ℝ × ℝ => gf p.2) :=
          h_gf_meas.comp measurable_snd
        exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
      -- Now integrate out the second coordinate and obtain AEStronglyMeasurable in τ
      simpa [fourierIntegral]
        using
          (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
            (μ := volume) (ν := volume)
            (f := fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
            h_integrand_meas')
    simpa [F, hgf_def, mellin_logpull_fourierIntegral] using hF_meas_aux
  have h_meas_G : AEStronglyMeasurable G volume := by
    -- Same argument as for `h_meas_F`, replacing `f` with `g`.
    classical
    -- Auxiliary function for the Fourier side
    set gg : ℝ → ℂ := fun t => LogPull σ g t with hgg_def
    -- Measurability of `gg`
    have h_gg_meas : Measurable gg := by
      simpa [gg, hgg_def] using LogPull_measurable σ g
    -- Kernel measurability on the product space
    have h_kernel_meas : Measurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2) := by
      unfold fourierKernel
      apply Measurable.cexp
      apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * a.1 * a.2))
      apply Measurable.neg
      have : Measurable (fun a : ℝ × ℝ => a.1 * a.2) := by
        exact measurable_fst.mul measurable_snd
      convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
      ext a
      ring
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gg p.2)
          (volume.prod volume) := by
      have : Measurable (fun p : ℝ × ℝ => gg p.2) := h_gg_meas.comp measurable_snd
      exact (h_kernel_meas.mul this).aestronglyMeasurable
    -- Measurability of the Fourier integral map for gg
    have h_fourier_meas :
        AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gg ξ) volume := by
      simpa [fourierIntegral]
        using
          (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
            (μ := volume) (ν := volume)
            (f := fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gg p.2)
            h_integrand_meas)
    -- Compose with τ ↦ -τ / (2π)
    have h_arg_meas : Measurable (fun τ : ℝ => -τ / (2 * Real.pi)) := by
      have : Measurable (fun τ : ℝ => ((-1) / (2 * Real.pi)) * τ) :=
        measurable_const.mul measurable_id
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hG_meas_aux :
        AEStronglyMeasurable
          (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) volume := by
      -- Prove measurability directly via `integral_prod_right'` with a rescaled kernel
      have h_kernel_scaled_meas :
          Measurable (fun p : ℝ × ℝ =>
            fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
        unfold fourierKernel
        -- Build the measurable argument of the complex exponential
        apply Measurable.cexp
        apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
        apply Measurable.neg
        have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
          apply Measurable.mul
          · apply Measurable.div_const
            exact measurable_fst.neg
          · exact measurable_snd
        convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
        ext a
        field_simp
        ring
      have h_integrand_meas' :
          AEStronglyMeasurable
            (fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
            (volume.prod volume) := by
        have : Measurable (fun p : ℝ × ℝ => gg p.2) :=
          h_gg_meas.comp measurable_snd
        exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
      -- Now integrate out the second coordinate and obtain AEStronglyMeasurable in τ
      simpa [fourierIntegral]
        using
          (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
            (μ := volume) (ν := volume)
            (f := fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
            h_integrand_meas')
    simpa [G, hgg_def, mellin_logpull_fourierIntegral] using hG_meas_aux
  have h_meas : AEStronglyMeasurable
      (fun τ : ℝ => ((‖F τ + G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
    -- Combine measurability of F and G with continuity of norm, pow, and ofReal.
    have h_add : AEStronglyMeasurable (fun τ : ℝ => F τ + G τ) volume :=
      h_meas_F.add h_meas_G
    have h_norm : AEStronglyMeasurable (fun τ : ℝ => ‖F τ + G τ‖) volume :=
      h_add.norm
    have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖F τ + G τ‖ ^ 2 : ℝ)) volume := by
      -- compose with the continuous map x ↦ x^2
      exact (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable
        h_norm.aemeasurable
    -- lift to ℂ via Complex.ofReal
    exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
      h_sq_real.aemeasurable

  -- Pointwise inequality: ‖F+G‖^2 ≤ 2 (‖F‖^2 + ‖G‖^2), used for domination.
  have h_bound_ae :
      (∀ᵐ τ ∂volume,
        ‖(((‖F τ + G τ‖ ^ 2 : ℝ) : ℂ))‖
          ≤ ‖((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)‖) := by
    refine Filter.Eventually.of_forall ?_
    intro τ
    have h_nonneg : 0 ≤ (‖F τ + G τ‖ ^ 2 : ℝ) := by exact sq_nonneg _
    have h_nonneg' : 0 ≤ (2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) := by
      have h0 : 0 ≤ (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : 0 ≤ (2 : ℝ) * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
        exact mul_nonneg (by norm_num) h0
      simpa [mul_comm] using this
    have h_ineq : (‖F τ + G τ‖ ^ 2 : ℝ)
        ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
      -- Step 1: square the triangle inequality
      have h_add_le : ‖F τ + G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := norm_add_le (F τ) (G τ)
      have h_sq_le : (‖F τ + G τ‖ : ℝ) * ‖F τ + G τ‖
            ≤ (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖) := by
        refine mul_le_mul h_add_le h_add_le ?_ ?_
        · -- 0 ≤ ‖F+G‖
          exact norm_nonneg (F τ + G τ)
        · -- 0 ≤ ‖F‖ + ‖G‖
          exact add_nonneg (norm_nonneg (F τ)) (norm_nonneg (G τ))
      -- Step 2: expand and apply 2ab ≤ a^2 + b^2 with a=‖F‖, b=‖G‖
      have h_amgm : (2 : ℝ) * (‖F τ‖ * ‖G τ‖) ≤ ‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 := by
        -- From (‖F‖ - ‖G‖)^2 ≥ 0
        have h := sq_nonneg (‖F τ‖ - ‖G τ‖)
        -- (a - b)^2 = a^2 - 2ab + b^2
        have h_expand : (‖F τ‖ - ‖G τ‖) ^ 2 = ‖F τ‖ ^ 2 - 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2 := by ring
        rw [h_expand] at h
        linarith
      -- Combine the two steps and simplify polynomials
      have h_poly :
          (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖)
            ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
        -- Expand (a+b)^2 and bound the middle term by h_amgm
        have h_expand : (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖)
            = ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2 := by
          ring
        have h_mid : ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2
            ≤ ‖F τ‖ ^ 2 + (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) + ‖G τ‖ ^ 2 := by
          -- add h_amgm in the middle
          linarith [h_amgm]
        have h_eq : ‖F τ‖ ^ 2 + (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) + ‖G τ‖ ^ 2
            = 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by ring
        have h_upper :
            ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2
              ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
          simpa [h_eq] using h_mid
        -- Convert back using the expansion
        simpa [h_expand]
          using h_upper
      -- Convert the products to squares and chain inequalities
      simpa [pow_two] using h_sq_le.trans h_poly
    have h_norm_coe :
        ‖(((‖F τ + G τ‖ ^ 2 : ℝ) : ℂ))‖ = (‖F τ + G τ‖ ^ 2 : ℝ) := by
      simp [Real.norm_eq_abs, Complex.norm_real, abs_of_nonneg h_nonneg]
    have h_norm_coe' :
        ‖((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)‖
          = (2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_nonneg']
    rw [h_norm_coe, h_norm_coe']
    exact h_ineq

  -- Integrability of the majorant: 2 * (‖F‖^2 + ‖G‖^2).
  have h_int_Fsq : Integrable (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
    classical
    -- Strategy: obtain L²-membership for F via Mellin–Plancherel/isometry,
    -- then use `memLp_two_iff_integrable_sq_norm` and lift to ℂ via `ofReal`.
    have hF_L2 : MemLp F 2 volume := by
      classical
      -- Express F as a rescaled Fourier integral of a weighted LogPull
      set gf : ℝ → ℂ := fun t => LogPull σ f t with hgf_def
      -- Assumptions (to be provided upstream): gf ∈ L¹ ∩ L²
      have hgL1 : Integrable gf := by
        -- Direct from the hypothesis on the weighted LogPull of f
        simpa [gf, hgf_def] using hf_int
      have hgL2 : MemLp gf 2 volume := by
        -- Use the weighted L² hypothesis for f via `weighted_LogPull_memLp`
        simpa [gf, hgf_def] using weighted_LogPull_memLp (σ := σ) (f := f) hf_L2
      -- Fourier-Plancherel: the Fourier integral of gf is in L²
      have hFI_L2 : MemLp (fun ξ : ℝ => fourierIntegral gf ξ) 2 volume :=
        fourierIntegral_memLp_L1_L2 hgL1 hgL2
      -- Compose with the linear rescaling τ ↦ -τ/(2π)
      have h_fourier_meas : AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gf ξ) volume :=
        hFI_L2.1
      have h_arg_meas : Measurable (fun τ : ℝ => -τ / (2 * Real.pi)) := by
        have : Measurable (fun τ : ℝ => ((-1) / (2 * Real.pi)) * τ) :=
          measurable_const.mul measurable_id
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      have h_comp_meas : AEStronglyMeasurable
          (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) volume := by
        -- Provide measurability directly via a rescaled kernel and Fubini
        -- First, `gf` is measurable
        have h_gf_meas : Measurable gf := by
          simpa [gf, hgf_def] using LogPull_measurable σ f
        -- Next, the rescaled kernel is measurable on the product space
        have h_kernel_scaled_meas :
            Measurable (fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
          unfold fourierKernel
          apply Measurable.cexp
          apply Measurable.mul _ measurable_const
          apply Complex.measurable_ofReal.comp
          show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
          apply Measurable.neg
          have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
            apply Measurable.mul
            · apply Measurable.div_const
              exact measurable_fst.neg
            · exact measurable_snd
          convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
          ext a; field_simp; ring
        -- Build the integrand measurability on the product
        have h_integrand_meas' :
            AEStronglyMeasurable (fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
              (volume.prod volume) := by
          have : Measurable (fun p : ℝ × ℝ => gf p.2) :=
            h_gf_meas.comp measurable_snd
          exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
        -- Integrate out the second coordinate to get measurability in τ
        simpa [fourierIntegral]
          using
            (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
              (μ := volume) (ν := volume)
              (f := fun p : ℝ × ℝ =>
                fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
              h_integrand_meas')
      -- Integrability of the squared norm of the rescaled Fourier integral
      have h_comp_int : Integrable
          (fun τ : ℝ => ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2) volume :=
        integrable_fourierIntegral_rescale_sq_norm gf hFI_L2 h_fourier_meas h_comp_meas
      -- Conclude L² membership via the p=2 integrability equivalence
      have h_comp_L2 : MemLp (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) 2 volume :=
        (memLp_two_iff_integrable_sq_norm (μ := volume)
          (f := fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) h_comp_meas).2 h_comp_int
      -- Identify with F via the Mellin–Fourier relation
      simpa [F, hgf_def, mellin_logpull_fourierIntegral]
        using h_comp_L2
    -- Real-valued integrability of the squared norm follows from L²-membership.
    have h_real : Integrable (fun τ : ℝ => (‖F τ‖ ^ 2 : ℝ)) volume :=
      (memLp_two_iff_integrable_sq_norm (μ := volume) (f := F) hF_L2.1).1 hF_L2
    -- Lift to a complex-valued integrable function via `Complex.ofReal`.
    have h_meas_sq : AEStronglyMeasurable
        (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
      -- measurability via composition: τ ↦ ‖F τ‖ is a.e.-s.m., then pow, then ofReal
      have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖F τ‖ ^ 2 : ℝ)) volume :=
        (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable
          (hF_L2.1.norm.aemeasurable)
      exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
        h_sq_real.aemeasurable
    have h_fin : HasFiniteIntegral
        (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
      -- Compare the Bochner norm with the real absolute value
      have h_fin_real := h_real.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_norm]
      calc ∫⁻ a, ENNReal.ofReal ‖(((‖F a‖ ^ 2 : ℝ) : ℂ))‖
          = ∫⁻ a, ENNReal.ofReal (‖F a‖ ^ 2) := by
            congr 1
            ext τ
            have h_nonneg : 0 ≤ ‖F τ‖ ^ 2 := sq_nonneg _
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_nonneg]
        _ < ⊤ := by
            have : (fun a => ENNReal.ofReal (‖F a‖ ^ 2)) =
                (fun a => ENNReal.ofReal ‖(‖F a‖ ^ 2 : ℝ)‖) := by
              ext a
              congr
              exact (Real.norm_of_nonneg (sq_nonneg _)).symm
            rw [this, ← hasFiniteIntegral_iff_norm]
            exact h_fin_real
    exact ⟨h_meas_sq, h_fin⟩
  have h_int_Gsq : Integrable (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
    classical
    -- Mirror the argument for `F`, now with `g`.
    -- Step 1: obtain L²-membership for G via the Fourier side.
    have hG_L2 : MemLp G 2 volume := by
      classical
      -- Auxiliary function on the log side for `g`.
      set gg : ℝ → ℂ := fun t => LogPull σ g t with hgg_def
      -- Assumptions: gg ∈ L¹ and in L² (weighted hypothesis for g).
      have hgL1 : Integrable gg := by
        simpa [gg, hgg_def] using hg_int
      have hgL2 : MemLp gg 2 volume := by
        simpa [gg, hgg_def] using weighted_LogPull_memLp (σ := σ) (f := g) hg_L2
      -- Fourier-Plancherel placeholder: Fourier integral of gg lies in L².
      have hFI_L2 : MemLp (fun ξ : ℝ => fourierIntegral gg ξ) 2 volume :=
        fourierIntegral_memLp_L1_L2 hgL1 hgL2
      -- Compose with the rescaling τ ↦ -τ/(2π) and obtain measurability.
      have h_fourier_meas : AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gg ξ) volume :=
        hFI_L2.1
      have h_comp_meas : AEStronglyMeasurable
          (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) volume := by
        -- Direct measurability via kernel measurability and `integral_prod_right'`.
        -- Kernel measurability on the product space with the rescaled parameter.
        have h_kernel_scaled_meas :
            Measurable (fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
          unfold fourierKernel
          apply Measurable.cexp
          apply Measurable.mul _ measurable_const
          apply Complex.measurable_ofReal.comp
          show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
          apply Measurable.neg
          have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
            apply Measurable.mul
            · apply Measurable.div_const
              exact measurable_fst.neg
            · exact measurable_snd
          convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
          ext a; field_simp; ring
        -- Measurability of gg ∘ snd
        have h_gg_meas : Measurable gg := by
          simpa [gg, hgg_def] using LogPull_measurable σ g
        have h_integrand_meas' :
            AEStronglyMeasurable (fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
              (volume.prod volume) := by
          have : Measurable (fun p : ℝ × ℝ => gg p.2) :=
            h_gg_meas.comp measurable_snd
          exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
        -- Integrate out the second coordinate to get measurability in τ
        simpa [fourierIntegral]
          using
            (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
              (μ := volume) (ν := volume)
              (f := fun p : ℝ × ℝ =>
                fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
              h_integrand_meas')
      -- Integrability of the squared norm after rescaling.
      have h_comp_int : Integrable
          (fun τ : ℝ => ‖fourierIntegral gg (-τ / (2 * Real.pi))‖ ^ 2) volume :=
        integrable_fourierIntegral_rescale_sq_norm gg hFI_L2 h_fourier_meas h_comp_meas
      -- Conclude L² membership for the composed map, then identify with `G`.
      have h_comp_L2 : MemLp (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) 2 volume :=
        (memLp_two_iff_integrable_sq_norm (μ := volume)
          (f := fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) h_comp_meas).2 h_comp_int
      simpa [G, hgg_def, mellin_logpull_fourierIntegral]
        using h_comp_L2
    -- Step 2: real integrability of ‖G‖² follows from L²-membership.
    have h_real : Integrable (fun τ : ℝ => (‖G τ‖ ^ 2 : ℝ)) volume :=
      (memLp_two_iff_integrable_sq_norm (μ := volume) (f := G) hG_L2.1).1 hG_L2
    -- Step 3: lift to a complex-valued integrable via ofReal.
    have h_meas_sq : AEStronglyMeasurable
        (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
      -- measurability via composition on the real side and `ofReal`.
      have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖G τ‖ ^ 2 : ℝ)) volume :=
        (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable
          (hG_L2.1.norm.aemeasurable)
      exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
        h_sq_real.aemeasurable
    have h_fin : HasFiniteIntegral
        (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
      -- Compare norms with the real absolute value and use `h_real`.
      have h_fin_real := h_real.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_norm]
      calc ∫⁻ a, ENNReal.ofReal ‖(((‖G a‖ ^ 2 : ℝ) : ℂ))‖
          = ∫⁻ a, ENNReal.ofReal (‖G a‖ ^ 2) := by
            congr 1; ext τ
            have h_nonneg : 0 ≤ ‖G τ‖ ^ 2 := sq_nonneg _
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_nonneg]
        _ < ⊤ := by
            have : (fun a => ENNReal.ofReal (‖G a‖ ^ 2)) =
                (fun a => ENNReal.ofReal ‖(‖G a‖ ^ 2 : ℝ)‖) := by
              ext a; congr
              exact (Real.norm_of_nonneg (sq_nonneg _)).symm
            rw [this, ← hasFiniteIntegral_iff_norm]
            exact h_fin_real
    exact ⟨h_meas_sq, h_fin⟩
  have h_int_sum : Integrable
      (fun τ : ℝ => (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) : ℂ))) volume := by
    -- Combine integrability of the two squares and identify with `ofReal` of the sum.
    have h := h_int_Fsq.add h_int_Gsq
    have h_ae :
        (fun τ => ((‖F τ‖ ^ 2 : ℝ) : ℂ) + ((‖G τ‖ ^ 2 : ℝ) : ℂ))
          =ᵐ[volume]
        (fun τ => (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) : ℂ))) := by
      refine Filter.Eventually.of_forall ?_
      intro τ; simp [Complex.ofReal_add, add_comm, add_left_comm, add_assoc]
    exact (Integrable.congr h h_ae)
  have h_int_majorant' : Integrable
      (fun τ : ℝ => ((2 : ℂ) * (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) : ℂ)))) volume :=
    h_int_sum.const_mul (2 : ℂ)
  have h_int_majorant : Integrable
      (fun τ : ℝ => ((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ)) volume := by
    -- Pointwise identification between `(2:ℂ) * ofReal r` and `ofReal (2*r)`.
    have h_ae :
        (fun τ : ℝ => ((2 : ℂ) * (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) : ℂ))))
          =ᵐ[volume]
        (fun τ : ℝ => ((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ)) := by
      refine Filter.Eventually.of_forall ?_
      intro τ; simp [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
    exact (Integrable.congr h_int_majorant' h_ae)

  -- Conclude by domination.
  refine ⟨h_meas, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ a, ENNReal.ofReal ‖((‖F a + G a‖ ^ 2 : ℝ) : ℂ)‖
      ≤ ∫⁻ a, ENNReal.ofReal ‖((2 * (‖F a‖ ^ 2 + ‖G a‖ ^ 2) : ℝ) : ℂ)‖ := by
        apply lintegral_mono_ae
        refine Filter.Eventually.mono h_bound_ae ?_
        intro τ hτ
        exact ENNReal.ofReal_le_ofReal hτ
    _ = ∫⁻ a, ENNReal.ofReal ‖(2 : ℂ) * ↑(‖F a‖ ^ 2 + ‖G a‖ ^ 2)‖ := by
        congr 1
        ext τ
        congr 1
        simp [Complex.ofReal_mul]
    _ < ⊤ := by
        rw [← hasFiniteIntegral_iff_norm]
        exact h_int_majorant.hasFiniteIntegral

/-- Integrability of norm squared of difference of Mellin transforms -/
lemma integrable_mellin_norm_sq_sub (σ : ℝ) (f g : Hσ σ)
    (hf_L2 : has_weighted_L2_norm σ f)
    (hf_int : Integrable (fun t => LogPull σ f t))
    (hg_L2 : has_weighted_L2_norm σ g)
    (hg_int : Integrable (fun t => LogPull σ g t)) :
    Integrable (fun τ : ℝ => ((‖mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ))
    - mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ))‖ ^ 2 : ℝ) : ℂ)) volume := by
  classical
  -- Abbreviations for the Mellin transforms of `f` and `g` along the line `σ + iτ`.
  set F : ℝ → ℂ :=
    fun τ => mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ)) with hF
  set G : ℝ → ℂ :=
    fun τ => mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ)) with hG

  -- Strong measurability of F and G using the Fourier representation of Mellin.
  have h_meas_F : AEStronglyMeasurable F volume := by
    -- Express F via a Fourier integral of a measurable function and use
    -- `integral_prod_right'` to get a.e.-strong measurability.
    classical
    -- Define the auxiliary function for the Fourier side
    set gf : ℝ → ℂ := fun t => LogPull σ f t with hgf_def
    -- Measurability of `gf`
    have h_gf_meas : Measurable gf := by
      simpa [gf, hgf_def] using LogPull_measurable σ f
    -- Kernel measurability on the product space
    have h_kernel_meas : Measurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2) := by
      -- fourierKernel ξ t = exp(ofReal (-(2π) * ξ * t) * I)
      unfold fourierKernel
      apply Measurable.cexp
      apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * a.1 * a.2))
      apply Measurable.neg
      have : Measurable (fun a : ℝ × ℝ => a.1 * a.2) := by
        exact measurable_fst.mul measurable_snd
      convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
      ext a
      ring
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gf p.2)
          (volume.prod volume) := by
      have : Measurable (fun p : ℝ × ℝ => gf p.2) := h_gf_meas.comp measurable_snd
      exact (h_kernel_meas.mul this).aestronglyMeasurable
    -- Measurability of the Fourier integral map for gf
    have h_fourier_meas :
        AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gf ξ) volume := by
      simpa [fourierIntegral]
        using
          (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
            (μ := volume) (ν := volume)
            (f := fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gf p.2)
            h_integrand_meas)
    -- Compose with the linear change of variable τ ↦ -τ / (2π)
    have h_arg_meas : Measurable (fun τ : ℝ => -τ / (2 * Real.pi)) := by
      have : Measurable (fun τ : ℝ => ((-1) / (2 * Real.pi)) * τ) :=
        measurable_const.mul measurable_id
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this
    -- Identify F with the composed Fourier integral and conclude measurability.
    have hF_meas_aux :
        AEStronglyMeasurable
          (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) volume := by
      -- Prove measurability directly via `integral_prod_right'` with a rescaled kernel
      have h_kernel_scaled_meas :
          Measurable (fun p : ℝ × ℝ =>
            fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
        unfold fourierKernel
        -- Build the measurable argument of the complex exponential
        apply Measurable.cexp
        apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
        apply Measurable.neg
        have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
          apply Measurable.mul
          · apply Measurable.div_const
            exact measurable_fst.neg
          · exact measurable_snd
        convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
        ext a
        field_simp
        ring
      have h_integrand_meas' :
          AEStronglyMeasurable
            (fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
            (volume.prod volume) := by
        -- Product measurability from the scaled kernel and gf ∘ snd
        have : Measurable (fun p : ℝ × ℝ => gf p.2) :=
          h_gf_meas.comp measurable_snd
        exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
      -- Now integrate out the second coordinate and obtain AEStronglyMeasurable in τ
      simpa [fourierIntegral]
        using
          (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
            (μ := volume) (ν := volume)
            (f := fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
            h_integrand_meas')
    simpa [F, hgf_def, mellin_logpull_fourierIntegral] using hF_meas_aux
  have h_meas_G : AEStronglyMeasurable G volume := by
    -- Same argument as for `h_meas_F`, replacing `f` with `g`.
    classical
    -- Auxiliary function for the Fourier side
    set gg : ℝ → ℂ := fun t => LogPull σ g t with hgg_def
    -- Measurability of `gg`
    have h_gg_meas : Measurable gg := by
      simpa [gg, hgg_def] using LogPull_measurable σ g
    -- Kernel measurability on the product space
    have h_kernel_meas : Measurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2) := by
      unfold fourierKernel
      apply Measurable.cexp
      apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * a.1 * a.2))
      apply Measurable.neg
      have : Measurable (fun a : ℝ × ℝ => a.1 * a.2) := by
        exact measurable_fst.mul measurable_snd
      convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
      ext a
      ring
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gg p.2)
          (volume.prod volume) := by
      have : Measurable (fun p : ℝ × ℝ => gg p.2) := h_gg_meas.comp measurable_snd
      exact (h_kernel_meas.mul this).aestronglyMeasurable
    -- Measurability of the Fourier integral map for gg
    have h_fourier_meas :
        AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gg ξ) volume := by
      simpa [fourierIntegral]
        using
          (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
            (μ := volume) (ν := volume)
            (f := fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gg p.2)
            h_integrand_meas)
    -- Compose with τ ↦ -τ / (2π)
    have h_arg_meas : Measurable (fun τ : ℝ => -τ / (2 * Real.pi)) := by
      have : Measurable (fun τ : ℝ => ((-1) / (2 * Real.pi)) * τ) :=
        measurable_const.mul measurable_id
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hG_meas_aux :
        AEStronglyMeasurable
          (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) volume := by
      -- Prove measurability directly via `integral_prod_right'` with a rescaled kernel
      have h_kernel_scaled_meas :
          Measurable (fun p : ℝ × ℝ =>
            fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
        unfold fourierKernel
        -- Build the measurable argument of the complex exponential
        apply Measurable.cexp
        apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
        apply Measurable.neg
        have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
          apply Measurable.mul
          · apply Measurable.div_const
            exact measurable_fst.neg
          · exact measurable_snd
        convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
        ext a
        field_simp
        ring
      have h_integrand_meas' :
          AEStronglyMeasurable
            (fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
            (volume.prod volume) := by
        have : Measurable (fun p : ℝ × ℝ => gg p.2) :=
          h_gg_meas.comp measurable_snd
        exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
      -- Now integrate out the second coordinate and obtain AEStronglyMeasurable in τ
      simpa [fourierIntegral]
        using
          (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
            (μ := volume) (ν := volume)
            (f := fun p : ℝ × ℝ =>
              fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
            h_integrand_meas')
    simpa [G, hgg_def, mellin_logpull_fourierIntegral] using hG_meas_aux

  -- Strong measurability of the target integrand.
  have h_meas : AEStronglyMeasurable
      (fun τ : ℝ => ((‖F τ - G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
    -- Combine measurability of F and G with continuity of norm, pow, and ofReal.
    have h_sub : AEStronglyMeasurable (fun τ : ℝ => F τ - G τ) volume :=
      h_meas_F.sub h_meas_G
    have h_norm : AEStronglyMeasurable (fun τ : ℝ => ‖F τ - G τ‖) volume :=
      h_sub.norm
    have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖F τ - G τ‖ ^ 2 : ℝ)) volume := by
      -- compose with the continuous map x ↦ x^2
      exact (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable
        h_norm.aemeasurable
    -- lift to ℂ via Complex.ofReal
    exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
      h_sq_real.aemeasurable

  -- Pointwise inequality: ‖F-G‖^2 ≤ 2 (‖F‖^2 + ‖G‖^2), used for domination.
  have h_bound_ae :
      (∀ᵐ τ ∂volume,
        ‖(((‖F τ - G τ‖ ^ 2 : ℝ) : ℂ))‖
          ≤ ‖((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)‖) := by
    refine Filter.Eventually.of_forall ?_
    intro τ
    have h_nonneg : 0 ≤ (‖F τ - G τ‖ ^ 2 : ℝ) := by exact sq_nonneg _
    have h_nonneg' : 0 ≤ (2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) := by
      have h0 : 0 ≤ (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : 0 ≤ (2 : ℝ) * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
        exact mul_nonneg (by norm_num) h0
      simpa [mul_comm] using this
    have h_ineq : (‖F τ - G τ‖ ^ 2 : ℝ)
        ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
      -- Step 1: square the reverse triangle inequality in the form |a - b| ≤ |a| + |b|
      have h_sub_le : ‖F τ - G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := norm_sub_le (F τ) (G τ)
      have h_sq_le : (‖F τ - G τ‖ : ℝ) * ‖F τ - G τ‖
            ≤ (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖) := by
        refine mul_le_mul h_sub_le h_sub_le ?_ ?_
        · -- 0 ≤ ‖F-G‖
          exact norm_nonneg (F τ - G τ)
        · -- 0 ≤ ‖F‖ + ‖G‖
          exact add_nonneg (norm_nonneg (F τ)) (norm_nonneg (G τ))
      -- Step 2: expand and bound the middle term using 2ab ≤ a^2 + b^2
      have h_amgm : (2 : ℝ) * (‖F τ‖ * ‖G τ‖) ≤ ‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 := by
        have h := sq_nonneg (‖F τ‖ - ‖G τ‖)
        -- (a - b)^2 = a^2 - 2ab + b^2
        have h_expand : (‖F τ‖ - ‖G τ‖) ^ 2 = ‖F τ‖ ^ 2 - 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2 := by ring
        rw [h_expand] at h
        linarith
      -- Combine the steps and simplify
      have h_poly :
          (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖)
            ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
        have h_expand : (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖)
            = ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2 := by
          ring
        have h_mid : ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2
            ≤ ‖F τ‖ ^ 2 + (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) + ‖G τ‖ ^ 2 := by
          linarith [h_amgm]
        have h_eq : ‖F τ‖ ^ 2 + (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) + ‖G τ‖ ^ 2
            = 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by ring
        have h_upper :
            ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2
              ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
          simpa [h_eq] using h_mid
        simpa [h_expand] using h_upper
      simpa [pow_two] using h_sq_le.trans h_poly
    -- Convert to norms of complex numbers via `abs_of_nonneg`
    have h_norm_coe :
        ‖(((‖F τ - G τ‖ ^ 2 : ℝ) : ℂ))‖ = (‖F τ - G τ‖ ^ 2 : ℝ) := by
      simp [Real.norm_eq_abs, Complex.norm_real, abs_of_nonneg h_nonneg]
    have h_norm_coe' :
        ‖((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)‖
          = (2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_nonneg']
    rw [h_norm_coe, h_norm_coe']
    exact h_ineq

  -- Integrability of the majorant: 2 * (‖F‖^2 + ‖G‖^2).
  have h_int_majorant : Integrable
      (fun τ : ℝ => ((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)) volume := by
    -- Reduce to the unscaled sum via const_mul, then rewrite `(2:ℂ) * ofReal r = ofReal (2*r)`.
    -- First, integrability of the unscaled sum.
    have h_int_sum : Integrable
        (fun τ : ℝ => (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ)) volume := by
      -- Combine integrability of the two squares and identify with `ofReal` of the sum.
      -- Placeholders for the component integrabilities; follow the `add` case proof.
      have h_int_Fsq : Integrable (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
        -- Replicate the F-case from the `add` lemma using the provided hypotheses.
        classical
        -- Obtain L²-membership for F via the Fourier side and the weighted hypotheses.
        have hF_L2 : MemLp F 2 volume := by
          -- Auxiliary function for the Fourier side
          set gf : ℝ → ℂ := fun t => LogPull σ f t with hgf_def
          have hgL1 : Integrable gf := by simpa [gf, hgf_def] using hf_int
          have hgL2 : MemLp gf 2 volume := by
            simpa [gf, hgf_def] using weighted_LogPull_memLp (σ := σ) (f := f) hf_L2
          -- Plancherel placeholder
          have hFI_L2 : MemLp (fun ξ : ℝ => fourierIntegral gf ξ) 2 volume :=
            fourierIntegral_memLp_L1_L2 hgL1 hgL2
          -- Measurability and rescaling τ ↦ -τ/(2π)
          have h_fourier_meas : AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gf ξ) volume :=
            hFI_L2.1
          have h_comp_meas : AEStronglyMeasurable
              (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) volume := by
            -- Establish measurability via product integral, as above
            -- Kernel measurability
            have h_kernel_scaled_meas :
                Measurable (fun p : ℝ × ℝ =>
                  fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
              unfold fourierKernel
              apply Measurable.cexp
              apply Measurable.mul _ measurable_const
              apply Complex.measurable_ofReal.comp
              show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
              apply Measurable.neg
              have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
                apply Measurable.mul
                · apply Measurable.div_const; exact measurable_fst.neg
                · exact measurable_snd
              convert (measurable_const : Measurable
                (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
              ext a; field_simp; ring
            -- Measurability of gf ∘ snd
            have h_gf_meas : Measurable gf := by
              simpa [gf, hgf_def] using LogPull_measurable σ f
            have h_integrand_meas' :
                AEStronglyMeasurable (fun p : ℝ × ℝ =>
                  fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
                  (volume.prod volume) := by
              have : Measurable (fun p : ℝ × ℝ => gf p.2) := h_gf_meas.comp measurable_snd
              exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
            -- Integrate out product
            simpa [fourierIntegral]
              using
                (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
                  (μ := volume) (ν := volume)
                  (f := fun p : ℝ × ℝ =>
                    fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
                  h_integrand_meas')
          -- Integrability of the squared norm after rescaling
          have h_comp_int : Integrable
              (fun τ : ℝ => ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2) volume :=
            integrable_fourierIntegral_rescale_sq_norm gf hFI_L2 h_fourier_meas h_comp_meas
          -- Conclude L² membership and identify with F via Mellin–Fourier relation
          have h_comp_L2 : MemLp (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) 2 volume :=
            (memLp_two_iff_integrable_sq_norm (μ := volume)
              (f := fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) h_comp_meas).2 h_comp_int
          simpa [F, hgf_def, mellin_logpull_fourierIntegral] using h_comp_L2
        -- Real integrability of the squared norm, then lift to ℂ
        have h_real : Integrable (fun τ : ℝ => (‖F τ‖ ^ 2 : ℝ)) volume :=
          (memLp_two_iff_integrable_sq_norm (μ := volume) (f := F) hF_L2.1).1 hF_L2
        have h_meas_sq : AEStronglyMeasurable
            (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖F τ‖ ^ 2 : ℝ)) volume :=
            (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable (hF_L2.1.norm.aemeasurable)
          exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
            h_sq_real.aemeasurable
        have h_fin : HasFiniteIntegral
            (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_fin_real := h_real.hasFiniteIntegral
          rw [hasFiniteIntegral_iff_norm]
          calc ∫⁻ a, ENNReal.ofReal ‖(((‖F a‖ ^ 2 : ℝ) : ℂ))‖
              = ∫⁻ a, ENNReal.ofReal (‖F a‖ ^ 2) := by
                congr 1; ext τ; have hn : 0 ≤ ‖F τ‖ ^ 2 := sq_nonneg _
                simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
            _ < ⊤ := by
                have : (fun a => ENNReal.ofReal (‖F a‖ ^ 2)) =
                    (fun a => ENNReal.ofReal ‖(‖F a‖ ^ 2 : ℝ)‖) := by
                  ext a; congr; exact (Real.norm_of_nonneg (sq_nonneg _)).symm
                rw [this, ← hasFiniteIntegral_iff_norm]; exact h_fin_real
        exact ⟨h_meas_sq, h_fin⟩
      have h_int_Gsq : Integrable (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
        classical
        -- Obtain L²-membership for G via the Fourier side and the weighted hypotheses.
        have hG_L2 : MemLp G 2 volume := by
          -- Auxiliary function for the Fourier side
          set gg : ℝ → ℂ := fun t => LogPull σ g t with hgg_def
          have hgL1 : Integrable gg := by simpa [gg, hgg_def] using hg_int
          have hgL2 : MemLp gg 2 volume := by
            simpa [gg, hgg_def] using weighted_LogPull_memLp (σ := σ) (f := g) hg_L2
          -- Plancherel placeholder
          have hFI_L2 : MemLp (fun ξ : ℝ => fourierIntegral gg ξ) 2 volume :=
            fourierIntegral_memLp_L1_L2 hgL1 hgL2
          -- Measurability and rescaling τ ↦ -τ/(2π)
          have h_fourier_meas : AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gg ξ) volume :=
            hFI_L2.1
          have h_comp_meas : AEStronglyMeasurable
              (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) volume := by
            -- Kernel measurability for the rescaled kernel
            have h_kernel_scaled_meas :
                Measurable (fun p : ℝ × ℝ =>
                  fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
              unfold fourierKernel
              apply Measurable.cexp
              apply Measurable.mul _ measurable_const
              apply Complex.measurable_ofReal.comp
              show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
              apply Measurable.neg
              have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
                apply Measurable.mul
                · apply Measurable.div_const; exact measurable_fst.neg
                · exact measurable_snd
              convert (measurable_const : Measurable
                (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
              ext a; field_simp; ring
            -- Measurability of gg ∘ snd
            have h_gg_meas : Measurable gg := by
              simpa [gg, hgg_def] using LogPull_measurable σ g
            have h_integrand_meas' :
                AEStronglyMeasurable (fun p : ℝ × ℝ =>
                  fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
                  (volume.prod volume) := by
              have : Measurable (fun p : ℝ × ℝ => gg p.2) := h_gg_meas.comp measurable_snd
              exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
            -- Integrate out product
            simpa [fourierIntegral]
              using
                (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
                  (μ := volume) (ν := volume)
                  (f := fun p : ℝ × ℝ =>
                    fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
                  h_integrand_meas')
          -- Integrability of the squared norm after rescaling
          have h_comp_int : Integrable
              (fun τ : ℝ => ‖fourierIntegral gg (-τ / (2 * Real.pi))‖ ^ 2) volume :=
            integrable_fourierIntegral_rescale_sq_norm gg hFI_L2 h_fourier_meas h_comp_meas
          -- Conclude L² membership and identify with G via Mellin–Fourier relation
          have h_comp_L2 : MemLp (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) 2 volume :=
            (memLp_two_iff_integrable_sq_norm (μ := volume)
              (f := fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) h_comp_meas).2 h_comp_int
          simpa [G, hgg_def, mellin_logpull_fourierIntegral] using h_comp_L2
        -- Real integrability of the squared norm, then lift to ℂ
        have h_real : Integrable (fun τ : ℝ => (‖G τ‖ ^ 2 : ℝ)) volume :=
          (memLp_two_iff_integrable_sq_norm (μ := volume) (f := G) hG_L2.1).1 hG_L2
        have h_meas_sq : AEStronglyMeasurable
            (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖G τ‖ ^ 2 : ℝ)) volume :=
            (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable (hG_L2.1.norm.aemeasurable)
          exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
            h_sq_real.aemeasurable
        have h_fin : HasFiniteIntegral
            (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_fin_real := h_real.hasFiniteIntegral
          rw [hasFiniteIntegral_iff_norm]
          calc ∫⁻ a, ENNReal.ofReal ‖(((‖G a‖ ^ 2 : ℝ) : ℂ))‖
              = ∫⁻ a, ENNReal.ofReal (‖G a‖ ^ 2) := by
                congr 1; ext τ; have hn : 0 ≤ ‖G τ‖ ^ 2 := sq_nonneg _
                simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
            _ < ⊤ := by
                have : (fun a => ENNReal.ofReal (‖G a‖ ^ 2)) =
                    (fun a => ENNReal.ofReal ‖(‖G a‖ ^ 2 : ℝ)‖) := by
                  ext a; congr; exact (Real.norm_of_nonneg (sq_nonneg _)).symm
                rw [this, ← hasFiniteIntegral_iff_norm]; exact h_fin_real
        exact ⟨h_meas_sq, h_fin⟩
      have h := h_int_Fsq.add h_int_Gsq
      have h_ae :
          (fun τ => ((‖F τ‖ ^ 2 : ℝ) : ℂ) + ((‖G τ‖ ^ 2 : ℝ) : ℂ))
            =ᵐ[volume]
          (fun τ => (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) : ℂ))) := by
        refine Filter.Eventually.of_forall ?_
        intro τ; simp [Complex.ofReal_add, add_comm, add_left_comm, add_assoc]
      exact (Integrable.congr h h_ae)
    -- First scale by the complex constant 2.
    have h_scaled : Integrable
        (fun τ : ℝ => ((2 : ℂ) * (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ))) volume :=
      h_int_sum.const_mul (2 : ℂ)
    -- Align the target by an a.e. equality.
    have h_ae :
        (fun τ : ℝ => ((2 : ℂ) * (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ)))
          =ᵐ[volume]
        (fun τ : ℝ => ((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)) := by
      refine Filter.Eventually.of_forall ?_
      intro τ; simp [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
    exact (Integrable.congr h_scaled h_ae)

  -- Conclude by dominated convergence using the AE bound and integrable majorant.
  have h_int_majorant' : Integrable
      (fun τ : ℝ => ((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
    -- Derive by scaling `h_int_majorant` with (1/2) and rewriting pointwise.
    have h_scaled : Integrable
        (fun τ : ℝ => ((1 / 2 : ℂ) * (((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℝ) : ℂ))) volume :=
      h_int_majorant.const_mul (1 / 2 : ℂ)
    have h_ae :
        (fun τ : ℝ => ((1 / 2 : ℂ) * (((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℝ) : ℂ)))
          =ᵐ[volume]
        (fun τ : ℝ => ((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) : ℂ)) := by
      refine Filter.Eventually.of_forall ?_
      intro τ
      have h12 : ((1 / 2 : ℝ) * 2) = 1 := by norm_num
      -- (1/2 : ℂ) * (ofReal (2 * r)) = ofReal ((1/2) * (2 * r)) = ofReal r
      simp [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc, h12]
    exact (Integrable.congr h_scaled h_ae)

  -- Use the bound to obtain integrability for the target function.
  have h_hasFinite : HasFiniteIntegral
      (fun τ : ℝ => ((‖F τ - G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
    -- Use Integrable.mono to derive from the integrable majorant.
    -- Since we have an AE bound and an integrable dominating function,
    -- we can conclude finite integral via monotonicity.
    refine Integrable.hasFiniteIntegral ?_
    refine Integrable.mono h_int_majorant h_meas ?_
    -- AE bound from `h_bound_ae`: ‖(‖F τ - G τ‖² : ℂ)‖ ≤ ‖(2 * (‖F τ‖² + ‖G τ‖²) : ℂ)‖
    exact h_bound_ae

  exact ⟨h_meas, h_hasFinite⟩

/-- Integrability of norm squared of sum with I scaling -/
lemma integrable_mellin_norm_sq_add_I (σ : ℝ) (f g : Hσ σ)
    (hf_L2 : has_weighted_L2_norm σ f)
    (hf_int : Integrable (fun t => LogPull σ f t))
    (hg_L2 : has_weighted_L2_norm σ g)
    (hg_int : Integrable (fun t => LogPull σ g t)) :
    Integrable (fun τ : ℝ => ((‖mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ))
    + I * mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ))‖ ^ 2 : ℝ) : ℂ)) volume := by
  classical
  -- Abbreviations
  set F : ℝ → ℂ := fun τ => mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ)) with hF
  set G : ℝ → ℂ := fun τ => mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ)) with hG

  -- Measurability of F and G as in the previous lemmas
  have h_meas_F : AEStronglyMeasurable F volume := by
    -- Obtain via Fourier representation and `integral_prod_right'`.
    set gf : ℝ → ℂ := fun t => LogPull σ f t with hgf_def
    have h_gf_meas : Measurable gf := by
      simpa [gf, hgf_def] using LogPull_measurable σ f
    have h_kernel_meas : Measurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2) := by
      unfold fourierKernel; apply Measurable.cexp
      apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * a.1 * a.2))
      apply Measurable.neg
      show Measurable (fun x : ℝ × ℝ => 2 * Real.pi * x.1 * x.2)
      exact Measurable.mul (Measurable.mul measurable_const measurable_fst) measurable_snd
    have h_integrand_meas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gf p.2)
        (volume.prod volume) := by
      have : Measurable (fun p : ℝ × ℝ => gf p.2) := h_gf_meas.comp measurable_snd
      exact (h_kernel_meas.mul this).aestronglyMeasurable
    have h_fourier_meas : AEStronglyMeasurable
        (fun ξ : ℝ => fourierIntegral gf ξ) volume := by
      simpa [fourierIntegral] using
        (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := volume) (ν := volume)
          (f := fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gf p.2)
          h_integrand_meas)
    have h_arg_meas : Measurable (fun τ : ℝ => -τ / (2 * Real.pi)) := by
      have : Measurable (fun τ : ℝ => ((-1) / (2 * Real.pi)) * τ) :=
        measurable_const.mul measurable_id
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hF_meas_aux : AEStronglyMeasurable
        (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) volume := by
      -- Use the scaled kernel as in prior lemmas
      have h_kernel_scaled_meas : Measurable
          (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
        unfold fourierKernel; apply Measurable.cexp
        apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
        apply Measurable.neg
        have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
          apply Measurable.mul
          · apply Measurable.div_const; exact measurable_fst.neg
          · exact measurable_snd
        convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
        ext a; field_simp; ring
      have h_integrand_meas' : AEStronglyMeasurable
          (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
          (volume.prod volume) := by
        have : Measurable (fun p : ℝ × ℝ => gf p.2) := h_gf_meas.comp measurable_snd
        exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
      simpa [fourierIntegral] using
        (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := volume) (ν := volume)
          (f := fun p : ℝ × ℝ =>
            fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
          h_integrand_meas')
    -- Identify back with F
    simpa [F, hgf_def, mellin_logpull_fourierIntegral] using hF_meas_aux
  have h_meas_G : AEStronglyMeasurable G volume := by
    -- Same with g
    set gg : ℝ → ℂ := fun t => LogPull σ g t with hgg_def
    have h_gg_meas : Measurable gg := by
      simpa [gg, hgg_def] using LogPull_measurable σ g
    have h_kernel_meas : Measurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2) := by
      unfold fourierKernel; apply Measurable.cexp
      apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * a.1 * a.2))
      apply Measurable.neg
      show Measurable (fun x : ℝ × ℝ => 2 * Real.pi * x.1 * x.2)
      exact Measurable.mul (Measurable.mul measurable_const measurable_fst) measurable_snd
    have h_integrand_meas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gg p.2)
        (volume.prod volume) := by
      have : Measurable (fun p : ℝ × ℝ => gg p.2) := h_gg_meas.comp measurable_snd
      exact (h_kernel_meas.mul this).aestronglyMeasurable
    have h_fourier_meas : AEStronglyMeasurable
        (fun ξ : ℝ => fourierIntegral gg ξ) volume := by
      simpa [fourierIntegral] using
        (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := volume) (ν := volume)
          (f := fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gg p.2)
          h_integrand_meas)
    have h_arg_meas : Measurable (fun τ : ℝ => -τ / (2 * Real.pi)) := by
      have : Measurable (fun τ : ℝ => ((-1) / (2 * Real.pi)) * τ) :=
        measurable_const.mul measurable_id
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hG_meas_aux : AEStronglyMeasurable
        (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) volume := by
      -- scaled kernel
      have h_kernel_scaled_meas : Measurable
          (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
        unfold fourierKernel; apply Measurable.cexp
        apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
        apply Measurable.neg
        have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
          apply Measurable.mul
          · apply Measurable.div_const; exact measurable_fst.neg
          · exact measurable_snd
        convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
        ext a; field_simp; ring
      have h_integrand_meas' : AEStronglyMeasurable
          (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
          (volume.prod volume) := by
        have : Measurable (fun p : ℝ × ℝ => gg p.2) := h_gg_meas.comp measurable_snd
        exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
      simpa [fourierIntegral] using
        (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := volume) (ν := volume)
          (f := fun p : ℝ × ℝ =>
            fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
          h_integrand_meas')
    simpa [G, hgg_def, mellin_logpull_fourierIntegral] using hG_meas_aux

  -- Measurability of the target integrand
  have h_meas : AEStronglyMeasurable
      (fun τ : ℝ => ((‖F τ + Complex.I * G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
    have h_add : AEStronglyMeasurable (fun τ : ℝ => F τ + Complex.I * G τ) volume :=
      h_meas_F.add (h_meas_G.const_smul Complex.I)
    have h_norm : AEStronglyMeasurable (fun τ : ℝ => ‖F τ + Complex.I * G τ‖) volume :=
      h_add.norm
    have h_sq_real : AEStronglyMeasurable
      (fun τ : ℝ => (‖F τ + Complex.I * G τ‖ ^ 2 : ℝ)) volume := by
      exact (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable h_norm.aemeasurable
    exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable h_sq_real.aemeasurable

  -- Pointwise bound: same as add/sub cases, using ‖I * G‖ = ‖G‖.
  have h_bound_ae :
      (∀ᵐ τ ∂volume,
        ‖(((‖F τ + Complex.I * G τ‖ ^ 2 : ℝ) : ℂ))‖
          ≤ ‖((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)‖) := by
    refine Filter.Eventually.of_forall ?_
    intro τ
    have h_nonneg : 0 ≤ (‖F τ + Complex.I * G τ‖ ^ 2 : ℝ) := by exact sq_nonneg _
    have h_nonneg' : 0 ≤ (2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) := by
      have h0 : 0 ≤ (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : 0 ≤ (2 : ℝ) * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := mul_nonneg (by norm_num) h0
      simpa [mul_comm] using this
    have h_ineq : (‖F τ + Complex.I * G τ‖ ^ 2 : ℝ)
        ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
      -- Triangle inequality and AM-GM as in previous lemmas
      have h_add_le : ‖F τ + Complex.I * G τ‖ ≤ ‖F τ‖ + ‖Complex.I * G τ‖ :=
        norm_add_le (F τ) (Complex.I * G τ)
      have h_smul : ‖Complex.I * G τ‖ = ‖G τ‖ := by simp
      have h_sq_le : (‖F τ + Complex.I * G τ‖ : ℝ) * ‖F τ + Complex.I * G τ‖
            ≤ (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖) := by
        have h_le : ‖F τ + Complex.I * G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := by
          simpa [h_smul] using h_add_le
        -- Use `mul_le_mul` with nonneg
        refine mul_le_mul h_le h_le ?_ ?_
        · exact norm_nonneg (F τ + Complex.I * G τ)
        · exact add_nonneg (norm_nonneg (F τ)) (norm_nonneg (G τ))
      have h_amgm : (2 : ℝ) * (‖F τ‖ * ‖G τ‖) ≤ ‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 := by
        have h := sq_nonneg (‖F τ‖ - ‖G τ‖)
        have h_expand : (‖F τ‖ - ‖G τ‖) ^ 2 = ‖F τ‖ ^ 2 - 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2 := by ring
        rw [h_expand] at h; linarith
      have h_poly : (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖)
            ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
        have h_expand : (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖)
            = ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2 := by ring
        have h_mid : ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2
            ≤ ‖F τ‖ ^ 2 + (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) + ‖G τ‖ ^ 2 := by linarith [h_amgm]
        have h_eq : ‖F τ‖ ^ 2 + (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) + ‖G τ‖ ^ 2
            = 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by ring
        simpa [h_expand, h_eq] using h_mid
      simpa [pow_two] using h_sq_le.trans h_poly
    have h_norm_coe : ‖(((‖F τ + Complex.I * G τ‖ ^ 2 : ℝ) : ℂ))‖ =
        (‖F τ + Complex.I * G τ‖ ^ 2 : ℝ) := by
      simp [Real.norm_eq_abs, Complex.norm_real, abs_of_nonneg h_nonneg]
    have h_norm_coe' : ‖((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)‖ =
        (2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_nonneg']
    rw [h_norm_coe, h_norm_coe']
    exact h_ineq

  -- Integrability of the majorant: as in the sub-case
  have h_int_majorant : Integrable
      (fun τ : ℝ => ((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)) volume := by
    -- Use the same `h_int_sum` construction
    have h_int_sum : Integrable
        (fun τ : ℝ => (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ)) volume := by
      -- Combine from component squares
      -- Reuse the F/G square integrability with the hypotheses
      -- F-part
      have h_int_Fsq : Integrable (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
        -- Deduce from L² membership as before
        -- We can invoke the earlier construction; repeat briefly
        have hF_L2 : MemLp F 2 volume := by
          -- Build via Fourier integral of gf
          set gf : ℝ → ℂ := fun t => LogPull σ f t with hgf_def
          have hgL1 : Integrable gf := by simpa [gf, hgf_def] using hf_int
          have hgL2 : MemLp gf 2 volume := by
            simpa [gf, hgf_def] using weighted_LogPull_memLp (σ := σ) (f := f) hf_L2
          have hFI_L2 : MemLp (fun ξ : ℝ => fourierIntegral gf ξ) 2 volume :=
            fourierIntegral_memLp_L1_L2 hgL1 hgL2
          have h_fourier_meas : AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gf ξ) volume :=
            hFI_L2.1
          -- product measurability as above
          have h_kernel_scaled_meas : Measurable
              (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
            unfold fourierKernel; apply Measurable.cexp
            apply Measurable.mul _ measurable_const
            apply Complex.measurable_ofReal.comp
            show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
            apply Measurable.neg
            have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
              apply Measurable.mul
              · apply Measurable.div_const; exact measurable_fst.neg
              · exact measurable_snd
            convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
            ext a; field_simp; ring
          have h_gf_meas : Measurable gf := by
            simpa [gf, hgf_def] using LogPull_measurable σ f
          have h_integrand_meas' : AEStronglyMeasurable
              (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
              (volume.prod volume) := by
            have : Measurable (fun p : ℝ × ℝ => gf p.2) := h_gf_meas.comp measurable_snd
            exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
          have h_comp_meas : AEStronglyMeasurable
              (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) volume := by
            simpa [fourierIntegral]
              using
                (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
                  (μ := volume) (ν := volume)
                  (f := fun p : ℝ × ℝ =>
                    fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
                  h_integrand_meas')
          have h_comp_int : Integrable
              (fun τ : ℝ => ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2) volume :=
            integrable_fourierIntegral_rescale_sq_norm gf hFI_L2 h_fourier_meas h_comp_meas
          have h_comp_L2 : MemLp (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) 2 volume :=
            (memLp_two_iff_integrable_sq_norm (μ := volume)
              (f := fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) h_comp_meas).2 h_comp_int
          convert h_comp_L2 using 1
          ext τ
          simp [F, hgf_def, mellin_logpull_fourierIntegral]
        have h_real : Integrable (fun τ : ℝ => (‖F τ‖ ^ 2 : ℝ)) volume :=
          (memLp_two_iff_integrable_sq_norm (μ := volume) (f := F) hF_L2.1).1 hF_L2
        -- Lift to complex
        have h_meas_sq : AEStronglyMeasurable
            (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖F τ‖ ^ 2 : ℝ)) volume :=
            (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable (h_meas_F.norm.aemeasurable)
          exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
            h_sq_real.aemeasurable
        have h_fin : HasFiniteIntegral
            (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_fin_real := h_real.hasFiniteIntegral
          rw [hasFiniteIntegral_iff_norm]
          calc ∫⁻ a, ENNReal.ofReal ‖(((‖F a‖ ^ 2 : ℝ) : ℂ))‖
              = ∫⁻ a, ENNReal.ofReal (‖F a‖ ^ 2) := by
                congr 1; ext τ; have hn : 0 ≤ ‖F τ‖ ^ 2 := sq_nonneg _
                simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
            _ < ⊤ := by
                have : (fun a => ENNReal.ofReal (‖F a‖ ^ 2)) =
                    (fun a => ENNReal.ofReal ‖(‖F a‖ ^ 2 : ℝ)‖) := by
                  ext a; congr; exact (Real.norm_of_nonneg (sq_nonneg _)).symm
                rw [this, ← hasFiniteIntegral_iff_norm]; exact h_fin_real
        exact ⟨h_meas_sq, h_fin⟩
      -- G-part
      have h_int_Gsq : Integrable (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
        -- Mirror of the F-part; we can refer to earlier block for full details.
        -- For brevity, we outline the same steps as established previously.
        -- Establish MemLp G 2 via Fourier side
        have hG_L2' : MemLp G 2 volume := by
          set gg : ℝ → ℂ := fun t => LogPull σ g t with hgg_def
          have hgL1 : Integrable gg := by simpa [gg, hgg_def] using hg_int
          have hgL2 : MemLp gg 2 volume := by
            simpa [gg, hgg_def] using weighted_LogPull_memLp (σ := σ) (f := g) hg_L2
          have hFI_L2 : MemLp (fun ξ : ℝ => fourierIntegral gg ξ) 2 volume :=
            fourierIntegral_memLp_L1_L2 hgL1 hgL2
          have h_fourier_meas : AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gg ξ) volume :=
            hFI_L2.1
          -- scaled kernel measurability as before
          have h_kernel_scaled_meas : Measurable
              (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
            unfold fourierKernel; apply Measurable.cexp
            apply Measurable.mul _ measurable_const
            apply Complex.measurable_ofReal.comp
            show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
            apply Measurable.neg
            have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
              apply Measurable.mul
              · apply Measurable.div_const; exact measurable_fst.neg
              · exact measurable_snd
            convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
            ext a; field_simp; ring
          have h_gg_meas : Measurable gg := by
            simpa [gg, hgg_def] using LogPull_measurable σ g
          have h_integrand_meas' : AEStronglyMeasurable
              (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
              (volume.prod volume) := by
            have : Measurable (fun p : ℝ × ℝ => gg p.2) := h_gg_meas.comp measurable_snd
            exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
          have h_comp_meas : AEStronglyMeasurable
              (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) volume := by
            simpa [fourierIntegral]
              using
                (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
                  (μ := volume) (ν := volume)
                  (f := fun p : ℝ × ℝ =>
                    fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
                  h_integrand_meas')
          have h_comp_int : Integrable
              (fun τ : ℝ => ‖fourierIntegral gg (-τ / (2 * Real.pi))‖ ^ 2) volume :=
            integrable_fourierIntegral_rescale_sq_norm gg hFI_L2 h_fourier_meas h_comp_meas
          have h_comp_L2 : MemLp (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) 2 volume :=
            (memLp_two_iff_integrable_sq_norm (μ := volume)
              (f := fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) h_comp_meas).2 h_comp_int
          convert h_comp_L2 using 1
          ext τ
          simp [G, hgg_def, mellin_logpull_fourierIntegral]
        have h_real : Integrable (fun τ : ℝ => (‖G τ‖ ^ 2 : ℝ)) volume :=
          (memLp_two_iff_integrable_sq_norm (μ := volume) (f := G) (by exact h_meas_G)).1 hG_L2'
        have h_meas_sq : AEStronglyMeasurable
            (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖G τ‖ ^ 2 : ℝ)) volume :=
            (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable (h_meas_G.norm.aemeasurable)
          exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
            h_sq_real.aemeasurable
        have h_fin : HasFiniteIntegral
            (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_fin_real := h_real.hasFiniteIntegral
          rw [hasFiniteIntegral_iff_norm]
          calc ∫⁻ a, ENNReal.ofReal ‖(((‖G a‖ ^ 2 : ℝ) : ℂ))‖
              = ∫⁻ a, ENNReal.ofReal (‖G a‖ ^ 2) := by
                congr 1; ext τ; have hn : 0 ≤ ‖G τ‖ ^ 2 := sq_nonneg _
                simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
            _ < ⊤ := by
                have : (fun a => ENNReal.ofReal (‖G a‖ ^ 2)) =
                    (fun a => ENNReal.ofReal ‖(‖G a‖ ^ 2 : ℝ)‖) := by
                  ext a; congr; exact (Real.norm_of_nonneg (sq_nonneg _)).symm
                rw [this, ← hasFiniteIntegral_iff_norm]; exact h_fin_real
        exact ⟨h_meas_sq, h_fin⟩
      have h := h_int_Fsq.add h_int_Gsq
      have h_ae :
          (fun τ => ((‖F τ‖ ^ 2 : ℝ) : ℂ) + ((‖G τ‖ ^ 2 : ℝ) : ℂ))
            =ᵐ[volume]
          (fun τ => (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) : ℂ))) := by
        refine Filter.Eventually.of_forall ?_
        intro τ; simp [Complex.ofReal_add, add_comm, add_left_comm, add_assoc]
      exact (Integrable.congr h h_ae)
    -- scale by 2 and rewrite
    have h_scaled : Integrable
        (fun τ : ℝ => ((2 : ℂ) * (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ))) volume :=
      h_int_sum.const_mul (2 : ℂ)
    have h_ae :
        (fun τ : ℝ => ((2 : ℂ) * (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ)))
          =ᵐ[volume]
        (fun τ : ℝ => ((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)) := by
      refine Filter.Eventually.of_forall ?_
      intro τ; simp [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
    exact (Integrable.congr h_scaled h_ae)

  -- Conclude via domination
  refine ⟨h_meas, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ a, ENNReal.ofReal ‖((‖F a + Complex.I * G a‖ ^ 2 : ℝ) : ℂ)‖
      ≤ ∫⁻ a, ENNReal.ofReal ‖((2 * (‖F a‖ ^ 2 + ‖G a‖ ^ 2) : ℝ) : ℂ)‖ := by
        apply lintegral_mono_ae
        refine Filter.Eventually.mono h_bound_ae ?_
        intro τ hτ; exact ENNReal.ofReal_le_ofReal hτ
    _ = ∫⁻ a, ENNReal.ofReal ‖(2 : ℂ) * ↑(‖F a‖ ^ 2 + ‖G a‖ ^ 2)‖ := by
        congr 1; ext τ; congr 1; simp [Complex.ofReal_mul]
    _ < ⊤ := by
        rw [← hasFiniteIntegral_iff_norm]
        have h_eq : (fun a => (2 : ℂ) * ↑(‖F a‖ ^ 2 + ‖G a‖ ^ 2))
                  = (fun τ => ((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)) := by
          ext τ; simp [Complex.ofReal_mul]
        rw [h_eq]; exact h_int_majorant.hasFiniteIntegral

/-- Integrability of norm squared of difference with I scaling -/
lemma integrable_mellin_norm_sq_sub_I (σ : ℝ) (f g : Hσ σ)
    (hf_L2 : has_weighted_L2_norm σ f)
    (hf_int : Integrable (fun t => LogPull σ f t))
    (hg_L2 : has_weighted_L2_norm σ g)
    (hg_int : Integrable (fun t => LogPull σ g t)) :
    Integrable (fun τ : ℝ => ((‖mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ))
    - I * mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ))‖ ^ 2 : ℝ) : ℂ)) volume := by
  classical
  -- Abbreviations
  set F : ℝ → ℂ := fun τ => mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ)) with hF
  set G : ℝ → ℂ := fun τ => mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ)) with hG

  -- Measurability of F and G (via Fourier representation as before)
  have h_meas_F : AEStronglyMeasurable F volume := by
    set gf : ℝ → ℂ := fun t => LogPull σ f t with hgf_def
    have h_gf_meas : Measurable gf := by
      simpa [gf, hgf_def] using LogPull_measurable σ f
    have h_kernel_meas : Measurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2) := by
      unfold fourierKernel; apply Measurable.cexp
      apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * a.1 * a.2))
      apply Measurable.neg
      have : Measurable (fun a : ℝ × ℝ => a.1 * a.2) := measurable_fst.mul measurable_snd
      convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
      ext a; ring
    have h_integrand_meas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gf p.2)
        (volume.prod volume) := by
      have : Measurable (fun p : ℝ × ℝ => gf p.2) := h_gf_meas.comp measurable_snd
      exact (h_kernel_meas.mul this).aestronglyMeasurable
    have hF_meas_aux : AEStronglyMeasurable
        (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) volume := by
      -- scaled kernel measurability
      have h_kernel_scaled_meas : Measurable
          (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
        unfold fourierKernel; apply Measurable.cexp
        apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
        apply Measurable.neg
        have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
          apply Measurable.mul
          · apply Measurable.div_const; exact measurable_fst.neg
          · exact measurable_snd
        convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
        ext a; field_simp; ring
      have h_integrand_meas' : AEStronglyMeasurable
          (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
          (volume.prod volume) := by
        have : Measurable (fun p : ℝ × ℝ => gf p.2) := h_gf_meas.comp measurable_snd
        exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
      simpa [fourierIntegral] using
        (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := volume) (ν := volume)
          (f := fun p : ℝ × ℝ =>
            fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
          h_integrand_meas')
    simpa [F, hgf_def, mellin_logpull_fourierIntegral] using hF_meas_aux
  have h_meas_G : AEStronglyMeasurable G volume := by
    set gg : ℝ → ℂ := fun t => LogPull σ g t with hgg_def
    have h_gg_meas : Measurable gg := by
      simpa [gg, hgg_def] using LogPull_measurable σ g
    have h_kernel_meas : Measurable (fun p : ℝ × ℝ => fourierKernel p.1 p.2) := by
      unfold fourierKernel; apply Measurable.cexp
      apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * a.1 * a.2))
      apply Measurable.neg
      have : Measurable (fun a : ℝ × ℝ => a.1 * a.2) := measurable_fst.mul measurable_snd
      convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
      ext a; ring
    have h_integrand_meas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => fourierKernel p.1 p.2 * gg p.2)
        (volume.prod volume) := by
      have : Measurable (fun p : ℝ × ℝ => gg p.2) := h_gg_meas.comp measurable_snd
      exact (h_kernel_meas.mul this).aestronglyMeasurable
    have hG_meas_aux : AEStronglyMeasurable
        (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) volume := by
      -- scaled kernel measurability
      have h_kernel_scaled_meas : Measurable
          (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
        unfold fourierKernel; apply Measurable.cexp
        apply Measurable.mul _ measurable_const
        apply Complex.measurable_ofReal.comp
        show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
        apply Measurable.neg
        have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
          apply Measurable.mul
          · apply Measurable.div_const; exact measurable_fst.neg
          · exact measurable_snd
        convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
        ext a; field_simp; ring
      have h_integrand_meas' : AEStronglyMeasurable
          (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
          (volume.prod volume) := by
        have : Measurable (fun p : ℝ × ℝ => gg p.2) := h_gg_meas.comp measurable_snd
        exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
      simpa [fourierIntegral] using
        (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := volume) (ν := volume)
          (f := fun p : ℝ × ℝ =>
            fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
          h_integrand_meas')
    simpa [G, hgg_def, mellin_logpull_fourierIntegral] using hG_meas_aux

  -- Measurability of the target integrand
  have h_meas : AEStronglyMeasurable
      (fun τ : ℝ => ((‖F τ - Complex.I * G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
    have h_sub : AEStronglyMeasurable (fun τ : ℝ => F τ - Complex.I * G τ) volume :=
      h_meas_F.sub (h_meas_G.const_smul Complex.I)
    have h_norm : AEStronglyMeasurable (fun τ : ℝ => ‖F τ - Complex.I * G τ‖) volume :=
      h_sub.norm
    have h_sq_real :
        AEStronglyMeasurable (fun τ : ℝ => (‖F τ - Complex.I * G τ‖ ^ 2 : ℝ)) volume := by
      exact (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable h_norm.aemeasurable
    exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable h_sq_real.aemeasurable

  -- Pointwise bound
  have h_bound_ae :
      (∀ᵐ τ ∂volume,
        ‖(((‖F τ - Complex.I * G τ‖ ^ 2 : ℝ) : ℂ))‖
          ≤ ‖((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)‖) := by
    refine Filter.Eventually.of_forall ?_
    intro τ
    have h_nonneg : 0 ≤ (‖F τ - Complex.I * G τ‖ ^ 2 : ℝ) := by exact sq_nonneg _
    have h_nonneg' : 0 ≤ (2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) := by
      have h0 : 0 ≤ (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : 0 ≤ (2 : ℝ) * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := mul_nonneg (by norm_num) h0
      simpa [mul_comm] using this
    have h_ineq : (‖F τ - Complex.I * G τ‖ ^ 2 : ℝ)
        ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
      -- Use norm_sub_le and AM-GM
      have h_sub_le : ‖F τ - Complex.I * G τ‖ ≤ ‖F τ‖ + ‖Complex.I * G τ‖ :=
        norm_sub_le (F τ) (Complex.I * G τ)
      have h_smul : ‖Complex.I * G τ‖ = ‖G τ‖ := by simp
      have h_sq_le : (‖F τ - Complex.I * G τ‖ : ℝ) * ‖F τ - Complex.I * G τ‖
            ≤ (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖) := by
        rw [h_smul] at h_sub_le
        exact mul_self_le_mul_self (norm_nonneg _) h_sub_le
      have h_amgm : (2 : ℝ) * (‖F τ‖ * ‖G τ‖) ≤ ‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 := by
        have h := sq_nonneg (‖F τ‖ - ‖G τ‖)
        have h_expand : (‖F τ‖ - ‖G τ‖) ^ 2 = ‖F τ‖ ^ 2 - 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2 := by ring
        rw [h_expand] at h; linarith
      have h_poly : (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖)
            ≤ 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by
        have h_expand : (‖F τ‖ + ‖G τ‖) * (‖F τ‖ + ‖G τ‖)
            = ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2 := by ring
        have h_mid : ‖F τ‖ ^ 2 + 2 * (‖F τ‖ * ‖G τ‖) + ‖G τ‖ ^ 2
            ≤ ‖F τ‖ ^ 2 + (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) + ‖G τ‖ ^ 2 := by linarith [h_amgm]
        have h_eq : ‖F τ‖ ^ 2 + (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) + ‖G τ‖ ^ 2
            = 2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) := by ring
        simpa [h_expand, h_eq] using h_mid
      simpa [pow_two] using h_sq_le.trans h_poly
    have h_norm_coe : ‖(((‖F τ - Complex.I * G τ‖ ^ 2 : ℝ) : ℂ))‖ =
        (‖F τ - Complex.I * G τ‖ ^ 2 : ℝ) := by
      simp [Real.norm_eq_abs, Complex.norm_real, abs_of_nonneg h_nonneg]
    have h_norm_coe' : ‖((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)‖
          = (2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) := by
      have h_sum_nonneg : 0 ≤ (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have h_nonneg_loc : 0 ≤ (2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) := by
        apply mul_nonneg; norm_num; exact h_sum_nonneg
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg h_nonneg_loc]
    rw [h_norm_coe, h_norm_coe']
    exact h_ineq

  -- Integrable majorant: reuse the add_I construction (sum of squares)
  have h_int_majorant : Integrable
      (fun τ : ℝ => ((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)) volume := by
    -- Build integrability of the unscaled sum from component squares, as before
    have h_int_sum : Integrable
        (fun τ : ℝ => (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ)) volume := by
      -- F-part
      have h_int_Fsq : Integrable (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
        -- derive via L² membership; identical to earlier constructions
        -- Obtain MemLp F 2
        -- Use same proof as in `integrable_mellin_norm_sq_add_I`
        -- For brevity, we replicate the argument
        have hF_L2' : MemLp F 2 volume := by
          set gf : ℝ → ℂ := fun t => LogPull σ f t with hgf_def
          have hgL1 : Integrable gf := by simpa [gf, hgf_def] using hf_int
          have hgL2 : MemLp gf 2 volume := by
            simpa [gf, hgf_def] using weighted_LogPull_memLp (σ := σ) (f := f) hf_L2
          have hFI_L2 : MemLp (fun ξ : ℝ => fourierIntegral gf ξ) 2 volume :=
            fourierIntegral_memLp_L1_L2 hgL1 hgL2
          have h_fourier_meas : AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gf ξ) volume :=
            hFI_L2.1
          have h_kernel_scaled_meas : Measurable
              (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
            unfold fourierKernel; apply Measurable.cexp; apply Measurable.mul _ measurable_const
            apply Complex.measurable_ofReal.comp
            show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
            apply Measurable.neg
            have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
              apply Measurable.mul; · apply Measurable.div_const; exact measurable_fst.neg
              · exact measurable_snd
            convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
            ext a; field_simp; ring
          have h_gf_meas : Measurable gf := by
            simpa [gf, hgf_def] using LogPull_measurable σ f
          have h_integrand_meas' : AEStronglyMeasurable
              (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
              (volume.prod volume) := by
            have : Measurable (fun p : ℝ × ℝ => gf p.2) := h_gf_meas.comp measurable_snd
            exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
          have h_comp_meas : AEStronglyMeasurable
              (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) volume := by
            simpa [fourierIntegral]
              using
                (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
                  (μ := volume) (ν := volume)
                  (f := fun p : ℝ × ℝ =>
                    fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gf p.2)
                  h_integrand_meas')
          have h_comp_int : Integrable
              (fun τ : ℝ => ‖fourierIntegral gf (-τ / (2 * Real.pi))‖ ^ 2) volume :=
            integrable_fourierIntegral_rescale_sq_norm gf hFI_L2 h_fourier_meas h_comp_meas
          have h_comp_L2 : MemLp (fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) 2 volume :=
            (memLp_two_iff_integrable_sq_norm (μ := volume)
              (f := fun τ : ℝ => fourierIntegral gf (-τ / (2 * Real.pi))) h_comp_meas).2 h_comp_int
          convert h_comp_L2 using 1
          ext τ
          simp [F, hgf_def, mellin_logpull_fourierIntegral]
        have h_real : Integrable (fun τ : ℝ => (‖F τ‖ ^ 2 : ℝ)) volume :=
          (memLp_two_iff_integrable_sq_norm (μ := volume) (f := F) (by exact h_meas_F)).1 hF_L2'
        have h_meas_sq : AEStronglyMeasurable
            (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖F τ‖ ^ 2 : ℝ)) volume :=
            (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable (h_meas_F.norm.aemeasurable)
          exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
            h_sq_real.aemeasurable
        have h_fin : HasFiniteIntegral
            (fun τ : ℝ => ((‖F τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_fin_real := h_real.hasFiniteIntegral
          rw [hasFiniteIntegral_iff_norm]
          calc ∫⁻ a, ENNReal.ofReal ‖(((‖F a‖ ^ 2 : ℝ) : ℂ))‖
              = ∫⁻ a, ENNReal.ofReal (‖F a‖ ^ 2) := by
                congr 1; ext τ; have hn : 0 ≤ ‖F τ‖ ^ 2 := sq_nonneg _
                simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
            _ < ⊤ := by
                have : (fun a => ENNReal.ofReal (‖F a‖ ^ 2)) =
                    (fun a => ENNReal.ofReal ‖(‖F a‖ ^ 2 : ℝ)‖) := by
                  ext a; congr; exact (Real.norm_of_nonneg (sq_nonneg _)).symm
                rw [this, ← hasFiniteIntegral_iff_norm]; exact h_fin_real
        exact ⟨h_meas_sq, h_fin⟩
      -- G-part
      have h_int_Gsq : Integrable (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
        -- Build via L² membership of G
        have hG_L2' : MemLp G 2 volume := by
          set gg : ℝ → ℂ := fun t => LogPull σ g t with hgg_def
          have hgL1 : Integrable gg := by simpa [gg, hgg_def] using hg_int
          have hgL2 : MemLp gg 2 volume := by
            simpa [gg, hgg_def] using weighted_LogPull_memLp (σ := σ) (f := g) hg_L2
          have hFI_L2 : MemLp (fun ξ : ℝ => fourierIntegral gg ξ) 2 volume :=
            fourierIntegral_memLp_L1_L2 hgL1 hgL2
          have h_fourier_meas : AEStronglyMeasurable (fun ξ : ℝ => fourierIntegral gg ξ) volume :=
            hFI_L2.1
          have h_kernel_scaled_meas : Measurable
              (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2) := by
            unfold fourierKernel; apply Measurable.cexp; apply Measurable.mul _ measurable_const
            apply Complex.measurable_ofReal.comp
            show Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * (-a.1 / (2 * Real.pi)) * a.2))
            apply Measurable.neg
            have : Measurable (fun a : ℝ × ℝ => (-a.1 / (2 * Real.pi)) * a.2) := by
              apply Measurable.mul; · apply Measurable.div_const; exact measurable_fst.neg
              · exact measurable_snd
            convert (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul this using 1
            ext a; field_simp; ring
          have h_gg_meas : Measurable gg := by
            simpa [gg, hgg_def] using LogPull_measurable σ g
          have h_integrand_meas' : AEStronglyMeasurable
              (fun p : ℝ × ℝ => fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
              (volume.prod volume) := by
            have : Measurable (fun p : ℝ × ℝ => gg p.2) := h_gg_meas.comp measurable_snd
            exact (h_kernel_scaled_meas.mul this).aestronglyMeasurable
          have h_comp_meas : AEStronglyMeasurable
              (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) volume := by
            simpa [fourierIntegral]
              using
                (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
                  (μ := volume) (ν := volume)
                  (f := fun p : ℝ × ℝ =>
                    fourierKernel (-p.1 / (2 * Real.pi)) p.2 * gg p.2)
                  h_integrand_meas')
          have h_comp_int : Integrable
              (fun τ : ℝ => ‖fourierIntegral gg (-τ / (2 * Real.pi))‖ ^ 2) volume :=
            integrable_fourierIntegral_rescale_sq_norm gg hFI_L2 h_fourier_meas h_comp_meas
          have h_comp_L2 : MemLp (fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) 2 volume :=
            (memLp_two_iff_integrable_sq_norm (μ := volume)
              (f := fun τ : ℝ => fourierIntegral gg (-τ / (2 * Real.pi))) h_comp_meas).2 h_comp_int
          convert h_comp_L2 using 1
          ext τ
          simp [G, hgg_def, mellin_logpull_fourierIntegral]
        have h_real : Integrable (fun τ : ℝ => (‖G τ‖ ^ 2 : ℝ)) volume :=
          (memLp_two_iff_integrable_sq_norm (μ := volume) (f := G) (by exact h_meas_G)).1 hG_L2'
        have h_meas_sq : AEStronglyMeasurable
            (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_sq_real : AEStronglyMeasurable (fun τ : ℝ => (‖G τ‖ ^ 2 : ℝ)) volume :=
            (continuous_pow 2).aestronglyMeasurable.comp_aemeasurable (h_meas_G.norm.aemeasurable)
          exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
            h_sq_real.aemeasurable
        have h_fin : HasFiniteIntegral
            (fun τ : ℝ => ((‖G τ‖ ^ 2 : ℝ) : ℂ)) volume := by
          have h_fin_real := h_real.hasFiniteIntegral
          rw [hasFiniteIntegral_iff_norm]
          calc ∫⁻ a, ENNReal.ofReal ‖(((‖G a‖ ^ 2 : ℝ) : ℂ))‖
              = ∫⁻ a, ENNReal.ofReal (‖G a‖ ^ 2) := by
                congr 1; ext τ; have hn : 0 ≤ ‖G τ‖ ^ 2 := sq_nonneg _
                simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
            _ < ⊤ := by
                have : (fun a => ENNReal.ofReal (‖G a‖ ^ 2)) =
                    (fun a => ENNReal.ofReal ‖(‖G a‖ ^ 2 : ℝ)‖) := by
                  ext a; congr; exact (Real.norm_of_nonneg (sq_nonneg _)).symm
                rw [this, ← hasFiniteIntegral_iff_norm]; exact h_fin_real
        exact ⟨h_meas_sq, h_fin⟩
      have h := h_int_Fsq.add h_int_Gsq
      have h_ae :
          (fun τ => ((‖F τ‖ ^ 2 : ℝ) : ℂ) + ((‖G τ‖ ^ 2 : ℝ) : ℂ))
            =ᵐ[volume]
          (fun τ => (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ) : ℂ))) := by
        refine Filter.Eventually.of_forall ?_
        intro τ; simp [Complex.ofReal_add, add_comm, add_left_comm, add_assoc]
      exact (Integrable.congr h h_ae)
    -- scale by 2
    have h_scaled : Integrable
        (fun τ : ℝ => ((2 : ℂ) * (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ))) volume :=
      h_int_sum.const_mul (2 : ℂ)
    have h_ae :
        (fun τ : ℝ => ((2 : ℂ) * (((‖F τ‖ ^ 2 + ‖G τ‖ ^ 2 : ℝ)) : ℂ)))
          =ᵐ[volume]
        (fun τ : ℝ => ((2 * (‖F τ‖ ^ 2 + ‖G τ‖ ^ 2) : ℝ) : ℂ)) := by
      refine Filter.Eventually.of_forall ?_
      intro τ; simp [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
    exact (Integrable.congr h_scaled h_ae)

  -- Conclude by domination
  refine ⟨h_meas, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ a, ENNReal.ofReal ‖((‖F a - Complex.I * G a‖ ^ 2 : ℝ) : ℂ)‖
      ≤ ∫⁻ a, ENNReal.ofReal ‖((2 * (‖F a‖ ^ 2 + ‖G a‖ ^ 2) : ℝ) : ℂ)‖ := by
        apply lintegral_mono_ae
        refine Filter.Eventually.mono h_bound_ae ?_
        intro τ hτ; exact ENNReal.ofReal_le_ofReal hτ
    _ = ∫⁻ a, ENNReal.ofReal ‖(2 : ℂ) * ↑(‖F a‖ ^ 2 + ‖G a‖ ^ 2)‖ := by
        congr 1; ext τ; congr 1
        simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    _ < ⊤ := by
        have : (fun a => ENNReal.ofReal ‖(2 : ℂ) * ↑(‖F a‖ ^ 2 + ‖G a‖ ^ 2)‖) =
               (fun a => ENNReal.ofReal ‖((2 * (‖F a‖ ^ 2 + ‖G a‖ ^ 2) : ℝ) : ℂ)‖) := by
          ext τ; congr 1; simp [Complex.ofReal_mul]
        rw [this, ← hasFiniteIntegral_iff_norm]
        exact h_int_majorant.hasFiniteIntegral

/-- Auxiliary lemma: linearity of integral for polarization identity components -/
lemma integral_polarization_split (A B C1 C2 : ℝ → ℝ)
    (h_int_A : Integrable (fun τ => ((A τ : ℝ) : ℂ)) volume)
    (h_int_B : Integrable (fun τ => ((B τ : ℝ) : ℂ)) volume)
    (h_int_C1 : Integrable (fun τ => ((C1 τ : ℝ) : ℂ)) volume)
    (h_int_C2 : Integrable (fun τ => ((C2 τ : ℝ) : ℂ)) volume) :
    ∫ τ, ((A τ : ℝ) : ℂ) - ((B τ : ℝ) : ℂ)
          - Complex.I * ((C1 τ : ℝ) : ℂ)
          + Complex.I * ((C2 τ : ℝ) : ℂ) ∂volume
      = (∫ τ, ((A τ : ℝ) : ℂ) ∂volume)
        - (∫ τ, ((B τ : ℝ) : ℂ) ∂volume)
        - Complex.I * (∫ τ, ((C1 τ : ℝ) : ℂ) ∂volume)
        + Complex.I * (∫ τ, ((C2 τ : ℝ) : ℂ) ∂volume) := by
  -- Combine linearly using integral_sub, integral_add, integral_const_mul
  have h_subAB :
      ∫ τ, ((A τ : ℝ) : ℂ) - ((B τ : ℝ) : ℂ) ∂volume
        = (∫ τ, ((A τ : ℝ) : ℂ) ∂volume)
          - (∫ τ, ((B τ : ℝ) : ℂ) ∂volume) :=
    integral_sub h_int_A h_int_B
  have h_linC :
      ∫ τ, (-Complex.I) * ((C1 τ : ℝ) : ℂ) + Complex.I * ((C2 τ : ℝ) : ℂ) ∂volume
        = (-Complex.I) * (∫ τ, ((C1 τ : ℝ) : ℂ) ∂volume)
          + Complex.I * (∫ τ, ((C2 τ : ℝ) : ℂ) ∂volume) := by
    -- Use linearity: integral_add and integral_const_mul
    have h_c1' :
        ∫ τ, (-Complex.I) * ((C1 τ : ℝ) : ℂ) ∂volume
          = (-Complex.I) * (∫ τ, ((C1 τ : ℝ) : ℂ) ∂volume) :=
      integral_const_mul _ _
    have h_c2' :
        ∫ τ, (Complex.I) * ((C2 τ : ℝ) : ℂ) ∂volume
          = (Complex.I) * (∫ τ, ((C2 τ : ℝ) : ℂ) ∂volume) :=
      integral_const_mul _ _
    -- Now sum the two equalities via `integral_add`
    have h_add := integral_add
      (hf := (h_int_C1.const_mul (-Complex.I)))
      (hg := (h_int_C2.const_mul Complex.I))
    -- Rewrite the statement with the computed equalities
    rw [h_add, h_c1', h_c2']
  -- Put pieces together
  have h_add := integral_add
    (hf := (h_int_A.sub h_int_B))
    (hg := ((h_int_C1.const_mul (-Complex.I)).add (h_int_C2.const_mul Complex.I)))
  -- Evaluate both sides using previously derived equalities
  calc ∫ τ, ((A τ : ℝ) : ℂ) - ((B τ : ℝ) : ℂ)
          - Complex.I * ((C1 τ : ℝ) : ℂ)
          + Complex.I * ((C2 τ : ℝ) : ℂ) ∂volume
      = ∫ a, ((fun τ => ((A τ : ℝ) : ℂ)) - fun τ => ((B τ : ℝ) : ℂ)) a
          + ((fun x => -Complex.I * ((C1 x : ℝ) : ℂ)) + fun x =>
          Complex.I * ((C2 x : ℝ) : ℂ)) a ∂volume := by
        congr 1; ext τ; simp; ring
    _ = (∫ a, ((fun τ => ((A τ : ℝ) : ℂ)) - fun τ => ((B τ : ℝ) : ℂ)) a ∂volume)
        + (∫ a, ((fun x => -Complex.I * ((C1 x : ℝ) : ℂ)) + fun x =>
        Complex.I * ((C2 x : ℝ) : ℂ)) a ∂volume) := h_add
    _ = (∫ τ, ((A τ : ℝ) : ℂ) ∂volume) - (∫ τ, ((B τ : ℝ) : ℂ) ∂volume)
        - Complex.I * (∫ τ, ((C1 τ : ℝ) : ℂ) ∂volume)
        + Complex.I * (∫ τ, ((C2 τ : ℝ) : ℂ) ∂volume) := by
      have eq1 : (∫ a, ((fun τ => ((A τ : ℝ) : ℂ)) - fun τ => ((B τ : ℝ) : ℂ)) a ∂volume)
                  = (∫ τ, ((A τ : ℝ) : ℂ) ∂volume) - (∫ τ, ((B τ : ℝ) : ℂ) ∂volume) := h_subAB
      have eq2 : (∫ a, ((fun x => -Complex.I * ((C1 x : ℝ) : ℂ)) + fun x =>
        Complex.I * ((C2 x : ℝ) : ℂ)) a ∂volume)
        = (-Complex.I) * (∫ τ, ((C1 τ : ℝ) : ℂ) ∂volume) +
        Complex.I * (∫ τ, ((C2 τ : ℝ) : ℂ) ∂volume) := h_linC
      rw [eq1, eq2]; ring

end ParsevalEquivalence

end Frourio
