import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
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
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))) :
    IntegrableOn (fun t : ℝ => (c • f : ℝ → ℂ) t * t ^ (σ + I * τ - 1)) (Set.Ioi 0) := by
  classical
  -- Start from the base integrability for `f` at `σ + i τ`.
  have h_base : IntegrableOn (fun t : ℝ => (f : ℝ → ℂ) t * t ^ (σ + I * τ - 1)) (Set.Ioi 0) :=
    mellin_integrable_of_weighted_L2 σ f τ hf_int
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
  -- Strategy skeleton:
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

  -- Change of variables on the lintegral side (skeleton step):
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
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
    (hg_L2 : has_weighted_L2_norm σ g)
    (hg_int : Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :
    Integrable (fun τ : ℝ => ((‖mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ))
    + mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ))‖ ^ 2 : ℝ) : ℂ)) volume := by
  classical
  -- Abbreviations for the Mellin transforms of `f` and `g` along the line `σ + iτ`.
  set F : ℝ → ℂ :=
    fun τ => mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ)) with hF
  set G : ℝ → ℂ :=
    fun τ => mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ)) with hG

  -- Strong measurability of the target integrand (skeleton: deferred).
  have h_meas_F : AEStronglyMeasurable F volume := by
    -- Express F via a Fourier integral of a measurable function and use
    -- `integral_prod_right'` to get a.e.-strong measurability.
    classical
    -- Define the auxiliary function for the Fourier side
    set gf : ℝ → ℂ := fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t) with hgf_def
    -- Measurability of `gf`
    have h_gf_meas : Measurable gf := by
      have h_logpull : Measurable (LogPull σ f) := LogPull_measurable σ f
      have h_exp : Measurable (fun t : ℝ => Complex.exp (((1 / 2 : ℂ) * (t : ℂ)))) := by
        have h_lin : Measurable (fun t : ℝ => ((1 / 2 : ℂ) * (t : ℂ))) :=
          measurable_const.mul Complex.measurable_ofReal
        exact Complex.measurable_exp.comp h_lin
      -- Coerce `((1/2 : ℝ) * t)` to `((1/2 : ℂ) * (t : ℂ))` implicitly
      simpa [gf, hgf_def] using h_logpull.mul h_exp
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
    set gg : ℝ → ℂ := fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t) with hgg_def
    -- Measurability of `gg`
    have h_gg_meas : Measurable gg := by
      have h_logpull : Measurable (LogPull σ g) := LogPull_measurable σ g
      have h_exp : Measurable (fun t : ℝ => Complex.exp (((1 / 2 : ℂ) * (t : ℂ)))) := by
        have h_lin : Measurable (fun t : ℝ => ((1 / 2 : ℂ) * (t : ℂ))) :=
          measurable_const.mul Complex.measurable_ofReal
        exact Complex.measurable_exp.comp h_lin
      simpa [gg, hgg_def] using h_logpull.mul h_exp
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
      set gf : ℝ → ℂ := fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t) with hgf_def
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
          have h_logpull : Measurable (LogPull σ f) := LogPull_measurable σ f
          have h_exp : Measurable (fun t : ℝ => Complex.exp (((1 / 2 : ℂ) * (t : ℂ)))) := by
            have h_lin : Measurable (fun t : ℝ => ((1 / 2 : ℂ) * (t : ℂ))) :=
              measurable_const.mul Complex.measurable_ofReal
            exact Complex.measurable_exp.comp h_lin
          simpa [gf, hgf_def] using h_logpull.mul h_exp
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
      set gg : ℝ → ℂ := fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t) with hgg_def
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
          have h_logpull : Measurable (LogPull σ g) := LogPull_measurable σ g
          have h_exp : Measurable (fun t : ℝ => Complex.exp (((1 / 2 : ℂ) * (t : ℂ)))) := by
            have h_lin : Measurable (fun t : ℝ => ((1 / 2 : ℂ) * (t : ℂ))) :=
              measurable_const.mul Complex.measurable_ofReal
            exact Complex.measurable_exp.comp h_lin
          simpa [gg, hgg_def] using h_logpull.mul h_exp
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
lemma integrable_mellin_norm_sq_sub (σ : ℝ) (f g : Hσ σ) :
    Integrable (fun τ : ℝ => ((‖mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ))
    - mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ))‖ ^ 2 : ℝ) : ℂ)) volume := by
  sorry

/-- Integrability of norm squared of sum with I scaling -/
lemma integrable_mellin_norm_sq_add_I (σ : ℝ) (f g : Hσ σ) :
    Integrable (fun τ : ℝ => ((‖mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ))
    + I * mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ))‖ ^ 2 : ℝ) : ℂ)) volume := by
  sorry

/-- Integrability of norm squared of difference with I scaling -/
lemma integrable_mellin_norm_sq_sub_I (σ : ℝ) (f g : Hσ σ) :
    Integrable (fun τ : ℝ => ((‖mellinTransform (f : ℝ → ℂ) (σ + I * (τ : ℂ))
    - I * mellinTransform (g : ℝ → ℂ) (σ + I * (τ : ℂ))‖ ^ 2 : ℝ) : ℂ)) volume := by
  sorry

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
            (starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ))
              * mellinTransform (g : ℝ → ℂ) (σ + I * τ)) * 4 ∂volume := by
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
              integrable_mellin_norm_sq_sub σ f g
            have h_int_C1 : Integrable (fun τ => ((C1 τ : ℝ) : ℂ)) volume :=
              integrable_mellin_norm_sq_add_I σ f g
            have h_int_C2 : Integrable (fun τ => ((C2 τ : ℝ) : ℂ)) volume :=
              integrable_mellin_norm_sq_sub_I σ f g

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
        -- Use Complex.ofReal (C * A) = C * Complex.ofReal A and ring
        sorry
      -- Combine the last two displays.
      sorry

    -- Conclude by comparing both expressions for 4 ⟪f,g⟫ and divide by 4.
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
