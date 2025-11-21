import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore6
import Frourio.Analysis.HilbertSpaceCore
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

open MeasureTheory Measure Real Complex Set NNReal
open scoped ENNReal Topology FourierTransform InnerProductSpace

noncomputable section

namespace Frourio
open Schwartz

section Applications

/-- Helper lemma: relate the Mellin-side inner product to the `V`-image
inner product in `L²(ℝ)` using the normalization constant `rescaleNorm`. -/
lemma mellin_inner_rescale_to_V (σ : ℝ) (f g : Hσ σ)
    (hfL1 : Integrable (LogPull σ f)) (hgL1 : Integrable (LogPull σ g))
    (V : Hσ σ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hV :
      ∀ (h : Hσ σ), Integrable (LogPull σ h) →
        (fun τ : ℝ =>
          rescaleNorm⁻¹ • mellinTransform (h : ℝ → ℂ) (σ + I * τ))
        =ᵐ[volume] (V h : ℝ → ℂ)) :
    ∫ τ : ℝ, mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
      starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
    = (2 * Real.pi) * ∫ τ : ℝ, (V f : ℝ → ℂ) τ *
      starRingEnd ℂ ((V g : ℝ → ℂ) τ) ∂volume := by
  classical
  -- Shorthands for Mellin transforms along the vertical line `Re s = σ`.
  set Mf : ℝ → ℂ := fun τ =>
    mellinTransform (f : ℝ → ℂ) (σ + I * τ) with hMf
  set Mg : ℝ → ℂ := fun τ =>
    mellinTransform (g : ℝ → ℂ) (σ + I * τ) with hMg

  -- Rescaled Mellin transforms (the ones appearing in `hV`).
  set F₁ : ℝ → ℂ := fun τ => rescaleNorm⁻¹ • Mf τ with hF₁
  set G₁ : ℝ → ℂ := fun τ => rescaleNorm⁻¹ • Mg τ with hG₁

  -- A.e. identification of the rescaled Mellin transforms with `V f` and `V g`.
  have hVf : F₁ =ᵐ[volume] (V f : ℝ → ℂ) := by
    simpa [F₁, Mf, hMf] using hV f hfL1
  have hVg : G₁ =ᵐ[volume] (V g : ℝ → ℂ) := by
    simpa [G₁, Mg, hMg] using hV g hgL1

  -- First, express the Mellin-side integrand via the rescaled transforms.
  have h_pointwise :
      (fun τ : ℝ =>
        Mf τ * starRingEnd ℂ (Mg τ))
        =
      fun τ : ℝ =>
        (rescaleNorm : ℂ) ^ 2 *
          (F₁ τ * starRingEnd ℂ (G₁ τ)) := by
    funext τ
    -- Express `Mf` and `Mg` in terms of the rescaled transforms `F₁`, `G₁`.
    have hF : (rescaleNorm : ℂ) • F₁ τ = Mf τ := by
      -- `F₁ τ = rescaleNorm⁻¹ • Mf τ`, so multiplying by `rescaleNorm` recovers `Mf τ`.
      have h_ne : (rescaleNorm : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt rescaleNorm_pos)
      simp [F₁, Mf, smul_smul]
      field_simp [h_ne]
    have hG : (rescaleNorm : ℂ) • G₁ τ = Mg τ := by
      have h_ne : (rescaleNorm : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt rescaleNorm_pos)
      simp [G₁, Mg, smul_smul]
      field_simp [h_ne]
    -- Substitute and simplify.
    calc
      Mf τ * starRingEnd ℂ (Mg τ)
          = ((rescaleNorm : ℂ) • F₁ τ) *
              starRingEnd ℂ ((rescaleNorm : ℂ) • G₁ τ) := by
                rw [← hF, ← hG]
      _ = ((rescaleNorm : ℂ) • F₁ τ) *
              ((rescaleNorm : ℂ) • starRingEnd ℂ (G₁ τ)) := by
                -- conjugation is ℂ-linear, and `rescaleNorm` is real
                congr 1
                simp only [smul_eq_mul]
                rw [map_mul, starRingEnd_apply]
                congr 1
                exact conj_ofReal rescaleNorm
      _ = (rescaleNorm : ℂ) ^ 2 *
              (F₁ τ * starRingEnd ℂ (G₁ τ)) := by
                -- Move the scalar factors out and combine them.
                simp [pow_two, smul_mul_assoc, mul_comm, mul_left_comm, mul_assoc]

  -- Use the pointwise equality to rewrite the Mellin inner product in terms of F₁,G₁.
  have h_integral_FG :
      ∫ τ : ℝ, Mf τ * starRingEnd ℂ (Mg τ) ∂volume
        = (rescaleNorm : ℂ) ^ 2 *
          ∫ τ : ℝ, F₁ τ * starRingEnd ℂ (G₁ τ) ∂volume := by
    -- Rewrite the integrand using `h_pointwise`.
    have h_eq :
        (fun τ : ℝ => Mf τ * starRingEnd ℂ (Mg τ))
          =
        fun τ : ℝ =>
          (rescaleNorm : ℂ) ^ 2 *
            (F₁ τ * starRingEnd ℂ (G₁ τ)) :=
      h_pointwise
    simp [h_eq]  -- move to an integral of `rescaleNorm^2 * ...`
    -- Pull out the constant scalar `(rescaleNorm : ℂ) ^ 2`.
    have h_smul :
        ∫ τ : ℝ,
            (rescaleNorm : ℂ) ^ 2 *
              (F₁ τ * starRingEnd ℂ (G₁ τ)) ∂volume
          = (rescaleNorm : ℂ) ^ 2 *
              ∫ τ : ℝ, F₁ τ * starRingEnd ℂ (G₁ τ) ∂volume := by
      -- Express as a scalar multiple via `smul` and use `integral_smul`.
      have hfun :
          (fun τ : ℝ =>
              (rescaleNorm : ℂ) ^ 2 *
                (F₁ τ * starRingEnd ℂ (G₁ τ)))
            =
          fun τ : ℝ =>
              (rescaleNorm : ℂ) ^ 2 •
                (F₁ τ * starRingEnd ℂ (G₁ τ)) := by
        funext τ
        simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      simp [hfun, MeasureTheory.integral_smul]  -- `smul_eq_mul` on the integral
    simpa using h_smul

  -- Next, use the a.e. equalities `F₁ = V f`, `G₁ = V g` to replace the integrand.
  have h_integral_V :
      ∫ τ : ℝ, F₁ τ * starRingEnd ℂ (G₁ τ) ∂volume
        = ∫ τ : ℝ, (V f : ℝ → ℂ) τ *
          starRingEnd ℂ ((V g : ℝ → ℂ) τ) ∂volume := by
    -- Build an a.e. equality for the products using the individual a.e. equalities.
    have hG₁_star :
        (fun τ : ℝ => starRingEnd ℂ (G₁ τ))
          =ᵐ[volume]
        fun τ : ℝ => starRingEnd ℂ ((V g : ℝ → ℂ) τ) := by
      refine hVg.mono ?_
      intro τ hτ
      simpa [G₁] using congrArg (starRingEnd ℂ) hτ
    have h_prod :
        (fun τ : ℝ => F₁ τ * starRingEnd ℂ (G₁ τ))
          =ᵐ[volume]
        fun τ : ℝ =>
          (V f : ℝ → ℂ) τ *
            starRingEnd ℂ ((V g : ℝ → ℂ) τ) :=
      Filter.EventuallyEq.mul hVf hG₁_star
    exact integral_congr_ae (μ := volume) h_prod

  -- Combine everything and substitute `rescaleNorm ^ 2 = 2π`.
  calc
    ∫ τ : ℝ, mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
        starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
        = ∫ τ : ℝ, Mf τ * starRingEnd ℂ (Mg τ) ∂volume := by
            rfl
    _ = (rescaleNorm : ℂ) ^ 2 *
          ∫ τ : ℝ, F₁ τ * starRingEnd ℂ (G₁ τ) ∂volume := h_integral_FG
    _ = (rescaleNorm : ℂ) ^ 2 *
          ∫ τ : ℝ, (V f : ℝ → ℂ) τ *
            starRingEnd ℂ ((V g : ℝ → ℂ) τ) ∂volume := by
            simp [h_integral_V]
    _ = (2 * Real.pi) *
          ∫ τ : ℝ, (V f : ℝ → ℂ) τ *
            starRingEnd ℂ ((V g : ℝ → ℂ) τ) ∂volume := by
            -- identify `(rescaleNorm : ℂ) ^ 2` with the real scalar `2π`
            have h_scalar_C : (rescaleNorm : ℂ) ^ 2 = (2 * Real.pi : ℝ) := by
              -- coerce `rescaleNorm_sq` to `ℂ`
              have := congrArg (fun x : ℝ => (x : ℂ)) rescaleNorm_sq
              simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
            simp [h_scalar_C]

/-- Helper lemma: inner product on `Lp ℂ 2 μ` as an explicit integral. -/
lemma integral_mul_star_eq_inner_Lp {μ : Measure ℝ}
    (g φ : Lp ℂ 2 μ) :
    ∫ x, (g : ℝ → ℂ) x * starRingEnd ℂ ((φ : ℝ → ℂ) x) ∂μ
      = @inner ℂ (Lp ℂ 2 μ) _ φ g := by
  classical
  -- Express the `Lp` inner product via the `L²` inner product definition.
  have h_inner :
      @inner ℂ (Lp ℂ 2 μ) _ φ g
        = ∫ x, ⟪(φ : ℝ → ℂ) x, (g : ℝ → ℂ) x⟫_ℂ ∂μ := by
    -- `Lp ℂ 2 μ` is definitionally the L² space `ℝ →₂[μ] ℂ`.
    simpa using
      (MeasureTheory.L2.inner_def (μ := μ) (f := φ) (g := g) :
        ⟪φ, g⟫_ℂ = ∫ x, ⟪(φ : ℝ → ℂ) x, (g : ℝ → ℂ) x⟫_ℂ ∂μ)
  -- Rewrite the pointwise inner product on `ℂ` as `g x * star (φ x)`.
  have h_integrand :
      (fun x : ℝ =>
        (g : ℝ → ℂ) x * starRingEnd ℂ ((φ : ℝ → ℂ) x))
        =
      fun x : ℝ =>
        ⟪(φ : ℝ → ℂ) x, (g : ℝ → ℂ) x⟫_ℂ := by
    funext x
    -- On `ℂ` viewed as a C⋆-module over itself we have `⟪z, w⟫ = w * star z`.
    have h0 :
        ⟪(φ : ℝ → ℂ) x, (g : ℝ → ℂ) x⟫_ℂ
          = (g : ℝ → ℂ) x * star ((φ : ℝ → ℂ) x) := by
      simp
    -- Replace `starRingEnd` by `star` and use `h0`.
    change (g : ℝ → ℂ) x * star ((φ : ℝ → ℂ) x)
      = ⟪(φ : ℝ → ℂ) x, (g : ℝ → ℂ) x⟫_ℂ
    simp
  -- Combine the two equalities.
  calc
    ∫ x, (g : ℝ → ℂ) x * starRingEnd ℂ ((φ : ℝ → ℂ) x) ∂μ
        = ∫ x, ⟪(φ : ℝ → ℂ) x, (g : ℝ → ℂ) x⟫_ℂ ∂μ := by
            simp [h_integrand]
    _ = @inner ℂ (Lp ℂ 2 μ) _ φ g := by
            simpa using h_inner.symm

/-- Helper lemma: identify the `Hσ σ` inner product with the weighted integral on `(0,∞)`.
With the convention `inner g f = ∫ (f · conj g)`, the roles of `f` and `g` in the
integrand are swapped compared to the inner product arguments. -/
lemma inner_Hσ_eq_weighted_integral
    (σ : ℝ) (f g : Hσ σ) :
    @inner ℂ (Hσ σ) _ g f
      = ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℂ) x *
          starRingEnd ℂ ((g : ℝ → ℂ) x) * (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := by
  classical
  -- Abbreviations for the weighted measure defining `Hσ σ`.
  let μ0 : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let w  : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x ^ (2 * σ - 1))
  let μ  : Measure ℝ := μ0.withDensity w

  -- Step 1: express the `Hσ` inner product as an integral over the weighted measure `μ`.
  have h_inner_lp :
      @inner ℂ (Hσ σ) _ g f
        = ∫ x, (f : ℝ → ℂ) x *
            starRingEnd ℂ ((g : ℝ → ℂ) x) ∂μ := by
    -- By definition, `Hσ σ` is `Lp ℂ 2 μ`.
    -- Use the general `Lp` inner-product lemma with `g := f`, `φ := g`.
    symm
    simpa [Hσ, μ, μ0, w] using
      (integral_mul_star_eq_inner_Lp
        (μ := μ) (g := (f : Hσ σ)) (φ := (g : Hσ σ)))

  -- Step 2: rewrite the integral over `μ = μ0.withDensity w` as a set integral on `(0,∞)`
  -- with an explicit weight.
  have hw_ae_meas : AEMeasurable w μ0 := by
    -- The weight is measurable, hence a.e. measurable.
    have hw_meas : Measurable w := by
      -- Direct measurability by calculus of measurable functions.
      -- (Uses `measurability` tactic to expand the proof.)
      simpa [w] using
        (by
          have : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) := by
            measurability
          exact this)
    exact hw_meas.aemeasurable

  have hw_finite : ∀ᵐ x ∂μ0, w x < ∞ := by
    -- `ofReal` is always finite.
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp [w]

  -- Integral w.r.t. `μ = μ0.withDensity w` as an integral w.r.t. `μ0` with a scalar weight.
  have h_withDensity :
      ∫ x, (f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x) ∂μ
        =
      ∫ x, (w x).toReal •
          ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x)) ∂μ0 := by
    -- Use the Bochner integral change-of-measure lemma for `withDensity`.
    have :=
      integral_withDensity_eq_integral_toReal_smul₀
        (μ := μ0) (f := w)
        (f_meas := hw_ae_meas) (hf_lt_top := hw_finite)
        (g :=
          fun x => (f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x))
    -- The lemma states:
    --   ∫ g ∂ μ0.withDensity w = ∫ (w x).toReal • g x ∂ μ0.
    -- Here, `μ = μ0.withDensity w`.
    simpa [μ] using this

  -- Step 3: rewrite the integral over `μ0` as a set integral over `(0,∞)` for `volume`.
  have h_set :
      ∫ x, (w x).toReal •
          ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x)) ∂μ0
        =
      ∫ x in Set.Ioi (0 : ℝ),
          (w x).toReal •
            ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x)) ∂volume := by
    -- By notation, the set integral is just integration with respect to the restricted measure.
    -- `μ0` was defined as `volume.restrict (Set.Ioi 0)`.
    rfl

  -- Step 4: identify the scalar weight and rewrite it as multiplication by `(x : ℂ)^(2σ-1)`.
  -- Build a pointwise equality on `(0,∞)` between the integrands.
  have h_pointwise :
      ∀ᵐ x ∂volume,
        x ∈ Set.Ioi (0 : ℝ) →
          (w x).toReal •
              ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x))
            =
          (f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x) *
            (x : ℂ) ^ (2 * σ - 1 : ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    -- Simplify `(w x).toReal` to the real weight `x^(2σ-1)`.
    have h_toReal :
        (w x).toReal = x ^ (2 * σ - 1) := by
      have hnonneg : 0 ≤ x ^ (2 * σ - 1) :=
        Real.rpow_nonneg hx0 _
      -- `ENNReal.toReal_ofReal` collapses under nonnegativity.
      simp [w, hnonneg]
    -- Translate real scalar multiplication on `ℂ` into complex multiplication.
    have h_smul :
        (w x).toReal •
            ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x))
          =
        (↑(x ^ (2 * σ - 1)) : ℂ) *
          ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x)) := by
      -- In `ℂ`, real scalar multiplication is just multiplication by the coerced real.
      -- Use `smul_eq_mul` to rewrite.
      simp [h_toReal, smul_eq_mul]
    -- Relate the real power to the complex power `(x : ℂ)^(2σ-1)`.
    have h_cpow :
        (↑(x ^ (2 * σ - 1)) : ℂ)
          = (x : ℂ) ^ (2 * σ - 1 : ℂ) := by
      -- This is `ofReal_cpow` specialized to `x > 0`.
      rw [Complex.ofReal_cpow hx0 (2 * σ - 1)]
      simp
    -- Combine the scalar identities and rearrange the products.
    calc
      (w x).toReal •
          ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x))
          = (↑(x ^ (2 * σ - 1)) : ℂ) *
              ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x)) := h_smul
      _ = (x : ℂ) ^ (2 * σ - 1 : ℂ) *
              ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x)) := by
            simp [h_cpow]
      _ =
          (f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x) *
            (x : ℂ) ^ (2 * σ - 1 : ℂ) := by
            -- Rearrange the scalar to the right.
            ring_nf

  -- Use the pointwise equality on `(0,∞)` to replace the integrand.
  have h_weighted :
      ∫ x in Set.Ioi (0 : ℝ),
          (w x).toReal •
            ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x)) ∂volume
        =
      ∫ x in Set.Ioi (0 : ℝ),
          (f : ℝ → ℂ) x *
            starRingEnd ℂ ((g : ℝ → ℂ) x) *
            (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := by
    -- Restrict the a.e. equality to the set `Ioi 0`.
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
    -- On `Ioi 0`, the two integrands coincide.
    exact h_pointwise

  -- Assemble all the steps.
  calc
    @inner ℂ (Hσ σ) _ g f
        = ∫ x, (f : ℝ → ℂ) x *
            starRingEnd ℂ ((g : ℝ → ℂ) x) ∂μ := h_inner_lp
    _ = ∫ x, (w x).toReal •
            ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x)) ∂μ0 := h_withDensity
    _ = ∫ x in Set.Ioi (0 : ℝ),
            (w x).toReal •
              ((f : ℝ → ℂ) x * starRingEnd ℂ ((g : ℝ → ℂ) x)) ∂volume := h_set
    _ = ∫ x in Set.Ioi (0 : ℝ),
            (f : ℝ → ℂ) x *
              starRingEnd ℂ ((g : ℝ → ℂ) x) *
              (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := h_weighted

/-- Mellin-Parseval identity for inner products.
The inner product in frequency space (Mellin transforms) equals the inner product
in the original weighted space Hσ(σ). The normalization depends on the Fourier
kernel convention: with kernel e^(-2πiξt), the coefficient is 1. -/
theorem mellin_parseval_inner_product (σ : ℝ) (f g : Hσ σ)
    (hfL1 : Integrable (LogPull σ f)) (hgL1 : Integrable (LogPull σ g)) :
    ∫ τ : ℝ, mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
      starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
    = (2 * Real.pi) * ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℂ) x *
      starRingEnd ℂ ((g : ℝ → ℂ) x) * (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := by
  classical
  -- This is the Mellin-Parseval identity for inner products:
  -- ∫ M_f(σ+iτ) · conj(M_g(σ+iτ)) dτ = ∫ f(x) · conj(g(x)) · x^(2σ-1) dx
  -- Proof outline:
  -- 1. Use change of variables x = e^t to convert RHS to L²(ℝ) inner product
  -- 2. Apply Fourier-Plancherel identity (with angular frequency normalization)
  -- 3. Use the relation M[f](σ+iτ) = F[LogPull(σ,f)](τ/2π) with proper normalization
  -- Step 1: use the unitary Mellin–Fourier equivalence constructed in Core6.
  obtain ⟨V, hV⟩ := mellin_fourier_unitary_equivalence σ

  -- Step 2: identify the Mellin-side inner product with the L² inner product of `V f`, `V g`.
  have h_mellin_to_V :
      ∫ τ : ℝ, mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
        starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
        = (2 * Real.pi) * ∫ τ : ℝ, (V f : ℝ → ℂ) τ *
          starRingEnd ℂ ((V g : ℝ → ℂ) τ) ∂volume :=
    mellin_inner_rescale_to_V σ f g hfL1 hgL1 V hV

  -- Step 3: express the L² inner product in terms of the `Lp` inner product.
  have h_V_inner :
      ∫ τ : ℝ, (V f : ℝ → ℂ) τ *
        starRingEnd ℂ ((V g : ℝ → ℂ) τ) ∂volume
        = @inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ (V g) (V f) := by
    simpa using
      (integral_mul_star_eq_inner_Lp (μ := volume) (g := (V f)) (φ := (V g)))

  -- Step 4: identify the `Hσ σ` inner product with the weighted integral on `(0,∞)`.
  have h_Hσ_inner :
      @inner ℂ (Hσ σ) _ g f
        = ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℂ) x *
          starRingEnd ℂ ((g : ℝ → ℂ) x) * (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume :=
    inner_Hσ_eq_weighted_integral σ f g

  -- Combine all steps.
  calc
    ∫ τ : ℝ, mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
        starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
        = (2 * Real.pi) *
          ∫ τ : ℝ, (V f : ℝ → ℂ) τ *
            starRingEnd ℂ ((V g : ℝ → ℂ) τ) ∂volume := h_mellin_to_V
    _ = (2 * Real.pi) *
          @inner ℂ (Lp ℂ 2 (volume : Measure ℝ)) _ (V g) (V f) := by
            simp [h_V_inner]
    _ = (2 * Real.pi) * @inner ℂ (Hσ σ) _ g f := by
            simp
    _ = (2 * Real.pi) *
          ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℂ) x *
            starRingEnd ℂ ((g : ℝ → ℂ) x) * (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := by
            simp [h_Hσ_inner]

/-- Energy conservation in Mellin space (Plancherel theorem for Mellin transform).
The L² norm in the weighted space Hσ(σ) is preserved (up to a constant factor)
under the Mellin transform. The factor 2π comes from the angular frequency
normalization in the Fourier kernel e^(-2πiξt). -/
theorem mellin_energy_conservation (σ : ℝ) (f : Hσ σ)
    (hfL1 : Integrable (LogPull σ f)) :
    (2 * Real.pi) * ∫ x in Set.Ioi (0 : ℝ), ‖(f : ℝ → ℂ) x‖ ^ 2 * (x : ℝ) ^ (2 * σ - 1) ∂volume
    = ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
  classical
  -- Step 1: relate the Mellin-side inner product for `f` with itself
  -- to the weighted inner product on `Hσ σ`.
  have h_parseval :=
    mellin_parseval_inner_product (σ := σ) (f := f) (g := f) hfL1 hfL1

  -- Abbreviation for the Mellin transform along the vertical line `Re s = σ`.
  set Mf : ℝ → ℂ :=
    fun τ => mellinTransform (f : ℝ → ℂ) (σ + I * τ) with hMf

  -- Rewrite `h_parseval` using `Mf`.
  have h_parseval_Mf :
      ∫ τ : ℝ, Mf τ * starRingEnd ℂ (Mf τ) ∂volume
        = (2 * Real.pi) *
          ∫ x in Set.Ioi (0 : ℝ),
            (f : ℝ → ℂ) x *
              starRingEnd ℂ ((f : ℝ → ℂ) x) *
              (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := by
    simpa [Mf, hMf] using h_parseval

  -- Step 2: identify the Mellin-side integral with the integral of the squared norm.
  -- Pointwise, we have `Mf τ * conj(Mf τ) = (‖Mf τ‖ ^ 2 : ℝ)` as a complex number.
  have h_Mf_pointwise :
      (fun τ : ℝ => Mf τ * starRingEnd ℂ (Mf τ))
        = fun τ : ℝ => ((‖Mf τ‖ ^ 2 : ℝ) : ℂ) := by
    funext τ
    -- `starRingEnd ℂ` is complex conjugation.
    simp [Mf, Complex.mul_conj, Complex.normSq_eq_norm_sq]

  have h_Mf_integral :
      ∫ τ : ℝ, Mf τ * starRingEnd ℂ (Mf τ) ∂volume
        = (∫ τ : ℝ, ‖Mf τ‖ ^ 2 ∂volume : ℝ) := by
    -- Rewrite the integrand using the pointwise identity.
    simp only [h_Mf_pointwise]
    exact integral_ofReal

  -- Step 3: identify the Hσ-side integrand with the weighted squared norm.
  have h_f_pointwise :
      ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        (f : ℝ → ℂ) x *
            starRingEnd ℂ ((f : ℝ → ℂ) x) *
            (x : ℂ) ^ (2 * σ - 1 : ℂ)
          =
        ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) * (x : ℝ) ^ (2 * σ - 1) : ℝ) := by
    -- On `(0,∞)`, powers `(x : ℂ)^(2σ-1)` are real and positive.
    refine (ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have h_cpow :
        (x : ℂ) ^ (2 * σ - 1 : ℂ) = (x ^ (2 * σ - 1) : ℝ) := by
      -- Real power agrees with complex power on `(0,∞)`.
      rw [Complex.ofReal_cpow hx0 (2 * σ - 1)]
      simp
    -- Use the standard identity `z * conj z = ‖z‖^2` in `ℂ`.
    have h_mul :
        (f : ℝ → ℂ) x * starRingEnd ℂ ((f : ℝ → ℂ) x)
          = (‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) := by
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    -- Combine the two identities.
    calc
      (f : ℝ → ℂ) x *
          starRingEnd ℂ ((f : ℝ → ℂ) x) *
          (x : ℂ) ^ (2 * σ - 1 : ℂ)
          = ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) *
              (x : ℂ) ^ (2 * σ - 1 : ℂ) := by
                simp [h_mul]
      _ = ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) * (x : ℝ) ^ (2 * σ - 1) : ℝ) := by
            simp [h_cpow]

  have h_f_integral :
      ∫ x in Set.Ioi (0 : ℝ),
          (f : ℝ → ℂ) x *
            starRingEnd ℂ ((f : ℝ → ℂ) x) *
            (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume
        =
      (∫ x in Set.Ioi (0 : ℝ),
          ‖(f : ℝ → ℂ) x‖ ^ 2 * (x : ℝ) ^ (2 * σ - 1) ∂volume : ℝ) := by
    -- Use the a.e. pointwise identity on `(0,∞)`.
    have h_ae : ∀ᵐ x ∂volume, x ∈ Set.Ioi (0 : ℝ) →
        (f : ℝ → ℂ) x *
            starRingEnd ℂ ((f : ℝ → ℂ) x) *
            (x : ℂ) ^ (2 * σ - 1 : ℂ)
          =
        ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) * (x : ℝ) ^ (2 * σ - 1) : ℝ) := by
      rw [← ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi]
      exact h_f_pointwise
    simp only [setIntegral_congr_ae (E := ℂ) measurableSet_Ioi h_ae]
    exact integral_ofReal

  -- Step 4: combine all pieces and rearrange.
  -- First substitute the norm-squared expressions into Parseval.
  have h_norm_eq :
      ∫ τ : ℝ, (‖Mf τ‖ ^ 2 : ℝ) ∂volume
        = (2 * Real.pi) *
          ∫ x in Set.Ioi (0 : ℝ),
            (‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) * (x : ℝ) ^ (2 * σ - 1) ∂volume := by
    have := h_parseval_Mf
    -- Rewrite both sides using the two integral identities.
    rw [h_Mf_integral, h_f_integral] at this
    -- Remove the complex casts from both sides
    have : (∫ τ : ℝ, ‖Mf τ‖ ^ 2 ∂volume : ℝ) = (2 * Real.pi : ℝ) *
        (∫ x in Set.Ioi (0 : ℝ), ‖(f : ℝ → ℂ) x‖ ^ 2 * (x : ℝ) ^ (2 * σ - 1) ∂volume : ℝ) := by
      exact_mod_cast this
    exact this

  -- Finally, rewrite in the requested orientation.
  -- All quantities are real, so we can work in `ℝ` directly.
  have h_symm :
      (2 * Real.pi) *
          ∫ x in Set.Ioi (0 : ℝ),
            ‖(f : ℝ → ℂ) x‖ ^ 2 * (x : ℝ) ^ (2 * σ - 1) ∂volume
        = ∫ τ : ℝ, ‖Mf τ‖ ^ 2 ∂volume := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_norm_eq.symm

  -- Unfold `Mf` in the right-hand side.
  simpa [Mf, hMf] using h_symm

end Applications

end Frourio
