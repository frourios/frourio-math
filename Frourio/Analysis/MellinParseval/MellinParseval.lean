import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore6
import Frourio.Analysis.HilbertSpaceCore
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
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace Frourio
open Schwartz

section Applications

/-- Mellin-Parseval identity for inner products.
The inner product in frequency space (Mellin transforms) equals the inner product
in the original weighted space Hσ(σ). The normalization depends on the Fourier
kernel convention: with kernel e^(-2πiξt), the coefficient is 1. -/
theorem mellin_parseval_inner_product (σ : ℝ) (f g : Hσ σ)
    (hfL1 : Integrable (LogPull σ f)) (hgL1 : Integrable (LogPull σ g)) :
    ∫ τ : ℝ, mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
      starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
    = ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℂ) x *
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

  -- For each `f ∈ Hσ`, the normalized Mellin transform agrees a.e.
  -- with the `Lp` representative `V f` in frequency space.
  have hVf :
      (fun τ : ℝ =>
        rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ))
        =ᵐ[volume] (V f : ℝ → ℂ) :=
    hV f hfL1
  have hVg :
      (fun τ : ℝ =>
        rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ))
        =ᵐ[volume] (V g : ℝ → ℂ) :=
    hV g hgL1

  -- Step 2: identify the frequency-side inner product
  --   ∫ M_f(σ+iτ) · conj(M_g(σ+iτ)) dτ
  -- with the L²(ℝ) inner product ⟪V f, V g⟫, using the a.e. identities `hVf` and `hVg`
  -- together with the explicit `Lp` inner-product-as-integral formula.
  have h_freq_inner :
      ∫ τ : ℝ,
          mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
            starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
        = inner ℂ (V f) (V g) := by
    -- Strategy:
    -- 1. Express the Mellin-side integral in terms of the normalized transforms
    --    `rescaleNorm⁻¹ • mellinTransform`, which agree a.e. with `V f` and `V g`.
    -- 2. Use the `L²` inner product formula in `Lp` to rewrite the integral
    --    as `inner ℂ (V f) (V g)`.  The algebraic details are handled in the
    --    Mellin–Parseval core development.
    -- Step 2.1: rewrite the integrand using the normalization factor.
    have h_rescale :
        ∀ τ : ℝ,
          mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
              starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ))
            = (rescaleNorm : ℝ) ^ 2 *
                ((rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
                  starRingEnd ℂ
                    (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ))) := by
      intro τ
      -- Abbreviate the Mellin values at σ + iτ.
      set A : ℂ := mellinTransform (f : ℝ → ℂ) (σ + I * τ) with hA
      set B : ℂ := mellinTransform (g : ℝ → ℂ) (σ + I * τ) with hB
      -- Reduce the statement to a purely algebraic identity in A and B.
      have h_alg :
          A * starRingEnd ℂ B
            = (rescaleNorm : ℝ) ^ 2 *
                ((rescaleNorm⁻¹ • A) *
                  starRingEnd ℂ (rescaleNorm⁻¹ • B)) := by
        -- Work in the real scalar action on ℂ. For real λ, conjugation commutes
        -- with scalar multiplication, and scalar factors can be pulled in and out
        -- of products via `smul_mul_assoc` and `mul_smul`.
        have h_conj_smul :
            starRingEnd ℂ (rescaleNorm⁻¹ • B)
              = (rescaleNorm⁻¹ : ℝ) • starRingEnd ℂ B := by
          -- Rewrite the smul as multiplication by a real scalar and use
          -- multiplicativity of `starRingEnd` together with the fact that real
          -- scalars are fixed by conjugation.
          simp [Circle.smul_def, map_mul, mul_comm, mul_left_comm, mul_assoc]
        -- First pull all scalar factors together using bilinearity.
        have h_smul :
            (rescaleNorm⁻¹ • A) *
                starRingEnd ℂ (rescaleNorm⁻¹ • B)
              = ((rescaleNorm⁻¹ : ℝ) ^ 2) •
                  (A * starRingEnd ℂ B) := by
          -- Use the ℝ-linearity of conjugation and bilinearity of multiplication.
          -- Replace the conjugated smul using `h_conj_smul`.
          simp [h_conj_smul, smul_mul_assoc, mul_smul, smul_smul, pow_two,
            mul_comm, mul_left_comm, mul_assoc]
        -- Now combine the outer factor `(rescaleNorm)^2` with the inner smul
        -- by scalar associativity.
        have h_scalar :
            (rescaleNorm : ℝ) ^ 2 *
                ((rescaleNorm⁻¹ : ℝ) ^ 2 • (A * starRingEnd ℂ B))
              = (A * starRingEnd ℂ B) := by
          -- `rescaleNorm` is a nonzero real, so `(rescaleNorm)² ⋅ (rescaleNorm⁻¹)² = 1`.
          have hpos : (rescaleNorm : ℝ) ≠ 0 :=
            ne_of_gt rescaleNorm_pos
          -- Direct algebraic simplification - handle the coercion carefully
          have h1 : (rescaleNorm : ℝ) ^ 2 * ((rescaleNorm⁻¹ : ℝ) ^ 2 • (A * starRingEnd ℂ B))
              = ((rescaleNorm : ℝ) ^ 2 * (rescaleNorm⁻¹ : ℝ) ^ 2) • (A * starRingEnd ℂ B) := by
            norm_cast
            rw [mul_smul]
            norm_cast
          have h2 : (rescaleNorm : ℝ) ^ 2 * (rescaleNorm⁻¹ : ℝ) ^ 2 = 1 := by
            field_simp [pow_two, hpos]
          rw [h1, h2, one_smul]
        -- Assemble the pieces.
        calc
          A * starRingEnd ℂ B
              = (rescaleNorm : ℝ) ^ 2 *
                  ((rescaleNorm⁻¹ : ℝ) ^ 2 • (A * starRingEnd ℂ B)) := by
                    rw [h_scalar]
          _ = (rescaleNorm : ℝ) ^ 2 *
                  ((rescaleNorm⁻¹ • A) *
                    starRingEnd ℂ (rescaleNorm⁻¹ • B)) := by
                    rw [← h_smul]
      -- Revert to the original expressions in terms of Mellin transforms.
      simpa [hA, hB] using h_alg

    have h_rescale_int :
        ∫ τ : ℝ,
            mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
              starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
          = (rescaleNorm : ℝ) ^ 2 *
              ∫ τ : ℝ,
                (rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
                  starRingEnd ℂ
                    (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume := by
      -- Step 2.1: move the pointwise identity `h_rescale` under the integral.
      have hfunext :
          (fun τ : ℝ =>
            mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
              starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)))
            =
          (fun τ : ℝ =>
            (rescaleNorm : ℝ) ^ 2 *
              ((rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
                starRingEnd ℂ
                  (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ)))) := by
        funext τ; exact h_rescale τ

      have h_int_eq :
          ∫ τ : ℝ,
              mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
                starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
            =
          ∫ τ : ℝ,
              (rescaleNorm : ℝ) ^ 2 *
                ((rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
                  starRingEnd ℂ
                    (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ))) ∂volume := by
        -- Rewrite the integrand using `hfunext`.
        simp [hfunext]

      -- Step 2.2: pull out the constant factor `(rescaleNorm)²` from the integral.
      have h_pull_const :
          ∫ τ : ℝ,
              (rescaleNorm : ℝ) ^ 2 *
                ((rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
                  starRingEnd ℂ
                    (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ))) ∂volume
            =
          (rescaleNorm : ℝ) ^ 2 *
            ∫ τ : ℝ,
              (rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
                starRingEnd ℂ
                  (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume := by
        -- Rewrite using smul and apply integral_smul
        conv_lhs =>
          arg 2; ext τ
          rw [← smul_eq_mul]
        rw [integral_smul]
        rfl

      exact h_int_eq.trans h_pull_const

    -- Step 2.2: identify the normalized Mellin integrand with the `Lp` inner product
    -- integrand for `V f` and `V g`, using the a.e. equalities `hVf` and `hVg`.
    have h_inner_int :
        ∫ τ : ℝ,
            (rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
              starRingEnd ℂ
                (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
          = inner ℂ (V g) (V f) := by
      -- Step 2.2a: identify the inner product `inner (V g) (V f)` with an
      -- explicit integral in terms of pointwise representatives.
      have hinner0 :=
        (MeasureTheory.L2.inner_def (𝕜 := ℂ) (μ := volume)
          (f := (V g)) (g := (V f)))
      -- Expand the scalar inner product on ℂ and rearrange the integrand
      -- into the form `(V f τ) * conj (V g τ)`.
      have hinner_int :
          (∫ τ : ℝ,
              starRingEnd ℂ ((V g : Lp ℂ 2 volume) τ) *
                ((V f : Lp ℂ 2 volume) τ) ∂volume)
            =
          ∫ τ : ℝ,
              (V f : Lp ℂ 2 volume) τ *
                starRingEnd ℂ ((V g : Lp ℂ 2 volume) τ) ∂volume := by
        refine integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro τ
        -- multiplication in ℂ is commutative.
        ring
      have hinner :
          inner ℂ (V g) (V f)
            = ∫ τ : ℝ,
                (V f : Lp ℂ 2 volume) τ *
                  starRingEnd ℂ ((V g : Lp ℂ 2 volume) τ) ∂volume := by
        -- Combine `L2.inner_def` with the pointwise scalar inner expansion.
        -- L2.inner_def says: inner (V g) (V f) = ∫ inner (V g τ) (V f τ) dτ
        -- For ℂ, inner a b = starRingEnd a * b
        rw [hinner0]
        convert hinner_int using 2
        ext τ
        rw [RCLike.inner_apply]
        ring

      -- Step 2.2b: transport the a.e. identities `hVf`, `hVg` to the product
      -- integrand involving the normalized Mellin transforms.
      -- The normalized Mellin transform functions agree a.e. with V f and V g.

      -- Conjugation respects a.e. equality.
      have hB_conj_ae :
          (fun (τ : ℝ) => starRingEnd ℂ (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ)))
            =ᵐ[volume]
          (fun (τ : ℝ) => starRingEnd ℂ ((V g : Lp ℂ 2 volume) τ)) := by
        refine hVg.mono ?_
        intro τ hτ
        simp [hτ]

      -- Combine the a.e. equalities for the two factors.
      have h_integrand_ae :
          (fun τ : ℝ =>
            (rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
            starRingEnd ℂ (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ)))
            =ᵐ[volume]
          (fun τ : ℝ =>
            (V f : Lp ℂ 2 volume) τ *
              starRingEnd ℂ ((V g : Lp ℂ 2 volume) τ)) := by
        exact (hVf.mul hB_conj_ae)

      have h_integral_eq :
          ∫ τ : ℝ,
            (rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
              starRingEnd ℂ (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
            = ∫ τ : ℝ,
                (V f : Lp ℂ 2 volume) τ *
                  starRingEnd ℂ ((V g : Lp ℂ 2 volume) τ) ∂volume := by
        refine integral_congr_ae ?_
        exact h_integrand_ae

      -- Step 2.2c: conclude by using the integral equality and inner product.
      calc
        ∫ τ : ℝ,
            (rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
              starRingEnd ℂ
                (rescaleNorm⁻¹ • mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
            = ∫ τ : ℝ,
                (V f : Lp ℂ 2 volume) τ *
                  starRingEnd ℂ ((V g : Lp ℂ 2 volume) τ) ∂volume := h_integral_eq
        _ = inner ℂ (V g) (V f) := hinner

    sorry

  -- Step 3: use unitarity of `V` to transfer the inner product back to `Hσ σ`.
  have h_unitary :
      inner ℂ (V f) (V g) = inner ℂ f g := by
    -- This is the defining property of a linear isometry equivalence
    -- between Hilbert spaces: it preserves the inner product.
    sorry

  -- Step 4: identify the Hσ inner product ⟪f, g⟫ with the explicit
  -- weighted integral over (0,∞) appearing on the right-hand side.
  have h_space_inner :
      inner ℂ f g
        = ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℂ) x *
            starRingEnd ℂ ((g : ℝ → ℂ) x) * (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := by
    -- Expand the Hσ inner product by definition, rewrite the measure as
    -- the weighted Lebesgue measure x^(2σ-1) dx on (0,∞), and identify
    -- the resulting integral with the stated RHS.
    sorry

  -- Step 5: assemble the chain of equalities.
  calc
    ∫ τ : ℝ,
        mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
          starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
        = inner ℂ (V f) (V g) := h_freq_inner
    _ = inner ℂ f g := h_unitary
    _ = ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℂ) x *
          starRingEnd ℂ ((g : ℝ → ℂ) x) * (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume :=
      h_space_inner

/-- Energy conservation in Mellin space (Plancherel theorem for Mellin transform).
The L² norm in the weighted space Hσ(σ) is preserved (up to a constant factor)
under the Mellin transform. The factor 2π comes from the angular frequency
normalization in the Fourier kernel e^(-2πiξt). -/
theorem mellin_energy_conservation (σ : ℝ) (f : Hσ σ) :
    (2 * Real.pi) * ∫ x in Set.Ioi (0 : ℝ), ‖(f : ℝ → ℂ) x‖ ^ 2 * (x : ℝ) ^ (2 * σ - 1) ∂volume
    = ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
  -- Proof outline:
  -- 1. LHS = 2π · ∫ |f(x)|² x^(2σ-1) dx = 2π · ‖f‖²_{Hσ(σ)}
  -- 2. Change of variables x = e^t: LHS = 2π · ∫ |LogPull(σ,f)(t)|² dt
  -- 3. M[f](σ+iτ) = F[LogPull(σ,f)](τ/2π) where F uses kernel e^(-2πiξt)
  -- 4. Variable change τ ↔ ξ = τ/2π in RHS gives Fourier-Plancherel
  -- 5. ∫ |M[f](σ+iτ)|² dτ = 2π · ∫ |F[LogPull](ξ)|² dξ = 2π · ‖LogPull(σ,f)‖²
  sorry

end Applications

end Frourio
