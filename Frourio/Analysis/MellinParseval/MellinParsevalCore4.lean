import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore3
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

/-- Bridge from the ENNReal/Real presentation (coming from Parseval on `(0,∞)`) to
the Hσ-norm squared for the specific combination `f + g`. This packages the
rewriting needed for the `h_eq_fp` step inside the main proof. -/
lemma h_eq_fp_of_ofReal (σ : ℝ) (C : ℝ) (f g : Hσ σ)
    (h_ofReal_fp : Complex.ofReal
      ((∫⁻ x in Set.Ioi (0 : ℝ),
          ‖Hσ.toFun (f + g) x‖₊ ^ 2
            * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal)
      = Complex.ofReal (C * ∫ τ : ℝ,
          ‖mellinTransform (((f + g : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume)) :
    Complex.ofReal (‖(f + g : Hσ σ)‖ ^ 2)
      = Complex.ofReal (C * ∫ τ : ℝ,
          ‖mellinTransform ((↑↑f + ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume) := by
  classical
  -- Abbreviate the sum in Hσ.
  set h := (f + g : Hσ σ) with hh

  -- Step 1: peel off `Complex.ofReal` on the hypothesis to obtain the real equality
  -- relating the ENNReal/Real presentation to the Mellin-side integral for `h`.
  have h_real :
      ((∫⁻ x in Set.Ioi (0 : ℝ),
          ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal)
        = C * ∫ τ : ℝ,
            ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume := by
    -- Use injectivity of `Complex.ofReal`.
    apply Complex.ofReal_injective
    simpa [hh] using h_ofReal_fp

  -- Step 2: relate the Hσ norm-square of `h` to the ENNReal/Real presentation.
  -- Use the canonical formula for the Hσ norm squared (written over Lebesgue on (0,∞)).
  have h_norm_toReal :
      Complex.ofReal (‖h‖ ^ 2)
        = Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal) := by
    simpa using congrArg Complex.ofReal (Hσ_norm_squared (σ := σ) h)

  -- Step 3: combine the previous two steps and identify the Mellin-side integrand.
  calc
    Complex.ofReal (‖(f + g : Hσ σ)‖ ^ 2)
        = Complex.ofReal (‖h‖ ^ 2) := by simp [hh]
    _ = Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal) :=
        h_norm_toReal
    _ = Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) := by
        simp [h_real]
    _ = Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform ((↑↑f + ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume) := by
        -- Replace the Mellin input `((h : Hσ σ) : ℝ → ℂ)` by `↑↑f + ↑↑g`.
        -- Use a.e.-equality of representatives on `(0, ∞)` transported to Lebesgue.
        classical
        -- a.e. equality under the weighted measure
        have h_add_ae_weighted := toFun_add_ae σ f g
        -- transport to Lebesgue restricted to (0,∞)
        have h_reverse_ac :
            volume.restrict (Set.Ioi (0 : ℝ)) ≪
              mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
          volume_restrict_absolutelyContinuous_weighted σ
        have h_add_ae_vol :
            (fun x : ℝ => Hσ.toFun (f + g) x)
              =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
            (fun x : ℝ => Hσ.toFun f x + Hσ.toFun g x) :=
          h_reverse_ac.ae_eq h_add_ae_weighted
        have h_add_ae_vol' :
            (fun x : ℝ => ((h : Hσ σ) : ℝ → ℂ) x)
              =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
            (fun x : ℝ => Hσ.toFun f x + Hσ.toFun g x) := by
          simpa [hh] using h_add_ae_vol
        -- pointwise equality of Mellin transforms for each τ via integral_congr_ae
        have h_mellin_eq : ∀ τ : ℝ,
            mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)
              = mellinTransform ((↑↑f + ↑↑g)) (σ + I * τ) := by
          intro τ
          unfold Frourio.mellinTransform
          have h_ae_mul :
              (fun x : ℝ => ((h : Hσ σ) : ℝ → ℂ) x * x ^ (σ + I * (τ : ℂ) - 1))
                =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
              (fun x : ℝ => (Hσ.toFun f x + Hσ.toFun g x)
                    * x ^ (σ + I * (τ : ℂ) - 1)) := by
            refine h_add_ae_vol'.mono ?_
            intro x hx
            simp [hx, mul_comm, mul_left_comm, mul_assoc]
          simpa using integral_congr_ae h_ae_mul
        -- now upgrade to equality of the L²-integrands in τ and integrate
        have h_aeτ :
            (fun τ : ℝ =>
              ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2)
              =ᵐ[volume]
            (fun τ : ℝ =>
              ‖mellinTransform ((↑↑f + ↑↑g)) (σ + I * τ)‖ ^ 2) := by
          refine Filter.Eventually.of_forall ?_
          intro τ; simp [h_mellin_eq τ]
        have h_int_eq :
            ∫ τ : ℝ,
                ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume
              = ∫ τ : ℝ,
                ‖mellinTransform ((↑↑f + ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume :=
          integral_congr_ae h_aeτ
        simp [h_int_eq]

/-- Bridge lemma for the subtraction case: converts the ENNReal/Real presentation
for `f - g` into the desired Mellin-side squared norm identity. This packages the
`h_eq_fm` step used in the main polarization argument. -/
lemma h_eq_fm_of_ofReal (σ : ℝ) (C : ℝ) (f g : Hσ σ)
    (h_ofReal_fm : Complex.ofReal
      ((∫⁻ x in Set.Ioi (0 : ℝ),
          ‖Hσ.toFun (f - g) x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal)
      = Complex.ofReal (C * ∫ τ : ℝ,
          ‖mellinTransform (((f - g : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume)) :
    Complex.ofReal (‖(f - g : Hσ σ)‖ ^ 2)
      = Complex.ofReal (C * ∫ τ : ℝ,
          ‖mellinTransform ((↑↑f - ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume) := by
  classical
  -- Abbreviate the difference in Hσ.
  set h := (f - g : Hσ σ) with hh

  -- Step 1: peel off `Complex.ofReal` on the hypothesis to obtain the real equality
  -- for the ENNReal/Real presentation attached to `h`.
  have h_real :
      ((∫⁻ x in Set.Ioi (0 : ℝ),
          ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal)
        = C * ∫ τ : ℝ,
            ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume := by
    -- Use injectivity of `Complex.ofReal`.
    apply Complex.ofReal_injective
    simpa [hh] using h_ofReal_fm

  -- Step 2: identify the Mellin-side integrand for `h` with the difference of
  -- representatives `↑↑f - ↑↑g` a.e., then integrate.
  -- We mimic the addition case, deriving an a.e. identity on `(0,∞)` and
  -- transporting it to Lebesgue restricted to `(0,∞)`.
  have h_add_ae_weighted := toFun_add_ae σ f ((-1 : ℂ) • g)
  have h_smul_ae_weighted := toFun_smul_ae σ (-1 : ℂ) g
  -- Combine the two a.e. relations to obtain the subtraction form under the
  -- weighted measure used in the Hσ setup.
  have h_sub_ae_weighted :
      (fun x : ℝ => Hσ.toFun (f - g) x)
        =ᵐ[mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun g x) := by
    -- Combine AE equalities for addition and scalar multiplication, then
    -- rewrite `f - g` as `f + (-1)•g` and simplify.
    refine (h_add_ae_weighted.and h_smul_ae_weighted).mono ?_
    intro x hx
    have hx_add := hx.1
    have hx_smul := hx.2
    calc
      Hσ.toFun (f - g) x
          = Hσ.toFun (f + (-1 : ℂ) • g) x := by
              simp [sub_eq_add_neg, neg_one_smul]
      _ = Hσ.toFun f x + Hσ.toFun ((-1 : ℂ) • g) x := by
              simpa using hx_add
      _ = Hσ.toFun f x + (-1) * Hσ.toFun g x := by
              simpa [Pi.smul_apply] using hx_smul
      _ = Hσ.toFun f x - Hσ.toFun g x := by
              simp [sub_eq_add_neg]

  -- transport to Lebesgue restricted to (0,∞)
  have h_reverse_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ

  have h_sub_ae_vol :
      (fun x : ℝ => Hσ.toFun (f - g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun g x) :=
    h_reverse_ac.ae_eq h_sub_ae_weighted

  have h_sub_ae_vol' :
      (fun x : ℝ => ((h : Hσ σ) : ℝ → ℂ) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun g x) := by
    simpa [hh] using h_sub_ae_vol

  -- pointwise equality of Mellin transforms for each τ via integral_congr_ae
  have h_mellin_eq : ∀ τ : ℝ,
      mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)
        = mellinTransform ((↑↑f - ↑↑g)) (σ + I * τ) := by
    intro τ
    unfold Frourio.mellinTransform
    have h_ae_mul :
        (fun x : ℝ => ((h : Hσ σ) : ℝ → ℂ) x * x ^ (σ + I * (τ : ℂ) - 1))
          =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun x : ℝ => (Hσ.toFun f x - Hσ.toFun g x)
              * x ^ (σ + I * (τ : ℂ) - 1)) := by
      refine h_sub_ae_vol'.mono ?_
      intro x hx
      simp [hx, mul_comm, mul_left_comm, mul_assoc]
    simpa using integral_congr_ae h_ae_mul

  -- now upgrade to equality of the L²-integrands in τ and integrate
  have h_aeτ :
      (fun τ : ℝ =>
        ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2)
        =ᵐ[volume]
      (fun τ : ℝ =>
        ‖mellinTransform ((↑↑f - ↑↑g)) (σ + I * τ)‖ ^ 2) := by
    refine Filter.Eventually.of_forall ?_
    intro τ; simp [h_mellin_eq τ]

  have h_int_eq :
      ∫ τ : ℝ,
          ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume
        = ∫ τ : ℝ,
          ‖mellinTransform ((↑↑f - ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume :=
    integral_congr_ae h_aeτ

  -- Step 3: identify the Hσ norm-square of `h` with the ENNReal/Real presentation.
  have h_norm_toReal :
      Complex.ofReal (‖h‖ ^ 2)
        = Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal) := by
    simpa using (congrArg Complex.ofReal (Hσ_norm_squared (σ := σ) h))

  calc
    Complex.ofReal (‖(f - g : Hσ σ)‖ ^ 2)
        = Complex.ofReal (‖h‖ ^ 2) := by simp [hh]
    _ = Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal) :=
        h_norm_toReal
    _ = Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) := by
        simp [h_real]
    _ = Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform ((↑↑f - ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume) := by
        simp [h_int_eq]

/-- Bridge lemma for the `f + I • g` case: converts the ENNReal/Real presentation
for `f + I • g` into the Mellin-side squared norm identity used in the polarization. -/
lemma h_eq_fi_of_ofReal (σ : ℝ) (C : ℝ) (f g : Hσ σ)
    (h_ofReal_fi : Complex.ofReal ((∫⁻ x in Set.Ioi (0 : ℝ),
      ‖Hσ.toFun (f + Complex.I • g) x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal)
      = Complex.ofReal (C * ∫ τ : ℝ,
          ‖mellinTransform (((f + Complex.I • g : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume)) :
    Complex.ofReal (‖(f + Complex.I • g : Hσ σ)‖ ^ 2)
      = Complex.ofReal (C * ∫ τ : ℝ,
          ‖mellinTransform ((↑↑f + I • ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume) := by
  classical
  -- Abbreviate the combination in Hσ.
  set h := (f + Complex.I • g : Hσ σ) with hh

  -- Step 1: convert the hypothesis to a real equality by injectivity of `Complex.ofReal`.
  have h_real :
      ((∫⁻ x in Set.Ioi (0 : ℝ),
          ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal)
        = C * ∫ τ : ℝ,
            ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume := by
    apply Complex.ofReal_injective
    simpa [hh] using h_ofReal_fi

  -- Step 2: identify the Mellin-side integrand for `h` with `↑↑f + I • ↑↑g` a.e.
  have h_add_ae_weighted := toFun_add_ae σ f (Complex.I • g)
  have h_smul_ae_weighted := toFun_smul_ae σ Complex.I g
  have h_add_ae_weighted' :
      (fun x : ℝ => Hσ.toFun (f + Complex.I • g) x)
        =ᵐ[mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x : ℝ => Hσ.toFun f x + Complex.I * Hσ.toFun g x) := by
    refine (h_add_ae_weighted.and h_smul_ae_weighted).mono ?_
    intro x hx
    have hx_add := hx.1; have hx_smul := hx.2
    calc
      Hσ.toFun (f + Complex.I • g) x
          = Hσ.toFun f x + Hσ.toFun (Complex.I • g) x := by
              simpa using hx_add
      _ = Hσ.toFun f x + Complex.I * Hσ.toFun g x := by
              simpa [Pi.smul_apply] using hx_smul

  -- Transport to Lebesgue restricted to (0, ∞).
  have h_reverse_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ

  have h_add_ae_vol :
      (fun x : ℝ => Hσ.toFun (f + Complex.I • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x + Complex.I * Hσ.toFun g x) :=
    h_reverse_ac.ae_eq h_add_ae_weighted'

  have h_add_ae_vol' :
      (fun x : ℝ => ((h : Hσ σ) : ℝ → ℂ) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x + Complex.I * Hσ.toFun g x) := by
    simpa [hh] using h_add_ae_vol

  -- Pointwise equality of Mellin transforms for each τ via integral_congr_ae.
  have h_mellin_eq : ∀ τ : ℝ,
      mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)
        = mellinTransform ((↑↑f + Complex.I • ↑↑g)) (σ + I * τ) := by
    intro τ
    unfold Frourio.mellinTransform
    have h_ae_mul :
        (fun x : ℝ => ((h : Hσ σ) : ℝ → ℂ) x * x ^ (σ + I * (τ : ℂ) - 1))
          =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun x : ℝ => (Hσ.toFun f x + Complex.I * Hσ.toFun g x)
              * x ^ (σ + I * (τ : ℂ) - 1)) := by
      refine h_add_ae_vol'.mono ?_
      intro x hx
      simp [hx, mul_comm, mul_left_comm, mul_assoc]
    simpa using integral_congr_ae h_ae_mul

  -- Upgrade to equality of the L²-integrands in τ and integrate.
  have h_aeτ :
      (fun τ : ℝ =>
        ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2)
        =ᵐ[volume]
      (fun τ : ℝ =>
        ‖mellinTransform ((↑↑f + Complex.I • ↑↑g)) (σ + I * τ)‖ ^ 2) := by
    refine Filter.Eventually.of_forall ?_
    intro τ; simp [h_mellin_eq τ]

  have h_int_eq :
      ∫ τ : ℝ,
          ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume
        = ∫ τ : ℝ,
          ‖mellinTransform ((↑↑f + Complex.I • ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume :=
    integral_congr_ae h_aeτ

  -- Step 3: identify the Hσ norm-square of `h` with the ENNReal/Real presentation.
  have h_norm_toReal :
      Complex.ofReal (‖h‖ ^ 2)
        = Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal) := by
    simpa using (congrArg Complex.ofReal (Hσ_norm_squared (σ := σ) h))

  -- Combine all steps.
  calc
    Complex.ofReal (‖(f + Complex.I • g : Hσ σ)‖ ^ 2)
        = Complex.ofReal (‖h‖ ^ 2) := by simp [hh]
    _ = Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal) :=
        h_norm_toReal
    _ = Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) := by
        simp [h_real]
    _ = Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform ((↑↑f + I • ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume) := by
        simp [h_int_eq]

/-- Bridge lemma for the `f - I • g` case: converts the ENNReal/Real presentation
for `f - I • g` into the Mellin-side squared norm identity used in the polarization. -/
lemma h_eq_fmi_of_ofReal (σ : ℝ) (C : ℝ) (f g : Hσ σ)
    (h_ofReal_fmi : Complex.ofReal ((∫⁻ x in Set.Ioi (0 : ℝ),
      ‖Hσ.toFun (f - Complex.I • g) x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal)
      = Complex.ofReal (C * ∫ τ : ℝ,
          ‖mellinTransform (((f - Complex.I • g : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume)) :
    Complex.ofReal (‖(f - Complex.I • g : Hσ σ)‖ ^ 2)
      = Complex.ofReal (C * ∫ τ : ℝ,
          ‖mellinTransform ((↑↑f - I • ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume) := by
  classical
  -- Abbreviate the combination in Hσ.
  set h := (f - Complex.I • g : Hσ σ) with hh

  -- Convert the hypothesis using injectivity of `Complex.ofReal`.
  have h_real :
      ((∫⁻ x in Set.Ioi (0 : ℝ),
          ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal)
        = C * ∫ τ : ℝ,
            ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume := by
    apply Complex.ofReal_injective
    simpa [hh] using h_ofReal_fmi

  -- a.e. equality for the pointwise representatives: f - I•g = f + (-I)•g
  have h_add_ae_weighted := toFun_add_ae σ f ((-Complex.I : ℂ) • g)
  have h_smul_ae_weighted := toFun_smul_ae σ (-Complex.I : ℂ) g
  have h_sub_ae_weighted' :
      (fun x : ℝ => Hσ.toFun (f - Complex.I • g) x)
        =ᵐ[mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x : ℝ => Hσ.toFun f x - Complex.I * Hσ.toFun g x) := by
    refine (h_add_ae_weighted.and h_smul_ae_weighted).mono ?_
    intro x hx
    have hx_add := hx.1; have hx_smul := hx.2
    calc
      Hσ.toFun (f - Complex.I • g) x
          = Hσ.toFun (f + (-Complex.I : ℂ) • g) x := by
              simp [sub_eq_add_neg]
      _ = Hσ.toFun f x + Hσ.toFun ((-Complex.I : ℂ) • g) x := by
              simpa using hx_add
      _ = Hσ.toFun f x + (-Complex.I) * Hσ.toFun g x := by
              simpa [Pi.smul_apply] using hx_smul
      _ = Hσ.toFun f x - Complex.I * Hσ.toFun g x := by
              simp [sub_eq_add_neg]

  -- Transport this a.e. equality to Lebesgue restricted to (0, ∞).
  have h_reverse_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ

  have h_sub_ae_vol :
      (fun x : ℝ => Hσ.toFun (f - Complex.I • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x - Complex.I * Hσ.toFun g x) :=
    h_reverse_ac.ae_eq h_sub_ae_weighted'

  have h_sub_ae_vol' :
      (fun x : ℝ => ((h : Hσ σ) : ℝ → ℂ) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x - Complex.I * Hσ.toFun g x) := by
    simpa [hh] using h_sub_ae_vol

  -- Pointwise equality of Mellin transforms for each τ via integral_congr_ae.
  have h_mellin_eq : ∀ τ : ℝ,
      mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)
        = mellinTransform ((↑↑f - Complex.I • ↑↑g)) (σ + I * τ) := by
    intro τ
    unfold Frourio.mellinTransform
    have h_ae_mul :
        (fun x : ℝ => ((h : Hσ σ) : ℝ → ℂ) x * x ^ (σ + I * (τ : ℂ) - 1))
          =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun x : ℝ => (Hσ.toFun f x - Complex.I * Hσ.toFun g x)
              * x ^ (σ + I * (τ : ℂ) - 1)) := by
      refine h_sub_ae_vol'.mono ?_
      intro x hx
      simp [hx, mul_comm, mul_left_comm, mul_assoc]
    simpa using integral_congr_ae h_ae_mul

  -- Upgrade to equality of the L²-integrands in τ and integrate.
  have h_aeτ :
      (fun τ : ℝ =>
        ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2)
        =ᵐ[volume]
      (fun τ : ℝ =>
        ‖mellinTransform ((↑↑f - Complex.I • ↑↑g)) (σ + I * τ)‖ ^ 2) := by
    refine Filter.Eventually.of_forall ?_
    intro τ; simp [h_mellin_eq τ]

  have h_int_eq :
      ∫ τ : ℝ,
          ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume
        = ∫ τ : ℝ,
          ‖mellinTransform ((↑↑f - Complex.I • ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume :=
    integral_congr_ae h_aeτ

  -- Identify the Hσ norm-square of `h` with the ENNReal/Real presentation.
  have h_norm_toReal :
      Complex.ofReal (‖h‖ ^ 2)
        = Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal) := by
    simpa using (congrArg Complex.ofReal (Hσ_norm_squared (σ := σ) h))

  -- Combine all steps.
  calc
    Complex.ofReal (‖(f - Complex.I • g : Hσ σ)‖ ^ 2)
        = Complex.ofReal (‖h‖ ^ 2) := by simp [hh]
    _ = Complex.ofReal
          ((∫⁻ x in Set.Ioi (0 : ℝ),
              ‖Hσ.toFun h x‖₊ ^ 2 * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal) :=
        h_norm_toReal
    _ = Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) := by
        simp [h_real]
    _ = Complex.ofReal (C * ∫ τ : ℝ,
            ‖mellinTransform ((↑↑f - I • ↑↑g)) (σ + I * τ)‖ ^ 2 ∂volume) := by
        simp [h_int_eq]

end ParsevalEquivalence

end Frourio
