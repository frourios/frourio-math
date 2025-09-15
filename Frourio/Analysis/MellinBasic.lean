import Frourio.Analysis.MellinTransform
import Frourio.Algebra.Operators
import Frourio.Algebra.Properties
import Frourio.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory Measure Real Complex
open scoped Topology ENNReal

namespace Frourio

section MulHaarMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma mulHaar_apply (s : Set ℝ) (hs : MeasurableSet s) :
    mulHaar s = ∫⁻ x in s ∩ Set.Ioi 0, ENNReal.ofReal (1 / x) ∂volume := by
  simp only [mulHaar, restrict_apply hs]
  rw [withDensity_apply _ (hs.inter measurableSet_Ioi)]

noncomputable instance (σ : ℝ) : NormedAddCommGroup (Hσ σ) := inferInstance
noncomputable instance (σ : ℝ) : NormedSpace ℂ (Hσ σ) := inferInstance

-- Helper lemmas for Hσ_norm_squared

lemma Lp_norm_sq_as_lintegral {ν : Measure ℝ} (f : Lp ℂ 2 ν) :
    ‖f‖^2 = (∫⁻ x, ‖(f : ℝ → ℂ) x‖₊ ^ 2 ∂ν).toReal := by
  classical
  -- Step A: L²ノルム二乗を ENNReal ノルムで表す
  have h0 : (2 : ℝ≥0∞) ≠ 0 := by simp
  have htop : (2 : ℝ≥0∞) ≠ ∞ := by simp
  have heq := eLpNorm_eq_lintegral_rpow_enorm (μ := ν) (f := f) h0 htop
  -- Set A = ∫⁻ ‖f x‖ₑ ^ 2
  set A : ℝ≥0∞ := ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) ∂ν
  have hnorm : ‖f‖ = (A ^ (1 / (2 : ℝ))).toReal := by
    simp [Lp.norm_def, heq, ENNReal.toReal_ofNat, one_div, A]
  -- Square both sides and simplify ((A^(1/2)).toReal)^2 = (A).toReal
  have hsq : ‖f‖ ^ 2 = ((A ^ (1 / (2 : ℝ))).toReal) ^ 2 := by
    -- Square both sides of hnorm without rewriting to multiplication
    have h := congrArg (fun t => t ^ 2) hnorm
    exact h
  have h_toReal_sq : ((A ^ ((2 : ℝ)⁻¹)).toReal) ^ 2 = A.toReal := by
    -- First, move the square outside of toReal using toReal_pow
    have h1 : ((A ^ ((2 : ℝ)⁻¹)).toReal) ^ 2 = (((A ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ)).toReal) := by
      simp [pow_two]
    -- Convert nat exponent 2 to real exponent 2 and apply rpow_mul
    have h2a : ((A ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ)) = (A ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) := by
      simp
    have h2b : (A ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = A ^ (((2 : ℝ)⁻¹) * (2 : ℝ)) := by
      exact (ENNReal.rpow_mul A ((2 : ℝ)⁻¹) (2 : ℝ)).symm
    have h2 : ((A ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ)) = A ^ (((2 : ℝ)⁻¹) * (2 : ℝ)) := by
      exact h2a.trans h2b
    have h2' : (((A ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ)).toReal) = (A ^ (((2 : ℝ)⁻¹) * (2 : ℝ))).toReal := by
      simpa using congrArg ENNReal.toReal h2
    have h3 : ((2 : ℝ)⁻¹) * (2 : ℝ) = (1 : ℝ) := by
      have : (2 : ℝ) ≠ 0 := by norm_num
      simp [this]
    have h4 : (A ^ (((2 : ℝ)⁻¹) * (2 : ℝ))).toReal = (A ^ (1 : ℝ)).toReal := by simp
    -- Chain the equalities
    calc
      ((A ^ ((2 : ℝ)⁻¹)).toReal) ^ 2
          = (((A ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ)).toReal) := h1
      _ = (A ^ (((2 : ℝ)⁻¹) * (2 : ℝ))).toReal := h2'
      _ = (A ^ (1 : ℝ)).toReal := h4
      _ = A.toReal := by simp [ENNReal.rpow_one]
  have h_enorm : ‖f‖ ^ 2 = A.toReal := by
    -- rewrite to match exponent notation 2⁻¹
    have hinv : (A ^ (1 / (2 : ℝ))).toReal = (A ^ ((2 : ℝ)⁻¹)).toReal := by
      have : (1 / (2 : ℝ)) = ((2 : ℝ)⁻¹) := by simp [one_div]
      simp [this]
    simpa [hsq, hinv]
  -- Step B: 被積分関数を ‖·‖₊ ^ 2 に置換
  have h_pointwise : (fun x => ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ)) =
    (fun x => ((‖(f : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))) := by
    funext x
    have hx : (‖(f : ℝ → ℂ) x‖ₑ : ℝ≥0∞) = (‖(f : ℝ → ℂ) x‖₊ : ℝ≥0∞) := rfl
    simp [hx]
  have h_integral_swap : (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) ∂ν)
      = (∫⁻ x, ((‖(f : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂ν) := by
    refine lintegral_congr_ae ?_;
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hx : (‖(f : ℝ → ℂ) x‖ₑ : ℝ≥0∞) = (‖(f : ℝ → ℂ) x‖₊ : ℝ≥0∞) := rfl
    simp [hx]
  have h_goal : ‖f‖ ^ 2
      = (∫⁻ x, ((‖(f : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂ν).toReal := by
    simpa [A, h_integral_swap] using h_enorm
  simpa using h_goal

lemma lintegral_withDensity_expand {g : ℝ → ℝ≥0∞} {wσ : ℝ → ℝ≥0∞}
    (hg : Measurable g) (hwσ : Measurable wσ) :
    ∫⁻ x, g x ∂(mulHaar.withDensity wσ) = ∫⁻ x, g x * wσ x ∂mulHaar := by
  -- The library lemma gives ∫ g ∂(μ.withDensity w) = ∫ w * g ∂μ.
  -- Our statement has the factors reversed; use commutativity of (*) in ℝ≥0∞.
  have h := (lintegral_withDensity_eq_lintegral_mul (μ := mulHaar)
      (f := wσ) (h_mf := hwσ)) hg
  simpa [mul_comm] using h

lemma lintegral_mulHaar_expand {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂mulHaar = ∫⁻ x in Set.Ioi 0, g x * ENNReal.ofReal (1 / x) ∂volume := by
  -- Measurability of the density x ↦ ofReal (x⁻¹)
  have h_w : Measurable (fun x : ℝ => ENNReal.ofReal (x⁻¹)) := by
    have hinv : Measurable fun x : ℝ => x⁻¹ := measurable_inv
    exact ENNReal.measurable_ofReal.comp hinv
  -- Unfold mulHaar and use the set-lintegral notation directly
  -- Expand definition of mulHaar and apply density lemma on the restricted measure
  -- First, use the global lemma and then restrict both sides to the set `Ioi 0`
  -- Work over the restricted measure and then rewrite back to set-lintegral form
  have h :=
    ((lintegral_withDensity_eq_lintegral_mul (μ := volume.restrict (Set.Ioi 0))
        (f := fun x => ENNReal.ofReal (x⁻¹)) (h_mf := h_w) (g := g)) hg)
  -- Show withDensity commutes with restrict for our measurable weight
  have h_comm :
      (volume.withDensity (fun x => ENNReal.ofReal (x⁻¹))).restrict (Set.Ioi 0)
        = (volume.restrict (Set.Ioi 0)).withDensity (fun x => ENNReal.ofReal (x⁻¹)) := by
    ext s hs
    simp [withDensity_apply _ hs, withDensity_apply _ (hs.inter measurableSet_Ioi),
      restrict_apply, hs]
  have h' :
      (∫⁻ x, g x ∂((volume.withDensity (fun x => ENNReal.ofReal (x⁻¹))).restrict (Set.Ioi 0)))
        = (∫⁻ x, ENNReal.ofReal (x⁻¹) * g x ∂(volume.restrict (Set.Ioi 0))) := by
    simpa [h_comm]
      using h
  simpa [mulHaar, one_div, mul_comm]
    using h'

lemma weight_product_simplify (σ : ℝ) (x : ℝ) (hx : x ∈ Set.Ioi 0) :
    ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal (1 / x) =
    ENNReal.ofReal (x ^ (2 * σ - 1) / x) := by
  have hxpos : 0 < x := hx
  have hx0 : 0 ≤ x := le_of_lt hxpos
  have h1 : 0 ≤ x ^ (2 * σ - 1) := by
    simpa using Real.rpow_nonneg hx0 (2 * σ - 1)
  have h2 : 0 ≤ 1 / x := by
    have : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0
    simpa [one_div] using this
  calc
    ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal (1 / x)
        = ENNReal.ofReal (1 / x) * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
          simp [mul_comm]
    _ = ENNReal.ofReal ((1 / x) * (x ^ (2 * σ - 1))) := by
          -- `ENNReal.ofReal_mul` only needs nonnegativity of the first factor
          -- and states `ofReal (a*b) = ofReal a * ofReal b`.
          -- We use the symmetric direction to match the goal order.
          simpa using (ENNReal.ofReal_mul (p := 1 / x) (q := x ^ (2 * σ - 1)) h2).symm
    _ = ENNReal.ofReal ((x ^ (2 * σ - 1)) * (1 / x)) := by
          simp [mul_comm]
    _ = ENNReal.ofReal (x ^ (2 * σ - 1) / x) := by
          simp [div_eq_mul_inv]

lemma Hσ_norm_squared {σ : ℝ} (f : Hσ σ) :
    ‖f‖^2 = (∫⁻ x in Set.Ioi 0, ‖Hσ.toFun f x‖₊ ^ 2 *
      ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal := by
  classical
  -- Abbreviate the weight and the integrand
  set wσ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x ^ (2 * σ - 1)) with hwσ
  have hwσ_meas : Measurable wσ := by
    rw [hwσ]
    measurability
  set g : ℝ → ℝ≥0∞ := fun x => (ENNReal.ofReal (‖Hσ.toFun f x‖)) ^ (2 : ℕ) with hgdef
  have hg_meas : Measurable g := by
    -- Build measurability from the Lp representative via the real norm
    have hsm : StronglyMeasurable fun x => Hσ.toFun f x := by
      simpa using (Lp.stronglyMeasurable (f := (f : Lp ℂ 2 (mulHaar.withDensity wσ))))
    have hfn : Measurable fun x => Hσ.toFun f x := hsm.measurable
    have hnorm : Measurable fun x => ‖Hσ.toFun f x‖ := hfn.norm
    have h_ofReal : Measurable fun x => ENNReal.ofReal (‖Hσ.toFun f x‖) :=
      ENNReal.measurable_ofReal.comp hnorm
    simpa [hgdef] using h_ofReal.pow_const (2 : ℕ)
  -- Step 1: express the L² norm squared as a lintegral over the weighted measure
  have h0 :=
    Lp_norm_sq_as_lintegral (ν := mulHaar.withDensity wσ) (f := (f : Lp ℂ 2 _))
  -- Replace the generic integrand with g
  have h0' : ‖f‖ ^ 2 = (∫⁻ x, g x ∂(mulHaar.withDensity wσ)).toReal := by
    simpa [hgdef] using h0
  -- Step 2: expand the withDensity weight
  have h1 :
      (∫⁻ x, g x ∂(mulHaar.withDensity wσ))
        = ∫⁻ x, g x * wσ x ∂mulHaar := by
    exact lintegral_withDensity_expand (g := g) (wσ := wσ) hg_meas hwσ_meas
  -- Step 3: expand mulHaar as a set-lintegral over Ioi 0 with density 1/x
  have h2 :
      (∫⁻ x, g x * wσ x ∂mulHaar)
        = ∫⁻ x in Set.Ioi 0, (g x * wσ x) * ENNReal.ofReal (1 / x) ∂volume := by
    -- Apply the expansion lemma to the function x ↦ g x * wσ x
    simpa using lintegral_mulHaar_expand (g := fun x => g x * wσ x)
      ((hg_meas.mul hwσ_meas))
  -- Combine the two densities later under ae on Ioi 0; no global pointwise equality needed
  -- Put all steps together and simplify to the target expression
  calc
    ‖f‖ ^ 2
        = (∫⁻ x, g x ∂(mulHaar.withDensity wσ)).toReal := h0'
    _ = (∫⁻ x, g x * wσ x ∂mulHaar).toReal := by simp [h1]
    _ = (∫⁻ x in Set.Ioi 0, (g x * wσ x) * ENNReal.ofReal (1 / x) ∂volume).toReal := by
          simp [h2]
    _ = (∫⁻ x in Set.Ioi 0,
            ((‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal := by
          -- reorder factors and apply pointwise simplification for the weights
          -- equality of the lintegrand under the set integral
          refine congrArg ENNReal.toReal ?h
          apply lintegral_congr_ae
          -- Reduce to an implication over the base measure via ae_restrict
          refine ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
          refine Filter.Eventually.of_forall ?_
          intro x hx
          -- On Ioi 0, apply the weight simplification (commuted to start with ofReal (1/x))
          have hx' := weight_product_simplify σ x hx
          have hx'' : ENNReal.ofReal (1 / x) * ENNReal.ofReal (x ^ (2 * σ - 1))
              = ENNReal.ofReal (x ^ (2 * σ - 1) / x) := by
            simpa [one_div, mul_comm] using hx'
          -- Multiply both sides by the norm square on the right and simplify
          simpa [g, hgdef, wσ, hwσ, mul_comm, mul_left_comm, mul_assoc]
            using congrArg (fun t => t * (‖Hσ.toFun f x‖ₑ ^ (2 : ℕ))) hx''

section BasicAPI

lemma zeroLatticeSpacing_pos {φ : ℝ} (hφ : 1 < φ) : 0 < zeroLatticeSpacing φ := by
  simp only [zeroLatticeSpacing]
  exact div_pos Real.pi_pos (Real.log_pos hφ)

end BasicAPI

end MulHaarMeasure

section MellinIsometry

/-- Helper lemma: The preimage of s under log, intersected with (0,∞), equals exp(s) -/
lemma log_preimage_inter_Ioi_eq_exp_image {s : Set ℝ} :
    Real.log ⁻¹' s ∩ Set.Ioi (0 : ℝ) = Real.exp '' s := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_image]
  constructor
  · intro ⟨hlog, hpos⟩
    use Real.log x
    constructor
    · exact hlog
    · exact Real.exp_log hpos
  · intro ⟨t, ht, hxt⟩
    rw [← hxt]
    constructor
    · simp [Real.log_exp, ht]
    · exact Real.exp_pos t

/-- Helper lemma: For a measurable set s, the volume of exp(s) equals
the integral of exp over s. -/
lemma volume_exp_image_eq_integral {s : Set ℝ} (hs : MeasurableSet s) :
    volume (Real.exp '' s) = ∫⁻ t in s, ENNReal.ofReal (Real.exp t) ∂volume := by
  -- Use the change of variables formula for one-dimensional functions
  -- The derivative of exp is exp, and exp is injective
  have hexp_deriv : ∀ x, HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp
  have hexp_deriv_within : ∀ x ∈ s, HasDerivWithinAt Real.exp (Real.exp x) s x := by
    intros x hx
    exact (hexp_deriv x).hasDerivWithinAt
  have hexp_inj : Set.InjOn Real.exp s := Real.exp_injective.injOn

  -- Apply the change of variables theorem
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul hs hexp_deriv_within hexp_inj (fun x => 1)

  -- Simplify the result
  simp only [Pi.one_apply, mul_one, lintegral_one, Measure.restrict_apply MeasurableSet.univ,
             Set.univ_inter] at h

  -- Now h : volume (exp '' s) = ∫⁻ x in s, ENNReal.ofReal |exp x|
  rw [h]

  -- Simplify: |exp x| = exp x since exp x > 0
  congr 1
  ext x
  rw [abs_of_pos (Real.exp_pos x)]

/-- Helper lemma: exp maps ℝ onto (0,∞) -/
lemma exp_surjective_onto_Ioi :
    Set.SurjOn Real.exp Set.univ (Set.Ioi (0 : ℝ)) := by
  intro x hx
  use Real.log x
  constructor
  · trivial
  · exact Real.exp_log hx

/-- Helper lemma: The image of a measurable set under exp is measurable -/
lemma measurableSet_exp_image {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet (Real.exp '' s) := by
  -- The exp function is continuous and injective, so by the Lusin-Souslin theorem,
  -- the image of a measurable set is measurable.
  apply MeasurableSet.image_of_continuousOn_injOn hs
  · exact Real.continuous_exp.continuousOn
  · exact Real.exp_injective.injOn

/-- Pushforward of Lebesgue measure on `(0,∞)` by `log` equals Lebesgue on `ℝ`
weighted by the density `exp`. Concretely:
`Measure.map Real.log (volume.restrict (Set.Ioi 0)) = volume.withDensity (fun t => ENNReal.ofReal (Real.exp t))`.
This is the change-of-variables formula for `x = exp t` at the level of measures. -/
lemma map_log_restrict_Ioi_eq_withDensity_exp :
    Measure.map Real.log (volume.restrict (Set.Ioi (0 : ℝ)))
      = volume.withDensity (fun t => ENNReal.ofReal (Real.exp t)) := by
  -- Use `Measure.ext` on measurable sets.
  refine Measure.ext (fun s hs => ?_)
  -- We need to show:
  -- (Measure.map Real.log (volume.restrict (Set.Ioi 0))) s =
  -- (volume.withDensity (fun t => ENNReal.ofReal (Real.exp t))) s

  -- Left side: map measure
  rw [Measure.map_apply Real.measurable_log hs]

  -- Right side: withDensity measure
  rw [withDensity_apply _ hs]

  -- Now we have:
  -- volume.restrict (Set.Ioi 0) (Real.log ⁻¹' s) =
  -- ∫⁻ t in s, ENNReal.ofReal (Real.exp t) ∂volume

  -- Simplify the restriction on the left
  rw [restrict_apply' measurableSet_Ioi]

  -- The preimage Real.log ⁻¹' s ∩ Set.Ioi 0 corresponds to
  -- {x > 0 : log x ∈ s} = {exp t : t ∈ s}

  -- Use change of variables: x = exp(t), dx = exp(t) dt
  -- volume {x > 0 : log x ∈ s} = ∫ 1_{s}(t) · exp(t) dt

  -- Key observation: Real.log ⁻¹' s ∩ Set.Ioi 0 = Real.exp '' s
  have h_preimage : Real.log ⁻¹' s ∩ Set.Ioi 0 = Real.exp '' s := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_image]
    constructor
    · intro ⟨hlog, hpos⟩
      use Real.log x
      constructor
      · exact hlog
      · exact Real.exp_log hpos
    · intro ⟨t, ht, hxt⟩
      rw [← hxt]
      constructor
      · simp [Real.log_exp, ht]
      · exact Real.exp_pos t

  rw [h_preimage]

  -- Now we need: volume (Real.exp '' s) = ∫⁻ t in s, ENNReal.ofReal (Real.exp t) ∂volume
  -- This is the image measure formula for the exponential function

  -- Apply our helper lemma for the volume of exp(s)
  exact volume_exp_image_eq_integral hs

/-- The pullback of functions from Hσ to L²(ℝ, pushforwardMeasure σ).
    This maps f : (0,∞) → ℂ to f ∘ exp : ℝ → ℂ -/
noncomputable def LogPull (σ : ℝ) (f : Hσ σ) : ℝ → ℂ :=
  fun t => if 0 < Real.exp t then Hσ.toFun f (Real.exp t) else 0

/-- Helper lemma: the weight function is measurable -/
lemma weight_measurable (σ : ℝ) :
    Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp ((2 * σ) * t))) := by
  apply Measurable.ennreal_ofReal
  exact Real.measurable_exp.comp (measurable_const.mul measurable_id)

/-- Helper lemma: LogPull preserves measurability -/
lemma LogPull_measurable (σ : ℝ) (f : Hσ σ) : Measurable (LogPull σ f) := by
  unfold LogPull
  -- The function is essentially f ∘ exp since exp t > 0 always
  simp only [Real.exp_pos, if_true]
  exact (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp

/-- Isometry identity for `Hσ`: a concrete norm formula.
This version exposes the `Hσ`-norm as an explicit weighted integral on `(0,∞)`.
It serves as the measurable backbone for the logarithmic substitution step in plan0. -/
theorem LogPull_isometry (σ : ℝ) (f : Hσ σ) :
    ‖f‖^2 = (∫⁻ x in Set.Ioi 0, ‖Hσ.toFun f x‖₊ ^ 2 *
      ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal := by
  simpa using (Hσ_norm_squared (σ := σ) f)

/-- The Mellin transform as Fourier transform after logarithmic substitution.
    For f ∈ Hσ, define Mellin[f](σ + iτ) = Fourier[LogPull f](τ)
    Note: This is a placeholder - full implementation requires proper L¹ theory -/
noncomputable def MellinTransformAt (σ : ℝ) (_f : Hσ σ) (_τ : ℝ) : ℂ :=
  -- Placeholder for now - requires Fourier transform setup
  0

/-- Uσ: The unitary map from Hσ to L²(ℝ) via Mellin transform
    This is the main isometry establishing Mellin-Plancherel -/
noncomputable def Uσ (σ : ℝ) : Hσ σ →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  -- Placeholder - will compose LogPull with normalized Fourier transform
  0

/-- Interim property for the current placeholder `Uσ`.
Since `Uσ` is currently the zero map, it is `0`-Lipschitz (nonexpansive with constant `0`).
This serves as a temporary, truthful contract until the isometric `Uσ` is implemented. -/
theorem Uσ_lipschitz_zero (σ : ℝ) : LipschitzWith 0 (Uσ σ) := by
  intro f g
  -- Both images are `0`, so the distance is `0`.
  simp [Uσ]

/-!
## Change of Variables Lemmas for Mellin-Plancherel

These lemmas establish the key change of variables formulas needed for the
logarithmic pullback map from L²(ℝ) to Hσ.
-/

/-- Change of variables formula: x = exp(t) for integration over (0,∞).
For a measurable function f and real α, we have:
∫₀^∞ f(log x) · x^α dx = ∫₋∞^∞ f(t) · exp((α + 1) · t) dt -/
lemma lintegral_change_of_variables_exp {α : ℝ} {f : ℝ → ENNReal}
    (hf : Measurable f) :
    ∫⁻ x in Set.Ioi 0, f (Real.log x) * ENNReal.ofReal (x ^ α) ∂(volume.restrict (Set.Ioi 0)) =
    ∫⁻ t, f t * ENNReal.ofReal (Real.exp (α * t + t)) ∂volume := by
  classical
  -- Step 1: express the left side via the pushforward of `volume.restrict (Ioi 0)` by `log`.
  -- The identity `Measure.map Real.log (volume.restrict (Ioi 0)) = volume.withDensity (ofReal ∘ exp)`
  -- is a standard change-of-variables fact. We leave it as a placeholder here.
  have h_push :
      Measure.map Real.log (volume.restrict (Set.Ioi (0 : ℝ)))
        = volume.withDensity (fun t => ENNReal.ofReal (Real.exp t)) := by
    simpa using map_log_restrict_Ioi_eq_withDensity_exp
  -- Measurability of the target integrand on ℝ
  have h_meas :
      Measurable fun t : ℝ => f t * ENNReal.ofReal (Real.exp (α * t)) := by
    have h1 : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (α * t)) := by
      have : Measurable fun t : ℝ => Real.exp (α * t) :=
        Real.measurable_exp.comp ((measurable_const.mul measurable_id))
      exact ENNReal.measurable_ofReal.comp this
    exact hf.mul h1
  -- Use the mapping property of lintegral under `map log` to pull `f ∘ log` back to ℝ.
  have h_map :
      ∫⁻ x in Set.Ioi 0, f (Real.log x) * ENNReal.ofReal (x ^ α) ∂(volume.restrict (Set.Ioi 0))
        = ∫⁻ t, (f t * ENNReal.ofReal (Real.exp (α * t)))
              ∂(Measure.map Real.log (volume.restrict (Set.Ioi 0))) := by
    -- We want to apply lintegral_map' but we need the right form
    have hlog : AEMeasurable Real.log (volume.restrict (Set.Ioi 0)) :=
      Real.measurable_log.aemeasurable

    have hA : AEMeasurable (fun t => f t * ENNReal.ofReal (Real.exp (α * t)))
        (Measure.map Real.log (volume.restrict (Set.Ioi 0))) :=
      h_meas.aemeasurable

    -- lintegral_map' gives: ∫ h d(map g μ) = ∫ h∘g dμ
    rw [MeasureTheory.lintegral_map' hA hlog]

    -- Now we need to show that (f t * exp(α*t)) ∘ log = f(log x) * x^α on (0,∞)
    -- Do this with an a.e. pointwise equality under the restricted measure.
    have h_ae :
        (fun x : ℝ => f (Real.log x) * ENNReal.ofReal (x ^ α))
          =ᵐ[volume.restrict (Set.Ioi 0)]
        (fun x : ℝ => f (Real.log x) * ENNReal.ofReal (Real.exp (α * Real.log x))) := by
      -- Reduce to a statement on the base measure with implication `x ∈ Ioi 0 → ...`.
      refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      intro hxpos
      -- Using the definition of real exponentiation via exponential and logarithm:
      -- for x > 0, x^α = exp (α * log x).
      have hxpos' : 0 < x := hxpos
      have hxexp : x ^ α = Real.exp (α * Real.log x) := by
        -- `Real.rpow_def_of_pos` gives x^α = exp (α * log x) for x > 0.
        simpa [Real.rpow_def_of_pos hxpos', mul_comm]
      simp [hxexp.symm]
    -- Apply the a.e. congruence.
    simpa using lintegral_congr_ae h_ae
  -- Substitute the pushforward identity and expand the withDensity on the right.
  calc
    ∫⁻ x in Set.Ioi 0, f (Real.log x) * ENNReal.ofReal (x ^ α)
        ∂(volume.restrict (Set.Ioi 0))
        = ∫⁻ t, (f t * ENNReal.ofReal (Real.exp (α * t)))
            ∂(Measure.map Real.log (volume.restrict (Set.Ioi 0))) := h_map
    _ = ∫⁻ t, (f t * ENNReal.ofReal (Real.exp (α * t)))
            ∂(volume.withDensity (fun t => ENNReal.ofReal (Real.exp t))) := by
          simpa [h_push]
    _ = ∫⁻ t, (f t * ENNReal.ofReal (Real.exp t)) * ENNReal.ofReal (Real.exp (α * t)) ∂volume := by
          -- expand withDensity: ∫ g d(μ.withDensity w) = ∫ g * w dμ
          -- with factors reordered to prepare for combining exponentials
          have hW : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp t)) :=
            ENNReal.measurable_ofReal.comp Real.measurable_exp
          have := lintegral_withDensity_eq_lintegral_mul
            (μ := volume) (f := fun t : ℝ => ENNReal.ofReal (Real.exp t))
            (h_mf := hW)
            (g := fun t : ℝ => f t * ENNReal.ofReal (Real.exp (α * t))) h_meas
          simpa [mul_comm, mul_left_comm, mul_assoc]
            using this
    _ = ∫⁻ t, f t * ENNReal.ofReal (Real.exp (α * t + t)) ∂volume := by
          -- combine exponentials: exp(α t) · exp(t) = exp(α t + t)
          refine lintegral_congr_ae ?_;
          refine Filter.Eventually.of_forall (fun t => ?_)
          have hpos1 : 0 ≤ Real.exp (α * t) := (Real.exp_pos _).le
          have hpos2 : 0 ≤ Real.exp t := (Real.exp_pos t).le
          simp only
          rw [mul_assoc, ← ENNReal.ofReal_mul hpos2]
          congr 1
          rw [mul_comm (Real.exp t), Real.exp_add]

/-- Special case for α = -1: ∫₀^∞ f(log x) · x⁻¹ dx = ∫₋∞^∞ f(t) dt -/
lemma lintegral_log_substitute {f : ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ x in Set.Ioi 0, f (Real.log x) * ENNReal.ofReal (x⁻¹) ∂(volume.restrict (Set.Ioi 0)) =
    ∫⁻ t, f t ∂volume := by
  -- When α = -1, we get exp((-1+1)·t) = exp(0) = 1
  convert lintegral_change_of_variables_exp (α := -1) hf using 2
  · congr 1
    ext x
    simp only [inv_eq_one_div, rpow_neg_one]
  · congr 1
    ext t
    -- We need to show: exp((-1) * t + t) = exp(0) = 1
    have : (-1 : ℝ) * t + t = 0 := by ring
    rw [this, Real.exp_zero, ENNReal.ofReal_one, mul_one]

/-- Relationship between mulHaar measure and volume with density 1/x -/
lemma mulHaar_eq_volume_div_x :
    mulHaar = volume.withDensity (fun x => ENNReal.ofReal (1 / x)) := by
  classical
  -- Unfold the definition from `MellinTransform.lean`.
  -- We show the restriction is redundant since the density vanishes on `(-∞,0]`.
  unfold mulHaar
  -- Let `w x = ofReal (1/x)` be the density.
  set w : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (1 / x) with hw
  -- First, prove that the withDensity measure of `(-∞,0]` is `0` since `w = 0` there.
  have h_zero_Iic : (volume.withDensity w) (Set.Iic (0 : ℝ)) = 0 := by
    have hmeas : MeasurableSet (Set.Iic (0 : ℝ)) := measurableSet_Iic
    -- Evaluate via `withDensity_apply` and pointwise vanishing of `w` on `(-∞,0]`.
    have h_ae_zero : (fun x => w x) =ᵐ[volume.restrict (Set.Iic (0 : ℝ))] 0 := by
      -- On `x ≤ 0`, we have `1/x ≤ 0`, hence `ofReal (1/x) = 0`.
      refine (ae_restrict_iff' hmeas).2 ?_
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      have hxle : x ≤ 0 := hx
      have hle : 1 / x ≤ 0 := by
        simpa [one_div] using inv_nonpos.mpr hxle
      simpa [hw, ENNReal.ofReal_eq_zero, one_div]
        using hle
    -- Turn a.e. zero into zero integral.
    have : ∫⁻ x in Set.Iic (0 : ℝ), w x ∂volume
        = ∫⁻ x in Set.Iic (0 : ℝ), 0 ∂volume := lintegral_congr_ae h_ae_zero
    simpa [withDensity_apply _ hmeas]
      using this.trans (by simp)
  -- Since the complement of `(0,∞)` has measure zero under `withDensity w`,
  -- the restriction to `(0,∞)` is equal to the original measure.
  have h_compl : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic (0 : ℝ) := by
    simpa using (Set.compl_Ioi (a := (0 : ℝ)))
  have h_restrict :
      (volume.withDensity w).restrict (Set.Ioi (0 : ℝ)) = volume.withDensity w := by
    -- Prove equality of measures by agreeing on all measurable sets.
    refine Measure.ext (fun t ht => ?_)
    -- By definition of `restrict`, rewrite to a statement about measures.
    -- Use the parameterized lemma `restrict_apply ht` to avoid expanding `withDensity`.
    rw [Measure.restrict_apply ht]
    have hzero : (volume.withDensity w) ((Set.Ioi (0 : ℝ))ᶜ) = 0 := by
      simpa [h_compl] using h_zero_Iic
    have hzero' : (volume.withDensity w) (t ∩ (Set.Ioi (0 : ℝ))ᶜ) = 0 := by
      -- Monotonicity from `t ∩ sᶜ ⊆ sᶜ`.
      have hsubset : t ∩ (Set.Ioi (0 : ℝ))ᶜ ⊆ (Set.Ioi (0 : ℝ))ᶜ := by
        intro x hx; exact And.right hx
      simpa using measure_mono_null hsubset hzero
    -- Rearrange the identity μ t = μ (t ∩ Ioi 0) + μ (t \ Ioi 0).
    -- Note that t \ Ioi 0 = t ∩ (Ioi 0)ᶜ by Set.diff_eq
    have : (volume.withDensity w) t = (volume.withDensity w) (t ∩ Set.Ioi 0) +
           (volume.withDensity w) (t \ Set.Ioi 0) := by
      rw [← measure_inter_add_diff t measurableSet_Ioi]
    -- Since t \ Ioi 0 = t ∩ (Ioi 0)ᶜ = t ∩ Iic 0, and this has measure 0
    rw [Set.diff_eq] at this
    -- Conclude using the zero mass of the complement part.
    -- First deduce μ t = μ (t ∩ Ioi 0), then flip sides to match the goal.
    -- Make the zero part match simp's normalization `(Ioi 0)ᶜ = Iic 0`.
    have hzero'' : (volume.withDensity w) (t ∩ Set.Iic 0) = 0 := by
      simpa [h_compl] using hzero'
    have h' : (volume.withDensity w) t = (volume.withDensity w) (t ∩ Set.Ioi 0) := by
      simpa [hzero'', add_comm] using this
    simpa using h'.symm
  -- Conclude by rewriting `mulHaar` and `w`.
  rw [hw] at h_restrict
  exact h_restrict

/-- For positive real x and real σ, the norm of x^(-σ) as a complex number equals x^(-σ) -/
lemma norm_cpow_real (x : ℝ) (σ : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ (-σ : ℂ)‖₊ = NNReal.rpow (Real.toNNReal x) (-σ) := by
  -- Prove equality by comparing real coercions on both sides.
  apply Subtype.ext
  -- Reduce to an equality in ℝ
  change ‖(x : ℂ) ^ (-σ : ℂ)‖ = ((NNReal.rpow (Real.toNNReal x) (-σ)) : ℝ)
  -- Left: use cpow = exp and |exp z| = exp(Re z), plus log of positive real.
  have h_left : ‖(x : ℂ) ^ (-σ : ℂ)‖ = Real.exp ((-σ) * Real.log x) := by
    -- (x:ℂ)^(a) = exp(a * log x) for x ≠ 0
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have hcpow' : (x : ℂ) ^ (-σ : ℂ)
        = Complex.exp (-(Complex.log (x : ℂ) * (σ : ℂ))) := by
      -- unfold cpow at nonzero base
      simpa [Complex.cpow_def, hx0]
    have : (x : ℂ) ^ (-σ : ℂ) = Complex.exp ((-σ : ℂ) * Complex.log (x : ℂ)) := by
      -- commute multiplication inside the negation
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcpow'
    -- log of positive real is real-valued
    have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := by
      exact (Complex.ofReal_log (le_of_lt hx)).symm
    -- First: relate the norm of the power to the norm of the exponential
    have hpow_to_exp : ‖(x : ℂ) ^ (-σ : ℂ)‖
        = ‖Complex.exp ((-σ : ℂ) * Complex.log (x : ℂ))‖ := by
      simpa using congrArg norm this
    -- Norm of exp z equals exp of the real part of z
    have hnorm_exp : ‖Complex.exp ((-σ : ℂ) * Complex.log (x : ℂ))‖
        = Real.exp (((-σ : ℂ) * Complex.log (x : ℂ)).re) := by
      simpa using Complex.norm_exp ((-σ : ℂ) * Complex.log (x : ℂ))
    -- simplify Re((−σ) * log x)
    have hre : (((-σ : ℂ) * Complex.log (x : ℂ)).re) = (-σ) * Real.log x := by
      -- both factors are real
      simp [hlog, Complex.ofReal_mul]
    -- Express the real part of the product and rewrite via re(log x) = Real.log x
    have hReMul : (((-σ : ℂ) * Complex.log (x : ℂ)).re)
        = - (σ * (Complex.log (x : ℂ)).re) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    have hre0 : (Complex.log (x : ℂ)).re = Real.log x := by
      simpa using Complex.log_ofReal_re x
    -- Chain the equalities
    have : ‖(x : ℂ) ^ (-σ : ℂ)‖ = Real.exp (-(σ * (Complex.log (x : ℂ)).re)) := by
      simpa [hReMul] using hpow_to_exp.trans hnorm_exp
    simpa [hre0] using this
  -- Right: coe of NNReal.rpow is the real rpow of the real coercion.
  have h_right : ((NNReal.rpow (Real.toNNReal x) (-σ)) : ℝ)
      = Real.rpow ((Real.toNNReal x : ℝ)) (-σ) := by
    -- known coercion lemma for NNReal.rpow
    simpa using (NNReal.coe_rpow (Real.toNNReal x) (-σ))
  -- Since x > 0, toNNReal x coerces to x and real rpow is exp(r * log x).
  have h_base : ((Real.toNNReal x : ℝ)) = x := by
    -- toNNReal x = max x 0, so for x > 0 this is x
    simp [Real.toNNReal, max_eq_left_of_lt hx]
  have : Real.rpow ((Real.toNNReal x : ℝ)) (-σ) = Real.exp ((-σ) * Real.log x) := by
    -- rpow on positives: x^y = exp(y * log x); commute to match ordering
    simpa [h_base, Real.rpow_def_of_pos hx, mul_comm]
  -- Rewrite the RHS target into (max x 0) ^ (-σ) and identify it with exp(…)
  have hrpow_max : (max x 0) ^ (-σ) = Real.exp (-(σ * Real.log x)) := by
    have hxmax : max x 0 = x := by simpa [max_eq_left_of_lt hx]
    simpa [hxmax, mul_comm] using (Real.rpow_def_of_pos hx (y := -σ))
  -- Finish by rewriting with hrpow_max
  simpa [hrpow_max] using h_left

/-! Small helper lemmas used in local algebraic cancellations -/

lemma coe_nnnorm_mul (a b : ℂ) :
    ((‖a * b‖₊ : ℝ≥0∞)) = ((‖a‖₊ : ℝ≥0∞) * (‖b‖₊ : ℝ≥0∞)) := by
  -- move to ℝ≥0, use `nnnorm_mul`, then coerce back to `ℝ≥0∞`
  change ((↑(‖a * b‖₊)) : ℝ≥0∞) = ((↑(‖a‖₊)) * (↑(‖b‖₊)) : ℝ≥0∞)
  have : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ := by simpa using (nnnorm_mul a b)
  simpa [this, ENNReal.coe_mul]

/-!
Auxiliary placeholder embedding from `L²(ℝ)` (Lebesgue) into `Hσ`.
In the present phase, this acts as the zero map to keep the API flowing.
It will be replaced by the genuine logarithmic pullback inverse in P3.
-/

lemma hwσ_meas_for_optimization (σ : ℝ) (wσ : ℝ → ℝ≥0∞)
    (hwσ : wσ = fun x ↦ ENNReal.ofReal (x ^ (2 * σ - 1))) : Measurable wσ := by
  rw [hwσ]
  measurability

lemma hx_cancel_for_optimization (σ x : ℝ) (hx' : 0 < x) (wσ : ℝ → ℝ≥0∞)
    (hwσ : wσ = fun x ↦ ENNReal.ofReal (x ^ (2 * σ - 1)))
    (hnorm₁ : (‖(x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ)‖₊ : ℝ≥0∞) = ENNReal.ofReal (x ^ (-(σ - 1/2)))) :
    (↑‖↑x ^ (2⁻¹ - ↑σ)‖₊ * (↑‖↑x ^ (2⁻¹ - ↑σ)‖₊ * wσ x)) = (1 : ℝ≥0∞) := by
  -- rewrite the nnnorm as ofReal of a real rpow
  have hpos : 0 ≤ x := le_of_lt hx'
  -- Note that -(σ - 1/2) = 1/2 - σ
  have h_exp_eq : x ^ (-(σ - 1/2)) = x ^ (1/2 - σ) := by
    congr 1
    ring
  -- 1/2 - σ = -(σ - 1/2); we will directly use `hnorm₁` in subsequent simp
  -- move to ofReal world and multiply inside
  have hA0 : 0 ≤ x ^ (1/2 - σ) := by
    rw [← h_exp_eq]
    exact Real.rpow_nonneg hpos (-(σ - 1/2))
  have hB0 : 0 ≤ x ^ (2 * σ - 1) := by simpa using Real.rpow_nonneg hpos (2 * σ - 1)
  -- combine the two identical factors into a square
  have :
      (ENNReal.ofReal (x ^ (1/2 - σ)) * ENNReal.ofReal (x ^ (1/2 - σ)))
        = ENNReal.ofReal ((x ^ (1/2 - σ)) * (x ^ (1/2 - σ))) := by
    simpa using (ENNReal.ofReal_mul (p := x ^ (1/2 - σ)) (q := x ^ (1/2 - σ)) hA0).symm
  -- now include the weight wσ x
  have :
      (ENNReal.ofReal (x ^ (1/2 - σ)) * ENNReal.ofReal (x ^ (1/2 - σ)) * ENNReal.ofReal (x ^ (2 * σ - 1)))
        = ENNReal.ofReal ((x ^ (1/2 - σ)) * (x ^ (1/2 - σ))) * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
    -- use `ofReal_mul` on the first two factors, then multiply both sides by the third
    have hpair := (ENNReal.ofReal_mul (p := x ^ (1/2 - σ)) (q := x ^ (1/2 - σ)) hA0).symm
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using congrArg (fun t => t * ENNReal.ofReal (x ^ (2 * σ - 1))) hpair
  -- pack all three ofReal factors into one
  have :
      ENNReal.ofReal ((x ^ (1/2 - σ)) * (x ^ (1/2 - σ))) * ENNReal.ofReal (x ^ (2 * σ - 1))
        = ENNReal.ofReal (((x ^ (1/2 - σ)) * (x ^ (1/2 - σ))) * (x ^ (2 * σ - 1))) := by
    have hnonneg : 0 ≤ (x ^ (1/2 - σ)) * (x ^ (1/2 - σ)) :=
      mul_nonneg hA0 hA0
    simpa using
      (ENNReal.ofReal_mul (p := ((x ^ (1/2 - σ)) * (x ^ (1/2 - σ)))) (q := x ^ (2 * σ - 1)) hnonneg).symm
  -- simplify exponents: (x^(1/2-σ))^2 * x^(2σ-1) = x^0 = 1
  -- first, rewrite the product of two identical rpow terms as a square,
  -- then convert the square into doubling the exponent via `Real.rpow_mul`.
  have hx0' : 0 ≤ x := le_of_lt hx'
  have hsquare : (x ^ (1/2 - σ)) ^ (2 : ℕ) = x ^ (2 * (1/2 - σ)) := by
    -- via rpow_mul: (x^a)^2 = x^(a*2)
    simpa [pow_two, mul_comm] using (Real.rpow_mul (x := x) (y := (1/2 - σ)) (z := (2 : ℝ)) hx0').symm
  have hsum : (2 * (1/2 - σ)) + (2 * σ - 1) = 0 := by ring
  -- conclude: the real product reduces to x^0 = 1
  have hxpos : 0 < x := hx'
  have hmul' : x ^ (1/2 - σ) * x ^ (1/2 - σ) * x ^ (2 * σ - 1)
      = x ^ (2 * (1/2 - σ)) * x ^ (2 * σ - 1) := by
    -- replace the first product by the doubled-exponent form using `hsquare`
    have hmulBase : x ^ (1/2 - σ) * x ^ (1/2 - σ) = x ^ (2 * (1/2 - σ)) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    rw [hmulBase]
  have hadd : x ^ (2 * (1/2 - σ)) * x ^ (2 * σ - 1)
      = x ^ (2 * (1/2 - σ) + (2 * σ - 1)) := by
    simpa using (Real.rpow_add hxpos (2 * (1/2 - σ)) (2 * σ - 1)).symm
  have : x ^ (1/2 - σ) * x ^ (1/2 - σ) * x ^ (2 * σ - 1)
      = x ^ (2 * (1/2 - σ) + (2 * σ - 1)) := by
    rw [hmul', hadd]
  -- now use the exponent sum equals 0
  have : x ^ (1/2 - σ) * x ^ (1/2 - σ) * x ^ (2 * σ - 1) = 1 := by
    rw [this, hsum, Real.rpow_zero]
  -- assemble
  -- turn lhs into ofReal of the triple product, then reduce to 1 by the above
  -- the earlier equalities justify the conversions
  -- Finally conclude the cancellation equality
  -- As we built equalities through `have` steps named `this`, `simp` will close it
  simp only [hnorm₁, h_exp_eq] at *
  -- We need to show ENNReal.ofReal (x ^ (σ * 2 - 1)) * (↑‖x ^ (2⁻¹ - σ)‖₊ * ↑‖x ^ (2⁻¹ - σ)‖₊) = 1
  -- We have this : x ^ (σ * 2 - 1) * (x ^ (2⁻¹ - σ) * x ^ (2⁻¹ - σ)) = 1
  -- Since x ^ (2⁻¹ - σ) is positive, its norm is itself
  have h_norm_eq : ‖x ^ (2⁻¹ - σ)‖ = x ^ (2⁻¹ - σ) := by
    rw [Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg hpos _)]
  -- Convert the norm to ENNReal
  have h_norm : (‖x ^ (2⁻¹ - σ)‖₊ : ℝ≥0∞) = ENNReal.ofReal (x ^ (2⁻¹ - σ)) := by
    have : (‖x ^ (2⁻¹ - σ)‖₊ : ℝ) = x ^ (2⁻¹ - σ) := by
      simp [h_norm_eq]
    rw [ENNReal.coe_nnreal_eq]
    simp [this, ENNReal.ofReal, Real.toNNReal, max_eq_left (Real.rpow_nonneg hpos _)]
  -- The goal is already in ENNReal.ofReal form, just expand wσ
  rw [hwσ]
  -- Combine the three ENNReal.ofReal factors into one in a structured way
  have h12 :
      ENNReal.ofReal (x ^ (2⁻¹ - σ)) * ENNReal.ofReal (x ^ (2⁻¹ - σ))
        = ENNReal.ofReal (x ^ (2⁻¹ - σ) * x ^ (2⁻¹ - σ)) := by
    -- use ofReal_mul for the first two factors
    have hA0' : 0 ≤ x ^ (2⁻¹ - σ) := by
      simpa using Real.rpow_nonneg hpos (2⁻¹ - σ)
    exact (ENNReal.ofReal_mul hA0').symm
  have hLHS_eq :
      ENNReal.ofReal (x ^ (2⁻¹ - σ)) * ENNReal.ofReal (x ^ (2⁻¹ - σ)) * ENNReal.ofReal (x ^ (2 * σ - 1))
        = ENNReal.ofReal (x ^ (2⁻¹ - σ) * x ^ (2⁻¹ - σ) * x ^ (2 * σ - 1)) := by
    -- multiply h12 by the third factor and combine again using ofReal_mul
    have hnonneg : 0 ≤ x ^ (2⁻¹ - σ) * x ^ (2⁻¹ - σ) := by
      have hx := Real.rpow_nonneg hpos (2⁻¹ - σ)
      exact mul_nonneg hx hx
    -- First rewrite the product of the first two factors
    have := congrArg (fun t => t * ENNReal.ofReal (x ^ (2 * σ - 1))) h12
    -- Then fold the remaining ofReal with the third factor
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using (this.trans
        ((ENNReal.ofReal_mul
          (p := x ^ (2⁻¹ - σ) * x ^ (2⁻¹ - σ)) (q := x ^ (2 * σ - 1)) hnonneg).symm))
  -- The real-level product equals 1, hence its ofReal is 1
  have h_half : (2⁻¹ : ℝ) = 1/2 := by norm_num
  have hprod_one : ENNReal.ofReal (x ^ (2⁻¹ - σ) * x ^ (2⁻¹ - σ) * x ^ (2 * σ - 1)) = 1 := by
    -- First, move through ofReal and close with ofReal_one
    have h' : ENNReal.ofReal (x ^ (1 / 2 - σ) * x ^ (1 / 2 - σ) * x ^ (2 * σ - 1)) = 1 := by
      simpa using (congrArg ENNReal.ofReal this).trans ENNReal.ofReal_one
    -- Then align exponents using a separate equality to avoid simp loops
    have hpow : x ^ (2⁻¹ - σ) = x ^ (1 / 2 - σ) := by
      -- rewrite the exponent using 2⁻¹ = 1/2 without invoking heavy simp
      have hexp : (2⁻¹ : ℝ) - σ = 1 / 2 - σ := by
        exact congrArg (fun t : ℝ => t - σ) h_half
      simpa [hexp]
    simpa [hpow] using h'
  -- Conclude by transporting equality through the two equalities above
  rw [h_norm]
  simpa [hwσ, mul_assoc] using hLHS_eq.trans hprod_one

lemma hg_meas_for_optimization (σ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ))
    (g : ℝ → ℂ) (hg_def : g = fun x =>
      if hx : 0 < x then
        ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ)
      else 0) :
    Measurable fun x => (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ) := by
  classical
  -- Rewrite `g` as an indicator of `Ioi 0` of a product of measurable functions
  have h_eq_ind :
      g = Set.indicator (Set.Ioi (0 : ℝ)) (fun x =>
        ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ)) := by
    funext x; by_cases hx : 0 < x
    · simp [hg_def, hx, Set.indicator_of_mem hx]
    · simp [hg_def, hx, Set.indicator_of_not_mem hx]
  -- Measurability of the inside function: (f ∘ log) · (x ↦ x^const)
  have h_f_log : Measurable fun x : ℝ => ((f : ℝ → ℂ) (Real.log x)) :=
    (Lp.stronglyMeasurable f).measurable.comp Real.measurable_log
  have h_cpow : Measurable fun x : ℝ => (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ) := by
    -- Keep this local use of `measurability` small and focused
    measurability
  have h_prod : Measurable fun x : ℝ =>
      ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ) :=
    h_f_log.mul h_cpow
  have hg_meas : Measurable g := by
    -- indicator over a measurable set preserves measurability
    simpa [h_eq_ind] using (h_prod.indicator measurableSet_Ioi)
  -- Compose with nnnorm and a fixed natural power
  have h_nnnorm : Measurable fun x => (‖g x‖₊ : ℝ≥0∞) := by
    -- Directly use measurability of `nnnorm` into `ℝ≥0∞`
    simpa using (hg_meas.nnnorm)
  -- Finally, raise to the power 2 (as a natural): preserves measurability
  simpa using (h_nnnorm.pow_const (2 : ℕ))

lemma expand_withDensity (g : ℝ → ℂ) (wσ : ℝ → ℝ≥0∞)
    (hg_meas : Measurable fun x => (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
    (hwσ_meas : Measurable wσ) :
    ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(mulHaar.withDensity wσ)
      = ∫⁻ x, ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x ∂mulHaar := by
  exact lintegral_withDensity_expand (g := fun x => ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)))
    (wσ := wσ) hg_meas hwσ_meas

/-- Map an `L²(ℝ)` function to an element of `Hσ`.
Implementation via logarithmic pullback: f(t) ↦ f(log x) with appropriate measure adjustment.
For f ∈ L²(ℝ), we define g(x) = f(log x) · x^(-σ) which lies in Hσ. -/
noncomputable def toHσ_ofL2 (σ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : Hσ σ := by
  classical
  -- Define the pullback: g(x) = 1_{x>0} · f(log x) · x^(-(σ - 1/2))
  -- The exponent choice x^(-(σ - 1/2)) ensures isometry under the Hσ-weight.
  let g : ℝ → ℂ := fun x =>
    if hx : 0 < x then
      ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ)
    else 0
  -- Target measure and weight
  set wσ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x ^ (2 * σ - 1)) with hwσ
  have hwσ_meas : Measurable wσ := hwσ_meas_for_optimization σ wσ hwσ
  -- Show g ∈ L²(μσ) where μσ = mulHaar.withDensity wσ
  have hg_memLp : MemLp g 2 (mulHaar.withDensity wσ) := by
    -- We compute the L²-lintegral and relate it to ‖f‖² via change of variables.
    -- Abbreviate the squared-ENorm integrand
    have hg_meas : Measurable fun x => (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ) :=
      hg_meas_for_optimization σ f g rfl
    -- Express the lintegral under withDensity as a product by wσ
    have h_expand_withDensity := expand_withDensity g wσ hg_meas hwσ_meas
    -- Expand mulHaar as set-integral over (0,∞) with density 1/x
    have h_expand_mulHaar :
        ∫⁻ x, ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x ∂mulHaar
          = ∫⁻ x in Set.Ioi 0,
              (((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x) * ENNReal.ofReal (1 / x) ∂volume := by
      simpa using lintegral_mulHaar_expand
        (g := fun x => ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x)
        (hg := ((hg_meas.mul hwσ_meas)))
    -- On (0,∞), unfold g and simplify the weight using weight_product_simplify
    have h_on_Ioi :
        ∫⁻ x in Set.Ioi 0,
            (((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x) * ENNReal.ofReal (1 / x) ∂volume
          = ∫⁻ x in Set.Ioi 0,
              ((‖((f : ℝ → ℂ) (Real.log x))‖₊ : ℝ≥0∞) ^ (2 : ℕ))
                * ENNReal.ofReal (1 / x) ∂volume := by
      -- Reduce to a.e. equality on Ioi 0
      refine lintegral_congr_ae ?_;
      refine ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      -- On x>0: g x = f(log x) * x^(-(σ-1/2)); its norm-square times the Hσ-weight collapses with 1/x
      have hx' : 0 < x := hx
      have hx'' := weight_product_simplify (σ := σ) x hx
      -- Use that ‖a * b‖ = ‖a‖ * ‖b‖ and ‖x^(−(σ-1/2))‖² · x^(2σ-1) = x
      -- so after multiplying by ofReal(1/x), only the factor 1/x remains.
      -- We discharge equalities via `simp` and `ring`-style arithmetic encoded in prior lemmas.
      have hx_id :
          (((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x) * ENNReal.ofReal (1 / x)
            = ((‖((f : ℝ → ℂ) (Real.log x))‖₊ : ℝ≥0∞) ^ (2 : ℕ))
                * ENNReal.ofReal (1 / x) := by
        -- Unfold g at x>0 and rewrite weights
        have hxg : g x = ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ) := by
          simp [g, hx']
        have hwx : (wσ x) * ENNReal.ofReal (1 / x) = ENNReal.ofReal (x ^ (2 * σ - 1) / x) := by
          simpa [wσ, hwσ, mul_comm] using hx''
        -- Reshuffle and reduce to cancelling the cpow factor with the weight
        simp [hxg, hwx, mul_comm, mul_left_comm, mul_assoc]
        -- Bring out the product inside the squared nnnorm
        have hsplit :
            ((‖((f : ℝ → ℂ) (Real.log x) * (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ))‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              = (((‖((f : ℝ → ℂ) (Real.log x))‖₊ : ℝ≥0∞) *
                  (‖(x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ)‖₊ : ℝ≥0∞)) ^ (2 : ℕ)) := by
          simpa [coe_nnnorm_mul]
        -- Use exponent arithmetic to match x^(2σ-1) with (x^(σ-1/2))^2
        have h_exp : x ^ (2 * σ - 1) = x ^ (2 * (σ - 1/2)) := by
          congr 1; ring
        have h_exp_comm : x ^ (σ * 2 - 1) = x ^ (2 * σ - 1) := by
          have : (σ * 2 - 1 : ℝ) = 2 * σ - 1 := by ring
          simpa using congrArg (fun t : ℝ => x ^ t) this
        have hx0 : 0 ≤ x := le_of_lt hx'
        have h_combine : x ^ (2 * (σ - 1/2)) = (x ^ (σ - 1/2)) ^ 2 := by
          simpa [mul_comm] using (Real.rpow_mul (x := x) (y := (σ - 1/2)) (z := (2 : ℝ)) hx0)
        -- Finish: cancel the cpow factor squared with the weight squared to 1
        -- Convert the cpow nnnorm to a real rpow via the prepared lemma
        have hnorm₁ : (‖(x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ)‖₊ : ℝ≥0∞)
            = ENNReal.ofReal (x ^ (-(σ - 1/2))) := by
          have hnn : ‖(x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ)‖₊
              = NNReal.rpow (Real.toNNReal x) (-(σ - 1/2)) := by
            simpa using norm_cpow_real x (σ - 1/2) hx'
          -- move to real values via coercion to ℝ and then lift with ofReal
          have : ENNReal.ofReal ((‖(x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ)‖₊ : NNReal) : ℝ)
                = ENNReal.ofReal ((Real.toNNReal x : ℝ) ^ (-(σ - 1/2))) := by
            have := congrArg (fun r : NNReal => (r : ℝ)) hnn
            simpa [NNReal.coe_rpow] using congrArg ENNReal.ofReal this
          have hx_to : ((Real.toNNReal x : ℝ)) = x := by
            simp [Real.toNNReal, max_eq_left_of_lt hx']
          simpa [hx_to] using this
        -- Put all exponent identities together and cancel
        -- Rearrange to isolate ((‖x^(1/2-σ)‖₊)^2) * wσ x
        have hx_cancel :
            (↑‖↑x ^ (2⁻¹ - ↑σ)‖₊ * (↑‖↑x ^ (2⁻¹ - ↑σ)‖₊ * wσ x)) = (1 : ℝ≥0∞) :=
          hx_cancel_for_optimization σ x hx' wσ hwσ hnorm₁
        -- Now use the cancellation inside the big product and finish
        -- target has a common left factor ENNReal.ofReal x⁻¹; after cancellation we match RHS
        -- Define A := ‖x^(1/2-σ)‖₊ and B := ‖f(log x)‖₊ * ‖f(log x)‖₊ in ℝ≥0∞
        set A : ℝ≥0∞ := ((‖(x : ℂ) ^ ((2⁻¹ - σ) : ℂ)‖₊ : ℝ≥0∞)) with hA
        set B : ℝ≥0∞ := ((‖(f : ℝ → ℂ) (Real.log x)‖₊ : ℝ≥0∞) * (‖(f : ℝ → ℂ) (Real.log x)‖₊ : ℝ≥0∞)) with hB
        have hx_cancel' : wσ x * (A * A * B) = B := by
          -- Rearrange the cancellation equation
          calc wσ x * (A * A * B) = (wσ x * A * A) * B := by ring
            _ = (A * (A * wσ x)) * B := by ring
            _ = 1 * B := by
              have h1 : A * (A * wσ x) = 1 := by
                rw [hA]
                have : (‖(x : ℂ) ^ ((2⁻¹ - σ) : ℂ)‖₊ : ℝ≥0∞) = (‖x ^ (2⁻¹ - σ)‖₊ : ℝ≥0∞) := by
                  -- We need to show the complex power norm equals the real power norm
                  -- First show the norms are equal as real numbers
                  have h_norm : ‖(x : ℂ) ^ ((2⁻¹ - σ) : ℂ)‖ = ‖x ^ (2⁻¹ - σ)‖ := by
                    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx']
                    -- After norm_cpow_eq_rpow_re_of_pos, the goal is x ^ (2⁻¹ - ↑σ).re = ‖x ^ (2⁻¹ - σ)‖
                    -- Note that (2⁻¹ - ↑σ).re = 2⁻¹ - σ
                    have : (2⁻¹ - (σ : ℂ)).re = 2⁻¹ - σ := by simp [Complex.sub_re, Complex.ofReal_re]
                    rw [this, Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg hx0 _)]
                  -- Convert to nnnorm equality
                  have h_nnnorm : ‖(x : ℂ) ^ ((2⁻¹ - σ) : ℂ)‖₊ = ‖x ^ (2⁻¹ - σ)‖₊ := by
                    ext
                    exact h_norm
                  -- Finally convert to ENNReal
                  simp only [h_nnnorm]
                rw [this]
                exact hx_cancel
              calc A * (A * wσ x) * B = (A * (A * wσ x)) * B := by ring
                _ = 1 * B := by rw [h1]
            _ = B := by rw [one_mul]
        -- Apply to get the desired form
        have h_eq : ENNReal.ofReal x⁻¹ * (wσ x * (A * A * B)) = ENNReal.ofReal x⁻¹ * B := by
          rw [hx_cancel']
        -- Now we need to convert to the squared form
        have : ENNReal.ofReal x⁻¹ * (wσ x * (A * ‖(f : ℝ → ℂ) (Real.log x)‖₊) ^ 2) =
               ENNReal.ofReal x⁻¹ * ‖(f : ℝ → ℂ) (Real.log x)‖₊ ^ 2 := by
          simp only [pow_two, hA, hB] at h_eq ⊢
          convert h_eq using 2
          ring
        exact this
      exact hx_id
    -- Change variables x = exp t with α = -1 to get the L² integral of f
    have h_change :
        ∫⁻ x in Set.Ioi 0,
            ((‖((f : ℝ → ℂ) (Real.log x))‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              * ENNReal.ofReal (1 / x) ∂volume
          = ∫⁻ t, ((‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume := by
      -- Apply the ready-made α = -1 change-of-variables lemma
      -- with f := fun t => ‖f t‖₊ ^ 2
      have hf_meas : Measurable fun t => ((‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
        -- f is strongly measurable in L², hence measurable; build up the norm^2
        have hsm : StronglyMeasurable (fun t => ((f : ℝ → ℂ) t)) := Lp.stronglyMeasurable f
        have hm : Measurable (fun t => ((f : ℝ → ℂ) t)) := hsm.measurable
        have hn : Measurable fun t => ‖((f : ℝ → ℂ) t)‖ := hm.norm
        simpa using ((ENNReal.measurable_ofReal.comp hn).pow_const (2 : ℕ))
      simpa [one_div] using
        (lintegral_log_substitute (f := fun t => ((‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ))) hf_meas)
    -- Put the pieces together: the L²-lintegral for g under μσ equals that for f under volume,
    -- hence finiteness transfers; then build MemLp by definition.
    -- Equality of squared-norm integrals
    have hint_eq :
        (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(mulHaar.withDensity wσ))
          = ∫⁻ t, ((‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume :=
      calc
        (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(mulHaar.withDensity wσ))
            = ∫⁻ x, ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x ∂mulHaar := h_expand_withDensity
        _ = ∫⁻ x in Set.Ioi 0,
              (((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x)
                * ENNReal.ofReal (1 / x) ∂volume := h_expand_mulHaar
        _ = ∫⁻ x in Set.Ioi 0,
              ((‖((f : ℝ → ℂ) (Real.log x))‖₊ : ℝ≥0∞) ^ (2 : ℕ))
                * ENNReal.ofReal (1 / x) ∂volume := h_on_Ioi
        _ = ∫⁻ t, ((‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume := h_change
    -- Finiteness on the right-hand side because f ∈ L²(volume)
    have hf_mem : MemLp (fun t => ((f : ℝ → ℂ) t)) 2 (volume : Measure ℝ) := Lp.memLp f
    -- Convert eLpNorm finiteness at p=2 into finiteness of the squared-norm lintegral
    have hf_fin : (∫⁻ t, ((‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) < ∞ := by
      -- rewrite the integrand via ofReal of the real norm to match the eLpNorm definition
      have hrepr :
          (fun t => ((‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ)))
            = (fun t => (ENNReal.ofReal ‖((f : ℝ → ℂ) t)‖) ^ (2 : ℕ)) := by
        funext t
        -- ‖f t‖₊ is the nonnegative norm, and its coercion to ENNReal equals ofReal of the norm
        -- Note that ‖f t‖₊ = Real.toNNReal ‖f t‖ by definition
        -- and (↑(Real.toNNReal x) : ℝ≥0∞) = ENNReal.ofReal x for x ≥ 0
        have : (‖(f : ℝ → ℂ) t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖(f : ℝ → ℂ) t‖ := by
          rw [← enorm_eq_nnnorm]
          rw [ofReal_norm]
        rw [this]
      -- hf_mem.2 gives us eLpNorm f 2 volume < ∞
      have h1 : eLpNorm (fun t => (f : ℝ → ℂ) t) 2 volume < ∞ := hf_mem.2
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] at h1
      simp only [ENNReal.toReal_ofNat] at h1
      -- The eLpNorm is (∫⁻ t, ‖f t‖ₑ ^ 2) ^ (1/2)
      -- We want ∫⁻ t, ‖f t‖ₑ ^ 2 < ∞
      -- First fix the type: 1/2 = 2⁻¹
      have h1' : (∫⁻ t, ‖(f : ℝ → ℂ) t‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) < ∞ := by
        have : (1 / (2 : ℝ)) = ((2 : ℝ)⁻¹) := by norm_num
        rw [← this]
        exact h1
      have h3 : (∫⁻ t, ‖(f : ℝ → ℂ) t‖ₑ ^ (2 : ℝ)) < ∞ := by
        by_contra hn
        simp only [not_lt, top_le_iff] at hn
        rw [hn] at h1'
        simp at h1'
      -- Convert the exponent from ℝ to ℕ and norm forms
      have h4 : (∫⁻ t, ((‖(f : ℝ → ℂ) t‖₊ : ℝ≥0∞) ^ (2 : ℕ))) < ∞ := by
        have : (∫⁻ t, ‖(f : ℝ → ℂ) t‖ₑ ^ (2 : ℝ)) = (∫⁻ t, ‖(f : ℝ → ℂ) t‖ₑ ^ (2 : ℕ)) := by
          congr 1
          funext t
          norm_cast
        rw [this] at h3
        have : (∫⁻ t, ‖(f : ℝ → ℂ) t‖ₑ ^ (2 : ℕ)) = (∫⁻ t, ((‖(f : ℝ → ℂ) t‖₊ : ℝ≥0∞) ^ (2 : ℕ))) := by
          simp only [enorm_eq_nnnorm]
        rw [← this]
        exact h3
      exact h4
    -- Transfer finiteness to the left-hand side via the equality
    have hg_int_fin :
        (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(mulHaar.withDensity wσ)) < ∞ := by
      simpa [hint_eq]
        using hf_fin
    -- Almost everywhere strongly measurable: build measurability of g, then upgrade
    have hg_measurable : Measurable g := by
      -- As in `hg_meas`, `g` is an indicator over `Ioi 0` of a product of measurables
      have h_eq_ind :
          g = Set.indicator (Set.Ioi (0 : ℝ)) (fun x =>
            ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ)) := by
        funext x; by_cases hx : 0 < x
        · simp [g, hx, Set.indicator_of_mem hx]
        · simp [g, hx, Set.indicator_of_not_mem hx]
      have h_f_log : Measurable fun x : ℝ => ((f : ℝ → ℂ) (Real.log x)) :=
        (Lp.stronglyMeasurable f).measurable.comp Real.measurable_log
      have h_cpow : Measurable fun x : ℝ => (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ) := by
        measurability
      have h_prod : Measurable fun x : ℝ =>
          ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1/2 : ℝ)) : ℂ) :=
        h_f_log.mul h_cpow
      simpa [h_eq_ind] using (h_prod.indicator measurableSet_Ioi)
    have hg_aes : AEStronglyMeasurable g (mulHaar.withDensity wσ) :=
      hg_measurable.aestronglyMeasurable
    -- Package MemLp directly by definition (p = 2)
    exact And.intro hg_aes (by
      -- Rewrite eLpNorm at p=2 on both sides and use the equality of integrals.
      -- Unfold both eLpNorm variants at p=2 to the same powered integral
      have hrepr_g' :
          eLpNorm' g 2 (mulHaar.withDensity wσ)
            = ((∫⁻ x, ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(mulHaar.withDensity wσ)) ^ (1 / (2 : ℝ))) := by
        -- Pointwise equality of integrands
        have hrepr :
            (fun x => (‖g x‖ₑ : ℝ≥0∞) ^ (2 : ℕ))
              = (fun x => ((↑‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ))) := by
          funext x
          have hx : (‖g x‖ₑ : ℝ≥0∞) = (↑‖g x‖₊ : ℝ≥0∞) := rfl
          simpa [hx]
        -- Lift to equality of lintegrals and take the 1/2 power
        have hrepr_int :
            (∫⁻ x, (ENNReal.ofReal ‖g x‖) ^ (2 : ℕ) ∂(mulHaar.withDensity wσ))
              = ∫⁻ x, ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(mulHaar.withDensity wσ) := by
          simpa using congrArg (fun φ => ∫⁻ x, φ x ∂(mulHaar.withDensity wσ)) hrepr
        simpa [eLpNorm', one_div] using congrArg (fun t => t ^ (1 / (2 : ℝ))) hrepr_int
      -- Also record the same equality for `eLpNorm` (not the primed variant)
      have hrepr_g'' :
          eLpNorm g 2 (mulHaar.withDensity wσ)
            = ((∫⁻ x, ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(mulHaar.withDensity wσ)) ^ (1 / (2 : ℝ))) := by
        -- Replace the ofReal-based integrand by the nnnorm-based one inside `eLpNorm`
        have hrepr_int :
            (∫⁻ x, (ENNReal.ofReal ‖g x‖) ^ (2 : ℕ) ∂(mulHaar.withDensity wσ))
              = ∫⁻ x, ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(mulHaar.withDensity wσ) := by
          -- pointwise equality of integrands
          have :
              (fun x => (ENNReal.ofReal ‖g x‖) ^ (2 : ℕ))
                = (fun x => ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ))) := by
            funext x
            -- By definition, ‖·‖ₑ = (↑‖·‖₊ : ℝ≥0∞)
            have hx : (‖g x‖ₑ : ℝ≥0∞) = (↑‖g x‖₊ : ℝ≥0∞) := rfl
            simpa [hx]
          simpa using congrArg (fun φ => ∫⁻ x, φ x ∂(mulHaar.withDensity wσ)) this
        -- eLpNorm for p = 2 is defined differently
        rw [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
        simp only [ENNReal.toReal_ofNat, eLpNorm']
        -- Note that ‖g a‖ₑ = ↑‖g a‖₊ by definition
        congr 1
        congr 1
        funext x
        -- Both sides are equal since ‖g x‖ₑ = ↑‖g x‖₊
        -- The exponent types differ (ℝ vs ℕ), but the values are the same
        have : (‖g x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) = (‖g x‖ₑ : ℝ≥0∞) ^ (2 : ℕ) := by
          norm_cast
        rw [this]
        rfl
      -- Synchronize the two equivalent integrand forms for f
      have hrepr_f_norm :
          (∫⁻ (a : ℝ), (‖((f : ℝ → ℂ) a)‖ₑ : ℝ≥0∞) ^ (2 : ℕ) ∂volume) ^ ((2 : ℝ)⁻¹)
            = ((∫⁻ (t : ℝ), ((↑‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) ^ ((2 : ℝ)⁻¹)) := by
        -- pointwise equality of integrands
        have hp :
            (fun t => ((‖((f : ℝ → ℂ) t)‖ₑ : ℝ≥0∞) ^ (2 : ℕ)))
              = (fun t => (((↑‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞)) ^ (2 : ℕ))) := by
          funext t
          have : ((‖((f : ℝ → ℂ) t)‖ₑ : ℝ≥0∞)) = (↑‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) := rfl
          simpa [this]
        -- integrate both sides and raise to the same power
        have hi :
            (∫⁻ t, ((‖((f : ℝ → ℂ) t)‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
              = (∫⁻ t, (((↑‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞)) ^ (2 : ℕ)) ∂volume) := by
          simpa using congrArg (fun φ => ∫⁻ x, φ x ∂(volume : Measure ℝ)) hp
        simpa using congrArg (fun s => s ^ ((2 : ℝ)⁻¹)) hi
      have hf' :
          ((∫⁻ t, ((‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) ^ (1 / (2 : ℝ))) < ∞ := by
        -- hf_mem.2 gives us eLpNorm f 2 volume < ∞
        -- eLpNorm f 2 = (∫⁻ t, ‖f t‖ₑ ^ 2) ^ (1/2) for p = 2
        have h1 : eLpNorm (fun t => (f : ℝ → ℂ) t) 2 volume < ∞ := hf_mem.2
        rw [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] at h1
        simp only [ENNReal.toReal_ofNat, eLpNorm', one_div] at h1
        -- Now we need to show the integrands are the same
        have : (∫⁻ t, ‖(f : ℝ → ℂ) t‖ₑ ^ (2 : ℝ)) = (∫⁻ t, ((‖((f : ℝ → ℂ) t)‖₊ : ℝ≥0∞) ^ (2 : ℕ))) := by
          congr 1
          funext t
          have : (‖(f : ℝ → ℂ) t‖ₑ : ℝ≥0∞) ^ (2 : ℝ) = (‖(f : ℝ → ℂ) t‖ₑ : ℝ≥0∞) ^ (2 : ℕ) := by norm_cast
          rw [this]
          rfl
        rw [this] at h1
        -- Convert 2⁻¹ to 1/2
        have : ((2 : ℝ)⁻¹) = (1 / (2 : ℝ)) := by norm_num
        rw [← this]
        exact h1
      -- Use the equality of integrals to transport finiteness from f-side to g-side
      simpa [hrepr_g'', hint_eq] using hf'
    )
  -- Package as an Lp element over μσ
  exact MemLp.toLp g hg_memLp

end MellinIsometry

end Frourio
