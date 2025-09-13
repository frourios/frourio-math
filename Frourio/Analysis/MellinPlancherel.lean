import Frourio.Analysis.MellinTransform
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
    -- measurability
    simpa [wσ] using (by
      -- measurability
      have h : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) := by
        -- measurability
        measurability
      exact h)
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

end Frourio
