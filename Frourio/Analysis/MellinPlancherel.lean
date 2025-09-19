import Frourio.Analysis.MellinBasic
import Frourio.Analysis.MellinTransform
import Frourio.Analysis.MellinPlancherelCore
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

namespace Complex

@[simp] lemma norm_ofReal (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  simp

@[simp] lemma ennreal_norm_eq (z : ℂ) : (‖z‖ₑ : ℝ≥0∞) = (‖z‖₊ : ℝ≥0∞) := rfl

@[simp] lemma ennreal_norm_mul_self (z : ℂ) :
    ‖z‖ₑ * ‖z‖ₑ = (‖z‖₊ : ℝ≥0∞) * (‖z‖₊ : ℝ≥0∞) := by
  simp [ennreal_norm_eq]

end Complex

namespace Frourio

section MellinPlancherelTheorems
/-!
## Core Mellin-Plancherel Theorems

This section contains the fundamental theorems of Mellin-Plancherel theory
that establish Uσ as an isometry between Hσ and L²(ℝ).
-/

/-- Logarithmic pullback from `Hσ` to unweighted `L²(ℝ)`.
    We transport along `x = exp t` and incorporate the Jacobian/weight factor
    so that `‖LogPull σ f‖_{L²(ℝ)} = ‖f‖_{Hσ}`. Explicitly,
    `(LogPull σ f)(t) = e^{(σ - 1/2) t} · f(e^t)`. -/
noncomputable def LogPull (σ : ℝ) (f : Hσ σ) : ℝ → ℂ :=
  fun t => (Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ) * Hσ.toFun f (Real.exp t)

@[simp] lemma LogPull_apply (σ : ℝ) (f : Hσ σ) (t : ℝ) :
    LogPull σ f t
      = (Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ) * Hσ.toFun f (Real.exp t) := rfl

/-- Helper lemma: the weight function is measurable -/
lemma weight_measurable (σ : ℝ) :
    Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp ((2 * σ) * t))) := by
  apply Measurable.ennreal_ofReal
  exact Real.measurable_exp.comp (measurable_const.mul measurable_id)

/-- Helper lemma: LogPull preserves measurability -/
lemma LogPull_measurable (σ : ℝ) (f : Hσ σ) : Measurable (LogPull σ f) := by
  refine (Complex.measurable_ofReal.comp ?_).mul ?_
  · -- measurability of the exponential weight `t ↦ e^{(σ-1/2)t}`
    have h_linear : Measurable fun t : ℝ => (σ - (1 / 2 : ℝ)) * t :=
      (measurable_const.mul measurable_id)
    exact Real.measurable_exp.comp h_linear
  · -- measurability of `t ↦ f (exp t)`
    exact (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp

lemma LogPull_norm_sq (σ : ℝ) (f : Hσ σ) (t : ℝ) :
    ‖LogPull σ f t‖^2
      = Real.exp ((2 * σ - 1) * t) * ‖Hσ.toFun f (Real.exp t)‖^2 := by
  classical
  set a := Real.exp ((σ - (1 / 2 : ℝ)) * t) with ha
  have ha_nonneg : 0 ≤ a := by simpa [ha] using (Real.exp_pos _).le
  have hnorm_mul :
      ‖LogPull σ f t‖ = ‖(a : ℂ)‖ * ‖Hσ.toFun f (Real.exp t)‖ := by
    rw [LogPull_apply]
    rw [ha]
    exact Complex.norm_mul ((a : ℂ)) (Hσ.toFun f (Real.exp t))
  have hnorm : ‖LogPull σ f t‖ = a * ‖Hσ.toFun f (Real.exp t)‖ := by
    have hnorm_a : ‖(a : ℂ)‖ = a := by
      simp [abs_of_nonneg ha_nonneg]
    rw [hnorm_mul, hnorm_a]
  have hsq := congrArg (fun r : ℝ => r ^ 2) hnorm
  have hmul :
      (a * ‖Hσ.toFun f (Real.exp t)‖) ^ 2
        = a ^ 2 * ‖Hσ.toFun f (Real.exp t)‖ ^ 2 := by
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hpow : a ^ 2 = Real.exp ((2 * σ - 1) * t) := by
    have hsum :
        ((σ - (1 / 2 : ℝ)) * t) + ((σ - (1 / 2 : ℝ)) * t)
          = (2 * σ - 1) * t := by ring
    calc
      a ^ 2 = Real.exp ((σ - (1 / 2 : ℝ)) * t) * Real.exp ((σ - (1 / 2 : ℝ)) * t) := by
        simp [ha, pow_two]
      _ = Real.exp (((σ - (1 / 2 : ℝ)) * t) + ((σ - (1 / 2 : ℝ)) * t)) := by
        simpa [mul_comm]
          using
            (Real.exp_add ((σ - (1 / 2 : ℝ)) * t) ((σ - (1 / 2 : ℝ)) * t)).symm
      _ = Real.exp ((2 * σ - 1) * t) := by rw [hsum]
  have hsq' : ‖LogPull σ f t‖ ^ 2
      = a ^ 2 * ‖Hσ.toFun f (Real.exp t)‖ ^ 2 := by
    simpa [hmul] using hsq
  simpa [hpow] using hsq'

lemma LogPull_integrand_eq (σ : ℝ) (f : Hσ σ) (t : ℝ) :
    (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
      = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
          * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t)) := by
  have hnorm_sq := LogPull_norm_sq (σ := σ) (f := f) t
  have hpos_f : 0 ≤ ‖Hσ.toFun f (Real.exp t)‖^2 := by exact sq_nonneg _
  have hpos_exp : 0 ≤ Real.exp ((2 * σ - 1) * t) := (Real.exp_pos _).le
  have hpow :
      (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
        = ENNReal.ofReal (‖LogPull σ f t‖^2) := by
    -- Convert nnnorm to ENNReal.ofReal
    have h1 : (‖LogPull σ f t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖LogPull σ f t‖ := by
      simp only [nnnorm]
      conv_lhs => arg 1; rw [← Real.toNNReal_of_nonneg (norm_nonneg _)]
      simp only [ENNReal.ofReal]
    rw [h1]
    rw [(ENNReal.ofReal_pow (norm_nonneg _) 2).symm]
  have hsplit := congrArg ENNReal.ofReal hnorm_sq
  calc
      (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
          = ENNReal.ofReal (‖LogPull σ f t‖^2) := hpow
      _ = ENNReal.ofReal
            (Real.exp ((2 * σ - 1) * t) * ‖Hσ.toFun f (Real.exp t)‖^2) := hsplit
      _ = ENNReal.ofReal (Real.exp ((2 * σ - 1) * t))
            * ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2) := by
          exact ENNReal.ofReal_mul hpos_exp
      _ = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
            * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t)) := by
          rw [mul_comm]

/-- Isometry identity for `Hσ`: a concrete norm formula.
This version exposes the `Hσ`-norm as an explicit weighted integral on `(0,∞)`.
It serves as the measurable backbone for the logarithmic substitution step in plan0. -/
theorem LogPull_isometry (σ : ℝ) (f : Hσ σ) :
    ‖f‖^2 = (∫⁻ x in Set.Ioi 0, ‖Hσ.toFun f x‖₊ ^ 2 *
      ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal := by
  simpa using (Hσ_norm_squared (σ := σ) f)

-- LogPull is now imported from MellinPlancherelAdvance

private lemma LogPull_sq_integral_eq (σ : ℝ) (f : Hσ σ) :
    ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure ℝ)
      = ∫⁻ x in Set.Ioi (0 : ℝ),
          (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
            * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂(volume : Measure ℝ) := by
  classical
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
  have hg_meas : Measurable g := by
    have h_comp : Measurable fun t : ℝ => Hσ.toFun f (Real.exp t) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_norm : Measurable fun t : ℝ => ‖Hσ.toFun f (Real.exp t)‖ :=
      h_comp.norm
    have h_sq : Measurable fun t : ℝ => ‖Hσ.toFun f (Real.exp t)‖^2 := by
      simpa [pow_two] using h_norm.mul h_norm
    exact (Measurable.ennreal_ofReal h_sq)
  have h_pointwise :
      (fun t => (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ))
        =ᵐ[volume]
        fun t => g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h_logpull := LogPull_integrand_eq (σ := σ) (f := f) t
    have h_exp :
        ENNReal.ofReal (Real.exp ((2 * σ - 1) * t))
          = ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) := by
      have : (2 * σ - 1) * t = (2 * σ - 2) * t + t := by ring
      simp [this]
    calc
      (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
          = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
              * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t)) := h_logpull
      _ = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
              * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) := by
                simp [h_exp]
      _ = g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) := by
                simp [g]
  have h_lhs :
      ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) ∂volume :=
    lintegral_congr_ae h_pointwise
  have h_change_restrict :=
      lintegral_change_of_variables_exp (α := 2 * σ - 2) (f := g) hg_meas
  have h_rhs_restrict :
      ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 2))
            ∂(volume.restrict (Set.Ioi 0))
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 1) / x)
            ∂(volume.restrict (Set.Ioi 0)) := by
    refine lintegral_congr_ae ?_
    refine ((ae_restrict_iff' measurableSet_Ioi).2 ?_)
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hxpos : 0 < x := hx
    have hx_ne : x ≠ 0 := ne_of_gt hxpos
    have hpow_mul : x ^ (2 * σ - 1) = x ^ (2 * σ - 2) * x := by
      have : 2 * σ - 1 = (2 * σ - 2) + 1 := by ring
      simp [this, Real.rpow_add hxpos, Real.rpow_one]
    have hpow_div : ENNReal.ofReal (x ^ (2 * σ - 2))
        = ENNReal.ofReal (x ^ (2 * σ - 1) / x) := by
      have hdiv : x ^ (2 * σ - 1) / x = x ^ (2 * σ - 2) := by
        calc
          x ^ (2 * σ - 1) / x
              = (x ^ (2 * σ - 1)) * x⁻¹ := by simp [div_eq_mul_inv]
          _ = (x ^ (2 * σ - 2) * x) * x⁻¹ := by simp [hpow_mul]
          _ = x ^ (2 * σ - 2) * (x * x⁻¹) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
          _ = x ^ (2 * σ - 2) := by simp [hx_ne]
      simp [hdiv.symm]
    have h_g : g (Real.log x) = ENNReal.ofReal (‖Hσ.toFun f x‖^2) := by
      simp [g, Real.exp_log hxpos]
    have h_norm_sq :
        ENNReal.ofReal (‖Hσ.toFun f x‖^2)
          = (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) := by
      simp [pow_two]
    calc
      g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 2))
          = ENNReal.ofReal (‖Hσ.toFun f x‖^2)
              * ENNReal.ofReal (x ^ (2 * σ - 2)) := by
                simp [h_g]
      _ = (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 2)) := by
                simp [h_norm_sq]
      _ = (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 1) / x) := by
                simp [hpow_div]
  have h_change :
      ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) ∂volume := by
    simpa using h_change_restrict
  have h_rhs :
      ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
              * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume := by
    simpa using h_rhs_restrict
  calc
    ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂volume
        = ∫⁻ t, g t * ENNReal.ofReal (Real.exp ((2 * σ - 2) * t + t)) ∂volume := h_lhs
    _ = ∫⁻ x in Set.Ioi (0 : ℝ), g (Real.log x) *
        ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume := h_change.symm
    _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
            * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume := h_rhs

/-- When f = 0 in Hσ, the L2 integral of its squared norm is 0 -/
lemma Hσ_zero_integral (σ : ℝ) :
    ∫⁻ x in Set.Ioi (0 : ℝ),
      (‖Hσ.toFun (0 : Hσ σ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
        * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume = 0 := by
  -- The zero element in Hσ has Hσ.toFun 0 x = 0 for every x
  -- Hence the integrand vanishes pointwise and the integral is zero
  classical
  -- Reuse the `Hσ_norm_squared` machinery to evaluate the zero integrand
  set wσ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x ^ (2 * σ - 1)) with hwσ
  set μ := mulHaar.withDensity wσ with hμ
  set g : ℝ → ℝ≥0∞ :=
      fun x => (ENNReal.ofReal (‖Hσ.toFun (0 : Hσ σ) x‖)) ^ (2 : ℕ) with hg
  have hwσ_meas : Measurable wσ := by
    rw [hwσ]
    measurability
  have hg_meas : Measurable g := by
    -- identical to the argument used in `Hσ_norm_squared`
    have hsm : StronglyMeasurable fun x => Hσ.toFun (0 : Hσ σ) x := by
      simpa using
        (Lp.stronglyMeasurable
          (f := ((0 : Hσ σ) : Lp ℂ 2 (mulHaar.withDensity wσ))))
    have hfn : Measurable fun x => Hσ.toFun (0 : Hσ σ) x := hsm.measurable
    have hnorm : Measurable fun x => ‖Hσ.toFun (0 : Hσ σ) x‖ := hfn.norm
    have h_ofReal : Measurable fun x => ENNReal.ofReal (‖Hσ.toFun (0 : Hσ σ) x‖) :=
      ENNReal.measurable_ofReal.comp hnorm
    simpa [g, hg] using h_ofReal.pow_const (2 : ℕ)
  have hzero_ae : Hσ.toFun (0 : Hσ σ) =ᵐ[μ] (0 : ℝ → ℂ) := by
    simpa [μ, hμ, Hσ, wσ, hwσ] using
      (Lp.coeFn_zero (E := ℂ) (μ := μ) (p := (2 : ℝ≥0∞)))
  have hg_zero : g =ᵐ[μ] 0 :=
    hzero_ae.mono (by intro x hx; simp [g, hx])
  have h_int_μ : ∫⁻ x, g x ∂μ = 0 := by
    have := lintegral_congr_ae (μ := μ) hg_zero
    simpa [g, hg] using this
  -- Expand the weighted measure back to the stated integral
  have h_expand₁ :
      (∫⁻ x, g x ∂μ)
        = ∫⁻ x, g x * wσ x ∂mulHaar := by
    simpa [μ, hμ] using
      (lintegral_withDensity_expand (g := g) (wσ := wσ) hg_meas hwσ_meas)
  have h_expand₂ :
      (∫⁻ x, g x * wσ x ∂mulHaar)
        = ∫⁻ x in Set.Ioi 0, (g x * wσ x) * ENNReal.ofReal (1 / x) ∂volume := by
    simpa using
      lintegral_mulHaar_expand (g := fun x : ℝ => g x * wσ x)
        ((hg_meas.mul hwσ_meas))
  have h_expand₃ :
      (fun x : ℝ => (g x * wσ x) * ENNReal.ofReal (1 / x))
          =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun x : ℝ =>
          ((‖Hσ.toFun (0 : Hσ σ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
            * ENNReal.ofReal (x ^ (2 * σ - 1) / x)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    -- simplify the weight product on `Ioi 0`
    have hx' := weight_product_simplify (σ := σ) x hx
    have hx'' :
        ENNReal.ofReal (1 / x) * wσ x
          = ENNReal.ofReal (x ^ (2 * σ - 1) / x) := by
      simpa [wσ, hwσ, mul_comm] using hx'
    -- multiply both sides by the squared norm factor
    have hx_multipled :=
      congrArg (fun t => t * (ENNReal.ofReal (‖Hσ.toFun (0 : Hσ σ) x‖) ^ (2 : ℕ))) hx''
    simpa [g, hg, wσ, hwσ, mul_comm, mul_left_comm, mul_assoc]
      using hx_multipled
  -- Put the expansions together and rewrite the lintegral in volume form
  have h_expand :
      ∫⁻ x, g x ∂μ
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            ((‖Hσ.toFun (0 : Hσ σ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume := by
    calc
      ∫⁻ x, g x ∂μ
          = ∫⁻ x, g x * wσ x ∂mulHaar := by simpa using h_expand₁
      _ = ∫⁻ x in Set.Ioi 0, (g x * wσ x) * ENNReal.ofReal (1 / x) ∂volume := h_expand₂
      _ = ∫⁻ x in Set.Ioi 0,
            ((‖Hσ.toFun (0 : Hσ σ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume := by
            apply lintegral_congr_ae
            simpa using h_expand₃
  simpa [h_expand] using h_int_μ

lemma LogPull_memLp (σ : ℝ) (f : Hσ σ) :
    MemLp (LogPull σ f) 2 (volume : Measure ℝ) := by
  classical
  have h_meas : Measurable (LogPull σ f) := LogPull_measurable (σ := σ) f
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  set I := ∫⁻ x in Set.Ioi (0 : ℝ),
      (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
        * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume with hI
  have h_integral_eq := LogPull_sq_integral_eq (σ := σ) (f := f)
  have h_norm := Hσ_norm_squared (σ := σ) f
  have h_integral_eq' :
      ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂volume = I := by
    simpa [hI] using h_integral_eq
  have h_norm' : ‖f‖ ^ 2 = I.toReal := by
    simpa [hI] using h_norm
  have hI_ne_top : I ≠ ∞ := by
    intro htop
    have hnorm_sq_zero : ‖f‖ ^ 2 = 0 := by
      simp [h_norm', htop, ENNReal.toReal_top]
    have hf_norm_zero : ‖f‖ = 0 := by
      have : ‖f‖ * ‖f‖ = 0 := by simpa [pow_two] using hnorm_sq_zero
      exact mul_self_eq_zero.mp this
    have hf_zero : f = 0 := norm_eq_zero.mp hf_norm_zero
    have hI_zero : I = 0 := by
      subst hf_zero
      simp only [hI]
      exact Hσ_zero_integral σ
    exact ENNReal.zero_ne_top (by simpa [hI_zero] using htop)
  have hI_lt_top : I < ∞ := lt_of_le_of_ne le_top hI_ne_top
  have h_integral_lt_top :
      (∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂volume) < ∞ := by
    exact h_integral_eq'.symm ▸ hI_lt_top
  have h_integral_repr :
      ∫⁻ t, (‖LogPull σ f t‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂volume
        = ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂volume := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp [pow_two]
  have h_integral_enorm_lt_top :
      (∫⁻ t, (‖LogPull σ f t‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) < ∞ := by
    simpa [h_integral_repr] using h_integral_lt_top
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by
    simp
  have h_eLp_repr :
      eLpNorm (LogPull σ f) (2 : ℝ≥0∞) volume
        = (∫⁻ t, (‖LogPull σ f t‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa using
      (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        (μ := volume) (f := LogPull σ f) (p := (2 : ℝ≥0∞))
        (hp_ne_zero := hp_ne_zero) (hp_ne_top := hp_ne_top))
  have h_eLp_lt_top :
      eLpNorm (LogPull σ f) (2 : ℝ≥0∞) volume < ∞ := by
    have h_base_ne_top :
        (∫⁻ t, (‖LogPull σ f t‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ≠ ∞ :=
      ne_of_lt h_integral_enorm_lt_top
    have h_exponent_nonneg : 0 ≤ 1 / (2 : ℝ) := by norm_num
    have h_pow_lt :
        (∫⁻ t, (‖LogPull σ f t‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) < ∞ :=
      ENNReal.rpow_lt_top_of_nonneg h_exponent_nonneg h_base_ne_top
    simpa [h_eLp_repr] using h_pow_lt
  simpa using h_eLp_lt_top

/-- The Mellin transform of an L² function on ℝ₊ with weight t^(2σ-1)
    belongs to L²(ℝ) when evaluated along the critical line Re(s) = σ -/
theorem mellin_in_L2 (σ : ℝ) (f : Hσ σ) :
    MemLp (LogPull σ f) 2 (volume : Measure ℝ) := by
  exact LogPull_memLp σ f

/-- Direct isometry theorem: The Mellin transform preserves L² norm -/
theorem mellin_direct_isometry (σ : ℝ) :
    ∃ C > 0, ∀ f : Hσ σ,
      ∫ τ : ℝ, ‖LogPull σ f τ‖^2 ∂volume = C * ‖f‖^2 := by
  classical
  refine ⟨1, by simp, ?_⟩
  intro f
  -- Abbreviate the Mellin transform on the critical line
  set g : ℝ → ℂ := LogPull σ f with hg
  -- L² integrability of the squared norm of `g`
  have hMem : MemLp g 2 (volume : Measure ℝ) := mellin_in_L2 σ f
  have hInt_sq : Integrable (fun τ => ‖g τ‖ ^ 2) (volume : Measure ℝ) := by
    have := (memLp_two_iff_integrable_sq_norm hMem.1).1 hMem
    simpa [hg, g, pow_two] using this
  have hNonneg : 0 ≤ᵐ[volume] fun τ => ‖g τ‖ ^ 2 :=
    Filter.Eventually.of_forall (fun τ => sq_nonneg _)
  -- Relate the real integral to the corresponding lintegral
  have hOfReal :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt_sq hNonneg
  have hIntegral_nonneg :
      0 ≤ ∫ τ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ) :=
    integral_nonneg (fun τ => sq_nonneg _)
  have hIntegral_eq :
      ∫ τ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ)
        = (∫⁻ τ, ENNReal.ofReal (‖g τ‖ ^ 2)
            ∂(volume : Measure ℝ)).toReal := by
    have := congrArg ENNReal.toReal hOfReal
    simpa [hIntegral_nonneg, ENNReal.toReal_ofReal] using this
  -- Express the lintegral using the standard L² integrand
  set I : ℝ≥0∞ := ∫⁻ τ, (‖g τ‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure ℝ)
    with hI
  have hI_ofReal :
      (∫⁻ τ, ENNReal.ofReal (‖g τ‖ ^ 2) ∂(volume : Measure ℝ)) = I := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun τ => ?_)
    have hnn : 0 ≤ ‖g τ‖ := norm_nonneg _
    simp [pow_two, ENNReal.ofReal_mul, g]
  -- Change of variables for the logarithmic pullback identifies `I`
  set J : ℝ≥0∞ := ∫⁻ x in Set.Ioi (0 : ℝ),
      (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) *
        ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume with hJ
  have hI_eq_J : I = J := by
    have := LogPull_sq_integral_eq (σ := σ) (f := f)
    simpa [I, J, g, hg, LogPull]
  -- Combine with the norm identity for `Hσ`
  have hJ_toReal : J.toReal = ‖f‖ ^ 2 := by
    simpa [J] using (LogPull_isometry (σ := σ) (f := f)).symm
  have hI_toReal : I.toReal = ‖f‖ ^ 2 := by
    have := congrArg ENNReal.toReal hI_eq_J
    exact this.trans hJ_toReal
  -- Put everything together
  have hIntegral_I :
      ∫ τ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ) = I.toReal := by
    simpa [hI_ofReal] using hIntegral_eq
  have hFinal : ∫ τ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ) = ‖f‖ ^ 2 :=
    hIntegral_I.trans hI_toReal
  simpa [g, hg, LogPull, one_mul] using hFinal

/-- Main theorem: Mellin transform intertwines D_Φ with multiplication -/
theorem mellin_intertwines_DΦ_direct (φ : ℝ) (hφ : 1 < φ) (σ : ℝ) (f : Hσ σ) :
    ∀ τ : ℝ, LogPull (σ - 1) (DΦ φ σ f) τ =
             phiSymbol φ σ * LogPull σ f τ := by
  intro τ
  -- The Frourio differential D_Φ in the time domain becomes multiplication
  -- by phiSymbol in the frequency domain
  -- This is the key intertwining property
  sorry

/-- Mellin-Plancherel Formula: The Mellin transform preserves the L² norm
    up to a constant factor depending on σ -/
theorem mellin_plancherel_formula (σ : ℝ) (f : Hσ σ) :
    ∃ C > 0, ∫ τ : ℝ, ‖LogPull σ f τ‖^2 ∂volume = C * ‖f‖^2 := by
  obtain ⟨C, hC_pos, hC_eq⟩ := mellin_direct_isometry (σ := σ)
  exact ⟨C, hC_pos, hC_eq f⟩

/-- Auxiliary identity: the Jacobian weight appearing in `LogPull` cancels with
the inverse weight built into `toHσ_ofL2`. -/
lemma exp_weight_cancel (σ τ : ℝ) :
    (Real.exp ((σ - (1 / 2 : ℝ)) * τ) : ℂ)
        * (Real.exp τ : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ) = 1 := by
  classical
  set a : ℝ := σ - (1 / 2 : ℝ)
  set z : ℂ := (Real.exp τ : ℂ) with hz_def
  have hz_ne : z ≠ 0 := by
    have : (Real.exp τ : ℂ) ≠ 0 := by
      simp
    simp [hz_def]
  have hlog : Complex.log z = τ := by
    have hx_nonneg : 0 ≤ Real.exp τ := (Real.exp_pos τ).le
    have := (Complex.ofReal_log hx_nonneg).symm
    simpa [hz_def, Real.log_exp] using this
  have h_pos : z ^ (a : ℂ) = (Real.exp (a * τ) : ℂ) := by
    calc
      z ^ (a : ℂ)
          = Complex.exp ((a : ℂ) * Complex.log z) := by
              simp [Complex.cpow_def, hz_ne, mul_comm]
      _ = Complex.exp ((a : ℂ) * τ) := by
        rw [hlog]
      _ = (Real.exp (a * τ) : ℂ) := by
        have : ((a : ℂ) * τ) = (a * τ : ℝ) := by
          simp
        rw [this]
        simp
  have h_neg : z ^ (-(a : ℂ)) = (Real.exp ((-a) * τ) : ℂ) := by
    calc
      z ^ (-(a : ℂ))
          = Complex.exp (-(a : ℂ) * Complex.log z) := by
              simp [Complex.cpow_def, hz_ne, mul_comm]
      _ = Complex.exp (-(a : ℂ) * τ) := by
        rw [hlog]
      _ = (Real.exp ((-a) * τ) : ℂ) := by
        have : (-(a : ℂ)) * τ = (-a * τ : ℝ) := by
          simp
        rw [this]
        simp
  have h_prod : z ^ (a : ℂ) * z ^ (-(a : ℂ)) = 1 := by
    have h_cpow_add := Complex.cpow_add (a : ℂ) (-(a : ℂ)) hz_ne
    have h_sum : (a : ℂ) + (-(a : ℂ)) = 0 := by simp
    have : z ^ (a : ℂ) * z ^ (-(a : ℂ)) = z ^ ((a : ℂ) + (-(a : ℂ))) := h_cpow_add.symm
    rw [this, h_sum]
    simp [Complex.cpow_zero]
  calc
    (Real.exp ((σ - (1 / 2 : ℝ)) * τ) : ℂ)
        * (Real.exp τ : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ)
        = (Real.exp (a * τ) : ℂ) * (Real.exp τ : ℂ) ^ (-(a : ℂ)) := by
          congr 2
          simp only [a]
          norm_cast
    _ = (Real.exp (a * τ) : ℂ) * z ^ (-(a : ℂ)) := by
          rw [hz_def]
    _ = z ^ (a : ℂ) * z ^ (-(a : ℂ)) := by
          rw [←h_pos]
    _ = 1 := h_prod

/-- Evaluating `LogPull` on the canonical preimage produced by `toHσ_ofL2`
recovers the original L² function pointwise. -/
lemma LogPull_toHσ_ofL2 (σ : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ τ : ℝ, LogPull σ (toHσ_ofL2 σ g) τ = (g : ℝ → ℂ) τ := by
  intro τ
  classical
  have hpos : 0 < Real.exp τ := Real.exp_pos τ
  have h_eval_if :
      Hσ.toFun (toHσ_ofL2 σ g) (Real.exp τ)
        = (if (0 < Real.exp τ) then
            (g : ℝ → ℂ) (Real.log (Real.exp τ))
              * (Real.exp τ : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ)
          else 0) := by
    -- toHσ_ofL2 constructs a function h(x) = g(log x) * x^(-(σ - 1/2)) when x > 0
    -- Hσ.toFun extracts the underlying function from the Lp type
    -- We need to show that evaluating at exp(τ) gives g(log(exp(τ))) * exp(τ)^(-(σ - 1/2))
    -- which simplifies to g(τ) * exp(τ)^(-(σ - 1/2)) since log(exp(τ)) = τ

    -- The key insight is that toHσ_ofL2 σ g produces a function that when evaluated at x
    -- gives g(log x) * x^(-(σ - 1/2)) if x > 0, and 0 otherwise
    -- This follows from the definition of toHσ_ofL2 in MellinBasic.lean
    sorry -- Need to unfold definitions and use properties of MemLp.toLp
  have h_eval :
      Hσ.toFun (toHσ_ofL2 σ g) (Real.exp τ)
        = (g : ℝ → ℂ) τ * (Real.exp τ : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ) := by
    simpa [hpos, Real.log_exp] using h_eval_if
  have h_cancel := exp_weight_cancel σ τ
  calc
    LogPull σ (toHσ_ofL2 σ g) τ
        = (Real.exp ((σ - (1 / 2 : ℝ)) * τ) : ℂ)
            * ((g : ℝ → ℂ) τ
                * (Real.exp τ : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ)) := by
              simp [LogPull, h_eval]
    _ = ((Real.exp ((σ - (1 / 2 : ℝ)) * τ) : ℂ)
            * (Real.exp τ : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ))
            * (g : ℝ → ℂ) τ := by
              simp [mul_comm, mul_assoc]
    _ = (g : ℝ → ℂ) τ := by
        sorry -- Need to show cancellation of exponential terms

/-- The inverse Mellin transform formula -/
theorem mellin_inverse_formula (σ : ℝ) (g : ℝ → ℂ)
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    ∃ f : Hσ σ, ∀ τ : ℝ, LogPull σ f τ = g τ := by
  classical
  -- Promote g ∈ L²(ℝ) to an element of `Lp` and apply the inverse construction
  let gLp : Lp ℂ 2 (volume : Measure ℝ) := MemLp.toLp g hg
  refine ⟨toHσ_ofL2 σ gLp, ?_⟩
  intro τ
  -- `LogPull` composed with `toHσ_ofL2` yields the original L² function
  have hpull := LogPull_toHσ_ofL2 (σ := σ) (g := gLp) τ
  sorry -- Need to show that gLp and g are equal pointwise

/-- Mellin transform intertwines multiplication by t^α with translation -/
theorem mellin_scaling_translation (σ : ℝ) (α : ℝ) (f : Hσ σ) :
    ∀ τ : ℝ, LogPull σ f τ =
              LogPull σ f τ * Complex.exp (-2 * Real.pi * α * τ * Complex.I) := by
  sorry

/-- Parseval's identity for Mellin transform -/
theorem mellin_parseval (σ : ℝ) (f g : Hσ σ) :
    @inner ℂ _ _ f g = (2 * Real.pi)⁻¹ *
      ∫ τ, star (LogPull σ f τ) * LogPull σ g τ ∂volume := by
  -- Parseval's identity relates inner product in Hσ to integral in frequency domain
  -- This is a consequence of the Plancherel formula
  sorry

/-- Mellin convolution theorem -/
theorem mellin_convolution (σ : ℝ) (f g : Hσ σ) :
    ∀ τ : ℝ, LogPull σ f τ * LogPull σ g τ =
    mellinTransform (fun t => if 0 < t then
      ∫ u in Set.Ioi 0, (f : ℝ → ℂ) u * (g : ℝ → ℂ) (t / u) * u⁻¹ ∂volume
    else 0) (↑σ + ↑τ * Complex.I) := by
  sorry

/-- The Mellin transform of a Gaussian is a Gaussian -/
theorem mellin_gaussian (σ : ℝ) (a : ℝ) (ha : 0 < a) :
    ∀ τ : ℝ, mellinTransform (fun t => if 0 < t then Complex.exp (-(a : ℂ) * (t : ℂ)^2) else 0)
                              (↑σ + ↑τ * Complex.I) =
    Complex.ofReal (Real.sqrt (Real.pi / a)) *
      Complex.exp (-(Real.pi : ℂ)^2 * (τ : ℂ)^2 / (4 * (a : ℂ))) := by
  sorry

end MellinPlancherelTheorems

section Chapter0API
/-!
## Step 6: Chapter 0 API Export (0章の「二点 Frourio 作用素×等長」API)

This section exports the main definitions and theorems from Chapter 0,
providing a complete API for the measure-theoretic foundations,
Mellin transform isometry, and zero lattice characterization.
-/

/-- Tφ_on_L2: The multiplication operator on L²(ℝ) corresponding to phiSymbol.
    This represents the action τ ↦ S_{-(σ+iτ)} in frequency space. -/
noncomputable def Tφ_on_L2 (φ : ℝ) (_ : 1 < φ) (σ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  -- This is the multiplication by phiSymbol φ (-(σ + i·))
  -- For consistency with Mφ, we use the negated argument
  (phiSymbol φ (-(σ : ℂ))) • (ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ)))

end Chapter0API

end Frourio
