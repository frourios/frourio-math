import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Frourio.Analysis.HolderInequality.HolderInequality
import Frourio.Analysis.SchwartzDensityLp.LpDuality

/-!
# Minkowski's Integral Inequality

This file contains Minkowski's integral inequality and related results.

Minkowski's integral inequality is a fundamental inequality in analysis that
generalizes the triangle inequality to integrals. It states that for measurable
functions and 1 ≤ p < ∞:

  ‖∫ F(·, y) dν(y)‖_{L^p(μ)} ≤ ∫ ‖F(·, y)‖_{L^p(μ)} dν(y)

This inequality is crucial for proving:
- Young's inequality for convolution
- Convolution bounds in L^p spaces
- Various interpolation inequalities

## Main results

- `minkowski_integral_inequality`: The main Minkowski integral inequality
- `minkowski_integral_inequality_ennreal`: Version with extended non-negative reals
- `minkowski_integral_inequality_one`: Special case p = 1
- `minkowski_integral_inequality_two`: Special case p = 2

## References

- Folland, Real Analysis: Modern Techniques and Their Applications, Section 6.2
- Lieb & Loss, Analysis, Section 2.5
- Stein & Shakarchi, Real Analysis, Chapter 2

## Implementation notes

The proof proceeds in several steps:
1. Show the inequality for simple functions
2. Extend to non-negative measurable functions by monotone convergence
3. Extend to general functions by considering real and imaginary parts
4. Handle the case p = ∞ separately using essential supremum

-/

open MeasureTheory ENNReal NNReal
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section MinkowskiBasic

variable [SFinite ν]

/--
**Minkowski's integral inequality (basic version for p = 1).**

For any measurable function F : α × β → E,
  ‖∫ (∫ F(x,y) dν(y)) dμ(x)‖ ≤ ∫∫ ‖F(x,y)‖ dν(y) dμ(x)

This is essentially the triangle inequality for integrals.
-/
theorem minkowski_integral_inequality_one
    (F : α → β → E)
    (hF : Integrable (Function.uncurry F) (μ.prod ν)) :
    ‖∫ x, ∫ y, F x y ∂ν ∂μ‖ ≤ ∫ x, ∫ y, ‖F x y‖ ∂ν ∂μ := by
  classical
  have hF_left : Integrable (fun x => ∫ y, F x y ∂ν) μ := hF.integral_prod_left
  have hF_norm : Integrable (fun x => ∫ y, ‖F x y‖ ∂ν) μ := hF.integral_norm_prod_left
  have h_pointwise :
      ∀ᵐ x ∂μ, ‖∫ y, F x y ∂ν‖ ≤ ∫ y, ‖F x y‖ ∂ν :=
    ae_of_all _ fun x => norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
  have h_integral_le :=
    integral_mono_ae hF_left.norm hF_norm h_pointwise
  have h_norm_le :
      ‖∫ x, ∫ y, F x y ∂ν ∂μ‖ ≤ ∫ x, ‖∫ y, F x y ∂ν‖ ∂μ :=
    norm_integral_le_integral_norm (fun x => ∫ y, F x y ∂ν)
  exact h_norm_le.trans h_integral_le

/--
**Minkowski's integral inequality (basic version for p = 1, with ENNReal).**

This version works with extended non-negative reals and uses `eLpNorm`.
-/
theorem minkowski_integral_inequality_one_ennreal
    (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν)) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) 1 μ ≤
    ∫⁻ x, ∫⁻ y, (‖F x y‖₊ : ℝ≥0∞) ∂ν ∂μ := by
  classical
  have h_meas : AEStronglyMeasurable (fun x => ∫ y, F x y ∂ν) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := ν) (f := Function.uncurry F) hF)
  have h_pointwise :
      (fun x => ‖∫ y, F x y ∂ν‖ₑ) ≤ᵐ[μ]
        fun x => ∫⁻ y, ‖F x y‖ₑ ∂ν :=
    ae_of_all _ fun x => enorm_integral_le_lintegral_enorm (μ := ν) (f := fun y => F x y)
  have h_mono := lintegral_mono_ae h_pointwise
  simpa [eLpNorm_one_eq_lintegral_enorm, ofReal_norm_eq_enorm] using h_mono

end MinkowskiBasic

section MinkowskiGeneral

variable [SFinite μ] [SFinite ν]

/--
**Minkowski's integral inequality (general form with eLpNorm).**

For 1 ≤ p < ∞ and measurable F : α × β → E,
  ‖∫ F(·, y) dν(y)‖_{L^p(μ)} ≤ ∫ ‖F(·, y)‖_{L^p(μ)} dν(y)

This is the key inequality for proving Young's inequality for convolution.
-/
theorem minkowski_integral_inequality
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_int : ∀ᵐ y ∂ν, Integrable (fun x => F x y) μ)
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν) := by
  classical
  have h_meas : AEStronglyMeasurable (fun x => ∫ y, F x y ∂ν) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := ν) (f := Function.uncurry F) hF)
  have h_integrable : Integrable (fun x => ∫ y, F x y ∂ν) μ := by
    have h_bound :
        ∀ᵐ x ∂μ, ‖∫ y, F x y ∂ν‖ ≤ ∫ y, ‖F x y‖ ∂ν :=
      ae_of_all _ fun x => norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    refine Integrable.mono'
      (hF_prod.integral_norm_prod_left)
      h_meas
      h_bound
  have h_norm_finite : (∫⁻ y, ‖(eLpNorm (fun x => F x y) p μ).toReal‖ₑ ∂ν) < ∞ :=
    hF_norm.hasFiniteIntegral
  -- The right-hand side is nonnegative, so we may work with real-valued estimates
  have h_rhs_nonneg :
      0 ≤ ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν :=
    integral_nonneg fun y => ENNReal.toReal_nonneg
  -- Reduce the claim to the integral formulation of the `L^p` seminorm
  have hp_ne_zero : p ≠ 0 := by
    intro h
    have : (1 : ℝ≥0∞) ≤ 0 := by simp [h] at hp
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ≥0∞) < 1)) this
  have h_lhs_rewrite :=
    eLpNorm_eq_lintegral_rpow_enorm (μ := μ)
      (f := fun x => ∫ y, F x y ∂ν) hp_ne_zero hp_ne_top
  -- Work with the auxiliary scalar function given by the norm of the fibrewise integral.
  set g : α → ℝ := fun x => ‖∫ y, F x y ∂ν‖
  set B : ℝ := ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν
  have hB_nonneg : 0 ≤ B :=
    integral_nonneg fun _ => ENNReal.toReal_nonneg
  by_cases hp_eq_one : p = 1
  · subst hp_eq_one
    have h_pointwise :
        ∀ᵐ x ∂μ, g x ≤ ∫ y, ‖F x y‖ ∂ν :=
      ae_of_all _ fun x =>
        norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    have hg_int : Integrable g μ := h_integrable.norm
    have h_integral_le :
        ∫ x, g x ∂μ ≤ ∫ x, ∫ y, ‖F x y‖ ∂ν ∂μ :=
      integral_mono_ae hg_int
        (hF_prod.integral_norm_prod_left)
        h_pointwise
    have h_inner_eq :
        ∀ᵐ y ∂ν,
          ∫ x, ‖F x y‖ ∂μ =
            (eLpNorm (fun x => F x y) 1 μ).toReal := by
      filter_upwards [hF_int] with y hy_int
      have h_eq :=
        integral_norm_eq_toReal_lintegral (μ := μ)
          (f := fun x => F x y) hy_int
      simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        using h_eq
    have h_double :
        ∫ x, ∫ y, ‖F x y‖ ∂ν ∂μ = B := by
      have h_swap :=
        integral_norm_kernel_swap (μ := μ) (ν := ν) hF_prod
      have h_congr := integral_congr_ae h_inner_eq
      simpa [g, B] using h_swap.trans h_congr
    have h_integral_bound : ∫ x, g x ∂μ ≤ B := by
      simpa [h_double] using h_integral_le
    have h_toReal_aux :=
      integral_norm_eq_toReal_lintegral (μ := μ)
        (f := fun x => ∫ y, F x y ∂ν) h_integrable
    have h_toReal :
        (eLpNorm (fun x => ∫ y, F x y ∂ν) 1 μ).toReal = ∫ x, g x ∂μ := by
      simpa [g, MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        using h_toReal_aux.symm
    have h_toReal_le :
        (eLpNorm (fun x => ∫ y, F x y ∂ν) 1 μ).toReal ≤ B := by
      simpa [h_toReal] using h_integral_bound
    have h_memLp :
        MemLp (fun x => ∫ y, F x y ∂ν) 1 μ :=
      (memLp_one_iff_integrable : _ ↔ _).2 h_integrable
    have h_ne_top := h_memLp.eLpNorm_ne_top
    exact
      (le_ofReal_iff_toReal_le h_ne_top hB_nonneg).2 h_toReal_le
  · have hp_one_lt : 1 < p :=
      lt_of_le_of_ne' hp (by simpa [eq_comm] using hp_eq_one)
    have hp_lt_top : p < ∞ :=
      lt_of_le_of_ne le_top hp_ne_top
    obtain ⟨q, hpq, -⟩ :=
      conjugate_exponent_formula (p := p) hp_one_lt hp_lt_top
    have hq_gt_one : 1 < q := by
      rcases hpq with hpq | hpq
      · rcases hpq with ⟨hp_eq, _⟩
        simp [hp_eq] at hp_one_lt
      · rcases hpq with hpq | hpq
        · rcases hpq with ⟨hp_eq, _⟩
          simpa [hp_eq] using hp_lt_top.ne
        · rcases hpq with ⟨_, _, hq, _, _⟩
          exact hq
    have hg_mem : MemLp g p μ :=
      SchwartzDensityLp.memLp_norm_integral (μ := μ) (ν := ν) (p := p)
        hp hp_ne_top hF hF_prod hF_int hF_memLp hF_norm
    have h_pairing_bound :
        ∀ φ : α → ℝ,
          MemLp φ q μ →
          (eLpNorm φ q μ).toReal ≤ 1 →
          Integrable (fun x => g x * φ x) μ →
          |∫ x, g x * φ x ∂μ| ≤ B := by
      intro φ hφ_mem hφ_norm _hφ_int
      have h_est :=
        holder_kernel_pairing_bound (μ := μ) (ν := ν)
          (p := p) (q := q) hpq
          hF hF_prod hF_memLp hF_norm hφ_mem
      have h_mul :
          (eLpNorm φ q μ).toReal * B ≤ B := by
        have := mul_le_mul_of_nonneg_right hφ_norm hB_nonneg
        simpa [mul_comm, mul_left_comm, mul_assoc]
          using this
      exact h_est.trans h_mul
    have h_norm_le :
        (eLpNorm g p μ).toReal ≤ B :=
      SchwartzDensityLp.lp_duality_norm_le_of_pairing_bound (μ := μ)
        (p := p) (q := q)
        hp_one_lt hq_gt_one hpq hg_mem h_pairing_bound
    have h_ne_top :
        eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≠ ∞ := by
      have hg_ne_top := hg_mem.eLpNorm_ne_top
      simpa [g]
        using hg_ne_top
    have h_toReal_le :
        (eLpNorm (fun x => ∫ y, F x y ∂ν) p μ).toReal ≤ B := by
      simpa [g] using h_norm_le
    exact
      (le_ofReal_iff_toReal_le h_ne_top hB_nonneg).2 h_toReal_le

/--
**Minkowski's integral inequality (ENNReal version).**

This version uses lintegral (extended integration) throughout.
-/
theorem minkowski_integral_inequality_ennreal
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν) := by
  sorry

end MinkowskiGeneral

section MinkowskiSpecialCases

/--
**Minkowski's integral inequality for p = 2 (Hilbert space case).**

This case is simpler because L² has inner product structure.
-/
theorem minkowski_integral_inequality_two
    (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_int : ∀ᵐ y ∂ν, Integrable (fun x => F x y) μ)
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) 2 μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) 2 μ).toReal) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) 2 μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) 2 μ).toReal ∂ν) := by
  sorry

/--
**Minkowski's integral inequality for finite measures.**

When both measures are finite, the hypotheses can be simplified.
-/
theorem minkowski_integral_inequality_finite
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_bound : ∀ᵐ (p : α × β) ∂(μ.prod ν), ‖F p.1 p.2‖ ≤ 1) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν) := by
  sorry

end MinkowskiSpecialCases

section MinkowskiConvolution

/--
**Minkowski's inequality applied to convolution kernels.**

This is the form most directly used in proving Young's inequality.

For f : α → E and g : α → ℝ≥0 (non-negative weight),
  ‖∫ f(x - y) g(y) dy‖_{L^p(dx)} ≤ ∫ ‖f(· - y)‖_{L^p} g(y) dy
-/
theorem minkowski_inequality_convolution
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G)
    [SFinite μ] [μ.IsAddRightInvariant]
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : G → E)
    (g : G → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hg : Integrable g μ)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hfg : ∀ᵐ y ∂μ, Integrable (fun x => (g y) • f (x - y)) μ) :
    eLpNorm (fun x => ∫ y, (g y) • f (x - y) ∂μ) p μ ≤
    ENNReal.ofReal (∫ y, |g y| * (eLpNorm (fun x => f (x - y)) p μ).toReal ∂μ) := by
  sorry

/--
**Simplified version for scalar-valued functions.**

When both f and g are scalar-valued, the statement simplifies.
-/
theorem minkowski_inequality_convolution_scalar
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G)
    [SFinite μ] [μ.IsAddRightInvariant]
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f g : G → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hg : Integrable g μ)
    (hg_nonneg : ∀ x, 0 ≤ g x) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) p μ ≤
    ENNReal.ofReal (∫ y, |g y| * (eLpNorm (fun x => f (x - y)) p μ).toReal ∂μ) := by
  sorry

end MinkowskiConvolution

section AuxiliaryLemmas

/--
**Jensen's inequality for integrals with convex functions.**

This is used in the proof of Minkowski's inequality.
-/
theorem jensen_integral_convex
    {f : α → ℝ}
    (hf : Integrable f μ)
    (φ : ℝ → ℝ)
    (hφ : ConvexOn ℝ (Set.univ) φ)
    (hφ_cont : Continuous φ) :
    φ (∫ x, f x ∂μ) ≤ ∫ x, φ (f x) ∂μ := by
  sorry

/--
**Power function is convex for p ≥ 1.**

The function x ↦ |x|^p is convex for p ≥ 1.
-/
theorem abs_pow_convex
    {p : ℝ}
    (hp : 1 ≤ p) :
    ConvexOn ℝ (Set.univ) (fun x : ℝ => |x| ^ p) := by
  sorry

/--
**Translation preserves L^p norm for Haar measure.**

For Haar measure, ‖f(· - y)‖_p = ‖f‖_p for all y.
-/
theorem eLpNorm_comp_sub_right
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G)
    [SFinite μ] [μ.IsAddRightInvariant]
    (f : G → E)
    (y : G)
    (p : ℝ≥0∞) :
    eLpNorm (fun x => f (x - y)) p μ = eLpNorm f p μ := by
  sorry

/--
**Fubini for non-negative convolution integrals.**

Swap order of integration for convolution-type integrals.
-/
theorem lintegral_convolution_swap
    {G : Type*} [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G)
    [SFinite μ] [μ.IsAddRightInvariant]
    (f g : G → ℝ≥0∞)
    (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) :
    ∫⁻ x, ∫⁻ y, f (x - y) * g y ∂μ ∂μ =
    ∫⁻ y, ∫⁻ x, f (x - y) * g y ∂μ ∂μ := by
  sorry

end AuxiliaryLemmas
