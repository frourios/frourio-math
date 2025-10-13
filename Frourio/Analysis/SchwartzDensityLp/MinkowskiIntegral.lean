import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
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

- `minkowski_integral_inequality_one`: Special case `p = 1`
- `minkowski_integral_inequality_one_ennreal`: L¹-version phrased with `eLpNorm`
- `minkowski_integral_inequality`: The general inequality for `1 ≤ p < ∞`
- `minkowski_integral_inequality_ennreal`: General version phrased with `eLpNorm`

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
variable {E : Type*} [NormedAddCommGroup E]

section MinkowskiBasic

variable [SFinite ν]

/--
**Minkowski's integral inequality (basic version for p = 1).**

For any measurable function F : α × β → E,
  ‖∫ (∫ F(x,y) dν(y)) dμ(x)‖ ≤ ∫∫ ‖F(x,y)‖ dν(y) dμ(x)

This is essentially the triangle inequality for integrals.
-/
theorem minkowski_integral_inequality_one
    (F : α → β → E) [NormedSpace ℝ E]
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
    (F : α → β → E) [NormedSpace ℝ E]
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
    [NormedSpace ℝ E] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (F : α → β → E)
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
        hp hp_ne_top hF hF_prod hF_memLp hF_norm
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
    [NormedSpace ℝ E] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν) := by
  classical
  have hF_int : ∀ᵐ y ∂ν, Integrable (fun x => F x y) μ := by
    simpa [Function.uncurry]
      using (hF_prod.prod_left_ae (μ := μ) (ν := ν))
  exact
    minkowski_integral_inequality p hp hp_ne_top F hF hF_prod hF_int hF_memLp hF_norm

end MinkowskiGeneral

section MinkowskiSpecialCases

variable [SFinite μ] [SFinite ν]

/--
**Minkowski's integral inequality for p = 2 (Hilbert space case).**

This case is simpler because L² has inner product structure.
-/
theorem minkowski_integral_inequality_two
    [NormedSpace ℝ E] (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_int : ∀ᵐ y ∂ν, Integrable (fun x => F x y) μ)
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) 2 μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) 2 μ).toReal) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) 2 μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) 2 μ).toReal ∂ν) := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
  exact
    minkowski_integral_inequality (μ := μ) (ν := ν)
      (p := (2 : ℝ≥0∞)) hp hp_ne_top F hF hF_prod hF_int hF_memLp hF_norm

/--
**Minkowski's integral inequality for finite measures.**

When both measures are finite, the hypotheses can be simplified.
-/
theorem minkowski_integral_inequality_finite
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F : α → β → E) (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_bound : ∀ᵐ (p : α × β) ∂(μ.prod ν), ‖F p.1 p.2‖ ≤ 1) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν) := by
  classical
  -- Replace `F` with a globally strongly measurable representative `Fmk`.
  set Fmk : α → β → E := fun x y => hF.mk (Function.uncurry F) (x, y)
  have h_eq_mk : Function.uncurry F =ᵐ[μ.prod ν] Function.uncurry Fmk := by
    simpa [Fmk, Function.uncurry] using hF.ae_eq_mk
  have hFmk_meas : AEStronglyMeasurable (Function.uncurry Fmk) (μ.prod ν) := by
    simpa [Fmk, Function.uncurry] using hF.stronglyMeasurable_mk.aestronglyMeasurable
  -- Pointwise bound transfers to the measurable representative.
  have hFmk_bound : ∀ᵐ z ∂μ.prod ν, ‖Fmk z.1 z.2‖ ≤ (1 : ℝ) := by
    filter_upwards [hF_bound, h_eq_mk] with z hz h_eq
    have h_eq_z : F z.1 z.2 = Fmk z.1 z.2 := by
      simpa [Function.uncurry] using h_eq
    simpa [h_eq_z]
      using hz
  -- Measurability of the level set required for `ae_ae_comm`.
  have h_bound_set :
      MeasurableSet {z : α × β | ‖Fmk z.1 z.2‖ ≤ (1 : ℝ)} := by
    have h_meas : Measurable fun z : α × β => (‖Fmk z.1 z.2‖ : ℝ) := by
      simpa [Fmk, Function.uncurry]
        using hF.stronglyMeasurable_mk.norm.measurable
    simpa [Set.preimage, Set.Iic]
      using h_meas measurableSet_Iic
  -- Extract the fibrewise bound in both orders.
  have hFmk_bound_x :
      ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ‖Fmk x y‖ ≤ (1 : ℝ) :=
    (Measure.ae_prod_iff_ae_ae (μ := μ) (ν := ν) h_bound_set).1 hFmk_bound
  have hFmk_bound_y :
      ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, ‖Fmk x y‖ ≤ (1 : ℝ) :=
    (Measure.ae_ae_comm (μ := μ) (ν := ν)
        (p := fun x y => ‖Fmk x y‖ ≤ (1 : ℝ)) h_bound_set).1 hFmk_bound_x
  -- Basic integrability of the representative on the product space.
  have h_const_prod : Integrable (fun _ : α × β => (1 : ℝ)) (μ.prod ν) := integrable_const _
  have hFmk_prod : Integrable (Function.uncurry Fmk) (μ.prod ν) := by
    refine Integrable.mono' (μ := μ.prod ν)
      (f := Function.uncurry Fmk)
      (g := fun _ : α × β => (1 : ℝ))
      h_const_prod
      hFmk_meas ?_
    simpa [Function.uncurry, Fmk]
      using hFmk_bound
  -- Preparatory measurability facts for the fibres of `Fmk`.
  have hFmk_swap :
      AEStronglyMeasurable (fun z : β × α => Fmk z.2 z.1) (ν.prod μ) := by
    have := hF.stronglyMeasurable_mk
    exact (this.comp_measurable measurable_swap).aestronglyMeasurable
  have hFmk_meas_y :
      ∀ᵐ y ∂ν, AEStronglyMeasurable (fun x => Fmk x y) μ := by
    refine (MeasureTheory.AEStronglyMeasurable.prodMk_left
      (μ := ν) (ν := μ) hFmk_swap).mono ?_
    intro y hy
    simpa [Fmk]
      using hy
  -- Fibrewise integrability and membership in `L^p` follow from the bound.
  have hFmk_int : ∀ᵐ y ∂ν, Integrable (fun x => Fmk x y) μ := by
    refine (hFmk_meas_y.and hFmk_bound_y).mono ?_
    intro y hy
    rcases hy with ⟨hy_meas, hy_bound⟩
    refine Integrable.mono' (μ := μ)
      (f := fun x => Fmk x y)
      (g := fun _ : α => (1 : ℝ))
      (integrable_const _)
      hy_meas ?_
    simpa using hy_bound
  have hFmk_memLp : ∀ᵐ y ∂ν, MemLp (fun x => Fmk x y) p μ := by
    refine (hFmk_meas_y.and hFmk_bound_y).mono ?_
    intro y hy
    rcases hy with ⟨hy_meas, hy_bound⟩
    exact MemLp.of_bound hy_meas (1 : ℝ) hy_bound
  -- Uniform bound on the fibrewise `L^p` norms.
  have hp_ne_zero : p ≠ 0 :=
    (lt_of_lt_of_le (zero_lt_one : (0 : ℝ≥0∞) < 1) hp).ne'
  have hp_toReal_pos : 0 < p.toReal :=
    ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have h_exp_nonneg : 0 ≤ p.toReal⁻¹ := inv_nonneg.mpr hp_toReal_pos.le
  have hμ_lt_top : μ Set.univ < ∞ := measure_lt_top _ _
  have hC_lt_top : μ Set.univ ^ p.toReal⁻¹ < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg h_exp_nonneg hμ_lt_top.ne
  have h_bound_eLp :
      ∀ᵐ y ∂ν, eLpNorm (fun x => Fmk x y) p μ ≤ μ Set.univ ^ p.toReal⁻¹ := by
    refine hFmk_bound_y.mono ?_
    intro y hy
    simpa using eLpNorm_le_of_ae_bound hy
  have h_bound_eLp_real :
      ∀ᵐ y ∂ν,
        (eLpNorm (fun x => Fmk x y) p μ).toReal
          ≤ (μ Set.univ ^ p.toReal⁻¹).toReal := by
    refine h_bound_eLp.mono ?_
    intro y hy
    have h_eLp_lt_top :
        eLpNorm (fun x => Fmk x y) p μ < ∞ := lt_of_le_of_lt hy hC_lt_top
    exact (ENNReal.toReal_le_toReal h_eLp_lt_top.ne hC_lt_top.ne).2 hy
  have h_integrand_aemeasurable :
      AEMeasurable
        (fun z : α × β => (‖Fmk z.1 z.2‖ₑ) ^ p.toReal) (μ.prod ν) := by
    have := hFmk_meas.aemeasurable.enorm.pow_const p.toReal
    simpa [Function.uncurry] using this
  have h_lintegral_aemeasurable :
      AEMeasurable
        (fun y => ∫⁻ x, (‖Fmk x y‖ₑ) ^ p.toReal ∂μ) ν :=
    h_integrand_aemeasurable.lintegral_prod_left'
  have h_eLp_aemeasurable :
      AEMeasurable (fun y => eLpNorm (fun x => Fmk x y) p μ) ν := by
    have hp_ne_zero' : p ≠ 0 := hp_ne_zero
    have hp_ne_top' : p ≠ ∞ := hp_ne_top
    have h_pow_meas : Measurable fun t : ℝ≥0∞ => t ^ (1 / p.toReal) :=
      (measurable_id.pow_const (1 / p.toReal))
    have := h_pow_meas.comp_aemeasurable h_lintegral_aemeasurable
    refine this.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    simp [eLpNorm_eq_lintegral_rpow_enorm (μ := μ)
      (f := fun x => Fmk x y) hp_ne_zero' hp_ne_top']
  have h_meas_toReal :
      AEStronglyMeasurable (fun y => (eLpNorm (fun x => Fmk x y) p μ).toReal) ν :=
    (h_eLp_aemeasurable.ennreal_toReal).aestronglyMeasurable
  have h_bound_eLp_norm :
      ∀ᵐ y ∂ν,
        ‖(eLpNorm (fun x => Fmk x y) p μ).toReal‖
          ≤ (μ Set.univ ^ p.toReal⁻¹).toReal := by
    refine h_bound_eLp_real.mono ?_
    intro y hy
    have h_nonneg : 0 ≤ (eLpNorm (fun x => Fmk x y) p μ).toReal :=
      ENNReal.toReal_nonneg
    simpa [Real.norm_of_nonneg h_nonneg]
      using hy
  have hFmk_norm :
      Integrable (fun y => (eLpNorm (fun x => Fmk x y) p μ).toReal) ν := by
    refine Integrable.mono' (μ := ν)
      (f := fun y => (eLpNorm (fun x => Fmk x y) p μ).toReal)
      (g := fun _ : β => (μ Set.univ ^ p.toReal⁻¹).toReal)
      (integrable_const _)
      h_meas_toReal
      h_bound_eLp_norm
  -- Apply the general inequality to the strongly measurable representative.
  have h_mk_result :=
    minkowski_integral_inequality (μ := μ) (ν := ν)
      (p := p) hp hp_ne_top Fmk hFmk_meas hFmk_prod hFmk_int hFmk_memLp hFmk_norm
  -- Identify both sides with the original function using the a.e. equality.
  have h_int_congr :
      ∀ᵐ x ∂μ, ∫ y, F x y ∂ν = ∫ y, Fmk x y ∂ν := by
    have h_eq_ae :
        ∀ᵐ x ∂μ, F x =ᵐ[ν] Fmk x :=
      (Measure.ae_ae_eq_of_ae_eq_uncurry (μ := μ) (ν := ν) h_eq_mk)
    refine h_eq_ae.mono ?_
    intro x hx
    exact integral_congr_ae hx
  have h_lhs_eq :
      eLpNorm (fun x => ∫ y, F x y ∂ν) p μ
          = eLpNorm (fun x => ∫ y, Fmk x y ∂ν) p μ :=
    eLpNorm_congr_norm_ae <|
      h_int_congr.mono fun _ hx => by simp [hx]
  have h_rhs_eq :
      ∀ᵐ y ∂ν,
          (eLpNorm (fun x => F x y) p μ).toReal
            = (eLpNorm (fun x => Fmk x y) p μ).toReal := by
    -- For ae y, the eLpNorms are equal because F = Fmk ae on the product
    have h_eq_prod : ∀ᵐ (p : α × β) ∂(μ.prod ν), F p.1 p.2 = Fmk p.1 p.2 := by
      filter_upwards [h_eq_mk] with p hp
      simpa [Function.uncurry] using hp
    -- Swap to get ν × μ order
    have h_swap_fn : (fun q : β × α => F q.2 q.1) =ᵐ[ν.prod μ] (fun q => Fmk q.2 q.1) := by
      have h_comp := (Measure.measurePreserving_swap (μ := ν)
        (ν := μ)).quasiMeasurePreserving.ae_eq_comp h_eq_prod
      simpa [Function.comp, Prod.swap] using h_comp
    -- Apply curry to extract y-fibres
    have h_curry_swap := Measure.ae_ae_eq_curry_of_prod (μ := ν) (ν := μ) h_swap_fn
    refine h_curry_swap.mono fun y hy => ?_
    have : (fun x => F x y) =ᵐ[μ] (fun x => Fmk x y) := by simpa [Function.curry] using hy
    simp [eLpNorm_congr_ae this]
  have h_rhs_eq_integral :
      ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν
        = ∫ y, (eLpNorm (fun x => Fmk x y) p μ).toReal ∂ν :=
    integral_congr_ae h_rhs_eq
  -- Transport the inequality from `Fmk` back to the original `F`.
  simpa [h_lhs_eq, h_rhs_eq_integral]
    using h_mk_result

end MinkowskiSpecialCases

section MinkowskiConvolution

/--
**Minkowski's inequality applied to convolution kernels.**

We specialise the abstract inequality to the kernel `(x, y) ↦ (g y) • f (x - y)`.
-/
theorem minkowski_inequality_convolution
    {G : Type*} [NormedSpace ℝ E] [NormedAddCommGroup G] [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G)
    [SFinite μ] [μ.IsAddRightInvariant]
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : G → E)
    (g : G → ℝ)
    (h_meas : AEStronglyMeasurable
      (fun q : G × G => (g q.2) • f (q.1 - q.2)) (μ.prod μ))
    (h_prod : Integrable (fun q : G × G => (g q.2) • f (q.1 - q.2)) (μ.prod μ))
    (h_int : ∀ᵐ y ∂μ, Integrable (fun x => (g y) • f (x - y)) μ)
    (h_memLp : ∀ᵐ y ∂μ, MemLp (fun x => (g y) • f (x - y)) p μ)
    (h_norm : Integrable
      (fun y => (eLpNorm (fun x => (g y) • f (x - y)) p μ).toReal) μ) :
    eLpNorm (fun x => ∫ y, (g y) • f (x - y) ∂μ) p μ ≤
    ENNReal.ofReal (∫ y, |g y| * (eLpNorm (fun x => f (x - y)) p μ).toReal ∂μ) := by
  classical
  have h_minkowski :=
    minkowski_integral_inequality (μ := μ) (ν := μ) (p := p)
      hp hp_ne_top (fun x y => (g y) • f (x - y))
      h_meas h_prod h_int h_memLp h_norm
  have h_scaling :
      ∀ y,
        eLpNorm (fun x => (g y) • f (x - y)) p μ =
          ENNReal.ofReal |g y| * eLpNorm (fun x => f (x - y)) p μ := by
    intro y
    have :=
      eLpNorm_const_smul (μ := μ) (p := p) (c := g y)
        (f := fun x => f (x - y))
    simpa [Real.norm_eq_abs, (ofReal_norm_eq_enorm (g y)).symm]
      using this
  set h_left : G → ℝ :=
      fun y => (eLpNorm (fun x => (g y) • f (x - y)) p μ).toReal
    with h_left_def
  set h_right : G → ℝ :=
      fun y => |g y| * (eLpNorm (fun x => f (x - y)) p μ).toReal
    with h_right_def
  have h_pointwise : h_left =ᵐ[μ] h_right := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have h_eq := h_scaling y
    have h_toReal := congrArg ENNReal.toReal h_eq
    simpa [h_left_def, h_right_def, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal, abs_nonneg] using h_toReal
  have h_integral_eq : ∫ y, h_left y ∂μ = ∫ y, h_right y ∂μ :=
    integral_congr_ae h_pointwise
  have h_minkowski_left :
      eLpNorm (fun x => ∫ y, (g y) • f (x - y) ∂μ) p μ ≤
        ENNReal.ofReal (∫ y, h_left y ∂μ) := by
    simpa [h_left_def] using h_minkowski
  have h_result :
      eLpNorm (fun x => ∫ y, (g y) • f (x - y) ∂μ) p μ ≤
        ENNReal.ofReal (∫ y, h_right y ∂μ) := by
    simpa [h_right_def, h_integral_eq] using h_minkowski_left
  simpa [h_right_def] using h_result

/--
**Scalar kernel version.**
-/
theorem minkowski_inequality_convolution_scalar
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G)
    [SFinite μ] [μ.IsAddRightInvariant]
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f g : G → ℝ)
    (h_meas : AEStronglyMeasurable
      (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ))
    (h_prod : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ))
    (h_int : ∀ᵐ y ∂μ, Integrable (fun x => f (x - y) * g y) μ)
    (h_memLp : ∀ᵐ y ∂μ, MemLp (fun x => f (x - y) * g y) p μ)
    (h_norm : Integrable
      (fun y => (eLpNorm (fun x => f (x - y) * g y) p μ).toReal) μ) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) p μ ≤
    ENNReal.ofReal (∫ y, |g y| * (eLpNorm (fun x => f (x - y)) p μ).toReal ∂μ) := by
  classical
  have h_meas' : AEStronglyMeasurable
      (fun q : G × G => (g q.2) • f (q.1 - q.2)) (μ.prod μ) := by
    simpa [smul_eq_mul, mul_comm] using h_meas
  have h_prod' : Integrable (fun q : G × G => (g q.2) • f (q.1 - q.2)) (μ.prod μ) := by
    simpa [smul_eq_mul, mul_comm] using h_prod
  have h_int' : ∀ᵐ y ∂μ, Integrable (fun x => (g y) • f (x - y)) μ := by
    simpa [smul_eq_mul, mul_comm] using h_int
  have h_memLp' : ∀ᵐ y ∂μ, MemLp (fun x => (g y) • f (x - y)) p μ := by
    simpa [smul_eq_mul, mul_comm] using h_memLp
  have h_norm' : Integrable
      (fun y => (eLpNorm (fun x => (g y) • f (x - y)) p μ).toReal) μ := by
    simpa [smul_eq_mul, mul_comm] using h_norm
  have h_general :=
    minkowski_inequality_convolution (μ := μ) (p := p)
      hp hp_ne_top (f := f) (g := g)
      h_meas' h_prod' h_int' h_memLp' h_norm'
  simpa [smul_eq_mul, mul_comm] using h_general

end MinkowskiConvolution

section ConvolutionPreparatory

variable {G : Type*}
variable [NormedAddCommGroup G] [MeasurableSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]
variable (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]

/--
Almost everywhere measurability of the convolution kernel produced from `L^p` data. This lemma
packages the hypotheses needed to apply Minkowski's integral inequality in the Young inequality
arguments.
-/
lemma convolution_kernel_aestronglyMeasurable
    (f g : G → ℂ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
  classical
  have hf_aemeas : AEMeasurable f μ := hf.aemeasurable
  have hg_aemeas : AEMeasurable g μ := hg.aemeasurable
  have h_sub_qmp :
      Measure.QuasiMeasurePreserving (fun q : G × G => q.1 - q.2)
        (μ.prod μ) μ := by
    have h_sub_prod :
        MeasurePreserving (fun q : G × G => (q.1 - q.2, q.2))
          (μ.prod μ) (μ.prod μ) :=
      measurePreserving_sub_prod (μ := μ) (ν := μ)
    have h_fst_qmp :
        Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
          (μ.prod μ) μ :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
    have h_comp := h_fst_qmp.comp h_sub_prod.quasiMeasurePreserving
    simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
      using h_comp
  have hf_prod_aemeas :
      AEMeasurable (fun q : G × G => f (q.1 - q.2)) (μ.prod μ) :=
    hf_aemeas.comp_quasiMeasurePreserving h_sub_qmp
  have hg_prod_aemeas :
      AEMeasurable (fun q : G × G => g q.2) (μ.prod μ) :=
    hg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have h_mul_aemeas :
      AEMeasurable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
    have := hf_prod_aemeas.mul hg_prod_aemeas
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  exact h_mul_aemeas.aestronglyMeasurable

/--
Integrability of the convolution kernel assuming the factors themselves are integrable. This is the
basic input needed for the convolution estimates below.
-/
lemma convolution_kernel_integrable
    (f g : G → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
  classical
  -- Basic measurability for the kernel
  have h_meas : AEStronglyMeasurable
      (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) :=
    convolution_kernel_aestronglyMeasurable (μ := μ)
      f g hf.aestronglyMeasurable hg.aestronglyMeasurable
  -- Work with the nonnegative integrand built from the norms of `f` and `g`.
  set Af : G → ℝ≥0∞ := fun x => ‖f x‖ₑ
  set Ag : G → ℝ≥0∞ := fun y => ‖g y‖ₑ
  have hAf_aemeas : AEMeasurable Af μ :=
    hf.aestronglyMeasurable.enorm
  have hAg_aemeas : AEMeasurable Ag μ :=
    hg.aestronglyMeasurable.enorm
  have hAf_lt_top : (∫⁻ x, Af x ∂μ) < ∞ := by
    simpa [Af, HasFiniteIntegral]
      using hf.hasFiniteIntegral
  have hAg_lt_top : (∫⁻ y, Ag y ∂μ) < ∞ := by
    simpa [Ag, HasFiniteIntegral]
      using hg.hasFiniteIntegral
  -- Express the norm of the kernel pointwise in terms of `Af` and `Ag`.
  have h_norm_rewrite :
      (∫⁻ q : G × G, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ))
        = ∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ) := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro q
    simp [Af, Ag, norm_mul, ENNReal.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
  -- Change variables via the measure-preserving map `(x, y) ↦ (x - y, y)`.
  set τ : G × G → G × G := fun q => (q.1 - q.2, q.2)
  have h_pres : MeasurePreserving τ (μ.prod μ) (μ.prod μ) :=
    measurePreserving_sub_prod (μ := μ) (ν := μ)
  have h_map : Measure.map τ (μ.prod μ) = μ.prod μ := h_pres.map_eq
  have hAf_prod_aemeas :
      AEMeasurable (fun q : G × G => Af q.1) (μ.prod μ) :=
    hAf_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
  have hAg_prod_aemeas :
      AEMeasurable (fun q : G × G => Ag q.2) (μ.prod μ) :=
    hAg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have h_prod_aemeas :
      AEMeasurable (fun q : G × G => Af q.1 * Ag q.2) (μ.prod μ) :=
    hAf_prod_aemeas.mul hAg_prod_aemeas
  have h_change :
      ∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ)
        = ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ) := by
    have h_integrand_map :
        AEMeasurable (fun q : G × G => Af q.1 * Ag q.2)
          (Measure.map τ (μ.prod μ)) := by
      simpa [h_map]
        using h_prod_aemeas
    have h_comp :=
      lintegral_map' h_integrand_map
        (aemeasurable_id'.comp_measurable h_pres.measurable)
    have h_comp' :
        ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ q, Af (τ q).1 * Ag (τ q).2 ∂(μ.prod μ) := by
      simpa [τ, h_map]
        using h_comp
    simpa [τ]
      using h_comp'.symm
  -- Evaluate the remaining product integral via Tonelli.
  have h_tonelli :=
    MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
      (f := fun q : G × G => Af q.1 * Ag q.2) h_prod_aemeas
  have h_const_mul :
      ∀ x : G, ∫⁻ y, Af x * Ag y ∂μ = Af x * ∫⁻ y, Ag y ∂μ := by
    intro x
    simpa using
      (lintegral_const_mul'' (μ := μ)
        (r := Af x) (f := Ag) hAg_aemeas)
  have h_split :
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
        = ∫⁻ x : G, ∫⁻ y : G, Af x * Ag y ∂μ ∂μ := by
    simpa [Function.uncurry]
      using h_tonelli
  have h_point :
      (fun x : G => ∫⁻ y, Af x * Ag y ∂μ)
        = fun x : G => Af x * ∫⁻ y, Ag y ∂μ := by
    funext x
    exact h_const_mul x
  have h_outer :
      ∫⁻ x : G, Af x * ∫⁻ y : G, Ag y ∂μ ∂μ
        = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := by
    simpa [mul_comm]
      using
        (lintegral_mul_const'' (μ := μ)
          (r := ∫⁻ y, Ag y ∂μ) (f := Af) hAf_aemeas)
  have h_lintegral_prod :
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    calc
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ x : G, ∫⁻ y : G, Af x * Ag y ∂μ ∂μ := h_split
      _ = ∫⁻ x : G, Af x * ∫⁻ y : G, Ag y ∂μ ∂μ := by
            simp [h_point]
      _ = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := h_outer
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
            simp [mul_comm]
  -- Collect the previous computations to bound the kernel integral.
  have h_kernel_lintegral :
      (∫⁻ q : G × G, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ))
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    calc
      ∫⁻ q, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ)
          = ∫⁻ q, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ) := h_norm_rewrite
      _ = ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ) := h_change
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := h_lintegral_prod
  have h_aux :
      (∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ)) < ∞ := by
    simpa [h_change, h_lintegral_prod]
      using ENNReal.mul_lt_top hAf_lt_top hAg_lt_top
  have h_kernel_fin :
      (∫⁻ q : G × G, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ)) < ∞ := by
    simpa [h_norm_rewrite]
      using h_aux
  exact ⟨h_meas, h_kernel_fin⟩

/--
Norm control for the fibrewise convolution kernels required in Minkowski's inequality. This will be
used to verify the integrability of the `L^p`-norms appearing in the convolution estimates.
-/
lemma convolution_kernel_norm_integrable
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddRightInvariant]
    (f g : G → ℂ)
    (p : ℝ≥0∞)
    (hf : MemLp f p μ) (hg : Integrable g μ) :
    Integrable
      (fun y => (eLpNorm (fun x => f (x - y) * g y) p μ).toReal) μ := by
  classical
  -- Record basic integrability information coming from the `MemLp` hypotheses.
  have hg_norm_integrable : Integrable (fun y => ‖g y‖) μ := by
    simpa using hg.norm
  -- Translation invariance shows the fiberwise `L^p` norm of `f` does not depend on `y`.
  have h_shift : ∀ y : G, eLpNorm (fun x => f (x - y)) p μ = eLpNorm f p μ := by
    intro y
    have h_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using measurePreserving_add_right (μ := μ) (-y)
    simpa [Function.comp, sub_eq_add_neg]
      using
        (eLpNorm_comp_measurePreserving (μ := μ) (ν := μ) (p := p)
          hf.aestronglyMeasurable h_pres)
  -- Scaling out the constant `g y` from the fibrewise integral.
  have h_scaling :
      ∀ y : G,
        eLpNorm (fun x => f (x - y) * g y) p μ =
          ENNReal.ofReal ‖g y‖ * eLpNorm (fun x => f (x - y)) p μ := by
    intro y
    simpa [smul_eq_mul, mul_comm]
      using
        (eLpNorm_const_smul (μ := μ) (p := p) (c := g y)
          (f := fun x => f (x - y)))
  -- Identify the integrand explicitly as `|g y|` times a constant.
  set C : ℝ := (eLpNorm f p μ).toReal
  have h_pointwise :
      ∀ᵐ y ∂μ,
        (eLpNorm (fun x => f (x - y) * g y) p μ).toReal = C * ‖g y‖ := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have h_prod :
        eLpNorm (fun x => f (x - y) * g y) p μ
            = ENNReal.ofReal ‖g y‖ * eLpNorm f p μ := by
      simpa [h_shift y] using h_scaling y
    have h_mul_toReal :
        (ENNReal.ofReal ‖g y‖ * eLpNorm f p μ).toReal
            = ‖g y‖ * C := by
      have h_ofReal_ne_top : (ENNReal.ofReal ‖g y‖) ≠ ∞ := by simp
      calc
        (ENNReal.ofReal ‖g y‖ * eLpNorm f p μ).toReal
            = (ENNReal.ofReal ‖g y‖).toReal * (eLpNorm f p μ).toReal := by
              simp [ENNReal.toReal_mul, h_ofReal_ne_top, hf.eLpNorm_ne_top]
        _ = ‖g y‖ * C := by simp [C]
    calc
      (eLpNorm (fun x => f (x - y) * g y) p μ).toReal
          = (ENNReal.ofReal ‖g y‖ * eLpNorm f p μ).toReal := by simp [h_prod]
      _ = ‖g y‖ * C := h_mul_toReal
      _ = C * ‖g y‖ := by simp [mul_comm]
  -- The right-hand side is integrable because it is a constant multiple of `|g y|`.
  set majorant : G → ℝ := fun y => C * ‖g y‖
  have h_majorant_integrable : Integrable majorant μ := by
    simpa [majorant, mul_comm, mul_left_comm, mul_assoc]
      using hg_norm_integrable.mul_const C
  -- Conclude by identifying both functions almost everywhere.
  have h_ae_eq :
      (fun y => (eLpNorm (fun x => f (x - y) * g y) p μ).toReal)
        =ᵐ[μ] majorant :=
    h_pointwise.mono fun y hy => by
      have h_majorant : C * ‖g y‖ = majorant y := by
        simp [majorant]
      exact hy.trans h_majorant
  exact h_majorant_integrable.congr h_ae_eq.symm

lemma memLp_convolution_left_of_memLp
    [IsFiniteMeasure μ] {p : ℝ≥0∞} {f : G → ℂ} (hf : MemLp f p μ) :
    MemLp (fun q : G × G => f (q.1 - q.2)) p (μ.prod μ) := by
  classical
  have hμ_ne_top : μ Set.univ ≠ ∞ := by
    exact ne_of_lt (measure_lt_top μ Set.univ)
  let τ : G × G → G × G := fun q => (q.1 - q.2, q.2)
  have hτ_pres : MeasurePreserving τ (μ.prod μ) (μ.prod μ) := by
    simpa [τ] using (measurePreserving_sub_prod (μ := μ) (ν := μ))
  have h_map_fst :
      Measure.map Prod.fst (μ.prod μ) = (μ Set.univ) • μ := by
    simp
  have hf_scaled : MemLp f p ((μ Set.univ) • μ) :=
    hf.smul_measure hμ_ne_top
  have hf_prod_fst : MemLp (fun q : G × G => f q.1) p (μ.prod μ) := by
    have hf_map : MemLp f p (Measure.map Prod.fst (μ.prod μ)) := by
      simpa [h_map_fst] using hf_scaled
    have hf_meas : AEStronglyMeasurable f (Measure.map Prod.fst (μ.prod μ)) :=
      hf_map.aestronglyMeasurable
    have hfst_meas : AEMeasurable Prod.fst (μ.prod μ) :=
      measurable_fst.aemeasurable
    have :=
      (memLp_map_measure_iff (μ := μ.prod μ) (p := p)
          (g := f) (f := Prod.fst) hf_meas hfst_meas).1 hf_map
    simpa using this
  have hf_comp :
      MemLp ((fun q : G × G => f q.1) ∘ τ) p (μ.prod μ) :=
    hf_prod_fst.comp_measurePreserving hτ_pres
  simpa [Function.comp, τ, sub_eq_add_neg] using hf_comp

lemma memLp_convolution_right_of_memLp
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [IsFiniteMeasure μ]
    {q : ℝ≥0∞} {g : G → ℂ} (hg : MemLp g q μ) :
    MemLp (fun r : G × G => g r.2) q (μ.prod μ) := by
  classical
  have hμ_ne_top : μ Set.univ ≠ ∞ := by
    exact (measure_lt_top μ Set.univ).ne
  have h_map_snd : Measure.map Prod.snd (μ.prod μ) = (μ Set.univ) • μ := by
    simp
  have hg_scaled : MemLp g q ((μ Set.univ) • μ) :=
    hg.smul_measure hμ_ne_top
  have hg_map : MemLp g q (Measure.map Prod.snd (μ.prod μ)) := by
    simpa [h_map_snd] using hg_scaled
  have hg_meas : AEStronglyMeasurable g (Measure.map Prod.snd (μ.prod μ)) :=
    hg_map.aestronglyMeasurable
  have hsnd_meas : AEMeasurable Prod.snd (μ.prod μ) :=
    measurable_snd.aemeasurable
  have :=
      (memLp_map_measure_iff (μ := μ.prod μ) (p := q)
        (g := g) (f := Prod.snd) hg_meas hsnd_meas).1 hg_map
  simpa using this

lemma convolution_kernel_integrable_of_memLp
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [IsFiniteMeasure μ]
    [μ.IsAddRightInvariant] {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {f g : G → ℂ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
  classical
  have hf_L1 : MemLp f 1 μ := hf.mono_exponent (p := (1 : ℝ≥0∞)) (q := p) hp
  have hg_L1 : MemLp g 1 μ := hg.mono_exponent (p := (1 : ℝ≥0∞)) (q := q) hq
  have hf_int : Integrable f μ := (memLp_one_iff_integrable).1 hf_L1
  have hg_int : Integrable g μ := (memLp_one_iff_integrable).1 hg_L1
  have h := convolution_kernel_integrable (μ := μ) (f := f) (g := g) hf_int hg_int
  change Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)
  exact h

lemma convolution_kernel_fiber_integrable_of_memLp
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [IsFiniteMeasure μ]
    [μ.IsAddRightInvariant] {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {f g : G → ℂ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ∀ᵐ y ∂μ, Integrable (fun x => f (x - y) * g y) μ := by
  classical
  have hf_L1 : MemLp f 1 μ := hf.mono_exponent (p := (1 : ℝ≥0∞)) (q := p) hp
  have hg_L1 : MemLp g 1 μ := hg.mono_exponent (p := (1 : ℝ≥0∞)) (q := q) hq
  have hf_int : Integrable f μ := (memLp_one_iff_integrable).1 hf_L1
  have hg_int : Integrable g μ := (memLp_one_iff_integrable).1 hg_L1
  have h_kernel : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) :=
    convolution_kernel_integrable (μ := μ) (f := f) (g := g) hf_int hg_int
  have h_fiber := Integrable.prod_left_ae (μ := μ) (ν := μ) h_kernel
  refine h_fiber.mono ?_
  intro y hy
  simpa [sub_eq_add_neg] using hy

lemma convolution_kernel_fiber_memLp_of_memLp
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    {p q : ℝ≥0∞} {f g : G → ℂ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ∀ᵐ y ∂μ, MemLp (fun x => f (x - y) * g y) p μ := by
  classical
  refine Filter.Eventually.of_forall ?_
  intro y
  have hg_meas : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have h_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using measurePreserving_add_right (μ := μ) (-y)
  have h_translate : MemLp (fun x : G => f (x - y)) p μ :=
    hf.comp_measurePreserving h_pres
  have h_const : MemLp (fun x : G => g y * f (x - y)) p μ :=
    h_translate.const_mul (g y)
  simpa [mul_comm, sub_eq_add_neg, mul_left_comm, mul_assoc] using h_const

lemma convolution_kernel_norm_integrable_of_memLp
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [IsFiniteMeasure μ]
    [μ.IsAddRightInvariant] {p q : ℝ≥0∞} (hq : 1 ≤ q)
    {f g : G → ℂ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun y => (eLpNorm (fun x => f (x - y) * g y) p μ).toReal) μ := by
  classical
  have hg_L1 : MemLp g 1 μ := hg.mono_exponent (p := (1 : ℝ≥0∞)) (q := q) hq
  have hg_int : Integrable g μ := (memLp_one_iff_integrable).1 hg_L1
  simpa [sub_eq_add_neg] using
    convolution_kernel_norm_integrable (μ := μ) (f := f) (g := g) (p := p) hf hg_int

end ConvolutionPreparatory

section AuxiliaryLemmas

/--
**Jensen's inequality for integrals with convex functions.**

Assuming `μ` is a probability measure and both `f` and `φ ∘ f` are integrable, Jensen yields the
stated inequality. This formulation is sufficient for the applications in this file.
-/
theorem jensen_integral_convex
    [IsProbabilityMeasure μ]
    {f : α → ℝ}
    (hf : Integrable f μ) (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.univ) φ) (hφ_cont : Continuous φ)
    (hφ_int : Integrable (fun x => φ (f x)) μ) :
    φ (∫ x, f x ∂μ) ≤ ∫ x, φ (f x) ∂μ := by
  classical
  have h_contOn : ContinuousOn φ (Set.univ : Set ℝ) := hφ_cont.continuousOn
  have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have h_mem : ∀ᵐ x ∂μ, f x ∈ (Set.univ : Set ℝ) :=
    ae_of_all _ fun _ => trivial
  simpa [Function.comp] using
    hφ.map_integral_le (μ := μ) (f := f) (g := φ)
      h_contOn h_closed h_mem hf hφ_int

/--
**Power function is convex for p ≥ 1.**

The function x ↦ |x|^p is convex for p ≥ 1.
-/
theorem abs_pow_convex
    {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ (Set.univ) (fun x : ℝ => |x| ^ p) := by
  classical
  have hp_nonneg : 0 ≤ p := (zero_le_one.trans hp)
  -- The image of `x ↦ ‖x‖` is the nonnegative reals.
  have h_range : Set.range (fun x : ℝ => |x|) = Set.Ici (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      simp [Set.mem_Ici]
    · intro hx
      have hx' : 0 ≤ x := by simpa [Set.mem_Ici] using hx
      refine ⟨x, ?_⟩
      simp [abs_of_nonneg hx']
  have h_image_range :
      (fun x : ℝ => ‖x‖) '' (Set.univ : Set ℝ) = Set.range (fun x : ℝ => |x|) := by
    simp [Set.image_univ, Real.norm_eq_abs]
  -- Convexity of the base function `x ↦ ‖x‖`.
  have h_base : ConvexOn ℝ (Set.univ : Set ℝ) fun x : ℝ => ‖x‖ := convexOn_univ_norm
  -- Convexity of the exponent function on the nonnegative reals.
  have h_exp :
      ConvexOn ℝ ((fun x : ℝ => ‖x‖) '' (Set.univ : Set ℝ))
        (fun t : ℝ => t ^ p) := by
    simpa [h_image_range, h_range] using (convexOn_rpow (p := p) hp)
  -- Monotonicity of the exponent function on the relevant image.
  have h_mono :
      MonotoneOn (fun t : ℝ => t ^ p)
        ((fun x : ℝ => ‖x‖) '' (Set.univ : Set ℝ)) := by
    simpa [h_image_range, h_range] using
      (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (r := p) hp_nonneg)
  -- Compose the two convex functions.
  have h_comp :
      ConvexOn ℝ (Set.univ : Set ℝ)
        (fun x : ℝ => (‖x‖) ^ p) :=
    ConvexOn.comp h_exp h_base h_mono
  simpa [Real.norm_eq_abs] using h_comp

/--
**Translation preserves L^p norm for Haar measure.**

For Haar measure, ‖f(· - y)‖_p = ‖f‖_p for all y.
-/
theorem eLpNorm_comp_add_right
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G)
    [SFinite μ] [μ.IsAddRightInvariant]
    (f : G → E)
    (y : G)
    (p : ℝ≥0∞)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f (x + y)) p μ = eLpNorm f p μ := by
  classical
  have h_pres : MeasurePreserving (fun x : G => x + y) μ μ :=
    measurePreserving_add_right (μ := μ) y
  simpa [Function.comp] using
    (eLpNorm_comp_measurePreserving (μ := μ) (ν := μ) (p := p) hf h_pres)

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
  classical
  have hf_prod :
      AEMeasurable (Function.uncurry fun x y : G => f (x - y)) (μ.prod μ) := by
    have h_sub_qmp :
        Measure.QuasiMeasurePreserving (fun z : G × G => z.1 - z.2)
          (μ.prod μ) μ := by
      have h_measPres :
          MeasurePreserving (fun z : G × G => (z.1 - z.2, z.2))
            (μ.prod μ) (μ.prod μ) :=
        measurePreserving_sub_prod (μ := μ) (ν := μ)
      have h_fst :
          Measure.QuasiMeasurePreserving (fun z : G × G => z.1)
            (μ.prod μ) μ :=
        MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
      simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
        using h_fst.comp h_measPres.quasiMeasurePreserving
    have hf_prod' :
        AEMeasurable (fun z : G × G => f (z.1 - z.2)) (μ.prod μ) :=
      hf.comp_quasiMeasurePreserving h_sub_qmp
    simpa [Function.uncurry] using hf_prod'
  have hg_prod :
      AEMeasurable (Function.uncurry fun _ y : G => g y) (μ.prod μ) := by
    have hg_prod' :
        AEMeasurable (fun z : G × G => g z.2) (μ.prod μ) :=
      hg.comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
    simpa [Function.uncurry] using hg_prod'
  have h_prod_meas :
      AEMeasurable (Function.uncurry fun x y : G => f (x - y) * g y) (μ.prod μ) := by
    have := hf_prod.mul hg_prod
    simpa [Function.uncurry, mul_comm, mul_left_comm, mul_assoc]
      using this
  simpa using
    MeasureTheory.lintegral_lintegral_swap (μ := μ) (ν := μ) h_prod_meas

end AuxiliaryLemmas
