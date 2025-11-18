import Frourio.Analysis.SchwartzDensityLp.SchwartzDensityLpCore0
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.Algebra.Support

/-!
# Cauchy-Schwarz inequality for compactly supported functions

This file contains the standard textbook result relating L¹ and L² norms
for functions with compact support.

## Main results

- `eLpNorm_one_le_eLpNorm_two_mul_sqrt_measure`: The fundamental inequality
  ‖f‖₁ ≤ ‖f‖₂ · √(μ(support f)) for compactly supported functions.

- `eLpNorm_one_le_eLpNorm_two_mul_sqrt_measure_set`: The same inequality
  restricted to a measurable set E with finite measure.

## References

This is a standard result found in:
- Rudin, "Real and Complex Analysis", Chapter 3
- Folland, "Real Analysis", Chapter 6
- Brezis, "Functional Analysis, Sobolev Spaces and Partial Differential Equations"

The general form is:
  ‖f‖_p ≤ ‖f‖_q · (μ(E))^(1/p - 1/q) for p < q and μ(E) < ∞

Our specific case is p=1, q=2 on the support of f.
-/

open MeasureTheory
open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/--
**Cauchy-Schwarz inequality for L^p spaces on sets of finite measure.**

For a function f supported on a set E with finite measure, we have:
  ‖f‖₁ ≤ ‖f‖₂ · √(μ(E))

This is the standard textbook result, a special case (p=1, q=2) of:
  ‖f‖_p ≤ ‖f‖_q · (μ(E))^(1/p - 1/q) for p ≤ q

## Mathematical content

Given:
- f : α → E, a measurable function
- E : Set α, a measurable set with μ(E) < ∞
- supp(f) ⊆ E (f is supported on E)

Then: ∫ ‖f‖ dμ ≤ (∫ ‖f‖² dμ)^(1/2) · √(μ(E))

## Proof strategy

Apply Hölder's inequality to f and the constant function 1:
  ∫_E |f · 1| dμ ≤ ‖f‖_L²(E) · ‖1‖_L²(E)
                = ‖f‖_L²(E) · √(μ(E))
-/
theorem eLpNorm_one_le_eLpNorm_two_mul_sqrt_measure_set
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    {s : Set α} (hs : MeasurableSet s) (hs_finite : μ s < ∞)
    (h_supp : ∀ x ∉ s, f x = 0) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ * ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) := by
  classical
  have h_support_subset : Function.support f ⊆ s := by
    intro x hx
    have hx' : f x ≠ 0 := hx
    by_contra hx_mem
    exact hx' (h_supp x hx_mem)
  have hs_ne_top : μ s ≠ ∞ := ne_of_lt hs_finite
  by_cases hμs_zero : μ s = 0
  · have hf_indicator : Set.indicator s f = f := by
      funext x
      by_cases hx : x ∈ s
      · simp [hx]
      · simp [hx, h_supp x hx]
    have h_indicator :=
      eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := (1 : ℝ≥0∞))
        (s := s) (f := f) hs
    have h_restrict_zero : μ.restrict s = (0 : Measure α) :=
      Measure.restrict_eq_zero.2 hμs_zero
    have h_eLp_zero : eLpNorm f 1 μ = 0 := by
      rw [← hf_indicator, h_indicator, h_restrict_zero]
      exact eLpNorm_measure_zero
    have h_factor_zero : ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) = 0 := by
      have h_toReal : (μ s).toReal = 0 := by simp [hμs_zero]
      simp [h_toReal]
    simp [h_eLp_zero, h_factor_zero]
  have hμs_ne_zero : μ s ≠ 0 := by intro h; exact hμs_zero h
  by_cases hf_top : eLpNorm f 2 μ = ∞
  · have h_toReal_pos : 0 < (μ s).toReal :=
      ENNReal.toReal_pos hμs_ne_zero hs_ne_top
    have h_factor_pos : ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) ≠ 0 := by
      have h_pos : 0 < (μ s).toReal ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos h_toReal_pos _
      exact ENNReal.ofReal_pos.2 h_pos |>.ne'
    calc eLpNorm f 1 μ
        ≤ ⊤ := le_top
      _ = ⊤ * ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) :=
          (ENNReal.top_mul h_factor_pos).symm
      _ = eLpNorm f 2 μ * ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) := by
          rw [hf_top]
  let φ : α → ℂ := fun x => (‖f x‖ : ℂ)
  let ψ : α → ℂ := s.indicator fun _ => (1 : ℂ)
  have hφ_meas : AEStronglyMeasurable φ μ :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.norm)
  have hψ_memLp : MemLp ψ 2 μ := by
    refine memLp_indicator_const (μ := μ) (p := (2 : ℝ≥0∞)) hs (1 : ℂ) ?_
    exact Or.inr hs_ne_top
  have hφ_mul : ∀ x, φ x = φ x * ψ x := by
    intro x; by_cases hx : x ∈ s
    · simp [φ, ψ, hx]
    · have hx_zero : f x = 0 := h_supp x hx
      simp [φ, ψ, hx, hx_zero]
  have hφ_norm_ae : ∀ᵐ x ∂μ, ‖φ x‖ = ‖f x‖ :=
    Filter.Eventually.of_forall (fun x => by simp [φ])
  have hφ_eLp_one : eLpNorm φ 1 μ = eLpNorm f 1 μ :=
    eLpNorm_congr_norm_ae hφ_norm_ae
  have hφ_eLp_two : eLpNorm φ 2 μ = eLpNorm f 2 μ :=
    eLpNorm_congr_norm_ae hφ_norm_ae
  have h_holder : eLpNorm (φ * ψ) 1 μ ≤ eLpNorm φ 2 μ * eLpNorm ψ 2 μ := by
    classical
    have hψ_meas : AEStronglyMeasurable ψ μ := hψ_memLp.1
    haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) := by
      simpa using
        (ENNReal.HolderConjugate.instTwoTwo : ENNReal.HolderConjugate (2 : ℝ≥0∞) 2)
    simpa [Pi.mul_def, Pi.smul_def] using
      (MeasureTheory.eLpNorm_smul_le_mul_eLpNorm (μ := μ)
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
        (f := ψ) (φ := φ) (hf := hψ_meas) (hφ := hφ_meas))
  have hψ_indicator :=
    eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := (2 : ℝ≥0∞))
      (s := s) (f := fun _ : α => (1 : ℂ)) hs
  have hμ_restrict_ne_zero : μ.restrict s ≠ (0 : Measure α) := by
    intro h
    exact hμs_ne_zero (Measure.restrict_eq_zero.1 h)
  have hψ_norm : eLpNorm ψ 2 μ = (μ s) ^ (1 / 2 : ℝ) := by
    have h_const :=
      eLpNorm_const (μ := μ.restrict s) (p := (2 : ℝ≥0∞)) (c := (1 : ℂ))
        (by norm_num) hμ_restrict_ne_zero
    have h_univ : (μ.restrict s) Set.univ = μ s := by
      simp [Measure.restrict_apply, hs, Set.inter_univ]
    simpa [ψ, h_univ] using (hψ_indicator.trans h_const)
  have h_pow_eq :
      (μ s) ^ (1 / 2 : ℝ) = ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) := by
    have h_base : μ s = ENNReal.ofReal (μ s).toReal := (ENNReal.ofReal_toReal hs_ne_top).symm
    have h_nonneg : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
    have h_rpow :=
      ENNReal.ofReal_rpow_of_nonneg (x := (μ s).toReal) (p := (1 / 2 : ℝ))
        h_nonneg (by positivity)
    have h_pow_base := congrArg (fun t : ℝ≥0∞ => t ^ (1 / 2 : ℝ)) h_base
    calc
      (μ s) ^ (1 / 2 : ℝ)
          = (ENNReal.ofReal (μ s).toReal) ^ (1 / 2 : ℝ) := h_pow_base
      _ = ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) := by
          simpa using h_rpow
  have h_main :
      eLpNorm φ 1 μ ≤ eLpNorm φ 2 μ * (μ s) ^ (1 / 2 : ℝ) := by
    have h_funext : φ = φ * ψ := funext fun x => by
      simpa [Pi.mul_def] using hφ_mul x
    have h_eq : eLpNorm φ 1 μ = eLpNorm (φ * ψ) 1 μ :=
      congrArg (fun g => eLpNorm g 1 μ) h_funext
    have h_main' : eLpNorm φ 1 μ ≤ eLpNorm φ 2 μ * eLpNorm ψ 2 μ :=
      h_eq ▸ h_holder
    simpa [hψ_norm] using h_main'
  calc eLpNorm f 1 μ
      = eLpNorm φ 1 μ := hφ_eLp_one.symm
    _ ≤ eLpNorm φ 2 μ * (μ s) ^ (1 / 2 : ℝ) := h_main
    _ = eLpNorm f 2 μ * (μ s) ^ (1 / 2 : ℝ) := by rw [← hφ_eLp_two]
    _ = eLpNorm f 2 μ * ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) := by rw [← h_pow_eq]

/--
**Cauchy-Schwarz for compactly supported functions.**

If f has compact support, then:
  ‖f‖₁ ≤ ‖f‖₂ · √(vol(tsupport f))

This is a direct corollary of the previous theorem, using that
the topological support of a compactly supported function has finite measure.
-/
theorem eLpNorm_one_le_eLpNorm_two_mul_sqrt_tsupport
    [TopologicalSpace α] [BorelSpace α]
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    (h_finite : μ (tsupport f) < ∞) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ * ENNReal.ofReal ((μ (tsupport f)).toReal ^ (1 / 2 : ℝ)) := by
  classical
  have hs_meas : MeasurableSet (tsupport f) :=
    (isClosed_tsupport _).measurableSet
  have h_zero : ∀ x ∉ tsupport f, f x = 0 := by
    intro x hx
    have hx_not_support : x ∉ Function.support f := fun hx_support =>
      hx (subset_closure hx_support)
    have : ¬ f x ≠ 0 := by
      intro hx_ne
      exact hx_not_support (by simp [Function.support, Set.mem_setOf_eq, hx_ne])
    exact not_not.mp this
  have :=
    eLpNorm_one_le_eLpNorm_two_mul_sqrt_measure_set
      (μ := μ) (f := f) hf hs_meas h_finite h_zero
  simpa using this

/--
**Variant with ENNReal for the measure term.**

Sometimes it's more convenient to work with ENNReal directly.
This version states:
  ‖f‖₁ ≤ ‖f‖₂ · (μ s)^(1/2)
where the exponentiation is in ENNReal.
-/
theorem eLpNorm_one_le_eLpNorm_two_mul_rpow_measure_set
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    {s : Set α} (hs : MeasurableSet s) (hs_finite : μ s < ∞)
    (h_supp : ∀ x ∉ s, f x = 0) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ * (μ s) ^ (1 / 2 : ℝ) := by
  classical
  have h :=
    eLpNorm_one_le_eLpNorm_two_mul_sqrt_measure_set (μ := μ) (f := f)
      hf hs hs_finite h_supp
  calc eLpNorm f 1 μ
      ≤ eLpNorm f 2 μ * ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) := h
    _ = eLpNorm f 2 μ * (μ s) ^ (1 / 2 : ℝ) := by
        congr 1
        have h_nonneg : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
        have h_rpow := ENNReal.ofReal_rpow_of_nonneg h_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ))
        have h_base : μ s = ENNReal.ofReal (μ s).toReal :=
          (ENNReal.ofReal_toReal (ne_of_lt hs_finite)).symm
        calc ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ))
            = (ENNReal.ofReal (μ s).toReal) ^ (1 / 2 : ℝ) := h_rpow.symm
          _ = (μ s) ^ (1 / 2 : ℝ) := by rw [← h_base]

/--
**Application: Bounding L¹ error by L² error for compact support.**

This is the form most directly useful for our density approximation:

Given:
- f, g both with compact support
- ‖f - g‖₂ ≤ ε
- The support of f - g is contained in a set of measure M

Then: ‖f - g‖₁ ≤ ε · √M

This is exactly what we need for the mollifier approximation theorem.
-/
theorem eLpNorm_sub_one_le_eLpNorm_sub_two_of_compact_support
    [TopologicalSpace α] [BorelSpace α]
    {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    {ε : ℝ≥0∞} (h_L2 : eLpNorm (f - g) 2 μ ≤ ε)
    (h_supp_measure : μ (tsupport f ∪ tsupport g) < ∞) :
    eLpNorm (f - g) 1 μ ≤ ε * (μ (tsupport f ∪ tsupport g)) ^ (1 / 2 : ℝ) := by
  classical
  set s := tsupport f ∪ tsupport g
  have hs_meas : MeasurableSet s :=
    (isClosed_tsupport _).measurableSet.union (isClosed_tsupport _).measurableSet
  have hf_zero : ∀ x ∉ tsupport f, f x = 0 := by
    intro x hx
    simpa using image_eq_zero_of_notMem_tsupport hx
  have hg_zero : ∀ x ∉ tsupport g, g x = 0 := by
    intro x hx
    simpa using image_eq_zero_of_notMem_tsupport hx
  have h_sub_zero : ∀ x ∉ s, f x - g x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport f ∧ x ∉ tsupport g := by
      simpa [s, Set.mem_union, not_or] using hx
    have hx_f : f x = 0 := hf_zero x hx'.1
    have hx_g : g x = 0 := hg_zero x hx'.2
    simp [s, hx_f, hx_g]
  have h_meas_sub : AEStronglyMeasurable (fun x => f x - g x) μ := hf.sub hg
  have h_bound :=
    eLpNorm_one_le_eLpNorm_two_mul_rpow_measure_set (μ := μ)
      (f := fun x => f x - g x) h_meas_sub hs_meas h_supp_measure h_sub_zero
  calc eLpNorm (f - g) 1 μ
      ≤ eLpNorm (f - g) 2 μ * (μ s) ^ (1 / 2 : ℝ) := h_bound
    _ ≤ ε * (μ s) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right h_L2 (by positivity : 0 ≤ (μ s) ^ (1 / 2 : ℝ))

/--
**Quantitative version: if the measure is bounded by M, we can bound the L¹ norm.**

If μ(support) ≤ M and ‖f - g‖₂ ≤ ε, then ‖f - g‖₁ ≤ ε · √M.

This is the most practical form for applications where we know
an explicit bound on the support measure.
-/
theorem eLpNorm_sub_one_le_of_eLpNorm_sub_two_le_of_measure_le
    [TopologicalSpace α] [BorelSpace α] [IsFiniteMeasureOnCompacts μ]
    {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf_compact : HasCompactSupport f) (hg_compact : HasCompactSupport g)
    {ε M : ℝ} (hε_pos : 0 ≤ ε) (hM_pos : 0 ≤ M)
    (h_L2 : eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε)
    (h_measure : (μ (tsupport f ∪ tsupport g)).toReal ≤ M) :
    eLpNorm (f - g) 1 μ ≤ ENNReal.ofReal (ε * Real.sqrt M) := by
  classical
  set s := tsupport f ∪ tsupport g
  have hs_meas : MeasurableSet s :=
    (isClosed_tsupport _).measurableSet.union (isClosed_tsupport _).measurableSet
  have hs_compact : IsCompact s := hf_compact.union hg_compact
  have hs_finite : μ s < ∞ := hs_compact.measure_lt_top
  have hf_zero : ∀ x ∉ tsupport f, f x = 0 := by
    intro x hx; simpa using image_eq_zero_of_notMem_tsupport hx
  have hg_zero : ∀ x ∉ tsupport g, g x = 0 := by
    intro x hx; simpa using image_eq_zero_of_notMem_tsupport hx
  have h_sub_zero : ∀ x ∉ s, f x - g x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport f ∧ x ∉ tsupport g := by
      simpa [s, Set.mem_union, not_or] using hx
    have hx_f : f x = 0 := hf_zero x hx'.1
    have hx_g : g x = 0 := hg_zero x hx'.2
    simp [s, hx_f, hx_g]
  have h_meas_sub : AEStronglyMeasurable (fun x => f x - g x) μ := hf.sub hg
  have h_main :=
    eLpNorm_sub_one_le_eLpNorm_sub_two_of_compact_support (μ := μ) (f := f) (g := g)
      hf hg (ε := ENNReal.ofReal ε) h_L2
      (by simpa [s] using hs_finite)
  have h_pow_eq :
      (μ s) ^ (1 / 2 : ℝ) = ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) := by
    have h_nonneg : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
    have h_rpow := ENNReal.ofReal_rpow_of_nonneg h_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ))
    have h_toReal := (ENNReal.ofReal_toReal (ne_of_lt hs_finite)).symm
    have h_ofReal_toReal : (ENNReal.ofReal (μ s).toReal).toReal = (μ s).toReal := by
      rw [ENNReal.toReal_ofReal (ENNReal.toReal_nonneg)]
    rw [h_toReal, h_rpow, h_ofReal_toReal]
  have h_bound :
      eLpNorm (f - g) 1 μ
        ≤ ENNReal.ofReal ε * ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) := by
    rw [← h_pow_eq]
    simpa [s] using h_main
  have h_mul_eq :
      ENNReal.ofReal ε * ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ))
        = ENNReal.ofReal (ε * ((μ s).toReal ^ (1 / 2 : ℝ))) := by
    rw [ENNReal.ofReal_mul hε_pos]
  have h_bound' :
      eLpNorm (f - g) 1 μ
        ≤ ENNReal.ofReal (ε * ((μ s).toReal ^ (1 / 2 : ℝ))) := by
    rw [← h_mul_eq]
    exact h_bound
  have h_sqrt_le : ((μ s).toReal) ^ (1 / 2 : ℝ) ≤ Real.sqrt M := by
    have h_nonneg : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
    have h_nonneg' : 0 ≤ M := hM_pos
    rw [Real.sqrt_eq_rpow]
    have h_le : (μ s).toReal ≤ M := by simpa [s] using h_measure
    have h := Real.rpow_le_rpow h_nonneg h_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa using h
  have h_real : ε * ((μ s).toReal ^ (1 / 2 : ℝ)) ≤ ε * Real.sqrt M :=
    mul_le_mul_of_nonneg_left h_sqrt_le hε_pos
  have h_target :
      ENNReal.ofReal (ε * ((μ s).toReal ^ (1 / 2 : ℝ)))
        ≤ ENNReal.ofReal (ε * Real.sqrt M) :=
    ENNReal.ofReal_le_ofReal h_real
  exact h_bound'.trans h_target
