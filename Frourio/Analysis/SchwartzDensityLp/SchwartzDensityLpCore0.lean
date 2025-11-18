import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology

/-!
# Density of Schwartz functions in Lp spaces

This file contains fundamental density theorems about Schwartz functions
in Lp spaces, which are standard results in harmonic analysis.

## Main results

- `schwartz_dense_Lp`: Schwartz functions are dense in Lp(ℝⁿ) for 1 ≤ p < ∞
- `schwartz_dense_L1_L2_simultaneous`: Simultaneous approximation in L¹ and L²
- `continuous_compactSupport_dense_Lp`: Cc(ℝⁿ) is dense in Lp
- `smooth_compactSupport_dense_Lp`: C∞c(ℝⁿ) is dense in Lp

## References

Standard textbooks covering these results:
- Stein & Shakarchi, "Functional Analysis", Chapter 4
- Folland, "Real Analysis", Chapter 8
- Rudin, "Functional Analysis", Chapter 1
- Grafakos, "Classical Fourier Analysis", Chapter 2
- Reed & Simon, "Methods of Modern Mathematical Physics I", Section II.3

The density of Schwartz functions (or C∞c) in Lp is a cornerstone result
used throughout harmonic analysis and PDE theory.
-/

variable {n : ℕ}

/--
**Continuous compactly supported functions are dense in Lp.**

This is Theorem 3.14 in Rudin, "Real and Complex Analysis".
Also Theorem 8.14 in Folland, "Real Analysis".

For any f ∈ Lp(ℝⁿ) with 1 ≤ p < ∞ and any ε > 0, there exists
a continuous function g with compact support such that ‖f - g‖_p < ε.
-/
theorem continuous_compactSupport_dense_Lp
    (p : ℝ≥0∞)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℂ,
      Continuous g ∧
      HasCompactSupport g ∧
      MemLp g p volume ∧
      eLpNorm (f - g) p volume < ENNReal.ofReal ε := by
  -- apply the standard Lᵖ-density result for compactly supported continuous functions
  have hε_half_pos : 0 < ε / 2 := by
    have : (0 : ℝ) < 2 := by norm_num
    exact div_pos hε this
  have hε_half_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    have : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr hε_half_pos
    exact ne_of_gt this
  obtain ⟨g, hg_compact, hg_bound, hg_cont, hg_memLp⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le hp_ne_top hε_half_ne
  have h_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε := by
    have h_half_lt : ε / 2 < ε := by simpa using half_lt_self hε
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 h_half_lt
  refine ⟨g, hg_cont, hg_compact, hg_memLp, ?_⟩
  exact lt_of_le_of_lt hg_bound h_lt

/-- Auxiliary covering lemma for compact supports.
    Any compactly supported function has its topological support
    contained in some closed ball of radius at least 1. -/
lemma tsupport_subset_closedBall
    (g : (Fin n → ℝ) → ℂ) (hg_compact : HasCompactSupport g) :
    ∃ R : ℝ, tsupport g ⊆ Metric.closedBall (0 : Fin n → ℝ) R ∧ 1 ≤ R := by
  classical
  -- tsupport g is compact by assumption
  have h_compact : IsCompact (tsupport g) := hg_compact
  -- Compact sets in ℝⁿ are bounded
  have h_bounded : Bornology.IsBounded (tsupport g) := h_compact.isBounded
  -- Bounded sets can be covered by a closed ball
  obtain ⟨R₀, hR₀⟩ := h_bounded.subset_closedBall (0 : Fin n → ℝ)
  -- Take R = max(R₀, 1) to ensure R ≥ 1
  refine ⟨max R₀ 1, ?_, le_max_right R₀ 1⟩
  exact hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left R₀ 1))

lemma contDiff_implies_aestronglyMeasurable
    {φ₀ : (Fin n → ℝ) → ℂ} {m : ℕ∞}
    (hφ₀_smooth : ContDiff ℝ m φ₀) :
    AEStronglyMeasurable φ₀ (volume : Measure (Fin n → ℝ)) :=
  hφ₀_smooth.continuous.aestronglyMeasurable

lemma aestronglyMeasurable_sub_of_continuous
    {g φ₀ : (Fin n → ℝ) → ℂ}
    (hg_cont : Continuous g)
    (hφ₀_aesm : AEStronglyMeasurable φ₀ (volume : Measure (Fin n → ℝ))) :
    AEStronglyMeasurable (fun x => g x - φ₀ x) volume :=
  AEStronglyMeasurable.sub hg_cont.aestronglyMeasurable hφ₀_aesm

lemma aestronglyMeasurable_sub_of_aesm_continuous
    {φ₀ ψ : (Fin n → ℝ) → ℂ}
    (hφ₀_aesm : AEStronglyMeasurable φ₀ (volume : Measure (Fin n → ℝ)))
    (hψ_cont : Continuous ψ) :
    AEStronglyMeasurable (fun x => φ₀ x - ψ x) volume :=
  hφ₀_aesm.sub hψ_cont.aestronglyMeasurable

lemma continuous_compactSupport_memLp
    {ψ : (Fin n → ℝ) → ℂ}
    (hψ_cont : Continuous ψ)
    (hψ_support : HasCompactSupport ψ)
    (p : ℝ≥0∞) :
    MemLp ψ p (volume : Measure (Fin n → ℝ)) :=
  hψ_cont.memLp_of_hasCompactSupport (μ := volume) (p := p) hψ_support

lemma aestronglyMeasurable_sub_continuous_contDiff
    {g φ₀ : (Fin n → ℝ) → ℂ} {m : ℕ∞}
    (hg_cont : Continuous g)
    (hφ₀_smooth : ContDiff ℝ m φ₀) :
    AEStronglyMeasurable (fun x => g x - φ₀ x) (volume : Measure (Fin n → ℝ)) :=
  hg_cont.aestronglyMeasurable.sub hφ₀_smooth.continuous.aestronglyMeasurable

lemma aestronglyMeasurable_sub_contDiff_continuous
    {φ₀ ψ : (Fin n → ℝ) → ℂ} {m : ℕ∞}
    (hφ₀_smooth : ContDiff ℝ m φ₀)
    (hψ_cont : Continuous ψ) :
    AEStronglyMeasurable (fun x => φ₀ x - ψ x) (volume : Measure (Fin n → ℝ)) :=
  hφ₀_smooth.continuous.aestronglyMeasurable.sub hψ_cont.aestronglyMeasurable

lemma sub_eq_add_sub {α : Type*} [AddCommGroup α] (g φ₀ ψ : (Fin n → ℝ) → α) :
    (fun x => g x - ψ x) = (fun x => g x - φ₀ x) + fun x => φ₀ x - ψ x := by
  funext x; simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma eLpNorm_triangle_ineq_lt
    {g φ₀ ψ : (Fin n → ℝ) → ℂ}
    (p : ℝ≥0∞)
    (hp_one : 1 ≤ p)
    (hg_cont : Continuous g)
    (hφ₀_smooth : ContDiff ℝ ∞ φ₀)
    (hψ_cont : Continuous ψ)
    {ε : ℝ}
    (h_term_support : eLpNorm (fun x => g x - φ₀ x) p volume < ENNReal.ofReal (ε / 2))
    (h_term_cutoff : eLpNorm (fun x => φ₀ x - ψ x) p volume < ENNReal.ofReal (ε / 2))
    (hε_half : 0 < ε / 2) :
    eLpNorm (fun x => g x - ψ x) p volume < ENNReal.ofReal ε := by
  have h_meas₁ : AEStronglyMeasurable (fun x => g x - φ₀ x) volume :=
    aestronglyMeasurable_sub_continuous_contDiff hg_cont hφ₀_smooth
  have h_meas₂ : AEStronglyMeasurable (fun x => φ₀ x - ψ x) volume :=
    aestronglyMeasurable_sub_contDiff_continuous hφ₀_smooth hψ_cont
  have h_fun_eq :
      (fun x => g x - ψ x)
        = (fun x => g x - φ₀ x) + fun x => φ₀ x - ψ x :=
    sub_eq_add_sub g φ₀ ψ
  have h_triangle :
      eLpNorm (fun x => g x - ψ x) p volume
          ≤
        eLpNorm (fun x => g x - φ₀ x) p volume
          + eLpNorm (fun x => φ₀ x - ψ x) p volume := by
    simpa [h_fun_eq] using
      (eLpNorm_add_le (μ := volume) (p := p)
        (f := fun x => g x - φ₀ x)
        (g := fun x => φ₀ x - ψ x)
        (hf := h_meas₁) (hg := h_meas₂) hp_one)
  have h_lt0 :
      eLpNorm (fun x => g x - φ₀ x) p volume
          + eLpNorm (fun x => φ₀ x - ψ x) p volume
        < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
    ENNReal.add_lt_add h_term_support h_term_cutoff
  have h_half_nonneg : 0 ≤ ε / 2 := le_of_lt hε_half
  have h_add := ENNReal.ofReal_add h_half_nonneg h_half_nonneg
  have h_twice : ε / 2 + ε / 2 = ε := by ring
  have h_target :
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
          = ENNReal.ofReal ε := by
    calc
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
          = ENNReal.ofReal (ε / 2 + ε / 2) := by
            simpa [add_comm, add_left_comm, add_assoc] using h_add.symm
      _ = ENNReal.ofReal ε := by simp [h_twice]
  have h_sum_lt :
      eLpNorm (fun x => g x - φ₀ x) p volume
          + eLpNorm (fun x => φ₀ x - ψ x) p volume
        < ENNReal.ofReal ε := by
    simpa [h_target] using h_lt0
  exact lt_of_le_of_lt h_triangle h_sum_lt

lemma phi0_eq_zero_outside_enlarged_ball
    (φ₀ : (Fin n → ℝ) → ℂ) (R : ℝ)
    (h_support : tsupport φ₀ ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1)) :
    ∀ ⦃x : Fin n → ℝ⦄, R + 1 < ‖x‖ → φ₀ x = 0 := by
  classical
  intro x hx_norm
  have hx_not_tsupport : x ∉ tsupport φ₀ := by
    intro hx
    have hx_le : dist x (0 : (Fin n → ℝ)) ≤ R + 1 :=
      (Metric.mem_closedBall.mp (h_support hx))
    have hx_norm_le : ‖x‖ ≤ R + 1 := by
      simpa [dist_eq_norm] using hx_le
    exact (not_le_of_gt hx_norm) hx_norm_le
  by_contra h_nonzero
  have hx_support : x ∈ Function.support φ₀ := by
    simp [Function.support, h_nonzero]
  have hx_tsupport : x ∈ tsupport φ₀ := by
    have hx_closure : x ∈ closure (Function.support φ₀) := subset_closure hx_support
    simpa [tsupport] using hx_closure
  exact hx_not_tsupport hx_tsupport

/-- Approximating a continuous compactly supported function by a smooth function in `Lᵖ`. -/
theorem mollifier_compactSupport_Lp_approx
    (p : ℝ≥0∞) (hp_one : 1 ≤ p) (g : (Fin n → ℝ) → ℂ)
    (hg_cont : Continuous g) (hg_compact : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) φ ∧
      eLpNorm (fun x => g x - φ x) p volume < ENNReal.ofReal ε ∧
      MemLp φ p volume := by
  -- The proof uses the following key steps:
  -- 1. g has compact support, so it's uniformly continuous
  -- 2. Use UniformContinuous.exists_contDiff_dist_le to get a smooth approximation
  -- 3. Control the Lp error using the pointwise bound and the finite measure of the support

  -- Step 1: g is uniformly continuous
  have hg_uc : UniformContinuous g := hg_compact.uniformContinuous_of_continuous hg_cont

  -- Step 2: The support is compact and has finite measure
  have hsupp_compact : IsCompact (tsupport g) := hg_compact
  have hsupp_finite : volume (tsupport g) < (∞ : ℝ≥0∞) := hsupp_compact.measure_lt_top

  -- Step 3: Choose ε' such that pointwise approximation gives Lp bound
  -- We need to handle the case where the support has zero measure separately
  by_cases h_zero : volume (tsupport g) = 0
  · -- If support has measure zero, g = 0 a.e., so we can take φ = 0
    refine ⟨0, contDiff_const, ?_, MemLp.zero⟩
    classical
    have h_nonzero_subset : {x : (Fin n → ℝ) | g x ≠ 0} ⊆ tsupport g := by
      intro x hx
      by_contra hx'
      have hx_zero : g x = 0 := image_eq_zero_of_notMem_tsupport hx'
      exact hx hx_zero
    have h_nonzero_null : volume {x : (Fin n → ℝ) | g x ≠ 0} = 0 :=
      measure_mono_null h_nonzero_subset h_zero
    have hg_zero : g =ᵐ[volume] (0 : (Fin n → ℝ) → ℂ) := by
      have : ∀ᵐ x ∂volume, g x = 0 :=
        (ae_iff).2 (by simpa [Classical.not_not] using h_nonzero_null)
      simpa using this
    have hnorm_g : eLpNorm g p volume = 0 := by
      calc
        eLpNorm g p volume
            = eLpNorm (0 : (Fin n → ℝ) → ℂ) p volume :=
              (eLpNorm_congr_ae (μ := volume) hg_zero)
        _ = 0 := eLpNorm_zero
    have hnorm_g' : eLpNorm (fun x => g x) p volume = 0 := by
      simpa using hnorm_g
    have h_pos : 0 < ENNReal.ofReal ε := by
      simpa [ENNReal.ofReal_pos] using hε
    simpa [hnorm_g'] using h_pos

  -- Main case: support has positive measure
  · classical
    -- Step 3a: choose a bounded region covering the support and set up quantitative bounds.
    have h_tsupport_compact : IsCompact (tsupport g) := hsupp_compact
    obtain ⟨R, hR_subset, hR_ge_one⟩ := tsupport_subset_closedBall g hg_compact
    set B : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) R with hB_def
    have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_ge_one
    have hB_meas : MeasurableSet B := by
      simpa [hB_def] using (Metric.isClosed_closedBall :
        IsClosed (Metric.closedBall (0 : Fin n → ℝ) R)).measurableSet
    have hμB_lt_top : volume B < ⊤ := by
      simpa [hB_def] using
        (MeasureTheory.measure_closedBall_lt_top (x := (0 : Fin n → ℝ)) (r := R))
    have hμB_ne_top : volume B ≠ ∞ := ne_of_lt hμB_lt_top
    have hg_zero_outside : ∀ x ∉ B, g x = 0 := by
      intro x hxB
      classical
      by_contra hx_nonzero
      have hx_support : x ∈ Function.support g := by
        have : g x ≠ 0 := hx_nonzero
        simpa [Function.support] using this
      have hx_tsupport : x ∈ tsupport g := by
        have hx_closure : x ∈ closure (Function.support g) := subset_closure hx_support
        simpa [tsupport] using hx_closure
      exact hxB (hR_subset hx_tsupport)
    set S : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) (R + 1) with hS_def
    have hS_meas : MeasurableSet S := by
      simpa [hS_def] using
        (Metric.isClosed_closedBall :
          IsClosed (Metric.closedBall (0 : Fin n → ℝ) (R + 1))).measurableSet
    have hμS_lt_top : volume S < ⊤ := by
      simpa [hS_def] using
        (MeasureTheory.measure_closedBall_lt_top (x := (0 : Fin n → ℝ)) (r := R + 1))
    have hμS_ne_top : volume S ≠ ∞ := ne_of_lt hμS_lt_top
    have h_exponent_nonneg : 0 ≤ 1 / p.toReal := by
      have hp_nonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
      exact (div_nonneg zero_le_one hp_nonneg)
    have h_pow_ne_top : (volume B) ^ (1 / p.toReal) ≠ (∞ : ℝ≥0∞) :=
      ENNReal.rpow_ne_top_of_nonneg h_exponent_nonneg hμB_ne_top
    have h_powS_ne_top : (volume S) ^ (1 / p.toReal) ≠ (∞ : ℝ≥0∞) :=
      ENNReal.rpow_ne_top_of_nonneg h_exponent_nonneg hμS_ne_top
    let denom : ℝ := max 1 ((volume S) ^ (1 / p.toReal)).toReal
    have hB_subset_S : B ⊆ S := by
      intro x hx
      have hx_norm_le : ‖x‖ ≤ R := by
        simpa [B, hB_def, dist_eq_norm] using Metric.mem_closedBall.mp hx
      have hx_norm_le' : ‖x‖ ≤ R + 1 := le_trans hx_norm_le (by linarith)
      exact Metric.mem_closedBall.mpr
        (by simpa [S, hS_def, dist_eq_norm] using hx_norm_le')
    have hμB_le_S : volume B ≤ volume S :=
      measure_mono hB_subset_S
    have hdenom_pos : 0 < denom := by
      have : (1 : ℝ) ≤ denom := le_max_left _ _
      exact lt_of_lt_of_le zero_lt_one this
    have hdenom_nonneg : 0 ≤ denom := le_of_lt hdenom_pos
    have hdenom_ne_zero : denom ≠ 0 := ne_of_gt hdenom_pos
    have hε_half : 0 < ε / 2 := half_pos hε
    have hε_denom_pos : 0 < ε / (8 * denom) := by
      have h_mul_pos : 0 < (8 : ℝ) * denom := mul_pos (by norm_num) hdenom_pos
      exact div_pos hε h_mul_pos
    have hε_denom_nonneg : 0 ≤ ε / (8 * denom) := le_of_lt hε_denom_pos
    set δ : ℝ := min (ε / 2) (ε / (8 * denom)) with hδ_def
    have hδ_pos : 0 < δ := by
      have hpos₁ : 0 < ε / 2 := hε_half
      have hpos₂ : 0 < ε / (8 * denom) := hε_denom_pos
      have hmin : 0 < min (ε / 2) (ε / (8 * denom)) := lt_min hpos₁ hpos₂
      simpa [δ, hδ_def] using hmin
    have h_powS_toReal_le : ((volume S) ^ (1 / p.toReal)).toReal ≤ denom := by
      simp [denom]
    obtain ⟨φ_raw, hφ_raw_smooth, hφ_raw_close⟩ :=
      hg_uc.exists_contDiff_dist_le hδ_pos

    -- Step 3c: build a smooth cutoff `χ` which equals `1` on the ball covering the support
    -- and vanishes outside a slightly larger ball. This ensures compact support after cutting.
    classical
    let fχ : ContDiffBump (0 : Fin n → ℝ) := ⟨R, R + 1, hR_pos, by simp⟩
    let χ : (Fin n → ℝ) → ℝ := fχ
    have hχ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) χ := fχ.contDiff
    have hχ_support : HasCompactSupport χ := fχ.hasCompactSupport
    have hχ_one : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) R, χ x = (1 : ℝ) := by
      intro x hx
      simpa [χ] using fχ.one_of_mem_closedBall hx
    have hχ_nonneg : ∀ x, 0 ≤ χ x := by
      intro x
      simpa [χ] using fχ.nonneg' x
    have hχ_le_one : ∀ x, χ x ≤ 1 := by
      intro x
      simpa [χ] using (ContDiffBump.le_one (f := fχ) (x := x))

    set φ₀ : (Fin n → ℝ) → ℂ := fun x => (χ x : ℝ) • φ_raw x with hφ₀_def
    have hφ₀_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ₀ := by
      simpa [φ₀] using hχ_smooth.smul hφ_raw_smooth
    have hφ₀_support : HasCompactSupport φ₀ :=
      (HasCompactSupport.smul_right (M := ℂ) (f := χ) hχ_support)
    have hφ₀_support_subset_supportχ :
        Function.support φ₀ ⊆ Function.support χ := by
      intro x hx
      have hxχ : χ x ≠ 0 := by
        have hxφ : φ₀ x ≠ 0 := hx
        by_contra hxχ
        have : φ₀ x = 0 := by simp [φ₀, hxχ]
        exact hxφ this
      simpa [Function.support] using hxχ
    have hφ₀_support_subset : Function.support φ₀ ⊆ Metric.ball (0 : Fin n → ℝ) (R + 1) := by
      intro x hx
      have hx_supportχ : x ∈ Function.support χ :=
        hφ₀_support_subset_supportχ hx
      have hχ_support_eq : Function.support χ = Metric.ball (0 : Fin n → ℝ) (R + 1) := by
        simpa [χ] using fχ.support_eq
      simpa [hχ_support_eq] using hx_supportχ
    have hφ₀_support_subset_closed :
        tsupport φ₀ ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1) := by
      intro x hx
      have hx_closure : x ∈ closure (Function.support φ₀) := by
        simpa [tsupport] using hx
      have hx_supportχ : x ∈ closure (Function.support χ) :=
        closure_mono hφ₀_support_subset_supportχ hx_closure
      have hχ_support_eq : Function.support χ = Metric.ball (0 : Fin n → ℝ) (R + 1) := by
        simpa [χ] using fχ.support_eq
      have hx_ball_closure : x ∈ closure (Metric.ball (0 : Fin n → ℝ) (R + 1)) := by
        simpa [hχ_support_eq] using hx_supportχ
      exact (Metric.closure_ball_subset_closedBall :
        closure (Metric.ball (0 : Fin n → ℝ) (R + 1)) ⊆
          Metric.closedBall (0 : Fin n → ℝ) (R + 1)) hx_ball_closure
    have hφ₀_close : ∀ x, dist (φ₀ x) (g x) < δ := by
      classical
      intro x
      by_cases hxB : x ∈ B
      · have hχx : χ x = (1 : ℝ) := hχ_one x hxB
        have := hφ_raw_close x
        simpa [φ₀, hχx, dist_eq_norm, norm_sub_rev]
      · have hgx : g x = 0 := hg_zero_outside x hxB
        have h_raw : dist (φ_raw x) (g x) < δ := hφ_raw_close x
        have h_raw_norm : ‖φ_raw x‖ < δ := by
          simpa [dist_eq_norm, hgx] using h_raw
        have hφ₀_norm : ‖φ₀ x‖ < δ := by
          have hx_nonneg := hχ_nonneg x
          have hx_bound : ‖φ₀ x‖ = ‖χ x‖ * ‖φ_raw x‖ := by
            simp [φ₀, norm_smul]
          have hx_abs_eq : ‖χ x‖ = χ x := by
            simp [Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
          have hx_abs_le : ‖χ x‖ ≤ 1 := by
            simpa [hx_abs_eq] using hχ_le_one x
          have hx_norm_nonneg : 0 ≤ ‖φ_raw x‖ := norm_nonneg _
          have hx_mul_le : ‖χ x‖ * ‖φ_raw x‖ ≤ ‖φ_raw x‖ :=
            (mul_le_of_le_one_left hx_norm_nonneg hx_abs_le)
          have hx_le : ‖φ₀ x‖ ≤ ‖φ_raw x‖ := by
            simpa [hx_bound]
              using hx_mul_le
          exact lt_of_le_of_lt hx_le h_raw_norm
        simpa [dist_eq_norm, hgx] using hφ₀_norm
    have h_pointwise_le : ∀ x, ‖g x - φ₀ x‖ ≤ δ := by
      intro x
      have := hφ₀_close x
      simp only [dist_eq_norm, norm_sub_rev] at this
      exact le_of_lt this
    have h_pointwise_small : ∀ x, ‖g x - φ₀ x‖ ≤ ε / 2 := by
      intro x
      exact le_trans (h_pointwise_le x) (min_le_left _ _)
    have h_pointwise_bound : ∀ x, ‖g x - φ₀ x‖ ≤ ε / (8 * denom) := by
      intro x
      exact le_trans (h_pointwise_le x) (min_le_right _ _)

    -- Step 3d: cut off the preliminary approximation so that it gains compact support.
    set ψ : (Fin n → ℝ) → ℂ := fun x => (χ x : ℝ) • φ₀ x with hψ_def
    have hψ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ := by
      simpa [ψ] using (hχ_smooth.smul hφ₀_smooth)
    have hψ_support : HasCompactSupport ψ :=
      (HasCompactSupport.smul_right (M := ℂ) (f := χ) hχ_support)
    have hψ_cont : Continuous ψ := hψ_smooth.continuous

    -- Step 3e: relate `ψ` with the original approximation on the support of `g`.
    have hψ_eq_on_support : ∀ x ∈ tsupport g, ψ x = φ₀ x := by
      intro x hx
      have hx_ball : x ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR_subset hx
      have hχx : χ x = (1 : ℝ) := hχ_one x hx_ball
      simp [ψ, hχx]

    -- Step 3f: estimate the Lᵖ error by splitting the domain into the support region
    -- and the exterior, keeping track of the uniform bounds obtained earlier.
    have h_term_support :
        eLpNorm (fun x => g x - φ₀ x) p volume < ENNReal.ofReal (ε / 2) := by
      classical
      -- Since `g` is compactly supported, the error `g - φ₀` is controlled on this ball.
      -- We split the integration domain according to the ball enclosure.
      have h_split :
          eLpNorm (fun x => g x - φ₀ x) p volume
              ≤
            eLpNorm (fun x => (Set.indicator B
                (fun y => g y - φ₀ y) x)) p volume
              +
            eLpNorm (fun x => (Set.indicator Bᶜ
                (fun y => g y - φ₀ y) x)) p volume :=
        by
          classical
          let f₁ : (Fin n → ℝ) → ℂ := fun x => Set.indicator B (fun y => g y - φ₀ y) x
          let f₂ : (Fin n → ℝ) → ℂ := fun x => Set.indicator Bᶜ (fun y => g y - φ₀ y) x
          have h_partition : (fun x => g x - φ₀ x) = fun x => f₁ x + f₂ x := by
            funext x
            have hx :=
              congrArg (fun f : (Fin n → ℝ) → ℂ => f x)
                (Set.indicator_self_add_compl (s := B) (f := fun y => g y - φ₀ y))
            simp [f₁, f₂, B, Pi.add_apply]
          have h_meas_base :
              AEStronglyMeasurable (fun x => g x - φ₀ x) volume :=
            (hg_cont.aestronglyMeasurable.sub
              (hφ₀_smooth.continuous.aestronglyMeasurable))
          have h_meas₁ : AEStronglyMeasurable f₁ volume :=
            h_meas_base.indicator measurableSet_closedBall
          have h_meas₂ : AEStronglyMeasurable f₂ volume :=
            h_meas_base.indicator (measurableSet_closedBall.compl)
          -- The inequality follows from the triangle inequality in `Lᵖ`.
          calc eLpNorm (fun x => g x - φ₀ x) p volume
              = eLpNorm (fun x => f₁ x + f₂ x) p volume := by rw [h_partition]
            _ ≤ eLpNorm f₁ p volume + eLpNorm f₂ p volume :=
                eLpNorm_add_le h_meas₁ h_meas₂ hp_one
      have h_ball_bound :
          eLpNorm (fun x => Set.indicator B (fun y => g y - φ₀ y) x) p volume
              < ENNReal.ofReal (ε / 4) := by
        classical
        set A := volume B ^ (1 / p.toReal) with hA_def
        have h_eLp_indicator :
            eLpNorm (fun x => Set.indicator B (fun y => g y - φ₀ y) x) p volume
                = eLpNorm (fun x => g x - φ₀ x) p (volume.restrict B) := by
          simpa using
            (eLpNorm_indicator_eq_eLpNorm_restrict
              (μ := volume) (s := B) (f := fun x => g x - φ₀ x) hB_meas)
        have h_restrict_bound :
            ∀ᵐ x ∂volume.restrict B, ‖g x - φ₀ x‖ ≤ ε / (8 * denom) :=
          (ae_of_all _ h_pointwise_bound)
        have h_eLp_le' :
            eLpNorm (fun x => g x - φ₀ x) p (volume.restrict B)
                ≤ (volume.restrict B Set.univ) ^ (1 / p.toReal) *
                    ENNReal.ofReal (ε / (8 * denom)) := by
          simpa using
            (eLpNorm_le_of_ae_bound (μ := volume.restrict B) (p := p)
              (f := fun x => g x - φ₀ x) h_restrict_bound)
        have hμB : volume.restrict B Set.univ = volume B := by
          simp [Measure.restrict_apply, hB_meas]
        have h_eLp_le :
            eLpNorm (fun x => Set.indicator B (fun y => g y - φ₀ y) x) p volume
                ≤ A * ENNReal.ofReal (ε / (8 * denom)) := by
          simpa [h_eLp_indicator, A, hA_def, hμB]
            using h_eLp_le'
        have hA_ne_top : A ≠ (∞ : ℝ≥0∞) := by
          simpa [A, hA_def] using h_pow_ne_top
        have hA_le : A ≤ ENNReal.ofReal denom := by
          have hA_le' : (volume B) ^ (1 / p.toReal)
              ≤ (volume S) ^ (1 / p.toReal) :=
            ENNReal.rpow_le_rpow hμB_le_S h_exponent_nonneg
          have hA_le'' : A ≤ (volume S) ^ p.toReal⁻¹ := by
            simpa [A, hA_def, one_div]
              using hA_le'
          have hS_le : (volume S) ^ p.toReal⁻¹
              ≤ ENNReal.ofReal denom := by
            have h_eq : p.toReal⁻¹ = 1 / p.toReal := (one_div _).symm
            rw [h_eq, ← ENNReal.ofReal_toReal h_powS_ne_top]
            exact ENNReal.ofReal_le_ofReal h_powS_toReal_le
          exact hA_le''.trans (by simpa [one_div] using hS_le)
        have h_mul_le :
            A * ENNReal.ofReal (ε / (8 * denom))
                ≤ ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom)) :=
          mul_le_mul_right' hA_le _
        have h_mul_eq :
            ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom))
                = ENNReal.ofReal (ε / 8) := by
          have hdenom_ne_zero : denom ≠ 0 := ne_of_gt hdenom_pos
          have hdenom_mul_ne_zero : (8 : ℝ) * denom ≠ 0 :=
            mul_ne_zero (by norm_num) hdenom_ne_zero
          have h_mul :
              ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom))
                  = ENNReal.ofReal (denom * (ε / (8 * denom))) := by
            simpa using
              (ENNReal.ofReal_mul (p := denom) (q := ε / (8 * denom))
                hdenom_nonneg).symm
          have h_cancel : denom * (ε / (8 * denom)) = ε / 8 := by
            have h_cancel' : ε * denom / (8 * denom) = ε / 8 := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (mul_div_mul_left (a := ε) (b := (8 : ℝ)) (c := denom)
                  hdenom_ne_zero)
            have h_rewrite :
                denom * (ε / (8 * denom)) = ε * denom / (8 * denom) := by
              simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
            exact h_rewrite.trans h_cancel'
          simpa [h_cancel] using h_mul
        have h_bound :
            eLpNorm (fun x => Set.indicator B (fun y => g y - φ₀ y) x) p volume
                ≤ ENNReal.ofReal (ε / 8) := by
          refine le_trans h_eLp_le ?_
          refine le_trans h_mul_le ?_
          simp [h_mul_eq]
        have hε_frac_lt_real : ε / 8 < ε / 4 := by
          have hfrac : (1 : ℝ) / 8 < 1 / 4 := by norm_num
          have hε_pos : 0 < ε := hε
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            (mul_lt_mul_of_pos_left hfrac hε_pos)
        have hε_quarter_pos : 0 < ε / 4 := by
          have : (0 : ℝ) < 4 := by norm_num
          exact div_pos hε this
        have hε_frac_lt : ENNReal.ofReal (ε / 8) < ENNReal.ofReal (ε / 4) :=
          (ENNReal.ofReal_lt_ofReal_iff hε_quarter_pos).2
            hε_frac_lt_real
        exact lt_of_le_of_lt h_bound hε_frac_lt
      have hφ₀_zero :=
        phi0_eq_zero_outside_enlarged_ball φ₀ R hφ₀_support_subset_closed
      classical
      set f := fun x : (Fin n → ℝ) => g x - φ₀ x with hf_def
      have h_support_zero : ∀ {x : Fin n → ℝ}, x ∉ S → f x = 0 := by
        intro x hxS
        have hx_norm : R + 1 < ‖x‖ := by
          have hx_lt : ¬dist x (0 : Fin n → ℝ) ≤ R + 1 := by
            simpa [hS_def, Metric.mem_closedBall] using hxS
          have : dist x (0 : Fin n → ℝ) = ‖x‖ := by
            simp [dist_eq_norm]
          simpa [this] using lt_of_not_ge hx_lt
        have hx_not_B : x ∉ B := by
          intro hxB
          have hx_le : dist x (0 : Fin n → ℝ) ≤ R := Metric.mem_closedBall.mp hxB
          have hx_norm_le : ‖x‖ ≤ R := by
            simpa [dist_eq_norm] using hx_le
          have hR_lt : R < R + 1 := by linarith
          exact (not_le_of_gt <| lt_trans hR_lt hx_norm) hx_norm_le
        have hg_zero : g x = 0 := hg_zero_outside x hx_not_B
        have hφ₀_zero' : φ₀ x = 0 := hφ₀_zero hx_norm
        simp [hf_def, hg_zero, hφ₀_zero']
      have h_indicator_support :
          ∀ {x : Fin n → ℝ}, x ∉ S → Set.indicator Bᶜ f x = 0 := by
        intro x hxS
        by_cases hxBc : x ∈ Bᶜ
        · have hzero := h_support_zero hxS
          simp [Set.indicator, hxBc, hzero]
        · simp [Set.indicator, hxBc]
      have h_indicator_eq :
          Set.indicator Bᶜ f = Set.indicator S (Set.indicator Bᶜ f) := by
        funext x
        by_cases hxS : x ∈ S
        · simp [Set.indicator, hxS]
        · have hf_zero : f x = 0 := h_support_zero hxS
          simp [Set.indicator, hxS, hf_zero]
      have h_indicator_bound :
          ∀ᵐ x ∂volume.restrict S,
            ‖Set.indicator Bᶜ f x‖ ≤ ε / (8 * denom) :=
        Filter.Eventually.of_forall <| by
          intro x
          by_cases hxBc : x ∈ Bᶜ
          · have hx_bound := h_pointwise_bound x
            simpa [hf_def, Set.indicator, hxBc] using hx_bound
          · simp [Set.indicator, hxBc, hε_denom_nonneg]
      have h_eLp_le :
          eLpNorm (fun x => Set.indicator Bᶜ f x) p (volume.restrict S)
              ≤ (volume S) ^ (1 / p.toReal) *
                ENNReal.ofReal (ε / (8 * denom)) := by
        have :=
          (eLpNorm_le_of_ae_bound (μ := volume.restrict S) (p := p)
            (f := fun x => Set.indicator Bᶜ f x) h_indicator_bound)
        simpa [Measure.restrict_apply, hS_meas, hS_def]
          using this
      have h_eLp_eq :
          eLpNorm (fun x => Set.indicator Bᶜ f x) p volume
              = eLpNorm (fun x => Set.indicator Bᶜ f x) p (volume.restrict S) := by
        have h_congr :=
          congrArg (fun g => eLpNorm g p volume) h_indicator_eq
        have h_tmp :=
          (eLpNorm_indicator_eq_eLpNorm_restrict
            (μ := volume) (p := p) (s := S)
            (f := fun x => Set.indicator Bᶜ f x) hS_meas)
        exact h_congr.trans h_tmp
      have h_main_le :
          eLpNorm (fun x => Set.indicator Bᶜ f x) p volume
              ≤ (volume S) ^ (1 / p.toReal) *
                ENNReal.ofReal (ε / (8 * denom)) := by
        simpa [h_eLp_eq]
          using h_eLp_le
      have h_target :
          (volume S) ^ (1 / p.toReal) * ENNReal.ofReal (ε / (8 * denom))
              < ENNReal.ofReal (ε / 4) := by
        set x := ((volume S) ^ (1 / p.toReal)).toReal with hx_def
        have hx_nonneg : 0 ≤ x := ENNReal.toReal_nonneg
        have hx_eq : ENNReal.ofReal x = (volume S) ^ (1 / p.toReal) := by
          simpa [hx_def] using ENNReal.ofReal_toReal h_powS_ne_top
        have hx_le : x ≤ denom := by
          simpa [hx_def] using h_powS_toReal_le
        have hx_mul_le : x * (ε / (8 * denom)) ≤ ε / 8 := by
          have h_mul :=
            mul_le_mul_of_nonneg_right hx_le hε_denom_nonneg
          have h₁ : denom ≠ 0 := hdenom_ne_zero
          have h₂ : (8 : ℝ) ≠ 0 := by norm_num
          have h_cancel : denom * (ε / (8 * denom)) = ε / 8 := by
            field_simp [h₁, h₂]
            ring
          simpa [h_cancel] using h_mul
        have hε_frac_lt_real : ε / 8 < ε / 4 := by
          have hfrac : (1 : ℝ) / 8 < 1 / 4 := by norm_num
          have hε_pos : 0 < ε := hε
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            (mul_lt_mul_of_pos_left hfrac hε_pos)
        have hε_quarter_pos : 0 < ε / 4 := by
          have : (0 : ℝ) < 4 := by norm_num
          exact div_pos hε this
        have h_real_lt : x * (ε / (8 * denom)) < ε / 4 :=
          lt_of_le_of_lt hx_mul_le hε_frac_lt_real
        have h_mul_eq :
            (volume S) ^ (1 / p.toReal) * ENNReal.ofReal (ε / (8 * denom))
                = ENNReal.ofReal (x * (ε / (8 * denom))) := by
          rw [← hx_eq]
          exact (ENNReal.ofReal_mul hx_nonneg).symm
        have h_mul_nonneg : 0 ≤ x * (ε / (8 * denom)) :=
          mul_nonneg hx_nonneg hε_denom_nonneg
        have h_target_real :
            ENNReal.ofReal (x * (ε / (8 * denom))) < ENNReal.ofReal (ε / 4) :=
          (ENNReal.ofReal_lt_ofReal_iff hε_quarter_pos).2 h_real_lt
        rw [h_mul_eq]
        exact h_target_real
      have h_outside_bound :
          eLpNorm (fun x => Set.indicator Bᶜ f x) p volume
              < ENNReal.ofReal (ε / 4) := by
        simpa [hf_def]
          using
            (lt_of_le_of_lt h_main_le h_target :
              eLpNorm (fun x => Set.indicator Bᶜ f x) p volume
                < ENNReal.ofReal (ε / 4))
      have h_sum :
          eLpNorm (fun x => g x - φ₀ x) p volume < ENNReal.ofReal (ε / 2) := by
        have h_lt :
            eLpNorm f p volume <
              ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
          have h_sum_lt := ENNReal.add_lt_add h_ball_bound h_outside_bound
          exact (lt_of_le_of_lt h_split (by simpa [hf_def] using h_sum_lt))
        have hquarter_pos : 0 < ε / 4 := by
          have : (0 : ℝ) < 4 := by norm_num
          exact div_pos hε this
        have hquarter_nonneg : 0 ≤ ε / 4 := le_of_lt hquarter_pos
        have h_add := ENNReal.ofReal_add hquarter_nonneg hquarter_nonneg
        have h_twice : ε / 4 + ε / 4 = ε / 2 := by ring
        have h_eq :
            ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
                = ENNReal.ofReal (ε / 2) := by
          simpa [h_twice] using h_add.symm
        simpa [hf_def, h_eq] using h_lt
      exact h_sum
    have h_term_cutoff :
        eLpNorm (fun x => φ₀ x - ψ x) p volume < ENNReal.ofReal (ε / 2) := by
      -- The difference `φ₀ - ψ` lives where the cutoff deviates from `1`.
      -- Its support is compact, and we can bound it using the uniform estimates on `φ₀`.
      classical
      set f_cut : (Fin n → ℝ) → ℂ := fun x => φ₀ x - ψ x with hfcut_def
      have h_support_subset : Function.support φ₀ ⊆ S := by
        intro x hx
        have hx_ball := hφ₀_support_subset hx
        have hx_closed :
            x ∈ Metric.closedBall (0 : Fin n → ℝ) (R + 1) :=
          (Metric.ball_subset_closedBall :
              Metric.ball (0 : Fin n → ℝ) (R + 1)
                ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1)) hx_ball
        simpa [S, hS_def] using hx_closed
      have h_outside_zero : ∀ {x : Fin n → ℝ}, x ∉ S → f_cut x = 0 := by
        intro x hxS
        have hφ₀_zero : φ₀ x = 0 := by
          by_contra hx_nonzero
          have hx_support : x ∈ Function.support φ₀ := by
            have : φ₀ x ≠ 0 := hx_nonzero
            simpa [Function.support] using this
          exact hxS (h_support_subset hx_support)
        have hψ_zero : ψ x = 0 := by simp [ψ, hφ₀_zero]
        simp [f_cut, hfcut_def, hφ₀_zero, hψ_zero]
      have h_pointwise_cut_le : ∀ x, ‖f_cut x‖ ≤ δ := by
        intro x
        by_cases hxB : x ∈ B
        · have hχx : χ x = (1 : ℝ) := hχ_one x hxB
          have : f_cut x = 0 := by simp [f_cut, hfcut_def, ψ, hχx]
          simp [this, le_of_lt hδ_pos]
        · have hgx : g x = 0 := hg_zero_outside x hxB
          have hφ₀_norm : ‖φ₀ x‖ ≤ δ := by
            have h_base : ‖φ₀ x - g x‖ ≤ δ := by
              simpa [norm_sub_rev] using h_pointwise_le x
            simpa [hgx] using h_base
          have h_factored : f_cut x = ((1 - χ x) : ℝ) • φ₀ x := by
            have h := sub_smul (1 : ℝ) (χ x) (φ₀ x)
            have h' : ((1 - χ x) : ℝ) • φ₀ x = φ₀ x - ψ x := by
              simpa [ψ] using h
            simpa [f_cut, hfcut_def] using h'.symm
          have h_norm_eq : ‖f_cut x‖ = |1 - χ x| * ‖φ₀ x‖ := by
            simpa [h_factored, Real.norm_eq_abs]
              using norm_smul ((1 - χ x) : ℝ) (φ₀ x)
          have h_abs_le_one : |1 - χ x| ≤ 1 := by
            have h_nonneg : 0 ≤ 1 - χ x := by linarith [hχ_le_one x]
            have h_le : 1 - χ x ≤ 1 := by linarith [hχ_nonneg x]
            have h_abs_eq : |1 - χ x| = 1 - χ x := abs_of_nonneg h_nonneg
            simpa [h_abs_eq] using h_le
          have h_mul_le : |1 - χ x| * ‖φ₀ x‖ ≤ δ := by
            have h_le' : |1 - χ x| * ‖φ₀ x‖ ≤ ‖φ₀ x‖ := by
              have :=
                mul_le_mul_of_nonneg_right h_abs_le_one (norm_nonneg (φ₀ x))
              simpa using this
            exact h_le'.trans hφ₀_norm
          have h_norm_le : ‖f_cut x‖ ≤ δ := by
            simpa [h_norm_eq] using h_mul_le
          exact h_norm_le
      have h_pointwise_cut_bound : ∀ x, ‖f_cut x‖ ≤ ε / (8 * denom) := by
        intro x
        exact (h_pointwise_cut_le x).trans (min_le_right _ _)
      have h_ae_bound :
          ∀ᵐ x ∂volume.restrict S, ‖f_cut x‖ ≤ ε / (8 * denom) :=
        Filter.Eventually.of_forall h_pointwise_cut_bound
      have h_indicator_eq : Set.indicator S f_cut = f_cut := by
        funext x
        by_cases hxS : x ∈ S
        · simp [Set.indicator, hxS, f_cut, hfcut_def]
        · have h_zero : f_cut x = 0 := h_outside_zero hxS
          simp [Set.indicator, hxS, f_cut, hfcut_def, h_zero]
      have h_eLp_eq :
          eLpNorm f_cut p volume = eLpNorm f_cut p (volume.restrict S) := by
        have h_congr :=
          congrArg (fun g => eLpNorm g p volume) h_indicator_eq.symm
        have h_tmp :=
          (eLpNorm_indicator_eq_eLpNorm_restrict
            (μ := volume) (p := p) (s := S) (f := f_cut) hS_meas)
        exact h_congr.trans h_tmp
      have h_eLp_le_aux :
          eLpNorm f_cut p (volume.restrict S)
              ≤ (volume S) ^ (1 / p.toReal) *
                ENNReal.ofReal (ε / (8 * denom)) := by
        simpa [Measure.restrict_apply, hS_meas, hS_def]
          using
            (eLpNorm_le_of_ae_bound (μ := volume.restrict S) (p := p)
              (f := f_cut) h_ae_bound)
      have h_eLp_le :
          eLpNorm f_cut p volume
              ≤ (volume S) ^ (1 / p.toReal) *
                ENNReal.ofReal (ε / (8 * denom)) := by
        simpa [h_eLp_eq] using h_eLp_le_aux
      have h_le' :
          ENNReal.ofReal (((volume S) ^ (1 / p.toReal)).toReal)
              ≤ ENNReal.ofReal denom :=
        ENNReal.ofReal_le_ofReal h_powS_toReal_le
      have h_powS_le :
          (volume S) ^ (1 / p.toReal) ≤ ENNReal.ofReal denom := by
        have h_eq :
            (volume S) ^ (1 / p.toReal)
                = ENNReal.ofReal (((volume S) ^ (1 / p.toReal)).toReal) :=
          (ENNReal.ofReal_toReal h_powS_ne_top).symm
        exact (le_of_eq_of_le h_eq h_le')
      have h_mul_le :
          (volume S) ^ (1 / p.toReal) *
              ENNReal.ofReal (ε / (8 * denom))
            ≤ ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom)) :=
        mul_le_mul_right' h_powS_le _
      have h_mul_eq :
          ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom))
              = ENNReal.ofReal (ε / 8) := by
        have hdenom_ne_zero : denom ≠ 0 := ne_of_gt hdenom_pos
        have h_mul :
            ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom))
                = ENNReal.ofReal (denom * (ε / (8 * denom))) := by
          have hdenom_nonneg : 0 ≤ denom := le_of_lt hdenom_pos
          exact (ENNReal.ofReal_mul hdenom_nonneg).symm
        have h_cancel' : ε * denom / (8 * denom) = ε / 8 := by
          simpa [mul_comm, mul_left_comm, mul_assoc]
            using
              (mul_div_mul_left (a := ε) (b := (8 : ℝ)) (c := denom)
                hdenom_ne_zero)
        have h_cancel : denom * (ε / (8 * denom)) = ε / 8 := by
          have h₈ : (8 : ℝ) ≠ 0 := by norm_num
          have h_denom_mul : (8 : ℝ) * denom ≠ 0 := mul_ne_zero h₈ hdenom_ne_zero
          calc denom * (ε / (8 * denom))
            = denom * ε / (8 * denom) := by rw [mul_div_assoc]
            _ = ε * denom / (8 * denom) := by rw [mul_comm denom ε]
            _ = ε / 8 := by rw [mul_div_mul_right _ _ hdenom_ne_zero]
        rw [← h_cancel]
        exact h_mul
      have h_bound :
          eLpNorm f_cut p volume ≤ ENNReal.ofReal (ε / 8) := by
        refine h_eLp_le.trans ?_
        refine h_mul_le.trans ?_
        simp [h_mul_eq]
      have h_real_lt : ε / 8 < ε / 2 := by
        calc ε / 8 = ε * (1 / 8) := div_eq_mul_one_div ε 8
          _ < ε * (1 / 2) := mul_lt_mul_of_pos_left (by norm_num : (1 : ℝ) / 8 < 1 / 2) hε
          _ = ε / 2 := (div_eq_mul_one_div ε 2).symm
      have hε_half_pos : 0 < ε / 2 := half_pos hε
      have h_lt :
          ENNReal.ofReal (ε / 8) < ENNReal.ofReal (ε / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff hε_half_pos).2 h_real_lt
      have h_bound' :
          eLpNorm (fun x => φ₀ x - ψ x) p volume ≤ ENNReal.ofReal (ε / 8) := by
        convert h_bound using 2
      exact lt_of_le_of_lt h_bound' h_lt

    have h_eLp_bound :
        eLpNorm (fun x => g x - ψ x) p volume < ENNReal.ofReal ε :=
      eLpNorm_triangle_ineq_lt p hp_one hg_cont hφ₀_smooth hψ_cont
        h_term_support h_term_cutoff hε_half

    -- Step 3g: `ψ` has compact support, so it automatically belongs to every Lᵖ space.
    have hψ_memLp : MemLp ψ p volume :=
      continuous_compactSupport_memLp hψ_cont hψ_support p

    -- Assemble the data for the final approximation step.
    refine ⟨ψ, hψ_smooth, ?_, hψ_memLp⟩
    exact h_eLp_bound

/-- Auxiliary lemma: smoothly cut off a continuous compactly supported function while
keeping control of the `Lᵖ` error. -/
lemma smooth_cutoff_compactSupport_Lp_aux
    (p : ℝ≥0∞) (hp_one : 1 ≤ p)
    (g : (Fin n → ℝ) → ℂ)
    (hg_cont : Continuous g)
    (hg_compact : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧
      HasCompactSupport ψ ∧
      MemLp ψ p volume ∧
      eLpNorm (fun x => g x - ψ x) p volume < ENNReal.ofReal ε := by
  classical
  have _ := hp_one
  obtain ⟨Rg, hRg_subset, hRg_one⟩ := tsupport_subset_closedBall g hg_compact
  have hRg_pos : 0 < Rg := lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hRg_one
  set S : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) (Rg + 1) with hS_def
  have hS_meas : MeasurableSet S :=
    (Metric.isClosed_closedBall :
      IsClosed (Metric.closedBall (0 : Fin n → ℝ) (Rg + 1))).measurableSet
  have hμS_lt_top : volume S < (⊤ : ℝ≥0∞) := by
    simpa [hS_def]
      using MeasureTheory.measure_closedBall_lt_top (x := (0 : Fin n → ℝ)) (r := Rg + 1)
  have hμS_ne_top : volume S ≠ (⊤ : ℝ≥0∞) := ne_of_lt hμS_lt_top
  let volFactor : ℝ≥0∞ := (volume S) ^ (1 / p.toReal)
  have hvol_ne_top : volFactor ≠ (⊤ : ℝ≥0∞) := by
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hμS_ne_top
    have hp_toReal_nonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
    exact (div_nonneg zero_le_one hp_toReal_nonneg)
  let C : ℝ := volFactor.toReal
  have hC_nonneg : 0 ≤ C := ENNReal.toReal_nonneg
  set δ : ℝ := (ε / 8) / (C + 1) with hδ_def
  have hδ_pos : 0 < δ := by
    have hnum_pos : 0 < ε / 8 := by
      have : (0 : ℝ) < 8 := by norm_num
      exact div_pos hε this
    have hden_pos : 0 < C + 1 := add_pos_of_nonneg_of_pos hC_nonneg zero_lt_one
    simpa [hδ_def] using div_pos hnum_pos hden_pos
  have hg_uc : UniformContinuous g := hg_compact.uniformContinuous_of_continuous hg_cont
  obtain ⟨φ₀, hφ₀_smooth, hφ₀_close⟩ := hg_uc.exists_contDiff_dist_le hδ_pos
  let fχ : ContDiffBump (0 : Fin n → ℝ) := ⟨Rg, Rg + 1, hRg_pos, by simp⟩
  let χ : (Fin n → ℝ) → ℝ := fχ
  have hχ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) χ := fχ.contDiff
  have hχ_support : HasCompactSupport χ := fχ.hasCompactSupport
  have hχ_one : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) Rg, χ x = (1 : ℝ) := by
    intro x hx
    simpa [χ] using fχ.one_of_mem_closedBall hx
  have hχ_nonneg : ∀ x, 0 ≤ χ x := by
    intro x; simpa [χ] using fχ.nonneg' x
  have hχ_le_one : ∀ x, χ x ≤ 1 := by
    intro x
    simpa [χ] using (fχ.le_one (x := x))
  set ψ : (Fin n → ℝ) → ℂ := fun x => (χ x : ℝ) • φ₀ x with hψ_def
  have hψ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ := by
    simpa [ψ] using hχ_smooth.smul hφ₀_smooth
  have hψ_support : HasCompactSupport ψ :=
    (HasCompactSupport.smul_right (M := ℂ) (f := χ) hχ_support)
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hψ_memLp : MemLp ψ p volume :=
    continuous_compactSupport_memLp hψ_cont hψ_support p
  have hg_zero_outside_ball :
      ∀ ⦃x : Fin n → ℝ⦄,
        x ∉ Metric.closedBall (0 : Fin n → ℝ) Rg → g x = 0 := by
    intro x hx
    have hx_not_support : x ∉ tsupport g := by
      intro hx_support
      exact hx (hRg_subset hx_support)
    simpa using image_eq_zero_of_notMem_tsupport hx_not_support
  have hχ_zero_outside : ∀ {x : Fin n → ℝ}, x ∉ S → χ x = 0 := by
    intro x hxS
    have hx_not_ball : x ∉ Metric.ball (0 : Fin n → ℝ) (Rg + 1) := by
      intro hx_ball
      exact hxS (Metric.ball_subset_closedBall hx_ball)
    have hx_not_support : x ∉ Function.support χ := by
      simpa [χ, fχ.support_eq] using hx_not_ball
    simpa [Function.support] using hx_not_support
  set diff : (Fin n → ℝ) → ℂ := fun x => g x - ψ x with hdiff_def
  have hdiff_zero_outside : ∀ {x : Fin n → ℝ}, x ∉ S → diff x = 0 := by
    intro x hxS
    have hx_norm_gt : Rg + 1 < ‖x‖ := by
      have hx_not_le : ¬ ‖x‖ ≤ Rg + 1 := by simpa [S, hS_def, dist_eq_norm] using hxS
      exact lt_of_not_ge hx_not_le
    have hx_not_closed : x ∉ Metric.closedBall (0 : Fin n → ℝ) Rg := by
      intro hx_mem
      have hx_le : ‖x‖ ≤ Rg := by simpa [dist_eq_norm] using hx_mem
      have hx_gt : Rg < ‖x‖ := lt_of_le_of_lt (show (Rg : ℝ) ≤ Rg + 1 by linarith) hx_norm_gt
      exact (not_lt_of_ge hx_le) hx_gt
    have hxg_zero : g x = 0 := hg_zero_outside_ball hx_not_closed
    have hxχ_zero : χ x = 0 := hχ_zero_outside hxS
    simp [diff, ψ, hxg_zero, hxχ_zero]
  have h_pointwise : ∀ x ∈ S, ‖diff x‖ ≤ δ := by
    intro x hxS
    have hx_norm_le : dist x (0 : Fin n → ℝ) ≤ Rg + 1 := by
      simpa [S, hS_def, dist_eq_norm] using hxS
    have hx_mem_outer : x ∈ Metric.closedBall (0 : Fin n → ℝ) (Rg + 1) := by
      simpa [Metric.mem_closedBall, dist_eq_norm]
        using hx_norm_le
    by_cases hx_inner : x ∈ Metric.closedBall (0 : Fin n → ℝ) Rg
    · have hχx : χ x = (1 : ℝ) := hχ_one x hx_inner
      have hx_bound := hφ₀_close x
      have hx_lt : ‖φ₀ x - g x‖ < δ := by
        simpa [dist_eq_norm] using hx_bound
      have hx_norm : ‖φ₀ x - g x‖ ≤ δ := le_of_lt hx_lt
      simpa [diff, ψ, hχx, norm_sub_rev]
        using hx_norm
    · have hxg_zero : g x = 0 := hg_zero_outside_ball hx_inner
      have hxφ₀_lt : ‖φ₀ x‖ < δ := by
        have hx_bound := hφ₀_close x
        simpa [dist_eq_norm, hxg_zero, norm_sub_rev] using hx_bound
      have hxφ₀_le : ‖φ₀ x‖ ≤ δ := le_of_lt hxφ₀_lt
      have hχ_norm_le : ‖χ x‖ ≤ 1 := by
        have hx_le := hχ_le_one x
        have hx_nonneg := hχ_nonneg x
        have hx_abs : |χ x| = χ x := abs_of_nonneg hx_nonneg
        have hx_norm : ‖χ x‖ = χ x := by simp [Real.norm_eq_abs, hx_abs]
        simpa [hx_norm]
          using hx_le
      have hxψ_le : ‖ψ x‖ ≤ δ := by
        have hxψ_norm : ‖ψ x‖ = ‖χ x‖ * ‖φ₀ x‖ := by
          simp [ψ, norm_smul]
        have hx_mul_le : ‖χ x‖ * ‖φ₀ x‖ ≤ ‖φ₀ x‖ :=
          (mul_le_of_le_one_left (norm_nonneg _) hχ_norm_le)
        have hψ_le_phi : ‖ψ x‖ ≤ ‖φ₀ x‖ := by
          simpa [ψ, norm_smul] using hx_mul_le
        exact hψ_le_phi.trans hxφ₀_le
      simpa [diff, hxg_zero]
        using hxψ_le
  have h_pointwise_all : ∀ x, ‖diff x‖ ≤ δ := by
    intro x
    by_cases hxS : x ∈ S
    · exact h_pointwise x hxS
    · have hx_zero : diff x = 0 := hdiff_zero_outside hxS
      simp [hx_zero, le_of_lt hδ_pos]
  have h_ae_bound :
      ∀ᵐ x ∂volume.restrict S, ‖diff x‖ ≤ δ :=
    Filter.Eventually.of_forall h_pointwise_all
  have h_indicator_eq : Set.indicator S diff = diff := by
    funext x
    by_cases hxS : x ∈ S
    · simp [diff, hxS]
    · have hx_zero : diff x = 0 := hdiff_zero_outside hxS
      simp [Set.indicator, hxS, diff, hx_zero]
  have h_eLp_eq :
      eLpNorm diff p volume = eLpNorm diff p (volume.restrict S) := by
    have h_indicator :=
      (eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := volume) (p := p) (s := S) (f := diff) hS_meas)
    simpa [h_indicator_eq] using h_indicator
  have h_eLp_le_aux :
      eLpNorm diff p (volume.restrict S)
        ≤ volFactor * ENNReal.ofReal δ := by
    have h_aux :=
      (eLpNorm_le_of_ae_bound
        (μ := volume.restrict S) (p := p) (f := diff) h_ae_bound)
    have h_simplified :
        eLpNorm diff p (volume.restrict S)
          ≤ (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δ := by
      simpa [Measure.restrict_apply, hS_meas, hS_def]
        using h_aux
    simpa [volFactor] using h_simplified
  have h_eLp_le :
      eLpNorm diff p volume ≤ volFactor * ENNReal.ofReal δ := by
    simpa [h_eLp_eq] using h_eLp_le_aux
  have h_volfactor_eq : volFactor = ENNReal.ofReal C :=
    (ENNReal.ofReal_toReal hvol_ne_top).symm
  have h_vol_le : volFactor ≤ ENNReal.ofReal (C + 1) := by
    have hC_le : C ≤ C + 1 := by linarith
    simpa [h_volfactor_eq] using ENNReal.ofReal_le_ofReal hC_le
  have h_mul_le :
      volFactor * ENNReal.ofReal δ
        ≤ ENNReal.ofReal (C + 1) * ENNReal.ofReal δ :=
    mul_le_mul_right' h_vol_le _
  have h_mul_eq :
      ENNReal.ofReal (C + 1) * ENNReal.ofReal δ
        = ENNReal.ofReal (ε / 8) := by
    have hden_pos : 0 < C + 1 := add_pos_of_nonneg_of_pos hC_nonneg zero_lt_one
    have hden_ne_zero : C + 1 ≠ 0 := ne_of_gt hden_pos
    have hden_nonneg : 0 ≤ C + 1 := le_of_lt hden_pos
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
    have h_mul :
        ENNReal.ofReal (C + 1) * ENNReal.ofReal δ
          = ENNReal.ofReal ((C + 1) * δ) :=
      (ENNReal.ofReal_mul hden_nonneg).symm
    have h_cancel : (C + 1) * δ = ε / 8 := by
      simp [δ, hδ_def, div_eq_mul_inv, hden_ne_zero, mul_comm, mul_left_comm, mul_assoc]
    simp [h_mul, h_cancel]
  have h_eLp_le' : eLpNorm diff p volume ≤ ENNReal.ofReal (ε / 8) :=
    h_eLp_le.trans <| h_mul_le.trans <| le_of_eq h_mul_eq
  have hε_eighth_lt : ε / 8 < ε / 4 := by
    have : (1 : ℝ) / 8 < 1 / 4 := by norm_num
    have hε_pos : 0 < ε := hε
    have := mul_lt_mul_of_pos_left this hε_pos
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hε_quarter_pos : 0 < ε / 4 := by
    have : (0 : ℝ) < 4 := by norm_num
    exact div_pos hε this
  have h_eLp_lt : eLpNorm diff p volume < ENNReal.ofReal (ε / 4) :=
    lt_of_le_of_lt h_eLp_le'
      ((ENNReal.ofReal_lt_ofReal_iff hε_quarter_pos).2 hε_eighth_lt)
  refine ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, ?_⟩
  have hε_quarter_lt_real : ε / 4 < ε := by
    have : (0 : ℝ) < ε := hε
    linarith
  have hε_quarter_lt : ENNReal.ofReal (ε / 4) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 hε_quarter_lt_real
  exact lt_trans h_eLp_lt hε_quarter_lt

/-- Cutting off a smooth function so that it has compact support while keeping control of the
`Lᵖ` error. -/
theorem smooth_cutoff_compactSupport_Lp
    (p : ℝ≥0∞)
    (hp_one : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (φ : (Fin n → ℝ) → ℂ)
    (hφ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ)
    (hφ_memLp : MemLp φ p volume)
    {R : ℝ} (hR_pos : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ ∧ MemLp ψ p volume ∧
      eLpNorm (fun x => φ x - ψ x) p volume < ENNReal.ofReal ε := by
  classical
  have _ := hR_pos
  have hε_quarter_pos : 0 < ε / 4 := by
    have : (0 : ℝ) < 4 := by norm_num
    exact div_pos hε this
  obtain ⟨g, hg_cont, hg_compact, hg_memLp, hφg⟩ :=
    continuous_compactSupport_dense_Lp
      (p := p) (hp_ne_top := hp_ne_top)
      φ hφ_memLp (ε := ε / 4) hε_quarter_pos
  obtain ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, hgψ⟩ :=
    smooth_cutoff_compactSupport_Lp_aux (p := p) (hp_one := hp_one)
      g hg_cont hg_compact (ε := ε / 4) hε_quarter_pos
  have hφg_le :
      eLpNorm (fun x => φ x - g x) p volume ≤ ENNReal.ofReal (ε / 4) :=
    le_of_lt hφg
  have hgψ_le :
      eLpNorm (fun x => g x - ψ x) p volume ≤ ENNReal.ofReal (ε / 4) :=
    le_of_lt hgψ
  have hφg_meas :
      AEStronglyMeasurable (fun x => φ x - g x) volume :=
    aestronglyMeasurable_sub_contDiff_continuous hφ_smooth hg_cont
  have hgψ_meas :
      AEStronglyMeasurable (fun x => g x - ψ x) volume :=
    aestronglyMeasurable_sub_continuous_contDiff hg_cont hψ_smooth
  have h_fun_eq :
      (fun x => φ x - ψ x)
        = (fun x => φ x - g x) + fun x => g x - ψ x :=
    sub_eq_add_sub φ g ψ
  have h_triangle :
      eLpNorm (fun x => φ x - ψ x) p volume
        ≤ eLpNorm (fun x => φ x - g x) p volume
            + eLpNorm (fun x => g x - ψ x) p volume := by
    simpa [h_fun_eq]
      using
        (eLpNorm_add_le (μ := volume) (p := p)
          (f := fun x => φ x - g x)
          (g := fun x => g x - ψ x)
          (hf := hφg_meas) (hg := hgψ_meas) hp_one)
  have h_add_le :
      eLpNorm (fun x => φ x - g x) p volume
            + eLpNorm (fun x => g x - ψ x) p volume
        ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    add_le_add hφg_le hgψ_le
  have h_total_le :
      eLpNorm (fun x => φ x - ψ x) p volume
        ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    h_triangle.trans h_add_le
  have h_add_eq :
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
        = ENNReal.ofReal (ε / 2) := by
    have hnonneg : 0 ≤ ε / 4 := le_of_lt hε_quarter_pos
    have h_sum : ε / 4 + ε / 4 = ε / 2 := by ring
    have h_add := ENNReal.ofReal_add hnonneg hnonneg
    simpa [h_sum] using h_add.symm
  have h_total_le' :
      eLpNorm (fun x => φ x - ψ x) p volume ≤ ENNReal.ofReal (ε / 2) := by
    simpa [h_add_eq] using h_total_le
  have hε_half_lt_real : ε / 2 < ε := by
    have : (0 : ℝ) < ε := hε
    linarith
  have hε_half_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 hε_half_lt_real
  have h_total_lt :
      eLpNorm (fun x => φ x - ψ x) p volume < ENNReal.ofReal ε :=
    lt_of_le_of_lt h_total_le' hε_half_lt
  exact ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, h_total_lt⟩

/--
**C∞ compactly supported functions are dense in Lp.**

This is Corollary 8.15 in Folland, "Real Analysis".
Also appears in Reed & Simon, "Methods of Modern Mathematical Physics I", Theorem II.17.

For any f ∈ Lp(ℝⁿ) with 1 ≤ p < ∞ and any ε > 0, there exists
a C∞ function g with compact support such that ‖f - g‖_p < ε.

## Proof strategy

This follows from continuous compactly supported density plus mollification:
1. First approximate f by continuous compactly supported g
2. Then mollify g (convolve with smooth approximation to identity)
3. For small mollification parameter, the smooth approximation is close in Lp
-/
theorem smooth_compactSupport_dense_Lp
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
    HasCompactSupport g ∧
    MemLp g p volume ∧
    eLpNorm (f - g) p volume < ENNReal.ofReal ε := by
  classical
  have hε_half_pos : 0 < ε / 2 := half_pos hε
  have hε_quarter_pos : 0 < ε / 4 := by
    have : (0 : ℝ) < 4 := by norm_num
    exact div_pos hε this
  obtain ⟨g₀, hg₀_cont, hg₀_support, hg₀_memLp, hf_g₀⟩ :=
    continuous_compactSupport_dense_Lp
      (p := p) (hp_ne_top := hp_ne_top)
      f hf (ε := ε / 4) hε_quarter_pos
  obtain ⟨φ₀, hφ₀_smooth, hg₀_φ₀, hφ₀_memLp⟩ :=
    mollifier_compactSupport_Lp_approx
      (p := p) (hp_one := hp) g₀ hg₀_cont hg₀_support (ε := ε / 4) hε_quarter_pos
  obtain ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, hφ₀ψ⟩ :=
    smooth_cutoff_compactSupport_Lp
      (p := p) (hp_one := hp) (hp_ne_top := hp_ne_top)
      φ₀ hφ₀_smooth hφ₀_memLp (R := 1) (hR_pos := by norm_num)
      (ε := ε / 2) hε_half_pos

  -- First combine the two preliminary approximations `f → g₀` and `g₀ → φ₀`.
  have hf_g₀_le :
      eLpNorm (fun x => f x - g₀ x) p volume ≤ ENNReal.ofReal (ε / 4) :=
    le_of_lt hf_g₀
  have hg₀_φ₀_le :
      eLpNorm (fun x => g₀ x - φ₀ x) p volume ≤ ENNReal.ofReal (ε / 4) :=
    le_of_lt hg₀_φ₀
  have hf_g₀_meas :
      AEStronglyMeasurable (fun x => f x - g₀ x) volume :=
    aestronglyMeasurable_sub_of_aesm_continuous hf.aestronglyMeasurable hg₀_cont
  have hg₀_φ₀_meas :
      AEStronglyMeasurable (fun x => g₀ x - φ₀ x) volume :=
    aestronglyMeasurable_sub_continuous_contDiff hg₀_cont hφ₀_smooth
  have h_f_sub_φ₀_eq :
      (fun x => f x - φ₀ x)
        = (fun x => f x - g₀ x) + fun x => g₀ x - φ₀ x :=
    sub_eq_add_sub f g₀ φ₀
  have h_triangle_fg₀φ₀ :
      eLpNorm (fun x => f x - φ₀ x) p volume
        ≤ eLpNorm (fun x => f x - g₀ x) p volume
            + eLpNorm (fun x => g₀ x - φ₀ x) p volume := by
    simpa [h_f_sub_φ₀_eq]
      using
        (eLpNorm_add_le (μ := volume) (p := p)
          (f := fun x => f x - g₀ x)
          (g := fun x => g₀ x - φ₀ x)
          (hf := hf_g₀_meas) (hg := hg₀_φ₀_meas) hp)
  have h_sum_lt_fg₀φ₀ :
      eLpNorm (fun x => f x - g₀ x) p volume
          + eLpNorm (fun x => g₀ x - φ₀ x) p volume
        < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    ENNReal.add_lt_add hf_g₀ hg₀_φ₀
  have h_add_eq_quarter :
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
        = ENNReal.ofReal (ε / 2) := by
    have hnonneg : 0 ≤ ε / 4 := le_of_lt hε_quarter_pos
    have h_sum : ε / 4 + ε / 4 = ε / 2 := by ring
    have h_add := ENNReal.ofReal_add hnonneg hnonneg
    simpa [h_sum] using h_add.symm
  have hf_φ₀_lt :
      eLpNorm (fun x => f x - φ₀ x) p volume < ENNReal.ofReal (ε / 2) :=
    lt_of_le_of_lt h_triangle_fg₀φ₀ <|
      by simpa [h_add_eq_quarter] using h_sum_lt_fg₀φ₀

  -- Now combine the previous approximation with the smooth cut-off step `φ₀ → ψ`.
  have hf_φ₀_meas :
      AEStronglyMeasurable (fun x => f x - φ₀ x) volume :=
    hf.aestronglyMeasurable.sub hφ₀_smooth.continuous.aestronglyMeasurable
  have hφ₀_ψ_meas :
      AEStronglyMeasurable (fun x => φ₀ x - ψ x) volume :=
    aestronglyMeasurable_sub_contDiff_continuous hφ₀_smooth hψ_smooth.continuous
  have h_f_sub_ψ_eq :
      (fun x => f x - ψ x)
        = (fun x => f x - φ₀ x) + fun x => φ₀ x - ψ x :=
    sub_eq_add_sub f φ₀ ψ
  have h_triangle_final :
      eLpNorm (fun x => f x - ψ x) p volume
        ≤ eLpNorm (fun x => f x - φ₀ x) p volume
            + eLpNorm (fun x => φ₀ x - ψ x) p volume := by
    simpa [h_f_sub_ψ_eq]
      using
        (eLpNorm_add_le (μ := volume) (p := p)
          (f := fun x => f x - φ₀ x)
          (g := fun x => φ₀ x - ψ x)
          (hf := hf_φ₀_meas) (hg := hφ₀_ψ_meas) hp)
  have h_sum_lt_final :
      eLpNorm (fun x => f x - φ₀ x) p volume
          + eLpNorm (fun x => φ₀ x - ψ x) p volume
        < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
    ENNReal.add_lt_add hf_φ₀_lt hφ₀ψ
  have h_add_eq_half :
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
        = ENNReal.ofReal ε := by
    have hnonneg : 0 ≤ ε / 2 := le_of_lt hε_half_pos
    have h_sum : ε / 2 + ε / 2 = ε := by ring
    have h_add := ENNReal.ofReal_add hnonneg hnonneg
    simpa [h_sum] using h_add.symm
  have hf_ψ_lt :
      eLpNorm (fun x => f x - ψ x) p volume < ENNReal.ofReal ε :=
    lt_of_le_of_lt h_triangle_final <|
      by simpa [h_add_eq_half] using h_sum_lt_final

  -- Assemble the final data.
  refine ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, ?_⟩
  simpa [Pi.sub_def] using hf_ψ_lt

/-- Smooth compactly supported functions are Schwartz. -/
lemma smooth_compactSupport_to_schwartz
    (g : (Fin n → ℝ) → ℂ)
    (hg_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hg_support : HasCompactSupport g) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ), (φ : (Fin n → ℝ) → ℂ) = g := by
  classical
  have h_decay : ∀ k m : ℕ, ∃ C : ℝ,
      ∀ x : (Fin n → ℝ), ‖x‖ ^ k * ‖iteratedFDeriv ℝ m g x‖ ≤ C := by
    intro k m
    classical
    set K := tsupport g with hK_def
    have hK_compact : IsCompact K := by simpa [hK_def] using hg_support
    have h_iter_subset : tsupport (iteratedFDeriv ℝ m g) ⊆ K := by
      simpa [hK_def] using
        (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := g) (n := m))
    set h : (Fin n → ℝ) → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ m g x‖
    have h_nonneg : ∀ x, 0 ≤ h x := fun x =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    by_cases h_support_empty : tsupport (iteratedFDeriv ℝ m g) = (∅ : Set (Fin n → ℝ))
    · refine ⟨0, ?_⟩
      intro x
      have hx_not : x ∉ tsupport (iteratedFDeriv ℝ m g) := by
        simp [h_support_empty]
      have hx_zero : iteratedFDeriv ℝ m g x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      simp [h, hx_zero]
    · have h_support_nonempty : (tsupport (iteratedFDeriv ℝ m g)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr h_support_empty
      obtain ⟨x₀, hx₀_support⟩ := h_support_nonempty
      have hx₀K : x₀ ∈ K := h_iter_subset hx₀_support
      have h_pow_cont : Continuous fun x : (Fin n → ℝ) => ‖x‖ ^ k :=
        (continuous_norm : Continuous fun x => ‖x‖).pow _
      have h_iter_cont : Continuous fun x : (Fin n → ℝ) => iteratedFDeriv ℝ m g x :=
        hg_smooth.continuous_iteratedFDeriv (hm := by
          exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞)))
      have h_cont : Continuous h :=
        h_pow_cont.mul (h_iter_cont.norm)
      have h_image_compact : IsCompact (h '' K) := hK_compact.image h_cont
      have h_image_nonempty : (h '' K).Nonempty := ⟨h x₀, ⟨x₀, hx₀K, rfl⟩⟩
      obtain ⟨C, hC_isGreatest⟩ :=
        h_image_compact.exists_isGreatest h_image_nonempty
      obtain ⟨⟨xC, hxC_K, rfl⟩, hC_max⟩ := hC_isGreatest
      refine ⟨h xC, ?_⟩
      intro x
      by_cases hxK : x ∈ K
      · have hx_mem : h x ∈ h '' K := ⟨x, hxK, rfl⟩
        exact hC_max hx_mem
      · have hx_not : x ∉ tsupport (iteratedFDeriv ℝ m g) := fun hx => hxK (h_iter_subset hx)
        have hx_zero : iteratedFDeriv ℝ m g x = 0 :=
          image_eq_zero_of_notMem_tsupport hx_not
        have hx_val : h x = 0 := by simp [h, hx_zero]
        have hxC_nonneg : 0 ≤ h xC := h_nonneg xC
        have hx_le : h x ≤ h xC := by simpa [hx_val] using hxC_nonneg
        exact hx_le
  refine ⟨⟨g, hg_smooth, h_decay⟩, rfl⟩

/--
**Schwartz functions are dense in Lp for 1 ≤ p < ∞.**

This is Theorem 4.1.2 in Stein & Shakarchi, "Functional Analysis".
Also appears as Theorem 8.16 in Folland, "Real Analysis".

For any f ∈ Lp(ℝⁿ) with 1 ≤ p < ∞ and any ε > 0, there exists
a Schwartz function φ such that ‖f - φ‖_p < ε.

## Mathematical content

The proof typically proceeds in stages:
1. Simple functions are dense in Lp
2. Continuous compactly supported functions approximate simple functions
3. Mollification (convolution with smooth approximation to identity)
   produces smooth compactly supported functions
4. Smooth compactly supported functions can be made rapidly decreasing

This is one of the most fundamental approximation theorems in analysis.
-/
theorem schwartz_dense_Lp
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ),
      eLpNorm (fun x => f x - φ x) p volume < ENNReal.ofReal ε := by
  classical
  have hε_half_pos : 0 < ε / 2 := half_pos hε
  obtain ⟨g, hg_smooth, hg_support, _, hf_g⟩ :=
    smooth_compactSupport_dense_Lp
      (p := p) (hp := hp) (hp_ne_top := hp_ne_top)
      f hf (ε := ε / 2) hε_half_pos
  obtain ⟨φ, hφ_eq⟩ := smooth_compactSupport_to_schwartz g hg_smooth hg_support
  have h_norm_eq :
      eLpNorm (fun x => f x - φ x) p volume
        = eLpNorm (fun x => f x - g x) p volume := by
    simp [hφ_eq, Pi.sub_def]
  have hf_g_lt :
      eLpNorm (fun x => f x - g x) p volume < ENNReal.ofReal (ε / 2) := hf_g
  have h_half_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 (by
      have : 0 < ε := hε
      linarith)
  have hf_φ_lt :
      eLpNorm (fun x => f x - φ x) p volume < ENNReal.ofReal ε := by
    simpa [h_norm_eq] using lt_of_lt_of_le hf_g_lt h_half_lt.le
  exact ⟨φ, hf_φ_lt⟩

/-- Hölder's inequality for the product of two L²-functions. -/
lemma holder_memLp_L1_L2
    (f g : (Fin n → ℝ) → ℂ)
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    eLpNorm (fun x => f x * g x) 1 volume
      ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
  classical
  have h_bound :
      ∀ᵐ x ∂volume,
        ‖(fun x => f x * g x) x‖₊ ≤ (1 : ℝ≥0) * ‖f x‖₊ * ‖g x‖₊ :=
    ae_of_all _ fun x => by
      have hx : ‖f x * g x‖₊ = ‖f x‖₊ * ‖g x‖₊ := by
        simp [nnnorm_mul]
      have h' : ‖f x‖₊ * ‖g x‖₊ ≤ (1 : ℝ≥0) * ‖f x‖₊ * ‖g x‖₊ :=
        le_of_eq (by simp [one_mul, mul_comm, mul_left_comm, mul_assoc])
      exact hx.le.trans h'
  have h :=
    (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volume)
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      hf.aestronglyMeasurable hg.aestronglyMeasurable
      (fun x y : ℂ => x * y) (1 : ℝ≥0) h_bound)
  have h' :
      (1 : ℝ≥0∞) * eLpNorm f 2 volume * eLpNorm g 2 volume
        = eLpNorm f 2 volume * eLpNorm g 2 volume := by
    simp [one_mul, mul_comm, mul_left_comm, mul_assoc]
  simpa [h'] using h

/-- Cauchy–Schwarz inequality specialised to complex-valued functions on `ℝⁿ`. -/
lemma cauchy_schwarz_memLp
    (f g : (Fin n → ℝ) → ℂ)
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    ‖∫ x, f x * star (g x) ∂volume‖
      ≤ (eLpNorm f 2 volume * eLpNorm g 2 volume).toReal := by
  classical
  -- introduce the conjugate of `g`
  let gConj := fun x => star (g x)
  have hgConj_meas : AEStronglyMeasurable gConj volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hgConj_norm : ∀ᵐ x ∂volume, ‖g x‖ = ‖gConj x‖ :=
    Filter.Eventually.of_forall fun x => by simp [gConj]
  have hgConj : MemLp gConj 2 volume :=
    hg.congr_norm hgConj_meas hgConj_norm

  -- eLpNorm is invariant under conjugation
  have h_eLp_conj : eLpNorm gConj 2 volume = eLpNorm g 2 volume := by
    simp only [gConj]
    exact eLpNorm_conj g 2 volume

  -- Hölder inequality (Cauchy–Schwarz) for the pointwise product
  have h_holder :=
    holder_memLp_L1_L2 (f := f) (g := gConj) hf hgConj
  have h_holder' :
      eLpNorm (fun x => f x * gConj x) 1 volume
        ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
    simp only [gConj] at h_holder ⊢
    calc eLpNorm (fun x => f x * star (g x)) 1 volume
        ≤ eLpNorm f 2 volume * eLpNorm (fun x => star (g x)) 2 volume := h_holder
      _ = eLpNorm f 2 volume * eLpNorm g 2 volume := by rw [← h_eLp_conj]

  -- the product lies in L¹
  have h_mul_memLp :
      MemLp (fun x => f x * gConj x) 1 volume :=
    (MemLp.mul' (μ := volume) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (hf := hgConj) (hφ := hf))
  have h_integrable : Integrable (fun x => f x * gConj x) volume :=
    (memLp_one_iff_integrable).1 h_mul_memLp

  -- bound the integral via its L¹ norm
  have h_norm_integral :
      ‖∫ x, f x * gConj x ∂volume‖
        ≤ ∫ x, ‖f x * gConj x‖ ∂volume :=
    norm_integral_le_integral_norm _
  have h_integral_eq :
      ∫ x, ‖f x * gConj x‖ ∂volume
        = (eLpNorm (fun x => f x * gConj x) 1 volume).toReal := by
    simpa [gConj, eLpNorm_one_eq_lintegral_enorm]
      using integral_norm_eq_lintegral_enorm h_integrable.aestronglyMeasurable

  -- convert the Hölder bound to real form
  have h_mul_fin :
      eLpNorm (fun x => f x * gConj x) 1 volume ≠ ∞ :=
    h_mul_memLp.eLpNorm_ne_top
  have hf_fin : eLpNorm f 2 volume ≠ ∞ := hf.eLpNorm_ne_top
  have hg_fin : eLpNorm g 2 volume ≠ ∞ := hg.eLpNorm_ne_top
  have h_product_fin :
      eLpNorm f 2 volume * eLpNorm g 2 volume ≠ ∞ :=
    ENNReal.mul_ne_top hf_fin hg_fin
  have h_holder_real :
      (eLpNorm (fun x => f x * gConj x) 1 volume).toReal
        ≤ (eLpNorm f 2 volume * eLpNorm g 2 volume).toReal :=
    (ENNReal.toReal_le_toReal h_mul_fin h_product_fin).2
      h_holder'

  -- combine the bounds
  calc
    ‖∫ x, f x * star (g x) ∂volume‖
        = ‖∫ x, f x * gConj x ∂volume‖ := by rfl
    _ ≤ ∫ x, ‖f x * gConj x‖ ∂volume := h_norm_integral
    _ = (eLpNorm (fun x => f x * gConj x) 1 volume).toReal := h_integral_eq
    _ ≤ (eLpNorm f 2 volume * eLpNorm g 2 volume).toReal := h_holder_real

/-- Schwartz functions belong to every `Lᵖ` space. -/
lemma schwartz_memLp
    (φ : 𝓢((Fin n → ℝ), ℂ)) (p : ℝ≥0∞) :
    MemLp (fun x => φ x) p volume := by
  simpa using φ.memLp p (μ := volume)

/-- Tail estimate for integrable functions on `ℝⁿ` (placeholder). -/
lemma integrable_tail_small
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f 1 volume)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ R > 0, ∫ x, ‖f x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) < ε :=
  by
  classical
  set g : (Fin n → ℝ) → ℝ := fun x => ‖f x‖ with hg_def
  have hf_int : Integrable f volume :=
    (memLp_one_iff_integrable).1 hf
  have hg_integrable : Integrable g volume := by
    simpa [hg_def] using hf_int.norm
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => norm_nonneg _
  let tail : ℕ → Set (Fin n → ℝ) := fun k => {x | (k : ℝ) ≤ ‖x‖}

  have h_tail_meas : ∀ k, MeasurableSet (tail k) := by
    intro k
    have h_closed :
        IsClosed {x : (Fin n → ℝ) | (k : ℝ) ≤ ‖x‖} :=
      (isClosed_le continuous_const continuous_norm)
    simpa [tail] using h_closed.measurableSet

  have h_tendsto :
      Filter.Tendsto
        (fun k : ℕ => ∫ x, Set.indicator (tail k) g x ∂volume)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    have h_meas : ∀ k : ℕ,
        AEStronglyMeasurable (fun x => Set.indicator (tail k) g x) volume := by
      intro k
      exact hg_integrable.aestronglyMeasurable.indicator (h_tail_meas k)
    have h_bound : ∀ k : ℕ, ∀ᵐ x ∂volume,
        ‖Set.indicator (tail k) g x‖ ≤ g x := by
      intro k
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : x ∈ tail k
      · have hx_nonneg : 0 ≤ g x := hg_nonneg x
        simp [tail, hx, hg_def, Real.norm_eq_abs, hx_nonneg,
          abs_of_nonneg hx_nonneg]
      · simp [tail, hx, hg_def, Real.norm_eq_abs, hg_nonneg x]
    have h_lim : ∀ᵐ x ∂volume,
        Filter.Tendsto (fun k : ℕ => Set.indicator (tail k) g x)
          Filter.atTop (𝓝 (0 : ℝ)) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      have h_eventually_zero :
          (fun k : ℕ => Set.indicator (tail k) g x)
            =ᶠ[Filter.atTop] fun _ : ℕ => (0 : ℝ) := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨N, ?_⟩
        intro k hk
        have hk' : ¬ (k : ℝ) ≤ ‖x‖ := by
          have hx_lt : ‖x‖ < (k : ℝ) := lt_of_lt_of_le hN (Nat.cast_le.mpr hk)
          exact not_le_of_gt hx_lt
        simp [tail, hk', hg_def]
      exact
        (Filter.Tendsto.congr' h_eventually_zero.symm)
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
    have h_tendsto' :=
      MeasureTheory.tendsto_integral_of_dominated_convergence g h_meas
        hg_integrable h_bound h_lim
    simpa using h_tendsto'

  have h_eventually : ∀ᶠ k : ℕ in Filter.atTop,
      ∫ x in tail k, g x ∂volume < ε := by
    have h_tail_nonneg : ∀ k : ℕ, 0 ≤ ∫ x in tail k, g x ∂volume := by
      intro k
      have h_indicator_nonneg :
          0 ≤ᵐ[volume] fun x => Set.indicator (tail k) g x :=
        Filter.Eventually.of_forall (fun x => by
          by_cases hx : x ∈ tail k
          · simp [tail, hx, hg_def, hg_nonneg x]
          · simp [tail, hx, hg_def, hg_nonneg x])
      have h_eq : ∫ x, Set.indicator (tail k) g x ∂volume
          = ∫ x in tail k, g x ∂volume :=
        MeasureTheory.integral_indicator (h_tail_meas k)
      have h_integral_nonneg :
          0 ≤ ∫ x, Set.indicator (tail k) g x ∂volume :=
        MeasureTheory.integral_nonneg_of_ae h_indicator_nonneg
      simpa [h_eq]
        using h_integral_nonneg
    have h_dist := (Metric.tendsto_nhds.mp h_tendsto) ε (by simpa using hε)
    refine h_dist.mono ?_
    intro k hk
    have h_eq : ∫ x, Set.indicator (tail k) g x ∂volume
        = ∫ x in tail k, g x ∂volume :=
      MeasureTheory.integral_indicator (h_tail_meas k)
    simpa [Real.dist_eq, h_eq, abs_of_nonneg (h_tail_nonneg k)] using hk

  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
  let M : ℕ := max N 1
  have hM_ge_N : N ≤ M := le_max_left _ _
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos_nat : 0 < M := lt_of_lt_of_le (Nat.succ_pos 0) hM_ge_one
  have hM_tail_lt : ∫ x in tail M, g x ∂volume < ε := hN M hM_ge_N
  have hM_pos : 0 < (M : ℝ) := by exact_mod_cast hM_pos_nat
  refine ⟨(M : ℝ), hM_pos, ?_⟩
  have h_eq :
      ∫ x, ‖f x‖ ∂(volume.restrict {x | (M : ℝ) ≤ ‖x‖})
        = ∫ x in tail M, g x ∂volume := by
    rfl
  simpa [tail, hg_def, h_eq]
    using hM_tail_lt

/-- L² bound implies L¹ bound on a fixed ball (placeholder). -/
lemma eLpNorm_L2_ball_control
    (f : (Fin n → ℝ) → ℂ) (φ : 𝓢((Fin n → ℝ), ℂ)) {R : ℝ}
    (hfφ : MemLp (fun x => f x - φ x) 2 volume) :
    ∫ x, ‖f x - φ x‖ ∂(volume.restrict {x | ‖x‖ ≤ R})
        ≤ ((volume : Measure (Fin n → ℝ)) {x | ‖x‖ ≤ R}).toReal ^ (1 / 2 : ℝ)
            * (eLpNorm (fun x => f x - φ x) 2 volume).toReal := by
  classical
  set s : Set (Fin n → ℝ) := {x | ‖x‖ ≤ R} with hs_def
  have hs_meas : MeasurableSet s :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hs_closedBall : s = Metric.closedBall (0 : Fin n → ℝ) R := by
    ext x; simp [hs_def, Metric.mem_closedBall, dist_eq_norm]
  have hs_lt_top : volume s < (⊤ : ℝ≥0∞) := by
    rw [hs_closedBall]
    exact MeasureTheory.measure_closedBall_lt_top
        (x := (0 : Fin n → ℝ)) (r := R)
  have hs_finite : volume s ≠ (⊤ : ℝ≥0∞) := ne_of_lt hs_lt_top

  have hfφ_nonneg : 0 ≤ᵐ[volume] fun x => ‖f x - φ x‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _

  set χ : (Fin n → ℝ) → ℝ := s.indicator fun _ => (1 : ℝ) with hχ_def

  have hχ_nonneg : 0 ≤ᵐ[volume] χ :=
    Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ s
      · simp [hχ_def, hx]
      · simp [hχ_def, hx]

  have hfφ_norm : MemLp (fun x => ‖f x - φ x‖) (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using hfφ.norm

  have hχ_mem : MemLp χ (ENNReal.ofReal (2 : ℝ)) volume := by
    refine memLp_indicator_const (μ := volume)
      (p := ENNReal.ofReal (2 : ℝ)) hs_meas (1 : ℝ) ?_
    exact Or.inr hs_finite

  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) := Real.HolderConjugate.two_two

  have h_holder :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume)
      (p := (2 : ℝ)) (q := (2 : ℝ)) hpq hfφ_nonneg hχ_nonneg hfφ_norm hχ_mem

  have h_indicator_mul :
      (fun x => ‖f x - φ x‖ * χ x) = s.indicator fun x => ‖f x - φ x‖ := by
    funext x
    by_cases hx : x ∈ s
    · simp [hχ_def, hx]
    · simp [hχ_def, hx]

  have h_integral_eq :
      ∫ x, ‖f x - φ x‖ * χ x ∂volume
        = ∫ x in s, ‖f x - φ x‖ ∂volume := by
    simpa [h_indicator_mul]
      using MeasureTheory.integral_indicator (μ := volume)
        (f := fun x => ‖f x - φ x‖) hs_meas

  have h_chi_sq_eq :
      ∀ᵐ x ∂volume, χ x ^ (2 : ℝ) = χ x :=
    Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ s
      · simp [hχ_def, hx]
      · simp [hχ_def, hx, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]

  have h_int_chi_sq : ∫ x, χ x ^ (2 : ℝ) ∂volume = ∫ x, χ x ∂volume :=
    integral_congr_ae h_chi_sq_eq

  have h_int_chi : ∫ x, χ x ∂volume = (volume s).toReal := by
    simpa [hχ_def]
      using MeasureTheory.integral_indicator (μ := volume)
        (f := fun _ : (Fin n → ℝ) => (1 : ℝ)) hs_meas

  have h_rhs_chi :
      (∫ x, χ x ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
        = (volume s).toReal ^ (1 / 2 : ℝ) := by
    have h := congrArg (fun t : ℝ => t ^ (1 / 2 : ℝ)) h_int_chi_sq
    simpa [h_int_chi] using h

  let A : ℝ := (∫ x, ‖f x - φ x‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)

  have h_eLpNorm_eq :
      eLpNorm (fun x => f x - φ x) 2 volume = ENNReal.ofReal A := by
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
    simpa [A, one_div]
      using MemLp.eLpNorm_eq_integral_rpow_norm
        (μ := volume) (f := fun x => f x - φ x) hp0 hp_top hfφ

  have h_base_nonneg :
      0 ≤ ∫ x, ‖f x - φ x‖ ^ (2 : ℝ) ∂volume :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _

  have hA_nonneg : 0 ≤ A :=
    Real.rpow_nonneg h_base_nonneg _

  have h_toReal :
      (eLpNorm (fun x => f x - φ x) 2 volume).toReal = A := by
    have h := congrArg ENNReal.toReal h_eLpNorm_eq
    have h_ofReal : (ENNReal.ofReal A).toReal = A := ENNReal.toReal_ofReal hA_nonneg
    exact h.trans h_ofReal

  have h_rhs_f :
      (∫ x, ‖f x - φ x‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
        = (eLpNorm (fun x => f x - φ x) 2 volume).toReal := by
    simpa [A] using h_toReal.symm

  have h_holder' :
      ∫ x in s, ‖f x - φ x‖ ∂volume
        ≤ (∫ x, ‖f x - φ x‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
            * (∫ x, χ x ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
    simpa [h_integral_eq]
      using h_holder

  have h_result :
      ∫ x in s, ‖f x - φ x‖ ∂volume
        ≤ (volume s).toReal ^ (1 / 2 : ℝ)
            * (eLpNorm (fun x => f x - φ x) 2 volume).toReal := by
    have htmp := h_holder'
    simp_rw [h_rhs_f, h_rhs_chi, one_div] at htmp
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using htmp

  change
      ∫ x in s, ‖f x - φ x‖ ∂volume
        ≤ (volume s).toReal ^ (1 / 2 : ℝ)
            * (eLpNorm (fun x => f x - φ x) 2 volume).toReal at h_result
  simpa [hs_def] using h_result

/-- Control of the Schwartz tail on the complement of a large ball (placeholder). -/
lemma schwartz_tail_small
    (φ : 𝓢((Fin n → ℝ), ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R > 0, ∫ x, ‖φ x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) < ε :=
  by
  classical
  have hφ_mem : MemLp (fun x => φ x) 1 volume :=
    schwartz_memLp φ 1
  obtain ⟨R, hR_pos, h_tail⟩ :=
    integrable_tail_small (f := fun x => φ x) hφ_mem (ε := ε) hε
  exact ⟨R, hR_pos, h_tail⟩

lemma measurable_set_norm_le
    (R : ℝ) : MeasurableSet {x : (Fin n → ℝ) | ‖x‖ ≤ R} := by
  exact (isClosed_le continuous_norm continuous_const).measurableSet

lemma measurable_set_norm_ge
    (R : ℝ) : MeasurableSet {x : (Fin n → ℝ) | R ≤ ‖x‖} := by
  exact (isClosed_le continuous_const continuous_norm).measurableSet

lemma volume_sphere_norm
    (R : ℝ) (hn : 0 < n) :
    volume {x : (Fin n → ℝ) | ‖x‖ = R} = 0 := by
  classical
  have h_nonempty : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  haveI : Nonempty (Fin n) := h_nonempty
  haveI : Inhabited (Fin n) := Classical.inhabited_of_nonempty h_nonempty
  haveI : Nontrivial (Fin n → ℝ) := Pi.nontrivial
  haveI : NoAtoms (volume : Measure (Fin n → ℝ)) := by infer_instance
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin n → ℝ)) := by infer_instance
  have h_sphere :
      {x : (Fin n → ℝ) | ‖x‖ = R} = Metric.sphere (0 : Fin n → ℝ) R := by
    ext x; simp [Metric.mem_sphere, dist_eq_norm]
  have h := MeasureTheory.Measure.addHaar_sphere (μ := volume) (x := (0 : Fin n → ℝ)) (r := R)
  simpa [h_sphere] using h

lemma ae_eq_norm_le_lt
    (R : ℝ) (hn : 0 < n) :
    {x : (Fin n → ℝ) | R ≤ ‖x‖} =ᵐ[volume]
      {x : (Fin n → ℝ) | R < ‖x‖} := by
  classical
  have hsubset : {x : (Fin n → ℝ) | R < ‖x‖} ⊆ {x : (Fin n → ℝ) | R ≤ ‖x‖} := by
    intro x hx; exact (le_of_lt hx : R ≤ ‖x‖)
  have hdiff :
      {x : (Fin n → ℝ) | R ≤ ‖x‖} \ {x : (Fin n → ℝ) | R < ‖x‖}
        = {x : (Fin n → ℝ) | ‖x‖ = R} := by
    ext x; constructor
    · intro hx
      have hxle : R ≤ ‖x‖ := hx.1
      have hnotlt : ¬ R < ‖x‖ := hx.2
      have hxge : ‖x‖ ≤ R := by
        have : ¬ ‖x‖ > R := by simpa [gt_iff_lt] using hnotlt
        exact le_of_not_gt this
      have hxeq : ‖x‖ = R := le_antisymm hxge hxle
      simp [Set.mem_setOf_eq, hxeq]
    · intro hx
      have hxeq : ‖x‖ = R := by simpa [Set.mem_setOf_eq] using hx
      have hxle : R ≤ ‖x‖ := by simp [hxeq]
      have hnotlt : ¬ R < ‖x‖ := by simp [hxeq]
      exact ⟨hxle, hnotlt⟩
  have hμ_zero :
      volume ({x : (Fin n → ℝ) | R ≤ ‖x‖} \ {x : (Fin n → ℝ) | R < ‖x‖}) = 0 := by
    simpa [hdiff] using volume_sphere_norm (n := n) (R := R) hn
  have hμ'_zero :
      volume ({x : (Fin n → ℝ) | R < ‖x‖} \ {x : (Fin n → ℝ) | R ≤ ‖x‖}) = 0 := by
    simp [Set.diff_eq_empty.2 hsubset]
  exact (MeasureTheory.ae_eq_set).2 ⟨hμ_zero, hμ'_zero⟩

lemma lintegral_enorm_split_ball_tail
    (f : (Fin n → ℝ) → ℂ) (R : ℝ) (hn : 0 < n) :
    ∫⁻ x, ‖f x‖ₑ ∂volume
      = ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict {x | ‖x‖ ≤ R})
          + ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖}) := by
  classical
  have hS : MeasurableSet {x : (Fin n → ℝ) | ‖x‖ ≤ R} :=
    measurable_set_norm_le (R := R)
  have hcompl : {x : (Fin n → ℝ) | ‖x‖ ≤ R}ᶜ = {x : (Fin n → ℝ) | R < ‖x‖} := by
    ext x; simp [not_le]
  have hRestrEq :
      volume.restrict {x : (Fin n → ℝ) | R < ‖x‖}
        = volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖} :=
    (Measure.restrict_congr_set (μ := volume)
      (ae_eq_norm_le_lt (n := n) (R := R) hn)).symm
  have hsplit :=
    (lintegral_add_compl (μ := volume)
      (f := fun x : (Fin n → ℝ) => ‖f x‖ₑ) hS).symm
  calc
    ∫⁻ x, ‖f x‖ₑ ∂volume
        = ∫⁻ x in {x : (Fin n → ℝ) | ‖x‖ ≤ R}, ‖f x‖ₑ ∂volume
            + ∫⁻ x in {x : (Fin n → ℝ) | ‖x‖ ≤ R}ᶜ, ‖f x‖ₑ ∂volume := by
            simpa using hsplit
    _ = ∫⁻ x in {x : (Fin n → ℝ) | ‖x‖ ≤ R}, ‖f x‖ₑ ∂volume
            + ∫⁻ x in {x : (Fin n → ℝ) | R < ‖x‖}, ‖f x‖ₑ ∂volume := by
            simp [hcompl]
    _ = ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict {x : (Fin n → ℝ) | ‖x‖ ≤ R})
            + ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict {x : (Fin n → ℝ) | R < ‖x‖}) := rfl
    _ = ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict {x : (Fin n → ℝ) | ‖x‖ ≤ R})
            + ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) := by
            simp [hRestrEq]

/-- Control the tail `L¹` mass of `‖f - φ‖ₑ` by the tails of `‖f‖ₑ` and `‖φ‖ₑ`. -/
lemma lintegral_tail_enorm_sub_le
    (f : (Fin n → ℝ) → ℂ) (φ : (Fin n → ℝ) → ℂ) (R : ℝ)
    (hφ : AEMeasurable φ (volume.restrict {x | R ≤ ‖x‖})) :
    ∫⁻ x, ‖f x - φ x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖})
      ≤ ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖})
        + ∫⁻ x, ‖φ x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖}) :=
  by
  classical
  let μ := volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}
  have htriangle : ∀ x, ‖f x - φ x‖ₑ ≤ ‖f x‖ₑ + ‖φ x‖ₑ := by
    intro x
    simpa [sub_eq_add_neg] using enorm_add_le (f x) (-φ x)
  have hmono :
      ∫⁻ x, ‖f x - φ x‖ₑ ∂μ
        ≤ ∫⁻ x, ‖f x‖ₑ + ‖φ x‖ₑ ∂μ :=
    lintegral_mono htriangle
  have hsum :
      ∫⁻ x, ‖f x‖ₑ + ‖φ x‖ₑ ∂μ
        = ∫⁻ x, ‖f x‖ₑ ∂μ + ∫⁻ x, ‖φ x‖ₑ ∂μ :=
    by
      simpa [μ]
        using
          (lintegral_add_right'
            (μ := μ)
            (f := fun x => ‖f x‖ₑ)
            (g := fun x => ‖φ x‖ₑ)
            (hg := hφ.enorm))
  have hmono' := hmono
  have hsum' := hsum
  simpa [μ] using (hmono'.trans_eq hsum')

/-- Express the `L¹` seminorm of `f` as a `lintegral`. -/
lemma eLpNorm_one_eq_lintegral_enorm'
    (f : (Fin n → ℝ) → ℂ) :
    eLpNorm f 1 volume = ∫⁻ x, ‖f x‖ₑ ∂volume := by
  simp only [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]

/-- Combine ball and tail bounds to control an `L¹` norm. -/
lemma combine_ball_tail_bound
    (f : (Fin n → ℝ) → ℂ)
    (φ : 𝓢((Fin n → ℝ), ℂ))
    {R ε ε₁ ε₂ ε₃ : ℝ}
    (hn : 0 < n)
    (hε : 0 < ε)
    (hε₁_nn : 0 ≤ ε₁)
    (hε₂ : 0 < ε₂)
    (hε₃ : 0 < ε₃)
    (hf_L1 : MemLp f 1 volume)
    (h_ball : ∫ x, ‖f x - φ x‖ ∂(volume.restrict {x | ‖x‖ ≤ R}) ≤ ε₁)
    (hf_tail : ∫ x, ‖f x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) < ε₂)
    (hφ_tail : ∫ x, ‖φ x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) < ε₃)
    (h_sum : ε₁ + ε₂ + ε₃ < ε) :
    eLpNorm (fun x => f x - φ x) 1 volume < ENNReal.ofReal ε :=
  by
  classical
  set S : Set (Fin n → ℝ) := {x | ‖x‖ ≤ R} with hS_def
  have hS_meas : MeasurableSet S := by
    simpa [S, hS_def] using measurable_set_norm_le (n := n) (R := R)
  have hCompl : Sᶜ = {x : (Fin n → ℝ) | R < ‖x‖} := by
    ext x; simp [S, hS_def, not_le]

  -- Integrability data
  have hf_int : Integrable f volume := (memLp_one_iff_integrable).1 hf_L1
  have hφ_memLp : MemLp (fun x => φ x) 1 volume := schwartz_memLp φ 1
  have hφ_int : Integrable (fun x => φ x) volume :=
    (memLp_one_iff_integrable).1 hφ_memLp
  have hdiff_int : Integrable (fun x => f x - φ x) volume := hf_int.sub hφ_int
  have hφ_int_norm : Integrable (fun x => ‖φ x‖) volume := hφ_int.norm
  have hf_int_norm : Integrable (fun x => ‖f x‖) volume := hf_int.norm

  -- Measurability of φ on the tail measure
  have hφ_meas_volume : AEMeasurable (fun x : Fin n → ℝ => φ x) volume :=
    (SchwartzMap.continuous φ).aemeasurable
  have hφ_tail_meas :
      AEMeasurable (fun x : (Fin n → ℝ) => φ x)
        (volume.restrict {x | R ≤ ‖x‖}) :=
    hφ_meas_volume.mono_measure
      (Measure.restrict_le_self (μ := volume) (s := {x : (Fin n → ℝ) | R ≤ ‖x‖}))

  -- equality of tail measures (≤ vs <)
  have hRestrEq :
      volume.restrict {x : (Fin n → ℝ) | R < ‖x‖}
        = volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖} :=
    (Measure.restrict_congr_set (μ := volume)
        (ae_eq_norm_le_lt (n := n) (R := R) hn)).symm

  -- split the L¹ seminorm into ball and tail parts
  have h_split :
      eLpNorm (fun x => f x - φ x) 1 volume
        = ∫⁻ x, ‖f x - φ x‖ₑ ∂(volume.restrict S)
            + ∫⁻ x, ‖f x - φ x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖}) := by
    have :=
      (lintegral_add_compl (μ := volume)
          (f := fun x : (Fin n → ℝ) => ‖f x - φ x‖ₑ) hS_meas).symm
    simpa [S, hS_def, hCompl, hRestrEq, eLpNorm_one_eq_lintegral_enorm'] using this

  -- define the real integrals appearing in the hypotheses
  set I_ball : ℝ := ∫ x, ‖f x - φ x‖ ∂(volume.restrict S) with hI_ball_def
  set I_tail_f : ℝ := ∫ x, ‖f x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) with hI_tail_f_def
  set I_tail_φ : ℝ := ∫ x, ‖φ x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) with hI_tail_φ_def

  -- convert the real ball integral to a `lintegral`
  have h_ball_eq :
      ∫⁻ x, ‖f x - φ x‖ₑ ∂(volume.restrict S) = ENNReal.ofReal I_ball := by
    have h_nonneg : 0 ≤ᵐ[volume.restrict S] fun x => ‖f x - φ x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    have hInt := (hdiff_int.norm.restrict (s := S))
    have h_ofReal :=
      ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict S)
        (f := fun x => ‖f x - φ x‖)
        hInt h_nonneg
    have h_enorm :=
      lintegral_enorm_of_nonneg
        (μ := volume.restrict S)
        (f := fun x : (Fin n → ℝ) => ‖f x - φ x‖)
        (fun _ => norm_nonneg _)
    simpa [I_ball, hI_ball_def] using h_enorm.trans h_ofReal.symm

  have h_ball_le : I_ball ≤ ε₁ := by simpa [I_ball, hI_ball_def, S, hS_def] using h_ball
  have h_ball_bound :
      ∫⁻ x, ‖f x - φ x‖ₑ ∂(volume.restrict S) ≤ ENNReal.ofReal ε₁ := by
    have := ENNReal.ofReal_le_ofReal h_ball_le
    simpa [h_ball_eq] using this

  -- convert tail integrals to `lintegral`
  have h_tail_f_eq :
      ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖})
        = ENNReal.ofReal I_tail_f := by
    have h_nonneg : 0 ≤ᵐ[volume.restrict {x | R ≤ ‖x‖}] fun x => ‖f x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    have hInt := (hf_int.norm.restrict
      (s := {x : (Fin n → ℝ) | R ≤ ‖x‖}))
    have h_ofReal :=
      ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict {x | R ≤ ‖x‖})
        (f := fun x => ‖f x‖)
        hInt h_nonneg
    have h_enorm :=
      lintegral_enorm_of_nonneg
        (μ := volume.restrict {x | R ≤ ‖x‖})
        (f := fun x : (Fin n → ℝ) => ‖f x‖)
        (fun _ => norm_nonneg _)
    simpa [I_tail_f, hI_tail_f_def] using h_enorm.trans h_ofReal.symm

  have h_tail_φ_eq :
      ∫⁻ x, ‖φ x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖})
        = ENNReal.ofReal I_tail_φ := by
    have h_nonneg : 0 ≤ᵐ[volume.restrict {x | R ≤ ‖x‖}] fun x => ‖φ x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    have hInt := (hφ_int.norm.restrict
      (s := {x : (Fin n → ℝ) | R ≤ ‖x‖}))
    have h_ofReal :=
      ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict {x | R ≤ ‖x‖})
        (f := fun x => ‖φ x‖)
        hInt h_nonneg
    have h_enorm :=
      lintegral_enorm_of_nonneg
        (μ := volume.restrict {x | R ≤ ‖x‖})
        (f := fun x : (Fin n → ℝ) => ‖φ x‖)
        (fun _ => norm_nonneg _)
    simpa [I_tail_φ, hI_tail_φ_def] using h_enorm.trans h_ofReal.symm

  have h_tail_f_le :
      ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖}) ≤ ENNReal.ofReal ε₂ := by
    have hIf_le : I_tail_f ≤ ε₂ :=
      le_of_lt (by simpa [I_tail_f, hI_tail_f_def] using hf_tail)
    have := ENNReal.ofReal_le_ofReal hIf_le
    simpa [h_tail_f_eq] using this

  have h_tail_φ_le :
      ∫⁻ x, ‖φ x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖}) ≤ ENNReal.ofReal ε₃ := by
    have hIφ_le : I_tail_φ ≤ ε₃ :=
      le_of_lt (by simpa [I_tail_φ, hI_tail_φ_def] using hφ_tail)
    have := ENNReal.ofReal_le_ofReal hIφ_le
    simpa [h_tail_φ_eq] using this

  -- apply the tail inequality
  have h_tail_bound :=
    lintegral_tail_enorm_sub_le
      (f := f) (φ := fun x => φ x) (R := R)
      (hφ := hφ_tail_meas)

  have h_tail_le :
      ∫⁻ x, ‖f x - φ x‖ₑ ∂(volume.restrict {x | R ≤ ‖x‖})
        ≤ ENNReal.ofReal ε₂ + ENNReal.ofReal ε₃ := by
    have h_add := add_le_add h_tail_f_le h_tail_φ_le
    have := h_tail_bound.trans h_add
    simpa [add_comm, add_left_comm, add_assoc]
      using this

  -- combine the ball and tail bounds
  have h_total_le :
      eLpNorm (fun x => f x - φ x) 1 volume
        ≤ ENNReal.ofReal ε₁ + (ENNReal.ofReal ε₂ + ENNReal.ofReal ε₃) := by
    simpa [h_split] using add_le_add h_ball_bound h_tail_le

  have h_sum' : ε₁ + (ε₂ + ε₃) < ε := by
    simpa [add_assoc] using h_sum

  have h_final :
      ENNReal.ofReal ε₁ + (ENNReal.ofReal ε₂ + ENNReal.ofReal ε₃) < ENNReal.ofReal ε := by
    have hε₂_nn : 0 ≤ ε₂ := le_of_lt hε₂
    have hε₃_nn : 0 ≤ ε₃ := le_of_lt hε₃
    have h_eq₁ : ENNReal.ofReal ε₂ + ENNReal.ofReal ε₃ = ENNReal.ofReal (ε₂ + ε₃) :=
      (ENNReal.ofReal_add hε₂_nn hε₃_nn).symm
    have h_eq₂ :
        ENNReal.ofReal ε₁ + ENNReal.ofReal (ε₂ + ε₃)
          = ENNReal.ofReal (ε₁ + (ε₂ + ε₃)) :=
      (ENNReal.ofReal_add hε₁_nn (add_nonneg hε₂_nn hε₃_nn)).symm
    have h_temp := (ENNReal.ofReal_lt_ofReal_iff hε).2 h_sum'
    simpa [h_eq₁, h_eq₂] using h_temp

  exact lt_of_le_of_lt h_total_le h_final

/-- Monotonicity of tail integrals with respect to the radius (placeholder). -/
lemma tail_bound_mono
    (F : (Fin n → ℝ) → ℝ) {R₁ R₂ ε : ℝ} (hR : R₁ ≤ R₂) (h_nonneg : ∀ x, 0 ≤ F x)
    (h_int : Integrable F (volume.restrict {x | R₁ ≤ ‖x‖}))
    (h_bound : ∫ x, F x ∂(volume.restrict {x | R₁ ≤ ‖x‖}) < ε) :
    ∫ x, F x ∂(volume.restrict {x | R₂ ≤ ‖x‖}) < ε :=
  by
  classical
  set S₁ : Set (Fin n → ℝ) := {x | R₁ ≤ ‖x‖}
  set S₂ : Set (Fin n → ℝ) := {x | R₂ ≤ ‖x‖}
  have h_subset : S₂ ⊆ S₁ := by
    intro x hx
    have hR₂ : R₂ ≤ ‖x‖ := hx
    exact le_trans hR hR₂
  have hμ_le : (volume.restrict S₂) ≤ (volume.restrict S₁) :=
    Measure.restrict_mono_set (μ := volume) h_subset
  have h_nonneg_ae : 0 ≤ᵐ[volume.restrict S₁] fun x => F x :=
    Filter.Eventually.of_forall h_nonneg
  have h_le :=
    integral_mono_measure (μ := volume.restrict S₂) (ν := volume.restrict S₁)
      hμ_le h_nonneg_ae h_int
  have h_le_real :
      ∫ x, F x ∂(volume.restrict S₂) ≤ ∫ x, F x ∂(volume.restrict S₁) := h_le
  exact lt_of_le_of_lt h_le_real h_bound

/-- Small L² error implies small L¹ error for integrable data. -/
lemma eLpNorm_L2_small_implies_L1_small
    (f : (Fin n → ℝ) → ℂ) (hf_L1 : MemLp f 1 volume) (φ : 𝓢((Fin n → ℝ), ℂ))
    {ε R : ℝ} (hn : 0 < n) (hε : 0 < ε)
    (h_ball : ∫ x, ‖f x - φ x‖ ∂(volume.restrict {x | ‖x‖ ≤ R}) ≤ ε / 2)
    (hf_tail : ∫ x, ‖f x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) < ε / 8)
    (hφ_support : ∀ x, R ≤ ‖x‖ → φ x = 0) :
    eLpNorm (fun x => f x - φ x) 1 volume < ENNReal.ofReal ε := by
  classical
  have h_sum : ε / 2 + ε / 8 + ε / 8 < ε := by
    have : 0 < ε := hε
    nlinarith
  have hφ_memLp : MemLp (fun x => φ x) 1 volume := schwartz_memLp φ 1
  have hφ_int : Integrable (fun x => φ x) volume :=
    (memLp_one_iff_integrable).1 hφ_memLp
  have hφ_int_norm : Integrable (fun x => ‖φ x‖) volume := hφ_int.norm
  have hφ_restrict_int : Integrable (fun x => ‖φ x‖)
      (volume.restrict {x | R ≤ ‖x‖}) :=
    hφ_int_norm.mono_measure Measure.restrict_le_self

  have hφ_tail_zero :
      ∫ x, ‖φ x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) = 0 := by
    have h_meas : MeasurableSet {x : Fin n → ℝ | R ≤ ‖x‖} := by
      have : IsClosed {x : Fin n → ℝ | R ≤ ‖x‖} :=
        isClosed_le continuous_const continuous_norm
      exact this.measurableSet
    have h_zero : ∀ᵐ x ∂(volume.restrict {x | R ≤ ‖x‖}), ‖φ x‖ = 0 := by
      filter_upwards [ae_restrict_mem h_meas] with x hx
      have hφx_zero : φ x = 0 := hφ_support x hx
      simp [hφx_zero]
    exact integral_eq_zero_of_ae h_zero

  have hφ_tail_lt :
      ∫ x, ‖φ x‖ ∂(volume.restrict {x | R ≤ ‖x‖}) < ε / 8 := by
    have hε_eighth_pos : 0 < ε / 8 := by
      have : 0 < (8 : ℝ) := by norm_num
      exact div_pos hε this
    simpa [hφ_tail_zero] using hε_eighth_pos

  exact
    combine_ball_tail_bound (f := f) (φ := φ)
      (R := R) (ε := ε) (ε₁ := ε / 2) (ε₂ := ε / 8) (ε₃ := ε / 8)
      hn hε (by linarith : 0 ≤ ε / 2) (by positivity) (by positivity)
      hf_L1 h_ball hf_tail hφ_tail_lt h_sum
