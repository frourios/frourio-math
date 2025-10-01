import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core0
import Frourio.Analysis.MellinParsevalCore
import Frourio.Analysis.SchwartzDensity.SchwartzDensity
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Topology.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Lp.lpSpace

open MeasureTheory Complex Real SchwartzMap
open scoped Topology ENNReal NNReal ComplexConjugate

noncomputable section

namespace Frourio
open Schwartz

section Auxiliary

/-- Relate pairing with a Schwartz test function to the `L²` inner product. -/
lemma integral_mul_star_eq_inner
    {g : ℝ → ℂ} (hg_mem : MemLp g 2 volume) (φ : SchwartzMap ℝ ℂ) :
    ∫ x, g x * (starRingEnd ℂ) (SchwartzMap.toFun φ x) ∂volume
      =
        @inner ℂ (Lp ℂ 2 volume) _
          ((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
            (fun x => φ x)) (hg_mem.toLp g) := by
  classical
  -- Choose the `L²` representatives of the Schwartz function and `g`.
  set φLp : Lp ℂ 2 volume :=
    ((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
      (fun x => φ x)) with hφLp
  set gLp : Lp ℂ 2 volume := hg_mem.toLp g with hgLp

  -- Express the inner product as an integral in terms of the chosen representatives.
  have h_inner :
      @inner ℂ (Lp ℂ 2 volume) _ φLp gLp
        = ∫ x, conj (φLp x) * gLp x ∂volume := by
    have h_def := MeasureTheory.L2.inner_def (𝕜 := ℂ) (μ := volume) (f := φLp) (g := gLp)
    rw [h_def]
    congr 1
    ext x
    -- The inner product of complex numbers is conj(a) * b
    rw [RCLike.inner_apply, starRingEnd_apply]
    ring
  have h_inner' :
      @inner ℂ (Lp ℂ 2 volume) _ φLp gLp
        = ∫ x, gLp x * conj (φLp x) ∂volume := by
    simpa [mul_comm] using h_inner

  -- Relate the representatives back to the original functions almost everywhere.
  have hφ_eq :
      (fun x => (φLp : ℝ → ℂ) x) =ᵐ[volume] fun x => φ x := by
    simpa [φLp, hφLp] using
      (MemLp.coeFn_toLp
        (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)))
  have hg_eq :
      (fun x => (gLp : ℝ → ℂ) x) =ᵐ[volume] g := by
    simpa [gLp, hgLp] using MemLp.coeFn_toLp hg_mem
  have hφ_star :
      (fun x => (starRingEnd ℂ) (φ x))
        =ᵐ[volume] fun x => conj (φLp x) := by
    refine hφ_eq.mono ?_
    intro x hx
    simp [hx.symm]

  -- Replace the integrand using the almost everywhere equal representatives.
  have h_integral :
      ∫ x, g x * (starRingEnd ℂ) (φ x) ∂volume
        = ∫ x, gLp x * conj (φLp x) ∂volume := by
    refine integral_congr_ae ?_
    have := Filter.EventuallyEq.mul (hg_eq.symm) hφ_star
    simpa using this

  -- Finish by substituting back the definitions of the representatives.
  have h_result := h_integral.trans h_inner'.symm
  simpa [φLp, gLp, hφLp, hgLp] using h_result

/-- Two `L²` functions that have identical pairings with all Schwartz tests
coincide almost everywhere. -/
lemma ae_eq_of_memLp_schwartz_pairings
    {g₁ g₂ : ℝ → ℂ}
    (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume)
    (h_pairings : ∀ φ : SchwartzMap ℝ ℂ,
      ∫ x, g₁ x * (starRingEnd ℂ) (SchwartzMap.toFun φ x) ∂volume =
      ∫ x, g₂ x * (starRingEnd ℂ) (SchwartzMap.toFun φ x) ∂volume) :
    g₁ =ᵐ[volume] g₂ := by
  classical
  -- Lift the functions into `L²`.
  let g₁Lp : Lp ℂ 2 volume := hg₁.toLp g₁
  let g₂Lp : Lp ℂ 2 volume := hg₂.toLp g₂

  -- Pairings with every Schwartz test function agree for the `L²` representatives.
  have h_inner_eq : ∀ φ : SchwartzMap ℝ ℂ,
      @inner ℂ (Lp ℂ 2 volume) _
        ((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
          (fun x => φ x)) g₁Lp
        =
      @inner ℂ (Lp ℂ 2 volume) _
        ((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
          (fun x => φ x)) g₂Lp := by
    intro φ
    have h₁ := integral_mul_star_eq_inner (hg_mem := hg₁) (φ := φ)
    have h₂ := integral_mul_star_eq_inner (hg_mem := hg₂) (φ := φ)
    exact (h₁.symm.trans (h_pairings φ)).trans h₂

  -- The difference has zero pairing with every Schwartz test function.
  have h_inner_zero : ∀ φ : SchwartzMap ℝ ℂ,
      @inner ℂ (Lp ℂ 2 volume) _ (g₁Lp - g₂Lp)
        ((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
          (fun x => φ x)) = 0 := by
    intro φ
    set φLp : Lp ℂ 2 volume :=
      (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
        (fun x => φ x)
    have h_conj := congrArg (starRingEnd ℂ) (h_inner_eq φ)
    have h_flip :
        @inner ℂ (Lp ℂ 2 volume) _ g₁Lp φLp
          = @inner ℂ (Lp ℂ 2 volume) _ g₂Lp φLp := by
      simpa [φLp, inner_conj_symm] using h_conj
    simp [φLp, inner_sub_left, h_flip]

  -- Conclude that the `L²` difference vanishes.
  have h_sub_eq_zero : g₁Lp - g₂Lp = (0 : Lp ℂ 2 volume) :=
    L2_eq_zero_of_inner_schwartz h_inner_zero
  have hLp_eq : g₁Lp = g₂Lp := sub_eq_zero.mp h_sub_eq_zero

  -- Translate the `L²` equality back to almost everywhere equality of functions.
  have h_coe_sub_zero :
      (fun x => (g₁Lp : ℝ → ℂ) x - (g₂Lp : ℝ → ℂ) x)
        =ᵐ[volume] (fun _ : ℝ => (0 : ℂ)) := by
    have h_coe_sub := Lp.coeFn_sub g₁Lp g₂Lp
    have h_zero :
        ((g₁Lp - g₂Lp : Lp ℂ 2 volume) : ℝ → ℂ)
          =ᵐ[volume] fun _ : ℝ => (0 : ℂ) := by
      rw [h_sub_eq_zero]
      exact Lp.coeFn_zero (E := ℂ) (p := (2 : ℝ≥0∞)) (μ := volume)
    exact h_coe_sub.symm.trans h_zero
  have h_coe_eq :
      (fun x => (g₁Lp : ℝ → ℂ) x)
        =ᵐ[volume] fun x => (g₂Lp : ℝ → ℂ) x :=
    h_coe_sub_zero.mono fun x hx => by simpa using sub_eq_zero.mp hx

  -- Use the a.e. equality of representatives together with the `MemLp` representatives.
  have hg₁_coe :
      (fun x => (g₁Lp : ℝ → ℂ) x) =ᵐ[volume] g₁ := MemLp.coeFn_toLp hg₁
  have hg₂_coe :
      (fun x => (g₂Lp : ℝ → ℂ) x) =ᵐ[volume] g₂ := MemLp.coeFn_toLp hg₂
  exact (hg₁_coe.symm.trans h_coe_eq).trans hg₂_coe

end Auxiliary

section Approximation

/-- Helper lemma: For integrable functions, the tail integral can be made arbitrarily small. -/
lemma integrable_tail_small {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ δ > 0, ∃ R > 0, ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ∂volume < δ := by
  classical
  intro δ hδ
  set g : ℝ → ℝ := fun t => ‖f t‖ with hg_def
  have hg_integrable : Integrable g := by
    simpa [hg_def] using hf.norm
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t => norm_nonneg _
  let tail : ℕ → Set ℝ := fun n => {t : ℝ | (n : ℝ) ≤ |t|}
  have h_tail_measurable : ∀ n, MeasurableSet (tail n) := by
    intro n
    have h_closed : IsClosed (tail n) :=
      (isClosed_le continuous_const _root_.continuous_abs)
    simpa [tail] using h_closed.measurableSet
  have h_tendsto :
      Filter.Tendsto
        (fun n : ℕ => ∫ t, Set.indicator (tail n) g t ∂volume)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    have h_meas : ∀ n : ℕ,
        AEStronglyMeasurable (fun t : ℝ => Set.indicator (tail n) g t) volume := by
      intro n
      exact hg_integrable.aestronglyMeasurable.indicator (h_tail_measurable n)
    have h_bound : ∀ n : ℕ, ∀ᵐ t ∂volume,
        ‖Set.indicator (tail n) g t‖ ≤ g t := by
      intro n
      refine Filter.Eventually.of_forall ?_
      intro t
      by_cases ht : t ∈ tail n
      · have hnonneg : 0 ≤ g t := hg_nonneg t
        have h_indicator : Set.indicator (tail n) g t = g t := by
          simp [tail, ht, hg_def]
        simp [h_indicator, Real.norm_eq_abs, hnonneg, abs_of_nonneg hnonneg]
      · have hnonneg : 0 ≤ g t := hg_nonneg t
        have h_indicator : Set.indicator (tail n) g t = 0 := by
          simp [tail, ht, hg_def]
        simp [h_indicator, Real.norm_eq_abs, hnonneg]
    have h_lim : ∀ᵐ t ∂volume,
        Filter.Tendsto (fun n : ℕ => Set.indicator (tail n) g t)
          Filter.atTop (𝓝 (0 : ℝ)) := by
      refine Filter.Eventually.of_forall ?_
      intro t
      obtain ⟨N, hN⟩ := exists_nat_gt |t|
      have h_eventually_zero :
          (fun n : ℕ => Set.indicator (tail n) g t)
            =ᶠ[Filter.atTop] fun _ : ℕ => (0 : ℝ) := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨N, ?_⟩
        intro n hn
        have h_not : ¬ (n : ℝ) ≤ |t| := by
          have h_lt : |t| < (n : ℝ) :=
            lt_of_lt_of_le hN (Nat.cast_le.mpr hn)
          exact not_le_of_gt h_lt
        simp [tail, h_not]
      exact
        (Filter.Tendsto.congr' h_eventually_zero.symm)
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
    have h_tendsto' :=
      MeasureTheory.tendsto_integral_of_dominated_convergence g h_meas
        hg_integrable h_bound h_lim
    simpa using h_tendsto'
  have h_eventually : ∀ᶠ n : ℕ in Filter.atTop,
      ∫ t in tail n, g t ∂volume < δ := by
    have h_tail_nonneg : ∀ n : ℕ, 0 ≤ ∫ t in tail n, g t ∂volume := by
      intro n
      have h_indicator_nonneg :
          0 ≤ᵐ[volume] fun t => Set.indicator (tail n) g t := by
        refine Filter.Eventually.of_forall ?_
        intro t
        by_cases ht : t ∈ tail n
        · simp [tail, ht, hg_def, hg_nonneg t]
        · simp [tail, ht, hg_def, hg_nonneg t]
      have h_eq : ∫ t, Set.indicator (tail n) g t ∂volume
          = ∫ t in tail n, g t ∂volume :=
        MeasureTheory.integral_indicator (h_tail_measurable n)
      have h_integral_nonneg :
          0 ≤ ∫ t, Set.indicator (tail n) g t ∂volume :=
        MeasureTheory.integral_nonneg_of_ae h_indicator_nonneg
      simpa [h_eq] using h_integral_nonneg
    have h_dist := (Metric.tendsto_nhds.mp h_tendsto) δ (by simpa using hδ)
    refine h_dist.mono ?_
    intro n hn
    have h_eq : ∫ t, Set.indicator (tail n) g t ∂volume
        = ∫ t in tail n, g t ∂volume :=
      MeasureTheory.integral_indicator (h_tail_measurable n)
    simpa [Real.dist_eq, h_eq, abs_of_nonneg (h_tail_nonneg n)] using hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
  let M : ℕ := max N 1
  have hM_ge_N : N ≤ M := le_max_left _ _
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos_nat : 0 < M := lt_of_lt_of_le (Nat.succ_pos 0) hM_ge_one
  have hM_tail_lt : ∫ t in tail M, g t ∂volume < δ := by
    exact hN M hM_ge_N
  have hM_pos : 0 < (M : ℝ) := by exact_mod_cast hM_pos_nat
  refine ⟨(M : ℝ), hM_pos, ?_⟩
  simpa [tail] using hM_tail_lt

/-- Hölder's inequality on a ball: L¹ norm bounded by L² norm times measure to the 1/2. -/
lemma eLpNorm_one_le_measure_mul_eLpNorm_two_of_ball
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (R : ℝ) :
    ∫ t in {t : ℝ | |t| ≤ R}, ‖f t‖ ∂volume ≤
      (volume {t : ℝ | |t| ≤ R}).toReal ^ (1/2 : ℝ) *
      (eLpNorm f 2 volume).toReal := by
  classical
  set s : Set ℝ := {t : ℝ | |t| ≤ R}
  set χ : ℝ → ℝ := s.indicator fun _ => (1 : ℝ)

  have h_ball_eq_closedBall : s = Metric.closedBall (0 : ℝ) R := by
    ext t
    simp [s, Metric.mem_closedBall, Real.norm_eq_abs, Real.dist_eq, abs_sub_comm]

  have h_meas : MeasurableSet s := by
    simpa [h_ball_eq_closedBall] using (measurableSet_closedBall :
      MeasurableSet (Metric.closedBall (0 : ℝ) R))

  have h_volume : volume s = ENNReal.ofReal (2 * R) := by
    simp [s, h_ball_eq_closedBall]

  have h_volume_ne_top : volume s ≠ ∞ := by
    simp [h_volume]

  have hf_nonneg : 0 ≤ᵐ[volume] fun t => ‖f t‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _

  have hχ_nonneg : 0 ≤ᵐ[volume] χ :=
    Filter.Eventually.of_forall fun t => by
      by_cases ht : t ∈ s
      · simp [χ, ht]
      · simp [χ, ht]

  have hf_norm : MemLp (fun t => ‖f t‖) (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using hf.norm

  have hχ_mem : MemLp χ (ENNReal.ofReal (2 : ℝ)) volume := by
    refine memLp_indicator_const (μ := volume)
      (p := ENNReal.ofReal (2 : ℝ)) h_meas (1 : ℝ) ?_
    exact Or.inr h_volume_ne_top

  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) := HolderConjugate.two_two

  have h_holder :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume)
      (p := (2 : ℝ)) (q := (2 : ℝ)) hpq hf_nonneg hχ_nonneg hf_norm hχ_mem

  have h_indicator_mul :
      (fun t => ‖f t‖ * χ t) = s.indicator fun t => ‖f t‖ := by
    funext t
    by_cases ht : t ∈ s
    · simp [χ, ht]
    · simp [χ, ht]

  have h_lhs :
      ∫ t, ‖f t‖ * χ t ∂volume = ∫ t in s, ‖f t‖ ∂volume := by
    simpa [h_indicator_mul] using
      MeasureTheory.integral_indicator (μ := volume)
        (f := fun t => ‖f t‖) h_meas

  have h_chi_sq_eq : ∀ᵐ t ∂volume, χ t ^ (2 : ℝ) = χ t :=
    Filter.Eventually.of_forall fun t => by
      by_cases ht : t ∈ s
      · simp [χ, ht]
      · simp [χ, ht, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]

  have h_int_chi_sq : ∫ t, χ t ^ (2 : ℝ) ∂volume = ∫ t, χ t ∂volume :=
    integral_congr_ae h_chi_sq_eq

  have h_int_chi : ∫ t, χ t ∂volume = (volume s).toReal := by
    simpa [χ] using
      MeasureTheory.integral_indicator (μ := volume)
        (f := fun _ : ℝ => (1 : ℝ)) h_meas

  have h_rhs_chi :
      (∫ t, χ t ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
        = (volume s).toReal ^ (1 / 2 : ℝ) := by
    have h := congrArg (fun x : ℝ => x ^ (1 / 2 : ℝ)) h_int_chi_sq
    simpa [h_int_chi] using h

  let A : ℝ := (∫ t, ‖f t‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)

  have h_eLpNorm_eq : eLpNorm f 2 volume = ENNReal.ofReal A := by
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
    simpa [A, one_div] using
      MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
        (f := f) hp0 hp_top hf

  have h_base_nonneg : 0 ≤ ∫ t, ‖f t‖ ^ (2 : ℝ) ∂volume :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _

  have hA_nonneg : 0 ≤ A :=
    Real.rpow_nonneg h_base_nonneg _

  have h_toReal : (eLpNorm f 2 volume).toReal = A := by
    have h := congrArg ENNReal.toReal h_eLpNorm_eq
    have h_ofReal : (ENNReal.ofReal A).toReal = A := ENNReal.toReal_ofReal hA_nonneg
    exact h.trans h_ofReal

  have h_rhs_f :
      (∫ t, ‖f t‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
        = (eLpNorm f 2 volume).toReal := by
    simpa [A] using h_toReal.symm

  have h_holder' :
      ∫ t in s, ‖f t‖ ∂volume ≤
        (∫ t, ‖f t‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) *
          (∫ t, χ t ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
    simpa [h_lhs]
      using h_holder

  have h_result :
      ∫ t in s, ‖f t‖ ∂volume ≤
        (eLpNorm f 2 volume).toReal * (volume s).toReal ^ (1 / 2 : ℝ) := by
    have htmp := h_holder'
    simp_rw [h_rhs_f, h_rhs_chi, one_div] at htmp
    simpa [mul_comm] using htmp

  simpa [s, mul_comm] using h_result

/-- The Lebesgue measure of a ball in ℝ. -/
lemma volume_ball_eq (R : ℝ) :
    volume {t : ℝ | |t| ≤ R} = ENNReal.ofReal (2 * R) := by
  classical
  have h_set : {t : ℝ | |t| ≤ R} = Metric.closedBall (0 : ℝ) R := by
    ext t
    simp [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]
  simp [h_set]

/-- For a finite collection of integrable functions and their tails,
we can find a uniform radius R such that all tails are small. -/
lemma finite_uniform_tail_bound
    {ι : Type*} [Fintype ι] (g : ι → ℝ → ℂ) (hg : ∀ i, Integrable (g i))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ R > 0, ∀ i, ∫ t in {t : ℝ | R ≤ |t|}, ‖g i t‖ ∂volume < δ := by
  classical
  -- Obtain for each index a radius with small tail
  have h_each : ∀ i, ∃ R > 0, ∫ t in {t : ℝ | R ≤ |t|}, ‖g i t‖ ∂volume < δ := by
    intro i
    simpa using integrable_tail_small (hg i) δ hδ
  choose R hR_pos hR_tail using h_each

  -- Use nonnegative reals to keep track of the radii
  let Rnn : ι → ℝ≥0 := fun i => ⟨R i, (hR_pos i).le⟩
  let Rtotal : ℝ := 1 + ∑ i, (Rnn i : ℝ)

  have hsum_nonneg : 0 ≤ ∑ i, (Rnn i : ℝ) :=
    by
      exact_mod_cast (by
        have : (0 : ℝ≥0) ≤ ∑ i, Rnn i := bot_le
        exact this)

  have hRtotal_pos : 0 < Rtotal :=
    add_pos_of_pos_of_nonneg zero_lt_one hsum_nonneg

  -- Each individual radius is bounded by the chosen radius
  have hR_le_total : ∀ i, R i ≤ Rtotal := by
    intro i
    have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
    have h_single_le : Rnn i ≤ ∑ j, Rnn j := by
      classical
      refine Finset.single_le_sum (fun j _ => (bot_le : (0 : ℝ≥0) ≤ Rnn j)) hi
    have h_single_le_coe : (Rnn i : ℝ) ≤ ∑ j, (Rnn j : ℝ) := by
      exact_mod_cast h_single_le
    have h_sum_le : ∑ j, (Rnn j : ℝ) ≤ Rtotal := by
      simp [Rtotal, add_comm]
    calc
      R i = (Rnn i : ℝ) := rfl
      _ ≤ ∑ j, (Rnn j : ℝ) := h_single_le_coe
      _ ≤ Rtotal := h_sum_le

  refine ⟨Rtotal, hRtotal_pos, ?_⟩
  intro i
  -- The tail for R is contained in the tail for the individual radius
  have h_subset : {t : ℝ | Rtotal ≤ |t|} ⊆ {t : ℝ | R i ≤ |t|} := by
    intro t ht
    exact (hR_le_total i).trans ht
  have h_subset_ae :
      {t : ℝ | Rtotal ≤ |t|} ≤ᵐ[volume] {t : ℝ | R i ≤ |t|} :=
    (Filter.Eventually.of_forall h_subset)

  -- Apply monotonicity of integrals on sets
  have h_integrable_on : IntegrableOn (fun t => ‖g i t‖)
      {t : ℝ | R i ≤ |t|} volume :=
    ((hg i).norm).integrableOn
  have h_nonneg :
      0 ≤ᵐ[(volume.restrict {t : ℝ | R i ≤ |t|})]
        fun t => ‖g i t‖ :=
    (MeasureTheory.ae_restrict_of_ae (Filter.Eventually.of_forall
      (fun _ => norm_nonneg _)))

  have h_le :=
    MeasureTheory.setIntegral_mono_set (μ := volume)
      (s := {t : ℝ | Rtotal ≤ |t|}) (t := {t : ℝ | R i ≤ |t|})
      h_integrable_on h_nonneg h_subset_ae

  have h_tail := hR_tail i
  have h_lt : ∫ t in {t : ℝ | Rtotal ≤ |t|}, ‖g i t‖ ∂volume
      ≤ ∫ t in {t : ℝ | R i ≤ |t|}, ‖g i t‖ ∂volume := h_le
  exact lt_of_le_of_lt h_lt h_tail

/-- Helper: bound tail of difference by triangle inequality. -/
lemma tail_integral_diff_le
    (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (R : ℝ) :
    ∫ t in {t : ℝ | R ≤ |t|}, ‖f t - g t‖ ∂volume ≤
      ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ∂volume +
      ∫ t in {t : ℝ | R ≤ |t|}, ‖g t‖ ∂volume := by
  classical
  set tail : Set ℝ := {t : ℝ | R ≤ |t|}
  have h_meas : MeasurableSet tail :=
    (isClosed_le continuous_const continuous_norm).measurableSet

  have h_ae :
      (fun t => ‖f t - g t‖) ≤ᵐ[volume.restrict tail]
        fun t => ‖f t‖ + ‖g t‖ :=
    MeasureTheory.ae_restrict_of_ae <|
      Filter.Eventually.of_forall fun _ => norm_sub_le _ _

  have h_int_left : IntegrableOn (fun t => ‖f t - g t‖) tail volume :=
    (hf.sub hg).norm.integrableOn
  have h_int_right : IntegrableOn (fun t => ‖f t‖ + ‖g t‖) tail volume := by
    have hf_norm : IntegrableOn (fun t => ‖f t‖) tail volume := hf.norm.integrableOn
    have hg_norm : IntegrableOn (fun t => ‖g t‖) tail volume := hg.norm.integrableOn
    exact hf_norm.add hg_norm

  have h_le :=
    MeasureTheory.setIntegral_mono_ae_restrict h_int_left h_int_right h_ae

  have h_sum :
      ∫ t in tail, (‖f t‖ + ‖g t‖) ∂volume
        = ∫ t in tail, ‖f t‖ ∂volume + ∫ t in tail, ‖g t‖ ∂volume := by
    have hf_norm : IntegrableOn (fun t => ‖f t‖) tail volume := hf.norm.integrableOn
    have hg_norm : IntegrableOn (fun t => ‖g t‖) tail volume := hg.norm.integrableOn
    simpa using MeasureTheory.integral_add hf_norm hg_norm

  exact h_le.trans_eq h_sum

/-- If Schwartz functions φₙ approximate f in both L¹ and L², then their Fourier
transforms converge pointwise to the Fourier transform of f.
We require L¹ convergence explicitly, since L² convergence alone is insufficient. -/
lemma fourierIntegral_tendsto_of_schwartz_approx
    {φ : ℕ → SchwartzMap ℝ ℂ} {f : ℝ → ℂ}
    (hf_L1 : Integrable f) (hφ_L1 : ∀ n, Integrable (fun t : ℝ => φ n t))
    (hφ_tendsto_L1 : Filter.Tendsto (fun n =>
        eLpNorm (fun t : ℝ => f t - φ n t) 1 volume) Filter.atTop (𝓝 0))
    (ξ : ℝ) :
    Filter.Tendsto (fun n => fourierIntegral (fun t => φ n t) ξ)
      Filter.atTop (𝓝 (fourierIntegral f ξ)) := by
  -- Strategy: Show that the integrand converges and use dominated convergence
  -- fourierIntegral g ξ = ∫ t, exp(-2πi ξ t) * g(t) dt

  -- We want to show: ∫ exp(-2πi ξ t) * φ n(t) dt → ∫ exp(-2πi ξ t) * f(t) dt

  -- The integrand is: exp(-2πi ξ t) * (φ n(t) - f(t))
  -- We need: this integrand → 0 in L¹

  -- Step 1: We have L¹ convergence by assumption

  -- Step 2: Use continuity of Fourier integral in L¹ norm
  rw [Metric.tendsto_atTop]
  intro ε hε_pos

  -- From L¹ convergence (hφ_tendsto_L1), extract N such that the norm is small
  -- hφ_tendsto_L1 : eLpNorm (f - φ n) → 0
  -- We need: eventually eLpNorm (f - φ n) < ε

  -- Get N such that eLpNorm is small (use ε / 2 to obtain a strict ε bound)
  have h_small_norm : ∃ N, ∀ n ≥ N,
      eLpNorm (fun t => f t - φ n t) 1 volume ≤ ENNReal.ofReal (ε / 2) := by
    have hε_half_pos : 0 < ε / 2 := half_pos hε_pos
    have hε_pos' : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := by
      simpa [ENNReal.ofReal_pos] using (show 0 < ε / 2 from hε_half_pos)
    rw [ENNReal.tendsto_atTop_zero] at hφ_tendsto_L1
    exact hφ_tendsto_L1 (ENNReal.ofReal (ε / 2)) hε_pos'

  obtain ⟨N, hN⟩ := h_small_norm

  use N
  intro n hn

  -- Bound the difference of Fourier integrals by L¹ norm
  have h_diff : dist (fourierIntegral (fun t => φ n t) ξ) (fourierIntegral f ξ) ≤
      ∫ t, ‖φ n t - f t‖ ∂volume := by
    classical
    have h_sub :=
      (fourierIntegral_sub (f := fun t : ℝ => φ n t) (g := f)
        (hf := hφ_L1 n) (hg := hf_L1) ξ).symm
    have h_dist_eq :
        dist (fourierIntegral (fun t => φ n t) ξ) (fourierIntegral f ξ)
          = ‖fourierIntegral (fun t : ℝ => φ n t - f t) ξ‖ := by
      simp [dist_eq_norm, h_sub]
    have h_norm := norm_fourierIntegral_le (fun t : ℝ => φ n t - f t) ξ
    simpa [h_dist_eq] using h_norm

  calc dist (fourierIntegral (fun t => φ n t) ξ) (fourierIntegral f ξ)
      ≤ ∫ t, ‖φ n t - f t‖ ∂volume := h_diff
    _ < ε := by
        -- This follows from hN
        -- Convert eLpNorm to an integral bound and compare with ε / 2 < ε
        classical
        have hε_half_pos : 0 < ε / 2 := half_pos hε_pos
        have hε_half_nonneg : 0 ≤ ε / 2 := hε_half_pos.le
        set g : ℝ → ℂ := fun t => f t - φ n t
        have hg_int : Integrable g := hf_L1.sub (hφ_L1 n)
        have hg_memLp : MemLp g 1 volume :=
          (memLp_one_iff_integrable).2 hg_int
        have hp0 : (1 : ℝ≥0∞) ≠ 0 := by simp
        have hp_top : (1 : ℝ≥0∞) ≠ ∞ := by simp
        have hg_eLp : eLpNorm g 1 volume = ENNReal.ofReal (∫ t, ‖g t‖ ∂volume) := by
          simpa [g, one_div, Real.rpow_one] using
            MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
              (f := g) hp0 hp_top hg_memLp
        have hg_integral_nonneg : 0 ≤ ∫ t, ‖g t‖ ∂volume :=
          integral_nonneg fun _ => norm_nonneg _
        have hg_toReal :
            (∫ t, ‖g t‖ ∂volume) =
              (eLpNorm g 1 volume).toReal := by
          have h := congrArg ENNReal.toReal hg_eLp
          simpa [ENNReal.toReal_ofReal, hg_integral_nonneg] using h.symm
        have h_norm := hN n hn
        have h_norm' : eLpNorm g 1 volume ≤ ENNReal.ofReal (ε / 2) := by
          simpa [g] using h_norm
        have h_toReal_le :
            (eLpNorm g 1 volume).toReal ≤ ε / 2 :=
          ENNReal.toReal_le_of_le_ofReal hε_half_nonneg h_norm'
        have h_integral_le :
            ∫ t, ‖g t‖ ∂volume ≤ ε / 2 := by
          simpa [hg_toReal] using h_toReal_le
        have h_integral_lt : ∫ t, ‖g t‖ ∂volume < ε :=
          lt_of_le_of_lt h_integral_le (half_lt_self hε_pos)
        simpa [g, norm_sub_rev] using h_integral_lt

/-- If Schwartz functions φₙ approximate f in L², then their Fourier transforms
form a Cauchy sequence in L², which converges strongly to some limit in L². -/
lemma fourierIntegral_L2_convergence_of_schwartz_approx
    {φ : ℕ → SchwartzMap ℝ ℂ} {f : ℝ → ℂ}
    (_hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (hφ_L1 : ∀ n, Integrable (fun t : ℝ => φ n t))
    (hφ_L2 : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume)
    (hφ_tendsto : Filter.Tendsto (fun n =>
        eLpNorm (fun t : ℝ => f t - φ n t) 2 volume) Filter.atTop (𝓝 0)) :
    ∃ (ψLp : ℕ → Lp ℂ 2 volume) (ψ_lim : Lp ℂ 2 volume),
      (∀ n, ψLp n = (fourierIntegral_memLp_of_schwartz (φ n)).toLp
                      (fun ξ => fourierIntegral (fun t : ℝ => φ n t) ξ)) ∧
      Filter.Tendsto ψLp Filter.atTop (𝓝 ψ_lim) := by
  -- Construct the sequence of Fourier transforms as L² functions
  let ψFun : ℕ → ℝ → ℂ := fun n ξ => fourierIntegral (fun t : ℝ => φ n t) ξ
  have hψ_mem : ∀ n, MemLp (ψFun n) 2 volume := fun n =>
    fourierIntegral_memLp_of_schwartz (φ n)

  let ψLp : ℕ → Lp ℂ 2 volume := fun n => (hψ_mem n).toLp (ψFun n)

  -- Show that ψLp is Cauchy in L²
  have hψ_cauchy : CauchySeq ψLp := by
    simpa [ψLp, ψFun] using
      fourierIntegral_cauchySeq_of_schwartz_tendsto hf_L2 hφ_L1 hφ_L2 hφ_tendsto

  -- Since Lp is complete, the Cauchy sequence converges
  have hψ_complete : ∃ ψ_lim : Lp ℂ 2 volume, Filter.Tendsto ψLp Filter.atTop (𝓝 ψ_lim) :=
    cauchySeq_tendsto_of_complete hψ_cauchy

  obtain ⟨ψ_lim, hψ_lim⟩ := hψ_complete

  exact ⟨ψLp, ψ_lim, fun n => rfl, hψ_lim⟩

/-- When a function `f` is approximated in `L²` by Schwartz functions, the
corresponding Fourier transforms form a Cauchy sequence in `L²` and hence
converge to some limit in `L²`.  We package this convergence datum. -/
lemma fourierIntegral_memLp_limit
    {φ : ℕ → SchwartzMap ℝ ℂ} {f : ℝ → ℂ}
    (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume)
    (hφ_L1 : ∀ n, Integrable (fun t : ℝ => φ n t))
    (hφ_L2 : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume)
    (hφ_tendsto : Filter.Tendsto (fun n =>
        eLpNorm (fun t : ℝ => f t - φ n t) 2 volume) Filter.atTop (𝓝 0)) :
    ∃ (ψLp : ℕ → Lp ℂ 2 volume) (ψ_lim : Lp ℂ 2 volume),
      (∀ n, ψLp n =
        (fourierIntegral_memLp_of_schwartz (φ n)).toLp
          (fun ξ => fourierIntegral (fun t : ℝ => φ n t) ξ)) ∧
      Filter.Tendsto ψLp Filter.atTop (𝓝 ψ_lim) := by
  classical
  exact fourierIntegral_L2_convergence_of_schwartz_approx
    hf_L1 hf_L2 hφ_L1 hφ_L2 hφ_tendsto

lemma fourierIntegral_memLp_of_memLp (f : ℝ → ℂ)
    (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume) :
    ∃ (φ : ℕ → SchwartzMap ℝ ℂ)
      (hφ_L1 : ∀ n, Integrable (fun t : ℝ => φ n t))
      (hφ_L2 : ∀ n, MemLp (fun t : ℝ => φ n t) 2 volume)
      (ψLp : ℕ → Lp ℂ 2 volume) (ψ_lim : Lp ℂ 2 volume),
        (∀ n, ψLp n =
          (fourierIntegral_memLp_of_schwartz (φ n)).toLp
            (fun ξ => fourierIntegral (fun t : ℝ => φ n t) ξ)) ∧
        Filter.Tendsto ψLp Filter.atTop (𝓝 ψ_lim) :=
by
  classical
  obtain ⟨φ, hφ_L1, hφ_L2, hφ_tendsto⟩ :=
    exists_schwartz_L2_approx f hf_L1 hf_L2
  obtain ⟨ψLp, ψ_lim, hψLp_def, hψ_lim⟩ :=
    fourierIntegral_memLp_limit hf_L1 hf_L2 hφ_L1 hφ_L2 hφ_tendsto
  exact ⟨φ, hφ_L1, hφ_L2, ψLp, ψ_lim, hψLp_def, hψ_lim⟩

end Approximation

/-- For an `L²` function, the square of its norm is integrable. -/
lemma integrable_norm_sq_of_memLp_two {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    Integrable (fun t : ℝ => ‖f t‖ ^ 2) := by
  have h := hf.integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)
  simpa using h

/-- The tail of an `L²` function has small squared norm. -/
lemma memLp_two_tail_norm_sq_small {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    ∀ δ > 0, ∃ R > 0,
      ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ^ 2 ∂volume < δ := by
  intro δ hδ
  have h_int : Integrable (fun t : ℝ => ‖f t‖ ^ 2) :=
    integrable_norm_sq_of_memLp_two hf
  have h_int_complex :
      Integrable (fun t : ℝ => ((‖f t‖ ^ 2 : ℝ) : ℂ)) :=
    h_int.ofReal
  obtain ⟨R, hR_pos, h_tail⟩ :=
    integrable_tail_small
      (f := fun t : ℝ => ((‖f t‖ ^ 2 : ℝ) : ℂ)) h_int_complex δ hδ
  refine ⟨R, hR_pos, ?_⟩
  have h_norm : ∀ t, ‖(‖f t‖ ^ 2 : ℂ)‖ = ‖f t‖ ^ 2 := by
    intro t; simp
  simpa [h_norm] using h_tail

/-- Truncating an integrable function to a ball preserves integrability. -/
lemma integrable_indicator_ball_of_integrable {f : ℝ → ℂ}
    (hf : Integrable f) (R : ℝ) :
    Integrable (fun t : ℝ => Set.indicator {t : ℝ | |t| ≤ R} f t) := by
  classical
  have hset : MeasurableSet {t : ℝ | |t| ≤ R} := by
    have : {t : ℝ | |t| ≤ R} = Metric.closedBall (0 : ℝ) R := by
      ext t; simp [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]
    simpa [this] using (measurableSet_closedBall :
      MeasurableSet (Metric.closedBall (0 : ℝ) R))
  simpa using hf.indicator hset

/-- The support of a ball-truncated function is contained in that ball. -/
lemma tsupport_indicator_subset_ball {f : ℝ → ℂ} {R : ℝ} :
    tsupport (fun t : ℝ => Set.indicator {t : ℝ | |t| ≤ R} f t)
      ⊆ Metric.closedBall (0 : ℝ) R := by
  classical
  have h_support_subset :
      Function.support (fun t : ℝ => Set.indicator {t : ℝ | |t| ≤ R} f t)
        ⊆ {t : ℝ | |t| ≤ R} := by
    intro t ht
    have h_ne : Set.indicator {t : ℝ | |t| ≤ R} f t ≠ 0 := ht
    by_contra h_mem
    have h_zero : Set.indicator {t : ℝ | |t| ≤ R} f t = 0 := by
      simp [Set.indicator_of_notMem, h_mem]
    exact h_ne h_zero
  have h_closure_eq :
      closure {t : ℝ | |t| ≤ R} = Metric.closedBall (0 : ℝ) R := by
    have h_closed : IsClosed {t : ℝ | |t| ≤ R} :=
      (isClosed_le continuous_norm continuous_const)
    have h_eq : {t : ℝ | |t| ≤ R} = Metric.closedBall (0 : ℝ) R := by
      ext t; simp [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]
    simp [h_eq]
  intro x hx
  have hx_closure : x ∈ closure
      (Function.support fun t : ℝ => Set.indicator {t : ℝ | |t| ≤ R} f t) := by
    simpa [tsupport] using hx
  have hx_subset : x ∈ closure {t : ℝ | |t| ≤ R} :=
    (closure_mono h_support_subset) hx_closure
  simpa [h_closure_eq] using hx_subset

/-- Removing the ball of radius `R` from `f` corresponds to restricting `f` to the complement. -/
lemma sub_indicator_ball_eq_indicator_compl (f : ℝ → ℂ) (R : ℝ) :
    (fun t : ℝ => f t - Set.indicator {t : ℝ | |t| ≤ R} f t)
      = fun t : ℝ => Set.indicator {t : ℝ | |t| ≤ R}ᶜ f t := by
  classical
  funext t
  by_cases ht : |t| ≤ R
  · have ht_mem : t ∈ {t : ℝ | |t| ≤ R} := ht
    have ht_not_mem_compl : t ∉ {t : ℝ | |t| ≤ R}ᶜ := by
      intro h; exact h ht_mem
    simp [ht_mem, ht_not_mem_compl, sub_eq_add_neg]
  · have ht_not_mem : t ∉ {t : ℝ | |t| ≤ R} := ht
    have ht_mem_compl : t ∈ {t : ℝ | |t| ≤ R}ᶜ := by
      simpa [Set.mem_setOf_eq] using ht
    simp [ht_not_mem, ht_mem_compl, sub_eq_add_neg]

/-- Small L¹ and L² tails for integrable and `L²` functions. -/
lemma integrable_memLp_tail_small
    {f : ℝ → ℂ} (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume) :
    ∀ δ > 0, ∃ R > 0,
      ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ∂volume < δ ∧
      ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ^ 2 ∂volume < δ := by
  intro δ hδ
  classical
  -- Choose radii controlling the L¹- and L²-tails separately.
  obtain ⟨R₁, hR₁_pos, hR₁_tail⟩ := integrable_tail_small hf_L1 δ hδ
  obtain ⟨R₂, hR₂_pos, hR₂_tail⟩ := memLp_two_tail_norm_sq_small hf_L2 δ hδ
  -- Use the larger radius so both tails are simultaneously small.
  let R := max R₁ R₂
  have hR_pos : 0 < R := lt_of_lt_of_le hR₁_pos (le_max_left _ _)
  have hR_ge_R₁ : R₁ ≤ R := le_max_left _ _
  have hR_ge_R₂ : R₂ ≤ R := le_max_right _ _

  -- Describe the relevant tail sets.
  set sR : Set ℝ := {t : ℝ | R ≤ |t|} with hsR_def
  set s₁ : Set ℝ := {t : ℝ | R₁ ≤ |t|} with hs₁_def
  set s₂ : Set ℝ := {t : ℝ | R₂ ≤ |t|} with hs₂_def
  have hsR_subset_s₁ : sR ⊆ s₁ := by
    intro t ht
    exact le_trans hR_ge_R₁ ht
  have hsR_subset_s₂ : sR ⊆ s₂ := by
    intro t ht
    exact le_trans hR_ge_R₂ ht

  -- Measurability of the tail sets.
  have hsR_meas : MeasurableSet sR :=
    (isClosed_le continuous_const _root_.continuous_abs).measurableSet
  have hs₁_meas : MeasurableSet s₁ :=
    (isClosed_le continuous_const _root_.continuous_abs).measurableSet
  have hs₂_meas : MeasurableSet s₂ :=
    (isClosed_le continuous_const _root_.continuous_abs).measurableSet

  -- Nonnegativity of the truncated L¹ and L² integrands.
  have h_nonneg_L1 : 0 ≤ᵐ[volume] Set.indicator sR (fun t => ‖f t‖) := by
    refine Filter.Eventually.of_forall ?_
    intro t
    by_cases ht : t ∈ sR
    · simp [Set.indicator_of_mem, ht, norm_nonneg]
    · simp [Set.indicator_of_notMem, ht, norm_nonneg]
  have h_nonneg_L2 : 0 ≤ᵐ[volume] Set.indicator sR (fun t => ‖f t‖ ^ 2) := by
    refine Filter.Eventually.of_forall ?_
    intro t
    by_cases ht : t ∈ sR
    · simp [Set.indicator_of_mem, ht, sq_nonneg]
    · simp [Set.indicator_of_notMem, ht, sq_nonneg]

  -- Integrability of the dominating functions.
  have h_int_L1 : Integrable (fun t => Set.indicator s₁ (fun t => ‖f t‖) t) volume :=
    (hf_L1.norm.indicator hs₁_meas)
  have h_int_L2 : Integrable (fun t => Set.indicator s₂ (fun t => ‖f t‖ ^ 2) t) volume :=
    (integrable_norm_sq_of_memLp_two hf_L2).indicator hs₂_meas

  -- Pointwise comparison of the truncated L¹ integrands.
  have h_le_L1 : Set.indicator sR (fun t => ‖f t‖)
      ≤ᵐ[volume] Set.indicator s₁ (fun t => ‖f t‖) :=
    Filter.Eventually.of_forall <| by
      intro t
      by_cases ht : t ∈ sR
      · have ht' : t ∈ s₁ := hsR_subset_s₁ ht
        simp [Set.indicator_of_mem, ht, ht', norm_nonneg]
      · by_cases ht₁ : t ∈ s₁
        · simp [Set.indicator_of_mem, ht₁, ht, norm_nonneg]
        · simp [Set.indicator_of_notMem, ht, ht₁, norm_nonneg]

  -- Pointwise comparison of the truncated L² integrands.
  have h_le_L2 : Set.indicator sR (fun t => ‖f t‖ ^ 2)
      ≤ᵐ[volume] Set.indicator s₂ (fun t => ‖f t‖ ^ 2) :=
    Filter.Eventually.of_forall <| by
      intro t
      by_cases ht : t ∈ sR
      · have ht' : t ∈ s₂ := hsR_subset_s₂ ht
        simp [Set.indicator_of_mem, ht, ht', sq_nonneg]
      · by_cases ht₂ : t ∈ s₂
        · simp [Set.indicator_of_mem, ht₂, ht, sq_nonneg]
        · simp [Set.indicator_of_notMem, ht, ht₂, sq_nonneg]

  -- Monotonicity for the L¹ tail integral.
  have h_tail_L1_le :
      ∫ t in sR, ‖f t‖ ∂volume ≤ ∫ t in s₁, ‖f t‖ ∂volume := by
    simpa [MeasureTheory.integral_indicator, hsR_meas, hs₁_meas]
      using
        integral_mono_of_nonneg (μ := volume)
          (f := fun t => Set.indicator sR (fun t => ‖f t‖) t)
          (g := fun t => Set.indicator s₁ (fun t => ‖f t‖) t)
          h_nonneg_L1 h_int_L1 h_le_L1

  -- Monotonicity for the L² tail integral.
  have h_tail_L2_le :
      ∫ t in sR, ‖f t‖ ^ 2 ∂volume ≤ ∫ t in s₂, ‖f t‖ ^ 2 ∂volume := by
    simpa [MeasureTheory.integral_indicator, hsR_meas, hs₂_meas]
      using
        integral_mono_of_nonneg (μ := volume)
          (f := fun t => Set.indicator sR (fun t => ‖f t‖ ^ 2) t)
          (g := fun t => Set.indicator s₂ (fun t => ‖f t‖ ^ 2) t)
          h_nonneg_L2 h_int_L2 h_le_L2

  -- Both tails are now below the requested bound `δ`.
  have h_tail_L1_small : ∫ t in sR, ‖f t‖ ∂volume < δ :=
    lt_of_le_of_lt h_tail_L1_le <| by simpa [s₁, hs₁_def] using hR₁_tail
  have h_tail_L2_small : ∫ t in sR, ‖f t‖ ^ 2 ∂volume < δ :=
    lt_of_le_of_lt h_tail_L2_le <| by simpa [s₂, hs₂_def] using hR₂_tail
  refine ⟨R, hR_pos, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [sR, hsR_def] using h_tail_L1_small
  · simpa [sR, hsR_def] using h_tail_L2_small

/-- Control the L¹ error after truncating a function outside a ball using the tail integral. -/
lemma eLpNorm_one_tail_indicator_sub
    {f : ℝ → ℂ} (hf : Integrable f) {R δ : ℝ}
    (h_tail : ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ∂volume < δ) :
    eLpNorm (fun t : ℝ => f t - Set.indicator {t : ℝ | |t| ≤ R} f t) 1 volume
      < ENNReal.ofReal δ := by
  classical
  set ball : Set ℝ := {t : ℝ | |t| ≤ R} with h_ball
  set tail : Set ℝ := {t : ℝ | R < |t|} with h_tail_def
  set tailLe : Set ℝ := {t : ℝ | R ≤ |t|} with h_tailLe

  -- Describe the difference as an indicator of the tail set.
  have h_indicator_eq :
      (fun t : ℝ => f t - Set.indicator ball f t) = Set.indicator tail f := by
    funext t
    by_cases ht : |t| ≤ R
    · have ht_ball : t ∈ ball := by simpa [ball, Set.mem_setOf_eq] using ht
      have ht_tail : t ∉ tail := by
        have : ¬ R < |t| := not_lt.mpr ht
        simpa [tail, Set.mem_setOf_eq] using this
      simp [ball, tail, ht_ball, ht_tail]
    · have ht' : R < |t| := not_le.mp ht
      have ht_ball : t ∉ ball := by
        have : ¬ |t| ≤ R := ht
        simpa [ball, Set.mem_setOf_eq] using this
      have ht_tail : t ∈ tail := by simpa [tail, Set.mem_setOf_eq] using ht'
      simp [ball, tail, ht_ball, ht_tail, ht']

  -- Basic measurability facts about the tail regions.
  have h_tail_meas : MeasurableSet tail := by
    have : tail = (fun x : ℝ => |x|) ⁻¹' Set.Ioi R := by
      ext t; simp [tail]
    have h_abs : Measurable fun x : ℝ => |x| :=
      (_root_.continuous_abs : Continuous fun x : ℝ => |x|).measurable
    simpa [this] using h_abs measurableSet_Ioi
  have h_tailLe_meas : MeasurableSet tailLe := by
    have : tailLe = (fun x : ℝ => |x|) ⁻¹' Set.Ici R := by
      ext t; simp [tailLe]
    have h_abs : Measurable fun x : ℝ => |x| :=
      (_root_.continuous_abs : Continuous fun x : ℝ => |x|).measurable
    simpa [this] using h_abs measurableSet_Ici

  have h_subset : tail ⊆ tailLe := by
    intro t ht
    have : R < |t| := by simpa [tail, Set.mem_setOf_eq] using ht
    exact (le_of_lt this : R ≤ |t|)

  have h_eLp_tail :
      eLpNorm (fun t => f t - Set.indicator ball f t) 1 volume
        = ∫⁻ t in tail, (‖f t‖₊ : ℝ≥0∞) ∂volume := by
    calc
      eLpNorm (fun t => f t - Set.indicator ball f t) 1 volume
          = eLpNorm (Set.indicator tail f) 1 volume := by
              simp [h_indicator_eq]
      _ = ∫⁻ t, ‖Set.indicator tail f t‖ₑ ∂volume := by
              simp [eLpNorm_one_eq_lintegral_enorm]
      _ = ∫⁻ t, Set.indicator tail (fun t => ENNReal.ofReal ‖f t‖) t ∂volume := by
              refine MeasureTheory.lintegral_congr_ae ?_
              refine Filter.Eventually.of_forall ?_
              intro t
              by_cases ht : t ∈ tail
              · simp [Set.indicator_of_mem, ht]
              · simp [Set.indicator_of_notMem, ht]
      _ = ∫⁻ t in tail, (‖f t‖₊ : ℝ≥0∞) ∂volume := by
              simpa [ENNReal.ofReal_eq_coe_nnreal, norm_nonneg] using
                (MeasureTheory.lintegral_indicator (μ := volume)
                  (hs := h_tail_meas)
                  (f := fun t => ENNReal.ofReal ‖f t‖))

  -- Compare the strict tail integral with the non-strict tail integral.
  have h_tail_le :
      ∫⁻ t in tail, (‖f t‖₊ : ℝ≥0∞) ∂volume
        ≤ ∫⁻ t in tailLe, (‖f t‖₊ : ℝ≥0∞) ∂volume := by
    have h_ae_le :
        (fun t => Set.indicator tail (fun t => (‖f t‖₊ : ℝ≥0∞)) t)
          ≤ᵐ[volume]
        (fun t => Set.indicator tailLe (fun t => (‖f t‖₊ : ℝ≥0∞)) t) := by
      refine Filter.Eventually.of_forall ?_
      intro t
      by_cases ht : t ∈ tail
      · have ht' : t ∈ tailLe := h_subset ht
        simp [Set.indicator_of_mem, ht, ht']
      · simp [Set.indicator_of_notMem, ht]
    have h_lintegral_tail :=
      (MeasureTheory.lintegral_indicator (μ := volume)
        (hs := h_tail_meas)
        (f := fun t => (‖f t‖₊ : ℝ≥0∞)))
    have h_lintegral_tailLe :=
      (MeasureTheory.lintegral_indicator (μ := volume)
        (hs := h_tailLe_meas)
        (f := fun t => (‖f t‖₊ : ℝ≥0∞)))
    refine
      calc
        ∫⁻ t in tail, (‖f t‖₊ : ℝ≥0∞) ∂volume
            = ∫⁻ t, Set.indicator tail (fun t => (‖f t‖₊ : ℝ≥0∞)) t ∂volume := by
                simpa using h_lintegral_tail.symm
        _ ≤ ∫⁻ t, Set.indicator tailLe (fun t => (‖f t‖₊ : ℝ≥0∞)) t ∂volume :=
              MeasureTheory.lintegral_mono_ae h_ae_le
        _ = ∫⁻ t in tailLe, (‖f t‖₊ : ℝ≥0∞) ∂volume := by
              simpa using h_lintegral_tailLe

  -- Convert the assumption to an inequality in `ℝ≥0∞`.
  have h_indicator_ofReal :
      (fun t => ENNReal.ofReal (Set.indicator tailLe (fun t => ‖f t‖) t))
        = Set.indicator tailLe (fun t => ENNReal.ofReal ‖f t‖) := by
    funext t
    by_cases ht : t ∈ tailLe
    · simp [Set.indicator_of_mem, ht]
    · simp [Set.indicator_of_notMem, ht]
  have h_indicator_coe :
      Set.indicator tailLe (fun t => ENNReal.ofReal ‖f t‖)
        = Set.indicator tailLe (fun t => (‖f t‖₊ : ℝ≥0∞)) := by
    funext t
    by_cases ht : t ∈ tailLe
    · have h_coe : (⟨‖f t‖, (norm_nonneg (f t))⟩ : ℝ≥0) = ‖f t‖₊ := rfl
      simp [Set.indicator_of_mem, ht, ENNReal.ofReal_eq_coe_nnreal, norm_nonneg,
        h_coe]
    · simp [Set.indicator_of_notMem, ht]
  have h_integral_tailLe_lt :
      ∫⁻ t in tailLe, (‖f t‖₊ : ℝ≥0∞) ∂volume
        < ENNReal.ofReal δ := by
    have h_nonneg : 0 ≤ᵐ[volume]
        fun t => Set.indicator tailLe (fun t => ‖f t‖) t := by
      refine Filter.Eventually.of_forall ?_
      intro t
      by_cases ht : t ∈ tailLe
      · simp [tailLe, Set.indicator_of_mem, ht, norm_nonneg]
      · simp [Set.indicator_of_notMem, ht, norm_nonneg]
    have h_indicator_integrable :
        Integrable (fun t => Set.indicator tailLe (fun t => ‖f t‖) t) volume :=
      (hf.norm.indicator h_tailLe_meas)
    have h_meas : AEStronglyMeasurable
        (fun t => Set.indicator tailLe (fun t => ‖f t‖) t) volume :=
      h_indicator_integrable.aestronglyMeasurable
    have h_eq_toReal :
        ∫ t, Set.indicator tailLe (fun t => ‖f t‖) t ∂volume
          = (∫⁻ t, ENNReal.ofReal
              (Set.indicator tailLe (fun t => ‖f t‖) t) ∂volume).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg h_meas
    have h_indicator_integral :
        ∫ t, Set.indicator tailLe (fun t => ‖f t‖) t ∂volume
          = ∫ t in tailLe, ‖f t‖ ∂volume := by
      simp [MeasureTheory.integral_indicator, h_tailLe_meas]
    have h_indicator_lt :
        ∫ t, Set.indicator tailLe (fun t => ‖f t‖) t ∂volume < δ := by
      simpa [h_indicator_integral] using h_tail
    have h_toReal_lt :
        (∫⁻ t, ENNReal.ofReal
            (Set.indicator tailLe (fun t => ‖f t‖) t) ∂volume).toReal < δ := by
      simpa [h_eq_toReal] using h_indicator_lt
    have h_lintegral_tailLe_eq :
        ∫⁻ t in tailLe, (‖f t‖₊ : ℝ≥0∞) ∂volume
          = ∫⁻ t, ENNReal.ofReal
              (Set.indicator tailLe (fun t => ‖f t‖) t) ∂volume := by
      simpa [h_indicator_ofReal, h_indicator_coe, ENNReal.ofReal_eq_coe_nnreal,
        norm_nonneg] using
        (MeasureTheory.lintegral_indicator (μ := volume)
          (hs := h_tailLe_meas)
          (f := fun t => ENNReal.ofReal ‖f t‖)).symm
    have h_toReal_lt' :
        (∫⁻ t in tailLe, (‖f t‖₊ : ℝ≥0∞) ∂volume).toReal < δ := by
      simpa [h_lintegral_tailLe_eq] using h_toReal_lt
    have h_indicator_fun :
        (fun t => Set.indicator tailLe (fun t => (‖f t‖₊ : ℝ≥0∞)) t)
          ≤ᵐ[volume] fun t => (‖f t‖₊ : ℝ≥0∞) := by
      refine Filter.Eventually.of_forall ?_
      intro t
      by_cases ht : t ∈ tailLe
      · simp [Set.indicator_of_mem, ht]
      · simp [Set.indicator_of_notMem, ht]
    have h_le_total :
        ∫⁻ t in tailLe, (‖f t‖₊ : ℝ≥0∞) ∂volume
          ≤ ∫⁻ t, (‖f t‖₊ : ℝ≥0∞) ∂volume := by
      have h_le := MeasureTheory.lintegral_mono_ae h_indicator_fun
      have h_lintegral_tailLe :=
        (MeasureTheory.lintegral_indicator (μ := volume)
          (hs := h_tailLe_meas)
          (f := fun t => (‖f t‖₊ : ℝ≥0∞)))
      simpa [h_lintegral_tailLe] using h_le
    have h_total_lt :
        ∫⁻ t, (‖f t‖₊ : ℝ≥0∞) ∂volume < ∞ := by
      simpa [MeasureTheory.HasFiniteIntegral, ENNReal.ofReal_eq_coe_nnreal,
        norm_norm, norm_nonneg] using hf.norm.hasFiniteIntegral
    have h_finite :
        ∫⁻ t in tailLe, (‖f t‖₊ : ℝ≥0∞) ∂volume < ∞ :=
      lt_of_le_of_lt h_le_total h_total_lt
    refine (ENNReal.lt_ofReal_iff_toReal_lt (ne_of_lt h_finite)).2 ?_
    simpa [h_lintegral_tailLe_eq] using h_toReal_lt'

  -- Combine the estimates.
  have h_tail_strict_lt :
      ∫⁻ t in tail, (‖f t‖₊ : ℝ≥0∞) ∂volume < ENNReal.ofReal δ :=
    lt_of_le_of_lt h_tail_le h_integral_tailLe_lt
  simpa [h_eLp_tail] using h_tail_strict_lt

/-- Control the L² error after truncating a function outside
  a ball using the squared tail integral. -/
lemma eLpNorm_two_tail_indicator_sub
    {f : ℝ → ℂ} (hf_L2 : MemLp f 2 volume) {R δ : ℝ}
    (hδ : 0 < δ)
    (h_tail : ∫ t in {t : ℝ | R ≤ |t|}, ‖f t‖ ^ 2 ∂volume < δ ^ 2) :
    eLpNorm (fun t : ℝ => f t - Set.indicator {t : ℝ | |t| ≤ R} f t) 2 volume
      < ENNReal.ofReal δ := by
  classical
  set ball : Set ℝ := {t : ℝ | |t| ≤ R} with h_ball
  set tail : Set ℝ := {t : ℝ | R < |t|} with h_tail_def
  set tailLe : Set ℝ := {t : ℝ | R ≤ |t|} with h_tailLe

  -- Describe the difference as an indicator of the tail set.
  have h_indicator_eq :
      (fun t : ℝ => f t - Set.indicator ball f t) = Set.indicator tail f := by
    funext t
    by_cases ht : |t| ≤ R
    · have ht_ball : t ∈ ball := by simpa [ball, Set.mem_setOf_eq] using ht
      have ht_tail : t ∉ tail := by
        have : ¬ R < |t| := not_lt.mpr ht
        simpa [tail, Set.mem_setOf_eq] using this
      simp [ball, tail, ht_ball, ht_tail]
    · have ht' : R < |t| := not_le.mp ht
      have ht_ball : t ∉ ball := by
        have : ¬ |t| ≤ R := ht
        simpa [ball, Set.mem_setOf_eq] using this
      have ht_tail : t ∈ tail := by simpa [tail, Set.mem_setOf_eq] using ht'
      simp [ball, tail, ht_ball, ht_tail, ht']

  -- Basic measurability facts about the tail regions.
  have h_tail_meas : MeasurableSet tail := by
    have : tail = (fun x : ℝ => |x|) ⁻¹' Set.Ioi R := by
      ext t; simp [tail]
    have h_abs : Measurable fun x : ℝ => |x| :=
      (_root_.continuous_abs : Continuous fun x : ℝ => |x|).measurable
    simpa [this] using h_abs measurableSet_Ioi
  have h_tailLe_meas : MeasurableSet tailLe := by
    have : tailLe = (fun x : ℝ => |x|) ⁻¹' Set.Ici R := by
      ext t; simp [tailLe]
    have h_abs : Measurable fun x : ℝ => |x| :=
      (_root_.continuous_abs : Continuous fun x : ℝ => |x|).measurable
    simpa [this] using h_abs measurableSet_Ici

  have h_subset : tail ⊆ tailLe := by
    intro t ht
    have : R < |t| := by simpa [tail, Set.mem_setOf_eq] using ht
    exact (le_of_lt this : R ≤ |t|)

  -- Compare the strict tail integral with the non-strict tail integral.
  have h_tail_sq_le :
      ∫ t in tail, ‖f t‖ ^ 2 ∂volume
        ≤ ∫ t in tailLe, ‖f t‖ ^ 2 ∂volume := by
    have h_nonneg :
        0 ≤ᵐ[volume] fun t =>
          Set.indicator tail (fun t => ‖f t‖ ^ 2) t := by
      refine Filter.Eventually.of_forall ?_
      intro t
      by_cases ht : t ∈ tail
      · simp [Set.indicator_of_mem, ht, sq_nonneg]
      · simp [Set.indicator_of_notMem, ht, sq_nonneg]
    have h_int_tailLe :
        Integrable
          (fun t => Set.indicator tailLe (fun t => ‖f t‖ ^ 2) t) volume :=
      (integrable_norm_sq_of_memLp_two hf_L2).indicator h_tailLe_meas
    have h_le :
        Set.indicator tail (fun t => ‖f t‖ ^ 2)
          ≤ᵐ[volume]
        Set.indicator tailLe (fun t => ‖f t‖ ^ 2) := by
      refine Filter.Eventually.of_forall ?_
      intro t
      by_cases ht : t ∈ tail
      · have ht' : t ∈ tailLe := h_subset ht
        simp [Set.indicator_of_mem, ht, ht']
      · by_cases ht' : t ∈ tailLe
        · simp [Set.indicator_of_notMem, ht, Set.indicator_of_mem, ht', sq_nonneg]
        · simp [Set.indicator_of_notMem, ht, Set.indicator_of_notMem, ht']
    simpa [MeasureTheory.integral_indicator, h_tail_meas, h_tailLe_meas]
      using
        integral_mono_of_nonneg (μ := volume)
          (f := fun t => Set.indicator tail (fun t => ‖f t‖ ^ 2) t)
          (g := fun t => Set.indicator tailLe (fun t => ‖f t‖ ^ 2) t)
          h_nonneg h_int_tailLe h_le

  have h_tail_sq_lt :
      ∫ t in tail, ‖f t‖ ^ 2 ∂volume < δ ^ 2 :=
    lt_of_le_of_lt h_tail_sq_le h_tail

  -- Work with the tail indicator.
  set g : ℝ → ℂ := Set.indicator tail f with hg_def
  have hg_mem : MemLp g 2 volume := by
    simpa [g, hg_def] using
      (hf_L2.indicator (μ := volume) h_tail_meas)

  -- Express the squared norm of `g` through the tail integral.
  have h_sq_indicator :
      (fun t => ‖g t‖ ^ (2 : ℝ))
        =ᵐ[volume]
      fun t => Set.indicator tail (fun t => ‖f t‖ ^ (2 : ℝ)) t := by
    refine Filter.Eventually.of_forall ?_
    intro t
    by_cases ht : t ∈ tail
    · simp [g, hg_def, Set.indicator_of_mem, ht, Real.rpow_natCast]
    · simp [g, hg_def, Set.indicator_of_notMem, ht, Real.rpow_natCast]

  have h_integral_sq :
      ∫ t, ‖g t‖ ^ (2 : ℝ) ∂volume
        = ∫ t in tail, ‖f t‖ ^ (2 : ℝ) ∂volume := by
    have h :=
      MeasureTheory.integral_congr_ae (μ := volume) h_sq_indicator
    simpa [MeasureTheory.integral_indicator, h_tail_meas]
      using h

  -- Tail integral as a real number.
  set Ig : ℝ := ∫ t in tail, ‖f t‖ ^ 2 ∂volume with hIg_def
  have hIg_nonneg : 0 ≤ Ig := by
    have h_eq :
        Ig = ∫ t, Set.indicator tail (fun t => ‖f t‖ ^ 2) t ∂volume := by
      simp [Ig, MeasureTheory.integral_indicator, h_tail_meas]
    have h_nonneg :
        0 ≤ᵐ[volume] fun t =>
          Set.indicator tail (fun t => ‖f t‖ ^ 2) t :=
      Filter.Eventually.of_forall <| by
        intro t; by_cases ht : t ∈ tail
        · simp [Set.indicator_of_mem, ht, sq_nonneg]
        · simp [Set.indicator_of_notMem, ht, sq_nonneg]
    have h_nonneg_int :=
      MeasureTheory.integral_nonneg_of_ae (μ := volume) h_nonneg
    simpa [h_eq] using h_nonneg_int

  have h_integral_sq_real :
      ∫ t, ‖g t‖ ^ (2 : ℝ) ∂volume = Ig := by
    simpa [Ig, Real.rpow_natCast] using h_integral_sq
  have h_integral_sq_nat :
      ∫ t, ‖g t‖ ^ 2 ∂volume = Ig := by
    simpa [Real.rpow_natCast] using h_integral_sq_real

  -- Express the L² seminorm of the indicator.
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
  have h_eLp_g : eLpNorm g 2 volume
      = ENNReal.ofReal (Ig ^ (1 / 2 : ℝ)) := by
    simpa [g, h_integral_sq_nat, one_div]
      using
        MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
          (f := g) hp0 hp_top hg_mem

  -- Relate to square roots.
  set A : ℝ := Real.sqrt Ig with hA_def
  have hA_nonneg : 0 ≤ A := Real.sqrt_nonneg _
  have hA_sq : A ^ 2 = Ig := by
    simpa [A, hA_def, pow_two] using Real.mul_self_sqrt hIg_nonneg
  have hA_eq_half : A = Ig ^ (1 / 2 : ℝ) := by
    simpa [A, hA_def] using Real.sqrt_eq_rpow Ig
  have hA_lt : A < δ := by
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
    have hIg_lt : Ig < δ ^ 2 := by simpa [hIg_def] using h_tail_sq_lt
    refine hA_def ▸ (Real.sqrt_lt hIg_nonneg hδ_nonneg).2 hIg_lt

  -- Convert the comparison into `ℝ≥0∞`.
  have h_eLp_g_lt : eLpNorm g 2 volume < ENNReal.ofReal δ := by
    have h_ofReal_lt : ENNReal.ofReal A < ENNReal.ofReal δ :=
      (ENNReal.ofReal_lt_ofReal_iff hδ).2 hA_lt
    have h2 : ENNReal.ofReal (Ig ^ (1 / 2 : ℝ)) < ENNReal.ofReal δ := by
      simpa [hA_eq_half] using h_ofReal_lt
    rw [h_eLp_g]
    exact h2

  -- Translate back to the original function.
  have h_diff_eq :
      eLpNorm (fun t => f t - Set.indicator ball f t) 2 volume
        = eLpNorm g 2 volume := by
    simp [g, hg_def, h_indicator_eq]
  rw [h_diff_eq]
  exact h_eLp_g_lt

/-- L¹/L² control on the difference between `f` and its ball truncation. -/
lemma memLp_one_indicator_ball_of_memLp_two
    {f : ℝ → ℂ} (hf_L2 : MemLp f 2 volume) (R : ℝ) :
    MemLp (fun t : ℝ => Set.indicator {t : ℝ | |t| ≤ R} f t) 1 volume := by
  classical
  set s : Set ℝ := {t : ℝ | |t| ≤ R} with hs_def
  have hs_meas : MeasurableSet s := by
    have : s = Metric.closedBall (0 : ℝ) R := by
      ext t; simp [s, Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]
    simpa [this]
      using (measurableSet_closedBall :
        MeasurableSet (Metric.closedBall (0 : ℝ) R))
  -- Membership in L² persists after truncation to a measurable set.
  have hf_L2_indicator : MemLp (s.indicator f) 2 volume :=
    MemLp.indicator (μ := volume) (s := s) hs_meas hf_L2
  -- Outside the ball, the indicator vanishes.
  have hf_zero_outside : ∀ x, x ∉ s → s.indicator f x = 0 := by
    intro x hx
    simp [Set.indicator_of_notMem, hx]
  -- The ball has finite measure, so we can decrease the exponent from 2 to 1.
  have hμs_ne_top : volume s ≠ ∞ := by
    simp [s, hs_def, volume_ball_eq]
  have h_exponent : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
  have hf_L1_indicator :=
    MemLp.mono_exponent_of_measure_support_ne_top
      (μ := volume) (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      hf_L2_indicator hf_zero_outside hμs_ne_top h_exponent
  simpa [s, hs_def] using hf_L1_indicator

lemma integrable_indicator_tail_of_tail_bound
    {f : ℝ → ℂ} (hf_L2 : MemLp f 2 volume) {R : ℝ}
    (h_tail_finite :
      HasFiniteIntegral
        (fun t => Set.indicator {t : ℝ | R ≤ |t|} (fun t => ‖f t‖) t)
        volume) :
    Integrable (fun t => Set.indicator {t : ℝ | R ≤ |t|} f t) := by
  classical
  set tail : Set ℝ := {t : ℝ | R ≤ |t|} with h_tail_def
  have h_tail_meas : MeasurableSet tail :=
    (isClosed_le continuous_const _root_.continuous_abs).measurableSet
  have hf_meas : AEStronglyMeasurable f volume := hf_L2.aestronglyMeasurable
  have hf_indicator_meas :
      AEStronglyMeasurable (fun t => Set.indicator tail f t) volume :=
    hf_meas.indicator h_tail_meas
  refine ⟨hf_indicator_meas, ?_⟩

  have h_norm_indicator :
      (fun t => ‖Set.indicator tail f t‖)
        = Set.indicator tail (fun t => ‖f t‖) := by
    funext t
    by_cases ht : t ∈ tail
    · simp [tail, ht]
    · simp [tail, ht]

  -- Pass the finite-integral hypothesis through the indicator/norm rewrite.
  have h_fin_norm : HasFiniteIntegral
      (fun t => ‖Set.indicator tail f t‖) volume := by
    rw [h_norm_indicator]
    exact h_tail_finite

  -- Combine measurability with finiteness of the Bochner integral.
  simpa [MeasureTheory.HasFiniteIntegral, tail, h_tail_def, h_norm_indicator]
    using h_fin_norm

lemma integrable_indicator_ball_of_memLp_two
    {f : ℝ → ℂ} (hf_L2 : MemLp f 2 volume) (R : ℝ) :
    Integrable (fun t => Set.indicator {t : ℝ | |t| ≤ R} f t) := by
  classical
  have h_memLp_one :=
    memLp_one_indicator_ball_of_memLp_two hf_L2 R
  simpa using (memLp_one_iff_integrable).1 h_memLp_one

lemma integrable_of_memLp_two_with_tail_bound
    {f : ℝ → ℂ} (hf_L2 : MemLp f 2 volume) {R : ℝ}
    (h_tail_finite :
      HasFiniteIntegral
        (fun t => Set.indicator {t : ℝ | R ≤ |t|} (fun t => ‖f t‖) t)
        volume) :
    Integrable f := by
  classical
  set ball : Set ℝ := {t : ℝ | |t| ≤ R} with h_ball_def
  set tailLe : Set ℝ := {t : ℝ | R ≤ |t|} with h_tailLe_def
  set tailGt : Set ℝ := {t : ℝ | R < |t|} with h_tailGt_def
  set boundary : Set ℝ := {t : ℝ | |t| = R} with h_boundary_def

  -- Integrability on the bounded region.
  have h_ball_integrable :
      Integrable (fun t => Set.indicator ball f t) := by
    simpa [ball, h_ball_def]
      using integrable_indicator_ball_of_memLp_two hf_L2 R

  -- Integrability on the tail (with `≤`) from the finite integral hypothesis.
  have h_tailLe_integrable :
      Integrable (fun t => Set.indicator tailLe f t) := by
    have := integrable_indicator_tail_of_tail_bound
      (f := f) hf_L2 (R := R) h_tail_finite
    simpa [tailLe, h_tailLe_def] using this

  -- Basic measurability facts for the boundary set.
  have h_boundary_closed : IsClosed boundary := by
    have h_closed : IsClosed ((fun t : ℝ => |t|) ⁻¹' ({R} : Set ℝ)) :=
      (isClosed_singleton : IsClosed ({R} : Set ℝ)).preimage continuous_norm
    simpa [boundary, h_boundary_def] using h_closed

  have h_boundary_meas : MeasurableSet boundary :=
    h_boundary_closed.measurableSet

  have hf_boundary_L2 :
      MemLp (fun t : ℝ => Set.indicator boundary f t) 2 volume :=
    MemLp.indicator (μ := volume) (s := boundary) h_boundary_meas hf_L2

  have h_boundary_zero_outside :
      ∀ x, x ∉ boundary → Set.indicator boundary f x = (0 : ℂ) := by
    intro x hx
    simp [boundary, h_boundary_def, hx]

  -- Control the measures of the relevant sets.
  have h_ball_subset_Icc :
      ball ⊆ Set.Icc (-abs R) (abs R) := by
    intro t ht
    have h_abs_le : |t| ≤ R := by simpa [ball, h_ball_def] using ht
    have hR_nonneg : 0 ≤ R := le_trans (abs_nonneg _) h_abs_le
    have h_bounds := abs_le.mp h_abs_le
    constructor
    · have h_left : -R ≤ t := h_bounds.1
      simpa [abs_of_nonneg hR_nonneg] using h_left
    · have h_right : t ≤ R := h_bounds.2
      simpa [abs_of_nonneg hR_nonneg] using h_right

  have h_boundary_subset_ball : boundary ⊆ ball := by
    intro t ht
    have ht_eq : |t| = R := by
      simpa [boundary, h_boundary_def] using ht
    have : |t| ≤ R := le_of_eq ht_eq
    simp [ball, h_ball_def, ht_eq]

  have h_Icc_lt_top :
      volume (Set.Icc (-abs R) (abs R)) < ∞ := by
    have h_le : (-abs R) ≤ abs R := by
      simp
    have h_volume :
        volume (Set.Icc (-abs R) (abs R))
          = ENNReal.ofReal (abs R - (-abs R)) := by
      simp [volume_Icc, h_le]
    have h_lt : ENNReal.ofReal (abs R - (-abs R)) < ∞ :=
      ENNReal.ofReal_lt_top
    simp [h_volume]

  have h_ball_lt_top : volume ball < ∞ :=
    lt_of_le_of_lt (measure_mono h_ball_subset_Icc) h_Icc_lt_top
  have h_ball_measure_ne_top : volume ball ≠ ∞ := h_ball_lt_top.ne

  have h_boundary_lt_top : volume boundary < ∞ :=
    lt_of_le_of_lt (measure_mono h_boundary_subset_ball) h_ball_lt_top
  have h_boundary_measure_ne_top : volume boundary ≠ ∞ :=
    h_boundary_lt_top.ne

  have h_exponent : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num

  have hf_boundary_L1 :
      MemLp (fun t : ℝ => Set.indicator boundary f t) 1 volume :=
    MemLp.mono_exponent_of_measure_support_ne_top
      (μ := volume) (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      hf_boundary_L2 h_boundary_zero_outside
      h_boundary_measure_ne_top h_exponent

  have h_boundary_integrable :
      Integrable (fun t => Set.indicator boundary f t) := by
    simpa [boundary, h_boundary_def]
      using (memLp_one_iff_integrable).1 hf_boundary_L1

  -- Replace the weak tail by its strict version, removing the boundary.
  have h_tailGt_integrable :
      Integrable (fun t => Set.indicator tailGt f t) := by
    have h_eq :
        (fun t => Set.indicator tailGt f t)
          = fun t => Set.indicator tailLe f t - Set.indicator boundary f t := by
      funext t
      classical
      by_cases hgt : R < |t|
      · have hle : R ≤ |t| := le_of_lt hgt
        have hne : |t| ≠ R := ne_of_gt hgt
        simp [tailGt, h_tailGt_def, tailLe, h_tailLe_def, boundary, h_boundary_def,
          hgt, hle, hne]
      · have hnot_gt : |t| ≤ R := le_of_not_gt hgt
        by_cases heq : |t| = R
        · have hle : R ≤ |t| := by simp [heq]
          simp [tailGt, h_tailGt_def, tailLe, h_tailLe_def, boundary, h_boundary_def,
            hgt, heq, hle]
        · have hlt : |t| < R := lt_of_le_of_ne hnot_gt heq
          have h_not_le : ¬ R ≤ |t| := not_le_of_gt hlt
          simp [tailGt, h_tailGt_def, tailLe, h_tailLe_def, boundary, h_boundary_def,
            hgt, hlt, h_not_le, heq]
    simpa [h_eq]
      using h_tailLe_integrable.sub h_boundary_integrable

  -- Decompose `f` as the sum of its bounded and tail parts.
  have h_decomp :
      f = fun t => Set.indicator ball f t + Set.indicator tailGt f t := by
    funext t
    by_cases hball : |t| ≤ R
    · have h_not_gt : ¬ R < |t| := not_lt.mpr hball
      simp [ball, h_ball_def, tailGt, h_tailGt_def, hball, h_not_gt]
    · have h_gt : R < |t| := lt_of_not_ge hball
      simp [ball, h_ball_def, tailGt, h_tailGt_def, hball, h_gt]

  -- Conclude integrability of `f`.
  have h_sum_integrable :
      Integrable
        (fun t => Set.indicator ball f t + Set.indicator tailGt f t) :=
    h_ball_integrable.add h_tailGt_integrable
  exact h_decomp ▸ h_sum_integrable

lemma hasFiniteIntegral_indicator_norm_of_integral_lt
    {f : ℝ → ℂ} (R δ : ℝ)
    (hf_meas :
      AEStronglyMeasurable
        (fun t =>
          Set.indicator {t : ℝ | R ≤ |t|} (fun t => ‖f t‖) t)
        volume)
    (h_tail :
      ∫⁻ t in {t : ℝ | R ≤ |t|}, ENNReal.ofReal ‖f t‖ ∂volume < ENNReal.ofReal δ) :
    HasFiniteIntegral
      (fun t => Set.indicator {t : ℝ | R ≤ |t|} (fun t => ‖f t‖) t)
      volume := by
  have h_meas_set : MeasurableSet {t : ℝ | R ≤ |t|} :=
    (isClosed_le continuous_const _root_.continuous_abs).measurableSet
  have h_norm_meas_restrict :
      AEStronglyMeasurable (fun t => ‖f t‖) (volume.restrict {t : ℝ | R ≤ |t|}) := by
    have h1 := hf_meas.mono_measure (ν := volume.restrict {t : ℝ | R ≤ |t|})
        (Measure.restrict_le_self (s := {t : ℝ | R ≤ |t|}))
    refine AEStronglyMeasurable.congr h1 ?_
    filter_upwards [ae_restrict_mem h_meas_set] with t ht using by
      simp only [Set.indicator, Set.mem_setOf_eq, ht, ↓reduceIte]
  have : Integrable (fun t => Set.indicator {t : ℝ | R ≤ |t|} (fun t => ‖f t‖) t) volume := by
    rw [integrable_indicator_iff h_meas_set]
    constructor
    · exact h_norm_meas_restrict
    · rw [HasFiniteIntegral]
      calc ∫⁻ a in {t | R ≤ |t|}, ‖‖f a‖‖₊
          = ∫⁻ a in {t | R ≤ |t|}, (‖f a‖₊ : ℝ≥0∞) := by congr; funext; simp [nnnorm_norm]
        _ = ∫⁻ a in {t | R ≤ |t|}, ENNReal.ofReal ‖f a‖ := by
            congr; funext a; exact (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm
        _ < ENNReal.ofReal δ := h_tail
        _ < ⊤ := ENNReal.ofReal_lt_top
  exact this.hasFiniteIntegral

/-- Upgrade a smooth compactly supported approximation to a Schwartz approximation in L¹ and L². -/
lemma smooth_compact_support_to_schwartz_L1_L2
    {g : ℝ → ℂ}
    (hg_compact : HasCompactSupport g) (hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ,
      eLpNorm (fun t : ℝ => g t - φ t) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun t : ℝ => g t - φ t) 2 volume < ENNReal.ofReal ε := by
  classical
  -- Show that every derivative of `g` has polynomial decay, using compact support.
  have hg_schwartz : ∀ k n : ℕ, ∃ C : ℝ,
      ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    intro k n
    classical
    set K := tsupport g with hK_def
    have hK_compact : IsCompact K := by simpa [hK_def] using hg_compact
    have h_iter_subset :
        tsupport (iteratedFDeriv ℝ n g) ⊆ K := by
      simpa [hK_def] using
        (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := g) (n := n))
    -- Consider the auxiliary function whose boundedness we need
    set h : ℝ → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖
    have h_nonneg : ∀ x, 0 ≤ h x := fun x =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    -- If the derivative has empty support, the desired bound is trivial.
    by_cases h_support_empty : tsupport (iteratedFDeriv ℝ n g) = ∅
    · refine ⟨0, ?_⟩
      intro x
      have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := by
        simp [h_support_empty]
      have hx_zero : iteratedFDeriv ℝ n g x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      simp [h, hx_zero]
    -- Otherwise, use compactness to bound the auxiliary function on the support
    · have h_support_nonempty :
        (tsupport (iteratedFDeriv ℝ n g)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr h_support_empty
      obtain ⟨x₀, hx₀_support⟩ := h_support_nonempty
      have hx₀K : x₀ ∈ K := h_iter_subset hx₀_support
      have h_pow_cont : Continuous fun x : ℝ => ‖x‖ ^ k :=
        (continuous_norm : Continuous fun x : ℝ => ‖x‖).pow _
      have h_iter_cont : Continuous fun x : ℝ => iteratedFDeriv ℝ n g x :=
        hg_smooth.continuous_iteratedFDeriv (hm := by
          exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞)))
      have h_cont : Continuous h :=
        h_pow_cont.mul (h_iter_cont.norm)
      have h_image_compact : IsCompact (h '' K) := hK_compact.image h_cont
      have h_image_nonempty : (h '' K).Nonempty :=
        ⟨h x₀, ⟨x₀, hx₀K, rfl⟩⟩
      obtain ⟨C, hC_isGreatest⟩ :=
        h_image_compact.exists_isGreatest h_image_nonempty
      obtain ⟨⟨xC, hxC_K, rfl⟩, hC_max⟩ := hC_isGreatest
      refine ⟨h xC, ?_⟩
      intro x
      by_cases hxK : x ∈ K
      · have hx_mem : h x ∈ h '' K := ⟨x, hxK, rfl⟩
        exact hC_max hx_mem
      · have hx_not : x ∉ tsupport (iteratedFDeriv ℝ n g) := fun hx => hxK (h_iter_subset hx)
        have hx_zero : iteratedFDeriv ℝ n g x = 0 :=
          image_eq_zero_of_notMem_tsupport hx_not
        have hx_val : h x = 0 := by simp [h, hx_zero]
        have h_nonneg_xC : 0 ≤ h xC := h_nonneg xC
        have hx_le : h x ≤ h xC := by simpa [hx_val] using h_nonneg_xC
        exact hx_le
  -- Package `g` as a Schwartz function.
  let φ : SchwartzMap ℝ ℂ := ⟨g, hg_smooth, hg_schwartz⟩
  have h_eq_g : (φ : ℝ → ℂ) = g := rfl
  have h_diff_zero : (fun t : ℝ => g t - φ t) = 0 := by
    funext t
    simp [h_eq_g]
  -- The L¹ and L² errors are zero, hence below any positive tolerance.
  have h_eLp_one_zero :
      eLpNorm (fun t : ℝ => g t - φ t) 1 volume = 0 := by
    simp [h_diff_zero]
  have h_eLp_two_zero :
      eLpNorm (fun t : ℝ => g t - φ t) 2 volume = 0 := by
    simp [h_diff_zero]
  have hε_pos' : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  refine ⟨φ, ?_, ?_⟩
  · simpa [h_eLp_one_zero] using hε_pos'
  · simpa [h_eLp_two_zero] using hε_pos'

end Frourio
