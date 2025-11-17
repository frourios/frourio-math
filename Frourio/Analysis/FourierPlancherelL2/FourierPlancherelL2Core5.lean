import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core4
import Frourio.Analysis.Gaussian
import Frourio.Analysis.HilbertSpace
import Frourio.Analysis.MellinParseval.MellinParsevalCore0
import Frourio.Analysis.SchwartzDensity.SchwartzDensity
import Frourio.Analysis.SchwartzDensityLp.SchwartzDensityLp
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Normed.Lp.lpSpace

open MeasureTheory Complex Real SchwartzMap Metric
open scoped Topology ENNReal NNReal ComplexConjugate Pointwise Convolution

noncomputable section

namespace Frourio
open Schwartz

namespace MeasureTheory

/-- Dominated convergence for parameter `R : ℝ` and the filter `atTop` on ℝ (signature only).

This is an `ℝ`-indexed analogue of `tendsto_integral_of_dominated_convergence`, specialized to
integrals over `ℝ` with respect to `volume` and complex-valued integrands.

If
- `g` is an integrable dominating function on `ℝ`,
- each `f R` is a.e. strongly measurable,
- `‖f R x‖` is dominated by `g x` for all `R`,
- and for almost every `x` we have `f R x → f∞ x` as `R → ∞`,

then the integrals `∫ f R` converge to `∫ f∞` as `R → ∞`. -/
lemma tendsto_integral_of_dominated_convergence_atTop_real
    (f : ℝ → ℝ → ℂ) (flim : ℝ → ℂ) (g : ℝ → ℝ)
    (h_meas : ∀ R : ℝ,
      AEStronglyMeasurable (f R) (volume : Measure ℝ))
    (hg_int : Integrable g (volume : Measure ℝ))
    (h_bound : ∀ R : ℝ, ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ‖f R x‖ ≤ g x)
    (h_lim : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      Filter.Tendsto (fun R : ℝ => f R x)
        Filter.atTop (𝓝 (flim x))) :
    Filter.Tendsto (fun R : ℝ =>
        ∫ x : ℝ, f R x ∂(volume : Measure ℝ))
      Filter.atTop
      (𝓝 (∫ x : ℝ, flim x ∂(volume : Measure ℝ))) := by
  classical
  -- Step 1: package the family of integrals and their limit.
  set I : ℝ → ℂ := fun R => ∫ x : ℝ, f R x ∂(volume : Measure ℝ)
  set Ilim : ℂ := ∫ x : ℝ, flim x ∂(volume : Measure ℝ)

  -- Step 2: for each R, deduce integrability of `f R` from the domination by `g`.
  have h_integrable_R :
      ∀ R : ℝ, Integrable (f R) (volume : Measure ℝ) := by
    intro R
    -- Use the standard domination lemma with majorant `g`.
    exact Integrable.mono' hg_int (h_meas R) (h_bound R)

  -- Step 3: apply a dominated convergence theorem for the filter `atTop` on ℝ.
  -- Conceptually, one wants a variant of
  -- `MeasureTheory.tendsto_integral_of_dominated_convergence` where the parameter
  -- lives in `ℝ` and the filter is `Filter.atTop` on `ℝ`. Such a lemma would take
  -- as input the data `h_meas`, `h_integrable_R`, `hg_int`, `h_bound`, and `h_lim`
  -- and return exactly the desired `Tendsto` statement.
  -- We record this reduction but keep the actual invocation as a placeholder.
  have h_tendsto_aux :
      Filter.Tendsto I Filter.atTop (𝓝 Ilim) := by
    -- First, upgrade the pointwise hypotheses to `Filter.Eventually` statements
    -- along the filter `atTop` on `ℝ`.
    have h_meas_eventually :
        ∀ᶠ R in Filter.atTop,
          AEStronglyMeasurable (f R) (volume : Measure ℝ) :=
      Filter.Eventually.of_forall h_meas
    have h_bound_eventually :
        ∀ᶠ R in Filter.atTop,
          ∀ᵐ x : ℝ ∂(volume : Measure ℝ), ‖f R x‖ ≤ g x :=
      Filter.Eventually.of_forall h_bound

    -- Now apply the dominated convergence theorem for countably generated filters.
    -- Here we specialize it to the filter `atTop` on `ℝ`, the measure `volume`,
    -- and the family `f : ℝ → ℝ → ℂ` with limit `flim`.
    have h_tendsto_integral :
        Filter.Tendsto (fun R : ℝ => ∫ x : ℝ, f R x ∂(volume : Measure ℝ))
          Filter.atTop
          (𝓝 (∫ x : ℝ, flim x ∂(volume : Measure ℝ))) :=
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := (volume : Measure ℝ))
        (l := Filter.atTop)
        (F := fun R : ℝ => f R)
        (f := fun x : ℝ => flim x)
        g
        h_meas_eventually
        h_bound_eventually
        hg_int
        h_lim

    -- Finally, rewrite the conclusion in terms of the auxiliary definitions `I` and `Ilim`.
    simpa [I, Ilim] using h_tendsto_integral

  -- Step 4: rewrite back in terms of the original expressions.
  simpa [I, Ilim] using h_tendsto_aux

end MeasureTheory

/-- Fourier-Plancherel theorem for L¹ ∩ L² functions.

This is the CORRECT version of the Plancherel identity for functions in both L¹ and L².
Unlike the invalid `fourierIntegral_l2_norm_INVALID`, this version has both:
- L¹ assumption (Integrable g): ensures fourierIntegral g is well-defined pointwise
- L² assumption (MemLp g 2): ensures the L² norms on both sides are finite

With both assumptions, we can prove:
1. fourierIntegral g ∈ L² (by Plancherel)
2. ∫ ‖g‖² = ∫ ‖fourierIntegral g‖²

The Fourier transform convention used is fourierKernel ξ t = exp(-2πiξt),
which gives Plancherel's identity without normalization constants. -/
lemma fourier_plancherel_L1_L2 (g : ℝ → ℂ)
    (hg_L1 : Integrable g)
    (hg_L2 : MemLp g 2 volume) :
    ∫ t : ℝ, ‖g t‖ ^ 2 ∂volume
      = ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume := by
  classical
  -- Strategy: Approximate `g` first by a smooth compactly supported function in both norms,
  -- then convert it into a Schwartz function using mollification.
  -- Step 1: choose a smooth compactly supported approximation of `g`.
  have h_half_pos : 0 < (1 : ℝ) := by norm_num
  obtain ⟨g₀, hg₀_compact, hg₀_smooth, hg₀_L1_error, hg₀_L2_error⟩ :=
    exists_smooth_compact_support_L1_L2_close g hg_L1 hg_L2 1 h_half_pos

  -- Step 2: upgrade the approximation to a Schwartz function.
  obtain ⟨φ₀, hφ₀_L1_error, hφ₀_L2_error⟩ :=
    smooth_compact_support_to_schwartz_L1_L2 hg₀_compact hg₀_smooth 1 h_half_pos

  -- Step 3: combine the two approximations using the triangle inequality in both norms.
  have hg₀_integrable : Integrable g₀ :=
    (hg₀_smooth.continuous.integrable_of_hasCompactSupport hg₀_compact)
  have hφ₀_integrable : Integrable (fun t : ℝ => φ₀ t) := schwartz_integrable φ₀
  have h_diff1_meas : AEStronglyMeasurable (fun t : ℝ => g t - g₀ t) volume :=
    (hg_L1.sub hg₀_integrable).aestronglyMeasurable
  have h_diff2_meas : AEStronglyMeasurable (fun t : ℝ => g₀ t - φ₀ t) volume :=
    (hg₀_integrable.sub hφ₀_integrable).aestronglyMeasurable
  have hφ₀_L1 :
      eLpNorm (fun t : ℝ => g t - φ₀ t) 1 volume
        ≤ eLpNorm (fun t : ℝ => g t - g₀ t) 1 volume
            + eLpNorm (fun t : ℝ => g₀ t - φ₀ t) 1 volume := by
    have h_add :=
      eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞))
        (f := fun t : ℝ => g t - g₀ t)
        (g := fun t : ℝ => g₀ t - φ₀ t)
        h_diff1_meas h_diff2_meas (le_rfl : (1 : ℝ≥0∞) ≤ (1 : ℝ≥0∞))
    have h_eq :
        (fun t : ℝ => g t - φ₀ t)
          = (fun t : ℝ => g t - g₀ t) + fun t : ℝ => g₀ t - φ₀ t := by
      funext t; simp [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simpa [h_eq]
      using h_add

  have hφ₀_L2 :
      eLpNorm (fun t : ℝ => g t - φ₀ t) 2 volume
        ≤ eLpNorm (fun t : ℝ => g t - g₀ t) 2 volume
            + eLpNorm (fun t : ℝ => g₀ t - φ₀ t) 2 volume := by
    have :=
      eLpNorm_triangle_diff g g₀ (fun t : ℝ => φ₀ t)
        hg_L2.aestronglyMeasurable
        (hg₀_smooth.continuous.aestronglyMeasurable)
        ((SchwartzMap.continuous φ₀).aestronglyMeasurable)
    simpa [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this

  -- Step 4: use the existing density lemma to produce a sequence of Schwartz functions
  -- with L¹ and L² convergence to `g`.
  have h_aux := exists_schwartz_L1_L2_approx g hg_L1 hg_L2
  obtain ⟨φ, hφ_L1, hφ_L2, hφ_tendsto_L1, hφ_tendsto_L2⟩ := h_aux

  -- Step 5: deduce the Plancherel identity for `g` using the approximating sequence `φ n`.
  -- L¹ convergence gives pointwise convergence of the Fourier integrals.
  have h_fourier_pointwise : ∀ ξ, Filter.Tendsto
      (fun n => fourierIntegral (fun t => φ n t) ξ)
      Filter.atTop (𝓝 (fourierIntegral g ξ)) := by
    intro ξ
    exact fourierIntegral_tendsto_of_schwartz_approx hg_L1 hφ_L1 hφ_tendsto_L1 ξ

  -- For each `φ n`, Plancherel holds (with unit constant) by `fourier_plancherel`.
  have h_schwartz_plancherel : ∀ n,
      ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume
        = ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume := by
    intro n
    -- Rephrase the classical Plancherel identity for Schwartz functions
    have h :=
      fourier_plancherel (φ n)
    -- `fourierIntegral` is the `ℂ`-valued Fourier transform with norm preservation.
    simpa using h

  -- L² convergence of `φ n` to `g`.
  have h_left_tendsto : Filter.Tendsto
      (fun n => ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume)) := by
    have h_sq_nonneg : ∀ t, ‖g t‖ ^ 2 = ‖g t‖ ^ 2 := by simp
    have h_sq_integrable : Integrable (fun t : ℝ => ‖g t‖ ^ 2) :=
      integrable_norm_sq_of_memLp_two hg_L2
    have h_sq_nonneg' : 0 ≤ᵐ[volume] fun t : ℝ => ‖g t‖ ^ 2 :=
      Filter.Eventually.of_forall fun _ => sq_nonneg _
    -- Convert L² convergence of `φ n` → `g` to convergence of squared norms using
    -- `FourierPlancherelL2Core`.
    have h :=
      continuous_integral_norm_sq_of_L2_tendsto
        (g := g) (φ := fun n => φ n) hg_L2 hφ_L2 hφ_tendsto_L2
    simpa using h

  -- L² convergence on the Fourier side using Plancherel and the pointwise limit.
  have h_right_tendsto : Filter.Tendsto
      (fun n => ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume)) := by
    -- Alternative approach: Use Schwartz Plancherel to rewrite the left side,
    -- then use the already-proven convergence h_left_tendsto

    -- For each n: ∫‖F[φ_n]‖² = ∫‖φ_n‖² (by Schwartz Plancherel)
    have h_eq : ∀ n,
        ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume
          = ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume :=
      fun n => (h_schwartz_plancherel n).symm

    -- Rewrite using Schwartz Plancherel: ∫‖F[φ_n]‖² = ∫‖φ_n‖²
    -- So the sequence ∫‖F[φ_n]‖² has the same limit as ∫‖φ_n‖², which is ∫‖g‖²
    have h_rewrite : Filter.Tendsto
        (fun n => ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume)
        Filter.atTop (𝓝 (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume)) := by
      apply Filter.Tendsto.congr' _ h_left_tendsto
      apply Filter.Eventually.of_forall
      intro n
      exact (h_eq n).symm

    -- Strategy: Show ∫‖F[φ_n]‖² → ∫‖F[g]‖² using a different approach
    -- We know: ∫‖F[φ_n]‖² → ∫‖g‖² (from h_rewrite)
    -- We want: ∫‖F[φ_n]‖² → ∫‖F[g]‖²
    -- Therefore: ∫‖g‖² = ∫‖F[g]‖² (by uniqueness of limits)

    -- Key insight: F[φ_n] is Cauchy in L² because φ_n is Cauchy in L²
    -- For Schwartz φ, ψ: ‖F[φ] - F[ψ]‖₂ = ‖F[φ - ψ]‖₂ = ‖φ - ψ‖₂

    -- Alternative approach: Use the fact that we already know where the limit should be
    -- We have h_rewrite: ∫‖F[φ_n]‖² → ∫‖g‖²
    -- We want to show: ∫‖F[φ_n]‖² → ∫‖F[g]‖²
    -- By uniqueness of limits, this would give us ∫‖g‖² = ∫‖F[g]‖²

    -- The key observation: We can use lower semicontinuity
    -- For any subsequence, we have convergence, so the limit is unique

    -- Key insight: We will show that the limit must be ∫‖F[g]‖²
    -- by using the structure of the overall proof.

    -- We have:
    -- 1. Pointwise convergence: F[φ_n](ξ) → F[g](ξ) for all ξ
    -- 2. Integral convergence: ∫‖F[φ_n]‖² → ∫‖g‖² (from h_rewrite)
    -- 3. F[g] ∈ L²

    have hFg_L2 : MemLp (fun ξ => fourierIntegral g ξ) 2 volume :=
      fourierIntegral_memLp_L1_L2 hg_L1 hg_L2

    -- Strategy: Show eLpNorm(F[φ_n] - F[g]) → 0 using Plancherel
    -- Then use continuous_integral_norm_sq_of_L2_tendsto

    have hF_tendsto_L2 : Filter.Tendsto
        (fun n => eLpNorm (fun ξ => fourierIntegral g ξ -
                                    fourierIntegral (fun t => φ n t) ξ) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      -- Strategy: Use the Cauchy property of F[φ_n] from Schwartz Plancherel,
      -- completeness of L², and pointwise convergence to identify the limit.
      have hF_cauchy : CauchySeq (fun n =>
          (fourierIntegral_memLp_L1_L2 (schwartz_integrable (φ n))
            (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))).toLp
          (fun ξ => fourierIntegral (fun t => φ n t) ξ)) := by
        exact fourierIntegral_cauchySeq_of_schwartz_tendsto hg_L2
          (fun n => schwartz_integrable (φ n))
          (fun n => SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
          hφ_tendsto_L2

      classical
      obtain ⟨F_lim, hF_lim⟩ := cauchySeq_tendsto_of_complete hF_cauchy

      -- Package the Fourier transforms of the approximants as L² functions.
      set ψFun : ℕ → ℝ → ℂ := fun n ξ => fourierIntegral (fun t => φ n t) ξ
      have hψ_mem : ∀ n, MemLp (ψFun n) 2 volume := fun n =>
        fourierIntegral_memLp_L1_L2 (schwartz_integrable (φ n))
          (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
      let ψLp : ℕ → Lp ℂ 2 volume := fun n => (hψ_mem n).toLp (ψFun n)
      have hψ_tendsto : Filter.Tendsto ψLp Filter.atTop (𝓝 F_lim) := by
        simpa [ψLp, ψFun, hψ_mem] using hF_lim

      -- Identify the limit candidate with the Fourier transform of `g`.
      let ψ_gLp : Lp ℂ 2 volume := hFg_L2.toLp (fun ξ => fourierIntegral g ξ)

      -- Relate the chosen `ψLp` with the version used in the weak-convergence lemmas.
      have hψLp_schwartz : ∀ n,
          ψLp n
            = (fourierIntegral_memLp_of_schwartz (φ n)).toLp
                (fun ξ : ℝ => fourierIntegral (fun t => φ n t) ξ) := by
        intro n
        refine (MemLp.toLp_eq_toLp_iff (hψ_mem n)
            (fourierIntegral_memLp_of_schwartz (φ n))).mpr ?_
        exact Filter.EventuallyEq.rfl

      -- Weak convergence of Fourier transforms against Schwartz test functions.
      have h_weak_base :=
        weak_limit_fourierIntegral_of_schwartz_tendsto
          (hf_L2 := hg_L2)
          (hφ_L1 := fun n => schwartz_integrable (φ n))
          (hφ_L2 :=
            fun n => SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
          hφ_tendsto_L2

      have h_weak_limit :
          ∀ ψ : SchwartzMap ℝ ℂ,
            Filter.Tendsto (fun n =>
                @inner ℂ (Lp ℂ 2 volume) _
                  ((fourierIntegral_memLp_of_schwartz ψ).toLp
                    (fun ξ => fourierIntegral (fun t => ψ t) ξ))
                  (ψLp n))
              Filter.atTop
              (𝓝 (∫ t : ℝ, g t * conj (ψ t) ∂volume)) := by
        intro ψ
        have h := h_weak_base ψ
        refine h.congr' ?_
        exact Filter.Eventually.of_forall fun n => by
          simp [ψLp, hψLp_schwartz n]

      -- Identify the weak limits on the frequency side with Fourier integrals.
      have h_freq_tendsto :=
        weak_convergence_fourierIntegral_of_schwartz_approx
          (φ := φ) (f := g) hg_L1 ψLp
          (fun n => hψLp_schwartz n) h_weak_limit

      -- Strong convergence of `ψLp` implies the same weak limits.
      have h_strong_tendsto :=
        strong_L2_implies_weak_convergence_schwartz ψLp F_lim hψ_tendsto

      -- Equate the two limiting values for every Schwartz test function.
      have h_integral_eq : ∀ ψ : SchwartzMap ℝ ℂ,
          ∫ x, F_lim x * (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume
              = ∫ x, fourierIntegral g x *
                  (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume := by
        intro ψ
        exact tendsto_nhds_unique (h_strong_tendsto ψ) (h_freq_tendsto ψ)

      -- Use the equality of pairings with Schwartz functions to identify the limit.
      have h_inner_zero : ∀ ψ : SchwartzMap ℝ ℂ,
          @inner ℂ (Lp ℂ 2 volume) _ (F_lim - ψ_gLp)
              ((SchwartzMap.memLp ψ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
                (fun x => ψ x)) = 0 := by
        intro ψ
        set ψTimeMem :=
          SchwartzMap.memLp ψ (p := (2 : ℝ≥0∞)) (μ := volume)
        set ψTimeLp : Lp ℂ 2 volume := ψTimeMem.toLp (fun x => ψ x)
        have hψ_coe : (fun x => ψTimeLp x) =ᵐ[volume] fun x => ψ x :=
          MemLp.coeFn_toLp ψTimeMem
        have hψ_star :
            (fun x => star (ψTimeLp x))
              =ᵐ[volume] fun x => (starRingEnd ℂ) (SchwartzMap.toFun ψ x) :=
          hψ_coe.mono <| by
            intro x hx
            simpa [SchwartzMap.toFun] using congrArg star hx
        have h_inner_F_lim :
            @inner ℂ (Lp ℂ 2 volume) _ ψTimeLp F_lim
              = ∫ x : ℝ, F_lim x *
                  (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume := by
          have h_def :=
            (MeasureTheory.L2.inner_def (𝕜 := ℂ) (μ := volume)
              (f := ψTimeLp) (g := F_lim))
          have h_mul :
              (fun x : ℝ =>
                  @inner ℂ ℂ _ (ψTimeLp x) (F_lim x))
                = fun x : ℝ => F_lim x * star (ψTimeLp x) := by
            funext x
            simp only [RCLike.inner_apply, starRingEnd_apply]
          have h_int := by
            simpa [h_mul, mul_comm] using h_def
          refine h_int.trans ?_
          refine integral_congr_ae ?_
          exact hψ_star.mono (by
            intro x hx
            simpa [SchwartzMap.toFun]
              using congrArg (fun y => F_lim x * y) hx)
        have hψg_coe :
            (fun x => ψ_gLp x) =ᵐ[volume] fun x => fourierIntegral g x :=
          MemLp.coeFn_toLp hFg_L2
        have h_inner_ψg :
            @inner ℂ (Lp ℂ 2 volume) _ ψTimeLp ψ_gLp
              = ∫ x : ℝ, (fourierIntegral g x) *
                  (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume := by
          have h_def :=
            (MeasureTheory.L2.inner_def (𝕜 := ℂ) (μ := volume)
              (f := ψTimeLp) (g := ψ_gLp))
          have h_mul :
              (fun x : ℝ =>
                  @inner ℂ ℂ _ (ψTimeLp x) (ψ_gLp x))
                = fun x : ℝ => ψ_gLp x * star (ψTimeLp x) := by
            funext x
            simp only [RCLike.inner_apply, starRingEnd_apply]
          have h_int := by
            simpa [h_mul, mul_comm] using h_def
          refine h_int.trans ?_
          refine integral_congr_ae ?_
          refine (Filter.EventuallyEq.mul hψg_coe hψ_star).mono ?_
          intro x hx
          simpa [SchwartzMap.toFun, mul_comm] using hx
        have h_inner_eq := by
          simpa [h_inner_F_lim, h_inner_ψg] using h_integral_eq ψ
        have h_int_diff :
            (∫ x : ℝ, F_lim x *
                  (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume) -
                ∫ x : ℝ, fourierIntegral g x *
                    (starRingEnd ℂ) (SchwartzMap.toFun ψ x) ∂volume = 0 :=
          sub_eq_zero.mpr h_inner_eq
        have h_inner_diff :
            @inner ℂ (Lp ℂ 2 volume) _ ψTimeLp (F_lim - ψ_gLp) = 0 := by
          simpa [inner_sub_right, h_inner_F_lim, h_inner_ψg] using h_int_diff
        have h_inner_diff' :
            @inner ℂ (Lp ℂ 2 volume) _ (F_lim - ψ_gLp) ψTimeLp = 0 := by
          simpa [inner_conj_symm]
            using congrArg (starRingEnd ℂ) h_inner_diff
        exact h_inner_diff'

      have h_diff_zero : F_lim - ψ_gLp = 0 :=
        L2_eq_zero_of_inner_schwartz h_inner_zero
      have hF_lim_eq : F_lim = ψ_gLp := sub_eq_zero.mp h_diff_zero

      -- Convert strong convergence of `ψLp` to convergence towards `ψ_gLp`.
      have hψ_tendsto' : Filter.Tendsto ψLp Filter.atTop (𝓝 ψ_gLp) := by
        simpa [ψ_gLp, hF_lim_eq] using hψ_tendsto
      have h_dist_tendsto_zero : Filter.Tendsto
          (fun n => dist (ψLp n) ψ_gLp) Filter.atTop (𝓝 (0 : ℝ)) :=
        (tendsto_iff_dist_tendsto_zero).1 hψ_tendsto'

      -- Relate distances in L² to the `eLpNorm` of the pointwise difference.
      have h_dist_eq : ∀ n,
          dist (ψLp n) ψ_gLp
              = (eLpNorm
                    (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume).toReal :=
        by
          intro n
          have hcalc :
              ψLp n - ψ_gLp
                  = ((hψ_mem n).sub hFg_L2).toLp
                      (fun ξ : ℝ => ψFun n ξ - fourierIntegral g ξ) := by
            simpa [ψLp, ψ_gLp, ψFun]
              using (MemLp.toLp_sub (hψ_mem n) hFg_L2).symm
          have hnorm :=
            Lp.norm_toLp (μ := volume)
              (f := fun ξ : ℝ => ψFun n ξ - fourierIntegral g ξ)
              ((hψ_mem n).sub hFg_L2)
          have hswap :=
            eLpNorm_sub_comm (f := fun ξ : ℝ => ψFun n ξ)
              (g := fun ξ : ℝ => fourierIntegral g ξ)
              (p := (2 : ℝ≥0∞)) (μ := volume)
          calc
            dist (ψLp n) ψ_gLp
                = ‖ψLp n - ψ_gLp‖ := by simp [dist_eq_norm]
            _ = ‖((hψ_mem n).sub hFg_L2).toLp
                    (fun ξ : ℝ => ψFun n ξ - fourierIntegral g ξ)‖ := by
                  simp [ψLp, ψ_gLp, ψFun, hcalc]
            _ =
                (eLpNorm (fun ξ : ℝ => ψFun n ξ - fourierIntegral g ξ) 2 volume).toReal := by
                  simp [ψFun]
            _ =
                (eLpNorm (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume).toReal := by
                  simpa [ψFun] using congrArg ENNReal.toReal hswap

      have h_toReal_tendsto : Filter.Tendsto
          (fun n =>
            (eLpNorm (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume).toReal)
          Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa [h_dist_eq] using h_dist_tendsto_zero

      have h_noninf : ∀ n,
          eLpNorm (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume ≠ ∞ :=
        fun n => (hFg_L2.sub (hψ_mem n)).2.ne

      have h_ENNReal_tendsto : Filter.Tendsto
          (fun n => eLpNorm (fun ξ : ℝ => fourierIntegral g ξ - ψFun n ξ) 2 volume)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
        (ENNReal.tendsto_toReal_iff h_noninf (by simp)).mp
          (by simpa [ψFun] using h_toReal_tendsto)

      simpa [ψFun]
        using h_ENNReal_tendsto

    -- Now apply continuous_integral_norm_sq_of_L2_tendsto
    have hF_memLp : ∀ n, MemLp (fun ξ => fourierIntegral (fun t => φ n t) ξ) 2 volume := by
      intro n
      exact fourierIntegral_memLp_L1_L2 (schwartz_integrable (φ n))
        (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))

    exact continuous_integral_norm_sq_of_L2_tendsto hFg_L2 hF_memLp hF_tendsto_L2

  -- Combine the limits with the sequence-wise Plancherel identity.
  have h_scaled_tendsto : Filter.Tendsto
      (fun n => ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume)) := h_left_tendsto
  have h_scaled_tendsto' : Filter.Tendsto
      (fun n => ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume)) :=
    h_right_tendsto

  have h_eq_seq : ∀ n, ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume
      = ∫ ξ : ℝ, ‖fourierIntegral (fun t => φ n t) ξ‖ ^ 2 ∂volume :=
    h_schwartz_plancherel

  have h_scaled_tendsto'' : Filter.Tendsto
      (fun n => ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n => (h_eq_seq n).symm)
      h_scaled_tendsto'

  exact tendsto_nhds_unique h_scaled_tendsto h_scaled_tendsto''

/-- Fourier inversion for Schwartz functions.
For any Schwartz function `φ`, the inverse Fourier transform of its Fourier
transform recovers `φ` pointwise. -/
lemma fourierIntegralInv_fourierIntegral_schwartz
    (φ : SchwartzMap ℝ ℂ) :
    (fun t : ℝ =>
      Real.fourierIntegralInv
        (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) t)
      = fun t : ℝ => φ t := by
  classical
  funext t
  -- Convert the inverse transform to a forward transform at `-t`.
  have h_inv :
      Real.fourierIntegralInv
          (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) t
        = Real.fourierIntegral
            (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) (-t) := by
    simp [fourierIntegralInv_eq_fourierIntegral_neg]
  -- Identify two expressions for `Real.fourierIntegral (conj ∘ 𝓕 φ) t`.
  have h_left :
      Real.fourierIntegral
          (fun ξ : ℝ => conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ)) t
        = conj (φ t) := by
    -- From `fourierIntegral (conjFourierTransform φ) = conj ∘ φ`.
    have h := (Schwartz.fourierIntegral_conj_fourierIntegral (f := φ))
    have h' := congrArg (fun F => F t) h
    simpa [fourierIntegral_eq_real] using h'
  have h_right :
      Real.fourierIntegral
          (fun ξ : ℝ => conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ)) t
        = conj (Real.fourierIntegral
            (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) (-t)) := by
    -- Conjugation identity applied to `fourierTransformCLE ℝ φ`.
    have h :=
      Schwartz.fourierIntegral_conj_eq_neg_real
        (f := fourierTransformCLE ℝ φ) (ξ := t)
    simpa [Schwartz.fourierIntegral_eq_fourierTransform] using h
  -- Cancel conjugation to identify the inner expressions.
  have h_eq :
      Real.fourierIntegral
          (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) (-t)
        = φ t := by
    have :
        conj (Real.fourierIntegral
            (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) (-t))
          = conj (φ t) := by
      simpa [h_right] using h_left
    -- Apply `conj` to both sides and simplify using `conj_conj`.
    have := congrArg conj this
    simpa using this
  simpa [h_inv] using h_eq

/-!
Auxiliary lemmas needed for the L²-based proof of a.e. inversion on L¹ ∩ L².

These are stated here with placeholder proofs to document the intended API and
to decouple signature design from the future detailed implementation.
-/

/-- L² Cauchy of `φ n` implies L² Cauchy of their Fourier transforms (Schwartz case).
In particular, `(F[φ n])` admits an L² limit. -/
lemma fourierIntegral_schwartz_cauchy_L2
    (φ : ℕ → SchwartzMap ℝ ℂ)
    (hC : CauchySeq (fun n =>
        let h : MemLp (fun t : ℝ => φ n t) 2 volume :=
          SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume)
        h.toLp (fun t => φ n t))) :
    ∃ F_lim : Lp ℂ 2 volume,
      Filter.Tendsto (fun n =>
        (fourierIntegral_memLp_of_schwartz (φ n)).toLp
          (fun ξ => Frourio.fourierIntegral (fun t => φ n t) ξ))
        Filter.atTop (𝓝 F_lim) := by
  classical
  -- Time-side L² representatives and their Cauchy property
  let φLp : ℕ → Lp ℂ 2 volume := fun n =>
    (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume)).toLp (fun t => φ n t)
  have hφ_cauchy : CauchySeq φLp := by
    simpa using hC

  -- Frequency-side L² representatives
  let ψFun : ℕ → ℝ → ℂ := fun n ξ => Frourio.fourierIntegral (fun t => φ n t) ξ
  have hψ_mem : ∀ n, MemLp (ψFun n) 2 volume := fun n =>
    fourierIntegral_memLp_of_schwartz (φ n)
  let ψLp : ℕ → Lp ℂ 2 volume := fun n => (hψ_mem n).toLp (ψFun n)

  -- Show ψLp is Cauchy by comparing distances via Plancherel on differences
  have hψ_cauchy : CauchySeq ψLp := by
    refine Metric.cauchySeq_iff.mpr ?_
    intro ε hε_pos
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hφ_cauchy ε hε_pos
    refine ⟨N, ?_⟩; intro m hm n hn
    -- Distance on frequency side via eLpNorm of the difference
    have hdiffψ : MemLp (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume :=
      (hψ_mem m).sub (hψ_mem n)
    have hdistψ :
        dist (ψLp m) (ψLp n)
          = ENNReal.toReal
              (eLpNorm (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume) := by
      have hsubψ := MemLp.toLp_sub (hψ_mem m) (hψ_mem n)
      calc
        dist (ψLp m) (ψLp n) = ‖ψLp m - ψLp n‖ := by simp [dist_eq_norm]
        _ = ‖(hψ_mem m).toLp (ψFun m) - (hψ_mem n).toLp (ψFun n)‖ := by
              rfl
        _ = ‖(hψ_mem m).sub (hψ_mem n) |>.toLp (ψFun m - ψFun n)‖ := by
              rw [← hsubψ]
        _ = ‖hdiffψ.toLp (fun ξ => ψFun m ξ - ψFun n ξ)‖ := by
              congr 1
        _ = (eLpNorm (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume).toReal := by
              simp
    -- Identify frequency difference with transform of time difference
    have hFourier_diff :
        eLpNorm (fun ξ : ℝ => ψFun m ξ - ψFun n ξ) 2 volume
          = eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume := by
      have hrewrite :
          (fun ξ : ℝ => ψFun m ξ - ψFun n ξ)
            = fun ξ => Frourio.fourierIntegral
                (fun t : ℝ => φ m t - φ n t) ξ := by
        funext ξ
        have := fourierIntegral_sub
            (f := fun t => φ m t) (g := fun t => φ n t)
            (hf := schwartz_integrable (φ m)) (hg := schwartz_integrable (φ n))
            (ξ := ξ)
        simpa [ψFun, sub_eq_add_neg] using this.symm
      simpa [hrewrite]
        using fourierIntegral_eLpNorm_eq (φ := φ m - φ n)
    -- Distance on time side
    have hdiffφ : MemLp (fun t : ℝ => φ m t - φ n t) 2 volume :=
      (SchwartzMap.memLp (φ m) (p := (2 : ℝ≥0∞)) (μ := volume)).sub
        (SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume))
    have hdistφ :
        dist (φLp m) (φLp n)
          = ENNReal.toReal
              (eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume) := by
      let hφm := SchwartzMap.memLp (φ m) (p := (2 : ℝ≥0∞)) (μ := volume)
      let hφn := SchwartzMap.memLp (φ n) (p := (2 : ℝ≥0∞)) (μ := volume)
      have hsubφ := MemLp.toLp_sub hφm hφn
      calc
        dist (φLp m) (φLp n) = ‖φLp m - φLp n‖ := by simp [dist_eq_norm]
        _ = ‖hφm.toLp (fun t => φ m t) - hφn.toLp (fun t => φ n t)‖ := by
              rfl
        _ = ‖(hφm.sub hφn).toLp ((fun t => φ m t) - (fun t => φ n t))‖ := by
              rw [← hsubφ]
        _ = ‖hdiffφ.toLp (fun t => φ m t - φ n t)‖ := by
              congr 1
        _ = (eLpNorm (fun t : ℝ => φ m t - φ n t) 2 volume).toReal := by
              simp
    -- Conclude using equality of the two distances
    have hψφ_eq : dist (ψLp m) (ψLp n) = dist (φLp m) (φLp n) := by
      simpa [hdistψ, hdistφ] using congrArg ENNReal.toReal hFourier_diff
    exact (by simpa [hψφ_eq] using hN m hm n hn)

  -- Completeness of L² yields the limit
  obtain ⟨F_lim, h_tendsto⟩ := cauchySeq_tendsto_of_complete hψ_cauchy
  exact ⟨F_lim, h_tendsto⟩

/-- The inverse Fourier transform is an L² isometry on the closure of the Schwartz range.
Hence, L² convergence on the frequency side transports to L² convergence after applying
the inverse transform. -/
lemma inverseFourier_tendsto_L2_of_tendsto_L2
    {u : ℕ → ℝ → ℂ} {v : ℝ → ℂ}
    (hu_schw : ∀ n, ∃ φn : SchwartzMap ℝ ℂ,
        u n = fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φn t) ξ)
    (hv_schw : ∃ ψ : SchwartzMap ℝ ℂ,
        v = fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ)
    (h_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun ξ => u n ξ - v ξ) 2 volume)
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n =>
      eLpNorm (fun t =>
        Real.fourierIntegralInv (fun ξ => u n ξ) t
          - Real.fourierIntegralInv (fun ξ => v ξ) t) 2 volume)
      Filter.atTop (𝓝 0) := by
  classical
  -- Choose Schwartz witnesses for u and v
  choose φ hφ_repr using hu_schw
  obtain ⟨ψ, hψ_repr⟩ := hv_schw

  -- Identify inverse transforms with the original Schwartz functions
  have h_inv_n : ∀ n,
      (fun t : ℝ =>
        Real.fourierIntegralInv (fun ξ : ℝ => u n ξ) t)
        = fun t : ℝ => φ n t := by
    intro n
    have :
        (fun t : ℝ =>
          Real.fourierIntegralInv
            (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ) t)
          = fun t : ℝ => φ n t :=
      fourierIntegralInv_fourierIntegral_schwartz (φ n)
    simpa [hφ_repr n]
      using this

  have h_inv_v :
      (fun t : ℝ =>
        Real.fourierIntegralInv (fun ξ : ℝ => v ξ) t)
        = fun t : ℝ => ψ t := by
    have :
        (fun t : ℝ =>
          Real.fourierIntegralInv
            (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ) t)
          = fun t : ℝ => ψ t :=
      fourierIntegralInv_fourierIntegral_schwartz ψ
    simpa [hψ_repr]
      using this

  -- For each n, relate the frequency-side L² error to the time-side one.
  have h_err_eq : ∀ n,
      eLpNorm (fun ξ : ℝ => u n ξ - v ξ) 2 volume
        = eLpNorm (fun t : ℝ => φ n t - ψ t) 2 volume := by
    intro n
    have hsub :
        (fun ξ : ℝ => u n ξ - v ξ)
          = fun ξ : ℝ =>
              Frourio.fourierIntegral (fun t : ℝ => φ n t - ψ t) ξ := by
      funext ξ
      have hlin :=
        fourierIntegral_sub
          (f := fun t : ℝ => φ n t) (g := fun t : ℝ => ψ t)
          (hf := schwartz_integrable (φ n)) (hg := schwartz_integrable ψ)
          (ξ := ξ)
      calc
        u n ξ - v ξ
          = Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ
            - Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ := by
              rw [hφ_repr n, hψ_repr]
        _ = Frourio.fourierIntegral (fun t : ℝ => φ n t - ψ t) ξ := by
              rw [← hlin]
    -- Use L² isometry for Schwartz functions
    simpa [hsub]
      using fourierIntegral_eLpNorm_eq (φ := φ n - ψ)

  -- The target sequence equals the time-side L² error via the inverse identities
  have h_target_eq : ∀ n,
      eLpNorm (fun t : ℝ =>
        Real.fourierIntegralInv (fun ξ : ℝ => u n ξ) t
          - Real.fourierIntegralInv (fun ξ : ℝ => v ξ) t) 2 volume
        = eLpNorm (fun t : ℝ => φ n t - ψ t) 2 volume := by
    intro n
    have :
        (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ : ℝ => u n ξ) t
            - Real.fourierIntegralInv (fun ξ : ℝ => v ξ) t)
          = fun t : ℝ => φ n t - ψ t := by
      funext t
      simp [h_inv_n n, h_inv_v]
    simp [this]

  -- Transport convergence along pointwise equalities of the sequences
  have h1 : Filter.Tendsto (fun n => eLpNorm (fun t : ℝ => φ n t - ψ t) 2 volume)
      Filter.atTop (𝓝 0) := by
    refine h_tendsto.congr' ?_
    exact Filter.Eventually.of_forall h_err_eq
  refine h1.congr' ?_
  exact Filter.Eventually.of_forall (fun n => (h_target_eq n).symm)

/-- L² convergence from approximation with controlled error bounds.

Given a sequence of approximations `approx n` to a target function `target` in L²,
where the approximation error `‖target - approx n‖₂` is bounded by `err n` and
the error bounds `err n` tend to zero, this shows that `approx n` converges to
`target` in L². -/
lemma eLpNorm_tendsto_of_error_tendsto
    {approx : ℕ → ℝ → ℂ} {target : ℝ → ℂ} {err : ℕ → ℝ≥0∞}
    (h_bound : ∀ n, eLpNorm (fun x => target x - approx n x) 2 volume < err n)
    (h_err_tendsto : Filter.Tendsto err Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun n => eLpNorm (fun x => target x - approx n x) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  -- Squeeze theorem: 0 ≤ eLpNorm(...) < err n and err n → 0 implies eLpNorm(...) → 0
  have h_nonneg : ∀ n, 0 ≤ eLpNorm (fun x => target x - approx n x) 2 volume :=
    fun n => zero_le _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ h_err_tendsto h_nonneg ?_
  · exact tendsto_const_nhds
  · intro n
    exact le_of_lt (h_bound n)

/-- Uniqueness of L² limits: if two functions are both L² limits of a common
sequence, they are a.e. equal.

Given a sequence `ψ n` in L² and two L² functions `u` and `v` such that
both `u` and `v` are strong L² limits of `ψ n` (i.e., `‖ψ n - u‖₂ → 0` and
`‖ψ n - v‖₂ → 0`), this lemma shows that `u =ᵐ[volume] v`. -/
lemma ae_eq_of_L2_two_limits
    {ψ : ℕ → ℝ → ℂ} {u v : ℝ → ℂ}
    (hψ_L2 : ∀ n, MemLp (ψ n) 2 volume)
    (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume)
    (hu_lim : Filter.Tendsto (fun n => eLpNorm (fun t => u t - ψ n t) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (hv_lim : Filter.Tendsto (fun n => eLpNorm (fun t => v t - ψ n t) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    u =ᵐ[volume] v := by
  classical
  -- Lift to L² elements
  let ψLp : ℕ → Lp ℂ 2 volume := fun n => (hψ_L2 n).toLp (ψ n)
  let uLp : Lp ℂ 2 volume := hu.toLp u
  let vLp : Lp ℂ 2 volume := hv.toLp v
  -- Control the norm of the difference by triangle inequality
  have h_norm_u : ∀ n,
      ‖uLp - ψLp n‖
        = ENNReal.toReal (eLpNorm (fun t => u t - ψ n t) 2 volume) := by
    intro n
    have hdiff : MemLp (fun t => u t - ψ n t) 2 volume := hu.sub (hψ_L2 n)
    have hcalc :
        ((hu.sub (hψ_L2 n)).toLp (fun t => u t - ψ n t))
          = uLp - ψLp n := by
      simpa [uLp, ψLp] using MemLp.toLp_sub hu (hψ_L2 n)
    have hnorm := Lp.norm_toLp (μ := volume)
        (f := fun t => u t - ψ n t) hdiff
    simpa [hdiff, hcalc, norm_sub_rev]
      using hnorm
  have h_norm_v : ∀ n,
      ‖vLp - ψLp n‖
        = ENNReal.toReal (eLpNorm (fun t => v t - ψ n t) 2 volume) := by
    intro n
    have hdiff : MemLp (fun t => v t - ψ n t) 2 volume := hv.sub (hψ_L2 n)
    have hcalc :
        ((hv.sub (hψ_L2 n)).toLp (fun t => v t - ψ n t))
          = vLp - ψLp n := by
      simpa [vLp, ψLp] using MemLp.toLp_sub hv (hψ_L2 n)
    have hnorm := Lp.norm_toLp (μ := volume)
        (f := fun t => v t - ψ n t) hdiff
    simpa [hdiff, hcalc, norm_sub_rev]
      using hnorm
  -- Convert the ENNReal limits to real limits via toReal
  have h_toReal_u : Filter.Tendsto
      (fun n => ENNReal.toReal (eLpNorm (fun t => u t - ψ n t) 2 volume))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    have h_ne : ∀ n, eLpNorm (fun t => u t - ψ n t) 2 volume ≠ ∞ :=
      fun n => (hu.sub (hψ_L2 n)).2.ne
    simpa using
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n => eLpNorm (fun t => u t - ψ n t) 2 volume)
        h_ne (by simp)).mpr hu_lim
  have h_toReal_v : Filter.Tendsto
      (fun n => ENNReal.toReal (eLpNorm (fun t => v t - ψ n t) 2 volume))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    have h_ne : ∀ n, eLpNorm (fun t => v t - ψ n t) 2 volume ≠ ∞ :=
      fun n => (hv.sub (hψ_L2 n)).2.ne
    simpa using
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n => eLpNorm (fun t => v t - ψ n t) 2 volume)
        h_ne (by simp)).mpr hv_lim
  -- Use epsilon argument on the triangle inequality to show the difference has zero norm.
  have h_norm_zero : ‖uLp - vLp‖ = 0 := by
    -- Translate the ENNReal limits to real limits on norms of differences
    have hu0 : Filter.Tendsto (fun n => ‖uLp - ψLp n‖) Filter.atTop (𝓝 (0 : ℝ)) := by
      refine h_toReal_u.congr' ?_
      exact Filter.Eventually.of_forall (fun n => (h_norm_u n).symm)
    have hv0 : Filter.Tendsto (fun n => ‖vLp - ψLp n‖) Filter.atTop (𝓝 (0 : ℝ)) := by
      refine h_toReal_v.congr' ?_
      exact Filter.Eventually.of_forall (fun n => (h_norm_v n).symm)
    -- Prove by contradiction using an ε-argument on the triangle inequality
    classical
    by_contra hne
    have hpos : 0 < ‖uLp - vLp‖ :=
      lt_of_le_of_ne (norm_nonneg _) (by simpa [eq_comm] using hne)
    set ε : ℝ := ‖uLp - vLp‖ / 2 with hε_def
    have hε_pos : 0 < ε := by simpa [ε, hε_def] using half_pos hpos
    have h_event_u : ∀ᶠ n in Filter.atTop, ‖uLp - ψLp n‖ < ε / 2 :=
      Filter.Tendsto.eventually_lt hu0 tendsto_const_nhds
        (by simpa [ε, hε_def] using half_pos hε_pos)
    have h_event_v : ∀ᶠ n in Filter.atTop, ‖vLp - ψLp n‖ < ε / 2 :=
      Filter.Tendsto.eventually_lt hv0 tendsto_const_nhds
        (by simpa [ε, hε_def] using half_pos hε_pos)
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 h_event_u
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 h_event_v
    have htri : ∀ n ≥ max N1 N2,
        ‖uLp - vLp‖ ≤ ‖uLp - ψLp n‖ + ‖vLp - ψLp n‖ := by
      intro n hn
      have hsum : (uLp - ψLp n) + (ψLp n - vLp) = uLp - vLp := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      have := norm_add_le (uLp - ψLp n) (ψLp n - vLp)
      simpa [hsum, norm_sub_rev]
        using this
    have hN1' : ∀ n ≥ max N1 N2, ‖uLp - ψLp n‖ < ε / 2 :=
      fun n hn => hN1 n (le_trans (le_max_left _ _) hn)
    have hN2' : ∀ n ≥ max N1 N2, ‖vLp - ψLp n‖ < ε / 2 :=
      fun n hn => hN2 n (le_trans (le_max_right _ _) hn)
    have hsum : ∀ n ≥ max N1 N2,
        ‖uLp - ψLp n‖ + ‖vLp - ψLp n‖ < ε := by
      intro n hn; nlinarith [hN1' n hn, hN2' n hn]
    have hlt : ‖uLp - vLp‖ < ε :=
      lt_of_le_of_lt (htri (max N1 N2) le_rfl) (hsum (max N1 N2) le_rfl)
    have : ε < ‖uLp - vLp‖ := by
      have := half_lt_self hpos
      simpa [ε, hε_def] using this
    exact (not_lt.mpr (le_of_lt hlt)) this
  -- Equality in Lp implies a.e. equality of representatives
  have h_sub_zero : uLp - vLp = 0 := by
    simpa using (norm_eq_zero.mp h_norm_zero)
  have : uLp = vLp := sub_eq_zero.mp h_sub_zero
  -- Convert back to concrete functions
  have hu_coe : (fun t => (uLp : ℝ → ℂ) t) =ᵐ[volume] u := MemLp.coeFn_toLp hu
  have hv_coe : (fun t => (vLp : ℝ → ℂ) t) =ᵐ[volume] v := MemLp.coeFn_toLp hv
  have hv_coe' : (fun t => (uLp : ℝ → ℂ) t) =ᵐ[volume] v := by
    simpa [this] using hv_coe
  exact (hu_coe.symm.trans hv_coe')

/-! ## Fourier transform as an L² operator

We define the Fourier transform and its inverse as continuous linear operators on L²(ℝ).
This is the mathematically correct approach that avoids circularity issues.

### The Circular Dependency Problem

The original approach defined the inverse Fourier transform as a pointwise integral:
```
u(t) = ∫ w(ξ) e^{2πitξ} dξ
```
and then attempted to prove `u ∈ L²`. This creates a circular dependency:

- To prove `u ∈ L²`, we need to show the inverse transform preserves L² membership
- But proving this requires knowing that inverse transforms of L² approximants converge
- Which requires knowing the limit is in L²
- Which is what we're trying to prove!

### The Solution: Operator-Based Definition

Standard mathematics avoids this by defining the Fourier transform as an **operator** rather
than a pointwise integral. The construction is:

1. **On Schwartz functions**: Define F[φ] and show it's an isometry (Plancherel)
2. **Density**: Schwartz functions are dense in L²
3. **Extension**: Every isometry on a dense subspace extends uniquely to the whole space
4. **L² definition**: The Fourier transform on L² is this unique extension

This approach never asks "is the pointwise integral in L²?" - instead, it constructs
the L² element directly through the extension theorem.
-/

/-- The Fourier transform as a densely defined operator on L²,
initially defined on Schwartz functions. -/
def fourierTransformDense (φ : SchwartzMap ℝ ℂ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (fourierIntegral_memLp_of_schwartz φ).toLp (fun ξ => Frourio.fourierIntegral φ ξ)

/-- The Fourier transform preserves L² norm on Schwartz functions. -/
lemma fourierTransformDense_isometry (φ : SchwartzMap ℝ ℂ) :
    ‖fourierTransformDense φ‖ = ‖(SchwartzMap.memLp φ 2 (volume : Measure ℝ)).toLp φ‖ := by
  unfold fourierTransformDense
  have h_norm := Lp.norm_toLp (μ := (volume : Measure ℝ))
    (f := fun ξ => Frourio.fourierIntegral φ ξ)
    (fourierIntegral_memLp_of_schwartz φ)
  rw [h_norm]
  have h_eq := fourierIntegral_eLpNorm_eq φ
  rw [h_eq]
  exact (Lp.norm_toLp (μ := (volume : Measure ℝ)) (f := φ)
    (SchwartzMap.memLp φ 2 (volume : Measure ℝ))).symm

/-- Helper: The inverse Fourier transform of a Schwartz function is in L². -/
lemma inverseFourierIntegral_memLp_of_schwartz_function (ψ : SchwartzMap ℝ ℂ) :
    MemLp (fun t => Real.fourierIntegralInv (fun ξ => ψ ξ) t) 2 volume := by
  classical
  -- First, the forward Fourier transform of a Schwartz function is in L².
  have h_fwd :
      MemLp (fun t : ℝ => Real.fourierIntegral (fun ξ : ℝ => ψ ξ) t) 2 volume := by
    -- Use the existing L² membership for `fourierIntegral` on Schwartz functions,
    -- switching names of dummy variables and converting to `Real.fourierIntegral`.
    simpa [fourierIntegral_eq_real] using
      (fourierIntegral_memLp_of_schwartz (φ := ψ))
  -- The inverse transform is the forward transform evaluated at `-t`.
  have h_eq :
      (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => ψ ξ) t)
        = fun t : ℝ => Real.fourierIntegral (fun ξ : ℝ => ψ ξ) (-t) := by
    funext t; simp [fourierIntegralInv_eq_fourierIntegral_neg]
  -- Precomposition with reflection `t ↦ -t` preserves L² membership.
  have h_comp :
      MemLp (fun t : ℝ => Real.fourierIntegral (fun ξ : ℝ => ψ ξ) (-t)) 2 volume := by
    simpa using
      h_fwd.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  -- Conclude using the identification with the inverse Fourier transform.
  simpa [h_eq] using h_comp

/-- The inverse Fourier transform as a densely defined operator on L²,
initially defined on Schwartz functions. -/
def inverseFourierTransformDense (ψ : SchwartzMap ℝ ℂ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (inverseFourierIntegral_memLp_of_schwartz_function ψ).toLp
    (fun t => Real.fourierIntegralInv (fun ξ => ψ ξ) t)

/-- The inverse Fourier transform preserves L² norm on Schwartz functions. -/
lemma inverseFourierTransformDense_isometry (ψ : SchwartzMap ℝ ℂ) :
    ‖inverseFourierTransformDense ψ‖ = ‖(SchwartzMap.memLp ψ 2 (volume : Measure ℝ)).toLp ψ‖ := by
  unfold inverseFourierTransformDense
  rw [Lp.norm_toLp]
  -- Reduce the inverse transform to the forward transform at `-t`.
  have h_inv_as_fwd :
      (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => ψ ξ) t)
        = fun t : ℝ => Real.fourierIntegral (fun ξ : ℝ => ψ ξ) (-t) := by
    funext t; simp [fourierIntegralInv_eq_fourierIntegral_neg]
  -- The forward Fourier transform of a Schwartz function is a.e.-strongly measurable.
  have h_meas_fwd :
      AEStronglyMeasurable (fun t : ℝ => Real.fourierIntegral (fun ξ : ℝ => ψ ξ) t)
        (volume : Measure ℝ) := by
    have h_mem :
        MemLp (fun t : ℝ => Real.fourierIntegral (fun ξ : ℝ => ψ ξ) t) 2 (volume : Measure ℝ) := by
      simpa [fourierIntegral_eq_real]
        using (fourierIntegral_memLp_of_schwartz (φ := ψ))
    exact h_mem.1
  -- Use measure preservation of reflection `t ↦ -t` to remove the composition in the L² norm.
  have h_eLp_inv_eq_fwd :
      eLpNorm (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => ψ ξ) t) 2 (volume : Measure ℝ)
        = eLpNorm (fun t : ℝ => Real.fourierIntegral
          (fun ξ : ℝ => ψ ξ) t) 2 (volume : Measure ℝ) := by
    have h :=
      eLpNorm_comp_measurePreserving (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (p := (2 : ℝ≥0∞))
        (f := fun t : ℝ => -t)
        (g := fun t : ℝ => Real.fourierIntegral (fun ξ : ℝ => ψ ξ) t)
        h_meas_fwd (Measure.measurePreserving_neg (volume : Measure ℝ))
    simpa [Function.comp, h_inv_as_fwd]
      using h
  -- Switch from `Real.fourierIntegral` to our kernel formulation and invoke Plancherel on Schwartz.
  have h_fwd_real_to_kernel :
      eLpNorm (fun t : ℝ => Real.fourierIntegral (fun ξ : ℝ => ψ ξ) t) 2 (volume : Measure ℝ)
        = eLpNorm (fun t : ℝ => Frourio.fourierIntegral (fun ξ : ℝ => ψ ξ) t) 2
            (volume : Measure ℝ) := by
    simp [fourierIntegral_eq_real]
  have h_plancherel :
      eLpNorm (fun t : ℝ => Frourio.fourierIntegral (fun ξ : ℝ => ψ ξ) t) 2 (volume : Measure ℝ)
        = eLpNorm (fun t : ℝ => ψ t) 2 (volume : Measure ℝ) := by
    simpa using (fourierIntegral_eLpNorm_eq (φ := ψ))
  -- Chain the equalities and conclude via the `Lp.norm_toLp` identity on the time side.
  have h_chain :
      eLpNorm (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => ψ ξ) t) 2 (volume : Measure ℝ)
        = eLpNorm (fun t : ℝ => ψ t) 2 (volume : Measure ℝ) := by
    calc
      eLpNorm (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => ψ ξ) t) 2 (volume : Measure ℝ)
          = eLpNorm (fun t : ℝ => Real.fourierIntegral
            (fun ξ : ℝ => ψ ξ) t) 2 (volume : Measure ℝ) := h_eLp_inv_eq_fwd
      _ = eLpNorm (fun t : ℝ => Frourio.fourierIntegral
          (fun ξ : ℝ => ψ ξ) t) 2 (volume : Measure ℝ) := h_fwd_real_to_kernel
      _ = eLpNorm (fun t : ℝ => ψ t) 2 (volume : Measure ℝ) := h_plancherel
  -- Finish: identify the RHS with the norm of `(SchwartzMap.memLp ψ).toLp ψ`.
  simp [h_chain]

/-- Helper: Schwartz function corresponding to Fourier transform of another Schwartz function.
This is a temporary construction showing that F[φ] viewed as a function is actually Schwartz. -/
def fourierAsSchwartzFunction (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := by
  -- Use mathlib's Fourier transform on Schwartz space.
  exact fourierTransformCLE ℝ φ

/-- The L² element from fourierTransformDense agrees with the Schwartz function view. -/
lemma fourierTransformDense_eq_schwartz (φ : SchwartzMap ℝ ℂ) :
    fourierTransformDense φ =
      (SchwartzMap.memLp (fourierAsSchwartzFunction φ) 2 (volume : Measure ℝ)).toLp
        (fourierAsSchwartzFunction φ) := by
  classical
  unfold fourierTransformDense
  -- Compare the two `toLp` representatives via a.e. equality of functions.
  refine
    (MemLp.toLp_eq_toLp_iff
        (fourierIntegral_memLp_of_schwartz φ)
        (SchwartzMap.memLp (fourierAsSchwartzFunction φ)
          (p := (2 : ℝ≥0∞)) (μ := (volume : Measure ℝ)))).mpr ?_
  -- Pointwise identity: the explicit-kernel Fourier integral equals
  -- mathlib's Schwartz Fourier transform.
  refine Filter.Eventually.of_forall ?_
  intro ξ
  simpa [fourierAsSchwartzFunction]
    using (Schwartz.fourierIntegral_eq_fourierTransform (f := φ) (ξ := ξ))

/-- The composition of inverse and Fourier transforms is identity on Schwartz functions (in L²). -/
lemma inverseFourier_comp_fourier_eq_id (φ : SchwartzMap ℝ ℂ) :
    inverseFourierTransformDense (fourierAsSchwartzFunction φ) =
      (SchwartzMap.memLp φ 2 (volume : Measure ℝ)).toLp φ := by
  classical
  unfold inverseFourierTransformDense
  -- Compare `toLp` representatives via a.e. equality.
  refine
    (MemLp.toLp_eq_toLp_iff
        (inverseFourierIntegral_memLp_of_schwartz_function
          (ψ := fourierAsSchwartzFunction φ))
        (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := (volume : Measure ℝ)))).mpr ?_
  -- Show pointwise equality using Fourier inversion on Schwartz functions.
  refine Filter.Eventually.of_forall ?_
  intro t
  -- Identify the frequency-side input with our explicit Fourier integral.
  have hψ :
      (fun ξ : ℝ => (fourierAsSchwartzFunction φ) ξ)
        = fun ξ : ℝ => Frourio.fourierIntegral (fun s : ℝ => φ s) ξ := by
    funext ξ
    simpa [fourierAsSchwartzFunction]
      using (Schwartz.fourierIntegral_eq_fourierTransform (f := φ) (ξ := ξ)).symm
  -- Apply the inversion formula for Schwartz functions.
  have := fourierIntegralInv_fourierIntegral_schwartz (φ := φ)
  -- Evaluate at `t` and rewrite the input using `hψ`.
  have h_eval :
      Real.fourierIntegralInv
          (fun ξ : ℝ => Frourio.fourierIntegral (fun s : ℝ => φ s) ξ) t
        = φ t := by
    simpa using congrArg (fun F => F t) this
  simpa [hψ] using h_eval

/-- Pairing identity for integrable frequency-side functions (signature only).

If `f ∈ L¹` and `φ` is Schwartz, then
  ∫ invF(f)(t) · conj(φ(t)) dt = ∫ f(ξ) · conj(F[φ](ξ)) dξ. -/
lemma inverseFourier_pairing_schwartz_L1
    {f : ℝ → ℂ} (hf : Integrable f) (φ : SchwartzMap ℝ ℂ) :
    ∫ t : ℝ, (Real.fourierIntegralInv (fun ξ : ℝ => f ξ) t) * (conj (φ t)) ∂volume
      = ∫ ξ : ℝ, (f ξ) * (conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ)) ∂volume := by
  classical
  -- Schwartz functions are integrable (L¹)
  have hφ_L1 : Integrable (fun t : ℝ => φ t) := schwartz_integrable φ
  have hφ_conj_L1 : Integrable (fun t : ℝ => conj (φ t)) :=
    integrable_conj_of_integrable hφ_L1

  -- Rewrite the inverse Fourier integral using the explicit kernel on the frequency side.
  have h_inv_apply : ∀ t : ℝ,
      Real.fourierIntegralInv (fun ξ : ℝ => f ξ) t
        = ∫ ξ : ℝ, fourierKernel (-t) ξ * f ξ := by
    intro t
    -- First move to the forward real transform at `-t`, then to the explicit kernel form.
    have h_eq :
        Real.fourierIntegral (fun ξ : ℝ => f ξ) (-t)
          = ∫ ξ : ℝ, fourierKernel (-t) ξ * f ξ := by
      simp [fourierIntegral_eq_real, fourierIntegral]
    simpa [fourierIntegralInv_eq_fourierIntegral_neg] using h_eq

  -- Pull the time-side factor inside the frequency integral.
  have h_pull : ∀ t : ℝ,
      (∫ ξ : ℝ, fourierKernel (-t) ξ * f ξ) * conj (φ t)
        = ∫ ξ : ℝ, (fourierKernel (-t) ξ * f ξ) * conj (φ t) := by
    intro t
    have hint : Integrable (fun ξ : ℝ => fourierKernel (-t) ξ * f ξ) := by
      -- Fixed t: integrability in ξ follows from hf and ‖fourierKernel‖ = 1
      simpa using integrable_fourierKernel_mul (-t) hf
    simpa using
      (MeasureTheory.integral_mul_const (μ := volume)
        (f := fun ξ : ℝ => fourierKernel (-t) ξ * f ξ) (r := conj (φ t))).symm

  -- Rewrite the left-hand side as a double integral over t and ξ.
  have h_lhs_rewrite :
      ∫ t : ℝ,
          (Real.fourierIntegralInv (fun ξ : ℝ => f ξ) t) * conj (φ t) ∂volume
        = ∫ t : ℝ, ∫ ξ : ℝ,
            (fourierKernel (-t) ξ * f ξ) * conj (φ t) ∂volume ∂volume := by
    have :=
      integral_congr_ae (μ := (volume : Measure ℝ))
        (f := fun t : ℝ =>
          (Real.fourierIntegralInv (fun ξ : ℝ => f ξ) t) * conj (φ t))
        (g := fun t : ℝ =>
          (∫ ξ : ℝ, fourierKernel (-t) ξ * f ξ) * conj (φ t))
        (Filter.Eventually.of_forall (fun t => by simp [h_inv_apply]))
    -- Push the factor `conj (φ t)` inside the inner integral.
    simp [h_inv_apply, h_pull]

  -- Establish integrability on the product to justify Fubini/Tonelli swap.
  have h_prod_int :
      Integrable (fun p : ℝ × ℝ =>
        (fourierKernel (-p.1) p.2 * f p.2) * conj (φ p.1)) (volume.prod volume) := by
    -- Measurability of each factor on the product.
    have h_meas_kernel : Measurable (fun p : ℝ × ℝ => fourierKernel (-p.1) p.2) := by
      -- fourierKernel ξ t = exp(ofReal (-(2π) * ξ * t) * I)
      unfold fourierKernel
      apply Measurable.cexp
      apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      have h' : Measurable (fun a : ℝ × ℝ => (2 * Real.pi) * (-a.1 * a.2)) :=
        (measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * Real.pi)).mul
          ((measurable_fst.neg.mul measurable_snd))
      have : Measurable (fun a : ℝ × ℝ => -(2 * Real.pi * -a.1 * a.2)) := by
        apply Measurable.neg
        convert h' using 1
        ext a
        ring
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using this
    have h_meas_f : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (volume.prod volume) := by
      -- f is integrable on ℝ, hence AEStronglyMeasurable
      have h_f_aesm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
      -- Get a strongly measurable representative g of f
      obtain ⟨g, hg_meas, hg_ae⟩ := h_f_aesm
      -- g ∘ snd is strongly measurable on the product
      refine ⟨fun p => g p.2, ?_, ?_⟩
      · -- g ∘ snd is strongly measurable
        exact hg_meas.comp_measurable measurable_snd
      · -- f ∘ snd =ᵃᵉ g ∘ snd on product measure
        -- Use the null_of_locally_null or prod measure properties
        rw [Filter.EventuallyEq, ae_iff] at hg_ae ⊢
        -- The set {p | f p.2 ≠ g p.2} = ℝ × {x | f x ≠ g x}
        calc (volume.prod volume) {p : ℝ × ℝ | f p.2 ≠ g p.2}
            = (volume.prod volume) (Set.univ ×ˢ {x | f x ≠ g x}) := by
                congr; ext ⟨a, b⟩; simp
          _ = volume Set.univ * volume {x | f x ≠ g x} := by
                apply Measure.prod_prod
          _ = volume Set.univ * 0 := by rw [hg_ae]
          _ = 0 := by simp
    have h_meas_phi_aem : AEMeasurable (fun p : ℝ × ℝ => conj (φ p.1)) (volume.prod volume) := by
      have : Measurable (fun p : ℝ × ℝ => conj (φ p.1)) :=
        (Complex.continuous_conj.comp (SchwartzMap.continuous φ)).measurable.comp measurable_fst
      exact this.aemeasurable
    have h_meas_phi : AEStronglyMeasurable (fun p : ℝ × ℝ => conj (φ p.1)) (volume.prod volume) :=
      h_meas_phi_aem.aestronglyMeasurable
    have h_aesm : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (fourierKernel (-p.1) p.2 * f p.2) * conj (φ p.1))
        (volume.prod volume) :=
      ((h_meas_kernel.aestronglyMeasurable).mul h_meas_f).mul h_meas_phi

    -- Finite L¹ norm via Tonelli and factorization into marginals.
    have h_point :
        (fun p : ℝ × ℝ =>
            ‖(fourierKernel (-p.1) p.2 * f p.2) * conj (φ p.1)‖ₑ)
          = (fun p : ℝ × ℝ => ENNReal.ofReal ‖φ p.1‖ * ENNReal.ofReal ‖f p.2‖) := by
      funext p
      have hk : ‖fourierKernel (-p.1) p.2‖ = 1 := by
        simpa using fourierKernel_norm (-p.1) p.2
      calc ‖(fourierKernel (-p.1) p.2 * f p.2) * conj (φ p.1)‖ₑ
          = (‖(fourierKernel (-p.1) p.2 * f p.2) * conj (φ p.1)‖₊ : ℝ≥0∞) := rfl
        _ = (‖fourierKernel (-p.1) p.2 * f p.2‖₊ : ℝ≥0∞) * ‖conj (φ p.1)‖₊ := by
              rw [nnnorm_mul]; simp only [ENNReal.coe_mul]
        _ = ((‖fourierKernel (-p.1) p.2‖₊ : ℝ≥0∞) * ‖f p.2‖₊) * ‖conj (φ p.1)‖₊ := by
              rw [nnnorm_mul]; simp only [ENNReal.coe_mul]
        _ = ((1 : ℝ≥0∞) * ‖f p.2‖₊) * ‖φ p.1‖₊ := by
              have h1 : (‖fourierKernel (-p.1) p.2‖₊ : ℝ≥0∞) = 1 := by
                have : ‖fourierKernel (-p.1) p.2‖₊ = 1 := by
                  ext; simp [hk]
                simp [this]
              have h2 : (‖conj (φ p.1)‖₊ : ℝ≥0∞) = ‖φ p.1‖₊ := by
                have : ‖conj (φ p.1)‖ = ‖φ p.1‖ := norm_conj _
                simp [this]
              rw [h1, h2]
        _ = (‖φ p.1‖₊ : ℝ≥0∞) * ‖f p.2‖₊ := by ring
        _ = ENNReal.ofReal ‖φ p.1‖ * ENNReal.ofReal ‖f p.2‖ := by
              congr 1
              · rw [← ENNReal.ofReal_coe_nnreal]; rfl
              · rw [← ENNReal.ofReal_coe_nnreal]; rfl
    have h_tonelli :=
      MeasureTheory.lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (f := fun q : ℝ × ℝ => ENNReal.ofReal ‖φ q.1‖ * ENNReal.ofReal ‖f q.2‖)
        (by
          apply AEMeasurable.mul
          · apply Measurable.aemeasurable
            apply Measurable.ennreal_ofReal
            exact (SchwartzMap.continuous φ).norm.measurable.comp measurable_fst
          · have : AEMeasurable (fun p : ℝ × ℝ => ‖f p.2‖) (volume.prod volume) := by
              -- Use existing hypothesis h_meas_f which gives us what we need
              exact h_meas_f.norm.aemeasurable
            apply AEMeasurable.ennreal_ofReal
            exact this
        )
    have h_iter :
        ∫⁻ p, ENNReal.ofReal ‖φ p.1‖ * ENNReal.ofReal ‖f p.2‖ ∂(volume.prod volume)
          = ∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal ‖φ x‖ * ENNReal.ofReal ‖f y‖ := by
      simpa using h_tonelli
    have h_congr :
        ∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal ‖φ x‖ * ENNReal.ofReal ‖f y‖
          = ∫⁻ x : ℝ, ENNReal.ofReal ‖φ x‖ * ∫⁻ y : ℝ, ENNReal.ofReal ‖f y‖ := by
      refine lintegral_congr_ae ?_
      apply Filter.Eventually.of_forall
      intro x
      simp only
      have h_aemeas : AEMeasurable (fun y => ENNReal.ofReal ‖f y‖) volume := by
        refine AEMeasurable.ennreal_ofReal ?_
        exact hf.aestronglyMeasurable.norm.aemeasurable
      rw [← lintegral_const_mul'' (ENNReal.ofReal ‖φ x‖) h_aemeas]
    have h_prod_eq :
        ∫⁻ p, ENNReal.ofReal ‖φ p.1‖ * ENNReal.ofReal ‖f p.2‖ ∂(volume.prod volume)
          = (∫⁻ t, ENNReal.ofReal ‖φ t‖) * ∫⁻ ξ, ENNReal.ofReal ‖f ξ‖ := by
      calc
        ∫⁻ p, ENNReal.ofReal ‖φ p.1‖ * ENNReal.ofReal ‖f p.2‖ ∂(volume.prod volume)
            = ∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal ‖φ x‖ * ENNReal.ofReal ‖f y‖ := h_iter
        _ = ∫⁻ x : ℝ, ENNReal.ofReal ‖φ x‖ * ∫⁻ y : ℝ, ENNReal.ofReal ‖f y‖ := h_congr
        _ = (∫⁻ x : ℝ, ENNReal.ofReal ‖φ x‖) * ∫⁻ y : ℝ, ENNReal.ofReal ‖f y‖ := by
              have h_meas : Measurable (fun x => ENNReal.ofReal ‖φ x‖) := by
                -- φ is a Schwartz function, hence continuous
                -- The norm of a continuous function is continuous, hence measurable
                apply Measurable.ennreal_ofReal
                exact (SchwartzMap.continuous φ).norm.measurable
              rw [lintegral_mul_const _ h_meas]
    have h_fin :
        (∫⁻ p, ‖(fourierKernel (-p.1) p.2 * f p.2) * conj (φ p.1)‖ₑ ∂(volume.prod volume)) < ∞ := by
      have hf_fin : (∫⁻ ξ, ‖f ξ‖ₑ ∂volume) < ∞ := hf.hasFiniteIntegral
      have hφ_fin : (∫⁻ t, ‖φ t‖ₑ ∂volume) < ∞ := hφ_L1.hasFiniteIntegral
      -- Convert ‖·‖ₑ to ENNReal.ofReal ‖·‖
      -- Note: ‖x‖ₑ = (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ when ‖x‖ ≥ 0
      have hf_fin' : (∫⁻ ξ, ENNReal.ofReal ‖f ξ‖ ∂volume) < ∞ := by
        convert hf_fin using 2
        ext ξ
        simp [ENNReal.ofReal_coe_nnreal]
      have hφ_fin' : (∫⁻ t, ENNReal.ofReal ‖φ t‖ ∂volume) < ∞ := by
        convert hφ_fin using 2
        ext t
        simp [ENNReal.ofReal_coe_nnreal]
      have : (∫⁻ p, ENNReal.ofReal ‖φ p.1‖ * ENNReal.ofReal ‖f p.2‖ ∂(volume.prod volume)) < ∞ := by
        rw [h_prod_eq]
        exact ENNReal.mul_lt_top hφ_fin' hf_fin'
      simp only [h_point]
      exact this
    exact ⟨h_aesm, h_fin⟩

  -- Swap the order of integration (Fubini).
  have h_swap :=
    MeasureTheory.integral_integral_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (f := fun t ξ => (fourierKernel (-t) ξ * f ξ) * conj (φ t))
      h_prod_int

  -- Evaluate the inner (time-side) integral: it equals the conjugate Fourier transform.
  have h_inner : ∀ ξ : ℝ,
      ∫ t : ℝ, (fourierKernel (-t) ξ * f ξ) * conj (φ t) ∂volume
        = f ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) := by
    intro ξ
    -- Factor the constant `f ξ` out of the inner integral.
    have h_fac :=
      (MeasureTheory.integral_const_mul (μ := volume)
        (r := f ξ) (f := fun t : ℝ => fourierKernel (-t) ξ * conj (φ t)))
    -- Identify the remaining integral using conjugation.
    have h_conv :
        (fun t : ℝ => fourierKernel (-t) ξ * conj (φ t))
          = fun t : ℝ => conj (fourierKernel ξ t * φ t) := by
      funext t
      -- As functions of `t`, we have `fourierKernel (-t) ξ = conj (fourierKernel ξ t)`
      -- and `conj` distributes over multiplication.
      have hk : fourierKernel (-t) ξ = conj (fourierKernel ξ t) := by
        have hswap : fourierKernel (-t) ξ = fourierKernel (-ξ) t := by
          simp [fourierKernel, mul_comm, mul_left_comm, mul_assoc]
        simpa [fourierKernel_neg] using hswap
      simp [hk, map_mul, mul_comm, mul_left_comm, mul_assoc]
    have h_int_core :
        Integrable (fun t : ℝ => fourierKernel ξ t * φ t) := by
      simpa using integrable_fourierKernel_mul ξ hφ_L1
    have h_int_core_conj :
        Integrable (fun t : ℝ => fourierKernel (-t) ξ * conj (φ t)) := by
      -- Conjugation preserves integrability and matches the desired integrand.
      have h' := integrable_conj_of_integrable h_int_core
      simpa [h_conv]
        using h'
    -- Evaluate the inner `t`-integral explicitly via conjugation and the Fourier integral.
    have h_eval :
        ∫ t : ℝ, fourierKernel (-t) ξ * conj (φ t) ∂volume
          = conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) := by
      -- First, rewrite the integrand a.e. using `h_conv` and then apply `integral_congr_ae`.
      have h_ae :
          (fun t : ℝ => fourierKernel (-t) ξ * conj (φ t))
            =ᵐ[volume] (fun t : ℝ => conj (fourierKernel ξ t * φ t)) := by
        refine Filter.Eventually.of_forall ?_
        intro t
        -- Identify `fourierKernel (-t) ξ` with the conjugate of `fourierKernel ξ t`.
        have hk : fourierKernel (-t) ξ = conj (fourierKernel ξ t) := by
          -- Swap arguments using commutativity, then apply the `fourierKernel_neg` lemma.
          have hswap : fourierKernel (-t) ξ = fourierKernel (-ξ) t := by
            simp [fourierKernel, mul_comm, mul_left_comm, mul_assoc]
          simpa [fourierKernel_neg] using hswap
        -- Conclude by distributing conjugation over the product.
        calc
          fourierKernel (-t) ξ * conj (φ t)
              = conj (fourierKernel ξ t) * conj (φ t) := by
                    simp [hk]
          _ = conj (fourierKernel ξ t * φ t) := by
                    simp [map_mul, mul_comm, mul_left_comm, mul_assoc]
      calc
        ∫ t : ℝ, fourierKernel (-t) ξ * conj (φ t) ∂volume
            = ∫ t : ℝ, conj (fourierKernel ξ t * φ t) ∂volume :=
              (integral_congr_ae h_ae)
        _ = conj (∫ t : ℝ, fourierKernel ξ t * φ t ∂volume) := by
              simpa [eq_comm] using
                (integral_conj (μ := volume)
                  (f := fun t : ℝ => fourierKernel ξ t * φ t))
        _ = conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) := by
              simp [fourierIntegral]
    -- Conclude the claimed identity for the inner integral, adjusting multiplication order.
    simpa [h_eval, mul_comm, mul_left_comm, mul_assoc] using h_fac

  -- Combine all the pieces.
  have h_rhs :
      ∫ t : ℝ, ∫ ξ : ℝ,
          (fourierKernel (-t) ξ * f ξ) * conj (φ t) ∂volume ∂volume
        = ∫ ξ : ℝ, f ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume := by
    -- `h_swap` rewrites the double integral in the opposite order.
    -- Then evaluate the inner time-side integral using `h_inner`.
    simpa [h_inner] using h_swap

  -- Final identity by chaining the rewrites.
  simpa [h_lhs_rewrite] using h_rhs

end Frourio
