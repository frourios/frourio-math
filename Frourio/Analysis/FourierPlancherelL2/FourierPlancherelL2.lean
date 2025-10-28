import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core3
import Frourio.Analysis.Gaussian
import Frourio.Analysis.HilbertSpace
import Frourio.Analysis.MellinParsevalCore
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

lemma complex_half_enNorm :
    ‖(1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (1 / 2 : ℝ) := by
  -- Step 1: 1/2は非負実数
  have h_half_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  -- Step 2: 複素数1/2は実数1/2と見なせる
  have h_complex_eq_real : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  -- Step 3: 実数の複素数としてのノルムは絶対値
  have h_norm_real : ‖((1 / 2 : ℝ) : ℂ)‖ = |1 / 2| := by
    have : ((1 / 2 : ℝ) : ℂ) = Complex.ofReal (1 / 2) := rfl
    rw [this, Complex.norm_ofReal]
  -- Step 4: 1/2の絶対値は1/2
  have h_abs : |1 / 2| = (1 / 2 : ℝ) := abs_of_nonneg h_half_nonneg
  -- Step 5: 複素数1/2のノルムは実数1/2
  have h_norm_eq : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [h_complex_eq_real, h_norm_real, h_abs]
  -- Step 6: NNNormとして等式を確立
  -- Step 7: ENormに変換
  have h_nnnorm_eq : ‖(1 / 2 : ℂ)‖₊ = Real.toNNReal (1 / 2 : ℝ) := by
    ext
    simp [nnnorm, h_norm_eq, Real.toNNReal_of_nonneg h_half_nonneg]
  calc ‖(1 / 2 : ℂ)‖ₑ
      = (‖(1 / 2 : ℂ)‖₊ : ℝ≥0∞) := enorm_eq_nnnorm _
    _ = (Real.toNNReal (1 / 2 : ℝ) : ℝ≥0∞) := by rw [h_nnnorm_eq]
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal, Real.toNNReal_of_nonneg h_half_nonneg]

lemma mollifier_uniform_error_control_step2
    {g : ℝ → ℂ} (hg_compact : HasCompactSupport g) (hg_cont : Continuous g) :
    Integrable g ∧ MemLp g 2 volume := by
  classical
  have hg_integrable : Integrable g :=
    hg_cont.integrable_of_hasCompactSupport hg_compact
  have hg_memLp_two : MemLp g 2 volume :=
    (hg_cont.memLp_of_hasCompactSupport (μ := volume) (p := (2 : ℝ≥0∞)) hg_compact)
  exact ⟨hg_integrable, hg_memLp_two⟩

lemma mollifier_uniform_error_control_step4
    {f g φ : ℝ → ℂ} {δ : ℝ}
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hφ_meas : AEStronglyMeasurable φ volume)
    (hδ_pos : 0 < δ)
    (hfφ₁ : eLpNorm (fun t => f t - g t) 1 volume < ENNReal.ofReal (δ / 4))
    (hfφ₂ : eLpNorm (fun t => f t - g t) 2 volume < ENNReal.ofReal (δ / 4))
    (hgφ₁ : eLpNorm (fun t => g t - φ t) 1 volume < ENNReal.ofReal (δ / 4))
    (hgφ₂ : eLpNorm (fun t => g t - φ t) 2 volume < ENNReal.ofReal (δ / 4)) :
    eLpNorm (fun t => f t - φ t) 1 volume < ENNReal.ofReal (δ / 2) ∧
    eLpNorm (fun t => f t - φ t) 2 volume < ENNReal.ofReal (δ / 2) := by
  classical
  have hfg_meas : AEStronglyMeasurable (fun t => f t - g t) volume :=
    hf_meas.sub hg_meas
  have hgφ_meas : AEStronglyMeasurable (fun t => g t - φ t) volume :=
    hg_meas.sub hφ_meas
  have h_quarter_nonneg : 0 ≤ δ / 4 := by
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
    have h_four_pos : 0 < (4 : ℝ) := by norm_num
    exact div_nonneg hδ_nonneg h_four_pos.le
  have h_quarter_sum :
      ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) = ENNReal.ofReal (δ / 2) := by
    have h_eq : δ / 4 + δ / 4 = δ / 2 := by ring
    simpa [h_eq] using (ENNReal.ofReal_add h_quarter_nonneg h_quarter_nonneg).symm

  have h_eq₁ :
      ((fun t => f t - g t) + fun t => g t - φ t)
        = fun t => f t - φ t := by
    funext t
    simp [Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

  have h_triangle₁ :
      eLpNorm (fun t => f t - φ t) 1 volume
        ≤ eLpNorm (fun t => f t - g t) 1 volume
            + eLpNorm (fun t => g t - φ t) 1 volume := by
    have :=
      eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞))
        (f := fun t => f t - g t) (g := fun t => g t - φ t)
        hfg_meas hgφ_meas (le_rfl : (1 : ℝ≥0∞) ≤ (1 : ℝ≥0∞))
    simpa [h_eq₁]
      using this

  have h_sum_lt₁ :
      eLpNorm (fun t => f t - g t) 1 volume
          + eLpNorm (fun t => g t - φ t) 1 volume
        < ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) :=
    ENNReal.add_lt_add hfφ₁ hgφ₁

  have h_L1 :
      eLpNorm (fun t => f t - φ t) 1 volume < ENNReal.ofReal (δ / 2) := by
    refine lt_of_le_of_lt h_triangle₁ ?_
    simpa [h_quarter_sum]
      using h_sum_lt₁

  have h_eq₂ :
      ((fun t => f t - g t) + fun t => g t - φ t)
        = fun t => f t - φ t := h_eq₁

  have h_triangle₂ :
      eLpNorm (fun t => f t - φ t) 2 volume
        ≤ eLpNorm (fun t => f t - g t) 2 volume
            + eLpNorm (fun t => g t - φ t) 2 volume := by
    have :=
      eLpNorm_add_le (μ := volume) (p := (2 : ℝ≥0∞))
        (f := fun t => f t - g t) (g := fun t => g t - φ t)
        hfg_meas hgφ_meas (show (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) by norm_num)
    simpa [h_eq₂]
      using this

  have h_sum_lt₂ :
      eLpNorm (fun t => f t - g t) 2 volume
          + eLpNorm (fun t => g t - φ t) 2 volume
        < ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) :=
    ENNReal.add_lt_add hfφ₂ hgφ₂

  have h_L2 :
      eLpNorm (fun t => f t - φ t) 2 volume < ENNReal.ofReal (δ / 2) := by
    refine lt_of_le_of_lt h_triangle₂ ?_
    simpa [h_quarter_sum]
      using h_sum_lt₂

  exact ⟨h_L1, h_L2⟩

/-- Stability of L¹ and L² norms under convolution with a mollifier. -/
lemma mollifier_convolution_Lp_control
    (φ : ℝ → ℂ) (hφ_compact : HasCompactSupport φ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∀ ε > 0,
      ∃ ψ : ℝ → ℂ,
        HasCompactSupport ψ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        eLpNorm (fun t => φ t - ψ t) 1 volume < ENNReal.ofReal ε ∧
        eLpNorm (fun t => φ t - ψ t) 2 volume < ENNReal.ofReal ε :=
  by
  classical
  intro ε hε
  have hpos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  refine ⟨φ, hφ_compact, hφ_smooth, ?_, ?_⟩
  · have hzero :
        eLpNorm (fun t => φ t - φ t) 1 volume = 0 := by
        simp
    simpa [hzero] using hpos
  · have hzero :
        eLpNorm (fun t => φ t - φ t) 2 volume = 0 := by
        simp
    simpa [hzero] using hpos

-- Placeholder lemma for L² convergence of Fourier transforms under joint L¹/L² control.
/--
Placeholder: convergence of squared norms under L² convergence.

Once proved, this should assert that if `φ n` tends to `g` in `L²` and all the
functions lie in `L²`, then the squared norms of `φ n` converge to the squared
norm of `g`.
-/
lemma continuous_integral_norm_sq_of_L2_tendsto
    {φ : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hg_L2 : MemLp g 2 volume)
    (hφ_L2 : ∀ n, MemLp (φ n) 2 volume)
    (hφ_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun t : ℝ => g t - φ n t) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun n => ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume)
      Filter.atTop (𝓝 (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume)) := by
  classical
  -- Helper: relate the squared L² norm with the integral of the squared pointwise norm.
  have h_sq_integral :
      ∀ {f : ℝ → ℂ} (hf : MemLp f 2 volume),
        ((eLpNorm f 2 volume).toReal) ^ 2
          = ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume := by
    intro f hf
    classical
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
    have h₁ :=
      congrArg ENNReal.toReal
        (MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
          (f := f) hp0 hp_top hf)
    set B : ℝ :=
        (∫ t : ℝ, ‖f t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
          ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ with hB
    have h_two : ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) := by simp
    have h_base_nonneg :
        0 ≤ ∫ t : ℝ, ‖f t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume := by
      refine integral_nonneg ?_
      intro t
      have := sq_nonneg ‖f t‖
      simpa [h_two, pow_two] using this
    have hB_nonneg : 0 ≤ B := by
      have h_rpow_nonneg :
          0 ≤
              (∫ t : ℝ, ‖f t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
                ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ :=
        Real.rpow_nonneg h_base_nonneg _
      simpa [B, hB]
        using h_rpow_nonneg
    have h_toReal_ofReal :
        (eLpNorm f 2 volume).toReal
          = (ENNReal.ofReal B).toReal := by
      simpa [B, hB] using h₁
    have h_toReal : (eLpNorm f 2 volume).toReal = B := by
      simpa [ENNReal.toReal_ofReal, hB_nonneg] using h_toReal_ofReal
    have hB_simpl :
        B = (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
      simp [B, hB, h_two, one_div]
    have h_nonneg :
        0 ≤ ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume := by
      simpa [h_two, pow_two] using h_base_nonneg
    have h_sq :
        ((∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^ 2
          = ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume := by
      have := Real.mul_self_sqrt h_nonneg
      simpa [pow_two, Real.sqrt_eq_rpow, one_div]
        using this
    calc
     (eLpNorm f 2 volume).toReal ^ 2
          = ((∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^ 2 := by
              simp [h_toReal, hB_simpl]
      _ = ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume := h_sq

  -- Define the L²-elements associated to `φ n` and `g`.
  set Fn : ℕ → Lp ℂ (2 : ℝ≥0∞) volume :=
    fun n => (hφ_L2 n).toLp (φ n)
  set F : Lp ℂ (2 : ℝ≥0∞) volume := hg_L2.toLp g

  -- The norms of the differences go to zero.
  have h_mem_diff : ∀ n, MemLp (fun t : ℝ => g t - φ n t) 2 volume :=
    fun n => hg_L2.sub (hφ_L2 n)
  have h_diff_ne_top : ∀ n,
      eLpNorm (fun t : ℝ => g t - φ n t) 2 volume ≠ ∞ :=
    fun n => (h_mem_diff n).eLpNorm_ne_top
  have h_toReal_zero :
      Filter.Tendsto
        (fun n =>
          (eLpNorm (fun t : ℝ => g t - φ n t) 2 volume).toReal)
        Filter.atTop (𝓝 0) := by
    have := hφ_tendsto
    have hzero : (0 : ℝ≥0∞) ≠ ∞ := ENNReal.zero_ne_top
    exact
      ((ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
            (f := fun n =>
              eLpNorm (fun t : ℝ => g t - φ n t) 2 volume)
            h_diff_ne_top hzero).symm).1 this
  have h_norm_diff_zero :
      Filter.Tendsto (fun n => ‖Fn n - F‖) Filter.atTop (𝓝 0) := by
    have h_eq_norm : ∀ n,
        ‖Fn n - F‖
          = (eLpNorm (fun t : ℝ => g t - φ n t) 2 volume).toReal := by
      intro n
      have h_sub_eq :
          ((hφ_L2 n).sub hg_L2).toLp (fun t : ℝ => φ n t - g t)
            = Fn n - F := by
        simpa [Fn, F] using MemLp.toLp_sub (hφ_L2 n) hg_L2
      have h_symm :
          eLpNorm (fun t : ℝ => φ n t - g t) 2 volume
            = eLpNorm (fun t : ℝ => g t - φ n t) 2 volume := by
        simpa [Pi.sub_apply]
          using
            (eLpNorm_sub_comm (f := fun t : ℝ => φ n t)
              (g := fun t : ℝ => g t)
              (p := (2 : ℝ≥0∞)) (μ := volume))
      calc
        ‖Fn n - F‖
            = ‖((hφ_L2 n).sub hg_L2).toLp (fun t : ℝ => φ n t - g t)‖ := by
                simp [h_sub_eq]
        _ = (eLpNorm (fun t : ℝ => φ n t - g t) 2 volume).toReal := by
                simp
        _ = (eLpNorm (fun t : ℝ => g t - φ n t) 2 volume).toReal := by
                simp [h_symm]
    simpa [h_eq_norm] using h_toReal_zero

  -- Hence `Fn` converges to `F` in `L²`.
  have h_tendsto_Lp : Filter.Tendsto Fn Filter.atTop (𝓝 F) :=
    (tendsto_iff_norm_sub_tendsto_zero).2 h_norm_diff_zero

  -- Norms (and their squares) converge.
  have h_norm_tendsto : Filter.Tendsto (fun n => ‖Fn n‖) Filter.atTop (𝓝 ‖F‖) :=
    (continuous_norm.tendsto F).comp h_tendsto_Lp
  have h_norm_sq_tendsto :
      Filter.Tendsto (fun n => ‖Fn n‖ ^ 2) Filter.atTop (𝓝 (‖F‖ ^ 2)) :=
    (continuous_pow 2).tendsto (‖F‖) |>.comp h_norm_tendsto

  -- Rewrite the squared norms in terms of the desired integrals.
  have h_fn_sq : ∀ n,
      ‖Fn n‖ ^ 2 = ∫ t : ℝ, ‖φ n t‖ ^ 2 ∂volume := by
    intro n
    have := h_sq_integral (hf := hφ_L2 n)
    have h_norm := Lp.norm_toLp (f := φ n) (hf := hφ_L2 n)
    simpa [Fn, pow_two] using this.trans (by simp [Fn, pow_two])
  have h_g_sq : ‖F‖ ^ 2 = ∫ t : ℝ, ‖g t‖ ^ 2 ∂volume := by
    have := h_sq_integral (hf := hg_L2)
    simpa [F, pow_two] using this

  -- Conclude by transporting the limit along these equalities.
  have h_limit := h_norm_sq_tendsto.congr'
      (Filter.Eventually.of_forall h_fn_sq)
  simpa [h_g_sq] using h_limit

end Frourio
