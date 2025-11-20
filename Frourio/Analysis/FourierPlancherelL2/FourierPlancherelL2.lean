import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core5
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

-- Gaussian L² membership via measure scaling
lemma gaussian_memLp_two (R : ℝ) (hR : 0 < R) :
    MemLp (fun ξ : ℝ => (Real.exp (-(Real.pi) * (ξ / R)^2))) 2 volume := by
  classical
  -- Reduce to the standard real Gaussian `exp (-(a) * ξ²)` with `a = π / R²`.
  have hR2_pos : 0 < R ^ 2 := sq_pos_of_pos hR
  have ha : 0 < Real.pi / R ^ 2 := div_pos Real.pi_pos hR2_pos
  -- Base L² membership for the rescaled Gaussian.
  have h_base := gaussian_memLp (Real.pi / R ^ 2) ha
  -- Prove the functions are equal
  have : (fun ξ : ℝ => Real.exp (-(Real.pi) * (ξ / R)^2))
       = (fun ξ : ℝ => Real.exp (-(Real.pi / R ^ 2) * ξ ^ 2)) := by
    ext ξ
    congr 1
    rw [div_pow]
    ring
  rw [this]
  exact h_base

/-- Integrability of Gaussian cutoff times an L² function.

If `w ∈ L²` and `R > 0`, then `ξ ↦ exp(-π (ξ/R)^2) · w(ξ)` is integrable. -/
lemma integrable_gaussian_mul_L2
    {w : ℝ → ℂ} (hw : MemLp w 2 volume) (R : ℝ) (hR : 0 < R) :
    Integrable (fun ξ : ℝ => (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ) * w ξ) := by
  classical
  -- Put the Gaussian into L² and apply the generic Lᵖ×Lᵠ → L¹ product lemma
  have hg_L2 : MemLp (fun ξ : ℝ => (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ)) 2 volume := by
    -- `gaussian_memLp_two` is stated for ℝ-valued Gaussians; coerce to ℂ using ofReal
    have hg_real :
        MemLp (fun ξ : ℝ => Real.exp (-(Real.pi) * (ξ / R)^2)) 2 volume :=
      gaussian_memLp_two R hR
    -- The coercion ℝ → ℂ preserves L² membership
    exact hg_real.ofReal
  -- Apply the generic product integrability lemma with p = q = 2.
  -- This is Hölder (Cauchy–Schwarz) in `Lp`.
  have :=
    MeasureTheory.MemLp.integrable_mul
      (μ := volume) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (f := fun ξ : ℝ => (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ))
      (g := w) hg_L2 hw
  simpa [Pi.mul_apply] using this

/-- Dominated convergence for Gaussian cutoffs in the Fourier-side pairing.

Let `w ∈ L²` and `φ` Schwartz. Then, with Gaussian cutoffs `GR(ξ) = exp(-π (ξ/R)^2)`,
the integrals `∫ GR(ξ) w(ξ) · conj(F[φ](ξ)) dξ` converge to
`∫ w(ξ) · conj(F[φ](ξ)) dξ` as `R → ∞`. -/
lemma gaussian_pairing_tendsto
    {w : ℝ → ℂ} (hw : MemLp w 2 volume) (φ : SchwartzMap ℝ ℂ) :
    Filter.Tendsto (fun R : ℝ =>
        ∫ ξ : ℝ, (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ) * w ξ
              * (conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ)) ∂volume)
      (Filter.atTop)
      (𝓝 (∫ ξ : ℝ, (w ξ) * (conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ)) ∂volume)) := by
  classical
  -- Notation: Fourier transform of φ.
  set Fφ : ℝ → ℂ := fun ξ => Frourio.fourierIntegral (fun t : ℝ => φ t) ξ

  -- R–dependent integrand and its limit as R → ∞.
  set I : ℝ → ℝ → ℂ :=
    fun R ξ => (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ) * w ξ * conj (Fφ ξ)
  set Ilim : ℝ → ℂ := fun ξ => w ξ * conj (Fφ ξ)

  -- 1. Pointwise convergence of the Gaussian cutoff for almost every ξ.
  have h_pointwise :
      ∀ᵐ ξ : ℝ,
        Filter.Tendsto (fun R : ℝ => I R ξ) Filter.atTop (𝓝 (Ilim ξ)) := by
    -- In fact, the convergence holds for every ξ, so we upgrade a pointwise
    -- statement to an a.e. one.
    refine Filter.Eventually.of_forall ?_
    intro ξ
    -- Gaussian factor converges to 1 as R → ∞.
    have h_gauss_real :
        Filter.Tendsto (fun R : ℝ =>
            Real.exp (-(Real.pi) * (ξ / R)^2)) Filter.atTop (𝓝 (1 : ℝ)) := by
      -- Continuity of x ↦ exp(-π x²)
      have h_cont :
          Continuous fun x : ℝ => Real.exp (-(Real.pi) * (x * x)) :=
        Real.continuous_exp.comp (continuous_const.mul (continuous_id.mul continuous_id))
      -- x ↦ exp(-π x²) tends to 1 as x → 0
      have h0 : Filter.Tendsto
          (fun x : ℝ => Real.exp (-(Real.pi) * (x * x))) (𝓝 (0 : ℝ))
          (𝓝 (Real.exp (-(Real.pi) * 0 * 0))) := by
        simpa using h_cont.tendsto 0
      -- R ↦ ξ / R tends to 0 as R → ∞
      have h_div : Filter.Tendsto (fun R : ℝ => ξ / R)
          Filter.atTop (𝓝 (0 : ℝ)) := by
        have h_inv : Filter.Tendsto (fun R : ℝ => R⁻¹)
            Filter.atTop (𝓝 (0 : ℝ)) :=
          tendsto_inv_atTop_zero
        have h_mul :=
          (tendsto_const_nhds.mul h_inv :
            Filter.Tendsto (fun R : ℝ => ξ * R⁻¹) Filter.atTop (𝓝 (ξ * 0)))
        simpa [div_eq_mul_inv] using h_mul
      -- Compose the two limits: x = ξ / R → 0
      have h_comp := h0.comp h_div
      -- Simplify the composed expression and the limit value.
      simpa [Function.comp, pow_two] using h_comp
    -- Upgrade to ℂ-valued Gaussian factor via ofReal.
    have h_gauss :
        Filter.Tendsto (fun R : ℝ =>
            (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ))
          Filter.atTop (𝓝 (1 : ℂ)) := by
      have h_ofReal :
          Filter.Tendsto (fun x : ℝ => (x : ℂ))
            (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _)
      exact h_ofReal.comp h_gauss_real
    -- Multiply by the constant factors w ξ and conj (Fφ ξ).
    have h_const1 :
        Filter.Tendsto (fun _ : ℝ => w ξ)
          Filter.atTop (𝓝 (w ξ)) :=
      tendsto_const_nhds
    have h_const2 :
        Filter.Tendsto (fun _ : ℝ => conj (Fφ ξ))
          Filter.atTop (𝓝 (conj (Fφ ξ))) :=
      tendsto_const_nhds
    have h_prod :
        Filter.Tendsto (fun R : ℝ =>
            (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ) * w ξ * conj (Fφ ξ))
          Filter.atTop
          (𝓝 ((1 : ℂ) * w ξ * conj (Fφ ξ))) :=
      (h_gauss.mul h_const1).mul h_const2
    simpa [I, Ilim] using h_prod

  -- 2. A uniform L¹–dominating function independent of R.
  have h_dominated :
      ∃ g : ℝ → ℝ,
        Integrable g ∧
        ∀ R : ℝ, ∀ᵐ ξ : ℝ, ‖I R ξ‖ ≤ g ξ := by
    -- Put Fφ in L².
    have hFφ_L2 : MemLp Fφ 2 volume := by
      simpa [Fφ] using fourierIntegral_memLp_of_schwartz φ

    -- The product w · Fφ belongs to L¹ by Hölder/Cauchy–Schwarz.
    have h_prod_int :
        Integrable (fun ξ : ℝ => w ξ * Fφ ξ) := by
      have := MeasureTheory.MemLp.integrable_mul
        (μ := volume) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (f := w) (g := Fφ) hw hFφ_L2
      simpa [Pi.mul_apply] using this

    -- Dominating function g(ξ) = ‖w ξ * Fφ ξ‖.
    let g : ℝ → ℝ := fun ξ => ‖w ξ * Fφ ξ‖
    have hg_int : Integrable g := by
      simpa [g] using h_prod_int.norm

    refine ⟨g, hg_int, ?_⟩
    intro R
    -- Pointwise bound: ‖I R ξ‖ ≤ g ξ for every ξ.
    refine Filter.Eventually.of_forall ?_
    intro ξ

    -- The Gaussian factor has norm ≤ 1 for all R, ξ.
    have h_norm_gauss_le_one :
        ‖(Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ)‖ ≤ 1 := by
      have h_nonpos : -(Real.pi) * (ξ / R) ^ 2 ≤ 0 := by
        have h1 : -Real.pi ≤ (0 : ℝ) :=
          neg_nonpos.mpr (le_of_lt Real.pi_pos)
        have h2 : (0 : ℝ) ≤ (ξ / R) ^ 2 := sq_nonneg _
        exact mul_nonpos_of_nonpos_of_nonneg h1 h2
      have h_le_one : Real.exp (-(Real.pi) * (ξ / R) ^ 2) ≤ 1 := by
        -- `exp x ≤ 1` whenever `x ≤ 0`
        have := (Real.exp_le_one_iff).2 h_nonpos
        simpa using this
      -- Transfer the inequality to ℂ via the norm.
      rw [Complex.norm_real]
      simpa [abs_of_nonneg (Real.exp_nonneg _)] using h_le_one

    -- Norm of the product with the conjugate equals the product without conjugate.
    have h_prod_norm_eq :
        ‖w ξ * conj (Fφ ξ)‖ = ‖w ξ * Fφ ξ‖ := by
      calc
        ‖w ξ * conj (Fφ ξ)‖
            = ‖w ξ‖ * ‖conj (Fφ ξ)‖ := (norm_mul _ _)
        _ = ‖w ξ‖ * ‖Fφ ξ‖ := by simp [norm_conj]
        _ = ‖w ξ * Fφ ξ‖ := by simp [norm_mul]

    -- Combine the bounds.
    have h_bound_pointwise :
        ‖I R ξ‖ ≤ g ξ := by
      -- Group the product inside the norm as (Gaussian) * (w ξ * conj(Fφ ξ)).
      have h_norm_eq :
          ‖I R ξ‖
            = ‖(Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)
                * (w ξ * conj (Fφ ξ))‖ := by
        simp [I, mul_assoc]
      calc
        ‖I R ξ‖
            = ‖(Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)
                * (w ξ * conj (Fφ ξ))‖ := h_norm_eq
        _ = ‖(Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)‖
              * ‖w ξ * conj (Fφ ξ)‖ := by
                simp [mul_comm, mul_left_comm, mul_assoc]
        _ ≤ 1 * ‖w ξ * conj (Fφ ξ)‖ := by
              have := h_norm_gauss_le_one
              exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = ‖w ξ * conj (Fφ ξ)‖ := by ring
        _ = ‖w ξ * Fφ ξ‖ := h_prod_norm_eq
        _ = g ξ := rfl

    exact h_bound_pointwise

  -- Fix a dominating function `g` and its properties for later use.
  obtain ⟨g, hg_int, h_bound_all⟩ := h_dominated

  -- Basic measurability facts used below.
  have h_meas_w : AEStronglyMeasurable w volume :=
    hw.aestronglyMeasurable
  have hFφ_L2 : MemLp Fφ 2 volume := by
    simpa [Fφ] using fourierIntegral_memLp_of_schwartz φ
  have h_meas_Fφ : AEStronglyMeasurable Fφ volume :=
    hFφ_L2.aestronglyMeasurable

  -- Gaussian factor is a.e. strongly measurable for each radius.
  have h_meas_gauss :
      ∀ R : ℝ,
        AEStronglyMeasurable
          (fun ξ : ℝ =>
            (Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)) volume := by
    intro R
    -- Continuity of ξ ↦ Real.exp (-(π) * (ξ / R)^2)
    have h_cont_div : Continuous fun ξ : ℝ => ξ / R := by
      have h_eq :
          (fun ξ : ℝ => ξ / R) = fun ξ : ℝ => ξ * (1 / R) := by
        funext ξ; simp [div_eq_mul_inv]
      simpa [h_eq] using
        (continuous_id.mul continuous_const :
          Continuous fun ξ : ℝ => ξ * (1 / R))
    have h_cont_real :
        Continuous fun ξ : ℝ =>
          Real.exp (-(Real.pi) * (ξ / R) ^ 2) :=
      Real.continuous_exp.comp
        (continuous_const.mul (h_cont_div.pow 2))
    -- Lift to ℂ via ofReal.
    have h_cont_complex :
        Continuous fun ξ : ℝ =>
          (Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ) :=
      Complex.continuous_ofReal.comp h_cont_real
    exact h_cont_complex.aestronglyMeasurable

  -- 3. Integrability of each cutoff integrand.
  have h_integrable_R :
      ∀ R : ℝ, Integrable (fun ξ : ℝ => I R ξ) := by
    -- Use `integrable_gaussian_mul_L2` to put the Gaussian·w factor in L¹ and
    -- then multiply by the fixed L² function Fφ, again via an L²×L² → L¹ bound.
    -- The special case R ≤ 0 can be handled separately or by restricting to
    -- large R in the atTop filter.
    intro R
    -- Measurability of the integrand I R.
    have h_meas_conjF :
        AEStronglyMeasurable (fun ξ : ℝ => conj (Fφ ξ)) volume := by
      -- conj is continuous, so it preserves AE strong measurability
      have h_conj_cont : Continuous (conj : ℂ → ℂ) := continuous_star
      exact h_conj_cont.comp_aestronglyMeasurable h_meas_Fφ
    have h_meas_I :
        AEStronglyMeasurable (fun ξ : ℝ => I R ξ) volume := by
      -- I R ξ = (Gaussian R ξ) * w ξ * conj (Fφ ξ)
      have h_gauss := h_meas_gauss R
      exact ((h_gauss.mul h_meas_w).mul h_meas_conjF)
    -- AE bound by the fixed integrable majorant g.
    have h_bound_R : ∀ᵐ ξ : ℝ, ‖I R ξ‖ ≤ g ξ := h_bound_all R
    -- Apply the standard domination lemma.
    exact Integrable.mono' hg_int h_meas_I h_bound_R

  -- 4. Integrability of the limit integrand.
  have h_integrable_lim : Integrable Ilim := by
    -- This is the product of w ∈ L² and Fφ ∈ L²; use the standard L²×L² → L¹ lemma.
    -- Step 1: use Hölder/Cauchy–Schwarz to put `w * Fφ` in L¹.
    have hFφ_L2 : MemLp Fφ 2 volume := by
      simpa [Fφ] using fourierIntegral_memLp_of_schwartz φ
    have h_int_base :
        Integrable (fun ξ : ℝ => w ξ * Fφ ξ) := by
      have := MeasureTheory.MemLp.integrable_mul
        (μ := volume) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (f := w) (g := Fφ) hw hFφ_L2
      simpa [Pi.mul_apply] using this

    -- Step 2: `Ilim = w * conj Fφ` has the same pointwise norm as `w * Fφ`.
    have h_meas_Ilim :
        AEStronglyMeasurable Ilim volume := by
      -- Ilim ξ = w ξ * conj (Fφ ξ)
      have h_meas_conjF :
          AEStronglyMeasurable (fun ξ : ℝ => conj (Fφ ξ)) volume := by
        have h_conj_cont : Continuous (conj : ℂ → ℂ) := continuous_star
        exact h_conj_cont.comp_aestronglyMeasurable h_meas_Fφ
      simpa [Ilim] using h_meas_w.mul h_meas_conjF

    have h_bound_Ilim :
        ∀ᵐ ξ : ℝ, ‖Ilim ξ‖ ≤ ‖w ξ * Fφ ξ‖ := by
      refine Filter.Eventually.of_forall ?_
      intro ξ
      have h_eq_norm :
          ‖w ξ * conj (Fφ ξ)‖ = ‖w ξ * Fφ ξ‖ := by
        calc
          ‖w ξ * conj (Fφ ξ)‖
              = ‖w ξ‖ * ‖conj (Fφ ξ)‖ := by simp [norm_mul]
          _ = ‖w ξ‖ * ‖Fφ ξ‖ := by simp [norm_conj]
          _ = ‖w ξ * Fφ ξ‖ := by simp [norm_mul]
      simp [Ilim, h_eq_norm]

    -- Step 3: conclude integrability of Ilim by domination.
    have h_int_norm : Integrable (fun ξ : ℝ => ‖w ξ * Fφ ξ‖) :=
      h_int_base.norm
    exact Integrable.mono' h_int_norm h_meas_Ilim h_bound_Ilim

  have h_tendsto :
      Filter.Tendsto (fun R : ℝ => ∫ ξ : ℝ, I R ξ ∂volume)
        Filter.atTop (𝓝 (∫ ξ : ℝ, Ilim ξ ∂volume)) := by
    -- Measurability of each integrand `I R`.
    have h_meas_I :
        ∀ R : ℝ,
          AEStronglyMeasurable (fun ξ : ℝ => I R ξ) volume := by
      intro R
      -- Already established via `h_integrable_R`.
      exact (h_integrable_R R).aestronglyMeasurable

    -- Apply the ℝ-parameter dominated convergence lemma.
    exact
      Frourio.MeasureTheory.tendsto_integral_of_dominated_convergence_atTop_real
        (f := fun R ξ => I R ξ)
        (flim := Ilim)
        (g := g)
        h_meas_I
        hg_int
        h_bound_all
        h_pointwise
  -- Rewrite in terms of the original expressions.
  simpa [I, Ilim, Fφ] using h_tendsto

lemma gaussian_frequency_cutoff_tendsto_L2
    {w : ℝ → ℂ} (hw : MemLp w 2 volume) :
    Filter.Tendsto (fun R : ℝ =>
        eLpNorm (fun ξ : ℝ =>
          (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ) * w ξ - w ξ) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  -- Notation: Gaussian cutoff on the frequency side.
  set GR : ℝ → ℝ → ℂ :=
    fun R ξ => (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ)

  -- 1. Pointwise convergence of the Gaussian factor to 1 for each frequency ξ.
  have h_pointwise_gauss :
      ∀ ξ : ℝ,
        Filter.Tendsto (fun R : ℝ => GR R ξ) Filter.atTop (𝓝 (1 : ℂ)) := by
    intro ξ
    -- Real-valued convergence: `exp (-(π) * (ξ/R)²) → 1` as `R → ∞`.
    have h_gauss_real :
        Filter.Tendsto (fun R : ℝ =>
            Real.exp (-(Real.pi) * (ξ / R) ^ 2)) Filter.atTop (𝓝 (1 : ℝ)) := by
      -- Continuity of `x ↦ exp (-(π) * x²)`.
      have h_cont :
          Continuous fun x : ℝ => Real.exp (-(Real.pi) * (x * x)) :=
        Real.continuous_exp.comp
          (continuous_const.mul (continuous_id.mul continuous_id))
      -- `x ↦ exp (-(π) * x²)` tends to `exp 0 = 1` as `x → 0`.
      have h0 : Filter.Tendsto
          (fun x : ℝ => Real.exp (-(Real.pi) * (x * x))) (𝓝 (0 : ℝ))
          (𝓝 (Real.exp (-(Real.pi) * 0 * 0))) := by
        simpa using h_cont.tendsto 0
      -- `R ↦ ξ / R` tends to `0` as `R → ∞`.
      have h_div : Filter.Tendsto (fun R : ℝ => ξ / R)
          Filter.atTop (𝓝 (0 : ℝ)) := by
        have h_inv : Filter.Tendsto (fun R : ℝ => R⁻¹)
            Filter.atTop (𝓝 (0 : ℝ)) :=
          tendsto_inv_atTop_zero
        have h_mul :
            Filter.Tendsto (fun R : ℝ => ξ * R⁻¹)
              Filter.atTop (𝓝 (ξ * 0)) :=
          (tendsto_const_nhds.mul h_inv)
        simpa [div_eq_mul_inv] using h_mul
      -- Compose the limits.
      have h_comp := h0.comp h_div
      simpa [Function.comp, pow_two] using h_comp
    -- Lift to ℂ via `ofReal`.
    have h_ofReal :
        Filter.Tendsto (fun x : ℝ => (x : ℂ))
          (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _)
    exact h_ofReal.comp h_gauss_real

  -- 2. Pointwise convergence of the cutoff–modified function to `w` in ℂ for each ξ.
  have h_pointwise_w :
      ∀ ξ : ℝ,
        Filter.Tendsto (fun R : ℝ => GR R ξ * w ξ) Filter.atTop (𝓝 (w ξ)) := by
    intro ξ
    -- Multiply the Gaussian convergence by the fixed factor `w ξ`.
    -- Concretely: GR R ξ → 1 and hence GR R ξ * w ξ → 1 * w ξ = w ξ.
    have h_mul :
        Filter.Tendsto (fun R : ℝ => (w ξ) * GR R ξ)
          Filter.atTop (𝓝 ((w ξ) * (1 : ℂ))) :=
      (tendsto_const_nhds.mul (h_pointwise_gauss ξ))
    simpa [mul_comm] using h_mul

  -- 3. Uniform L²–bound for the cutoff–modified functions.
  -- Conceptually: use that ‖GR R ξ‖ ≤ 1 for all R, ξ, so
  --   ‖GR R · w‖₂ ≤ ‖w‖₂,
  -- and the L² norm of the difference is controlled by a dominated convergence
  -- argument on the integrand ‖GR R ξ * w ξ - w ξ‖².
  have h_L2_uniform_bound :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ R : ℝ,
          (eLpNorm (fun ξ : ℝ => GR R ξ * w ξ) 2 volume) ≤ (ENNReal.ofReal C) := by
    -- Choose `C = (eLpNorm w 2 volume).toReal` and use the pointwise bound
    -- ‖GR R ξ‖ ≤ 1 together with the monotonicity of the L² norm.
    -- This is a standard estimate; we leave the details to the core development.
    classical
    -- Define the global L² bound in terms of the L² norm of `w`.
    let C : ℝ := (eLpNorm (fun ξ : ℝ => w ξ) 2 volume).toReal
    have hC_nonneg : 0 ≤ C := by
      have h := ENNReal.toReal_nonneg
        (a := eLpNorm (fun ξ : ℝ => w ξ) 2 volume)
      simp [C]
    refine ⟨C, hC_nonneg, ?_⟩
    intro R
    -- Step 1: pointwise control `‖GR R ξ * w ξ‖ ≤ ‖w ξ‖` via `‖GR R ξ‖ ≤ 1`.
    have h_pointwise_le :
        ∀ ξ : ℝ, ‖GR R ξ * w ξ‖ ≤ ‖w ξ‖ := by
      intro ξ
      -- Bound the Gaussian factor in norm by 1.
      have h_norm_gauss_le_one :
          ‖GR R ξ‖ ≤ 1 := by
        -- GR R ξ = exp (-(π) * (ξ/R)²) with real argument ≤ 0.
        have h_nonpos :
            -(Real.pi) * (ξ / R) ^ 2 ≤ 0 := by
          have h1 : -Real.pi ≤ (0 : ℝ) :=
            neg_nonpos.mpr (le_of_lt Real.pi_pos)
          have h2 : (0 : ℝ) ≤ (ξ / R) ^ 2 := sq_nonneg _
          exact mul_nonpos_of_nonpos_of_nonneg h1 h2
        have h_le_one :
            Real.exp (-(Real.pi) * (ξ / R) ^ 2) ≤ 1 := by
          -- `exp x ≤ 1` whenever `x ≤ 0`.
          have := (Real.exp_le_one_iff).2 h_nonpos
          simpa using this
        -- Transfer the bound to ℂ via the norm.
        have h_GR_def : (GR R ξ) = (Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ) := rfl
        have h_nonneg_exp :
            0 ≤ Real.exp (-(Real.pi) * (ξ / R) ^ 2) :=
          Real.exp_nonneg _
        -- For a nonnegative real r, ‖(r : ℂ)‖ = r
        have h_norm_real :
            ‖(Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)‖
              = Real.exp (-(Real.pi) * (ξ / R) ^ 2) := by
          rw [Complex.norm_real]
          exact abs_of_nonneg h_nonneg_exp
        -- Combine the pieces.
        have :
            ‖GR R ξ‖
              = Real.exp (-(Real.pi) * (ξ / R) ^ 2) := by
          rw [h_GR_def]
          exact h_norm_real
        have hfinal :
            ‖GR R ξ‖ ≤ 1 := by
          simpa [this] using h_le_one
        exact hfinal
      -- Use the multiplicative property of the norm together with the bound on ‖GR R ξ‖.
      have hmul :
          ‖GR R ξ * w ξ‖
            = ‖GR R ξ‖ * ‖w ξ‖ := by
        simp [norm_mul]  -- `norm_mul` in ℂ
      calc
        ‖GR R ξ * w ξ‖
            = ‖GR R ξ‖ * ‖w ξ‖ := hmul
        _ ≤ 1 * ‖w ξ‖ := by
              have := mul_le_mul_of_nonneg_right
                h_norm_gauss_le_one (norm_nonneg (w ξ))
              simpa [one_mul] using this
        _ = ‖w ξ‖ := by
              simp [one_mul]

    -- Step 2: upgrade the pointwise bound to an L² bound on the entire function
    -- using monotonicity of `eLpNorm`.
    have h_L2_le :
        eLpNorm (fun ξ : ℝ => GR R ξ * w ξ) 2 volume
          ≤ eLpNorm (fun ξ : ℝ => w ξ) 2 volume := by
      -- Apply `eLpNorm_mono` to the pointwise inequality `h_pointwise_le`.
      refine eLpNorm_mono ?_
      intro ξ
      exact h_pointwise_le ξ

    -- Step 3: rewrite `‖w‖₂` as `ENNReal.ofReal C` using the definition of `C`
    -- and the finiteness provided by `hw`.
    -- The L² norm of `w` is finite since `w ∈ L²`.
    have hw_fin : eLpNorm (fun ξ : ℝ => w ξ) 2 volume < ∞ := hw.2
    have h_ne_top :
        eLpNorm (fun ξ : ℝ => w ξ) 2 volume ≠ ∞ :=
      ne_of_lt hw_fin
    have h_eLp_eq :
        ENNReal.ofReal C
          = eLpNorm (fun ξ : ℝ => w ξ) 2 volume := by
      -- For finite `a`, `ENNReal.ofReal a.toReal = a`.
      simpa [C] using (ENNReal.ofReal_toReal h_ne_top)
    -- Combine the L² inequality with the identification of `C`.
    have h_bound_R :
        eLpNorm (fun ξ : ℝ => GR R ξ * w ξ) 2 volume
          ≤ ENNReal.ofReal C := by
      simpa [h_eLp_eq] using h_L2_le
    exact h_bound_R

  -- 4. L² dominated convergence for the error term.
  -- Write the L² error as the eLpNorm of the difference and identify a dominating
  -- integrable function for the squared norm of the difference using the previous
  -- uniform bound and the fact that `w ∈ L²`.
  have h_L2_error_tendsto :
      Filter.Tendsto (fun R : ℝ =>
          eLpNorm (fun ξ : ℝ => GR R ξ * w ξ - w ξ) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    classical
    -- Error function on the frequency side.
    set E : ℝ → ℝ → ℂ :=
      fun R ξ => GR R ξ * w ξ - w ξ

    -- Step 1: pointwise convergence of the error `E R ξ` to `0` for each ξ.
    have h_pointwise_error :
        ∀ ξ : ℝ,
          Filter.Tendsto (fun R : ℝ => E R ξ)
            Filter.atTop (𝓝 (0 : ℂ)) := by
      intro ξ
      -- From `GR R ξ * w ξ → w ξ`, we get `GR R ξ * w ξ - w ξ → 0`.
      have h_main := h_pointwise_w ξ
      have h_sub :
          Filter.Tendsto (fun R : ℝ => GR R ξ * w ξ - w ξ)
            Filter.atTop (𝓝 (w ξ - w ξ)) :=
        h_main.sub tendsto_const_nhds
      simpa [E] using h_sub

    -- Step 2: domination of the squared error by an L¹ majorant.
    have h_dominated_sq :
        ∃ g : ℝ → ℝ,
          Integrable g ∧
          ∀ R : ℝ, ∀ᵐ ξ : ℝ,
            ‖E R ξ‖ ^ (2 : ℝ) ≤ g ξ := by
      classical
      -- Use the L² membership of `w` to build an L¹ majorant.
      -- A natural choice is `g ξ = (2 * ‖w ξ‖) ^ 2 = 4 * ‖w ξ‖^2`, which is integrable
      -- because `w ∈ L²` and the square of the norm is L¹.
      let g : ℝ → ℝ := fun ξ => (2 * ‖w ξ‖) ^ (2 : ℝ)

      -- Integrability of `g`: consequence of `hw : MemLp w 2`.
      have hg_int : Integrable g volume := by
        -- First, `w ∈ L²` implies integrability of the squared norm `‖w ξ‖²`.
        have hw_sq_int :
            Integrable (fun ξ : ℝ => ‖w ξ‖ ^ (2 : ℝ)) volume := by
          -- Directly reuse the general L² lemma from the core theory.
          simpa using
            (Frourio.integrable_norm_sq_of_memLp_two (f := w) hw)

        -- Multiply the integrable function `‖w ξ‖²` by the constant factor `4`.
        have h_int_4 :
            Integrable (fun ξ : ℝ => (4 : ℝ) * ‖w ξ‖ ^ (2 : ℝ)) volume :=
          (hw_sq_int.const_mul 4)

        -- Identify this function with `g`.
        have h_g_eq :
            (fun ξ : ℝ => (4 : ℝ) * ‖w ξ‖ ^ (2 : ℝ)) = g := by
          funext ξ
          -- `g ξ = (2‖w ξ‖)² = 4‖w ξ‖²`.
          simp only [g]
          rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)]
          norm_num

        rw [← h_g_eq]
        exact h_int_4

      -- Pointwise bound: ‖E R ξ‖² ≤ g ξ for every R, ξ.
      have h_bound_all :
          ∀ R : ℝ, ∀ᵐ ξ : ℝ, ‖E R ξ‖ ^ (2 : ℝ) ≤ g ξ := by
        intro R
        -- Start from the triangle inequality:
        --   ‖E R ξ‖ = ‖GR R ξ * w ξ - w ξ‖
        --          ≤ ‖GR R ξ * w ξ‖ + ‖w ξ‖.
        -- Using the pointwise bound ‖GR R ξ * w ξ‖ ≤ ‖w ξ‖ (which we prove below),
        -- we get
        --   ‖E R ξ‖ ≤ 2 * ‖w ξ‖,
        -- hence
        --   ‖E R ξ‖² ≤ (2 * ‖w ξ‖)² = g ξ.
        refine Filter.Eventually.of_forall ?_
        intro ξ
        have h_tri :
            ‖E R ξ‖
              ≤ ‖GR R ξ * w ξ‖ + ‖w ξ‖ := by
          -- Triangle inequality in ℂ.
          have := norm_add_le (GR R ξ * w ξ) (-w ξ)
          simpa [E, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            norm_neg] using this
        have h_le_2 :
            ‖E R ξ‖ ≤ 2 * ‖w ξ‖ := by
          -- Prove ‖GR R ξ * w ξ‖ ≤ ‖w ξ‖ using ‖GR R ξ‖ ≤ 1
          have h_mul_le : ‖GR R ξ * w ξ‖ ≤ ‖w ξ‖ := by
            have h_norm_GR : ‖GR R ξ‖ ≤ 1 := by
              -- GR R ξ = exp(-(π)(ξ/R)²) is real and ≤ 1
              have h_def : (GR R ξ) = (Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ) := rfl
              have h_nonneg : 0 ≤ Real.exp (-(Real.pi) * (ξ / R) ^ 2) :=
                Real.exp_nonneg _
              have h_exp_le : Real.exp (-(Real.pi) * (ξ / R) ^ 2) ≤ 1 := by
                apply Real.exp_le_one_iff.mpr
                exact mul_nonpos_of_nonpos_of_nonneg
                  (neg_nonpos.mpr (le_of_lt Real.pi_pos)) (sq_nonneg _)
              rw [h_def, Complex.norm_real]
              exact le_trans (le_of_eq (abs_of_nonneg h_nonneg)) h_exp_le
            calc ‖GR R ξ * w ξ‖
                = ‖GR R ξ‖ * ‖w ξ‖ := norm_mul _ _
              _ ≤ 1 * ‖w ξ‖ := by
                  exact mul_le_mul_of_nonneg_right h_norm_GR (norm_nonneg _)
              _ = ‖w ξ‖ := one_mul _
          -- `‖GR R ξ * w ξ‖ + ‖w ξ‖ ≤ ‖w ξ‖ + ‖w ξ‖ = 2‖w ξ‖`.
          have h_sum :
              ‖GR R ξ * w ξ‖ + ‖w ξ‖ ≤ ‖w ξ‖ + ‖w ξ‖ :=
            add_le_add h_mul_le (le_refl _)
          have h_rhs :
              ‖w ξ‖ + ‖w ξ‖ = 2 * ‖w ξ‖ := by
            ring_nf
          exact
            le_trans h_tri
              (by simpa [h_rhs] using h_sum)
        -- Square both sides (both nonnegative) to get the desired bound.
        have h_nonneg_left : 0 ≤ ‖E R ξ‖ := norm_nonneg _
        have h_nonneg_right : 0 ≤ 2 * ‖w ξ‖ :=
          mul_nonneg (by norm_num) (norm_nonneg _)
        have h_sq : ‖E R ξ‖ ^ (2 : ℝ) ≤ (2 * ‖w ξ‖) ^ (2 : ℝ) := by
          have : ‖E R ξ‖ ^ (2 : ℝ) ≤ (2 * ‖w ξ‖) ^ (2 : ℝ) :=
            Real.rpow_le_rpow h_nonneg_left h_le_2 (by norm_num : (0 : ℝ) ≤ 2)
          exact this
        simpa [g] using h_sq

      exact ⟨g, hg_int, h_bound_all⟩
    obtain ⟨g, hg_int, h_bound_all⟩ := h_dominated_sq

    -- Step 3: measurability of the squared error integrand for each R.
    have h_meas_sq :
        ∀ R : ℝ,
          AEStronglyMeasurable (fun ξ : ℝ => (‖E R ξ‖ : ℝ) ^ (2 : ℝ)) volume := by
      intro R
      -- First, `w` is a.e. strongly measurable since it belongs to L².
      have h_meas_w : AEStronglyMeasurable w volume :=
        hw.aestronglyMeasurable

      -- The Gaussian cutoff `GR R` is continuous in ξ, hence a.e. strongly measurable.
      have h_meas_GR :
          AEStronglyMeasurable (fun ξ : ℝ => GR R ξ) volume := by
        -- Continuity of ξ ↦ ξ / R.
        have h_cont_div : Continuous fun ξ : ℝ => ξ / R := by
          have h_eq :
              (fun ξ : ℝ => ξ / R) = fun ξ : ℝ => ξ * (1 / R) := by
            funext ξ; simp [div_eq_mul_inv]
          simpa [h_eq] using
            (continuous_id.mul continuous_const :
              Continuous fun ξ : ℝ => ξ * (1 / R))
        -- Continuity of the real Gaussian factor.
        have h_cont_real :
            Continuous fun ξ : ℝ =>
              Real.exp (-(Real.pi) * (ξ / R) ^ 2) :=
          Real.continuous_exp.comp
            (continuous_const.mul (h_cont_div.pow 2))
        -- Lift to ℂ and conclude a.e. strong measurability.
        have h_cont_complex :
            Continuous fun ξ : ℝ =>
              (Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ) :=
          Complex.continuous_ofReal.comp h_cont_real
        simpa [GR] using h_cont_complex.aestronglyMeasurable

      -- Hence the error term `E R` is a.e. strongly measurable.
      have h_meas_E :
          AEStronglyMeasurable (fun ξ : ℝ => E R ξ) volume := by
        have h_meas_prod :
            AEStronglyMeasurable (fun ξ : ℝ => GR R ξ * w ξ) volume :=
          h_meas_GR.mul h_meas_w
        -- `E R ξ = GR R ξ * w ξ - w ξ`.
        simpa [E] using h_meas_prod.sub h_meas_w

      -- Take the norm: ξ ↦ ‖E R ξ‖ is a.e. strongly measurable.
      have h_meas_norm :
          AEStronglyMeasurable (fun ξ : ℝ => (‖E R ξ‖ : ℝ)) volume :=
        h_meas_E.norm

      -- Finally, compose with the (real) map x ↦ x^(2:ℝ), which is measurable;
      -- this yields measurability of ξ ↦ ‖E R ξ‖².
      have h_meas_pow :
          AEStronglyMeasurable (fun ξ : ℝ => (‖E R ξ‖ : ℝ) ^ (2 : ℝ)) volume := by
        -- The function x ↦ x^2 is continuous, hence strongly measurable.
        have h_cont : Continuous fun x : ℝ => x ^ (2 : ℝ) := by
          exact continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)
        exact h_cont.aestronglyMeasurable.comp_aemeasurable h_meas_norm.aemeasurable

      exact h_meas_pow

    -- Step 4: dominated convergence for the squared L² norm on the frequency side.
    have h_lintegral_sq_tendsto :
        Filter.Tendsto (fun R : ℝ =>
            ∫ ξ : ℝ, (‖E R ξ‖ : ℝ) ^ (2 : ℝ) ∂volume)
          Filter.atTop (𝓝 (0 : ℝ)) := by
      -- Apply dominated convergence to the nonnegative real family
      -- `f R ξ = ‖E R ξ‖²`, dominated by `g` and converging pointwise to `0`.
      classical
      -- 1. Measurability of each integrand, from `h_meas_sq`.
      have h_meas_f :
          ∀ R : ℝ,
            AEStronglyMeasurable
              (fun ξ : ℝ => (‖E R ξ‖ : ℝ) ^ (2 : ℝ)) volume :=
        h_meas_sq

      -- 2. Integrability of the dominating function `g` is given by `hg_int`.

      -- 3. Pointwise domination: for each `R` we have
      --      ‖E R ξ‖² ≤ g ξ   a.e.,
      --    provided by `h_bound_all`.
      have h_bound_f :
          ∀ R : ℝ, ∀ᵐ ξ : ℝ ∂volume,
            ‖(fun ξ => (‖E R ξ‖ : ℝ) ^ (2 : ℝ)) ξ‖ ≤ g ξ := by
        intro R
        -- Since the integrand is nonnegative real-valued, its real norm is itself.
        have h_dom := h_bound_all R
        refine h_dom.mono ?_
        intro ξ hξ
        -- `‖‖E R ξ‖²‖ = ‖E R ξ‖²` for real values.
        simpa using hξ

      -- 4. Pointwise convergence to 0 for almost every ξ:
      -- from `E R ξ → 0` we get `‖E R ξ‖² → 0`.
      have h_lim_f :
          ∀ᵐ ξ : ℝ ∂volume,
            Filter.Tendsto (fun R : ℝ =>
                (‖E R ξ‖ : ℝ) ^ (2 : ℝ))
              Filter.atTop (𝓝 (0 : ℝ)) := by
        -- Start from `h_pointwise_error : ∀ ξ, E R ξ → 0` and upgrade to an
        -- a.e. statement by `Filter.Eventually.of_forall`.
        refine Filter.Eventually.of_forall ?_
        intro ξ
        have hE := h_pointwise_error ξ
        -- Compose with the continuous map x ↦ ‖x‖² : ℂ → ℝ to get convergence.
        have h_cont :
            Continuous fun z : ℂ => (‖z‖ : ℝ) ^ (2 : ℝ) := by
          -- continuity of the norm and of the squaring map
          have h_norm : Continuous fun z : ℂ => (‖z‖ : ℝ) :=
            continuous_norm
          have h_pow : Continuous fun x : ℝ => x ^ (2 : ℝ) :=
            continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)
          exact h_pow.comp h_norm
        simpa using h_cont.continuousAt.tendsto.comp hE

      -- 5. Apply the dominated convergence lemma (real-valued version with parameter ℝ).
      -- Define a helper that explicitly converts real to complex
      have h_meas_f_complex : ∀ R : ℝ,
          AEStronglyMeasurable (fun ξ => (Complex.ofReal ((‖E R ξ‖ : ℝ) ^ (2 : ℝ)))) volume := by
        intro R
        have : (fun ξ => Complex.ofReal ((‖E R ξ‖ : ℝ) ^ (2 : ℝ))) =
            Complex.ofReal ∘ (fun ξ => (‖E R ξ‖ : ℝ) ^ (2 : ℝ)) := rfl
        rw [this]
        exact Complex.continuous_ofReal.comp_aestronglyMeasurable (h_meas_f R)

      -- Adapt h_bound_f to the complex-valued version
      have h_bound_f_complex : ∀ R : ℝ, ∀ᵐ ξ : ℝ ∂volume,
          ‖Complex.ofReal ((‖E R ξ‖ : ℝ) ^ (2 : ℝ))‖ ≤ g ξ := by
        intro R
        have := h_bound_f R
        refine this.mono ?_
        intro ξ hξ
        simp only at hξ ⊢
        rw [Complex.norm_real, Real.norm_eq_abs]
        have h_nonneg : 0 ≤ (‖E R ξ‖ : ℝ) ^ (2 : ℝ) := by
          apply Real.rpow_nonneg
          exact norm_nonneg _
        calc
          |(‖E R ξ‖ : ℝ) ^ (2 : ℝ)| = (‖E R ξ‖ : ℝ) ^ (2 : ℝ) := abs_of_nonneg h_nonneg
          _ = ‖(‖E R ξ‖ : ℝ) ^ (2 : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
          _ ≤ g ξ := hξ

      -- Adapt h_lim_f to the complex-valued version
      have h_lim_f_complex : ∀ᵐ ξ : ℝ ∂volume,
          Filter.Tendsto (fun R : ℝ => Complex.ofReal ((‖E R ξ‖ : ℝ) ^ (2 : ℝ)))
            Filter.atTop (𝓝 (0 : ℂ)) := by
        have := h_lim_f
        refine this.mono ?_
        intro ξ hξ
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp hξ

      have h_tendsto :=
        Frourio.MeasureTheory.tendsto_integral_of_dominated_convergence_atTop_real
          (f := fun R ξ => Complex.ofReal ((‖E R ξ‖ : ℝ) ^ (2 : ℝ)))
          (flim := fun _ξ => (0 : ℂ))
          (g := g)
          (h_meas := h_meas_f_complex)
          (hg_int := hg_int)
          (h_bound := h_bound_f_complex)
          (h_lim := h_lim_f_complex)

      -- 6. Identify integrals with the real integral
      have h_integral_eq : ∀ R : ℝ,
          ∫ ξ : ℝ, Complex.ofReal ((‖E R ξ‖ : ℝ) ^ (2 : ℝ)) ∂volume =
            Complex.ofReal (∫ ξ : ℝ, (‖E R ξ‖ : ℝ) ^ (2 : ℝ) ∂volume) := by
        intro R
        have : (fun ξ => Complex.ofReal ((‖E R ξ‖ : ℝ) ^ (2 : ℝ))) =
            fun ξ => (↑((‖E R ξ‖ : ℝ) ^ (2 : ℝ)) : ℂ) := rfl
        rw [this]
        exact integral_ofReal

      -- Rewrite the conclusion of `h_tendsto` in the desired form.
      have h_tendsto_ofReal : Filter.Tendsto (fun R : ℝ =>
          Complex.ofReal (∫ ξ : ℝ, (‖E R ξ‖ : ℝ) ^ (2 : ℝ) ∂volume))
        Filter.atTop (𝓝 (0 : ℂ)) := by
        have : (fun R => ∫ ξ : ℝ, Complex.ofReal ((‖E R ξ‖ : ℝ) ^ (2 : ℝ)) ∂volume) =
            (fun R => Complex.ofReal (∫ ξ : ℝ, (‖E R ξ‖ : ℝ) ^ (2 : ℝ) ∂volume)) := by
          ext R
          exact h_integral_eq R
        rw [← this]
        simpa using h_tendsto

      -- Convert from complex to real convergence
      have : Filter.Tendsto (fun R : ℝ =>
          (∫ ξ : ℝ, (‖E R ξ‖ : ℝ) ^ (2 : ℝ) ∂volume))
        Filter.atTop (𝓝 (0 : ℝ)) := by
        rw [← Complex.ofReal_zero] at h_tendsto_ofReal
        exact (Complex.continuous_re.tendsto _).comp h_tendsto_ofReal

      exact this

    -- Step 5: translate convergence of the squared norm integrals into convergence
    -- of the L² `eLpNorm` to `0` in `ℝ≥0∞`, using the standard formula expressing
    -- `eLpNorm` via the rpow of the lintegral of the squared `enorm`.
    -- This uses continuity and monotonicity of the root map at `0`.
    -- The detailed conversion is supplied by the Fourier–Plancherel L² core
    -- together with basic properties of `eLpNorm` and the L² norm.
    have h_L2_error_tendsto :
        Filter.Tendsto (fun R : ℝ =>
            eLpNorm (fun ξ : ℝ => E R ξ) 2 volume)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      classical

      -- For each radius `R`, the error function `E R` is in L², since its squared
      -- norm is dominated by the integrable function `g`.
      have h_memLp_E :
          ∀ R : ℝ, MemLp (fun ξ : ℝ => E R ξ) 2 volume := by
        intro R
        -- Measurability of `E R` was already obtained when proving `h_meas_sq`.
        have h_meas_E_R :
            AEStronglyMeasurable (fun ξ : ℝ => E R ξ) volume := by
          -- Reuse the construction from `h_meas_sq`.
          have h_meas_w : AEStronglyMeasurable w volume :=
            hw.aestronglyMeasurable
          have h_meas_GR :
              AEStronglyMeasurable (fun ξ : ℝ => GR R ξ) volume := by
            have h_cont_div : Continuous fun ξ : ℝ => ξ / R := by
              have h_eq :
                  (fun ξ : ℝ => ξ / R) = fun ξ : ℝ => ξ * (1 / R) := by
                funext ξ; simp [div_eq_mul_inv]
              simpa [h_eq] using
                (continuous_id.mul continuous_const :
                  Continuous fun ξ : ℝ => ξ * (1 / R))
            have h_cont_real :
                Continuous fun ξ : ℝ =>
                  Real.exp (-(Real.pi) * (ξ / R) ^ 2) :=
              Real.continuous_exp.comp
                (continuous_const.mul (h_cont_div.pow 2))
            have h_cont_complex :
                Continuous fun ξ : ℝ =>
                  (Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ) :=
              Complex.continuous_ofReal.comp h_cont_real
            simpa [GR] using h_cont_complex.aestronglyMeasurable
          have h_meas_prod :
              AEStronglyMeasurable (fun ξ : ℝ => GR R ξ * w ξ) volume :=
            h_meas_GR.mul h_meas_w
          simpa [E] using h_meas_prod.sub h_meas_w

        -- Integrability of the squared norm of `E R`.
        have h_integrable_sq_R :
            Integrable (fun ξ : ℝ => (‖E R ξ‖ : ℝ) ^ (2 : ℝ)) volume := by
          -- From `h_bound_all R` we have a.e. bound by the fixed integrable `g`.
          have h_bound_R : ∀ᵐ ξ : ℝ ∂volume,
              ‖(fun ξ : ℝ => (‖E R ξ‖ : ℝ) ^ (2 : ℝ)) ξ‖ ≤ g ξ := by
            have h_dom := h_bound_all R
            refine h_dom.mono ?_
            intro ξ hξ
            -- The integrand is real and nonnegative, so its norm is itself.
            simpa using hξ
          exact Integrable.mono' hg_int (h_meas_sq R) h_bound_R

        -- Convert integrability of the squared norm into L² membership via the
        -- standard characterization `MemLp` ↔ integrability of the square.
        -- We use the helper lemma from the Gaussian development.
        have h_memLp_two :=
          (memLp_two_iff_integrable_sq_complex
            (f := fun ξ : ℝ => E R ξ)
            (hmeas := h_meas_E_R)).2 ?_
        · exact h_memLp_two
        · -- The real integrand in `memLp_two_iff_integrable_sq_complex` is
          -- `‖E R ξ‖ ^ (2 : ℕ)`; this coincides with our squared norm
          -- `(‖E R ξ‖ : ℝ) ^ (2 : ℝ)`, so integrability transfers directly.
          have h_eq :
              (fun ξ : ℝ => (‖E R ξ‖ : ℝ) ^ (2 : ℕ)) =
                fun ξ : ℝ => (‖E R ξ‖ : ℝ) ^ (2 : ℝ) := by
            funext ξ
            -- For nonnegative real numbers, the usual square and the real-power
            -- square agree.
            have h_nonneg : 0 ≤ (‖E R ξ‖ : ℝ) := norm_nonneg _
            -- Use the standard identity `x^2 = x^(2 : ℝ)` for `x ≥ 0`.
            simp [pow_two]
          simpa [h_eq] using h_integrable_sq_R

      -- Real-valued convergence of the L² norms via the squared integral.
      have h_toReal_tendsto :
          Filter.Tendsto (fun R : ℝ =>
              (eLpNorm (fun ξ : ℝ => E R ξ) 2 volume).toReal)
            Filter.atTop (𝓝 (0 : ℝ)) := by
        -- Express `(‖E R‖₂)` in terms of the integral of `‖E R‖²`.
        have h_eq :
            ∀ R : ℝ,
              (eLpNorm (fun ξ : ℝ => E R ξ) 2 volume).toReal
                = Real.sqrt
                    (∫ ξ : ℝ, (‖E R ξ‖ : ℝ) ^ (2 : ℝ) ∂volume) := by
          intro R
          -- Use the general identity relating the L² norm with the integral
          -- of the squared pointwise norm.
          have h_meas_E_R :
              AEStronglyMeasurable (fun ξ : ℝ => E R ξ) volume :=
            (h_memLp_E R).1
          have h_memLp_R : MemLp (fun ξ : ℝ => E R ξ) 2 volume :=
            h_memLp_E R
          have h_norm_sq :=
            lintegral_norm_sq_eq_integral_norm_sq
              (f := fun ξ : ℝ => E R ξ)
              (hmeas := h_meas_E_R)
              (hf := h_memLp_R)
          -- The left-hand side of `h_norm_sq` is exactly the real L² norm of `E R`.
          have h_id :
              (eLpNorm (fun ξ : ℝ => E R ξ) 2 volume).toReal
                = ((∫⁻ ξ, ‖(fun ξ : ℝ => E R ξ) ξ‖ₑ ^ (2 : ℝ) ∂volume) ^
                    (1 / (2 : ℝ))).toReal := by
            -- This follows from the general formula for `eLpNorm` at `p = 2`.
            have h₂_ne_zero : ((2 : ℝ≥0∞)) ≠ 0 := by simp
            have h₂_ne_top : ((2 : ℝ≥0∞)) ≠ ∞ := by simp
            have h_eLp :=
              (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
                (μ := volume)
                (f := fun ξ : ℝ => E R ξ)
                (p := (2 : ℝ≥0∞)) h₂_ne_zero h₂_ne_top).symm
            -- Simplify ENNReal.toReal 2 = 2
            simp only [ENNReal.toReal_ofNat] at h_eLp
            -- Take `toReal` on both sides.
            rw [h_eLp]
          -- Combine the two identities.
          simpa [h_id] using h_norm_sq

        -- Compose the convergence of the squared integrals with continuity of
        -- the square root at `0`.
        have h_sqrt_tendsto :
            Filter.Tendsto (fun R : ℝ =>
                Real.sqrt (∫ ξ : ℝ, (‖E R ξ‖ : ℝ) ^ (2 : ℝ) ∂volume))
              Filter.atTop (𝓝 (Real.sqrt (0 : ℝ))) := by
          have h_cont_sqrt : Continuous fun x : ℝ => Real.sqrt x :=
            Real.continuous_sqrt
          have h_comp := h_cont_sqrt.tendsto (0 : ℝ)
          -- Compose with the convergence of the squared integrals.
          have := h_comp.comp h_lintegral_sq_tendsto
          simpa using this

        have h_sqrt_zero : Real.sqrt (0 : ℝ) = 0 := by simp
        simpa [h_eq, h_sqrt_zero] using h_sqrt_tendsto

      -- Finally, lift the real-valued convergence to `ℝ≥0∞` using `toReal`.
      have h_ne_top :
          ∀ R : ℝ,
            eLpNorm (fun ξ : ℝ => E R ξ) 2 volume ≠ ∞ := by
        intro R
        exact (h_memLp_E R).2.ne
      have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp
      exact
        (ENNReal.tendsto_toReal_iff
          (fi := Filter.atTop)
          (f := fun R : ℝ =>
            eLpNorm (fun ξ : ℝ => E R ξ) 2 volume)
          h_ne_top h_zero_ne_top).mp h_toReal_tendsto

    exact h_L2_error_tendsto

  -- 5. This is exactly the desired statement.
  exact h_L2_error_tendsto

/-- Schwartz density in L²: every L² function can be approximated in L²
by Schwartz functions. -/
lemma schwartz_dense_in_L2
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    ∃ φ : ℕ → SchwartzMap ℝ ℂ,
      Filter.Tendsto (fun n => eLpNorm (fun t : ℝ => g t - φ n t) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  -- Step 1: pointwise approximation of a fixed L² function by a single
  -- Schwartz function with arbitrarily small L² error. This is provided by
  -- `exists_schwartz_L2_approx_general`.
  have h_approx :
      ∀ ε > 0, ∃ φ : SchwartzMap ℝ ℂ,
        eLpNorm (fun t : ℝ => g t - φ t) 2 volume < ENNReal.ofReal ε := by
    intro ε hε
    simpa using
      exists_schwartz_L2_approx_general (f := g) hg (ε := ε) hε

  -- Step 2: choose a sequence of tolerances εₙ → 0 and corresponding Schwartz
  -- approximants φₙ with L² error bounded by εₙ.
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    have h_denom_pos : (0 : ℝ) < (n + 1 : ℝ) := by
      -- `n.succ` is positive as a natural number, hence positive as a real.
      have : (0 : ℕ) < n.succ := Nat.succ_pos n
      exact_mod_cast this
    exact one_div_pos.mpr h_denom_pos

  -- For each n, pick a Schwartz approximant φ n with L² error < ε n.
  choose φ hφ using
    fun n => h_approx (ε n) (hε_pos n)

  -- Step 3: show that the L² error sequence tends to 0 in `ℝ≥0∞`.
  have h_tendsto :
      Filter.Tendsto (fun n => eLpNorm (fun t : ℝ => g t - φ n t) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    -- Following the pattern of `exists_schwartz_L2_approx` in
    -- `FourierPlancherelL2Core0`, we convert the pointwise bounds given by
    -- `hφ` into a convergence statement using a squeeze argument on
    -- real-valued norms.
    let gseq : ℕ → ℝ≥0∞ := fun n =>
      eLpNorm (fun t : ℝ => g t - φ n t) 2 volume
    have h_ne_top : ∀ n, gseq n ≠ ∞ := fun n =>
      ne_of_lt <|
        lt_trans (hφ n) ENNReal.ofReal_lt_top
    have h_nonneg : ∀ n, 0 ≤ (gseq n).toReal := fun _ =>
      ENNReal.toReal_nonneg
    have h_le : ∀ n, (gseq n).toReal ≤ ε n := by
      intro n
      have h_le' : gseq n ≤ ENNReal.ofReal (ε n) :=
        le_of_lt (hφ n)
      have h_pos : 0 ≤ ε n := (hε_pos n).le
      exact ENNReal.toReal_le_of_le_ofReal h_pos h_le'
    -- The sequence `ε n = 1 / (n+1)` tends to 0 in ℝ.
    have h_tendsto_aux : Filter.Tendsto ε Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_one_nhds_0
    -- Squeeze `(gseq n).toReal` between 0 and `ε n` to get convergence to 0.
    have h_tendsto_real :
        Filter.Tendsto (fun n : ℕ => (gseq n).toReal)
          Filter.atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_le h_tendsto_aux
    -- Finally, transfer the convergence back to ℝ≥0∞ using `ENNReal.toReal`.
    have h_tendsto' :
        Filter.Tendsto gseq Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      -- Use the characterization of convergence to 0 in ℝ≥0∞.
      rw [ENNReal.tendsto_atTop_zero]
      intro δ hδ_pos
      by_cases hδ_top : δ = ∞
      · refine ⟨0, fun n _ => ?_⟩
        simp [hδ_top]
      · have hδ_finite : δ ≠ ∞ := hδ_top
        have hδ_lt_top : δ < ∞ := lt_of_le_of_ne le_top hδ_finite
        have hδ_toReal_pos : (0 : ℝ) < δ.toReal := by
          rw [ENNReal.toReal_pos_iff]
          exact ⟨hδ_pos, hδ_lt_top⟩
        -- Use convergence of `(gseq n).toReal` to find an index where
        -- `(gseq n).toReal < δ.toReal`, and translate this back to ℝ≥0∞.
        have h_eventually :
            ∀ᶠ n in Filter.atTop, (gseq n).toReal < δ.toReal :=
          Filter.Tendsto.eventually_lt h_tendsto_real
            tendsto_const_nhds hδ_toReal_pos
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
        refine ⟨N, fun n hn => ?_⟩
        have h_toReal_lt : (gseq n).toReal < δ.toReal := hN n hn
        have h_ne_top_n : gseq n ≠ ⊤ := h_ne_top n
        have h_lt : gseq n < δ :=
          (ENNReal.toReal_lt_toReal h_ne_top_n hδ_finite).mp h_toReal_lt
        exact le_of_lt h_lt
    simpa [gseq] using h_tendsto'

  exact ⟨φ, h_tendsto⟩

/-- A.e. uniqueness from Schwartz pairings: if two L² functions have
the same pairing against every Schwartz test function, then they are equal a.e. -/
lemma ae_eq_of_schwartz_pairing_zero
    {f g : ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hpair : ∀ φ : SchwartzMap ℝ ℂ,
      ∫ t, (f t - g t) * conj (φ t) ∂volume = 0) :
    f =ᵐ[volume] g := by
  classical
  -- Consider the L² functions `f - g` and `g - g ≡ 0`.
  have hf_sub_g : MemLp (fun t : ℝ => f t - g t) 2 volume :=
    hf.sub hg
  have hg_sub_g : MemLp (fun t : ℝ => g t - g t) 2 volume :=
    hg.sub hg

  -- Show that their pairings against every Schwartz test function coincide.
  have h_pairings_eq :
      ∀ φ : SchwartzMap ℝ ℂ,
        ∫ t, (f t - g t)
              * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume
          = ∫ t, (g t - g t)
              * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume := by
    intro φ
    -- Left pairing: identified with the given vanishing Schwartz pairing.
    have h_left :
        ∫ t, (f t - g t)
              * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume = 0 := by
      -- Rewrite the integrand to the form appearing in `hpair`.
      have h_left' : ∫ t, (f t - g t) * conj (φ t) ∂volume = 0 := hpair φ
      have h_eq :
          (fun t : ℝ =>
            (f t - g t) * conj (φ t)) =
            fun t : ℝ =>
              (f t - g t) * (starRingEnd ℂ) (SchwartzMap.toFun φ t) := by
        funext t
        rfl
      rw [← h_eq]
      exact h_left'
    -- Right pairing: the integrand is identically zero.
    have h_right :
        ∫ t, (g t - g t)
              * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume = 0 := by
      have h_zero :
          (fun t : ℝ =>
            (g t - g t) * (starRingEnd ℂ) (SchwartzMap.toFun φ t))
            = fun _ : ℝ => (0 : ℂ) := by
        funext t
        have hsub : g t - g t = (0 : ℂ) := sub_self _
        rw [hsub, zero_mul]
      simp [h_zero]
    exact h_left.trans h_right.symm

  -- Apply the general a.e. uniqueness lemma in L² to `f - g` and `g - g ≡ 0`.
  have h_ae :
      (fun t : ℝ => f t - g t)
        =ᵐ[volume] fun t : ℝ => g t - g t :=
    ae_eq_of_memLp_schwartz_pairings
      (g₁ := fun t : ℝ => f t - g t)
      (g₂ := fun t : ℝ => g t - g t)
      (hg₁ := hf_sub_g) (hg₂ := hg_sub_g) (h_pairings := h_pairings_eq)

  -- Conclude that `f = g` almost everywhere.
  refine h_ae.mono ?_
  intro t ht
  have h_diff_zero : f t - g t = 0 := by
    simpa using congrArg (fun x => x) ht
  exact sub_eq_zero.mp h_diff_zero

/-- Continuity of the L²–Schwartz pairing in the first argument.

If `fₙ → f` in L² and `φ` is Schwartz (hence in L²), then
  ∫ fₙ · conj φ → ∫ f · conj φ. -/
lemma pairing_tendsto_L2_left
    {fn : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hfn_L2 : ∀ n, MemLp (fn n) 2 volume)
    (hf_L2 : MemLp f 2 volume)
    (φ : SchwartzMap ℝ ℂ)
    (hf_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun t => f t - fn n t) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun n => ∫ t : ℝ, (fn n t) * (conj (φ t)) ∂volume)
      Filter.atTop (𝓝 (∫ t : ℝ, f t * (conj (φ t)) ∂volume)) := by
  classical
  -- Pass to the `Lp` representatives of `fn n`, `f`, and the fixed test function `φ`.
  let fnLp : ℕ → Lp ℂ 2 volume :=
    fun n => (hfn_L2 n).toLp (fn n)
  let fLp : Lp ℂ 2 volume := hf_L2.toLp f
  let φLp : Lp ℂ 2 volume :=
    (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
      (fun t : ℝ => φ t)

  -- Step 1: upgrade convergence in `eLpNorm` to convergence in the `Lp` norm.
  -- Define the L²-distance between `fnLp n` and `fLp` in terms of `eLpNorm`.
  have hdist_eq :
      (fun n => dist (fnLp n) fLp)
        = fun n =>
            (eLpNorm (fun t : ℝ => f t - fn n t) 2 volume).toReal := by
    funext n
    -- `f - fn n` lies in L².
    have hdiff_mem :
        MemLp (fun t : ℝ => f t - fn n t) 2 volume :=
      hf_L2.sub (hfn_L2 n)
    -- Its `Lp` representative is `fLp - fnLp n`.
    have hcalc :
        hdiff_mem.toLp (fun t : ℝ => f t - fn n t)
          = fLp - fnLp n := by
      simpa [fnLp, fLp] using
        MemLp.toLp_sub hf_L2 (hfn_L2 n)
    -- Express the `Lp` norm via `eLpNorm`.
    have hnorm :=
      Lp.norm_toLp (μ := volume)
        (f := fun t : ℝ => f t - fn n t) hdiff_mem
    -- Rewrite the metric distance in terms of the `eLpNorm` of the difference.
    calc
      dist (fnLp n) fLp
          = ‖fnLp n - fLp‖ := by
              simp [dist_eq_norm]
      _ = ‖- (fLp - fnLp n)‖ := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = ‖fLp - fnLp n‖ := by
              simpa using (norm_neg (fLp - fnLp n))
      _ = (eLpNorm (fun t : ℝ => f t - fn n t) 2 volume).toReal := by
              simpa [hdiff_mem, hcalc] using hnorm

  -- `eLpNorm (f - fn n)` is finite for each n since `f - fn n ∈ L²`.
  have h_ne_top : ∀ n,
      eLpNorm (fun t : ℝ => f t - fn n t) 2 volume ≠ ∞ := fun n =>
    (hf_L2.sub (hfn_L2 n)).2.ne
  have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp

  -- Convert ENNReal convergence to real convergence via `toReal`.
  have h_toReal :
      Filter.Tendsto
        (fun n =>
          (eLpNorm (fun t : ℝ => f t - fn n t) 2 volume).toReal)
        Filter.atTop (𝓝 (0 : ℝ)) :=
    (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n =>
          eLpNorm (fun t : ℝ => f t - fn n t) 2 volume)
        h_ne_top h_zero_ne_top).mpr hf_tendsto

  -- Hence the `Lp` distance between `fnLp n` and `fLp` tends to zero.
  have hdist_tendsto :
      Filter.Tendsto (fun n => dist (fnLp n) fLp)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [hdist_eq] using h_toReal

  have hLp_tendsto :
      Filter.Tendsto fnLp Filter.atTop (𝓝 fLp) :=
    (tendsto_iff_dist_tendsto_zero).2 hdist_tendsto

  -- Step 2: apply continuity of the inner product in `Lp` with fixed left argument `φLp`.
  have h_inner_tendsto :
      Filter.Tendsto
        (fun n =>
          @inner ℂ (Lp ℂ 2 volume) _ φLp (fnLp n))
        Filter.atTop
        (𝓝 (@inner ℂ (Lp ℂ 2 volume) _ φLp fLp)) :=
    tendsto_inner_const_left_of_L2_tendsto hLp_tendsto φLp

  -- Step 3: identify the inner products with the original pairings.
  -- For each n, `∫ fn n · conj φ` equals the `L²` inner product in `Lp`.
  have h_fun_eq :
      (fun n =>
        ∫ t : ℝ, fn n t * (conj (φ t)) ∂volume)
        =
      fun n =>
        @inner ℂ (Lp ℂ 2 volume) _ φLp (fnLp n) := by
    funext n
    -- Start from the general integral/inner-product identity.
    have h_base :=
      integral_mul_star_eq_inner (hg_mem := hfn_L2 n) (φ := φ)
    -- Relate `starRingEnd` to complex conjugation in the integrand.
    have h_integrand :
        (fun t : ℝ =>
          fn n t * (starRingEnd ℂ) (SchwartzMap.toFun φ t))
          =
        fun t : ℝ =>
          fn n t * conj (φ t) := by
      funext t
      rfl
    -- Rewrite the integral accordingly.
    calc
      ∫ t, fn n t * conj (φ t) ∂volume
          = ∫ t, fn n t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume := by
              rw [← h_integrand]
      _ = @inner ℂ (Lp ℂ 2 volume) _ φLp (fnLp n) := by
              rw [← h_base]

  -- Likewise for the limit `f`.
  have h_lim_eq :
      ∫ t : ℝ, f t * (conj (φ t)) ∂volume
        =
      @inner ℂ (Lp ℂ 2 volume) _ φLp fLp := by
    have h_base :=
      integral_mul_star_eq_inner (hg_mem := hf_L2) (φ := φ)
    have h_integrand :
        (fun t : ℝ =>
          f t * (starRingEnd ℂ) (SchwartzMap.toFun φ t))
          =
        fun t : ℝ =>
          f t * conj (φ t) := by
      funext t
      rfl
    calc
      ∫ t, f t * conj (φ t) ∂volume
          = ∫ t, f t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume := by
              rw [← h_integrand]
      _ = @inner ℂ (Lp ℂ 2 volume) _ φLp fLp := by
              rw [← h_base]

  -- Step 4: transfer the convergence back to the original integral pairings.
  have h_tendsto_inner' :
      Filter.Tendsto
        (fun n =>
          ∫ t : ℝ, fn n t * (conj (φ t)) ∂volume)
        Filter.atTop
        (𝓝 (@inner ℂ (Lp ℂ 2 volume) _ φLp fLp)) := by
    simpa [h_fun_eq] using h_inner_tendsto

  have h_tendsto_integral :
      Filter.Tendsto
        (fun n =>
          ∫ t : ℝ, fn n t * (conj (φ t)) ∂volume)
        Filter.atTop
        (𝓝 (∫ t : ℝ, f t * (conj (φ t)) ∂volume)) := by
    simpa [h_lim_eq] using h_tendsto_inner'

  exact h_tendsto_integral

/-- Continuity of the L²–Schwartz pairing via Lp convergence.

If `(fn n).toLp → f.toLp` in L² and `φ` is Schwartz (hence in L²), then
  ∫ fn n · conj φ → ∫ f · conj φ. -/
lemma pairing_tendsto_L2_left_Lp
    {fn : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hfn_L2 : ∀ n, MemLp (fn n) 2 volume)
    (hf_L2 : MemLp f 2 volume)
    (φ : SchwartzMap ℝ ℂ)
    (hLp_tendsto : Filter.Tendsto
      (fun n => (hfn_L2 n).toLp (fn n))
      Filter.atTop (𝓝 (hf_L2.toLp f))) :
    Filter.Tendsto (fun n => ∫ t : ℝ, (fn n t) * (conj (φ t)) ∂volume)
      Filter.atTop (𝓝 (∫ t : ℝ, f t * (conj (φ t)) ∂volume)) := by
  classical
  -- Express Lp convergence in terms of the L² norm of the difference.
  have hdist_eq :
      (fun n =>
        dist ((hfn_L2 n).toLp (fn n)) (hf_L2.toLp f))
        = fun n =>
            (eLpNorm (fun t : ℝ => f t - fn n t) 2 volume).toReal := by
    funext n
    -- L² membership of the difference.
    have hdiff_mem :
        MemLp (fun t : ℝ => f t - fn n t) 2 volume :=
      hf_L2.sub (hfn_L2 n)
    -- Its Lp representative equals the difference of the Lp representatives.
    have hcalc :
        hdiff_mem.toLp (fun t : ℝ => f t - fn n t)
          = hf_L2.toLp f - (hfn_L2 n).toLp (fn n) := by
      simpa using
        MemLp.toLp_sub hf_L2 (hfn_L2 n)
    have hnorm :=
      Lp.norm_toLp (μ := volume)
        (f := fun t : ℝ => f t - fn n t) hdiff_mem
    calc
      dist ((hfn_L2 n).toLp (fn n)) (hf_L2.toLp f)
          = ‖(hfn_L2 n).toLp (fn n) - hf_L2.toLp f‖ := by
              simp [dist_eq_norm]
      _ = ‖- (hf_L2.toLp f - (hfn_L2 n).toLp (fn n))‖ := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = ‖hf_L2.toLp f - (hfn_L2 n).toLp (fn n)‖ := by
              simpa using (norm_neg (hf_L2.toLp f - (hfn_L2 n).toLp (fn n)))
      _ = (eLpNorm (fun t : ℝ => f t - fn n t) 2 volume).toReal := by
              simpa [hcalc] using hnorm

  -- From Lp convergence, deduce `eLpNorm (f - fn n) → 0` in `ℝ≥0∞`.
  have hdist_tendsto :
      Filter.Tendsto
        (fun n =>
          dist ((hfn_L2 n).toLp (fn n)) (hf_L2.toLp f))
        Filter.atTop (𝓝 (0 : ℝ)) :=
    (tendsto_iff_dist_tendsto_zero).1 hLp_tendsto
  have h_toReal :
      Filter.Tendsto
        (fun n =>
          (eLpNorm (fun t : ℝ => f t - fn n t) 2 volume).toReal)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [hdist_eq] using hdist_tendsto

  have h_ne_top : ∀ n,
      eLpNorm (fun t : ℝ => f t - fn n t) 2 volume ≠ ∞ := fun n =>
    (hf_L2.sub (hfn_L2 n)).2.ne
  have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp

  have hf_tendsto :
      Filter.Tendsto
        (fun n => eLpNorm (fun t : ℝ => f t - fn n t) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n =>
          eLpNorm (fun t : ℝ => f t - fn n t) 2 volume)
        h_ne_top h_zero_ne_top).mp h_toReal

  -- Now apply the L² pairing continuity lemma.
  exact pairing_tendsto_L2_left
    (hfn_L2 := hfn_L2) (hf_L2 := hf_L2) φ hf_tendsto

/- If `φ n → g` in `L²` and `φ n → h` pointwise (in the product topology on functions),
then `h = g` almost everywhere. Skeleton lemma (proof deferred). -/
lemma ae_eq_of_L2_limit_pointwise
    (φ : ℕ → ℝ → ℂ) (g h : ℝ → ℂ)
    (hφ_L2 : ∀ n, MemLp (φ n) 2 volume)
    (hg_L2 : MemLp g 2 volume)
    (hφ_tendsto_L2 : Filter.Tendsto
        (fun n => eLpNorm (fun t => g t - φ n t) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (h_pointwise : Filter.Tendsto (fun n => fun t => φ n t)
        Filter.atTop (𝓝 h)) :
    h =ᵐ[volume] g := by
  -- Standard: extract an a.e.-convergent subsequence from the `L²` convergence and
  -- identify the pointwise limit using uniqueness of a.e. limits.
  classical
  -- Lift the sequence and the limit to L² representatives
  let φLp : ℕ → Lp ℂ 2 volume := fun n => (hφ_L2 n).toLp (φ n)
  let gLp : Lp ℂ 2 volume := hg_L2.toLp g

  -- Show convergence in L² of the lifted sequence
  have h_norm_eq : ∀ n,
      ‖φLp n - gLp‖
        = ENNReal.toReal (eLpNorm (fun t => g t - φ n t) 2 volume) := by
    intro n
    have hdiff_mem : MemLp (fun t => g t - φ n t) 2 volume :=
      hg_L2.sub (hφ_L2 n)
    have hcalc :
        ((hg_L2.sub (hφ_L2 n)).toLp (fun t => g t - φ n t))
          = gLp - φLp n := by
      simpa [φLp, gLp] using MemLp.toLp_sub hg_L2 (hφ_L2 n)
    have hnorm :=
      Lp.norm_toLp (μ := volume)
        (f := fun t : ℝ => g t - φ n t) hdiff_mem
    simpa [hdiff_mem, hcalc, norm_sub_rev] using hnorm

  have h_toReal_tendsto :
      Filter.Tendsto
        (fun n => ENNReal.toReal
          (eLpNorm (fun t => g t - φ n t) 2 volume))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    -- Use `ENNReal.tendsto_toReal_iff` with eventual finiteness at all indices
    have h_ne_top : ∀ n,
        eLpNorm (fun t => g t - φ n t) 2 volume ≠ ∞ :=
      fun n => (hg_L2.sub (hφ_L2 n)).2.ne
    have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp
    -- Convert the given ENNReal convergence to real convergence after `toReal`
    simpa using
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
          (f := fun n => eLpNorm (fun t => g t - φ n t) 2 volume)
          h_ne_top h_zero_ne_top).mpr hφ_tendsto_L2

  have h_tendsto_Lp :
      Filter.Tendsto φLp Filter.atTop (𝓝 gLp) := by
    -- Characterize convergence in normed groups by norm of the difference → 0
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine h_toReal_tendsto.congr' ?_
    exact Filter.Eventually.of_forall (fun n => (h_norm_eq n).symm)

  -- Extract a subsequence that converges a.e. to `g` via convergence in measure
  have h_in_measure :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp (f := φLp) (g := gLp) h_tendsto_Lp
  obtain ⟨s, hs_mono, h_ae⟩ := h_in_measure.exists_seq_tendsto_ae

  -- The subsequence also converges pointwise to `h` (by composition)
  have hs_tendsto : Filter.Tendsto s Filter.atTop Filter.atTop :=
    StrictMono.tendsto_atTop hs_mono
  have h_pointwise_subseq :
      Filter.Tendsto (fun k => fun t => φ (s k) t)
        Filter.atTop (𝓝 h) :=
    h_pointwise.comp hs_tendsto

  -- Turn function convergence into pointwise convergence at each t by evaluation
  have h_eval_lim : ∀ t : ℝ,
      Filter.Tendsto (fun k => φ (s k) t)
        Filter.atTop (𝓝 (h t)) := by
    intro t
    have : ∀ x, Filter.Tendsto (fun k => (fun t' => φ (s k) t') x)
        Filter.atTop (𝓝 (h x)) :=
      (tendsto_pi_nhds.1 h_pointwise_subseq)
    simpa using this t

  -- For almost every t, the subsequence tends to g t; by uniqueness of limits, h t = g t
  -- Relate `Lp` representatives and concrete functions a.e.
  have h_coeφ : ∀ n, (fun t => (φLp n : ℝ → ℂ) t) =ᵐ[volume] φ n := by
    intro n; simpa [φLp] using MemLp.coeFn_toLp (hφ_L2 n)
  have h_coeg : (fun t => (gLp : ℝ → ℂ) t) =ᵐ[volume] g := MemLp.coeFn_toLp hg_L2

  -- Transfer the a.e. tendsto of representatives to the concrete functions
  have h_eq_ae : ∀ᵐ t ∂volume, h t = g t := by
    -- From `exists_seq_tendsto_ae`, we have a.e. tendsto of `φLp (s k)` to `gLp`
    -- Upgrade it using the a.e. equalities of representatives.
    have h_all_φ : ∀ᵐ t ∂volume, ∀ k, (φLp (s k) t) = φ (s k) t := by
      -- move `∀ k` outside using `ae_all_iff`
      refine (ae_all_iff.mpr ?_)
      intro k
      have hk : (fun t => (φLp (s k) : ℝ → ℂ) t) =ᵐ[volume] φ (s k) := h_coeφ (s k)
      simpa using hk
    have h_all_g : ∀ᵐ t ∂volume, (gLp : ℝ → ℂ) t = g t := h_coeg
    refine (h_ae.and <| h_all_φ.and h_all_g) |>.mono ?_
    intro t htrip
    rcases htrip with ⟨ht, hrest⟩
    rcases hrest with ⟨hφeq, hgeq⟩
    -- ht : Tendsto (fun k => (φLp (s k)) t) atTop (𝓝 ((gLp : ℝ → ℂ) t))
    -- hφeq : ∀ k, (φLp (s k) t) = φ (s k) t
    -- hgeq : (gLp : ℝ → ℂ) t = g t
    have ht' : Filter.Tendsto (fun k => φ (s k) t)
        Filter.atTop (𝓝 (g t)) := by
      have h_congr :
          (fun k => (φLp (s k) t)) =ᶠ[Filter.atTop]
            (fun k => φ (s k) t) :=
        Filter.Eventually.of_forall (fun k => by simpa using (hφeq k))
      -- Rewrite both the function and the limit
      simpa [hgeq] using ht.congr' h_congr
    -- uniqueness of limits in Hausdorff spaces with the pointwise limit to h
    have hh : Filter.Tendsto (fun k => φ (s k) t)
        Filter.atTop (𝓝 (h t)) := h_eval_lim t
    exact tendsto_nhds_unique hh ht'

  -- Conclude the a.e. equality of functions
  exact h_eq_ae

/-- L² convergence of Fourier transforms.

If Schwartz functions `φ_n` converge to `g` in L² and `g ∈ L¹ ∩ L²`, then
their Fourier transforms `F(φ_n)` converge to `F(g)` in L² norm.

This is a direct consequence of the Plancherel theorem: the Fourier transform
is an L² isometry, so ‖F(φ_n) - F(g)‖₂ = ‖φ_n - g‖₂ → 0.

The lemma packages the fact that L² convergence on the time side implies
L² convergence on the frequency side under the Fourier transform.
-/
lemma fourierTransform_tendsto_L2_of_schwartz_approx
    (g : ℝ → ℂ)
    (hg_L1 : Integrable g)
    (hg_L2 : MemLp g 2 volume)
    (φ : ℕ → SchwartzMap ℝ ℂ)
    (hφ_tendsto_L2 :
      Filter.Tendsto
        (fun n => eLpNorm (fun t => g t - φ n t) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n =>
        eLpNorm
          (fun ξ : ℝ =>
            Frourio.fourierIntegral g ξ - Frourio.fourierIntegral (fun t => φ n t) ξ)
          2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  -- This follows from Plancherel's theorem: the Fourier transform is an
  -- L² isometry, so the L² distance is preserved.
  -- Formally, one would use the fact that
  --   ‖F(g) - F(φ_n)‖₂ = ‖F(g - φ_n)‖₂ = ‖g - φ_n‖₂ → 0.
  classical

  -- Step 1: Rewrite the goal to show that the frequency-side difference
  -- equals the Fourier transform of the time-side difference.
  have h_eq : ∀ n : ℕ,
      (fun ξ : ℝ => fourierIntegral g ξ - fourierIntegral (fun t => φ n t) ξ)
        = (fun ξ : ℝ => fourierIntegral (fun t => g t - φ n t) ξ) := by
    intro n
    ext ξ
    -- Use linearity of the Fourier integral
    have hφ_int : Integrable (fun t : ℝ => φ n t) := (φ n).integrable
    exact (fourierIntegral_sub hg_L1 hφ_int ξ).symm

  -- Step 2: For each n, show that the eLpNorm on the frequency side equals
  -- the eLpNorm on the time side by the Plancherel isometry for
  -- g - φ_n (which is the difference of an L¹∩L² function and a Schwartz function).
  have h_norm_eq : ∀ n : ℕ,
      eLpNorm (fun ξ : ℝ => fourierIntegral g ξ - fourierIntegral (fun t => φ n t) ξ) 2 volume
        = eLpNorm (fun t => g t - φ n t) 2 volume := by
    intro n
    rw [h_eq n]
    -- We need to show that φ_n and g - φ_n have the necessary properties
    -- to apply the Plancherel-type equality.
    -- Since φ_n is Schwartz and g ∈ L¹ ∩ L², we have g - φ_n ∈ L¹ ∩ L².

    -- First, show g - φ_n is integrable
    have hφ_int : Integrable (fun t : ℝ => φ n t) := (φ n).integrable
    have h_diff_int : Integrable (fun t => g t - φ n t) := hg_L1.sub hφ_int

    -- Second, show g - φ_n ∈ L²
    have hφ_L2 : MemLp (fun t : ℝ => φ n t) 2 volume :=
      SchwartzMap.memLp (φ n) (p := 2) (μ := volume)
    have h_diff_L2 : MemLp (fun t => g t - φ n t) 2 volume := hg_L2.sub hφ_L2

    -- Apply the Plancherel identity for L¹ ∩ L² functions
    -- We need to convert from integral equality to eLpNorm equality
    set F := fun ξ : ℝ => fourierIntegral (fun t => g t - φ n t) ξ
    set G := fun t => g t - φ n t

    have hF_mem : MemLp F 2 volume := fourierIntegral_memLp_L1_L2 h_diff_int h_diff_L2
    have hG_mem : MemLp G 2 volume := h_diff_L2

    have hF_int_sq : Integrable (fun ξ : ℝ => ‖F ξ‖ ^ 2) volume := by
      have := (memLp_two_iff_integrable_sq_norm hF_mem.1).1 hF_mem
      simpa [F, pow_two] using this
    have hG_int_sq : Integrable (fun t : ℝ => ‖G t‖ ^ 2) volume := by
      have := (memLp_two_iff_integrable_sq_norm hG_mem.1).1 hG_mem
      simpa [G, pow_two] using this

    have h_plancherel := fourier_plancherel_L1_L2 G h_diff_int h_diff_L2

    -- Convert the integral equality to eLpNorm equality
    have h_integral_eq : ∫ ξ : ℝ, ‖F ξ‖ ^ 2 ∂volume = ∫ t : ℝ, ‖G t‖ ^ 2 ∂volume := by
      simpa [F, G] using h_plancherel.symm

    -- Use the fact that eLpNorm is determined by the integral of the square of the norm
    have hF_nonneg : 0 ≤ᵐ[volume] fun ξ : ℝ => ‖F ξ‖ ^ 2 :=
      Filter.Eventually.of_forall fun _ => sq_nonneg _
    have hG_nonneg : 0 ≤ᵐ[volume] fun t : ℝ => ‖G t‖ ^ 2 :=
      Filter.Eventually.of_forall fun _ => sq_nonneg _

    have hF_lintegral :
        ∫⁻ ξ : ℝ, (‖F ξ‖₊ : ℝ≥0∞) ^ 2 ∂volume
          = ∫⁻ ξ : ℝ, ENNReal.ofReal (‖F ξ‖ ^ 2) ∂volume := by
      refine lintegral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro ξ
      simp [F, pow_two, ENNReal.ofReal_mul]
    have hG_lintegral :
        ∫⁻ t : ℝ, (‖G t‖₊ : ℝ≥0∞) ^ 2 ∂volume
          = ∫⁻ t : ℝ, ENNReal.ofReal (‖G t‖ ^ 2) ∂volume := by
      refine lintegral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro t
      simp [G, pow_two, ENNReal.ofReal_mul]

    have hF_ofReal :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF_int_sq hF_nonneg
    have hG_ofReal :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG_int_sq hG_nonneg

    have h_eq_lintegral :
        ∫⁻ ξ : ℝ, (‖F ξ‖₊ : ℝ≥0∞) ^ 2 ∂volume
          = ∫⁻ t : ℝ, (‖G t‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
      rw [hF_lintegral, hG_lintegral, ← hF_ofReal, ← hG_ofReal, h_integral_eq]

    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have h_twoReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    have hF_formula :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        (μ := volume) (f := F) (p := (2 : ℝ≥0∞))
        (hp_ne_zero := hp0) (hp_ne_top := hp_top)
    have hG_formula :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        (μ := volume) (f := G) (p := (2 : ℝ≥0∞))
        (hp_ne_zero := hp0) (hp_ne_top := hp_top)
    have hF_eval :
        eLpNorm F 2 volume
          = (∫⁻ ξ : ℝ, (‖F ξ‖₊ : ℝ≥0∞) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
      simpa [h_twoReal, one_div] using hF_formula
    have hG_eval :
        eLpNorm G 2 volume
          = (∫⁻ t : ℝ, (‖G t‖₊ : ℝ≥0∞) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
      simpa [h_twoReal, one_div] using hG_formula

    calc eLpNorm F 2 volume
        = (∫⁻ ξ : ℝ, (‖F ξ‖₊ : ℝ≥0∞) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := hF_eval
      _ = (∫⁻ t : ℝ, (‖G t‖₊ : ℝ≥0∞) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by rw [h_eq_lintegral]
      _ = eLpNorm G 2 volume := hG_eval.symm

  -- Step 3: Conclude by transferring the convergence from time side to frequency side
  simp_rw [h_norm_eq]
  exact hφ_tendsto_L2

/-- **Auxiliary lemma**: If a sequence in L² converges, and the pointwise representatives
of each term converge a.e. to a limit, then the L² limit's representative equals
that pointwise limit a.e.

This is a general fact about L² spaces: if `fₙ → f` in L² and `fₙ → g` a.e.,
then `f =ᵐ g`. -/
lemma Lp_limit_ae_eq_of_ae_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → Lp ℂ 2 μ) (f_lim : Lp ℂ 2 μ) (g : α → ℂ)
    (hf_tendsto : Filter.Tendsto f Filter.atTop (𝓝 f_lim))
    (hf_ae : ∀ n, (f n : α → ℂ) =ᵐ[μ] (fun x => g x))
    (hg_mem : MemLp g 2 μ) :
    (f_lim : α → ℂ) =ᵐ[μ] g := by
  classical
  -- L² representative of `g`.
  let gLp : Lp ℂ 2 μ := hg_mem.toLp g

  -- 1. Each `f n` equals `gLp` in `Lp`, since their representatives agree a.e.
  have hf_eq_gLp : ∀ n, f n = gLp := by
    intro n
    apply Lp.ext
    -- a.e. equality of representatives:
    -- (f n) = g and gLp = g ⇒ (f n) = gLp a.e.
    have h1 : (f n : α → ℂ) =ᵐ[μ] g := hf_ae n
    have h2 : (gLp : α → ℂ) =ᵐ[μ] g := MemLp.coeFn_toLp hg_mem
    exact h1.trans h2.symm

  -- 2. Identify the L² limit `f_lim` with `gLp` using uniqueness of limits.
  have hf_const : f = fun _ : ℕ => gLp := by
    funext n
    exact hf_eq_gLp n
  have h_const_tendsto :
      Filter.Tendsto (fun _ : ℕ => gLp) Filter.atTop (𝓝 gLp) :=
    tendsto_const_nhds
  have h_lim_eq : f_lim = gLp := by
    -- Rewrite `hf_tendsto` along the identification `f = const gLp`.
    have h_tendsto' :
        Filter.Tendsto (fun _ : ℕ => gLp) Filter.atTop (𝓝 f_lim) := by
      simpa [hf_const] using hf_tendsto
    -- Ensure the filter atTop on ℕ is nontrivial.
    haveI : Filter.NeBot (Filter.atTop : Filter ℕ) := by infer_instance
    exact tendsto_nhds_unique h_tendsto' h_const_tendsto

  -- 3. Transfer back to functions: `gLp` represents `g` a.e., and `f_lim = gLp`.
  have h_gLp_ae : (gLp : α → ℂ) =ᵐ[μ] g := MemLp.coeFn_toLp hg_mem
  simpa [h_lim_eq] using h_gLp_ae

/-- **Auxiliary lemma**: L² convergence of a sequence implies the existence of
an a.e. convergent subsequence.

If `fₙ → f` in L², then there exists a subsequence that converges a.e. to `f`. -/
lemma exists_ae_tendsto_of_Lp_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → Lp ℂ 2 μ) (f_lim : Lp ℂ 2 μ)
    (hf_tendsto : Filter.Tendsto f Filter.atTop (𝓝 f_lim)) :
    ∃ (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun k => (f (ns k) : α → ℂ) x) Filter.atTop
        (𝓝 ((f_lim : α → ℂ) x))) := by
  classical
  -- L² convergence in `Lp` implies convergence in measure.
  have h_in_measure :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp (f := f) (g := f_lim) hf_tendsto
  -- From convergence in measure, extract an a.e. convergent subsequence.
  obtain ⟨ns, hs_mono, h_ae⟩ := h_in_measure.exists_seq_tendsto_ae
  exact ⟨ns, hs_mono, h_ae⟩

/-- **Auxiliary lemma**: Two L² functions that are L² limits of the same sequence
(in the Cauchy sense) are equal a.e.

If both `F[φₙ] → f₁` and `F[φₙ] → f₂` in L², then `f₁ =ᵐ f₂`. -/
lemma ae_eq_of_Lp_tendsto_same
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℂ) (f₁ f₂ : Lp ℂ 2 μ)
    (hf_mem : ∀ n, MemLp (f n) 2 μ)
    (hf₁_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun x => (f₁ : α → ℂ) x - f n x) 2 μ)
      Filter.atTop (𝓝 0))
    (hf₂_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun x => (f₂ : α → ℂ) x - f n x) 2 μ)
      Filter.atTop (𝓝 0)) :
    (f₁ : α → ℂ) =ᵐ[μ] (f₂ : α → ℂ) := by
  classical
  -- Pass to the `Lp` representatives of the approximating sequence.
  let fnLp : ℕ → Lp ℂ 2 μ := fun n => (hf_mem n).toLp (f n)

  -- L² membership of the fixed limits as concrete functions.
  have hf₁_mem : MemLp (fun x => (f₁ : α → ℂ) x) 2 μ := Lp.memLp f₁
  have hf₂_mem : MemLp (fun x => (f₂ : α → ℂ) x) 2 μ := Lp.memLp f₂

  -- 1. Upgrade `hf₁_tendsto` to convergence of `fnLp` to `f₁` in `Lp`.
  have hdist_eq₁ :
      (fun n => dist (fnLp n) f₁)
        = fun n =>
            (eLpNorm (fun x => (f₁ : α → ℂ) x - f n x) 2 μ).toReal := by
    funext n
    -- L² membership of the difference `f₁ - f n`.
    have hdiff_mem₁ :
        MemLp (fun x => (f₁ : α → ℂ) x - f n x) 2 μ :=
      hf₁_mem.sub (hf_mem n)
    -- Its `Lp` representative equals the difference of the `Lp` representatives.
    have hcalc₁ :
        hdiff_mem₁.toLp (fun x => (f₁ : α → ℂ) x - f n x)
          = f₁ - fnLp n := by
      -- This is an instance of `MemLp.toLp_sub` with `hf₁_mem` and `hf_mem n`.
      simpa [fnLp] using MemLp.toLp_sub hf₁_mem (hf_mem n)
    -- Express the `Lp` norm in terms of `eLpNorm`.
    have hnorm₁ :=
      Lp.norm_toLp (μ := μ)
        (f := fun x : α => (f₁ : α → ℂ) x - f n x) hdiff_mem₁
    -- Rewrite the metric distance in terms of `eLpNorm`.
    calc
      dist (fnLp n) f₁
          = ‖fnLp n - f₁‖ := by
              simp [dist_eq_norm]
      _ = ‖- (f₁ - fnLp n)‖ := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = ‖f₁ - fnLp n‖ := by
              simpa using (norm_neg (f₁ - fnLp n))
      _ = (eLpNorm (fun x : α => (f₁ : α → ℂ) x - f n x) 2 μ).toReal := by
              simpa [hdiff_mem₁, hcalc₁] using hnorm₁

  have h_ne_top₁ :
      ∀ n, eLpNorm (fun x => (f₁ : α → ℂ) x - f n x) 2 μ ≠ ∞ := fun n =>
    (hf₁_mem.sub (hf_mem n)).2.ne
  have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp

  have h_toReal₁ :
      Filter.Tendsto
        (fun n =>
          (eLpNorm (fun x => (f₁ : α → ℂ) x - f n x) 2 μ).toReal)
        Filter.atTop (𝓝 (0 : ℝ)) :=
    (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n =>
          eLpNorm (fun x => (f₁ : α → ℂ) x - f n x) 2 μ)
        h_ne_top₁ h_zero_ne_top).mpr hf₁_tendsto

  have hdist_tendsto₁ :
      Filter.Tendsto (fun n => dist (fnLp n) f₁)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [hdist_eq₁] using h_toReal₁

  have hLp_tendsto₁ :
      Filter.Tendsto fnLp Filter.atTop (𝓝 f₁) :=
    (tendsto_iff_dist_tendsto_zero).2 hdist_tendsto₁

  -- 2. Similarly, upgrade `hf₂_tendsto` to convergence of `fnLp` to `f₂` in `Lp`.
  have hdist_eq₂ :
      (fun n => dist (fnLp n) f₂)
        = fun n =>
            (eLpNorm (fun x => (f₂ : α → ℂ) x - f n x) 2 μ).toReal := by
    funext n
    have hdiff_mem₂ :
        MemLp (fun x => (f₂ : α → ℂ) x - f n x) 2 μ :=
      hf₂_mem.sub (hf_mem n)
    have hcalc₂ :
        hdiff_mem₂.toLp (fun x => (f₂ : α → ℂ) x - f n x)
          = f₂ - fnLp n := by
      simpa [fnLp] using MemLp.toLp_sub hf₂_mem (hf_mem n)
    have hnorm₂ :=
      Lp.norm_toLp (μ := μ)
        (f := fun x : α => (f₂ : α → ℂ) x - f n x) hdiff_mem₂
    calc
      dist (fnLp n) f₂
          = ‖fnLp n - f₂‖ := by
              simp [dist_eq_norm]
      _ = ‖- (f₂ - fnLp n)‖ := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = ‖f₂ - fnLp n‖ := by
              simpa using (norm_neg (f₂ - fnLp n))
      _ = (eLpNorm (fun x : α => (f₂ : α → ℂ) x - f n x) 2 μ).toReal := by
              simpa [hdiff_mem₂, hcalc₂] using hnorm₂

  have h_ne_top₂ :
      ∀ n, eLpNorm (fun x => (f₂ : α → ℂ) x - f n x) 2 μ ≠ ∞ := fun n =>
    (hf₂_mem.sub (hf_mem n)).2.ne

  have h_toReal₂ :
      Filter.Tendsto
        (fun n =>
          (eLpNorm (fun x => (f₂ : α → ℂ) x - f n x) 2 μ).toReal)
        Filter.atTop (𝓝 (0 : ℝ)) :=
    (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n =>
          eLpNorm (fun x => (f₂ : α → ℂ) x - f n x) 2 μ)
        h_ne_top₂ h_zero_ne_top).mpr hf₂_tendsto

  have hdist_tendsto₂ :
      Filter.Tendsto (fun n => dist (fnLp n) f₂)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [hdist_eq₂] using h_toReal₂

  have hLp_tendsto₂ :
      Filter.Tendsto fnLp Filter.atTop (𝓝 f₂) :=
    (tendsto_iff_dist_tendsto_zero).2 hdist_tendsto₂

  -- 3. Uniqueness of limits in the Hausdorff space `Lp` implies `f₁ = f₂`.
  have hLp_eq : f₁ = f₂ := by
    haveI : Filter.NeBot (Filter.atTop : Filter ℕ) := by infer_instance
    exact tendsto_nhds_unique hLp_tendsto₁ hLp_tendsto₂

  -- 4. Translate equality in `Lp` back to almost everywhere equality of representatives.
  have h_sub_eq_zero : f₁ - f₂ = (0 : Lp ℂ 2 μ) :=
    sub_eq_zero.mpr hLp_eq

  have h_coe_sub_zero :
      (fun x => (f₁ : α → ℂ) x - (f₂ : α → ℂ) x)
        =ᵐ[μ] fun _ : α => (0 : ℂ) := by
    -- Coe of the difference equals difference of the coes, a.e.
    have h_coe_sub := Lp.coeFn_sub f₁ f₂
    -- Coe of the zero element is a.e. zero.
    have h_zero :
        ((f₁ - f₂ : Lp ℂ 2 μ) : α → ℂ)
          =ᵐ[μ] fun _ : α => (0 : ℂ) := by
      rw [h_sub_eq_zero]
      exact Lp.coeFn_zero (E := ℂ) (p := (2 : ℝ≥0∞)) (μ := μ)
    exact h_coe_sub.symm.trans h_zero

  -- From a.e. vanishing of the difference, deduce a.e. equality.
  exact h_coe_sub_zero.mono (fun x hx => sub_eq_zero.mp hx)

/-- **Signature only**: identification of the L² Fourier–side limit with the
concrete Fourier transform.

If Schwartz functions `φ n` approximate `g` in L² (with the usual L¹ and L²
hypotheses), and `ψLp`, `ψ_lim` are as in `fourierIntegral_memLp_limit`, then
the L² limit `ψ_lim` represents the concrete Fourier transform of `g` almost
everywhere.

This lemma is intended as a reusable packaging of the uniqueness-of-limit
argument that appears in the Plancherel development above.

**Proof strategy**:
1. Use `fourierTransform_tendsto_L2_of_schwartz_approx` to show F[φₙ] → F[g] in L².
2. Note that ψLp n → ψ_lim in L² by assumption.
3. Show that ψLp n =ᵐ F[φₙ].
4. Apply `ae_eq_of_Lp_tendsto_same` to conclude ψ_lim =ᵐ F[g].
-/
lemma fourierIntegral_L2_limit_ae_eq
    {φ : ℕ → SchwartzMap ℝ ℂ} {g : ℝ → ℂ}
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume)
    (hφ_tendsto_L2 : Filter.Tendsto
        (fun n => eLpNorm (fun t : ℝ => g t - φ n t) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)))
    (ψLp : ℕ → Lp ℂ 2 volume) (ψ_lim : Lp ℂ 2 volume)
    (hψLp_def : ∀ n,
        ψLp n =
          (fourierIntegral_memLp_of_schwartz (φ n)).toLp
            (fun ξ : ℝ => fourierIntegral (fun t : ℝ => φ n t) ξ))
    (hψ_tendsto : Filter.Tendsto ψLp Filter.atTop (𝓝 ψ_lim)) :
    (fun ξ : ℝ => (ψ_lim : ℝ → ℂ) ξ)
      =ᵐ[volume] (fun ξ : ℝ => fourierIntegral g ξ) := by
  classical
  -- Strategy: Show that both ψ_lim and F[g] are L² limits of F[φₙ],
  -- then apply uniqueness of L² limits.

  -- Step 1: Establish that F[φₙ] → F[g] in L² using the Plancherel isometry.
  -- This follows from the already-proven `fourierTransform_tendsto_L2_of_schwartz_approx`.
  have hFφ_tendsto_Fg : Filter.Tendsto
      (fun n => eLpNorm
        (fun ξ : ℝ =>
          fourierIntegral (fun t : ℝ => φ n t) ξ - fourierIntegral g ξ)
        2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    -- First use the symmetric version with reversed difference.
    have h :=
      fourierTransform_tendsto_L2_of_schwartz_approx g hg_L1 hg_L2 φ hφ_tendsto_L2
    -- `h` states that ‖F[g] - F[φₙ]‖₂ → 0; we rewrite to ‖F[φₙ] - F[g]‖₂ → 0
    have h_eq :
        (fun n =>
          eLpNorm
            (fun ξ : ℝ =>
              fourierIntegral (fun t : ℝ => φ n t) ξ - fourierIntegral g ξ)
            2 volume)
          = fun n =>
              eLpNorm
                (fun ξ : ℝ =>
                  fourierIntegral g ξ - fourierIntegral (fun t : ℝ => φ n t) ξ)
                2 volume := by
      funext n
      -- Use symmetry of the L² norm under swapping the arguments of the difference.
      simpa using
        (eLpNorm_sub_comm
          (f := fun ξ : ℝ => fourierIntegral (fun t : ℝ => φ n t) ξ)
          (g := fun ξ : ℝ => fourierIntegral g ξ)
          (p := (2 : ℝ≥0∞)) (μ := volume))
    -- Transport the convergence along this pointwise equality.
    simpa [h_eq] using h

  -- Step 2: Show that ψLp n represents F[φₙ] almost everywhere.
  have hψLp_ae_eq : ∀ n, (ψLp n : ℝ → ℂ) =ᵐ[volume]
      (fun ξ : ℝ => fourierIntegral (fun t : ℝ => φ n t) ξ) := by
    intro n
    rw [hψLp_def n]
    simpa using
      (MeasureTheory.MemLp.coeFn_toLp
        (fourierIntegral_memLp_of_schwartz (φ n)))

  -- Step 3: F[g] is in L² (by the result we've already proven).
  have hFg_mem : MemLp (fun ξ : ℝ => fourierIntegral g ξ) 2 volume :=
    fourierIntegral_memLp_L1_L2 hg_L1 hg_L2

  -- Step 4: Apply the uniqueness-of-limit lemma.
  -- Both ψ_lim and F[g] are L² limits of the sequence F[φₙ].
  -- By uniqueness, they must be equal a.e.

  -- First, convert the L² convergence of ψLp to the form needed
  have hψ_tendsto_eLp : Filter.Tendsto
      (fun n => eLpNorm (fun ξ : ℝ => (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ) 2 volume)
      Filter.atTop (𝓝 0) := by
    -- Express the `Lp` distance in terms of the L² `eLpNorm` of the difference.
    have hdist_eq :
        (fun n => dist (ψLp n) ψ_lim)
          = fun n =>
              (eLpNorm
                (fun ξ : ℝ =>
                  (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ)
                2 volume).toReal := by
      funext n
      -- L² membership of the difference.
      have hdiff_mem :
          MemLp (fun ξ : ℝ => (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ) 2 volume :=
        (Lp.memLp ψ_lim).sub (Lp.memLp (ψLp n))
      -- Its `Lp` representative equals the difference of the `Lp` elements.
      have hcalc :
          hdiff_mem.toLp
              (fun ξ : ℝ => (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ)
            = ψ_lim - ψLp n := by
        simpa using MemLp.toLp_sub (Lp.memLp ψ_lim) (Lp.memLp (ψLp n))
      -- Identify the `Lp` norm with the L² `eLpNorm` via `norm_toLp`.
      have hnorm :=
        Lp.norm_toLp (μ := volume)
          (f := fun ξ : ℝ =>
            (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ) hdiff_mem
      calc
        dist (ψLp n) ψ_lim
            = ‖ψLp n - ψ_lim‖ := by
                simp [dist_eq_norm]
        _ = ‖- (ψ_lim - ψLp n)‖ := by
                simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        _ = ‖ψ_lim - ψLp n‖ := by
                simpa using (norm_neg (ψ_lim - ψLp n))
        _ = (eLpNorm
              (fun ξ : ℝ =>
                (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ)
              2 volume).toReal := by
                simpa [hdiff_mem, hcalc] using hnorm

    -- Convergence in `Lp` implies the metric distance tends to zero.
    have hdist_tendsto :
        Filter.Tendsto (fun n => dist (ψLp n) ψ_lim)
          Filter.atTop (𝓝 (0 : ℝ)) :=
      (tendsto_iff_dist_tendsto_zero).1 hψ_tendsto

    -- Hence the real-valued norms of the differences tend to zero.
    have h_toReal :
        Filter.Tendsto
          (fun n =>
            (eLpNorm
              (fun ξ : ℝ =>
                (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ)
              2 volume).toReal)
          Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa [hdist_eq] using hdist_tendsto

    -- The L² norms themselves are finite for each n.
    have h_ne_top :
        ∀ n,
          eLpNorm
              (fun ξ : ℝ =>
                (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ)
              2 volume ≠ ∞ := by
      intro n
      have hdiff_mem :
          MemLp (fun ξ : ℝ => (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ) 2 volume :=
        (Lp.memLp ψ_lim).sub (Lp.memLp (ψLp n))
      exact hdiff_mem.2.ne

    have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp

    -- Convert convergence of `toReal` to convergence in `ℝ≥0∞`.
    exact
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
          (f := fun n =>
            eLpNorm
              (fun ξ : ℝ =>
                (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ)
              2 volume)
          h_ne_top h_zero_ne_top).mp h_toReal

  -- Combine with the a.e. equality to get convergence to F[φₙ]
  have hψ_tendsto_Fφ : Filter.Tendsto
      (fun n => eLpNorm
        (fun ξ : ℝ => (ψ_lim : ℝ → ℂ) ξ - fourierIntegral (fun t : ℝ => φ n t) ξ)
        2 volume)
      Filter.atTop (𝓝 0) := by
    -- For each n, the difference with ψLp n and the difference with F[φₙ]
    -- are equal in L² norm, since ψLp n =ᵐ F[φₙ].
    have h_eq_norm :
        ∀ n,
          eLpNorm
              (fun ξ : ℝ =>
                (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ)
              2 volume
            = eLpNorm
                (fun ξ : ℝ =>
                  (ψ_lim : ℝ → ℂ) ξ
                    - fourierIntegral (fun t : ℝ => φ n t) ξ)
                2 volume := by
      intro n
      -- a.e. equality of integrands
      have h_ae :
          (fun ξ : ℝ =>
              (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ)
            =ᵐ[volume]
            (fun ξ : ℝ =>
              (ψ_lim : ℝ → ℂ) ξ
                - fourierIntegral (fun t : ℝ => φ n t) ξ) := by
        have hψ_eq := hψLp_ae_eq n
        refine hψ_eq.mono ?_
        intro ξ hξ
        -- Rewrite the second term using the a.e. equality.
        simp [hξ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      exact eLpNorm_congr_ae h_ae

    -- Upgrade the convergence using these equalities.
    have h_congr :
        (fun n =>
          eLpNorm
            (fun ξ : ℝ =>
              (ψ_lim : ℝ → ℂ) ξ - (ψLp n : ℝ → ℂ) ξ)
            2 volume)
          =ᶠ[Filter.atTop]
        (fun n =>
          eLpNorm
            (fun ξ : ℝ =>
              (ψ_lim : ℝ → ℂ) ξ
                - fourierIntegral (fun t : ℝ => φ n t) ξ)
            2 volume) :=
      Filter.Eventually.of_forall (fun n => by simp [h_eq_norm n])

    exact hψ_tendsto_eLp.congr' h_congr

  -- Similarly for F[g]
  have hFg_tendsto_Fφ : Filter.Tendsto
      (fun n => eLpNorm
        (fun ξ : ℝ => fourierIntegral g ξ - fourierIntegral (fun t : ℝ => φ n t) ξ)
        2 volume)
      Filter.atTop (𝓝 0) := by
    -- This is the same convergence as `hFφ_tendsto_Fg`, using symmetry of the L² norm.
    have h_eq :
        (fun n =>
          eLpNorm
            (fun ξ : ℝ =>
              fourierIntegral g ξ - fourierIntegral (fun t : ℝ => φ n t) ξ)
            2 volume)
          = fun n =>
              eLpNorm
                (fun ξ : ℝ =>
                  fourierIntegral (fun t : ℝ => φ n t) ξ - fourierIntegral g ξ)
                2 volume := by
      funext n
      -- Swap the arguments in the difference inside the L² norm.
      simpa using
        (eLpNorm_sub_comm
          (f := fun ξ : ℝ => fourierIntegral g ξ)
          (g := fun ξ : ℝ => fourierIntegral (fun t : ℝ => φ n t) ξ)
          (p := (2 : ℝ≥0∞)) (μ := volume))
    simpa [h_eq] using hFφ_tendsto_Fg

  -- Now we have the L² representation of ψ_lim
  have hψ_lim_mem : MemLp (fun ξ : ℝ => (ψ_lim : ℝ → ℂ) ξ) 2 volume := by
    -- Any `Lp` element has a canonical `MemLp` representative.
    simpa using (Lp.memLp ψ_lim)

  -- Create the Lp version of F[g]
  set Fg_Lp : Lp ℂ 2 volume := hFg_mem.toLp (fun ξ => fourierIntegral g ξ)

  -- Convert hFg_tendsto_Fφ to use Fg_Lp's representative
  have hFg_Lp_tendsto_Fφ : Filter.Tendsto
      (fun n => eLpNorm
        (fun ξ : ℝ => (Fg_Lp : ℝ → ℂ) ξ - fourierIntegral (fun t : ℝ => φ n t) ξ)
        2 volume)
      Filter.atTop (𝓝 0) := by
    -- Fg_Lp's representative equals fourierIntegral g a.e., so the norms are equal
    have hFg_Lp_ae : (Fg_Lp : ℝ → ℂ) =ᵐ[volume] (fun ξ => fourierIntegral g ξ) := by
      exact MemLp.coeFn_toLp hFg_mem
    -- For each n, the L² norms with `Fg_Lp` and with `fourierIntegral g` coincide.
    have h_eq_norm :
        ∀ n,
          eLpNorm
              (fun ξ : ℝ =>
                fourierIntegral g ξ - fourierIntegral (fun t : ℝ => φ n t) ξ)
              2 volume
            = eLpNorm
                (fun ξ : ℝ =>
                  (Fg_Lp : ℝ → ℂ) ξ
                    - fourierIntegral (fun t : ℝ => φ n t) ξ)
                2 volume := by
      intro n
      -- a.e. equality of the first term in the difference
      have h_ae :
          (fun ξ : ℝ =>
              fourierIntegral g ξ - fourierIntegral (fun t : ℝ => φ n t) ξ)
            =ᵐ[volume]
            (fun ξ : ℝ =>
              (Fg_Lp : ℝ → ℂ) ξ
                - fourierIntegral (fun t : ℝ => φ n t) ξ) := by
        refine hFg_Lp_ae.mono ?_
        intro ξ hξ
        simp [hξ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      exact eLpNorm_congr_ae h_ae

    -- Transport the convergence `hFg_tendsto_Fφ` along this equality.
    have h_congr :
        (fun n =>
          eLpNorm
            (fun ξ : ℝ =>
              fourierIntegral g ξ - fourierIntegral (fun t : ℝ => φ n t) ξ)
            2 volume)
          =ᶠ[Filter.atTop]
        (fun n =>
          eLpNorm
            (fun ξ : ℝ =>
              (Fg_Lp : ℝ → ℂ) ξ
                - fourierIntegral (fun t : ℝ => φ n t) ξ)
            2 volume) :=
      Filter.Eventually.of_forall (fun n => by simp [h_eq_norm n])

    exact hFg_tendsto_Fφ.congr' h_congr

  -- Apply uniqueness of L² limits
  have h_unique := ae_eq_of_Lp_tendsto_same
    (fun n ξ => fourierIntegral (fun t : ℝ => φ n t) ξ)
    ψ_lim
    Fg_Lp
    (fun n => fourierIntegral_memLp_of_schwartz (φ n))
    hψ_tendsto_Fφ
    hFg_Lp_tendsto_Fφ

  -- Finally, combine with the fact that Fg_Lp =ᵐ F[g]
  have hFg_Lp_ae : (Fg_Lp : ℝ → ℂ) =ᵐ[volume] (fun ξ => fourierIntegral g ξ) := by
    exact MemLp.coeFn_toLp hFg_mem

  exact h_unique.trans hFg_Lp_ae

end Frourio
