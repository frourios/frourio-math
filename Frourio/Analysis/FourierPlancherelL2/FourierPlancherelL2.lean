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

/-- L² convergence of Gaussian frequency cutoffs (skeleton).

For `w ∈ L²(ℝ)`, consider the Gaussian cutoff
`GR_R(ξ) = exp(-π (ξ / R)^2)` on the frequency side and the modified functions
`ξ ↦ GR_R(ξ) · w(ξ)`. As `R → ∞`, these converge to `w` in L².

This lemma records the precise L² convergence statement needed in
`gaussian_inverseFourier_cutoff_pointwise`.  The proof uses the
pointwise convergence `GR_R(ξ) → 1`, uniform L²-boundedness of the cutoffs,
and dominated convergence in L²; it is deferred to the Fourier–Plancherel L²
core development. -/
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

/-- **Signature only**: the Fourier transform on Schwartz space has dense range in L².

Equivalently, the closure of the image of `fourierTransformDense : Schwartz → L²`
is all of `Lp ℂ 2`.  This is the operator‑theoretic formulation of
“Fourier transforms of Schwartz functions are dense on the frequency side”. -/
lemma fourierTransformDense_denseRange :
    DenseRange (fourierTransformDense) := by
  classical
  sorry

/-- **Signature only**: approximation of an L² frequency-side function by Fourier transforms
of Schwartz functions.

Given `g ∈ L²(ℝ)` on the frequency side, there exists for every `ε > 0` a Schwartz function
`ψ` on the time side whose Fourier transform approximates `g` in L² to accuracy `ε`.  This is
the concrete `MemLp`/`eLpNorm` version of `fourierTransformDense_denseRange`, and will be
used in `schwartz_fourier_dense_in_L2` (Application 層) to implement the core approximation
step `h_schwartz_approx_core`. -/
lemma exists_schwartz_fourier_L2_approx
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    ∀ ε > 0, ∃ ψ : SchwartzMap ℝ ℂ,
      eLpNorm (fun ξ => g ξ - Frourio.fourierIntegral (fun t => ψ t) ξ) 2 volume
        < ENNReal.ofReal ε := by
  classical
  sorry

/-- Schwartz 関数の Fourier 変換による L² の密度定理。

任意の `w ∈ L²(ℝ, ℂ)` に対して、Schwartz 関数の Fourier 変換で
任意の精度で L² 近似できる。

この定理は `inverseFourier_isometry_on_closure` を実用的に使うために必須である。
証明方針：
1. L² の dense な部分集合（compact support を持つ連続関数など）から始める
2. Fourier 変換の等長性を使って時間側での Schwartz 密度を周波数側に転送する
3. または Mathlib の既存結果を利用する

TODO: この証明を実装する（優先度：高） -/
lemma schwartz_fourier_dense_in_L2
    (w : ℝ → ℂ) (hw : MemLp w 2 volume) :
    ∀ ε > 0, ∃ ψ : SchwartzMap ℝ ℂ,
      eLpNorm (fun ξ => w ξ - Frourio.fourierIntegral (fun t => ψ t) ξ) 2 volume
        < ENNReal.ofReal ε := by
  classical
  intro ε hε

  -- Step 1: approximate `w` in L² by a “core” dense subspace of
  -- smooth, compactly supported functions (in particular, continuous
  -- and compactly supported).
  have h_core_approx :
      ∃ g : ℝ → ℂ,
        Continuous g ∧
        HasCompactSupport g ∧
        MemLp g 2 volume ∧
        eLpNorm (fun ξ => w ξ - g ξ) 2 volume
          < ENNReal.ofReal (ε / 2) := by
    -- Use the dedicated L²-density lemma for smooth compactly supported functions.
    have hε_half_pos : 0 < ε / 2 := half_pos hε
    obtain ⟨g, hg_cpt, hg_smooth, hg_close⟩ :=
      smooth_compactly_supported_dense_L2 (f_L2 := w) hw (ε := ε / 2) hε_half_pos
    have hg_cont : Continuous g := hg_smooth.continuous
    have hg_memLp : MemLp g 2 volume :=
      hg_cont.memLp_of_hasCompactSupport (μ := volume) (p := (2 : ℝ≥0∞)) hg_cpt
    refine ⟨g, hg_cont, hg_cpt, hg_memLp, ?_⟩
    simpa [Pi.sub_def] using hg_close
  obtain ⟨g, hg_cont, hg_cpt, hg_L2, hwg_L2⟩ := h_core_approx

  -- Step 2 (skeleton): approximate the core function `g` by Fourier transforms
  -- of Schwartz functions on the frequency side.
  -- Conceptually, we apply the Fourier–Plancherel isometry to move to the
  -- time side, use Schwartz density there (e.g. `schwartz_dense_L1_L2_simultaneous`
  -- for `n = 1`), and then come back via the isometry.
  have h_schwartz_approx_core :
      ∃ ψ : SchwartzMap ℝ ℂ,
        eLpNorm (fun ξ =>
          g ξ - Frourio.fourierIntegral (fun t => ψ t) ξ) 2 volume
          < ENNReal.ofReal (ε / 2) := by
    -- Use the core approximation lemma that any L² frequency-side function `g`
    -- can be approximated in L² by Fourier transforms of Schwartz functions.
    have h_core := exists_schwartz_fourier_L2_approx g hg_L2
    have hε_half_pos : 0 < ε / 2 := half_pos hε
    exact h_core (ε / 2) hε_half_pos
  rcases h_schwartz_approx_core with ⟨ψ, hψ_core⟩

  -- Step 3 (skeleton): combine the two approximations via the triangle inequality
  -- in L² to obtain the desired ε-approximation of `w` by `F[ψ]`.
  have h_triangle :
      eLpNorm (fun ξ =>
          w ξ - Frourio.fourierIntegral (fun t => ψ t) ξ) 2 volume
        ≤ eLpNorm (fun ξ => w ξ - g ξ) 2 volume
            + eLpNorm (fun ξ =>
                g ξ - Frourio.fourierIntegral (fun t => ψ t) ξ) 2 volume := by
    -- Apply the L² triangle inequality in the form `eLpNorm_add_le`
    -- to the decomposition `w - F[ψ] = (w - g) + (g - F[ψ])`.
    have h_meas_w : AEStronglyMeasurable w volume := hw.aestronglyMeasurable
    have h_meas_g : AEStronglyMeasurable g volume := hg_L2.aestronglyMeasurable
    have h_mem_F :
        MemLp (fun ξ : ℝ =>
          Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ) 2 volume :=
      fourierIntegral_memLp_of_schwartz ψ
    have h_meas_F :
        AEStronglyMeasurable (fun ξ : ℝ =>
          Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ) volume :=
      h_mem_F.aestronglyMeasurable

    have h_meas1 :
        AEStronglyMeasurable (fun ξ : ℝ => w ξ - g ξ) volume :=
      h_meas_w.sub h_meas_g
    have h_meas2 :
        AEStronglyMeasurable
          (fun ξ : ℝ =>
            g ξ - Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ) volume :=
      h_meas_g.sub h_meas_F

    have h_eq :
        (fun ξ : ℝ =>
          w ξ - Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ)
          = fun ξ : ℝ =>
              (w ξ - g ξ)
                + (g ξ - Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ) := by
      funext ξ
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

    have h :=
      eLpNorm_add_le (μ := volume) (p := (2 : ℝ≥0∞))
        (f := fun ξ : ℝ => w ξ - g ξ)
        (g := fun ξ : ℝ =>
          g ξ - Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ)
        h_meas1 h_meas2 (show (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) by norm_num)
    simpa [h_eq] using h

  -- Step 4 (skeleton): numerically bound the right-hand side by ε using the
  -- two < ε/2 estimates and the positivity of ε.
  have h_sum_lt :
      eLpNorm (fun ξ => w ξ - g ξ) 2 volume
        + eLpNorm (fun ξ =>
            g ξ - Frourio.fourierIntegral (fun t => ψ t) ξ) 2 volume
          < ENNReal.ofReal ε := by
    -- Use `hwg_L2` and `hψ_core`, together with
    -- `ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε`.
    have h_half_nonneg : 0 ≤ ε / 2 := (half_pos hε).le
    have h_half_sum :
        ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
          = ENNReal.ofReal ε := by
      have h_eq : ε / 2 + ε / 2 = ε := by ring
      simpa [h_eq] using
        (ENNReal.ofReal_add h_half_nonneg h_half_nonneg).symm

    have h_lt_half_sum :
        eLpNorm (fun ξ => w ξ - g ξ) 2 volume
            + eLpNorm (fun ξ =>
                g ξ - Frourio.fourierIntegral (fun t => ψ t) ξ) 2 volume
          < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hwg_L2 hψ_core

    have h_le_sum :
        ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
          ≤ ENNReal.ofReal ε :=
      le_of_eq h_half_sum

    exact lt_of_lt_of_le h_lt_half_sum h_le_sum

  -- Final step: choose this ψ and close the ε-estimate.
  refine ⟨ψ, ?_⟩
  -- The desired bound follows from `h_triangle` and `h_sum_lt`.
  -- One applies `lt_of_le_of_lt h_triangle h_sum_lt`.
  exact lt_of_le_of_lt h_triangle h_sum_lt

/-- Gaussian cutoff された L² 関数の Schwartz 近似可能性。

`w ∈ L²` に対して、Gaussian cutoff された関数
`wR ξ = exp(-π(ξ/R)²) · w ξ` は Schwartz 関数の Fourier 変換で近似可能である。

これは `inverseFourier_isometry_on_closure` を Gaussian cutoff に適用するために必要。 -/
lemma gaussian_cutoff_schwartz_approx
    {w : ℝ → ℂ} (hw : MemLp w 2 volume) (R : ℝ) :
    ∀ ε > 0, ∃ ψ : SchwartzMap ℝ ℂ,
      eLpNorm (fun ξ =>
        (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ) * w ξ
          - Frourio.fourierIntegral (fun t => ψ t) ξ) 2 volume
        < ENNReal.ofReal ε := by
  classical
  intro ε hε

  -- Frequency-side Gaussian cutoff applied to w.
  set wR : ℝ → ℂ :=
    fun ξ => (Real.exp (-(Real.pi) * (ξ / R)^2) : ℂ) * w ξ

  -- Step 1 (skeleton): show that the cutoff `wR` still belongs to L².
  have h_mem_wR : MemLp wR 2 volume := by
    -- Measurability of `w`.
    have h_meas_w : AEStronglyMeasurable w volume := hw.aestronglyMeasurable

    -- The Gaussian factor is continuous hence a.e. strongly measurable.
    have h_meas_gauss :
        AEStronglyMeasurable
          (fun ξ : ℝ =>
            (Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)) volume := by
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
      exact h_cont_complex.aestronglyMeasurable

    -- Hence `wR` is a.e. strongly measurable.
    have h_meas_wR : AEStronglyMeasurable wR volume := by
      have h_meas_prod :
          AEStronglyMeasurable
            (fun ξ : ℝ =>
              (Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ) * w ξ) volume :=
        h_meas_gauss.mul h_meas_w
      simpa [wR] using h_meas_prod

    -- Pointwise bound ‖wR ξ‖ ≤ ‖w ξ‖ via ‖Gaussian‖ ≤ 1.
    have h_pointwise_le :
        ∀ ξ : ℝ, ‖wR ξ‖ ≤ ‖w ξ‖ := by
      intro ξ
      -- Bound the Gaussian factor.
      have h_norm_gauss_le_one :
          ‖(Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)‖ ≤ 1 := by
        have h_nonpos :
            -(Real.pi) * (ξ / R) ^ 2 ≤ 0 := by
          have h1 : -Real.pi ≤ (0 : ℝ) :=
            neg_nonpos.mpr (le_of_lt Real.pi_pos)
          have h2 : (0 : ℝ) ≤ (ξ / R) ^ 2 := sq_nonneg _
          exact mul_nonpos_of_nonpos_of_nonneg h1 h2
        have h_le_one :
            Real.exp (-(Real.pi) * (ξ / R) ^ 2) ≤ 1 := by
          have := (Real.exp_le_one_iff).2 h_nonpos
          simpa using this
        have h_nonneg_exp :
            0 ≤ Real.exp (-(Real.pi) * (ξ / R) ^ 2) :=
          Real.exp_nonneg _
        have h_norm_real :
            ‖(Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)‖
              = Real.exp (-(Real.pi) * (ξ / R) ^ 2) := by
          rw [Complex.norm_real]
          exact abs_of_nonneg h_nonneg_exp
        calc
          ‖(Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)‖
              = Real.exp (-(Real.pi) * (ξ / R) ^ 2) := h_norm_real
          _ ≤ 1 := h_le_one
      -- Use the bound to control the product.
      have hmul :
          ‖wR ξ‖
            = ‖(Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)‖ * ‖w ξ‖ := by
        simp [wR, norm_mul]
      calc
        ‖wR ξ‖
            = ‖(Real.exp (-(Real.pi) * (ξ / R) ^ 2) : ℂ)‖ * ‖w ξ‖ := hmul
        _ ≤ 1 * ‖w ξ‖ := by
              have := mul_le_mul_of_nonneg_right
                h_norm_gauss_le_one (norm_nonneg (w ξ))
              simpa [one_mul] using this
        _ = ‖w ξ‖ := by simp [one_mul]

    -- Use monotonicity of the L² norm under pointwise domination.
    have h_L2_le :
        eLpNorm wR 2 volume
          ≤ eLpNorm w 2 volume := by
      refine eLpNorm_mono ?_
      intro ξ
      exact h_pointwise_le ξ

    -- `w ∈ L²` implies `eLpNorm w 2 < ∞`, hence also for `wR`.
    have hw_fin : eLpNorm w 2 volume < ∞ := hw.2
    have hwR_fin :
        eLpNorm wR 2 volume < ∞ :=
      lt_of_le_of_lt h_L2_le hw_fin
    exact ⟨h_meas_wR, hwR_fin⟩

  -- Step 2: apply the global Schwartz density theorem to `wR`.
  obtain ⟨ψ, hψ_approx⟩ :=
    schwartz_fourier_dense_in_L2 (w := wR) h_mem_wR ε hε

  -- Step 3: rewrite in terms of the original expression.
  refine ⟨ψ, ?_⟩
  simpa [wR] using hψ_approx

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

/-- L² continuity of the inverse Fourier transform for `L¹ ∩ L²` frequency-side data
(signature only).

If `(fn n)` is a sequence of functions that are both integrable and in `L²`, and
`fn n → w` in `L²` on the frequency side, then the inverse Fourier integrals
`invF(fn n)` converge to `invF(w)` in `L²` on the time side.

This lemma is intended to be proved in the core Fourier–Plancherel development
using the operator-theoretic construction of the inverse transform, without
using Gaussian cutoffs or the pairing identity from the application layer. -/
lemma inverseFourier_tendsto_L2_L1_L2
    {fn : ℕ → ℝ → ℂ} {w : ℝ → ℂ}
    (hfn_L1 : ∀ n, Integrable (fn n) volume)
    (hfn_L2 : ∀ n, MemLp (fn n) 2 volume)
    (hw_L2 : MemLp w 2 volume)
    (h_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun ξ => fn n ξ - w ξ) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun n =>
      eLpNorm (fun t =>
        Real.fourierIntegralInv (fun ξ => fn n ξ) t
          - Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  -- Proof to be supplied in the core L² theory.
  -- It should proceed by approximating both `fn n` and `w` by Fourier transforms
  -- of Schwartz functions and applying the L² isometry for the inverse transform.
  sorry

/-- L² membership of the inverse Fourier transform for `L¹ ∩ L²` data (signature only).

If `f ∈ L¹ ∩ L²`, then its inverse Fourier integral belongs to `L²`.  The proof is
part of the core Fourier–Plancherel theory and is deferred. -/
lemma inverseFourierIntegral_memLp_L1_L2
    {f : ℝ → ℂ} (hf_L1 : Integrable f) (hf_L2 : MemLp f 2 volume) :
    MemLp (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => f ξ) t) 2 volume := by
  classical
  -- Proof deferred to the core Plancherel development.
  sorry

/-- L² membership of the inverse Fourier transform for general L² frequency-side data
(signature only).

If `w ∈ L²`, then its inverse Fourier integral also belongs to `L²`.  This is a
consequence of the extension of the inverse transform as an L² isometry on the
closure of the Schwartz range and can be proved using Schwartz approximation. -/
lemma inverseFourierIntegral_memLp_L2
    {w : ℝ → ℂ} (hw : MemLp w 2 volume) :
    MemLp (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => w ξ) t) 2 volume := by
  classical
  -- Proof deferred; it can be obtained, for example, from
  -- `inverseFourierIntegral_memLp_of_schwartz_approx` together with
  -- `schwartz_fourier_dense_in_L2`.
  sorry

-- Helper lemmas to support the pairing identity for inverse Fourier.
-- First, collect the helper lemmas used in the Gaussian cutoff proof.

-- Pairing identity for integrable frequency-side functions.
-- moved earlier

-- Gaussian L² membership on the frequency side.
-- moved earlier

-- Integrability of Gaussian cutoff times an L² function.
-- moved earlier

-- Dominated convergence for Gaussian cutoffs in the Fourier-side pairing.
-- moved earlier

-- Dominated convergence for the time-side pairing under Gaussian frequency cutoffs
-- moved earlier

/-- Duality identity: pairing of the inverse Fourier integral of an L² function with a
Schwartz test function equals the pairing of the function with the Fourier transform of
the test function. Implemented via Gaussian cutoff approximation and pairing continuity.
-/
lemma inverseFourier_pairing_schwartz
    {w : ℝ → ℂ} (hw : MemLp w 2 volume) (φ : SchwartzMap ℝ ℂ) :
    ∫ t : ℝ, (Real.fourierIntegralInv (fun ξ : ℝ => w ξ) t) * (conj (φ t)) ∂volume
      = ∫ ξ : ℝ, (w ξ) * (conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ)) ∂volume := by
  classical
  -- Step 0: basic data.
  -- Schwartz test functions are in L².
  have hφ_L2 : MemLp (fun t : ℝ => φ t) 2 volume :=
    SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)

  -- Step 1 (skeleton): approximate `w` in L² by integrable L¹∩L² functions.
  -- We obtain a sequence `(fn n)` with:
  --  • each `fn n` integrable and in L²,
  --  • `fn n → w` in L² as n → ∞.
  have h_approx :
      ∃ fn : ℕ → ℝ → ℂ,
        (∀ n, Integrable (fn n) volume) ∧
        (∀ n, MemLp (fn n) 2 volume) ∧
        Filter.Tendsto (fun n =>
          eLpNorm (fun ξ : ℝ => w ξ - fn n ξ) 2 volume)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    -- Use the smooth, compactly supported L² approximation sequence from Core0.
    obtain ⟨ψ, hψ_support, hψ_smooth, hψ_tendsto⟩ :=
      smooth_compactly_supported_dense_L2_sequence (f := w) hw
    -- Define fn n := ψ n.
    refine ⟨ψ, ?_, ?_, ?_⟩
    · -- Each ψ n is integrable by continuity and compact support.
      intro n
      have hcont : Continuous (ψ n) := (hψ_smooth n).continuous
      exact hcont.integrable_of_hasCompactSupport (hψ_support n)
    · -- Each ψ n lies in L² by the same reasoning.
      intro n
      have hcont : Continuous (ψ n) := (hψ_smooth n).continuous
      exact
        hcont.memLp_of_hasCompactSupport (μ := volume) (p := (2 : ℝ≥0∞))
          (hψ_support n)
    · -- L² convergence of ψ n to w is provided by the core lemma.
      exact hψ_tendsto
  obtain ⟨fn, hfn_L1, hfn_L2, hfn_tendsto_L2⟩ := h_approx

  -- Step 2: for each approximant `fn n`, apply the L¹ pairing lemma.
  -- Since `fn n` is integrable, the inverse Fourier pairing identity holds.
  have h_pair_n : ∀ n : ℕ,
      ∫ t : ℝ,
          Real.fourierIntegralInv (fun ξ : ℝ => fn n ξ) t * conj (φ t) ∂volume
        = ∫ ξ : ℝ,
          fn n ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume := by
    intro n
    exact inverseFourier_pairing_schwartz_L1 (f := fn n) (hf := hfn_L1 n) φ

  -- Step 3 (frequency side, skeleton): show that the right-hand side converges
  -- to the desired frequency-side pairing as `n → ∞`.
  have h_freq_tendsto :
      Filter.Tendsto (fun n : ℕ =>
          ∫ ξ : ℝ,
            fn n ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)
        Filter.atTop
        (𝓝 (∫ ξ : ℝ,
          w ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)) := by
    -- Apply the generic L² pairing continuity lemma on the frequency side with
    -- test function given by the Fourier transform of φ.
    have h_base :
        Filter.Tendsto (fun n : ℕ =>
            ∫ ξ : ℝ,
              fn n ξ * conj ((fourierAsSchwartzFunction φ) ξ) ∂volume)
          Filter.atTop
          (𝓝 (∫ ξ : ℝ,
            w ξ * conj ((fourierAsSchwartzFunction φ) ξ) ∂volume)) :=
      pairing_tendsto_L2_left
        (fn := fn) (f := w)
        (hfn_L2 := hfn_L2) (hf_L2 := hw)
        (φ := fourierAsSchwartzFunction φ)
        (hf_tendsto := hfn_tendsto_L2)

    -- Identify `fourierAsSchwartzFunction φ` with the explicit Fourier integral.
    have h_coe :
        (fun ξ : ℝ => (fourierAsSchwartzFunction φ) ξ)
          = fun ξ : ℝ =>
              Frourio.fourierIntegral (fun t : ℝ => φ t) ξ := by
      funext ξ
      simpa [fourierAsSchwartzFunction]
        using
          (Schwartz.fourierIntegral_eq_fourierTransform (f := φ) (ξ := ξ)).symm

    -- Rewrite both the approximating pairings and the limit in terms of F[φ].
    have h_int_eq_n :
        (fun n : ℕ =>
          ∫ ξ : ℝ,
            fn n ξ * conj ((fourierAsSchwartzFunction φ) ξ) ∂volume)
          =
        fun n : ℕ =>
          ∫ ξ : ℝ,
            fn n ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume := by
      funext n
      have h_integrand :
          (fun ξ : ℝ =>
            fn n ξ * conj ((fourierAsSchwartzFunction φ) ξ))
            =
          fun ξ : ℝ =>
            fn n ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) := by
        funext ξ; simp [h_coe]
      simp [h_integrand]

    have h_int_eq_lim :
        ∫ ξ : ℝ,
            w ξ * conj ((fourierAsSchwartzFunction φ) ξ) ∂volume
          =
        ∫ ξ : ℝ,
            w ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume := by
      have h_integrand :
          (fun ξ : ℝ =>
            w ξ * conj ((fourierAsSchwartzFunction φ) ξ))
            =
          fun ξ : ℝ =>
            w ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) := by
        funext ξ; simp [h_coe]
      simp [h_integrand]

    -- Transfer the convergence statement through these identifications.
    have h_base' :
        Filter.Tendsto (fun n : ℕ =>
            ∫ ξ : ℝ,
              fn n ξ * conj ((fourierAsSchwartzFunction φ) ξ) ∂volume)
          Filter.atTop
          (𝓝 (∫ ξ : ℝ,
            w ξ * conj ((fourierAsSchwartzFunction φ) ξ) ∂volume)) :=
      h_base
    simpa [h_int_eq_n, h_int_eq_lim] using h_base'

  -- Step 4 (time side, skeleton): show that the left-hand side converges to the
  -- desired time-side pairing as `n → ∞`.
  have h_time_tendsto :
      Filter.Tendsto (fun n : ℕ =>
          ∫ t : ℝ,
            Real.fourierIntegralInv (fun ξ : ℝ => fn n ξ) t * conj (φ t) ∂volume)
        Filter.atTop
        (𝓝 (∫ t : ℝ,
          Real.fourierIntegralInv (fun ξ : ℝ => w ξ) t * conj (φ t) ∂volume)) := by
    -- Use the core L² continuity of the inverse Fourier transform to upgrade
    -- frequency-side L² convergence `fn n → w` to time-side L² convergence
    -- `invF(fn n) → invF(w)`.
    have h_time_L2 :
        Filter.Tendsto (fun n =>
            eLpNorm (fun t =>
              Real.fourierIntegralInv (fun ξ => fn n ξ) t
                - Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      -- Convert from `w - fn n` to `fn n - w` order
      -- Use the fact that ‖f - g‖₂ = ‖g - f‖₂
      have h_tendsto_swap : Filter.Tendsto (fun n =>
          eLpNorm (fun ξ => fn n ξ - w ξ) 2 volume)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
        have h_norm_symm : ∀ n, eLpNorm (fun ξ => fn n ξ - w ξ) 2 volume
            = eLpNorm (fun ξ => w ξ - fn n ξ) 2 volume := by
          intro n
          have h_neg : (fun ξ => fn n ξ - w ξ) = -(fun ξ => w ξ - fn n ξ) := by
            ext ξ; simp [Pi.neg_apply]
          rw [h_neg, eLpNorm_neg]
        simp_rw [h_norm_symm]
        exact hfn_tendsto_L2
      exact inverseFourier_tendsto_L2_L1_L2
        (fn := fn) (w := w)
        (hfn_L1 := hfn_L1) (hfn_L2 := hfn_L2)
        (hw_L2 := hw) (h_tendsto := h_tendsto_swap)

    -- L² membership of the time-side inverse transforms.
    have h_inv_fn_L2 :
        ∀ n, MemLp (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ : ℝ => fn n ξ) t) 2 volume :=
      fun n =>
        inverseFourierIntegral_memLp_L1_L2 (hf_L1 := hfn_L1 n) (hf_L2 := hfn_L2 n)

    have h_inv_w_L2 :
        MemLp (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ : ℝ => w ξ) t) 2 volume :=
      inverseFourierIntegral_memLp_L2 (hw := hw)

    -- Convert h_time_L2 to the order expected by pairing_tendsto_L2_left
    have h_time_L2_swap : Filter.Tendsto (fun n =>
          eLpNorm (fun t =>
            Real.fourierIntegralInv (fun ξ => w ξ) t
              - Real.fourierIntegralInv (fun ξ => fn n ξ) t) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have h_norm_symm : ∀ n, eLpNorm (fun t =>
            Real.fourierIntegralInv (fun ξ => w ξ) t
              - Real.fourierIntegralInv (fun ξ => fn n ξ) t) 2 volume
          = eLpNorm (fun t =>
            Real.fourierIntegralInv (fun ξ => fn n ξ) t
              - Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume := by
        intro n
        have h_neg : (fun t => Real.fourierIntegralInv (fun ξ => w ξ) t
              - Real.fourierIntegralInv (fun ξ => fn n ξ) t)
            = -(fun t => Real.fourierIntegralInv (fun ξ => fn n ξ) t
              - Real.fourierIntegralInv (fun ξ => w ξ) t) := by
          ext t; simp [Pi.neg_apply]
        rw [h_neg, eLpNorm_neg]
      simp_rw [h_norm_symm]
      exact h_time_L2

    -- Apply the generic L² pairing continuity lemma on the time side with test
    -- function φ.
    exact
      pairing_tendsto_L2_left
        (fn := fun n t =>
          Real.fourierIntegralInv (fun ξ : ℝ => fn n ξ) t)
        (f := fun t =>
          Real.fourierIntegralInv (fun ξ : ℝ => w ξ) t)
        (hfn_L2 := h_inv_fn_L2)
        (hf_L2 := h_inv_w_L2)
        (φ := φ)
        (hf_tendsto := h_time_L2_swap)

  -- Step 5: identify the limits using the pointwise pairing identity for each n.
  have h_seq_freq :
      Filter.Tendsto (fun n : ℕ =>
          ∫ ξ : ℝ,
            fn n ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)
        Filter.atTop
        (𝓝 (∫ ξ : ℝ,
          w ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)) :=
    h_freq_tendsto

  have h_seq_time :
      Filter.Tendsto (fun n : ℕ =>
          ∫ t : ℝ,
            Real.fourierIntegralInv (fun ξ : ℝ => fn n ξ) t * conj (φ t) ∂volume)
        Filter.atTop
        (𝓝 (∫ t : ℝ,
          Real.fourierIntegralInv (fun ξ : ℝ => w ξ) t * conj (φ t) ∂volume)) :=
    h_time_tendsto

  -- The two sequences are equal termwise by `h_pair_n`, hence their limits coincide.
  have h_limits_equal :
      ∫ t : ℝ,
          Real.fourierIntegralInv (fun ξ : ℝ => w ξ) t * conj (φ t) ∂volume
        = ∫ ξ : ℝ,
          w ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume := by
    -- Use uniqueness of limits in a Hausdorff space: the two pairings are the
    -- limits of the same sequence indexed by `n`, given pointwise by `h_pair_n`.
    -- First, rewrite the frequency-side convergence as convergence of the
    -- time-side sequence using the pointwise identities.
    have h_seq_freq_as_time :
        Filter.Tendsto (fun n : ℕ =>
            ∫ t : ℝ,
              Real.fourierIntegralInv (fun ξ : ℝ => fn n ξ) t * conj (φ t) ∂volume)
          Filter.atTop
          (𝓝 (∫ ξ : ℝ,
            w ξ * conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)) := by
      -- For each n, the time- and frequency-side pairings agree by `h_pair_n`.
      exact
        h_seq_freq.congr'
          (Filter.Eventually.of_forall (fun n => (h_pair_n n).symm))

    -- Now uniqueness of limits in a Hausdorff space (`ℂ`) gives equality of
    -- the two candidate limits for the same time-side sequence.
    exact tendsto_nhds_unique h_seq_time h_seq_freq_as_time

  -- Final step: the desired pairing identity is exactly `h_limits_equal`.
  exact h_limits_equal

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

/-- From vanishing Schwartz pairings to L² a.e. equality.

If `g ∈ L²` and for every Schwartz `φ` the pairing against `f - g` vanishes, then
`f ∈ L²` and `f = g` almost everywhere. -/
lemma memLp_and_ae_eq_of_schwartz_pairing
    {f g : ℝ → ℂ}
    (hg : MemLp g 2 volume)
    (hpair : ∀ φ : SchwartzMap ℝ ℂ,
      ∫ t, (f t) * conj (φ t) ∂volume
        = ∫ t, (g t) * conj (φ t) ∂volume) :
    MemLp f 2 volume ∧ f =ᵐ[volume] g := by
  classical
  -- Step 1: prove `f ∈ L²` using a uniform pairing bound and L² duality.
  -- The constant controlling the pairings is the L² norm of `g`.
  let C : ℝ := (eLpNorm (fun t => g t) 2 volume).toReal
  have hC_nonneg : 0 ≤ C := by
    have := ENNReal.toReal_nonneg (a := eLpNorm (fun t => g t) 2 volume)
    simp [C]

  have hpair_bound :
      ∀ φ : SchwartzMap ℝ ℂ,
        ‖∫ t, f t * conj (φ t) ∂volume‖
          ≤ C * (eLpNorm (fun t => φ t) 2 volume).toReal := by
    intro φ
    -- Identify the pairing with `f` and `g`.
    have h_eq := hpair φ

    -- Express the RHS pairing with `g` in the `starRingEnd` form needed for
    -- the `integral_mul_star_eq_inner` lemma, and then as an inner product.
    have h_integral_eq_g :
        ∫ t, g t * conj (φ t) ∂volume
          =
        ∫ t, g t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume := by
      have hfun :
          (fun t : ℝ => g t * conj (φ t)) =
            fun t : ℝ =>
              g t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) := by
        funext t
        rfl
      simp [hfun]

    -- Use the L² inner product representation for the pairing with `g`.
    have h_inner :
        ∫ t, g t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume
          =
        @inner ℂ (Lp ℂ 2 volume) _
          ((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
            (fun x => φ x))
          (hg.toLp g) :=
      integral_mul_star_eq_inner (hg_mem := hg) (φ := φ)

    -- Cauchy–Schwarz in L² gives the desired bound for the inner product.
    have h_cs :
        ‖@inner ℂ (Lp ℂ 2 volume) _
            ((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
              (fun x => φ x))
            (hg.toLp g)‖
          ≤
        ‖((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
              (fun x => φ x))‖
          * ‖hg.toLp g‖ :=
      norm_inner_le_norm _ _

    -- Combine everything to bound the pairing with `g`.
    have h_bound_g :
        ‖∫ t, g t * conj (φ t) ∂volume‖
          ≤ C * (eLpNorm (fun t => φ t) 2 volume).toReal := by
      have :
          ‖∫ t, g t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume‖
            ≤ C * (eLpNorm (fun t => φ t) 2 volume).toReal := by
        -- Rewrite via the inner product and apply Cauchy–Schwarz.
        have h_main :
            ‖∫ t, g t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume‖
              ≤
            (eLpNorm (fun t => φ t) 2 volume).toReal
              * (eLpNorm (fun t => g t) 2 volume).toReal := by
          calc
            ‖∫ t, g t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume‖
                = ‖@inner ℂ (Lp ℂ 2 volume) _
                      ((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
                        (fun x => φ x))
                      (hg.toLp g)‖ := by
                      simp [h_inner]
            _ ≤ ‖((SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
                    (fun x => φ x))‖ * ‖hg.toLp g‖ := h_cs
            _ = (eLpNorm (fun t => φ t) 2 volume).toReal
                  * (eLpNorm (fun t => g t) 2 volume).toReal := by
                    simp [mul_comm]
        -- Our chosen constant is exactly the L² norm of `g`.
        have hC : C = (eLpNorm (fun t => g t) 2 volume).toReal := rfl
        simpa [hC, mul_comm, mul_left_comm, mul_assoc] using h_main
      simpa [h_integral_eq_g] using this

    -- Transport the bound from `g` to `f` using the assumed equality of pairings.
    have h_eq' :
        ∫ t, f t * conj (φ t) ∂volume
          = ∫ t, g t * conj (φ t) ∂volume := h_eq
    simpa [h_eq'] using h_bound_g

  -- Apply the abstract L² duality lemma (skeleton) to deduce `f ∈ L²`.
  have hf : MemLp f 2 volume :=
    memLp_two_of_schwartz_pairing_bound f C hC_nonneg hpair_bound

  -- Step 2: from equality of Schwartz pairings and L² membership, deduce a.e. equality.
  -- Repackage the pairings in the form expected by `ae_eq_of_memLp_schwartz_pairings`.
  have h_pairings_star :
      ∀ φ : SchwartzMap ℝ ℂ,
        ∫ t, f t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume
          = ∫ t, g t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume := by
    intro φ
    have h_eq := hpair φ
    -- Relate the `conj` formulation to the `starRingEnd` formulation on both sides.
    have h_left :
        ∫ t, f t * conj (φ t) ∂volume
          = ∫ t, f t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume := by
      have hfun :
          (fun t : ℝ => f t * conj (φ t)) =
            fun t : ℝ =>
              f t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) := by
        funext t
        rfl
      simp [hfun]
    have h_right :
        ∫ t, g t * conj (φ t) ∂volume
          = ∫ t, g t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) ∂volume := by
      have hfun :
          (fun t : ℝ => g t * conj (φ t)) =
            fun t : ℝ =>
              g t * (starRingEnd ℂ) (SchwartzMap.toFun φ t) := by
        funext t
        rfl
      simp [hfun]
    -- Use the original pairing equality and rewrite both sides.
    exact (h_left.trans h_eq).trans h_right.symm

  -- Apply the general a.e. uniqueness lemma for L² functions.
  have h_ae : f =ᵐ[volume] g :=
    ae_eq_of_memLp_schwartz_pairings
      (g₁ := f) (g₂ := g)
      (hg₁ := hf) (hg₂ := hg)
      (h_pairings := h_pairings_star)

  exact ⟨hf, h_ae⟩

/-- L² membership of the inverse Fourier transform on the closure of the Schwartz range.

If a function `w` in L² can be approximated arbitrarily well in L² by Fourier transforms
of Schwartz functions, then its inverse Fourier transform is also in L². This relies on
the fact that the inverse Fourier transform extends to an L² isometry on the closure of
the Schwartz range. -/
lemma inverseFourierIntegral_memLp_of_schwartz_approx
    {w : ℝ → ℂ}
    (hw : MemLp w 2 volume)
    (hw_approx : ∀ ε > 0, ∃ ψ : SchwartzMap ℝ ℂ,
        eLpNorm (fun ξ => w ξ - Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ) 2 volume
          < ENNReal.ofReal ε) :
    MemLp (fun t => Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume := by
  classical
  -- Step 1: fix a tolerance sequence ε n → 0 and choose Schwartz approximants
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε_pos : ∀ n, 0 < ε n := by
    intro n; have : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    simpa [ε] using one_div_pos.mpr this
  have h_exists_ψ : ∀ n, ∃ ψn : SchwartzMap ℝ ℂ,
      eLpNorm (fun ξ => w ξ - Frourio.fourierIntegral (fun t => ψn t) ξ) 2 volume
        < ENNReal.ofReal (ε n) := by
    intro n; exact hw_approx (ε n) (hε_pos n)
  choose ψ hψ_err using h_exists_ψ

  -- Frequency-side approximants and their L² membership
  let wApprox : ℕ → ℝ → ℂ := fun n ξ => Frourio.fourierIntegral (fun t => ψ n t) ξ
  have hwApprox_L2 : ∀ n, MemLp (wApprox n) 2 volume :=
    fun n => by simpa [wApprox] using fourierIntegral_memLp_of_schwartz (ψ n)

  -- ε n → 0 in ℝ≥0∞
  have hε_tendsto : Filter.Tendsto (fun n => ENNReal.ofReal (ε n))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have h_real : Filter.Tendsto ε Filter.atTop (𝓝 (0 : ℝ)) := by
      have h_eq : ε = fun (n : ℕ) => 1 / ((n : ℝ) + 1) := rfl
      rw [h_eq]
      have h_atTop : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.atTop_add
        · exact tendsto_natCast_atTop_atTop
        · exact tendsto_const_nhds
      exact tendsto_const_nhds.div_atTop h_atTop
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
    exact ENNReal.tendsto_ofReal h_real

  -- Conclude L² convergence of the frequency-side approximants to w
  have hw_freq_tendsto0 : Filter.Tendsto
      (fun n => eLpNorm (fun ξ => w ξ - wApprox n ξ) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    eLpNorm_tendsto_of_error_tendsto hψ_err hε_tendsto

  -- Lift to Lp and use completeness to get a time-side L² limit of the inverses
  let wLp : ℕ → Lp ℂ 2 volume := fun n => (hwApprox_L2 n).toLp (wApprox n)
  let wLim : Lp ℂ 2 volume := hw.toLp w
  have hwLp_tendsto : Filter.Tendsto wLp Filter.atTop (𝓝 wLim) := by
    -- Direct proof as in `toLp_tendsto_of_eLpNorm_tendsto`, without Schwartz restriction
    -- Express distances via eLpNorm of differences
    have hdist_eq :
        (fun n => dist (wLp n) wLim)
          = fun n =>
              (eLpNorm (fun ξ : ℝ => w ξ - wApprox n ξ) 2 volume).toReal := by
      funext n
      have hdiff : MemLp (fun ξ : ℝ => wApprox n ξ - w ξ) 2 volume :=
        (hwApprox_L2 n).sub hw
      have hcalc : hdiff.toLp (fun ξ => wApprox n ξ - w ξ) = wLp n - wLim := by
        simpa [wLp, wLim] using MemLp.toLp_sub (hwApprox_L2 n) hw
      have hnorm :=
        Lp.norm_toLp (μ := volume)
          (f := fun ξ : ℝ => wApprox n ξ - w ξ) hdiff
      have : (eLpNorm (fun ξ : ℝ => wApprox n ξ - w ξ) 2 volume).toReal
            = (eLpNorm (fun ξ : ℝ => w ξ - wApprox n ξ) 2 volume).toReal := by
        simpa [sub_eq_add_neg]
          using congrArg ENNReal.toReal
            (eLpNorm_sub_comm (f := fun ξ : ℝ => wApprox n ξ)
              (g := fun ξ : ℝ => w ξ) (p := (2 : ℝ≥0∞)) (μ := volume))
      calc
        dist (wLp n) wLim = ‖wLp n - wLim‖ := by simp [dist_eq_norm]
        _ = (eLpNorm (fun ξ : ℝ => wApprox n ξ - w ξ) 2 volume).toReal := by
              simpa [hdiff, hcalc, norm_sub_rev] using hnorm
        _ = (eLpNorm (fun ξ : ℝ => w ξ - wApprox n ξ) 2 volume).toReal := this
    -- Convert ENNReal limit to real via toReal and conclude metric convergence
    have h_ne_top : ∀ n,
        eLpNorm (fun ξ : ℝ => w ξ - wApprox n ξ) 2 volume ≠ ∞ :=
      fun n => (hw.sub (hwApprox_L2 n)).2.ne
    have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp
    have h_toReal :=
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n => eLpNorm (fun ξ => w ξ - wApprox n ξ) 2 volume)
        h_ne_top h_zero_ne_top).mpr hw_freq_tendsto0
    have hdist_tendsto :
        Filter.Tendsto (fun n => dist (wLp n) wLim) Filter.atTop (𝓝 0) := by
      simpa [hdist_eq] using h_toReal
    exact (tendsto_iff_dist_tendsto_zero).2 hdist_tendsto

  -- Time-side inverses are Schwartz, hence L², and form a Cauchy sequence in L²
  have hψ_L2 : ∀ n, MemLp (fun t : ℝ => ψ n t) 2 volume :=
    fun n => SchwartzMap.memLp (ψ n) (p := (2 : ℝ≥0∞)) (μ := volume)
  let ψLp : ℕ → Lp ℂ 2 volume := fun n => (hψ_L2 n).toLp (fun t => ψ n t)

  -- Show ψLp is Cauchy using equality of distances with wLp
  have hψ_cauchy : CauchySeq ψLp := by
    -- For any ε>0 pick N so that wLp is ε/2-close to the limit then transfer distances
    refine Metric.cauchySeq_iff.2 ?_
    intro εr hεr
    have hεr2 : 0 < εr / 2 := half_pos hεr
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hwLp_tendsto (εr / 2) hεr2
    refine ⟨N, ?_⟩
    intro m hm n hn
    -- Dist(ψLp m, ψLp n) = Dist(wLp m, wLp n)
    have hdist_w : dist (wLp m) (wLp n)
        = ENNReal.toReal (eLpNorm (fun ξ => wApprox m ξ - wApprox n ξ) 2 volume) := by
      simp only [wLp]
      rw [dist_comm, dist_edist,
        Lp.edist_toLp_toLp (wApprox n) (wApprox m) (hwApprox_L2 n) (hwApprox_L2 m)]
      congr 1
      exact eLpNorm_sub_comm (wApprox n) (wApprox m) 2 volume
    have hdist_ψ : dist (ψLp m) (ψLp n)
        = ENNReal.toReal (eLpNorm (fun t => ψ m t - ψ n t) 2 volume) := by
      simp only [ψLp]
      rw [dist_comm, dist_edist,
        Lp.edist_toLp_toLp (fun t => ψ n t) (fun t => ψ m t) (hψ_L2 n) (hψ_L2 m)]
      congr 1
      exact eLpNorm_sub_comm (fun t => ψ n t) (fun t => ψ m t) 2 volume
    have hfreq_eq :
        eLpNorm (fun ξ => wApprox m ξ - wApprox n ξ) 2 volume
          = eLpNorm (fun t => ψ m t - ψ n t) 2 volume := by
      -- Plancherel for Schwartz differences
      have hrewrite :
          (fun ξ => wApprox m ξ - wApprox n ξ)
            = fun ξ => Frourio.fourierIntegral (fun t => ψ m t - ψ n t) ξ := by
        funext ξ
        have := fourierIntegral_sub
            (f := fun t => ψ m t) (g := fun t => ψ n t)
            (hf := schwartz_integrable (ψ m)) (hg := schwartz_integrable (ψ n)) (ξ := ξ)
        simpa [wApprox, sub_eq_add_neg] using this.symm
      simpa [hrewrite] using fourierIntegral_eLpNorm_eq (φ := ψ m - ψ n)
    -- Distances coincide, so control by the limit point
    have hdist_eq : dist (ψLp m) (ψLp n) = dist (wLp m) (wLp n) := by
      rw [hdist_w, hdist_ψ]
      exact congrArg ENNReal.toReal hfreq_eq.symm
    -- Triangle via the limit wLim
    have htriangle :
        dist (wLp m) (wLp n) ≤ dist (wLp m) wLim + dist (wLp n) wLim := by
      simpa [dist_comm] using dist_triangle (wLp m) wLim (wLp n)
    have hmε : dist (wLp m) wLim < εr / 2 := hN m hm
    have hnε : dist (wLp n) wLim < εr / 2 := hN n hn
    have hsum_lt : dist (wLp m) wLim + dist (wLp n) wLim < εr := by
      have := add_lt_add hmε hnε
      calc dist (wLp m) wLim + dist (wLp n) wLim < εr / 2 + εr / 2 := this
        _ = εr := by ring
    have hmn_lt : dist (wLp m) (wLp n) < εr :=
      lt_of_le_of_lt htriangle hsum_lt
    simpa [hdist_eq] using hmn_lt

  -- Completeness yields the time-side Lp limit
  obtain ⟨ψ_lim, hψ_tendsto⟩ := cauchySeq_tendsto_of_complete hψ_cauchy

  -- Identify the limit as the inverse Fourier integral of w via Schwartz pairings
  -- First, express convergence of ψ n to the L² representative ψ_lim at the function level
  let ψ_lim_fun : ℝ → ℂ := fun t => (ψ_lim : ℝ → ℂ) t
  have hψ_lim_L2 : MemLp ψ_lim_fun 2 volume := Lp.memLp ψ_lim
  -- Use Lp convergence directly for pairings on the left

  -- For any Schwartz test function φ, compare pairings and pass to the limit
  have h_pairing_eq : ∀ φ : SchwartzMap ℝ ℂ,
      ∫ t, (Real.fourierIntegralInv (fun ξ => w ξ) t) * conj (φ t) ∂volume
        = ∫ t, (ψ_lim_fun t) * conj (φ t) ∂volume := by
    intro φ
    -- For each n, identify the pairing via the inverse Fourier identity on Schwartz
    have h_eq_n : ∀ n,
        ∫ t, (ψ n t) * conj (φ t) ∂volume
          = ∫ ξ, (wApprox n ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume := by
      intro n
      -- invF(wApprox n) = ψ n at the function level
      have h_inv_eq :
          (fun t : ℝ => Real.fourierIntegralInv (fun ξ => wApprox n ξ) t)
            = fun t : ℝ => ψ n t := by
        simpa [wApprox] using fourierIntegralInv_fourierIntegral_schwartz (ψ n)
      -- Apply the pairing lemma to wApprox n and rewrite the LHS
      have := inverseFourier_pairing_schwartz (w := wApprox n) (hw := hwApprox_L2 n) φ
      simpa [h_inv_eq]
        using this
    -- Take limits on both sides using L² pairing continuity
    -- identify the Lp limit as the `toLp` of its representative
    have hψlim_toLp_eq : (hψ_lim_L2).toLp ψ_lim_fun = ψ_lim := by
      simp [ψ_lim_fun]
    have h_left :=
      pairing_tendsto_L2_left_Lp (hfn_L2 := hψ_L2) (hf_L2 := hψ_lim_L2) φ
        (hLp_tendsto := by simpa [hψlim_toLp_eq] using hψ_tendsto)
    -- Right side: convergence with test function equals the Fourier transform of φ
    have h_right_base :=
      pairing_tendsto_L2_left (hfn_L2 := hwApprox_L2) (hf_L2 := hw)
        (φ := fourierAsSchwartzFunction φ)
        (hf_tendsto := by simpa using hw_freq_tendsto0)
    -- Rewrite the test function via equality with the explicit Fourier integral
    have hψ_test :
        (fun ξ : ℝ => (fourierAsSchwartzFunction φ) ξ)
          = fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ t) ξ := by
      funext ξ
      simp [fourierAsSchwartzFunction, fourierIntegral_eq_real]
    have h_right : Filter.Tendsto
        (fun n => ∫ ξ, (wApprox n ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)
        Filter.atTop (𝓝 (∫ ξ, (w ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)) := by
      -- Rewrite both the sequence terms and the limit using hψ_test
      simpa [hψ_test] using h_right_base
    -- Transport the equality along the limits: both sequences are equal termwise
    -- and converge to the displayed limits.
    have h_seq_eq : Filter.Tendsto
        (fun n => ∫ t, (ψ n t) * conj (φ t) ∂volume)
        Filter.atTop (𝓝 (∫ t, (ψ_lim_fun t) * conj (φ t) ∂volume)) := h_left
    have h_seq_eq' : Filter.Tendsto
        (fun n => ∫ ξ, (wApprox n ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)
        Filter.atTop (𝓝 (∫ ξ, (w ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)) := h_right
    -- Since the nth terms are equal, their limits must coincide
    have h_limits_equal :
        (∫ t, (ψ_lim_fun t) * conj (φ t) ∂volume)
          = (∫ ξ, (w ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume) := by
      -- Replace the right-hand tendsto by an equal sequence using h_eq_n
      have h_right_as_left : Filter.Tendsto
          (fun n => ∫ t, (ψ n t) * conj (φ t) ∂volume)
          Filter.atTop (𝓝 (∫ ξ, (w ξ) *
                conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)) := by
        exact h_seq_eq'.congr' (Filter.Eventually.of_forall (fun n => (h_eq_n n).symm))
      exact tendsto_nhds_unique h_seq_eq h_right_as_left
    -- But the RHS also equals the pairing with invF w by the pairing lemma
    have h_pair_w := inverseFourier_pairing_schwartz (w := w) (hw := hw) φ
    -- Compose the two equalities to get the desired pairing identity
    have h_goal :
        ∫ t, (Real.fourierIntegralInv (fun ξ => w ξ) t) * conj (φ t) ∂volume
          = ∫ t, (ψ_lim_fun t) * conj (φ t) ∂volume := by
      exact h_pair_w.trans h_limits_equal.symm
    exact h_goal

  -- Conclude: invF(w) agrees a.e. with ψ_lim_fun, hence is in L²
  have h_mem_and_ae :=
    memLp_and_ae_eq_of_schwartz_pairing (f := fun t => Real.fourierIntegralInv (fun ξ => w ξ) t)
      (g := ψ_lim_fun) hψ_lim_L2 (hpair := by
        intro φ; exact (h_pairing_eq φ))
  exact h_mem_and_ae.1

/-- Continuity of the inverse Fourier transform on the closure of the Schwartz
range (skeleton statement, proof deferred).

If `wApprox n` is an L²-approximating sequence for `w` on the frequency side,
with each `wApprox n` the Fourier transform of a Schwartz function, then the
inverse transforms `inv(wApprox n)` converge to `inv(w)` in L² on the time side.

This is the continuity counterpart to
`inverseFourierIntegral_memLp_of_schwartz_approx` and is used in the proof of
`inverseFourier_isometry_on_closure`. -/
lemma inverseFourier_tendsto_of_schwartz_approx
    (w : ℝ → ℂ) (wApprox : ℕ → ℝ → ℂ)
    (hw : MemLp w 2 volume)
    (hwApprox_L2 : ∀ n, MemLp (wApprox n) 2 volume)
    (hwApprox_isFourier :
      ∀ n, ∃ ψ : SchwartzMap ℝ ℂ,
        wApprox n = fun ξ => Frourio.fourierIntegral (fun t => ψ t) ξ)
    (hw_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun ξ => w ξ - wApprox n ξ) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n =>
        ENNReal.toReal (eLpNorm (fun t =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  classical
  -- Step 0: choose Schwartz witnesses for the approximating sequence `wApprox n`.
  choose ψ hψ_repr using hwApprox_isFourier

  -- Frequency-side sequence in L².
  have hwApprox_L2' : ∀ n, MemLp (wApprox n) 2 volume := hwApprox_L2

  -- Step 1: lift `wApprox n → w` in L² to convergence in `Lp`.
  let wLp : ℕ → Lp ℂ 2 volume := fun n => (hwApprox_L2' n).toLp (wApprox n)
  let wLim : Lp ℂ 2 volume := hw.toLp w

  have hwLp_tendsto : Filter.Tendsto wLp Filter.atTop (𝓝 wLim) := by
    -- Distances in `Lp` are expressed via the eLpNorm of differences.
    have hdist_eq :
        (fun n => dist (wLp n) wLim)
          = fun n =>
              (eLpNorm (fun ξ : ℝ => w ξ - wApprox n ξ) 2 volume).toReal := by
      funext n
      -- `wApprox n - w` lies in L².
      have hdiff : MemLp (fun ξ : ℝ => wApprox n ξ - w ξ) 2 volume :=
        (hwApprox_L2' n).sub hw
      have hcalc :
          hdiff.toLp (fun ξ : ℝ => wApprox n ξ - w ξ)
            = wLp n - wLim := by
        simpa [wLp, wLim] using
          MemLp.toLp_sub (hwApprox_L2' n) hw
      have hnorm :=
        Lp.norm_toLp (μ := volume)
          (f := fun ξ : ℝ => wApprox n ξ - w ξ) hdiff
      have hswap :
          (eLpNorm (fun ξ : ℝ => wApprox n ξ - w ξ) 2 volume)
            = eLpNorm (fun ξ : ℝ => w ξ - wApprox n ξ) 2 volume :=
        eLpNorm_sub_comm (f := fun ξ : ℝ => wApprox n ξ)
          (g := fun ξ : ℝ => w ξ)
          (p := (2 : ℝ≥0∞)) (μ := volume)
      calc
        dist (wLp n) wLim
            = ‖wLp n - wLim‖ := by simp [dist_eq_norm]
        _ = (eLpNorm (fun ξ : ℝ => wApprox n ξ - w ξ) 2 volume).toReal := by
              simpa [hdiff, hcalc, norm_sub_rev] using hnorm
        _ = (eLpNorm (fun ξ : ℝ => w ξ - wApprox n ξ) 2 volume).toReal := by
              simpa using congrArg ENNReal.toReal hswap

    -- Convert ENNReal convergence to real convergence via `toReal`.
    have h_ne_top : ∀ n,
        eLpNorm (fun ξ : ℝ => w ξ - wApprox n ξ) 2 volume ≠ ∞ :=
      fun n => (hw.sub (hwApprox_L2' n)).2.ne
    have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp
    have h_toReal :=
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n =>
          eLpNorm (fun ξ : ℝ => w ξ - wApprox n ξ) 2 volume)
        h_ne_top h_zero_ne_top).mpr hw_tendsto
    have hdist_tendsto :
        Filter.Tendsto (fun n => dist (wLp n) wLim) Filter.atTop (𝓝 0) := by
      simpa [hdist_eq] using h_toReal
    exact (tendsto_iff_dist_tendsto_zero).2 hdist_tendsto

  -- Step 2: the time-side inverse transforms of the approximants are Schwartz
  -- (hence in L²) and form a Cauchy sequence in `Lp`.
  have hψ_L2 : ∀ n, MemLp (fun t : ℝ => ψ n t) 2 volume :=
    fun n => SchwartzMap.memLp (ψ n) (p := (2 : ℝ≥0∞)) (μ := volume)
  let ψLp : ℕ → Lp ℂ 2 volume := fun n => (hψ_L2 n).toLp (fun t => ψ n t)

  -- Show `ψLp` is Cauchy by transporting Cauchy-ness from `wLp`.
  have hψ_cauchy : CauchySeq ψLp := by
    refine Metric.cauchySeq_iff.2 ?_
    intro εr hεr
    have hεr2 : 0 < εr / 2 := half_pos hεr
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hwLp_tendsto (εr / 2) hεr2
    refine ⟨N, ?_⟩
    intro m hm n hn
    -- Dist(ψLp m, ψLp n) = Dist(wLp m, wLp n).
    have hdist_w : dist (wLp m) (wLp n)
        = ENNReal.toReal (eLpNorm (fun ξ => wApprox m ξ - wApprox n ξ) 2 volume) := by
      simp only [wLp]
      rw [dist_comm, dist_edist,
        Lp.edist_toLp_toLp (wApprox n) (wApprox m) (hwApprox_L2' n) (hwApprox_L2' m)]
      congr 1
      exact eLpNorm_sub_comm (wApprox n) (wApprox m) 2 volume
    have hdist_ψ : dist (ψLp m) (ψLp n)
        = ENNReal.toReal (eLpNorm (fun t => ψ m t - ψ n t) 2 volume) := by
      simp only [ψLp]
      rw [dist_comm, dist_edist,
        Lp.edist_toLp_toLp (fun t => ψ n t) (fun t => ψ m t)
          (hψ_L2 n) (hψ_L2 m)]
      congr 1
      exact eLpNorm_sub_comm (fun t => ψ n t) (fun t => ψ m t) 2 volume
    have hfreq_eq :
        eLpNorm (fun ξ => wApprox m ξ - wApprox n ξ) 2 volume
          = eLpNorm (fun t => ψ m t - ψ n t) 2 volume := by
      -- Plancherel for Schwartz differences.
      have hrewrite :
          (fun ξ => wApprox m ξ - wApprox n ξ)
            = fun ξ => Frourio.fourierIntegral (fun t => ψ m t - ψ n t) ξ := by
        funext ξ
        have := fourierIntegral_sub
          (f := fun t => ψ m t) (g := fun t => ψ n t)
          (hf := schwartz_integrable (ψ m))
          (hg := schwartz_integrable (ψ n)) (ξ := ξ)
        simpa [hψ_repr, sub_eq_add_neg] using this.symm
      simpa [hrewrite] using fourierIntegral_eLpNorm_eq (φ := ψ m - ψ n)
    -- Distances coincide, so we control them via the limit point `wLim`.
    have hdist_eq : dist (ψLp m) (ψLp n) = dist (wLp m) (wLp n) := by
      rw [hdist_w, hdist_ψ]
      exact congrArg ENNReal.toReal hfreq_eq.symm
    -- Triangle via the limit `wLim`.
    have htriangle :
        dist (wLp m) (wLp n) ≤ dist (wLp m) wLim + dist (wLp n) wLim := by
      simpa [dist_comm] using dist_triangle (wLp m) wLim (wLp n)
    have hmε : dist (wLp m) wLim < εr / 2 := hN m hm
    have hnε : dist (wLp n) wLim < εr / 2 := hN n hn
    have hsum_lt : dist (wLp m) wLim + dist (wLp n) wLim < εr := by
      have := add_lt_add hmε hnε
      have : dist (wLp m) wLim + dist (wLp n) wLim
          < εr / 2 + εr / 2 := this
      simpa [two_mul, mul_div_cancel₀ εr (two_ne_zero : (2 : ℝ) ≠ 0),
        add_comm, add_left_comm, add_assoc] using this
    have hmn_lt : dist (wLp m) (wLp n) < εr :=
      lt_of_le_of_lt htriangle hsum_lt
    simpa [hdist_eq] using hmn_lt

  -- Completeness of L² yields the time-side Lp limit.
  obtain ⟨ψ_lim, hψ_tendsto⟩ := cauchySeq_tendsto_of_complete hψ_cauchy

  -- Step 3: identify the Lp limit as the inverse Fourier transform of `w`
  -- using Schwartz pairings.
  let ψ_lim_fun : ℝ → ℂ := fun t => (ψ_lim : ℝ → ℂ) t
  have hψ_lim_L2 : MemLp ψ_lim_fun 2 volume := Lp.memLp ψ_lim

  -- For any Schwartz test function φ, compare pairings and pass to the limit.
  have h_pairing_eq : ∀ φ : SchwartzMap ℝ ℂ,
      ∫ t, (Real.fourierIntegralInv (fun ξ => w ξ) t) * conj (φ t) ∂volume
        = ∫ t, (ψ_lim_fun t) * conj (φ t) ∂volume := by
    intro φ
    -- For each n, identify the pairing via the inverse Fourier identity on Schwartz.
    have h_eq_n : ∀ n,
        ∫ t, (ψ n t) * conj (φ t) ∂volume
          = ∫ ξ, (wApprox n ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume := by
      intro n
      -- invF(wApprox n) = ψ n at the function level.
      have h_inv_eq :
          (fun t : ℝ => Real.fourierIntegralInv (fun ξ => wApprox n ξ) t)
            = fun t : ℝ => ψ n t := by
        simpa [hψ_repr n] using
          fourierIntegralInv_fourierIntegral_schwartz (ψ n)
      -- Apply the pairing lemma to wApprox n and rewrite the LHS.
      have :=
        inverseFourier_pairing_schwartz (w := wApprox n)
          (hw := hwApprox_L2' n) φ
      simpa [h_inv_eq] using this

    -- Left side: pass to the limit using Lp convergence of ψLp.
    have hψlim_toLp_eq : (hψ_lim_L2).toLp ψ_lim_fun = ψ_lim := by
      simp [ψ_lim_fun]
    have h_left :=
      pairing_tendsto_L2_left_Lp (hfn_L2 := hψ_L2) (hf_L2 := hψ_lim_L2) φ
        (hLp_tendsto := by simpa [hψlim_toLp_eq] using hψ_tendsto)

    -- Right side: use continuity of the pairing in the first argument and the
    -- given L² convergence `wApprox n → w`.
    have h_right_base :=
      pairing_tendsto_L2_left (hfn_L2 := hwApprox_L2') (hf_L2 := hw)
        (φ := fourierAsSchwartzFunction φ)
        (hf_tendsto := by simpa using hw_tendsto)

    -- Rewrite the test function as the explicit Fourier integral.
    have hψ_test :
        (fun ξ : ℝ => (fourierAsSchwartzFunction φ) ξ)
          = fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ t) ξ := by
      funext ξ
      simp [fourierAsSchwartzFunction, fourierIntegral_eq_real]

    have h_right : Filter.Tendsto
        (fun n => ∫ ξ, (wApprox n ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)
        Filter.atTop (𝓝 (∫ ξ, (w ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)) := by
      simpa [hψ_test] using h_right_base

    -- Transport equality along the limits: both sequences have equal nth terms
    -- and converge to the displayed limits.
    have h_seq_eq : Filter.Tendsto
        (fun n => ∫ t, (ψ n t) * conj (φ t) ∂volume)
        Filter.atTop (𝓝 (∫ t, (ψ_lim_fun t) * conj (φ t) ∂volume)) := h_left
    have h_seq_eq' : Filter.Tendsto
        (fun n => ∫ ξ, (wApprox n ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)
        Filter.atTop (𝓝 (∫ ξ, (w ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)) := h_right

    have h_limits_equal :
        (∫ t, (ψ_lim_fun t) * conj (φ t) ∂volume)
          = (∫ ξ, (w ξ) *
              conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume) := by
      -- Replace the right-hand limit by an equal sequence using `h_eq_n`.
      have h_right_as_left : Filter.Tendsto
          (fun n => ∫ t, (ψ n t) * conj (φ t) ∂volume)
          Filter.atTop (𝓝 (∫ ξ, (w ξ) *
                conj (Frourio.fourierIntegral (fun t : ℝ => φ t) ξ) ∂volume)) := by
        exact h_seq_eq'.congr'
          (Filter.Eventually.of_forall (fun n => (h_eq_n n).symm))
      exact tendsto_nhds_unique h_seq_eq h_right_as_left

    -- The RHS also equals the pairing with `invF w` by the pairing lemma.
    have h_pair_w :=
      inverseFourier_pairing_schwartz (w := w) (hw := hw) φ

    -- Compose the two equalities.
    have h_goal :
        ∫ t, (Real.fourierIntegralInv (fun ξ => w ξ) t) * conj (φ t) ∂volume
          = ∫ t, (ψ_lim_fun t) * conj (φ t) ∂volume := by
      exact h_pair_w.trans h_limits_equal.symm
    exact h_goal

  -- `invF w` agrees a.e. with `ψ_lim_fun`, and both are in L².
  have h_mem_and_ae :=
    memLp_and_ae_eq_of_schwartz_pairing
      (f := fun t => Real.fourierIntegralInv (fun ξ => w ξ) t)
      (g := ψ_lim_fun) hψ_lim_L2
      (hpair := by intro φ; exact h_pairing_eq φ)

  have h_inv_w_ae :
      (fun t => Real.fourierIntegralInv (fun ξ => w ξ) t)
        =ᵐ[volume] ψ_lim_fun := h_mem_and_ae.2

  -- Step 4: use Lp convergence of `ψLp` to obtain convergence of the inverses.
  have h_norm_tendsto :
      Filter.Tendsto (fun n => ‖ψLp n - ψ_lim‖)
        Filter.atTop (𝓝 (0 : ℝ)) :=
    (tendsto_iff_norm_sub_tendsto_zero).1 hψ_tendsto

  -- Express the Lp distance via the eLpNorm of the difference of representatives.
  have h_norm_eq :
      ∀ n,
        ‖ψLp n - ψ_lim‖
          = ENNReal.toReal
              (eLpNorm (fun t => ψ n t - ψ_lim_fun t) 2 volume) := by
    intro n
    have hdiff : MemLp (fun t => ψ n t - ψ_lim_fun t) 2 volume :=
      (hψ_L2 n).sub hψ_lim_L2
    have hcalc :
        hdiff.toLp (fun t => ψ n t - ψ_lim_fun t)
          = ψLp n - ψ_lim := by
      simpa [ψLp, ψ_lim_fun] using
        MemLp.toLp_sub (hψ_L2 n) hψ_lim_L2
    have hnorm :=
      Lp.norm_toLp (μ := volume)
        (f := fun t : ℝ => ψ n t - ψ_lim_fun t) hdiff
    simpa [hdiff, hcalc, norm_sub_rev] using hnorm

  have h_toReal_tendsto :
      Filter.Tendsto (fun n =>
        ENNReal.toReal
          (eLpNorm (fun t => ψ n t - ψ_lim_fun t) 2 volume))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    refine h_norm_tendsto.congr'
      (Filter.Eventually.of_forall (fun n => h_norm_eq n))

  -- Relate these eLpNorms to the ones appearing in the statement using a.e. equality.
  have h_inv_eLp_eq : ∀ n,
      eLpNorm (fun t =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume
        = eLpNorm (fun t => ψ n t - ψ_lim_fun t) 2 volume := by
    intro n
    -- invF(wApprox n) = ψ n pointwise.
    have h_inv_wApprox :
        (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t)
          = fun t : ℝ => ψ n t := by
      simpa [hψ_repr n] using
        fourierIntegralInv_fourierIntegral_schwartz (ψ n)
    -- Use the a.e. equality for `invF w`.
    have h_ae_diff :
        (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => w ξ) t)
          =ᵐ[volume]
        (fun t : ℝ => ψ n t - ψ_lim_fun t) := by
      -- First, rewrite the inverse of wApprox n.
      have h1 :
          (fun t : ℝ =>
            Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
              - Real.fourierIntegralInv (fun ξ => w ξ) t)
            = fun t : ℝ =>
                ψ n t - Real.fourierIntegralInv (fun ξ => w ξ) t := by
        funext t
        simp [h_inv_wApprox, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      -- Then replace `invF w` by `ψ_lim_fun` a.e.
      have h2 :
          (fun t : ℝ =>
            ψ n t - Real.fourierIntegralInv (fun ξ => w ξ) t)
            =ᵐ[volume]
          (fun t : ℝ => ψ n t - ψ_lim_fun t) := by
        refine h_inv_w_ae.mono ?_
        intro t ht
        simp [ht, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      exact h2.mono (fun t ht => by
        -- combine h1 (pointwise) with the a.e. equality h2
        rw [h1]
        exact ht)
    -- Conclude equality of eLpNorms by a.e. congruence.
    have h_congr :=
      eLpNorm_congr_ae (μ := volume) (p := (2 : ℝ≥0∞)) h_ae_diff
    simpa using h_congr

  -- Finally, transport convergence along these equalities.
  refine h_toReal_tendsto.congr'
    (Filter.Eventually.of_forall (fun n => ?_))
  -- Rewrite the target sequence using `h_inv_eLp_eq`.
  simp [h_inv_eLp_eq n]

set_option maxHeartbeats 400000 in -- for timeout
/-- L² isometry of the inverse Fourier transform on the closure of the Schwartz range
(signature only).

If `w, z ∈ L²(ℝ)` on the frequency side and each can be approximated in L² by
Fourier transforms of Schwartz functions, then the inverse Fourier transform is
an isometry on their difference: the L² distance on the time side equals the L²
distance on the frequency side. This formulates the Plancherel isometry for the
inverse transform on the closure of the Schwartz range. -/
lemma inverseFourier_isometry_on_closure
    {w z : ℝ → ℂ}
    (hw : MemLp w 2 volume) (hz : MemLp z 2 volume)
    (hw_approx : ∀ ε > 0, ∃ ψ : SchwartzMap ℝ ℂ,
        eLpNorm (fun ξ => w ξ
          - Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ) 2 volume
          < ENNReal.ofReal ε)
    (hz_approx : ∀ ε > 0, ∃ ψ : SchwartzMap ℝ ℂ,
        eLpNorm (fun ξ => z ξ
          - Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ) 2 volume
          < ENNReal.ofReal ε) :
    eLpNorm (fun t : ℝ =>
      Real.fourierIntegralInv (fun ξ : ℝ => w ξ) t
        - Real.fourierIntegralInv (fun ξ : ℝ => z ξ) t) 2 volume
      = eLpNorm (fun ξ : ℝ => w ξ - z ξ) 2 volume := by
  classical
  -- Skeleton of proof by density and continuity (Plancherel extension):
  -- 1) Fix a tolerance sequence ε n = 1 / (n+1).
  -- 2) Choose Schwartz approximants ψ n for w and χ n for z with L² errors < ε n.
  -- 3) For each n, use the Schwartz isometry: ‖inv(F[ψ n]) - inv(F[χ n])‖₂ = ‖F[ψ n] - F[χ n]‖₂.
  -- 4) Pass to the limit using triangle inequality and the L² continuity of the
  --    inverse transform on the closure of the Schwartz range.

  -- Step 1: tolerance sequence
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε_pos : ∀ n, 0 < ε n := by
    intro n; have : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    simpa [ε] using one_div_pos.mpr this

  -- Step 2: choose approximants on the frequency side by Fourier transforms of Schwartz
  have h_exists_ψ : ∀ n, ∃ ψn : SchwartzMap ℝ ℂ,
      eLpNorm (fun ξ => w ξ - Frourio.fourierIntegral (fun t => ψn t) ξ) 2 volume
        < ENNReal.ofReal (ε n) := by
    intro n; exact hw_approx (ε n) (hε_pos n)
  have h_exists_χ : ∀ n, ∃ χn : SchwartzMap ℝ ℂ,
      eLpNorm (fun ξ => z ξ - Frourio.fourierIntegral (fun t => χn t) ξ) 2 volume
        < ENNReal.ofReal (ε n) := by
    intro n; exact hz_approx (ε n) (hε_pos n)
  choose ψ hψ_err using h_exists_ψ
  choose χ hχ_err using h_exists_χ

  -- Define the approximating frequency-side functions
  let wApprox : ℕ → ℝ → ℂ := fun n ξ => Frourio.fourierIntegral (fun t => ψ n t) ξ
  let zApprox : ℕ → ℝ → ℂ := fun n ξ => Frourio.fourierIntegral (fun t => χ n t) ξ

  -- Step 3: exact equality at the Schwartz level for each n
  have h_isometry_schwartz : ∀ n,
      eLpNorm (fun t =>
        Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
          - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume
        = eLpNorm (fun ξ => wApprox n ξ - zApprox n ξ) 2 volume := by
    intro n
    -- Identify inverse integrals with the Schwartz functions themselves
    have h_inv_wA :
        (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => wApprox n ξ) t)
          = fun t : ℝ => ψ n t := by
      simpa [wApprox] using fourierIntegralInv_fourierIntegral_schwartz (ψ n)
    have h_inv_zA :
        (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => zApprox n ξ) t)
          = fun t : ℝ => χ n t := by
      simpa [zApprox] using fourierIntegralInv_fourierIntegral_schwartz (χ n)
    -- Equality of norms via Plancherel for Schwartz
    have h_freq_eq :
        eLpNorm (fun ξ => wApprox n ξ - zApprox n ξ) 2 volume
          = eLpNorm (fun t => ψ n t - χ n t) 2 volume := by
      have hrewrite :
          (fun ξ => wApprox n ξ - zApprox n ξ)
            = fun ξ => Frourio.fourierIntegral (fun t => ψ n t - χ n t) ξ := by
        funext ξ
        have := fourierIntegral_sub
            (f := fun t => ψ n t) (g := fun t => χ n t)
            (hf := schwartz_integrable (ψ n)) (hg := schwartz_integrable (χ n))
            (ξ := ξ)
        simpa [wApprox, zApprox, sub_eq_add_neg] using this.symm
      simpa [hrewrite] using fourierIntegral_eLpNorm_eq (φ := ψ n - χ n)
    have h_time_eq :
        eLpNorm (fun t => ψ n t - χ n t) 2 volume
          = eLpNorm (fun t =>
              Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
                - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume := by
      -- Plain rewriting by the inverse identities
      have : (fun t =>
            Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
              - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t)
            = fun t => ψ n t - χ n t := by
        funext t; simp [h_inv_wA, h_inv_zA]
      simp [this]
    simpa [h_time_eq] using h_freq_eq.symm

  -- Step 4: pass to the limit using the approximations
  -- First, show that ε n → 0
  have hε_tendsto : Filter.Tendsto (fun n => ENNReal.ofReal (ε n))
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have h_real : Filter.Tendsto ε Filter.atTop (𝓝 (0 : ℝ)) := by
      have h_eq : ε = fun (n : ℕ) => 1 / ((n : ℝ) + 1) := rfl
      rw [h_eq]
      have h_atTop : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.atTop_add
        · exact tendsto_natCast_atTop_atTop
        · exact tendsto_const_nhds
      exact tendsto_const_nhds.div_atTop h_atTop
    have h_nonneg : ∀ n, 0 ≤ ε n := fun n => le_of_lt (hε_pos n)
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
    exact ENNReal.tendsto_ofReal h_real

  -- Frequency-side convergence of the approximants to w and z
  have hw_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun ξ => w ξ - wApprox n ξ) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    eLpNorm_tendsto_of_error_tendsto hψ_err hε_tendsto

  have hz_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun ξ => z ξ - zApprox n ξ) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    eLpNorm_tendsto_of_error_tendsto hχ_err hε_tendsto

  -- L² membership of the inverse transforms of w and z
  have hinv_w_L2 : MemLp (fun t => Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume :=
    inverseFourierIntegral_memLp_of_schwartz_approx hw hw_approx

  have hinv_z_L2 : MemLp (fun t => Real.fourierIntegralInv (fun ξ => z ξ) t) 2 volume :=
    inverseFourierIntegral_memLp_of_schwartz_approx hz hz_approx

  -- Conclude equality by a 3ε argument using triangle inequality and continuity:
  --   ‖inv w - inv z‖₂ ≤ limsup_n (‖inv w - inv wApprox n‖₂ + ‖inv wApprox n - inv zApprox n‖₂
  --                                   + ‖inv zApprox n - inv z‖₂)
  -- and the middle term equals ‖wApprox n - zApprox n‖₂ by h_isometry_schwartz n.
  -- Conversely, reverse roles to get ≥, hence equality.
  -- Full details deferred.
  -- Frequency-side: show that the L² norms of the differences converge to ‖w - z‖₂.
  -- L² membership of approximants
  have hwA_L2 : ∀ n, MemLp (wApprox n) 2 volume :=
    fun n => by simpa [wApprox] using fourierIntegral_memLp_of_schwartz (ψ n)
  have hzA_L2 : ∀ n, MemLp (zApprox n) 2 volume :=
    fun n => by simpa [zApprox] using fourierIntegral_memLp_of_schwartz (χ n)

  -- Lift to Lp
  let wALp : ℕ → Lp ℂ 2 volume := fun n => (hwA_L2 n).toLp (wApprox n)
  let zALp : ℕ → Lp ℂ 2 volume := fun n => (hzA_L2 n).toLp (zApprox n)
  let wLp : Lp ℂ 2 volume := hw.toLp w
  let zLp : Lp ℂ 2 volume := hz.toLp z

  -- Show wApprox n → w and zApprox n → z in L² (as Lp convergence)
  have h_w_norm_eq : ∀ n,
      ‖wALp n - wLp‖
        = ENNReal.toReal (eLpNorm (fun ξ => w ξ - wApprox n ξ) 2 volume) := by
    intro n
    have hdiff : MemLp (fun ξ => w ξ - wApprox n ξ) 2 volume := hw.sub (hwA_L2 n)
    have hcalc :
        ((hw.sub (hwA_L2 n)).toLp (fun ξ => w ξ - wApprox n ξ))
          = wLp - wALp n := by
      simpa [wALp, wLp] using MemLp.toLp_sub hw (hwA_L2 n)
    have hnorm := Lp.norm_toLp (μ := volume)
        (f := fun ξ => w ξ - wApprox n ξ) hdiff
    simpa [hdiff, hcalc, norm_sub_rev]
      using hnorm

  have h_z_norm_eq : ∀ n,
      ‖zALp n - zLp‖
        = ENNReal.toReal (eLpNorm (fun ξ => z ξ - zApprox n ξ) 2 volume) := by
    intro n
    have hdiff : MemLp (fun ξ => z ξ - zApprox n ξ) 2 volume := hz.sub (hzA_L2 n)
    have hcalc :
        ((hz.sub (hzA_L2 n)).toLp (fun ξ => z ξ - zApprox n ξ))
          = zLp - zALp n := by
      simpa [zALp, zLp] using MemLp.toLp_sub hz (hzA_L2 n)
    have hnorm := Lp.norm_toLp (μ := volume)
        (f := fun ξ => z ξ - zApprox n ξ) hdiff
    simpa [hdiff, hcalc, norm_sub_rev]
      using hnorm

  have h_w_toReal :
      Filter.Tendsto (fun n => ENNReal.toReal
          (eLpNorm (fun ξ => w ξ - wApprox n ξ) 2 volume))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    have h_ne_top : ∀ n,
        eLpNorm (fun ξ => w ξ - wApprox n ξ) 2 volume ≠ ∞ :=
      fun n => (hw.sub (hwA_L2 n)).2.ne
    have h0 : (0 : ℝ≥0∞) ≠ ∞ := by simp
    simpa using
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n => eLpNorm (fun ξ => w ξ - wApprox n ξ) 2 volume)
        h_ne_top h0).mpr hw_tendsto

  have h_z_toReal :
      Filter.Tendsto (fun n => ENNReal.toReal
          (eLpNorm (fun ξ => z ξ - zApprox n ξ) 2 volume))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    have h_ne_top : ∀ n,
        eLpNorm (fun ξ => z ξ - zApprox n ξ) 2 volume ≠ ∞ :=
      fun n => (hz.sub (hzA_L2 n)).2.ne
    have h0 : (0 : ℝ≥0∞) ≠ ∞ := by simp
    simpa using
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n => eLpNorm (fun ξ => z ξ - zApprox n ξ) 2 volume)
        h_ne_top h0).mpr hz_tendsto

  have h_wLp_tendsto : Filter.Tendsto wALp Filter.atTop (𝓝 wLp) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact h_w_toReal.congr'
      (Filter.Eventually.of_forall (fun n => (h_w_norm_eq n).symm))

  have h_zLp_tendsto : Filter.Tendsto zALp Filter.atTop (𝓝 zLp) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact h_z_toReal.congr'
      (Filter.Eventually.of_forall (fun n => (h_z_norm_eq n).symm))

  -- Combine the two convergences for the difference sequence in L²
  have h_diff_norm_tendsto0 : Filter.Tendsto
      (fun n => ‖(wALp n - zALp n) - (wLp - zLp)‖)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    -- bound by triangle inequality
    have h_nonneg : ∀ n, 0 ≤ ‖(wALp n - zALp n) - (wLp - zLp)‖ :=
      fun _ => norm_nonneg _
    have h_upper : Filter.Tendsto
        (fun n => ‖wALp n - wLp‖ + ‖zALp n - zLp‖)
        Filter.atTop (𝓝 (0 : ℝ)) := by
      -- From the `toReal`-limits we obtained, deduce real norm limits to 0
      have hw0 : Filter.Tendsto (fun n => ‖wALp n - wLp‖)
          Filter.atTop (𝓝 (0 : ℝ)) :=
        h_w_toReal.congr'
          (Filter.Eventually.of_forall (fun n => (h_w_norm_eq n).symm))
      have hz0 : Filter.Tendsto (fun n => ‖zALp n - zLp‖)
          Filter.atTop (𝓝 (0 : ℝ)) :=
        h_z_toReal.congr'
          (Filter.Eventually.of_forall (fun n => (h_z_norm_eq n).symm))
      simpa using hw0.add hz0
    -- Squeeze
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ h_upper h_nonneg ?_
    · exact tendsto_const_nhds
    · intro n
      -- ‖(a-b) - (c-d)‖ = ‖(a-c) - (b-d)‖ ≤ ‖a-c‖ + ‖b-d‖ in any normed group
      have h := norm_sub_le (wALp n - wLp) (zALp n - zLp)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_sub_rev]
        using h

  -- Identify real norms with ENNReal eLpNorms for the frequency-side differences
  have h_freq_norm_eq_left : ∀ n,
      ‖wALp n - zALp n‖
        = ENNReal.toReal (eLpNorm (fun ξ => wApprox n ξ - zApprox n ξ) 2 volume) := by
    intro n
    have hdiff : MemLp (fun ξ => wApprox n ξ - zApprox n ξ) 2 volume :=
      (hwA_L2 n).sub (hzA_L2 n)
    have hcalc : hdiff.toLp (fun ξ => wApprox n ξ - zApprox n ξ)
          = wALp n - zALp n := by
      simpa [wALp, zALp] using MemLp.toLp_sub (hwA_L2 n) (hzA_L2 n)
    have hnorm := Lp.norm_toLp (μ := volume)
        (f := fun ξ => wApprox n ξ - zApprox n ξ) hdiff
    simpa [hdiff, hcalc, norm_sub_rev] using hnorm

  have h_freq_norm_eq_right :
      ‖wLp - zLp‖
        = ENNReal.toReal (eLpNorm (fun ξ => w ξ - z ξ) 2 volume) := by
    have hdiff : MemLp (fun ξ => w ξ - z ξ) 2 volume := hw.sub hz
    have hcalc : hdiff.toLp (fun ξ => w ξ - z ξ) = wLp - zLp := by
      simpa [wLp, zLp] using MemLp.toLp_sub hw hz
    have hnorm := Lp.norm_toLp (μ := volume)
        (f := fun ξ => w ξ - z ξ) hdiff
    simpa [hdiff, hcalc, norm_sub_rev] using hnorm

  have h_freq_toReal_lim : Filter.Tendsto
      (fun n => ENNReal.toReal (eLpNorm (fun ξ => wApprox n ξ - zApprox n ξ) 2 volume))
      Filter.atTop (𝓝 (ENNReal.toReal (eLpNorm (fun ξ => w ξ - z ξ) 2 volume))) := by
    have h_sub_tendsto : Filter.Tendsto (fun n => wALp n - zALp n)
        Filter.atTop (𝓝 (wLp - zLp)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact h_diff_norm_tendsto0
    -- Apply continuity of norm
    have h_norm_tendsto : Filter.Tendsto (fun n => ‖wALp n - zALp n‖)
        Filter.atTop (𝓝 ‖wLp - zLp‖) :=
      (Continuous.tendsto continuous_norm _).comp h_sub_tendsto
    -- Rewrite using the norm identities
    show Filter.Tendsto (fun n =>
      ENNReal.toReal (eLpNorm (fun ξ => wApprox n ξ - zApprox n ξ) 2 volume))
        Filter.atTop (𝓝 (ENNReal.toReal (eLpNorm (fun ξ => w ξ - z ξ) 2 volume)))
    simp only [← h_freq_norm_eq_left, ← h_freq_norm_eq_right]
    exact h_norm_tendsto

  -- Convert real convergence to ENNReal for frequency-side sequence
  have h_freq_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun ξ => wApprox n ξ - zApprox n ξ) 2 volume)
      Filter.atTop (𝓝 (eLpNorm (fun ξ => w ξ - z ξ) 2 volume)) := by
    have h_ne_left : ∀ n,
        eLpNorm (fun ξ => wApprox n ξ - zApprox n ξ) 2 volume ≠ ∞ :=
      fun n => ((hwA_L2 n).sub (hzA_L2 n)).2.ne
    have h_ne_right : eLpNorm (fun ξ => w ξ - z ξ) 2 volume ≠ ∞ :=
      (hw.sub hz).2.ne
    simpa using
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n => eLpNorm (fun ξ => wApprox n ξ - zApprox n ξ) 2 volume)
        h_ne_left h_ne_right).1 h_freq_toReal_lim

  -- Time-side: show the L² norms of inverse differences converge to ‖inv w - inv z‖₂.
  -- Inverse transforms of approximants equal the time-side Schwartz functions
  have h_inv_wA : ∀ n,
      (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => wApprox n ξ) t)
        = fun t : ℝ => ψ n t := by
    intro n; simpa [wApprox] using fourierIntegralInv_fourierIntegral_schwartz (ψ n)
  have h_inv_zA : ∀ n,
      (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => zApprox n ξ) t)
        = fun t : ℝ => χ n t := by
    intro n; simpa [zApprox] using fourierIntegralInv_fourierIntegral_schwartz (χ n)

  -- L² membership of inverse approximants
  have hinv_wA_L2 : ∀ n, MemLp (fun t =>
      Real.fourierIntegralInv (fun ξ => wApprox n ξ) t) 2 volume :=
    fun n => by
      have h : MemLp (ψ n) 2 volume := SchwartzMap.memLp (ψ n) (p := (2 : ℝ≥0∞)) (μ := volume)
      convert h using 1
      exact h_inv_wA n
  have hinv_zA_L2 : ∀ n, MemLp (fun t =>
      Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume :=
    fun n => by
      have h : MemLp (χ n) 2 volume := SchwartzMap.memLp (χ n) (p := (2 : ℝ≥0∞)) (μ := volume)
      convert h using 1
      exact h_inv_zA n

  -- Lift time-side to Lp
  let iwALp : ℕ → Lp ℂ 2 volume :=
    fun n => (hinv_wA_L2 n).toLp (fun t => Real.fourierIntegralInv (fun ξ => wApprox n ξ) t)
  let izALp : ℕ → Lp ℂ 2 volume :=
    fun n => (hinv_zA_L2 n).toLp (fun t => Real.fourierIntegralInv (fun ξ => zApprox n ξ) t)
  let iwLp : Lp ℂ 2 volume := hinv_w_L2.toLp (fun t => Real.fourierIntegralInv (fun ξ => w ξ) t)
  let izLp : Lp ℂ 2 volume := hinv_z_L2.toLp (fun t => Real.fourierIntegralInv (fun ξ => z ξ) t)

  -- Convergence: inv(wApprox n) → inv(w), inv(zApprox n) → inv(z) in L² via the closure lemma
  have h_inv_w_tendsto0 : Filter.Tendsto
      (fun n => ENNReal.toReal (eLpNorm (fun t =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    -- Apply continuity of the inverse transform on the closure, using the
    -- frequency-side approximants `wApprox n` for `w`.
    have hwApprox_isFourier :
        ∀ n, ∃ ψn : SchwartzMap ℝ ℂ,
          wApprox n = fun ξ => Frourio.fourierIntegral (fun t => ψn t) ξ := by
      intro n
      refine ⟨ψ n, ?_⟩
      funext ξ; rfl
    exact inverseFourier_tendsto_of_schwartz_approx
      (w := w) (wApprox := wApprox)
      (hw := hw) (hwApprox_L2 := hwA_L2)
      (hwApprox_isFourier := hwApprox_isFourier)
      (hw_tendsto := hw_tendsto)

  have h_inv_z_tendsto0 : Filter.Tendsto
      (fun n => ENNReal.toReal (eLpNorm (fun t =>
          Real.fourierIntegralInv (fun ξ => zApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => z ξ) t) 2 volume))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    -- Same continuity statement for `z` and its approximants `zApprox n`.
    have hzApprox_isFourier :
        ∀ n, ∃ χn : SchwartzMap ℝ ℂ,
          zApprox n = fun ξ => Frourio.fourierIntegral (fun t => χn t) ξ := by
      intro n
      refine ⟨χ n, ?_⟩
      funext ξ; rfl
    exact inverseFourier_tendsto_of_schwartz_approx
      (w := z) (wApprox := zApprox)
      (hw := hz) (hwApprox_L2 := hzA_L2)
      (hwApprox_isFourier := hzApprox_isFourier)
      (hw_tendsto := hz_tendsto)

  -- Conclude time-side convergence of the norms of differences
  have h_time_diff_norm_tendsto0 : Filter.Tendsto
      (fun n => ‖(iwALp n - izALp n) - (iwLp - izLp)‖)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    -- Bound by triangle inequality using the two 0-limits above
    have hw0 := h_inv_w_tendsto0
    have hz0 := h_inv_z_tendsto0
    -- Extract as convergence of Lp norms: already in real via toReal
    -- Use the same inequality as before
    have h_nonneg : ∀ n, 0 ≤ ‖(iwALp n - izALp n) - (iwLp - izLp)‖ := fun _ => norm_nonneg _
    have h_upper : Filter.Tendsto (fun n => ‖iwALp n - iwLp‖ + ‖izALp n - izLp‖)
        Filter.atTop (𝓝 (0 : ℝ)) := by
      -- Identify the two summands with the toReal limits proved above
      have h1 : Filter.Tendsto (fun n => ‖iwALp n - iwLp‖) Filter.atTop (𝓝 0) := by
        refine h_inv_w_tendsto0.congr' ?_
        exact Filter.Eventually.of_forall (fun n => by
          -- re-express the real norms as toReal of eLpNorm via norm_toLp
          have hdiff : MemLp (fun t =>
              Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
                - Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume :=
            (hinv_wA_L2 n).sub hinv_w_L2
          have hcalc : hdiff.toLp _ = iwALp n - iwLp := by
            simpa [iwALp, iwLp] using MemLp.toLp_sub (hinv_wA_L2 n) hinv_w_L2
          have hnorm := Lp.norm_toLp (μ := volume)
              (f := fun t =>
                Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
                  - Real.fourierIntegralInv (fun ξ => w ξ) t) hdiff
          simp only
          rw [← hnorm, hcalc, norm_sub_rev])
      have h2 : Filter.Tendsto (fun n => ‖izALp n - izLp‖) Filter.atTop (𝓝 0) := by
        refine h_inv_z_tendsto0.congr' ?_
        exact Filter.Eventually.of_forall (fun n => by
          have hdiff : MemLp (fun t =>
              Real.fourierIntegralInv (fun ξ => zApprox n ξ) t
                - Real.fourierIntegralInv (fun ξ => z ξ) t) 2 volume :=
            (hinv_zA_L2 n).sub hinv_z_L2
          have hcalc : hdiff.toLp _ = izALp n - izLp := by
            simpa [izALp, izLp] using MemLp.toLp_sub (hinv_zA_L2 n) hinv_z_L2
          have hnorm := Lp.norm_toLp (μ := volume)
              (f := fun t =>
                Real.fourierIntegralInv (fun ξ => zApprox n ξ) t
                  - Real.fourierIntegralInv (fun ξ => z ξ) t) hdiff
          simp only
          rw [← hnorm, hcalc, norm_sub_rev])
      simpa using h1.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ h_upper h_nonneg ?_
    · exact tendsto_const_nhds
    · intro n
      calc ‖iwALp n - izALp n - (iwLp - izLp)‖
          = ‖(iwALp n - iwLp) - (izALp n - izLp)‖ := by
            congr 1
            abel
        _ ≤ ‖iwALp n - iwLp‖ + ‖izALp n - izLp‖ := norm_sub_le _ _

  -- Identify time-side real norms with ENNReal eLpNorms for inverse differences
  have h_time_norm_eq_left : ∀ n,
      ‖iwALp n - izALp n‖
        = ENNReal.toReal (eLpNorm (fun t =>
            Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
              - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume) := by
    intro n
    have hdiff : MemLp (fun t =>
        Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
          - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume :=
      (hinv_wA_L2 n).sub (hinv_zA_L2 n)
    have hcalc : hdiff.toLp _ = iwALp n - izALp n := by
      simpa [iwALp, izALp] using MemLp.toLp_sub (hinv_wA_L2 n) (hinv_zA_L2 n)
    have hnorm := Lp.norm_toLp (μ := volume)
        (f := fun t =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) hdiff
    simpa [hdiff, hcalc, norm_sub_rev] using hnorm

  have h_time_norm_eq_right :
      ‖iwLp - izLp‖
        = ENNReal.toReal (eLpNorm (fun t =>
            Real.fourierIntegralInv (fun ξ => w ξ) t
              - Real.fourierIntegralInv (fun ξ => z ξ) t) 2 volume) := by
    have hdiff : MemLp (fun t =>
        Real.fourierIntegralInv (fun ξ => w ξ) t
          - Real.fourierIntegralInv (fun ξ => z ξ) t) 2 volume :=
      hinv_w_L2.sub hinv_z_L2
    have hcalc : hdiff.toLp _ = iwLp - izLp := by
      simpa [iwLp, izLp] using MemLp.toLp_sub hinv_w_L2 hinv_z_L2
    have hnorm := Lp.norm_toLp (μ := volume)
        (f := fun t =>
          Real.fourierIntegralInv (fun ξ => w ξ) t
            - Real.fourierIntegralInv (fun ξ => z ξ) t) hdiff
    simpa [hdiff, hcalc, norm_sub_rev] using hnorm

  have h_time_toReal_lim : Filter.Tendsto
      (fun n => ENNReal.toReal (eLpNorm (fun t =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume))
      Filter.atTop (𝓝 (ENNReal.toReal (eLpNorm (fun t =>
        Real.fourierIntegralInv (fun ξ => w ξ) t
          - Real.fourierIntegralInv (fun ξ => z ξ) t) 2 volume))) := by
    have h_sub_tendsto : Filter.Tendsto (fun n => iwALp n - izALp n)
        Filter.atTop (𝓝 (iwLp - izLp)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact h_time_diff_norm_tendsto0
    have h_norm_tendsto := (Continuous.tendsto continuous_norm _).comp h_sub_tendsto
    refine h_norm_tendsto.congr' ?_ |>.trans ?_
    · refine Filter.Eventually.of_forall (fun n => ?_)
      simp only [Function.comp_apply]
      exact h_time_norm_eq_left n
    · simp [h_time_norm_eq_right]

  have h_time_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun t =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume)
      Filter.atTop (𝓝 (eLpNorm (fun t =>
        Real.fourierIntegralInv (fun ξ => w ξ) t
          - Real.fourierIntegralInv (fun ξ => z ξ) t) 2 volume)) := by
    have h_ne_left : ∀ n,
        eLpNorm (fun t =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume ≠ ∞ :=
      fun n => ((hinv_wA_L2 n).sub (hinv_zA_L2 n)).2.ne
    have h_ne_right : eLpNorm (fun t =>
        Real.fourierIntegralInv (fun ξ => w ξ) t
          - Real.fourierIntegralInv (fun ξ => z ξ) t) 2 volume ≠ ∞ :=
      (hinv_w_L2.sub hinv_z_L2).2.ne
    simpa using
      (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n => eLpNorm (fun t =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume)
        h_ne_left h_ne_right).1 h_time_toReal_lim

  -- Since for every n, the time- and frequency-side norms agree (by Schwartz isometry),
  -- the two limits must be equal by uniqueness of limits in a Hausdorff space.
  have h_seq_eq : Filter.Tendsto
      (fun n => eLpNorm (fun t =>
          Real.fourierIntegralInv (fun ξ => wApprox n ξ) t
            - Real.fourierIntegralInv (fun ξ => zApprox n ξ) t) 2 volume)
      Filter.atTop (𝓝 (eLpNorm (fun ξ => w ξ - z ξ) 2 volume)) := by
    -- Transport the frequency-side limit along the pointwise equality of sequences
    exact h_freq_tendsto.congr'
      (Filter.Eventually.of_forall (fun n => by
        have := h_isometry_schwartz n
        simpa using this.symm))

  -- Uniqueness of limits gives the desired equality of constants
  exact tendsto_nhds_unique h_time_tendsto h_seq_eq

/-- L² continuity of the inverse Fourier transform on the closure of the
Schwartz range.

If `u n` are Fourier transforms of Schwartz functions and converge to `v` in L²
on the frequency side (with `v ∈ L²`), then applying the inverse Fourier integrals
converges in L² on the time side without assuming `v` itself is a Fourier transform
of a Schwartz function. This packages the fact that the inverse transform extends
to an L² isometry on the closure of the Schwartz range. -/
lemma inverseFourier_tendsto_L2_on_closure
    {u : ℕ → ℝ → ℂ} {v : ℝ → ℂ}
    (hu_schw : ∀ n, ∃ φn : SchwartzMap ℝ ℂ,
        u n = fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φn t) ξ)
    (hv_L2 : MemLp v 2 volume)
    (h_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun ξ => u n ξ - v ξ) 2 volume)
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n =>
      eLpNorm (fun t =>
        Real.fourierIntegralInv (fun ξ => u n ξ) t
          - Real.fourierIntegralInv (fun ξ => v ξ) t) 2 volume)
      Filter.atTop (𝓝 0) := by
  classical
  -- Step 0: pick Schwartz witnesses for the sequence `u n` on the frequency side.
  choose φ hφ_repr using hu_schw

  -- Step 1: approximate the target `v` in L² by Fourier transforms of Schwartz
  -- functions on the time side. This encodes the density of the Schwartz range
  -- under the Fourier transform in L² (Plancherel extension). We only need the
  -- existence of some approximating sequence and its L² convergence; the full
  -- construction is provided elsewhere in this development.
  --
  -- Precisely, we assume the existence of a sequence `ψ m : SchwartzMap ℝ ℂ`
  -- such that `v_m := (ξ ↦ fourierIntegral (ψ m) ξ)` satisfies
  --   eLpNorm (v - v_m) 2 → 0  as m → ∞.
  -- This follows from the closure of the Schwartz range in L²(ℝ) on the
  -- frequency side ensured by the Plancherel theorem.
  -- We can reuse the given witnesses `φ` for `u n`. Setting `ψ := φ` gives
  -- frequency-side approximants `vApprox m = u m`, hence the desired
  -- convergence is exactly `h_tendsto` (up to swapping the subtraction order).
  obtain ⟨ψ, hψ_approx⟩ :
      ∃ (ψ : ℕ → SchwartzMap ℝ ℂ),
        Filter.Tendsto (fun m =>
          eLpNorm (fun ξ : ℝ =>
            v ξ - Frourio.fourierIntegral (fun t : ℝ => ψ m t) ξ) 2 volume)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    refine ⟨φ, ?_⟩
    -- Symmetry of the L² error under exchanging the order in the difference.
    have h_symm : ∀ m,
        eLpNorm (fun ξ : ℝ =>
            v ξ - Frourio.fourierIntegral (fun t : ℝ => φ m t) ξ) 2 volume
          = eLpNorm (fun ξ : ℝ =>
              Frourio.fourierIntegral (fun t : ℝ => φ m t) ξ - v ξ) 2 volume := by
      intro m
      have hneg_ae :
          (fun ξ : ℝ => v ξ - Frourio.fourierIntegral (fun t : ℝ => φ m t) ξ)
            =ᵐ[volume]
              fun ξ : ℝ =>
                - (Frourio.fourierIntegral (fun t : ℝ => φ m t) ξ - v ξ) :=
        Filter.Eventually.of_forall <| by
          intro ξ; simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      have hcongr :=
        eLpNorm_congr_ae (μ := volume) (p := (2 : ℝ≥0∞)) hneg_ae
      simpa using hcongr.trans
        (eLpNorm_neg (f := fun ξ : ℝ =>
            Frourio.fourierIntegral (fun t : ℝ => φ m t) ξ - v ξ)
          (p := (2 : ℝ≥0∞)) (μ := volume))
    -- Transport convergence along the pointwise equalities `u m = F[φ m]`.
    refine h_tendsto.congr' ?_
    exact Filter.Eventually.of_forall (fun m => by
      simpa [hφ_repr m] using (h_symm m).symm)

  -- Define the frequency-side Schwartz approximants to `v`.
  let vApprox : ℕ → ℝ → ℂ :=
    fun m ξ => Frourio.fourierIntegral (fun t : ℝ => ψ m t) ξ

  -- Step 2: for each fixed approximant `vApprox m`, use the L² continuity of the
  -- inverse transform on Schwartz ranges to transport the convergence of `u n → vApprox m`.
  have h_inv_cont_each_m : ∀ m,
      Filter.Tendsto (fun n =>
        eLpNorm (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ : ℝ => u n ξ) t
            - Real.fourierIntegralInv (fun ξ : ℝ => vApprox m ξ) t) 2 volume)
        Filter.atTop
        (𝓝 (eLpNorm (fun ξ => v ξ - vApprox m ξ) 2 volume)) := by
    intro m
    -- Rewrite the target using the existing lemma for the case when the limit is
    -- also a Fourier transform of a Schwartz function.
    have hv_schw : ∃ ψm : SchwartzMap ℝ ℂ,
        (fun ξ : ℝ => vApprox m ξ)
          = fun ξ : ℝ =>
              Frourio.fourierIntegral (fun t : ℝ => ψm t) ξ := by
      refine ⟨ψ m, ?_⟩; rfl
    -- Reduce to the case handled by `inverseFourier_tendsto_L2_of_tendsto_L2` by
    -- transporting the frequency-side convergence along pointwise equalities.
    have h_freq_congr : Filter.Tendsto
        (fun n => eLpNorm (fun ξ => u n ξ - vApprox m ξ) 2 volume)
        Filter.atTop (𝓝 (eLpNorm (fun ξ => v ξ - vApprox m ξ) 2 volume)) := by
      -- Lift to L² and use continuity of translation + norm.
      classical
      -- L² membership
      have hu_mem : ∀ n, MemLp (u n) 2 volume := by
        intro n; simpa [hφ_repr n] using fourierIntegral_memLp_of_schwartz (φ n)
      have hv_mem : MemLp v 2 volume := hv_L2
      have hvA_mem : MemLp (vApprox m) 2 volume := by
        -- `vApprox m` is the Fourier transform of a Schwartz function
        simpa [vApprox] using fourierIntegral_memLp_of_schwartz (ψ m)

      -- Lift to Lp
      let uLp : ℕ → Lp ℂ 2 volume := fun n => (hu_mem n).toLp (u n)
      let vLp : Lp ℂ 2 volume := hv_mem.toLp v
      let aLp : Lp ℂ 2 volume := hvA_mem.toLp (vApprox m)

      -- Show uLp → vLp using the given frequency-side convergence to v
      have h_norm_eq0 : ∀ n,
          ‖uLp n - vLp‖
            = ENNReal.toReal (eLpNorm (fun ξ => u n ξ - v ξ) 2 volume) := by
        intro n
        have hdiff : MemLp (fun ξ => u n ξ - v ξ) 2 volume := (hu_mem n).sub hv_mem
        have hcalc : ((hu_mem n).sub hv_mem).toLp (fun ξ => u n ξ - v ξ)
              = uLp n - vLp := by
          simpa [uLp, vLp] using MemLp.toLp_sub (hu_mem n) hv_mem
        have hnorm := Lp.norm_toLp (μ := volume)
            (f := fun ξ => u n ξ - v ξ) hdiff
        simpa [hdiff, hcalc, norm_sub_rev]
          using hnorm

      have h_toReal0 : Filter.Tendsto
          (fun n => ENNReal.toReal (eLpNorm (fun ξ => u n ξ - v ξ) 2 volume))
          Filter.atTop (𝓝 (0 : ℝ)) := by
        have h_ne_top : ∀ n,
            eLpNorm (fun ξ => u n ξ - v ξ) 2 volume ≠ ∞ :=
          fun n => ((hu_mem n).sub hv_mem).2.ne
        have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp
        simpa using
          (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
            (f := fun n => eLpNorm (fun ξ => u n ξ - v ξ) 2 volume)
            h_ne_top h_zero_ne_top).mpr h_tendsto

      have h_uLp_tendsto : Filter.Tendsto uLp Filter.atTop (𝓝 vLp) := by
        -- Characterize via norm of the difference → 0
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact h_toReal0.congr'
          (Filter.Eventually.of_forall (fun n => (h_norm_eq0 n).symm))

      -- Now translate by aLp and take norms.
      have h_sub_cont : Continuous fun x : Lp ℂ 2 volume => x - aLp := by
        simpa [sub_eq_add_neg] using
          (continuous_id.add (continuous_const : Continuous fun _ : Lp ℂ 2 volume => -aLp))
      have h_translated := (h_sub_cont.tendsto vLp).comp h_uLp_tendsto
      have h_norm_tendsto :
          Filter.Tendsto (fun n => ‖uLp n - aLp‖)
            Filter.atTop (𝓝 ‖vLp - aLp‖) :=
        (Continuous.tendsto continuous_norm _).comp h_translated

      -- Identify the norms with eLpNorms (converted to ℝ via toReal)
      have h_norm_eq_left : ∀ n,
          ‖uLp n - aLp‖
            = ENNReal.toReal (eLpNorm (fun ξ => u n ξ - vApprox m ξ) 2 volume) := by
        intro n
        have hdiff : MemLp (fun ξ => u n ξ - vApprox m ξ) 2 volume :=
          (hu_mem n).sub hvA_mem
        have hcalc : ((hu_mem n).sub hvA_mem).toLp (fun ξ => u n ξ - vApprox m ξ)
              = uLp n - aLp := by
          simpa [uLp, aLp] using MemLp.toLp_sub (hu_mem n) hvA_mem
        have hnorm := Lp.norm_toLp (μ := volume)
            (f := fun ξ => u n ξ - vApprox m ξ) hdiff
        simpa [hdiff, hcalc, norm_sub_rev]
          using hnorm

      have h_norm_eq_right :
          ‖vLp - aLp‖
            = ENNReal.toReal (eLpNorm (fun ξ => v ξ - vApprox m ξ) 2 volume) := by
        have hdiff : MemLp (fun ξ => v ξ - vApprox m ξ) 2 volume :=
          hv_mem.sub hvA_mem
        have hcalc : (hv_mem.sub hvA_mem).toLp (fun ξ => v ξ - vApprox m ξ)
              = vLp - aLp := by
          simpa [vLp, aLp] using MemLp.toLp_sub hv_mem hvA_mem
        have hnorm := Lp.norm_toLp (μ := volume)
            (f := fun ξ => v ξ - vApprox m ξ) hdiff
        simpa [hdiff, hcalc, norm_sub_rev]
          using hnorm

      -- Convert the real convergence to ENNReal convergence via toReal
      have h_toReal_lim : Filter.Tendsto
          (fun n => ENNReal.toReal
              (eLpNorm (fun ξ => u n ξ - vApprox m ξ) 2 volume))
          Filter.atTop (𝓝 (ENNReal.toReal
              (eLpNorm (fun ξ => v ξ - vApprox m ξ) 2 volume))) := by
        have h' := h_norm_tendsto.congr'
          (Filter.Eventually.of_forall (fun n => (h_norm_eq_left n)))
        simpa [h_norm_eq_right] using h'

      -- Eventual finiteness for applying `tendsto_toReal_iff` in reverse
      have h_ne_top_left : ∀ n,
          eLpNorm (fun ξ => u n ξ - vApprox m ξ) 2 volume ≠ ∞ := by
        intro n; exact ((hu_mem n).sub hvA_mem).2.ne
      have h_ne_top_right : eLpNorm (fun ξ => v ξ - vApprox m ξ) 2 volume ≠ ∞ := by
        exact (hv_mem.sub hvA_mem).2.ne

      simpa using
        (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
          (f := fun n => eLpNorm (fun ξ => u n ξ - vApprox m ξ) 2 volume)
          h_ne_top_left h_ne_top_right).1 h_toReal_lim
    -- Identify inverse transforms with the Schwartz representatives
    have h_inv_u : ∀ n,
        (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => u n ξ) t)
          = fun t : ℝ => φ n t := by
      intro n; simpa [hφ_repr n]
        using fourierIntegralInv_fourierIntegral_schwartz (φ n)
    have h_inv_vA :
        (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => vApprox m ξ) t)
          = fun t : ℝ => ψ m t := by
      simpa [vApprox]
        using fourierIntegralInv_fourierIntegral_schwartz (ψ m)

    -- Equate time-side and frequency-side L² errors for Schwartz pairs
    have h_err_freq : ∀ n,
        eLpNorm (fun ξ : ℝ => u n ξ - vApprox m ξ) 2 volume
          = eLpNorm (fun t : ℝ => φ n t - ψ m t) 2 volume := by
      intro n
      have hsub :
          (fun ξ : ℝ => u n ξ - vApprox m ξ)
            = fun ξ : ℝ =>
                Frourio.fourierIntegral (fun t : ℝ => φ n t - ψ m t) ξ := by
        funext ξ
        have hlin := fourierIntegral_sub
            (f := fun t : ℝ => φ n t) (g := fun t : ℝ => ψ m t)
            (hf := schwartz_integrable (φ n)) (hg := schwartz_integrable (ψ m))
            (ξ := ξ)
        simpa [hφ_repr n, vApprox, sub_eq_add_neg] using hlin.symm
      simpa [hsub] using fourierIntegral_eLpNorm_eq (φ := φ n - ψ m)

    have h_err_time : ∀ n,
        eLpNorm (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ : ℝ => u n ξ) t
            - Real.fourierIntegralInv (fun ξ : ℝ => vApprox m ξ) t) 2 volume
          = eLpNorm (fun t : ℝ => φ n t - ψ m t) 2 volume := by
      intro n
      have : (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ : ℝ => u n ξ) t
            - Real.fourierIntegralInv (fun ξ : ℝ => vApprox m ξ) t)
            = fun t : ℝ => φ n t - ψ m t := by
        funext t; simp [h_inv_u n, h_inv_vA]
      simp [this]

    -- Consequently, time- and frequency-side errors agree for each n
    have h_time_eq_freq : ∀ n,
        eLpNorm (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ : ℝ => u n ξ) t
            - Real.fourierIntegralInv (fun ξ : ℝ => vApprox m ξ) t) 2 volume
          = eLpNorm (fun ξ : ℝ => u n ξ - vApprox m ξ) 2 volume := by
      intro n; simpa [h_err_time n] using (h_err_freq n).symm

    -- As a byproduct, we also inherit the limit along n from the frequency side
    have _h_tendsto_time_const : Filter.Tendsto
        (fun n => eLpNorm (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ : ℝ => u n ξ) t
            - Real.fourierIntegralInv (fun ξ : ℝ => vApprox m ξ) t) 2 volume)
        Filter.atTop (𝓝 (eLpNorm (fun ξ => v ξ - vApprox m ξ) 2 volume)) := by
      refine h_freq_congr.congr'
        (Filter.Eventually.of_forall (fun n => (h_time_eq_freq n).symm))
    -- This is exactly the desired statement for this `m`.
    simpa using _h_tendsto_time_const

  -- Step 3: use the triangle inequality and the L² isometry of the inverse transform
  -- on the closure to pass from `vApprox m` to `v`. The standard diagonal/ε–N
  -- argument shows:
  --   limsup_n eLpNorm(inv(u n) - inv(v))
  --     ≤ limsup_n ( eLpNorm(inv(u n) - inv(vApprox m))
  --                 + eLpNorm(inv(vApprox m) - inv(v)) )
  --     ≤ 0 + eLpNorm(vApprox m - v)
  -- and then let `m → ∞` using `hψ_approx`.
  -- We encode this as a final placeholder, as it only combines the above steps
  -- with the isometry property on the closure.
  -- Conclude: eLpNorm(inv(u n) - inv(v)) → 0 as n → ∞.
  -- Shortcut: use the L² isometry of the inverse transform on the closure
  -- to identify time-side distances with frequency-side ones for each n.
  -- Then the desired tendsto follows from the given frequency-side tendsto.
  classical
  -- L² membership of each u n on the frequency side
  have hu_mem : ∀ n, MemLp (u n) 2 volume :=
    fun n => by
      simpa [hφ_repr n] using fourierIntegral_memLp_of_schwartz (φ n)

  -- Approximation hypothesis for v on the frequency side derived from hψ_approx
  have hz_approx : ∀ ε > 0, ∃ χ : SchwartzMap ℝ ℂ,
      eLpNorm (fun ξ => v ξ - Frourio.fourierIntegral (fun t : ℝ => χ t) ξ) 2 volume
        < ENNReal.ofReal ε := by
    intro ε hε
    -- From tendsto to 0, eventually the error is < ε; pick such an index.
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := by
      simpa [ENNReal.ofReal_pos] using hε
    have h_event : ∀ᶠ m in Filter.atTop,
        eLpNorm (fun ξ => v ξ - vApprox m ξ) 2 volume < ENNReal.ofReal ε := by
      -- Turn `hψ_approx` into an eventual strict bound using continuity
      -- of the constant map and the order topology on ℝ≥0∞.
      refine Filter.Tendsto.eventually_lt hψ_approx tendsto_const_nhds hpos
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 h_event
    refine ⟨ψ M, ?_⟩
    simpa [vApprox]
      using hM M le_rfl

  -- For each fixed n, apply the closure isometry with `w = u n` and `z = v`.
  have h_isom_n : ∀ n,
      eLpNorm (fun t =>
        Real.fourierIntegralInv (fun ξ => u n ξ) t
          - Real.fourierIntegralInv (fun ξ => v ξ) t) 2 volume
        = eLpNorm (fun ξ => u n ξ - v ξ) 2 volume := by
    intro n
    -- Trivial approximation for `w = u n` by itself
    have hw_approx : ∀ ε > 0, ∃ ψw : SchwartzMap ℝ ℂ,
        eLpNorm (fun ξ => u n ξ
            - Frourio.fourierIntegral (fun t : ℝ => ψw t) ξ) 2 volume
          < ENNReal.ofReal ε := by
      intro ε hε
      refine ⟨φ n, ?_⟩
      -- Exact equality gives zero error, hence strictly less than any positive bound
      simpa [hφ_repr n]
    -- Apply the isometry on the closure of the Schwartz range
    exact inverseFourier_isometry_on_closure
      (w := u n) (z := v)
      (hw := hu_mem n) (hz := hv_L2)
      (hw_approx := hw_approx) (hz_approx := hz_approx)

  -- Transport the frequency-side convergence to the time side via the isometry
  refine h_tendsto.congr'
    (Filter.Eventually.of_forall (fun n => (h_isom_n n).symm))

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

/-- A.e. Fourier inversion for L¹ ∩ L² functions (signature placeholder).

If `g ∈ L¹(ℝ) ∩ L²(ℝ)`, then the inverse Fourier integral of its Fourier
integral recovers `g` almost everywhere, with the explicit kernel convention
`Frourio.fourierIntegral` used in this project. -/
lemma fourierIntegralInv_fourierIntegral_ae_of_L1_L2
    (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => Frourio.fourierIntegral g ξ) t)
      =ᵐ[volume] g := by
  classical
  obtain ⟨φ, hφ_L1, hφ_L2, hφ_tendsto_L1, hφ_tendsto_L2⟩ :=
    Frourio.exists_schwartz_L1_L2_approx g hg_L1 hg_L2

  have h_inv_schwartz : ∀ n : ℕ,
      (fun t : ℝ =>
        Real.fourierIntegralInv
          (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ) t)
        = fun t : ℝ => φ n t := by
    intro n
    exact fourierIntegralInv_fourierIntegral_schwartz (φ n)

  have h_fourier_pointwise : ∀ ξ : ℝ,
      Filter.Tendsto (fun n => Frourio.fourierIntegral (fun t => φ n t) ξ)
        Filter.atTop (𝓝 (Frourio.fourierIntegral g ξ)) := by
    intro ξ
    exact
      Frourio.fourierIntegral_tendsto_of_schwartz_approx
        (hf_L1 := hg_L1) (hφ_L1 := hφ_L1) (hφ_tendsto_L1 := hφ_tendsto_L1) ξ

  -- New strategy (L² route, no frequency-side L¹ convergence required):
  -- 1) Use Plancherel on Schwartz differences to show (F φ_n) is Cauchy in L².
  -- 2) Let H be the L² limit of (F φ_n).
  -- 3) From L¹ convergence on time side, (F φ_n)(ξ) → F g(ξ) pointwise.
  --    Apply a.e.-uniqueness of L² limits to deduce H = F g a.e.
  -- 4) By L² isometry of the inverse transform on the closure, F⁻¹(F φ_n) → F⁻¹ H in L².
  --    But F⁻¹(F φ_n) = φ_n pointwise, hence φ_n → F⁻¹ H in L². Since also φ_n → g in L²,
  --    conclude F⁻¹ H = g a.e. Combining with H = F g a.e., obtain F⁻¹(F g) = g a.e.

  -- Step 3: Convergence of inverse Fourier integrals
  -- New Step 4 (L²-only route): identify the inverse limit in L² and conclude a.e.
  -- We avoid pointwise dominated convergence for the inverse integral and instead
  -- use uniqueness of L² limits.

  -- It remains to produce the second L² limit: φ n → inv(F[g]) in L².
  -- Using that invF(F[φ n]) = φ n and the (extended) L² isometry of the inverse
  -- transform, this follows from L² convergence of F[φ n] to F[g] on the
  -- frequency side. This part is established earlier via the density/Plancherel
  -- machinery, and we reuse it here.
  have h_inv_L2_limit : Filter.Tendsto
      (fun n => eLpNorm (fun t : ℝ =>
          Real.fourierIntegralInv (fun ξ : ℝ => Frourio.fourierIntegral g ξ) t
            - φ n t) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    classical
    -- Frequency-side functions
    let u : ℕ → ℝ → ℂ := fun n ξ => Frourio.fourierIntegral (fun t => φ n t) ξ
    let v : ℝ → ℂ := fun ξ => Frourio.fourierIntegral g ξ

    -- Each u n is the Fourier transform of a Schwartz function
    have hu_schw : ∀ n, ∃ φn : SchwartzMap ℝ ℂ,
        u n = fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φn t) ξ := by
      intro n; exact ⟨φ n, rfl⟩

    -- L² membership of v on the frequency side for g ∈ L¹ ∩ L²
    have hv_L2 : MemLp v 2 volume :=
      fourierIntegral_memLp_L1_L2 hg_L1 hg_L2

    -- Build the L² limit of u n on the frequency side via the approximation machinery
    obtain ⟨ψLp, ψ_lim, hψLp_def, hψ_tendsto⟩ :=
      fourierIntegral_memLp_limit
        (hf_L1 := hg_L1) (hf_L2 := hg_L2)
        (hφ_L1 := hφ_L1) (hφ_L2 := hφ_L2) (hφ_tendsto := hφ_tendsto_L2)

    -- Package u n as concrete functions and record their L² membership
    have hu_mem : ∀ n, MemLp (u n) 2 volume :=
      fun n => by simpa [u] using fourierIntegral_memLp_of_schwartz (φ n)

    -- Show eLpNorm(gLim - u n) → 0 where gLim is a representative of ψ_lim
    let gLim : ℝ → ℂ := fun ξ => (ψ_lim : ℝ → ℂ) ξ
    have hgLim_L2 : MemLp gLim 2 volume := Lp.memLp ψ_lim

    have h_norm_eq : ∀ n,
        ‖ψLp n - ψ_lim‖
          = ENNReal.toReal (eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume) := by
      intro n
      have hdiff : MemLp (fun ξ => gLim ξ - u n ξ) 2 volume :=
        hgLim_L2.sub (hu_mem n)
      have hcalc :
          ((hgLim_L2.sub (hu_mem n)).toLp (fun ξ => gLim ξ - u n ξ))
            = ψ_lim - ψLp n := by
        -- Rewrite Lp difference via MemLp.toLp_sub
        simpa [gLim, u, hψLp_def n] using MemLp.toLp_sub hgLim_L2 (hu_mem n)
      have hnorm :=
        Lp.norm_toLp (μ := volume)
          (f := fun ξ : ℝ => gLim ξ - u n ξ) hdiff
      simpa [hdiff, hcalc, norm_sub_rev]
        using hnorm

    have h_toReal_tendsto : Filter.Tendsto
        (fun n => ENNReal.toReal (eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume))
        Filter.atTop (𝓝 (0 : ℝ)) := by
      -- Convert Lp convergence ψLp → ψ_lim to real convergence of norms
      have : Filter.Tendsto (fun n => ‖ψLp n - ψ_lim‖)
          Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa [tendsto_iff_norm_sub_tendsto_zero]
          using hψ_tendsto
      refine this.congr' (Filter.Eventually.of_forall (fun n => ?_))
      exact h_norm_eq n

    have h_freq_to_zero : Filter.Tendsto
        (fun n => eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      -- Upgrade real convergence to ENNReal via tendsto_toReal_iff
      have h_ne_top : ∀ n,
          eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume ≠ ∞ :=
        fun n => (hgLim_L2.sub (hu_mem n)).2.ne
      have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp
      exact (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
        (f := fun n => eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume)
        h_ne_top h_zero_ne_top).mp h_toReal_tendsto

    -- Pointwise convergence on the frequency side comes from L¹ convergence on time side
    have h_pointwise_fun : Filter.Tendsto (fun n => fun ξ => u n ξ)
        Filter.atTop (𝓝 v) := by
      -- Use `tendsto_pi_nhds` from pointwise convergence at each frequency
      refine (tendsto_pi_nhds.mpr ?_)
      intro ξ; simpa [u, v]
        using h_fourier_pointwise ξ

    -- Identify the L² limit ψ_lim with v a.e. by uniqueness of L² limits
    have h_v_eq_gLim : v =ᵐ[volume] gLim :=
      ae_eq_of_L2_limit_pointwise (φ := u) (g := gLim) (h := v)
        (hφ_L2 := hu_mem) (hg_L2 := hgLim_L2)
        (hφ_tendsto_L2 := h_freq_to_zero)
        (h_pointwise := h_pointwise_fun)

    -- Transport the frequency-side limit to the target `v` using a.e. congruence
    have h_freq_tendsto : Filter.Tendsto
        (fun n => eLpNorm (fun ξ => u n ξ - v ξ) 2 volume)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      -- Replace v by gLim in the norm using a.e. equality
      refine h_freq_to_zero.congr' ?_
      exact Filter.Eventually.of_forall (fun n => by
        have h_ae_sub :
            (fun ξ => gLim ξ - u n ξ)
              =ᵐ[volume] (fun ξ => v ξ - u n ξ) := by
          have : (fun ξ => gLim ξ) =ᵐ[volume] v := h_v_eq_gLim.symm
          exact this.sub (Filter.EventuallyEq.rfl)
        have h_eq :=
          (eLpNorm_congr_ae (μ := volume) (p := (2 : ℝ≥0∞)) h_ae_sub)
        -- Swap the subtraction order on the right using symmetry of the L² quasi-norm
        have h_eq' :
            eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume
              = eLpNorm (fun ξ => u n ξ - v ξ) 2 volume := by
          rw [h_eq]
          exact eLpNorm_sub_comm (v) (u n) 2 volume
        exact h_eq'
        )

    -- Transfer frequency-side L² convergence through the inverse transform
    have h_inv :=
      inverseFourier_tendsto_L2_on_closure hu_schw hv_L2 h_freq_tendsto

    -- Rewrite the target using `invF(F[φ n]) = φ n` and symmetry of the norm
    refine h_inv.congr' (Filter.Eventually.of_forall (fun n => by
      have h_id := h_inv_schwartz n
      -- Use symmetry: ‖a - b‖₂ = ‖b - a‖₂
      simp only [u, v, h_id]
      exact eLpNorm_sub_comm (fun t => (φ n) t)
        (fun t => fourierIntegralInv (fun ξ => fourierIntegral g ξ) t) 2 volume
      ))

  -- Finally, use the L² uniqueness lemma with the two strong L² limits.
  -- First, record L²-membership of the inverse transform of F[g]
  have hv : MemLp (fun t : ℝ =>
      Real.fourierIntegralInv (fun ξ : ℝ => Frourio.fourierIntegral g ξ) t) 2 volume := by
    classical
    -- View the frequency-side function as an abstract `w` in L².
    let w : ℝ → ℂ := fun ξ => Frourio.fourierIntegral g ξ
    have hw : MemLp w 2 volume :=
      fourierIntegral_memLp_L1_L2 hg_L1 hg_L2
    -- Approximation of `w` in L² by Fourier transforms of Schwartz functions.
    -- This follows from the Plancherel/density machinery developed earlier and
    -- is encoded abstractly by an existence statement of the form required by
    -- `inverseFourierIntegral_memLp_of_schwartz_approx`.
    have hw_approx : ∀ ε > 0, ∃ ψ : SchwartzMap ℝ ℂ,
        eLpNorm (fun ξ => w ξ - Frourio.fourierIntegral (fun t : ℝ => ψ t) ξ) 2 volume
          < ENNReal.ofReal ε := by
      intro ε hε
      -- Step 1: obtain frequency-side L² convergence
      --   eLpNorm (w - F[φ n])₂ → 0
      -- from the time-side L¹/L² convergence of `φ n → g` via Plancherel.
      have h_freq_tendsto : Filter.Tendsto
          (fun n =>
            eLpNorm (fun ξ =>
              w ξ - Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ) 2 volume)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
        -- Rephrase the statement using the explicit description `w = F[g]`.
        have h_freq' : Filter.Tendsto
            (fun n =>
              eLpNorm (fun ξ =>
                Frourio.fourierIntegral g ξ
                  - Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ) 2 volume)
            Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
          classical
          -- Frequency-side sequence and candidate limit.
          let u : ℕ → ℝ → ℂ :=
            fun n ξ => Frourio.fourierIntegral (fun t => φ n t) ξ
          let v : ℝ → ℂ := fun ξ => Frourio.fourierIntegral g ξ

          -- Build the L² limit of `u n` via the approximation machinery.
          obtain ⟨ψLp, ψ_lim, hψLp_def, hψ_tendsto⟩ :=
            fourierIntegral_memLp_limit
              (hf_L1 := hg_L1) (hf_L2 := hg_L2)
              (hφ_L1 := hφ_L1) (hφ_L2 := hφ_L2)
              (hφ_tendsto := hφ_tendsto_L2)

          -- Representative of the L² limit as a concrete function.
          let gLim : ℝ → ℂ := fun ξ => (ψ_lim : ℝ → ℂ) ξ
          have hgLim_L2 : MemLp gLim 2 volume := Lp.memLp ψ_lim

          -- L² membership of each `u n`.
          have hu_mem : ∀ n, MemLp (u n) 2 volume := by
            intro n
            simpa [u] using fourierIntegral_memLp_of_schwartz (φ n)

          -- Express `‖ψLp n - ψ_lim‖` via the eLpNorm of `gLim - u n`.
          have h_norm_eq : ∀ n,
              ‖ψLp n - ψ_lim‖
                = ENNReal.toReal
                    (eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume) := by
            intro n
            have hdiff : MemLp (fun ξ => gLim ξ - u n ξ) 2 volume :=
              hgLim_L2.sub (hu_mem n)
            have hcalc :
                ((hgLim_L2.sub (hu_mem n)).toLp
                    (fun ξ => gLim ξ - u n ξ))
                  = ψ_lim - ψLp n := by
              -- Rewrite Lp difference via `MemLp.toLp_sub`.
              simpa [gLim, u, hψLp_def n] using
                MemLp.toLp_sub hgLim_L2 (hu_mem n)
            have hnorm :=
              Lp.norm_toLp (μ := volume)
                (f := fun ξ : ℝ => gLim ξ - u n ξ) hdiff
            simpa [hdiff, hcalc, norm_sub_rev] using hnorm

          -- Convert Lp convergence `ψLp → ψ_lim` to eLpNorm convergence.
          have h_toReal_tendsto : Filter.Tendsto
              (fun n =>
                ENNReal.toReal
                  (eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume))
              Filter.atTop (𝓝 (0 : ℝ)) := by
            have : Filter.Tendsto (fun n => ‖ψLp n - ψ_lim‖)
                Filter.atTop (𝓝 (0 : ℝ)) :=
              (tendsto_iff_norm_sub_tendsto_zero).1 hψ_tendsto
            refine this.congr' (Filter.Eventually.of_forall (fun n => ?_))
            exact h_norm_eq n

          have h_freq_to_zero : Filter.Tendsto
              (fun n =>
                eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume)
              Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
            -- Upgrade real convergence to ENNReal convergence.
            have h_ne_top : ∀ n,
                eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume ≠ ∞ :=
              fun n => (hgLim_L2.sub (hu_mem n)).2.ne
            have h_zero_ne_top : (0 : ℝ≥0∞) ≠ ∞ := by simp
            exact
              (ENNReal.tendsto_toReal_iff (fi := Filter.atTop)
                  (f :=
                    fun n =>
                      eLpNorm (fun ξ => gLim ξ - u n ξ) 2 volume)
                  h_ne_top h_zero_ne_top).mp h_toReal_tendsto

          -- Pointwise convergence of `u n` to `v` on the frequency side.
          have h_pointwise_fun :
              Filter.Tendsto (fun n => fun ξ => u n ξ)
                Filter.atTop (𝓝 v) := by
            refine (tendsto_pi_nhds.mpr ?_)
            intro ξ
            simpa [u, v] using h_fourier_pointwise ξ

          -- Identify the limit function `gLim` with `v` a.e. via L² uniqueness.
          have h_v_eq_gLim : v =ᵐ[volume] gLim :=
            ae_eq_of_L2_limit_pointwise
              (φ := u) (g := gLim) (h := v)
              (hφ_L2 := hu_mem) (hg_L2 := hgLim_L2)
              (hφ_tendsto_L2 := h_freq_to_zero)
              (h_pointwise := h_pointwise_fun)

          -- Transport the L² convergence from `gLim` to `v` using the a.e. equality.
          have h_freq_to_zero' : Filter.Tendsto
              (fun n =>
                eLpNorm (fun ξ => v ξ - u n ξ) 2 volume)
              Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
            refine h_freq_to_zero.congr'
              (Filter.Eventually.of_forall (fun n => ?_))
            have h_ae_sub :
                (fun ξ => gLim ξ - u n ξ)
                  =ᵐ[volume] (fun ξ => v ξ - u n ξ) := by
              have : (fun ξ => gLim ξ) =ᵐ[volume] v := h_v_eq_gLim.symm
              exact this.sub (Filter.EventuallyEq.rfl)
            have h_eq :=
              (eLpNorm_congr_ae (μ := volume)
                (p := (2 : ℝ≥0∞)) h_ae_sub)
            simpa using h_eq

          -- Rewrite in terms of concrete Fourier-integral expressions.
          have : Filter.Tendsto
              (fun n =>
                eLpNorm (fun ξ =>
                  Frourio.fourierIntegral g ξ
                    - Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ) 2 volume)
              Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
            simpa [u, v, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
              using h_freq_to_zero'
          exact this
        -- Identify the abstract `w` with `F[g]` and transport the convergence.
        have h_eq_fun :
            (fun n =>
              eLpNorm (fun ξ =>
                w ξ - Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ) 2 volume)
              =
            fun n =>
              eLpNorm (fun ξ =>
                Frourio.fourierIntegral g ξ
                  - Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ) 2 volume := by
          funext n
          have h_pointwise :
              (fun ξ =>
                w ξ - Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ)
                =
              fun ξ =>
                Frourio.fourierIntegral g ξ
                  - Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ := by
            funext ξ
            simp [w]
          simp [h_pointwise]
        simpa [h_eq_fun] using h_freq'

      -- Step 2: turn convergence to 0 into an eventual strict ε–bound.
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := by
        simpa [ENNReal.ofReal_pos] using hε
      have h_event :
          ∀ᶠ n in Filter.atTop,
            eLpNorm (fun ξ =>
                w ξ - Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ) 2 volume
              < ENNReal.ofReal ε :=
        Filter.Tendsto.eventually_lt h_freq_tendsto
          (tendsto_const_nhds) hpos

      -- Step 3: choose a concrete index and package the corresponding Schwartz
      -- function as the desired approximant ψ.
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_event
      refine ⟨φ N, ?_⟩
      simpa using hN N le_rfl
    -- Apply the general L²-membership lemma for inverse Fourier transforms on
    -- the closure of the Schwartz range.
    have hw_inv : MemLp
        (fun t => Real.fourierIntegralInv (fun ξ => w ξ) t) 2 volume :=
      inverseFourierIntegral_memLp_of_schwartz_approx
        (w := w) (hw := hw) (hw_approx := hw_approx)
    -- Unfold the definition of `w` to recover the desired statement.
    simpa [w] using hw_inv

  exact (ae_eq_of_L2_two_limits
    (ψ := fun n => fun t => φ n t)
    (u := g)
    (v := fun t => Real.fourierIntegralInv (fun ξ => Frourio.fourierIntegral g ξ) t)
    hφ_L2 hg_L2 hv hφ_tendsto_L2 h_inv_L2_limit).symm

end Frourio
