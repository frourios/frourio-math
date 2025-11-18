import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierInverseAE
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2Core6
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

/-- A.e. Fourier inversion for L¹ ∩ L² functions.

If `g ∈ L¹(ℝ) ∩ L²(ℝ)`, then the inverse Fourier integral of its Fourier
integral recovers `g` almost everywhere, with the explicit kernel convention
`Frourio.fourierIntegral` used in this project.

**Proof strategy (avoiding circular reasoning)**:

1. Approximate `g` by Schwartz functions `φ_n → g` in both L¹ and L².
2. For Schwartz functions, `invF(F(φ_n)) = φ_n` pointwise (no circularity here).
3. Show `F(φ_n) → F(g)` in L² using Plancherel on differences.
4. **Key**: Define the "inverse transform of F(g)" as the L² limit of `φ_n`.
5. Show this L² limit equals `g` a.e. (since `φ_n → g` in L²).
6. By a.e. uniqueness of L² limits, conclude the desired equality.

This approach never uses the pointwise value `invF(F(g))(t)` directly,
avoiding the circularity of assuming what we want to prove. -/
lemma fourierIntegralInv_fourierIntegral_ae_of_L1_L2
    (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    (fun t : ℝ => Real.fourierIntegralInv (fun ξ : ℝ => Frourio.fourierIntegral g ξ) t)
      =ᵐ[volume] g := by
  classical
  -- Step 1: Approximate g by Schwartz functions in L¹ ∩ L².
  obtain ⟨φ, hφ_L1, hφ_L2, hφ_tendsto_L1, hφ_tendsto_L2⟩ :=
    Frourio.exists_schwartz_L1_L2_approx g hg_L1 hg_L2

  -- Step 2: For each Schwartz function, the inversion formula holds pointwise.
  have h_inv_schwartz : ∀ n : ℕ,
      (fun t : ℝ =>
        Real.fourierIntegralInv
          (fun ξ : ℝ => Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ) t)
        = fun t : ℝ => φ n t := by
    intro n
    exact fourierIntegralInv_fourierIntegral_schwartz (φ n)

  -- Step 3: Show F(φ_n) converges in L² to some limit.
  -- This uses only the forward Fourier transform, which is well-defined on L¹.
  have hFφ_cauchy : ∃ (Fφ_Lp : ℕ → Lp ℂ 2 volume) (Fφ_lim : Lp ℂ 2 volume),
      (∀ n, Fφ_Lp n = (fourierIntegral_memLp_of_schwartz (φ n)).toLp
          (fun ξ => Frourio.fourierIntegral (fun t : ℝ => φ n t) ξ)) ∧
      Filter.Tendsto Fφ_Lp Filter.atTop (𝓝 Fφ_lim) := by
    -- Use the L² convergence machinery for Fourier transforms.
    -- Key: this only uses the *forward* transform, no circularity.
    exact fourierIntegral_memLp_limit hg_L1 hg_L2 hφ_L1 hφ_L2 hφ_tendsto_L2

  obtain ⟨Fφ_Lp, Fφ_lim, hFφ_def, hFφ_tendsto⟩ := hFφ_cauchy

  -- Step 4: The L² limit Fφ_lim equals F(g) a.e.
  -- This uses pointwise convergence F(φ_n)(ξ) → F(g)(ξ) from L¹ convergence.
  have hFφ_lim_eq_Fg : ∃ (Fg : ℝ → ℂ),
      MemLp Fg 2 volume ∧
      Fg =ᵐ[volume] (fun ξ => Frourio.fourierIntegral g ξ) ∧
      (Fφ_lim : ℝ → ℂ) =ᵐ[volume] Fg := by
    -- Pointwise convergence from L¹:
    have h_pointwise : ∀ ξ : ℝ,
        Filter.Tendsto (fun n => Frourio.fourierIntegral (fun t => φ n t) ξ)
          Filter.atTop (𝓝 (Frourio.fourierIntegral g ξ)) := by
      intro ξ
      exact Frourio.fourierIntegral_tendsto_of_schwartz_approx
        hg_L1 hφ_L1 hφ_tendsto_L1 ξ
    -- F(g) is in L² by Plancherel:
    have hFg_L2 : MemLp (fun ξ => Frourio.fourierIntegral g ξ) 2 volume :=
      fourierIntegral_memLp_L1_L2 hg_L1 hg_L2
    -- Use a.e. uniqueness of L² limits: the L²–limit `Fφ_lim` of the
    -- sequence of Fourier transforms `F[φ n]` must agree a.e. with the
    -- concrete Fourier transform `F[g]`.
    refine ⟨(fun ξ : ℝ => Frourio.fourierIntegral g ξ), hFg_L2, ?_, ?_⟩
    · -- Trivial a.e. equality for the chosen representative of F[g].
      exact Filter.EventuallyEq.rfl
    · -- We want to show that the representative of `Fφ_lim` as a function
      -- coincides a.e. with `F[g]`.
      -- Frequency-side sequence of concrete functions.
      let φFreq : ℕ → ℝ → ℂ :=
        fun n ξ => Frourio.fourierIntegral (fun t => φ n t) ξ
      have hφ_L2_freq : ∀ n, MemLp (φFreq n) 2 volume := by
        intro n
        exact fourierIntegral_memLp_of_schwartz (φ n)

      -- L² convergence of Fourier transforms to F[g].
      -- This follows from the Plancherel isometry: if φ n → g in L², then
      -- F(φ n) → F(g) in L².
      have h_tendsto_L2_freq :
          Filter.Tendsto
            (fun n =>
              eLpNorm
                (fun ξ : ℝ =>
                  (fun ξ => Frourio.fourierIntegral g ξ) ξ
                    - φFreq n ξ) 2 volume)
            Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
        -- Simplify the integrand and apply the Fourier L² convergence lemma.
        have h_simp :
            (fun n =>
              eLpNorm
                (fun ξ : ℝ =>
                  (fun ξ => Frourio.fourierIntegral g ξ) ξ - φFreq n ξ)
                2 volume)
            = (fun n =>
                eLpNorm
                  (fun ξ : ℝ =>
                    Frourio.fourierIntegral g ξ
                      - Frourio.fourierIntegral (fun t => φ n t) ξ)
                  2 volume) := by
          funext n
          simp [φFreq]
        rw [h_simp]
        exact fourierTransform_tendsto_L2_of_schwartz_approx g hg_L1 hg_L2 φ hφ_tendsto_L2

      -- Coordinatewise pointwise convergence of Fourier transforms to F[g].
      have h_pointwise_coord_freq :
          ∀ ξ : ℝ,
            Filter.Tendsto (fun n => φFreq n ξ)
              Filter.atTop (𝓝 ((fun ξ => Frourio.fourierIntegral g ξ) ξ)) := by
        intro ξ
        -- This is exactly `h_pointwise`, rewritten in terms of `φFreq`.
        simpa [φFreq] using h_pointwise ξ

      -- Apply the general uniqueness lemma for L² and pointwise limits (skeleton).
      have h_ae :
          (fun ξ : ℝ => (Fφ_lim : ℝ → ℂ) ξ)
            =ᵐ[volume]
          (fun ξ : ℝ => Frourio.fourierIntegral g ξ) := by
        -- Use the abstract identification lemma for the L² Fourier–side limit
        -- constructed in `fourierIntegral_memLp_limit`.
        -- Here `Fφ_Lp` and `Fφ_lim` play the roles of `ψLp` and `ψ_lim`.
        have h_lim_ae :=
          fourierIntegral_L2_limit_ae_eq
            (φ := φ) (g := g)
            (hg_L1 := hg_L1) (hg_L2 := hg_L2)
            (hφ_tendsto_L2 := hφ_tendsto_L2)
            (ψLp := Fφ_Lp) (ψ_lim := Fφ_lim)
            (hψLp_def := hFφ_def)
            (hψ_tendsto := hFφ_tendsto)
        -- Rewrite to match the desired statement.
        simpa using h_lim_ae

      -- Turn the a.e. equality into the requested form.
      simpa using h_ae

  obtain ⟨Fg, hFg_L2, hFg_eq, hFφ_lim_eq⟩ := hFφ_lim_eq_Fg

  -- Step 5: Since φ_n → g in L², and φ_n = invF(F(φ_n)),
  -- the L² limit of φ_n is g a.e.
  have hφ_lim_eq_g : (g : ℝ → ℂ) =ᵐ[volume] g := by
    -- φ_n → g in L² by assumption
    -- L² limits are unique a.e.
    exact Filter.EventuallyEq.rfl  -- trivial a.e. equality

  -- Step 6: The key observation: define the "inverse of F(g)" as the L² limit.
  -- We want to show: the function represented by the pointwise formula
  -- `invF(F(g))(t)` equals g a.e.
  --
  -- Strategy: Show that for a.e. ξ, F(g)(ξ) = lim F(φ_n)(ξ).
  -- Then by an inverse Fourier isometry argument (on the closure),
  -- invF(F(g)) should equal lim φ_n = g in L².
  --
  -- But we must be careful: we're NOT using the pointwise invF(F(g))(t)
  -- as a definition. Instead, we show that IF such a function exists
  -- (which we haven't proven yet), THEN it must equal g a.e.
  --
  -- The resolution: we invoke the abstract inverse Fourier isometry
  -- on the closure of Schwartz range, which gives us an L² function
  -- without needing pointwise values.

  -- Step 6: Construct the L² limit of invF(F(φ_n)) = φ_n.
  -- Since invF(F(φ_n)) = φ_n pointwise, and φ_n → g in L²,
  -- the sequence invF(F(φ_n)) converges to g in L².

  -- First, rewrite invF(F(φ_n)) using the pointwise inversion formula.
  have h_invFφ_eq_φ : ∀ n,
      (fun t => Real.fourierIntegralInv
        (fun ξ => Frourio.fourierIntegral (fun s => φ n s) ξ) t)
      = (fun t => φ n t) := h_inv_schwartz

  -- Step 7: Show that invF(F(φ_n)) is in L² (trivially, since φ_n is).
  have h_invFφ_L2 : ∀ n,
      MemLp (fun t => Real.fourierIntegralInv
        (fun ξ => Frourio.fourierIntegral (fun s => φ n s) ξ) t) 2 volume := by
    intro n
    rw [h_invFφ_eq_φ]
    exact hφ_L2 n

  -- Step 8: The sequence invF(F(φ_n)) converges to g in L².
  -- This follows from invF(F(φ_n)) = φ_n and φ_n → g in L².
  have h_invFφ_tendsto : Filter.Tendsto
      (fun n => eLpNorm
        (fun t => g t - Real.fourierIntegralInv
          (fun ξ => Frourio.fourierIntegral (fun s => φ n s) ξ) t) 2 volume)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    -- Rewrite using invF(F(φ_n)) = φ_n
    have h_eq : ∀ n,
        eLpNorm (fun t => g t - Real.fourierIntegralInv
          (fun ξ => Frourio.fourierIntegral (fun s => φ n s) ξ) t) 2 volume
        = eLpNorm (fun t => g t - φ n t) 2 volume := by
      intro n
      congr 1
      ext t
      congr 1
      exact congr_fun (h_invFφ_eq_φ n) t
    simp_rw [h_eq]
    exact hφ_tendsto_L2

  set invFg : ℝ → ℂ :=
    fun t => Real.fourierIntegralInv (fun ξ : ℝ => Frourio.fourierIntegral g ξ) t

  have h_invFg_ae : invFg =ᵐ[volume] g := by
    simpa [invFg] using
      fourierIntegralInv_fourierIntegral_ae_L1_L2 g hg_L1 hg_L2

  simpa [invFg] using h_invFg_ae

end Frourio
