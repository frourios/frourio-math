import Frourio.Analysis.MellinBasic
import Frourio.Analysis.HilbertSpaceCore
import Frourio.Analysis.MellinTransform
import Frourio.Analysis.MellinPlancherelCore
import Frourio.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory Measure Real Complex
open scoped Topology ENNReal

namespace Frourio

section MellinPlancherelTheorems
/-!
## Core Mellin-Plancherel Theorems

This section contains the fundamental theorems of Mellin-Plancherel theory
that establish Uσ as an isometry between Hσ and L²(ℝ).
-/

/-- Logarithmic pullback from `Hσ` to unweighted `L²(ℝ)`.
    We transport along `x = exp t` and incorporate the weight factor
    so that `‖LogPull σ f‖_{L²(ℝ)} = ‖f‖_{Hσ}`. Explicitly,
    `(LogPull σ f)(t) = e^{σ t} · f(e^t)`. -/
noncomputable def LogPull (σ : ℝ) (f : Hσ σ) : ℝ → ℂ :=
  fun t => (Real.exp (σ * t) : ℂ) * Hσ.toFun f (Real.exp t)

@[simp] lemma LogPull_apply (σ : ℝ) (f : Hσ σ) (t : ℝ) :
    LogPull σ f t
      = (Real.exp (σ * t) : ℂ) * Hσ.toFun f (Real.exp t) := rfl

/-- Helper lemma: the weight function is measurable -/
lemma weight_measurable (σ : ℝ) :
    Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp ((2 * σ) * t))) := by
  apply Measurable.ennreal_ofReal
  exact Real.measurable_exp.comp (measurable_const.mul measurable_id)

/-- Helper lemma: LogPull preserves measurability -/
lemma LogPull_measurable (σ : ℝ) (f : Hσ σ) : Measurable (LogPull σ f) := by
  refine (Complex.measurable_ofReal.comp ?_).mul ?_
  · -- measurability of the exponential weight `t ↦ e^{σ t}`
    have h_linear : Measurable fun t : ℝ => (σ) * t :=
      (measurable_const.mul measurable_id)
    exact Real.measurable_exp.comp h_linear
  · -- measurability of `t ↦ f (exp t)`
    exact (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp

/-!
Helper lemma towards the Mellin–Plancherel isometry: if a function is
almost everywhere zero with respect to a `withDensity` measure whose
density is strictly positive a.e. on the base, then it is also almost
everywhere zero with respect to the base measure itself.

We keep the proof as a placeholder here, since it requires a careful
analysis of null sets for `withDensity`. The structure of the proof
will be reused when specializing to the concrete Mellin weights.
-/
lemma ae_zero_of_ae_zero_withDensity
    {μ : Measure ℝ} {w : ℝ → ℝ≥0∞} {f : ℝ → ℂ}
    (hpos : ∀ᵐ x ∂μ, 0 < w x)
    (hw : AEMeasurable w μ)
    (hf : f =ᵐ[μ.withDensity w] 0) :
    f =ᵐ[μ] 0 := by
  -- Step 1: express the a.e.-zero property in terms of the set
  -- `A := {x | f x ≠ 0}`. From `hf`, we know that `A` has measure zero
  -- with respect to `μ.withDensity w`.
  classical
  let A : Set ℝ := {x | f x ≠ 0}
  have hA_zero_withDensity :
      μ.withDensity w A = 0 := by
    -- From `hf : f =ᵐ[μ.withDensity w] 0`, we know that
    -- `f x = 0` holds for `μ.withDensity w`-almost every `x`. By the
    -- `ae_iff` characterization, this means the set where `f x ≠ 0`
    -- has `μ.withDensity w`-measure zero.
    have hAE : ∀ᵐ x ∂μ.withDensity w, f x = 0 := hf
    have hset : {x | ¬ f x = 0} = A := by
      ext x; simp [A]
    simpa [hset] using (ae_iff.1 hAE)

  -- Step 2: use positivity of the weight `w` almost everywhere to show
  -- that `μ A = 0` whenever `μ.withDensity w A = 0`. We do this by
  -- transferring the a.e. equality along `withDensity` and using
  -- positivity of `w` to discharge the implication.
  have hA_zero : μ A = 0 := by
    -- Start from the a.e. equality with respect to `μ.withDensity w`.
    have hf_ae_withDensity : ∀ᵐ x ∂μ.withDensity w, f x = 0 := hf
    -- Transfer this statement back to `μ` using `ae_withDensity_iff'`.
    have hf_imp :
        ∀ᵐ x ∂μ, w x ≠ 0 → f x = 0 :=
      (MeasureTheory.ae_withDensity_iff'
          (μ := μ) (f := w) (p := fun x => f x = 0) hw).1
        hf_ae_withDensity
    -- Positivity `0 < w x` a.e. implies `w x ≠ 0` a.e.
    have hw_ne_zero : ∀ᵐ x ∂μ, w x ≠ 0 := by
      refine hpos.mono ?_
      intro x hx
      exact ne_of_gt hx
    -- Combine the implication with `w x ≠ 0` a.e. to obtain `f x = 0` a.e. w.r.t. `μ`.
    have hf_ae_base : ∀ᵐ x ∂μ, f x = 0 := by
      refine (hf_imp.and hw_ne_zero).mono ?_
      intro x hx
      exact hx.1 hx.2
    -- Finally, translate this into the null-set statement for `A`.
    have hset' : {x | ¬ f x = 0} = A := by
      ext x; simp [A]
    have h_meas_zero : μ {x : ℝ | ¬ f x = 0} = 0 :=
      (ae_iff.1 hf_ae_base)
    simpa [hset'] using h_meas_zero

  -- Step 3: convert the null-set statement back into an a.e.-equality
  -- `f = 0` with respect to `μ`.
  have hf_ae : f =ᵐ[μ] 0 := by
    -- Use the `ae_iff` characterization with the null set `A`.
    -- The set where `f x ≠ 0` is exactly `A`, which has `μ`-measure zero
    -- by `hA_zero`.
    refine ae_iff.2 ?_
    have hset : {x | f x ≠ 0} = A := by
      ext x; simp [A]
    simpa [hset]
      using hA_zero
  exact hf_ae


/-!
  Auxiliary lemma: If a function `f` is almost everywhere zero on `(0,∞)`
  with respect to Lebesgue measure (restricted), then the composition
  `t ↦ f (exp t)` is almost everywhere zero on ℝ. This is the measure-theoretic
  content behind the change-of-variables map `x = exp t`.

  The full proof will use the Jacobian-one-dimensional API and the fact that
  `exp` is a C¹ diffeomorphism from ℝ onto `(0,∞)` with inverse `log`.
-/
lemma ae_zero_comp_exp_of_ae_zero_on_Ioi
    {f : ℝ → ℂ}
    (hf_meas : Measurable f)
    (hf_restrict : f =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] 0) :
    (fun t : ℝ => f (Real.exp t))
      =ᵐ[volume.restrict (Set.univ : Set ℝ)] 0 := by
  classical
  -- Work with the base measure on `(0,∞)`.
  set μ0 : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ0

  -- Step 1: the squared norm of f vanishes a.e. on `(0,∞)`.
  have hf_zero : ∀ᵐ x ∂μ0, f x = 0 := by
    simpa [hμ0] using hf_restrict

  have hf_norm_sq_zero :
      ∀ᵐ x ∂μ0, ‖f x‖^2 = 0 := by
    refine hf_zero.mono ?_
    intro x hx
    simp [hx]

  -- Step 2: the weighted squared norm is a.e. zero on `(0,∞)`.
  have h_integrand_ae_zero :
      ∀ᵐ x ∂μ0,
        ENNReal.ofReal (‖f x‖^2) * ENNReal.ofReal (x ^ (-1 : ℝ))
          = (0 : ℝ≥0∞) := by
    refine hf_norm_sq_zero.mono ?_
    intro x hx
    simp [hx]

  -- Hence the corresponding lintegral over `(0,∞)` vanishes.
  have h_lintegral_zero :
      ∫⁻ x, ENNReal.ofReal (‖f x‖^2) * ENNReal.ofReal (x ^ (-1 : ℝ))
          ∂μ0 = 0 := by
    have h_congr :
        (fun x =>
          ENNReal.ofReal (‖f x‖^2) * ENNReal.ofReal (x ^ (-1 : ℝ)))
          =ᵐ[μ0] (fun _ => (0 : ℝ≥0∞)) := h_integrand_ae_zero
    simpa using (lintegral_congr_ae (μ := μ0) h_congr)

  -- Step 3: express the same lintegral via the change of variables x = exp t.
  -- Define the ENNReal integrand on ℝ corresponding to t ↦ ‖f (exp t)‖².
  set G : ℝ → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (‖f (Real.exp t)‖^2) with hG

  have hG_meas : Measurable G := by
    -- measurability of t ↦ f (exp t)
    have h_meas_fexp : Measurable fun t : ℝ => f (Real.exp t) :=
      hf_meas.comp Real.measurable_exp
    have h_meas_norm : Measurable fun t : ℝ => ‖f (Real.exp t)‖ :=
      h_meas_fexp.norm
    have h_meas_sq : Measurable fun t : ℝ => ‖f (Real.exp t)‖^2 := by
      simpa [pow_two] using h_meas_norm.mul h_meas_norm
    simpa [hG] using (ENNReal.measurable_ofReal.comp h_meas_sq)

  -- Apply the change-of-variables lemma with α = -1 and integrand G.
  have h_change :=
    lintegral_change_of_variables_exp
      (α := (-1 : ℝ)) (f := G) hG_meas

  -- Rewrite the left-hand side of the change-of-variables identity
  -- to match the lintegral we already know is zero.
  have h_exp_log :
      ∀ᵐ x ∂μ0,
        G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ))
          = ENNReal.ofReal (‖f x‖^2) * ENNReal.ofReal (x ^ (-1 : ℝ)) := by
    -- On `(0,∞)`, we have `exp (log x) = x`.
    have h_mem : ∀ᵐ x ∂μ0, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [hμ0] using
        (ae_restrict_mem (μ := volume) (s := Set.Ioi (0 : ℝ)))
    refine h_mem.mono ?_
    intro x hx
    have hxpos : 0 < x := by simpa [Set.mem_Ioi] using hx
    have hGx :
        G (Real.log x)
          = ENNReal.ofReal (‖f x‖^2) := by
      simp [hG, Real.exp_log hxpos]
    simp [hGx]

  have h_LHS_eq :
      ∫⁻ x, G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ)) ∂μ0
        = ∫⁻ x, ENNReal.ofReal (‖f x‖^2) * ENNReal.ofReal (x ^ (-1 : ℝ)) ∂μ0 := by
    have h_congr :
        (fun x =>
          G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ)))
          =ᵐ[μ0]
        (fun x =>
          ENNReal.ofReal (‖f x‖^2) * ENNReal.ofReal (x ^ (-1 : ℝ))) :=
      h_exp_log
    exact lintegral_congr_ae (μ := μ0) h_congr

  -- Use the change-of-variables identity with α = -1.
  have h_change' :
      ∫⁻ x, G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ)) ∂μ0
        = ∫⁻ t, G t * ENNReal.ofReal (Real.exp ((-1 : ℝ) * t + t))
            ∂volume := by
    -- Start from the change-of-variables formula on `(0,∞)` and rewrite the
    -- set-lintegral as a lintegral over the restricted measure `μ0`.
    -- First, express the left-hand side of `h_change` as a lintegral over `μ0`.
    have h_mem : ∀ᵐ x ∂μ0, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [μ0, hμ0] using
        (ae_restrict_mem (μ := volume) (s := Set.Ioi (0 : ℝ)))
    have h_ind :
        (fun x =>
          Set.indicator (Set.Ioi (0 : ℝ))
            (fun x => G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ))) x)
          =ᵐ[μ0]
        (fun x => G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ))) := by
      refine h_mem.mono ?_
      intro x hx
      simp [Set.indicator_of_mem hx]
    -- Rewrite the set-lintegral as an indicator lintegral and compare a.e.
    have h_left :
        ∫⁻ x in Set.Ioi (0 : ℝ),
          G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ))
            ∂(volume.restrict (Set.Ioi (0 : ℝ)))
          = ∫⁻ x, G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ)) ∂μ0 := by
      -- By definition, `μ0 = volume.restrict (Ioi 0)`.
      have := lintegral_congr_ae (μ := μ0) h_ind
      -- Use the set-lintegral/indicator identity.
      simp [μ0, hμ0, lintegral_indicator, measurableSet_Ioi]
    -- Now combine with the original change-of-variables identity.
    have := h_change
    -- Replace the left-hand side using `h_left`.
    have h_final :
        ∫⁻ x, G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ)) ∂μ0
          = ∫⁻ t, G t * ENNReal.ofReal (Real.exp ((-1 : ℝ) * t + t)) ∂volume := by
      simpa [h_left, μ0, hμ0] using this
    exact h_final

  -- Combine the equalities to identify the lintegral of G on ℝ.
  have h_G_lintegral_zero :
      ∫⁻ t, G t * ENNReal.ofReal (Real.exp ((-1 : ℝ) * t + t))
          ∂volume = 0 := by
    -- Start from h_lintegral_zero and rewrite using h_LHS_eq
    calc ∫⁻ t, G t * ENNReal.ofReal (Real.exp ((-1 : ℝ) * t + t)) ∂volume
        = ∫⁻ x, G (Real.log x) * ENNReal.ofReal (x ^ (-1 : ℝ)) ∂μ0 := h_change'.symm
      _ = ∫⁻ x, ENNReal.ofReal (‖f x‖^2) * ENNReal.ofReal (x ^ (-1 : ℝ)) ∂μ0 := h_LHS_eq
      _ = 0 := h_lintegral_zero

  -- Simplify the exponential factor: for α = -1, we have `(-1) * t + t = 0`.
  have h_exp_simpl :
      (fun t : ℝ =>
        G t * ENNReal.ofReal (Real.exp ((-1 : ℝ) * t + t)))
        = fun t => G t := by
    funext t
    have : (-1 : ℝ) * t + t = 0 := by ring
    simp [this]

  have h_G_lintegral_zero' :
      ∫⁻ t, G t ∂volume = 0 := by
    simpa [h_exp_simpl] using h_G_lintegral_zero

  -- Step 4: apply `lintegral_eq_zero_iff'` to deduce `G = 0` a.e. on ℝ.
  have hG_aemeas :
      AEMeasurable G (volume : Measure ℝ) :=
    hG_meas.aemeasurable

  have hG_ae_zero :
      (fun t : ℝ => G t)
        =ᵐ[volume] (fun _ => (0 : ℝ≥0∞)) :=
    (lintegral_eq_zero_iff' hG_aemeas).1 h_G_lintegral_zero'

  -- Translate back from `G t = 0` to `f (exp t) = 0`.
  have hf_comp_ae_zero :
      (fun t : ℝ => f (Real.exp t))
        =ᵐ[volume] (fun _ => (0 : ℂ)) := by
    refine hG_ae_zero.mono ?_
    intro t ht
    -- From `ofReal (‖f (exp t)‖^2) = 0`, deduce `f (exp t) = 0`.
    have h_sq_le_zero :
        ‖f (Real.exp t)‖^2 ≤ 0 :=
      (ENNReal.ofReal_eq_zero.1 (by simpa [G, hG] using ht))
    have h_sq_ge_zero : 0 ≤ ‖f (Real.exp t)‖^2 :=
      sq_nonneg _
    have h_sq_zero : ‖f (Real.exp t)‖^2 = 0 :=
      le_antisymm h_sq_le_zero h_sq_ge_zero
    have h_norm_zero : ‖f (Real.exp t)‖ = 0 := by
      -- From `a^2 = 0` we deduce `a = 0` in ℝ.
      have := h_sq_zero
      -- Rewrite `‖·‖^2` as `(‖·‖)^2`.
      simpa [pow_two] using this
    -- Use `norm_eq_zero` to conclude.
    exact norm_eq_zero.1 h_norm_zero

  -- Finally, identify `volume.restrict univ` with `volume`.
  simpa using hf_comp_ae_zero

/-- If a function is almost everywhere zero with respect to the weighted
measure defining `Hσ`, then its composition with `exp` is almost everywhere
zero on ℝ with respect to Lebesgue measure. This is the a.e. counterpart of
the Mellin change-of-variables `x = exp t`. -/
lemma ae_zero_comp_exp_of_ae_zero
    (σ : ℝ) {f : ℝ → ℂ}
    (hf_meas : Measurable f)
    (hf : f =ᵐ[weightedMeasure σ] 0) :
    (fun t => f (Real.exp t)) =ᵐ[volume] 0 := by
  -- Step 1: reinterpret the a.e.-zero hypothesis on the base restricted measure.
  -- Using `Hσ_measure_eq_weightedMeasure`, the weighted measure coincides with
  -- the `withDensity` construction on `volume.restrict (Ioi 0)`.
  have hf_base :
      f
        =ᵐ[(volume.restrict (Set.Ioi 0)).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))] 0 := by
    -- This is just a change of measure along an equality of measures.
    simpa [Hσ_measure_eq_weightedMeasure (σ := σ)] using hf

  -- Step 2: upgrade to an a.e.-zero statement for Lebesgue measure restricted
  -- to `(0,∞)`. This uses the fact that the density is positive a.e. on `Ioi 0`,
  -- so `withDensity` is equivalent to the base restricted measure there.
  have hf_restrict :
      f =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] 0 := by
    -- We apply the abstract transfer lemma with `μ := volume.restrict (Ioi 0)`
    -- and weight `w x = ofReal (x^(2σ-1))`, using positivity of the weight
    -- almost everywhere on `(0,∞)`.
    have hpos :
        ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
          0 < ENNReal.ofReal (x ^ (2 * σ - 1)) := by
      -- On `Ioi 0`, we know `0 < x`. We will use this to show that
      -- `x ^ (2 * σ - 1)` is strictly positive as a real number, and then
      -- lift this to `ℝ≥0∞` via `ENNReal.ofReal`.
      refine
        (ae_restrict_iff'
          (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      -- Here `hx : x ∈ Ioi 0`, so `0 < x`.
      have hxpos : 0 < x := by
        simpa [Set.mem_Ioi] using hx
      -- Positivity of the real power on `(0,∞)`
      have hxpow : 0 < x ^ (2 * σ - 1) :=
        Real.rpow_pos_of_pos hxpos (2 * σ - 1)
      -- Lift positivity to `ℝ≥0∞` via `ofReal`
      have h_ofReal : 0 < ENNReal.ofReal (x ^ (2 * σ - 1)) :=
        ENNReal.ofReal_pos.mpr hxpow
      simpa using h_ofReal
    -- Measurability (hence a.e.-measurability) of the weight function.
    have hw_meas : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) := by
      measurability
    have hw_aemeas :
        AEMeasurable (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hw_meas.aemeasurable
    exact ae_zero_of_ae_zero_withDensity
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (w := fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))
      (f := f) hpos hw_aemeas hf_base

  -- Step 3: transport the a.e.-zero set along the exponential map `exp : ℝ → (0,∞)`.
  -- The key analytic fact is that `exp` is a C¹ diffeomorphism with inverse `log`,
  -- so the preimage of a null set in `(0,∞)` is null in ℝ. This will be shown
  -- via the change-of-variables theorem already developed for Mellin–Plancherel.
  have hf_comp_restrict :
      (fun t : ℝ => f (Real.exp t))
        =ᵐ[volume.restrict (Set.univ : Set ℝ)] 0 := by
    -- Apply the auxiliary lemma that transfers the a.e.-zero property on
    -- `(0,∞)` through the exponential change of variables.
    exact ae_zero_comp_exp_of_ae_zero_on_Ioi
      (f := f) hf_meas hf_restrict

  -- Step 4: simplify the restriction to `univ` back to the full Lebesgue measure.
  simpa using hf_comp_restrict

lemma LogPull_norm_sq (σ : ℝ) (f : Hσ σ) (t : ℝ) :
    ‖LogPull σ f t‖^2
      = Real.exp ((2 * σ) * t) * ‖Hσ.toFun f (Real.exp t)‖^2 := by
  classical
  set a := Real.exp (σ * t) with ha
  have ha_nonneg : 0 ≤ a := by simpa [ha] using (Real.exp_pos _).le
  have hnorm_mul :
      ‖LogPull σ f t‖ = ‖(a : ℂ)‖ * ‖Hσ.toFun f (Real.exp t)‖ := by
    rw [LogPull_apply]
    rw [ha]
    exact Complex.norm_mul ((a : ℂ)) (Hσ.toFun f (Real.exp t))
  have hnorm : ‖LogPull σ f t‖ = a * ‖Hσ.toFun f (Real.exp t)‖ := by
    have hnorm_a : ‖(a : ℂ)‖ = a := by
      simp [abs_of_nonneg ha_nonneg]
    rw [hnorm_mul, hnorm_a]
  have hsq := congrArg (fun r : ℝ => r ^ 2) hnorm
  have hmul :
      (a * ‖Hσ.toFun f (Real.exp t)‖) ^ 2
        = a ^ 2 * ‖Hσ.toFun f (Real.exp t)‖ ^ 2 := by
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hpow : a ^ 2 = Real.exp ((2 * σ) * t) := by
    have hsum : (σ * t) + (σ * t) = (2 * σ) * t := by ring
    calc
      a ^ 2 = Real.exp (σ * t) * Real.exp (σ * t) := by
        simp [ha, pow_two]
      _ = Real.exp ((σ * t) + (σ * t)) := by
        simpa [mul_comm]
          using
            (Real.exp_add (σ * t) (σ * t)).symm
      _ = Real.exp ((2 * σ) * t) := by rw [hsum]
  have hsq' : ‖LogPull σ f t‖ ^ 2
      = a ^ 2 * ‖Hσ.toFun f (Real.exp t)‖ ^ 2 := by
    simpa [hmul] using hsq
  simpa [hpow] using hsq'

lemma LogPull_integrand_eq (σ : ℝ) (f : Hσ σ) (t : ℝ) :
    (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
      = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
          * ENNReal.ofReal (Real.exp ((2 * σ) * t)) := by
  have hnorm_sq := LogPull_norm_sq (σ := σ) (f := f) t
  have hpos_f : 0 ≤ ‖Hσ.toFun f (Real.exp t)‖^2 := by exact sq_nonneg _
  have hpos_exp : 0 ≤ Real.exp ((2 * σ) * t) := (Real.exp_pos _).le
  have hpow :
      (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
        = ENNReal.ofReal (‖LogPull σ f t‖^2) := by
    -- Convert nnnorm to ENNReal.ofReal
    have h1 : (‖LogPull σ f t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖LogPull σ f t‖ := by
      simp only [nnnorm]
      conv_lhs => arg 1; rw [← Real.toNNReal_of_nonneg (norm_nonneg _)]
      simp only [ENNReal.ofReal]
    rw [h1]
    rw [(ENNReal.ofReal_pow (norm_nonneg _) 2).symm]
  have hsplit := congrArg ENNReal.ofReal hnorm_sq
  calc
      (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
          = ENNReal.ofReal (‖LogPull σ f t‖^2) := hpow
      _ = ENNReal.ofReal
            (Real.exp ((2 * σ) * t) * ‖Hσ.toFun f (Real.exp t)‖^2) := hsplit
      _ = ENNReal.ofReal (Real.exp ((2 * σ) * t))
            * ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2) := by
          exact ENNReal.ofReal_mul hpos_exp
      _ = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
            * ENNReal.ofReal (Real.exp ((2 * σ) * t)) := by
          rw [mul_comm]

/-- Change of variables for the squared LogPull integrand (statement only).
This is the key x = exp t substitution linking the LHS over ℝ and RHS over (0,∞). -/
lemma LogPull_sq_integral_eq (σ : ℝ) (f : Hσ σ) :
    ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure ℝ)
      = ∫⁻ x in Set.Ioi (0 : ℝ),
          (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
            * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂(volume : Measure ℝ) := by
  classical
  -- Step 1: rewrite the LHS integrand using the explicit formula for LogPull
  have h_integrand :
      (fun t => (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ))
        = (fun t =>
            ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
              * ENNReal.ofReal (Real.exp ((2 * σ) * t))) := by
    funext t; simpa using LogPull_integrand_eq (σ := σ) (f := f) (t := t)

  -- Abbreviate F(t) := ofReal ‖f(exp t)‖^2 for change of variables
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2) with hF
  have hF_meas : Measurable F := by
    -- measurability of t ↦ f (exp t) and of the norm/real-squared wrapper
    have h_meas_f : Measurable fun x : ℝ => Hσ.toFun f x :=
      (Lp.stronglyMeasurable (f := f)).measurable
    have h_meas_comp : Measurable fun t : ℝ => Hσ.toFun f (Real.exp t) :=
      h_meas_f.comp Real.measurable_exp
    have h_meas_norm : Measurable fun t : ℝ => ‖Hσ.toFun f (Real.exp t)‖ :=
      h_meas_comp.norm
    have h_meas_sq : Measurable fun t : ℝ => ‖Hσ.toFun f (Real.exp t)‖^2 := by
      simpa [pow_two] using h_meas_norm.mul h_meas_norm
    simpa [hF] using (ENNReal.measurable_ofReal.comp h_meas_sq)

  -- Step 2: apply the exponential change-of-variables on ENNReal lintegrals
  -- Choose α so that exp(α t + t) = exp((2σ) t), i.e. α = 2σ - 1
  have h_change :=
    lintegral_change_of_variables_exp (α := (2 * σ - 1)) (f := F) hF_meas

  -- Prepare to use h_change: rewrite the LHS via h_integrand and the RHS via h_change
  -- On the t-side, replace the integrand using h_integrand and simplify α*t + t
  have h_exp_exponent :
      (fun t : ℝ => F t * ENNReal.ofReal (Real.exp (((2 * σ - 1)) * t + t)))
        = (fun t : ℝ => F t * ENNReal.ofReal (Real.exp ((2 * σ) * t))) := by
    funext t
    have : ((2 * σ - 1) * t + t) = (2 * σ) * t := by ring
    simp [this]

  -- Replace the LHS (over t) using h_integrand; then use the change-of-variables identity
  -- First, replace the LHS integrand pointwise using `h_integrand`.
  have hstep :
      ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure ℝ)
        = ∫⁻ t, F t * ENNReal.ofReal (Real.exp ((2 * σ) * t)) ∂volume := by
    refine lintegral_congr_ae ?_;
    refine Filter.Eventually.of_forall (fun t => ?_)
    simpa [hF] using LogPull_integrand_eq (σ := σ) (f := f) t
  calc
    ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure ℝ)
        = ∫⁻ t, F t * ENNReal.ofReal (Real.exp ((2 * σ) * t)) ∂volume := hstep
    _ = ∫⁻ t, F t * ENNReal.ofReal (Real.exp (((2 * σ - 1)) * t + t)) ∂volume := by
          simp [h_exp_exponent]
    _ = ∫⁻ x in Set.Ioi (0 : ℝ), F (Real.log x) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume := by
          simpa using h_change.symm
    _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun f (Real.exp (Real.log x))‖^2)
            * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume := by
          -- unfold F on the set side
          rfl
    _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖Hσ.toFun f x‖^2) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume := by
          -- on (0,∞), exp (log x) = x
          refine lintegral_congr_ae ?_;
          refine (ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))).2 ?_
          refine Filter.Eventually.of_forall (fun x hx => ?_)
          have hxpos : 0 < x := hx
          simp [Real.exp_log hxpos]
    _ = ∫⁻ x in Set.Ioi (0 : ℝ),
          ((‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume := by
          -- rewrite ofReal (‖·‖^2) as (‖·‖₊)^2
          refine lintegral_congr_ae ?_;
          refine Filter.Eventually.of_forall (fun x => ?_)
          have hsq : (ENNReal.ofReal ‖Hσ.toFun f x‖) ^ (2 : ℕ)
              = ENNReal.ofReal (‖Hσ.toFun f x‖^2) := by
            rw [pow_two, pow_two]
            rw [ENNReal.ofReal_mul (norm_nonneg _)]
          -- Convert (ofReal ‖·‖)^2 into (‖·‖₊)^2 via coercions
          calc
            ENNReal.ofReal (‖Hσ.toFun f x‖^2) * ENNReal.ofReal (x ^ (2 * σ - 1))
                = (ENNReal.ofReal ‖Hσ.toFun f x‖) ^ (2 : ℕ) * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
                  rw [← hsq]
            _ = ((‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
              -- coe of NNReal and power commute; nnnorm is the NNReal norm
              congr 1
              simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
              rw [← ENNReal.coe_pow]
              norm_cast

/-- The LogPull of `f ∈ Hσ` belongs to `L²(ℝ)`.
This provides the L² membership used by Mellin–Plancherel; the finiteness
follows from the change-of-variables lemma `LogPull_sq_integral_eq` and the
definition of `Hσ`. -/
lemma mellin_in_L2 (σ : ℝ) (f : Hσ σ) :
    MemLp (LogPull σ f) 2 (volume : Measure ℝ) := by
  refine ⟨(LogPull_measurable σ f).aestronglyMeasurable, ?_⟩
  -- Finite L² norm: reduce to the weighted integral on (0,∞)
  -- via `LogPull_sq_integral_eq`, then appeal to the Hσ finiteness.
  -- We structure the proof without completing the final bound here.
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  -- Express the eLpNorm in terms of the lintegral of squared ENNReal norm
  -- and show that lintegral is finite.
  -- It suffices to show I < ∞ where I is the squared-‖LogPull‖ integrand lintegral.
  set I : ℝ≥0∞ := ∫⁻ t, ((‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(volume : Measure ℝ) with hI
  set J : ℝ≥0∞ := ∫⁻ x in Set.Ioi (0 : ℝ),
      (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
        * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂(volume : Measure ℝ) with hJ
  -- Change of variables: I = J
  have hI_eq_J : I = J := by
    have := LogPull_sq_integral_eq (σ := σ) (f := f)
    simpa [I, J, LogPull] using this
  -- Target: I < ∞. Reduce to J < ∞ via equality.
  have hJ_fin : J < ∞ := by
    -- From f ∈ Hσ, the weighted L² integral with weight x^(2σ-1) on (0,∞) is finite.
    -- Use MemLp → base finiteness, then expand withDensity to the set integral form.
    set wσ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x ^ (2 * σ - 1)) with hwσ
    have hf_mem : MemLp (Hσ.toFun f) 2 ((volume.restrict (Set.Ioi 0)).withDensity wσ) := by
      simpa [Hσ.toFun, hwσ] using (Frourio.memLp_of_Hσ (σ := σ) (f := f))
    have h_base_fin_ofReal :
        (∫⁻ x, (ENNReal.ofReal ‖Hσ.toFun f x‖) ^ (2 : ℕ)
            ∂((volume.restrict (Set.Ioi 0)).withDensity wσ)) < ∞ :=
      Frourio.lintegral_ofReal_norm_sq_lt_top_of_memLp (σ := σ) (f := f)
        (wσ := wσ) hf_mem
    have h_base_fin :
        (∫⁻ x, ((‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
            ∂((volume.restrict (Set.Ioi 0)).withDensity wσ)) < ∞ := by
      convert h_base_fin_ofReal using 2
      funext x
      simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
      rw [← ENNReal.coe_pow]
      norm_cast
    have h_weighted_fin :
        (∫⁻ x in Set.Ioi (0 : ℝ), (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ 2 * wσ x ∂volume) < ∞ :=
      Frourio.lintegral_withDensity_to_weighted (σ := σ) (f := f)
        (wσ := wσ) (hwσ := hwσ) h_base_fin
    simpa [J, hwσ] using h_weighted_fin
  -- Wrap up: I < ∞, hence the corresponding eLpNorm is finite.
  have hI_fin : I < ∞ := by simpa [hI_eq_J] using hJ_fin
  -- Convert the lintegral with e-norm to the nnnorm form (equals I)
  have h_enorm_to_nnnorm :
      (∫⁻ t, ‖(LogPull σ f) t‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ))
        = ∫⁻ t, ((‖(LogPull σ f) t‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(volume : Measure ℝ) := by
    simpa using (enorm_to_nnnorm_lintegral (fun t => LogPull σ f t))
  have h_lintegral_fin :
      (∫⁻ t, ‖(LogPull σ f) t‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) < ∞ := by
    simpa [h_enorm_to_nnnorm, I, hI] using hI_fin
  -- Finally, rewrite eLpNorm via the lintegral and conclude finiteness
  have : eLpNorm (LogPull σ f) 2 (volume : Measure ℝ) < ∞ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
    simp only [ENNReal.toReal_ofNat, one_div]
    -- eLpNorm = (∫⁻ x, ‖f x‖ₑ ^ p)^(1/p), so we need to show the root is finite
    have : (∫⁻ t, ‖(LogPull σ f) t‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) ^ (2 : ℝ)⁻¹ < ∞ := by
      apply ENNReal.rpow_lt_top_of_nonneg
      · simp
      · exact h_lintegral_fin.ne
    exact this
  exact this

/-- Mellin–Plancherel formula (isometry).
For the normalization used in this project, the logarithmic pullback
`LogPull σ` is an isometry from `Hσ` into `L²(ℝ)`, i.e.
`∫ ‖LogPull σ f‖² = ‖f‖²` for every `f ∈ Hσ`. -/
theorem mellin_plancherel_formula (σ : ℝ) (f : Hσ σ) :
    ∫ τ : ℝ, ‖LogPull σ f τ‖^2 ∂volume = ‖f‖^2 := by
  classical
  -- Abbreviate g := LogPull σ f
  set g : ℝ → ℂ := LogPull σ f with hg

  -- Step 1: g is in L²(ℝ).
  -- In the project, this follows from the change-of-variables lemma and the
  -- definition of Hσ; see Parseval development for a full proof.
  have hMem : MemLp g 2 (volume : Measure ℝ) := by
    -- Use the project-local L² lemma for LogPull
    simpa [g, hg] using mellin_in_L2 σ f

  -- Step 2: Convert the (Bochner) integral of ‖g‖² to the toReal of a lintegral.
  have hInt_sq : Integrable (fun τ : ℝ => ‖g τ‖ ^ 2) (volume : Measure ℝ) := by
    -- Standard: MemLp with p=2 implies integrable of the square of the norm
    have := (memLp_two_iff_integrable_sq_norm hMem.1).1 hMem
    simpa [g, hg, pow_two] using this

  have hNonneg : 0 ≤ᵐ[volume] fun τ : ℝ => ‖g τ‖ ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _

  have hOfReal :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt_sq hNonneg

  have hIntegral_eq :
      ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ)
        = (∫⁻ τ, ENNReal.ofReal (‖g τ‖ ^ 2) ∂(volume : Measure ℝ)).toReal := by
    have := congrArg ENNReal.toReal hOfReal
    -- integral is nonnegative, so toReal (ofReal _) matches
    have hge : 0 ≤ ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂(volume : Measure ℝ) :=
      integral_nonneg fun _ => sq_nonneg _
    simpa [hge, ENNReal.toReal_ofReal] using this

  -- Step 3: Define the two lintegrals that change variables will relate.
  set I : ℝ≥0∞ := ∫⁻ τ, (‖g τ‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure ℝ) with hI
  set J : ℝ≥0∞ := ∫⁻ x in Set.Ioi (0 : ℝ),
      (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ) * ENNReal.ofReal (x ^ (2 * σ - 1)) ∂volume with hJ

  -- Relate ofReal (‖g‖²) to (‖g‖₊)^2 inside the lintegral
  have hI_ofReal :
      (∫⁻ τ, ENNReal.ofReal (‖g τ‖ ^ 2) ∂(volume : Measure ℝ)) = I := by
    -- First rewrite ENNReal.ofReal (‖g τ‖^2) as (ENNReal.ofReal ‖g τ‖)^2
    have h_sq_ofReal :
        (fun τ => ENNReal.ofReal (‖g τ‖ ^ 2))
          = (fun τ => (ENNReal.ofReal ‖g τ‖) ^ (2 : ℕ)) := by
      funext τ
      have hnn : 0 ≤ ‖g τ‖ := norm_nonneg _
      simp [pow_two, ENNReal.ofReal_mul, hnn]
    -- Then convert (ENNReal.ofReal ‖·‖)^2 to (‖·‖₊)^2 using a canned lemma
    have h_toNN :
        (fun τ => (ENNReal.ofReal ‖g τ‖) ^ (2 : ℕ))
          = (fun τ => ((‖g τ‖₊ : ℝ≥0∞) ^ (2 : ℕ))) := by
      simpa using ofReal_norm_eq_coe_nnnorm g
    -- Conclude by identifying the integrand of I
    simpa [I, hI, h_sq_ofReal, h_toNN]

  -- Step 4: Change of variables t = log x on the ENNReal side (already proved above)
  have hI_eq_J : I = J := by
    -- direct from the prepared change-of-variables lemma
    have := LogPull_sq_integral_eq (σ := σ) (f := f)
    simpa [I, J, g, hg, LogPull] using this

  -- Step 5: Evaluate J.toReal via the Hσ norm formula
  have hJ_toReal : J.toReal = ‖f‖ ^ 2 := by
    have h' := Hσ_norm_squared (σ := σ) (f := f)
    simpa [J] using h'.symm

  -- Step 6: Put pieces together.
  calc
    ∫ τ : ℝ, ‖LogPull σ f τ‖^2 ∂volume
        = (∫⁻ τ, ENNReal.ofReal (‖g τ‖ ^ 2) ∂(volume : Measure ℝ)).toReal := by
              simpa [g, hg] using hIntegral_eq
    _ = I.toReal := by simp [hI_ofReal]
    _ = J.toReal := by simp [hI_eq_J]
    _ = ‖f‖ ^ 2 := hJ_toReal

/-- Auxiliary identity: the Jacobian weight appearing in `LogPull` cancels with
the inverse weight built into `toHσ_ofL2`. -/
lemma exp_weight_cancel (σ τ : ℝ) :
    (Real.exp ((σ - (1 / 2 : ℝ)) * τ) : ℂ)
        * (Real.exp τ : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ) = 1 := by
  classical
  set a : ℝ := σ - (1 / 2 : ℝ)
  set z : ℂ := (Real.exp τ : ℂ) with hz_def
  have hz_ne : z ≠ 0 := by
    have : (Real.exp τ : ℂ) ≠ 0 := by
      simp
    simp [hz_def]
  have hlog : Complex.log z = τ := by
    have hx_nonneg : 0 ≤ Real.exp τ := (Real.exp_pos τ).le
    have := (Complex.ofReal_log hx_nonneg).symm
    simpa [hz_def, Real.log_exp] using this
  have h_pos : z ^ (a : ℂ) = (Real.exp (a * τ) : ℂ) := by
    calc
      z ^ (a : ℂ)
          = Complex.exp ((a : ℂ) * Complex.log z) := by
              simp [Complex.cpow_def, hz_ne, mul_comm]
      _ = Complex.exp ((a : ℂ) * τ) := by
        rw [hlog]
      _ = (Real.exp (a * τ) : ℂ) := by
        have : ((a : ℂ) * τ) = (a * τ : ℝ) := by
          simp
        rw [this]
        simp
  have h_neg : z ^ (-(a : ℂ)) = (Real.exp ((-a) * τ) : ℂ) := by
    calc
      z ^ (-(a : ℂ))
          = Complex.exp (-(a : ℂ) * Complex.log z) := by
              simp [Complex.cpow_def, hz_ne, mul_comm]
      _ = Complex.exp (-(a : ℂ) * τ) := by
        rw [hlog]
      _ = (Real.exp ((-a) * τ) : ℂ) := by
        have : (-(a : ℂ)) * τ = (-a * τ : ℝ) := by
          simp
        rw [this]
        simp
  have h_prod : z ^ (a : ℂ) * z ^ (-(a : ℂ)) = 1 := by
    have h_cpow_add := Complex.cpow_add (a : ℂ) (-(a : ℂ)) hz_ne
    have h_sum : (a : ℂ) + (-(a : ℂ)) = 0 := by simp
    have : z ^ (a : ℂ) * z ^ (-(a : ℂ)) = z ^ ((a : ℂ) + (-(a : ℂ))) := h_cpow_add.symm
    rw [this, h_sum]
    simp [Complex.cpow_zero]
  calc
    (Real.exp ((σ - (1 / 2 : ℝ)) * τ) : ℂ)
        * (Real.exp τ : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ)
        = (Real.exp (a * τ) : ℂ) * (Real.exp τ : ℂ) ^ (-(a : ℂ)) := by
          congr 2
          simp only [a]
          norm_cast
    _ = (Real.exp (a * τ) : ℂ) * z ^ (-(a : ℂ)) := by
          rw [hz_def]
    _ = z ^ (a : ℂ) * z ^ (-(a : ℂ)) := by
          rw [←h_pos]
    _ = 1 := h_prod

end MellinPlancherelTheorems

end Frourio
