import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore1
import Frourio.Analysis.HilbertSpaceCore
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

open MeasureTheory Measure Real Complex Set
open scoped ENNReal Topology FourierTransform

namespace Frourio
open Schwartz

/-- Change of variables formula for lintegral under linear scaling.
For a nonzero scalar `a : ℝ` and a function `f : ℝ → ℝ≥0∞`,
the Lebesgue integral transforms as:
`∫⁻ x, f (a * x) ∂μ = |a⁻¹| * ∫⁻ x, f x ∂μ`

This is the extended non-negative (lintegral) version of the change of variables formula
for linear scaling in one dimension. -/
lemma Measure.lintegral_comp_mul_left (a : ℝ) (ha : a ≠ 0)
    (f : ℝ → ℝ≥0∞)
    (hf_vol : AEMeasurable f (volume : Measure ℝ)) :
    (∫⁻ x, f (a * x) ∂(volume : Measure ℝ))
      = ENNReal.ofReal (|a⁻¹|) * (∫⁻ x, f x ∂(volume : Measure ℝ)) := by
  classical
  -- Define the scaling map g(x) = a * x and basic measurability
  set g : ℝ → ℝ := fun x => a * x with hg
  have hg_meas : Measurable g := by simpa [hg, mul_comm, mul_left_comm, mul_assoc] using
    (measurable_const.mul measurable_id)
  have hg_aemeas : AEMeasurable g (volume : Measure ℝ) := hg_meas.aemeasurable

  -- Pushforward of Lebesgue measure under linear scaling by a
  -- is a scalar multiple by |a|^{-1}. We'll use it twice below.
  have h_map_scale :
      Measure.map g (volume : Measure ℝ)
        = (ENNReal.ofReal ((|a|)⁻¹)) • (volume : Measure ℝ) := by
    -- We reduce to the `Fin 1 → ℝ` case where a general linear-map formula is available,
    -- via the linear isometry equivalence `E : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ` given by evaluation at 0.
    -- Then we conjugate the map `g` by `E` and apply
    -- `Real.map_linearMap_volume_pi_eq_smul_volume_pi`.
    classical
    -- Linear isometry equivalence between `(Fin 1 → ℝ)` and `ℝ`.
    haveI := (inferInstance : FiniteDimensional ℝ (Fin 1 → ℝ))
    let E : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ :=
      { toLinearEquiv :=
          { toFun := fun x => x 0
            invFun := fun t _ => t
            map_add' := by intro x y; rfl
            map_smul' := by intro c x; rfl
            left_inv := by
              intro x; funext i
              have : i = (0 : Fin 1) := Subsingleton.elim _ _
              simp [this]
            right_inv := by intro t; rfl }
        norm_map' := by
          intro x
          have hx_const : x = fun _ : Fin 1 => x 0 := by
            funext i
            have : i = (0 : Fin 1) := Subsingleton.elim _ _
            simp [this]
          have hx_norm' : ‖fun _ : Fin 1 => x 0‖ = ‖x‖ := by
            simpa using congrArg norm hx_const.symm
          have hx_norm'' : ‖fun _ : Fin 1 => x 0‖ = ‖x 0‖ := by
            simp
          have hx_norm : ‖x‖ = ‖x 0‖ := by
            simpa [hx_norm''] using hx_norm'.symm
          simp [hx_norm.symm] }
    -- Scaling map on `(Fin 1 → ℝ)`.
    set gF : (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun x => (a : ℝ) • x with hgF
    have hgF_meas : Measurable gF := by
      simpa [hgF] using (continuous_const_smul (a : ℝ)).measurable
    -- Conjugacy identity: `g = E ∘ gF ∘ E.symm`.
    have h_conj : (fun t : ℝ => E (gF (E.symm t))) = g := by
      funext t; simp [hgF, g, mul_comm, mul_left_comm, mul_assoc]
    -- Measure-preserving properties of `E` and `E.symm`.
    have h_pres_E : MeasurePreserving (fun x : (Fin 1 → ℝ) => E x) := by
      simpa [E] using (volume_preserving_piUnique (fun _ : Fin 1 => ℝ))
    have h_pres_Esymm : MeasurePreserving (fun t : ℝ => E.symm t) := by
      have h := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm
      simpa [E] using h
    have h_map_E : Measure.map (fun x : (Fin 1 → ℝ) => E x) (volume : Measure (Fin 1 → ℝ))
        = (volume : Measure ℝ) := h_pres_E.map_eq
    have h_map_Esymm : Measure.map (fun t : ℝ => E.symm t) (volume : Measure ℝ)
        = (volume : Measure (Fin 1 → ℝ)) := h_pres_Esymm.map_eq
    -- Pushforward under `gF` on `(Fin 1 → ℝ)` via the linear change-of-variables formula.
    have h_map_gF :
        Measure.map gF (volume : Measure (Fin 1 → ℝ))
          = ENNReal.ofReal (abs ((LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
              • (volume : Measure (Fin 1 → ℝ)) := by
      -- Determinant is nonzero since `a ≠ 0`.
      have hdet_ne :
          LinearMap.det
              ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) ≠ 0 := by
        have hdet :
            LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
              = (a : ℝ) ^ (Module.finrank ℝ (Fin 1 → ℝ)) := by
          simp
        have hpow_ne : (a : ℝ) ^ (Module.finrank ℝ (Fin 1 → ℝ)) ≠ 0 :=
          pow_ne_zero (Module.finrank ℝ (Fin 1 → ℝ)) ha
        simpa [hdet] using hpow_ne
      -- Apply the general linear-map formula on `(Fin 1 → ℝ)`.
      have hgF_lin :
          (fun x : (Fin 1 → ℝ) =>
            (((a : ℝ) •
              (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) :
                (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) x)
            = gF := by
        funext x; simp [hgF]
      simpa [hgF_lin]
        using
          Real.map_linearMap_volume_pi_eq_smul_volume_pi
            (f := ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))) hdet_ne
    -- Now compute `map g volume` by conjugating through `E` and using `h_map_gF`.
    -- Start by rewriting via `map_map` and the conjugacy identity.
    have h_map_conj :
        Measure.map g (volume : Measure ℝ)
          = Measure.map (fun x : (Fin 1 → ℝ) => E (gF x))
              (Measure.map (fun t : ℝ => E.symm t) (volume : Measure ℝ)) := by
      have h_meas_left : Measurable (fun x : (Fin 1 → ℝ) => E (gF x)) :=
        (E.toLinearIsometry.continuous.comp (continuous_const_smul (a : ℝ))).measurable
      have h_meas_right : Measurable (fun t : ℝ => E.symm t) :=
        E.symm.toLinearIsometry.continuous.measurable
      -- map g volume = map (E ∘ gF ∘ E.symm) volume = map E (map gF (map E.symm volume))
      rw [← h_conj]
      rw [Measure.map_map h_meas_left h_meas_right]
      rfl
    -- Substitute `map E.symm volume = volume`.
    have h_map_conj' :
        Measure.map g (volume : Measure ℝ)
          = Measure.map (fun x : (Fin 1 → ℝ) => E (gF x))
              (volume : Measure (Fin 1 → ℝ)) := by
      simpa [h_map_Esymm] using h_map_conj
    -- Evaluate the right-hand side using `h_map_gF` and `map_map` again.
    have h_rhs :
        Measure.map (fun x : (Fin 1 → ℝ) => E (gF x)) (volume : Measure (Fin 1 → ℝ))
          = ENNReal.ofReal (abs ((LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
              • (volume : Measure ℝ) := by
      have h_meas_E : Measurable (fun x : (Fin 1 → ℝ) => E x) :=
        E.toLinearIsometry.continuous.measurable
      -- map E (map gF volume) = map (E ∘ gF) volume
      have h_map_comp := @Measure.map_map (Fin 1 → ℝ) (Fin 1 → ℝ) ℝ _ _ _
        (volume : Measure (Fin 1 → ℝ)) (fun x : (Fin 1 → ℝ) => E x) gF h_meas_E hgF_meas
      -- Now substitute `h_map_gF` and use that `map E` preserves volume.
      -- We prove equality by extensionality on measurable sets.
      -- Turn the previous identity into a pointwise equality on measurable sets.
      -- Using the identity `map E volume = volume`.
      -- Evaluate both sides on a measurable set `s`.
      refine Measure.ext (fun s hs => ?_)
      -- Left-hand side: map E (map gF volume) applied to `s`.
      -- From `map_map`, it equals `map (E ∘ gF) volume` applied to `s`.
      have hL :
          (Measure.map (fun x : (Fin 1 → ℝ) => E (gF x))
              (volume : Measure (Fin 1 → ℝ))) s
            = (Measure.map (fun x : (Fin 1 → ℝ) => E x)
                (Measure.map gF (volume : Measure (Fin 1 → ℝ)))) s := by
        -- Unfold with `map_map` on measurable sets
        simpa using congrArg (fun μ => μ s) h_map_comp.symm
      -- Rewrite using `h_map_gF` and the definition of `Measure.map` on sets.
      have hL' :
          (Measure.map (fun x : (Fin 1 → ℝ) => E x)
              (Measure.map gF (volume : Measure (Fin 1 → ℝ)))) s
            = ENNReal.ofReal (abs ((LinearMap.det
                  ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
                * (volume : Measure (Fin 1 → ℝ)) (E ⁻¹' s) := by
        -- Evaluate `map` and then `smul` on the measurable set `E ⁻¹' s`.
        -- `Measure.smul_apply` + `Measure.map_apply`.
        have hs_pre : MeasurableSet ((fun x : (Fin 1 → ℝ) => E x) ⁻¹' s) :=
          hs.preimage h_meas_E
        -- Turn `map` into preimage and pull out the scalar.
        rw [Measure.map_apply h_meas_E hs]
        rw [Measure.map_apply hgF_meas hs_pre]
        -- Apply h_map_gF to the preimage set
        have h_gF_set :
            (Measure.map gF (volume : Measure (Fin 1 → ℝ))) ((fun x : (Fin 1 → ℝ) => E x) ⁻¹' s)
            = (ENNReal.ofReal (abs ((LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
              • (volume : Measure (Fin 1 → ℝ))) ((fun x : (Fin 1 → ℝ) => E x) ⁻¹' s) := by
          rw [h_map_gF]
        rw [← Measure.map_apply hgF_meas hs_pre, h_gF_set]
        simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_smul,
          Pi.smul_apply, Function.comp_apply]
      -- Combine the two left-hand equalities.
      have hL_final :
          (Measure.map (fun x : (Fin 1 → ℝ) => E (gF x))
              (volume : Measure (Fin 1 → ℝ))) s
            = ENNReal.ofReal (abs ((LinearMap.det
                  ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
                * (volume : Measure (Fin 1 → ℝ)) (E ⁻¹' s) := by
        simpa [hL] using hL'
      -- Right-hand side: scalar multiple of `map E volume`, which equals `volume`.
      have hR :
          (ENNReal.ofReal (abs ((LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
              • (volume : Measure ℝ)) s
            = ENNReal.ofReal (abs ((LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
                * (Measure.map (fun x : (Fin 1 → ℝ) => E x)
                    (volume : Measure (Fin 1 → ℝ))) s := by
        simp [Measure.smul_apply, h_map_E, hs]
      -- Express the right-hand side using `Measure.map_apply`.
      have hR' :
          (Measure.map (fun x : (Fin 1 → ℝ) => E x)
              (volume : Measure (Fin 1 → ℝ))) s
            = (volume : Measure (Fin 1 → ℝ)) (E ⁻¹' s) := by
        rw [Measure.map_apply h_meas_E hs]
      -- Conclude both sides coincide.
      calc (Measure.map (fun x : (Fin 1 → ℝ) => E (gF x)) (volume : Measure (Fin 1 → ℝ))) s
          = ENNReal.ofReal (abs ((LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
              * (volume : Measure (Fin 1 → ℝ)) (E ⁻¹' s) := hL_final
        _ = ENNReal.ofReal (abs ((LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
              * (Measure.map (fun x : (Fin 1 → ℝ) => E x) (volume : Measure (Fin 1 → ℝ))) s := by
          rw [hR']
        _ = (ENNReal.ofReal (abs ((LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
              • (volume : Measure ℝ)) s := hR.symm
    -- Finally, identify the determinant factor in dimension one.
    have h_finrank : Module.finrank ℝ (Fin 1 → ℝ) = 1 := by simp
    have h_det_simp :
        ENNReal.ofReal (abs ((LinearMap.det
              ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹))
          = ENNReal.ofReal ((|a|)⁻¹) := by
      have hdet :
          LinearMap.det
              ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
            = (a : ℝ) ^ (Module.finrank ℝ (Fin 1 → ℝ)) := by
        simp
      -- |(det)⁻¹| = |det|⁻¹ and `|a ^ 1| = |a|`.
      have h_abs_inv :
          abs ((LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) )⁻¹)
            = (abs (LinearMap.det
                ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))))⁻¹ := by
        exact abs_inv _
      have h_abs_det :
          abs (LinearMap.det
              ((a : ℝ) • (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))))
            = |a| := by
        -- Reduce to `abs (a ^ 1) = |a|` using `h_finrank`.
        simp [hdet, h_finrank]
      rw [h_abs_inv, h_abs_det]
    -- Assemble the final identity.
    rw [h_map_conj', h_rhs, h_det_simp]

  -- Change of variables for lintegral via the pushforward measure under g
  -- First, ensure a.e.-measurability of f under the pushed-forward measure.
  have hf_map : AEMeasurable f (Measure.map g (volume : Measure ℝ)) := by
    simpa [h_map_scale]
      using aemeasurable_smul_measure_of_aemeasurable
        (f := f) (μ := (volume : Measure ℝ))
        (c := ENNReal.ofReal ((|a|)⁻¹)) hf_vol
  -- lintegral under the map equals lintegral of the pullback integrand
  have h_map_eq : ∫⁻ y, f y ∂(Measure.map g (volume : Measure ℝ))
      = ∫⁻ x, f (g x) ∂(volume : Measure ℝ) := by
    simpa [hg]
      using
        (MeasureTheory.lintegral_map'
          (μ := (volume : Measure ℝ))
          (f := f) (g := g) hf_map hg_aemeas)

  -- Use the pushforward description to pull out the constant in lintegral.

  have h_pull_const :
      ∫⁻ y, f y ∂(Measure.map g (volume : Measure ℝ))
        = ENNReal.ofReal ((|a|)⁻¹) * ∫⁻ y, f y ∂(volume : Measure ℝ) := by
    simp [h_map_scale, lintegral_smul_measure, mul_comm, mul_left_comm, mul_assoc]

  -- Combine mapping identity with the scalar factor extraction
  have h_scaled :
      ∫⁻ x, f (a * x) ∂(volume : Measure ℝ)
        = ENNReal.ofReal ((|a|)⁻¹) * ∫⁻ y, f y ∂(volume : Measure ℝ) := by
    -- From h_map_eq: RHS lintegral equals LHS lintegral of pullback integrand
    -- Then apply h_pull_const.
    have := congrArg id h_map_eq.symm
    -- Replace the mapped lintegral by the scaled one
    simpa [hg] using this.trans h_pull_const

  -- Rewrite the constant in the expected form using |a⁻¹| = (|a|)⁻¹
  have h_abs : ENNReal.ofReal ((|a|)⁻¹) = ENNReal.ofReal (|a⁻¹|) := by
    have : |a⁻¹| = (|a|)⁻¹ := abs_inv a
    rw [this]

  simpa [h_abs] using h_scaled

section ParsevalEquivalence

-- Complex measure-theoretic proof involving pushforward measures and absolute continuity
/-- Integrability of the weighted LogPull is preserved under addition -/
lemma LogPull_integrable_add (σ : ℝ) (f g : Hσ σ)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
    (hg_int : Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :
    Integrable (fun t => LogPull σ (f + g) t * Complex.exp ((1 / 2 : ℝ) * t)) := by
  classical
  -- We will rewrite the integrand a.e. using the a.e. linearity of the Lp
  -- representative `Hσ.toFun` transported along `x = exp t`.
  -- Start from the a.e. identity on the physical side (x-variable).
  have h_add_ae_weighted := toFun_add_ae σ f g
  -- Transport the a.e. equality to the Lebesgue measure on (0,∞).
  have h_rev_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ
  have h_add_ae_vol :
      (fun x : ℝ => Hσ.toFun (f + g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x + Hσ.toFun g x) :=
    h_rev_ac.ae_eq h_add_ae_weighted
  -- Also, mulHaar is absolutely continuous w.r.t. the restricted Lebesgue measure.
  have h_mulHaar_to_volume : mulHaar ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    -- Absolute continuity for withDensity followed by restriction
    have h_base :
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)) ≪ volume := by
      simpa using
        (withDensity_absolutelyContinuous
          (μ := volume) (f := fun x : ℝ => ENNReal.ofReal (1 / x)))
    simpa [mulHaar] using h_base.restrict (Set.Ioi (0 : ℝ))
  -- Hence the equality also holds a.e. for mulHaar on (0,∞).
  have h_add_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (f + g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => Hσ.toFun f x + Hσ.toFun g x) :=
    h_mulHaar_to_volume.ae_eq h_add_ae_vol
  -- Push forward along log to obtain an a.e. equality on t with respect to volume.
  obtain ⟨c, hc0, hcTop, h_map⟩ := mulHaar_pushforward_log
  have h_meas_set : MeasurableSet
      {t : ℝ |
        Hσ.toFun (f + g) (Real.exp t)
          = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)} := by
    -- measurability of both sides composed with exp, then equality set
    have h_meas_l : Measurable (fun t : ℝ => Hσ.toFun (f + g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (f + g)).measurable.comp Real.measurable_exp
    have h_meas_f : Measurable (fun t : ℝ => Hσ.toFun f (Real.exp t)) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_meas_g : Measurable (fun t : ℝ => Hσ.toFun g (Real.exp t)) :=
      (Lp.stronglyMeasurable g).measurable.comp Real.measurable_exp
    have h_meas_r : Measurable (fun t : ℝ =>
        Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)) :=
      h_meas_f.add h_meas_g
    -- {t | u t = v t} is measurable as preimage of the diagonal
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (f + g) (Real.exp t),
         Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t))) :=
      h_meas_l.prodMk h_meas_r
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ |
          Hσ.toFun (f + g) (Real.exp t)
            = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (f + g) (Real.exp t),
               Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have hlog_aemeas : AEMeasurable Real.log mulHaar :=
    Real.measurable_log.aemeasurable
  -- Convert the x-a.e. equality to a t-a.e. equality via `ae_map_iff` and the pushforward.
  have h_ae_map : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (f + g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)) := by
    -- Use the equivalence `ae_map_iff` to pull back to mulHaar.
    have hiff := ae_map_iff (μ := mulHaar)
      (f := Real.log) hlog_aemeas h_meas_set
    rw [hiff]
    -- On x-side (mulHaar), the equality holds a.e.
    -- We need to rewrite x as exp(log x) for x > 0
    -- a.e. on mulHaar we have x > 0 since mulHaar is restricted to Ioi 0
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      -- unfold mulHaar and use `ae_restrict_mem`
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    -- Combine the a.e. equality on x with the positivity to rewrite exp (log x) = x
    refine (h_add_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq :
        Hσ.toFun (f + g) x = Hσ.toFun f x + Hσ.toFun g x := hx.1
    have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    -- Now rewrite the goal using `exp (log x) = x`.
    simpa [Set.mem_setOf_eq, h_exp_log]
  -- Identify the pushforward measure with Lebesgue measure (up to a positive scalar).
  have h_ae_t : (∀ᵐ t ∂ volume,
      Hσ.toFun (f + g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)) := by
    -- Define the predicate used for ae statements on t.
    let P : ℝ → Prop := fun t =>
      Hσ.toFun (f + g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun g (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | P t} := h_meas_set
    -- Use the identification `Measure.map Real.log mulHaar = c • volume`.
    have h_ae_cvol : (∀ᵐ t ∂ (c • volume), P t) := by
      -- First, rewrite the pushforward along the restricted mulHaar.
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by
        simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), P t) := by
        simpa [h_restrict'] using h_ae_map
      -- Then use `h_map` to identify the measure with `c • volume`.
      simpa [h_map] using h'
    -- Pass from `c • volume` to `volume` using that `c ≠ 0`.
    -- Use the `ae_iff` characterization via null sets.
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ P t} := hP_meas.compl
    have h_null_c : (c • volume) {t : ℝ | ¬ P t} = 0 := by
      -- Convert a.e. statement to null-set on `c • volume`.
      have := ((ae_iff (μ := (c • volume)) (p := fun t : ℝ => P t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : c * volume {t : ℝ | ¬ P t} = 0 := by
      -- Rewrite the smul-measure on measurable sets.
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable]
        using h_null_c
    have h_zero : volume {t : ℝ | ¬ P t} = 0 :=
      (mul_eq_zero.mp h_mul_zero).resolve_left hc0
    -- Conclude the a.e. statement for `volume`.
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => P t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  -- With the a.e. identity in hand, rewrite the integrand and conclude by additivity.
  have h_integrand_ae :
      (fun t => LogPull σ (f + g) t * Complex.exp ((1 / 2 : ℝ) * t))
        =ᵐ[volume]
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) +
        (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    refine h_ae_t.mono ?_
    intro t ht
    -- Expand LogPull and use the a.e. linearity of Hσ.toFun at x = exp t.
    simp [LogPull, LogPull_apply, ht, mul_add, mul_left_comm,
          mul_comm, mul_assoc]
  -- The right-hand side is integrable as a sum of integrable functions.
  have h_sum_int : Integrable
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) +
        (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :=
    (hf_int.add hg_int)
  -- Transfer integrability along the a.e. equality.
  exact h_sum_int.congr h_integrand_ae.symm

/-- Integrability of the weighted LogPull for subtraction -/
lemma LogPull_integrable_sub (σ : ℝ) (f g : Hσ σ)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
    (hg_int : Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :
    Integrable (fun t => LogPull σ (f - g) t * Complex.exp ((1 / 2 : ℝ) * t)) := by
  classical
  -- Start from the a.e. identity for subtraction on the physical side (x-variable).
  have h_sub_ae_weighted :
      (fun x : ℝ => Hσ.toFun (f - g) x)
        =ᵐ[mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun g x) :=
    (Lp.coeFn_sub (f := (f : Lp ℂ 2
      (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))))
      (g := (g : Lp ℂ 2
      (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))))
  -- Transport the a.e. equality to the Lebesgue measure on (0,∞).
  have h_rev_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ
  have h_sub_ae_vol :
      (fun x : ℝ => Hσ.toFun (f - g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun g x) :=
    h_rev_ac.ae_eq h_sub_ae_weighted
  -- Also, mulHaar is absolutely continuous w.r.t. the restricted Lebesgue measure.
  have h_mulHaar_to_volume : mulHaar ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    have h_base :
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)) ≪ volume := by
      simpa using
        (withDensity_absolutelyContinuous
          (μ := volume) (f := fun x : ℝ => ENNReal.ofReal (1 / x)))
    simpa [mulHaar] using h_base.restrict (Set.Ioi (0 : ℝ))
  -- Hence the equality also holds a.e. for mulHaar on (0,∞).
  have h_sub_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (f - g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun g x) :=
    h_mulHaar_to_volume.ae_eq h_sub_ae_vol
  -- Push forward along log to obtain an a.e. equality on t with respect to volume.
  obtain ⟨c, hc0, hcTop, h_map⟩ := mulHaar_pushforward_log
  have h_meas_set : MeasurableSet
      {t : ℝ |
        Hσ.toFun (f - g) (Real.exp t)
          = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)} := by
    -- measurability of both sides composed with exp, then equality set
    have h_meas_l : Measurable (fun t : ℝ => Hσ.toFun (f - g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (f - g)).measurable.comp Real.measurable_exp
    have h_meas_f : Measurable (fun t : ℝ => Hσ.toFun f (Real.exp t)) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_meas_g : Measurable (fun t : ℝ => Hσ.toFun g (Real.exp t)) :=
      (Lp.stronglyMeasurable g).measurable.comp Real.measurable_exp
    have h_meas_r : Measurable (fun t : ℝ =>
        Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)) :=
      h_meas_f.sub h_meas_g
    -- {t | u t = v t} is measurable as preimage of the diagonal
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (f - g) (Real.exp t),
         Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t))) :=
      h_meas_l.prodMk h_meas_r
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ |
          Hσ.toFun (f - g) (Real.exp t)
            = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (f - g) (Real.exp t),
               Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have hlog_aemeas : AEMeasurable Real.log mulHaar :=
    Real.measurable_log.aemeasurable
  -- Convert the x-a.e. equality to a t-a.e. equality via `ae_map_iff` and the pushforward.
  have h_ae_map : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (f - g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)) := by
    -- Use the equivalence `ae_map_iff` to pull back to mulHaar.
    have hiff := ae_map_iff (μ := mulHaar)
      (f := Real.log) hlog_aemeas h_meas_set
    rw [hiff]
    -- On x-side (mulHaar), the equality holds a.e.
    -- We need to rewrite x as exp(log x) for x > 0
    -- a.e. on mulHaar we have x > 0 since mulHaar is restricted to Ioi 0
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      -- unfold mulHaar and use `ae_restrict_mem`
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    -- Combine the a.e. equality on x with the positivity to rewrite exp (log x) = x
    refine (h_sub_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq :
        Hσ.toFun (f - g) x = Hσ.toFun f x - Hσ.toFun g x := hx.1
    have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    -- Now rewrite the goal using `exp (log x) = x`.
    simpa [Set.mem_setOf_eq, h_exp_log]
  -- Identify the pushforward measure with Lebesgue measure (up to a positive scalar).
  have h_ae_t : (∀ᵐ t ∂ volume,
      Hσ.toFun (f - g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)) := by
    -- Define the predicate used for ae statements on t.
    let P : ℝ → Prop := fun t =>
      Hσ.toFun (f - g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun g (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | P t} := h_meas_set
    -- Use the identification `Measure.map Real.log mulHaar = c • volume`.
    have h_ae_cvol : (∀ᵐ t ∂ (c • volume), P t) := by
      -- First, rewrite the pushforward along the restricted mulHaar.
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by
        simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), P t) := by
        simpa [h_restrict'] using h_ae_map
      -- Then use `h_map` to identify the measure with `c • volume`.
      simpa [h_map] using h'
    -- Pass from `c • volume` to `volume` using that `c ≠ 0`.
    -- Use the `ae_iff` characterization via null sets.
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ P t} := hP_meas.compl
    have h_null_c : (c • volume) {t : ℝ | ¬ P t} = 0 := by
      -- Convert a.e. statement to null-set on `c • volume`.
      have := ((ae_iff (μ := (c • volume)) (p := fun t : ℝ => P t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : c * volume {t : ℝ | ¬ P t} = 0 := by
      -- Rewrite the smul-measure on measurable sets.
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable]
        using h_null_c
    have h_zero : volume {t : ℝ | ¬ P t} = 0 :=
      (mul_eq_zero.mp h_mul_zero).resolve_left hc0
    -- Conclude the a.e. statement for `volume`.
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => P t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  -- With the a.e. identity in hand, rewrite the integrand and conclude by subtraction.
  have h_integrand_ae :
      (fun t => LogPull σ (f - g) t * Complex.exp ((1 / 2 : ℝ) * t))
        =ᵐ[volume]
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) -
        (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    refine h_ae_t.mono ?_
    intro t ht
    -- Expand LogPull and use the a.e. linearity of Hσ.toFun at x = exp t.
    simp [LogPull, LogPull_apply, ht, mul_sub, mul_left_comm,
          mul_comm, mul_assoc]
  -- The right-hand side is integrable as a difference of integrable functions.
  have h_diff_int : Integrable
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) -
        (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :=
    (hf_int.sub hg_int)
  -- Transfer integrability along the a.e. equality.
  exact h_diff_int.congr h_integrand_ae.symm

/-- Integrability of the weighted LogPull for addition with scalar multiplication -/
lemma LogPull_integrable_add_smul (σ : ℝ) (f g : Hσ σ) (c : ℂ)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
    (hg_int : Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :
    Integrable (fun t => LogPull σ (f + c • g) t * Complex.exp ((1 / 2 : ℝ) * t)) := by
  classical
  -- Start from the a.e. identity on the physical side (x-variable).
  have h_add_ae_weighted := toFun_add_ae σ f (c • g)
  have h_smul_ae_weighted := toFun_smul_ae σ c g
  -- Transport the a.e. equality to the Lebesgue measure on (0,∞).
  have h_rev_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ
  have h_add_ae_vol :
      (fun x : ℝ => Hσ.toFun (f + c • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x + Hσ.toFun (c • g) x) :=
    h_rev_ac.ae_eq h_add_ae_weighted
  have h_smul_ae_vol :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    h_rev_ac.ae_eq h_smul_ae_weighted
  -- Also, mulHaar is absolutely continuous w.r.t. the restricted Lebesgue measure.
  have h_mulHaar_to_volume : mulHaar ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    have h_base :
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)) ≪ volume := by
      simpa using
        (withDensity_absolutelyContinuous
          (μ := volume) (f := fun x : ℝ => ENNReal.ofReal (1 / x)))
    simpa [mulHaar] using h_base.restrict (Set.Ioi (0 : ℝ))
  -- Hence the equalities also hold a.e. for mulHaar on (0,∞).
  have h_add_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (f + c • g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => Hσ.toFun f x + Hσ.toFun (c • g) x) :=
    h_mulHaar_to_volume.ae_eq h_add_ae_vol
  have h_smul_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    h_mulHaar_to_volume.ae_eq h_smul_ae_vol
  -- Push forward along log to obtain a.e. equalities on t with respect to volume.
  obtain ⟨cm, hcm0, hcmTop, h_map⟩ := mulHaar_pushforward_log
  -- Measurability of equality sets after composing with exp.
  have h_meas_set_add : MeasurableSet
      {t : ℝ |
        Hσ.toFun (f + c • g) (Real.exp t)
          = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)} := by
    have h_meas_l : Measurable (fun t : ℝ => Hσ.toFun (f + c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (f + c • g)).measurable.comp Real.measurable_exp
    have h_meas_f : Measurable (fun t : ℝ => Hσ.toFun f (Real.exp t)) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_meas_cg : Measurable (fun t : ℝ => Hσ.toFun (c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (c • g)).measurable.comp Real.measurable_exp
    have h_meas_r : Measurable (fun t : ℝ =>
        Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)) :=
      h_meas_f.add h_meas_cg
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (f + c • g) (Real.exp t),
         Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t))) :=
      h_meas_l.prodMk h_meas_r
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ |
          Hσ.toFun (f + c • g) (Real.exp t)
            = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (f + c • g) (Real.exp t),
               Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have h_meas_set_smul : MeasurableSet
      {t : ℝ |
        Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)} := by
    have h_meas_cg : Measurable (fun t : ℝ => Hσ.toFun (c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (c • g)).measurable.comp Real.measurable_exp
    have h_meas_g : Measurable (fun t : ℝ => Hσ.toFun g (Real.exp t)) :=
      (Lp.stronglyMeasurable g).measurable.comp Real.measurable_exp
    have h_meas_rhs : Measurable (fun t : ℝ => c * Hσ.toFun g (Real.exp t)) :=
      measurable_const.mul h_meas_g
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (c • g) (Real.exp t), c * Hσ.toFun g (Real.exp t))) :=
      h_meas_cg.prodMk h_meas_rhs
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ | Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (c • g) (Real.exp t), c * Hσ.toFun g (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have hlog_aemeas : AEMeasurable Real.log mulHaar :=
    Real.measurable_log.aemeasurable
  -- Convert the x-a.e. equalities to t-a.e. equalities via `ae_map_iff` and the pushforward.
  have h_ae_map_add : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (f + c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)) := by
    have hiff := ae_map_iff (μ := mulHaar) (f := Real.log) hlog_aemeas h_meas_set_add
    rw [hiff]
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    refine (h_add_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq := hx.1; have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [Set.mem_setOf_eq, h_exp_log] using hx_eq
  have h_ae_map_smul : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)) := by
    have hiff := ae_map_iff (μ := mulHaar) (f := Real.log) hlog_aemeas h_meas_set_smul
    rw [hiff]
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    refine (h_smul_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq := hx.1; have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [Set.mem_setOf_eq, h_exp_log] using hx_eq
  -- Identify the pushforward measure with Lebesgue measure (up to a positive scalar).
  have h_ae_t_add : (∀ᵐ t ∂ volume,
      Hσ.toFun (f + c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)) := by
    -- define predicate for add
    let Padd : ℝ → Prop := fun t =>
      Hσ.toFun (f + c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) + Hσ.toFun (c • g) (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | Padd t} := h_meas_set_add
    have h_ae_cvol : (∀ᵐ t ∂ (cm • volume), Padd t) := by
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), Padd t) := by
        simpa [h_restrict'] using h_ae_map_add
      simpa [h_map] using h'
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ Padd t} := hP_meas.compl
    have h_null_c : (cm • volume) {t : ℝ | ¬ Padd t} = 0 := by
      have := ((ae_iff (μ := (cm • volume)) (p := fun t : ℝ => Padd t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : cm * volume {t : ℝ | ¬ Padd t} = 0 := by
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable] using h_null_c
    have h_zero : volume {t : ℝ | ¬ Padd t} = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left hcm0
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => Padd t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  have h_ae_t_smul : (∀ᵐ t ∂ volume,
      Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)) := by
    let Psmul : ℝ → Prop := fun t => Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | Psmul t} := h_meas_set_smul
    have h_ae_cvol : (∀ᵐ t ∂ (cm • volume), Psmul t) := by
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), Psmul t) := by
        simpa [h_restrict'] using h_ae_map_smul
      simpa [h_map] using h'
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ Psmul t} := hP_meas.compl
    have h_null_c : (cm • volume) {t : ℝ | ¬ Psmul t} = 0 := by
      have := ((ae_iff (μ := (cm • volume)) (p := fun t : ℝ => Psmul t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : cm * volume {t : ℝ | ¬ Psmul t} = 0 := by
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable] using h_null_c
    have h_zero : volume {t : ℝ | ¬ Psmul t} = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left hcm0
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => Psmul t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  have h_integrand_ae :
      (fun t => LogPull σ (f + c • g) t * Complex.exp ((1 / 2 : ℝ) * t))
        =ᵐ[volume]
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) +
        c * (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    refine (h_ae_t_add.and h_ae_t_smul).mono ?_
    intro t hts
    have ht_add := hts.1
    have ht_smul := hts.2
    -- Expand LogPull and use the a.e. linearity at x = exp t and scalar multiplication.
    simp [LogPull, LogPull_apply, ht_add, ht_smul, mul_add, mul_left_comm,
          mul_comm, mul_assoc]
  -- The right-hand side is integrable as a sum of integrable functions and a constant multiple.
  have h_rhs_int : Integrable
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) +
        c * (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    exact hf_int.add (hg_int.const_mul c)
  -- Transfer integrability along the a.e. equality.
  exact h_rhs_int.congr h_integrand_ae.symm

/-- Integrability of the weighted LogPull for subtraction with scalar multiplication -/
lemma LogPull_integrable_sub_smul (σ : ℝ) (f g : Hσ σ) (c : ℂ)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)))
    (hg_int : Integrable (fun t => LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) :
    Integrable (fun t => LogPull σ (f - c • g) t * Complex.exp ((1 / 2 : ℝ) * t)) := by
  classical
  -- a.e. identities on the physical side (x-variable)
  have h_sub_ae_weighted :
      (fun x : ℝ => Hσ.toFun (f - c • g) x)
        =ᵐ[mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun (c • g) x) :=
    (Lp.coeFn_sub (f := (f : Lp ℂ 2
      (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))))
      (g := ((c • g) : Lp ℂ 2
      (mulHaar.withDensity fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1))))))
  have h_smul_ae_weighted :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[mulHaar.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    toFun_smul_ae σ c g
  -- Transport the a.e. equalities to the Lebesgue measure on (0,∞).
  have h_rev_ac :
      volume.restrict (Set.Ioi (0 : ℝ)) ≪
        mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) :=
    volume_restrict_absolutelyContinuous_weighted σ
  have h_sub_ae_vol :
      (fun x : ℝ => Hσ.toFun (f - c • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun (c • g) x) :=
    h_rev_ac.ae_eq h_sub_ae_weighted
  have h_smul_ae_vol :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    h_rev_ac.ae_eq h_smul_ae_weighted
  -- Also, mulHaar ≪ volume.restrict (Ioi 0)
  have h_mulHaar_to_volume : mulHaar ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    have h_base :
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x)) ≪ volume := by
      simpa using
        (withDensity_absolutelyContinuous
          (μ := volume) (f := fun x : ℝ => ENNReal.ofReal (1 / x)))
    simpa [mulHaar] using h_base.restrict (Set.Ioi (0 : ℝ))
  -- Hence these also hold a.e. for mulHaar on (0,∞).
  have h_sub_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (f - c • g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => Hσ.toFun f x - Hσ.toFun (c • g) x) :=
    h_mulHaar_to_volume.ae_eq h_sub_ae_vol
  have h_smul_ae_mulHaar :
      (fun x : ℝ => Hσ.toFun (c • g) x)
        =ᵐ[mulHaar]
      (fun x : ℝ => c * Hσ.toFun g x) :=
    h_mulHaar_to_volume.ae_eq h_smul_ae_vol
  -- Push forward along log to obtain t-a.e. equalities.
  obtain ⟨cm, hcm0, hcmTop, h_map⟩ := mulHaar_pushforward_log
  -- Measurability of equality sets after composing with exp.
  have h_meas_set_sub : MeasurableSet
      {t : ℝ |
        Hσ.toFun (f - c • g) (Real.exp t)
          = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)} := by
    have h_meas_l : Measurable (fun t : ℝ => Hσ.toFun (f - c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (f - c • g)).measurable.comp Real.measurable_exp
    have h_meas_f : Measurable (fun t : ℝ => Hσ.toFun f (Real.exp t)) :=
      (Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp
    have h_meas_cg : Measurable (fun t : ℝ => Hσ.toFun (c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (c • g)).measurable.comp Real.measurable_exp
    have h_meas_r : Measurable (fun t : ℝ =>
        Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)) :=
      h_meas_f.sub h_meas_cg
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (f - c • g) (Real.exp t),
         Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t))) :=
      h_meas_l.prodMk h_meas_r
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ |
          Hσ.toFun (f - c • g) (Real.exp t)
            = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (f - c • g) (Real.exp t),
               Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have h_meas_set_smul : MeasurableSet
      {t : ℝ |
        Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)} := by
    have h_meas_cg : Measurable (fun t : ℝ => Hσ.toFun (c • g) (Real.exp t)) :=
      (Lp.stronglyMeasurable (c • g)).measurable.comp Real.measurable_exp
    have h_meas_g : Measurable (fun t : ℝ => Hσ.toFun g (Real.exp t)) :=
      (Lp.stronglyMeasurable g).measurable.comp Real.measurable_exp
    have h_meas_rhs : Measurable (fun t : ℝ => c * Hσ.toFun g (Real.exp t)) :=
      measurable_const.mul h_meas_g
    have h_pair : Measurable (fun t =>
        (Hσ.toFun (c • g) (Real.exp t), c * Hσ.toFun g (Real.exp t))) :=
      h_meas_cg.prodMk h_meas_rhs
    have hS : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have h_eq :
        {t : ℝ | Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)}
          = (fun t =>
              (Hσ.toFun (c • g) (Real.exp t), c * Hσ.toFun g (Real.exp t))) ⁻¹'
            {p : ℂ × ℂ | p.1 = p.2} := by
      ext t; rfl
    rw [h_eq]
    exact hS.preimage h_pair
  have hlog_aemeas : AEMeasurable Real.log mulHaar :=
    Real.measurable_log.aemeasurable
  -- Convert equalities via ae_map_iff
  have h_ae_map_sub : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (f - c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)) := by
    have hiff := ae_map_iff (μ := mulHaar) (f := Real.log) hlog_aemeas h_meas_set_sub
    rw [hiff]
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    refine (h_sub_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq := hx.1; have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [Set.mem_setOf_eq, h_exp_log] using hx_eq
  have h_ae_map_smul : (∀ᵐ t ∂ (Measure.map Real.log mulHaar),
      Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)) := by
    have hiff := ae_map_iff (μ := mulHaar) (f := Real.log) hlog_aemeas h_meas_set_smul
    rw [hiff]
    have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
      simpa [mulHaar] using
        (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
          (s := Set.Ioi (0 : ℝ)))
    refine (h_smul_ae_mulHaar.and h_pos).mono ?_
    intro x hx
    have hx_eq := hx.1; have hx_pos : 0 < x := hx.2
    have h_exp_log : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [Set.mem_setOf_eq, h_exp_log] using hx_eq
  -- Identify the pushforward measure with Lebesgue measure (up to a positive scalar).
  have h_ae_t_sub : (∀ᵐ t ∂ volume,
      Hσ.toFun (f - c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)) := by
    let Psub : ℝ → Prop := fun t =>
      Hσ.toFun (f - c • g) (Real.exp t)
        = Hσ.toFun f (Real.exp t) - Hσ.toFun (c • g) (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | Psub t} := h_meas_set_sub
    have h_ae_cvol : (∀ᵐ t ∂ (cm • volume), Psub t) := by
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), Psub t) := by
        simpa [h_restrict'] using h_ae_map_sub
      simpa [h_map] using h'
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ Psub t} := hP_meas.compl
    have h_null_c : (cm • volume) {t : ℝ | ¬ Psub t} = 0 := by
      have := ((ae_iff (μ := (cm • volume)) (p := fun t : ℝ => Psub t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : cm * volume {t : ℝ | ¬ Psub t} = 0 := by
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable] using h_null_c
    have h_zero : volume {t : ℝ | ¬ Psub t} = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left hcm0
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => Psub t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  have h_ae_t_smul : (∀ᵐ t ∂ volume,
      Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)) := by
    let Psmul : ℝ → Prop := fun t => Hσ.toFun (c • g) (Real.exp t) = c * Hσ.toFun g (Real.exp t)
    have hP_meas : MeasurableSet {t : ℝ | Psmul t} := h_meas_set_smul
    have h_ae_cvol : (∀ᵐ t ∂ (cm • volume), Psmul t) := by
      have h_restrict' : mulHaar.restrict (Set.Ioi (0 : ℝ)) = mulHaar := by simp [mulHaar]
      have h' : (∀ᵐ t ∂ (Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ)))), Psmul t) := by
        simpa [h_restrict'] using h_ae_map_smul
      simpa [h_map] using h'
    have h_notP_meas : MeasurableSet {t : ℝ | ¬ Psmul t} := hP_meas.compl
    have h_null_c : (cm • volume) {t : ℝ | ¬ Psmul t} = 0 := by
      have := ((ae_iff (μ := (cm • volume)) (p := fun t : ℝ => Psmul t))).1 h_ae_cvol
      simpa [Set.compl_setOf] using this
    have h_mul_zero : cm * volume {t : ℝ | ¬ Psmul t} = 0 := by
      simpa [Measure.smul_apply, h_notP_meas, measure_toMeasurable] using h_null_c
    have h_zero : volume {t : ℝ | ¬ Psmul t} = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left hcm0
    exact ((ae_iff (μ := volume) (p := fun t : ℝ => Psmul t))).2
      (by simpa [Set.compl_setOf] using h_zero)
  have h_integrand_ae :
      (fun t => LogPull σ (f - c • g) t * Complex.exp ((1 / 2 : ℝ) * t))
        =ᵐ[volume]
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) -
        c * (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    refine (h_ae_t_sub.and h_ae_t_smul).mono ?_
    intro t hts
    have ht_sub := hts.1
    have ht_smul := hts.2
    simp [LogPull, LogPull_apply, ht_sub, ht_smul, mul_sub, mul_left_comm,
          mul_comm, mul_assoc]
  -- The right-hand side is integrable as a difference of integrable functions with scalar multiple.
  have h_rhs_int : Integrable
      (fun t =>
        (LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) -
        c * (LogPull σ g t * Complex.exp ((1 / 2 : ℝ) * t))) := by
    exact hf_int.sub (hg_int.const_mul c)
  exact h_rhs_int.congr h_integrand_ae.symm

-- Complex measure-theoretic proof involving ENNReal to Real to Complex conversion
/-- Convert ENNReal norm equality to Complex, handling coercion of binary operations -/
lemma norm_squared_to_complex_add_sub (σ C : ℝ) (h : Hσ σ)
    (hC_pos : C > 0)
    (h_norm : ∫⁻ (x : ℝ) in Set.Ioi 0, ENNReal.ofReal
      (‖(h : Hσ σ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume =
      ENNReal.ofReal (C * ∫ (τ : ℝ), ‖mellinTransform
        ((h : Hσ σ) : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)) :
    Complex.ofReal
      ((∫⁻ (x : ℝ) in Set.Ioi 0,
          ENNReal.ofReal (‖(h : Hσ σ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume).toReal)
      =
    Complex.ofReal (C * ∫ τ : ℝ,
        ‖mellinTransform (((h : Hσ σ) : ℝ → ℂ)) (σ + I * τ)‖ ^ 2 ∂volume) := by
  -- Convert the ENNReal equality into a real equality via `toReal`,
  -- then embed both sides into `ℂ` using `Complex.ofReal`.
  have h_toReal :
      (∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (‖(h : Hσ σ) x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume).toReal
        = C * ∫ τ : ℝ,
            ‖mellinTransform ((h : Hσ σ) : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
    have := congrArg ENNReal.toReal h_norm
    -- Right-hand side is nonnegative, so `toReal (ofReal _) = _` applies
    have h_nonneg :
        0 ≤ C * ∫ τ : ℝ,
          ‖mellinTransform ((h : Hσ σ) : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
      refine mul_nonneg (le_of_lt hC_pos) ?_
      refine integral_nonneg ?hpos
      intro τ
      exact sq_nonneg _
    simpa [ENNReal.toReal_ofReal h_nonneg]
      using this
  simp [h_toReal]

/-- Mellin transform is linear in the input (addition) on its natural domain.
For the set integral definition used here, this requires integrability of both
integrands over `(0,∞)`.

`hf` and `hg` assert integrability of the Mellin integrands for `f` and `g` respectively. -/
lemma mellinTransform_add
    (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun t : ℝ => f t * t ^ (s - 1)) (Set.Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => g t * t ^ (s - 1)) (Set.Ioi (0 : ℝ)) volume) :
    mellinTransform (f + g) s = mellinTransform f s + mellinTransform g s := by
  classical
  unfold Frourio.mellinTransform
  -- Use linearity of the set integral under the given integrability hypotheses
  have hlin := (MeasureTheory.integral_add hf hg)
  -- Rewrite the integrand `(f+g) * k` as `f*k + g*k` and simplify
  have h_eq : ∀ t, (f + g) t * t ^ (s - 1) = f t * t ^ (s - 1) + g t * t ^ (s - 1) := by
    intro t
    simp [Pi.add_apply]
    ring
  simp only [h_eq, hlin]

/-- Mellin transform is linear in the input (subtraction) on its natural domain.
Requires integrability of both integrands over `(0,∞)`. -/
lemma mellinTransform_sub
    (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun t : ℝ => f t * t ^ (s - 1)) (Set.Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => g t * t ^ (s - 1)) (Set.Ioi (0 : ℝ)) volume) :
    mellinTransform (f - g) s = mellinTransform f s - mellinTransform g s := by
  classical
  unfold Frourio.mellinTransform
  have hlin := MeasureTheory.integral_sub hf hg
  have h_eq : ∀ t, (f - g) t * t ^ (s - 1) = f t * t ^ (s - 1) - g t * t ^ (s - 1) := by
    intro t
    simp [Pi.sub_apply]
    ring
  simp only [h_eq, hlin]

/-- Mellin transform commutes with scalar multiplication (no extra hypotheses).
We use linearity of the Bochner integral over the restricted measure. -/
lemma mellinTransform_smul (c : ℂ) (f : ℝ → ℂ) (s : ℂ) :
    mellinTransform (c • f) s = c * mellinTransform f s := by
  classical
  unfold Frourio.mellinTransform
  -- Switch to the restricted measure presentation and pull out the scalar
  have hrewrite :
      (fun t : ℝ => (c • f) t * (↑t) ^ (s - 1))
        = (fun t : ℝ => c • (f t * (↑t) ^ (s - 1))) := by
    funext t
    simp [smul_eq_mul, mul_left_comm, mul_assoc]
  have h_integral := MeasureTheory.integral_smul
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (c := c)
      (f := fun t : ℝ => f t * (↑t) ^ (s - 1))
  rw [hrewrite, h_integral, smul_eq_mul]

/-- Under the weighted L² norm condition, the Mellin integrand is integrable. -/
lemma mellin_integrable_of_weighted_L2 (σ : ℝ) (f : Hσ σ) (τ : ℝ)
    (hf_int : Integrable (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t))) :
    IntegrableOn (fun t : ℝ => (f : ℝ → ℂ) t * t ^ (σ + I * τ - 1)) (Set.Ioi 0) := by
  classical
  -- Strategy outline:
  -- 1) Work with the restricted measure on `(0,∞)` and rewrite the goal
  --    as an `Integrable` statement for `volume.restrict (Ioi 0)`.
  -- 2) Use the logarithmic change of variables `x = exp t` to relate the
  --    Mellin integrand `(f x) * x^(σ + iτ - 1)` to
  --    `LogPull σ f t * exp((1/2) t)` times a unimodular factor `exp(iτ t)`.
  -- 3) Deduce integrability from the hypothesis `hf_int` and the boundedness
  --    of the unimodular factor.
  -- The detailed change-of-variables and a.e. identities are deferred as sorries.
  -- Reduce to the restricted-measure formulation
  change Integrable
    (fun x : ℝ => (f : ℝ → ℂ) x * x ^ (σ + I * τ - 1)) (volume.restrict (Set.Ioi 0)) at *
  -- Pointwise a.e. identification of the Mellin integrand via `x = exp t`
  have h_ae_change :
      (fun x : ℝ => (f : ℝ → ℂ) x * x ^ (σ + I * τ - 1))
        =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun x : ℝ =>
        ((LogPull σ f (Real.log x) * Complex.exp ((1 / 2 : ℝ) * Real.log x))
          * Complex.exp (Complex.I * (τ : ℝ) * Real.log x)) * (1 / (x : ℂ))) := by
    -- Skeleton: prove the pointwise identity for `x > 0` using `x = exp t`.
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hxpos : 0 < x := hx
    -- For x>0, we can rewrite powers via `log` and `exp`.
    -- Goal: (f x) * x^(σ + I*τ - 1)
    --   = (LogPull σ f (log x) * exp((1/2) log x)) * exp(i τ log x) * (1/x).
    -- This follows from `LogPull σ f (log x) = exp((σ - 1/2) log x) * f x` and
    -- `x^w = exp(w * log x)` for x>0.
    -- Full algebraic rewriting is deferred.
    -- Set t = log x and record `exp t = x` for x>0.
    set t : ℝ := Real.log x with ht
    have hxexp : Real.exp t = x := by simpa [ht] using Real.exp_log hxpos
    -- Expand LogPull at t = log x.
    have h_logpull :
        LogPull σ f t = (Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ) * (Hσ.toFun f x) := by
      -- Use `LogPull_apply` and `exp_log`.
      rw [LogPull_apply]
      congr 1
      rw [hxexp]
    -- Combine the weights: (σ-1/2) and 1/2 to get σ.
    have h_sigma :
        (LogPull σ f t) * Complex.exp ((1 / 2 : ℝ) * t)
          = (Real.exp (σ * t) : ℂ) * (Hσ.toFun f x) := by
      -- Rewrite `LogPull` and regroup factors.
      calc
        (LogPull σ f t) * Complex.exp ((1 / 2 : ℝ) * t)
            = ((Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ) * (Hσ.toFun f x))
                * Complex.exp ((1 / 2 : ℝ) * t) := by
                  rw [h_logpull]
        _ = ((Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ)
                * Complex.exp ((1 / 2 : ℝ) * t)) * (Hσ.toFun f x) := by
                  simp [mul_comm, mul_left_comm, mul_assoc]
        _ = (((Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ)
                * (Real.exp ((1 / 2 : ℝ) * t) : ℂ))) * (Hσ.toFun f x) := by
                  -- Convert complex exponential at a real to a real exponential coerced to ℂ
                  simp only [Complex.ofReal_exp]
                  ring_nf
                  simp [mul_comm, mul_left_comm, mul_assoc]
        _ = (Real.exp (σ * t) : ℂ) * (Hσ.toFun f x) := by
                  -- Combine the real exponentials using `exp_add` and `ring`.
                  have hsum : ((σ - (1 / 2 : ℝ)) * t) + ((1 / 2 : ℝ) * t) = σ * t := by
                    ring
                  have h_real :
                      Real.exp ((σ - (1 / 2 : ℝ)) * t) * Real.exp ((1 / 2 : ℝ) * t)
                        = Real.exp (σ * t) := by
                    -- From `exp_add : exp (a + b) = exp a * exp b`.
                    rw [← Real.exp_add, hsum]
                  have h_complex :
                      ((Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ)
                        * (Real.exp ((1 / 2 : ℝ) * t) : ℂ))
                        = (Real.exp (σ * t) : ℂ) := by
                    simp only [← Complex.ofReal_mul]
                    rw [h_real]
                  simp only [Complex.ofReal_exp]
                  rw [← Complex.exp_add]
                  congr 1
                  push_cast
                  ring_nf
    -- Multiply by the unimodular factor exp(i τ t).
    have h_sigma_tau :
        ((LogPull σ f t) * Complex.exp ((1 / 2 : ℝ) * t))
            * Complex.exp (Complex.I * (τ : ℝ) * t)
          = (Hσ.toFun f x) * Complex.exp ((σ + Complex.I * (τ : ℝ)) * t) := by
      -- Multiply the identity `h_sigma` by the unimodular factor and regroup.
      have := congrArg (fun z => z * Complex.exp (Complex.I * (τ : ℝ) * t)) h_sigma
      -- Reassociate to place `(Hσ.toFun f x)` in front.
      have h_step :
          ((Real.exp (σ * t) : ℂ) * (Hσ.toFun f x))
              * Complex.exp (Complex.I * (τ : ℝ) * t)
            = (Hσ.toFun f x)
                * (((Real.exp (σ * t) : ℂ)
                      * Complex.exp (Complex.I * (τ : ℝ) * t))) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      -- Combine exponentials: `exp(σ t) * exp(i τ t) = exp((σ + i τ) t)`.
      have h_exp :
          ((Real.exp (σ * t) : ℂ) * Complex.exp (Complex.I * (τ : ℝ) * t))
            = Complex.exp ((σ + Complex.I * (τ : ℝ)) * t) := by
        -- Convert the real exponential to complex exponential and use `exp_add`.
        have : Complex.exp (σ * t) = (Real.exp (σ * t) : ℂ) := by
          simp only [Complex.ofReal_exp]
          congr 1
          push_cast
          ring
        -- Replace and apply `exp_add`.
        have h' :
            Complex.exp (σ * t) * Complex.exp (Complex.I * (τ : ℝ) * t)
                = Complex.exp ((σ * t) + (Complex.I * (τ : ℝ) * t)) := by
          rw [← Complex.exp_add]
        -- Rewrite `(σ * t) + (i τ * t) = (σ + i τ) * t` in `ℂ`.
        have hlin :
            ((σ * t) + (Complex.I * (τ : ℝ) * t) : ℂ)
              = ((σ + Complex.I * (τ : ℝ)) * t : ℂ) := by
          ring_nf
        -- Assemble the chain.
        have := by
          simpa [hlin] using h'
        simp [this]
      -- Finish by substituting the combined exponential into `h_step` and `this`.
      -- Start from the left-hand side using `this`.
      have hL :
          ((LogPull σ f t) * Complex.exp ((1 / 2 : ℝ) * t))
              * Complex.exp (Complex.I * (τ : ℝ) * t)
            = ((Real.exp (σ * t) : ℂ) * (Hσ.toFun f x))
                * Complex.exp (Complex.I * (τ : ℝ) * t) := by
        simpa using this
      -- Now rewrite via `h_step` and then collapse exponentials via `h_exp`.
      calc
        ((LogPull σ f t) * Complex.exp ((1 / 2 : ℝ) * t))
            * Complex.exp (Complex.I * (τ : ℝ) * t)
            = ((Real.exp (σ * t) : ℂ) * (Hσ.toFun f x))
                * Complex.exp (Complex.I * (τ : ℝ) * t) := hL
        _ = (Hσ.toFun f x)
                * (((Real.exp (σ * t) : ℂ)
                      * Complex.exp (Complex.I * (τ : ℝ) * t))) := h_step
        _ = (Hσ.toFun f x) * Complex.exp ((σ + Complex.I * (τ : ℝ)) * t) := by
              rw [h_exp]
    -- Divide by x = exp t, i.e. multiply by exp(-t), to get (σ + iτ - 1).
    have h_sigma_tau_one :
        (((LogPull σ f t) * Complex.exp ((1 / 2 : ℝ) * t))
            * Complex.exp (Complex.I * (τ : ℝ) * t)) * (1 / (x : ℂ))
          = (Hσ.toFun f x) * Complex.exp (((σ + Complex.I * (τ : ℝ)) - 1) * t) := by
      -- Multiply `h_sigma_tau` by `1/x` and regroup factors.
      have := congrArg (fun z => z * (1 / (x : ℂ))) h_sigma_tau
      have h_step :
          ((Hσ.toFun f x) * Complex.exp ((σ + Complex.I * (τ : ℝ)) * t))
              * (1 / (x : ℂ))
            = (Hσ.toFun f x)
                * (Complex.exp ((σ + Complex.I * (τ : ℝ)) * t) * (1 / (x : ℂ))) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      -- Express `1/x` as `exp (−t)` using `x = exp t` for `x>0`.
      have hxRC : (Real.exp t : ℂ) = (x : ℂ) := by
        simpa using congrArg (fun r : ℝ => (r : ℂ)) hxexp
      have hxexpC : Complex.exp (t : ℂ) = (x : ℂ) := by
        simpa [Complex.ofReal_exp] using hxRC
      have hx_inv : (1 / (x : ℂ)) = Complex.exp (-(t : ℂ)) := by
        have h' : (x : ℂ) = Complex.exp (t : ℂ) := by simpa using hxexpC.symm
        have hinv := congrArg Inv.inv h'
        simpa [one_div, Complex.exp_neg] using hinv
      -- Combine exponentials: `exp((σ + iτ)t) * exp(−t) = exp(((σ + iτ) − 1) t)`.
      have h_exp :
          Complex.exp ((σ + Complex.I * (τ : ℝ)) * t) * Complex.exp (-(t : ℂ))
            = Complex.exp (((σ + Complex.I * (τ : ℝ)) - 1) * t) := by
        rw [← Complex.exp_add]
        congr 1
        ring_nf
      -- Assemble the pieces.
      calc
        (((LogPull σ f t) * Complex.exp ((1 / 2 : ℝ) * t))
            * Complex.exp (Complex.I * (τ : ℝ) * t)) * (1 / (x : ℂ))
            = ((Hσ.toFun f x) * Complex.exp ((σ + Complex.I * (τ : ℝ)) * t))
                * (1 / (x : ℂ)) := by simpa using this
        _ = (Hσ.toFun f x)
                * (Complex.exp ((σ + Complex.I * (τ : ℝ)) * t) * (1 / (x : ℂ))) := h_step
        _ = (Hσ.toFun f x)
                * (Complex.exp ((σ + Complex.I * (τ : ℝ)) * t)
                    * Complex.exp (-(t : ℂ))) := by simp [hx_inv]
        _ = (Hσ.toFun f x) * Complex.exp (((σ + Complex.I * (τ : ℝ)) - 1) * t) := by
              simp [h_exp]
    -- Identify the result with `(f x) * x^(σ + iτ - 1)` via `x = exp t`.
    -- This step uses the complex-power identity `x^w = exp(w * log x)` for x>0.
    have h_pow :
        (Hσ.toFun f x) * Complex.exp (((σ + Complex.I * (τ : ℝ)) - 1) * t)
          = (f : ℝ → ℂ) x * x ^ (σ + I * τ - 1) := by
      -- Identify `exp(((σ + iτ) - 1) * t)` with `(x : ℂ)^((σ + iτ) - 1)` using `t = log x`.
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hxpos)
      have hlogC : Complex.log (x : ℂ) = (t : ℂ) := by
        -- log of positive real equals real log
        have : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
          (Complex.ofReal_log (le_of_lt hxpos)).symm
        simpa [ht] using this
      have hcpow :
          (x : ℂ) ^ ((σ + Complex.I * (τ : ℝ)) - 1)
            = Complex.exp ((((σ + Complex.I * (τ : ℝ)) - 1) : ℂ)
                * Complex.log (x : ℂ)) := by
        -- cpow in terms of exp and log for nonzero base
        rw [Complex.cpow_def]
        simp only [if_neg hx0]
        congr 1
        ring
      have h_exp_eq :
          Complex.exp (((σ + Complex.I * (τ : ℝ)) - 1) * (t : ℂ))
            = Complex.exp ((((σ + Complex.I * (τ : ℝ)) - 1) : ℂ)
                * Complex.log (x : ℂ)) := by
        -- Replace `log (x)` by `t`
        rw [hlogC]
      -- Conclude by substituting back and simplifying the front factor
      have h_exp_to_pow : Complex.exp (((σ + Complex.I * (τ : ℝ)) - 1) * t)
            = (x : ℂ) ^ ((σ + Complex.I * (τ : ℝ)) - 1) := by
        -- coerce `t` to `ℂ` in the exponent equality
        have h_cast : Complex.exp (((σ + Complex.I * (τ : ℝ)) - 1) * t) =
                      Complex.exp (((σ + Complex.I * (τ : ℝ)) - 1) * (t : ℂ)) := by
          rfl
        rw [h_cast, h_exp_eq, hcpow]
      -- Replace `Hσ.toFun f x` with `(f : ℝ → ℂ) x` definitionally
      rw [h_exp_to_pow]
      rfl
    -- Chain the equalities to conclude the a.e. identity at `x`.
    have :
        ((LogPull σ f (Real.log x) * Complex.exp ((1 / 2 : ℝ) * Real.log x))
            * Complex.exp (Complex.I * (τ : ℝ) * Real.log x)) * (1 / (x : ℂ))
          = (f : ℝ → ℂ) x * x ^ (σ + I * τ - 1) := by
      -- Replace `Real.log x` by `t` and use the previous steps.
      simpa [ht] using (h_sigma_tau_one.trans h_pow)
    -- Flip sides to match the target orientation.
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using this.symm
  -- It suffices to prove integrability of the RHS.
  -- Prove integrability for the RHS, then transfer along `h_ae_change`.
  have h_rhs_int :
      Integrable
        (fun x : ℝ =>
          ((LogPull σ f (Real.log x) * Complex.exp ((1 / 2 : ℝ) * Real.log x))
            * Complex.exp (Complex.I * (τ : ℝ) * Real.log x)) * (1 / (x : ℂ)))
        (volume.restrict (Set.Ioi 0)) := by
    classical
    -- Abbreviations for clarity
    set g : ℝ → ℂ := fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t) with hg_def
    set J : ℝ → ℂ :=
      fun x => g (Real.log x) * Complex.exp (Complex.I * (τ : ℝ) * Real.log x) with hJ_def

    -- Step 1: `g` is integrable on ℝ by hypothesis; multiplying by a unimodular
    -- factor preserves integrability.
    have hg_int : Integrable g := by simpa [hg_def] using hf_int
    have hgτ_int : Integrable (fun t => g t * Complex.exp (Complex.I * (τ : ℝ) * t)) := by
      -- Define the phase factor and record measurability
      let phase : ℝ → ℂ := fun t => Complex.exp (Complex.I * (τ : ℝ) * (t : ℂ))
      have hphase_cont : Continuous phase := by
        -- phase t = exp(I * ((τ : ℂ) * (t : ℂ)))
        have h1 : Continuous fun t : ℝ => (t : ℂ) := Complex.continuous_ofReal
        have h2 : Continuous fun t : ℝ => (τ : ℂ) * (t : ℂ) := continuous_const.mul h1
        have h3 : Continuous fun t : ℝ => Complex.I * ((τ : ℂ) * (t : ℂ)) :=
          continuous_const.mul h2
        simpa [phase, mul_assoc] using Complex.continuous_exp.comp h3
      have hphase_aesm : AEStronglyMeasurable phase (volume : Measure ℝ) :=
        hphase_cont.measurable.aestronglyMeasurable
      -- Measurability of the product
      have h_prod_aesm :
          AEStronglyMeasurable (fun t : ℝ => g t * phase t) (volume : Measure ℝ) := by
        apply AEStronglyMeasurable.mul
        · exact (hg_int.aestronglyMeasurable)
        · exact hphase_aesm
      -- Norm of the phase is 1; use this to inherit integrability from g
      have h_norm_eq : (fun t : ℝ => ‖g t * phase t‖) = fun t => ‖g t‖ := by
        funext t
        have : ‖phase t‖ = (1 : ℝ) := by
          -- Use the helper lemma from ZakMellin
          simpa [phase] using phase_abs_one (ξ := τ) (t := t)
        simp [phase, norm_mul, this]
      have h_norm_int : Integrable (fun t : ℝ => ‖g t * phase t‖) := by
        rw [h_norm_eq]
        exact hg_int.norm
      -- Package into Bochner integrability
      have h_hasFinInt : HasFiniteIntegral
          (fun t => g t * Complex.exp (Complex.I * (τ : ℝ) * t)) := by
        have h_norm_prod : ∀ a, ‖g a * Complex.exp (Complex.I * (τ : ℝ) * a)‖ = ‖g a‖ := by
          intro a
          have h_norm_phase : ‖Complex.exp (Complex.I * (τ : ℝ) * a)‖ = 1 := by
            simpa [phase] using phase_abs_one (ξ := τ) (t := a)
          simp [norm_mul, h_norm_phase]
        rw [HasFiniteIntegral]
        calc ∫⁻ a, ‖g a * Complex.exp (Complex.I * (τ : ℝ) * a)‖₊
            = ∫⁻ a, ‖g a‖₊ := by
                congr 1
                funext a
                rw [nnnorm_mul]
                have h_nnnorm_phase : ‖Complex.exp (Complex.I * (τ : ℝ) * a)‖₊ = 1 := by
                  ext
                  simpa [phase] using phase_abs_one (ξ := τ) (t := a)
                simp [h_nnnorm_phase]
          _ < ⊤ := hg_int.hasFiniteIntegral
      exact ⟨h_prod_aesm, h_hasFinInt⟩

    -- Step 2: Transport integrability from ℝ to (0,∞) via the pushforward of mulHaar.
    -- We first observe that under `log`, mulHaar pushes to a multiple of Lebesgue.
    obtain ⟨c, hc0, hcTop, h_map⟩ := mulHaar_pushforward_log

    -- From `hgτ_int` and the pushforward identity, deduce that
    -- `J` is integrable with respect to `mulHaar` on (0,∞).
    have hJ_mulHaar_int : Integrable J mulHaar := by
      -- Strategy: view `J = (t ↦ g t * exp(i τ t)) ∘ log` and use
      -- `mulHaar_pushforward_log` to transfer integrability from Lebesgue to mulHaar.
      -- 1) a.e.-strong measurability of `J` (composition of measurable pieces)
      have hJ_aesm : AEStronglyMeasurable J mulHaar := by
        -- Measurability of `g`
        have h_g_meas : Measurable g := by
          -- g t = LogPull σ f t * exp((1/2) t)
          have h_exp_meas : Measurable (fun t : ℝ =>
              Complex.exp ((1 / 2 : ℝ) * (t : ℝ))) := by
            have hlin : Measurable fun t : ℝ => ((1 / 2 : ℝ) : ℂ) * (t : ℂ) := by
              refine measurable_const.mul ?_
              exact Complex.measurable_ofReal
            -- apply measurability of exp
            exact Complex.measurable_exp.comp hlin
          -- LogPull measurability is available
          have h_logpull_meas : Measurable (LogPull σ f) := LogPull_measurable σ f
          -- Product of measurable functions is measurable
          simpa [hg_def] using h_logpull_meas.mul h_exp_meas
        -- Measurability of the phase factor `t ↦ exp(i τ t)`
        let phase : ℝ → ℂ := fun t => Complex.exp (Complex.I * (τ : ℝ) * (t : ℂ))
        have h_phase_meas : Measurable phase := by
          have h1 : Measurable fun t : ℝ => (t : ℂ) := Complex.measurable_ofReal
          have h3 : Measurable fun t : ℝ => Complex.I * (τ : ℂ) * (t : ℂ) := by
            refine measurable_const.mul ?_
            exact h1
          exact Complex.measurable_exp.comp h3
        -- Compose both with `log`, which is measurable
        have h_log_meas : Measurable Real.log := Real.measurable_log
        have h_comp_g : Measurable (fun x : ℝ => g (Real.log x)) := h_g_meas.comp h_log_meas
        have h_comp_phase : Measurable (fun x : ℝ => phase (Real.log x)) :=
          h_phase_meas.comp h_log_meas
        -- Product of the two composed pieces gives measurability of `J`
        have hJ_meas : Measurable J := by
          simpa [J, hJ_def] using h_comp_g.mul h_comp_phase
        -- Convert to a.e.-strong measurability for the specific measure
        exact hJ_meas.aestronglyMeasurable
      -- 2) integrability of the norm via change of variables using `h_map` and `hgτ_int`
      have hJ_norm : Integrable (fun x => ‖J x‖) mulHaar := by
        -- Step A: simplify the norm using |exp(i τ log x)| = 1 (mulHaar-a.e. x>0)
        have h_pos : ∀ᵐ x ∂ mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
          simpa [mulHaar] using
            (ae_restrict_mem (μ := volume.withDensity fun x : ℝ => ENNReal.ofReal (1 / x))
              (s := Set.Ioi (0 : ℝ)))
        have h_norm_ae :
            (fun x : ℝ => ‖J x‖) =ᵐ[mulHaar]
            (fun x : ℝ => ‖g (Real.log x)‖) := by
          refine h_pos.mono ?_
          intro x hx
          have hphase : ‖Complex.exp (Complex.I * (τ : ℝ) * Real.log x)‖ = 1 := by
            simpa using phase_abs_one (ξ := τ) (t := Real.log x)
          have hJ : J x = g (Real.log x) * Complex.exp (Complex.I * (τ : ℝ) * Real.log x) := by
            simp [J, hJ_def]
          simp [hJ, norm_mul, hphase]
        -- Step B: use the pushforward identity of mulHaar under log
        -- to transfer integrability of `t ↦ ‖g t‖` (which holds by `hg_int.norm`).
        have h_int_map : Integrable (fun t : ℝ => ‖g t‖)
            (Measure.map Real.log mulHaar) := by
          -- Rewrite the pushforward as a scaled Lebesgue measure and lift integrability.
          have h_base : Integrable (fun t : ℝ => ‖g t‖) volume := hg_int.norm
          -- Scaling by a finite constant preserves integrability.
          have h_smul : Integrable (fun t : ℝ => ‖g t‖) (c • volume) := by
            -- a.e.-strong measurability under the scaled measure
            have h_g_meas : Measurable g := by
              -- g t = LogPull σ f t * exp((1/2) t)
              have h_exp_meas : Measurable (fun t : ℝ =>
                  Complex.exp ((1 / 2 : ℝ) * (t : ℝ))) := by
                have hlin : Measurable fun t : ℝ => ((1 / 2 : ℝ) : ℂ) * (t : ℂ) := by
                  refine measurable_const.mul ?_
                  exact Complex.measurable_ofReal
                -- apply measurability of exp
                exact Complex.measurable_exp.comp hlin
              have h_logpull_meas : Measurable (LogPull σ f) := LogPull_measurable σ f
              simpa [hg_def] using h_logpull_meas.mul h_exp_meas
            have h_meas_norm : AEStronglyMeasurable (fun t : ℝ => ‖g t‖) (c • volume) :=
              (h_g_meas.norm).aestronglyMeasurable
            -- finiteness of the integral under the scaled measure via lintegral_smul_measure
            have h_base_fin :
                (∫⁻ t, ‖(fun t : ℝ => ‖g t‖) t‖₊ ∂volume) < ∞ := by
              have h_int : HasFiniteIntegral (fun t : ℝ => ‖g t‖) volume := h_base.2
              simp only [HasFiniteIntegral] at h_int
              simpa [nnnorm_norm] using h_int
            have h_eval :
                (∫⁻ t, ‖(fun t : ℝ => ‖g t‖) t‖₊ ∂(c • volume))
                  = c * ∫⁻ t, ‖(fun t : ℝ => ‖g t‖) t‖₊ ∂volume := by
              simp [lintegral_smul_measure, mul_comm, mul_left_comm, mul_assoc]
            have h_c_lt_top : c < ∞ := lt_of_le_of_ne le_top hcTop
            have h_fin :
                (∫⁻ t, ‖(fun t : ℝ => ‖g t‖) t‖₊ ∂(c • volume)) < ∞ := by
              -- use monotonicity of < ∞ under multiplication by finite c
              simpa [h_eval] using ENNReal.mul_lt_top h_c_lt_top h_base_fin
            exact ⟨h_meas_norm, by simpa [HasFiniteIntegral] using h_fin⟩
          have h_mulHaar_eq : mulHaar = mulHaar.restrict (Set.Ioi 0) := by
            ext s hs
            simp [mulHaar, Measure.restrict_apply hs]
          rw [h_mulHaar_eq, h_map]
          exact h_smul
        -- Convert from the map-measure statement back to mulHaar via composition f ∘ log
        have h_back : Integrable (fun x : ℝ => ‖g (Real.log x)‖) mulHaar := by
          -- a.e.-strong measurability of the composed norm
          have h_g_meas : Measurable g := by
            have h_exp_meas : Measurable (fun t : ℝ => Complex.exp ((1 / 2 : ℝ) * (t : ℝ))) := by
              have hlin : Measurable fun t : ℝ => ((1 / 2 : ℝ) : ℂ) * (t : ℂ) := by
                refine measurable_const.mul ?_
                exact Complex.measurable_ofReal
              exact Complex.measurable_exp.comp hlin
            have h_logpull_meas : Measurable (LogPull σ f) := LogPull_measurable σ f
            simpa [hg_def] using h_logpull_meas.mul h_exp_meas
          have h_comp_meas : Measurable (fun x : ℝ => g (Real.log x)) :=
            h_g_meas.comp Real.measurable_log
          have h_back_aesm : AEStronglyMeasurable (fun x : ℝ => ‖g (Real.log x)‖) mulHaar :=
            (h_comp_meas.norm).aestronglyMeasurable
          -- finiteness of the integral via `lintegral_map'` and `h_int_map.hasFiniteIntegral`
          have hlog_aemeas : AEMeasurable Real.log mulHaar :=
            Real.measurable_log.aemeasurable
          have hA : AEMeasurable (fun t : ℝ => ENNReal.ofReal (‖g t‖))
              (Measure.map Real.log mulHaar) :=
            (h_int_map.aestronglyMeasurable.aemeasurable).ennreal_ofReal
          have h_map_eq :=
            lintegral_map' (μ := mulHaar)
              (f := fun t : ℝ => ENNReal.ofReal (‖g t‖))
              (g := Real.log) hA hlog_aemeas
          -- The RHS is finite by `h_int_map`.
          have h_rhs_fin :
              (∫⁻ t, ENNReal.ofReal (‖g t‖) ∂(Measure.map Real.log mulHaar)) < ∞ := by
            simpa [HasFiniteIntegral] using h_int_map.hasFiniteIntegral
          -- Transport finiteness to the LHS using `h_map_eq`.
          have h_lhs_fin :
              (∫⁻ x, ENNReal.ofReal (‖g (Real.log x)‖) ∂mulHaar) < ∞ := by
            rw [← h_map_eq]
            simp only
            exact h_rhs_fin
          -- Package as Bochner integrability
          exact ⟨h_back_aesm, by simpa [HasFiniteIntegral] using h_lhs_fin⟩
        -- Finish by congruence of the integrands a.e.
        exact (Integrable.congr h_back h_norm_ae.symm)
      have hJ_hasFin : HasFiniteIntegral J mulHaar := by
        rw [HasFiniteIntegral]
        calc (∫⁻ a, ‖J a‖ₑ ∂mulHaar)
            = (∫⁻ a, (‖J a‖₊ : ℝ≥0∞) ∂mulHaar) := by rfl
          _ = (∫⁻ a, ‖(fun x => ‖J x‖) a‖₊ ∂mulHaar) := by
                congr 1; ext a
                simp [nnnorm_norm]
          _ < ∞ := hJ_norm.hasFiniteIntegral
      exact ⟨hJ_aesm, hJ_hasFin⟩

    -- Step 3: Convert integrability under `mulHaar` to integrability under
    -- `volume.restrict (Ioi 0)` with the density `1/x`.
    have h_eq_meas : mulHaar = volume.withDensity (fun x => ENNReal.ofReal (1 / x)) :=
      mulHaar_eq_volume_div_x

    -- Under withDensity, integrability of `J` corresponds to integrability of
    -- `J * (1/x)` under Lebesgue on `(0,∞)`; match our target integrand via `hJ_def`.
    -- Final measure-conversion step left as a placeholder.
    have h_target :
        Integrable (fun x : ℝ => J x * (1 / (x : ℂ))) (volume.restrict (Set.Ioi 0)) := by
      -- Convert using `h_eq_meas` and the standard `withDensity` characterization.
      -- Also use that the density vanishes off `(0,∞)` so restriction is harmless.
      classical
      -- a.e.-strong measurability of the product `J x * (1/x)` on `(0,∞)`
      -- Measurability of `J` (reconstruct as in hJ_aesm)
      have h_g_meas : Measurable g := by
        have h_exp_meas : Measurable (fun t : ℝ => Complex.exp ((1 / 2 : ℝ) * (t : ℝ))) := by
          have hlin : Measurable fun t : ℝ => ((1 / 2 : ℝ) : ℂ) * (t : ℂ) := by
            refine measurable_const.mul ?_
            exact Complex.measurable_ofReal
          exact Complex.measurable_exp.comp hlin
        have h_logpull_meas : Measurable (LogPull σ f) := LogPull_measurable σ f
        simpa [hg_def] using h_logpull_meas.mul h_exp_meas
      have h_phase_meas : Measurable
          (fun t : ℝ => Complex.exp (Complex.I * (τ : ℝ) * (t : ℂ))) := by
        have h1 : Measurable fun t : ℝ => (t : ℂ) := Complex.measurable_ofReal
        have h2 : Measurable fun t : ℝ => Complex.I * (τ : ℂ) * (t : ℂ) := by
          refine measurable_const.mul ?_
          exact h1
        show Measurable fun t : ℝ => Complex.exp (Complex.I * (τ : ℝ) * (t : ℂ))
        simpa [mul_assoc] using Complex.measurable_exp.comp h2
      have hJ_meas : Measurable J := by
        have : J = fun x => g (Real.log x) * Complex.exp (Complex.I * (τ : ℝ) * Real.log x) := by
          funext x; simp [J, hJ_def]
        simpa [this] using (h_g_meas.comp Real.measurable_log).mul
          (h_phase_meas.comp Real.measurable_log)
      have h_inv_meas : Measurable (fun x : ℝ => (1 / (x : ℂ))) := by
        -- measurability via ofReal ∘ inv
        have h_invR : Measurable fun x : ℝ => (1 / x : ℝ) := by
          simpa [one_div] using measurable_inv
        show Measurable fun x : ℝ => (1 / (x : ℂ))
        convert Complex.measurable_ofReal.comp h_invR using 1
        ext x
        simp [Function.comp_apply]
      have h_prod_aesm : AEStronglyMeasurable
          (fun x : ℝ => J x * (1 / (x : ℂ))) (volume.restrict (Set.Ioi 0)) := by
        exact (hJ_meas.mul h_inv_meas).aestronglyMeasurable

      -- Finite integral: compare the lintegral of the norm with the withDensity expression
      -- First, rewrite the norm pointwise on `(0,∞)`.
      have h_norm_ae :
          (fun x : ℝ => (‖J x * (1 / (x : ℂ))‖₊ : ℝ≥0∞))
            =ᵐ[volume.restrict (Set.Ioi 0)]
          (fun x : ℝ => (‖J x‖₊ : ℝ≥0∞) * ENNReal.ofReal (1 / x)) := by
        refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
        refine Filter.Eventually.of_forall ?_
        intro x hx
        have hxpos : 0 < x := hx
        have h_norm_inv : ‖(1 / (x : ℂ))‖ = (1 / x) := by
          -- For x>0, the norm equals the absolute value, which is 1/x
          simp only [one_div]
          rw [norm_inv, Complex.norm_real]
          simp [abs_of_pos hxpos]
        -- move to ℝ≥0∞ via `coe_nnnorm_mul` and evaluate the scalar's norm
        have hcoe :
            ((‖J x * (1 / (x : ℂ))‖₊ : ℝ≥0∞))
              = ((‖J x‖₊ : ℝ≥0∞) * (‖(1 / (x : ℂ))‖₊ : ℝ≥0∞)) := by
          simp
        -- Convert the scalar nnnorm to ENNReal.ofReal (1/x)
        have h_scalar : (‖(1 / (x : ℂ))‖₊ : ℝ≥0∞) = ENNReal.ofReal (1 / x) := by
          -- coerce the equality of real norms to ENNReal via ofReal
          have h_nonneg : 0 ≤ 1 / x := by
            rw [one_div]
            exact inv_nonneg.mpr (le_of_lt hxpos)
          rw [ENNReal.ofReal]
          congr 1
          rw [Real.toNNReal_of_nonneg h_nonneg]
          ext
          simp [h_norm_inv, le_of_lt hxpos]
        simp only
        rw [hcoe, h_scalar]

      -- Now compare lintegrals using `lintegral_mulHaar_expand` with g := ofReal ‖J x‖.
      have hJ_fin : HasFiniteIntegral J mulHaar := hJ_mulHaar_int.hasFiniteIntegral
      have h_rhs_fin :
          (∫⁻ x in Set.Ioi 0, (ENNReal.ofReal (‖J x‖)) * ENNReal.ofReal (1 / x) ∂volume) < ∞ := by
        -- express via the mulHaar expansion
        -- Measurability of the integrand on the right
        have h_meas_en : Measurable (fun x : ℝ => ENNReal.ofReal (‖J x‖)) := by
          have h_norm_meas : Measurable (fun x => ‖J x‖) :=
            (hJ_meas.norm)
          exact Measurable.ennreal_ofReal h_norm_meas
        -- Relate to lintegral over mulHaar of ENNReal.ofReal ‖J x‖
        have h_eq := lintegral_mulHaar_expand
          (g := fun x => ENNReal.ofReal (‖J x‖)) h_meas_en
        -- Finite because J integrable under mulHaar
        have h_left_fin :
            (∫⁻ x, ENNReal.ofReal (‖J x‖) ∂mulHaar) < ∞ := by
          simpa [HasFiniteIntegral] using hJ_fin
        -- conclude finiteness of the RHS using equality h_eq
        rw [← h_eq]
        exact h_left_fin

      -- Bridge from ENNReal.ofReal ‖J x‖ to nnnorm using `h_norm_ae`.
      have h_fin' :
          (∫⁻ x in Set.Ioi 0, (‖J x * (1 / (x : ℂ))‖₊ : ℝ≥0∞) ∂volume) < ∞ := by
        -- use AE equality of integrands
        have := h_rhs_fin
        -- Convert ENNReal.ofReal ‖J x‖ to ↑‖J x‖₊
        have h_ofReal_eq : ∀ x, ENNReal.ofReal (‖J x‖) = (‖J x‖₊ : ℝ≥0∞) := by
          intro x
          rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (norm_nonneg _)]
          rfl
        have this' : (∫⁻ x in Set.Ioi 0, (‖J x‖₊ : ℝ≥0∞) * ENNReal.ofReal (1 / x) ∂volume) < ∞ := by
          convert this using 2
          ext x
          rw [← h_ofReal_eq]
        -- Convert the RHS integrand to match using `h_norm_ae` and product commutativity
        -- First, rewrite target using `lintegral_congr_ae`.
        have h_congr :=
          lintegral_congr_ae (μ := volume.restrict (Set.Ioi 0)) h_norm_ae
        -- Thus finiteness transfers across equal integrands a.e.
        rw [h_congr]
        exact this'

      -- Package as Bochner integrability on the restricted measure.
      refine ⟨h_prod_aesm, ?_⟩
      -- Interpret the finiteness in terms of `HasFiniteIntegral`.
      simpa [HasFiniteIntegral]
        using h_fin'

    -- Rewrite back in terms of the original expression and conclude.
    simpa [J, hJ_def, hg_def, mul_left_comm, mul_comm, mul_assoc]
      using h_target
  exact Integrable.congr h_rhs_int h_ae_change.symm

end ParsevalEquivalence

end Frourio
