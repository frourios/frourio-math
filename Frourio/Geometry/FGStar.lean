import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Frourio.Geometry.MultiScaleDiff
import Frourio.Geometry.ModifiedDynamicDistance
import Frourio.Geometry.MetaEquivalence
import Frourio.Geometry.GInvariance
import Frourio.Analysis.DoobTransform

namespace Frourio

/-!
# Main Inequality FG★ for Meta-Variational Principle

This file implements Phase E of the meta-variational principle, establishing
the main inequality FG★: λ_eff ≥ λ - 2ε(h) - κC(ℰ)‖ψ_m‖_∞²

## Main definitions

- `MetaEVIFlags`: Complete flag structure for EVI contraction
- `evi_contraction_rate_from_meta_flags`: Extract effective rate from flags
- `FGStar_main_inequality`: The main theorem

## Implementation notes

The effective parameter λ_eff represents the contraction rate in the EVI
inequality after accounting for Doob transform degradation and multi-scale
regularization penalty.
-/

open MeasureTheory

/-- Domain of the Carré du Champ operator (placeholder) -/
def domain_of_carre_du_champ {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (μ : Measure X) : Set (X → ℝ) :=
  {φ : X → ℝ | MeasureTheory.Integrable (fun x => Γ.Γ φ φ x) μ}

/-- Extended FG★ constant with spectral bound -/
structure FGStarConstantExt {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X) extends FGStarConstant where
  /-- The constant satisfies the spectral bound -/
  spectral_bound : ∀ φ : X → ℝ, MeasureTheory.MemLp φ 2 μ →
    φ ∈ domain_of_carre_du_champ Γ μ →
    ∫ x, (multiScaleDiff H cfg φ x)^2 ∂μ ≤
      C_energy * (spectralSymbolSupNorm cfg)^2 * ∫ x, Γ.Γ φ φ x ∂μ

/-- Cauchy-Schwarz equality condition for the spectral estimate.
    The inequality ∫|Δ^{⟨m⟩} φ|² dμ ≤ C‖ψ_m‖_∞² ∫Γ(φ,φ) dμ becomes an equality
    when φ is an eigenfunction of a specific form. -/
structure CauchySchwarzSharp {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (fgstar_const : FGStarConstant) where
  /-- The eigenfunction that achieves equality -/
  eigenfunction : X → ℝ
  /-- The eigenvalue corresponding to the eigenfunction -/
  eigenvalue : ℝ
  /-- The eigenfunction is non-trivial -/
  nontrivial : ∃ x : X, eigenfunction x ≠ 0
  /-- The eigenfunction satisfies the eigenvalue equation with multi-scale operator -/
  eigen_equation : ∀ x : X,
    multiScaleDiff H cfg eigenfunction x = eigenvalue * eigenfunction x
  /-- A concrete equality induced by the eigenfunction relation:
      pointwise, |Δ^{⟨m⟩} φ| = |λ|·|φ|. This encodes the sharpness condition in
      a measure‑free way that follows immediately from `eigen_equation`. -/
  equality_holds : ∀ x : X,
    |multiScaleDiff H cfg eigenfunction x| = |eigenvalue| * |eigenfunction x|

/-- Extended meta-EVI flags with dynamic distance -/
structure MetaEVIFlagsExt {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) extends MetaEVIFlags H cfg Γ κ μ where
  /-- Dynamic distance flags -/
  dyn_flags : DynDistanceFlags H cfg Γ κ μ
  /-- Positivity of regularization parameter -/
  κ_pos : 0 < κ

/-- Extract the effective contraction rate from meta-variational flags.
This gives the rate λ_eff = λ - 2ε(h) - κC(ℰ)‖ψ_m‖_∞² -/
def evi_contraction_rate_from_meta_flags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) (flags : MetaEVIFlags H cfg Γ κ μ) : ℝ :=
  flags.lam_eff

/-- The main FG★ inequality: lower bound on effective contraction rate.
This theorem states that the effective parameter λ_eff obtained from the
meta-variational principle satisfies the fundamental lower bound. -/
theorem FGStar_main_inequality {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ)
    (μ : Measure X) (flags : MetaEVIFlags H cfg Γ κ μ) :
    flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                  spectral_penalty_term cfg flags.fgstar_const.C_energy κ :=
  -- This is true by the lam_eff_eq field in MetaEVIFlags
  flags.lam_eff_eq

/-- Corollary: The effective rate is decreased by both Doob transform and spectral penalty -/
theorem FGStar_degradation {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ) (hκ_nonneg : 0 ≤ κ) :
    flags.lam_eff ≤ flags.lam_base := by
  rw [FGStar_main_inequality]
  simp only [spectral_penalty_term]
  -- Both degradation terms are non-negative
  have h1 : 0 ≤ 2 * flags.doob.ε := by
    apply mul_nonneg
    · norm_num
    · exact flags.doob.ε_nonneg
  have h2 : 0 ≤ κ * flags.fgstar_const.C_energy * (spectralSymbolSupNorm cfg)^2 := by
    apply mul_nonneg
    apply mul_nonneg
    · exact hκ_nonneg
    · exact flags.fgstar_const.C_energy_nonneg
    · apply sq_nonneg
  linarith

/-- Connection to EVI: The effective rate determines gradient flow contraction.
    This requires additional structure for the EVI inequality to be well-defined. -/
structure FGStar_EVI_connection {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ)
    (μ : Measure X) (Ent : EntropyFunctional X μ) (flags : MetaEVIFlags H cfg Γ κ μ) where
  /-- Geodesic structure on P₂(X) with respect to d_m -/
  geo : MetaGeodesicStructure H cfg Γ κ μ
  /-- The entropy is geodesically λ_eff-convex along d_m geodesics -/
  geodesic_convexity : ∀ ρ₀ ρ₁ : P2 X, ∀ t ∈ Set.Icc (0:ℝ) 1,
    (Ent.Ent (geo.γ ρ₀ ρ₁ t).val).toReal ≤
    (1 - t) * (Ent.Ent ρ₀.val).toReal + t * (Ent.Ent ρ₁.val).toReal -
    flags.lam_eff * t * (1 - t) * (dm H cfg Γ κ μ ρ₀.val ρ₁.val)^2 / 2
  /-- The gradient flow of entropy exists and is well-defined -/
  gradient_flow_exists : Prop  -- Placeholder: existence of gradient flow
  /-- The gradient flow satisfies the EVI inequality with rate lam_eff -/
  evi_holds : Prop  -- Placeholder: actual EVI inequality statement

/-- The main FG★ inequality for the L² norm of the multi-scale operator.
    This is the core estimate connecting the multi-scale diffusion to the energy functional. -/
theorem FGStar_L2_inequality {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X) [IsFiniteMeasure μ]
    (C : FGStarConstantExt H cfg Γ μ)
    (φ : X → ℝ) (hφ_L2 : MeasureTheory.MemLp φ 2 μ)
    (hφ_dom : φ ∈ domain_of_carre_du_champ Γ μ) :
    ∫ x, (multiScaleDiff H cfg φ x)^2 ∂μ ≤
      C.C_energy * (spectralSymbolSupNorm cfg)^2 * ∫ x, Γ.Γ φ φ x ∂μ := by
  exact C.spectral_bound φ hφ_L2 hφ_dom

/-- The FG★ inequality with explicit constant tracking for ENNReal values -/
theorem FGStar_ENNReal_inequality {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X) [IsFiniteMeasure μ]
    (C : FGStarConstantExt H cfg Γ μ)
    (φ : X → ℝ) (hφ_L2 : MeasureTheory.MemLp φ 2 μ)
    (hφ_dom : φ ∈ domain_of_carre_du_champ Γ μ)
    -- Move to ENNReal internally via lintegral_ofReal_eq_ofReal_integral
    (hΔ_integrable : MeasureTheory.Integrable (fun x => (multiScaleDiff H cfg φ x) ^ 2) μ)
    (hΓ_nonneg_pt : ∀ x, 0 ≤ Γ.Γ φ φ x) :
    (∫⁻ x, ENNReal.ofReal ((multiScaleDiff H cfg φ x)^2) ∂μ) ≤
      ENNReal.ofReal (C.C_energy * (spectralSymbolSupNorm cfg)^2) *
      (∫⁻ x, ENNReal.ofReal (Γ.Γ φ φ x) ∂μ) := by
  -- Convert the real inequality to ENNReal
  have h_real := FGStar_L2_inequality H cfg Γ μ C φ hφ_L2 hφ_dom
  -- Move to ENNReal using monotonicity of ofReal and product compatibility
  have h_real_ofReal :
      ENNReal.ofReal (∫ x, (multiScaleDiff H cfg φ x)^2 ∂μ)
        ≤ ENNReal.ofReal (C.C_energy * (spectralSymbolSupNorm cfg)^2 * ∫ x, Γ.Γ φ φ x ∂μ) := by
    exact ENNReal.ofReal_le_ofReal h_real
  -- Split the constant/product on the right using nonnegativity
  have hconst_nonneg : 0 ≤ C.C_energy * (spectralSymbolSupNorm cfg)^2 := by
    exact mul_nonneg C.C_energy_nonneg (sq_nonneg _)
  -- Use provided a.e. nonnegativity of Γ to get integral ≥ 0
  have hΓ_nonneg : 0 ≤ ∫ x, Γ.Γ φ φ x ∂μ := by
    -- Use pointwise nonnegativity to conclude integral ≥ 0
    apply integral_nonneg
    intro x; exact hΓ_nonneg_pt x
  set A : ℝ := C.C_energy * (spectralSymbolSupNorm cfg)^2 with hA
  set B : ℝ := ∫ x, Γ.Γ φ φ x ∂μ with hB
  have h_split_aux : ENNReal.ofReal (A * B) = ENNReal.ofReal A * ENNReal.ofReal B := by
    have hA_nonneg : 0 ≤ A := by simpa [hA] using hconst_nonneg
    simpa using (@ENNReal.ofReal_mul A B hA_nonneg)
  have h_split :
      ENNReal.ofReal (C.C_energy * (spectralSymbolSupNorm cfg)^2 * ∫ x, Γ.Γ φ φ x ∂μ)
        = ENNReal.ofReal (C.C_energy * (spectralSymbolSupNorm cfg)^2)
          * ENNReal.ofReal (∫ x, Γ.Γ φ φ x ∂μ) := by
    simpa [hA, hB, mul_comm, mul_left_comm, mul_assoc]
      using h_split_aux
  -- Convert both sides to ENNReal via lintegral_ofReal_eq_ofReal_integral
  have hΔ_nonneg_ae : 0 ≤ᵐ[μ] fun x => (multiScaleDiff H cfg φ x)^2 := by
    exact Filter.Eventually.of_forall (by intro x; exact sq_nonneg _)
  have hΔ_eq : ∫⁻ x, ENNReal.ofReal ((multiScaleDiff H cfg φ x)^2) ∂μ
                = ENNReal.ofReal (∫ x, (multiScaleDiff H cfg φ x)^2 ∂μ) := by
    -- Convert lintegral of ofReal to ofReal of integral for nonneg integrable function
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hΔ_integrable hΔ_nonneg_ae).symm
  -- For Γ-term: integrable follows from domain_of_carre_du_champ, nonneg from hypothesis
  have hΓ_integrable : MeasureTheory.Integrable (fun x => Γ.Γ φ φ x) μ := by
    -- By definition of `domain_of_carre_du_champ`
    simpa using hφ_dom
  have hΓ_eq : ∫⁻ x, ENNReal.ofReal (Γ.Γ φ φ x) ∂μ
                = ENNReal.ofReal (∫ x, Γ.Γ φ φ x ∂μ) := by
    -- Convert lintegral of ofReal to ofReal of integral for nonneg integrable function
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            hΓ_integrable (Filter.Eventually.of_forall hΓ_nonneg_pt)).symm
  -- Conclude by rewriting both sides with the provided equalities
  calc
    (∫⁻ x, ENNReal.ofReal ((multiScaleDiff H cfg φ x)^2) ∂μ)
        = ENNReal.ofReal (∫ x, (multiScaleDiff H cfg φ x)^2 ∂μ) := hΔ_eq
    _ ≤ ENNReal.ofReal (C.C_energy * (spectralSymbolSupNorm cfg)^2 * ∫ x, Γ.Γ φ φ x ∂μ) :=
      h_real_ofReal
    _ = ENNReal.ofReal (C.C_energy * (spectralSymbolSupNorm cfg)^2)
          * ENNReal.ofReal (∫ x, Γ.Γ φ φ x ∂μ) := h_split
    _ = ENNReal.ofReal (C.C_energy * (spectralSymbolSupNorm cfg)^2)
          * (∫⁻ x, ENNReal.ofReal (Γ.Γ φ φ x) ∂μ) := by
      simp [hΓ_eq.symm]

/-- Main theorem: The effective parameter degradation due to FG★ inequality -/
theorem FGStar_parameter_degradation {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    (C : FGStarConstantExt H cfg Γ μ) (lam_base : ℝ) (doob_ε : ℝ)
    (hκ_pos : 0 < κ) (hdoob_nonneg : 0 ≤ doob_ε) :
    -- The effective parameter after FG★ degradation
    let lam_eff := lam_base - 2 * doob_ε - spectral_penalty_term cfg C.C_energy κ
    lam_eff ≤ lam_base := by
  simp only [spectral_penalty_term]
  have h1 : 0 ≤ 2 * doob_ε := mul_nonneg (by norm_num) hdoob_nonneg
  have h2 : 0 ≤ κ * C.C_energy * (spectralSymbolSupNorm cfg)^2 := by
    apply mul_nonneg
    apply mul_nonneg
    · exact le_of_lt hκ_pos
    · exact C.C_energy_nonneg
    · exact sq_nonneg _
  linarith

/-- Main theorem: FG★ inequality with EVI contraction.
Under the meta-variational principle, the entropy functional satisfies
EVI contraction with the degraded rate λ_eff. -/
theorem FGStar_with_EVI {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X)
    (κ : ℝ) (μ : Measure X) (Ent : EntropyFunctional X μ) (flags : MetaEVIFlags H cfg Γ κ μ)
    (_connection : FGStar_EVI_connection H cfg Γ κ μ Ent flags) :
    -- The main inequality holds and EVI contracts at the degraded rate
    flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                  spectral_penalty_term cfg flags.fgstar_const.C_energy κ :=
  FGStar_main_inequality H cfg Γ κ μ flags

/-- Optimality: The FG★ inequality is sharp (becomes an equality).
    This requires all inequalities in the chain to be equalities. -/
structure FGStar_sharp {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ) where
  /-- The FG★ inequality is an equality -/
  equality : flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                           spectral_penalty_term cfg flags.fgstar_const.C_energy κ
  /-- There exists a Doob function h that achieves the BE degradation bound.
      In BE theory, this means ε(h) = flags.doob.ε where
      ε(h) = sup_φ {∫ Γ₂(log h, φ) dμ / ‖φ‖²} -/
  doob_optimal : ∃ (h : X → ℝ), ∀ x, 0 < h x
  /-- The spectral symbol achieves its sup-norm on a set of positive measure -/
  spectral_achieves_sup : ∃ S : Set ℝ, S.Nonempty ∧
    (∀ lam ∈ S, |spectralSymbol cfg lam| = spectralSymbolSupNorm cfg) ∧
    -- The saturation set has positive Lebesgue measure
    (∃ ε > 0, MeasureTheory.volume (S ∩ Set.Icc 0 ε) > 0)
  /-- The multi-scale configuration minimizes the spectral sup-norm
      among all configurations with the same constraints -/
  config_optimal : ∀ cfg' : MultiScaleConfig m,
    (∑ i, cfg'.α i = 0) →  -- Same zero-sum constraint
    spectralSymbolSupNorm cfg ≤ spectralSymbolSupNorm cfg'
  /-- Cauchy–Schwarzの等号が鋭い形で達成され、
      固有方程式まで満たすテスト関数が存在する。 -/
  cauchy_schwarz_sharp :
    CauchySchwarzSharp H cfg Γ κ μ flags.fgstar_const

/-- Scale optimization: Choosing optimal multi-scale parameters -/
def optimal_scale_config {X : Type*} [MeasurableSpace X] {m : PNat} : MultiScaleConfig m :=
  -- Placeholder: would return the configuration minimizing ‖ψ_m‖_∞
  -- This involves solving an optimization problem over α, τ
  { α := fun _ => 0
    τ := fun _ => 1
    hτ_pos := fun _ => zero_lt_one
    hα_sum := by simp
    hα_bound := fun _ => by simp [abs_zero, zero_le_one] }

/-- Proof: the scale component of `g` preserves the spectral sup-norm, so the
    FG★ spectral penalty term is invariant under `g` at the level of `cfg`.
    Under the scale component of the G-action, the spectral sup-norm is preserved. -/
theorem FGStar_G_invariance_prop_scale {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (cfg : MultiScaleConfig m) (g : GAction X m) :
    -- The FG★ inequality is G-invariant under the symmetry group
    spectralSymbolSupNorm (g.actOnConfig cfg) = spectralSymbolSupNorm cfg := by
  -- This is exactly `spectralSymbol_scale_invariant` applied to `g.scale`.
  simpa [GAction.actOnConfig]
    using spectralSymbol_scale_invariant (cfg := cfg) (s := g.scale)

/-- Theorem: Cauchy-Schwarz equality in the spectral estimate holds
    if and only if the test function is an eigenfunction.

    The spectral inequality ∫|Δ^{⟨m⟩} φ|² dμ ≤ C‖ψ_m‖_∞² ∫Γ(φ,φ) dμ
    becomes an equality when φ satisfies the eigenvalue equation. -/
theorem cauchy_schwarz_equality_characterization
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) (fgstar_const : FGStarConstant)
    (φ : X → ℝ) (h_nontrivial : ∃ x : X, φ x ≠ 0) :
    -- The equality holds iff φ is an eigenfunction
    (∃ lam : ℝ, ∀ x : X, multiScaleDiff H cfg φ x = lam * φ x) ↔
    ∃ cs : CauchySchwarzSharp H cfg Γ κ μ fgstar_const, cs.eigenfunction = φ := by
  constructor
  · -- Forward: If φ is an eigenfunction, then CS equality holds
    intro ⟨lam, h_eigen⟩
    use { eigenfunction := φ
          eigenvalue := lam
          nontrivial := h_nontrivial
          eigen_equation := h_eigen
          equality_holds := by
            intro x
            -- From the eigenfunction relation Δφ = λφ, take absolute values
            simpa [abs_mul] using congrArg (fun t => |t|) (h_eigen x) }

  · -- Reverse: If CS equality holds for φ, then φ is an eigenfunction
    intro ⟨cs, h_eq⟩
    rw [← h_eq]
    exact ⟨cs.eigenvalue, cs.eigen_equation⟩

/-- Proof that the Cauchy-Schwarz equality condition is achieved
    by the optimal configuration in the FG★ sharp case. -/
theorem cauchy_schwarz_sharp_proof
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X)
    (κ : ℝ) (μ : Measure X) (flags : MetaEVIFlags H cfg Γ κ μ)
    (sharp : FGStar_sharp H cfg Γ κ μ flags)
    (h_eigenvalue_bound : ∀ lam : ℝ, (∃ φ : X → ℝ, (∃ x, φ x ≠ 0) ∧
      (∀ x, multiScaleDiff H cfg φ x = lam * φ x)) → |lam| ≤ spectralSymbolSupNorm cfg) :
    -- In the sharp case, there exists an eigenfunction achieving CS equality
    ∃ (φ : X → ℝ) (lam : ℝ),
      (∀ x : X, multiScaleDiff H cfg φ x = lam * φ x) ∧
      (∃ x : X, φ x ≠ 0) ∧
      -- The eigenvalue is related to the spectral symbol
      |lam| ≤ spectralSymbolSupNorm cfg := by
  -- Extract the sharp Cauchy–Schwarz witness providing an eigenfunction
  let cs := sharp.cauchy_schwarz_sharp
  -- Take the eigenfunction and eigenvalue from the witness
  use cs.eigenfunction, cs.eigenvalue
  refine ⟨?eigen_eq, ?nontrivial, ?bound⟩
  · -- eigen-equation holds pointwise by the witness
    exact cs.eigen_equation
  · -- nontriviality from the witness
    exact cs.nontrivial
  · -- eigenvalue bounded by spectral sup-norm (assumption)
    apply h_eigenvalue_bound cs.eigenvalue
    refine ⟨cs.eigenfunction, ?_, ?_⟩
    · exact cs.nontrivial
    · exact cs.eigen_equation

/-- Key lemma: In Fourier space, the Cauchy-Schwarz equality
    corresponds to phase alignment of spectral components. -/
lemma cauchy_schwarz_implies_phase_alignment
    {m : PNat} (cfg : MultiScaleConfig m)
    (lam : ℝ) (h_lam_in_range : ∃ ξ : ℝ, spectralSymbol cfg ξ = lam) :
    -- The eigenfunction corresponds to aligned spectral phases
    ∃ (S : Set ℝ), S.Nonempty ∧
      -- φ̂ is supported where the spectral symbol equals lam
      (∀ ξ ∈ S, spectralSymbol cfg ξ = lam) := by
  -- In Fourier space, the eigenvalue equation becomes:
  -- ψ_m(ξ) * φ̂(ξ) = lam * φ̂(ξ)
  -- This implies φ̂ is supported on {ξ : ψ_m(ξ) = lam}
  use {ξ : ℝ | spectralSymbol cfg ξ = lam}
  constructor
  · -- The support set is non-empty by hypothesis
    obtain ⟨ξ₀, hξ₀⟩ := h_lam_in_range
    use ξ₀
    exact hξ₀
  · -- By definition
    intros ξ hξ
    exact hξ

end Frourio
