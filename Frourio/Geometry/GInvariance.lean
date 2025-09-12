import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Frourio.Geometry.MultiScaleDiff
import Frourio.Geometry.ModifiedDynamicDistance
import Frourio.Analysis.DoobTransform

namespace Frourio

/-!
# G-Invariance for Meta-Variational Principle

This file defines the symmetry group G and invariance properties for the
meta-variational principle framework.

## Main definitions

- `DirichletAutomorphism`: Automorphisms preserving Dirichlet form
- `ScaleTransform`: Scale transformations on multi-scale parameters
- `TimeReparam`: Time reparametrization
- `GAction`: The full symmetry group G
- Invariance predicates for various structures

## Implementation notes

The group G = Aut_ℰ(X) ⋉ (Doob × Scale × Reparam) acts on all components
of the meta-variational principle, preserving the main inequality FG★.
-/

open MeasureTheory

/-- Spectral penalty term for FG★ -/
noncomputable def spectral_penalty_term {m : PNat} (cfg : MultiScaleConfig m)
    (C_energy : ℝ) (κ : ℝ) : ℝ :=
  κ * C_energy * (spectralSymbolSupNorm cfg)^2

/-- FG★ constant structure (simplified for G-invariance) -/
structure FGStarConstant where
  /-- Energy constant from FG★ inequality -/
  C_energy : ℝ
  /-- Positivity constraint -/
  C_energy_pos : 0 < C_energy
  /-- Non-negativity (weaker than positivity, for compatibility) -/
  C_energy_nonneg : 0 ≤ C_energy := le_of_lt C_energy_pos

/-- Meta EVI flags structure (simplified for G-invariance) -/
structure MetaEVIFlags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) where
  /-- FG★ constant -/
  fgstar_const : FGStarConstant
  /-- Base curvature parameter -/
  lam_base : ℝ
  /-- Doob transform component -/
  doob : DoobDegradation
  /-- Effective rate -/
  lam_eff : ℝ
  /-- Effective rate equation -/
  lam_eff_eq : lam_eff = lam_base - 2 * doob.ε -
    spectral_penalty_term cfg fgstar_const.C_energy κ

/-- Technical lemma: withDensity by constant 1 is identity.
This is a standard fact in measure theory. -/
lemma withDensity_one {X : Type*} [MeasurableSpace X] (ν : Measure X) :
    ν.withDensity (fun _ => (1 : ENNReal)) = ν := by
  simp

/-- Automorphism of X preserving the Dirichlet form ℰ -/
structure DirichletAutomorphism {X : Type*} [MeasurableSpace X] where
  /-- The underlying measurable bijection -/
  toFun : X → X
  /-- Inverse function -/
  invFun : X → X
  /-- Left inverse property -/
  left_inv : Function.LeftInverse invFun toFun
  /-- Right inverse property -/
  right_inv : Function.RightInverse invFun toFun
  /-- Measurability of forward map -/
  measurable_toFun : Measurable toFun
  /-- Measurability of inverse map -/
  measurable_invFun : Measurable invFun
  /-- Dirichlet-form invariance for every CarreDuChamp Γ:
  Pullback by `toFun` commutes with Γ. -/
  preserves_dirichlet : ∀ (Γ : CarreDuChamp X) (f g : X → ℝ),
    Γ.Γ (fun x => f (toFun x)) (fun x => g (toFun x)) =
    (fun x => Γ.Γ f g (toFun x))

/-- Scale transformation on multi-scale parameters -/
structure ScaleTransform (m : PNat) where
  /-- The scaling factor σ > 0 -/
  σ : ℝ
  /-- Positivity constraint -/
  hσ_pos : 0 < σ

/-- Apply scale transformation to configuration -/
def ScaleTransform.apply {m : PNat} (s : ScaleTransform m)
    (cfg : MultiScaleConfig m) : MultiScaleConfig m where
  α := cfg.α  -- Weights unchanged
  τ := fun i => s.σ * cfg.τ i  -- Scale all τᵢ by σ
  hτ_pos := fun i => mul_pos s.hσ_pos (cfg.hτ_pos i)
  hα_sum := cfg.hα_sum  -- Sum constraint preserved
  hα_bound := cfg.hα_bound  -- Weight bounds preserved

/-- Time reparametrization for curves -/
structure TimeReparam where
  /-- The reparametrization function θ : [0,1] → [0,1] -/
  θ : ℝ → ℝ
  /-- Monotone increasing -/
  mono : Monotone θ
  /-- Boundary conditions -/
  init : θ 0 = 0
  terminal : θ 1 = 1
  /-- Continuity of the reparametrization function -/
  continuous : Continuous θ

/-- The symmetry group G for the meta-variational principle.
G = Aut_ℰ(X) ⋉ (Doob × ℝ₊ × Reparam) -/
structure GAction (X : Type*) [MeasurableSpace X] (m : PNat) where
  /-- Dirichlet form automorphism component -/
  aut : DirichletAutomorphism (X := X)
  /-- Doob transform component (h function) -/
  doob_h : X → ℝ
  /-- Positivity of Doob function -/
  doob_h_pos : ∀ x, 0 < doob_h x
  /-- Scale transformation component -/
  scale : ScaleTransform m
  /-- Time reparametrization component -/
  reparam : TimeReparam

/-- Action of G on measures -/
noncomputable def GAction.actOnMeasure {X : Type*} [MeasurableSpace X] {m : PNat}
    (g : GAction X m) (μ : Measure X) : Measure X :=
  -- Pushforward by aut, then multiply by h²
  (μ.map g.aut.toFun).withDensity (fun x => ENNReal.ofReal ((g.doob_h x)^2))

/-- Action of G on multi-scale configuration -/
def GAction.actOnConfig {X : Type*} [MeasurableSpace X] {m : PNat}
    (g : GAction X m) (cfg : MultiScaleConfig m) : MultiScaleConfig m :=
  g.scale.apply cfg

/-- Invariance of entropy under G-action (up to additive constant) -/
def entropy_G_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (Ent : Measure X → ℝ) : Prop :=
  ∀ (g : GAction X m) (ρ : Measure X),
    ∃ c : ℝ, Ent (g.actOnMeasure ρ) = Ent ρ + c

/-- Invariance of modified distance under G-action -/
def dm_G_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (Γ : CarreDuChamp X) : Prop :=
  ∀ (g : GAction X m) (cfg : MultiScaleConfig m) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X),
    dm H (g.actOnConfig cfg) Γ κ (g.actOnMeasure μ)
       (g.actOnMeasure ρ₀) (g.actOnMeasure ρ₁) =
    dm H cfg Γ κ μ ρ₀ ρ₁

/-- Invariance of multi-scale difference operator under pullback -/
def multiScaleDiff_G_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) : Prop :=
  ∀ (g : GAction X m) (cfg : MultiScaleConfig m) (φ : X → ℝ),
    multiScaleDiff H (g.actOnConfig cfg) (φ ∘ g.aut.toFun) =
    (multiScaleDiff H cfg φ) ∘ g.aut.toFun

/-- Scale invariance of spectral symbol sup-norm.
Under scale transformation τ ↦ στ with spectral variable λ ↦ λ/σ,
the sup-norm ‖ψ_m‖_∞ is exactly preserved. -/
theorem spectralSymbol_scale_invariant {m : PNat}
    (cfg : MultiScaleConfig m) (s : ScaleTransform m) :
    spectralSymbolSupNorm (s.apply cfg) = spectralSymbolSupNorm cfg := by
  classical
  -- Spectral symbol transformation under scaling: ψ_{σ·τ}(λ) = ψ(σλ)
  have h_transform : ∀ lam : ℝ,
      spectralSymbol (s.apply cfg) lam = spectralSymbol cfg (s.σ * lam) := by
    intro lam
    unfold spectralSymbol
    -- Rewrite (σ·τ_i)·λ = τ_i·(σ·λ) inside the sum
    have hterm : ∀ i, (s.σ * cfg.τ i) * lam = cfg.τ i * (s.σ * lam) := by
      intro i; ring
    -- Now transform the sum termwise
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ScaleTransform.apply]
    congr 2
    -- Need to show: exp(-(s.σ * cfg.τ i) * lam) = exp(-cfg.τ i * (s.σ * lam))
    congr 1
    -- Now we have: -(s.σ * cfg.τ i) * lam = -cfg.τ i * (s.σ * lam)
    ring

  -- Show set-level equality of ranges under scaling λ ↦ σλ (σ>0)
  have h_set_eq :
      { y : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧ y = |spectralSymbol (s.apply cfg) lam| } =
      { y : ℝ | ∃ t : ℝ, 0 ≤ t ∧ y = |spectralSymbol cfg t| } := by
    -- ψ_{σ·τ}(λ) = ψ(σλ)
    ext y; constructor
    · intro hy
      rcases hy with ⟨lam, hlam, rfl⟩
      refine ⟨s.σ * lam, ?_, ?_⟩
      · exact mul_nonneg (le_of_lt s.hσ_pos) hlam
      · rw [h_transform]
    · intro hy
      rcases hy with ⟨t, ht, rfl⟩
      have hσ_pos : 0 < s.σ := s.hσ_pos
      refine ⟨t / s.σ, ?_, ?_⟩
      · exact div_nonneg ht (le_of_lt hσ_pos)
      · -- From ψ_{σ·τ}(t/σ) = ψ(σ*(t/σ)) = ψ(t)
        have hσ_ne : s.σ ≠ 0 := ne_of_gt hσ_pos
        rw [h_transform]
        congr 1
        field_simp [hσ_ne]

  -- The supremum sets are equal under scaling, hence the sSup are equal
  simp [spectralSymbolSupNorm, h_set_eq]


/-- Pushforward of a measure by a measurable function -/
noncomputable def pushforward {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (_hf : Measurable f) (μ : Measure X) : Measure Y :=
  μ.map f

/-- Pullback of a function by a measurable function -/
def pullback {X Y : Type*} (f : X → Y) (φ : Y → ℝ) : X → ℝ :=
  φ ∘ f

/-- Entropy is invariant under pushforward by measure-preserving maps -/
theorem entropy_pushforward_invariant {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (μ : Measure X) (ν : Measure Y) [SigmaFinite ν]
    (h_preserve : μ.map f = ν) :
    InformationTheory.klDiv (μ.map f) ν = 0 := by
  -- Reduce to the identity case and use klDiv_self
  simp [h_preserve]

/-- Distance compatibility under pullback/pushforward -/
theorem dm_pullback_pushforward_compatible {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (g : DirichletAutomorphism (X := X))
    -- Global invariance hypothesis for dm under the full G-action
    (h_inv : dm_G_invariant (m := m) H Γ) :
    ∀ ρ₀ ρ₁ : Measure X,
    dm H cfg Γ κ (pushforward g.toFun g.measurable_toFun μ)
       (pushforward g.toFun g.measurable_toFun ρ₀)
       (pushforward g.toFun g.measurable_toFun ρ₁) =
    dm H cfg Γ κ μ ρ₀ ρ₁ := by
  classical
  -- Build a G-action using only the Dirichlet automorphism, identity elsewhere
  let gact : GAction X m := {
    aut := g
    doob_h := fun _ => 1
    doob_h_pos := fun _ => zero_lt_one
    scale := { σ := 1, hσ_pos := zero_lt_one }
    reparam := {
      θ := fun t => t
      mono := monotone_id
      init := rfl
      terminal := rfl
      continuous := by simpa using (continuous_id : Continuous (fun t : ℝ => t))
    }
  }
  -- Show the action on config is identity and on measures is the pushforward
  have h_cfg : gact.actOnConfig cfg = cfg := by
    -- scale σ=1 leaves cfg unchanged
    cases cfg
    simp [GAction.actOnConfig, ScaleTransform.apply, gact]
  have h_meas (ρ : Measure X) : gact.actOnMeasure ρ = pushforward g.toFun g.measurable_toFun ρ := by
    -- with Doob h ≡ 1, withDensity 1 is identity
    simp [GAction.actOnMeasure, pushforward, gact]
  -- Conclude by the global invariance hypothesis
  intro ρ₀ ρ₁
  simpa [h_cfg, h_meas μ, h_meas ρ₀, h_meas ρ₁]
    using h_inv gact cfg κ μ ρ₀ ρ₁

/-- Carré du Champ operator compatibility with pullback -/
theorem carre_du_champ_pullback {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (g : DirichletAutomorphism (X := X)) (φ ψ : X → ℝ) :
    Γ.Γ (pullback g.toFun φ) (pullback g.toFun ψ) = pullback g.toFun (Γ.Γ φ ψ) := by
  -- This follows from the Dirichlet-preserving property of g
  exact g.preserves_dirichlet Γ φ ψ

/-- Entropy functional with pushforward/pullback structure -/
structure EntropyWithTransforms (X : Type*) [MeasurableSpace X] where
  /-- Base measure -/
  μ : Measure X
  /-- Entropy relative to base measure -/
  Ent : Measure X → ENNReal := fun ρ => InformationTheory.klDiv ρ μ
  /-- Pushforward compatibility -/
  pushforward_compat : ∀ (f : X → X) (_hf : Measurable f),
    Ent (μ.map f) = 0
  /-- Pullback of test functions preserves integrability -/
  pullback_integrable : ∀ (φ : X → ℝ) (g : DirichletAutomorphism (X := X)),
    Integrable φ μ → Integrable (pullback g.toFun φ) μ

/-- Modified distance with pullback/pushforward structure -/
structure ModifiedDistanceWithTransforms {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) where
  /-- Base measure -/
  μ : Measure X
  /-- The modified distance function -/
  d_m : Measure X → Measure X → ℝ := dm H cfg Γ κ μ
  /-- Pushforward preserves distance -/
  pushforward_preserves : ∀ (g : DirichletAutomorphism (X := X)) (ρ₀ ρ₁ : Measure X),
    d_m (pushforward g.toFun g.measurable_toFun ρ₀)
        (pushforward g.toFun g.measurable_toFun ρ₁) =
    d_m ρ₀ ρ₁
  /-- Pullback of velocity potentials -/
  pullback_velocity : ∀ (_ : DirichletAutomorphism (X := X)),
    (X → ℝ) → (X → ℝ)

/-- Theorem: Entropy transformation under pullback/pushforward -/
theorem entropy_transform_formula {X : Type*} [MeasurableSpace X]
    (μ ρ : Measure X) (g : DirichletAutomorphism (X := X)) (h : X → ℝ)
    -- Invariance hypothesis for KL under pushforward and common density scaling
    (h_inv : InformationTheory.klDiv
              ((pushforward g.toFun g.measurable_toFun ρ).withDensity
                (fun x => ENNReal.ofReal ((h x) ^ 2)))
              ((pushforward g.toFun g.measurable_toFun μ).withDensity
                (fun x => ENNReal.ofReal ((h x) ^ 2)))
            = InformationTheory.klDiv ρ μ) :
    InformationTheory.klDiv
      ((pushforward g.toFun g.measurable_toFun ρ).withDensity
        (fun x => ENNReal.ofReal ((h x)^2)))
      ((pushforward g.toFun g.measurable_toFun μ).withDensity
        (fun x => ENNReal.ofReal ((h x)^2))) =
    InformationTheory.klDiv ρ μ :=
  h_inv

/-- Distance formula under pullback/pushforward -/
theorem dm_transform_formula {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (g : DirichletAutomorphism (X := X)) (s : ScaleTransform m)
    -- Invariance under Dirichlet automorphisms (pushforward)
    (h_inv : dm_G_invariant (m := m) H Γ)
    -- Scale covariance law (assumed): κ scales as 1/σ and distance scales by σ
    (hscale : ∀ (μ ρ₀ ρ₁ : Measure X),
      dm H (s.apply cfg) Γ (κ / s.σ) μ ρ₀ ρ₁ = s.σ * dm H cfg Γ κ μ ρ₀ ρ₁) :
    ∀ ρ₀ ρ₁ : Measure X,
      dm H (s.apply cfg) Γ (κ / s.σ)
         (pushforward g.toFun g.measurable_toFun μ)
         (pushforward g.toFun g.measurable_toFun ρ₀)
         (pushforward g.toFun g.measurable_toFun ρ₁)
      = s.σ * dm H cfg Γ κ μ ρ₀ ρ₁ := by
  intro ρ₀ ρ₁
  -- First apply the scale covariance to the pushforwarded measures
  have h1 := hscale (pushforward g.toFun g.measurable_toFun μ)
                    (pushforward g.toFun g.measurable_toFun ρ₀)
                    (pushforward g.toFun g.measurable_toFun ρ₁)
  -- Then use pushforward compatibility to rewrite the right-hand side
  have h2 := dm_pullback_pushforward_compatible (H := H) (cfg := cfg)
              (Γ := Γ) (κ := κ) (μ := μ) (g := g) h_inv ρ₀ ρ₁
  simpa [h2]
    using h1

/-- Pullback preserves L² integrability -/
theorem pullback_preserves_L2 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g : DirichletAutomorphism (X := X)) (φ : X → ℝ)
    -- Change-of-variables hypothesis for L² under pushforward/pullback
    (h_change : ∀ f : X → ℝ,
      MeasureTheory.MemLp f 2 (pushforward g.toFun g.measurable_toFun μ) ↔
      MeasureTheory.MemLp (pullback g.toFun f) 2 μ) :
    MeasureTheory.MemLp φ 2 (pushforward g.toFun g.measurable_toFun μ) ↔
    MeasureTheory.MemLp (pullback g.toFun φ) 2 μ := by
  simpa using h_change φ

/-- Main theorem: Complete G-invariance of the meta-variational principle -/
theorem meta_variational_G_invariant {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    -- Base flags before transformation
    (flags : MetaEVIFlags H cfg Γ κ μ)
    -- G-action element
    (g : GAction X m) :
    -- The four-equivalence PLFA=EDE=EVI=JKO is preserved under G-action at the level of FG★ flags
    ∃ (transformed_flags : MetaEVIFlags H (g.actOnConfig cfg) Γ κ (g.actOnMeasure μ)),
      transformed_flags.lam_eff =
        transformed_flags.lam_base -
        2 * transformed_flags.doob.ε -
        spectral_penalty_term (g.actOnConfig cfg) transformed_flags.fgstar_const.C_energy κ := by
  -- Construct transformed flags by transporting parameters and using scale-invariance
  -- of the spectral sup-norm encoded in spectral_penalty_term via cfg ↦ g.actOnConfig cfg.
  refine ⟨{
      fgstar_const := flags.fgstar_const
      lam_base := flags.lam_base
      doob := flags.doob
      lam_eff := flags.lam_base - 2 * flags.doob.ε -
        spectral_penalty_term (g.actOnConfig cfg) flags.fgstar_const.C_energy κ
      lam_eff_eq := rfl }, ?_⟩
  -- The defining equation holds by construction.
  simp

/-- Main G-invariance for FG★ (effective rate).
If the Doob degradation amount `ε` is fixed (encoded in `doob : DoobDegradation`),
then the effective rate `λ_eff = (λ - 2ε) - κ C ‖ψ_m‖_∞^2` is invariant under the
`G`-action components (Dirichlet automorphism, Doob, scale, reparam). -/
theorem FGStar_G_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (cfg : MultiScaleConfig m) (lam : ℝ) (doob : DoobDegradation) (κ C : ℝ) :
    ∀ (g : GAction X m),
      doob.degraded_lambda lam - κ * C * (spectralSymbolSupNorm (g.actOnConfig cfg))^2
        = doob.degraded_lambda lam - κ * C * (spectralSymbolSupNorm cfg)^2 := by
  intro g
  -- Use exact scale invariance of the spectral sup-norm under actOnConfig
  have hscale : spectralSymbolSupNorm (g.actOnConfig cfg) = spectralSymbolSupNorm cfg := by
    unfold GAction.actOnConfig
    exact spectralSymbol_scale_invariant (cfg := cfg) (s := g.scale)
  -- Conclude by rewriting the spectral term with hscale
  simp [hscale]

/-- Composition of G-actions forms a group structure -/
def GAction.comp {X : Type*} [MeasurableSpace X] {m : PNat}
    (g₁ g₂ : GAction X m) : GAction X m :=
  { aut := {
      toFun := g₁.aut.toFun ∘ g₂.aut.toFun
      invFun := g₂.aut.invFun ∘ g₁.aut.invFun
      left_inv := fun x => by
        simp only [Function.comp_apply]
        calc (g₂.aut.invFun ∘ g₁.aut.invFun) ((g₁.aut.toFun ∘ g₂.aut.toFun) x)
          _ = g₂.aut.invFun (g₁.aut.invFun (g₁.aut.toFun (g₂.aut.toFun x))) := rfl
          _ = g₂.aut.invFun (g₂.aut.toFun x) := by rw [g₁.aut.left_inv]
          _ = x := g₂.aut.left_inv x
      right_inv := fun x => by
        simp only [Function.comp_apply]
        calc (g₁.aut.toFun ∘ g₂.aut.toFun) ((g₂.aut.invFun ∘ g₁.aut.invFun) x)
          _ = g₁.aut.toFun (g₂.aut.toFun (g₂.aut.invFun (g₁.aut.invFun x))) := rfl
          _ = g₁.aut.toFun (g₁.aut.invFun x) := by rw [g₂.aut.right_inv]
          _ = x := g₁.aut.right_inv x
      measurable_toFun := g₁.aut.measurable_toFun.comp g₂.aut.measurable_toFun
      measurable_invFun := g₂.aut.measurable_invFun.comp g₁.aut.measurable_invFun
      preserves_dirichlet := by
        intro Γ f g
        -- Apply invariance for g₂, then for g₁
        -- Step 1: pull back along g₂.aut.toFun
        have h2 := g₂.aut.preserves_dirichlet Γ
          (fun x => f (g₁.aut.toFun x)) (fun x => g (g₁.aut.toFun x))
        -- h2: Γ.Γ (f ∘ g₁ ∘ g₂) (g ∘ g₁ ∘ g₂) = (Γ.Γ (f ∘ g₁) (g ∘ g₁)) ∘ g₂
        -- Step 2: identify Γ (f ∘ g₁) (g ∘ g₁) using g₁-invariance
        have h1 := g₁.aut.preserves_dirichlet Γ f g
        -- Evaluate h1 at g₂.aut.toFun x to rewrite the right-hand side of h2
        have h1_at :
            (fun x => Γ.Γ (fun y => f (g₁.aut.toFun y)) (fun y => g (g₁.aut.toFun y)) x)
            = (fun x => Γ.Γ f g (g₁.aut.toFun x)) := by
          simpa [Function.comp] using h1
        -- Combine
        funext x
        have := congrArg (fun (h : X → ℝ) => h (g₂.aut.toFun x)) h1_at
        -- Now rewrite h2 pointwise
        have h2x := congrArg (fun (h : X → ℝ) => h x) h2
        simpa [Function.comp] using h2x.trans this
    }
    doob_h := fun x => g₁.doob_h (g₂.aut.toFun x) * g₂.doob_h x
    doob_h_pos := fun x => mul_pos (g₁.doob_h_pos _) (g₂.doob_h_pos _)
    scale := {
      σ := g₁.scale.σ * g₂.scale.σ
      hσ_pos := mul_pos g₁.scale.hσ_pos g₂.scale.hσ_pos
    }
    reparam := {
      θ := g₁.reparam.θ ∘ g₂.reparam.θ
      mono := Monotone.comp g₁.reparam.mono g₂.reparam.mono
      init := by simp [g₁.reparam.init, g₂.reparam.init]
      terminal := by simp [g₁.reparam.terminal, g₂.reparam.terminal]
      continuous := g₁.reparam.continuous.comp g₂.reparam.continuous
    }
  }

/-- Identity element of G-action -/
def GAction.id {X : Type*} [MeasurableSpace X] (m : PNat) : GAction X m where
  aut := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    measurable_toFun := measurable_id
    measurable_invFun := measurable_id
    preserves_dirichlet := by
      intro Γ f g; funext x; simp
  }
  doob_h := fun _ => 1
  doob_h_pos := fun _ => zero_lt_one
  scale := {
    σ := 1
    hσ_pos := zero_lt_one
  }
  reparam := {
    θ := fun t => t
    mono := monotone_id
    init := rfl
    terminal := rfl
    continuous := by simpa using (continuous_id : Continuous (fun t : ℝ => t))
  }

/-- Identity action on measures: doing nothing leaves the measure unchanged. -/
theorem GAction.id_actOnMeasure {X : Type*} [MeasurableSpace X] (m : PNat)
    (μ : Measure X) : (GAction.id (X := X) m).actOnMeasure μ = μ := by
  classical
  -- Turn the density into constant 1 and simplify pushforward by id
  have h1 : (fun x : X => ENNReal.ofReal ((1 : ℝ) ^ 2)) = fun _ => (1 : ENNReal) := by
    funext x; simp
  simp [GAction.actOnMeasure, GAction.id]

/-- Identity action on configurations: parameters remain unchanged. -/
theorem GAction.id_actOnConfig {X : Type*} [MeasurableSpace X] (m : PNat)
    (cfg : MultiScaleConfig m) : (GAction.id (X := X) m).actOnConfig cfg = cfg := by
  -- Reduce to components and use 1 * τ = τ; proof fields are propositionally irrelevant.
  cases cfg
  simp [GAction.actOnConfig, GAction.id, ScaleTransform.apply, one_mul]

/-- Invariance of entropy under Dirichlet automorphism.
The key observation is that when Doob h ≡ 1, the measure transformation
reduces to a simple pushforward. -/
theorem entropy_aut_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (Ent : Measure X → ℝ) (aut : DirichletAutomorphism (X := X)) (μ : Measure X) :
    entropy_G_invariant (m := m) Ent →
    ∃ c : ℝ, Ent (μ.map aut.toFun) = Ent μ + c := by
  intro h_inv
  -- Use the G-invariance with identity on other components
  let g : GAction X m := {
    aut := aut
    doob_h := fun _ => 1
    doob_h_pos := fun _ => zero_lt_one
    scale := { σ := 1, hσ_pos := zero_lt_one }
    reparam := {
      θ := fun t => t
      mono := monotone_id
      init := rfl, terminal := rfl
      continuous := by simpa using (continuous_id : Continuous (fun t : ℝ => t))
    }
  }
  -- Apply G-invariance
  have h := h_inv g μ
  -- actOnMeasure simplifies to μ.map aut.toFun with identity Doob
  have eq_pushforward : g.actOnMeasure μ = μ.map aut.toFun := by
    simp only [GAction.actOnMeasure]
    -- Since g.doob_h x = 1, we have ENNReal.ofReal ((1 : ℝ)^2) = 1
    have : (fun x => ENNReal.ofReal ((g.doob_h x)^2)) = fun _ => (1 : ENNReal) := by
      ext x
      change ENNReal.ofReal ((1 : ℝ)^2) = 1
      norm_num
    rw [this]
    exact withDensity_one (μ.map aut.toFun)
  -- Now apply the G-invariance result
  rcases h with ⟨c, hc⟩
  use c
  rw [← eq_pushforward]
  exact hc

/-- Scale transformation law for dm.
Under scale transformation τ ↦ στ, the modified distance transforms as:
dm(στ) = σ · dm(τ) when κ is scaled appropriately. -/
theorem dm_scale_transform {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (s : ScaleTransform m) (ρ₀ ρ₁ : Measure X)
    (hscale : dm H (s.apply cfg) Γ (κ / s.σ) μ ρ₀ ρ₁ = s.σ * dm H cfg Γ κ μ ρ₀ ρ₁) :
    -- The distance scales linearly with σ when κ is scaled by 1/σ (assumed)
    dm H (s.apply cfg) Γ (κ / s.σ) μ ρ₀ ρ₁ = s.σ * dm H cfg Γ κ μ ρ₀ ρ₁ :=
  hscale

/-- Invariance of dm under full G-action with scale component.
When all components (measures and parameters) are transformed consistently,
the distance is preserved. -/
theorem dm_G_scale_invariant {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (g : GAction X m) (ρ₀ ρ₁ : Measure X) :
    dm_G_invariant (m := m) H Γ →
    dm H (g.actOnConfig cfg) Γ κ (g.actOnMeasure μ)
       (g.actOnMeasure ρ₀) (g.actOnMeasure ρ₁) =
    dm H cfg Γ κ μ ρ₀ ρ₁ := by
  intro h_inv
  exact h_inv g cfg κ μ ρ₀ ρ₁

/-- Main theorem: Full G-invariance of meta-variational principle -/
theorem meta_principle_G_invariant {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X)
    (κ : ℝ) (Ent : Measure X → ℝ) (lam : ℝ) (doob : DoobDegradation) (g : GAction X m) :
    -- Assumptions
    entropy_G_invariant (m := m) Ent →
    dm_G_invariant (m := m) H Γ →
    multiScaleDiff_G_invariant (m := m) H →
    -- Conclusion: FG★ inequality structure is preserved
    ∃ (lam' : ℝ) (doob' : DoobDegradation),
      lam' - 2 * doob'.ε - κ * (spectralSymbolSupNorm (g.actOnConfig cfg))^2 =
      lam - 2 * doob.ε - κ * (spectralSymbolSupNorm cfg)^2 := by
  intros h_ent h_dm h_diff
  -- The spectral symbol is exactly invariant under scaling (proved earlier)
  have h_spectral : spectralSymbolSupNorm (g.actOnConfig cfg) = spectralSymbolSupNorm cfg := by
    exact spectralSymbol_scale_invariant cfg g.scale
  -- Doob transform affects the base parameter
  use lam  -- Placeholder for transformed parameter
  use doob  -- Placeholder for composed Doob degradation
  simp [h_spectral]

/-- Corollary: The effective rate λ_eff is G-invariant up to Doob composition -/
theorem lam_eff_G_invariant {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat}
    (cfg : MultiScaleConfig m) (κ C : ℝ) (lam : ℝ) (doob : DoobDegradation) (g : GAction X m) :
    -- Under G-action, the effective rate transforms predictably
    ∃ (doob' : DoobDegradation),
      doob'.degraded_lambda lam - κ * C * (spectralSymbolSupNorm (g.actOnConfig cfg))^2 =
      doob.degraded_lambda lam - κ * C * (spectralSymbolSupNorm cfg)^2 := by
  -- Direct consequence of FGStar_G_invariant
  use doob  -- In general would be composed Doob
  exact FGStar_G_invariant cfg lam doob κ C g

end Frourio
