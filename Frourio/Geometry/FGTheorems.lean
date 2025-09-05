import Mathlib.Topology.MetricSpace.Basic
import Frourio.Geometry.FGCore
import Frourio.Analysis.EVI
import Frourio.Analysis.PLFACore
import Frourio.Analysis.DoobTransform
import Frourio.Analysis.FrourioFunctional
import Frourio.Geometry.GradientFlowFramework

/-!
# FG Theorems (Phase G2): Statement-only wrappers

This module provides statement-level definitions (Prop-valued) that tie
the FG core data to the existing analysis layer (EVI/Doob/Mosco), as
outlined in design phase G2. Proofs and quantitative details are left to
later phases; here we fix API shapes and dependencies.

References:
- papers/m点幾何学1-7.md: Scale rules, Doob×Scale compatibility
- design/10.md: Section 4 (G2-T1..T4)
-/

namespace Frourio

section X
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/- G2-T1: EVI scale rule (statement-level)
We package the isometry/similarity toggle and generator homogeneity and
expose the effective parameter via `effectiveLambda`. -/
def evi_scale_rule (FG : FGData X) (S : ScaleAction X) : Prop :=
  ∃ (α κ : ℝ),
    (((S.isometry) ∧ α = 0) ∨ S.similarity α) ∧
    S.generator_homogeneous κ ∧
    (∀ k : ℤ, ∃ lam' : ℝ, lam' = effectiveLambda α κ S.Lambda k FG.lam)

/--
Isometry scale rule (theoremized skeleton).

Sketch: In the isometric case, take `α = 0`. Under generator homogeneity
with exponent `κ`, the effective parameter becomes
`lam' = effectiveLambda 0 κ S.Lambda k FG.lam = exp((κ k) log Λ) · lam`.
Here we only assert the existence of such `α, κ` and the algebraic form of
`lam'` via the `effectiveLambda` helper; quantitative EVI preservation is
handled in later phases.
-/
theorem evi_scale_rule_isometry (FG : FGData X) (S : ScaleAction X)
  (hIso : S.isometry) (hκ : ∃ κ : ℝ, S.generator_homogeneous κ) :
  evi_scale_rule FG S := by
  rcases hκ with ⟨κ, hκ'⟩
  refine ⟨0, κ, ?_, hκ', ?_⟩
  · exact Or.inl ⟨hIso, rfl⟩
  · intro k; refine ⟨effectiveLambda 0 κ S.Lambda k FG.lam, rfl⟩

/--
Similarity scale rule (theoremized skeleton).

Sketch: In the similarity case with exponent `α`, and generator
homogeneity exponent `κ`, the EVI parameter rescales according to
`lam' = effectiveLambda α κ S.Lambda k FG.lam`. This statement packages
the existence of the pair `(α, κ)` and the algebraic form via
`effectiveLambda`; the full EVI preservation is treated in subsequent
proof phases.
-/
theorem evi_scale_rule_similarity (FG : FGData X) (S : ScaleAction X)
  (α : ℝ) (hSim : S.similarity α) (hκ : ∃ κ : ℝ, S.generator_homogeneous κ) :
  evi_scale_rule FG S := by
  rcases hκ with ⟨κ, hκ'⟩
  refine ⟨α, κ, ?_, hκ', ?_⟩
  · exact Or.inr hSim
  · intro k; refine ⟨effectiveLambda α κ S.Lambda k FG.lam, rfl⟩

end X

/- Mosco inheritance bridge (re-export to analysis layer) -/
def mosco_inheritance {ι : Type*} (S : MoscoSystem ι) : Prop := EVILimitHolds S

/-- Mosco inheritance theoremized via the analysis-layer `eviInheritance`. -/
theorem mosco_inheritance_thm {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoAssumptions S) : mosco_inheritance S :=
by
  -- `mosco_inheritance S H` is by definition `EVILimitHolds S`.
  -- Conclude using the analysis-layer inheritance theorem.
  exact eviInheritance S H

section X2
variable {X : Type*} [PseudoMetricSpace X]

end X2

/-- Integrated suite corollary: from weak hypothesis flags and an
equivalence assumption pack for `F := Ent + γ·Dσm` with
`λ_BE := lambdaBE S.base.lam S.eps`, plus a packaged lower bound and a
two‑EVI hypothesis, we obtain the three gradient-flow conclusions. -/
theorem flow_suite_from_packs
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  -- Build the equivalence package from weak hypotheses and the assumption pack
  have G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
    build_plfaEdeEvi_package_weak (FrourioFunctional.F S.func)
      (lambdaBE S.base.lam S.eps) Hpack
  -- Apply the integrated suite on the gradient-flow system
  exact gradient_flow_suite S G (lambdaBE S.base.lam S.eps) hLam Htwo

/-- Integrated suite built from consolidated analytic flags and bridge statements
for the PLFA↔EDE, EDE↔EVI, and JKO⇒PLFA components. Prefer this variant when
you already work at the analytic-flags level. -/
theorem flow_suite_from_flags_and_bridges
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (B : AnalyticBridges (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  have G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
    build_package_from_flags_and_bridges (FrourioFunctional.F S.func)
      (lambdaBE S.base.lam S.eps) A B
  exact gradient_flow_suite S G (lambdaBE S.base.lam S.eps) hLam Htwo

/-- Proof-backed variant: use analytic flags and an `EDEEVIAssumptions` pack
to construct the equivalence package, then assemble the integrated suite. -/
theorem flow_suite_from_flags_and_ede_evi_pack
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HplfaEde : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (P : EDEEVIAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HjkoPlfa : JKO_PLFA_from_analytic_flags (FrourioFunctional.F S.func))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  -- Build the equivalence from flags and EDE⇔EVI pack, then use the suite.
  have G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
    build_package_from_flags_and_ede_evi_pack
      (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) A HplfaEde P HjkoPlfa
  exact gradient_flow_suite S G (lambdaBE S.base.lam S.eps) hLam Htwo

/-- Tensorization (min rule) theoremized: if both factors satisfy the
coercivity surrogate `K1prime` and have nonnegative couplings, then the
combined system satisfies the statement-level tensorization predicate. -/
theorem tensorization_min_rule_thm {X Y : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y]
  (S₁ : GradientFlowSystem X) (S₂ : GradientFlowSystem Y)
  (hK1₁ : K1prime S₁.func) (hK1₂ : K1prime S₂.func)
  (hγ₁ : 0 ≤ S₁.func.gamma) (hγ₂ : 0 ≤ S₂.func.gamma) :
  tensorization_min_rule S₁ S₂ :=
by
  exact And.intro hK1₁ (And.intro hK1₂ (And.intro hγ₁ hγ₂))

/-- Step 1 (FG-level wrapper): from λ-semi-convexity and a strong upper bound
for `F := Ent + γ·Dσm` with `λ_eff := lambdaBE λ ε`, together with an analytic
bridge statement `EDE_EVI_from_analytic_flags`, obtain the component predicate
`EDE_EVI_pred` (i.e., `EDE ⇔ EVI(λ_eff)`) for all curves. -/
theorem ede_evi_pred_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (H : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  EDE_EVI_pred (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  exact ede_evi_equiv_from_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) HC SUB H

/-- Convenience: FG-level directional bridge (EDE → EVI) from analytic flags.
Wraps `ede_to_evi_from_flags_auto` at the `GradientFlowSystem` level. -/
theorem ede_to_evi_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (H : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  EDE_to_EVI_from_flags (X := X) (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  exact ede_to_evi_from_flags_auto (X := X)
    (F := FrourioFunctional.F S.func) (lamEff := lambdaBE S.base.lam S.eps) HC SUB H

/-- Convenience: FG-level directional bridge (EVI → EDE) from analytic flags. -/
theorem evi_to_ede_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (H : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  EVI_to_EDE_from_flags (X := X) (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  exact evi_to_ede_from_flags_auto (X := X)
    (F := FrourioFunctional.F S.func) (lamEff := lambdaBE S.base.lam S.eps) HC SUB H

/-- Step 1 (FG-level pack): the same as `ede_evi_pred_for_FG`, but packaged as
`EDEEVIAssumptions` for downstream assembly into the equivalence. -/
theorem ede_evi_pack_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (H : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  EDEEVIAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  refine build_EDEEVI_pack_from_flags
    (FrourioFunctional.F S.func)
    (lambdaBE S.base.lam S.eps)
    HC SUB H

/-- Step 3 (FG-level wrapper): from analytic flags for `F := Ent + γ·Dσm` with
`λ_eff := lambdaBE λ ε` and a PLFA⇔EDE analytic bridge, obtain the component
predicate `PLFA_EDE_pred` (i.e., `PLFA ⇔ EDE`) for all curves. -/
theorem plfa_ede_pred_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (H : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  PLFA_EDE_pred (FrourioFunctional.F S.func) :=
by
  exact plfa_ede_equiv_from_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)
    A.proper A.lsc A.coercive A.HC A.SUB H

/-- Step 3 (FG-level pack): the same as `plfa_ede_pred_for_FG`, but packaged as
`PLFAEDEAssumptions` for downstream assembly into the equivalence. -/
theorem plfa_ede_pack_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (H : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  PLFAEDEAssumptions (FrourioFunctional.F S.func) :=
by
  refine build_PLFAEDE_pack_from_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)
    A.proper A.lsc A.coercive A.HC A.SUB H

/-! Concrete sufficient conditions (FG-side, statement-level)

We provide lightweight constructors to obtain analytic flags and bridge packs
for `F := Ent + γ·Dσm` with `λ_eff := lambdaBE λ ε`, from FG-side assumptions.
The content remains statement-level until analytic proofs are added. -/

/-- Produce `AnalyticFlags` for `F := Ent + γ·Dσm` (statement-level).
We accept minimal nontrivial inputs (`K1prime`, `K4m`) and build the flags. -/
theorem analytic_flags_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (_HK1 : K1prime S.func) (_HK4 : K4m S.func)
  -- Optional: a slope upper bound predicate could be used here; omitted
  : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  -- All flags are placeholders at this phase, so they can be provided.
  refine { proper := ?_, lsc := ?_, coercive := ?_,
           HC := ?_, SUB := ?_, jkoStable := ?_ };
  · -- Proper: choose C = 0, so F x ≥ F x - 0
    refine ⟨0, ?_⟩
    intro x; simp
  · -- Lower semicontinuity: per-point slack with c = 0
    intro x; exact ⟨0, by norm_num, by simp⟩
  · -- Coercive: per-point slack with c = 0
    intro x; exact ⟨0, by norm_num, by simp⟩
  · -- HalfConvex: choose c = 0
    refine ⟨0, by norm_num, ?_⟩
    intro x; simp
  · -- StrongUpperBound: choose c = 0
    refine ⟨0, by norm_num, ?_⟩
    intro x; simp
  · -- JKOStable: constant curve from any initial point
    intro ρ0
    refine ⟨(fun _ => ρ0), rfl, ?_⟩
    intro t; simp

/-- Build `AnalyticBridges` from component packs for `F := Ent + γ·Dσm`.
Given the three component packs, we promote them to analytic-flag bridges by
ignoring the flag inputs (statement-level). -/
theorem analytic_bridges_from_component_packs
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (Hplfa_ede : PLFAEDEAssumptions (FrourioFunctional.F S.func))
  (Hede_evi : EDEEVIAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (Hjko_plfa : JKOPLFAAssumptions (FrourioFunctional.F S.func)) :
  AnalyticBridges (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  -- Build bridges by instantiating the general pack-to-bridge lemmas
  refine { plfaEde :=
             plfa_ede_bridge_from_pack (FrourioFunctional.F S.func)
               (lambdaBE S.base.lam S.eps) Hplfa_ede,
           edeEvi :=
             ede_evi_bridge_from_pack (FrourioFunctional.F S.func)
               (lambdaBE S.base.lam S.eps) Hede_evi,
           jkoPlfa :=
             jko_plfa_bridge_from_pack (FrourioFunctional.F S.func)
               (lambdaBE S.base.lam S.eps) Hjko_plfa }

/-- Build `AnalyticBridges` from an equivalence-assumption pack. -/
theorem analytic_bridges_from_equiv_pack
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (H : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  AnalyticBridges (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  refine { plfaEde :=
             plfa_ede_bridge_from_equiv_pack (FrourioFunctional.F S.func)
               (lambdaBE S.base.lam S.eps) H,
           edeEvi :=
             ede_evi_bridge_from_equiv_pack (FrourioFunctional.F S.func)
               (lambdaBE S.base.lam S.eps) H,
           jkoPlfa :=
             jko_plfa_bridge_from_equiv_pack (FrourioFunctional.F S.func)
               (lambdaBE S.base.lam S.eps) H }

/-- Bridge-eliminated variant: given analytic flags and an equivalence pack for
`F := Ent + γ·Dσm` with `λ_eff := lambdaBE λ ε`, synthesize the analytic bridges
internally and conclude the integrated suite. This replaces the bridge
propositions by explicit constructions. -/
theorem flow_suite_from_flags
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  -- Build analytic bridges from the equivalence pack
  have B := analytic_bridges_from_equiv_pack S Hpack
  exact flow_suite_from_flags_and_bridges S A B hLam Htwo

/-- Integrated suite from concrete component packs and minimal FG flags. -/
theorem flow_suite_from_concrete_conditions
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (_HK1 : K1prime S.func) (_HK4 : K4m S.func)
  (Hplfa_ede : PLFAEDEAssumptions (FrourioFunctional.F S.func))
  (Hede_evi : EDEEVIAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (Hjko_plfa : JKOPLFAAssumptions (FrourioFunctional.F S.func))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  have A := analytic_flags_for_FG S _HK1 _HK4
  have B := analytic_bridges_from_component_packs S Hplfa_ede Hede_evi Hjko_plfa
  exact flow_suite_from_flags_and_bridges S A B hLam Htwo

/-- Fully bridged variant: starting from minimal FG flags `K1′`/`K4^m` and an
equivalence pack for `F := Ent + γ·Dσm`, synthesize both the analytic flags and
bridges internally and conclude the integrated suite. -/
theorem flow_suite_from_fg_flags_and_equiv
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (_HK1 : K1prime S.func) (_HK4 : K4m S.func)
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  have A := analytic_flags_for_FG S _HK1 _HK4
  exact flow_suite_from_flags S A Hpack hLam Htwo

/-- Integrated suite via Doob + m-point assumptions: constructs the
effective-λ lower bound using the functional-layer wrapper and then applies
`flow_suite_from_packs`. This moves the lower-bound input from a raw
assumption to a theorem-backed construction. -/
theorem flow_suite_from_doob_mpoint
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (h : X → ℝ) (D : Diffusion X) (H : DoobAssumptions h D)
  (hM : MPointZeroOrderBound S.Ssup S.XiNorm)
  (hB : BudgetNonneg S.budget)
  (hg : 0 ≤ S.func.gamma)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  -- Construct a λ_eff via the DoobAssumptions-based analysis helper.
  rcases lambdaEffLowerBound_construct_from_doobAssumptions_mpoint S.func S.budget h D H
      S.base.lam S.eps S.Ssup S.XiNorm hM hB hg with ⟨lamEff, hLam⟩
  -- Invoke the pack-based suite with the constructed witness.
  have G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
    build_plfaEdeEvi_package_weak (FrourioFunctional.F S.func)
      (lambdaBE S.base.lam S.eps) Hpack
  have suite := gradient_flow_suite S G lamEff hLam Htwo
  simpa using suite

/-- Integrated suite via real analytic flags and the MM (real) route.
Given real analytic flags for `F := Ent + γ·Dσm` with `λ_eff := lambdaBE λ ε`,
and the three real-route bridges (PLFA⇔EDE, EDE⇔EVI via placeholder builder, and
JKO⇒PLFA), conclude the gradient-flow equivalence, effective-λ lower bound,
and two‑EVI with force. -/
theorem flow_suite_from_real_flags
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HplfaEde : PLFA_EDE_from_real_flags (X := X)
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HedeEvi_builder : EDE_EVI_from_analytic_flags
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HjkoPlfa : JKO_PLFA_from_real_flags (X := X)
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  -- Assemble the real‑route equivalence package and apply the gradient‑flow suite.
  have G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
    plfaEdeEviJko_equiv_real (X := X)
      (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)
      flags HplfaEde HedeEvi_builder HjkoPlfa
  exact gradient_flow_suite S G (lambdaBE S.base.lam S.eps) hLam Htwo

/-- Convenience: same as `flow_suite_from_real_flags` but automatically supplies
the real-route bridges using `PLFACore` builders. Only the EDE⇔EVI builder must be
provided. -/
theorem flow_suite_from_real_flags_auto
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HedeEvi_builder : EDE_EVI_from_analytic_flags
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  -- Obtain the real-route bridges directly from PLFACore.
  have HplfaEde := plfa_ede_from_real_flags_builder
    (X := X) (F := FrourioFunctional.F S.func) (lamEff := lambdaBE S.base.lam S.eps)
  have HjkoPlfa := jko_plfa_from_real_flags_builder
    (X := X) (F := FrourioFunctional.F S.func) (lamEff := lambdaBE S.base.lam S.eps)
  -- Delegate to the base real-flags suite.
  exact flow_suite_from_real_flags S flags HplfaEde HedeEvi_builder HjkoPlfa hLam Htwo

/-- Build the core equivalence `PLFA = EDE = EVI = JKO` for
`F := Ent + γ·Dσm` with `λ_eff := lambdaBE λ ε` from real analytic flags,
supplying the PLFA↔EDE and JKO→PLFA real-route bridges automatically. -/
theorem equivalence_from_real_flags_auto
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HedeEvi_builder : EDE_EVI_from_analytic_flags
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  have HplfaEde := plfa_ede_from_real_flags_builder
    (X := X) (F := FrourioFunctional.F S.func) (lamEff := lambdaBE S.base.lam S.eps)
  have HjkoPlfa := jko_plfa_from_real_flags_builder
    (X := X) (F := FrourioFunctional.F S.func) (lamEff := lambdaBE S.base.lam S.eps)
  exact plfaEdeEviJko_equiv_real (X := X)
    (F := FrourioFunctional.F S.func) (lamEff := lambdaBE S.base.lam S.eps)
    flags HplfaEde HedeEvi_builder HjkoPlfa

/-- Build the core equivalence from placeholder analytic flags and explicit
component builders (PLFA↔EDE, EDE⇔EVI builder, JKO→PLFA). -/
theorem equivalence_from_flags_and_bridges
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HplfaEde : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HedeEvi : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HjkoPlfa : JKO_PLFA_from_analytic_flags (FrourioFunctional.F S.func)) :
  plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  exact build_package_from_analytic_flags
    (F := FrourioFunctional.F S.func) (lamEff := lambdaBE S.base.lam S.eps)
    HplfaEde HedeEvi HjkoPlfa A

/-- Build the core equivalence from an `EquivBuildAssumptions` pack directly. -/
theorem equivalence_from_equiv_pack
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (H : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  exact build_plfaEdeEvi_package
    (F := FrourioFunctional.F S.func) (lamEff := lambdaBE S.base.lam S.eps) H

/-- Re-export: gradient-flow equivalence (PLFA = EDE = EVI = JKO). -/
def flow_equivalence {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : Prop :=
  gradient_flow_equiv S

/-- Re-export: effective lambda lower bound statement. -/
def lambda_eff_lower {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : Prop :=
  lambda_eff_lower_bound S

/-- Convenience: construct `lambda_eff_lower` from Doob assumptions and m‑point
zero‑order bounds using the analysis‑layer constructive inequality. -/
theorem lambda_eff_lower_from_doob
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (h : X → ℝ) (D : Diffusion X) (H : DoobAssumptions h D)
  (hM : MPointZeroOrderBound S.Ssup S.XiNorm)
  (hB : BudgetNonneg S.budget)
  (hg : 0 ≤ S.func.gamma) :
  lambda_eff_lower S :=
by
  -- Delegate to the framework‑level builder.
  exact lambda_eff_lower_bound_from_doob (X := X) S h D H hM hB hg

/-- Re-export: two-EVI with external force (squared-distance synchronization). -/
def two_evi_with_force_alias {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : Prop :=
  two_evi_with_force S

/-- Multiscale EVI parameter rule alias (m-dimensional scale composition). -/
def evi_multiscale_rule {m : ℕ}
  (Λ α κ : Fin m → ℝ) (k : Fin m → ℤ) : Prop :=
  multiscale_lambda_rule Λ α κ k

/-- Distance synchronization with error (concrete route):
From `two_evi_with_force S` and a Grönwall predicate for `W(t) = d2(u t, v t)`,
obtain a distance synchronization statement with an explicit error `η`.
This wraps `twoEVIWithForce_to_distance_concrete`. -/
theorem two_evi_with_force_to_distance_concrete
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (Htwo : two_evi_with_force S)
  (u v : ℝ → X) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred S.base.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v η :=
by
  have H : TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v := Htwo u v
  exact twoEVIWithForce_to_distance_concrete ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v H

/-- Closed distance synchronization (concrete route): if the Grönwall predicate
holds for all `η`, then `two_evi_with_force S` yields a distance synchronization
bound without additional inputs. Wraps `twoEVIWithForce_to_distance_concrete_closed`. -/
theorem two_evi_with_force_to_distance_concrete_closed
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (Htwo : two_evi_with_force S)
  (u v : ℝ → X)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred S.base.lam η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v η :=
by
  have H : TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v := Htwo u v
  exact twoEVIWithForce_to_distance_concrete_closed
    ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v H Hgr_all

end Frourio
