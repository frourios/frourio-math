import Mathlib.Topology.MetricSpace.Basic
import Frourio.Geometry.FGCore
import Frourio.Analysis.EVI
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

/- G2-T2: Doob×Scale commute (sufficient-condition shell)
We keep this abstract: for any weight `h` and scale step `k`, the Doob
transform should commute with the scale action under suitable (omitted)
assumptions. -/
def doob_scale_commute (_D : Diffusion X) (_S : ScaleAction X) : Prop :=
  ∀ (_h : X → ℝ) (_k : ℤ), True

end X

/- G2-T3: Mosco inheritance bridge (re-export to analysis layer) -/
def mosco_inheritance {ι : Type*} (S : MoscoSystem ι)
  (_H : MoscoAssumptions S) : Prop :=
  EVILimitHolds S

section X2
variable {X : Type*} [PseudoMetricSpace X]

/- G2-T4: two-EVI synchronization with an abstract error bound.
We existentially package the required ingredients and call the analysis
layer's `eviSumWithError`. -/
def evi_sum_with_error (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∃ (hu : IsEVISolution P u) (hv : IsEVISolution P v)
    (geodesicBetween : Prop) (η : ℝ),
      eviSumWithError P u v hu hv geodesicBetween
        ({ η := η, bound := fun _t => True } : MixedErrorBound X u v)

/-- Two-EVI synchronization: squared-distance bound with an error term.
Given the statement-level `eviSumWithError` and an inhomogeneous Grönwall
lemma in the `half` form, we obtain a linear-in-time upper bound for the
squared distance. -/
theorem evi_two_sync_sq_with_error
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop) (η : ℝ)
  (Hgr : gronwall_exponential_contraction_with_error_half_pred P.lam η
    (fun t => d2 (u t) (v t))) :
  (eviSumWithError P u v hu hv geodesicBetween
    ({ η := η, bound := fun _t => True } : MixedErrorBound X u v)) →
  ∀ t : ℝ,
    d2 (u t) (v t) ≤
      Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) + (2 * η) * t :=
by
  intro Hsum
  -- Direct application of the inhomogeneous Grönwall placeholder.
  have h := Hgr (by
    intro t
    -- This is exactly the inequality packaged by `eviSumWithError`.
    simpa using (Hsum t))
  intro t; simpa using h t

/-- Error-free synchronization corollary: with zero error term and a
`half`-form Grönwall lemma, we recover squared-distance contraction. -/
theorem evi_two_sync_sq_zero_error
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop)
  (Hgr0 : gronwall_exponential_contraction_with_error_half_pred P.lam (0 : ℝ)
    (fun t => d2 (u t) (v t))) :
  (eviSumWithError P u v hu hv geodesicBetween
    ({ η := 0, bound := fun _t => True } : MixedErrorBound X u v)) →
  ContractionPropertySq P u v :=
by
  intro Hsum
  -- Instantiate the general bound with η = 0, then simplify.
  have h := evi_two_sync_sq_with_error P u v hu hv geodesicBetween (0 : ℝ) Hgr0 Hsum
  intro t
  simpa [zero_mul, add_comm, add_left_comm, add_assoc] using h t

end X2

/-- Integrated suite corollary: from weak hypothesis flags and an
equivalence assumption pack for `F := Ent + γ·Dσm` with
`λ_BE := lambdaBE S.base.lam S.eps`, plus a packaged lower bound and a
two‑EVI hypothesis, we obtain the three gradient-flow conclusions. -/
theorem flow_suite_from_packs
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  -- Build the equivalence package from weak hypotheses and the assumption pack
  have G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
    build_plfaEdeEvi_package_weak (FrourioFunctional.F S.func)
      (lambdaBE S.base.lam S.eps) HC SUB Hpack
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
  refine build_EDEEVI_pack_from_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) HC SUB H

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

/-- Step 2 (FG-level wrapper): from analytic flags and a JKO⇒PLFA bridge,
obtain the component predicate `JKO_to_PLFA_pred` for `F := Ent + γ·Dσm`. -/
theorem jko_plfa_pred_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (H : JKO_PLFA_from_analytic_flags (FrourioFunctional.F S.func)) :
  JKO_to_PLFA_pred (FrourioFunctional.F S.func) :=
by
  exact jko_to_plfa_from_flags (FrourioFunctional.F S.func) H A.proper A.lsc A.coercive A.jkoStable

/-- Step 2 (FG-level pack): the same as `jko_plfa_pred_for_FG`, but packaged as
`JKOPLFAAssumptions` for downstream assembly. -/
theorem jko_plfa_pack_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (H : JKO_PLFA_from_analytic_flags (FrourioFunctional.F S.func)) :
  JKOPLFAAssumptions (FrourioFunctional.F S.func) :=
by
  refine build_JKOPLFA_pack_from_flags (FrourioFunctional.F S.func) H A.proper A.lsc A.coercive A.jkoStable

/-- Step 2 (FG-level theorem): from analytic flags and bridges (JKO⇒PLFA and
PLFA⇔EDE), conclude `JKO ⇒ EDE` for `F := Ent + γ·Dσm`. -/
theorem jko_ede_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (Hjko : JKO_PLFA_from_analytic_flags (FrourioFunctional.F S.func))
  (HplfaEde : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  ∀ ρ0 : X, JKO (FrourioFunctional.F S.func) ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ EDE (FrourioFunctional.F S.func) ρ :=
by
  exact jko_to_ede_from_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)
    Hjko HplfaEde A.proper A.lsc A.coercive A.jkoStable A.HC A.SUB

/-- Step 2 (FG-level theorem): from analytic flags and bridges (JKO⇒PLFA,
PLFA⇔EDE, EDE⇔EVI), conclude `JKO ⇒ EVI(λ_eff)` for `F := Ent + γ·Dσm`. -/
theorem jko_evi_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (Hjko : JKO_PLFA_from_analytic_flags (FrourioFunctional.F S.func))
  (HplfaEde : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HedeEvi : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  ∀ ρ0 : X, JKO (FrourioFunctional.F S.func) ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧
    IsEVISolution ({ E := FrourioFunctional.F S.func, lam := lambdaBE S.base.lam S.eps } : EVIProblem X) ρ :=
by
  exact jko_to_evi_from_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)
    Hjko HplfaEde HedeEvi A.proper A.lsc A.coercive A.jkoStable A.HC A.SUB

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
  all_goals exact trivial

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
  refine { plfaEde := plfa_ede_bridge_from_pack (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) Hplfa_ede,
           edeEvi := ede_evi_bridge_from_pack (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) Hede_evi,
           jkoPlfa := jko_plfa_bridge_from_pack (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) Hjko_plfa }

/-- Build `AnalyticBridges` from an equivalence-assumption pack. -/
theorem analytic_bridges_from_equiv_pack
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (H : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  AnalyticBridges (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
by
  refine { plfaEde := plfa_ede_bridge_from_equiv_pack (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) H,
           edeEvi := ede_evi_bridge_from_equiv_pack (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) H,
           jkoPlfa := jko_plfa_bridge_from_equiv_pack (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) H }

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
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hM : MPointZeroOrderBound S.Ssup S.XiNorm)
  (hB : BudgetNonneg S.budget)
  (hg : 0 ≤ S.func.gamma)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S :=
by
  -- Choose λ_eff as the RHS target to satisfy the inequality by reflexivity.
  let lamEff := lambdaBE S.base.lam S.eps
    - S.func.gamma * (S.budget.cStar * S.Ssup ^ (2 : ℕ) + S.budget.cD * S.XiNorm)
  have hDoob : DoobCDShift S.base.lam S.eps (lambdaBE S.base.lam S.eps) := by
    exact ⟨trivial, rfl⟩
  have hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps lamEff S.Ssup S.XiNorm := by
    refine lambdaEffLowerBound_from_doob_mpoint S.func S.budget
      S.base.lam S.eps lamEff S.Ssup S.XiNorm hDoob hM hB hg ?ineq
    -- lamEff ≥ lamEff
    exact le_of_eq rfl
  -- Invoke the pack-based suite with the constructed lower bound.
  have G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps) :=
    build_plfaEdeEvi_package_weak (FrourioFunctional.F S.func)
      (lambdaBE S.base.lam S.eps) HC SUB Hpack
  have suite := gradient_flow_suite S G lamEff hLam Htwo
  simpa using suite

/-- Re-export: gradient-flow equivalence (PLFA = EDE = EVI = JKO). -/
def flow_equivalence {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : Prop :=
  gradient_flow_equiv S

/-- Re-export: effective lambda lower bound statement. -/
def lambda_eff_lower {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : Prop :=
  lambda_eff_lower_bound S

/-- Re-export: two-EVI with external force (squared-distance synchronization). -/
def two_evi_with_force_alias {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : Prop :=
  two_evi_with_force S

/-- Multiscale EVI parameter rule alias (m-dimensional scale composition). -/
def evi_multiscale_rule {m : ℕ}
  (Λ α κ : Fin m → ℝ) (k : Fin m → ℤ) : Prop :=
  multiscale_lambda_rule Λ α κ k

end Frourio
