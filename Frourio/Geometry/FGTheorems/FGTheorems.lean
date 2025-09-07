import Mathlib.Topology.MetricSpace.Basic
import Frourio.Geometry.FGCore
import Frourio.Analysis.PLFA.PLFA
import Frourio.Analysis.DoobTransform
import Frourio.Analysis.FrourioFunctional
import Frourio.Geometry.GradientFlowFramework
import Frourio.Geometry.FGTheorems.FGTheoremsCore0

namespace Frourio

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
