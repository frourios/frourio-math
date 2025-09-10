import Mathlib.Topology.MetricSpace.Basic
import Frourio.Geometry.FGCore
import Frourio.Analysis.PLFA.PLFA
import Frourio.Analysis.DoobTransform
import Frourio.Analysis.FrourioFunctional
import Frourio.Geometry.GradientFlowFramework

/-!
# FG Theorems: Statement-only wrappers

This module provides statement-level definitions (Prop-valued) that tie
the FG core data to the existing analysis layer (EVI/Doob/Mosco), as
outlined in design phase G2. Proofs and quantitative details are left to
later phases; here we fix API shapes and dependencies.
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

/-- Placeholder coefficient `c_* (σ)` controlling the `‖S_m‖_∞^2` contribution. -/
noncomputable def cStarCoeff (_σ : ℝ) : ℝ := 0

/-- Placeholder coefficient `c_D (σ)` controlling the `‖Ξ_m‖` contribution. -/
noncomputable def cDCoeff (_σ : ℝ) : ℝ := 0

/-- Build the analysis‑layer budget from the m‑point coefficients at scale `σ`. -/
noncomputable def budgetFromSigma (σ : ℝ) : ConstantBudget :=
  ⟨cStarCoeff σ, cDCoeff σ⟩

/-- Boolean toggle for commutative-design simplification at scale `σ`.
When `comm = true`, the `c_*` contribution is set to `0` in the assembled budget. -/
noncomputable def budgetFromSigmaWithFlag (σ : ℝ) (comm : Bool) : ConstantBudget :=
  ⟨if comm then 0 else cStarCoeff σ, cDCoeff σ⟩

lemma budgetFromSigmaWithFlag_comm_true (σ : ℝ) :
  (budgetFromSigmaWithFlag σ true).cStar = 0 ∧ (budgetFromSigmaWithFlag σ true).cD = cDCoeff σ := by
  simp [budgetFromSigmaWithFlag]

lemma budgetFromSigmaWithFlag_comm_false (σ : ℝ) :
  (budgetFromSigmaWithFlag σ false).cStar = (budgetFromSigma σ).cStar ∧
  (budgetFromSigmaWithFlag σ false).cD = (budgetFromSigma σ).cD := by
  simp [budgetFromSigmaWithFlag, budgetFromSigma]

/-- Statement-level link: under a commutative-design regime, one may set
`c_* (σ) = 0` in the budget assembly. This is kept as a Prop-level lemma for
downstream use; quantitative proofs are deferred. -/
lemma budget_commutative_simplify (σ : ℝ) :
  ∃ B : ConstantBudget, B.cStar = 0 ∧ B.cD = cDCoeff σ := by
  -- Choose the boolean-flagged budget with `comm = true`.
  refine ⟨budgetFromSigmaWithFlag σ true, ?_, ?_⟩
  · simpa using (budgetFromSigmaWithFlag_comm_true σ).1
  · simpa using (budgetFromSigmaWithFlag_comm_true σ).2

/-- A simple nontrivial model for the m‑point coefficients.
Tunable gains `k*`, `kD` produce nonnegative coefficients depending on `σ`. -/
noncomputable def cStarCoeff_model (kStar : ℝ) (σ : ℝ) : ℝ := kStar * σ ^ (2 : ℕ)
noncomputable def cDCoeff_model (kD : ℝ) (σ : ℝ) : ℝ := kD * |σ|

lemma cStarCoeff_model_nonneg {kStar σ : ℝ} (hk : 0 ≤ kStar) :
  0 ≤ cStarCoeff_model kStar σ := by
  unfold cStarCoeff_model
  have hσ2 : 0 ≤ σ ^ (2 : ℕ) := by
    -- σ^2 ≥ 0 on ℝ
    simpa [pow_two] using mul_self_nonneg σ
  exact mul_nonneg hk hσ2

lemma cDCoeff_model_nonneg {kD σ : ℝ} (hk : 0 ≤ kD) :
  0 ≤ cDCoeff_model kD σ := by
  unfold cDCoeff_model
  have : 0 ≤ |σ| := abs_nonneg σ
  exact mul_nonneg hk this

/-- Assemble a budget from the nontrivial model. -/
noncomputable def budgetFromSigmaModel (kStar kD σ : ℝ) : ConstantBudget :=
  ⟨cStarCoeff_model kStar σ, cDCoeff_model kD σ⟩

lemma budgetFromSigmaModel_nonneg {kStar kD σ : ℝ}
  (hks : 0 ≤ kStar) (hkd : 0 ≤ kD) :
  0 ≤ (budgetFromSigmaModel kStar kD σ).cStar ∧ 0 ≤ (budgetFromSigmaModel kStar kD σ).cD := by
  constructor
  · simpa [budgetFromSigmaModel] using cStarCoeff_model_nonneg (kStar := kStar) (σ := σ) hks
  · simpa [budgetFromSigmaModel] using cDCoeff_model_nonneg (kD := kD) (σ := σ) hkd

/-- Supply an explicit `lambdaEffLowerBound` using the model budget.
The witness is the canonical right-hand side value. -/
theorem lambdaEffLowerBound_from_sigma_model {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (lam eps Ssup XiNorm σ kStar kD : ℝ) :
  lambdaEffLowerBound A (budgetFromSigmaModel kStar kD σ) lam eps
    (lambdaBE lam eps
      - A.gamma * ((budgetFromSigmaModel kStar kD σ).cStar * Ssup ^ (2 : ℕ)
                   + (budgetFromSigmaModel kStar kD σ).cD * XiNorm))
    Ssup XiNorm := by
  -- Directly use the theoremized wrapper with equality.
  apply lambdaEffLowerBound_thm
  rfl

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

end Frourio
