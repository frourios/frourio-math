import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Frourio.Analysis.EVI
import Frourio.Analysis.PLFACore

namespace Frourio

/-!
Bridges part of PLFA/EDE/JKO: EVI-dependent statements and packages.
This file places `[PseudoMetricSpace X]` only where needed.
-/

section X
variable {X : Type*} [PseudoMetricSpace X]

-- EVI-dependent predicates and packages
def EDE_EVI_pred (F : X → ℝ) (lamEff : ℝ) : Prop :=
  ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ

def plfaEdeEviJko_equiv (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ) ∧
  (∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ) ∧
  (∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

structure EquivBuildAssumptions (F : X → ℝ) (lamEff : ℝ) : Prop where
  (plfa_iff_ede : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ)
  (ede_iff_evi : ∀ ρ : ℝ → X,
    EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ)
  (jko_to_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

theorem build_plfaEdeEvi_package (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  And.intro (fun ρ => H.plfa_iff_ede ρ)
    (And.intro (fun ρ => H.ede_iff_evi ρ) (fun ρ0 h => H.jko_to_plfa ρ0 h))

theorem build_plfaEdeEvi_package_weak (F : X → ℝ) (lamEff : ℝ)
  (_HC : HalfConvex F lamEff) (_SUB : StrongUpperBound F)
  (H : EquivBuildAssumptions F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_plfaEdeEvi_package F lamEff H

structure EDEEVIAssumptions (F : X → ℝ) (lamEff : ℝ) : Prop where
  (ede_iff_evi : ∀ ρ : ℝ → X,
    EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ)

theorem ede_evi_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EDE_EVI_pred F lamEff := H.ede_iff_evi

def EDE_EVI_from_analytic_flags (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (HalfConvex F lamEff ∧ StrongUpperBound F) → EDE_EVI_pred F lamEff

/-- Directional bridge (flags → EDE ⇒ EVI). If this holds together with the
reverse direction, it yields `EDE_EVI_from_analytic_flags`. -/
def EDE_to_EVI_from_flags (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (HalfConvex F lamEff ∧ StrongUpperBound F) →
    ∀ ρ : ℝ → X, EDE F ρ → IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ

/-- Directional bridge (flags → EVI ⇒ EDE). Pairs with `EDE_to_EVI_from_flags`
to produce `EDE_EVI_from_analytic_flags`. -/
def EVI_to_EDE_from_flags (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (HalfConvex F lamEff ∧ StrongUpperBound F) →
    ∀ ρ : ℝ → X, IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ → EDE F ρ

/-- Assemble the equivalence builder `EDE_EVI_from_analytic_flags` from the two
directional bridges under the same analytic flags. -/
theorem build_ede_evi_from_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff :=
by
  intro hFlags; intro ρ; constructor
  · intro hEDE; exact Hfwd hFlags ρ hEDE
  · intro hEVI; exact Hrev hFlags ρ hEVI

/-- From `AnalyticFlags`, obtain the predicate-level equivalence `EDE_EVI_pred`
provided the two directional bridges hold under the (weaker) core flags
`HalfConvex` and `StrongUpperBound`. -/
theorem ede_evi_pred_from_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff) :
  EDE_EVI_pred F lamEff :=
by
  -- Build the equivalence builder from the directional bridges, then apply it
  -- directly to the core flags contained in `A`.
  intro ρ
  exact ((build_ede_evi_from_directional_bridges F lamEff Hfwd Hrev) ⟨A.HC, A.SUB⟩) ρ

/-- Package form: build `EDEEVIAssumptions` from `AnalyticFlags` and the two
directional bridges. This is convenient for downstream pack-based assembly. -/
theorem build_EDEEVI_pack_from_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff) :
  EDEEVIAssumptions F lamEff :=
by
  have Hpred : EDE_EVI_pred F lamEff :=
    ede_evi_pred_from_directional_bridges F lamEff A Hfwd Hrev
  -- Package the pointwise equivalence as `EDEEVIAssumptions`.
  refine ⟨?_⟩; intro ρ; exact Hpred ρ

/-- Convenience: extract each implication directly from the builder and flags. -/
theorem ede_to_evi_from_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ : ℝ → X, EDE F ρ → IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
by
  intro ρ hEDE; exact ((H ⟨HC, SUB⟩) ρ).mp hEDE

/-- Convenience: extract the reverse implication from the builder and flags. -/
theorem evi_to_ede_from_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ : ℝ → X, IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ → EDE F ρ :=
by
  intro ρ hEVI; exact ((H ⟨HC, SUB⟩) ρ).mpr hEVI

-- (moved below after `build_package_from_analytic_flags` to satisfy dependency order)

theorem ede_evi_bridge_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EDE_EVI_from_analytic_flags F lamEff :=
by intro _flags; exact H.ede_iff_evi

theorem plfa_ede_bridge_from_equiv_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : PLFA_EDE_from_analytic_flags F lamEff :=
by intro _flags; exact H.plfa_iff_ede

theorem ede_evi_bridge_from_equiv_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : EDE_EVI_from_analytic_flags F lamEff :=
by intro _flags; exact H.ede_iff_evi

theorem jko_plfa_bridge_from_equiv_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : JKO_PLFA_from_analytic_flags F :=
by intro _flags; exact H.jko_to_plfa

theorem ede_evi_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
  H ⟨HC, SUB⟩

/- Materialize `EDE_EVI_pred` from core analytic flags using the A/B
directional bridges (`EDE_to_EVI_from_flags`, `EVI_to_EDE_from_flags`). -/
theorem ede_evi_pred_from_core_flags (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff) :
  EDE_EVI_pred F lamEff :=
  ede_evi_pred_from_directional_bridges F lamEff A Hfwd Hrev

/-- Compatibility alias: recover the old route from flags via a builder. -/
theorem ede_evi_pred_from_core_flags_via_builder (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) : EDE_EVI_pred F lamEff :=
by
  intro ρ; exact (H ⟨A.HC, A.SUB⟩) ρ

theorem build_EDEEVI_pack_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags F lamEff) : EDEEVIAssumptions F lamEff :=
by refine ⟨?_⟩; exact ede_evi_equiv_from_flags F lamEff HC SUB H

-- Combining analytic flags into component predicates
theorem component_predicates_from_analytic_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) : PLFA_EDE_pred F ∧ EDE_EVI_pred F lamEff ∧ JKO_to_PLFA_pred F :=
by
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · exact H1 ⟨A.proper, A.lsc, A.coercive, A.HC, A.SUB⟩
  · exact H2 ⟨A.HC, A.SUB⟩
  · exact H3 ⟨A.proper, A.lsc, A.coercive, A.jkoStable⟩

structure GlobalSufficientPack (F : X → ℝ) (lamEff : ℝ) : Prop where
  (HC : HalfConvex F lamEff)
  (SUB : StrongUpperBound F)
  (components : PLFA_EDE_pred F ∧ EDE_EVI_pred F lamEff ∧ JKO_to_PLFA_pred F)

theorem global_sufficient_pack_from_analytic_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) : GlobalSufficientPack F lamEff :=
by
  rcases component_predicates_from_analytic_flags F lamEff H1 H2 H3 A with ⟨h1, htmp⟩
  rcases htmp with ⟨h2, h3⟩
  exact ⟨A.HC, A.SUB, And.intro h1 (And.intro h2 h3)⟩

theorem build_package_from_global (F : X → ℝ) (lamEff : ℝ)
  (H : GlobalSufficientPack F lamEff) : plfaEdeEviJko_equiv F lamEff :=
by
  rcases H.components with ⟨h1, htmp⟩; rcases htmp with ⟨h2, h3⟩
  have Hp : EquivBuildAssumptions F lamEff :=
    { plfa_iff_ede := h1, ede_iff_evi := h2, jko_to_plfa := h3 }
  exact build_plfaEdeEvi_package F lamEff Hp

theorem build_package_from_analytic_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_package_from_global F lamEff
    (global_sufficient_pack_from_analytic_flags F lamEff H1 H2 H3 A)

/-- Materialize the full equivalence `PLFA = EDE = EVI = JKO` from core
analytic flags and the three builder routes, without additional bridges. -/
theorem plfaEdeEviJko_equiv_from_core_flags (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F) :
  plfaEdeEviJko_equiv F lamEff :=
by
  exact build_package_from_analytic_flags F lamEff H1 H2 H3 A

/-- Build the full equivalence from analytic flags, using `PLFA_EDE` and `JKO_PLFA`
builders, and directional bridges to assemble `EDE_EVI`. -/
theorem build_package_from_flags_and_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff)
  (HjkoPlfa : JKO_PLFA_from_analytic_flags F) : plfaEdeEviJko_equiv F lamEff :=
by
  -- Assemble the EDE⇔EVI builder from directional bridges
  have HE : EDE_EVI_from_analytic_flags F lamEff :=
    build_ede_evi_from_directional_bridges F lamEff Hfwd Hrev
  -- Use the generic builder route from analytic flags
  exact build_package_from_analytic_flags F lamEff HplfaEde HE HjkoPlfa A

/-- Global sufficient pack from flags and directional bridges. -/
theorem global_sufficient_pack_from_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff)
  (HjkoPlfa : JKO_PLFA_from_analytic_flags F) : GlobalSufficientPack F lamEff :=
by
  rcases A with ⟨hP, hL, hC, HC, SUB, hJ⟩
  -- Obtain component predicates
  have h1 : PLFA_EDE_pred F := HplfaEde ⟨hP, hL, hC, HC, SUB⟩
  have HE : EDE_EVI_from_analytic_flags F lamEff :=
    build_ede_evi_from_directional_bridges F lamEff Hfwd Hrev
  have h2 : EDE_EVI_pred F lamEff := HE ⟨HC, SUB⟩
  have h3 : JKO_to_PLFA_pred F := HjkoPlfa ⟨hP, hL, hC, hJ⟩
  exact ⟨HC, SUB, And.intro h1 (And.intro h2 h3)⟩

/-- Derive the forward directional bridge from a pointwise `EDE ⇔ EVI` predicate. -/
theorem ede_to_evi_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : EDE_to_EVI_from_flags F lamEff :=
by
  intro _flags ρ hEDE; exact (Hpred ρ).mp hEDE

/-- Derive the reverse directional bridge from a pointwise `EDE ⇔ EVI` predicate. -/
theorem evi_to_ede_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : EVI_to_EDE_from_flags F lamEff :=
by
  intro _flags ρ hEVI; exact (Hpred ρ).mpr hEVI

/-- Directional bridges from an `EDEEVIAssumptions` pack (ignores the flags). -/
theorem ede_to_evi_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EDE_to_EVI_from_flags F lamEff :=
by
  intro _flags ρ hEDE; exact (H.ede_iff_evi ρ).mp hEDE

theorem evi_to_ede_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EVI_to_EDE_from_flags F lamEff :=
by
  intro _flags ρ hEVI; exact (H.ede_iff_evi ρ).mpr hEVI

/-- Directional bridges from an `EDE_EVI_from_analytic_flags` builder via flags. -/
theorem ede_to_evi_from_flags_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  EDE_to_EVI_from_flags F lamEff :=
by
  intro _flags ρ hEDE; exact ((H ⟨HC, SUB⟩) ρ).mp hEDE

theorem evi_to_ede_from_flags_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  EVI_to_EDE_from_flags F lamEff :=
by
  intro _flags ρ hEVI; exact ((H ⟨HC, SUB⟩) ρ).mpr hEVI

/-- Tie the flags-directional bridge to a generic EVI-side forward bridge predicate. -/
theorem ede_to_evi_from_evi_pred (F : X → ℝ) (lamEff : ℝ)
  (H : Frourio.EVIBridgeForward (fun F ρ => EDE F ρ) F lamEff) :
  EDE_to_EVI_from_flags F lamEff :=
by
  intro _flags ρ hEDE; exact H ρ hEDE

/-- Tie the flags-directional bridge to a generic EVI-side backward bridge predicate. -/
theorem evi_to_ede_from_evi_pred (F : X → ℝ) (lamEff : ℝ)
  (H : Frourio.EVIBridgeBackward (fun F ρ => EDE F ρ) F lamEff) :
  EVI_to_EDE_from_flags F lamEff :=
by
  intro _flags ρ hEVI; exact H ρ hEVI

/-- Fully build `EDE_EVI_from_analytic_flags` from EVI‑side forward/backward
bridges specialized to `P := EDE`. The flags are not used at this phase
but are kept to match the target API. -/
theorem ede_evi_from_evi_bridges (F : X → ℝ) (lamEff : ℝ)
  (HF : Frourio.EVIBridgeForward (fun F ρ => EDE F ρ) F lamEff)
  (HB : Frourio.EVIBridgeBackward (fun F ρ => EDE F ρ) F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff :=
by
  intro _flags ρ; constructor
  · intro hEDE; exact HF ρ hEDE
  · intro hEVI; exact HB ρ hEVI

/-- Variant: build `EDE_EVI_from_analytic_flags` from an EVI‑side equivalence
bridge, i.e. both directions bundled together. -/
theorem ede_evi_from_evi_equiv_bridge (F : X → ℝ) (lamEff : ℝ)
  (H : Frourio.EVIEquivBridge (fun F ρ => EDE F ρ) F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff :=
by
  rcases H with ⟨HF, HB⟩
  exact ede_evi_from_evi_bridges F lamEff HF HB

/-- Produce the EVI‑side forward bridge instance from the builder and core flags. -/
theorem evi_forward_bridge_from_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  Frourio.EVIBridgeForward (fun F ρ => EDE F ρ) F lamEff :=
by
  intro ρ hEDE; exact ((H ⟨HC, SUB⟩) ρ).mp hEDE

/-- Produce the EVI‑side backward bridge instance from the builder and core flags. -/
theorem evi_backward_bridge_from_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  Frourio.EVIBridgeBackward (fun F ρ => EDE F ρ) F lamEff :=
by
  intro ρ hEVI; exact ((H ⟨HC, SUB⟩) ρ).mpr hEVI

/-- Concrete EVI‑side forward bridge predicate specialized to `P := EDE`. -/
def EDE_to_EVI_concrete (F : X → ℝ) (lamEff : ℝ) : Prop :=
  Frourio.EVIBridgeForward (fun F ρ => EDE F ρ) F lamEff

/-- Concrete EVI‑side backward bridge predicate specialized to `P := EDE`. -/
def EVI_to_EDE_concrete (F : X → ℝ) (lamEff : ℝ) : Prop :=
  Frourio.EVIBridgeBackward (fun F ρ => EDE F ρ) F lamEff

/-- Use the concrete EVI‑side bridges to produce the flags‑builder `EDE_EVI_from_analytic_flags`. -/
theorem ede_evi_from_concrete_bridges (F : X → ℝ) (lamEff : ℝ)
  (HF : EDE_to_EVI_concrete F lamEff)
  (HB : EVI_to_EDE_concrete F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff :=
by
  -- delegate to the generic specialization already provided
  exact ede_evi_from_evi_bridges F lamEff HF HB

/-- Turn a concrete forward bridge into the flags‑directional bridge. -/
theorem ede_to_evi_from_concrete (F : X → ℝ) (lamEff : ℝ)
  (HF : EDE_to_EVI_concrete F lamEff) :
  EDE_to_EVI_from_flags F lamEff :=
  ede_to_evi_from_evi_pred F lamEff HF

/-- Turn a concrete backward bridge into the flags‑directional bridge. -/
theorem evi_to_ede_from_concrete (F : X → ℝ) (lamEff : ℝ)
  (HB : EVI_to_EDE_concrete F lamEff) :
  EVI_to_EDE_from_flags F lamEff :=
  evi_to_ede_from_evi_pred F lamEff HB

/-- Obtain a concrete forward bridge `EDE → EVI` from a pointwise equivalence predicate. -/
theorem ede_to_evi_concrete_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) :
  EDE_to_EVI_concrete F lamEff :=
by
  intro ρ hEDE; exact (Hpred ρ).mp hEDE

/-- Obtain a concrete backward bridge `EVI → EDE` from a pointwise equivalence predicate. -/
theorem evi_to_ede_concrete_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) :
  EVI_to_EDE_concrete F lamEff :=
by
  intro ρ hEVI; exact (Hpred ρ).mpr hEVI

/-- Concrete bridges from an `EDEEVIAssumptions` pack. -/
theorem ede_to_evi_concrete_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) :
  EDE_to_EVI_concrete F lamEff :=
by
  intro ρ hEDE; exact (H.ede_iff_evi ρ).mp hEDE

theorem evi_to_ede_concrete_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) :
  EVI_to_EDE_concrete F lamEff :=
by
  intro ρ hEVI; exact (H.ede_iff_evi ρ).mpr hEVI

/-- Concrete bridges from an equivalence package `plfaEdeEviJko_equiv`. -/
theorem ede_to_evi_concrete_from_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) :
  EDE_to_EVI_concrete F lamEff :=
by
  intro ρ hEDE; exact ((G.2.1) ρ).mp hEDE

theorem evi_to_ede_concrete_from_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) :
  EVI_to_EDE_concrete F lamEff :=
by
  intro ρ hEVI; exact ((G.2.1) ρ).mpr hEVI

/-- Supply a concrete forward bridge from analytic flags and the
`EDE_EVI_from_analytic_flags` builder. -/
theorem ede_to_evi_concrete_from_flags (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  EDE_to_EVI_concrete F lamEff :=
by
  -- Use the forward bridge obtained from the builder and core flags.
  exact evi_forward_bridge_from_builder F lamEff H A.HC A.SUB

/-- Supply a concrete backward bridge from analytic flags and the
`EDE_EVI_from_analytic_flags` builder. -/
theorem evi_to_ede_concrete_from_flags (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  EVI_to_EDE_concrete F lamEff :=
by
  -- Use the backward bridge obtained from the builder and core flags.
  exact evi_backward_bridge_from_builder F lamEff H A.HC A.SUB

/-- Final assembly route: if a global equivalence package is available,
it induces the desired builder `EDE_EVI_from_analytic_flags` outright. -/
theorem ede_evi_from_analytic_flags_via_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff :=
by
  intro _flags ρ; exact (G.2.1 ρ)

/-- Final assembly route: from concrete EVI‑side bridges (both directions),
obtain the builder `EDE_EVI_from_analytic_flags`. -/
theorem ede_evi_from_analytic_flags_final (F : X → ℝ) (lamEff : ℝ)
  (HF : EDE_to_EVI_concrete F lamEff)
  (HB : EVI_to_EDE_concrete F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff :=
  ede_evi_from_concrete_bridges F lamEff HF HB

/-! A compact notation for the concrete forward/backward bridges. -/

def HF (F : X → ℝ) (lamEff : ℝ) : Prop := EDE_to_EVI_concrete F lamEff
def HB (F : X → ℝ) (lamEff : ℝ) : Prop := EVI_to_EDE_concrete F lamEff

/-- Build `HF` from a pointwise equivalence predicate. -/
theorem HF_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : HF F lamEff :=
  ede_to_evi_concrete_from_pred F lamEff Hpred

/-- Build `HB` from a pointwise equivalence predicate. -/
theorem HB_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : HB F lamEff :=
  evi_to_ede_concrete_from_pred F lamEff Hpred

/-- Build `HF` from an `EDEEVIAssumptions` pack. -/
theorem HF_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : HF F lamEff :=
  ede_to_evi_concrete_from_pack F lamEff H

/-- Build `HB` from an `EDEEVIAssumptions` pack. -/
theorem HB_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : HB F lamEff :=
  evi_to_ede_concrete_from_pack F lamEff H

/-- Build `HF` from a global equivalence package. -/
theorem HF_from_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) : HF F lamEff :=
  ede_to_evi_concrete_from_global F lamEff G

/-- Build `HB` from a global equivalence package. -/
theorem HB_from_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) : HB F lamEff :=
  evi_to_ede_concrete_from_global F lamEff G

/-- Build `HF` from analytic flags and a builder. -/
theorem HF_from_flags_builder (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) : HF F lamEff :=
  ede_to_evi_concrete_from_flags F lamEff A H

/-- Build `HB` from analytic flags and a builder. -/
theorem HB_from_flags_builder (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) : HB F lamEff :=
  evi_to_ede_concrete_from_flags F lamEff A H

/-- If both `HF` and `HB` hold, assemble the final builder. -/
theorem ede_evi_builder_from_HF_HB (F : X → ℝ) (lamEff : ℝ)
  (hF : HF F lamEff) (hB : HB F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff :=
  ede_evi_from_analytic_flags_final F lamEff hF hB

/-- Shortcut input for building `EDE_EVI_from_analytic_flags`:
either a global equivalence pack, or both concrete bridges. -/
def EDE_EVI_short_input (F : X → ℝ) (lamEff : ℝ) : Prop :=
  plfaEdeEviJko_equiv F lamEff ∨ (EDE_to_EVI_concrete F lamEff ∧ EVI_to_EDE_concrete F lamEff)

/-- Build `EDE_EVI_from_analytic_flags` from the shortest available input. -/
theorem ede_evi_from_short_input (F : X → ℝ) (lamEff : ℝ)
  (Hin : EDE_EVI_short_input F lamEff) : EDE_EVI_from_analytic_flags F lamEff :=
by
  rcases Hin with h | h
  · exact ede_evi_from_analytic_flags_via_global F lamEff h
  · exact ede_evi_from_analytic_flags_final F lamEff h.1 h.2

/-- From a pointwise `EDE_EVI_pred`, directly build the flags‑builder by
materializing both concrete bridges then assembling them. -/
theorem ede_evi_from_pred_short (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : EDE_EVI_from_analytic_flags F lamEff :=
by
  have HF : EDE_to_EVI_concrete F lamEff := ede_to_evi_concrete_from_pred F lamEff Hpred
  have HB : EVI_to_EDE_concrete F lamEff := evi_to_ede_concrete_from_pred F lamEff Hpred
  exact ede_evi_from_analytic_flags_final F lamEff HF HB

/-- From an `EDEEVIAssumptions` pack (i.e., EDE⇔EVI pointwise), build the
flags‑builder. -/
theorem ede_evi_from_pack_short (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EDE_EVI_from_analytic_flags F lamEff :=
by
  have HF : EDE_to_EVI_concrete F lamEff := ede_to_evi_concrete_from_pack F lamEff H
  have HB : EVI_to_EDE_concrete F lamEff := evi_to_ede_concrete_from_pack F lamEff H
  exact ede_evi_from_analytic_flags_final F lamEff HF HB

structure AnalyticBridges (F : X → ℝ) (lamEff : ℝ) : Prop where
  (plfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (edeEvi : EDE_EVI_from_analytic_flags F lamEff)
  (jkoPlfa : JKO_PLFA_from_analytic_flags F)

theorem build_package_from_flags_and_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff) (B : AnalyticBridges F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_package_from_analytic_flags F lamEff
    B.plfaEde B.edeEvi B.jkoPlfa A

theorem plfaEdeEviJko_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_package_from_analytic_flags F lamEff
    H1 H2 H3 A

/-- Assemble a `GlobalSufficientPack` directly from core flags and an
`EDEEVIAssumptions` pack (EDE ⇔ EVI), alongside the non-metric builders. -/
theorem global_sufficient_pack_from_flags_and_ede_evi_pack (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (HedeEviPack : EDEEVIAssumptions F lamEff)
  (HjkoPlfa : JKO_PLFA_from_analytic_flags F) : GlobalSufficientPack F lamEff :=
by
  -- Build each component predicate from the supplied pieces
  have h1 : PLFA_EDE_pred F := HplfaEde ⟨A.proper, A.lsc, A.coercive, A.HC, A.SUB⟩
  have h2 : EDE_EVI_pred F lamEff := ede_evi_from_pack F lamEff HedeEviPack
  have h3 : JKO_to_PLFA_pred F := HjkoPlfa ⟨A.proper, A.lsc, A.coercive, A.jkoStable⟩
  exact ⟨A.HC, A.SUB, And.intro h1 (And.intro h2 h3)⟩

/-- Build the full equivalence from flags, EDE⇔EVI pack, and non-metric builders. -/
theorem build_package_from_flags_and_ede_evi_pack (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (HedeEviPack : EDEEVIAssumptions F lamEff)
  (HjkoPlfa : JKO_PLFA_from_analytic_flags F) : plfaEdeEviJko_equiv F lamEff :=
by
  exact build_package_from_global F lamEff
    (global_sufficient_pack_from_flags_and_ede_evi_pack F lamEff A HplfaEde HedeEviPack HjkoPlfa)

-- JKO ⇒ EDE/EVI from flags

theorem jko_to_evi_from_flags (F : X → ℝ) (lamEff : ℝ)
  (Hjko : JKO_PLFA_from_analytic_flags F)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (HedeEvi : EDE_EVI_from_analytic_flags F lamEff)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F) (hJ : JKOStable F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧
    IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
by
  intro ρ0 hJKO
  -- First produce an EDE evolution via the core non-metric route.
  rcases jko_to_ede_from_flags F lamEff Hjko HplfaEde hP hL hC hJ HC SUB ρ0 hJKO with ⟨ρ, h0, hEDE⟩
  -- Turn EDE into EVI using the EDE⇔EVI builder under core flags.
  have hEDE_EVI : ∀ r : ℝ → X,
      EDE F r ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) r := HedeEvi ⟨HC, SUB⟩
  exact ⟨ρ, h0, (hEDE_EVI ρ).mp hEDE⟩

-- Two-EVI with forcing and consequences
def TwoEVIWithForce (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∃ (hu : IsEVISolution P u) (hv : IsEVISolution P v)
    (geodesicBetween : Prop) (hR : MixedErrorBound X u v),
      eviSumWithError P u v hu hv geodesicBetween hR ∧
      (gronwall_exponential_contraction_with_error_half_pred P.lam hR.η
        (fun t => d2 (u t) (v t)) →
        ContractionPropertySqWithError P u v hR.η)

/-- Shared geodesic uniform evaluation predicate specialized to `P`. -/
def GeodesicUniformEvalFor (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  Frourio.GeodesicUniformEval P u v

/-- Variant of `TwoEVIWithForce` that uses the shared geodesic predicate. -/
def TwoEVIWithForceShared (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∃ (hu : IsEVISolution P u) (hv : IsEVISolution P v)
    (G : GeodesicUniformEvalFor P u v) (hR : MixedErrorBound X u v),
      (let geod : Prop := GeodesicUniformEvalFor P u v
       let _hg : geod := G
       eviSumWithError P u v hu hv geod hR) ∧
      (gronwall_exponential_contraction_with_error_half_pred P.lam hR.η
        (fun t => d2 (u t) (v t)) →
        ContractionPropertySqWithError P u v hR.η)

/-- From the shared predicate variant, recover the original `TwoEVIWithForce`. -/
theorem twoEVIShared_to_plain (P : EVIProblem X) (u v : ℝ → X) :
  TwoEVIWithForceShared P u v → TwoEVIWithForce P u v :=
by
  intro H; rcases H with ⟨hu, hv, _G, hR, Hsum, Himp⟩
  refine ⟨hu, hv, (GeodesicUniformEvalFor P u v), hR, ?_, Himp⟩
  simpa using Hsum

theorem twoEVIWithForce_to_distance (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForce P u v)
  (Hbridge : ∀ η : ℝ, HbridgeWithError P u v η) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError P u v η :=
by
  rcases H with ⟨hu, hv, geodesicBetween, hR, _Hsum, Himp⟩
  refine ⟨hR.η, ?_⟩
  intro Hgr
  have Hsq : ContractionPropertySqWithError P u v hR.η := Himp Hgr
  exact bridge_with_error P u v hR.η (Hbridge hR.η) Hsq

/-- Shared variant: distance synchronization from `TwoEVIWithForceShared`. -/
theorem twoEVIWithForceShared_to_distance (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForceShared P u v)
  (Hbridge : ∀ η : ℝ, HbridgeWithError P u v η) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError P u v η :=
by
  rcases (twoEVIShared_to_plain P u v H) with Hplain
  exact twoEVIWithForce_to_distance P u v Hplain Hbridge

theorem twoEVIWithForce_to_distance_closed (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForce P u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t)))
  (Hbridge : ∀ η : ℝ, HbridgeWithError P u v η) :
  ∃ η : ℝ, ContractionPropertyWithError P u v η :=
by
  rcases H with ⟨hu, hv, geodesicBetween, hR, _Hsum, Himp⟩
  refine ⟨hR.η, ?_⟩
  have Hsq : ContractionPropertySqWithError P u v hR.η := Himp (Hgr_all hR.η)
  exact bridge_with_error P u v hR.η (Hbridge hR.η) Hsq

/-- Shared variant: closed distance synchronization from `TwoEVIWithForceShared`. -/
theorem twoEVIWithForceShared_to_distance_closed (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForceShared P u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t)))
  (Hbridge : ∀ η : ℝ, HbridgeWithError P u v η) :
  ∃ η : ℝ, ContractionPropertyWithError P u v η :=
by
  rcases (twoEVIShared_to_plain P u v H) with Hplain
  exact twoEVIWithForce_to_distance_closed P u v Hplain Hgr_all Hbridge

/-- Two‑EVI with force: distance synchronization using the concrete with‑error
bridge from `EVI.lean` (no external bridge hypothesis needed). -/
theorem twoEVIWithForce_to_distance_concrete (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForce P u v) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError P u v η :=
by
  rcases H with ⟨hu, hv, geodesicBetween, hR, Hsum, _Himp⟩
  refine ⟨hR.η, ?_⟩
  intro Hgr
  -- Use the end‑to‑end concrete synchronization theorem from EVI.
  exact evi_synchronization_with_error_thm_concrete P u v hu hv geodesicBetween hR Hsum Hgr

/-- Shared variant: distance synchronization using the concrete with‑error bridge
from `EVI.lean` (no external bridge hypothesis needed). -/
theorem twoEVIWithForceShared_to_distance_concrete (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForceShared P u v) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError P u v η :=
by
  have Hplain : TwoEVIWithForce P u v := twoEVIShared_to_plain P u v H
  exact twoEVIWithForce_to_distance_concrete P u v Hplain

/-- Closed form: if a Grönwall predicate holds for all `η`, then the
two‑EVI with force yields a distance synchronization bound via the concrete bridge. -/
theorem twoEVIWithForce_to_distance_concrete_closed (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForce P u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError P u v η :=
by
  rcases twoEVIWithForce_to_distance_concrete P u v H with ⟨η, Himp⟩
  exact ⟨η, Himp (Hgr_all η)⟩

/-- Shared variant: closed form of the concrete with‑error synchronization. -/
theorem twoEVIWithForceShared_to_distance_concrete_closed (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForceShared P u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError P u v η :=
by
  have Hplain : TwoEVIWithForce P u v := twoEVIShared_to_plain P u v H
  exact twoEVIWithForce_to_distance_concrete_closed P u v Hplain Hgr_all

-- Convenience equivalences
theorem ede_iff_evi (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ : ℝ → X) :
  EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ := (G.2.1) ρ

theorem evi_iff_plfa (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ : ℝ → X) :
  IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ ↔ PLFA F ρ := by
  have h1 := (G.1) ρ; have h2 := (G.2.1) ρ; exact (h1.trans h2).symm

theorem jko_to_evi (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ0 : X) :
  JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
by
  intro hJ; rcases (G.2.2) ρ0 hJ with ⟨ρ, h0, hplfa⟩
  exact ⟨ρ, h0, (evi_iff_plfa F lamEff G ρ).mpr hplfa⟩

end X

end Frourio
