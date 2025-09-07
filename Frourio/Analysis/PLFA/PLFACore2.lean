import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Frourio.Analysis.PLFA.PLFACore1

namespace Frourio

/-!
Bridges part of PLFA/EDE/JKO: EVI-dependent statements and packages.
This file places `[PseudoMetricSpace X]` only where needed.
-/

section X
variable {X : Type*} [PseudoMetricSpace X]

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

end X

end Frourio
