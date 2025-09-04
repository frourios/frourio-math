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
  have Hjk : JKO_to_PLFA_pred F := jko_to_plfa_from_flags F Hjko hP hL hC hJ
  rcases Hjk ρ0 hJKO with ⟨ρ, h0, hplfa⟩
  have hPLFA_EDE : ∀ r : ℝ → X, PLFA F r ↔ EDE F r := HplfaEde ⟨hP, hL, hC, HC, SUB⟩
  have hEDE : EDE F ρ := (hPLFA_EDE ρ).mp hplfa
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
