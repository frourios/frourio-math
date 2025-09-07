import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Frourio.Analysis.PLFA.PLFACore2

namespace Frourio

section X
variable {X : Type*} [PseudoMetricSpace X]

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
