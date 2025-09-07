import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Semicontinuous
import Frourio.Analysis.PLFA.PLFACore0
import Frourio.Analysis.Slope
import Frourio.Analysis.MinimizingMovement

namespace Frourio

section RealExample
-- Example: Linear geodesic structure on ℝ
def linearGeodesicStructure : GeodesicStructure ℝ where
  γ := fun x y t => (1 - t) * x + t * y
  start_point := fun x y => by simp
  end_point := fun x y => by simp
  geodesic_property := fun x y s t _ _ _ _ => by
    simp only [dist]
    -- Calculate: γ(x,y,s) - γ(x,y,t) = ((1-s)*x + s*y) - ((1-t)*x + t*y)
    --                                 = (t-s)*(x-y)
    have h : (1 - s) * x + s * y - ((1 - t) * x + t * y) = (t - s) * (x - y) := by ring
    rw [h, abs_mul]

end RealExample

section Integration
variable {X : Type*} [PseudoMetricSpace X]

/-- Integration point: Choose between placeholder and real analytic flags. -/
def chooseAnalyticRoute (F : X → ℝ) (lamEff : ℝ) (useReal : Bool) : Prop :=
  if useReal then
    ∃ (_flags : AnalyticFlagsReal X F lamEff), PLFA_EDE_from_real_flags F lamEff
  else
    ∃ (_flags : AnalyticFlags F lamEff), PLFA_EDE_from_analytic_flags F lamEff

/-- Theorem: Both routes lead to PLFA/EDE equivalence (when they exist). -/
theorem both_routes_valid (F : X → ℝ) (lamEff : ℝ) :
    (∃ _real_flags : AnalyticFlagsReal X F lamEff, True) →
    (∃ _placeholder_flags : AnalyticFlags F lamEff, True) →
    (chooseAnalyticRoute F lamEff true ∨ chooseAnalyticRoute F lamEff false) := by
  intro ⟨real_flags, _⟩ ⟨placeholder_flags, _⟩
  -- Choose the placeholder route as default (simpler and always available)
  right
  simp [chooseAnalyticRoute]
  use placeholder_flags
  -- Provide concrete implementation of PLFA_EDE_from_analytic_flags
  exact fun _flags => fun ρ =>
    ⟨-- Direction 1: PLFA → EDE
     plfa_implies_ede F ρ,
     -- Direction 2: EDE → PLFA
     fun hEDE => by
       apply ede_to_plfa_with_gronwall_zero F ρ hEDE
       -- Provide the G0 condition: monotonicity from DiniUpper bounds
       exact fun s hDini t ht => by
         -- φ(τ) = F(ρ(s+τ)) - F(ρ s) is nonincreasing from 0
         -- because DiniUpperE φ ≤ 0 everywhere (from hDini)
         let φ := fun τ => F (ρ (s + τ)) - F (ρ s)
         -- Use Frourio.nonincreasing_of_DiniUpperE_nonpos directly
         have mono_prop := Frourio.nonincreasing_of_DiniUpperE_nonpos φ hDini
         -- Apply monotonicity: φ(t) ≤ φ(0)
         have : φ t ≤ φ 0 := mono_prop 0 t ht
         -- Now rewrite in terms of the original expression
         simp only [φ] at this
         -- this gives us: F (ρ (s + t)) - F (ρ s) ≤ F (ρ (s + 0)) - F (ρ s)
         exact this⟩

end Integration

/-! Real-route bridge builders (exported): provide the `PLFA_EDE_from_real_flags`
and `JKO_PLFA_from_real_flags` predicates directly from the corresponding
implementation lemmas above. These are convenient when a caller expects
the predicate-valued builders rather than the explicit lemmas. -/

section ExportBuilders
variable {X : Type*} [PseudoMetricSpace X]

/-- Exported builder: real flags ⇒ PLFA↔EDE predicate. -/
theorem plfa_ede_from_real_flags_builder (F : X → ℝ) (lamEff : ℝ) :
  PLFA_EDE_from_real_flags (X := X) F lamEff :=
by
  intro flags; exact plfa_ede_from_real_flags_impl (X := X) F lamEff flags

/-- Exported builder: real flags ⇒ JKO→PLFA predicate. -/
theorem jko_plfa_from_real_flags_builder (F : X → ℝ) (lamEff : ℝ) :
  JKO_PLFA_from_real_flags (X := X) F lamEff :=
by
  intro flags; exact jko_plfa_from_real_flags_impl (X := X) F lamEff flags

end ExportBuilders

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

-- Phase 2 (forward) note: axioms are forbidden. Use builder routes
-- like `ede_to_evi_from_flags_builder`/`_auto` to obtain the forward
-- direction from a supplied `EDE_EVI_from_analytic_flags` proof.

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

end X

end Frourio
