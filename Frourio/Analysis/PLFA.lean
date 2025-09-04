import Mathlib.Data.Real.Basic
import Frourio.Analysis.EVI

namespace Frourio

/-!
FG8 A2: PLFA/EDE/JKO predicates and equivalence skeleton (restored)

This module provides lightweight, Prop-valued predicates for the minimum
action principle (PLFA), Energy Dissipation Equality (EDE), and the JKO
minimizing movement scheme, together with statement-level equivalence
packaging and builders used by the FG layer.
-/

section X
variable {X : Type*} [PseudoMetricSpace X]

/-- PLFA predicate (monotone form): along `ρ`, the functional is nonincreasing
in time. -/
def PLFA (F : X → ℝ) (ρ : ℝ → X) : Prop := ∀ ⦃s t : ℝ⦄, s ≤ t → F (ρ t) ≤ F (ρ s)

/-- Action placeholder: currently an alias for `PLFA` to stabilize the API. -/
def Action (F : X → ℝ) (ρ : ℝ → X) : Prop := PLFA F ρ

/-- EDE predicate (minimalist): upper Dini derivative of `F ∘ ρ` is ≤ 0. -/
def EDE (F : X → ℝ) (ρ : ℝ → X) : Prop := ∀ t : ℝ, DiniUpper (fun τ => F (ρ τ)) t ≤ 0

/-- JKO predicate (skeleton): existence of a curve from `ρ0` with energy
controlled by the initial energy. -/
def JKO (F : X → ℝ) (ρ0 : X) : Prop := ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ ∀ t : ℝ, F (ρ t) ≤ F ρ0

/-- Placeholder analytic flags used across builders. -/
def HalfConvex (F : X → ℝ) (_lamEff : ℝ) : Prop := True
def StrongUpperBound (F : X → ℝ) : Prop := True
def Proper (F : X → ℝ) : Prop := True
def LowerSemicontinuous (F : X → ℝ) : Prop := True
def Coercive (F : X → ℝ) : Prop := True
def JKOStable (F : X → ℝ) : Prop := True

/-- Statement-level equivalence packaging PLFA, EDE, EVI(λ_eff), and JKO⇒PLFA. -/
def plfaEdeEviJko_equiv (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ) ∧
  (∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ) ∧
  (∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

/-- Assumption pack providing the three core components of the equivalence. -/
structure EquivBuildAssumptions (F : X → ℝ) (lamEff : ℝ) : Prop where
  (plfa_iff_ede : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ)
  (ede_iff_evi : ∀ ρ : ℝ → X,
    EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ)
  (jko_to_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

/-- Package the equivalence from an assumption pack. -/
theorem build_plfaEdeEvi_package (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  And.intro (fun ρ => H.plfa_iff_ede ρ)
    (And.intro (fun ρ => H.ede_iff_evi ρ) (fun ρ0 h => H.jko_to_plfa ρ0 h))

/-- Weak-hypothesis variant under placeholder flags. -/
theorem build_plfaEdeEvi_package_weak (F : X → ℝ) (lamEff : ℝ)
  (_HC : HalfConvex F lamEff) (_SUB : StrongUpperBound F)
  (H : EquivBuildAssumptions F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_plfaEdeEvi_package F lamEff H

/- Component-level predicates -/
def PLFA_EDE_pred (F : X → ℝ) : Prop := ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ
def EDE_EVI_pred (F : X → ℝ) (lamEff : ℝ) : Prop :=
  ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ
def JKO_to_PLFA_pred (F : X → ℝ) : Prop :=
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ

theorem plfa_iff_ede_from_pred (F : X → ℝ) (H : PLFA_EDE_pred F) :
  ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ := H
theorem ede_iff_evi_from_pred (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_pred F lamEff) :
  ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ := H
theorem jko_to_plfa_from_pred (F : X → ℝ) (H : JKO_to_PLFA_pred F) :
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ := H

/- Component packs -/
structure PLFAEDEAssumptions (F : X → ℝ) : Prop where
  (plfa_iff_ede : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ)
structure EDEEVIAssumptions (F : X → ℝ) (lamEff : ℝ) : Prop where
  (ede_iff_evi : ∀ ρ : ℝ → X,
    EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ)
structure JKOPLFAAssumptions (F : X → ℝ) : Prop where
  (jko_to_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

theorem plfa_ede_from_pack (F : X → ℝ) (H : PLFAEDEAssumptions F) : PLFA_EDE_pred F :=
  H.plfa_iff_ede
theorem ede_evi_from_pack (F : X → ℝ) (lamEff : ℝ) (H : EDEEVIAssumptions F lamEff) :
  EDE_EVI_pred F lamEff := H.ede_iff_evi
theorem jko_plfa_from_pack (F : X → ℝ) (H : JKOPLFAAssumptions F) : JKO_to_PLFA_pred F :=
  H.jko_to_plfa

/-- Analytic-flag bridges, statement-level -/
def PLFA_EDE_from_analytic_flags (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (Proper F ∧ LowerSemicontinuous F ∧ Coercive F ∧ HalfConvex F lamEff ∧ StrongUpperBound F) →
    PLFA_EDE_pred F
def EDE_EVI_from_analytic_flags (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (HalfConvex F lamEff ∧ StrongUpperBound F) → EDE_EVI_pred F lamEff
def JKO_PLFA_from_analytic_flags (F : X → ℝ) : Prop :=
  (Proper F ∧ LowerSemicontinuous F ∧ Coercive F ∧ JKOStable F) → JKO_to_PLFA_pred F

/-- Derive the PLFA⇔EDE analytic bridge from a component pack. -/
theorem plfa_ede_bridge_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : PLFAEDEAssumptions F) : PLFA_EDE_from_analytic_flags F lamEff :=
by
  intro _flags; exact H.plfa_iff_ede

/-- Derive the EDE⇔EVI analytic bridge from a component pack. -/
theorem ede_evi_bridge_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EDE_EVI_from_analytic_flags F lamEff :=
by
  intro _flags; exact H.ede_iff_evi

/-- Derive the JKO⇒PLFA analytic bridge from a component pack. -/
theorem jko_plfa_bridge_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : JKOPLFAAssumptions F) : JKO_PLFA_from_analytic_flags F :=
by
  intro _flags; exact H.jko_to_plfa

/-- Derive the PLFA⇔EDE analytic bridge directly from an equivalence pack. -/
theorem plfa_ede_bridge_from_equiv_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : PLFA_EDE_from_analytic_flags F lamEff :=
by
  intro _flags; exact H.plfa_iff_ede

/-- Derive the EDE⇔EVI analytic bridge directly from an equivalence pack. -/
theorem ede_evi_bridge_from_equiv_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : EDE_EVI_from_analytic_flags F lamEff :=
by
  intro _flags; exact H.ede_iff_evi

/-- Derive the JKO⇒PLFA analytic bridge directly from an equivalence pack. -/
theorem jko_plfa_bridge_from_equiv_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : JKO_PLFA_from_analytic_flags F :=
by
  intro _flags; exact H.jko_to_plfa

/-- Convenience: EDE ⇔ EVI from analytic flags. -/
theorem ede_evi_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
  H ⟨HC, SUB⟩

theorem build_EDEEVI_pack_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags F lamEff) : EDEEVIAssumptions F lamEff :=
by refine ⟨?_⟩; exact ede_evi_equiv_from_flags F lamEff HC SUB H

/-- JKO ⇒ PLFA from analytic flags. -/
theorem jko_to_plfa_from_flags (F : X → ℝ)
  (H : JKO_PLFA_from_analytic_flags F)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F) (hJ : JKOStable F) :
  JKO_to_PLFA_pred F := H ⟨hP, hL, hC, hJ⟩

theorem build_JKOPLFA_pack_from_flags (F : X → ℝ)
  (H : JKO_PLFA_from_analytic_flags F)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F) (hJ : JKOStable F) :
  JKOPLFAAssumptions F := by refine ⟨?_⟩; exact jko_to_plfa_from_flags F H hP hL hC hJ

/-- JKO ⇒ EDE using PLFA⇔EDE from flags. -/
theorem jko_to_ede_from_flags (F : X → ℝ) (lamEff : ℝ)
  (Hjko : JKO_PLFA_from_analytic_flags F)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F) (hJ : JKOStable F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ EDE F ρ :=
by
  intro ρ0 hJKO
  have Hjk : JKO_to_PLFA_pred F := jko_to_plfa_from_flags F Hjko hP hL hC hJ
  rcases Hjk ρ0 hJKO with ⟨ρ, h0, hplfa⟩
  have hbridge : ∀ r : ℝ → X, PLFA F r ↔ EDE F r := HplfaEde ⟨hP, hL, hC, HC, SUB⟩
  exact ⟨ρ, h0, (hbridge ρ).mp hplfa⟩

/-- JKO ⇒ EVI using bridges from flags. -/
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

/-- PLFA ⇔ EDE from analytic flags. -/
theorem plfa_ede_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : PLFA_EDE_from_analytic_flags F lamEff) :
  ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ := H ⟨hP, hL, hC, HC, SUB⟩

theorem build_PLFAEDE_pack_from_flags (F : X → ℝ) (lamEff : ℝ)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : PLFA_EDE_from_analytic_flags F lamEff) : PLFAEDEAssumptions F :=
by refine ⟨?_⟩; exact plfa_ede_equiv_from_flags F lamEff hP hL hC HC SUB H

/-- Action alias. -/
theorem action_iff_plfa (F : X → ℝ) (ρ : ℝ → X) : Action F ρ ↔ PLFA F ρ := Iff.rfl

/-- Analytic flags used to derive component predicates. -/
structure AnalyticFlags (F : X → ℝ) (lamEff : ℝ) : Prop where
  (proper : Proper F) (lsc : LowerSemicontinuous F) (coercive : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) (jkoStable : JKOStable F)

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
  build_package_from_global F lamEff (global_sufficient_pack_from_analytic_flags F lamEff H1 H2 H3 A)

structure AnalyticBridges (F : X → ℝ) (lamEff : ℝ) : Prop where
  (plfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (edeEvi : EDE_EVI_from_analytic_flags F lamEff)
  (jkoPlfa : JKO_PLFA_from_analytic_flags F)

theorem build_package_from_flags_and_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff) (B : AnalyticBridges F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_package_from_analytic_flags F lamEff B.plfaEde B.edeEvi B.jkoPlfa A

/-
P1: Connect EDE → EVI → PLFA under analytic flags (λ-half-convex + strong upper bound).
These helpers expose one-way implications derived by chaining the flag-bridges.
-/
theorem ede_to_plfa_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (HedeEvi : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ : ℝ → X, EDE F ρ → PLFA F ρ :=
by
  intro ρ hEDE
  -- Use EDE ⇔ EVI and PLFA ⇔ EDE provided by the flag bridges
  have h1 : ∀ r, EDE F r ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) r :=
    HedeEvi ⟨HC, SUB⟩
  have h2 : ∀ r, PLFA F r ↔ EDE F r :=
    HplfaEde ⟨(show Proper F from trivial), (show LowerSemicontinuous F from trivial),
               (show Coercive F from trivial), HC, SUB⟩
  -- From EDE, go to EVI (unused here) and back to PLFA via the PLFA⇔EDE bridge
  exact (h2 ρ).mpr hEDE

theorem plfa_to_evi_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (HedeEvi : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ : ℝ → X, PLFA F ρ → IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
by
  intro ρ hPLFA
  have h1 : ∀ r, EDE F r ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) r :=
    HedeEvi ⟨HC, SUB⟩
  have h2 : ∀ r, PLFA F r ↔ EDE F r :=
    HplfaEde ⟨(show Proper F from trivial), (show LowerSemicontinuous F from trivial),
               (show Coercive F from trivial), HC, SUB⟩
  have hEDE : EDE F ρ := (h2 ρ).mp hPLFA
  exact (h1 ρ).mp hEDE

theorem evi_to_plfa_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (HedeEvi : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ : ℝ → X, IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ → PLFA F ρ :=
by
  intro ρ hEVI
  have h1 : ∀ r, EDE F r ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) r :=
    HedeEvi ⟨HC, SUB⟩
  have h2 : ∀ r, PLFA F r ↔ EDE F r :=
    HplfaEde ⟨(show Proper F from trivial), (show LowerSemicontinuous F from trivial),
               (show Coercive F from trivial), HC, SUB⟩
  have hEDE : EDE F ρ := (h1 ρ).mpr hEVI
  exact (h2 ρ).mpr hEDE

/-
P4: Equivalence packaging theorem (alias to the builder), matching design naming.
-/
theorem plfaEdeEviJko_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_package_from_analytic_flags F lamEff H1 H2 H3 A

/-- Two-EVI with external forcing: statement-level predicate re-export. -/
def TwoEVIWithForce (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∃ (hu : IsEVISolution P u) (hv : IsEVISolution P v)
    (geodesicBetween : Prop) (hR : MixedErrorBound X u v),
      eviSumWithError P u v hu hv geodesicBetween hR ∧
      (gronwall_exponential_contraction_with_error_half_pred P.lam hR.η
        (fun t => d2 (u t) (v t)) →
        ContractionPropertySqWithError P u v hR.η)

/-- Distance-version consequence of `TwoEVIWithForce` via the error Grönwall
predicate and the bridge to distances. -/
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
  -- Obtain squared-distance synchronization with error, then bridge to distances.
  have Hsq : ContractionPropertySqWithError P u v hR.η := Himp Hgr
  exact bridge_with_error P u v hR.η (Hbridge hR.η) Hsq

/-- EDE ⇔ EVI under an equivalence package. -/
theorem ede_iff_evi (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ : ℝ → X) :
  EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ := (G.2.1) ρ

/-- EVI ⇔ PLFA under the same equivalence package. -/
theorem evi_iff_plfa (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ : ℝ → X) :
  IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ ↔ PLFA F ρ := by
  have h1 := (G.1) ρ; have h2 := (G.2.1) ρ; exact (h1.trans h2).symm

/-- JKO ⇒ EVI via the package. -/
theorem jko_to_evi (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ0 : X) :
  JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
by
  intro hJ; rcases (G.2.2) ρ0 hJ with ⟨ρ, h0, hplfa⟩
  exact ⟨ρ, h0, (evi_iff_plfa F lamEff G ρ).mpr hplfa⟩

end X

end Frourio
