import Mathlib.Data.Real.Basic
import Frourio.Analysis.EVI

namespace Frourio

/-!
FG8 A2: PLFA/EDE/JKO predicates and equivalence skeleton

This module provides lightweight, Prop-valued predicates for the minimum
action principle (PLFA), Energy Dissipation Equality (EDE), and the JKO
minimizing movement scheme. It also packages a statement-level equivalence
`plfaEdeEviJko_equiv` connecting them to EVI with an effective parameter.

We keep statements proof-light at this phase (no sorry/axiom) and design
shapes that align with later analytic development.
-/

section X
variable {X : Type*} [PseudoMetricSpace X]

-- (Assumption pack and lightweight hypothesis flags are defined below,
-- after the core predicates are introduced.)

/-- PLFA predicate (monotone form): along `ρ`, the functional is nonincreasing
in time, i.e. it does not increase when time advances. -/
def PLFA (F : X → ℝ) (ρ : ℝ → X) : Prop :=
  ∀ ⦃s t : ℝ⦄, s ≤ t → F (ρ t) ≤ F (ρ s)

/-- Action functional predicate (minimalist placeholder).
In later phases this will encode the metric action integral; here we keep
it as a thin wrapper to stabilize the API. -/
def Action (F : X → ℝ) (ρ : ℝ → X) : Prop := PLFA F ρ

/-- EDE predicate (minimalist): upper Dini derivative of `F ∘ ρ` is ≤ 0. -/
def EDE (F : X → ℝ) (ρ : ℝ → X) : Prop :=
  ∀ t : ℝ, DiniUpper (fun τ => F (ρ τ)) t ≤ 0

/-- JKO predicate: existence of a curve from `ρ0` with energy controlled by the
initial energy (minimal placeholder for the minimizing movement output). -/
def JKO (F : X → ℝ) (ρ0 : X) : Prop :=
  ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ ∀ t : ℝ, F (ρ t) ≤ F ρ0

/-- Weak assumptions pack to build the PLFA–EDE–EVI–JKO equivalence package.
This captures, at a statement level, the three ingredients needed to
construct `plfaEdeEviJko_equiv` without committing to heavy analysis yet. -/
structure EquivBuildAssumptions (F : X → ℝ) (lamEff : ℝ) : Prop where
  (plfa_iff_ede : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ)
  (ede_iff_evi : ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ)
  (jko_to_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

/-- Optional lightweight placeholders for typical analytic hypotheses that,
in later phases, will imply `EquivBuildAssumptions`. -/
def HalfConvex (F : X → ℝ) (_lamEff : ℝ) : Prop := True
def StrongUpperBound (F : X → ℝ) : Prop := True

/-- Statement-level equivalence packaging PLFA, EDE, EVI, and a JKO-to-PLFA link.
The EVI piece uses the problem `⟨F, λ_eff⟩` induced by `F` and an effective
parameter `λ_eff` (e.g. from Doob-corrected curvature in FG8). -/
def plfaEdeEviJko_equiv (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ) ∧
  (∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ) ∧
  (∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

/-- Build the PLFA–EDE–EVI–JKO equivalence package from a weak assumption pack. -/
theorem build_plfaEdeEvi_package (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  And.intro
    (fun ρ => H.plfa_iff_ede ρ)
    (And.intro
      (fun ρ => H.ede_iff_evi ρ)
      (fun ρ0 h => H.jko_to_plfa ρ0 h))

/-- Weak construction of the `EquivBuildAssumptions` pack from component
equivalences under placeholder analytic flags. This is a packaging theorem
that records the three core statements needed to build the PLFA–EDE–EVI–JKO
equivalence, while gating on `HalfConvex` and `StrongUpperBound` as phase‑G
entry conditions. -/
theorem build_equiv_assumptions_weak (F : X → ℝ) (lamEff : ℝ)
  (_HC : HalfConvex F lamEff) (_SUB : StrongUpperBound F)
  (Hplfa_ede : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ)
  (Hede_evi : ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ)
  (Hjko_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ) :
  EquivBuildAssumptions F lamEff :=
{ plfa_iff_ede := Hplfa_ede,
  ede_iff_evi := Hede_evi,
  jko_to_plfa := Hjko_plfa }

/-- Component-level predicate: PLFA ⇔ EDE for all curves. -/
def PLFA_EDE_pred (F : X → ℝ) : Prop :=
  ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ

/-- Component-level predicate: EDE ⇔ EVI(λ_eff) for all curves. -/
def EDE_EVI_pred (F : X → ℝ) (lamEff : ℝ) : Prop :=
  ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ

/-- Component-level predicate: JKO ⇒ PLFA. -/
def JKO_to_PLFA_pred (F : X → ℝ) : Prop :=
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ

/-- Sufficient condition wrapper: from `PLFA_EDE_pred` obtain the equivalence. -/
theorem plfa_iff_ede_from_pred (F : X → ℝ)
  (H : PLFA_EDE_pred F) : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ :=
  H

/-- Sufficient condition wrapper: from `EDE_EVI_pred` obtain the equivalence. -/
theorem ede_iff_evi_from_pred (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_pred F lamEff) :
  ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
  H

/-- Sufficient condition wrapper: from `JKO_to_PLFA_pred` obtain JKO ⇒ PLFA. -/
theorem jko_to_plfa_from_pred (F : X → ℝ)
  (H : JKO_to_PLFA_pred F) :
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ :=
  H

/-- Build `EquivBuildAssumptions` from the three component-level predicates
under the weak analytic flags (phase‑gate). -/
theorem build_equiv_assumptions_from_components (F : X → ℝ) (lamEff : ℝ)
  (_HC : HalfConvex F lamEff) (_SUB : StrongUpperBound F)
  (H1 : PLFA_EDE_pred F) (H2 : EDE_EVI_pred F lamEff) (H3 : JKO_to_PLFA_pred F) :
  EquivBuildAssumptions F lamEff :=
  build_equiv_assumptions_weak F lamEff _HC _SUB H1 H2 H3

/-- Build the packaged PLFA–EDE–EVI–JKO equivalence from component predicates. -/
theorem build_package_from_components (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H1 : PLFA_EDE_pred F) (H2 : EDE_EVI_pred F lamEff) (H3 : JKO_to_PLFA_pred F) :
  plfaEdeEviJko_equiv F lamEff :=
by
  exact build_plfaEdeEvi_package F lamEff
    (build_equiv_assumptions_from_components F lamEff HC SUB H1 H2 H3)

/-- Assumption pack for PLFA ⇔ EDE (component). -/
structure PLFAEDEAssumptions (F : X → ℝ) : Prop where
  (plfa_iff_ede : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ)

/-- Assumption pack for EDE ⇔ EVI(λ_eff) (component). -/
structure EDEEVIAssumptions (F : X → ℝ) (lamEff : ℝ) : Prop where
  (ede_iff_evi : ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ)

/-- Assumption pack for JKO ⇒ PLFA (component). -/
structure JKOPLFAAssumptions (F : X → ℝ) : Prop where
  (jko_to_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

/-- Extract the component predicates from their assumption packs. -/
theorem plfa_ede_from_pack (F : X → ℝ) (H : PLFAEDEAssumptions F) :
  PLFA_EDE_pred F :=
  H.plfa_iff_ede

theorem ede_evi_from_pack (F : X → ℝ) (lamEff : ℝ) (H : EDEEVIAssumptions F lamEff) :
  EDE_EVI_pred F lamEff :=
  H.ede_iff_evi

theorem jko_plfa_from_pack (F : X → ℝ) (H : JKOPLFAAssumptions F) :
  JKO_to_PLFA_pred F :=
  H.jko_to_plfa

/-- Build `EquivBuildAssumptions` from the three component packs under the
weak analytic flags (phase‑gate). -/
theorem build_equiv_assumptions_from_packs (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (Hplfa_ede : PLFAEDEAssumptions F)
  (Hede_evi : EDEEVIAssumptions F lamEff)
  (Hjko_plfa : JKOPLFAAssumptions F) :
  EquivBuildAssumptions F lamEff :=
  build_equiv_assumptions_from_components F lamEff HC SUB
    (plfa_ede_from_pack F Hplfa_ede)
    (ede_evi_from_pack F lamEff Hede_evi)
    (jko_plfa_from_pack F Hjko_plfa)

/-- Build the packaged equivalence from the three component packs. -/
theorem build_package_from_packs (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (Hplfa_ede : PLFAEDEAssumptions F)
  (Hede_evi : EDEEVIAssumptions F lamEff)
  (Hjko_plfa : JKOPLFAAssumptions F) :
  plfaEdeEviJko_equiv F lamEff :=
  build_plfaEdeEvi_package F lamEff
    (build_equiv_assumptions_from_packs F lamEff HC SUB Hplfa_ede Hede_evi Hjko_plfa)

/-- Extract component equivalences from an equivalence-assumption pack. -/
theorem component_PLFA_EDE_of_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : PLFA_EDE_pred F :=
  H.plfa_iff_ede

theorem component_EDE_EVI_of_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : EDE_EVI_pred F lamEff :=
  H.ede_iff_evi

theorem component_JKO_PLFA_of_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : JKO_to_PLFA_pred F :=
  H.jko_to_plfa

/-- Aggregate sufficient-condition pack collecting the weak analytic flags
and the three component equivalences/implications. This provides a single
handle to construct the full PLFA–EDE–EVI–JKO equivalence. -/
structure EquivSufficientPack (F : X → ℝ) (lamEff : ℝ) : Prop where
  (HC : HalfConvex F lamEff)
  (SUB : StrongUpperBound F)
  (plfa_ede : PLFA_EDE_pred F)
  (ede_evi : EDE_EVI_pred F lamEff)
  (jko_plfa : JKO_to_PLFA_pred F)

/-- Build the equivalence-assumption pack from the aggregate sufficient pack. -/
theorem build_equiv_assumptions_from_sufficient_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivSufficientPack F lamEff) : EquivBuildAssumptions F lamEff :=
  build_equiv_assumptions_from_components F lamEff H.HC H.SUB H.plfa_ede H.ede_evi H.jko_plfa

/-- Build the packaged equivalence from the aggregate sufficient pack. -/
theorem build_package_from_sufficient_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivSufficientPack F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_plfaEdeEvi_package F lamEff (build_equiv_assumptions_from_sufficient_pack F lamEff H)

/-- Minimal analytic flags (placeholders) typically used to derive component results. -/
def Proper (F : X → ℝ) : Prop := True
def LowerSemicontinuous (F : X → ℝ) : Prop := True
def Coercive (F : X → ℝ) : Prop := True
def JKOStable (F : X → ℝ) : Prop := True

/-- Component-level sufficient predicates (statement-only) bundling the target
equivalences/implications; these act as named handles for later analytic work. -/
def PLFA_EDE_sufficient (F : X → ℝ) (_lamEff : ℝ) : Prop := PLFA_EDE_pred F
def EDE_EVI_sufficient (F : X → ℝ) (lamEff : ℝ) : Prop := EDE_EVI_pred F lamEff
def JKO_PLFA_sufficient (F : X → ℝ) : Prop := JKO_to_PLFA_pred F

/-- Skeleton: from a sufficient predicate for PLFA ⇔ EDE, build its component pack. -/
theorem build_PLFAEDE_pack_from_sufficient (F : X → ℝ) (lamEff : ℝ)
  (H : PLFA_EDE_sufficient F lamEff) : PLFAEDEAssumptions F :=
{ plfa_iff_ede := H }

/-- Skeleton: from a sufficient predicate for EDE ⇔ EVI, build its component pack. -/
theorem build_EDEEVI_pack_from_sufficient (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_sufficient F lamEff) : EDEEVIAssumptions F lamEff :=
{ ede_iff_evi := H }

/-- Skeleton: from a sufficient predicate for JKO ⇒ PLFA, build its component pack. -/
theorem build_JKOPLFA_pack_from_sufficient (F : X → ℝ)
  (H : JKO_PLFA_sufficient F) : JKOPLFAAssumptions F :=
{ jko_to_plfa := H }

/-- Aggregated component-sufficient pack (statement-level). -/
structure ComponentSufficientPack (F : X → ℝ) (lamEff : ℝ) : Prop where
  (H1 : PLFA_EDE_sufficient F lamEff)
  (H2 : EDE_EVI_sufficient F lamEff)
  (H3 : JKO_PLFA_sufficient F)

/-- Build component packs from the aggregated component-sufficient pack. -/
theorem build_component_packs_from_sufficient (F : X → ℝ) (lamEff : ℝ)
  (H : ComponentSufficientPack F lamEff) :
  PLFAEDEAssumptions F ∧ EDEEVIAssumptions F lamEff ∧ JKOPLFAAssumptions F := by
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · exact build_PLFAEDE_pack_from_sufficient F lamEff H.H1
  · exact build_EDEEVI_pack_from_sufficient F lamEff H.H2
  · exact build_JKOPLFA_pack_from_sufficient F H.H3

/-- Global sufficient pack combining weak analytic flags and component sufficients. -/
structure GlobalSufficientPack (F : X → ℝ) (lamEff : ℝ) : Prop where
  (HC : HalfConvex F lamEff)
  (SUB : StrongUpperBound F)
  (components : ComponentSufficientPack F lamEff)

/-- Build EquivBuildAssumptions from the global sufficient pack. -/
theorem build_equiv_assumptions_from_global (F : X → ℝ) (lamEff : ℝ)
  (H : GlobalSufficientPack F lamEff) : EquivBuildAssumptions F lamEff := by
  rcases (build_component_packs_from_sufficient F lamEff H.components) with ⟨H1, H2, H3⟩
  exact build_equiv_assumptions_from_packs F lamEff H.HC H.SUB H1 H2 H3

/-- Build packaged equivalence from the global sufficient pack. -/
theorem build_package_from_global (F : X → ℝ) (lamEff : ℝ)
  (H : GlobalSufficientPack F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_plfaEdeEvi_package F lamEff (build_equiv_assumptions_from_global F lamEff H)

/-- Statement-level bridges from analytic flags to component predicates. -/
def PLFA_EDE_from_analytic_flags (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (Proper F ∧ LowerSemicontinuous F ∧ Coercive F ∧ HalfConvex F lamEff ∧ StrongUpperBound F) →
    PLFA_EDE_pred F

def EDE_EVI_from_analytic_flags (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (HalfConvex F lamEff ∧ StrongUpperBound F) → EDE_EVI_pred F lamEff

def JKO_PLFA_from_analytic_flags (F : X → ℝ) : Prop :=
  (Proper F ∧ LowerSemicontinuous F ∧ Coercive F ∧ JKOStable F) → JKO_to_PLFA_pred F

/-- Build the PLFA⇔EDE component pack from analytic flags via a provided bridge. -/
theorem build_PLFAEDE_pack_from_analytic (F : X → ℝ) (lamEff : ℝ)
  (H : PLFA_EDE_from_analytic_flags F lamEff)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  PLFAEDEAssumptions F :=
by
  refine ⟨?_⟩
  exact H ⟨hP, hL, hC, HC, SUB⟩

/-- JKO ⇒ PLFA (direct, definition-unfolding proof).
From the definition of `JKO`, we obtain a curve `ρ` with `ρ 0 = ρ0` and
nonincreasing energy relative to `ρ0`. Since `ρ 0 = ρ0`, this immediately
implies the PLFA predicate `∀ t, F (ρ t) ≤ F (ρ 0)`. This proof is
purely algebraic and does not require analytic flags. -/
theorem build_EDEEVI_pack_from_analytic (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  EDEEVIAssumptions F lamEff :=
by
  refine ⟨?_⟩
  exact H ⟨HC, SUB⟩

/-- Build the JKO⇒PLFA component pack from analytic flags via a provided bridge. -/
theorem build_JKOPLFA_pack_from_analytic (F : X → ℝ)
  (H : JKO_PLFA_from_analytic_flags F)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F) (hJ : JKOStable F) :
  JKOPLFAAssumptions F :=
by
  refine ⟨?_⟩
  exact H ⟨hP, hL, hC, hJ⟩

/-- Build the equivalence assumptions from analytic flags and the three component bridges. -/
theorem build_equiv_from_analytic (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) (hJ : JKOStable F) :
  EquivBuildAssumptions F lamEff :=
by
  have A1 := build_PLFAEDE_pack_from_analytic F lamEff H1 hP hL hC HC SUB
  have A2 := build_EDEEVI_pack_from_analytic F lamEff H2 HC SUB
  have A3 := build_JKOPLFA_pack_from_analytic F H3 hP hL hC hJ
  exact build_equiv_assumptions_from_packs F lamEff HC SUB A1 A2 A3

/-- Build the packaged equivalence from analytic flags and the three component bridges. -/
theorem build_package_from_analytic (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) (hJ : JKOStable F) :
  plfaEdeEviJko_equiv F lamEff :=
  build_plfaEdeEvi_package F lamEff
    (build_equiv_from_analytic F lamEff H1 H2 H3 hP hL hC HC SUB hJ)

/-- Direct bridge: if `PLFA F ρ` holds in the monotone sense, then
`EDE F ρ` holds, i.e. the upper Dini derivative of `F ∘ ρ` is nonpositive
at every time. -/
theorem ede_of_plfa_monotone (F : X → ℝ) (ρ : ℝ → X)
  (h : PLFA F ρ) : EDE F ρ := by
  intro t
  -- Apply the monotone→DiniUpper bridge to `φ = F ∘ ρ`.
  exact DiniUpper_nonpos_of_nonincreasing (fun τ => F (ρ τ)) t (by
    intro s u hsu; exact h hsu)

/-- Step 1 convenience: EDE ⇔ EVI from λ-semi-convexity and a strong upper bound,
given a bridge statement from analytic flags. -/
theorem ede_evi_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
  H ⟨HC, SUB⟩

/-- Step 1 convenience (pack form): build the EDE⇔EVI component pack from
λ-semi-convexity and a strong upper bound using an analytic-bridge statement. -/
theorem build_EDEEVI_pack_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  EDEEVIAssumptions F lamEff :=
by
  refine ⟨?_⟩
  exact ede_evi_equiv_from_flags F lamEff HC SUB H

/-- Step 2: JKO ⇒ PLFA from proper/l.s.c./coercive and JKO-stability, via the
analytic-bridge statement. -/
theorem jko_to_plfa_from_flags (F : X → ℝ)
  (H : JKO_PLFA_from_analytic_flags F)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F) (hJ : JKOStable F) :
  JKO_to_PLFA_pred F :=
  H ⟨hP, hL, hC, hJ⟩

/-- Step 2 (pack form): build the JKO⇒PLFA component pack from analytic flags. -/
theorem build_JKOPLFA_pack_from_flags (F : X → ℝ)
  (H : JKO_PLFA_from_analytic_flags F)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F) (hJ : JKOStable F) :
  JKOPLFAAssumptions F :=
by
  refine ⟨?_⟩
  exact jko_to_plfa_from_flags F H hP hL hC hJ

/-- Step 2 (to EDE): combine JKO⇒PLFA with the PLFA⇔EDE bridge to obtain JKO⇒EDE. -/
theorem jko_to_ede_from_flags (F : X → ℝ) (lamEff : ℝ)
  (Hjko : JKO_PLFA_from_analytic_flags F)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F) (hJ : JKOStable F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ EDE F ρ :=
by
  intro ρ0 hJKO
  -- obtain JKO⇒PLFA curve
  have Hjk : JKO_to_PLFA_pred F := jko_to_plfa_from_flags F Hjko hP hL hC hJ
  rcases Hjk ρ0 hJKO with ⟨ρ, h0, hplfa⟩
  -- convert PLFA to EDE using the bridge from flags
  have hbridge : ∀ r : ℝ → X, PLFA F r ↔ EDE F r := HplfaEde ⟨hP, hL, hC, HC, SUB⟩
  have hEDE : EDE F ρ := (hbridge ρ).mp hplfa
  exact ⟨ρ, h0, hEDE⟩

/-- Step 2 (to EVI): combine JKO⇒PLFA and EDE⇔EVI to obtain JKO⇒EVI. -/
theorem jko_to_evi_from_flags (F : X → ℝ) (lamEff : ℝ)
  (Hjko : JKO_PLFA_from_analytic_flags F)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (HedeEvi : EDE_EVI_from_analytic_flags F lamEff)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F) (hJ : JKOStable F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
by
  intro ρ0 hJKO
  -- JKO ⇒ PLFA
  have Hjk : JKO_to_PLFA_pred F := jko_to_plfa_from_flags F Hjko hP hL hC hJ
  rcases Hjk ρ0 hJKO with ⟨ρ, h0, hplfa⟩
  -- PLFA ⇒ EDE via bridge
  have hPLFA_EDE : ∀ r : ℝ → X, PLFA F r ↔ EDE F r := HplfaEde ⟨hP, hL, hC, HC, SUB⟩
  have hEDE : EDE F ρ := (hPLFA_EDE ρ).mp hplfa
  -- EDE ⇒ EVI via EDE⇔EVI
  have hEDE_EVI : ∀ r : ℝ → X, EDE F r ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) r :=
    HedeEvi ⟨HC, SUB⟩
  have hEVI : IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ := (hEDE_EVI ρ).mp hEDE
  exact ⟨ρ, h0, hEVI⟩

/-- Step 3: PLFA ⇔ EDE from proper/l.s.c./coercive and λ‑semi‑convexity + strong upper bound,
via the analytic-bridge statement. -/
theorem plfa_ede_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : PLFA_EDE_from_analytic_flags F lamEff) :
  ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ :=
  H ⟨hP, hL, hC, HC, SUB⟩

/-- Step 3 (pack form): build the PLFA⇔EDE component pack from analytic flags. -/
theorem build_PLFAEDE_pack_from_flags (F : X → ℝ) (lamEff : ℝ)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : PLFA_EDE_from_analytic_flags F lamEff) :
  PLFAEDEAssumptions F :=
by
  refine ⟨?_⟩
  exact plfa_ede_equiv_from_flags F lamEff hP hL hC HC SUB H

/-- Trivial identity: `Action` is currently a wrapper for `PLFA`. -/
theorem action_iff_plfa (F : X → ℝ) (ρ : ℝ → X) : Action F ρ ↔ PLFA F ρ := Iff.rfl

/-- Directional lemmas from the component predicate `PLFA_EDE_pred`. -/
theorem ede_of_plfa_from_pred (F : X → ℝ) (H : PLFA_EDE_pred F) (ρ : ℝ → X) :
  PLFA F ρ → EDE F ρ :=
  (H ρ).mp

theorem plfa_of_ede_from_pred (F : X → ℝ) (H : PLFA_EDE_pred F) (ρ : ℝ → X) :
  EDE F ρ → PLFA F ρ :=
  (H ρ).mpr

/-- Directional lemmas from the component predicate `EDE_EVI_pred`. -/
theorem evi_of_ede_from_pred (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_pred F lamEff) (ρ : ℝ → X) :
  EDE F ρ → IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
  (H ρ).mp

theorem ede_of_evi_from_pred (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_pred F lamEff) (ρ : ℝ → X) :
  IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ → EDE F ρ :=
  (H ρ).mpr

/-- Directional lemmas derived from an equivalence-assumption pack. -/
theorem ede_of_plfa_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) (ρ : ℝ → X) :
  PLFA F ρ → EDE F ρ :=
  (H.plfa_iff_ede ρ).mp

theorem plfa_of_ede_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) (ρ : ℝ → X) :
  EDE F ρ → PLFA F ρ :=
  (H.plfa_iff_ede ρ).mpr

theorem evi_of_ede_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) (ρ : ℝ → X) :
  EDE F ρ → IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
  (H.ede_iff_evi ρ).mp

theorem ede_of_evi_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) (ρ : ℝ → X) :
  IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ → EDE F ρ :=
  (H.ede_iff_evi ρ).mpr

/-- Aggregated analytic flags (statement-level) used to trigger component bridges. -/
structure AnalyticFlags (F : X → ℝ) (lamEff : ℝ) : Prop where
  (proper : Proper F)
  (lsc : LowerSemicontinuous F)
  (coercive : Coercive F)
  (HC : HalfConvex F lamEff)
  (SUB : StrongUpperBound F)
  (jkoStable : JKOStable F)

/-- From analytic flags and three bridge statements, produce the three component predicates. -/
theorem component_predicates_from_analytic_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) :
  PLFA_EDE_pred F ∧ EDE_EVI_pred F lamEff ∧ JKO_to_PLFA_pred F :=
by
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · exact H1 ⟨A.proper, A.lsc, A.coercive, A.HC, A.SUB⟩
  · exact H2 ⟨A.HC, A.SUB⟩
  · exact H3 ⟨A.proper, A.lsc, A.coercive, A.jkoStable⟩

/-- From analytic flags and bridge statements, produce a global sufficient pack. -/
theorem global_sufficient_pack_from_analytic_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) :
  GlobalSufficientPack F lamEff :=
by
  -- Build component predicates from flags
  have hcomps := component_predicates_from_analytic_flags F lamEff H1 H2 H3 A
  rcases hcomps with ⟨h1, htmp⟩; rcases htmp with ⟨h2, h3⟩
  -- Assemble the global pack using the obtained predicates as sufficient components
  refine ⟨A.HC, A.SUB, ?components⟩
  exact ⟨h1, h2, h3⟩

/-- From analytic flags and bridge statements, produce the packaged equivalence. -/
theorem build_package_from_analytic_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) :
  plfaEdeEviJko_equiv F lamEff :=
  build_package_from_global F lamEff (global_sufficient_pack_from_analytic_flags F lamEff H1 H2 H3 A)

/-- Bridge triples pack: collects the three analytic-flag bridges used to
produce component predicates. -/
structure AnalyticBridges (F : X → ℝ) (lamEff : ℝ) : Prop where
  (plfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (edeEvi : EDE_EVI_from_analytic_flags F lamEff)
  (jkoPlfa : JKO_PLFA_from_analytic_flags F)

/-- Canonical builder: from consolidated analytic flags and bridge triples,
construct the packaged equivalence. Prefer this as the single entry point
when working at the analytic-flags level. -/
theorem build_package_from_flags_and_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff) (B : AnalyticBridges F lamEff) :
  plfaEdeEviJko_equiv F lamEff :=
  build_package_from_analytic_flags F lamEff B.plfaEde B.edeEvi B.jkoPlfa A

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

/-- Weak-hypothesis variant: under model placeholders for λ_BE-semi-convexity
and a strong upper bound, if we also have an assumption pack that provides the
three equivalences, then we can build the PLFA–EDE–EVI–JKO package. This
matches the staged design where analytic hypotheses gate the construction,
while the actual equivalences are supplied in a separate pack. -/
theorem build_plfaEdeEvi_package_weak (F : X → ℝ) (lamEff : ℝ)
  (_HC : HalfConvex F lamEff) (_SUB : StrongUpperBound F)
  (H : EquivBuildAssumptions F lamEff) : plfaEdeEviJko_equiv F lamEff :=
  build_plfaEdeEvi_package F lamEff H

/-- Two-EVI with external forcing (statement-level): assumes a mixed EVI
sum inequality with error and concludes a squared-distance synchronization
bound once an inhomogeneous Grönwall lemma is provided. -/
def TwoEVIWithForce (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∃ (hu : IsEVISolution P u) (hv : IsEVISolution P v)
    (geodesicBetween : Prop) (hR : MixedErrorBound X u v),
      eviSumWithError P u v hu hv geodesicBetween hR ∧
      (gronwall_exponential_contraction_with_error_half_pred P.lam hR.η
        (fun t => d2 (u t) (v t)) →
        ContractionPropertySqWithError P u v hR.η)

/-- EDE ⇔ EVI under an equivalence package for `F` and `λ_eff`.
Proof outline: this is the second component of `plfaEdeEviJko_equiv`. -/
theorem ede_iff_evi (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ : ℝ → X) :
  EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
  (G.2.1) ρ

/-- EVI ⇔ PLFA under the same equivalence package.
Proof outline: combine `PLFA ↔ EDE` and `EDE ↔ EVI`, then take symmetry. -/
theorem evi_iff_plfa (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ : ℝ → X) :
  IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ ↔ PLFA F ρ := by
  have h1 := (G.1) ρ
  have h2 := (G.2.1) ρ
  -- h1 : PLFA ↔ EDE, h2 : EDE ↔ EVI; so PLFA ↔ EVI
  have h := h1.trans h2
  exact h.symm

/-- JKO ⇒ EVI: from a JKO curve we obtain a PLFA curve by the package,
then convert PLFA → EVI via `evi_iff_plfa` symmetry. -/
theorem jko_to_evi (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ0 : X) :
  JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
by
  intro hJ
  rcases (G.2.2) ρ0 hJ with ⟨ρ, h0, hplfa⟩
  have hEVI : IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ :=
    (evi_iff_plfa F lamEff G ρ).mpr hplfa
  exact ⟨ρ, h0, hEVI⟩

end X

end Frourio
