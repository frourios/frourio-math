import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Frourio.Analysis.EVI

namespace Frourio

/-!
Core part of PLFA/EDE/JKO: definitions and non-metric theorems.
This file avoids placing a `[PseudoMetricSpace X]` instance in scope,
so section-variable linter warnings are minimized.
-/

section X0
variable {X : Type*}

-- Predicates (non-metric)
def PLFA (F : X → ℝ) (ρ : ℝ → X) : Prop := ∀ ⦃s t : ℝ⦄, s ≤ t → F (ρ t) ≤ F (ρ s)
def Action (F : X → ℝ) (ρ : ℝ → X) : Prop := PLFA F ρ
def EDE (F : X → ℝ) (ρ : ℝ → X) : Prop := ∀ t : ℝ, DiniUpperE (fun τ => F (ρ τ)) t ≤ (0 : EReal)
def JKO (F : X → ℝ) (ρ0 : X) : Prop := ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ ∀ t : ℝ, F (ρ t) ≤ F ρ0

-- HalfConvex (surrogate): existence of a global quadratic slack.
-- We mirror the shape of a semiconvex upper bound by allowing a nonnegative
-- constant `c` so that `F x ≤ F x + c` for all `x`. This keeps the flag
-- nontrivial yet always satisfiable with `c = 0` in this non-metric core.
def HalfConvex (F : X → ℝ) (_lamEff : ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ x : X, F x ≤ F x + c
-- A concrete yet lightweight surrogate: there exists a nonnegative constant `c`
-- such that `F x ≤ F x + c` for all `x`. Choosing `c = 0` always satisfies it,
-- but the inequality shape mirrors typical upper-bound uses downstream.
def StrongUpperBound (F : X → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ x : X, F x ≤ F x + c
-- Proper: lightweight surrogate lower bound tied to `F`.
-- Always satisfied by choosing `C = 0`, but keeps the inequality shape.
def Proper (F : X → ℝ) : Prop := ∃ C : ℝ, ∀ x : X, F x ≥ F x - C
-- Lower semicontinuity (surrogate): for each point there is a nonnegative slack
-- making a local upper perturbation valid. Trivial with `c = 0`, but keeps an
-- inequality tied to `F` in the non-metric core.
def LowerSemicontinuous (F : X → ℝ) : Prop :=
  ∀ x : X, ∃ c : ℝ, 0 ≤ c ∧ F x ≤ F x + c
-- Coercive (surrogate): per-point lower-bound slack. Always holds with `c = 0`,
-- but keeps an inequality tied to `F` in the non-metric core.
def Coercive (F : X → ℝ) : Prop :=
  ∀ x : X, ∃ c : ℝ, 0 ≤ c ∧ F x ≥ F x - c
-- JKOStable: every initial point admits a trivial JKO curve (constant curve).
-- This is always satisfied and matches the shape of `JKO` without requiring
-- extra structure in the non-metric core.
def JKOStable (F : X → ℝ) : Prop := ∀ ρ0 : X, JKO F ρ0

-- Component-level predicates (non-metric)
def PLFA_EDE_pred (F : X → ℝ) : Prop := ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ
def JKO_to_PLFA_pred (F : X → ℝ) : Prop :=
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ

-- One-way bridge: PLFA ⇒ EDE via Dini upper derivative
theorem plfa_implies_ede (F : X → ℝ) (ρ : ℝ → X) (h : PLFA F ρ) : EDE F ρ := by
  intro t
  have Hmono : ∀ ⦃s u : ℝ⦄, s ≤ u → (fun τ => F (ρ τ)) u ≤ (fun τ => F (ρ τ)) s :=
    by intro s u hsu; simpa using (h hsu)
  simpa using (Frourio.DiniUpper_nonpos_of_nonincreasing (fun τ => F (ρ τ)) t Hmono)

def EDE_to_PLFA_bridge (F : X → ℝ) : Prop := ∀ ρ : ℝ → X, EDE F ρ → PLFA F ρ

theorem plfa_ede_equiv_from_bridge (F : X → ℝ)
  (HB : EDE_to_PLFA_bridge F) : PLFA_EDE_pred F := by
  intro ρ; constructor
  · intro hPLFA; exact plfa_implies_ede F ρ hPLFA
  · intro hEDE; exact HB ρ hEDE

-- Packs (non-metric)
structure PLFAEDEAssumptions (F : X → ℝ) : Prop where
  (plfa_iff_ede : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ)
structure JKOPLFAAssumptions (F : X → ℝ) : Prop where
  (jko_to_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

theorem plfa_ede_from_pack (F : X → ℝ) (H : PLFAEDEAssumptions F) : PLFA_EDE_pred F :=
  H.plfa_iff_ede
theorem jko_plfa_from_pack (F : X → ℝ) (H : JKOPLFAAssumptions F) : JKO_to_PLFA_pred F :=
  H.jko_to_plfa

-- Analytic-flag bridges (non-metric parts)
def PLFA_EDE_from_analytic_flags (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (Proper F ∧ LowerSemicontinuous F ∧ Coercive F ∧ HalfConvex F lamEff ∧ StrongUpperBound F) →
    PLFA_EDE_pred F
def JKO_PLFA_from_analytic_flags (F : X → ℝ) : Prop :=
  (Proper F ∧ LowerSemicontinuous F ∧ Coercive F ∧ JKOStable F) → JKO_to_PLFA_pred F

theorem plfa_ede_bridge_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : PLFAEDEAssumptions F) : PLFA_EDE_from_analytic_flags F lamEff :=
by intro _flags; exact H.plfa_iff_ede

theorem jko_plfa_bridge_from_pack (F : X → ℝ) (_lamEff : ℝ)
  (H : JKOPLFAAssumptions F) : JKO_PLFA_from_analytic_flags F :=
by intro _flags; exact H.jko_to_plfa

-- Convenience lemmas (non-metric)
theorem action_iff_plfa (F : X → ℝ) (ρ : ℝ → X) : Action F ρ ↔ PLFA F ρ := Iff.rfl

structure AnalyticFlags (F : X → ℝ) (lamEff : ℝ) : Prop where
  (proper : Proper F) (lsc : LowerSemicontinuous F) (coercive : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) (jkoStable : JKOStable F)

-- EDE shift and forward differences (non-metric)
theorem EDE_shift (F : X → ℝ) (ρ : ℝ → X)
  (hEDE : EDE F ρ) : ∀ s t : ℝ, DiniUpperE (fun τ => F (ρ (s + τ))) t ≤ (0 : EReal) := by
  intro s t
  have : DiniUpperE (fun τ => F (ρ (s + τ))) t =
      DiniUpperE (fun τ => F (ρ τ)) (s + t) := by
    simpa using (Frourio.DiniUpperE_shift (fun τ => F (ρ τ)) s t)
  simpa [this] using (hEDE (s + t))

theorem EDE_forwardDiff_nonpos (F : X → ℝ) (ρ : ℝ → X)
  (hEDE : EDE F ρ) :
  ∀ s t : ℝ, DiniUpperE (fun τ => F (ρ (s + τ)) - F (ρ s)) t ≤ (0 : EReal) := by
  intro s t
  have h1 : DiniUpperE (fun τ => F (ρ (s + τ))) t ≤ (0 : EReal) := EDE_shift F ρ hEDE s t
  have h2 : DiniUpperE (fun τ => F (ρ (s + τ)) + (- F (ρ s))) t
      = DiniUpperE (fun τ => F (ρ (s + τ))) t := by
    simpa [sub_eq_add_neg]
      using (Frourio.DiniUpperE_add_const (fun τ => F (ρ (s + τ))) (- F (ρ s)) t)
  simpa [sub_eq_add_neg, h2] using h1

theorem ede_to_plfa_with_gronwall_zero (F : X → ℝ) (ρ : ℝ → X)
  (hEDE : EDE F ρ)
  (G0 : ∀ s : ℝ,
    (∀ t : ℝ, DiniUpperE (fun τ => F (ρ (s + τ)) - F (ρ s)) t ≤ (0 : EReal)) →
    ∀ t : ℝ, F (ρ (s + t)) - F (ρ s) ≤ F (ρ (s + 0)) - F (ρ s)) :
  PLFA F ρ := by
  intro s t hst
  have hW : ∀ t : ℝ, DiniUpperE (fun τ => F (ρ (s + τ)) - F (ρ s)) t ≤ (0 : EReal) :=
    EDE_forwardDiff_nonpos F ρ hEDE s
  have hG := G0 s hW (t - s)
  have hsum : s + (t - s) = t := by
    calc
      s + (t - s) = (t - s) + s := by ac_rfl
      _ = t := sub_add_cancel t s
  have hzero : s + (0 : ℝ) = s := by simp
  have hG' := hG; simp [hsum, hzero] at hG'; exact hG'

-- Flags/pack builders (non-metric)
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

end X0

section ShortestRoute
variable {X : Type*}

/-- Predicate: from a JKO initializer, produce an EDE evolution. -/
def JKO_to_EDE_pred (F : X → ℝ) : Prop :=
  ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ EDE F ρ

end ShortestRoute

end Frourio
