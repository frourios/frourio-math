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

/-- PLFA predicate (minimalist): along `ρ`, the functional is nonincreasing. -/
def PLFA (F : X → ℝ) (ρ : ℝ → X) : Prop :=
  ∀ t : ℝ, F (ρ t) ≤ F (ρ 0)

/-- EDE predicate (minimalist): upper Dini derivative of `F ∘ ρ` is ≤ 0. -/
def EDE (F : X → ℝ) (ρ : ℝ → X) : Prop :=
  ∀ t : ℝ, DiniUpper (fun τ => F (ρ τ)) t ≤ 0

/-- JKO predicate: existence of a curve from `ρ0` with decreasing energy. -/
def JKO (F : X → ℝ) (ρ0 : X) : Prop :=
  ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ ∀ t : ℝ, F (ρ t) ≤ F ρ0

/-- Statement-level equivalence packaging PLFA, EDE, EVI, and a JKO-to-PLFA link.
The EVI piece uses the problem `⟨F, λ_eff⟩` induced by `F` and an effective
parameter `λ_eff` (e.g. from Doob-corrected curvature in FG8). -/
def plfaEdeEviJko_equiv (F : X → ℝ) (lamEff : ℝ) : Prop :=
  (∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ) ∧
  (∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ) ∧
  (∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ)

/-- Two-EVI with external forcing (statement-level): assumes a mixed EVI
sum inequality with error and concludes a squared-distance synchronization
bound once an inhomogeneous Grönwall lemma is provided. -/
def TwoEVIWithForce (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∃ (hu : IsEVISolution P u) (hv : IsEVISolution P v)
    (geodesicBetween : Prop) (hR : MixedErrorBound X u v),
      eviSumWithError P u v hu hv geodesicBetween hR ∧
      (gronwall_exponential_contraction_with_error_half P.lam hR.η
        (fun t => d2 (u t) (v t)) →
        ContractionPropertySqWithError P u v hR.η)

end X

end Frourio

