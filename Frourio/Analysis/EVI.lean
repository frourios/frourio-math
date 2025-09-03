import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

namespace Frourio

/-!
P4: Abstract EVI skeleton (definitions and statements only)

This file provides lightweight definitions for the EVI predicate on a
metric space, a Dini-type upper differential, and statement-shaped
properties for contraction, mixed-error EVI for a pair of evolutions,
and a Mosco-style convergence scaffold. Heavy analytical proofs are
intentionally deferred to later phases; here we only fix APIs and types.
-/

/- Basic squared distance helper -/
noncomputable def d2 {X : Type*} [PseudoMetricSpace X] (x y : X) : ℝ :=
  (dist x y) ^ (2 : ℕ)

/- Upper Dini derivative (skeleton placeholder). This keeps the API light
and avoids heavy measure/limsup machinery at this phase. -/
noncomputable def DiniUpper (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf { L : ℝ | ∀ ε > (0 : ℝ), ∃ h : ℝ, h > 0 ∧ φ (t + h) ≤ φ t + (L + ε) * h }

/- EVI problem datum: an energy and a parameter λ -/
structure EVIProblem (X : Type*) [PseudoMetricSpace X] where
  (E : X → ℝ)
  (lam : ℝ)

/- EVI predicate for a curve u : ℝ≥0 → X -/
def IsEVISolution {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u : ℝ → X) : Prop :=
  ∀ (t : ℝ) (v : X),
    (1 / 2 : ℝ) * DiniUpper (fun τ : ℝ => d2 (u τ) v) t
      + P.lam * d2 (u t) v ≤ P.E v - P.E (u t)

/- Contraction property statement (no proof here) -/
def ContractionProperty {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∀ t : ℝ,
    dist (u t) (v t) ≤ Real.exp (- P.lam * t) * dist (u 0) (v 0)

/- Contraction: packaged as a statement-producing definition -/
def eviContraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v) : Prop :=
  ContractionProperty P u v

/- Alias to match design naming (statement-level). -/
abbrev evi_contraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v) : Prop :=
  eviContraction P u v hu hv

/- Mixed-error bound skeleton for a pair (u, v). The `bound` field can
encode any intended inequality along a selected geodesic; we keep it
abstract at this stage. -/
structure MixedErrorBound (X : Type*) [PseudoMetricSpace X]
  (u v : ℝ → X) where
  (η : ℝ)
  (bound : ∀ _t : ℝ, Prop)

/- Mixed EVI sum statement (no proof; returns a Prop) -/
def eviSumWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v)
  (_geodesicBetween : Prop) (hR : MixedErrorBound X u v) : Prop :=
  ∀ t : ℝ,
    (1 / 2 : ℝ) * DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + P.lam * d2 (u t) (v t) ≤ hR.η

/- Optional: time-domain wrapper aligning (ℝ≥0 → X) with (ℝ → X) without
importing NNReal. We model nonnegative times as a subtype. -/
abbrev Rge0 := { t : ℝ // 0 ≤ t }

def toRge0 (t : ℝ) : Rge0 := ⟨max t 0, by exact le_max_right _ _⟩

def restrictNonneg {X : Type*} (u : Rge0 → X) : ℝ → X :=
  fun t => u (toRge0 t)

/-- EVI predicate on nonnegative time curves via the `restrictNonneg` wrapper. -/
def IsEVISolutionNonneg {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u : Rge0 → X) : Prop :=
  IsEVISolution P (restrictNonneg u)

/-- Contraction statement for nonnegative-time curves (wrapper version). -/
def evi_contraction_nonneg {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : Rge0 → X)
  (_hu : IsEVISolutionNonneg P u) (_hv : IsEVISolutionNonneg P v) : Prop :=
  ContractionProperty P (restrictNonneg u) (restrictNonneg v)

/- Mosco scaffold (index type ι for the family) -/
structure MoscoSystem (ι : Type*) where
  (Xh : ι → Type*)
  (X : Type*)
  [hx : ∀ h, PseudoMetricSpace (Xh h)]
  [x : PseudoMetricSpace X]
  (Th : ∀ h, Xh h → X)
  (Eh : ∀ h, Xh h → ℝ)
  (E : X → ℝ)

attribute [instance] MoscoSystem.hx MoscoSystem.x

/- Externalized Mosco predicates (placeholders to be refined later). These
are kept as `Prop`-valued definitions so that `MoscoAssumptions` can store
their proofs as fields, following the design intent. -/
def MoscoGeodesicComplete {ι : Type*} (_S : MoscoSystem ι) : Prop := True
def MoscoTight {ι : Type*} (_S : MoscoSystem ι) : Prop := True
def MoscoM1 {ι : Type*} (_S : MoscoSystem ι) : Prop := True
def MoscoM2 {ι : Type*} (_S : MoscoSystem ι) : Prop := True

/-- Assumption pack (kept as trivial proofs for now). The concrete
predicates `MoscoTight`, `MoscoM1`, `MoscoM2` are defined above and will
replace `True` fields in later phases. -/
structure MoscoAssumptions {ι : Type*} (S : MoscoSystem ι) : Prop where
  (geodesic_complete : MoscoGeodesicComplete S)
  (tightness : MoscoTight S)
  (lsc_Ent : True)
  (M1 : MoscoM1 S)
  (M2 : MoscoM2 S)

/- EVI inheritance statement placeholder. In later phases this will be
strengthened to explicit quantitative inequalities. -/
def eviInheritance {ι : Type*} (S : MoscoSystem ι)
  (_H : MoscoAssumptions S) : Prop :=
  True

end Frourio
