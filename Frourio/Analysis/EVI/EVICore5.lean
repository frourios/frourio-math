import Frourio.Analysis.EVI.EVICore4
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic

namespace Frourio

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

/- Geodesic completeness surrogate: nonemptiness of the limit space. -/
def MoscoGeodesicComplete {ι : Type*} (S : MoscoSystem ι) : Prop :=
  Nonempty S.X

/- Uniform lower bound (coercivity) for prelimit energies. -/
def MoscoTight {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∃ C : ℝ, ∀ (h : ι) (x : S.Xh h), S.Eh h x ≥ -C

/- Minimal liminf-type inequality along the identification maps `Th`. -/
def MoscoM1 {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∀ (h : ι) (x : S.Xh h), S.E (S.Th h x) ≤ S.Eh h x

/- Minimal recovery-type condition: for any `x` in the limit, there exists a
preimage with no energy inflation. -/
def MoscoM2 {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∀ x : S.X, ∃ (h : ι) (xh : S.Xh h), S.Th h xh = x ∧ S.Eh h xh ≤ S.E x

/- Sequential lower semicontinuity on a metric space: along any sequence
converging to `x`, the liminf of energies dominates the value at `x`. -/
def LowerSemicontinuousSeq {X : Type*} [PseudoMetricSpace X] (E : X → ℝ) : Prop :=
  ∀ x : X, ∀ s : ℕ → X, Filter.Tendsto s Filter.atTop (nhds x) →
    E x ≤ Filter.liminf (fun n => E (s n)) Filter.atTop

/-- Assumption pack using the minimal Mosco predicates,
with a concrete sequential lower semicontinuity requirement for the limit energy. -/
structure MoscoAssumptions {ι : Type*} (S : MoscoSystem ι) : Prop where
  (geodesic_complete : MoscoGeodesicComplete S)
  (tightness : MoscoTight S)
  (lsc_Ent : LowerSemicontinuousSeq S.E)
  (M1 : MoscoM1 S)
  (M2 : MoscoM2 S)

/-- Limit EVI property under Mosco convergence.
We record that the liminf/recovery/tightness and geodesic completeness
conditions are available at the limit. This predicate is deliberately
lightweight and will be strengthened to true EVI statements in later phases. -/
def EVILimitHolds {ι : Type*} (S : MoscoSystem ι) : Prop :=
  MoscoM1 S ∧ MoscoM2 S ∧ MoscoTight S ∧ MoscoGeodesicComplete S

/-- EVI inheritance under Mosco assumptions (theoremized skeleton).
Proof sketch: Under geodesic completeness, tightness, l.s.c., and M1/M2,
JKO-type minimizing movement schemes are tight, and limit curves satisfy
the EVI inequality for the Γ-limit functional. Here we provide a placeholder
result that will be refined in later phases. -/
theorem eviInheritance {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoAssumptions S) : EVILimitHolds S := by
  rcases H with ⟨Hg, Ht, _Hlsc, HM1, HM2⟩
  exact And.intro HM1 (And.intro HM2 (And.intro Ht Hg))

/-!
Sufficient conditions tailored to an “Entropy + Dirichlet form” setting.

We introduce lightweight predicates named after the intended analytic
assumptions and show how they imply the minimal Mosco predicates used by
this file (Tight/M1/M2). These remain Prop‑valued and proof‑light.
-/

/-- Uniform entropy lower bound (coercivity surrogate) across the prelimit
family: `∃ C, ∀ h x, E_h(x) ≥ -C`. -/
def EntropyUniformLowerBound {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∃ C : ℝ, ∀ (h : ι) (x : S.Xh h), S.Eh h x ≥ -C

/-- Dirichlet‑form liminf inequality along the identification maps. -/
def DirichletFormLiminf {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∀ (h : ι) (x : S.Xh h), S.E (S.Th h x) ≤ S.Eh h x

/-- Dirichlet‑form recovery inequality (no energy inflation at a preimage). -/
def DirichletFormRecovery {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∀ x : S.X, ∃ (h : ι) (xh : S.Xh h), S.Th h xh = x ∧ S.Eh h xh ≤ S.E x

/-- Entropy lower bound implies `MoscoTight`. -/
theorem MoscoTight_from_entropy {ι : Type*} (S : MoscoSystem ι)
  (H : EntropyUniformLowerBound S) : MoscoTight S :=
by
  rcases H with ⟨C, hC⟩; exact ⟨C, hC⟩

/-- Dirichlet liminf implies `MoscoM1`. -/
theorem MoscoM1_from_dirichlet_liminf {ι : Type*} (S : MoscoSystem ι)
  (H : DirichletFormLiminf S) : MoscoM1 S := H

/-- Dirichlet recovery implies `MoscoM2`. -/
theorem MoscoM2_from_dirichlet_recovery {ι : Type*} (S : MoscoSystem ι)
  (H : DirichletFormRecovery S) : MoscoM2 S := H

/-- Build `MoscoAssumptions` from entropy lower bound and Dirichlet liminf/recovery
statements, plus geodesic completeness (nonemptiness of the limit space). -/
theorem build_MoscoAssumptions_from_entropy_dirichlet {ι : Type*}
  (S : MoscoSystem ι)
  (Hg : MoscoGeodesicComplete S)
  (Hent : EntropyUniformLowerBound S)
  (Hlim : DirichletFormLiminf S)
  (Hrec : DirichletFormRecovery S)
  (Hlsc : LowerSemicontinuousSeq S.E) : MoscoAssumptions S :=
by
  refine ⟨Hg, MoscoTight_from_entropy S Hent, Hlsc,
          MoscoM1_from_dirichlet_liminf S Hlim,
          MoscoM2_from_dirichlet_recovery S Hrec⟩

/-- From the entropy/Dirichlet sufficient conditions, obtain the minimal
`EVILimitHolds` predicate used in this file. -/
theorem EVILimit_from_entropy_dirichlet {ι : Type*} (S : MoscoSystem ι)
  (Hg : MoscoGeodesicComplete S)
  (Hent : EntropyUniformLowerBound S)
  (Hlim : DirichletFormLiminf S)
  (Hrec : DirichletFormRecovery S)
  (Hlsc : LowerSemicontinuousSeq S.E) : EVILimitHolds S :=
by
  exact eviInheritance S (build_MoscoAssumptions_from_entropy_dirichlet S Hg Hent Hlim Hrec Hlsc)

/- Sufficient conditions for the Mosco predicates (lightweight wrappers). -/

/-- A uniform lower bound on all prelimit energies implies `MoscoTight`. -/
theorem MoscoTight_of_uniform_lower_bound {ι : Type*} (S : MoscoSystem ι)
  (C : ℝ) (h : ∀ (h' : ι) (x : S.Xh h'), S.Eh h' x ≥ -C) : MoscoTight S :=
by
  exact ⟨C, h⟩

/-- Pointwise liminf inequality along `Th` is exactly `MoscoM1`. -/
theorem MoscoM1_of_liminf_along_Th {ι : Type*} (S : MoscoSystem ι)
  (h : ∀ (h' : ι) (x : S.Xh h'), S.E (S.Th h' x) ≤ S.Eh h' x) : MoscoM1 S :=
by
  exact h

/-- Existence of recovery points with no energy inflation is exactly `MoscoM2`. -/
theorem MoscoM2_of_recovery_no_inflation {ι : Type*} (S : MoscoSystem ι)
  (h : ∀ x : S.X, ∃ (h' : ι) (xh : S.Xh h'), S.Th h' xh = x ∧ S.Eh h' xh ≤ S.E x) :
  MoscoM2 S :=
by
  exact h

/-- Pack of sufficient conditions (uniform bound, liminf, recovery, nonempty limit). -/
structure MoscoSufficientConditions {ι : Type*} (S : MoscoSystem ι) : Prop where
  (uniform_lower : ∃ C : ℝ, ∀ (h : ι) (x : S.Xh h), S.Eh h x ≥ -C)
  (liminf_along_Th : ∀ (h : ι) (x : S.Xh h), S.E (S.Th h x) ≤ S.Eh h x)
  (recovery_no_inflation : ∀ x : S.X, ∃ (h : ι) (xh : S.Xh h), S.Th h xh = x ∧ S.Eh h xh ≤ S.E x)
  (geodesic_complete : Nonempty S.X)
  (lsc_Ent : LowerSemicontinuousSeq S.E)

/-- Build `MoscoAssumptions` from sufficient conditions. -/
theorem build_MoscoAssumptions_from_sufficient {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoSufficientConditions S) : MoscoAssumptions S :=
by
  rcases H with ⟨⟨C, hUB⟩, hM1, hM2, hGC, hLSC⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- geodesic completeness surrogate
    exact hGC
  · -- tightness from the uniform lower bound
    exact ⟨C, hUB⟩
  · -- sequential lower semicontinuity of the limit energy
    exact hLSC
  · -- M1
    exact hM1
  · -- M2
    exact hM2

/-- From sufficient conditions, obtain the minimal `EVILimitHolds` predicate. -/
theorem EVILimit_from_sufficient {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoSufficientConditions S) : EVILimitHolds S :=
by
  have HA : MoscoAssumptions S := build_MoscoAssumptions_from_sufficient S H
  exact eviInheritance S HA

end Frourio
