import Frourio.Analysis.EVI.EVICore0
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

/-- Real bridge from the EReal inequality: if all three upper Dini derivatives
are finite in `EReal` (neither `⊤` nor `⊥`), then the real-valued additivity
upper bound holds. -/
theorem DiniUpper_add_le_of_finite
  (φ ψ : ℝ → ℝ) (t : ℝ)
  (hφ_fin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hψ_fin : DiniUpperE ψ t ≠ ⊤ ∧ DiniUpperE ψ t ≠ ⊥)
  (hsum_fin : DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊤ ∧
              DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊥)
  (hubφ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((φ (t + h) - φ t) / h) ≤ M)
  (hlbφ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((φ (t + h) - φ t) / h))
  (hubψ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((ψ (t + h) - ψ t) / h) ≤ M)
  (hlbψ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((ψ (t + h) - ψ t) / h))
  (hubsum : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M)
  (hlbsum : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)) :
  DiniUpper_add_le_pred φ ψ t := by
  -- Outline:
  -- 1) Apply `DiniUpperE_add_le` to get the EReal inequality.
  -- 2) Use `toReal_le_toReal` with finiteness to transport ≤ to real numbers.
  -- 3) Identify `toReal (DiniUpperE …)` with `DiniUpper …` under finiteness.
  -- The identification step is deferred and will be supplied by an auxiliary
  -- lemma linking `ℝ` and `EReal` limsups for finite values.
  --
  -- Step 1: EReal inequality.
  have hE :
      DiniUpperE (fun τ => φ τ + ψ τ) t ≤ DiniUpperE φ t + DiniUpperE ψ t :=
    DiniUpperE_add_le φ ψ t
      (Or.inl hφ_fin.2) (Or.inl hφ_fin.1)
  -- Right-hand side is not `⊤` since both summands are finite.
  have hsum_ne_top : DiniUpperE φ t + DiniUpperE ψ t ≠ ⊤ := by
    have hiff := EReal.add_ne_top_iff_ne_top₂ (hφ_fin.2) (hψ_fin.2)
    exact (hiff.mpr ⟨hφ_fin.1, hψ_fin.1⟩)
  -- Step 2: move to reals via `toReal_le_toReal`.
  have hR :
      (DiniUpperE (fun τ => φ τ + ψ τ) t).toReal
        ≤ (DiniUpperE φ t + DiniUpperE ψ t).toReal :=
    EReal.toReal_le_toReal hE (hsum_fin.2) hsum_ne_top
  -- Identify each side with the Real `DiniUpper` values.
  have hL_id :
      (DiniUpperE (fun τ => φ τ + ψ τ) t).toReal
        = DiniUpper (fun τ => φ τ + ψ τ) t := by
    symm; exact DiniUpper_eq_toReal_of_finite (fun τ => φ τ + ψ τ) t hsum_fin hubsum hlbsum
  have hφ_id : (DiniUpperE φ t).toReal = DiniUpper φ t := by
    symm; exact DiniUpper_eq_toReal_of_finite φ t hφ_fin hubφ hlbφ
  have hψ_id : (DiniUpperE ψ t).toReal = DiniUpper ψ t := by
    symm; exact DiniUpper_eq_toReal_of_finite ψ t hψ_fin hubψ hlbψ
  -- Rewrite the RHS `toReal` of a sum into sum of `toReal`.
  have hsum_toReal :
      (DiniUpperE φ t + DiniUpperE ψ t).toReal
        = (DiniUpperE φ t).toReal + (DiniUpperE ψ t).toReal := by
    -- Both summands are finite, so `toReal` is additive.
    simpa using EReal.toReal_add (hx := hφ_fin.1) (h'x := hφ_fin.2)
                                (hy := hψ_fin.1) (h'y := hψ_fin.2)
  -- Conclude the desired Real inequality.
  -- Assemble all identifications and simplify.
  have : DiniUpper (fun τ => φ τ + ψ τ) t
           ≤ DiniUpper φ t + DiniUpper ψ t := by
    simpa [hL_id, hφ_id, hψ_id, hsum_toReal, add_comm, add_left_comm, add_assoc] using hR
  -- Finish.
  simpa [DiniUpper_add_le_pred] using this

/-- Boundedness付き（上下の eventually 有界）での加法劣加法性。 -/
theorem DiniUpper_add_le_pred_of_bounds (φ ψ : ℝ → ℝ) (t : ℝ)
  (hφ_fin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hψ_fin : DiniUpperE ψ t ≠ ⊤ ∧ DiniUpperE ψ t ≠ ⊥)
  (hsum_fin : DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊤ ∧
              DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊥)
  (hubφ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((φ (t + h) - φ t) / h) ≤ M)
  (hlbφ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((φ (t + h) - φ t) / h))
  (hubψ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((ψ (t + h) - ψ t) / h) ≤ M)
  (hlbψ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((ψ (t + h) - ψ t) / h))
  (hubsum : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M)
  (hlbsum : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)) :
  DiniUpper_add_le_pred φ ψ t :=
  DiniUpper_add_le_of_finite φ ψ t hφ_fin hψ_fin hsum_fin
    hubφ hlbφ hubψ hlbψ hubsum hlbsum

/-- Supply an eventual upper bound for the forward difference quotient of a sum
from eventual upper bounds of the summands. -/
theorem forwardDiff_upper_bound_sum
  (φ ψ : ℝ → ℝ) (t : ℝ)
  (hubφ : ∃ Mφ : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            ((φ (t + h) - φ t) / h) ≤ Mφ)
  (hubψ : ∃ Mψ : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            ((ψ (t + h) - ψ t) / h) ≤ Mψ) :
  ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M :=
by
  rcases hubφ with ⟨Mφ, hφ⟩; rcases hubψ with ⟨Mψ, hψ⟩
  refine ⟨Mφ + Mψ, ?_⟩
  -- On the intersection event, use additivity of the difference quotient
  refine (hφ.and hψ).mono ?_
  intro h hh
  rcases hh with ⟨h1, h2⟩
  have hadd : (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)
            = ((φ (t + h) - φ t) / h) + ((ψ (t + h) - ψ t) / h) := by
    ring
  have hsum : ((φ (t + h) - φ t) / h) + ((ψ (t + h) - ψ t) / h) ≤ Mφ + Mψ :=
    add_le_add h1 h2
  simpa [hadd] using hsum

/-- Supply an eventual lower bound for the forward difference quotient of a sum -/
theorem forwardDiff_lower_bound_sum
  (φ ψ : ℝ → ℝ) (t : ℝ)
  (hlbφ : ∃ mφ : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            mφ ≤ ((φ (t + h) - φ t) / h))
  (hlbψ : ∃ mψ : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            mψ ≤ ((ψ (t + h) - ψ t) / h)) :
  ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) :=
by
  rcases hlbφ with ⟨mφ, hφ⟩; rcases hlbψ with ⟨mψ, hψ⟩
  refine ⟨mφ + mψ, ?_⟩
  refine (hφ.and hψ).mono ?_
  intro h hh
  rcases hh with ⟨h1, h2⟩
  have hadd : (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)
            = ((φ (t + h) - φ t) / h) + ((ψ (t + h) - ψ t) / h) := by
    ring
  have hsum : mφ + mψ ≤ ((φ (t + h) - φ t) / h) + ((ψ (t + h) - ψ t) / h) :=
    add_le_add h1 h2
  simpa [hadd] using hsum

-- Retain the original name as a placeholder (unconditional version is not
-- derivable in full generality without additional boundedness/finite limsup
-- hypotheses). Provide a version with explicit bounds instead.
theorem DiniUpper_add_le_pred_holds (φ ψ : ℝ → ℝ) (t : ℝ)
  (hφ_fin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hψ_fin : DiniUpperE ψ t ≠ ⊤ ∧ DiniUpperE ψ t ≠ ⊥)
  (hsum_fin : DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊤ ∧
              DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊥)
  (hubφ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((φ (t + h) - φ t) / h) ≤ M)
  (hlbφ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((φ (t + h) - φ t) / h))
  (hubψ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((ψ (t + h) - ψ t) / h) ≤ M)
  (hlbψ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((ψ (t + h) - ψ t) / h))
  (hubsum : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M)
  (hlbsum : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)) :
  DiniUpper_add_le_pred φ ψ t :=
by
  exact DiniUpper_add_le_pred_of_bounds φ ψ t hφ_fin hψ_fin hsum_fin
    hubφ hlbφ hubψ hlbψ hubsum hlbsum

/--
Gronwall-type exponential bound (statement): if a nonnegative function
`W` satisfies a linear differential inequality in the upper Dini sense,
then it contracts exponentially. Used to derive EVI contraction.
This is a statement-only placeholder at this phase.
-/
def gronwall_exponential_contraction_pred (lam : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) →
    ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0

/-- Inhomogeneous Grönwall-type bound (statement) -/
def gronwall_exponential_contraction_with_error_half_pred (lam η : ℝ)
  (W : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) →
    ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t

/- Contraction property statement (no proof here) -/
def ContractionProperty {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∀ t : ℝ,
    dist (u t) (v t) ≤ Real.exp (- P.lam * t) * dist (u 0) (v 0)

/-- Squared-distance version of the contraction property, aligned with the
Gronwall inequality that yields an `exp (-(2λ) t)` decay. -/
def ContractionPropertySq {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∀ t : ℝ,
    d2 (u t) (v t) ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0)

/-- Bridge hypothesis from squared-distance contraction to linear-distance
contraction. This encapsulates the usual `sqrt`-monotonicity and algebraic
identities that convert

  d2(u t, v t) ≤ exp (-(2λ) t) · d2(u 0, v 0)

into

  dist(u t, v t) ≤ exp (-λ t) · dist(u 0, v 0).

At this phase, we keep it as a named predicate to be provided by later
analytic lemmas, allowing higher-level theorems to depend only on this
bridge without committing to heavy proofs here. -/
def Hbridge {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ContractionPropertySq P u v → ContractionProperty P u v

/-- Assumption pack providing a concrete bridge from squared-distance
contraction to linear-distance contraction. In later phases this will be
constructed from square-root monotonicity and algebraic identities. -/
structure BridgeAssumptions {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop where
  (bridge : Hbridge P u v)

/-- Extract the bridge from the assumption pack. -/
theorem Hbridge_from_assumptions {X : Type*} [PseudoMetricSpace X]
  {P : EVIProblem X} {u v : ℝ → X}
  (H : BridgeAssumptions P u v) : Hbridge P u v :=
  H.bridge

/-! Helper lemmas (statement-level) for the bridge -/

/-- Square root of the squared distance equals the distance (statement). -/
def sqrt_d2_dist {X : Type*} [PseudoMetricSpace X]
  (x y : X) : Prop :=
  Real.sqrt (d2 x y) = dist x y

/-- Factorization of the square root of a product under nonnegativity
assumptions (statement). We parameterize the nonnegativity as explicit
arguments to align with `Real.sqrt_mul`. -/
def sqrt_mul_nonneg (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) : Prop :=
  Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b

/-- Square root of an exponential halves the exponent (statement). -/
def sqrt_exp_halves (x : ℝ) : Prop :=
  Real.sqrt (Real.exp x) = Real.exp (x / 2)

end Frourio
