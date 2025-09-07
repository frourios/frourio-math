import Frourio.Analysis.EVI.EVICore2
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

/-- Concrete bridge from squared-distance to linear-distance contraction.
It combines `sqrt_d2_dist_prop`, `sqrt_mul_nonneg_prop`, and
`sqrt_exp_halves_prop` with `Real.sqrt_le_sqrt` to pass to distances. -/
theorem bridge_contraction_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hSq : ContractionPropertySq P u v) :
  ContractionProperty P u v := by
  intro t
  have h := hSq t
  -- Both sides of the inequality are nonnegative, so `sqrt` preserves `≤`.
  have hL_nonneg : 0 ≤ d2 (u t) (v t) := by
    dsimp [d2]; exact sq_nonneg _
  have hR_nonneg : 0 ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) := by
    have hx : 0 ≤ Real.exp (-(2 * P.lam) * t) := le_of_lt (Real.exp_pos _)
    have hy : 0 ≤ d2 (u 0) (v 0) := by dsimp [d2]; exact sq_nonneg _
    exact mul_nonneg hx hy
  have hsqrt :
      Real.sqrt (d2 (u t) (v t)) ≤
        Real.sqrt (Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0)) :=
    Real.sqrt_le_sqrt h
  -- Normalize associativity in the exponential argument.
  have hassoc3 : (-(2 * P.lam) * t) = (-(2 * P.lam * t)) := by simp [mul_assoc]
  have hsqrt' :
      Real.sqrt (d2 (u t) (v t)) ≤
        Real.sqrt (Real.exp (-(2 * P.lam * t)) * d2 (u 0) (v 0)) := by
    simpa [hassoc3] using hsqrt
  -- Rewrite both sides via helper lemmas.
  have hLrw : Real.sqrt (d2 (u t) (v t)) = dist (u t) (v t) :=
    sqrt_d2_dist_prop _ _
  have hMul :
      Real.sqrt (Real.exp (-(2 * P.lam * t)) * d2 (u 0) (v 0)) =
        Real.sqrt (Real.exp (-(2 * P.lam * t))) *
          Real.sqrt (d2 (u 0) (v 0)) := by
    -- Apply the product rule for square roots under nonnegativity
    have hx : 0 ≤ Real.exp (-(2 * P.lam * t)) := le_of_lt (Real.exp_pos _)
    have hy : 0 ≤ d2 (u 0) (v 0) := by dsimp [d2]; exact sq_nonneg _
    simpa using sqrt_mul_nonneg_prop (Real.exp (-(2 * P.lam * t))) (d2 (u 0) (v 0)) hx hy
  have hErw : Real.sqrt (Real.exp (-(2 * P.lam * t))) = Real.exp (-(P.lam) * t) := by
    -- √(exp(x)) = exp(x/2) with x = (-(2 λ) t); then simplify the half.
    have hx := sqrt_exp_halves_prop (x := (-(2 * P.lam * t)))
    dsimp [sqrt_exp_halves] at hx
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hdiv : ((2 : ℝ) * (P.lam * t)) / 2 = (P.lam * t) := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      simp [mul_comm, h2]
    have hhalf : (-(2 * P.lam * t)) / 2 = -(P.lam * t) := by
      have : (-(2 * P.lam * t)) = -((2 : ℝ) * (P.lam * t)) := by ring
      have hneg : -((2 : ℝ) * (P.lam * t)) / 2 = -(((2 : ℝ) * (P.lam * t)) / 2) := by
        simp [neg_div]
      simpa [this, hdiv] using hneg
    simpa [hhalf] using hx
  have h0rw : Real.sqrt (d2 (u 0) (v 0)) = dist (u 0) (v 0) :=
    sqrt_d2_dist_prop _ _
  have hRrw :
      Real.sqrt (Real.exp (-(2 * P.lam * t)) * d2 (u 0) (v 0)) =
        Real.exp (-(P.lam) * t) * dist (u 0) (v 0) := by
    simpa [hErw, h0rw] using hMul
  -- Conclude after rewriting.
  simpa [hLrw, hRrw] using hsqrt'

/-- Pack the concrete bridge as an `Hbridge`. -/
theorem Hbridge_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) :
  Hbridge P u v :=
by
  intro hSq; exact bridge_contraction_concrete P u v hSq

-- The concrete bridge proof below combines
-- `sqrt_d2_dist_prop`, `sqrt_mul_nonneg_prop`, and `sqrt_exp_halves_prop`
-- with `Real.sqrt_le_sqrt` and elementary arithmetic rewrites.

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

-- moved below after `eviContraction_general`

/--
EVI contraction (self-curve special case).

Proof sketch: For any curve `u`, the contraction inequality against itself
reduces to `0 ≤ exp(-λ t) * 0`, since `dist (u t) (u t) = 0 = dist (u 0) (u 0)`.
Thus the desired inequality holds by reflexivity of `≤` on `0`.

This serves as a minimal, fully formal base case toward the full EVI
contraction proof (Gronwall-based) developed in later phases.
-/
theorem evi_contraction_self {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u : ℝ → X)
  (_hu : IsEVISolution P u) :
  ContractionProperty P u u := by
  intro t
  -- `dist (u t) (u t) = 0` and `dist (u 0) (u 0) = 0`
  have hL : dist (u t) (u t) = 0 := dist_self _
  have hR : dist (u 0) (u 0) = 0 := dist_self _
  -- RHS is `exp(-λ t) * 0 = 0`
  simp

/-- If the upper Dini differential inequality holds for the squared distance
and we have a Gronwall-type exponential contraction lemma for a function `W`,
then we obtain the squared-distance contraction property. This bridges the
EVI inequality to a ready-to-use decay statement without performing the
sqrt-step to linear distance yet. -/
theorem evi_contraction_sq_from_gronwall {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionPropertySq P u v := by
  -- Directly feed the differential inequality into the Gronwall helper.
  exact Hgr (by intro t; simpa using Hineq2 t)

/-- Final general contraction theorem via a bridge from squared to linear
distances. Given the squared-distance contraction and a user-provided bridge
that converts it to the linear-distance statement (using monotonicity of sqrt
and algebraic identities), we obtain the desired contraction property. -/
theorem eviContraction_general {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t)))
  (Hbridge : Hbridge P u v) :
  ContractionProperty P u v :=
by
  apply Hbridge
  exact evi_contraction_sq_from_gronwall P u v hu hv Hineq2 Hgr

/--
EVI contraction (named theorem form, P0 skeleton).

Proof strategy: Assume the squared-distance Dini inequality and a Grönwall
exponential decay statement for `W t = d2 (u t) (v t)`. This yields a
`ContractionPropertySq`. A bridge hypothesis converts it into the linear
`ContractionProperty`. Heavy analytic parts are abstracted as inputs.
-/
theorem eviContraction_thm
  {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t)))
  (Hbridge : Hbridge P u v) :
  ContractionProperty P u v :=
by
  exact eviContraction_general P u v hu hv Hineq2 Hgr Hbridge

/--
Concrete EVI contraction wrapper (closed via G1 + B1).

Given the squared-distance differential inequality for `W t = d2(u t, v t)`
and the Grönwall predicate `gronwall_exponential_contraction_pred`, this
derives the linear-distance contraction using the concrete bridge
`bridge_contraction_concrete`.

This closes the contraction pipeline without requiring an external
`Hbridge` argument. -/
theorem evi_contraction_thm_concrete
  {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionProperty P u v :=
by
  -- First get the squared-distance contraction via Grönwall (G1)
  have hSq : ContractionPropertySq P u v :=
    evi_contraction_sq_from_gronwall P u v hu hv Hineq2 Hgr
  -- Then bridge to linear distance via the concrete bridge (B1)
  exact bridge_contraction_concrete P u v hSq

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

/-- Mixed EVI sum without error (half form): expected output of the
"add-and-absorb-cross-terms" step when the geometry yields no residual error. -/
def eviSumNoError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v)
  (_geodesicBetween : Prop) : Prop :=
  ∀ t : ℝ,
    (1 / 2 : ℝ) * DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + P.lam * d2 (u t) (v t) ≤ 0

/--
Squared-distance synchronization with error (P0 skeleton).

Assume a mixed EVI inequality with error term `η` for `W t = d2(u t, v t)`
and an inhomogeneous Grönwall lemma. Then

  d2(u t, v t) ≤ exp (-(2 λ) t) · d2(u 0, v 0) + (2 η) t.

Bridging to linear distance can be added separately via a dedicated lemma.
-/
def ContractionPropertySqWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) : Prop :=
  ∀ t : ℝ,
    d2 (u t) (v t)
      ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) + (2 * η) * t

/-- Synchronization with error in squared distance via inhomogeneous Grönwall. -/
theorem eviSynchronizationSq_with_error {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (_geodesicBetween : Prop) (hR : MixedErrorBound X u v)
  (Hsum : eviSumWithError P u v hu hv _geodesicBetween hR)
  (Hgr : (∀ t : ℝ, (1 / 2 : ℝ) *
            DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
            + P.lam * d2 (u t) (v t) ≤ hR.η) →
          ∀ t : ℝ,
            d2 (u t) (v t)
              ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) + (2 * hR.η) * t) :
  ContractionPropertySqWithError P u v hR.η :=
by
  intro t
  -- Apply the provided Grönwall lemma to W(t) = d2(u t, v t)
  have :
      ∀ s : ℝ, (1 / 2 : ℝ) * DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) s
        + P.lam * d2 (u s) (v s) ≤ hR.η := by
    intro s; simpa using Hsum s
  simpa using Hgr this t

end Frourio
