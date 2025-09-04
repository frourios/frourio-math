import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic

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

/- Upper Dini derivative (upper right Dini via limsup of forward quotients). -/
noncomputable def DiniUpper (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Filter.limsup (fun h : ℝ => (φ (t + h) - φ t) / h)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/- If `φ` is nonincreasing, then the upper Dini derivative is ≤ 0. -/
theorem DiniUpper_nonpos_of_nonincreasing (φ : ℝ → ℝ) (t : ℝ)
  (Hmono : ∀ ⦃s u : ℝ⦄, s ≤ u → φ u ≤ φ s) :
  DiniUpper φ t ≤ 0 := by
  -- Detailed filter-based proof deferred; standard fact from real analysis.
  -- Each forward quotient `(φ (t + h) - φ t)/h` is ≤ 0 for `h > 0`,
  -- hence the limsup is ≤ 0.
  admit

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

/-- Time-rescale of a curve `u` by a positive factor `σ` (skeleton). -/
def timeRescale {X : Type*} (σ : ℝ) (u : ℝ → X) : ℝ → X :=
  fun t => u (σ * t)

/-- Statement-level helper: scaling rule for upper Dini derivative under
time reparameterization `t ↦ σ t` (to be proven in later phases). -/
def DiniUpper_timeRescale_pred (σ : ℝ) (φ : ℝ → ℝ) (t : ℝ) : Prop :=
  DiniUpper (fun τ => φ (σ * τ)) t = σ * DiniUpper φ (σ * t)

/--
Basic subadditivity lemma (statement): the upper Dini derivative of a
sum is bounded above by the sum of upper Dini derivatives. This is a
statement-only placeholder used in G-proofs; the quantitative proof is
introduced in later phases.
-/
def DiniUpper_add_le_pred (φ ψ : ℝ → ℝ) (t : ℝ) : Prop :=
  DiniUpper (fun τ => φ τ + ψ τ) t ≤ DiniUpper φ t + DiniUpper ψ t

/--
Gronwall-type exponential bound (statement): if a nonnegative function
`W` satisfies a linear differential inequality in the upper Dini sense,
then it contracts exponentially. Used to derive EVI contraction.
This is a statement-only placeholder at this phase.
-/
def gronwall_exponential_contraction_pred (lam : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) →
    ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0

/-- Inhomogeneous Grönwall-type bound (statement): if
`(1/2)·DiniUpper W + lam·W ≤ η`, then `W` admits a linear-in-time upper bound
of the form `exp (-(2 lam) t) · W 0 + (2 η) t`. This is a placeholder
capturing the shape needed for two-EVI synchronization with an error term. -/
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

/-! Proofs for the helper lemmas -/

theorem sqrt_d2_dist_prop {X : Type*} [PseudoMetricSpace X]
  (x y : X) : sqrt_d2_dist x y := by
  dsimp [sqrt_d2_dist, d2]
  -- Reduce to `sqrt ((dist x y)^2) = |dist x y|` and drop `|·|` via nonnegativity.
  have h := Real.sqrt_sq_eq_abs (dist x y)
  simp [h, abs_of_nonneg dist_nonneg]

theorem sqrt_mul_nonneg_prop (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  sqrt_mul_nonneg a b ha hb := by
  dsimp [sqrt_mul_nonneg]
  -- Rewrite a*b as a square of (√a * √b)
  have hsq : a * b = (Real.sqrt a * Real.sqrt b) ^ (2 : ℕ) := by
    simp [pow_two, mul_comm, mul_left_comm,
      Real.mul_self_sqrt ha, Real.mul_self_sqrt hb]
  have hrewrite :
      Real.sqrt (a * b) = Real.sqrt ((Real.sqrt a * Real.sqrt b) ^ (2 : ℕ)) := by
    simp [hsq]
  -- Apply √(z^2) = |z| and drop absolute value using nonnegativity.
  have hnonneg : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  simp [hrewrite, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]


theorem sqrt_exp_halves_prop (x : ℝ) : sqrt_exp_halves x := by
  dsimp [sqrt_exp_halves]
  have hxmul : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    simpa [add_halves] using (Real.exp_add (x / 2) (x / 2)).symm
  have hx' : Real.exp x = (Real.exp (x / 2)) ^ (2 : ℕ) := by
    simpa [pow_two] using hxmul.symm
  have hxpos : 0 < Real.exp (x / 2) := Real.exp_pos _
  -- Conclude via `sqrt (y^2) = |y|` and positivity of `exp`.
  simp [hx', Real.sqrt_sq_eq_abs, abs_of_pos hxpos]

/-- DiniUpper additivity upper bound (wrapper theorem from the predicate). -/
theorem DiniUpper_add_le (φ ψ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_add_le_pred φ ψ t) :
  DiniUpper (fun τ => φ τ + ψ τ) t ≤ DiniUpper φ t + DiniUpper ψ t := H

/-- Time-rescaling rule for DiniUpper (wrapper theorem from the predicate). -/
theorem DiniUpper_timeRescale (σ : ℝ) (φ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_timeRescale_pred σ φ t) :
  DiniUpper (fun τ => φ (σ * τ)) t = σ * DiniUpper φ (σ * t) := H

/-- Homogeneous Grönwall inequality (wrapper theorem from the predicate). -/
theorem gronwall_exponential_contraction (lam : ℝ) (W : ℝ → ℝ)
  (H : (∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) →
        ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 := H Hineq

/-- Inhomogeneous Grönwall inequality in the `half` form (wrapper theorem). -/
theorem gronwall_exponential_contraction_with_error_half
  (lam η : ℝ) (W : ℝ → ℝ)
  (H : (∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) →
        ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t := H Hineq

/-- Special case: time-reparameterization with unit factor is tautological. -/
theorem DiniUpper_timeRescale_one (φ : ℝ → ℝ) (t : ℝ) :
  DiniUpper (fun τ => φ (1 * τ)) t = (1 : ℝ) * DiniUpper φ (1 * t) := by
  -- Trivial by rewriting the argument and factor `1`.
  simp [DiniUpper, one_mul]

/-- Special case of homogeneous Grönwall at `λ = 0` using a provided predicate. -/
theorem gronwall_exponential_contraction_zero
  (W : ℝ → ℝ)
  (H : (∀ t : ℝ, DiniUpper W t + (2 * (0 : ℝ)) * W t ≤ 0) →
        ∀ t : ℝ, W t ≤ Real.exp (-(2 * (0 : ℝ)) * t) * W 0)
  (Hineq0 : ∀ t : ℝ, DiniUpper W t ≤ 0) :
  ∀ t : ℝ, W t ≤ W 0 := by
  have h := gronwall_exponential_contraction (0 : ℝ) W H (by
    intro t; simpa [zero_mul, add_comm] using (Hineq0 t))
  intro t; simpa [zero_mul, Real.exp_zero] using h t

/-- Special case of inhomogeneous Grönwall at `η = 0` using a provided predicate. -/
theorem gronwall_exponential_contraction_with_error_zero
  (lam : ℝ) (W : ℝ → ℝ)
  (H : (∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ 0) →
        ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0)
  (Hineq0 : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 := by
  -- Adapt `H` to the `η = 0` version expected by the `with_error_half` helper.
  have H' : (∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ (0 : ℝ)) →
            ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * (0 : ℝ)) * t := by
    intro hineq
    have h0 := H (by intro t; simpa using hineq t)
    intro t; simpa [zero_mul, add_comm] using h0 t
  have h := gronwall_exponential_contraction_with_error_half lam 0 W H' (by
    intro t; simpa using (Hineq0 t))
  intro t; simpa [zero_mul, add_comm] using h t

/-- Concrete bridge from squared-distance contraction to linear-distance
contraction using monotonicity of `Real.sqrt` and algebraic identities. -/
theorem bridge_contraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (H : Hbridge P u v) (hSq : ContractionPropertySq P u v) :
  ContractionProperty P u v :=
H hSq

-- Closed contraction theorem can be produced by combining
-- `evi_contraction_sq_from_gronwall` with a concrete `Hbridge`.

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
        Real.sqrt (Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0)) := by
    -- `sqrt` is monotone on nonnegative reals
    exact Real.sqrt_le_sqrt h
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
  have hErw : Real.sqrt (Real.exp (-(2 * P.lam) * t)) = Real.exp (-(P.lam) * t) := by
    -- √(exp(x)) = exp(x/2) with x = -(2 λ) t; simplify (-(2λ) t)/2 = -(λ t).
    have hx := sqrt_exp_halves_prop (-(2 * P.lam * t))
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hassoc : (2 * P.lam * t) = 2 * (P.lam * t) := by simp [mul_assoc]
    have hdiv : ((2 : ℝ) * (P.lam * t)) / 2 = (P.lam * t) := by
      simpa [mul_comm] using (mul_div_cancel (P.lam * t) h2)
    -- ((-(2λ) * t)) / 2 = -(λ * t)
    have hhalf : ((-(2 * P.lam) * t)) / 2 = -(P.lam * t) := by
      -- rewrite to -(2 * (λ * t)) / 2
      have : (-(2 * P.lam) * t) = -((2 * P.lam * t)) := by simp [mul_assoc]
      -- and use `neg_div` + `mul_div_cancel'`
      have hneg : -((2 * P.lam * t)) / 2 = -(((2 * P.lam * t)) / 2) := by
        simpa [neg_div]
      have : -(((2 * P.lam * t)) / 2) = -(P.lam * t) := by
        simpa [hassoc, hdiv]
      simpa [this] using hneg
    -- put pieces together
    have hstep : Real.sqrt (Real.exp (-(2 * P.lam) * t)) = Real.exp (((-(2 * P.lam) * t)) / 2) := by
      -- convert to the associativity form used in `hx`
      have hassoc2 : (-(2 * P.lam) * t) = (-(2 * P.lam * t)) := by
        simp [mul_assoc]
      simpa [hassoc2] using hx
    -- align the halving rewrite with the associativity form
    have hassoc2' : (-(2 * P.lam) * t) = (-(2 * P.lam * t)) := by
      simp [mul_assoc]
    have hhalf2 : (-(2 * P.lam * t)) / 2 = -(P.lam * t) := by
      simpa [hassoc2'] using hhalf
    simpa [hhalf2] using hstep
  have h0rw : Real.sqrt (d2 (u 0) (v 0)) = dist (u 0) (v 0) :=
    sqrt_d2_dist_prop _ _
  have hErw' : Real.sqrt (Real.exp (-(2 * P.lam * t))) = Real.exp (-(P.lam) * t) := by
    simpa [hassoc3] using hErw
  have hRrw :
      Real.sqrt (Real.exp (-(2 * P.lam * t)) * d2 (u 0) (v 0)) =
        Real.exp (-(P.lam) * t) * dist (u 0) (v 0) := by
    simpa [hErw', h0rw] using hMul
  -- Conclude after rewriting.
  simpa [hLrw, hRrw] using hsqrt'

/-- Pack the concrete bridge as an `Hbridge`. -/
theorem Hbridge_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) :
  Hbridge P u v :=
by
  intro hSq; exact bridge_contraction_concrete P u v hSq

/-- Concrete bridge: from squared-distance contraction to linear-distance
contraction using monotonicity of `Real.sqrt` and algebraic identities. -/
-- A concrete bridge proof can be added in a later phase by combining
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

/-- Distance-version synchronization with error. From the squared-distance
bound and algebraic `sqrt` identities, derive

  dist(u t, v t) ≤ exp (-(P.lam) t) · dist(u 0, v 0) + √(max 0 ((2 η) t)).

We use `max 0` to keep the radicand nonnegative when `η t < 0`. -/
def ContractionPropertyWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) : Prop :=
  ∀ t : ℝ,
    dist (u t) (v t) ≤
      Real.exp (-(P.lam) * t) * dist (u 0) (v 0)
        + Real.sqrt (max 0 ((2 * η) * t))

/-- Error-bridge predicate from squared to linear distance with an error term. -/
def HbridgeWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) : Prop :=
  ContractionPropertySqWithError P u v η → ContractionPropertyWithError P u v η

/-- Wrapper: apply a provided error-bridge to convert squared to linear distance. -/
theorem bridge_with_error {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ)
  (H : HbridgeWithError P u v η)
  (Hsq : ContractionPropertySqWithError P u v η) :
  ContractionPropertyWithError P u v η :=
H Hsq


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

/- Externalized Mosco predicates (minimal, nontrivial P0 forms).
They remain `Prop`-valued and lightweight, but relate the system fields
to avoid `True` stubs. -/
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

/-- Assumption pack using the minimal nontrivial Mosco predicates. -/
structure MoscoAssumptions {ι : Type*} (S : MoscoSystem ι) : Prop where
  (geodesic_complete : MoscoGeodesicComplete S)
  (tightness : MoscoTight S)
  (lsc_Ent : True)
  (M1 : MoscoM1 S)
  (M2 : MoscoM2 S)

/-- Limit EVI property under Mosco convergence (minimal nontrivial form).
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

end Frourio
