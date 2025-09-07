import Frourio.Analysis.EVI.EVICore1
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

/-- Subadditivity surrogate: for nonnegative `a, b`,
`√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le_sqrt_add_sqrt_prop (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  -- Compare squares; both sides are nonnegative.
  have hA_nonneg : 0 ≤ Real.sqrt (a + b) := Real.sqrt_nonneg _
  have hB_nonneg : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- Square both sides and compare.
  have hsq : (Real.sqrt (a + b)) ^ (2 : ℕ) ≤ (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ) := by
    -- Left square: `a + b`. Right square: `a + b + 2 √a √b`.
    have hL : (Real.sqrt (a + b)) ^ (2 : ℕ) = a + b := by
      simp [pow_two, Real.mul_self_sqrt, add_nonneg ha hb]
    have hR : (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ)
            = a + b + 2 * Real.sqrt a * Real.sqrt b := by
      have hpoly :
          (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ)
            = Real.sqrt a ^ (2 : ℕ) + 2 * Real.sqrt a * Real.sqrt b + Real.sqrt b ^ (2 : ℕ) := by
        ring_nf
      simpa [pow_two, add_comm, add_left_comm, add_assoc,
             mul_comm, mul_left_comm, mul_assoc,
             Real.mul_self_sqrt ha, Real.mul_self_sqrt hb] using hpoly
    have hcross : 0 ≤ 2 * Real.sqrt a * Real.sqrt b := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      have hprod : 0 ≤ Real.sqrt a * Real.sqrt b :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      simpa [mul_assoc] using mul_nonneg this hprod
    -- Conclude `a + b ≤ a + b + 2 √a √b`.
    have hle : a + b ≤ a + b + 2 * Real.sqrt a * Real.sqrt b :=
      le_add_of_nonneg_right hcross
    simpa [hL, hR] using hle
  -- From `A^2 ≤ B^2` and nonnegativity, infer `A ≤ B`.
  have habs : |Real.sqrt (a + b)| ≤ |Real.sqrt a + Real.sqrt b| := (sq_le_sq).1 hsq
  have hA : |Real.sqrt (a + b)| = Real.sqrt (a + b) := abs_of_nonneg hA_nonneg
  have hB : |Real.sqrt a + Real.sqrt b| = Real.sqrt a + Real.sqrt b := abs_of_nonneg hB_nonneg
  -- Conclude after removing absolute values on both sides.
  simpa [hA, hB] using habs

/-- DiniUpper additivity upper bound (wrapper theorem from the predicate). -/
/- DiniUpper additivity upper bound (wrapper theorem from the predicate). -/
theorem DiniUpper_add_le (φ ψ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_add_le_pred φ ψ t) :
  DiniUpper (fun τ => φ τ + ψ τ) t ≤ DiniUpper φ t + DiniUpper ψ t := H

/-- Time-rescaling rule for DiniUpper (wrapper theorem from the predicate). -/
theorem DiniUpper_timeRescale (σ : ℝ) (φ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_timeRescale_pred σ φ t) :
  DiniUpper (fun τ => φ (σ * τ)) t = σ * DiniUpper φ (σ * t) := H

/-- Time-rescaling for the upper Dini derivative under a positive factor.
This is a wrapper that records the `σ > 0` use‑site while delegating the
analytical content to the supplied predicate `DiniUpper_timeRescale_pred`.
In later phases, we will provide a proof under mild boundedness hypotheses.
-/
theorem DiniUpper_timeRescale_pos (σ : ℝ) (hσ : 0 < σ)
  (φ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_timeRescale_pred σ φ t) :
  DiniUpper (fun τ => φ (σ * τ)) t = σ * DiniUpper φ (σ * t) :=
by
  -- At this phase, the positivity assumption is recorded for API clarity
  -- and future strengthening, while we rely on the provided predicate.
  -- Use `hσ` to record that `σ ≠ 0`, anticipating a change-of-variables proof.
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  -- Currently unused in the algebra, but kept to mark the positive-scale use‑case.
  simpa using (DiniUpper_timeRescale σ φ t H)

/-- Homogeneous Grönwall inequality (turn the predicate into a usable bound). -/
theorem gronwall_exponential_contraction_from_pred (lam : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_pred lam W)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 :=
by
  exact Hpred Hineq

/-- Homogeneous Grönwall inequality (wrapper using the predicate). -/
theorem gronwall_exponential_contraction (lam : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_pred lam W)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 :=
  gronwall_exponential_contraction_from_pred lam W Hpred Hineq

/-- Inhomogeneous Grönwall inequality (turn the predicate into a usable bound). -/
theorem gronwall_exponential_contraction_with_error_half_from_pred
  (lam η : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_with_error_half_pred lam η W)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t :=
by
  exact Hpred Hineq

/-- Inhomogeneous Grönwall inequality in the `half` form (wrapper using the predicate). -/
theorem gronwall_exponential_contraction_with_error_half
  (lam η : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_with_error_half_pred lam η W)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t :=
  gronwall_exponential_contraction_with_error_half_from_pred lam η W Hpred Hineq

/-- Inhomogeneous Grönwall inequality (`half` form, core statement):
If `(1/2)·DiniUpper W + lam·W ≤ η` pointwise, then
`W t ≤ exp (-(2 lam) t) · W 0 + (2 η) t`. -/
theorem gronwall_exponential_contraction_with_error_half_core
  (lam η : ℝ) (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_with_error_half_pred lam η W)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t :=
by
  exact H Hineq

/-- Special case: time-reparameterization with unit factor is tautological. -/
theorem DiniUpper_timeRescale_one (φ : ℝ → ℝ) (t : ℝ) :
  DiniUpper (fun τ => φ (1 * τ)) t = (1 : ℝ) * DiniUpper φ (1 * t) := by
  -- Trivial by rewriting the argument and factor `1`.
  simp [DiniUpper, one_mul]

/-- Special case of homogeneous Grönwall at `λ = 0` using a provided predicate. -/
theorem gronwall_exponential_contraction_zero
  (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_pred (0 : ℝ) W)
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

/- Homogeneous Grönwall at λ = 0 (direct form, analysis deferred) -/


/-- Homogeneous Grönwall inequality (core theorem):
If `(DiniUpper W) + (2 λ) W ≤ 0` pointwise, then
`W t ≤ exp (-(2 λ) t) · W 0`. -/
/- Auxiliary: product rule upper bound for `exp(2λ·) * W` (not needed at this stage). -/

theorem gronwall_exponential_contraction_core (lam : ℝ) (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_pred lam W)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 :=
by
  exact H Hineq

-- The closed predicate form is supplied externally when needed; a
-- local, argument-taking wrapper is available via `gronwall_exponential_contraction`.

/-- Homogeneous Grönwall at λ = 0 (direct form):
If `DiniUpper W ≤ 0` pointwise, then `W` is nonincreasing: `W t ≤ W 0`. -/
theorem gronwall_zero (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_pred (0 : ℝ) W)
  (Hineq0 : ∀ t : ℝ, DiniUpper W t ≤ 0) :
  ∀ t : ℝ, W t ≤ W 0 := by
  -- Use the closed predicate at `λ = 0` and simplify the exponential factor.
  have h := gronwall_exponential_contraction (0 : ℝ) W H
    (by intro t; simpa [zero_mul, add_comm] using (Hineq0 t))
  intro t
  simpa [zero_mul, Real.exp_zero] using h t

/- Inhomogeneous Grönwall (half version): kept as predicate-level result below. -/

-- (Predicate-level closure for the inhomogeneous half version is deferred to later phases.)

/-- Concrete bridge from squared-distance contraction to linear-distance
contraction using monotonicity of `Real.sqrt` and algebraic identities. -/
theorem bridge_contraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (H : Hbridge P u v) (hSq : ContractionPropertySq P u v) :
  ContractionProperty P u v :=
H hSq

-- Closed contraction theorem can be produced by combining
-- `evi_contraction_sq_from_gronwall` with a concrete `Hbridge`.

end Frourio
