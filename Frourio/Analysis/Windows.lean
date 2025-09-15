import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic

namespace Frourio

open MeasureTheory

/-!
Step 5: STMT Gaussian windows and width control (design-level).

We introduce a Gaussian window and record decay/overlap bounds as `Prop`-level
signatures to be supplied in later phases. This keeps downstream APIs stable
without committing to full analytic proofs here.
-/

/-- Continuous Gaussian profile (real-valued). -/
noncomputable def gaussianFun (α : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(Real.pi) * α * t^2)

/-- L² window (placeholder): the actual `Lp` element will be provided when we
install the precise isometry context. -/
noncomputable def gaussian (_ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) := 0

/-- Decay statement for the Gaussian profile (signature).
Intended: `‖gaussianFun α t‖ ≤ exp(−c α t²)` with a suitable constant `c>0`. -/
def gaussian_decay (α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, |gaussianFun α t| ≤ Real.exp (-c * α * t^2)

/-- Overlap bound between shifted Gaussian peaks at lattice spacing `Δτ` (signature).
Intended: for `k ≠ 0`, `‖g( k Δτ )‖ ≲ exp(−c α (Δτ)² k²)` for some `c>0`. -/
def overlap_bound (α Δτ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℤ, k ≠ 0 →
    |gaussianFun α ((k : ℝ) * Δτ)| ≤ Real.exp (-c * α * (Δτ)^2 * (k : ℝ)^2)

/-- Concrete decay bound holds for any nonnegative `α` with an explicit constant. -/
theorem gaussian_decay_of_nonneg {α : ℝ} (hα : 0 ≤ α) : gaussian_decay α := by
  refine ⟨min Real.pi 1, ?_, ?_⟩
  · -- positivity of the constant
    have h0π : 0 < Real.pi := Real.pi_pos
    have h01 : 0 < (1 : ℝ) := by norm_num
    exact lt_min h0π h01
  · intro t
    -- Reduce absolute value using positivity of the exponential
    have hpos : 0 < Real.exp (-(Real.pi) * α * t^2) := Real.exp_pos _
    have hnorm : |gaussianFun α t| = Real.exp (-(Real.pi) * α * t^2) := by
      simp [gaussianFun]
    -- Monotonicity of exp with comparison of exponents
    have hA : 0 ≤ α * t^2 := mul_nonneg hα (by simpa using sq_nonneg t)
    have hπc : -Real.pi ≤ -(min Real.pi 1) := by
      exact neg_le_neg (min_le_left Real.pi 1)
    have hmul := mul_le_mul_of_nonneg_right hπc hA
    have : Real.exp (-(Real.pi) * (α * t^2)) ≤ Real.exp (-(min Real.pi 1) * (α * t^2)) :=
      Real.exp_le_exp.mpr hmul
    simpa [hnorm, mul_comm, mul_left_comm, mul_assoc]
      using this

end Frourio
