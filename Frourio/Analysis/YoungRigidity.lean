import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Complex

namespace Frourio

open scoped BigOperators
open scoped Topology

/- Convenience alias for measures on ℝ. -/
abbrev MeasureR := MeasureTheory.Measure ℝ

/- Abstract norms (R: placeholders; Z: concrete via infinite sums). -/
noncomputable def L2NormR (_f : ℝ → ℂ) : ℝ := 0

/- Total variation norm placeholder for a measure on ℝ. -/
noncomputable def TVNorm (_ν : MeasureR) : ℝ := 0

noncomputable def L2NormZ (a : ℤ → ℂ) : ℝ :=
  Real.sqrt (∑' n : ℤ, ‖a n‖ ^ (2 : ℕ))

noncomputable def L1NormZ (μ : ℤ → ℂ) : ℝ :=
  ∑' n : ℤ, ‖μ n‖

/- Convolutions (R: measured kernel wrapper; Z: discrete sum). -/
noncomputable def convR_measure (_f : ℝ → ℂ) (_ν : MeasureR) : ℝ → ℂ :=
  fun _x => 0

noncomputable def convZ (a : ℤ → ℂ) (μ : ℤ → ℂ) : ℤ → ℂ :=
  fun n => ∑' k : ℤ, a k * μ (n - k)

/- Rigidity via phase-Dirac model (statement only). -/
structure DiracLike where
  (phase : ℝ)
  (s0 : ℝ)

/-- A concrete nonzero test function on ℝ → ℂ: the constant-one map. -/
noncomputable def oneFunc : ℝ → ℂ := fun _ => (1 : ℂ)

lemma oneFunc_ne_zero : oneFunc ≠ (fun _ => (0 : ℂ)) := by
  intro h
  have h0 := congrArg (fun g : (ℝ → ℂ) => g 0) h
  dsimp [oneFunc] at h0
  exact (one_ne_zero : (1 : ℂ) ≠ 0) h0

/-- Linearity of `convR_measure` in the function argument (statement-only). -/
def convR_measure_is_linear (ν : MeasureR) : Prop :=
  ∀ (f g : ℝ → ℂ) (c : ℂ),
    (convR_measure (fun x => f x + g x) ν =
      fun x => convR_measure f ν x + convR_measure g ν x)
    ∧ (convR_measure (fun x => c • f x) ν =
      fun x => c • convR_measure f ν x)

end Frourio
