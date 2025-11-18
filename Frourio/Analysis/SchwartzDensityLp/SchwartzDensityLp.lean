import Frourio.Analysis.SchwartzDensityLp.SchwartzDensityLpCore1
import Frourio.Analysis.SchwartzDensityLp.ConvolutionTheory
import Frourio.Analysis.SchwartzDensityLp.ApproximateIdentity
import Frourio.Analysis.YoungInequality.YoungInequality
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate

variable {n : ℕ}

/--
Control of the L² norm from Schwartz pairings.

If a complex-valued function `f` on ℝ has uniformly bounded pairings against
all Schwartz test functions in L², with bound
`‖∫ f · conj φ‖ ≤ C · ‖φ‖₂` for some nonnegative `C`, then `f` belongs to L².

This is a specialization of the Riesz representation / L² duality theorem
to the dense subspace of Schwartz functions, and will be used in
`FourierPlancherelL2.lean` to upgrade distributional control to L² control.

Only the statement is provided here; the proof is deferred.
-/
lemma memLp_two_of_schwartz_pairing_bound
    (f : ℝ → ℂ) (C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hpair :
      ∀ φ : SchwartzMap ℝ ℂ,
        ‖∫ t, f t * conj (φ t) ∂volume‖
          ≤ C * (eLpNorm (fun t => φ t) 2 volume).toReal) :
    MemLp f 2 volume := by
  classical
  sorry
