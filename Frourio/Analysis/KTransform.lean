import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace Frourio

/-!
FG8 A3: K-transform skeleton and basic model

This module introduces a lightweight `KTransform` structure capturing the
multi-point transform `𝒦_σ` as a map into (signed) kernels on `ℝ` together
with minimal predicates representing (K1′) narrow continuity and (K4^m)
geodesic affinity. A 1D basic model is provided to serve as a concrete
instance. The design remains proof-light and avoids measure-theoretic load.
-/

section X
variable {X : Type*} [PseudoMetricSpace X]

/-- K-transform: a map attaching to each state `x : X` a kernel on `ℝ`.
The payload is an arbitrary function `ℝ → ℝ` at this phase. -/
structure KTransform (X : Type*) [PseudoMetricSpace X] where
  (map : X → ℝ → ℝ)
  (narrowContinuous : Prop)

/-- (K1′) surrogate: narrow continuity predicate. -/
def K1primeK (K : KTransform X) : Prop := K.narrowContinuous

/-- Auxiliary predicate: a uniform lower bound for the kernel at `s = 0`.
This lightweight surrogate is used to produce coercivity-style bounds for
`Dσm` when building the functional layer. -/
def UniformLowerBoundAtZero (K : KTransform X) (C0 : ℝ) : Prop :=
  ∀ x : X, K.map x 0 ≥ -C0

/-- Interface: build `Dσm` from a `KTransform` and a supplied sup-norm bound.
We keep it algebraic via a simple evaluation `map x 0`, scaled by `Ssup`. -/
noncomputable def DsigmamFromK (K : KTransform X) (Ssup : ℝ) : X → ℝ :=
  fun x => Ssup * K.map x 0

end X

/-! Basic boundedness helper for `DsigmamFromK` -/

section Bounds
variable {X : Type*} [PseudoMetricSpace X]

/-- Uniform lower bound for `Dσm` inherited from the kernel lower bound at `s=0`. -/
theorem DsigmamFromK_lower_bound (K : KTransform X) (Ssup C0 : ℝ)
  (hS : 0 ≤ Ssup) (hLB : UniformLowerBoundAtZero K C0) :
  ∀ x : X, DsigmamFromK K Ssup x ≥ -(Ssup * C0) :=
by
  intro x; dsimp [DsigmamFromK]
  have : -C0 ≤ K.map x 0 := by simpa using (hLB x)
  have hmul : Ssup * (-C0) ≤ Ssup * K.map x 0 :=
    mul_le_mul_of_nonneg_left this hS
  simpa [mul_comm, mul_left_comm, mul_assoc, mul_neg, neg_mul, ge_iff_le] using hmul

end Bounds

/-!
General templates to supply `(K1′)` beyond the basic example. These are
lightweight builders that keep narrow continuity as a Prop-level flag, while
offering convenient ways to construct `KTransform`s from pointwise
continuity-in-`x` hypotheses and functorial pullbacks.
-/

section Templates
variable {X : Type*} [PseudoMetricSpace X]

/-- Pointwise continuity in the state variable `x` (for each `s ∈ ℝ`). -/
def PointwiseContinuousInX (map : X → ℝ → ℝ) : Prop :=
  ∀ s : ℝ, Continuous fun x : X => map x s

/-- A template capturing `map` together with a pointwise continuity witness. -/
structure K1primeTemplate (X : Type*) [PseudoMetricSpace X] where
  (map : X → ℝ → ℝ)
  (pointwise_cont : PointwiseContinuousInX map)

/-- Pull back a template along a continuous map `g : Y → X` to obtain a
template on `Y`. This preserves pointwise continuity-in-`x`. -/
def K1primeTemplate.pullback {Y : Type*} [PseudoMetricSpace Y]
  (T : K1primeTemplate X) (g : Y → X) (hg : Continuous g) :
  K1primeTemplate Y :=
{ map := fun y s => T.map (g y) s,
  pointwise_cont := by
    intro s; dsimp; exact (T.pointwise_cont s).comp hg }

/-- Functorial builder: pull back a `KTransform` along `g : Y → X`. The
`narrowContinuous` flag is transported unchanged as a Prop. -/
def KTransform.pullback {Y : Type*} [PseudoMetricSpace Y]
  (K : KTransform X) (g : Y → X) : KTransform Y :=
{ map := fun y s => K.map (g y) s,
  narrowContinuous := K.narrowContinuous }

end Templates

section DisplacementAPI
variable (X : Type*) [PseudoMetricSpace X]

/- Displacement structure: an abstract interpolation `interp x y θ` of states
with endpoint axioms. This keeps the affinity predicate independent of any
specific geodesic machinery. -/
structure Displacement where
  (interp : X → X → ℝ → X)
  (endpoint0 : ∀ x y : X, interp x y 0 = x)
  (endpoint1 : ∀ x y : X, interp x y 1 = y)

end DisplacementAPI

section DisplacementAPI
variable {X : Type*} [PseudoMetricSpace X]

/-- Displacement affinity `(K4^m)` surrogate: along the displacement
interpolation, evaluation of the kernel is affine in `x` for each fixed `s`. -/
def DisplacementAffinity (K : KTransform X) (D : Displacement X) : Prop :=
  ∀ x y : X, ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 → ∀ s : ℝ,
    K.map (D.interp x y θ) s = (1 - θ) * K.map x s + θ * K.map y s

end DisplacementAPI

section LinearOnReal

/- Linear interpolation on `ℝ`. -/
noncomputable def linearDisplacement : Displacement ℝ :=
{ interp := fun x y θ => (1 - θ) * x + θ * y,
  endpoint0 := by intro x y; simp,
  endpoint1 := by intro x y; simp }

end LinearOnReal

end Frourio
