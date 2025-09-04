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

/-- (K4^m) surrogate: geodesic affinity predicate (placeholder). -/
def K4mK (_K : KTransform X) : Prop := True

/-- Auxiliary predicate: a uniform lower bound for the kernel at `s = 0`.
This lightweight surrogate is used to produce coercivity-style bounds for
`Dσm` when building the functional layer. -/
def UniformLowerBoundAtZero (K : KTransform X) (C0 : ℝ) : Prop :=
  ∀ x : X, K.map x 0 ≥ -C0

/-- Interface: build `Dσm` from a `KTransform` and a supplied sup-norm bound.
We keep it algebraic via a simple evaluation `map x 0`, scaled by `Ssup`. -/
noncomputable def DsigmamFromK (K : KTransform X) (Ssup : ℝ) : X → ℝ :=
  fun x => Ssup * K.map x 0

/-! 1D basic model (log isometry surrogate):
We provide a trivial kernel and record that (K1′) and (K4^m) hold by
construction at this phase. -/

noncomputable def KTransform.basic1D : KTransform ℝ :=
  { map := fun _x s => s,
    narrowContinuous := True }

theorem K1prime_basic1D : K1primeK (KTransform.basic1D) := by
  change True
  exact trivial

theorem K4mK_basic1D : K4mK (KTransform.basic1D) := by
  change True
  exact trivial

/-- In the 1D basic model, the kernel at `s = 0` is exactly `0`, hence admits
the uniform lower bound with `C0 = 0`. -/
theorem UniformLowerBoundAtZero_basic1D :
  UniformLowerBoundAtZero (KTransform.basic1D) 0 := by
  intro x; dsimp [UniformLowerBoundAtZero, KTransform.basic1D]; simp

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

/-- Build a `KTransform` from a template. The `narrowContinuous` flag is
set to the (placeholder) Prop `True`, and the pointwise continuity is
kept available from the template for downstream use. -/
noncomputable def KTransform.ofTemplate (T : K1primeTemplate X) : KTransform X :=
  { map := T.map, narrowContinuous := True }

/-- From a template-built transform, we can supply `(K1′)` in the current
phase as a placeholder truth. -/
theorem K1primeK_ofTemplate (T : K1primeTemplate X) :
  K1primeK (KTransform.ofTemplate T) := by change True; exact trivial

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

/-! Linear displacement model on `ℝ` and the basic1D proof -/

section LinearOnReal

/- Linear interpolation on `ℝ`. -/
noncomputable def linearDisplacement : Displacement ℝ :=
{ interp := fun x y θ => (1 - θ) * x + θ * y,
  endpoint0 := by intro x y; simp,
  endpoint1 := by intro x y; simp }

/- In the basic 1D model, the kernel ignores `x`, hence displacement
affinity holds trivially for the linear displacement on `ℝ`. -/
theorem K4m_linear_basic1D :
  DisplacementAffinity (KTransform.basic1D) linearDisplacement := by
  intro x y θ hθ s
  -- Reduce RHS to `s` via `(1-θ)*s + θ*s = s`.
  have hsum : (1 - θ : ℝ) * s + θ * s = s := by
    have h := (add_mul (1 - θ) θ s).symm
    -- `((1-θ)+θ) = 1`
    simpa [sub_eq_add_neg, add_comm] using h
  -- Both sides simplify to `s`.
  simp [KTransform.basic1D, linearDisplacement, hsum]

end LinearOnReal

end Frourio
