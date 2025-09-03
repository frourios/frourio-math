import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Frourio.Analysis.EVI

/-!
# FG Core (Phase G1): Frourio Geometry core API

This module introduces the minimal core types for Frourio Geometry (FG)
as per design phase G1, generalizing to the m-point calibration setting
while staying proof-light and non-destructive to existing analysis code.

References (design → papers):
- papers/m点幾何学1-7.md: FG data (X,d,μ; 𝓔, Λ), scale action S_{Λ^k}
- papers/代数学.md: Analytical backbone (EVI, Doob, Mosco, etc.)

Provided here:
- `FGData`: geometric/analytic data on a metric-measure space.
- `ScaleAction`: abstract scale action with isometry/similarity toggles
  and quasi-invariance/homogeneity predicates.
- `toEVI`: bridge from `FGData` to the existing `EVIProblem`.
- `effectiveLambda`: helper for similarity scaling of the EVI parameter.
-/

namespace Frourio

/-!
FG data on a metric-measure space with an energy and auxiliary
operators. This is intentionally lightweight: Γ, Γ₂ are abstract
endomorphisms to keep the API flexible at this phase.
-/
structure FGData (X : Type*) [PseudoMetricSpace X] [MeasurableSpace X] where
  (μ : MeasureTheory.Measure X)
  (E : X → ℝ)
  (Γ : (X → ℝ) → (X → ℝ))
  (Γ₂ : (X → ℝ) → (X → ℝ))
  (lam : ℝ)

/- Bridge from FG to the analysis-side EVI problem datum. -/
def FGData.toEVI {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (FG : FGData X) : EVIProblem X :=
  { E := FG.E, lam := FG.lam }

/-!
Scale action skeleton. The fields are `Prop`-valued to capture
requirements without committing to concrete constructions yet.

• `Λ`: scale factor (typically Λ > 1; the positivity/large-ness is
  asserted via separate predicates, not as fields here).
• `act`: integer-parameterized action k ↦ S_{Λ^k} on X.
• `isometry`: declares the action is isometric (α = 0 scenario).
• `similarity`: declares similarity with an exponent α.
• `measure_quasiInvariant`: pushforward relation (S_k)_# μ = θ_k μ.
• `generator_homogeneous`: generator scaling exponent κ.
-/
structure ScaleAction (X : Type*) where
  (Lambda : ℝ)
  (act : ℤ → X → X)
  (isometry : Prop)
  (similarity : ℝ → Prop)
  (measure_quasiInvariant : (k : ℤ) → Prop)
  (generator_homogeneous : ℝ → Prop)

/-!
Effective EVI parameter under similarity scaling. For a similarity with
exponent α and generator homogeneity exponent κ, the effective EVI
parameter at scale k is Λ^{(κ - 2α) k} · λ. We model the real power via
`Real.rpow` and coerce `k : ℤ` into ℝ.
-/
noncomputable def effectiveLambda (α κ Λ : ℝ) (k : ℤ) (lam : ℝ) : ℝ :=
  Real.exp (((κ - 2 * α) * (k : ℝ)) * Real.log Λ) * lam

end Frourio
