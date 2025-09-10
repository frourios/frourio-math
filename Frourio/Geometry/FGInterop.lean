import Mathlib.Topology.MetricSpace.Basic
import Frourio.Geometry.FGCore
import Frourio.Analysis.EVI.EVI

/-!
# FG Interop: Bridges to analysis APIs

Lightweight helpers connecting FG data to the analysis layer without
renaming existing APIs. These are thin wrappers around `EVIProblem` and
its predicates, aligning with the design goal of non-destructive
integration.
-/

namespace Frourio

section X
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- Induce an `EVIProblem` from FG data. -/
def evi_from_fg (FG : FGData X) : EVIProblem X := FG.toEVI

/-- Predicate alias: `u` is an EVI solution for the problem induced by `FG`. -/
def fg_IsEVISolution (FG : FGData X) (u : ℝ → X) : Prop :=
  IsEVISolution (evi_from_fg FG) u

/-- Contraction statement alias for two curves under the FG-induced EVI problem. -/
def fg_evi_contraction (FG : FGData X) (u v : ℝ → X)
  (hu : IsEVISolution (evi_from_fg FG) u)
  (hv : IsEVISolution (evi_from_fg FG) v) : Prop :=
  evi_contraction (evi_from_fg FG) u v hu hv

end X

section Xnonneg
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- Nonnegative-time contraction alias via the FG-induced problem. -/
def fg_evi_contraction_nonneg (FG : FGData X) (u v : Rge0 → X)
  (hu : IsEVISolutionNonneg (evi_from_fg FG) u)
  (hv : IsEVISolutionNonneg (evi_from_fg FG) v) : Prop :=
  evi_contraction_nonneg (evi_from_fg FG) u v hu hv

end Xnonneg

end Frourio
