import Mathlib.Topology.MetricSpace.Basic
import Frourio.Geometry.FGCore
import Frourio.Analysis.EVI
import Frourio.Analysis.DoobTransform

/-!
# FG Theorems (Phase G2): Statement-only wrappers

This module provides statement-level definitions (Prop-valued) that tie
the FG core data to the existing analysis layer (EVI/Doob/Mosco), as
outlined in design phase G2. Proofs and quantitative details are left to
later phases; here we fix API shapes and dependencies.

References:
- papers/m点幾何学1-7.md: Scale rules, Doob×Scale compatibility
- design/10.md: Section 4 (G2-T1..T4)
-/

namespace Frourio

section X
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/- G2-T1: EVI scale rule (statement-level)
We package the isometry/similarity toggle and generator homogeneity and
expose the effective parameter via `effectiveLambda`. -/
def evi_scale_rule (FG : FGData X) (S : ScaleAction X) : Prop :=
  ∃ (α κ : ℝ),
    (((S.isometry) ∧ α = 0) ∨ S.similarity α) ∧
    S.generator_homogeneous κ ∧
    (∀ k : ℤ, let lam' := effectiveLambda α κ S.Lambda k FG.lam; True)

/- G2-T2: Doob×Scale commute (sufficient-condition shell)
We keep this abstract: for any weight `h` and scale step `k`, the Doob
transform should commute with the scale action under suitable (omitted)
assumptions. -/
def doob_scale_commute (D : Diffusion X) (S : ScaleAction X) : Prop :=
  ∀ (h : X → ℝ) (k : ℤ), True

end X

/- G2-T3: Mosco inheritance bridge (re-export to analysis layer) -/
def mosco_inheritance {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoAssumptions S) : Prop :=
  eviInheritance S H

section X2
variable {X : Type*} [PseudoMetricSpace X]

/- G2-T4: two-EVI synchronization with an abstract error bound.
We existentially package the required ingredients and call the analysis
layer's `eviSumWithError`. -/
def evi_sum_with_error (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∃ (hu : IsEVISolution P u) (hv : IsEVISolution P v)
    (geodesicBetween : Prop) (η : ℝ),
      eviSumWithError P u v hu hv geodesicBetween
        ({ η := η, bound := fun _t => True } : MixedErrorBound X u v)

end X2

end Frourio

