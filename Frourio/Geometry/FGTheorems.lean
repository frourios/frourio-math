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
    (∀ k : ℤ, ∃ lam' : ℝ, lam' = effectiveLambda α κ S.Lambda k FG.lam)

/--
Isometry scale rule (theoremized skeleton).

Sketch: In the isometric case, take `α = 0`. Under generator homogeneity
with exponent `κ`, the effective parameter becomes
`lam' = effectiveLambda 0 κ S.Lambda k FG.lam = exp((κ k) log Λ) · lam`.
Here we only assert the existence of such `α, κ` and the algebraic form of
`lam'` via the `effectiveLambda` helper; quantitative EVI preservation is
handled in later phases.
-/
theorem evi_scale_rule_isometry (FG : FGData X) (S : ScaleAction X)
  (hIso : S.isometry) (hκ : ∃ κ : ℝ, S.generator_homogeneous κ) :
  evi_scale_rule FG S := by
  rcases hκ with ⟨κ, hκ'⟩
  refine ⟨0, κ, ?_, hκ', ?_⟩
  · exact Or.inl ⟨hIso, rfl⟩
  · intro k; refine ⟨effectiveLambda 0 κ S.Lambda k FG.lam, rfl⟩

/--
Similarity scale rule (theoremized skeleton).

Sketch: In the similarity case with exponent `α`, and generator
homogeneity exponent `κ`, the EVI parameter rescales according to
`lam' = effectiveLambda α κ S.Lambda k FG.lam`. This statement packages
the existence of the pair `(α, κ)` and the algebraic form via
`effectiveLambda`; the full EVI preservation is treated in subsequent
proof phases.
-/
theorem evi_scale_rule_similarity (FG : FGData X) (S : ScaleAction X)
  (α : ℝ) (hSim : S.similarity α) (hκ : ∃ κ : ℝ, S.generator_homogeneous κ) :
  evi_scale_rule FG S := by
  rcases hκ with ⟨κ, hκ'⟩
  refine ⟨α, κ, ?_, hκ', ?_⟩
  · exact Or.inr hSim
  · intro k; refine ⟨effectiveLambda α κ S.Lambda k FG.lam, rfl⟩

/- G2-T2: Doob×Scale commute (sufficient-condition shell)
We keep this abstract: for any weight `h` and scale step `k`, the Doob
transform should commute with the scale action under suitable (omitted)
assumptions. -/
def doob_scale_commute (_D : Diffusion X) (_S : ScaleAction X) : Prop :=
  ∀ (_h : X → ℝ) (_k : ℤ), True

end X

/- G2-T3: Mosco inheritance bridge (re-export to analysis layer) -/
def mosco_inheritance {ι : Type*} (S : MoscoSystem ι)
  (_H : MoscoAssumptions S) : Prop :=
  EVILimitHolds S

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

/-- Two-EVI synchronization: squared-distance bound with an error term.
Given the statement-level `eviSumWithError` and an inhomogeneous Grönwall
lemma in the `half` form, we obtain a linear-in-time upper bound for the
squared distance. -/
theorem evi_two_sync_sq_with_error
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop) (η : ℝ)
  (Hgr : gronwall_exponential_contraction_with_error_half P.lam η
    (fun t => d2 (u t) (v t))) :
  (eviSumWithError P u v hu hv geodesicBetween
    ({ η := η, bound := fun _t => True } : MixedErrorBound X u v)) →
  ∀ t : ℝ,
    d2 (u t) (v t) ≤
      Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) + (2 * η) * t :=
by
  intro Hsum
  -- Direct application of the inhomogeneous Grönwall placeholder.
  have h := Hgr (by
    intro t
    -- This is exactly the inequality packaged by `eviSumWithError`.
    simpa using (Hsum t))
  intro t; simpa using h t

/-- Error-free synchronization corollary: with zero error term and a
`half`-form Grönwall lemma, we recover squared-distance contraction. -/
theorem evi_two_sync_sq_zero_error
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop)
  (Hgr0 : gronwall_exponential_contraction_with_error_half P.lam (0 : ℝ)
    (fun t => d2 (u t) (v t))) :
  (eviSumWithError P u v hu hv geodesicBetween
    ({ η := 0, bound := fun _t => True } : MixedErrorBound X u v)) →
  ContractionPropertySq P u v :=
by
  intro Hsum
  -- Instantiate the general bound with η = 0, then simplify.
  have h := evi_two_sync_sq_with_error P u v hu hv geodesicBetween (0 : ℝ) Hgr0 Hsum
  intro t
  simpa [zero_mul, add_comm, add_left_comm, add_assoc] using h t

end X2

end Frourio
