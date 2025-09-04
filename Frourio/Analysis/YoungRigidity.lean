import Frourio.Analysis.YoungConvolution

namespace Frourio

/-!
Young rigidity (statement wrappers)

This module packages the statement-level Young L2 inequalities and their
rigidity forms from `YoungConvolution.lean` into small assumption packs and
wrapper theorems. Proofs remain deferred; we only move and name results so
they can be referenced from FG8 design points.
-/

section R
open scoped Topology

/-- Assumption pack for Young’s inequality and rigidity on ℝ. -/
structure YoungRigidityPackR (ν : Frourio.MeasureR) : Prop where
  (assm : YoungAssumptionsR ν)
  (ineq_all : young_L2_R_all ν)
  (rigidity : young_rigidity_R ν)

/-- Wrapper: from the pack, obtain the L2 inequality for all test functions. -/
theorem young_L2_R_from_pack (ν : Frourio.MeasureR) (P : YoungRigidityPackR ν) :
  ∀ f : ℝ → ℂ, L2NormR (convR_measure f ν) ≤ L2NormR f * TVNorm ν :=
by
  intro f; exact (P.ineq_all P.assm f)

/-- Wrapper: expose the rigidity equivalence from the pack. -/
theorem young_rigidity_R_from_pack (ν : Frourio.MeasureR) (P : YoungRigidityPackR ν) :
  young_rigidity_R ν := P.rigidity

/-- One-way equality (existence) from Dirac-like assumption, via the skeleton
convolution and norm models. -/
theorem young_rigidity_R_dirac_exists_from_pack (ν : Frourio.MeasureR)
  (_P : YoungRigidityPackR ν) :
  IsDiracMeasureR ν →
    ∃ f, f ≠ (fun _ => 0) ∧
      L2NormR (convR_measure f ν) = L2NormR f * TVNorm ν :=
by
  intro hD; exact young_rigidity_R_exists_from_dirac ν hD

end R

section Z

/-- Assumption pack for the discrete (ℤ) Young inequality. -/
structure YoungRigidityPackZ (μ : ℤ → ℂ) : Prop where
  (ineq : ∀ a : ℤ → ℂ, young_L2_Z a μ)
  (rigidity : young_rigidity_Z μ)

theorem young_L2_Z_from_pack (μ : ℤ → ℂ) (P : YoungRigidityPackZ μ) :
  ∀ a : ℤ → ℂ, young_L2_Z a μ := P.ineq

theorem young_rigidity_Z_from_pack (μ : ℤ → ℂ) (P : YoungRigidityPackZ μ) :
  young_rigidity_Z μ := P.rigidity

end Z

end Frourio
