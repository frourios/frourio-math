import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Frourio

open MeasureTheory

/-!
Minimal API for ζ on the critical line (design-level abstraction).

This interface decouples downstream development from the concrete implementation
of the Riemann zeta function. It only requires measurability and local
boundedness along the critical line. Concrete instances can be provided from
Mathlib or external libraries; we include a safe placeholder instance that maps
to `0`, keeping the API usable for testing other components.
-/

class ZetaLineAPI where
  zeta_on_line : ℝ → ℂ
  measurable : Measurable zeta_on_line
  loc_bounded : ∀ R : ℝ, ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ R → ‖zeta_on_line τ‖ ≤ C

/-!
Default placeholder instance: ζ(1/2 + iτ) ≡ 0. This satisfies measurability and
local boundedness trivially, and can be replaced by a true instance when
available without breaking downstream code.
-/

noncomputable instance defaultZetaLineAPI : ZetaLineAPI where
  zeta_on_line := fun _ => 0
  measurable := by
    -- constant function is measurable
    exact measurable_const
  loc_bounded := by
    intro R
    refine ⟨0, ?_⟩
    intro τ hτ
    simp

/-- Phase 5.1: injectable data for supplying a concrete ζ on the critical line.
This allows users to provide their own implementation (e.g. from Mathlib) and
produce a `ZetaLineAPI` value without committing it as a global instance. -/
structure ZetaData where
  zeta_on_line : ℝ → ℂ
  measurable : Measurable zeta_on_line
  loc_bounded : ∀ R : ℝ, ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ R → ‖zeta_on_line τ‖ ≤ C

/-- Build a `ZetaLineAPI` record from provided measurable/locally-bounded data. -/
noncomputable def ZetaLineAPI.ofData (d : ZetaData) : ZetaLineAPI where
  zeta_on_line := d.zeta_on_line
  measurable := d.measurable
  loc_bounded := d.loc_bounded

/-- Convenience: construct `ZetaData` from a function and proofs. -/
noncomputable def ZetaData.mk' (f : ℝ → ℂ)
    (hf_meas : Measurable f)
    (hf_loc : ∀ R : ℝ, ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ R → ‖f τ‖ ≤ C) : ZetaData :=
  { zeta_on_line := f, measurable := hf_meas, loc_bounded := hf_loc }

/-- Example: constant function as a trivial `ZetaData` provider. -/
noncomputable def ZetaData.const (c : ℂ) : ZetaData :=
  { zeta_on_line := fun _ => c
  , measurable := measurable_const
  , loc_bounded := by
      intro R; refine ⟨‖c‖, ?_⟩; intro τ _; simp }

end Frourio
