import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

namespace Frourio

/-!
Appendix E: Mellin–Sobolev algebra skeleton (H^s_×)

We provide lightweight signatures only, avoiding heavy analysis. The
carrier is modeled as `ℝ → ℂ`, with a placeholder norm. Algebraicity
and scale-action are recorded as `Prop` statements for later proof.
-/

-- Keep the carrier minimal for this phase
abbrev Htimes (_s : ℝ) := ℝ → ℂ

-- Placeholder Mellin–Sobolev norm (to be refined later)
noncomputable def HtimesNorm (_s : ℝ) (_f : Htimes _s) : ℝ := 0

/-- Algebra property: existence of a product bound constant C(s)
so that the pointwise product stays in H^s_× with the usual estimate. -/
def algebraProp_Htimes (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f g : Htimes s),
      HtimesNorm s (fun x => f x * g x) ≤ C * HtimesNorm s f * HtimesNorm s g

/-- Scale action statement: for α > 0, the scaling `f ↦ (x ↦ f (α x))`
acts boundedly on H^s_× with some constant depending on (α,s). -/
def scaleProp_Htimes (s : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : Htimes s, HtimesNorm s (fun x => f (α * x)) ≤ C * HtimesNorm s f

end Frourio
