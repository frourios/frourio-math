import Frourio.Zeta.Interfaces
import Frourio.Analysis.QuadraticForm
import Frourio.Analysis.MellinPlancherel
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Frourio

open MeasureTheory

variable [ZetaLineAPI]

/-- Zeta kernel on the critical line: Kζ(τ) = ‖ζ(1/2 + iτ)‖². -/
noncomputable def Kzeta (τ : ℝ) : ℝ := ‖ZetaLineAPI.zeta_on_line τ‖ ^ (2 : ℕ)

lemma measurable_Kzeta : Measurable Kzeta := by
  have hz : Measurable fun τ => ‖ZetaLineAPI.zeta_on_line τ‖ :=
    ZetaLineAPI.measurable.norm
  simpa [Kzeta] using hz.pow_const (2 : ℕ)

lemma Kzeta_nonneg (τ : ℝ) : 0 ≤ Kzeta τ := by
  have := sq_nonneg (‖ZetaLineAPI.zeta_on_line τ‖)
  simpa [Kzeta, pow_two] using this

/-- Continuous quadratic form with the zeta kernel on L²(ℝ). -/
noncomputable def Qζℝ (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ :=
  Qℝ (fun τ => Kzeta τ) g

/-- Pullback to Hσ: zeta-kernel quadratic form on Hσ via Uσ. -/
noncomputable def Qζσ (σ : ℝ) (f : Hσ σ) : ℝ :=
  Qσ (fun τ => Kzeta τ) f

/-- Positivity: Qζℝ ≥ 0. -/
theorem Qζ_pos (g : Lp ℂ 2 (volume : Measure ℝ)) : 0 ≤ Qζℝ g := by
  have hK : ∀ᵐ τ ∂volume, 0 ≤ Kzeta τ :=
    by
      -- strengthen to a pointwise statement then lift to ae
      exact (ae_of_all _ (fun τ => Kzeta_nonneg τ))
  simpa [Qζℝ] using Q_pos (K := fun τ => Kzeta τ) hK g

/-- Positivity on Hσ: Qζσ ≥ 0. -/
theorem Qζσ_pos (σ : ℝ) (f : Hσ σ) : 0 ≤ Qζσ σ f := by
  have hK : ∀ᵐ τ ∂volume, 0 ≤ Kzeta τ :=
    by exact (ae_of_all _ (fun τ => Kzeta_nonneg τ))
  simpa [Qζσ] using Qσ_pos (K := fun τ => Kzeta τ) hK f

/-- Kernel predicate for Qζ on L²: vanishing a.e. on the support of Kζ (design-level). -/
def Qζ_kernelPred (g : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  let Kc : ℝ → ℂ := fun τ => (Kzeta τ : ℝ)
  (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K Kc)] 0

/-- Trivial direction used in this phase: if g = 0 a.e. (globally), then Qζℝ g = 0. -/
theorem Qζ_eq_zero_of_ae_zero
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ((g : ℝ → ℂ) =ᵐ[volume] 0) → Qζℝ g = 0 := by
  intro hzero
  -- Specialize the generic lemma for Qℝ
  have :=
    (by
      -- local lemma scoped to use in `have` to avoid name clashes
      exact (by
        -- from QuadraticForm: if integrand is a.e. 0, integral is 0
        have hcongr : (fun τ => (Kzeta τ) * ‖(g : ℝ → ℂ) τ‖^2)
            =ᵐ[volume] (fun _ => 0) := by
          refine hzero.mono ?_
          intro τ hτ; simp [hτ]
        have : ∫ τ, Kzeta τ * ‖(g : ℝ → ℂ) τ‖^2 ∂volume = 0 := by
          simpa using integral_congr_ae hcongr
        simpa [Qζℝ, Qℝ] using this))
  simpa using this

end Frourio
