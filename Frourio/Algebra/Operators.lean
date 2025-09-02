import Frourio.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Frourio

open scoped BigOperators

/-- スケール変換作用素 U_Λ: f(x) ↦ f(Λx) -/
structure ScaleOperator where
  scale : ℝ
  scale_pos : 0 < scale

/-- 逆数乗算作用素 M_{1/x}: f(x) ↦ f(x)/x （型占位） -/
structure InverseMultOperator where

/-- m点Frourio作用素のパラメータ -/
structure FrourioParams (m : ℕ) where
  α : Fin m → ℂ           -- 複素係数
  χ : Fin m → Sign        -- 符号（+1 or -1）
  Λ : Fin m → ℝ           -- スケールパラメータ
  Λ_pos : ∀ i, 0 < Λ i    -- 正値条件

/-- m点Frourio作用素の定義
    Δ^⟨m⟩ = M_{1/x} (Σ_{i=1}^m α_i χ_i U_{Λ_i})
    ここではパラメータを束ねた構造として与える。 -/
structure FrourioOperator (m : ℕ) extends FrourioParams m where

/-- 2点Frourio作用素（基本ケース） -/
noncomputable def BasicFrourioOperator (a : ℝ) (ha : 0 < a) : FrourioOperator 2 :=
  { α := fun i => if i.1 = 0 then (a⁻¹ : ℂ) else (a : ℂ)
  , χ := fun i => if i.1 = 0 then Sign.pos else Sign.neg
  , Λ := fun i => if i.1 = 0 then a else a⁻¹
  , Λ_pos := by
      intro i
      by_cases h : i.1 = 0
      · simpa [h]
        using ha
      · have : 0 < a⁻¹ := inv_pos.mpr ha
        simpa [h]
        using this
  }

/-- 黄金Frourio作用素（φに特化） -/
noncomputable def GoldenFrourioOperator : FrourioOperator 2 :=
  BasicFrourioOperator φ (by
    -- φ = (1 + √5) / 2 > 0
    have h₁ : 0 < 1 + Real.sqrt 5 := by
      have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    have h₂ : 0 < (2 : ℝ) := by norm_num
    have : 0 < (1 + Real.sqrt 5) / 2 := div_pos h₁ h₂
    simpa [φ] using this)

end Frourio
