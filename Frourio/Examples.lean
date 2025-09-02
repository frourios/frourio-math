import Frourio.Algebra.Properties
import Frourio.Algebra.CrossedProduct
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Frourio

/-- 黄金比の基本性質 -/
lemma golden_ratio_property : φ^2 = φ + 1 := by
  -- φ = (1 + √5)/2 を用いた計算
  have hmul := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) 5)
  -- rewrite to exponent form for easier substitution
  have hsq : (Real.sqrt 5)^2 = (5 : ℝ) := by
    calc
      (Real.sqrt 5)^2 = (Real.sqrt 5) * (Real.sqrt 5) := by simp [pow_two]
      _ = (5 : ℝ) := hmul
  have h1 : φ^2 = ((1 + Real.sqrt 5)^2) / 4 := by
    have htmp : ((1 + Real.sqrt 5) / 2)^2 = ((1 + Real.sqrt 5)^2) / 4 := by
      ring
    simpa [φ] using htmp
  have h2 : φ + 1 = (3 + Real.sqrt 5) / 2 := by
    have htmp : (1 + Real.sqrt 5) / 2 + 1 = (3 + Real.sqrt 5) / 2 := by
      ring
    simpa [φ] using htmp
  calc
    φ^2
        = ((1 + Real.sqrt 5)^2) / 4 := h1
    _   = (1 + 2 * Real.sqrt 5 + (Real.sqrt 5)^2) / 4 := by ring
    _   = (1 + 2 * Real.sqrt 5 + 5) / 4 := by simp [hsq]
    _   = (6 + 2 * Real.sqrt 5) / 4 := by ring
    _   = (3 + Real.sqrt 5) / 2 := by ring
    _   = φ + 1 := by simp [h2]

/-- 黄金Frourio作用素のMellin記号 -/
noncomputable def goldenMellinSymbol (s : ℂ) : ℂ :=
  mellinSymbol GoldenFrourioOperator s

/-- 3点Frourio作用素の例 -/
noncomputable def ThreePointExample (δ : ℝ) (hδ : 0 < δ) : FrourioOperator 3 :=
  { α := fun _ => (1 : ℂ)
  , χ := fun _ => Sign.pos
  , Λ := fun i => δ ^ (i.1 + 1)
  , Λ_pos := by
      intro i
      -- pow_pos は自然数乗に対して正の値を保つ
      exact pow_pos hδ (i.1 + 1)
  }

end Frourio

namespace Frourio

/-- 交叉積の自明作用における簡単な計算例（m=2, Λ=φ）。 -/
example :
    CrossedProduct.mul (trivialZmAction ℝ 2)
      { base := φ, scales := fun _ => (0 : ℤ) }
      { base := 1, scales := fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0 }
      =
      { base := φ, scales := fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0 } := by
  -- 自明作用では base は通常の積、scales は加法
  have hzero : (fun _ : Fin 2 => (0 : ℤ)) = (0 : Fin 2 → ℤ) := rfl
  simp [CrossedProduct.mul, trivialZmAction, φ, hzero]

end Frourio
