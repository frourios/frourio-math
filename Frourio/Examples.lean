import Frourio.Algebra.Properties
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
