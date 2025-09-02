import Frourio.Algebra.Operators
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Frourio

open scoped BigOperators

/-- Mellin記号の定義（形式的） -/
noncomputable def mellinSymbol {m : ℕ} (op : FrourioOperator m) (s : ℂ) : ℂ :=
  ∑ i : Fin m, op.α i * ((op.χ i).toInt : ℂ) * ((op.Λ i : ℂ) ^ (-s))

/-- モーメント条件：設計パラメータが満たすべき条件（複素に埋め込んで定義） -/
def satisfiesMomentCondition {m : ℕ} (op : FrourioOperator m) (r : ℕ) : Prop :=
  (∀ k : ℕ, k < r → k ≠ 1 →
    ∑ i : Fin m, op.α i * ((op.χ i).toInt : ℂ) * ((Real.log (op.Λ i) : ℂ) ^ k) = 0) ∧
  (∑ i : Fin m, op.α i * ((op.χ i).toInt : ℂ) * (Real.log (op.Λ i) : ℂ) = (-1 : ℂ))

/-- 基本的な補題：m=0の場合は退化 -/
lemma frourio_zero_not_moment0 (op : FrourioOperator 0) :
  ¬ satisfiesMomentCondition op 0 := by
  intro h
  -- 第二条件は空和が 0 なので 0 = -1 となり矛盾
  have hsum0 :
      (∑ i : Fin 0, op.α i * ((op.χ i).toInt : ℂ) * (Real.log (op.Λ i) : ℂ)) = (0 : ℂ) := by
    simp
  -- rewrite the empty sum to 0 on the left-hand side
  have h0eq : (0 : ℂ) = (-1 : ℂ) := by
    rw [← hsum0]
    exact h.right
  -- 0 = -1 から矛盾を導く
  have : (0 : ℂ) ≠ (-1 : ℂ) := by norm_num
  exact this h0eq

/-- 基本的な補題：m=1は差分として不適切（定数項が消えない） -/
lemma frourio_one_insufficient (op : FrourioOperator 1) :
  ¬ satisfiesMomentCondition op 2 := by
  intro h
  -- k = 0 のモーメント条件より ∑ α_i χ_i = 0、m=1 なので α 0 = 0
  have h0 := h.left 0 (by decide) (by decide)
  have h0' : op.α 0 * ((op.χ 0).toInt : ℂ) = 0 := by
    -- Simplify the sum over `Fin 1` and the ^0 power
    convert h0 using 1
    simp [pow_zero, mul_one]
  have hχne : ((op.χ 0).toInt : ℂ) ≠ 0 := by
    cases op.χ 0 <;>
      -- ±1 は 0 でない
      simp [Sign.toInt]
  have hα0 : op.α 0 = 0 := by
    have := mul_eq_zero.mp h0'
    rcases this with hα | hχ0
    · exact hα
    · exact (hχne hχ0).elim
  -- 第二条件と矛盾（左辺が 0）
  -- Simplify the sum over `Fin 1`, then substitute α 0 = 0
  have h1 : op.α 0 * ((op.χ 0).toInt : ℂ) * (Real.log (op.Λ 0) : ℂ) = (-1 : ℂ) := by
    convert h.right using 1
    simp
  have hzero : (0 : ℂ) = (-1 : ℂ) := by
    rw [← h1]
    simp [hα0, zero_mul]
  -- 0 = -1 から矛盾を導く
  have : (0 : ℂ) ≠ (-1 : ℂ) := by norm_num
  exact this hzero

end Frourio
