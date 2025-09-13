import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
-- Note: BigOperators is not needed here

namespace Frourio

/-- 黄金比の定義 -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- The golden ratio is greater than 1 -/
theorem φ_gt_one : 1 < φ := by
  unfold φ
  -- We need to show (1 + √5) / 2 > 1
  -- This is equivalent to 1 + √5 > 2, or √5 > 1
  have h_sqrt5_gt_1 : 1 < Real.sqrt 5 := by
    rw [Real.lt_sqrt]
    · norm_num  -- 1^2 < 5
    · norm_num  -- 0 ≤ 1
  linarith

/-- 金属比の定義（パラメータpに対して） -/
noncomputable def metallic (p : ℝ) : ℝ := (p + Real.sqrt (p^2 + 4)) / 2

/-- 符号型（+1 または -1） -/
inductive Sign
  | pos : Sign
  | neg : Sign

/-- `Sign` を整数に写像する（+1 または -1）。 -/
def Sign.toInt : Sign → ℤ
  | Sign.pos => 1
  | Sign.neg => -1

end Frourio
