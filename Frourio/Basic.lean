import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
-- Note: BigOperators is not needed here

namespace Frourio

/-- 黄金比の定義 -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

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
