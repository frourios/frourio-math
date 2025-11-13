import Mathlib.Analysis.Convolution

open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff

variable {n : ℕ}

theorem young_convolution_inequality
    {n : ℕ}
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) r volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
  sorry
