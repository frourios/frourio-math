import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Basic

namespace Frourio

/-- 構造列 S_n = Λ^n - Λ^{-n} -/
noncomputable def S (Λ : ℝ) (n : ℤ) : ℝ := Λ ^ n - Λ ^ (-n)

/-- S_n の基本的な性質：S_{-n} = -S_n -/
theorem S_neg (Λ : ℝ) (n : ℤ) : S Λ (-n) = -S Λ n := by
  simp [S]

/-- S_0 = 0 -/
@[simp] theorem S_zero (Λ : ℝ) : S Λ 0 = 0 := by
  simp [S]

/-- S_1 の値 -/
theorem S_one (Λ : ℝ) : S Λ 1 = Λ - 1 / Λ := by
  unfold S
  rw [zpow_one, zpow_neg_one Λ]
  simp [one_div]

/-- S_n の加法公式: S_{m+n} = S_m Λ^n + S_n Λ^{-m} -/
theorem S_add (Λ : ℝ) (hΛ : 0 < Λ) (m n : ℤ) :
    S Λ (m + n) = S Λ m * Λ ^ n + S Λ n * Λ ^ (-m) := by
  have hne : Λ ≠ 0 := ne_of_gt hΛ
  unfold S
  have hneg_add : - (m + n) = -m + -n := by
    simpa [sub_eq_add_neg] using (neg_add m n)
  simp [hneg_add]
  rw [zpow_add₀ hne, zpow_add₀ hne]
  simp [zpow_neg, mul_comm]
  ring

/-- Helper: `2 * sinh` is odd. -/
lemma two_sinh_neg (t : ℝ) : 2 * Real.sinh (-t) = -(2 * Real.sinh t) := by
  simp [Real.sinh_neg]

/-!
D1: Hyperbolic representation via exponential identities.
-/

/-- Helper: exp of a natural multiple of log equals pow. -/
theorem exp_nat_mul_log_eq_pow (Λ : ℝ) (hΛpos : 0 < Λ) (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log Λ) = Λ ^ n := by
  induction' n with n ih
  · simp
  · have : ((n.succ : ℝ) * Real.log Λ) = (n : ℝ) * Real.log Λ + Real.log Λ := by
      simp [Nat.cast_succ, add_mul]
    simp [Nat.cast_succ, add_mul, ih, Real.exp_add, Real.exp_log hΛpos, pow_succ]

/-- Exponential-difference form for natural indices. -/
theorem S_as_exp_sub_exp_neg_ofNat (Λ : ℝ) (hΛpos : 0 < Λ) (n : ℕ) :
    S Λ (n : ℤ) = Real.exp ((n : ℝ) * Real.log Λ)
                    - Real.exp (-( (n : ℝ) * Real.log Λ)) := by
  have h1 : Real.exp ((n : ℝ) * Real.log Λ) = Λ ^ n := by
    simpa using exp_nat_mul_log_eq_pow Λ hΛpos n
  have h2 : Real.exp (-( (n : ℝ) * Real.log Λ)) = (Λ ^ n)⁻¹ := by
    simp [h1, Real.exp_neg]
  simp [S, h1, h2]

/-- Hyperbolic form via `sinh` for natural indices. -/
theorem S_as_sinh_ofNat (Λ : ℝ) (hΛpos : 0 < Λ) (n : ℕ) :
    S Λ (n : ℤ) = 2 * Real.sinh ((n : ℝ) * Real.log Λ) := by
  have h := S_as_exp_sub_exp_neg_ofNat Λ hΛpos n
  set t := (n : ℝ) * Real.log Λ with ht
  have hsinh : Real.exp t - Real.exp (-t) = 2 * Real.sinh t := by
    have hdef := (Real.sinh_eq t)
    have hmul := congrArg (fun y => (2 : ℝ) * y) hdef
    have hmul_simp : 2 * Real.sinh t = Real.exp t - Real.exp (-t) := by
      simpa [two_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, sub_eq_add_neg]
        using hmul
    exact hmul_simp.symm
  have h1 : S Λ (n : ℤ) = Real.exp t - Real.exp (-t) := by simpa [ht] using h
  exact h1.trans hsinh

/-- Hyperbolic form via `sinh` for integer indices. -/
theorem S_as_sinh_int (Λ : ℝ) (hΛpos : 0 < Λ) (m : ℤ) :
    S Λ m = 2 * Real.sinh ((m : ℝ) * Real.log Λ) := by
  cases m with
  | ofNat n => simpa using S_as_sinh_ofNat Λ hΛpos n
  | negSucc n =>
      have hS : S Λ (Int.negSucc n) = - S Λ (n.succ : ℤ) := by
        have hns : (Int.negSucc n : ℤ) = - (n.succ : ℤ) := rfl
        simpa [hns] using S_neg Λ (n.succ : ℤ)
      have hNat := S_as_sinh_ofNat Λ hΛpos (n.succ)
      have hcastR : ((Int.negSucc n : ℤ) : ℝ) = -((n.succ : ℝ)) := by simp
      have heq₁ : -(2 * Real.sinh (((n.succ : ℝ)) * Real.log Λ))
                  = 2 * Real.sinh ( - (((n.succ : ℝ)) * Real.log Λ)) := by simp
      have heq₂ : 2 * Real.sinh ( - (((n.succ : ℝ)) * Real.log Λ))
                  = 2 * Real.sinh (((-1 : ℝ) + - (n : ℝ)) * Real.log Λ) := by
        have : -(((n : ℝ) + 1) * Real.log Λ)
                = (((-1 : ℝ) + - (n : ℝ)) * Real.log Λ) := by ring
        simpa [Nat.cast_succ, add_comm] using congrArg (fun t => 2 * Real.sinh t) this
      calc
        S Λ (Int.negSucc n) = - S Λ (n.succ : ℤ) := hS
        _ = -(2 * Real.sinh ((n.succ : ℝ) * Real.log Λ)) := by simpa using congrArg Neg.neg hNat
        _ = 2 * Real.sinh ( - (((n.succ : ℝ)) * Real.log Λ)) := heq₁
        _ = 2 * Real.sinh (((-1 : ℝ) + - (n : ℝ)) * Real.log Λ) := heq₂
        _ = 2 * Real.sinh (((Int.negSucc n : ℤ) : ℝ) * Real.log Λ) := by
              simp [hcastR, Nat.cast_succ, add_comm]

/-! Basic inequalities derived from the exponential form (Λ > 1). -/

lemma S_nonneg_of_nat (Λ : ℝ) (hΛgt1 : 1 < Λ) (n : ℕ) :
    0 ≤ S Λ (n : ℤ) := by
  have hΛpos : 0 < Λ := lt_trans (by norm_num) hΛgt1
  have hlogpos : 0 < Real.log Λ := by
    have := Real.log_lt_log (by norm_num) hΛgt1; simpa using this
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have ht : 0 ≤ (n : ℝ) * Real.log Λ := mul_nonneg hn (le_of_lt hlogpos)
  have : 0 ≤ Real.exp ((n : ℝ) * Real.log Λ) - Real.exp (-( (n : ℝ) * Real.log Λ)) := by
    have hle : Real.exp (-( (n : ℝ) * Real.log Λ)) ≤ Real.exp ((n : ℝ) * Real.log Λ) := by
      have : -((n : ℝ) * Real.log Λ) ≤ (n : ℝ) * Real.log Λ :=
        le_trans (neg_nonpos.mpr ht) ht
      exact Real.exp_le_exp.mpr this
    exact sub_nonneg.mpr hle
  simpa [S_as_exp_sub_exp_neg_ofNat Λ hΛpos n]

lemma S_pos_of_nat_pos (Λ : ℝ) (hΛgt1 : 1 < Λ) {n : ℕ} (hn : 0 < n) :
    0 < S Λ (n : ℤ) := by
  have hΛpos : 0 < Λ := lt_trans (by norm_num) hΛgt1
  have hlog : 0 < Real.log Λ := by
    have := Real.log_lt_log (by norm_num) hΛgt1; simpa using this
  have ht : 0 < (n : ℝ) * Real.log Λ := by exact mul_pos (by exact_mod_cast hn) hlog
  have : 0 < Real.exp ((n : ℝ) * Real.log Λ) - Real.exp (-( (n : ℝ) * Real.log Λ)) := by
    have hle : Real.exp (-( (n : ℝ) * Real.log Λ)) ≤ 1 := by
      have : -((n : ℝ) * Real.log Λ) ≤ 0 := (neg_nonpos.mpr (le_of_lt ht))
      simpa using Real.exp_le_one_iff.mpr this
    have hlt' : 1 < Real.exp ((n : ℝ) * Real.log Λ) := by
      simpa using Real.one_lt_exp_iff.mpr ht
    exact sub_pos.mpr (lt_of_le_of_lt hle hlt')
  simpa [S_as_exp_sub_exp_neg_ofNat Λ hΛpos n]

lemma S_ne_zero_of_pos_ne_one (Λ : ℝ) (hΛpos : 0 < Λ) (hΛne1 : Λ ≠ 1)
    {n : ℕ} (hn : 0 < n) : S Λ (n : ℤ) ≠ 0 := by
  have hform := S_as_exp_sub_exp_neg_ofNat Λ hΛpos n
  have hlog_ne : Real.log Λ ≠ 0 := by
    intro h0
    have : Real.exp (Real.log Λ) = Real.exp 0 := by simp [h0]
    have : Λ = 1 := by simpa [Real.exp_log hΛpos, Real.exp_zero] using this
    exact hΛne1 this
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have harg_ne : (n : ℝ) * Real.log Λ ≠ 0 := mul_ne_zero hn' hlog_ne
  have hne : Real.exp ((n : ℝ) * Real.log Λ) - Real.exp (-( (n : ℝ) * Real.log Λ)) ≠ 0 := by
    rcases lt_or_gt_of_ne harg_ne with hlt | hgt
    · have hlt' : Real.exp ((n : ℝ) * Real.log Λ) < Real.exp (-( (n : ℝ) * Real.log Λ)) := by
        have : ((n : ℝ) * Real.log Λ) < -((n : ℝ) * Real.log Λ) := by
          have : ((n : ℝ) * Real.log Λ) < 0 := hlt
          simpa [neg_mul, neg_neg] using (lt_neg_self_iff.mpr this)
        exact Real.exp_lt_exp.mpr this
      exact ne_of_lt (sub_neg.mpr hlt')
    · have hgt' : Real.exp (-( (n : ℝ) * Real.log Λ)) < Real.exp ((n : ℝ) * Real.log Λ) := by
        have : -((n : ℝ) * Real.log Λ) < ((n : ℝ) * Real.log Λ) := by
          have : 0 < ((n : ℝ) * Real.log Λ) := hgt
          simpa using (neg_lt_self_iff.mpr this)
        exact Real.exp_lt_exp.mpr this
      exact ne_of_gt (sub_pos.mpr hgt')
  simpa [hform]

end Frourio
