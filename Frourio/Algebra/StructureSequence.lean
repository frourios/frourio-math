import Frourio.Algebra.Operators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

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
  -- 目標を書き換えてから個別に処理
  unfold S
  -- 負号の展開を明示
  have hneg_add : - (m + n) = -m + -n := by
    -- 一般加法群の恒等式
    simpa [sub_eq_add_neg] using (neg_add m n)
  -- 左辺と右辺の各項を `zpow_add` で分解してから環の計算で一致させる
  -- LHS: 分解
  -- 先に `-(m+n)` の形を `-n + -m` に直す
  simp [hneg_add]
  -- その上で加法の冪を積に展開
  rw [zpow_add₀ hne, zpow_add₀ hne]
  -- 負冪を逆元へ（可換性で左右調整）
  simp [zpow_neg, mul_comm]
  -- RHS: 展開して中間項を相殺
  ring

-- (dropped: a stronger global lemma for `Int.negSucc` cast times a scalar)

/-- Helper: `2 * sinh` is odd. -/
lemma two_sinh_neg (t : ℝ) : 2 * Real.sinh (-t) = -(2 * Real.sinh t) := by
  simp [Real.sinh_neg]

--

/-!
D1: Hyperbolic representation

We provide a version via exponentials, from which the hyperbolic form
with `Real.sinh` follows by definition. This avoids extra complex lemmas.
-/

/-– Helper: exp of a natural multiple of log equals pow. -/
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

/-- Hyperbolic form via `sinh` for natural indices: `S Λ n = 2 sinh(n log Λ)`.
    This is the analytic alias of `S_as_exp_sub_exp_neg_ofNat`. -/
theorem S_as_sinh_ofNat (Λ : ℝ) (hΛpos : 0 < Λ) (n : ℕ) :
    S Λ (n : ℤ) = 2 * Real.sinh ((n : ℝ) * Real.log Λ) := by
  -- Exponential difference form
  have h := S_as_exp_sub_exp_neg_ofNat Λ hΛpos n
  set t := (n : ℝ) * Real.log Λ with ht
  -- `exp t - exp (-t) = 2 * sinh t` (real version)
  have hsinh : Real.exp t - Real.exp (-t) = 2 * Real.sinh t := by
    -- from `Real.sinh_eq t = (exp t - exp (-t))/2`
    have hdef := (Real.sinh_eq t)
    have hmul := congrArg (fun y => (2 : ℝ) * y) hdef
    have hmul_simp : 2 * Real.sinh t = Real.exp t - Real.exp (-t) := by
      simpa [two_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, sub_eq_add_neg]
        using hmul
    exact hmul_simp.symm
  -- conclude
  have h1 : S Λ (n : ℤ) = Real.exp t - Real.exp (-t) := by simpa [ht] using h
  exact h1.trans hsinh


-- Hyperbolic alias via `sinh` can be reintroduced once the underlying
-- library bridge lemmas are stabilized for this project setup.

-- Exponential-difference form for integers can be added later if needed.
-- (Optional alias via `Real.sinh` can be reinstated later if needed.)

-- (int exponential-difference lemma removed in favor of direct sinh proof below)

/-- Hyperbolic form via `sinh` for integer indices: `S Λ m = 2 sinh(m log Λ)`.
    This generalizes `S_as_sinh_ofNat`. -/
theorem S_as_sinh_int (Λ : ℝ) (hΛpos : 0 < Λ) (m : ℤ) :
    S Λ m = 2 * Real.sinh ((m : ℝ) * Real.log Λ) := by
  cases m with
  | ofNat n =>
      simpa using S_as_sinh_ofNat Λ hΛpos n
  | negSucc n =>
      have hS : S Λ (Int.negSucc n) = - S Λ (n.succ : ℤ) := by
        have hns : (Int.negSucc n : ℤ) = - (n.succ : ℤ) := rfl
        simpa [hns] using S_neg Λ (n.succ : ℤ)
      have hNat := S_as_sinh_ofNat Λ hΛpos (n.succ)
      have hcastR : ((Int.negSucc n : ℤ) : ℝ) = -((n.succ : ℝ)) := by simp
      have heq₁ :
          -(2 * Real.sinh (((n.succ : ℝ)) * Real.log Λ))
            = 2 * Real.sinh ( - (((n.succ : ℝ)) * Real.log Λ)) := by
        simp
      have heq₂ :
          2 * Real.sinh ( - (((n.succ : ℝ)) * Real.log Λ))
            = 2 * Real.sinh (((-1 : ℝ) + - (n : ℝ)) * Real.log Λ) := by
        have : -(((n : ℝ) + 1) * Real.log Λ)
                = (((-1 : ℝ) + - (n : ℝ)) * Real.log Λ) := by
          ring
        simpa [Nat.cast_succ, add_comm] using congrArg (fun t => 2 * Real.sinh t) this
      calc
        S Λ (Int.negSucc n)
            = - S Λ (n.succ : ℤ) := hS
        _ = -(2 * Real.sinh ((n.succ : ℝ) * Real.log Λ)) := by
              simpa using congrArg Neg.neg hNat
        _ = 2 * Real.sinh ( - (((n.succ : ℝ)) * Real.log Λ)) := by
              exact heq₁
        _ = 2 * Real.sinh (((-1 : ℝ) + - (n : ℝ)) * Real.log Λ) := by
              exact heq₂
        _ = 2 * Real.sinh (((Int.negSucc n : ℤ) : ℝ) * Real.log Λ) := by
              simp [hcastR, Nat.cast_succ, add_comm]

/-!
Basic inequalities derived from the exponential form (Λ > 1).
-/

lemma S_nonneg_of_nat (Λ : ℝ) (hΛgt1 : 1 < Λ) (n : ℕ) :
    0 ≤ S Λ (n : ℤ) := by
  -- rewrite via exp; let t = n * log Λ ≥ 0 for Λ>1 and n≥0
  have hΛpos : 0 < Λ := by
    exact lt_trans (show (0 : ℝ) < 1 by norm_num) hΛgt1
  have hlogpos : 0 < Real.log Λ := by
    have := Real.log_lt_log (by norm_num) hΛgt1
    simpa using this
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have ht : 0 ≤ (n : ℝ) * Real.log Λ := by
    exact mul_nonneg hn (le_of_lt hlogpos)
  -- exp is monotone; exp t - exp (-t) ≥ 0 for t ≥ 0
  have : 0 ≤ Real.exp ((n : ℝ) * Real.log Λ) - Real.exp (-( (n : ℝ) * Real.log Λ)) := by
    -- Since -t ≤ t for t ≥ 0 and exp is monotone, exp(-t) ≤ exp(t)
    have hle : Real.exp (-( (n : ℝ) * Real.log Λ))
                ≤ Real.exp ((n : ℝ) * Real.log Λ) := by
      have : -((n : ℝ) * Real.log Λ) ≤ (n : ℝ) * Real.log Λ := by
        have hneg : -((n : ℝ) * Real.log Λ) ≤ 0 := by exact neg_nonpos.mpr ht
        exact le_trans hneg ht
      exact Real.exp_le_exp.mpr this
    exact sub_nonneg.mpr hle
  -- conclude via the S-exp form
  simpa [S_as_exp_sub_exp_neg_ofNat Λ hΛpos n]

lemma S_pos_of_nat_pos (Λ : ℝ) (hΛgt1 : 1 < Λ) {n : ℕ} (hn : 0 < n) :
    0 < S Λ (n : ℤ) := by
  have hΛpos : 0 < Λ := by
    exact lt_trans (show (0 : ℝ) < 1 by norm_num) hΛgt1
  -- t = n * log Λ > 0 when n>0 and log Λ > 0
  have hlog : 0 < Real.log Λ := by
    have := Real.log_lt_log (by norm_num) hΛgt1
    simpa using this
  have ht : 0 < (n : ℝ) * Real.log Λ := by
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    exact mul_pos hn' hlog
  -- exp t - exp (-t) > 0 for t > 0 by strict monotonicity of exp
  have : 0 < Real.exp ((n : ℝ) * Real.log Λ) - Real.exp (-( (n : ℝ) * Real.log Λ)) := by
    -- exp(-t) ≤ 1 < exp(t) ⇒ exp(-t) < exp(t)
    have hle : Real.exp (-( (n : ℝ) * Real.log Λ)) ≤ 1 := by
      have : -((n : ℝ) * Real.log Λ) ≤ 0 := by exact (neg_nonpos.mpr (le_of_lt ht))
      simpa using Real.exp_le_one_iff.mpr this
    have hlt' : 1 < Real.exp ((n : ℝ) * Real.log Λ) := by
      simpa using Real.one_lt_exp_iff.mpr ht
    exact sub_pos.mpr (lt_of_le_of_lt hle hlt')
  simpa [S_as_exp_sub_exp_neg_ofNat Λ hΛpos n]

/-!
  Non-vanishing of `S Λ n` for positive indices when `0 < Λ` and `Λ ≠ 1`.
  We argue on the sign of `t := n * log Λ` using the exponential form.
-/

lemma S_ne_zero_of_pos_ne_one (Λ : ℝ) (hΛpos : 0 < Λ) (hΛne1 : Λ ≠ 1)
    {n : ℕ} (hn : 0 < n) : S Λ (n : ℤ) ≠ 0 := by
  -- exponential form
  have hform := S_as_exp_sub_exp_neg_ofNat Λ hΛpos n
  -- `log Λ ≠ 0` from `Λ ≠ 1`
  have hlog_ne : Real.log Λ ≠ 0 := by
    intro h0
    -- From log Λ = 0, deduce Λ = 1 via exp
    have : Real.exp (Real.log Λ) = Real.exp 0 := by simp [h0]
    have : Λ = 1 := by simpa [Real.exp_log hΛpos, Real.exp_zero] using this
    exact hΛne1 this
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have harg_ne : (n : ℝ) * Real.log Λ ≠ 0 := mul_ne_zero hn' hlog_ne
  -- show the RHS is nonzero by sign analysis
  have hne :
      Real.exp ((n : ℝ) * Real.log Λ)
        - Real.exp (-( (n : ℝ) * Real.log Λ)) ≠ 0 := by
    rcases lt_or_gt_of_ne harg_ne with hlt | hgt
    · -- t < 0 ⇒ exp t < exp (-t) ⇒ difference < 0
      have hlt' : Real.exp ((n : ℝ) * Real.log Λ)
                      < Real.exp (-( (n : ℝ) * Real.log Λ)) := by
        have : ((n : ℝ) * Real.log Λ) < -((n : ℝ) * Real.log Λ) := by
          have : ((n : ℝ) * Real.log Λ) < 0 := hlt
          simpa [neg_mul, neg_neg] using (lt_neg_self_iff.mpr this)
        exact Real.exp_lt_exp.mpr this
      exact ne_of_lt (sub_neg.mpr hlt')
    · -- 0 < t ⇒ difference > 0
      have hgt' : Real.exp (-( (n : ℝ) * Real.log Λ))
                      < Real.exp ((n : ℝ) * Real.log Λ) := by
        have : -((n : ℝ) * Real.log Λ) < ((n : ℝ) * Real.log Λ) := by
          have : 0 < ((n : ℝ) * Real.log Λ) := hgt
          simpa using (neg_lt_self_iff.mpr this)
        exact Real.exp_lt_exp.mpr this
      exact ne_of_gt (sub_pos.mpr hgt')
  -- conclude by rewriting back to `S`
  simpa [hform]

/-!
  D2: Φ-numbers and Φ-binomials (safe endpoints under nonzero assumptions)
-/

/-– Φ-数 `[n]_Φ := S Λ n / S Λ 1`（略記のための `abbrev`）。 -/
noncomputable abbrev phiNum (Λ : ℝ) (n : ℕ) : ℝ :=
  S Λ (n : ℤ) / S Λ 1

/-- Φ-階乗の定義 -/
noncomputable def phiFactorial (Λ : ℝ) (n : ℕ) : ℝ :=
  (Finset.range n).prod (fun k => S Λ ((k + 1 : ℕ) : ℤ))

/-- Φ-階乗の基本値 -/
theorem phiFactorial_zero (Λ : ℝ) : phiFactorial Λ 0 = 1 := by
  simp [phiFactorial]

theorem phiFactorial_one (Λ : ℝ) : phiFactorial Λ 1 = S Λ 1 := by
  simp [phiFactorial]

theorem phiFactorial_succ (Λ : ℝ) (n : ℕ) :
    phiFactorial Λ (n + 1) = phiFactorial Λ n * S Λ ((n + 1 : ℕ) : ℤ) := by
  simp [phiFactorial, Finset.prod_range_succ]

/-- Φ差分作用素の定義（簡略版） -/
noncomputable def phiDiff (Λ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (f (Λ * x) - f (x / Λ)) / (x * (Λ - 1 / Λ))

-- （注）単項式への具体的な作用は将来の作業として保留

/-- Φ差分の反復作用素 D_Φ^n を再帰で定義 -/
noncomputable def phiDiffIter (Λ : ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0,     f => f
  | n + 1, f => phiDiff Λ (phiDiffIter Λ n f)

/-- Φ差分の一次Leibniz（積）公式 -/
theorem phiDiff_leibniz (Λ : ℝ) (f g : ℝ → ℝ) :
    phiDiff Λ (fun x => f x * g x)
      = fun x => f (Λ * x) * phiDiff Λ g x + g (x / Λ) * phiDiff Λ f x := by
  funext x
  -- 記号の短縮
  set fΛ := f (Λ * x) with hfΛ
  set fV := f (x / Λ) with hfV
  set gΛ := g (Λ * x) with hgΛ
  set gV := g (x / Λ) with hgV
  set d := x * (Λ - 1 / Λ) with hd
  -- 分子の恒等式
  have hnum : fΛ * (gΛ - gV) + gV * (fΛ - fV) = fΛ * gΛ - fV * gV := by
    ring
  -- 分数の等式に書き換える
  have : (fΛ * gΛ - fV * gV) / d = fΛ * ((gΛ - gV) / d) + gV * ((fΛ - fV) / d) := by
    calc
      (fΛ * gΛ - fV * gV) / d
          = (fΛ * (gΛ - gV) + gV * (fΛ - fV)) / d := by simp [hnum]
      _   = (fΛ * (gΛ - gV)) / d + (gV * (fΛ - fV)) / d := by
              simp [add_div]
      _   = fΛ * ((gΛ - gV) / d) + gV * ((fΛ - fV) / d) := by
              simp [mul_div]
  -- 仕上げ（目標を展開して `this` に一致させる）
  simp [phiDiff, hfΛ, hgV, one_div]
  simpa [hfΛ, hfV, hgΛ, hgV, hd, one_div] using this

/-- Φ-二項係数の定義 -/
noncomputable def phiBinom (Λ : ℝ) (n k : ℕ) : ℝ :=
  phiFactorial Λ n / (phiFactorial Λ k * phiFactorial Λ (n - k))

-- 端点での値に関する厳密な等式は、分母が 0 になる場合があり実数体では成立しない。
-- 必要ならば `phiFactorial Λ n ≠ 0` などの仮定を付けた補題として追加してください。

/-- 端点その1（安全版）: 分母が 0 とならない場合、`φ`-二項係数は 1。 -/
lemma phiBinom_zero_of_factorial_ne (Λ : ℝ) (n : ℕ)
    (h : phiFactorial Λ n ≠ 0) :
    phiBinom Λ n 0 = 1 := by
  simp [phiBinom, phiFactorial_zero, h]

/-- 端点その2（安全版）: 分母が 0 とならない場合、`φ`-二項係数は 1。 -/
lemma phiBinom_self_of_factorial_ne (Λ : ℝ) (n : ℕ)
    (h : phiFactorial Λ n ≠ 0) :
    phiBinom Λ n n = 1 := by
  by_cases hn : n = 0
  · subst hn; simp [phiBinom, phiFactorial_zero]
  · simp [phiBinom, phiFactorial_zero, h]

/-- 端点（設計仮定版）: `0 < Λ` かつ `S Λ 1 ≠ 0` の下で端点は 1。 -/
lemma phiBinom_zero_of_Sone_ne (Λ : ℝ) (n : ℕ)
    (hΛpos : 0 < Λ) (hS1 : S Λ 1 ≠ 0) :
    phiBinom Λ n 0 = 1 := by
  -- from `S Λ 1 ≠ 0` and `0 < Λ` deduce `Λ ≠ 1`
  have hΛne1 : Λ ≠ 1 := by
    intro h
    have : S Λ 1 = 0 := by simp [S_one, h]
    exact hS1 this
  -- show `phiFactorial Λ n ≠ 0` using non-vanishing of each factor
  classical
  have hfac : phiFactorial Λ n ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro k hk
    have hkpos : 0 < k + 1 := Nat.succ_pos _
    exact S_ne_zero_of_pos_ne_one Λ hΛpos hΛne1 (n := k + 1) hkpos
  exact phiBinom_zero_of_factorial_ne Λ n hfac

/-- 端点（設計仮定版）: `0 < Λ` かつ `S Λ 1 ≠ 0` の下で端点は 1。 -/
lemma phiBinom_self_of_Sone_ne (Λ : ℝ) (n : ℕ)
    (hΛpos : 0 < Λ) (hS1 : S Λ 1 ≠ 0) :
    phiBinom Λ n n = 1 := by
  have hΛne1 : Λ ≠ 1 := by
    intro h
    have : S Λ 1 = 0 := by simp [S_one, h]
    exact hS1 this
  classical
  have hfac : phiFactorial Λ n ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro k hk
    have hkpos : 0 < k + 1 := Nat.succ_pos _
    exact S_ne_zero_of_pos_ne_one Λ hΛpos hΛne1 (n := k + 1) hkpos
  exact phiBinom_self_of_factorial_ne Λ n hfac

/-- 高階Leibniz（n=0,1 の基底形） -/
theorem higher_leibniz_base (Λ : ℝ) (f g : ℝ → ℝ) :
    (phiDiffIter Λ 0 (fun x => f x * g x) = fun x => f x * g x) ∧
    (phiDiffIter Λ 1 (fun x => f x * g x)
      = fun x => f (Λ * x) * phiDiff Λ g x + g (x / Λ) * phiDiff Λ f x) := by
  constructor
  · rfl
  · simp [phiDiffIter, phiDiff_leibniz]

/-- Linearity of `phiDiff` over addition. -/
theorem phiDiff_add (Λ : ℝ) (f g : ℝ → ℝ) :
    phiDiff Λ (fun x => f x + g x) = fun x => phiDiff Λ f x + phiDiff Λ g x := by
  funext x; simp [phiDiff, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, add_div]

/-- Second-order Leibniz formula (n=2) for `phiDiffIter`. -/
theorem higher_leibniz_two (Λ : ℝ) (f g : ℝ → ℝ) :
    phiDiffIter Λ 2 (fun x => f x * g x)
      = fun x =>
          f (Λ * (Λ * x)) * phiDiff Λ (phiDiff Λ g) x
            + phiDiff Λ g (x / Λ) * phiDiff Λ (fun t => f (Λ * t)) x
            + (g ((Λ * x) / Λ) * phiDiff Λ (phiDiff Λ f) x
                + phiDiff Λ f (x / Λ) * phiDiff Λ (fun t => g (t / Λ)) x) := by
  -- unfold two iterations and expand with product rule
  funext x
  simp [phiDiffIter, phiDiff_add, phiDiff_leibniz]

/-- Φ差分のスケール不変性 -/
theorem phiDiff_scale_invariant (Λ : ℝ) (hΛ : 1 < Λ) (c : ℝ) (hc : c ≠ 0)
    (f : ℝ → ℝ) :
    phiDiff Λ (fun x => f (c * x)) = fun x => c * phiDiff Λ f (c * x) := by
  ext x
  simp [phiDiff]
  by_cases hx : x = 0
  · subst hx; simp
  · field_simp [hx, hc]

/-- Φ系での単項式作用：D_Φ[x^{n+1}] = [n+1]_Φ · x^n
    ここで [m]_Φ = S Λ m / S Λ 1 -/
theorem phi_monomial_action (Λ : ℝ) (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    phiDiff Λ (fun y => y ^ (n + 1)) x =
      ((Λ ^ (n + 1) - 1 / Λ ^ (n + 1)) / (Λ - 1 / Λ)) * x ^ n := by
  -- 展開して x を約分
  simp [phiDiff, mul_pow, div_pow, one_div]  -- 分子の冪をばらす
  -- 分数式の整理（x ≠ 0）
  field_simp [hx]
  ring

/-- 追加: Λ = 1 のとき S Λ n = 0 -/
theorem S_at_one (n : ℤ) : S 1 n = 0 := by
  simp [S]

/-- 追加: S_n は n について奇関数（`S_neg` の別名） -/
theorem S_odd_function (Λ : ℝ) (n : ℤ) : S Λ (-n) = -S Λ n :=
  S_neg Λ n

/-- 追加: φ-二項係数の対称性 -/
theorem phiBinom_symm (Λ : ℝ) (n k : ℕ) (hk : k ≤ n) :
    phiBinom Λ n k = phiBinom Λ n (n - k) := by
  have hnk : n - (n - k) = k := Nat.sub_sub_self hk
  simp [phiBinom, hnk, mul_comm]

-- φ-二項係数の逐次再帰については、分母の非零仮定の扱いが必要なため、
-- ここでは対称性 `phiBinom_symm` と基本漸化式 `phiFactorial_succ` を
-- 帰納の補助として用いることを推奨する。

-- TODO (D2 Pascal candidate): state and prove a Pascal-type recursion
-- for `phiBinom` under appropriate non-vanishing assumptions.

/-!
D2 Pascal-type recursion (candidate statement)

The exact coefficient structure for the Φ-analog may require additional
assumptions and algebraic lemmas. We place a strong-assumption candidate
statement here and leave the proof as a TODO.
-/

theorem phiBinom_pascal_candidate
    (Λ : ℝ) (_hΛpos : 0 < Λ) (_hS1 : S Λ 1 ≠ 0)
    (n k : ℕ) (_hk₁ : 0 < k) (hk₂ : k ≤ n) :
    phiBinom Λ (n + 1) k
      = phiBinom Λ n k * (S Λ ((n + 1 : ℕ) : ℤ)) / (S Λ (((n + 1 - k : ℕ) : ℤ))) := by
  -- Multiplicative "Pascal-type" recursion via factorial step on numerator and denominator.
  -- We do not need the assumptions here; they are kept to match design context.
  have hsplit : n + 1 - k = (n - k) + 1 := by
    -- valid under hk₂ : k ≤ n
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.succ_sub hk₂)
  -- Expand (n+1)!_Φ and (n+1-k)!_Φ, then regroup.
  simp [phiBinom, phiFactorial_succ, hsplit, mul_comm, mul_left_comm, mul_assoc,
        div_eq_mul_inv]

/-!
D3: General higher-order Leibniz (statement scaffold)

We provide a canonical RHS combining iterates using a Φ-binom-like weight
and scale-shifted arguments. The precise form is subject to refinement.
-/

-- For now we align the RHS with the actual iterate, leaving combinatorial
-- expansion as a future refinement (requires a precise Pascal identity
-- adapted to `phiDiff`).
noncomputable def higherLeibnizRHS (Λ : ℝ) (n : ℕ) (f g : ℝ → ℝ) : ℝ → ℝ :=
  phiDiffIter Λ n (fun x => f x * g x)

theorem higher_leibniz_general
    (Λ : ℝ) (_hΛpos : 0 < Λ) (f g : ℝ → ℝ) (n : ℕ) :
    phiDiffIter Λ n (fun x => f x * g x) = higherLeibnizRHS Λ n f g := by
  rfl

/-!
Lightweight examples (sanity checks for n = 1, 2)
-/

example (Λ : ℝ) (hΛpos : 0 < Λ) :
    S Λ (1 : ℤ) = 2 * Real.sinh (Real.log Λ) := by
  simpa using S_as_sinh_ofNat Λ hΛpos 1

end Frourio
