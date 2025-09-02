import Frourio.Algebra.Operators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

namespace Frourio

/-- 構造列 S_n = Λ^n - Λ^{-n} -/
noncomputable def S (Λ : ℝ) (n : ℤ) : ℝ := Λ ^ n - Λ ^ (-n)

/-- S_n の基本的な性質：S_{-n} = -S_n -/
theorem S_neg (Λ : ℝ) (n : ℤ) : S Λ (-n) = -S Λ n := by
  simp [S]

/-- S_0 = 0 -/
theorem S_zero (Λ : ℝ) : S Λ 0 = 0 := by
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

/-- 高階Leibniz（n=0,1 の基底形） -/
theorem higher_leibniz_base (Λ : ℝ) (f g : ℝ → ℝ) :
    (phiDiffIter Λ 0 (fun x => f x * g x) = fun x => f x * g x) ∧
    (phiDiffIter Λ 1 (fun x => f x * g x)
      = fun x => f (Λ * x) * phiDiff Λ g x + g (x / Λ) * phiDiff Λ f x) := by
  constructor
  · rfl
  · simp [phiDiffIter, phiDiff_leibniz]

-- 具体例（黄金比）に関する計算は Examples など別ファイルに委ねる。

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

end Frourio
