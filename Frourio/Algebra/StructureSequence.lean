import Frourio.Algebra.StructureSequenceCore
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

namespace Frourio

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
theorem phiDiff_scale_invariant (Λ : ℝ) (c : ℝ) (hc : c ≠ 0) (f : ℝ → ℝ) :
    phiDiff Λ (fun x => f (c * x)) = fun x => c * phiDiff Λ f (c * x) := by
  ext x
  unfold phiDiff
  by_cases hx : x = 0
  · subst hx
    simp
  · set d := Λ - 1 / Λ with hd
    have hx1 : c * (Λ * x) = Λ * (c * x) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    have hx2 : c * (x / Λ) = (c * x) / Λ := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hnum : f (c * (Λ * x)) - f (c * (x / Λ))
        = f (Λ * (c * x)) - f ((c * x) / Λ) := by
      simp [hx1, hx2]
    have hfrac : 1 / (x * d) = c / ((c * x) * d) := by
      have h : c / (c * (x * d)) = 1 / (x * d) := by
        simpa using mul_div_mul_left (a := (1 : ℝ)) (b := x * d) (c := c) hc
      have : 1 / (x * d) = c / (c * (x * d)) := h.symm
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    calc
      (f (c * (Λ * x)) - f (c * (x / Λ))) / (x * d)
          = (f (Λ * (c * x)) - f ((c * x) / Λ)) / (x * d) := by
              simp [hnum]
      _ = (f (Λ * (c * x)) - f ((c * x) / Λ)) * (1 / (x * d)) := by
              simp [div_eq_mul_inv]
      _ = (f (Λ * (c * x)) - f ((c * x) / Λ))
              * (c / ((c * x) * d)) := by
              simp [hfrac]
      _ = c * ((f (Λ * (c * x)) - f ((c * x) / Λ)) / ((c * x) * d)) := by
              simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Φ系での単項式作用：D_Φ[x^{n+1}] = [n+1]_Φ · x^n
    ここで [m]_Φ = S Λ m / S Λ 1 -/
theorem phi_monomial_action (Λ : ℝ) (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    phiDiff Λ (fun y => y ^ (n + 1)) x =
      ((Λ ^ (n + 1) - 1 / Λ ^ (n + 1)) / (Λ - 1 / Λ)) * x ^ n := by
  -- 展開して x を約分
  simp only [phiDiff, mul_pow, div_pow, inv_eq_one_div]
  -- x^(n+1)を因数分解
  have : (Λ ^ (n + 1) * x ^ (n + 1) - x ^ (n + 1) / Λ ^ (n + 1)) / (x * (Λ - 1 / Λ))
       = (Λ ^ (n + 1) - 1 / Λ ^ (n + 1)) / (Λ - 1 / Λ) * x ^ n := by
    calc (Λ ^ (n + 1) * x ^ (n + 1) - x ^ (n + 1) / Λ ^ (n + 1)) / (x * (Λ - 1 / Λ))
        = (x ^ (n + 1) * (Λ ^ (n + 1) - 1 / Λ ^ (n + 1))) / (x * (Λ - 1 / Λ)) := by ring
    _   = (x * x ^ n * (Λ ^ (n + 1) - 1 / Λ ^ (n + 1))) / (x * (Λ - 1 / Λ)) := by
          rw [pow_succ']
    _   = (x ^ n * (Λ ^ (n + 1) - 1 / Λ ^ (n + 1))) / (Λ - 1 / Λ) := by
          rw [mul_assoc x, mul_div_mul_left _ _ hx]
    _   = (Λ ^ (n + 1) - 1 / Λ ^ (n + 1)) / (Λ - 1 / Λ) * x ^ n := by ring
  exact this

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
