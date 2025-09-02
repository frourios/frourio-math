import Frourio.Algebra.CrossedProductCore
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Module.Basic

namespace Frourio

open scoped BigOperators

def IsPBWBasis {A : Type*} [Ring A] {m : ℕ}
    (basis : Set (CrossedProduct A m)) : Prop :=
  basis = Set.range (fun v : (Fin m → ℤ) => monomial (A := A) (m := m) v)

-- 強形式のPBW基底の定義（抽象環Eに対して）。
-- 将来的に `LinearIndependent` と `Submodule.span` を用いた強形式の定義を追加予定

/-- PBW基底の存在定理（スケルトン）。 -/
theorem pbw_basis {A : Type*} [Ring A] (m : ℕ) :
    ∃ (basis : Set (CrossedProduct A m)), IsPBWBasis basis := by
  refine ⟨Set.range (fun v : (Fin m → ℤ) => monomial (A := A) (m := m) v), rfl⟩

/-!  PBWの自由加群表示（Option A）  -/

/-- PBWモジュール：指数ベクトルに係数を割り当てる有限和表示 -/
noncomputable abbrev PBWModule (A : Type*) [Semiring A] (m : ℕ) := ((Fin m → ℤ) →₀ A)

/-- 係数付きPBW単項式（finsupp上） -/
noncomputable def pbwMonomial {A : Type*} [Semiring A] (m : ℕ)
    (v : Fin m → ℤ) (a : A) : PBWModule A m :=
  Finsupp.single v a

/-- 係数1のPBWファミリー -/
noncomputable def pbwFamily {A : Type*} [Semiring A] (m : ℕ) : (Fin m → ℤ) → PBWModule A m :=
  fun v => Finsupp.single v (1 : A)

/-! 強形式のPBW基底（軽量版）：
`LinearIndependent` や `Basis` を直接使わず、finsupp の性質のみで
（1）一次独立相当、（2）生成相当 を定義・証明する。 -/

/-- PBWの標準族 `pbwFamily` が一次独立であることを表す（finsupp版）。 -/
def PBWLinearIndependent (A : Type*) [Semiring A] (m : ℕ) : Prop :=
  ∀ l : (Fin m → ℤ) →₀ A,
    l.sum (fun v a => Finsupp.single v a) = 0 → l = 0

/-- PBWの標準族 `pbwFamily` が生成すること（任意の元が有限和で書けること）。 -/
def PBWSpans (A : Type*) [Semiring A] (m : ℕ) : Prop :=
  ∀ f : PBWModule A m, ∃ l : (Fin m → ℤ) →₀ A,
    f = l.sum (fun v a => Finsupp.single v a)

/-- 強形式のPBW基底（軽量版）：一次独立相当と生成相当の両立。 -/
structure StrongIsPBWBasis (A : Type*) [Semiring A] (m : ℕ) : Prop where
  (linIndep : PBWLinearIndependent A m)
  (spans : PBWSpans A m)

/-- 一次独立相当：係数finsuppの和が0なら係数が0。 -/
-- 補題：係数 `l` による単項式の和は `l` 自身に等しい
lemma sum_single_eq_self {A : Type*} [Semiring A] {m : ℕ}
    (l : (Fin m → ℤ) →₀ A) :
    l.sum (fun v a => Finsupp.single v a) = l := by
  classical
  induction l using Finsupp.induction with
  | zero => simp [Finsupp.sum_zero_index]
  | @single_add v a s hvs ha0 ih =>
      simp [Finsupp.sum_add_index, Finsupp.sum_single_index, ih, add_comm]

lemma pbw_linearIndependent_basic {A : Type*} [Semiring A] (m : ℕ) :
    PBWLinearIndependent A m := by
  classical
  intro l hl
  simpa [sum_single_eq_self (A := A) (m := m)] using hl

/-- 生成相当：任意の finsupp はそのまま単項式の有限和。 -/
lemma pbw_spans_basic {A : Type*} [Semiring A] (m : ℕ) :
    PBWSpans A m := by
  classical
  intro f
  refine ⟨f, ?_⟩
  simp [sum_single_eq_self (A := A) (m := m)]

/-- 強形式PBW基底（軽量版）の存在。 -/
theorem pbw_basis_strong {A : Type*} [Semiring A] (m : ℕ) :
    StrongIsPBWBasis A m :=
  ⟨pbw_linearIndependent_basic (A := A) m, pbw_spans_basic (A := A) m⟩

/-! 関係付け: CrossedProduct ↔ PBWModule（単項式レベル） -/

/-- CrossedProduct の単項式を PBWModule に埋め込む。 -/
noncomputable def toPBW {A : Type*} [Ring A] {m : ℕ}
    (x : CrossedProduct A m) : PBWModule A m :=
  Finsupp.single x.scales x.base

@[simp] lemma toPBW_def {A : Type*} [Ring A] {m : ℕ}
    (a : A) (v : Fin m → ℤ) :
    toPBW (A := A) { base := a, scales := v } = Finsupp.single v a := rfl

/-- PBWの単項式等式から CrossedProduct を構成する（明示的な証明引数を取る形）。 -/
def fromPBW_of_eq_single {A : Type*} [Ring A] {m : ℕ}
    {f : PBWModule A m} {v : Fin m → ℤ} {a : A}
    (_hv : f = Finsupp.single v a) : CrossedProduct A m :=
  { base := a, scales := v }

@[simp] lemma from_toPBW {A : Type*} [Ring A] {m : ℕ}
    (x : CrossedProduct A m) :
    fromPBW_of_eq_single (A := A) (m := m)
      (f := toPBW (A := A) x) (v := x.scales) (a := x.base) rfl = x := by
  cases x; rfl

@[simp] lemma to_fromPBW {A : Type*} [Ring A] {m : ℕ}
    {v : Fin m → ℤ} {a : A} :
    toPBW (A := A) (m := m)
      (fromPBW_of_eq_single (A := A) (m := m)
        (f := Finsupp.single v a) (v := v) (a := a) rfl)
      = Finsupp.single v a := by
  rfl

/-! ## toPBW Properties -/

@[simp] lemma toPBW_zero {A : Type*} [Ring A] {m : ℕ} :
    toPBW (A := A) (m := m) (0 : CrossedProduct A m) = 0 := by
  unfold toPBW
  -- 0 : CrossedProduct A m = { base := 0, scales := 0 }
  change Finsupp.single (0 : Fin m → ℤ) (0 : A) = (0 : PBWModule A m)
  exact @Finsupp.single_zero (Fin m → ℤ) A _ _

/-- toPBW preserves addition only when both have zero scales -/
lemma toPBW_add_zero_scales {A : Type*} [Ring A] {m : ℕ}
    (x y : CrossedProduct A m) (hx : x.scales = 0) (hy : y.scales = 0) :
    toPBW (x + y) = toPBW x + toPBW y := by
  cases x with
  | mk xb xs =>
    cases y with
    | mk yb ys =>
      simp only [toPBW]
      subst hx hy
      -- Now both have scales 0, so x + y has scales 0 + 0 = 0 and base xb + yb
      simp only [instAddCrossedProduct]
      -- The addition simplifies to: {base := xb + yb, scales := 0}
      change Finsupp.single 0 (xb + yb) = Finsupp.single 0 xb + Finsupp.single 0 yb
      rw [Finsupp.single_add]

/-- toPBW preserves negation only when scales are zero -/
lemma toPBW_neg_scale_zero {A : Type*} [Ring A] {m : ℕ}
    (x : CrossedProduct A m) (h : x.scales = 0) :
    toPBW (-x) = - toPBW x := by
  cases x with
  | mk xb xs =>
    simp only [toPBW, instNegCrossedProduct]
    subst h
    simp
    rfl

instance instSubCrossedProduct {A : Type*} [Ring A] {m : ℕ} : Sub (CrossedProduct A m) where
  sub x y := x + (-y)

/-- toPBW preserves subtraction only when scales are the same and equal to zero -/
lemma toPBW_sub_same_zero_scales {A : Type*} [Ring A] {m : ℕ}
    (x y : CrossedProduct A m) (hx : x.scales = 0) (hy : y.scales = 0) :
    toPBW (x - y) = toPBW x - toPBW y := by
  simp only [instSubCrossedProduct, sub_eq_add_neg]
  have h_neg_scales : (-y).scales = 0 := by
    cases y with
    | mk yb ys =>
      simp only [instNegCrossedProduct] at hy ⊢
      funext i
      simp [hy]
  -- x - y = x + (-y) by definition of instSubCrossedProduct
  have : x - y = x + (-y) := rfl
  rw [this]
  rw [toPBW_add_zero_scales x (-y) hx h_neg_scales]
  -- Now we need to show: toPBW x + toPBW (-y) = toPBW x + -toPBW y
  congr 1
  exact toPBW_neg_scale_zero y hy


/-! ## Normal Form and Identity Lemmas -/

@[simp] lemma single_eq_single_iff {A : Type*} [Ring A] {m : ℕ}
    {v w : Fin m → ℤ} {a b : A} :
    (Finsupp.single v a : PBWModule A m) = Finsupp.single w b ↔
    (v = w ∧ a = b) ∨ (a = 0 ∧ b = 0) := by
  simp [Finsupp.single_eq_single_iff]

lemma toPBW_injective_on_single {A : Type*} [Ring A] {m : ℕ}
    {v : Fin m → ℤ} {a : A} (ha : a ≠ 0) :
    ∀ x : CrossedProduct A m,
    toPBW x = Finsupp.single v a → x = { base := a, scales := v } := by
  intro x hx
  cases x with
  | mk xb xs =>
    simp only [toPBW] at hx
    -- From hx: Finsupp.single xs xb = Finsupp.single v a
    -- We need to show xs = v and xb = a
    have h := single_eq_single_iff.mp hx
    cases h with
    | inl h =>
      obtain ⟨hv, hb⟩ := h
      simp [hv, hb]
    | inr h =>
      exact absurd h.2 ha

lemma eq_of_toPBW_eq_on_single {A : Type*} [Ring A] {m : ℕ}
    (x y : CrossedProduct A m) (hx : x.base ≠ 0) (hy : y.base ≠ 0) :
    toPBW x = toPBW y → x = y := by
  intro h
  cases x with
  | mk xb xs =>
    cases y with
    | mk yb ys =>
      simp only [toPBW] at h
      -- From h: Finsupp.single xs xb = Finsupp.single ys yb
      -- We need xs = ys and xb = yb
      rw [single_eq_single_iff] at h
      cases h with
      | inl h => simp [h.1, h.2]
      | inr h =>
        simp at h
        exact absurd h.1 hx

noncomputable def pbwSum {A : Type*} [Semiring A] (m : ℕ)
    (s : Finset (Fin m → ℤ)) (c : (Fin m → ℤ) → A) : PBWModule A m :=
  Finset.sum s (fun v => (Finsupp.single v (c v)))

-- TODO: 有限和零 ⇒ 係数零 の直接証明（本スナップショットでは `simp` が循環するため保留）

/-- ねじれ畳み込みによるPBWModule上の乗法 -/
noncomputable def PBWModule.mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y : PBWModule A m) : PBWModule A m :=
  x.sum (fun v₁ a₁ =>
    y.sum (fun v₂ a₂ =>
      Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂)))

/-– PBWModuleのラッパーとしての交叉積 -/
structure FrourioCrossedProduct (A : Type*) [Ring A] (m : ℕ) where
  elem : PBWModule A m

noncomputable instance instMulFrourioCrossedProduct {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) : Mul (FrourioCrossedProduct A m) where
  mul x y := ⟨PBWModule.mul σ x.elem y.elem⟩

/-! ## Product Compatibility Lemmas (After PBWModule.mul Definition) -/

lemma toPBW_mul_single_right {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : CrossedProduct A m) (v : Fin m → ℤ) (a : A) :
    toPBW (CrossedProduct.mul σ x { base := a, scales := v }) =
    PBWModule.mul σ (toPBW x) (Finsupp.single v a) := by
  cases x with
  | mk xb xs =>
    simp [toPBW, CrossedProduct.mul, PBWModule.mul]
    simp [Finsupp.sum_single_index, σ.map_zero, mul_zero]

lemma toPBW_mul_single_left {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v : Fin m → ℤ) (a : A) (y : CrossedProduct A m) :
    toPBW (CrossedProduct.mul σ { base := a, scales := v } y) =
    PBWModule.mul σ (Finsupp.single v a) (toPBW y) := by
  cases y with
  | mk yb ys =>
    simp [toPBW, CrossedProduct.mul, PBWModule.mul]
    simp [Finsupp.sum_single_index, σ.map_zero]

lemma toPBW_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y : CrossedProduct A m) :
    toPBW (CrossedProduct.mul σ x y) = PBWModule.mul σ (toPBW x) (toPBW y) := by
  cases x with
  | mk xb xs =>
    cases y with
    | mk yb ys =>
      simp [toPBW, CrossedProduct.mul, PBWModule.mul]
      simp [Finsupp.sum_single_index, σ.map_zero, mul_zero]

end Frourio
