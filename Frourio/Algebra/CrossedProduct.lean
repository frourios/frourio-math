import Frourio.Algebra.Operators
import Mathlib.Algebra.Group.Defs
import Mathlib.RingTheory.OreLocalization.Basic
-- (avoid heavy linear algebra imports for now)
import Mathlib.Data.Int.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Module.Basic

namespace Frourio

open scoped BigOperators

/--
無限二面体群 D_∞ = ⟨u, r | r² = 1, r u r = u⁻¹⟩。
現時点ではプレースホルダ（後で群表示に基づく形式化へ置換）。
-/
structure DihedralInfinity where
  /- TODO: 生成元と関係式を群表示として実装 -/
  deriving Repr, Inhabited

namespace DihedralInfinity

/-- 無限二面体群の語（簡易表現）。
id, u^n, u^n⋅r の3形を持つ。後で積と簡約を導入する。 -/
inductive Word
  | id : Word
  | u (n : ℤ) : Word       -- u^n
  | ur (n : ℤ) : Word      -- u^n * r
  deriving Repr, DecidableEq

/-- 無限二面体群語の乗法（簡易ルール）。
後で正規形・簡約と整合性を証明する。 -/
def Word.mul : Word → Word → Word
  | Word.id, w => w
  | w, Word.id => w
  | Word.u n, Word.u m => Word.u (n + m)
  | Word.u n, Word.ur m => Word.ur (n + m)
  | Word.ur n, Word.u m => Word.ur (n - m)  -- rur = u⁻¹ より
  | Word.ur n, Word.ur m => Word.u (n - m)  -- r² = 1 より

end DihedralInfinity

/-- スケール作用による交叉積 A ⋊ ℤ^m（プレースホルダ実装） -/
structure CrossedProduct (A : Type*) [Ring A] (m : ℕ) where
  base : A
  scales : Fin m → ℤ  -- スケール作用の指数
  deriving Repr

/-- Z^m による A 上の作用を与えるデータ。
`act v` は環自己準同型（RingEnd）として振る舞うことを仮定する。
ここでは必要最小限の公理のみを与える。 -/
structure ZmAction (A : Type*) [Ring A] (m : ℕ) where
  act : (Fin m → ℤ) → A → A
  act_zero : ∀ a, act 0 a = a
  act_add : ∀ v w a, act (v + w) a = act v (act w a)
  map_one : ∀ v, act v 1 = 1
  map_mul : ∀ v a b, act v (a * b) = act v a * act v b
  map_zero : ∀ v, act v 0 = 0
  map_add : ∀ v a b, act v (a + b) = act v a + act v b

/-- 交叉積の乗法（パラメータ化）。
`x * y = ⟨x.base * σ(act x.scales) y.base, x.scales + y.scales⟩`。 -/
def CrossedProduct.mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m)
    (x y : CrossedProduct A m) : CrossedProduct A m :=
  { base := x.base * σ.act x.scales y.base
  , scales := x.scales + y.scales }

/-– 軽量な演算インスタンス（法則証明は今後強化）。 -/
instance instMulCrossedProduct {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) : Mul (CrossedProduct A m) where
  mul x y := CrossedProduct.mul σ x y

instance instOneCrossedProduct {A : Type*} [Ring A] {m : ℕ} : One (CrossedProduct A m) where
  one := { base := 1, scales := 0 }

instance instAddCrossedProduct {A : Type*} [Ring A] {m : ℕ} : Add (CrossedProduct A m) where
  add x y := { base := x.base + y.base, scales := x.scales + y.scales }

instance instZeroCrossedProduct {A : Type*} [Ring A] {m : ℕ} : Zero (CrossedProduct A m) where
  zero := { base := 0, scales := 0 }

instance instNegCrossedProduct {A : Type*} [Ring A] {m : ℕ} : Neg (CrossedProduct A m) where
  neg x := { base := -x.base, scales := fun i => -x.scales i }

theorem add_assoc_crossed {A : Type*} [Ring A] {m : ℕ}
    (x y z : CrossedProduct A m) : x + y + z = x + (y + z) := by
  cases x with
  | mk xb xs =>
    cases y with
    | mk yb ys =>
      cases z with
      | mk zb zs =>
        have hb : xb + yb + zb = xb + (yb + zb) := by
          simp [add_assoc]
        have hs : (xs + ys) + zs = xs + (ys + zs) := by
          funext i; simp [add_assoc]
        change CrossedProduct.mk (A := A) (m := m)
                 (xb + yb + zb) ((xs + ys) + zs)
              = CrossedProduct.mk (A := A) (m := m)
                 (xb + (yb + zb)) (xs + (ys + zs))
        simp [hb, hs]

theorem add_comm_crossed {A : Type*} [Ring A] {m : ℕ}
    (x y : CrossedProduct A m) : x + y = y + x := by
  cases x with
  | mk xb xs =>
    cases y with
      | mk yb ys =>
        have hb : xb + yb = yb + xb := by simp [add_comm]
        have hs : xs + ys = ys + xs := by
          funext i; simp [add_comm]
        change CrossedProduct.mk (A := A) (m := m)
                 (xb + yb) (xs + ys)
              = CrossedProduct.mk (A := A) (m := m)
                 (yb + xb) (ys + xs)
        simp [hb, hs]

theorem add_left_neg_crossed {A : Type*} [Ring A] {m : ℕ}
    (x : CrossedProduct A m) : -x + x = 0 := by
  cases x with
  | mk xb xs =>
    have hb : -xb + xb = 0 := by simp
    have hs : (fun i => -xs i) + xs = (0 : Fin m → ℤ) := by
      funext i; simp
    have hx0 : CrossedProduct.mk (A := A) (m := m)
                  (-xb + xb) ((fun i => -xs i) + xs)
                = { base := 0, scales := 0 } := by
      simp [hb, hs]
    have h0 : (0 : CrossedProduct A m) = { base := 0, scales := 0 } := rfl
    exact hx0.trans h0.symm

/-- 分配律が成り立つなら `z.scales = 0` を強制する（現在の表現では一般には分配しない）。 -/
theorem scales_eq_zero_if_left_distrib {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : CrossedProduct A m)
    (h : CrossedProduct.mul σ (x + y) z =
         (CrossedProduct.mul σ x z) + (CrossedProduct.mul σ y z)) :
    z.scales = 0 := by
  cases x with
  | mk xb xs =>
    cases y with
    | mk yb ys =>
      cases z with
      | mk zb zs =>
        have hscales : (xs + ys) + zs = (xs + zs) + (ys + zs) := by
          -- extract the `scales` component equality from `h`
          simpa [CrossedProduct.mul, instAddCrossedProduct] using congrArg (fun w => w.scales) h
        -- show `zs = 0` pointwise
        funext i
        have hi := congrArg (fun f => f i) hscales
        -- normalize both sides to `(xs i + ys i) + ...`
        have hi' : (xs i + ys i) + zs i = (xs i + ys i) + (zs i + zs i) := by
          simpa [add_comm, add_left_comm, add_assoc] using hi
        -- cancel the common prefix, then cancel `zs i`
        have hsum : zs i = zs i + zs i := by
          exact add_left_cancel hi'
        -- add `-zs i` to both sides to get `0 = zs i`
        have : 0 = zs i := by
          have := congrArg (fun t => t + (-zs i)) hsum
          simpa [add_comm, add_left_comm, add_assoc] using this
        simp [this]

/-- 乗法の結合律（`ZmAction` の公理から従う）。 -/
theorem mul_assoc_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : CrossedProduct A m) :
    CrossedProduct.mul σ (CrossedProduct.mul σ x y) z =
    CrossedProduct.mul σ x (CrossedProduct.mul σ y z) := by
  cases x with
  | mk xb xs =>
    cases y with
    | mk yb ys =>
      cases z with
      | mk zb zs =>
        -- Base component equality
        have hbase :
            (xb * σ.act xs yb) * σ.act (xs + ys) zb
              = xb * σ.act xs (yb * σ.act ys zb) := by
          calc
            (xb * σ.act xs yb) * σ.act (xs + ys) zb
                = xb * (σ.act xs yb * σ.act (xs + ys) zb) := by
                  simp [mul_assoc]
            _   = xb * (σ.act xs yb * σ.act xs (σ.act ys zb)) := by
                  simp [σ.act_add]
            _   = xb * σ.act xs (yb * σ.act ys zb) := by
                  have hmul' :
                    σ.act xs (yb * σ.act ys zb)
                      = σ.act xs yb * σ.act xs (σ.act ys zb) := by
                    exact (σ.map_mul xs yb (σ.act ys zb))
                  -- rewrite inside xb * (...) using hmul'.symm
                  have := congrArg (fun t => xb * t) hmul'.symm
                  simpa [mul_assoc] using this
        -- Scales component equality
        have hscales : (xs + ys) + zs = xs + (ys + zs) := by
          funext i; simp [add_assoc]
        -- Conclude by simplifying both sides to the same structure
        simp [CrossedProduct.mul, hbase, hscales]

/-- 左単位元（`1`）の性質。 -/
theorem one_mul_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : CrossedProduct A m) :
    CrossedProduct.mul σ (One.one) x = x := by
  cases x with
  | mk xb xs =>
    -- base: 1 * σ 0 xb = xb, scales: 0 + xs = xs
    simp [CrossedProduct.mul, One.one, σ.act_zero, zero_add]

/-- 右単位元（`1`）の性質。 -/
theorem mul_one_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : CrossedProduct A m) :
    CrossedProduct.mul σ x (One.one) = x := by
  cases x with
  | mk xb xs =>
    -- base: xb * σ xs 1 = xb, scales: xs + 0 = xs
    simp [CrossedProduct.mul, One.one, σ.map_one, add_zero]

/-- 交叉積の乗法に関するモノイド構造。 -/
instance instMonoidCrossedProduct {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) : Monoid (CrossedProduct A m) where
  mul x y := CrossedProduct.mul σ x y
  one := { base := 1, scales := 0 }
  mul_assoc := mul_assoc_mul σ
  one_mul := by
    intro x; simpa using one_mul_mul σ x
  mul_one := by
    intro x; simpa using mul_one_mul σ x

/-- 恒等作用による自明な Z^m-作用。 -/
def trivialZmAction (A : Type*) [Ring A] (m : ℕ) : ZmAction A m :=
  { act := fun _ a => a
  , act_zero := by intro a; rfl
  , act_add := by intro v w a; rfl
  , map_one := by intro v; rfl
  , map_mul := by intro v a b; rfl
  , map_zero := by intro v; rfl
  , map_add := by intro v a b; rfl }

/-- Frourio作用素から Z^m-作用を与える（現段階では自明作用）。
将来的に `A` を関数環等に特化した上でスケール `Λ` による作用へ差し替える。 -/
def FrourioOperator.toZmAction {m : ℕ}
    (_op : FrourioOperator m) (A : Type*) [Ring A] : ZmAction A m :=
  trivialZmAction A m

/-- v ∈ ℤ^m に対する合成スケール因子。
exp(∑ᵢ vᵢ log Λᵢ) として定義すると加法が積に対応し、作用の結合が証明しやすい。 -/
noncomputable def FrourioOperator.scaleFactor {m : ℕ}
    (op : FrourioOperator m) (v : Fin m → ℤ) : ℝ :=
  Real.exp (∑ i : Fin m, ((v i : ℝ) * Real.log (op.Λ i)))

/-- 関数環 `ℝ → B` 上の実スケール作用。 -/
noncomputable def FrourioOperator.toZmActionOnFunctions {m : ℕ}
    (op : FrourioOperator m) (B : Type*) [Ring B] :
    ZmAction (ℝ → B) m := by
  classical
  -- 定義
  refine
    { act := fun v (f : ℝ → B) => fun x => f (FrourioOperator.scaleFactor op v * x)
    , act_zero := ?h0
    , act_add := ?hadd
    , map_one := ?hone
    , map_mul := ?hmul
    , map_zero := ?hz
    , map_add := ?hmapadd };
  · -- act_zero
    intro a; funext x
    simp [FrourioOperator.scaleFactor]
  · -- act_add
    intro v w f; funext x
    -- 合成の引数はスケール因子の積になることを示す
    have hsum :
      ∑ i : Fin m, ((v i + w i : ℤ) : ℝ) * Real.log (op.Λ i)
        = (∑ i, (v i : ℝ) * Real.log (op.Λ i)) + (∑ i, (w i : ℝ) * Real.log (op.Λ i)) := by
      classical
      calc
        _ = ∑ i, ((v i : ℝ) * Real.log (op.Λ i) + (w i : ℝ) * Real.log (op.Λ i)) := by
              refine Finset.sum_congr rfl ?h
              intro i _
              simp [Int.cast_add, add_mul]
        _ = _ := by
              simp [Finset.sum_add_distrib]
    have hmulSF :
      FrourioOperator.scaleFactor op (v + w)
        = FrourioOperator.scaleFactor op v *
            FrourioOperator.scaleFactor op w := by
      unfold FrourioOperator.scaleFactor
      calc
        Real.exp (∑ i : Fin m,
            ((v i + w i : ℤ) : ℝ) * Real.log (op.Λ i))
            = Real.exp ((∑ i, (v i : ℝ) * Real.log (op.Λ i)) +
                        (∑ i, (w i : ℝ) * Real.log (op.Λ i))) := by
              exact congrArg Real.exp hsum
        _   = Real.exp (∑ i, (v i : ℝ) * Real.log (op.Λ i)) *
                Real.exp (∑ i, (w i : ℝ) * Real.log (op.Λ i)) := by
              exact (Real.exp_add _ _)
    have hx :
      FrourioOperator.scaleFactor op (v + w) * x
        = FrourioOperator.scaleFactor op w *
            (FrourioOperator.scaleFactor op v * x) := by
      calc
        FrourioOperator.scaleFactor op (v + w) * x
            = (FrourioOperator.scaleFactor op v *
                FrourioOperator.scaleFactor op w) * x := by
                  simp [hmulSF]
        _   = FrourioOperator.scaleFactor op w *
                (FrourioOperator.scaleFactor op v * x) := by
                  simp [mul_assoc, mul_comm]
    -- apply equality inside `f`
    simpa [FrourioOperator.scaleFactor] using congrArg f hx
  · -- map_one
    intro v; funext x; rfl
  · -- map_mul
    intro v f g; funext x; rfl
  · -- map_zero
    intro v; funext x; rfl
  · -- map_add
    intro v f g; funext x; rfl

/-- σ-微分（σ-derivation）の定義。
`δ` が積に対して `δ(ab) = σ(a)δ(b) + δ(a)b` を満たすことを表す。
-/
structure IsSigmaDerivation {A : Type*} [Ring A]
    (σ : A →+* A) (δ : A → A) : Prop where
  (map_add : ∀ a b, δ (a + b) = δ a + δ b)
  (map_mul : ∀ a b, δ (a * b) = σ a * δ b + δ a * b)

/-- Ore拡大の抽象データ。
`E` は拡大環、`Algebra A E` を通して `A` を埋め込み、記号元 `Δ : E` を持つ。
基本交換関係 `Δ⋅a - σ(a)⋅Δ = δ(a)`（右辺は `A` を `E` へ持ち上げたもの）を仮定。 -/
structure OreSystem (A : Type*) [CommRing A] where
  (E : Type*)
  [ringE : Ring E]
  [algebraAE : Algebra A E]
  (Δ : E)
  (σ : A →+* A)
  (δ : A → A)
  (isSigmaDerivation : IsSigmaDerivation σ δ)
  (ore_rel : ∀ a : A,
    Δ * (algebraMap A E a) - (algebraMap A E (σ a)) * Δ = algebraMap A E (δ a))
attribute [instance] OreSystem.ringE OreSystem.algebraAE

/-- Ore交換式（詳細化）：与えられたOre系で交換関係が成り立つこと。 -/
def oreExchange {A : Type*} [CommRing A] {m : ℕ}
    (_op : FrourioOperator m) (sys : OreSystem A) : Prop :=
  ∀ a : A,
    sys.Δ * (algebraMap A sys.E a)
      - (algebraMap A sys.E (sys.σ a)) * sys.Δ
      = algebraMap A sys.E (sys.δ a)

-- Frourio作用素から（退化的な）Ore系を与える（参考）。
-- 旧版では `Δ = 0` で構成していたが、ここでは `Δ = 1` を用いる。
/-- Frourio作用素から（非自明Δを持つ）退化Ore系を与える。
`E = A`, `Δ = 1`, `σ = id`, `δ = 0`。 -/
def FrourioOperator.toTrivialOreSystem {m : ℕ}
    (_op : FrourioOperator m) (A : Type*) [CommRing A] : OreSystem A :=
  { E := A
  , Δ := 1
  , σ := RingHom.id A
  , δ := fun _ => 0
  , isSigmaDerivation :=
      { map_add := by intro a b; simp
      , map_mul := by intro a b; simp }
  , ore_rel := by
      intro a; simp }

/-- 一般の環自己準同型 `σ` に対して、`Δ = 1`, `δ(a) = a - σ(a)` とする非自明なOre系。 -/
def oreFromSigma {A : Type*} [CommRing A] (σ : A →+* A) : OreSystem A :=
  { E := A
  , Δ := 1
  , σ := σ
  , δ := fun a => a - σ a
  , isSigmaDerivation := by
      refine
        { map_add := ?hadd
        , map_mul := ?hmul };
      · intro a b; simp [map_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      · intro a b
        -- δ(ab) = (a - σ a) * b + σ a * (b - σ b)
        have : a * b - σ a * σ b = (a - σ a) * b + σ a * (b - σ b) := by
          ring
        simpa [map_mul, add_comm, add_left_comm, add_assoc] using this
  , ore_rel := by
      intro a; simp }

/-- 実数スケール `c` による関数環上の環自己準同型。 -/
noncomputable def scaleRingHom (B : Type*) [CommRing B] (c : ℝ) :
    (ℝ → B) →+* (ℝ → B) :=
  { toFun := fun f x => f (c * x)
  , map_one' := by funext x; simp
  , map_mul' := by intro f g; funext x; simp
  , map_zero' := by funext x; simp
  , map_add' := by intro f g; funext x; simp }

/-- Frourio作用素のスケール `Λ i` を用いた、関数環上での非自明Ore系。 -/
noncomputable def FrourioOperator.toOreSystemOnFunctions
    {m : ℕ} (op : FrourioOperator m) (B : Type*) [CommRing B]
    (i : Fin m) : OreSystem (ℝ → B) :=
  oreFromSigma (A := (ℝ → B)) (σ := scaleRingHom B (op.Λ i))

/-- 具体例：`ℝ` 上の自明Ore系。 -/
noncomputable def phiOreSystem : OreSystem ℝ :=
  (BasicFrourioOperator φ (by
    -- φ > 0 の証明は `Operators.lean` に準拠
    have h₁ : 0 < 1 + Real.sqrt 5 := by
      have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    have h₂ : 0 < (2 : ℝ) := by norm_num
    have : 0 < (1 + Real.sqrt 5) / 2 := div_pos h₁ h₂
    simpa [φ] using this)).toTrivialOreSystem ℝ

/-- 交叉積における「単項式」：係数1と指数ベクトル `v` を持つ元。 -/
def monomial {A : Type*} [Ring A] {m : ℕ}
    (v : Fin m → ℤ) : CrossedProduct A m :=
  { base := (1 : A), scales := v }

/-- PBW基底の定義（スケルトン）：
指数ベクトル全体から得られる単項式像が基底集合であること。
（将来的に「張る」「一次独立」などの性質をここへ拡張する） -/
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

end Frourio
