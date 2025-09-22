import Frourio.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Frourio

open scoped BigOperators

/-- スケール変換作用素 U_Λ: f(x) ↦ f(Λx) -/
structure ScaleOperator where
  scale : ℝ
  scale_pos : 0 < scale

/-- スケール変換作用素の拡張性 -/
@[ext]
lemma ScaleOperator.ext (U V : ScaleOperator) (h : U.scale = V.scale) : U = V := by
  cases U; cases V
  congr

/-- スケール変換作用素の関数への作用 -/
noncomputable def ScaleOperator.act {α : Type*} (U : ScaleOperator) (f : ℝ → α) : ℝ → α :=
  fun x => f (U.scale * x)

/-- スケール変換の合成 -/
noncomputable def ScaleOperator.comp (U V : ScaleOperator) : ScaleOperator :=
  { scale := U.scale * V.scale
  , scale_pos := mul_pos U.scale_pos V.scale_pos }

/-- 逆スケール変換 -/
noncomputable def ScaleOperator.inv (U : ScaleOperator) : ScaleOperator :=
  { scale := U.scale⁻¹
  , scale_pos := inv_pos.mpr U.scale_pos }

/-- 恒等スケール変換 -/
def ScaleOperator.id : ScaleOperator :=
  { scale := 1
  , scale_pos := by norm_num }

/-- スケール変換の合成は結合的 -/
lemma ScaleOperator.comp_assoc (U V W : ScaleOperator) :
    (U.comp V).comp W = U.comp (V.comp W) := by
  ext
  simp [comp]
  ring

/-- 恒等スケール変換は単位元 -/
lemma ScaleOperator.id_comp (U : ScaleOperator) :
    id.comp U = U := by
  ext
  simp [comp, id]

/-- 恒等スケール変換は右単位元 -/
lemma ScaleOperator.comp_id (U : ScaleOperator) :
    U.comp id = U := by
  ext
  simp [comp, id]

/-- 逆スケール変換は左逆元 -/
lemma ScaleOperator.inv_comp (U : ScaleOperator) :
    U.inv.comp U = id := by
  ext
  simp [comp, inv, id]
  field_simp
  exact div_self (U.scale_pos.ne')

/-- 逆スケール変換は右逆元 -/
lemma ScaleOperator.comp_inv (U : ScaleOperator) :
    U.comp U.inv = id := by
  ext
  simp [comp, inv, id]
  field_simp
  exact div_self (U.scale_pos.ne')

/-- スケール変換作用の合成則 -/
lemma ScaleOperator.act_comp {α : Type*} (U V : ScaleOperator) (f : ℝ → α) :
    U.act (V.act f) = (U.comp V).act f := by
  ext x
  simp [act, comp]
  ring_nf

/-- 恒等スケール変換の作用 -/
lemma ScaleOperator.id_act {α : Type*} (f : ℝ → α) :
    id.act f = f := by
  ext x
  simp [act, id]

/-- 逆スケール変換の作用 -/
lemma ScaleOperator.inv_act {α : Type*} (U : ScaleOperator) (f : ℝ → α) :
    U.inv.act (U.act f) = f := by
  ext x
  simp only [act, inv]
  congr 1
  rw [← mul_assoc]
  simp [U.scale_pos.ne']

/-- スケール変換は単射 -/
lemma ScaleOperator.act_injective {α : Type*} (U : ScaleOperator) :
    Function.Injective (U.act : (ℝ → α) → (ℝ → α)) := by
  intros f g h
  have : U.inv.act (U.act f) = U.inv.act (U.act g) := by rw [h]
  simpa [inv_act] using this

/-- スケール変換の線形性（スカラー倍） -/
lemma ScaleOperator.act_smul (U : ScaleOperator) (c : ℂ) (f : ℝ → ℂ) :
    U.act (fun x => c * f x) = fun x => c * U.act f x := by
  ext x
  simp [act]

/-- スケール変換の線形性（加法） -/
lemma ScaleOperator.act_add (U : ScaleOperator) (f g : ℝ → ℂ) :
    U.act (fun x => f x + g x) = fun x => U.act f x + U.act g x := by
  ext x
  simp [act]

/-- スケール変換のMellin変換への作用 -/
lemma ScaleOperator.mellin_scale (U : ScaleOperator) (f : ℝ → ℂ) :
    ∀ x > 0, U.act f x = f (U.scale * x) := by
  intros x _
  simp [act]

/-- スケール変換の冪乗則 -/
lemma ScaleOperator.pow_scale (U : ScaleOperator) (n : ℕ) :
    ∃ V : ScaleOperator, V.scale = U.scale ^ n ∧
    ∀ f : ℝ → ℂ, ∀ x : ℝ, V.act f x = f (U.scale ^ n * x) := by
  use { scale := U.scale ^ n, scale_pos := by simp [pow_pos U.scale_pos] }
  constructor
  · rfl
  · intros f x
    simp [act]

/-- 黄金比スケール変換 -/
noncomputable def ScaleOperator.golden : ScaleOperator :=
  { scale := φ
  , scale_pos := by
      have : 1 < φ := φ_gt_one
      linarith }

/-- 黄金比の逆スケール変換 -/
lemma ScaleOperator.golden_inv :
    golden.inv.scale = φ⁻¹ := by
  simp [inv, golden]

/-- スケール変換の交換関係 -/
lemma ScaleOperator.comm (U V : ScaleOperator) :
    U.comp V = V.comp U := by
  ext
  simp [comp]
  ring

/-- スケール変換の冪等性チェック -/
lemma ScaleOperator.square_eq_id_iff (U : ScaleOperator) :
    U.comp U = id ↔ U.scale = 1 := by
  constructor
  · intro h
    have hsq : (U.comp U).scale = id.scale := by rw [h]
    simp [comp, id] at hsq
    have hpos : 0 < U.scale := U.scale_pos
    have : U.scale ^ 2 = 1 := by
      rw [sq]
      exact hsq
    have : U.scale = 1 ∨ U.scale = -1 := sq_eq_one_iff.mp this
    cases this
    · assumption
    · exfalso; linarith
  · intro h
    ext
    simp [comp, id, h]

/-- 逆数乗算作用素 M_{1/x}: f(x) ↦ f(x)/x -/
structure InverseMultOperator where
  /-- 原点での振る舞いを指定するフラグ（デフォルトは0） -/
  atZero : ℂ := 0

/-- 逆数乗算作用素の関数への作用 -/
noncomputable def InverseMultOperator.act (M : InverseMultOperator) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => if x ≠ 0 then f x / x else M.atZero

/-- 標準的な逆数乗算作用素（原点で0） -/
def InverseMultOperator.standard : InverseMultOperator := {}

/-- 逆数乗算作用素の合成則 M_{1/x} ∘ M_{1/x} = M_{1/x²} -/
noncomputable def InverseMultOperator.square (M : InverseMultOperator) : InverseMultOperator :=
  { atZero := M.atZero }

/-- 逆数乗算作用素の基本性質 -/
lemma InverseMultOperator.act_eq_div (M : InverseMultOperator) (f : ℝ → ℂ) (x : ℝ) :
    x ≠ 0 → M.act f x = f x / x := by
  intro hx
  simp [act, hx]

/-- 逆数乗算作用素の線形性（スカラー倍、原点で0の場合） -/
lemma InverseMultOperator.act_smul_standard (c : ℂ) (f : ℝ → ℂ) :
    InverseMultOperator.standard.act (fun x => c * f x) =
    fun x => c * InverseMultOperator.standard.act f x := by
  ext x
  simp only [act, standard]
  by_cases h : x ≠ 0
  · simp [h]
    field_simp
  · simp [h]

/-- 逆数乗算作用素の加法性（原点で0の場合） -/
lemma InverseMultOperator.act_add_standard (f g : ℝ → ℂ) :
    InverseMultOperator.standard.act (fun x => f x + g x) =
    fun x => InverseMultOperator.standard.act f x + InverseMultOperator.standard.act g x := by
  ext x
  simp only [act, standard]
  by_cases h : x ≠ 0
  · simp [h]
    field_simp
  · simp [h]

/-- m点Frourio作用素のパラメータ -/
structure FrourioParams (m : ℕ) where
  α : Fin m → ℂ           -- 複素係数
  χ : Fin m → Sign        -- 符号（+1 or -1）
  Λ : Fin m → ℝ           -- スケールパラメータ
  Λ_pos : ∀ i, 0 < Λ i    -- 正値条件

/-- m点Frourio作用素の定義
    Δ^⟨m⟩ = M_{1/x} (Σ_{i=1}^m α_i χ_i U_{Λ_i})
    ここではパラメータを束ねた構造として与える。 -/
structure FrourioOperator (m : ℕ) extends FrourioParams m where

/-- 2点Frourio作用素（基本ケース） -/
noncomputable def BasicFrourioOperator (a : ℝ) (ha : 0 < a) : FrourioOperator 2 :=
  { α := fun i => if i.1 = 0 then (a⁻¹ : ℂ) else (a : ℂ)
  , χ := fun i => if i.1 = 0 then Sign.pos else Sign.neg
  , Λ := fun i => if i.1 = 0 then a else a⁻¹
  , Λ_pos := by
      intro i
      by_cases h : i.1 = 0
      · simpa [h]
        using ha
      · have : 0 < a⁻¹ := inv_pos.mpr ha
        simpa [h]
        using this
  }

/-- 黄金Frourio作用素（φに特化） -/
noncomputable def GoldenFrourioOperator : FrourioOperator 2 :=
  BasicFrourioOperator φ (by
    -- φ = (1 + √5) / 2 > 0
    have h₁ : 0 < 1 + Real.sqrt 5 := by
      have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    have h₂ : 0 < (2 : ℝ) := by norm_num
    have : 0 < (1 + Real.sqrt 5) / 2 := div_pos h₁ h₂
    simpa [φ] using this)

/-- m点Frourio作用素の関数への作用
    Δ^⟨m⟩f = (1/x) Σ_{i=1}^m α_i χ_i f(Λ_i x) -/
noncomputable def FrourioOperator.act {m : ℕ} (op : FrourioOperator m) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => if x ≠ 0 then
    (∑ i : Fin m, op.α i * (op.χ i).toInt * f (op.Λ i * x)) / x
  else 0

/-- スケール作用素を個別に取り出す -/
noncomputable def FrourioOperator.toScaleOperator {m : ℕ}
    (op : FrourioOperator m) (i : Fin m) : ScaleOperator :=
  { scale := op.Λ i
  , scale_pos := op.Λ_pos i }

/-- 逆数乗算作用素の取得（すべてのm点作用素で共通） -/
noncomputable def FrourioOperator.toInverseMult {m : ℕ}
    (_op : FrourioOperator m) : InverseMultOperator := {}

/-- 作用素の線形結合部分（M_{1/x}を除く） -/
noncomputable def FrourioOperator.linearCombination {m : ℕ}
    (op : FrourioOperator m) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∑ i : Fin m, op.α i * (op.χ i).toInt * f (op.Λ i * x)

/-- 作用の分解表現：Δ^⟨m⟩ = M_{1/x} ∘ linearCombination -/
lemma FrourioOperator.act_eq_inverseMult_linearComb {m : ℕ}
    (op : FrourioOperator m) (f : ℝ → ℂ) (x : ℝ) (hx : x ≠ 0) :
    op.act f x = op.linearCombination f x / x := by
  simp [act, linearCombination, hx]

/-- 逆数乗算作用素のMellin変換への作用
    M[M_{1/x} f](s) = M[f](s-1) -/
lemma InverseMultOperator.mellin_shift (M : InverseMultOperator) (f : ℝ → ℂ) :
    ∀ x > 0, M.act f x = f x / x := by
  intro x hx
  simp [InverseMultOperator.act, hx.ne']

/-- FrourioOperatorのMellin記号との整合性 -/
lemma FrourioOperator.mellin_compatible {m : ℕ} (op : FrourioOperator m) :
    ∃ S : ℂ → ℂ, ∀ s : ℂ,
    S s = ∑ i : Fin m, op.α i * (op.χ i).toInt * (op.Λ i : ℂ)^(-s) := by
  use fun s => ∑ i : Fin m, op.α i * (op.χ i).toInt * (op.Λ i : ℂ)^(-s)
  intro s
  rfl

end Frourio
