import Frourio.Algebra.CrossedProduct

namespace Frourio

open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

/-- 単項式同士の積 -/
theorem pbw_mul_single_single {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v₁ v₂ : Fin m → ℤ) (a₁ a₂ : A) :
    PBWModule.mul σ (Finsupp.single v₁ a₁) (Finsupp.single v₂ a₂) =
    Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂) := by
  classical
  -- 二重の `Finsupp.sum_single_index` で単純化
  unfold PBWModule.mul
  simp [Finsupp.sum_single_index, σ.map_zero, zero_mul, mul_zero]

/-- ゼロ元との積（左） -/
theorem pbw_mul_zero_left {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : PBWModule A m) :
    PBWModule.mul σ 0 x = 0 := by
  classical
  unfold PBWModule.mul
  -- 外側の和が 0 のため 0
  simp [Finsupp.sum]

/-- ゼロ元との積（右） -/
theorem pbw_mul_zero_right {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : PBWModule A m) :
    PBWModule.mul σ x 0 = 0 := by
  classical
  unfold PBWModule.mul
  -- 内側の和が 0 のため 0
  simp [Finsupp.sum]

/-- 補助：ゼロ係数の和はゼロ -/
lemma sum_zero_coeff {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v : Fin m → ℤ) (y : PBWModule A m) :
    (y.sum fun v₂ a₂ => Finsupp.single (v + v₂) (0 * σ.act v a₂)) = 0 := by
  classical
  -- 各項が 0 なので有限和も 0
  simp [Finsupp.sum, zero_mul]

/-- 手動展開による左分配（単項式の場合） -/
theorem pbw_left_distrib_single_manual {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v : Fin m → ℤ) (a : A) (y z : PBWModule A m) :
    PBWModule.mul σ (Finsupp.single v a) (y + z) =
    PBWModule.mul σ (Finsupp.single v a) y + PBWModule.mul σ (Finsupp.single v a) z := by
  classical
  -- 定義を展開
  unfold PBWModule.mul

  -- 左辺: single v a の sum を展開
  have lhs : (Finsupp.single v a).sum (fun v₁ a₁ => (y + z).sum (fun v₂ a₂ =>
      Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂))) =
    (y + z).sum (fun v₂ a₂ => Finsupp.single (v + v₂) (a * σ.act v a₂)) := by
    rw [Finsupp.sum_single_index]
    apply sum_zero_coeff

  -- 右辺の第一項
  have rhs1 : (Finsupp.single v a).sum (fun v₁ a₁ => y.sum (fun v₂ a₂ =>
      Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂))) =
    y.sum (fun v₂ a₂ => Finsupp.single (v + v₂) (a * σ.act v a₂)) := by
    rw [Finsupp.sum_single_index]
    apply sum_zero_coeff

  -- 右辺の第二項
  have rhs2 : (Finsupp.single v a).sum (fun v₁ a₁ => z.sum (fun v₂ a₂ =>
      Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂))) =
    z.sum (fun v₂ a₂ => Finsupp.single (v + v₂) (a * σ.act v a₂)) := by
    rw [Finsupp.sum_single_index]
    apply sum_zero_coeff

  -- 書き換え
  rw [lhs, rhs1, rhs2]

  -- y + z の sum を分配
  have sum_distrib : (y + z).sum (fun v₂ a₂ => Finsupp.single (v + v₂) (a * σ.act v a₂)) =
      y.sum (fun v₂ a₂ => Finsupp.single (v + v₂) (a * σ.act v a₂)) +
      z.sum (fun v₂ a₂ => Finsupp.single (v + v₂) (a * σ.act v a₂)) := by
    -- Finsupp.sum_add_index を使用
    rw [Finsupp.sum_add_index]
    · -- h_zero: a₂ = 0 の場合
      intro k _
      rw [σ.map_zero, mul_zero]
      exact @Finsupp.single_zero _ _ _ (v + k)
    · -- h_add: 加法性
      intro k _ b c
      rw [σ.map_add, mul_add, Finsupp.single_add]

  exact sum_distrib

/-- 一般の左分配律 -/
theorem pbw_left_distrib {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : PBWModule A m) :
    PBWModule.mul σ x (y + z) = PBWModule.mul σ x y + PBWModule.mul σ x z := by
  classical
  unfold PBWModule.mul

  -- 外側の sum を分配
  -- x.sum (fun v₁ a₁ => (y + z).sum ...)
  -- = x.sum (fun v₁ a₁ => y.sum ... + z.sum ...)
  -- = x.sum (fun v₁ a₁ => y.sum ...) + x.sum (fun v₁ a₁ => z.sum ...)

  -- 各 v₁, a₁ に対して内側の和を分配（単項式版の補題を使用）
  have hInner :
      (fun v₁ a₁ =>
        (y + z).sum (fun v₂ a₂ => Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂)))
      =
      (fun v₁ a₁ =>
        y.sum (fun v₂ a₂ => Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂)) +
        z.sum (fun v₂ a₂ => Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂))) := by
    funext v₁ a₁
    simpa [PBWModule.mul] using
      (pbw_left_distrib_single_manual (A := A) (m := m) σ v₁ a₁ y z)

  -- 外側の和の分配を x に関する帰納法で証明
  have outer_distrib :
      x.sum (fun v₁ a₁ =>
        y.sum (fun v₂ a₂ => Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂)) +
        z.sum (fun v₂ a₂ => Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂)))
      =
      x.sum (fun v₁ a₁ =>
        y.sum (fun v₂ a₂ => Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂))) +
      x.sum (fun v₁ a₁ =>
        z.sum (fun v₂ a₂ => Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂))) := by
    revert x
    intro x
    induction x using Finsupp.induction with
    | zero =>
        simp [Finsupp.sum_zero_index]
    | @single_add v a s hvs ha0 ih =>
        simp

  -- 目標を hInner で書き換えてから適用
  simp [hInner]

/-- 右分配律 -/
theorem pbw_right_distrib {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : PBWModule A m) :
    PBWModule.mul σ (x + y) z = PBWModule.mul σ x z + PBWModule.mul σ y z := by
  classical
  unfold PBWModule.mul
  -- 外側の和（x + y）を分配
  rw [Finsupp.sum_add_index]
  · -- h_zero: a₁ = 0 の場合
    intro k
    simp [Finsupp.sum, zero_mul]
  · -- h_add: a₁ の加法性
    intro k _ b c
    classical
    have hsum :
        (∑ x ∈ z.support, Finsupp.single (k + x) ((b + c) * σ.act k (z x))) =
        ∑ x ∈ z.support,
          (Finsupp.single (k + x) (b * σ.act k (z x)) +
           Finsupp.single (k + x) (c * σ.act k (z x))) := by
      apply Finset.sum_congr rfl
      intro t ht
      have :
          Finsupp.single (k + t) ((b + c) * σ.act k (z t)) =
            Finsupp.single (k + t) (b * σ.act k (z t)) +
            Finsupp.single (k + t) (c * σ.act k (z t)) := by
        calc
          Finsupp.single (k + t) ((b + c) * σ.act k (z t))
              = Finsupp.single (k + t)
                  (b * σ.act k (z t) + c * σ.act k (z t)) := by
                    simp [add_mul]
          _   = Finsupp.single (k + t) (b * σ.act k (z t)) +
                Finsupp.single (k + t) (c * σ.act k (z t)) := by
                    simp [Finsupp.single_add]
      exact this
    simpa [Finset.sum_add_distrib] using hsum

/-! ## PBWModule Associativity and Unit -/

/-- 単項式3つに対する結合律 -/
theorem pbw_mul_assoc_single3 {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m)
    (v₁ v₂ v₃ : Fin m → ℤ) (a₁ a₂ a₃ : A) :
    PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v₁ a₁) (Finsupp.single v₂ a₂)) (Finsupp.single v₃ a₃)
      = PBWModule.mul σ (Finsupp.single v₁ a₁) (PBWModule.mul σ (Finsupp.single v₂ a₂) (Finsupp.single v₃ a₃)) := by
  classical
  simp [pbw_mul_single_single]
  have hbase : (a₁ * σ.act v₁ a₂) * σ.act (v₁ + v₂) a₃
             = a₁ * σ.act v₁ (a₂ * σ.act v₂ a₃) := by
    calc
      (a₁ * σ.act v₁ a₂) * σ.act (v₁ + v₂) a₃
          = a₁ * (σ.act v₁ a₂ * σ.act (v₁ + v₂) a₃) := by simp [mul_assoc]
      _   = a₁ * (σ.act v₁ a₂ * σ.act v₁ (σ.act v₂ a₃)) := by simp [σ.act_add]
      _   = a₁ * σ.act v₁ (a₂ * σ.act v₂ a₃) := by
            have := (σ.map_mul v₁ a₂ (σ.act v₂ a₃)).symm
            simpa [mul_comm, mul_left_comm, mul_assoc] using congrArg (fun t => a₁ * t) this
  have hscales : (v₁ + v₂) + v₃ = v₁ + (v₂ + v₃) := by
    funext i; simp [add_assoc]
  simp [hbase, hscales]

/-- 単項式を左に固定したときの結合律（一般元に拡張） -/
theorem pbw_assoc_single_left {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v : Fin m → ℤ) (a : A)
    (y z : PBWModule A m) :
    PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) y) z =
    PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ y z) := by
  classical
  revert z
  -- induction on y
  induction y using Finsupp.induction with
  | zero =>
    intro z; simp [PBWModule.mul]
  | @single_add v₂ a₂ s hvs ha0 ih =>
    intro z
    -- helper: associativity when y is a single monomial, by induction on z
    have assoc_single_single : ∀ z : PBWModule A m,
        PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) (Finsupp.single v₂ a₂)) z
          = PBWModule.mul σ (Finsupp.single v a)
              (PBWModule.mul σ (Finsupp.single v₂ a₂) z) := by
      intro z
      induction z using Finsupp.induction with
      | zero =>
        simp [PBWModule.mul]
      | @single_add v₃ a₃ s₃ hv3s ha30 ihz =>
        -- reduce to single + s₃
        calc
          PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) (Finsupp.single v₂ a₂)) (Finsupp.single v₃ a₃ + s₃)
              = PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) (Finsupp.single v₂ a₂)) (Finsupp.single v₃ a₃)
                + PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) (Finsupp.single v₂ a₂)) s₃ := by
                simp [pbw_left_distrib]
          _ = PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ (Finsupp.single v₂ a₂) (Finsupp.single v₃ a₃))
                + PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ (Finsupp.single v₂ a₂) s₃) := by
                have hfirst := pbw_mul_assoc_single3 (A := A) (m := m) σ v v₂ v₃ a a₂ a₃
                simpa [hfirst, ihz]
          _ = PBWModule.mul σ (Finsupp.single v a)
                (PBWModule.mul σ (Finsupp.single v₂ a₂) (Finsupp.single v₃ a₃)
                  + PBWModule.mul σ (Finsupp.single v₂ a₂) s₃) := by
                simp [pbw_left_distrib]
          _ = PBWModule.mul σ (Finsupp.single v a)
                (PBWModule.mul σ (Finsupp.single v₂ a₂) (Finsupp.single v₃ a₃ + s₃)) := by
                simp [pbw_left_distrib]
    -- combine for y = single v₂ a₂ + s
    have h1 := assoc_single_single z
    have h2 := ih z
    calc
      PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) (Finsupp.single v₂ a₂ + s)) z
          = PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) (Finsupp.single v₂ a₂)) z
            + PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) s) z := by
            simp [pbw_left_distrib, pbw_right_distrib]
      _ = PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ (Finsupp.single v₂ a₂) z)
            + PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) s) z := by
            simp [h1]
      _ = PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ (Finsupp.single v₂ a₂) z)
            + PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ s z) := by
            simp [h2]
      _ = PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ (Finsupp.single v₂ a₂ + s) z) := by
            simp [pbw_left_distrib, pbw_right_distrib]

/-- Associativity of PBWModule.mul -/
theorem pbw_mul_assoc {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : PBWModule A m) :
    PBWModule.mul σ (PBWModule.mul σ x y) z =
    PBWModule.mul σ x (PBWModule.mul σ y z) := by
  classical
  revert y z
  induction x using Finsupp.induction with
  | zero =>
    intro y z; simp [PBWModule.mul]
  | @single_add v a s hvs ha0 ih =>
    intro y z
    calc
      PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a + s) y) z
          = PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) y) z
            + PBWModule.mul σ (PBWModule.mul σ s y) z := by
            simp [pbw_right_distrib]
      _ = PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ y z)
            + PBWModule.mul σ s (PBWModule.mul σ y z) := by
            -- prove assoc for the single term and use IH for s
            have hsingle : PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) y) z
                  = PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ y z) :=
              pbw_assoc_single_left (A := A) (m := m) σ v a y z
            have hs : PBWModule.mul σ (PBWModule.mul σ s y) z
                  = PBWModule.mul σ s (PBWModule.mul σ y z) := ih y z
            simp [hsingle, hs]
      _ = PBWModule.mul σ (Finsupp.single v a + s) (PBWModule.mul σ y z) := by
            simp [pbw_right_distrib]

/-- The unit element for PBWModule.mul -/
noncomputable def pbwOne {A : Type*} [Ring A] (m : ℕ) : PBWModule A m :=
  Finsupp.single (0 : Fin m → ℤ) (1 : A)

/-- Left unit property -/
theorem pbw_one_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : PBWModule A m) :
    PBWModule.mul σ (pbwOne m) x = x := by
  classical
  unfold PBWModule.mul
  -- expand outer sum over single 0 1
  simp [pbwOne, Finsupp.sum_single_index, σ.act_zero,
        zero_mul, sum_single_eq_self (A := A) (m := m)]

/-- Right unit property -/
theorem pbw_mul_one {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : PBWModule A m) :
    PBWModule.mul σ x (pbwOne m) = x := by
  classical
  unfold PBWModule.mul
  -- expand inner sum over single 0 1
  -- use σ.map_zero for zero case, σ.map_one for coefficient
  simp [pbwOne, Finsupp.sum_single_index, σ.map_zero, σ.map_one,
        mul_one, sum_single_eq_self (A := A) (m := m)]

end Frourio
