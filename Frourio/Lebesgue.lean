/-
Copyright (c) 2024 Frourio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frourio Contributors
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic
import Mathlib.Topology.Basic

/-!
# Lebesgue Number Lemma

This file provides the Lebesgue number lemma for compact metric spaces,
which states that for any open cover of a compact set, there exists a
positive number L (the Lebesgue number) such that any subset with diameter
less than L is contained in some member of the cover.

## Main definitions

* `HasSmallDiam`: Predicate for sets with diameter less than a given value
* `LebesgueNumber`: Property that a number L is a Lebesgue number for a cover

## Main results

* `lebesgue_number_exists`: Every open cover of a compact metric space has a Lebesgue number
* `uniform_control_from_local`: Application to EVI theory - uniform control from local controls

-/

namespace Frourio

open Set Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A set has small diameter if all distances between its points are less than ε -/
def HasSmallDiam (A : Set X) (ε : ℝ) : Prop :=
  ∀ x y, x ∈ A → y ∈ A → dist x y < ε

/-- A number L is a Lebesgue number for a cover if every set with diameter < L
    is contained in some member of the cover -/
def LebesgueNumber {ι : Type*} (K : Set X) (U : ι → Set X) (L : ℝ) : Prop :=
  0 < L ∧ ∀ A ⊆ K, HasSmallDiam A L → ∃ i, A ⊆ U i

section MainTheorem

/-- ルベーグ数補題（コンパクト距離空間の開被覆） -/
theorem lebesgue_number_exists {ι : Type*} [Nonempty ι]
    {K : Set X} (hK : IsCompact K)
    {U : ι → Set X} (hU : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ L > 0, LebesgueNumber K U L :=
by
  classical
  by_cases hK_empty : K = ∅
  · -- K=∅ の場合：任意の正の L がルベーグ数
    refine ⟨1, by norm_num, ?_⟩
    refine ⟨by norm_num, ?_⟩
    intro A hA _
    subst hK_empty
    have : A = ∅ := by simp [subset_empty_iff.mp hA]
    rcases ‹Nonempty ι› with ⟨i⟩
    exact ⟨i, by simp [this]⟩

  -- K ≠ ∅
  have ⟨x₀, hx₀⟩ : ∃ x, x ∈ K := Set.nonempty_iff_ne_empty.mpr hK_empty
  -- 各点 x∈K に対し、U_{idx x} に入る半径 r_x を取る
  have point_radii :
      ∀ x ∈ K, ∃ (i : ι) (r : ℝ), 0 < r ∧ ball x (2*r) ⊆ U i := by
    intro x hx
    have hxU : x ∈ ⋃ i, U i := hcover hx
    rcases mem_iUnion.mp hxU with ⟨i, hi⟩
    -- 開集合の近傍でボールをとる
    have : U i ∈ nhds x := (hU i).mem_nhds hi
    rcases Metric.mem_nhds_iff.mp this with ⟨ε, hεpos, hεsub⟩
    refine ⟨i, ε/2, by linarith, ?_⟩
    -- 2*(ε/2)=ε
    have : 2 * (ε / 2) = ε := by field_simp
    rw [this]
    exact hεsub

  -- choice
  choose idx radius h_radius using point_radii

  -- ボール族で K を被覆
  have ball_cover : K ⊆ ⋃ x : K, ball x.1 (radius x.1 x.2) := by
    intro y hy
    refine mem_iUnion.mpr ?_
    refine ⟨⟨y, hy⟩, ?_⟩
    exact mem_ball_self (h_radius y hy).1

  -- 有限部分被覆
  obtain ⟨F, hFcov⟩ :=
    hK.elim_finite_subcover
      (fun x : K => ball x.1 (radius x.1 x.2))
      (fun _ => isOpen_ball) ball_cover

  by_cases hFne : F.Nonempty
  · -- 有限集合 F の最小半径を L にする
    let L := (F.image (fun x : K => radius x.1 x.2)).min' (hFne.image _)
    refine ⟨L, ?_, ?_⟩
    · -- L>0
      have : ∀ r ∈ F.image (fun x : K => radius x.1 x.2), 0 < r := by
        intro r hr; rcases Finset.mem_image.mp hr with ⟨x, hxF, rfl⟩
        exact (h_radius x.1 x.2).1
      exact this _ (Finset.min'_mem _ _)
    · -- L はレベーグ数
      refine ⟨?pos, ?main⟩
      · -- 再掲：L>0
        have : ∀ r ∈ F.image (fun x : K => radius x.1 x.2), 0 < r := by
          intro r hr; rcases Finset.mem_image.mp hr with ⟨x, hxF, rfl⟩
          exact (h_radius x.1 x.2).1
        exact this _ (Finset.min'_mem _ _)
      · intro A hA hdiam
        by_cases hAemp : A = ∅
        · subst hAemp
          exact ⟨idx x₀ hx₀, by simp⟩
        -- a∈A を取り、有限被覆のいずれかのボールに入れる
        rcases Set.nonempty_iff_ne_empty.mpr hAemp with ⟨a, ha⟩
        have haK : a ∈ K := hA ha
        have : a ∈ ⋃ x ∈ F, ball x.1 (radius x.1 x.2) := hFcov haK
        simp only [mem_iUnion] at this
        rcases this with ⟨x, hxF, hball⟩
        -- A 全体が ball x (2*radius) に入る
        have hA_big : A ⊆ ball x.1 (2 * radius x.1 x.2) := by
          intro z hz
          have h_az : dist a z < L := hdiam a z ha hz
          have hx_a : dist x.1 a < radius x.1 x.2 := by
            rw [mem_ball] at hball
            rw [dist_comm]
            exact hball
          have hL_le : L ≤ radius x.1 x.2 := by
            apply Finset.min'_le
            apply Finset.mem_image_of_mem
            exact hxF
          -- dist x z ≤ dist x a + dist a z < r + L ≤ 2r
          have : dist x.1 z < radius x.1 x.2 + L := by
            calc dist x.1 z ≤ dist x.1 a + dist a z := dist_triangle x.1 a z
                 _ < radius x.1 x.2 + L := add_lt_add hx_a h_az
          have : dist x.1 z < 2 * radius x.1 x.2 := by
            nlinarith
          simpa [mem_ball, dist_comm] using this
        -- ball x (2r) ⊆ U (idx x)
        exact ⟨idx x.1 x.2, hA_big.trans (h_radius x.1 x.2).2⟩
  · -- F=∅ なら K=∅（矛盾）
    have hFempty : F = ∅ := by
      simpa [Finset.nonempty_iff_ne_empty] using hFne
    have : K = ∅ := by
      by_contra hne
      rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨y, hy⟩
      have : y ∈ ⋃ x ∈ F, ball x.1 (radius x.1 x.2) := hFcov hy
      simp at this
      simp [hFempty] at this
    exact absurd this hK_empty

end MainTheorem

section EVIApplications

/-- （変更版）二点局所制御を**球近傍**で与える仮定から、
    ルベーグ数に基づく一様二点制御を得る。向き条件は用いない。 -/
lemma lebesgue_property_from_two_point_local
    {φ : ℝ → ℝ} {s r ε : ℝ}
    (hr : 0 < r) (_hε : 0 < ε)
    (two_point_ball_local :
      ∀ w ∈ Set.Icc 0 r, ∃ ρw > 0, ∃ δw > 0,
        ∀ u ∈ Set.Icc 0 r, ∀ v ∈ Set.Icc 0 r,
          dist u w < ρw → dist v w < ρw →
          φ (s + v) - φ (s + u) ≤ ε * (v - u)) :
    ∃ L > 0,
      ∀ y ∈ Set.Icc 0 r, ∀ z ∈ Set.Icc 0 r, dist y z < L →
        ∃ w ∈ Set.Icc 0 r, ∃ δw > 0,
          dist y w < δw ∧ dist z w < δw ∧
          φ (s + z) - φ (s + y) ≤ ε * (z - y) :=
by
  classical
  -- インデックス：区間 [0,r] の部分型
  let ι := {w : ℝ // w ∈ Set.Icc 0 r}
  haveI : Nonempty ι := ⟨⟨0, by simp [Set.mem_Icc, le_of_lt hr]⟩⟩

  -- 各 w に対して ρw, δw を選ぶ
  choose ρ hρpos δ hδpos hctrl using two_point_ball_local

  -- 開被覆：U w := ball(w, ρw/2)
  let U : ι → Set ℝ := fun i => ball i.1 (ρ i.1 i.2 / 2)
  have hUopen : ∀ i, IsOpen (U i) := fun _ => isOpen_ball

  -- 被覆性：x は i:=⟨x,hx⟩ の U i に入る
  have hcover : (Set.Icc 0 r) ⊆ ⋃ i, U i := by
    intro x hx
    refine mem_iUnion.mpr ?_
    refine ⟨⟨x, hx⟩, ?_⟩
    have : 0 < ρ x hx / 2 := by linarith [hρpos x hx]
    simpa [U, mem_ball, dist_self] using this

  -- ルベーグ数 L を取得
  rcases lebesgue_number_exists (X := ℝ) (ι := ι) (K := Set.Icc 0 r)
    (hK := isCompact_Icc) (U := U) (hU := hUopen) (hcover := hcover)
    with ⟨L, hLpos, hLeb⟩

  -- 主張
  refine ⟨L, hLpos, ?_⟩
  intro y hy z hz hdist
  -- A={y,z} は直径 < L，よってある i で A ⊆ U i
  let A : Set ℝ := {y, z}
  have hA_sub : A ⊆ Set.Icc 0 r := by
    intro t ht
    simp [A] at ht
    rcases ht with rfl | rfl
    · exact hy
    · exact hz
  have hA_small : HasSmallDiam A L := by
    intro u v hu hv
    have hu' : u = y ∨ u = z := by simp [A] at hu; exact hu
    have hv' : v = y ∨ v = z := by simp [A] at hv; exact hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · simp [dist_self]; exact hLpos
    · exact hdist
    · rw [dist_comm]; exact hdist
    · simp [dist_self]; exact hLpos
  rcases (hLeb.2 A hA_sub hA_small) with ⟨i, hAin⟩

  -- y,z ともに ball(i, ρ_i/2) に入る
  have hyU : y ∈ U i := hAin (by simp [A])
  have hzU : z ∈ U i := hAin (by simp [A])
  have hy_close : dist y i.1 < ρ i.1 i.2 / 2 := by simpa [U, mem_ball] using hyU
  have hz_close : dist z i.1 < ρ i.1 i.2 / 2 := by simpa [U, mem_ball] using hzU

  -- ball 半径を ρ_i/2 にしたので、二点とも ρ_i の中
  have hy_close' : dist y i.1 < ρ i.1 i.2 := by
    have : ρ i.1 i.2 / 2 < ρ i.1 i.2 := by
      have := hρpos i.1 i.2; simpa using half_lt_self this
    exact lt_trans hy_close this
  have hz_close' : dist z i.1 < ρ i.1 i.2 := by
    have : ρ i.1 i.2 / 2 < ρ i.1 i.2 := by
      have := hρpos i.1 i.2; simpa using half_lt_self this
    exact lt_trans hz_close this

  -- 二点制御を適用
  -- δ を ρ と同じ値に設定して使用
  refine ⟨i.1, i.2, ρ i.1 i.2, hρpos i.1 i.2, ?_, ?_, ?_⟩
  · exact hy_close'
  · exact hz_close'
  · exact hctrl i.1 i.2 y hy z hz hy_close' hz_close'

end EVIApplications

end Frourio
