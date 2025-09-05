import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.EReal.Basic

namespace Frourio

/-!
Descending slope (metric slope) for real-valued energies on a (pseudo)metric space.

We use the right-neighborhood filter around `x` restricted to points at
positive distance, `nhdsWithin x {y | 0 < dist y x}`, to avoid division by 0
in the pseudometric setting.
-/

variable {X : Type*} [PseudoMetricSpace X]

/-! A helper set for points at positive distance from `x`. -/
def posDist (x : X) : Set X := {y | 0 < dist y x}

-- Positive part and basic inequalities.
/-- Positive part of a real number, implemented as `max r 0` (local helper). -/
@[simp] def posPart (r : ℝ) : ℝ := max r 0

@[simp] theorem posPart_nonneg (r : ℝ) : 0 ≤ posPart r := by
  dsimp [posPart]; exact le_max_right _ _

@[simp] theorem posPart_le_abs (r : ℝ) : posPart r ≤ |r| := by
  dsimp [posPart]
  -- `max r 0 ≤ |r|` follows from `r ≤ |r|` and `0 ≤ |r|`.
  refine max_le ?h1 ?h2
  · exact le_abs_self r
  · exact abs_nonneg r

/-- Local quotient used in the slope definition. -/
noncomputable def slopeQuot (F : X → ℝ) (x y : X) : ℝ := (posPart (F x - F y)) / dist x y

/-- Pointwise nonnegativity of the slope quotient when the distance is positive. -/
theorem slopeQuot_nonneg_of_posdist (F : X → ℝ) (x y : X)
  (h : 0 < dist x y) : 0 ≤ slopeQuot F x y := by
  dsimp [slopeQuot]
  exact div_nonneg (posPart_nonneg _) (le_of_lt h)

/-- EReal descending slope `|∂F|_E(x) = limsup_{y→x, 0<dist(y,x)} ((F x - F y)^+) / d(x,y)`.
This EReal form is convenient when moving to Dini/EVI-style statements. -/
noncomputable def descendingSlopeE (F : X → ℝ) (x : X) : EReal :=
  Filter.limsup (fun y : X => (((posPart (F x - F y)) / dist x y : ℝ) : EReal))
    (nhdsWithin x (posDist x))

/-- Real descending slope `|∂F|(x) = limsup_{y→x, 0<dist(y,x)} ((F x - F y)^+) / d(x,y)`.
We restrict to points at positive distance to avoid division by zero in
`PseudoMetricSpace`s. -/
noncomputable def descendingSlope (F : X → ℝ) (x : X) : ℝ :=
  Filter.limsup (fun y : X => (posPart (F x - F y)) / dist x y)
    (nhdsWithin x (posDist x))

-- Basic sanity: for a constant function the inner quotient is 0 pointwise;
-- lemmas identifying the `limsup` are provided later where appropriate
-- boundedness/nontriviality conditions are organized.

end Frourio

namespace Frourio

variable {X : Type*} [PseudoMetricSpace X]

-- (Reserved) Lipschitz control lemmas can be added later when needed.

-- (A real nonnegativity lemma for the limsup can be added later once
-- we fix the boundedness route needed by `le_limsup_of_frequently_le`.)

-- Event-level nonnegativity of the quotient used in `descendingSlope`/`descendingSlopeE`.
theorem eventually_nonneg_slopeQuot (F : X → ℝ) (x : X) :
  ∀ᶠ y in nhdsWithin x (posDist x),
    0 ≤ (posPart (F x - F y)) / dist x y := by
  refine Filter.eventually_of_mem (by exact self_mem_nhdsWithin) ?_;
  intro y hy
  have hpos : 0 < dist x y := by
    have : 0 < dist y x := hy
    simpa [dist_comm] using this
  exact div_nonneg (posPart_nonneg _) (le_of_lt hpos)

/-- Constant function: EReal descending slope is 0 (nontrivial restricted neighborhood). -/
theorem descendingSlopeE_const (x : X) (c : ℝ)
  [Filter.NeBot (nhdsWithin x (posDist x))] :
  descendingSlopeE (fun _ : X => c) x = 0 := by
  dsimp [descendingSlopeE, posPart]
  have : (fun y : X => (((max (c - c) 0) / dist x y : ℝ) : EReal))
                = (fun _ : X => (0 : EReal)) := by
    funext y; simp
  rw [this]
  simp

/-- Constant function: real descending slope is 0 (nontrivial restricted neighborhood). -/
theorem descendingSlope_const (x : X) (c : ℝ)
  [Filter.NeBot (nhdsWithin x (posDist x))] :
  descendingSlope (fun _ : X => c) x = 0 := by
  dsimp [descendingSlope, posPart]
  have : (fun y : X => (max (c - c) 0) / dist x y)
                = (fun _ : X => (0 : ℝ)) := by
    funext y; simp
  rw [this]
  simp

/-- Final Lipschitz bound (EReal): `descendingSlopeE F x ≤ K` when `F` is `K`‑Lipschitz. -/
theorem descendingSlopeE_le_of_lipschitzWith
  (K : Real) (_hK : 0 ≤ K) (F : X → ℝ) (x : X) (hL : ∀ x y, dist (F x) (F y) ≤ K * dist x y) :
  descendingSlopeE F x ≤ (K : EReal) := by
  -- Build a real-valued eventual bound and lift it to EReal.
  have hEvR0 : ∀ᶠ y in nhdsWithin x (posDist x),
      0 ≤ K - (posPart (F x - F y)) / dist x y := by
    refine Filter.eventually_of_mem (by exact self_mem_nhdsWithin) ?_;
    intro y hy
    have hpos : 0 < dist x y := by
      have : 0 < dist y x := hy
      simpa [dist_comm] using this
    have h1 : posPart (F x - F y) ≤ |F x - F y| := posPart_le_abs _
    have h2 : |F x - F y| ≤ K * dist x y := by
      have := hL x y
      rwa [Real.dist_eq] at this
    have h12 : posPart (F x - F y) ≤ K * dist x y := le_trans h1 h2
    have hnonneg : 0 ≤ (1 / dist x y) := by
      have := inv_nonneg.mpr (le_of_lt hpos)
      rw [one_div]; exact this
    have hmul := mul_le_mul_of_nonneg_right h12 hnonneg
    have : (posPart (F x - F y)) / dist x y
              ≤ (K * dist x y) * (1 / dist x y) := by
      simpa [div_eq_mul_inv] using hmul
    have hnz : dist x y ≠ 0 := ne_of_gt hpos
    have hle : (posPart (F x - F y)) / dist x y ≤ K := by
      rw [div_eq_mul_inv] at this ⊢
      rw [one_div] at this
      rw [mul_assoc] at this
      have : posPart (F x - F y) * (dist x y)⁻¹ ≤ K * (dist x y * (dist x y)⁻¹) := this
      rw [mul_inv_cancel₀ hnz] at this
      simp at this
      exact this
    have := sub_nonneg.mpr hle
    -- rearrange to the stated form
    simpa [sub_eq_add_neg, add_comm] using this
  -- Convert back to the desired `≤ K` form and lift into `EReal`.
  have hEvR : ∀ᶠ y in nhdsWithin x (posDist x),
      (posPart (F x - F y)) / dist x y ≤ K :=
    hEvR0.mono (fun _ hy => by exact (sub_nonneg.mp hy))
  have hEv : ∀ᶠ y in nhdsWithin x (posDist x),
      (((posPart (F x - F y)) / dist x y : ℝ) : EReal) ≤ (K : EReal) :=
    hEvR.mono (fun _ hy => by exact EReal.coe_le_coe_iff.mpr hy)
  dsimp [descendingSlopeE]
  exact Filter.limsup_le_of_le (h := hEv)

end Frourio
