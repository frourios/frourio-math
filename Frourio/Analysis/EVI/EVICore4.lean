import Frourio.Analysis.EVI.EVICore3
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic

namespace Frourio

/-- Synchronization in squared distance (no error) via homogeneous Grönwall.
Takes the mixed half-form inequality with `η = 0`, upgrades it to the
`DiniUpper W + (2λ) W ≤ 0` form, and applies the homogeneous Grönwall predicate. -/
theorem eviSynchronizationSq_no_error {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (_geodesicBetween : Prop)
  (Hsum0 : eviSumNoError P u v hu hv _geodesicBetween)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionPropertySq P u v :=
by
  -- Turn the half-form inequality into the homogeneous Grönwall form.
  have Hineq2 : ∀ t : ℝ,
      DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
        + (2 * P.lam) * d2 (u t) (v t) ≤ 0 := by
    intro t
    have h := Hsum0 t
    -- Multiply by 2 (> 0) to remove the 1/2 factor and scale λ accordingly.
    have h' : (2 : ℝ) * ((1 / 2 : ℝ) * DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
              + P.lam * d2 (u t) (v t)) ≤ (2 : ℝ) * 0 := by
      have h2pos : (0 : ℝ) ≤ 2 := by norm_num
      exact (mul_le_mul_of_nonneg_left h h2pos)
    -- Simplify both sides: 2*(1/2)*A = 1*A and 2*(λ*W) = (2λ)*W.
    have h2half : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
    simpa [mul_add, mul_assoc, h2half, one_mul,
           mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc]
      using h'
  -- Apply the homogeneous Grönwall predicate on W(t) = d2(u t, v t).
  exact evi_contraction_sq_from_gronwall P u v hu hv Hineq2 Hgr

/-- two‑EVI (no error): squared-distance synchronization from the mixed half-form
sum inequality and a homogeneous Grönwall lemma. -/
theorem twoEVI_sq_from_sum {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop)
  (Hsum0 : eviSumNoError P u v hu hv geodesicBetween)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionPropertySq P u v :=
by
  exact eviSynchronizationSq_no_error P u v hu hv geodesicBetween Hsum0 Hgr

/-- two‑EVI (no error): distance synchronization using a homogeneous Grönwall
lemma and a bridge from squared to linear distances. -/
theorem twoEVI_dist_from_sum {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop)
  (Hsum0 : eviSumNoError P u v hu hv geodesicBetween)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t)))
  (Hbridge : Hbridge P u v) :
  ContractionProperty P u v :=
by
  apply Hbridge
  exact twoEVI_sq_from_sum P u v hu hv geodesicBetween Hsum0 Hgr

/-- End-to-end (no error): from a mixed half-form EVI sum and a homogeneous
Gronwall predicate, obtain the distance-version synchronization via the
concrete bridge. -/
theorem evi_synchronization_thm_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop)
  (Hsum0 : eviSumNoError P u v hu hv geodesicBetween)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionProperty P u v :=
by
  -- First, obtain the squared-distance synchronization via homogeneous Grönwall.
  have hSq : ContractionPropertySq P u v :=
    eviSynchronizationSq_no_error P u v hu hv geodesicBetween Hsum0 Hgr
  -- Then apply the concrete bridge.
  exact bridge_contraction_concrete P u v hSq

/-- Distance-version synchronization with error. From the squared-distance
bound and algebraic `sqrt` identities, derive

  dist(u t, v t) ≤ exp (-(P.lam) t) · dist(u 0, v 0) + √(max 0 ((2 η) t)).

We use `max 0` to keep the radicand nonnegative when `η t < 0`. -/
def ContractionPropertyWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) : Prop :=
  ∀ t : ℝ,
    dist (u t) (v t) ≤
      Real.exp (-(P.lam) * t) * dist (u 0) (v 0)
        + Real.sqrt (max 0 ((2 * η) * t))

/-- Error-bridge predicate from squared to linear distance with an error term. -/
def HbridgeWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) : Prop :=
  ContractionPropertySqWithError P u v η → ContractionPropertyWithError P u v η

/-- Wrapper: apply a provided error-bridge to convert squared to linear distance. -/
theorem bridge_with_error {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ)
  (H : HbridgeWithError P u v η)
  (Hsq : ContractionPropertySqWithError P u v η) :
  ContractionPropertyWithError P u v η :=
H Hsq



/-- two‑EVI (with external force): squared-distance synchronization from a
single mixed EVI sum hypothesis and an inhomogeneous Grönwall lemma. -/
theorem twoEVI_sq_with_error_from_sum {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop) (hR : MixedErrorBound X u v)
  (Hsum : eviSumWithError P u v hu hv geodesicBetween hR)
  (Hgr : gronwall_exponential_contraction_with_error_half_pred P.lam hR.η
            (fun t => d2 (u t) (v t))) :
  ContractionPropertySqWithError P u v hR.η :=
by
  exact eviSynchronizationSq_with_error P u v hu hv geodesicBetween hR Hsum Hgr

/-- two‑EVI (with external force): distance synchronization with error from a
single mixed sum hypothesis, an inhomogeneous Grönwall lemma, and a bridge. -/
theorem twoEVI_with_error_dist_from_sum {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop) (hR : MixedErrorBound X u v)
  (Hsum : eviSumWithError P u v hu hv geodesicBetween hR)
  (Hgr : gronwall_exponential_contraction_with_error_half_pred P.lam hR.η
            (fun t => d2 (u t) (v t)))
  (Hbridge : HbridgeWithError P u v hR.η) :
  ContractionPropertyWithError P u v hR.η :=
by
  -- First obtain the squared-distance synchronization via inhomogeneous Grönwall
  have hSq : ContractionPropertySqWithError P u v hR.η :=
    twoEVI_sq_with_error_from_sum P u v hu hv geodesicBetween hR Hsum Hgr
  -- Then bridge to distances using the provided error bridge
  exact bridge_with_error P u v hR.η Hbridge hSq

/-- Concrete error-bridge: from squared-distance synchronization with error to
distance-version with error, using `√(x + y) ≤ √x + √y` and the algebraic
identities for `√(exp)` and `√(a·b)`. -/
theorem bridge_contraction_with_error_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) :
  HbridgeWithError P u v η :=
by
  intro hSq; intro t
  -- Start from the squared-distance bound with error.
  have h := hSq t
  -- Set `a := exp (-(2λ) t) · d2(u0,v0)` and `b0 := (2η) t`.
  set a := Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) with ha
  set b0 := (2 * η) * t with hb0
  -- Monotonicity of `sqrt` with `b := max 0 b0`.
  have hmax : b0 ≤ max 0 b0 := le_max_right _ _
  have ha_nonneg : 0 ≤ a := by
    have hx : 0 ≤ Real.exp (-(2 * P.lam) * t) := le_of_lt (Real.exp_pos _)
    have hy : 0 ≤ d2 (u 0) (v 0) := by dsimp [d2]; exact sq_nonneg _
    simpa [ha] using mul_nonneg hx hy
  have hb_nonneg : 0 ≤ max 0 b0 := le_max_left _ _
  have hsum_le : d2 (u t) (v t) ≤ a + max 0 b0 := by
    have : d2 (u t) (v t) ≤ a + b0 := by simpa [ha, hb0] using h
    exact this.trans (add_le_add_left hmax a)
  -- Apply `sqrt` to both sides and then subadditivity.
  have hL_nonneg' : 0 ≤ d2 (u t) (v t) := by dsimp [d2]; exact sq_nonneg _
  have hRsum_nonneg : 0 ≤ a + max 0 b0 := add_nonneg ha_nonneg hb_nonneg
  have hsqrt1 : Real.sqrt (d2 (u t) (v t)) ≤ Real.sqrt (a + max 0 b0) :=
    Real.sqrt_le_sqrt hsum_le
  have hsqrt2 : Real.sqrt (a + max 0 b0) ≤ Real.sqrt a + Real.sqrt (max 0 b0) := by
    exact sqrt_add_le_sqrt_add_sqrt_prop a (max 0 b0) ha_nonneg hb_nonneg
  have hsqrt : Real.sqrt (d2 (u t) (v t)) ≤ Real.sqrt a + Real.sqrt (max 0 b0) :=
    hsqrt1.trans hsqrt2
  -- Rewrite the left side and the `a`-term on the right.
  have hLrw : Real.sqrt (d2 (u t) (v t)) = dist (u t) (v t) :=
    sqrt_d2_dist_prop _ _
  -- Factor `√(a)` into `√(exp) * √(d2)` and simplify.
  have hMul : Real.sqrt a =
      Real.sqrt (Real.exp (-(2 * P.lam) * t)) * Real.sqrt (d2 (u 0) (v 0)) := by
    have hx : 0 ≤ Real.exp (-(2 * P.lam) * t) := le_of_lt (Real.exp_pos _)
    have hy : 0 ≤ d2 (u 0) (v 0) := by dsimp [d2]; exact sq_nonneg _
    simpa [ha] using (sqrt_mul_nonneg_prop (Real.exp (-(2 * P.lam) * t)) (d2 (u 0) (v 0)) hx hy)
  -- `√(exp(-(2λ)t)) = exp(-(λ) t)` by halving the exponent.
  have hErw : Real.sqrt (Real.exp (-(2 * P.lam) * t)) = Real.exp (-(P.lam) * t) := by
    have hx := sqrt_exp_halves_prop (x := (-(2 * P.lam * t)))
    dsimp [sqrt_exp_halves] at hx
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hdiv : ((2 : ℝ) * (P.lam * t)) / 2 = (P.lam * t) := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      simp [mul_comm, h2]
    have hhalf : (-(2 * P.lam * t)) / 2 = -(P.lam * t) := by
      have : (-(2 * P.lam * t)) = -((2 : ℝ) * (P.lam * t)) := by ring
      have hneg : -((2 : ℝ) * (P.lam * t)) / 2 = -(((2 : ℝ) * (P.lam * t)) / 2) := by
        simp [neg_div]
      simpa [this, hdiv] using hneg
    simpa [hhalf] using hx
  have h0rw : Real.sqrt (d2 (u 0) (v 0)) = dist (u 0) (v 0) := sqrt_d2_dist_prop _ _
  -- Align factor order and exponential argument shape robustly.
  have hMul2' : Real.sqrt a = Real.sqrt (Real.exp (-(2 * P.lam) * t)) * dist (u 0) (v 0) := by
    simpa [h0rw] using hMul
  have hErw' : Real.sqrt (Real.exp (-(2 * P.lam) * t)) = Real.exp (-(P.lam * t)) := by
    simpa [neg_mul] using hErw
  have hErw'' : Real.sqrt (Real.exp (-(2 * P.lam * t))) = Real.exp (-(P.lam * t)) := by
    -- adjust associativity inside the exponential argument
    simpa [mul_assoc] using hErw'
  have hRArw : Real.sqrt a = Real.exp (-(P.lam * t)) * dist (u 0) (v 0) := by
    simpa [hErw''] using hMul2'
  -- Rewrite the inequality into the target shape.
  have hfinal :
      dist (u t) (v t)
        ≤ Real.exp (-(P.lam) * t) * dist (u 0) (v 0) + Real.sqrt (max 0 b0) := by
    simpa [hLrw, hRArw, hb0]
      using hsqrt
  -- Conclude by replacing `√(max 0 b0)` with `√(max 0 ((2η) t))`.
  simpa [hb0] using hfinal

/-- Provide a concrete with‑error bridge for all error levels `η` by
reusing the explicit square‑root algebra above. -/
theorem HbridgeWithError_concrete_all_eta {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) :
  ∀ η : ℝ, HbridgeWithError P u v η :=
by
  intro η; exact bridge_contraction_with_error_concrete P u v η

/-- End-to-end: from a mixed EVI sum and an inhomogeneous Grönwall helper,
obtain the distance-version synchronization with error via the concrete bridge. -/
theorem evi_synchronization_with_error_thm_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop) (hR : MixedErrorBound X u v)
  (Hsum : eviSumWithError P u v hu hv geodesicBetween hR)
  (Hgr : (∀ t : ℝ, (1 / 2 : ℝ) *
            DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
            + P.lam * d2 (u t) (v t) ≤ hR.η) →
          ∀ t : ℝ,
            d2 (u t) (v t)
              ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) + (2 * hR.η) * t) :
  ContractionPropertyWithError P u v hR.η :=
by
  -- First, obtain the squared-distance synchronization via inhomogeneous Grönwall.
  have hSq : ContractionPropertySqWithError P u v hR.η :=
    eviSynchronizationSq_with_error P u v hu hv geodesicBetween hR Hsum Hgr
  -- Then apply the concrete bridge with error.
  exact bridge_contraction_with_error_concrete P u v hR.η hSq

end Frourio
