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

/-!
P4: Abstract EVI skeleton (definitions and statements only)

This file provides lightweight definitions for the EVI predicate on a
metric space, a Dini-type upper differential, and statement-shaped
properties for contraction, mixed-error EVI for a pair of evolutions,
and a Mosco-style convergence scaffold. Heavy analytical proofs are
intentionally deferred to later phases; here we only fix APIs and types.
-/

/- Basic squared distance helper -/
noncomputable def d2 {X : Type*} [PseudoMetricSpace X] (x y : X) : ℝ :=
  (dist x y) ^ (2 : ℕ)

/- Upper Dini derivative into EReal (avoids coboundedness hassles). -/
noncomputable def DiniUpperE (φ : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((φ (t + h) - φ t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))



/-- Time shift: `t ↦ s + t` just shifts the evaluation point (EReal form). -/
lemma DiniUpperE_shift (φ : ℝ → ℝ) (s u : ℝ) :
  DiniUpperE (fun τ => φ (s + τ)) u = DiniUpperE φ (s + u) := by
  unfold DiniUpperE
  have : (fun h : ℝ =>
            (((φ (s + (u + h)) - φ (s + u)) / h : ℝ) : EReal)) =
         (fun h : ℝ =>
            (((φ ((s + u) + h) - φ (s + u)) / h : ℝ) : EReal)) := by
    funext h; congr 1; ring_nf
  simp [this, add_comm, add_left_comm]

/-- Adding a constant does not change the upper Dini derivative (EReal form). -/
lemma DiniUpperE_add_const (φ : ℝ → ℝ) (c : ℝ) (t : ℝ) :
  DiniUpperE (fun x => φ x + c) t = DiniUpperE φ t := by
  unfold DiniUpperE
  have : (fun h : ℝ => (((φ (t + h) + c) - (φ t + c)) / h : ℝ)) =
         (fun h : ℝ => ((φ (t + h) - φ t) / h : ℝ)) := by
    funext h; ring
  simp

/- If `φ` is nonincreasing, then the upper Dini derivative is ≤ 0 (EReal form). -/
theorem DiniUpper_nonpos_of_nonincreasing (φ : ℝ → ℝ) (t : ℝ)
  (Hmono : ∀ ⦃s u : ℝ⦄, s ≤ u → φ u ≤ φ s) :
  DiniUpperE φ t ≤ (0 : EReal) := by
  -- Show the forward difference quotient is eventually ≤ 0 for h → 0+.
  have hEv : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ((φ (t + h) - φ t) / h : ℝ) ≤ 0 := by
    refine Filter.eventually_of_mem (by exact self_mem_nhdsWithin) ?_;
    intro h hh
    have hpos : 0 < h := hh
    have hmon : φ (t + h) ≤ φ t := by
      have : t ≤ t + h := by exact le_of_lt (by simpa using hpos)
      simpa using (Hmono this)
    have hnum_nonpos : φ (t + h) - φ t ≤ 0 := sub_nonpos.mpr hmon
    have : (φ (t + h) - φ t) / h ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos (le_of_lt hpos)
    simpa using this
  -- Promote to EReal and conclude via `limsup ≤` monotonicity there.
  have hEvE : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (((φ (t + h) - φ t) / h : ℝ) : EReal) ≤ (0 : EReal) :=
    hEv.mono (fun _ hh => by simpa using hh)
  have hbound :
      Filter.limsup (fun h : ℝ => (((φ (t + h) - φ t) / h : ℝ) : EReal))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ≤ (0 : EReal) :=
    Filter.limsup_le_of_le (h := hEvE)
  simpa [DiniUpperE] using hbound

/- Real-valued upper Dini derivative retained for EVI statements. -/
noncomputable def DiniUpper (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Filter.limsup (fun h : ℝ => (φ (t + h) - φ t) / h)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- Time shift: `t ↦ s + t` just shifts the evaluation point (Real form). -/
theorem DiniUpper_shift (φ : ℝ → ℝ) (s t : ℝ) :
  DiniUpper (fun τ => φ (s + τ)) t = DiniUpper φ (s + t) := by
  -- Unfold and normalize using associativity of addition.
  dsimp [DiniUpper]
  -- `(s + (t + h)) = (s + t) + h`
  simp [add_assoc]

/-- Adding a constant to the function does not change the upper Dini derivative (Real form). -/
theorem DiniUpper_add_const (ψ : ℝ → ℝ) (c t : ℝ) :
  DiniUpper (fun τ => ψ τ + c) t = DiniUpper ψ t := by
  -- The constant cancels in the forward difference quotient.
  dsimp [DiniUpper]
  -- `(ψ (t+h) + c) - (ψ t + c) = ψ (t+h) - ψ t`
  simp

/-! Convenience lemmas for Phase P1: constants, add-constant, and time rescale. -/

/-- Upper Dini derivative into EReal for a constant map is 0. -/
theorem DiniUpperE_const (c t : ℝ) :
  DiniUpperE (fun _ => c) t = (0 : EReal) := by
  -- Forward difference quotient is identically 0 on `Ioi 0`.
  dsimp [DiniUpperE];
  simp

/-- Upper Dini derivative (real) for a constant map is 0. -/
theorem DiniUpper_const (c t : ℝ) :
  DiniUpper (fun _ => c) t = 0 := by
  dsimp [DiniUpper]
  simp

/-- Forward difference quotients of a constant map are eventually bounded above by `0`. -/
theorem DiniUpperE_bounds_const_upper (c t : ℝ) :
  ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (((fun _ => c) (t + h) - (fun _ => c) t) / h) ≤ M := by
  refine ⟨0, ?_⟩
  -- The quotient is identically 0 on the right-neighborhood of 0.
  exact Filter.Eventually.of_forall (fun _h => by simp)

/-- Forward difference quotients of a constant map are eventually bounded below by `0`. -/
theorem DiniUpperE_bounds_const_lower (c t : ℝ) :
  ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      m ≤ (((fun _ => c) (t + h) - (fun _ => c) t) / h) := by
  refine ⟨0, ?_⟩
  exact Filter.Eventually.of_forall (fun _h => by simp)

theorem DiniUpper_timeRescale_const (σ c t : ℝ) :
  DiniUpper (fun τ => (fun _ => c) (σ * τ)) t = σ * DiniUpper (fun _ => c) (σ * t) := by
  -- Both sides are 0 since the map is constant.
  simp [DiniUpper_const]

/- EVI problem datum: an energy and a parameter λ -/
structure EVIProblem (X : Type*) [PseudoMetricSpace X] where
  (E : X → ℝ)
  (lam : ℝ)

/- EVI predicate for a curve u : ℝ≥0 → X -/
def IsEVISolution {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u : ℝ → X) : Prop :=
  ∀ (t : ℝ) (v : X),
    (1 / 2 : ℝ) * DiniUpper (fun τ : ℝ => d2 (u τ) v) t
      + P.lam * d2 (u t) v ≤ P.E v - P.E (u t)

/-- Time-rescale of a curve `u` by a positive factor `σ` (skeleton). -/
def timeRescale {X : Type*} (σ : ℝ) (u : ℝ → X) : ℝ → X :=
  fun t => u (σ * t)

/-- Statement-level helper: scaling rule for upper Dini derivative under
time reparameterization `t ↦ σ t` (to be proven in later phases). -/
def DiniUpper_timeRescale_pred (σ : ℝ) (φ : ℝ → ℝ) (t : ℝ) : Prop :=
  DiniUpper (fun τ => φ (σ * τ)) t = σ * DiniUpper φ (σ * t)

/-
Basic subadditivity lemma (statement): the upper Dini derivative of a
sum is bounded above by the sum of upper Dini derivatives. This is a
statement-only placeholder used in G-proofs; the quantitative proof is
introduced in later phases.
-/
def DiniUpper_add_le_pred (φ ψ : ℝ → ℝ) (t : ℝ) : Prop :=
  DiniUpper (fun τ => φ τ + ψ τ) t ≤ DiniUpper φ t + DiniUpper ψ t

/- Add-constant special cases of the additivity upper bound. -/
/-- Left constant: `DiniUpper (c + ψ) ≤ DiniUpper c + DiniUpper ψ` holds with equality. -/
theorem DiniUpper_add_le_pred_const_left (c : ℝ) (ψ : ℝ → ℝ) (t : ℝ) :
  DiniUpper_add_le_pred (fun _ => c) ψ t := by
  -- Rewrite the LHS and RHS using constant rules.
  have hL : DiniUpper (fun τ => (fun _ => c) τ + ψ τ) t = DiniUpper ψ t := by
    -- `(fun _ => c) τ + ψ τ = c + ψ τ`
    simpa [add_comm] using (DiniUpper_add_const ψ c t)
  have hC : DiniUpper (fun _ => c) t = 0 := DiniUpper_const c t
  -- Reduce to `DiniUpper ψ t ≤ DiniUpper ψ t`.
  simp [DiniUpper_add_le_pred, hL, hC]

/-- Right constant: `DiniUpper (φ + c) ≤ DiniUpper φ + DiniUpper c` holds with equality. -/
theorem DiniUpper_add_le_pred_const_right (φ : ℝ → ℝ) (c : ℝ) (t : ℝ) :
  DiniUpper_add_le_pred φ (fun _ => c) t := by
  have hL : DiniUpper (fun τ => φ τ + (fun _ => c) τ) t = DiniUpper φ t := by
    -- `φ τ + (fun _ => c) τ = φ τ + c`
    simpa using (DiniUpper_add_const φ c t)
  have hC : DiniUpper (fun _ => c) t = 0 := DiniUpper_const c t
  simp [DiniUpper_add_le_pred, hL, hC]

/- Subadditivity of the upper Dini derivative via ε-approximation on the right filter. -/
-- TODO(EReal route): Prove `DiniUpper_add_le_pred` via limsup subadditivity on EReal.
-- A robust path is to work with `DiniUpperE` and use
-- `Topology/Instances/EReal/Lemmas.lean: limsup_add_le_of_le` with an ε/2 argument,
-- then bridge back to `ℝ`.
-- NOTE: move helper below to use `DiniUpper_add_le_of_finite`.

/-- EReal subadditivity for the upper Dini derivative, under the standard
exclusions for `EReal` addition at `(⊥, ⊤)` and `(⊤, ⊥)` encoded in mathlib's
`limsup_add_le` hypotheses. -/
theorem DiniUpperE_add_le
  (φ ψ : ℝ → ℝ) (t : ℝ)
  (h1 : DiniUpperE φ t ≠ ⊥ ∨ DiniUpperE ψ t ≠ ⊤)
  (h2 : DiniUpperE φ t ≠ ⊤ ∨ DiniUpperE ψ t ≠ ⊥) :
  DiniUpperE (fun τ => φ τ + ψ τ) t ≤ DiniUpperE φ t + DiniUpperE ψ t := by
  -- Unfold everything to a limsup over the right-neighborhood filter.
  dsimp [DiniUpperE]
  set l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  -- EReal-valued difference quotients for φ and ψ.
  set uE : ℝ → EReal := fun h => (((φ (t + h) - φ t) / h : ℝ) : EReal)
  set vE : ℝ → EReal := fun h => (((ψ (t + h) - ψ t) / h : ℝ) : EReal)
  -- Forward difference of the sum equals sum of forward differences (as EReals).
  have hsum : (fun h : ℝ => (((φ (t + h) + ψ (t + h) - (φ t + ψ t)) / h : ℝ) : EReal))
              = fun h : ℝ => uE h + vE h := by
    funext h; simp [uE, vE, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_div]
  -- Apply EReal limsup subadditivity with its standard disjunction side conditions.
  have H : Filter.limsup (fun h : ℝ => uE h + vE h) l ≤
            Filter.limsup uE l + Filter.limsup vE l := by
    -- Transport the side conditions from `DiniUpperE`.
    have hu1 : Filter.limsup uE l ≠ ⊥ ∨ Filter.limsup vE l ≠ ⊤ := by
      simpa [uE, vE, DiniUpperE, l]
        using (h1 : DiniUpperE φ t ≠ ⊥ ∨ DiniUpperE ψ t ≠ ⊤)
    have hu2 : Filter.limsup uE l ≠ ⊤ ∨ Filter.limsup vE l ≠ ⊥ := by
      simpa [uE, vE, DiniUpperE, l]
        using (h2 : DiniUpperE φ t ≠ ⊤ ∨ DiniUpperE ψ t ≠ ⊥)
    simpa using (EReal.limsup_add_le (f := l) (u := uE) (v := vE) hu1 hu2)
  -- Rewrite via `hsum` and conclude.
  simpa [hsum, uE, vE, l]

/-- Identification of Real/EReal DiniUpper under finiteness. -/
theorem DiniUpper_eq_toReal_of_finite
  (φ : ℝ → ℝ) (t : ℝ)
  (_hfin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hub : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            ((φ (t + h) - φ t) / h) ≤ M)
  (hlb : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            m ≤ ((φ (t + h) - φ t) / h)) :
  DiniUpper φ t = (DiniUpperE φ t).toReal := by
  -- Work with the right-neighborhood filter.
  dsimp [DiniUpper, DiniUpperE]
  set l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  -- Real/EReal difference quotients.
  set fu : ℝ → ℝ := fun h => (φ (t + h) - φ t) / h
  set uE : ℝ → EReal := fun h => ((fu h : ℝ) : EReal)
  haveI : Filter.NeBot l := by
    simpa [l] using (nhdsWithin_Ioi_neBot (α := ℝ) (a := 0) (b := 0) le_rfl)
  -- Supply boundedness assumptions for `fu` on `l`.
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) l fu := by
    rcases hub with ⟨M, hM⟩
    exact Filter.isBoundedUnder_of_eventually_le (f := l) (u := fu) (a := M) hM
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) l fu := by
    rcases hlb with ⟨m, hm⟩
    exact Filter.isCoboundedUnder_le_of_eventually_le (l := l) (f := fu) (x := m) hm
  -- Monotone + continuous coercion `ℝ → EReal` transports limsup.
  have hmap : ((Filter.limsup fu l : ℝ) : EReal)
      = Filter.limsup (fun h : ℝ => ((fu h : ℝ) : EReal)) l := by
    have hmono : Monotone (fun x : ℝ => (x : EReal)) := by
      intro a b hab; simpa [EReal.coe_le_coe_iff] using hab
    have hcont : ContinuousAt (fun x : ℝ => (x : EReal)) (Filter.limsup fu l) :=
      (continuous_coe_real_ereal).continuousAt
    simpa [uE]
      using (Monotone.map_limsup_of_continuousAt (F := l)
                 (f := fun x : ℝ => (x : EReal)) (a := fu)
                 (f_incr := hmono) (f_cont := hcont)
                 (bdd_above := hbdd) (cobdd := hcobdd))
  -- Apply `toReal` to both sides; simplify LHS via `toReal_coe`.
  have hR : Filter.limsup fu l
      = (Filter.limsup (fun h : ℝ => ((fu h : ℝ) : EReal)) l).toReal := by
    have := congrArg (fun x => EReal.toReal x) hmap
    simpa using this
  -- Unfold the definitions and conclude.
  simpa [l, fu, uE]
    using hR

end Frourio
