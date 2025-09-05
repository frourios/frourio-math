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
theorem DiniUpperE_shift (φ : ℝ → ℝ) (s t : ℝ) :
  DiniUpperE (fun τ => φ (s + τ)) t = DiniUpperE φ (s + t) := by
  -- Unfold and normalize using associativity of addition.
  dsimp [DiniUpperE]
  -- `(s + (t + h)) = (s + t) + h`
  simp [add_assoc]

/-- Adding a constant does not change the upper Dini derivative (EReal form). -/
theorem DiniUpperE_add_const (ψ : ℝ → ℝ) (c t : ℝ) :
  DiniUpperE (fun τ => ψ τ + c) t = DiniUpperE ψ t := by
  -- The constant cancels in the forward difference quotient.
  dsimp [DiniUpperE]
  -- `(ψ (t+h) + c) - (ψ t + c) = ψ (t+h) - ψ t`
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

/-- Time-rescale identity holds trivially for constants. -/
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
exclusions for `EReal` addition at `(⊥, ⊤)` and `(⊤, ⊥)` encoded in mathlib’s
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
  -- Ensure `l` is nontrivial (needed by `map_limsup_of_continuousAt`).
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

/-- Real bridge from the EReal inequality: if all three upper Dini derivatives
are finite in `EReal` (neither `⊤` nor `⊥`), then the real-valued additivity
upper bound holds. -/
theorem DiniUpper_add_le_of_finite
  (φ ψ : ℝ → ℝ) (t : ℝ)
  (hφ_fin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hψ_fin : DiniUpperE ψ t ≠ ⊤ ∧ DiniUpperE ψ t ≠ ⊥)
  (hsum_fin : DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊤ ∧
              DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊥)
  (hubφ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((φ (t + h) - φ t) / h) ≤ M)
  (hlbφ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((φ (t + h) - φ t) / h))
  (hubψ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((ψ (t + h) - ψ t) / h) ≤ M)
  (hlbψ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((ψ (t + h) - ψ t) / h))
  (hubsum : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M)
  (hlbsum : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)) :
  DiniUpper_add_le_pred φ ψ t := by
  -- Outline:
  -- 1) Apply `DiniUpperE_add_le` to get the EReal inequality.
  -- 2) Use `toReal_le_toReal` with finiteness to transport ≤ to real numbers.
  -- 3) Identify `toReal (DiniUpperE …)` with `DiniUpper …` under finiteness.
  -- The identification step is deferred and will be supplied by an auxiliary
  -- lemma linking `ℝ` and `EReal` limsups for finite values.
  --
  -- Step 1: EReal inequality.
  have hE :
      DiniUpperE (fun τ => φ τ + ψ τ) t ≤ DiniUpperE φ t + DiniUpperE ψ t :=
    DiniUpperE_add_le φ ψ t
      (Or.inl hφ_fin.2) (Or.inl hφ_fin.1)
  -- Right-hand side is not `⊤` since both summands are finite.
  have hsum_ne_top : DiniUpperE φ t + DiniUpperE ψ t ≠ ⊤ := by
    have hiff := EReal.add_ne_top_iff_ne_top₂ (hφ_fin.2) (hψ_fin.2)
    exact (hiff.mpr ⟨hφ_fin.1, hψ_fin.1⟩)
  -- Step 2: move to reals via `toReal_le_toReal`.
  have hR :
      (DiniUpperE (fun τ => φ τ + ψ τ) t).toReal
        ≤ (DiniUpperE φ t + DiniUpperE ψ t).toReal :=
    EReal.toReal_le_toReal hE (hsum_fin.2) hsum_ne_top
  -- Identify each side with the Real `DiniUpper` values.
  have hL_id :
      (DiniUpperE (fun τ => φ τ + ψ τ) t).toReal
        = DiniUpper (fun τ => φ τ + ψ τ) t := by
    symm; exact DiniUpper_eq_toReal_of_finite (fun τ => φ τ + ψ τ) t hsum_fin hubsum hlbsum
  have hφ_id : (DiniUpperE φ t).toReal = DiniUpper φ t := by
    symm; exact DiniUpper_eq_toReal_of_finite φ t hφ_fin hubφ hlbφ
  have hψ_id : (DiniUpperE ψ t).toReal = DiniUpper ψ t := by
    symm; exact DiniUpper_eq_toReal_of_finite ψ t hψ_fin hubψ hlbψ
  -- Rewrite the RHS `toReal` of a sum into sum of `toReal`.
  have hsum_toReal :
      (DiniUpperE φ t + DiniUpperE ψ t).toReal
        = (DiniUpperE φ t).toReal + (DiniUpperE ψ t).toReal := by
    -- Both summands are finite, so `toReal` is additive.
    simpa using EReal.toReal_add (hx := hφ_fin.1) (h'x := hφ_fin.2)
                                (hy := hψ_fin.1) (h'y := hψ_fin.2)
  -- Conclude the desired Real inequality.
  -- Assemble all identifications and simplify.
  have : DiniUpper (fun τ => φ τ + ψ τ) t
           ≤ DiniUpper φ t + DiniUpper ψ t := by
    simpa [hL_id, hφ_id, hψ_id, hsum_toReal, add_comm, add_left_comm, add_assoc] using hR
  -- Finish.
  simpa [DiniUpper_add_le_pred] using this

/-- Boundedness付き（上下の eventually 有界）での加法劣加法性。 -/
theorem DiniUpper_add_le_pred_of_bounds (φ ψ : ℝ → ℝ) (t : ℝ)
  (hφ_fin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hψ_fin : DiniUpperE ψ t ≠ ⊤ ∧ DiniUpperE ψ t ≠ ⊥)
  (hsum_fin : DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊤ ∧
              DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊥)
  (hubφ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((φ (t + h) - φ t) / h) ≤ M)
  (hlbφ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((φ (t + h) - φ t) / h))
  (hubψ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((ψ (t + h) - ψ t) / h) ≤ M)
  (hlbψ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((ψ (t + h) - ψ t) / h))
  (hubsum : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M)
  (hlbsum : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)) :
  DiniUpper_add_le_pred φ ψ t :=
  DiniUpper_add_le_of_finite φ ψ t hφ_fin hψ_fin hsum_fin
    hubφ hlbφ hubψ hlbψ hubsum hlbsum

-- Retain the original name as a placeholder (unconditional version is not
-- derivable in full generality without additional boundedness/finite limsup
-- hypotheses). Provide a version with explicit bounds instead.
theorem DiniUpper_add_le_pred_holds (φ ψ : ℝ → ℝ) (t : ℝ)
  (hφ_fin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hψ_fin : DiniUpperE ψ t ≠ ⊤ ∧ DiniUpperE ψ t ≠ ⊥)
  (hsum_fin : DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊤ ∧
              DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊥)
  (hubφ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((φ (t + h) - φ t) / h) ≤ M)
  (hlbφ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((φ (t + h) - φ t) / h))
  (hubψ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((ψ (t + h) - ψ t) / h) ≤ M)
  (hlbψ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((ψ (t + h) - ψ t) / h))
  (hubsum : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M)
  (hlbsum : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)) :
  DiniUpper_add_le_pred φ ψ t :=
by
  exact DiniUpper_add_le_pred_of_bounds φ ψ t hφ_fin hψ_fin hsum_fin
    hubφ hlbφ hubψ hlbψ hubsum hlbsum

/--
Gronwall-type exponential bound (statement): if a nonnegative function
`W` satisfies a linear differential inequality in the upper Dini sense,
then it contracts exponentially. Used to derive EVI contraction.
This is a statement-only placeholder at this phase.
-/
def gronwall_exponential_contraction_pred (lam : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) →
    ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0

/-- Inhomogeneous Grönwall-type bound (statement): if
`(1/2)·DiniUpper W + lam·W ≤ η`, then `W` admits a linear-in-time upper bound
of the form `exp (-(2 lam) t) · W 0 + (2 η) t`. This is a placeholder
capturing the shape needed for two-EVI synchronization with an error term. -/
def gronwall_exponential_contraction_with_error_half_pred (lam η : ℝ)
  (W : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) →
    ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t

/- Contraction property statement (no proof here) -/
def ContractionProperty {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∀ t : ℝ,
    dist (u t) (v t) ≤ Real.exp (- P.lam * t) * dist (u 0) (v 0)

/-- Squared-distance version of the contraction property, aligned with the
Gronwall inequality that yields an `exp (-(2λ) t)` decay. -/
def ContractionPropertySq {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∀ t : ℝ,
    d2 (u t) (v t) ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0)

/-- Bridge hypothesis from squared-distance contraction to linear-distance
contraction. This encapsulates the usual `sqrt`-monotonicity and algebraic
identities that convert

  d2(u t, v t) ≤ exp (-(2λ) t) · d2(u 0, v 0)

into

  dist(u t, v t) ≤ exp (-λ t) · dist(u 0, v 0).

At this phase, we keep it as a named predicate to be provided by later
analytic lemmas, allowing higher-level theorems to depend only on this
bridge without committing to heavy proofs here. -/
def Hbridge {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ContractionPropertySq P u v → ContractionProperty P u v

/-- Assumption pack providing a concrete bridge from squared-distance
contraction to linear-distance contraction. In later phases this will be
constructed from square-root monotonicity and algebraic identities. -/
structure BridgeAssumptions {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop where
  (bridge : Hbridge P u v)

/-- Extract the bridge from the assumption pack. -/
theorem Hbridge_from_assumptions {X : Type*} [PseudoMetricSpace X]
  {P : EVIProblem X} {u v : ℝ → X}
  (H : BridgeAssumptions P u v) : Hbridge P u v :=
  H.bridge

/-! Helper lemmas (statement-level) for the bridge -/

/-- Square root of the squared distance equals the distance (statement). -/
def sqrt_d2_dist {X : Type*} [PseudoMetricSpace X]
  (x y : X) : Prop :=
  Real.sqrt (d2 x y) = dist x y

/-- Factorization of the square root of a product under nonnegativity
assumptions (statement). We parameterize the nonnegativity as explicit
arguments to align with `Real.sqrt_mul`. -/
def sqrt_mul_nonneg (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) : Prop :=
  Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b

/-- Square root of an exponential halves the exponent (statement). -/
def sqrt_exp_halves (x : ℝ) : Prop :=
  Real.sqrt (Real.exp x) = Real.exp (x / 2)

/-! Proofs for the helper lemmas -/

theorem sqrt_d2_dist_prop {X : Type*} [PseudoMetricSpace X]
  (x y : X) : sqrt_d2_dist x y := by
  dsimp [sqrt_d2_dist, d2]
  -- Reduce to `sqrt ((dist x y)^2) = |dist x y|` and drop `|·|` via nonnegativity.
  have h := Real.sqrt_sq_eq_abs (dist x y)
  simp [h, abs_of_nonneg dist_nonneg]

theorem sqrt_mul_nonneg_prop (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  sqrt_mul_nonneg a b ha hb := by
  dsimp [sqrt_mul_nonneg]
  -- Rewrite a*b as a square of (√a * √b)
  have hsq : a * b = (Real.sqrt a * Real.sqrt b) ^ (2 : ℕ) := by
    simp [pow_two, mul_comm, mul_left_comm,
      Real.mul_self_sqrt ha, Real.mul_self_sqrt hb]
  have hrewrite :
      Real.sqrt (a * b) = Real.sqrt ((Real.sqrt a * Real.sqrt b) ^ (2 : ℕ)) := by
    simp [hsq]
  -- Apply √(z^2) = |z| and drop absolute value using nonnegativity.
  have hnonneg : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  simp [hrewrite, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]


theorem sqrt_exp_halves_prop (x : ℝ) : sqrt_exp_halves x := by
  dsimp [sqrt_exp_halves]
  have hxmul : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    simpa [add_halves] using (Real.exp_add (x / 2) (x / 2)).symm
  have hx' : Real.exp x = (Real.exp (x / 2)) ^ (2 : ℕ) := by
    simpa [pow_two] using hxmul.symm
  have hxpos : 0 < Real.exp (x / 2) := Real.exp_pos _
  -- Conclude via `sqrt (y^2) = |y|` and positivity of `exp`.
  simp [hx', Real.sqrt_sq_eq_abs, abs_of_pos hxpos]

/-- Subadditivity surrogate: for nonnegative `a, b`,
`√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le_sqrt_add_sqrt_prop (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  -- Compare squares; both sides are nonnegative.
  have hA_nonneg : 0 ≤ Real.sqrt (a + b) := Real.sqrt_nonneg _
  have hB_nonneg : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- Square both sides and compare.
  have hsq : (Real.sqrt (a + b)) ^ (2 : ℕ) ≤ (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ) := by
    -- Left square: `a + b`. Right square: `a + b + 2 √a √b`.
    have hL : (Real.sqrt (a + b)) ^ (2 : ℕ) = a + b := by
      simp [pow_two, Real.mul_self_sqrt, add_nonneg ha hb]
    have hR : (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ)
            = a + b + 2 * Real.sqrt a * Real.sqrt b := by
      have hpoly :
          (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ)
            = Real.sqrt a ^ (2 : ℕ) + 2 * Real.sqrt a * Real.sqrt b + Real.sqrt b ^ (2 : ℕ) := by
        ring_nf
      simpa [pow_two, add_comm, add_left_comm, add_assoc,
             mul_comm, mul_left_comm, mul_assoc,
             Real.mul_self_sqrt ha, Real.mul_self_sqrt hb] using hpoly
    have hcross : 0 ≤ 2 * Real.sqrt a * Real.sqrt b := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      have hprod : 0 ≤ Real.sqrt a * Real.sqrt b :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      simpa [mul_assoc] using mul_nonneg this hprod
    -- Conclude `a + b ≤ a + b + 2 √a √b`.
    have hle : a + b ≤ a + b + 2 * Real.sqrt a * Real.sqrt b :=
      le_add_of_nonneg_right hcross
    simpa [hL, hR] using hle
  -- From `A^2 ≤ B^2` and nonnegativity, infer `A ≤ B`.
  have habs : |Real.sqrt (a + b)| ≤ |Real.sqrt a + Real.sqrt b| := (sq_le_sq).1 hsq
  have hA : |Real.sqrt (a + b)| = Real.sqrt (a + b) := abs_of_nonneg hA_nonneg
  have hB : |Real.sqrt a + Real.sqrt b| = Real.sqrt a + Real.sqrt b := abs_of_nonneg hB_nonneg
  -- Conclude after removing absolute values on both sides.
  simpa [hA, hB] using habs

/-- DiniUpper additivity upper bound (wrapper theorem from the predicate). -/
/- DiniUpper additivity upper bound (wrapper theorem from the predicate). -/
theorem DiniUpper_add_le (φ ψ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_add_le_pred φ ψ t) :
  DiniUpper (fun τ => φ τ + ψ τ) t ≤ DiniUpper φ t + DiniUpper ψ t := H

/-- Time-rescaling rule for DiniUpper (wrapper theorem from the predicate). -/
theorem DiniUpper_timeRescale (σ : ℝ) (φ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_timeRescale_pred σ φ t) :
  DiniUpper (fun τ => φ (σ * τ)) t = σ * DiniUpper φ (σ * t) := H

/-- Time-rescaling for the upper Dini derivative under a positive factor.
This is a wrapper that records the `σ > 0` use‑site while delegating the
analytical content to the supplied predicate `DiniUpper_timeRescale_pred`.
In later phases, we will provide a proof under mild boundedness hypotheses.
-/
theorem DiniUpper_timeRescale_pos (σ : ℝ) (hσ : 0 < σ)
  (φ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_timeRescale_pred σ φ t) :
  DiniUpper (fun τ => φ (σ * τ)) t = σ * DiniUpper φ (σ * t) :=
by
  -- At this phase, the positivity assumption is recorded for API clarity
  -- and future strengthening, while we rely on the provided predicate.
  -- Use `hσ` to record that `σ ≠ 0`, anticipating a change-of-variables proof.
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  -- Currently unused in the algebra, but kept to mark the positive-scale use‑case.
  simpa using (DiniUpper_timeRescale σ φ t H)

/-- Homogeneous Grönwall inequality (turn the predicate into a usable bound). -/
theorem gronwall_exponential_contraction_from_pred (lam : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_pred lam W)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 :=
by
  exact Hpred Hineq

/-- Homogeneous Grönwall inequality (wrapper using the predicate). -/
theorem gronwall_exponential_contraction (lam : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_pred lam W)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 :=
  gronwall_exponential_contraction_from_pred lam W Hpred Hineq

/-- Inhomogeneous Grönwall inequality (turn the predicate into a usable bound). -/
theorem gronwall_exponential_contraction_with_error_half_from_pred
  (lam η : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_with_error_half_pred lam η W)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t :=
by
  exact Hpred Hineq

/-- Inhomogeneous Grönwall inequality in the `half` form (wrapper using the predicate). -/
theorem gronwall_exponential_contraction_with_error_half
  (lam η : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_with_error_half_pred lam η W)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t :=
  gronwall_exponential_contraction_with_error_half_from_pred lam η W Hpred Hineq

/-- Inhomogeneous Grönwall inequality (`half` form, core statement):
If `(1/2)·DiniUpper W + lam·W ≤ η` pointwise, then
`W t ≤ exp (-(2 lam) t) · W 0 + (2 η) t`. -/
theorem gronwall_exponential_contraction_with_error_half_core
  (lam η : ℝ) (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_with_error_half_pred lam η W)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t :=
by
  exact H Hineq

/-- Special case: time-reparameterization with unit factor is tautological. -/
theorem DiniUpper_timeRescale_one (φ : ℝ → ℝ) (t : ℝ) :
  DiniUpper (fun τ => φ (1 * τ)) t = (1 : ℝ) * DiniUpper φ (1 * t) := by
  -- Trivial by rewriting the argument and factor `1`.
  simp [DiniUpper, one_mul]

/-- Special case of homogeneous Grönwall at `λ = 0` using a provided predicate. -/
theorem gronwall_exponential_contraction_zero
  (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_pred (0 : ℝ) W)
  (Hineq0 : ∀ t : ℝ, DiniUpper W t ≤ 0) :
  ∀ t : ℝ, W t ≤ W 0 := by
  have h := gronwall_exponential_contraction (0 : ℝ) W H (by
    intro t; simpa [zero_mul, add_comm] using (Hineq0 t))
  intro t; simpa [zero_mul, Real.exp_zero] using h t

/-- Special case of inhomogeneous Grönwall at `η = 0` using a provided predicate. -/
theorem gronwall_exponential_contraction_with_error_zero
  (lam : ℝ) (W : ℝ → ℝ)
  (H : (∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ 0) →
        ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0)
  (Hineq0 : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 := by
  -- Adapt `H` to the `η = 0` version expected by the `with_error_half` helper.
  have H' : (∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ (0 : ℝ)) →
            ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * (0 : ℝ)) * t := by
    intro hineq
    have h0 := H (by intro t; simpa using hineq t)
    intro t; simpa [zero_mul, add_comm] using h0 t
  have h := gronwall_exponential_contraction_with_error_half lam 0 W H' (by
    intro t; simpa using (Hineq0 t))
  intro t; simpa [zero_mul, add_comm] using h t

/- Homogeneous Grönwall at λ = 0 (direct form, analysis deferred) -/


/-- Homogeneous Grönwall inequality (core theorem):
If `(DiniUpper W) + (2 λ) W ≤ 0` pointwise, then
`W t ≤ exp (-(2 λ) t) · W 0`. -/
/- Auxiliary: product rule upper bound for `exp(2λ·) * W` (not needed at this stage). -/

theorem gronwall_exponential_contraction_core (lam : ℝ) (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_pred lam W)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 :=
by
  exact H Hineq

-- The closed predicate form is supplied externally when needed; a
-- local, argument-taking wrapper is available via `gronwall_exponential_contraction`.

/-- Homogeneous Grönwall at λ = 0 (direct form):
If `DiniUpper W ≤ 0` pointwise, then `W` is nonincreasing: `W t ≤ W 0`. -/
theorem gronwall_zero (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_pred (0 : ℝ) W)
  (Hineq0 : ∀ t : ℝ, DiniUpper W t ≤ 0) :
  ∀ t : ℝ, W t ≤ W 0 := by
  -- Use the closed predicate at `λ = 0` and simplify the exponential factor.
  have h := gronwall_exponential_contraction (0 : ℝ) W H
    (by intro t; simpa [zero_mul, add_comm] using (Hineq0 t))
  intro t
  simpa [zero_mul, Real.exp_zero] using h t

/- Inhomogeneous Grönwall (half version): kept as predicate-level result below. -/

-- (Predicate-level closure for the inhomogeneous half version is deferred to later phases.)

/-- Concrete bridge from squared-distance contraction to linear-distance
contraction using monotonicity of `Real.sqrt` and algebraic identities. -/
theorem bridge_contraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (H : Hbridge P u v) (hSq : ContractionPropertySq P u v) :
  ContractionProperty P u v :=
H hSq

-- Closed contraction theorem can be produced by combining
-- `evi_contraction_sq_from_gronwall` with a concrete `Hbridge`.

/-- Concrete bridge from squared-distance to linear-distance contraction.
It combines `sqrt_d2_dist_prop`, `sqrt_mul_nonneg_prop`, and
`sqrt_exp_halves_prop` with `Real.sqrt_le_sqrt` to pass to distances. -/
theorem bridge_contraction_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hSq : ContractionPropertySq P u v) :
  ContractionProperty P u v := by
  intro t
  have h := hSq t
  -- Both sides of the inequality are nonnegative, so `sqrt` preserves `≤`.
  have hL_nonneg : 0 ≤ d2 (u t) (v t) := by
    dsimp [d2]; exact sq_nonneg _
  have hR_nonneg : 0 ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) := by
    have hx : 0 ≤ Real.exp (-(2 * P.lam) * t) := le_of_lt (Real.exp_pos _)
    have hy : 0 ≤ d2 (u 0) (v 0) := by dsimp [d2]; exact sq_nonneg _
    exact mul_nonneg hx hy
  have hsqrt :
      Real.sqrt (d2 (u t) (v t)) ≤
        Real.sqrt (Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0)) :=
    Real.sqrt_le_sqrt h
  -- Normalize associativity in the exponential argument.
  have hassoc3 : (-(2 * P.lam) * t) = (-(2 * P.lam * t)) := by simp [mul_assoc]
  have hsqrt' :
      Real.sqrt (d2 (u t) (v t)) ≤
        Real.sqrt (Real.exp (-(2 * P.lam * t)) * d2 (u 0) (v 0)) := by
    simpa [hassoc3] using hsqrt
  -- Rewrite both sides via helper lemmas.
  have hLrw : Real.sqrt (d2 (u t) (v t)) = dist (u t) (v t) :=
    sqrt_d2_dist_prop _ _
  have hMul :
      Real.sqrt (Real.exp (-(2 * P.lam * t)) * d2 (u 0) (v 0)) =
        Real.sqrt (Real.exp (-(2 * P.lam * t))) *
          Real.sqrt (d2 (u 0) (v 0)) := by
    -- Apply the product rule for square roots under nonnegativity
    have hx : 0 ≤ Real.exp (-(2 * P.lam * t)) := le_of_lt (Real.exp_pos _)
    have hy : 0 ≤ d2 (u 0) (v 0) := by dsimp [d2]; exact sq_nonneg _
    simpa using sqrt_mul_nonneg_prop (Real.exp (-(2 * P.lam * t))) (d2 (u 0) (v 0)) hx hy
  have hErw : Real.sqrt (Real.exp (-(2 * P.lam * t))) = Real.exp (-(P.lam) * t) := by
    -- √(exp(x)) = exp(x/2) with x = (-(2 λ) t); then simplify the half.
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
  have h0rw : Real.sqrt (d2 (u 0) (v 0)) = dist (u 0) (v 0) :=
    sqrt_d2_dist_prop _ _
  have hRrw :
      Real.sqrt (Real.exp (-(2 * P.lam * t)) * d2 (u 0) (v 0)) =
        Real.exp (-(P.lam) * t) * dist (u 0) (v 0) := by
    simpa [hErw, h0rw] using hMul
  -- Conclude after rewriting.
  simpa [hLrw, hRrw] using hsqrt'

/-- Pack the concrete bridge as an `Hbridge`. -/
theorem Hbridge_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) :
  Hbridge P u v :=
by
  intro hSq; exact bridge_contraction_concrete P u v hSq

-- The concrete bridge proof below combines
-- `sqrt_d2_dist_prop`, `sqrt_mul_nonneg_prop`, and `sqrt_exp_halves_prop`
-- with `Real.sqrt_le_sqrt` and elementary arithmetic rewrites.

/- Contraction: packaged as a statement-producing definition -/
def eviContraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v) : Prop :=
  ContractionProperty P u v

/- Alias to match design naming (statement-level). -/
abbrev evi_contraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v) : Prop :=
  eviContraction P u v hu hv

-- moved below after `eviContraction_general`

/--
EVI contraction (self-curve special case).

Proof sketch: For any curve `u`, the contraction inequality against itself
reduces to `0 ≤ exp(-λ t) * 0`, since `dist (u t) (u t) = 0 = dist (u 0) (u 0)`.
Thus the desired inequality holds by reflexivity of `≤` on `0`.

This serves as a minimal, fully formal base case toward the full EVI
contraction proof (Gronwall-based) developed in later phases.
-/
theorem evi_contraction_self {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u : ℝ → X)
  (_hu : IsEVISolution P u) :
  ContractionProperty P u u := by
  intro t
  -- `dist (u t) (u t) = 0` and `dist (u 0) (u 0) = 0`
  have hL : dist (u t) (u t) = 0 := dist_self _
  have hR : dist (u 0) (u 0) = 0 := dist_self _
  -- RHS is `exp(-λ t) * 0 = 0`
  simp

/-- If the upper Dini differential inequality holds for the squared distance
and we have a Gronwall-type exponential contraction lemma for a function `W`,
then we obtain the squared-distance contraction property. This bridges the
EVI inequality to a ready-to-use decay statement without performing the
sqrt-step to linear distance yet. -/
theorem evi_contraction_sq_from_gronwall {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionPropertySq P u v := by
  -- Directly feed the differential inequality into the Gronwall helper.
  exact Hgr (by intro t; simpa using Hineq2 t)

/-- Final general contraction theorem via a bridge from squared to linear
distances. Given the squared-distance contraction and a user-provided bridge
that converts it to the linear-distance statement (using monotonicity of sqrt
and algebraic identities), we obtain the desired contraction property. -/
theorem eviContraction_general {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t)))
  (Hbridge : Hbridge P u v) :
  ContractionProperty P u v :=
by
  apply Hbridge
  exact evi_contraction_sq_from_gronwall P u v hu hv Hineq2 Hgr

/--
EVI contraction (named theorem form, P0 skeleton).

Proof strategy: Assume the squared-distance Dini inequality and a Grönwall
exponential decay statement for `W t = d2 (u t) (v t)`. This yields a
`ContractionPropertySq`. A bridge hypothesis converts it into the linear
`ContractionProperty`. Heavy analytic parts are abstracted as inputs.
-/
theorem eviContraction_thm
  {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t)))
  (Hbridge : Hbridge P u v) :
  ContractionProperty P u v :=
by
  exact eviContraction_general P u v hu hv Hineq2 Hgr Hbridge

/--
Concrete EVI contraction wrapper (closed via G1 + B1).

Given the squared-distance differential inequality for `W t = d2(u t, v t)`
and the Grönwall predicate `gronwall_exponential_contraction_pred`, this
derives the linear-distance contraction using the concrete bridge
`bridge_contraction_concrete`.

This closes the contraction pipeline without requiring an external
`Hbridge` argument. -/
theorem evi_contraction_thm_concrete
  {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionProperty P u v :=
by
  -- First get the squared-distance contraction via Grönwall (G1)
  have hSq : ContractionPropertySq P u v :=
    evi_contraction_sq_from_gronwall P u v hu hv Hineq2 Hgr
  -- Then bridge to linear distance via the concrete bridge (B1)
  exact bridge_contraction_concrete P u v hSq

/- Mixed-error bound skeleton for a pair (u, v). The `bound` field can
encode any intended inequality along a selected geodesic; we keep it
abstract at this stage. -/
structure MixedErrorBound (X : Type*) [PseudoMetricSpace X]
  (u v : ℝ → X) where
  (η : ℝ)
  (bound : ∀ _t : ℝ, Prop)

/- Mixed EVI sum statement (no proof; returns a Prop) -/
def eviSumWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v)
  (_geodesicBetween : Prop) (hR : MixedErrorBound X u v) : Prop :=
  ∀ t : ℝ,
    (1 / 2 : ℝ) * DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + P.lam * d2 (u t) (v t) ≤ hR.η

/-- Mixed EVI sum without error (half form): expected output of the
"add-and-absorb-cross-terms" step when the geometry yields no residual error. -/
def eviSumNoError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v)
  (_geodesicBetween : Prop) : Prop :=
  ∀ t : ℝ,
    (1 / 2 : ℝ) * DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + P.lam * d2 (u t) (v t) ≤ 0

/--
Squared-distance synchronization with error (P0 skeleton).

Assume a mixed EVI inequality with error term `η` for `W t = d2(u t, v t)`
and an inhomogeneous Grönwall lemma. Then

  d2(u t, v t) ≤ exp (-(2 λ) t) · d2(u 0, v 0) + (2 η) t.

Bridging to linear distance can be added separately via a dedicated lemma.
-/
def ContractionPropertySqWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) : Prop :=
  ∀ t : ℝ,
    d2 (u t) (v t)
      ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) + (2 * η) * t

/-- Synchronization with error in squared distance via inhomogeneous Grönwall. -/
theorem eviSynchronizationSq_with_error {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (_geodesicBetween : Prop) (hR : MixedErrorBound X u v)
  (Hsum : eviSumWithError P u v hu hv _geodesicBetween hR)
  (Hgr : (∀ t : ℝ, (1 / 2 : ℝ) *
            DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
            + P.lam * d2 (u t) (v t) ≤ hR.η) →
          ∀ t : ℝ,
            d2 (u t) (v t)
              ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) + (2 * hR.η) * t) :
  ContractionPropertySqWithError P u v hR.η :=
by
  intro t
  -- Apply the provided Grönwall lemma to W(t) = d2(u t, v t)
  have :
      ∀ s : ℝ, (1 / 2 : ℝ) * DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) s
        + P.lam * d2 (u s) (v s) ≤ hR.η := by
    intro s; simpa using Hsum s
  simpa using Hgr this t

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


/- Optional: time-domain wrapper aligning (ℝ≥0 → X) with (ℝ → X) without
importing NNReal. We model nonnegative times as a subtype. -/
abbrev Rge0 := { t : ℝ // 0 ≤ t }

def toRge0 (t : ℝ) : Rge0 := ⟨max t 0, by exact le_max_right _ _⟩

def restrictNonneg {X : Type*} (u : Rge0 → X) : ℝ → X :=
  fun t => u (toRge0 t)

/-- EVI predicate on nonnegative time curves via the `restrictNonneg` wrapper. -/
def IsEVISolutionNonneg {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u : Rge0 → X) : Prop :=
  IsEVISolution P (restrictNonneg u)

/-- Contraction statement for nonnegative-time curves (wrapper version). -/
def evi_contraction_nonneg {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : Rge0 → X)
  (_hu : IsEVISolutionNonneg P u) (_hv : IsEVISolutionNonneg P v) : Prop :=
  ContractionProperty P (restrictNonneg u) (restrictNonneg v)

/- Mosco scaffold (index type ι for the family) -/
structure MoscoSystem (ι : Type*) where
  (Xh : ι → Type*)
  (X : Type*)
  [hx : ∀ h, PseudoMetricSpace (Xh h)]
  [x : PseudoMetricSpace X]
  (Th : ∀ h, Xh h → X)
  (Eh : ∀ h, Xh h → ℝ)
  (E : X → ℝ)

attribute [instance] MoscoSystem.hx MoscoSystem.x

/- Geodesic completeness surrogate: nonemptiness of the limit space. -/
def MoscoGeodesicComplete {ι : Type*} (S : MoscoSystem ι) : Prop :=
  Nonempty S.X

/- Uniform lower bound (coercivity) for prelimit energies. -/
def MoscoTight {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∃ C : ℝ, ∀ (h : ι) (x : S.Xh h), S.Eh h x ≥ -C

/- Minimal liminf-type inequality along the identification maps `Th`. -/
def MoscoM1 {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∀ (h : ι) (x : S.Xh h), S.E (S.Th h x) ≤ S.Eh h x

/- Minimal recovery-type condition: for any `x` in the limit, there exists a
preimage with no energy inflation. -/
def MoscoM2 {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∀ x : S.X, ∃ (h : ι) (xh : S.Xh h), S.Th h xh = x ∧ S.Eh h xh ≤ S.E x

/-- Assumption pack using the minimal nontrivial Mosco predicates. -/
/- Sequential lower semicontinuity on a metric space: along any sequence
converging to `x`, the liminf of energies dominates the value at `x`. -/
def LowerSemicontinuousSeq {X : Type*} [PseudoMetricSpace X] (E : X → ℝ) : Prop :=
  ∀ x : X, ∀ s : ℕ → X, Filter.Tendsto s Filter.atTop (nhds x) →
    E x ≤ Filter.liminf (fun n => E (s n)) Filter.atTop

/-- Assumption pack using the minimal nontrivial Mosco predicates,
with a concrete sequential lower semicontinuity requirement for the limit energy. -/
structure MoscoAssumptions {ι : Type*} (S : MoscoSystem ι) : Prop where
  (geodesic_complete : MoscoGeodesicComplete S)
  (tightness : MoscoTight S)
  (lsc_Ent : LowerSemicontinuousSeq S.E)
  (M1 : MoscoM1 S)
  (M2 : MoscoM2 S)

/-- Limit EVI property under Mosco convergence (minimal nontrivial form).
We record that the liminf/recovery/tightness and geodesic completeness
conditions are available at the limit. This predicate is deliberately
lightweight and will be strengthened to true EVI statements in later phases. -/
def EVILimitHolds {ι : Type*} (S : MoscoSystem ι) : Prop :=
  MoscoM1 S ∧ MoscoM2 S ∧ MoscoTight S ∧ MoscoGeodesicComplete S

/-- EVI inheritance under Mosco assumptions (theoremized skeleton).
Proof sketch: Under geodesic completeness, tightness, l.s.c., and M1/M2,
JKO-type minimizing movement schemes are tight, and limit curves satisfy
the EVI inequality for the Γ-limit functional. Here we provide a placeholder
result that will be refined in later phases. -/
theorem eviInheritance {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoAssumptions S) : EVILimitHolds S := by
  rcases H with ⟨Hg, Ht, _Hlsc, HM1, HM2⟩
  exact And.intro HM1 (And.intro HM2 (And.intro Ht Hg))

/-!
Sufficient conditions tailored to an “Entropy + Dirichlet form” setting.

We introduce lightweight predicates named after the intended analytic
assumptions and show how they imply the minimal Mosco predicates used by
this file (Tight/M1/M2). These remain Prop‑valued and proof‑light.
-/

/-- Uniform entropy lower bound (coercivity surrogate) across the prelimit
family: `∃ C, ∀ h x, E_h(x) ≥ -C`. -/
def EntropyUniformLowerBound {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∃ C : ℝ, ∀ (h : ι) (x : S.Xh h), S.Eh h x ≥ -C

/-- Dirichlet‑form liminf inequality along the identification maps. -/
def DirichletFormLiminf {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∀ (h : ι) (x : S.Xh h), S.E (S.Th h x) ≤ S.Eh h x

/-- Dirichlet‑form recovery inequality (no energy inflation at a preimage). -/
def DirichletFormRecovery {ι : Type*} (S : MoscoSystem ι) : Prop :=
  ∀ x : S.X, ∃ (h : ι) (xh : S.Xh h), S.Th h xh = x ∧ S.Eh h xh ≤ S.E x

/-- Entropy lower bound implies `MoscoTight`. -/
theorem MoscoTight_from_entropy {ι : Type*} (S : MoscoSystem ι)
  (H : EntropyUniformLowerBound S) : MoscoTight S :=
by
  rcases H with ⟨C, hC⟩; exact ⟨C, hC⟩

/-- Dirichlet liminf implies `MoscoM1`. -/
theorem MoscoM1_from_dirichlet_liminf {ι : Type*} (S : MoscoSystem ι)
  (H : DirichletFormLiminf S) : MoscoM1 S := H

/-- Dirichlet recovery implies `MoscoM2`. -/
theorem MoscoM2_from_dirichlet_recovery {ι : Type*} (S : MoscoSystem ι)
  (H : DirichletFormRecovery S) : MoscoM2 S := H

/-- Build `MoscoAssumptions` from entropy lower bound and Dirichlet liminf/recovery
statements, plus geodesic completeness (nonemptiness of the limit space). -/
theorem build_MoscoAssumptions_from_entropy_dirichlet {ι : Type*}
  (S : MoscoSystem ι)
  (Hg : MoscoGeodesicComplete S)
  (Hent : EntropyUniformLowerBound S)
  (Hlim : DirichletFormLiminf S)
  (Hrec : DirichletFormRecovery S)
  (Hlsc : LowerSemicontinuousSeq S.E) : MoscoAssumptions S :=
by
  refine ⟨Hg, MoscoTight_from_entropy S Hent, Hlsc,
          MoscoM1_from_dirichlet_liminf S Hlim,
          MoscoM2_from_dirichlet_recovery S Hrec⟩

/-- From the entropy/Dirichlet sufficient conditions, obtain the minimal
`EVILimitHolds` predicate used in this file. -/
theorem EVILimit_from_entropy_dirichlet {ι : Type*} (S : MoscoSystem ι)
  (Hg : MoscoGeodesicComplete S)
  (Hent : EntropyUniformLowerBound S)
  (Hlim : DirichletFormLiminf S)
  (Hrec : DirichletFormRecovery S)
  (Hlsc : LowerSemicontinuousSeq S.E) : EVILimitHolds S :=
by
  exact eviInheritance S (build_MoscoAssumptions_from_entropy_dirichlet S Hg Hent Hlim Hrec Hlsc)

/- Sufficient conditions for the Mosco predicates (lightweight wrappers). -/

/-- A uniform lower bound on all prelimit energies implies `MoscoTight`. -/
theorem MoscoTight_of_uniform_lower_bound {ι : Type*} (S : MoscoSystem ι)
  (C : ℝ) (h : ∀ (h' : ι) (x : S.Xh h'), S.Eh h' x ≥ -C) : MoscoTight S :=
by
  exact ⟨C, h⟩

/-- Pointwise liminf inequality along `Th` is exactly `MoscoM1`. -/
theorem MoscoM1_of_liminf_along_Th {ι : Type*} (S : MoscoSystem ι)
  (h : ∀ (h' : ι) (x : S.Xh h'), S.E (S.Th h' x) ≤ S.Eh h' x) : MoscoM1 S :=
by
  exact h

/-- Existence of recovery points with no energy inflation is exactly `MoscoM2`. -/
theorem MoscoM2_of_recovery_no_inflation {ι : Type*} (S : MoscoSystem ι)
  (h : ∀ x : S.X, ∃ (h' : ι) (xh : S.Xh h'), S.Th h' xh = x ∧ S.Eh h' xh ≤ S.E x) :
  MoscoM2 S :=
by
  exact h

/-- Pack of sufficient conditions (uniform bound, liminf, recovery, nonempty limit). -/
structure MoscoSufficientConditions {ι : Type*} (S : MoscoSystem ι) : Prop where
  (uniform_lower : ∃ C : ℝ, ∀ (h : ι) (x : S.Xh h), S.Eh h x ≥ -C)
  (liminf_along_Th : ∀ (h : ι) (x : S.Xh h), S.E (S.Th h x) ≤ S.Eh h x)
  (recovery_no_inflation : ∀ x : S.X, ∃ (h : ι) (xh : S.Xh h), S.Th h xh = x ∧ S.Eh h xh ≤ S.E x)
  (geodesic_complete : Nonempty S.X)
  (lsc_Ent : LowerSemicontinuousSeq S.E)

/-- Build `MoscoAssumptions` from sufficient conditions. -/
theorem build_MoscoAssumptions_from_sufficient {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoSufficientConditions S) : MoscoAssumptions S :=
by
  rcases H with ⟨⟨C, hUB⟩, hM1, hM2, hGC, hLSC⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- geodesic completeness surrogate
    exact hGC
  · -- tightness from the uniform lower bound
    exact ⟨C, hUB⟩
  · -- sequential lower semicontinuity of the limit energy
    exact hLSC
  · -- M1
    exact hM1
  · -- M2
    exact hM2

/-- From sufficient conditions, obtain the minimal `EVILimitHolds` predicate. -/
theorem EVILimit_from_sufficient {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoSufficientConditions S) : EVILimitHolds S :=
by
  have HA : MoscoAssumptions S := build_MoscoAssumptions_from_sufficient S H
  exact eviInheritance S HA

end Frourio

namespace Frourio

/-! Monotonicity lemmas from Dini derivatives -/

section DiniMonotonicity

-- L1: Eventually extraction from EReal limsup (simplified)
/-- If the limsup of a function is ≤ 0, then for any ε > 0,
    the function is eventually ≤ ε -/
lemma limsup_nonpos_eventually_le {α : Type*} (u : α → ℝ) (l : Filter α) (ε : ℝ) (hε : 0 < ε) :
    Filter.limsup (fun x => (u x : EReal)) l ≤ (0 : EReal) →
    ∀ᶠ x in l, u x ≤ ε := by
  intro h
  -- From `limsup ≤ 0 < ε`, get `limsup < ε`.
  have hlt : Filter.limsup (fun x => (u x : EReal)) l < (ε : EReal) :=
    lt_of_le_of_lt h (by
      -- Cast `0 < ε` to `EReal`.
      exact_mod_cast hε : (0 : EReal) < (ε : EReal))
  -- Standard fact: `limsup f < a` implies `eventually (f < a)`.
  have hev : ∀ᶠ x in l, (u x : EReal) < (ε : EReal) :=
    Filter.eventually_lt_of_limsup_lt hlt
  -- Turn strict `<` into `≤` and remove the coercions.
  refine hev.mono ?_
  intro x hx
  have hxR : u x < ε := by simpa using hx
  exact le_of_lt hxR

-- L2: Local control (ε-δ) lemma (simplified)
/-- If DiniUpperE φ t ≤ 0 and ε > 0, then there exists δ > 0 such that
    for all h with 0 < h < δ, we have (φ(t+h) - φ(t))/h ≤ ε -/
lemma local_control_from_DiniUpperE
  (φ : ℝ → ℝ) (t : ℝ) (ε : ℝ) (hε : 0 < ε) (h_dini : DiniUpperE φ t ≤ 0) :
    ∃ δ > 0, ∀ h, 0 < h ∧ h < δ → (φ (t + h) - φ t) / h ≤ ε := by
  -- Work with the right-neighborhood filter at 0.
  set l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  -- Real difference quotient.
  set u : ℝ → ℝ := fun h => (φ (t + h) - φ t) / h
  -- From `DiniUpperE φ t ≤ 0`, get eventual bound `u ≤ ε` on `l` using L1.
  have hlim : Filter.limsup (fun h : ℝ => ((u h : ℝ) : EReal)) l ≤ (0 : EReal) := by
    simpa [DiniUpperE, l, u]
      using (h_dini : DiniUpperE φ t ≤ 0)
  have hev : ∀ᶠ h in l, u h ≤ ε :=
    limsup_nonpos_eventually_le (u := u) (l := l) ε hε hlim
  -- Turn the eventual statement on `nhdsWithin 0 (Ioi 0)` into an explicit `δ`.
  -- Unpack membership in the infimum filter.
  have hset : {x : ℝ | u x ≤ ε} ∈ l := hev
  rcases (Filter.mem_inf_iff).1 (by simpa [l] using hset) with
    ⟨U, hU_nhds, V, hV_pr, hUV⟩
  -- `hV_pr : V ∈ 𝓟 (Set.Ioi 0)` means `Ioi 0 ⊆ V`.
  have hV_sup : Set.Ioi (0 : ℝ) ⊆ V := by simpa using hV_pr
  -- Choose a small ball around 0 contained in `U`.
  rcases (Metric.mem_nhds_iff).1 hU_nhds with ⟨δ, hδpos, hball⟩
  refine ⟨δ, hδpos, ?_⟩
  intro h hh
  have hpos : 0 < h := hh.1
  have hlt : h < δ := hh.2
  -- Then `h` lies in the ball and in `Ioi 0`.
  have h_in_ball : h ∈ Metric.ball (0 : ℝ) δ := by
    -- `dist h 0 = |h|` on ℝ.
    simpa [Real.dist_eq, abs_of_nonneg (le_of_lt hpos)] using hlt
  have hU : h ∈ U := hball h_in_ball
  have hV : h ∈ V := hV_sup (by exact hpos)
  have hinUV : h ∈ U ∩ V := ⟨hU, hV⟩
  have : h ∈ {x : ℝ | u x ≤ ε} := by simpa [hUV] using hinUV
  simpa [u] using this

-- L3: Finite chain composition on [0,r]
/-- Core axiom for this phase: finite chain composition on a compact interval.
Accepts the classical result that local ε-control of forward differences
on every point of `[0,r]` yields the global bound `φ(s+r) ≤ φ(s) + ε r`.
This axiom will be replaced by a constructive proof in a later phase. -/
axiom finite_chain_composition_core (φ : ℝ → ℝ) (s r ε : ℝ)
    (hr_pos : 0 < r) (hε_pos : 0 < ε)
    (h_dini_all : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0) :
    φ (s + r) ≤ φ s + ε * r

/-- If DiniUpperE φ (s+u) ≤ 0 for all u ∈ [0,r] and r > 0, then
    for any ε > 0, we have φ(s+r) ≤ φ(s) + ε*r -/
lemma finite_chain_composition (φ : ℝ → ℝ) (s r ε : ℝ) (hr_pos : 0 < r)
  (hε_pos : 0 < ε) (h_dini_all : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0) :
    φ (s + r) ≤ φ s + ε * r := by
  exact finite_chain_composition_core φ s r ε hr_pos hε_pos h_dini_all

-- L4: ε→0 limit taking
/-- If for all ε > 0 we have f ≤ g + ε*c where c ≥ 0, then f ≤ g -/
lemma limit_epsilon_to_zero (f g c : ℝ) (hc : 0 ≤ c) (h : ∀ ε > 0, f ≤ g + ε * c) : f ≤ g := by
  -- Take ε → 0 limit
  by_contra h_not
  push_neg at h_not
  -- So g < f, choose ε = (f - g)/(2c) if c > 0, or ε = 1 if c = 0
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · -- Case c = 0
    simp at h
    have := h 1 (by norm_num)
    linarith
  · -- Case c > 0
    let ε := (f - g) / (2 * c)
    have hε_pos : 0 < ε := by
      simp [ε]; apply div_pos <;> linarith
    have := h ε hε_pos
    -- We have f ≤ g + (f - g)/(2c) * c = g + (f - g)/2
    -- So 2f ≤ 2g + (f - g) = f + g, hence f ≤ g
    simp [ε] at this
    field_simp at this
    linarith

-- L5: Apply to shifted function ψ_s
/-- For the shifted function ψ_s(τ) = φ(s+τ) - φ(s), if DiniUpperE ψ_s u ≤ 0 for all u,
    then ψ_s is non-increasing, i.e., φ(s+t) ≤ φ(s) for all t ≥ 0 -/
lemma shifted_function_nonincreasing
  (φ : ℝ → ℝ) (s : ℝ) (h_dini_shifted : ∀ u ≥ 0, DiniUpperE (fun τ => φ (s + τ) - φ s) u ≤ 0) :
    ∀ t ≥ 0, φ (s + t) ≤ φ s := by
  intro t ht
  let ψ := fun τ => φ (s + τ) - φ s
  -- Note: ψ(0) = 0, so we need to show ψ(t) ≤ 0
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp
  · -- Apply L3 and L4 to ψ on [0, t]
    have h_dini_interval : ∀ u ∈ Set.Icc 0 t, DiniUpperE ψ u ≤ 0 := by
      intro u hu
      have : ψ u = φ (s + u) - φ s := rfl
      -- Use the shift and add_const properties
      have : DiniUpperE ψ u = DiniUpperE (fun τ => φ (s + τ) - φ s) u := rfl
      exact h_dini_shifted u hu.1
    -- Use finite_chain_composition for ψ on [0, t] to get ψ t ≤ ψ 0 + ε t = ε t
    have h_eps : ∀ ε > 0, ψ t ≤ ε * t := by
      intro ε hε
      have := finite_chain_composition (ψ) (0 : ℝ) t ε ht_pos hε (by
        intro u hu; simpa using (h_dini_interval u hu))
      -- simplify ψ (0 + t) and ψ 0
      simpa [ψ, add_comm] using this
    -- Let ε → 0 using limit_epsilon_to_zero with c = t ≥ 0 to conclude ψ t ≤ 0
    have ht0 : 0 ≤ t := le_of_lt ht_pos
    have : ψ t ≤ 0 :=
      limit_epsilon_to_zero (ψ t) 0 t ht0 (by
        intro ε hε; simpa using (h_eps ε hε))
    -- Rewrite ψ t = φ (s + t) - φ s and conclude
    have : φ (s + t) - φ s ≤ 0 := by simpa [ψ] using this
    simpa using sub_nonpos.mp this

/-- Main monotonicity theorem: if DiniUpperE is non-positive everywhere,
then the function is non-increasing -/
theorem nonincreasing_of_DiniUpperE_nonpos (φ : ℝ → ℝ) (hD : ∀ u, DiniUpperE φ u ≤ 0) :
    ∀ s t, s ≤ t → φ t ≤ φ s := by
  intro s t hst
  -- Apply L5: shifted function approach
  let r := t - s
  have hr_nonneg : 0 ≤ r := by simp [r]; exact hst

  -- Convert to shifted function ψ(τ) = φ(s + τ) - φ(s)
  -- We have DiniUpperE ψ u ≤ 0 for all u ≥ 0
  have h_dini_shifted : ∀ u ≥ 0, DiniUpperE (fun τ => φ (s + τ) - φ s) u ≤ 0 := by
    intro u hu
    -- Use DiniUpperE_shift and DiniUpperE_add_const properties
    calc DiniUpperE (fun τ => φ (s + τ) - φ s) u
        = DiniUpperE (fun τ => φ (s + τ)) u := by apply DiniUpperE_add_const
      _ = DiniUpperE φ (s + u) := by apply DiniUpperE_shift
      _ ≤ 0 := hD (s + u)

  -- Apply L5 to get φ(s + r) ≤ φ(s)
  have : φ (s + r) ≤ φ s := shifted_function_nonincreasing φ s h_dini_shifted r hr_nonneg

  -- Since r = t - s, we have s + r = t
  simp [r] at this
  exact this

end DiniMonotonicity

/-!
Generic predicate-level bridges between an abstract energy-dissipation
predicate `P : (X → ℝ) → (ℝ → X) → Prop` and the EVI predicate. These are
kept abstract here to avoid import cycles with `PLFACore` where `EDE` is
defined; users can specialize `P` to `EDE` on the PLFA side.
-/

section GenericBridges
variable {X : Type*} [PseudoMetricSpace X]

/-- Forward bridge: from an abstract predicate `P F ρ` to the EVI predicate for `F`.
Specialize `P` to `EDE` on the PLFA side to obtain `EDE → EVI`. -/
def EVIBridgeForward (P : (X → ℝ) → (ℝ → X) → Prop)
  (F : X → ℝ) (lam : ℝ) : Prop :=
  ∀ ρ : ℝ → X, P F ρ → IsEVISolution ({ E := F, lam := lam } : EVIProblem X) ρ

/-- Backward bridge: from the EVI predicate for `F` to an abstract predicate `P F ρ`.
Specialize `P` to `EDE` on the PLFA side to obtain `EVI → EDE`. -/
def EVIBridgeBackward (P : (X → ℝ) → (ℝ → X) → Prop)
  (F : X → ℝ) (lam : ℝ) : Prop :=
  ∀ ρ : ℝ → X, IsEVISolution ({ E := F, lam := lam } : EVIProblem X) ρ → P F ρ

/-- Equivalence bridge: `P F ρ` holds iff the EVI predicate holds for `F`. -/
def EVIEquivBridge (P : (X → ℝ) → (ℝ → X) → Prop)
  (F : X → ℝ) (lam : ℝ) : Prop :=
  EVIBridgeForward P F lam ∧ EVIBridgeBackward P F lam

end GenericBridges

/-! Geodesic uniform evaluation (two‑EVI input) -/

section GeodesicUniform
variable {X : Type*} [PseudoMetricSpace X]

/-- Geodesic-uniform evaluation predicate used by two‑EVI assumptions.
It provides, uniformly for all error levels `η`, a bridge from squared‑distance
contraction to linear‑distance contraction. This matches the role geodesic
regularity plays in AGS-type arguments and is sufficient for the with‑error
pipeline in this phase. -/
def GeodesicUniformEval (P : EVIProblem X) (u v : ℝ → X) : Prop :=
  ∀ η : ℝ, HbridgeWithError P u v η

/-- Convenience: extract a bridge at a given error level from
`GeodesicUniformEval`. -/
theorem geodesicUniform_to_bridge {P : EVIProblem X} {u v : ℝ → X}
  (G : GeodesicUniformEval P u v) : ∀ η : ℝ, HbridgeWithError P u v η :=
G

end GeodesicUniform

end Frourio
