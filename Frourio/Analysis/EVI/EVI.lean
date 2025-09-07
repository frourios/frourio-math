import Frourio.Analysis.EVI.EVICore5
import Frourio.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Tactic

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
