import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.LiminfLimsup
import Frourio.Analysis.PLFA.PLFACore0
import Frourio.Analysis.PLFA.PLFACore1
import Frourio.Analysis.EVI.EVI

namespace Frourio

/-!
# EVI → EDE: Regularity‑aware minimal results

This file provides small, provable implications from EVI to EDE under
strong regularity assumptions, removing previous unprovable placeholders.
-/

section EVItoEDE

variable {X : Type*}

/- Constant‑curve case: if ρ is constant, then EDE holds (trivial). -/
theorem evi_to_ede_constant (F : X → ℝ) (x : X)
    (ρ : ℝ → X) (hconst : ∀ t, ρ t = x) :
    EDE F ρ := by
  intro t
  -- F ∘ ρ is constant since ρ is constant
  have : (fun τ => F (ρ τ)) = fun _ => F x := by
    funext τ; simp [hconst τ]
  -- DiniUpperE of a constant is 0
  simp [this, Frourio.DiniUpperE_const]

/- Local constancy around every t implies EDE (strong regularity). -/
theorem evi_to_ede_with_reg (F : X → ℝ) (ρ : ℝ → X)
    (hLocConst : ∀ t : ℝ, ∃ δ > 0, ∀ h, 0 < h ∧ h < δ → ρ (t + h) = ρ t) :
    EDE F ρ := by
  intro t
  rcases hLocConst t with ⟨δ, hδpos, hconst⟩
  set l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  set u : ℝ → ℝ := fun h => (F (ρ (t + h)) - F (ρ t)) / h
  have hEv : {h : ℝ | u h = 0} ∈ l := by
    -- Neighborhood (0,δ) on the right: use the metric characterization
    have hIoo : Set.Ioo (0 : ℝ) δ ∈ l := by
      -- Use: A ∈ nhdsWithin 0 (Ioi 0) iff ∃ ε>0, ball 0 ε ∩ Ioi 0 ⊆ A
      have hcrit : ∃ ε > 0, Metric.ball (0 : ℝ) ε ∩ Set.Ioi 0 ⊆ Set.Ioo (0 : ℝ) δ := by
        refine ⟨min (δ / 2) (1 : ℝ), ?_, ?_⟩
        · have : 0 < δ / 2 := by linarith
          exact lt_min this (by exact Real.zero_lt_one)
        · intro x hx
          rcases hx with ⟨hball, hxpos⟩
          have : dist x (0 : ℝ) < min (δ / 2) (1 : ℝ) := by simpa [Metric.mem_ball] using hball
          have hx_lt_half : dist x (0 : ℝ) < δ / 2 := lt_of_lt_of_le this (min_le_left _ _)
          have habs : |x| < δ / 2 := by simpa [Real.dist_eq] using hx_lt_half
          have hx_pos : 0 < x := by simpa using hxpos
          have hx_lt_δ : x < δ := by
            have : x ≤ |x| := le_abs_self x
            linarith
          exact ⟨hx_pos, hx_lt_δ⟩
      have : Set.Ioo (0 : ℝ) δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        (Metric.mem_nhdsWithin_iff).2 hcrit
      simpa [l] using this
    -- On (0,δ), u h = 0
    refine Filter.mem_of_superset hIoo ?subset
    intro h hh
    rcases hh with ⟨hpos, hlt⟩
    have hc := hconst h ⟨hpos, hlt⟩
    simp [u, hc]
  -- Hence limsup is 0 on the right neighborhood, giving DiniUpperE ≤ 0
  -- From eventual equality to 0, get an eventual ≤ 0 bound and conclude limsup ≤ 0
  have hEv0 : ∀ᶠ h in l, ((u h : ℝ) : EReal) ≤ (0 : EReal) := by
    have hEq0 : ∀ᶠ h in l, u h = 0 := hEv
    exact hEq0.mono (by intro h hh; simp [hh])
  have hbound :
      Filter.limsup (fun h : ℝ => ((u h : ℝ) : EReal)) l ≤ (0 : EReal) :=
    Filter.limsup_le_of_le (h := hEv0)
  -- Identify the goal with the same limsup
  change Filter.limsup (fun h : ℝ => ((u h : ℝ) : EReal)) l ≤ (0 : EReal)
  exact hbound

end EVItoEDE

end Frourio
