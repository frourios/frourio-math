import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.LiminfLimsup
import Frourio.Analysis.PLFA.PLFACore0
import Frourio.Analysis.PLFA.PLFACore1
import Frourio.Analysis.EVI.EVI
import Frourio.Analysis.EVI.EVICore0
import Frourio.Analysis.EVI.EVICore6Sub2
import Frourio.Analysis.MinimizingMovement

namespace Frourio

section SupportingLemmas

variable {X : Type*} [PseudoMetricSpace X]

/-- On the right neighborhood filter `nhdsWithin 0 (Ioi 0)`, if `u ≤ c` eventually
    and `u` is eventually bounded from both sides, then `limsup u ≤ c` (real version).
    This follows the pattern from DiniUpper_eq_toReal_of_finite but for general functions. -/
lemma limsup_le_of_eventually_le_right {u : ℝ → ℝ} {c : ℝ} :
    (∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ c) →
    (∃ M : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ M) →
    (∃ m : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), m ≤ u h) →
    Filter.limsup u (nhdsWithin 0 (Set.Ioi 0)) ≤ c := by
  intro hev hub hlb
  -- The standard approach: if eventually (u ≤ c), then limsup u ≤ c
  -- This is a fundamental property of limsup, but we need to handle coboundedness

  -- Apply the standard limsup bound: if eventually (u ≤ c), then limsup u ≤ c
  -- We need both upper and lower bounds for coboundedness
  obtain ⟨M, hM⟩ := hub
  obtain ⟨m, hm⟩ := hlb
  have h_cobdd : Filter.IsCoboundedUnder (· ≤ ·) (nhdsWithin 0 (Set.Ioi 0)) u := by
    -- Use the lower bound for coboundedness (co-bounded from below)
    exact Filter.isCoboundedUnder_le_of_eventually_le
      (l := nhdsWithin 0 (Set.Ioi 0)) (f := u) (x := m) hm
  exact Filter.limsup_le_of_le (h := hev) (hf := h_cobdd)

/-- General right-filter bridge: if u is eventually bounded from both sides
    and eventually ≤ c, then its real limsup ≤ c.
    This generalizes the pattern from DiniUpper_eq_toReal_of_finite. -/
lemma right_filter_limsup_le_of_bounded {u : ℝ → ℝ} {c : ℝ}
    (hub : ∃ M : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ M)
    (hlb : ∃ m : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), m ≤ u h)
    (hbound : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ c) :
    Filter.limsup u (nhdsWithin 0 (Set.Ioi 0)) ≤ c :=
  limsup_le_of_eventually_le_right hbound hub hlb

/-- Simplified version when the eventual upper bound c also serves as a global upper bound -/
lemma right_filter_limsup_le_simple {u : ℝ → ℝ} {c : ℝ}
    (hlb : ∃ m : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), m ≤ u h)
    (hbound : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ c) :
    Filter.limsup u (nhdsWithin 0 (Set.Ioi 0)) ≤ c :=
  right_filter_limsup_le_of_bounded ⟨c, hbound⟩ hlb hbound

/-- Helper lemma for DiniUpper bound: if quotients are bounded from both sides,
    DiniUpper is bounded -/
lemma dini_upper_le_of_quotient_bounded {f : ℝ → ℝ} {t c m : ℝ}
    (hub : ∀ h ∈ Set.Ioo (0 : ℝ) 1, (f (t + h) - f t) / h ≤ c)
    (hlb : ∀ h ∈ Set.Ioo (0 : ℝ) 1, m ≤ (f (t + h) - f t) / h) :
    DiniUpper f t ≤ c := by
  -- Work with the right-neighborhood filter at 0.
  dsimp [DiniUpper]
  set l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  haveI : Filter.NeBot l := by
    simpa [l] using (nhdsWithin_Ioi_neBot (α := ℝ) (a := 0) (b := 0) le_rfl)
  -- Show that (0,1) is a neighborhood of 0 within (0,∞).
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ l := by
    -- Using the metric characterization of nhdsWithin.
    have hcrit : ∃ ε > 0,
        Metric.ball (0 : ℝ) ε ∩ Set.Ioi 0 ⊆ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
      intro x hx; rcases hx with ⟨hball, hxpos⟩
      have : dist x (0 : ℝ) < (1 : ℝ) / 2 := by simpa [Metric.mem_ball] using hball
      have habs : |x| < (1 : ℝ) / 2 := by simpa [Real.dist_eq] using this
      have hx_pos : 0 < x := by simpa using hxpos
      have hx_lt_one : x < 1 := by
        have hx_le_abs : x ≤ |x| := le_abs_self x
        have : |x| < 1 := lt_trans habs (by norm_num)
        exact lt_of_le_of_lt hx_le_abs this
      exact ⟨hx_pos, hx_lt_one⟩
    have : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      (Metric.mem_nhdsWithin_iff).2 hcrit
    simpa [l] using this
  -- From the hypotheses, derive eventual bounds on the difference quotient.
  have hev_ub : ∀ᶠ h₀ in l, (f (t + h₀) - f t) / h₀ ≤ c :=
    Filter.mem_of_superset hIoo (by
      intro h₀ hh; exact hub h₀ (by simpa using hh))
  have hev_lb : ∀ᶠ h₀ in l, m ≤ (f (t + h₀) - f t) / h₀ :=
    Filter.mem_of_superset hIoo (by
      intro h₀ hh; exact hlb h₀ (by simpa using hh))

  -- Conclude via the helper lemma on the right-neighborhood filter.
  -- We now have the required two-sided boundedness
  have hub_ex : ∃ M : ℝ, ∀ᶠ h₀ in l, (f (t + h₀) - f t) / h₀ ≤ M := ⟨c, hev_ub⟩
  have hlb_ex : ∃ m_ex : ℝ, ∀ᶠ h₀ in l, m_ex ≤ (f (t + h₀) - f t) / h₀ := ⟨m, hev_lb⟩
  exact limsup_le_of_eventually_le_right hev_ub hub_ex hlb_ex

/-- Distance squared along a curve has controlled Dini derivative -/
lemma dini_upper_distance_squared (ρ : ℝ → X) (v : X) (t : ℝ)
    (hLipschitz : ∃ L > 0, ∀ s₁ s₂, |s₁ - s₂| < 1 → dist (ρ s₁) (ρ s₂) ≤ L * |s₁ - s₂|) :
    ∃ C : ℝ, DiniUpper (fun τ => d2 (ρ τ) v) t ≤ C := by
  -- Extract Lipschitz constant
  obtain ⟨L, hL_pos, hLip⟩ := hLipschitz

  -- We'll show that DiniUpper(d²(ρ(·), v)) ≤ 2L·dist(ρ(t), v)
  -- The key is that for small h > 0:
  -- d²(ρ(t+h), v) - d²(ρ(t), v) = dist²(ρ(t+h), v) - dist²(ρ(t), v)
  -- = (dist(ρ(t+h), v) - dist(ρ(t), v))·(dist(ρ(t+h), v) + dist(ρ(t), v))

  use 2 * L * dist (ρ t) v + L^2

  -- The difference quotient is:
  -- [d²(ρ(t+h), v) - d²(ρ(t), v)]/h

  -- Using the factorization a² - b² = (a-b)(a+b):
  have h_factor : ∀ h > 0, h < 1 →
      (d2 (ρ (t + h)) v - d2 (ρ t) v) / h =
      ((dist (ρ (t + h)) v - dist (ρ t) v) * (dist (ρ (t + h)) v + dist (ρ t) v)) / h := by
    intro h hpos hsmall
    unfold d2
    rw [sq_sub_sq, mul_comm]

  -- The reverse triangle inequality gives:
  -- |dist(ρ(t+h), v) - dist(ρ(t), v)| ≤ dist(ρ(t+h), ρ(t)) ≤ L·h
  have h_dist_diff : ∀ h > 0, h < 1 →
      |dist (ρ (t + h)) v - dist (ρ t) v| ≤ L * h := by
    intro h hpos hsmall
    -- Apply reverse triangle inequality: |dist(x,z) - dist(y,z)| ≤ dist(x,y)
    have h_tri : |dist (ρ (t + h)) v - dist (ρ t) v| ≤ dist (ρ (t + h)) (ρ t) :=
      abs_dist_sub_le (ρ (t + h)) (ρ t) v
    -- Then bound dist(ρ(t+h), ρ(t))
    have h_bound := hLip (t + h) t
    have h_arg : |(t + h) - t| = h := by simp [abs_of_pos hpos]
    rw [h_arg] at h_bound
    have h_lip := h_bound hsmall
    -- Combine
    exact le_trans h_tri h_lip

  -- Therefore the difference quotient is bounded by:
  -- L·(dist(ρ(t+h), v) + dist(ρ(t), v))
  -- ≤ L·(dist(ρ(t), v) + dist(ρ(t), ρ(t+h)) + dist(ρ(t), v))
  -- ≤ L·(2·dist(ρ(t), v) + L·h)

  -- Bound the difference quotient
  have h_quotient_bound : ∀ h > 0, h < 1 →
      (d2 (ρ (t + h)) v - d2 (ρ t) v) / h ≤ 2 * L * dist (ρ t) v + L^2 := by
    intro h hpos hsmall
    -- Use the factorization d²(x,y) - d²(z,y) = (dist(x,y) - dist(z,y))·(dist(x,y) + dist(z,y))
    unfold d2
    rw [sq_sub_sq, mul_comm, mul_div_assoc]

    -- Bound each factor
    have h1 := h_dist_diff h hpos hsmall
    have h_diff_bound : dist (ρ (t + h)) v - dist (ρ t) v ≤ L * h :=
      le_trans (le_abs_self _) h1

    have h_sum : dist (ρ (t + h)) v + dist (ρ t) v ≤ 2 * dist (ρ t) v + L * h := by
      have : dist (ρ (t + h)) v ≤ dist (ρ (t + h)) (ρ t) + dist (ρ t) v := dist_triangle _ _ _
      have h_rho : dist (ρ (t + h)) (ρ t) ≤ L * h := by
        have := hLip (t + h) t
        simp [abs_of_pos hpos] at this
        exact this hsmall
      linarith

    -- Combine
    calc (dist (ρ (t + h)) v - dist (ρ t) v) * ((dist (ρ (t + h)) v + dist (ρ t) v) / h)
        ≤ (L * h) * ((2 * dist (ρ t) v + L * h) / h) := by
          apply mul_le_mul _ _ _ _
          · exact h_diff_bound
          · exact div_le_div_of_nonneg_right h_sum (le_of_lt hpos)
          · apply div_nonneg
            · apply add_nonneg
              · exact dist_nonneg
              · exact dist_nonneg
            · exact le_of_lt hpos
          · exact mul_nonneg (le_of_lt hL_pos) (le_of_lt hpos)
      _ = L * (2 * dist (ρ t) v + L * h) := by
          -- We need to show:
          -- L * h * ((2 * dist (ρ t) v + L * h) / h) = L * (2 * dist (ρ t) v + L * h)
          -- First rewrite as (L * h) * ((2 * dist (ρ t) v + L * h) / h)
          rw [mul_assoc L h]
          -- Now we have L * (h * ((2 * dist (ρ t) v + L * h) / h))
          congr 1
          -- Need to show: h * ((2 * dist (ρ t) v + L * h) / h) = 2 * dist (ρ t) v + L * h
          rw [mul_div_assoc']
          -- Now we need: (h * (2 * dist (ρ t) v + L * h)) / h = 2 * dist (ρ t) v + L * h
          rw [mul_comm h]
          -- Now: ((2 * dist (ρ t) v + L * h) * h) / h = 2 * dist (ρ t) v + L * h
          rw [mul_div_assoc, div_self (ne_of_gt hpos), mul_one]
      _ = 2 * L * dist (ρ t) v + L^2 * h := by ring
      _ ≤ 2 * L * dist (ρ t) v + L^2 := by
          apply add_le_add_left
          exact mul_le_of_le_one_right (sq_nonneg L) (le_of_lt hsmall)

  -- DiniUpper f t = limsup_{h → 0⁺} (f(t+h) - f(t))/h
  -- We've shown: ∀ h ∈ (0,1), (d²(ρ(t+h), v) - d²(ρ(t), v))/h ≤ 2L·dist(ρ(t), v) + L²

  -- Apply our helper lemma to bound DiniUpper
  -- We have shown that for all h ∈ (0, 1), the quotient ≤ 2L·dist(ρ(t), v) + L²
  -- For the lower bound, note that the distance squared quotient can be negative
  -- (when moving closer to v), but it's bounded below by a Lipschitz-type estimate
  have h_quotient_lower : ∀ h > 0, h < 1 →
      (d2 (ρ (t + h)) v - d2 (ρ t) v) / h ≥ -(2 * L * dist (ρ t) v + L^2) := by
    intro h hpos hsmall
    -- The reverse triangle inequality also gives: dist(ρ(t+h), v) - dist(ρ(t), v) ≥ -L*h
    -- So the quotient is bounded below by -L*(2*dist(ρ(t), v) + L*h)
    -- Similar analysis as the upper bound, but with reversed inequalities
    have h_diff_lower : dist (ρ (t + h)) v - dist (ρ t) v ≥ -(L * h) := by
      have h1 := h_dist_diff h hpos hsmall
      -- |a - b| ≤ c implies a - b ≥ -c and a - b ≤ c
      have h_abs : |dist (ρ (t + h)) v - dist (ρ t) v| ≤ L * h := h1
      rw [ge_iff_le, neg_le_iff_add_nonneg]
      have := abs_le.1 h_abs
      linarith [this.1]
    -- The sum bound still applies
    have h_sum_bound : dist (ρ (t + h)) v + dist (ρ t) v ≤ 2 * dist (ρ t) v + L * h := by
      have : dist (ρ (t + h)) v ≤ dist (ρ (t + h)) (ρ t) + dist (ρ t) v := dist_triangle _ _ _
      have h_rho : dist (ρ (t + h)) (ρ t) ≤ L * h := by
        have := hLip (t + h) t
        simp [abs_of_pos hpos] at this
        exact this hsmall
      linarith
    -- Now bound the product: (negative term) * (positive term) ≥ negative result
    unfold d2
    rw [sq_sub_sq, mul_comm, mul_div_assoc]
    -- We have: (dist(...) - dist(...)) * (dist(...) + dist(...)) / h
    -- ≥ (-L*h) * (2*dist(ρ(t), v) + L*h) / h (since the sum is positive)
    -- = -L * (2*dist(ρ(t), v) + L*h) = -(2*L*dist(ρ(t), v) + L²*h)
    -- ≥ -(2*L*dist(ρ(t), v) + L²) (since h ≤ 1)
    have h_pos_sum : 0 ≤ dist (ρ (t + h)) v + dist (ρ t) v := add_nonneg dist_nonneg dist_nonneg
    calc (dist (ρ (t + h)) v - dist (ρ t) v) * ((dist (ρ (t + h)) v + dist (ρ t) v) / h)
        ≥ (-(L * h)) * ((dist (ρ (t + h)) v + dist (ρ t) v) / h) := by
          apply mul_le_mul_of_nonneg_right h_diff_lower
          exact div_nonneg h_pos_sum (le_of_lt hpos)
      _ ≥ (-(L * h)) * ((2 * dist (ρ t) v + L * h) / h) := by
          apply mul_le_mul_of_nonpos_left _
            (neg_nonpos.2 (mul_nonneg (le_of_lt hL_pos) (le_of_lt hpos)))
          exact div_le_div_of_nonneg_right h_sum_bound (le_of_lt hpos)
      _ = -(L * (2 * dist (ρ t) v + L * h)) := by
          rw [neg_mul]
          congr 1
          -- Simplify: L * h * ((2 * dist (ρ t) v + L * h) / h) = L * (2 * dist (ρ t) v + L * h)
          field_simp [ne_of_gt hpos]
          ring
      _ = -(2 * L * dist (ρ t) v + L^2 * h) := by ring
      _ ≥ -(2 * L * dist (ρ t) v + L^2) := by
          apply neg_le_neg
          apply add_le_add_left
          exact mul_le_of_le_one_right (sq_nonneg L) (le_of_lt hsmall)

  apply dini_upper_le_of_quotient_bounded
  · intro h hh
    exact h_quotient_bound h hh.1 hh.2
  · intro h hh
    exact h_quotient_lower h hh.1 hh.2

/-- Young's inequality for the EVI proof -/
lemma young_inequality_evi (a b ε : ℝ) (hε : 0 < ε) :
    a * b ≤ ε * a^2 / 2 + b^2 / (2 * ε) := by
  -- Young's inequality: ab ≤ εa²/2 + b²/(2ε)
  -- Proof: Complete the square for (√ε·a - b/√ε)² ≥ 0
  have sqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε

  have h_sq : 0 ≤ (Real.sqrt ε * a - b / Real.sqrt ε)^2 := sq_nonneg _

  -- Expand (x - y)² = x² - 2xy + y²
  have h_expand : (Real.sqrt ε * a - b / Real.sqrt ε)^2 =
      ε * a^2 - 2 * a * b + b^2 / ε := by
    calc (Real.sqrt ε * a - b / Real.sqrt ε)^2
        = (Real.sqrt ε * a)^2 - 2 * (Real.sqrt ε * a) * (b / Real.sqrt ε) +
          (b / Real.sqrt ε)^2 := by ring
      _ = ε * a^2 - 2 * (Real.sqrt ε * a) * (b / Real.sqrt ε) + b^2 / ε := by
          simp only [mul_pow, div_pow, Real.sq_sqrt (le_of_lt hε)]
      _ = ε * a^2 - 2 * a * b + b^2 / ε := by
          congr 2
          field_simp [sqrt_pos.ne']
          ring

  -- From 0 ≤ ε * a^2 - 2 * a * b + b^2 / ε
  -- We get: 2 * a * b ≤ ε * a^2 + b^2 / ε
  rw [h_expand] at h_sq
  have h_ineq : 2 * a * b ≤ ε * a^2 + b^2 / ε := by linarith [h_sq]

  -- Hence: a * b ≤ ε * a^2 / 2 + b^2 / (2 * ε)
  calc a * b
      = (2 * a * b) / 2 := by ring
    _ ≤ (ε * a^2 + b^2 / ε) / 2 := by
        apply div_le_div_of_nonneg_right h_ineq
        norm_num
    _ = ε * a^2 / 2 + b^2 / ε / 2 := by ring
    _ = ε * a^2 / 2 + b^2 / (2 * ε) := by ring

/-- Geodesic interpolation estimate -/
lemma geodesic_interpolation_estimate {G : GeodesicStructure X} (F : X → ℝ) (lamEff : ℝ)
    (hSemiconvex : GeodesicSemiconvex G F lamEff)
    (x y : X) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    F (G.γ x y t) ≤ (1 - t) * F x + t * F y - (lamEff / 2) * t * (1 - t) * (dist x y)^2 := by
  -- This follows directly from the definition of GeodesicSemiconvex
  -- Extract the bounds from the hypothesis
  have h_le : 0 ≤ t ∧ t ≤ 1 := ht

  -- Apply the GeodesicSemiconvex definition directly
  exact hSemiconvex x y t h_le.1 h_le.2

-- Note: DiniUpperE_add_le already exists in EVICore0.lean, so we import and use it directly

/-- Upper semicontinuous function using the quotient-based formulation
    Compatible with the EVI framework from EVICore6Sub2 -/
def UpperSemicontinuous (φ : ℝ → ℝ) : Prop :=
  ∀ s t, s < t → ∀ w ∈ Set.Icc 0 (t - s), ∀ y₀ ∈ Set.Icc 0 (t - s),
    |y₀ - w| < (t - s) / 4 → upper_semicontinuous_at_zero φ s y₀

-- Note: nonincreasing_of_DiniUpperE_nonpos is removed as it's redundant.
-- Use nonincreasing_of_DiniUpperE_nonpos_with_usc directly from EVI.lean

/-- Helper: Sum of USC function and locally Lipschitz continuous function is USC
    The key additional assumption is that for each ε > 0, we can find a neighborhood
    where the Lipschitz constant is bounded by ε/2 -/
lemma upperSemicontinuous_add_continuous {f g : ℝ → ℝ}
    (hf : UpperSemicontinuous f)
    (hg_lip_bound : ∀ x : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ y z, |y - x| < δ → |z - x| < δ →
      |g y - g z| < (ε/2) * |y - z|) :
    UpperSemicontinuous (f + g) := by
  intro s t hst w hw y₀ hy₀ hdist
  -- Use the USC property of f and continuity of g
  have hf_usc := hf s t hst w hw y₀ hy₀ hdist
  intro ε hε

  -- Get bounds from f's USC property with ε/2
  obtain ⟨α_f, hα_f, β_f, hβ_f, hf_bound⟩ := hf_usc (ε/2) (by linarith)

  -- Get the bounded Lipschitz property for g at s + y₀ with bound ε/2
  obtain ⟨δ_g, hδ_g_pos, hg_lip_local⟩ := hg_lip_bound (s + y₀) ε hε

  -- Choose α = min(α_f, δ_g/2) and β = min(β_f, δ_g/2)
  use min α_f (δ_g/2), by simp [hα_f, hδ_g_pos], min β_f (δ_g/2), by simp [hβ_f, hδ_g_pos]

  intro y h hy_near hh_pos hh_small

  -- Split the quotient function for f + g
  have h_split : quotient_function (f + g) s y h =
                 quotient_function f s y h + quotient_function g s y h := by
    unfold quotient_function
    simp only [Pi.add_apply]
    field_simp
    ring

  rw [h_split]

  -- Bound for f from USC
  have hf_contrib : quotient_function f s y h < ε/2 := by
    apply hf_bound
    · exact lt_of_lt_of_le hy_near (min_le_left _ _)
    · exact hh_pos
    · calc h < min β_f (δ_g/2) := hh_small
        _ ≤ β_f := min_le_left _ _

  -- Bound for g using continuity
  have hg_contrib : quotient_function g s y h < ε/2 := by
    unfold quotient_function
    -- We need to bound |g(s + y + h) - g(s + y)|/h
    -- First, both s + y + h and s + y are close to s + y₀
    have h_close1 : dist (s + (y + h)) (s + y₀) < δ_g := by
      rw [Real.dist_eq]
      calc |s + (y + h) - (s + y₀)| = |y + h - y₀| := by ring_nf
        _ = |(y - y₀) + h| := by ring_nf
        _ ≤ |y - y₀| + |h| := abs_add (y - y₀) h
        _ < min α_f (δ_g/2) + min β_f (δ_g/2) := by
            apply add_lt_add
            · exact hy_near
            · rw [abs_of_pos hh_pos]; exact hh_small
        _ ≤ δ_g/2 + δ_g/2 := by
            apply add_le_add
            · exact min_le_right _ _
            · exact min_le_right _ _
        _ = δ_g := by ring

    have h_close2 : dist (s + y) (s + y₀) < δ_g := by
      rw [Real.dist_eq]
      calc |s + y - (s + y₀)| = |y - y₀| := by ring_nf
        _ < min α_f (δ_g/2) := hy_near
        _ ≤ δ_g/2 := min_le_right _ _
        _ < δ_g := by linarith

    -- Apply the bounded Lipschitz property with bound ε/2
    -- Since both points are within δ_g of s + y₀, we can use the Lipschitz bound
    -- First handle the edge case where s + (y + h) = s + y
    -- Since h > 0, we have s + (y + h) ≠ s + y, so we can use the strict Lipschitz bound
    have hg_lip_bound : |g (s + (y + h)) - g (s + y)| < (ε/2) * |s + (y + h) - (s + y)| := by
      apply hg_lip_local
      · rw [Real.dist_eq] at h_close1; exact h_close1
      · rw [Real.dist_eq] at h_close2; exact h_close2

    calc (g (s + (y + h)) - g (s + y)) / h
        ≤ |g (s + (y + h)) - g (s + y)| / h := by
            apply div_le_div_of_nonneg_right (le_abs_self _) (le_of_lt hh_pos)
      _ < ((ε/2) * |s + (y + h) - (s + y)|) / h := by
            apply div_lt_div_of_pos_right hg_lip_bound hh_pos
      _ = ((ε/2) * |h|) / h := by
            congr 2
            ring_nf
      _ = ((ε/2) * h) / h := by rw [abs_of_pos hh_pos]
      _ = ε/2 := by
          field_simp
          ring

  -- Combine the bounds
  calc quotient_function f s y h + quotient_function g s y h
      < ε/2 + ε/2 := add_lt_add hf_contrib hg_contrib
    _ = ε := by ring

/-- EReal version: Limsup is bounded by a constant if the function is eventually bounded -/
lemma ereal_limsup_le_of_eventually_le {α : Type*} {f : α → EReal} {l : Filter α} {C : EReal}
    (h : ∀ᶠ x in l, f x ≤ C) :
    Filter.limsup f l ≤ C := by
  -- For EReal, we need to handle the coboundedness condition
  -- IsCoboundedUnder means there exists a lower bound b such that ∀ᶠ x, b ≤ f x
  have h_cobounded : Filter.IsCoboundedUnder (· ≤ ·) l f := by
    simp only [Filter.IsCoboundedUnder, Filter.IsCobounded]
    use ⊥
    intro a ha
    -- Need to show ⊥ ≤ a for any a that is eventually a lower bound
    exact bot_le
  -- Apply the general limsup_le_of_le theorem
  exact Filter.limsup_le_of_le h_cobounded h

/-- EReal version: Limsup of a constant function equals the constant -/
lemma ereal_limsup_const {α : Type*} {l : Filter α} {C : EReal} [l.NeBot] :
  Filter.limsup (fun _ : α => C) l = C := by simp [Filter.limsup_const]

/-- DiniUpperE of λ times squared distance along a Lipschitz curve -/
lemma DiniUpperE_lam_d2_bound_explicit {X : Type*} [PseudoMetricSpace X]
    (ρ : ℝ → X) (v : X) (t : ℝ) (lam L : ℝ)
    (hL_pos : 0 < L)
    (hL_bound : ∀ s ∈ Set.Ioo (t - 1) (t + 1), dist (ρ s) (ρ t) ≤ L * |s - t|) :
    DiniUpperE (fun τ => lam * d2 (ρ τ) v) t ≤ (|lam| * (2 * L * dist (ρ t) v + L^2) : ℝ) := by
  -- Work on the right-neighborhood filter at 0
  set l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  -- Show that (0,1) is a neighborhood in l to ensure t+h ∈ (t-1,t+1)
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ l := by
    have hcrit : ∃ ε > 0,
        Metric.ball (0 : ℝ) ε ∩ Set.Ioi 0 ⊆ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
      intro x hx; rcases hx with ⟨hball, hxpos⟩
      have : dist x (0 : ℝ) < (1 : ℝ) / 2 := by simpa [Metric.mem_ball] using hball
      have habs : |x| < (1 : ℝ) / 2 := by simpa [Real.dist_eq] using this
      have hx_pos : 0 < x := by simpa using hxpos
      have hx_lt_one : x < 1 := by
        have hx_le_abs : x ≤ |x| := le_abs_self x
        have : |x| < 1 := lt_trans habs (by norm_num)
        exact lt_of_le_of_lt hx_le_abs this
      exact ⟨hx_pos, hx_lt_one⟩
    have : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      (Metric.mem_nhdsWithin_iff).2 hcrit
    simpa [l] using this
  -- Establish the eventual bound on the EReal-valued forward quotient
  have h_ev : ∀ᶠ h in l,
      (((lam * d2 (ρ (t + h)) v - lam * d2 (ρ t) v) / h : ℝ) : EReal)
        ≤ (|lam| * (2 * L * dist (ρ t) v + L^2) : ℝ) := by
    -- Reduce to h ∈ (0,1)
    refine Filter.mem_of_superset hIoo ?_
    intro h hh
    rcases hh with ⟨hpos, hlt⟩
    -- Abbreviations
    set a := dist (ρ (t + h)) v
    set b := dist (ρ t) v
    -- Local Lipschitz: dist(ρ(t+h), ρ(t)) ≤ L h because t+h ∈ (t-1, t+1)
    have h_s_in : t + h ∈ Set.Ioo (t - 1) (t + 1) := by
      have : t - 1 < t + h := by linarith
      have h2 : t + h < t + 1 := by linarith
      exact ⟨this, h2⟩
    have h_lip : dist (ρ (t + h)) (ρ t) ≤ L * |(t + h) - t| :=
      hL_bound (t + h) h_s_in
    have h_lip' : dist (ρ (t + h)) (ρ t) ≤ L * h := by
      simpa [abs_of_pos hpos, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using h_lip
    -- Reverse triangle: |a - b| ≤ dist(ρ(t+h), ρ(t)) ≤ L h
    have h_diff : |a - b| ≤ L * h := by
      have := abs_dist_sub_le (ρ (t + h)) (ρ t) v
      exact this.trans h_lip'
    -- Sum bound: a ≤ dist(ρ(t+h), ρ(t)) + b ⇒ a + b ≤ 2b + L h
    have h_sum : a + b ≤ 2 * b + L * h := by
      have : a ≤ dist (ρ (t + h)) (ρ t) + b := dist_triangle _ _ _
      linarith
    -- |(a^2 - b^2)/h| ≤ L (2 b + L h)
    have h_abs_q : |((a^2 - b^2) / h)| ≤ L * (2 * b + L * h) := by
      -- factor a^2 - b^2 = (a-b)(a+b)
      have hpos' : 0 < h := hpos
      have h1 : |a - b| ≤ L * h := h_diff
      have h2 : |a + b| ≤ 2 * b + L * h := by
        have : 0 ≤ a + b := add_nonneg dist_nonneg dist_nonneg
        exact (abs_of_nonneg this).le.trans h_sum
      have habsprod : |(a - b) * (a + b)| ≤ (L * h) * (2 * b + L * h) := by
        calc |(a - b) * (a + b)| ≤ |a - b| * |a + b| := by
               simp [abs_mul]
             _ ≤ (L * h) * (2 * b + L * h) := by
               exact mul_le_mul h1 h2 (by
                 have : 0 ≤ |a + b| := abs_nonneg _; simp [this]) (by
                 have : 0 ≤ L * h := mul_nonneg (le_of_lt hL_pos) (le_of_lt hpos'); exact this)
      -- Simplify the bound
      have : |(a - b) * (a + b)| / h ≤ L * (2 * b + L * h) := by
        have hdiv : |(a - b) * (a + b)| / h ≤ ((L * h) * (2 * b + L * h)) / h := by
          exact div_le_div_of_nonneg_right habsprod (le_of_lt hpos')
        have : ((L * h) * (2 * b + L * h)) / h = L * (2 * b + L * h) := by
          field_simp [ne_of_gt hpos]
          ring
        rw [← this]
        exact hdiv
      -- Use the factorization a^2 - b^2 = (a - b) * (a + b)
      have hfac : a^2 - b^2 = (a - b) * (a + b) := by ring
      rw [hfac, abs_div]
      simp only [abs_of_pos hpos]
      exact this
    -- Uniform bound on (0,1): L (2 b + L h) ≤ 2 L b + L^2
    have h_abs_q' : |((a^2 - b^2) / h)| ≤ 2 * L * b + L^2 := by
      have : L * (2 * b + L * h) ≤ 2 * L * b + L^2 := by
        have : L * h ≤ L := by
          have : h ≤ 1 := le_of_lt hlt
          calc L * h ≤ L * 1 := mul_le_mul_of_nonneg_left this (le_of_lt hL_pos)
            _ = L := mul_one L
        nlinarith
      exact h_abs_q.trans this
    -- Scale by |lam| and drop absolute value: x ≤ |x|
    have h_main_real : (lam * (a^2) - lam * (b^2)) / h ≤ |lam| * (2 * L * b + L^2) := by
      have eq1 : (lam * (a^2) - lam * (b^2)) = lam * (a^2 - b^2) := by ring
      calc (lam * (a^2) - lam * (b^2)) / h
        = (lam * (a^2 - b^2)) / h := by rw [eq1]
        _ ≤ |(lam * (a^2 - b^2)) / h| := le_abs_self _
        _ = |lam| * |(a^2 - b^2) / h| := by
          -- Normalize using abs rules and associativity of division/multiplication
          calc
            |(lam * (a^2 - b^2)) / h| = |lam| * |a^2 - b^2| / |h| := by
              simp [abs_mul, abs_div]
            _ = |lam| * (|a^2 - b^2| / |h|) := by
              simp [mul_div_assoc]
            _ = |lam| * |(a^2 - b^2) / h| := by
              simp [abs_div]
        _ ≤ |lam| * (2 * L * b + L^2) := mul_le_mul_of_nonneg_left h_abs_q' (abs_nonneg _)
    -- Rewrite back and lift to EReal
    -- Show h satisfies the predicate
    change (((lam * d2 (ρ (t + h)) v - lam * d2 (ρ t) v) / h : ℝ) : EReal)
          ≤ (|lam| * (2 * L * dist (ρ t) v + L^2) : ℝ)
    -- a = dist(ρ(t+h),v), b = dist(ρ t, v)
    have eq2 : (lam * d2 (ρ (t + h)) v - lam * d2 (ρ t) v) / h
              = (lam * (a^2) - lam * (b^2)) / h := by
      simp [d2, a, b, pow_two]
    rw [eq2]
    simp only [EReal.coe_le_coe_iff]
    exact h_main_real
  -- Conclude via EReal limsup monotonicity
  have : Filter.limsup (fun h : ℝ =>
            (((lam * d2 (ρ (t + h)) v - lam * d2 (ρ t) v) / h : ℝ) : EReal)) l
            ≤ (|lam| * (2 * L * dist (ρ t) v + L^2) : ℝ) :=
    Filter.limsup_le_of_le (h := h_ev)
  simpa [DiniUpperE, l] using this

/-- DiniUpperE of λ times squared distance along a Lipschitz curve -/
lemma DiniUpperE_lam_d2_bound {X : Type*} [PseudoMetricSpace X]
    (ρ : ℝ → X) (v : X) (t : ℝ) (lam : ℝ)
    (hLip : ∃ L > 0, ∀ s ∈ Set.Ioo (t - 1) (t + 1), dist (ρ s) (ρ t) ≤ L * |s - t|) :
    ∃ C : EReal, DiniUpperE (fun τ => lam * d2 (ρ τ) v) t ≤ C := by
  -- Extract Lipschitz constant
  obtain ⟨L, hL_pos, hL_bound⟩ := hLip
  -- We give an explicit finite bound (coarse but uniform in h ∈ (0,1)):
  -- C = |lam| * (2 * L * dist(ρ(t), v) + L^2)
  use (|lam| * (2 * L * dist (ρ t) v + L^2) : ℝ)

  -- Work on the right-neighborhood filter at 0
  set l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  -- Show that (0,1) is a neighborhood in l to ensure t+h ∈ (t-1,t+1)
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ l := by
    have hcrit : ∃ ε > 0,
        Metric.ball (0 : ℝ) ε ∩ Set.Ioi 0 ⊆ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
      intro x hx; rcases hx with ⟨hball, hxpos⟩
      have : dist x (0 : ℝ) < (1 : ℝ) / 2 := by simpa [Metric.mem_ball] using hball
      have habs : |x| < (1 : ℝ) / 2 := by simpa [Real.dist_eq] using this
      have hx_pos : 0 < x := by simpa using hxpos
      have hx_lt_one : x < 1 := by
        have hx_le_abs : x ≤ |x| := le_abs_self x
        have : |x| < 1 := lt_trans habs (by norm_num)
        exact lt_of_le_of_lt hx_le_abs this
      exact ⟨hx_pos, hx_lt_one⟩
    have : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      (Metric.mem_nhdsWithin_iff).2 hcrit
    simpa [l] using this

  -- Establish the eventual bound on the EReal-valued forward quotient
  have h_ev : ∀ᶠ h in l,
      (((lam * d2 (ρ (t + h)) v - lam * d2 (ρ t) v) / h : ℝ) : EReal)
        ≤ (|lam| * (2 * L * dist (ρ t) v + L^2) : ℝ) := by
    -- Reduce to h ∈ (0,1)
    refine Filter.mem_of_superset hIoo ?_
    intro h hh
    rcases hh with ⟨hpos, hlt⟩
    -- Abbreviations
    set a := dist (ρ (t + h)) v
    set b := dist (ρ t) v
    -- Local Lipschitz: dist(ρ(t+h), ρ(t)) ≤ L h because t+h ∈ (t-1, t+1)
    have h_s_in : t + h ∈ Set.Ioo (t - 1) (t + 1) := by
      have : t - 1 < t + h := by linarith
      have h2 : t + h < t + 1 := by linarith
      exact ⟨this, h2⟩
    have h_lip : dist (ρ (t + h)) (ρ t) ≤ L * |(t + h) - t| :=
      hL_bound (t + h) h_s_in
    have h_lip' : dist (ρ (t + h)) (ρ t) ≤ L * h := by
      simpa [abs_of_pos hpos, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using h_lip
    -- Reverse triangle: |a - b| ≤ dist(ρ(t+h), ρ(t)) ≤ L h
    have h_diff : |a - b| ≤ L * h := by
      have := abs_dist_sub_le (ρ (t + h)) (ρ t) v
      exact this.trans h_lip'
    -- Sum bound: a ≤ dist(ρ(t+h), ρ(t)) + b ⇒ a + b ≤ 2b + L h
    have h_sum : a + b ≤ 2 * b + L * h := by
      have : a ≤ dist (ρ (t + h)) (ρ t) + b := dist_triangle _ _ _
      linarith
    -- |(a^2 - b^2)/h| ≤ L (2 b + L h)
    have h_abs_q : |((a^2 - b^2) / h)| ≤ L * (2 * b + L * h) := by
      -- factor a^2 - b^2 = (a-b)(a+b)
      have hpos' : 0 < h := hpos
      have h1 : |a - b| ≤ L * h := h_diff
      have h2 : |a + b| ≤ 2 * b + L * h := by
        have : 0 ≤ a + b := add_nonneg dist_nonneg dist_nonneg
        exact (abs_of_nonneg this).le.trans h_sum
      have habsprod : |(a - b) * (a + b)| ≤ (L * h) * (2 * b + L * h) := by
        calc |(a - b) * (a + b)| ≤ |a - b| * |a + b| := by
               simp [abs_mul]
             _ ≤ (L * h) * (2 * b + L * h) := by
               exact mul_le_mul h1 h2 (by
                 have : 0 ≤ |a + b| := abs_nonneg _; simp [this]) (by
                 have : 0 ≤ L * h := mul_nonneg (le_of_lt hL_pos) (le_of_lt hpos'); exact this)
      -- Simplify the bound
      have : |(a - b) * (a + b)| / h ≤ L * (2 * b + L * h) := by
        have hdiv : |(a - b) * (a + b)| / h ≤ ((L * h) * (2 * b + L * h)) / h := by
          exact div_le_div_of_nonneg_right habsprod (le_of_lt hpos')
        have : ((L * h) * (2 * b + L * h)) / h = L * (2 * b + L * h) := by
          field_simp [ne_of_gt hpos]
          ring
        rw [← this]
        exact hdiv
      -- Use the factorization a^2 - b^2 = (a - b) * (a + b)
      have hfac : a^2 - b^2 = (a - b) * (a + b) := by ring
      rw [hfac, abs_div]
      simp only [abs_of_pos hpos]
      exact this
    -- Uniform bound on (0,1): L (2 b + L h) ≤ 2 L b + L^2
    have h_abs_q' : |((a^2 - b^2) / h)| ≤ 2 * L * b + L^2 := by
      have : L * (2 * b + L * h) ≤ 2 * L * b + L^2 := by
        have : L * h ≤ L := by
          have : h ≤ 1 := le_of_lt hlt
          calc L * h ≤ L * 1 := mul_le_mul_of_nonneg_left this (le_of_lt hL_pos)
            _ = L := mul_one L
        nlinarith
      exact h_abs_q.trans this
    -- Scale by |lam| and drop absolute value: x ≤ |x|
    have h_main_real : (lam * (a^2) - lam * (b^2)) / h ≤ |lam| * (2 * L * b + L^2) := by
      have eq1 : (lam * (a^2) - lam * (b^2)) = lam * (a^2 - b^2) := by ring
      calc (lam * (a^2) - lam * (b^2)) / h
        = (lam * (a^2 - b^2)) / h := by rw [eq1]
        _ ≤ |(lam * (a^2 - b^2)) / h| := le_abs_self _
        _ = |lam| * |(a^2 - b^2) / h| := by
          -- Normalize using abs rules and associativity of division/multiplication
          calc
            |(lam * (a^2 - b^2)) / h| = |lam| * |a^2 - b^2| / |h| := by
              simp [abs_mul, abs_div]
            _ = |lam| * (|a^2 - b^2| / |h|) := by
              simp [mul_div_assoc]
            _ = |lam| * |(a^2 - b^2) / h| := by
              simp [abs_div]
        _ ≤ |lam| * (2 * L * b + L^2) := mul_le_mul_of_nonneg_left h_abs_q' (abs_nonneg _)
    -- Rewrite back and lift to EReal
    -- Show h satisfies the predicate
    change (((lam * d2 (ρ (t + h)) v - lam * d2 (ρ t) v) / h : ℝ) : EReal)
          ≤ (|lam| * (2 * L * dist (ρ t) v + L^2) : ℝ)
    -- a = dist(ρ(t+h),v), b = dist(ρ t, v)
    have eq2 : (lam * d2 (ρ (t + h)) v - lam * d2 (ρ t) v) / h
              = (lam * (a^2) - lam * (b^2)) / h := by
      simp [d2, a, b, pow_two]
    rw [eq2]
    simp only [EReal.coe_le_coe_iff]
    exact h_main_real

  -- Conclude via EReal limsup monotonicity
  have : Filter.limsup (fun h : ℝ =>
            (((lam * d2 (ρ (t + h)) v - lam * d2 (ρ t) v) / h : ℝ) : EReal)) l
            ≤ (|lam| * (2 * L * dist (ρ t) v + L^2) : ℝ) :=
    Filter.limsup_le_of_le (h := h_ev)
  simpa [DiniUpperE, l] using this

end SupportingLemmas

end Frourio
