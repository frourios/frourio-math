import Frourio.Analysis.Gaussian
import Frourio.Analysis.ZakMellin

/-!
# Suitable Window Conditions for Gaussian Functions

This file establishes that normalized Gaussian windows satisfy the suitable_window
conditions required for the Zak frame theory.

## Main Results

- `suitable_window_of_normalized_gaussian`: Shows that normalized Gaussian windows
  satisfy all requirements for suitable_window predicate

-/

open MeasureTheory Filter Topology Real
open scoped ENNReal NNReal Complex

namespace Frourio.Analysis

/-- Suitable window condition for frame theory -/
structure suitable_window (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop where
  normalized : ‖f‖ = 1
  time_localized : ∃ C > 0, ∀ᵐ t : ℝ, ‖f t‖ ≤ C * (1 + |t|)^(-(2 : ℝ))
  -- Additional conditions can be added as needed

/-- Main theorem: Normalized Gaussian windows are suitable windows -/
theorem suitable_window_of_normalized_gaussian (δ : ℝ) (hδ : 0 < δ) :
    ∃ w : Lp ℂ 2 volume, ‖w‖ = 1 ∧ suitable_window w := by
  -- Use the normalized Gaussian window and its a.e. bound by a Gaussian tail
  obtain ⟨w, hw_norm, hbound⟩ := normalized_gaussian_pointwise_bound δ hδ
  use w
  constructor
  · exact hw_norm
  · constructor
    · exact hw_norm
    · -- time_localized: bound Gaussian by a polynomial with an explicit constant
      -- Constants: A from the Gaussian bound and c = π/δ² for exponent rate
      let A : ℝ := (2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt δ
      let c : ℝ := Real.pi / δ ^ 2
      let m : ℝ := min (1 : ℝ) c
      refine ⟨(2 : ℝ) * A / m, ?_, ?_⟩
      · -- Positivity of the constant
        have hApos : 0 < A := by
          have h2pos : 0 < (2 : ℝ) ^ (1/4 : ℝ) :=
            Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
          exact div_pos h2pos (Real.sqrt_pos.mpr hδ)
        have hmp : 0 < m := by
          -- m = min 1 c with c = π/δ² > 0
          have hcpos : 0 < c := by
            have hδsq : 0 < δ ^ 2 := by simpa [pow_two] using mul_pos hδ hδ
            exact div_pos Real.pi_pos hδsq
          exact lt_min (by norm_num) hcpos
        have : 0 < (2 : ℝ) * A / m := by
          have h2pos : 0 < (2 : ℝ) := by norm_num
          exact div_pos (mul_pos h2pos hApos) hmp
        simpa [A, m] using this
      · -- a.e. bound: ‖w t‖ ≤ (2A/m) · (1 + |t|)^(-2)
        -- Start from the Gaussian pointwise bound
        have hA : ∀ᵐ t : ℝ,
            ‖((w : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t‖
              ≤ A * Real.exp (-Real.pi * t ^ 2 / δ ^ 2) := by
          -- hbound is exactly this with our A
          simpa [A] using hbound
        -- Show that the Gaussian is dominated by a polynomial tail
        have h_poly : ∀ t : ℝ,
            Real.exp (-Real.pi * t ^ 2 / δ ^ 2)
              ≤ (2 : ℝ) / m * (1 + |t|) ^ (-(2 : ℝ)) := by
          intro t
          -- Step 1: exp(-x) ≤ 1/(1+x) for all real x
          have hx : Real.exp (-(c * t ^ 2)) ≤ 1 / (1 + c * t ^ 2) := by
            -- From 1 + x ≤ exp x, take reciprocals
            have : 1 + c * t ^ 2 ≤ Real.exp (c * t ^ 2) := by
              rw [add_comm]
              exact Real.add_one_le_exp (c * t ^ 2)
            -- Both sides positive, so invert the inequality
            have hpos_exp : 0 < Real.exp (c * t ^ 2) := Real.exp_pos _
            have hpos_den : 0 < 1 + c * t ^ 2 := by
              have : 0 ≤ c * t ^ 2 := by
                have hcnonneg : 0 ≤ c := by
                  have hcpos : 0 < c := by
                    have hδsq : 0 < δ ^ 2 := by simpa [pow_two] using mul_pos hδ hδ
                    exact div_pos Real.pi_pos hδsq
                  exact le_of_lt hcpos
                have ht2 : 0 ≤ t ^ 2 := by exact sq_nonneg t
                exact mul_nonneg hcnonneg ht2
              have : 0 < (1 : ℝ) + c * t ^ 2 := add_pos_of_pos_of_nonneg (by norm_num) this
              simpa using this
            -- invert 1 + x ≤ exp x
            have := inv_anti₀ hpos_den this
            -- rearrange reciprocals using exp_neg
            simpa [Real.exp_neg, one_div, c, mul_comm, mul_left_comm, mul_assoc] using this
          -- Step 2: 1 + c t² ≥ m · (1 + t²)
          have hct : m * (1 + t ^ 2) ≤ 1 + c * t ^ 2 := by
            by_cases hle : c ≤ 1
            · -- m = c
              have hm : m = c := by simp [m, min_eq_right_iff.mpr hle]
              -- 1 ≥ c, so 1 + c t² ≥ c + c t²
              have : (1 : ℝ) ≥ c := le_trans (le_of_eq rfl) hle
              have h1 : (1 : ℝ) + c * t ^ 2 ≥ c + c * t ^ 2 := by
                exact add_le_add_right this (c * t ^ 2)
              simpa [hm, mul_add, add_comm, add_left_comm, add_assoc, mul_comm,
                mul_left_comm, mul_assoc] using h1
            · -- 1 ≤ c, so m = 1 and c t² ≥ t²
              have hge : 1 ≤ c := le_of_not_ge hle
              have hm : m = 1 := by
                have : min (1 : ℝ) c = 1 := by
                  simp [min_eq_left_iff.mpr hge]
                simpa [m] using this
              have ht2 : t ^ 2 ≤ c * t ^ 2 := by
                have ht2nonneg : 0 ≤ t ^ 2 := sq_nonneg t
                calc t ^ 2 = 1 * t ^ 2 := by ring
                  _ ≤ c * t ^ 2 := mul_le_mul_of_nonneg_right hge ht2nonneg
              have : 1 + t ^ 2 ≤ 1 + c * t ^ 2 := by exact add_le_add_left ht2 1
              simpa [hm, mul_add] using this
          -- Step 3: invert and compare with (1 + |t|)^2 using (1 + |t|)^2 ≤ 2(1 + t²)
          have hinv : 1 / (1 + c * t ^ 2) ≤ (1 / m) * (1 / (1 + t ^ 2)) := by
            have hposL : 0 < 1 + c * t ^ 2 := by
              have : 0 ≤ c * t ^ 2 := by
                have hcnonneg : 0 ≤ c := (le_of_lt (by
                  have hδsq : 0 < δ ^ 2 := by simpa [pow_two] using mul_pos hδ hδ
                  exact div_pos Real.pi_pos hδsq))
                have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
                exact mul_nonneg hcnonneg ht2
              have : 0 < (1 : ℝ) + c * t ^ 2 := add_pos_of_pos_of_nonneg (by norm_num) this
              simpa using this
            have hposR : 0 < m * (1 + t ^ 2) := by
              have hmpos : 0 < m := by
                have hcpos : 0 < c := by
                  have hδsq : 0 < δ ^ 2 := by simpa [pow_two] using mul_pos hδ hδ
                  exact div_pos Real.pi_pos hδsq
                exact lt_min (by norm_num) hcpos
              have : 0 < (1 : ℝ) + t ^ 2 := by
                have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
                have := add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 1) ht2
                simpa using this
              exact mul_pos hmpos this
            have := inv_anti₀ hposR hct
            have hLm : (1 / (m * (1 + t ^ 2))) = (1 / m) * (1 / (1 + t ^ 2)) := by
              field_simp
            simpa [hLm, one_div, mul_comm] using this
          -- Compare denominators: (1 + |t|)^2 ≤ 2(1 + t^2)
          have hden : (1 + |t|) ^ 2 ≤ (2 : ℝ) * (1 + t ^ 2) := by
            -- From (|t| - 1)^2 ≥ 0 ⇒ 2|t| ≤ t^2 + 1
            have hsq : 0 ≤ (|t| - 1) ^ 2 := by exact sq_nonneg _
            -- expand (|t| - 1)^2 = |t|^2 - 2|t| + 1
            have expand : (|t| - 1) ^ 2 = |t| ^ 2 - 2 * |t| + 1 := by ring
            -- use it to derive 2|t| ≤ |t|^2 + 1 = t^2 + 1
            have h' : 2 * |t| ≤ |t| ^ 2 + 1 := by
              calc 2 * |t| = |t| ^ 2 + 1 - ((|t| - 1) ^ 2) := by rw [expand]; ring
                _ ≤ |t| ^ 2 + 1 := by linarith [hsq]
            -- now (1+|t|)^2 = 1 + 2|t| + |t|^2 ≤ 2(1 + t^2)
            calc (1 + |t|) ^ 2 = 1 + 2 * |t| + |t| ^ 2 := by ring
              _ ≤ 1 + (|t| ^ 2 + 1) + |t| ^ 2 := by linarith [h']
              _ = 2 + 2 * |t| ^ 2 := by ring
              _ = 2 * (1 + |t| ^ 2) := by ring
              _ = 2 * (1 + t ^ 2) := by rw [sq_abs]
          -- Put together: exp ≤ 1/(1+c t²) ≤ (1/m)·1/(1+t²) ≤ (2/m)·(1+|t|)^(-2)
          have hexp_bound : Real.exp (-(c * t ^ 2)) ≤ (1 / m) * (1 / (1 + t ^ 2)) :=
            le_trans hx hinv
          -- final step to replace 1/(1+t²) with 2/(1+|t|)^2
          have hfinal : (1 / (1 + t ^ 2)) ≤ (2 : ℝ) * (1 / ((1 + |t|) ^ 2)) := by
            have hpos_t : 0 < 1 + t ^ 2 := by
              have : 0 ≤ t ^ 2 := sq_nonneg t
              exact add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 1) this
            have hpos_abs : 0 < (1 + |t|) ^ 2 := by
              have : 0 < 1 + |t| := add_pos_of_pos_of_nonneg
                (by norm_num : (0 : ℝ) < 1) (abs_nonneg _)
              exact pow_pos this 2
            -- From hden: (1 + |t|)^2 ≤ 2*(1 + t^2)
            -- Taking reciprocals: 1/(2*(1 + t^2)) ≤ 1/((1 + |t|)^2)
            -- Multiplying by 2: 1/(1 + t^2) ≤ 2/((1 + |t|)^2)
            have : (1 + |t|) ^ 2 ≤ (2 : ℝ) * (1 + t ^ 2) := hden
            have step1 := inv_anti₀ hpos_abs this
            -- We have: (1 + |t|)^2 ≤ 2*(1 + t^2)
            -- So: 1/(2*(1 + t^2)) ≤ 1/((1 + |t|)^2)
            -- Multiplying both sides by 2: 1/(1 + t^2) ≤ 2/((1 + |t|)^2)
            have h1 : 1 / (2 * (1 + t ^ 2)) ≤ 1 / ((1 + |t|) ^ 2) := by
              rw [one_div, one_div]
              exact step1
            calc 1 / (1 + t ^ 2) = 2 * (1 / (2 * (1 + t ^ 2))) := by field_simp
              _ ≤ 2 * (1 / ((1 + |t|) ^ 2)) :=
              mul_le_mul_of_nonneg_left h1 (by norm_num : 0 ≤ (2 : ℝ))
          -- combine inequalities
          have := mul_le_mul_of_nonneg_left hfinal (by
            have : 0 ≤ (1 / m) := by
              -- m > 0
              have hcpos : 0 < c := by
                have hδsq : 0 < δ ^ 2 := by simpa [pow_two] using mul_pos hδ hδ
                exact div_pos Real.pi_pos hδsq
              have hmpos : 0 < m := lt_min (by norm_num) hcpos
              simp only [one_div]
              exact le_of_lt (inv_pos.mpr hmpos)
            exact this)
          -- target form with (1+|t|)^(-2)
          have hbound_ineq : (1 / m) * (1 / (1 + t ^ 2)) ≤ (2 : ℝ) / m * (1 / ((1 + |t|) ^ 2)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
              using this
          -- Rewrite (1 / ((1 + |t|)^2)) as (1 + |t|)^(-2)
          have hpow : (1 / ((1 + |t|) ^ 2)) = (1 + |t|) ^ (-(2 : ℝ)) := by
            have hpos : 0 < (1 + |t|) := by
              exact add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 1) (abs_nonneg _)
            rw [one_div, Real.rpow_neg hpos.le, Real.rpow_two]
          -- assemble the chain
          calc
            Real.exp (-Real.pi * t ^ 2 / δ ^ 2)
                = Real.exp (-(c * t ^ 2)) := by
                  simp [c, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
            _ ≤ (1 / m) * (1 / (1 + t ^ 2)) := hexp_bound
            _ ≤ (2 : ℝ) / m * (1 / ((1 + |t|) ^ 2)) := hbound_ineq
            _ = (2 : ℝ) / m * (1 + |t|) ^ (-(2 : ℝ)) := by simp [hpow]
        -- conclude using AE bound and the pointwise inequality
        refine hA.mono ?_
        intro t ht
        have := h_poly t
        exact le_trans ht (by
          have : A * Real.exp (-Real.pi * t ^ 2 / δ ^ 2)
                ≤ A * ((2 : ℝ) / m * (1 + |t|) ^ (-(2 : ℝ))) :=
            by
              have hA_nonneg : 0 ≤ A := by
                have hApos : 0 < A := by
                  have h2pos : 0 < (2 : ℝ) ^ (1/4 : ℝ) :=
                    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
                  exact div_pos h2pos (Real.sqrt_pos.mpr hδ)
                exact le_of_lt hApos
              exact mul_le_mul_of_nonneg_left this hA_nonneg
          simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, A, m])

end Frourio.Analysis
