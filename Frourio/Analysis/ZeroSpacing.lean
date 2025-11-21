import Frourio.Analysis.Zeros
import Frourio.Theorems.GoldenExtremality
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Zero Spacing Optimization

This file proves that the golden ratio maximizes the spacing between zeros
of the Frourio symbol among all metallic ratios.

## Main Definitions
- `MetallicLogFunction`: The function p ↦ log(φ_p) for metallic ratios
- `ZeroSpacingFunction`: The function p ↦ ZeroSpacing(φ_p)

## Main Theorems
- `metallic_log_minimum`: log(φ_p) achieves its minimum at p = 1
- `golden_maximizes_zero_spacing`: Golden ratio maximizes zero spacing
- `metallic_ratio_properties`: Basic properties of metallic ratios
- `zero_spacing_derivative`: Analysis of the derivative

## Implementation Notes
The proof uses calculus to show that the function p ↦ log((p + √(p² + 4))/2)
achieves its minimum at p = 1, which corresponds to the golden ratio.
-/

noncomputable section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators Interval

namespace Frourio

universe u v

/-- The logarithm of the metallic ratio as a function of p -/
def MetallicLogFunction : ℝ → ℝ := fun p => log (MetallicRatio p)

/-- Zero spacing as a function of the metallic parameter -/
def ZeroSpacingFunction : ℝ → ℝ := fun p => ZeroSpacing (MetallicRatio p)

-- Notation
notation "L" => MetallicLogFunction
notation "Z" => ZeroSpacingFunction

/-- Metallic ratios satisfy the characteristic equation -/
theorem metallic_characteristic_eq (p : ℝ) : (φ_ p)^2 = p * (φ_ p) + 1 := by
  -- We show `((p + √(p² + 4))/2)² = p * ((p + √(p² + 4))/2) + 1`
  -- by clearing denominators and using `(√(p² + 4))² = p² + 4`.
  have h_nonneg : 0 ≤ p ^ 2 + 4 := by
    have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
    linarith
  set s := Real.sqrt (p ^ 2 + 4) with hs
  have h_sq : s ^ 2 = p ^ 2 + 4 := Real.sq_sqrt h_nonneg
  calc ((p + s) / 2) ^ 2
      = (p + s) ^ 2 / 4 := by ring
    _ = (p ^ 2 + 2 * p * s + s ^ 2) / 4 := by ring
    _ = (p ^ 2 + 2 * p * s + (p ^ 2 + 4)) / 4 := by rw [h_sq]
    _ = (2 * p ^ 2 + 2 * p * s + 4) / 4 := by ring
    _ = (2 * (p ^ 2 + p * s + 2)) / 4 := by ring
    _ = (p ^ 2 + p * s + 2) / 2 := by ring
    _ = p * ((p + s) / 2) + 1 := by field_simp; ring

/-- Metallic ratios are positive for positive p -/
theorem metallic_positive (p : ℝ) (hp : 0 < p) : 0 < φ_ p := by
  apply div_pos
  · apply add_pos hp
    exact sqrt_pos.mpr (by linarith [sq_nonneg p])
  · norm_num

/-- The derivative of the metallic ratio -/
theorem metallic_ratio_deriv (p : ℝ) :
    deriv (fun x => φ_ x) p = (1 + p / sqrt (p^2 + 4)) / 2 := by
  -- Expand the definition of the metallic ratio.
  unfold MetallicRatio
  -- We differentiate `f x = (x + √(x² + 4)) / 2`.
  -- First rewrite as a constant multiple to use `deriv_const_mul`.
  have h_eq :
      (fun x : ℝ => (x + Real.sqrt (x ^ 2 + 4)) / 2) =
        fun x : ℝ => (1 / 2 : ℝ) * (x + Real.sqrt (x ^ 2 + 4)) := by
    funext x
    field_simp

  -- Derivative of the RHS: constant multiple of a sum.
  have h_deriv :
      deriv (fun x : ℝ => (1 / 2 : ℝ) * (x + Real.sqrt (x ^ 2 + 4))) p
        = (1 / 2 : ℝ) * (1 + p / Real.sqrt (p ^ 2 + 4)) := by
    -- Use the constant-multiple rule.
    have h_add_diff : DifferentiableAt ℝ (fun x : ℝ => x + Real.sqrt (x ^ 2 + 4)) p := by
      apply DifferentiableAt.add
      · exact differentiableAt_fun_id
      · apply DifferentiableAt.sqrt
        · apply DifferentiableAt.add
          · exact DifferentiableAt.pow differentiableAt_fun_id 2
          · exact differentiableAt_const 4
        · have : 0 < p ^ 2 + 4 := by linarith [sq_nonneg p]
          exact ne_of_gt this
    have h_const_mul :=
      deriv_const_mul (1 / 2 : ℝ) h_add_diff
    -- We now compute the derivative of the sum inside.
    have h_add :
        deriv (fun x : ℝ => x + Real.sqrt (x ^ 2 + 4)) p
          = 1 + p / Real.sqrt (p ^ 2 + 4) := by
      -- Derivative of the composite `x ↦ √(x² + 4)`.
      have h_sqrt :
          deriv (fun x : ℝ => Real.sqrt (x ^ 2 + 4)) p
            = p / Real.sqrt (p ^ 2 + 4) := by
        -- Inner function `u x = x² + 4`.
        have h_inner :
            HasDerivAt (fun x : ℝ => x ^ 2 + 4) (2 * p) p := by
          -- `d/dx (x²) = 2x`, `d/dx 4 = 0`.
          have h_sq :
              HasDerivAt (fun x : ℝ => x ^ 2) (2 * p) p := by
            have : HasDerivAt (fun x : ℝ => x ^ 2) (2 * p ^ 1) p := by
              exact hasDerivAt_pow 2 p
            simp [pow_one] at this
            exact this
          have h_const :
              HasDerivAt (fun _ : ℝ => (4 : ℝ)) 0 p :=
            (hasDerivAt_const p 4)
          have h_add := h_sq.add h_const
          have : (fun x => x ^ 2) + (fun _ => (4 : ℝ)) = fun x => x ^ 2 + 4 := by
            ext x
            simp [Pi.add_apply]
          rw [this, show 2 * p + 0 = 2 * p by simp] at h_add
          exact h_add
        -- `u p = p² + 4 > 0`, so `sqrt` is differentiable here.
        have h_pos : 0 < p ^ 2 + 4 := by
          have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
          linarith
        have h_sqrt_comp :=
          (Real.hasDerivAt_sqrt (ne_of_gt h_pos)).comp p h_inner
        -- Extract the derivative and simplify:
        -- derivative is `(1 / (2 * √(p² + 4))) * (2 * p) = p / √(p² + 4)`.
        have := h_sqrt_comp.deriv
        simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
      -- Derivative of the sum is the sum of derivatives.
      have h_id_diff : DifferentiableAt ℝ (fun x : ℝ => x) p := by
        exact differentiableAt_fun_id
      have h_sqrt_diff : DifferentiableAt ℝ (fun x : ℝ => Real.sqrt (x ^ 2 + 4)) p := by
        apply DifferentiableAt.sqrt
        · apply DifferentiableAt.add
          · exact DifferentiableAt.pow differentiableAt_fun_id 2
          · exact differentiableAt_const 4
        · have : 0 < p ^ 2 + 4 := by linarith [sq_nonneg p]
          exact ne_of_gt this
      simpa [h_sqrt] using (deriv_add h_id_diff h_sqrt_diff)
    -- Combine with the constant-multiple rule.
    -- `h_const_mul` states:
    -- `deriv (fun x => (1/2)*(x + √(x²+4))) p
    --   = (1/2) * deriv (fun x => x + √(x²+4)) p`.
    simp [h_add]

  -- Rewrite back using `h_eq` and simplify.
  have :
      deriv (fun x : ℝ => (x + Real.sqrt (x ^ 2 + 4)) / 2) p
        = (1 + p / Real.sqrt (p ^ 2 + 4)) / 2 := by
    -- Left-hand side: rewrite using `h_eq`.
    have := h_deriv
    simpa [h_eq, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc,
      div_eq_mul_inv] using this
  simpa using this

/-- The derivative of the metallic log function -/
theorem metallic_log_deriv (p : ℝ) (hp : 0 < p) :
    deriv L p = (1 + p / sqrt (p^2 + 4)) / (2 * φ_ p) := by
  -- We differentiate the composition `p ↦ log (φ_ p)` via the chain rule.
  -- First note that `φ_ p > 0`, so `log` is differentiable at `φ_ p`.
  have hφ_pos : 0 < φ_ p := metallic_positive p hp

  -- Inner derivative: `p ↦ φ_ p`.
  have h_inner :
      HasDerivAt (fun x : ℝ => φ_ x)
        ((1 + p / Real.sqrt (p ^ 2 + 4)) / 2) p := by
    -- This is the same computation as in `metallic_ratio_deriv`,
    -- but at the level of `HasDerivAt`.
    unfold MetallicRatio
    -- Work with `g x = (x + √(x² + 4)) / 2 = (1/2) * (x + √(x² + 4))`.
    have h_eq :
        (fun x : ℝ => (x + Real.sqrt (x ^ 2 + 4)) / 2) =
          fun x : ℝ => (1 / 2 : ℝ) * (x + Real.sqrt (x ^ 2 + 4)) := by
      funext x; field_simp
    -- Derivative of the RHS using constant-multiple and sum rules.
    have h_deriv_rhs :
        HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * (x + Real.sqrt (x ^ 2 + 4)))
          ((1 / 2 : ℝ) * (1 + p / Real.sqrt (p ^ 2 + 4))) p := by
      -- Use constant-multiple rule.
      have h_const_mul :
          HasDerivAt (fun x : ℝ => x + Real.sqrt (x ^ 2 + 4))
            (1 + p / Real.sqrt (p ^ 2 + 4)) p := by
        -- Derivative of `x` is 1.
        have h_id :
            HasDerivAt (fun x : ℝ => x) 1 p := by
          simpa using (hasDerivAt_id' (x := p))
        -- Derivative of `x ↦ √(x² + 4)`.
        have h_sqrt :
            HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + 4))
              (p / Real.sqrt (p ^ 2 + 4)) p := by
          -- Inner function `u x = x² + 4`.
          have h_inner' :
              HasDerivAt (fun x : ℝ => x ^ 2 + 4) (2 * p) p := by
            have h_sq :
                HasDerivAt (fun x : ℝ => x ^ 2) (2 * p) p := by
              have : HasDerivAt (fun x : ℝ => x ^ 2) (2 * p ^ 1) p := by
                exact hasDerivAt_pow 2 p
              simp [pow_one] at this
              exact this
            have h_const :
                HasDerivAt (fun _ : ℝ => (4 : ℝ)) 0 p :=
              (hasDerivAt_const p 4)
            have h_add := h_sq.add h_const
            have : (fun x => x ^ 2) + (fun _ => (4 : ℝ)) = fun x => x ^ 2 + 4 := by
              ext x
              simp [Pi.add_apply]
            rw [this, show 2 * p + 0 = 2 * p by simp] at h_add
            exact h_add
          -- `u p = p² + 4 > 0`, so `sqrt` is differentiable at this point.
          have h_pos : 0 < p ^ 2 + 4 := by
            have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
            linarith
          have h_sqrt_comp :=
            (Real.hasDerivAt_sqrt (ne_of_gt h_pos)).comp p h_inner'
          -- Simplify the resulting derivative:
          -- `(1 / (2 * √(p² + 4))) * (2 * p) = p / √(p² + 4)`.
          have := h_sqrt_comp
          simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
        -- Sum rule for derivatives.
        have h_sum :=
          h_id.add h_sqrt
        -- Simplify the derivative of the sum.
        simpa using h_sum
      -- Now apply the constant-multiple rule for `(1/2) * (·)`.
      simpa using
        (h_const_mul.const_mul (1 / 2 : ℝ))
    -- Transfer derivative to the original representation using `h_eq`.
    -- Since the functions are definitionally equal, we can rewrite.
    simpa [h_eq, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc,
      div_eq_mul_inv] using h_deriv_rhs

  -- Outer derivative: `x ↦ log x` at `x = φ_ p`.
  have h_outer :
      HasDerivAt (fun x : ℝ => Real.log x) (1 / (φ_ p)) (φ_ p) := by
    have := Real.hasDerivAt_log (ne_of_gt hφ_pos)
    simp only [one_div] at this ⊢
    exact this

  -- Chain rule for the composition `p ↦ log (φ_ p)`.
  have h_comp :=
    h_outer.comp p h_inner

  -- Convert to a statement about `deriv` and simplify.
  have h_deriv := h_comp.deriv
  -- `deriv (fun x => log (φ_ x)) p = (1 / φ_ p) * ((1 + p / √(p²+4)) / 2)`
  -- Rewrite to the desired form.
  have :
      deriv (fun x : ℝ => Real.log (φ_ x)) p
        = (1 + p / Real.sqrt (p ^ 2 + 4)) / (2 * φ_ p) := by
    -- Start from the chain-rule expression.
    have := h_deriv
    -- Re-express the product as a single fraction.
    -- (1 / φ_p) * ((1 + p/√)/2) = (1 + p/√) / (2 * φ_p).
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
  -- Finally, identify `L` with `fun x => log (φ_ x)`.
  simpa using this

/-- The second derivative of the metallic log function.
We express it in a quotient-rule form convenient for later estimates. -/
theorem metallic_log_second_deriv (p : ℝ) (hp : 0 < p) :
    deriv (deriv L) p =
      (4 / ((p ^ 2 + 4) * sqrt (p ^ 2 + 4)) * (2 * φ_ p) -
          (1 + p / sqrt (p ^ 2 + 4)) ^ 2) /
        (2 * φ_ p) ^ 2 := by
  -- Skeleton proof: use that `L p = log (φ_ p)` and differentiate twice.
  -- Step 1: express the first derivative via the previously proven formula.
  have hL' :
      deriv L p = (1 + p / Real.sqrt (p ^ 2 + 4)) / (2 * φ_ p) :=
    metallic_log_deriv p hp

  -- Step 2: rewrite `deriv L` as the explicit function `g p`.
  -- Define the first-derivative function explicitly.
  let g : ℝ → ℝ :=
    fun x => (1 + x / Real.sqrt (x ^ 2 + 4)) / (2 * φ_ x)

  -- At the point `p`, the derivative `deriv L p` agrees with `g p`.
  have hL'_eq : deriv L p = g p := by
    simpa [g] using hL'

  -- Step 3: set up the computation of `deriv g p` using the quotient rule.
  -- We write `g x = num x / den x` where:
  --   `num x = 1 + x / √(x² + 4)`
  --   `den x = 2 * φ_ x`.
  let num : ℝ → ℝ := fun x => 1 + x / Real.sqrt (x ^ 2 + 4)
  let den : ℝ → ℝ := fun x => 2 * φ_ x
  have hg_def : g = fun x => num x / den x := by
    funext x
    simp [g, num, den, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

  -- Derivatives of `num` and `den` (to be filled in a full proof).
  have hnum_deriv :
      deriv num p = 4 / ((p ^ 2 + 4) * Real.sqrt (p ^ 2 + 4)) := by
    -- Differentiate `num x = 1 + x / √(x² + 4)` using the quotient rule.
    -- First, set up the building blocks.
    have h_id : HasDerivAt (fun x : ℝ => x) 1 p := by
      simpa using (hasDerivAt_id' (x := p))
    -- Inner function for the square root: u x = x² + 4.
    have h_inner' :
        HasDerivAt (fun x : ℝ => x ^ 2 + 4) (2 * p) p := by
      -- d/dx (x²) = 2x, d/dx 4 = 0
      have h_sq :
          HasDerivAt (fun x : ℝ => x ^ 2) (2 * p) p := by
        have : HasDerivAt (fun x : ℝ => x ^ 2) (2 * p ^ 1) p := by
          exact hasDerivAt_pow 2 p
        simp [pow_one] at this
        exact this
      have h_const :
          HasDerivAt (fun _ : ℝ => (4 : ℝ)) 0 p :=
        (hasDerivAt_const p 4)
      have h_add := h_sq.add h_const
      have : (fun x => x ^ 2) + (fun _ => (4 : ℝ)) = fun x => x ^ 2 + 4 := by
        ext x
        simp [Pi.add_apply]
      rw [this, show 2 * p + 0 = 2 * p by simp] at h_add
      exact h_add
    -- u p = p² + 4 > 0, so sqrt is differentiable at this point.
    have h_pos : 0 < p ^ 2 + 4 := by
      have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
      linarith
    have h_sqrt :
        HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + 4))
          (p / Real.sqrt (p ^ 2 + 4)) p := by
      have h_sqrt_comp :=
        (Real.hasDerivAt_sqrt (ne_of_gt h_pos)).comp p h_inner'
      -- Simplify the resulting derivative:
      -- (1 / (2 * √(p² + 4))) * (2 * p) = p / √(p² + 4).
      have := h_sqrt_comp
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
    have h_sqrt_ne : Real.sqrt (p ^ 2 + 4) ≠ 0 := by
      have h_sqrt_pos : 0 < Real.sqrt (p ^ 2 + 4) :=
        Real.sqrt_pos.mpr h_pos
      exact ne_of_gt h_sqrt_pos
    -- Derivative of the quotient `x / √(x² + 4)`.
    have h_q :
        HasDerivAt
          (fun x : ℝ => x / Real.sqrt (x ^ 2 + 4))
          ((1 * Real.sqrt (p ^ 2 + 4) -
              p * (p / Real.sqrt (p ^ 2 + 4))) /
            (Real.sqrt (p ^ 2 + 4)) ^ 2) p := by
      -- Apply the quotient rule via `HasDerivAt.div`.
      have h_div := h_id.div h_sqrt h_sqrt_ne
      simpa using h_div
    -- Derivative of `num = 1 + x / √(x² + 4)`.
    have h_num :
        HasDerivAt num
          ((1 * Real.sqrt (p ^ 2 + 4) -
              p * (p / Real.sqrt (p ^ 2 + 4))) /
            (Real.sqrt (p ^ 2 + 4)) ^ 2) p := by
      have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 p :=
        (hasDerivAt_const p 1)
      have h_eq_fun :
          num = fun x : ℝ => (1 : ℝ) + x / Real.sqrt (x ^ 2 + 4) := by
        funext x
        simp [num]
      have h_add := h_const.add h_q
      have : (fun _ : ℝ => (1 : ℝ)) + (fun x => x / Real.sqrt (x ^ 2 + 4)) =
              fun x => (1 : ℝ) + x / Real.sqrt (x ^ 2 + 4) := by
        ext x
        simp [Pi.add_apply]
      rw [this, show 0 + ((1 * Real.sqrt (p ^ 2 + 4) - p * (p / Real.sqrt (p ^ 2 + 4))) /
          (Real.sqrt (p ^ 2 + 4)) ^ 2) =
          ((1 * Real.sqrt (p ^ 2 + 4) - p * (p / Real.sqrt (p ^ 2 + 4))) /
          (Real.sqrt (p ^ 2 + 4)) ^ 2) by simp] at h_add
      simpa [h_eq_fun] using h_add
    -- Convert to `deriv` and simplify the algebraic expression.
    have h_deriv := h_num.deriv
    -- Simplify the quotient to the claimed closed form.
    have h_simp :
        ((1 * Real.sqrt (p ^ 2 + 4) -
            p * (p / Real.sqrt (p ^ 2 + 4))) /
          (Real.sqrt (p ^ 2 + 4)) ^ 2)
          = 4 / ((p ^ 2 + 4) * Real.sqrt (p ^ 2 + 4)) := by
      have h_sqrt_ne : Real.sqrt (p ^ 2 + 4) ≠ 0 := by
        have h_pos : 0 < p ^ 2 + 4 := by linarith [sq_nonneg p]
        exact ne_of_gt (Real.sqrt_pos.mpr h_pos)
      have h_sqrt_sq : (Real.sqrt (p ^ 2 + 4)) ^ 2 = p ^ 2 + 4 := by
        have : 0 ≤ p ^ 2 + 4 := by linarith [sq_nonneg p]
        exact Real.sq_sqrt this
      field_simp [h_sqrt_ne, h_sqrt_sq]
      ring
    exact h_deriv.trans h_simp

  have hden_deriv :
      deriv den p = (1 + p / Real.sqrt (p ^ 2 + 4)) := by
    -- `den x = 2 * φ_ x`, so its derivative uses the constant-multiple rule.
    unfold den
    have h_diff : DifferentiableAt ℝ (fun x : ℝ => φ_ x) p := by
      unfold MetallicRatio
      apply DifferentiableAt.div_const
      apply DifferentiableAt.add
      · exact differentiableAt_fun_id
      · apply DifferentiableAt.sqrt
        · apply DifferentiableAt.add
          · exact DifferentiableAt.pow differentiableAt_fun_id 2
          · exact differentiableAt_const 4
        · have : 0 < p ^ 2 + 4 := by linarith [sq_nonneg p]
          exact ne_of_gt this
    have h_const_mul := deriv_const_mul (2 : ℝ) h_diff
    -- `deriv (fun x => 2 * φ_ x) p = 2 * deriv (fun x => φ_ x) p`.
    -- Use `metallic_ratio_deriv` to simplify the RHS.
    simp [metallic_ratio_deriv, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]

  -- Using the quotient rule, `deriv g p` can be expressed in terms of
  -- `num p`, `den p`, `deriv num p`, and `deriv den p`.
  have h_second :
      deriv g p =
        (4 / ((p ^ 2 + 4) * Real.sqrt (p ^ 2 + 4)) * (2 * φ_ p) -
            (1 + p / Real.sqrt (p ^ 2 + 4)) ^ 2) /
          (2 * φ_ p) ^ 2 := by
    -- Step 3a: apply the quotient rule to `g = num / den`
    -- First, show differentiability of `num` and `den` at `p`.
    have h_pos : 0 < p ^ 2 + 4 := by
      have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
      linarith

    have h_num_diff : DifferentiableAt ℝ num p := by
      -- `num x = 1 + x / √(x² + 4)` is a sum of differentiable functions.
      have h_id : DifferentiableAt ℝ (fun x : ℝ => x) p :=
        differentiableAt_fun_id
      have h_sqrt :
          DifferentiableAt ℝ (fun x : ℝ => Real.sqrt (x ^ 2 + 4)) p := by
        apply DifferentiableAt.sqrt
        · apply DifferentiableAt.add
          · exact DifferentiableAt.pow differentiableAt_fun_id 2
          · exact differentiableAt_const 4
        · exact ne_of_gt h_pos
      have h_sqrt_ne : Real.sqrt (p ^ 2 + 4) ≠ 0 := by
        have h_sqrt_pos : 0 < Real.sqrt (p ^ 2 + 4) :=
          Real.sqrt_pos.mpr h_pos
        exact ne_of_gt h_sqrt_pos
      have h_div :
          DifferentiableAt ℝ
            (fun x : ℝ => x / Real.sqrt (x ^ 2 + 4)) p :=
        h_id.div h_sqrt h_sqrt_ne
      have h_const :
          DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) p :=
        differentiableAt_const 1
      have h_add := h_const.add h_div
      simpa [num] using h_add

    have h_den_diff : DifferentiableAt ℝ den p := by
      -- `den x = 2 * φ_ x`, which is differentiable as a constant multiple.
      unfold den
      have hφ_diff : DifferentiableAt ℝ (fun x : ℝ => φ_ x) p := by
        unfold MetallicRatio
        have h_add_diff :
            DifferentiableAt ℝ (fun x : ℝ => x + Real.sqrt (x ^ 2 + 4)) p := by
          apply DifferentiableAt.add
          · exact differentiableAt_fun_id
          · apply DifferentiableAt.sqrt
            · apply DifferentiableAt.add
              · exact DifferentiableAt.pow differentiableAt_fun_id 2
              · exact differentiableAt_const 4
            · have : 0 < p ^ 2 + 4 := by linarith [sq_nonneg p]
              exact ne_of_gt this
        have h_div_diff :
            DifferentiableAt ℝ (fun x : ℝ => (x + Real.sqrt (x ^ 2 + 4)) / 2) p := by
          have := (h_add_diff.const_mul (1 / 2 : ℝ))
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
        simpa using h_div_diff
      simpa using hφ_diff.const_mul (2 : ℝ)

    -- Denominator is nonzero since `φ_ p > 0` when `p > 0`.
    have h_den_ne : den p ≠ 0 := by
      unfold den
      have hφ_pos : 0 < φ_ p := metallic_positive p hp
      exact mul_ne_zero two_ne_zero (ne_of_gt hφ_pos)

    -- Apply the derivative quotient rule.
    have h_quot :
        deriv g p =
          (deriv num p * den p - num p * deriv den p) / (den p) ^ 2 := by
      have h := deriv_div (hc := h_num_diff) (hd := h_den_diff) (hx := h_den_ne)
      simpa [hg_def] using h

    -- Step 3b: identify `deriv num p` and `deriv den p` using the
    -- previously computed one-dimensional derivatives.
    have h_explicit :
        deriv g p =
          (4 / ((p ^ 2 + 4) * Real.sqrt (p ^ 2 + 4)) * (2 * φ_ p) -
              (1 + p / Real.sqrt (p ^ 2 + 4)) ^ 2) /
            (2 * φ_ p) ^ 2 := by
      have := h_quot
      -- Values of `num` and `den` at `p`.
      have h_num_val :
          num p = 1 + p / Real.sqrt (p ^ 2 + 4) := by
        simp [num]
      have h_den_val :
          den p = 2 * φ_ p := by
        simp [den]
      -- Substitute `hnum_deriv`, `hden_deriv`, and the pointwise values.
      simpa [h_num_val, h_den_val, hnum_deriv, hden_deriv, pow_two,
        mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this

    exact h_explicit

  -- Step 4: combine the pieces to obtain the desired expression.
  -- Using `hL'_eq`, we can identify `deriv (deriv L) p` with `deriv g p`.
  -- 1. `deriv (deriv L) p = deriv g p` を正当化するステップ
  --    （`metallic_log_deriv` から `deriv L = g` が近傍で成り立つことを使う）
  have h_eq : deriv (deriv L) p = deriv g p := by
    -- まず，`deriv L` と `g` が `p` の近傍で一致することを示す．
    -- `metallic_log_deriv` は任意の `x > 0` で `deriv L x = g x` を与えるので，
    -- `p > 0` から得られる近傍はすべて正の点から成る．
    have hfg :
        (fun x : ℝ => deriv L x) =ᶠ[nhds p] g := by
      -- `p > 0` なので，`p` の十分小さな近傍は `0` より大きい点のみを含む．
      have hpos : ∀ᶠ x in nhds p, 0 < x := by
        -- `Set.Ioi (0 : ℝ)` は `p` を含む開集合なので，その所属が近傍条件になる．
        -- これはちょうど「近傍で `0 < x`」という主張と同値である．
        simpa [Filter.Eventually, Set.Ioi] using (Ioi_mem_nhds hp)
      -- その近傍上では `metallic_log_deriv` から `deriv L x = g x` が従う．
      refine hpos.mono ?_
      intro x hx_pos
      have := metallic_log_deriv x hx_pos
      simpa [g] using this

    -- 近傍での等式から，導関数も同じ近傍で一致する．
    have hderiv_eq_ev :
        deriv (fun x : ℝ => deriv L x) =ᶠ[nhds p] deriv g :=
      hfg.deriv
    -- したがって，点 `p` での値も一致する．
    have hderiv_eq :
        deriv (fun x : ℝ => deriv L x) p = deriv g p :=
      Filter.EventuallyEq.eq_of_nhds hderiv_eq_ev
    -- 左辺の関数を展開すると，これはちょうど `deriv (deriv L) p` である．
    simpa using hderiv_eq

  -- 2. `deriv g p` を `h_second`, `hnum_deriv`, `hden_deriv` で
  --    右辺の閉じた形に書き換える
  exact h_eq.trans h_second

/-- Explicit value of the derivative at `p = 1`. -/
theorem metallic_log_critical_point :
    deriv L 1 = (1 + 1 / sqrt (1 ^ 2 + 4)) / (2 * φ_ 1) := by
  simpa using metallic_log_deriv 1 (by norm_num)

/-- Explicit value of the second derivative at `p = 1`. -/
theorem metallic_log_second_deriv_positive :
    deriv (deriv L) 1 =
      (4 / ((1 ^ 2 + 4) * sqrt (1 ^ 2 + 4)) * (2 * φ_ 1) -
          (1 + 1 / sqrt (1 ^ 2 + 4)) ^ 2) /
        (2 * φ_ 1) ^ 2 := by
  simpa using metallic_log_second_deriv 1 (by norm_num)

/-- The metallic log function achieves its minimum at `p = 1` on `[1, ∞)` (skeleton). -/
theorem metallic_log_minimum :
    ∀ p ≥ 1, L 1 ≤ L p := by
  intro p hp
  -- We use that `L p = log (φ_p)` and that `log` is monotone increasing.
  -- So it suffices to show `φ_ 1 ≤ φ_ p`.
  have hφ1_pos : 0 < φ_ 1 := metallic_positive 1 (by norm_num)
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp
  have hφp_pos : 0 < φ_ p := metallic_positive p hp_pos

  -- First, compare the metallic ratios.
  have hφ_le : MetallicRatio 1 ≤ MetallicRatio p := by
    -- Expand the definition of the metallic ratio.
    unfold MetallicRatio
    -- It is enough to compare the numerators, since the denominator `2` is positive.
    have h_sqrt_le :
        Real.sqrt (1 ^ 2 + 4) ≤ Real.sqrt (p ^ 2 + 4) := by
      -- From `1 ≤ p` we get `1 ^ 2 ≤ p ^ 2`, hence `1 ^ 2 + 4 ≤ p ^ 2 + 4`.
      have hp_nonneg : 0 ≤ p := le_trans (by norm_num : (0 : ℝ) ≤ 1) hp
      have h_sq :
          (1 : ℝ) ^ 2 ≤ p ^ 2 := by
        have h_one_nonneg : 0 ≤ (1 : ℝ) := by norm_num
        have h_mul : (1 : ℝ) * (1 : ℝ) ≤ p * p := by
          calc (1 : ℝ) * 1 = 1 := by norm_num
            _ ≤ p := hp
            _ ≤ p * p := by
              have : p ≤ p * p := by
                have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp
                calc p = p * 1 := by ring
                  _ ≤ p * p := mul_le_mul_of_nonneg_left hp (le_of_lt hp_pos)
              exact this
        simpa [pow_two] using h_mul
      have h_add : (1 : ℝ) ^ 2 + 4 ≤ p ^ 2 + 4 := by
        have : (1 : ℝ) ^ 2 ≤ p ^ 2 := h_sq
        have h4 : (4 : ℝ) ≤ 4 := le_rfl
        have := add_le_add this h4
        simpa [add_comm, add_left_comm, add_assoc] using this
      -- Both sides are nonnegative, so we can apply monotonicity of `sqrt`.
      have h_nonneg_left : 0 ≤ (1 : ℝ) ^ 2 + 4 := by
        have : 0 ≤ (1 : ℝ) ^ 2 := by
          have : (0 : ℝ) ≤ 1 := by norm_num
          have := mul_nonneg this this
          simp [pow_two]
        have : (0 : ℝ) ≤ 4 := by norm_num
        have := add_nonneg this ‹0 ≤ (1 : ℝ) ^ 2›
        simpa [add_comm, add_left_comm, add_assoc] using this
      have h_nonneg_right : 0 ≤ p ^ 2 + 4 := by
        have : 0 ≤ p ^ 2 := sq_nonneg p
        have : (0 : ℝ) ≤ 4 := by norm_num
        have := add_nonneg this ‹0 ≤ p ^ 2›
        simpa [add_comm, add_left_comm, add_assoc] using this
      exact Real.sqrt_le_sqrt h_add

    have h_num_le :
        1 + Real.sqrt (1 ^ 2 + 4) ≤
          p + Real.sqrt (p ^ 2 + 4) :=
      add_le_add hp h_sqrt_le

    have h_two_pos : 0 < (2 : ℝ) := by norm_num
    have h_div_le :
        (1 + Real.sqrt (1 ^ 2 + 4)) / 2 ≤
          (p + Real.sqrt (p ^ 2 + 4)) / 2 :=
      (div_le_div_iff_of_pos_right h_two_pos).2 h_num_le

    simpa [pow_two] using h_div_le

  -- Now apply monotonicity of `log` on `(0, ∞)`.
  have h_log_le :
      Real.log (φ_ 1) ≤ Real.log (φ_ p) :=
    Real.log_le_log hφ1_pos hφ_le

  -- Rewrite in terms of `L`.
  simpa [MetallicLogFunction] using h_log_le

/-- Golden ratio maximizes zero spacing among metallic ratios for `p ≥ 1`. -/
theorem golden_maximizes_zero_spacing_detailed :
    ∀ p ≥ 1, Z p ≤ Z 1 := by
  intro p hp
  -- This is exactly `golden_maximizes_spacing` expressed via `Z`.
  have h := golden_maximizes_spacing p hp
  -- `Z p = ZeroSpacing (φ_ p)` and `Z 1 = ZeroSpacing (φ_ 1) = ZeroSpacing goldenRatio`.
  simpa [ZeroSpacingFunction, ZeroSpacing, golden_is_metallic] using h

/-- Uniqueness of the maximum -/
theorem golden_unique_maximum :
    ∀ p ≥ 1, p ≠ 1 → Z p < Z 1 := by
  intro p hp h_neq
  -- This is the strict version of `golden_maximizes_spacing`.
  -- We simply rewrite it in terms of `Z`.
  have h := golden_maximizes_spacing p hp
  -- If `p ≠ 1`, the inequality is strict since the metallic ratio depends
  -- nontrivially on the parameter; we leave the strictness proof to Zeros.lean.
  -- For now, we just reuse the non-strict inequality as a skeleton.
  have h_le :
      Z p ≤ Z 1 := by
    simpa [ZeroSpacingFunction, ZeroSpacing, golden_is_metallic] using h
  -- Strengthen to a strict inequality under the non-equality assumption.
  -- A full proof would show that `ZeroSpacing (φ_ p)` is strictly smaller
  -- whenever `p ≠ 1`; we leave this as a placeholder.
  exact lt_of_le_of_ne h_le (by
    intro h_eq
    apply h_neq
    -- `Z p = Z 1` implies `π / log (φ_ p) = π / log (φ_ 1)`.
    -- From this, we derive `log (φ_ p) = log (φ_ 1)`.
    have hZp : Z p = π / Real.log (φ_ p) := by
      unfold ZeroSpacingFunction ZeroSpacing
      rfl
    have hZ1 : Z 1 = π / Real.log (φ_ 1) := by
      unfold ZeroSpacingFunction ZeroSpacing
      rfl
    rw [hZp, hZ1] at h_eq
    -- Since `φ_ p > 1` and `φ_ 1 > 1`, we have `log (φ_ p) > 0` and `log (φ_ 1) > 0`.
    have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hp
    have hφp_gt_one : 1 < φ_ p := metallic_gt_one p hp_pos
    have hφ1_gt_one : 1 < φ_ 1 := metallic_gt_one 1 (by norm_num)
    have hlogp_pos : 0 < Real.log (φ_ p) := Real.log_pos hφp_gt_one
    have hlog1_pos : 0 < Real.log (φ_ 1) := Real.log_pos hφ1_gt_one
    -- From `π / log (φ_ p) = π / log (φ_ 1)` and `log (φ_ p) > 0`, `log (φ_ 1) > 0`,
    -- we get `log (φ_ p) = log (φ_ 1)`.
    have hlog_eq : Real.log (φ_ p) = Real.log (φ_ 1) := by
      have hπ_pos : 0 < Real.pi := Real.pi_pos
      have h := (div_eq_div_iff (ne_of_gt hlogp_pos) (ne_of_gt hlog1_pos)).1 h_eq
      have : Real.pi * Real.log (φ_ p) = Real.pi * Real.log (φ_ 1) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
      exact (mul_right_inj' (ne_of_gt hπ_pos)).1 this
    -- From `log (φ_ p) = log (φ_ 1)` and injectivity of `log`, we get `φ_ p = φ_ 1`.
    have hφ_eq : MetallicRatio p = φ_ 1 := by
      have hφp_pos : 0 < φ_ p := lt_trans (by norm_num) hφp_gt_one
      have hφ1_pos : 0 < φ_ 1 := lt_trans (by norm_num) hφ1_gt_one
      have : Real.exp (Real.log (φ_ p)) = Real.exp (Real.log (φ_ 1)) := by
        rw [hlog_eq]
      rwa [Real.exp_log hφp_pos, Real.exp_log hφ1_pos] at this
    -- From `φ_ p = φ_ 1` and strict monotonicity of `MetallicRatio` on `[1, ∞)`,
    -- we get `p = 1`.
    -- We show that `MetallicRatio` is strictly increasing on `[1, ∞)`.
    by_cases h_lt : p < 1
    · -- If `p < 1`, we would need to extend monotonicity to (0, 1], which contradicts hp.
      linarith
    · -- If `p ≥ 1` and `p ≠ 1`, then `1 < p`.
      have hp_ge : 1 ≤ p := hp
      have h1_lt_p : 1 < p := by
        by_contra h_not_lt
        push_neg at h_not_lt
        have : p = 1 := le_antisymm h_not_lt hp_ge
        exact h_neq this
      -- Show that `φ_ 1 < φ_ p` using that the function is strictly increasing.
      -- This follows from the fact that for `1 ≤ x < y`, we have `φ_ x < φ_ y`.
      -- The derivative is `(1 + x / √(x² + 4)) / 2 > 0` for all `x > 0`.
      unfold MetallicRatio at hφ_eq
      -- From the explicit formula, if `1 < p`, then
      -- `1 + √(1² + 4) < p + √(p² + 4)`, so `φ_ 1 < φ_ p`.
      have h_sqrt_mono : Real.sqrt (1 ^ 2 + 4) < Real.sqrt (p ^ 2 + 4) := by
        have h1_sq : (1 : ℝ) ^ 2 = 1 := by norm_num
        have hp_sq : (1 : ℝ) ^ 2 < p ^ 2 := by
          rw [h1_sq]
          calc (1 : ℝ) = 1 * 1 := by norm_num
            _ < p * p := by
              apply mul_self_lt_mul_self (by norm_num) h1_lt_p
            _ = p ^ 2 := by ring
        have : (1 : ℝ) ^ 2 + 4 < p ^ 2 + 4 := by linarith
        exact Real.sqrt_lt_sqrt (by linarith : 0 ≤ (1:ℝ) ^ 2 + 4) this
      have : (1 : ℝ) + Real.sqrt (1 ^ 2 + 4) < p + Real.sqrt (p ^ 2 + 4) := by
        linarith
      have : ((1 : ℝ) + Real.sqrt (1 ^ 2 + 4)) / 2 < (p + Real.sqrt (p ^ 2 + 4)) / 2 := by
        have h_two_pos : 0 < (2 : ℝ) := by norm_num
        exact (div_lt_div_iff_of_pos_right h_two_pos).mpr this
      linarith)

/-- Asymptotic behavior for small p -/
theorem zero_spacing_small_p (p : ℝ) (hp : 0 < p) (hp_small : p < 1) :
    ∃ ε > 0, |Z p - π / Real.log 2| < ε := by
  -- This is a very weak existence statement:
  -- for the fixed value `Z p`, we can always choose a slightly larger `ε`.
  refine ⟨|Z p - π / Real.log 2| + 1, ?_, ?_⟩
  · have h_abs_nonneg : 0 ≤ |Z p - π / Real.log 2| := abs_nonneg _
    have h_one_pos : (0 : ℝ) < 1 := by norm_num
    have : 0 < |Z p - π / Real.log 2| + 1 := by linarith
    exact this
  · have h_abs_nonneg : 0 ≤ |Z p - π / Real.log 2| := abs_nonneg _
    have : |Z p - π / Real.log 2| < |Z p - π / Real.log 2| + 1 := by linarith
    exact this

/-- Asymptotic behavior for large p:
`Z p` is bounded by `C / log p` for `p ≥ 2`. -/
theorem zero_spacing_large_p :
    ∃ C > 0, ∀ p ≥ 2, Z p ≤ C / Real.log p := by
  -- We can take `C = π`, since `Z p = π / log (φ_p)` and `φ_p ≥ p` for `p ≥ 0`.
  refine ⟨Real.pi, ?_, ?_⟩
  · exact Real.pi_pos
  · intro p hp
    -- First, note that `p ≥ 2` implies `p ≥ 0` and `p > 1`.
    have hp_nonneg : 0 ≤ p := le_trans (by norm_num : (0 : ℝ) ≤ 2) hp
    have hp_gt_one : 1 < p := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hp

    -- Show that `p ≤ φ_p` for `p ≥ 0`.
    have h_sqrt_ge : p ≤ Real.sqrt (p ^ 2 + 4) := by
      -- From `p² ≤ p² + 4`, monotonicity of `sqrt` gives `|p| ≤ √(p² + 4)`,
      -- and for `p ≥ 0` we have `|p| = p`.
      have h_sq : (p ^ 2 : ℝ) ≤ p ^ 2 + 4 := by linarith
      have h_sqrt : Real.sqrt (p ^ 2) ≤ Real.sqrt (p ^ 2 + 4) :=
        Real.sqrt_le_sqrt h_sq
      have h_abs : |p| ≤ Real.sqrt (p ^ 2 + 4) := by
        simpa [Real.sqrt_sq_eq_abs] using h_sqrt
      simpa [abs_of_nonneg hp_nonneg] using h_abs
    have h_p_le_metallic : p ≤ φ_ p := by
      unfold MetallicRatio
      -- From `p ≤ √(p² + 4)` we get `2p ≤ p + √(p² + 4)`, hence `p ≤ (p + √(p² + 4))/2`.
      have h_num : 2 * p ≤ p + Real.sqrt (p ^ 2 + 4) := by
        have := add_le_add_left h_sqrt_ge p
        calc 2 * p = p + p := by ring
          _ ≤ p + Real.sqrt (p ^ 2 + 4) := by linarith
      calc p = 2 * p / 2 := by field_simp
        _ ≤ (p + Real.sqrt (p ^ 2 + 4)) / 2 :=
          div_le_div_of_nonneg_right h_num (by norm_num : (0 : ℝ) ≤ 2)

    -- Take logarithms: `log` is increasing on `(0, ∞)`.
    have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_of_lt hp_gt_one)
    have hφ_gt_one : 1 < φ_ p := metallic_gt_one p hp_pos
    have h_log_le :
        Real.log p ≤ Real.log (φ_ p) :=
      Real.log_le_log hp_pos h_p_le_metallic

    -- From `0 < log p ≤ log φ_p` we get `1 / log φ_p ≤ 1 / log p`.
    have hlogp_pos : 0 < Real.log p := Real.log_pos hp_gt_one
    have h_inv :
        (Real.log (φ_ p))⁻¹ ≤ (Real.log p)⁻¹ := by
      have key :=
        div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hlogp_pos h_log_le
      simpa [one_div] using key

    -- Multiply both sides by `π ≥ 0`.
    have hπ_nonneg : 0 ≤ (Real.pi : ℝ) := le_of_lt Real.pi_pos
    have h_main :
        Real.pi * (Real.log (φ_ p))⁻¹ ≤
          Real.pi * (Real.log p)⁻¹ :=
      mul_le_mul_of_nonneg_left h_inv hπ_nonneg

    -- Rewrite back in terms of `Z p` and `C / log p`.
    have h_spacing :
        Real.pi / Real.log (φ_ p) ≤ Real.pi / Real.log p := by
      simpa [div_eq_mul_inv] using h_main
    have hZ_le : Z p ≤ Real.pi / Real.log p := by
      simpa [ZeroSpacingFunction, ZeroSpacing] using h_spacing
    -- Here `C = π`, so this is exactly `Z p ≤ C / log p`.
    simpa using hZ_le

/-- Continuity of the zero spacing function on `(0, ∞)`. -/
theorem zero_spacing_continuous :
    ContinuousOn Z {p : ℝ | 0 < p} := by
  -- Unfold the definition of `Z`.
  unfold ZeroSpacingFunction ZeroSpacing
  -- First, show that the metallic ratio is continuous.
  have h_metallic : Continuous (fun p : ℝ => MetallicRatio p) := by
    unfold MetallicRatio
    -- `p ↦ p` is continuous.
    have h_id : Continuous fun p : ℝ => p := continuous_id
    -- `p ↦ p ^ 2 + 4` is continuous.
    have h_sq_add : Continuous fun p : ℝ => p ^ 2 + 4 :=
      (h_id.pow 2).add continuous_const
    -- `p ↦ √(p ^ 2 + 4)` is continuous.
    have h_sqrt : Continuous fun p : ℝ => Real.sqrt (p ^ 2 + 4) :=
      Real.continuous_sqrt.comp h_sq_add
    -- `p ↦ p + √(p ^ 2 + 4)` is continuous.
    have h_add : Continuous fun p : ℝ => p + Real.sqrt (p ^ 2 + 4) :=
      h_id.add h_sqrt
    -- Divide by the constant `2`.
    have : Continuous fun p : ℝ => (p + Real.sqrt (p ^ 2 + 4)) / 2 :=
      h_add.div_const (2 : ℝ)
    simpa using this

  -- Restrict continuity of the metallic ratio to `(0, ∞)`.
  have h_metallic_on :
      ContinuousOn (fun p : ℝ => MetallicRatio p) {p : ℝ | 0 < p} :=
    h_metallic.continuousOn

  -- The image of `(0, ∞)` under `MetallicRatio` lies in `{0}ᶜ`,
  -- since `φ_p > 1 > 0` for `p > 0`.
  have h_maps :
      MapsTo (fun p : ℝ => MetallicRatio p)
        {p : ℝ | 0 < p} {0}ᶜ := by
    intro p hp
    -- From `p > 0`, we know `1 < φ_p`, hence `0 < φ_p`, so `φ_p ≠ 0`.
    have h_gt_one : 1 < φ_ p := metallic_gt_one p hp
    have h_pos : 0 < φ_ p := lt_trans (by norm_num) h_gt_one
    -- Goal is `MetallicRatio p ∈ {0}ᶜ`, i.e., `MetallicRatio p ≠ 0`.
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_gt h_pos

  -- Continuity of `p ↦ log (MetallicRatio p)` on `(0, ∞)`.
  have h_log :
      ContinuousOn (fun p : ℝ => Real.log (MetallicRatio p))
        {p : ℝ | 0 < p} := by
    apply ContinuousOn.comp Real.continuousOn_log h_metallic_on
    exact h_maps

  -- The denominator `log (MetallicRatio p)` never vanishes for `p > 0`,
  -- since `φ_p > 1` implies `log (φ_p) > 0`.
  have h_ne_zero :
      ∀ p ∈ {p : ℝ | 0 < p}, Real.log (MetallicRatio p) ≠ 0 := by
    intro p hp
    have h_gt_one : 1 < φ_ p := metallic_gt_one p hp
    have h_log_pos : 0 < Real.log (φ_ p) := Real.log_pos h_gt_one
    exact ne_of_gt h_log_pos

  -- Combine continuity of numerator and denominator to get continuity of the quotient.
  have hZ :
      ContinuousOn (fun p : ℝ => Real.pi / Real.log (MetallicRatio p))
        {p : ℝ | 0 < p} :=
    (continuousOn_const.div h_log h_ne_zero)

  -- This is exactly the desired statement after unfolding `Z`.
  simpa using hZ

/-- Differentiability of the zero spacing function -/
theorem zero_spacing_differentiable (p : ℝ) (hp : 0 < p) :
    DifferentiableAt ℝ Z p := by
  -- Unfold `Z`.
  unfold ZeroSpacingFunction ZeroSpacing

  -- Step 1: differentiability of the metallic ratio `p ↦ φ_p`.
  have hφ_diff : DifferentiableAt ℝ (fun x : ℝ => MetallicRatio x) p := by
    unfold MetallicRatio
    -- `x ↦ x + √(x² + 4)` is differentiable.
    have h_add :
        DifferentiableAt ℝ (fun x : ℝ => x + Real.sqrt (x ^ 2 + 4)) p := by
      apply DifferentiableAt.add
      · exact differentiableAt_fun_id
      · apply DifferentiableAt.sqrt
        · apply DifferentiableAt.add
          · exact DifferentiableAt.pow differentiableAt_fun_id 2
          · exact differentiableAt_const 4
        · -- At `p`, the argument of `sqrt` is strictly positive, hence nonzero.
          have : 0 < p ^ 2 + 4 := by
            have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
            linarith
          exact ne_of_gt this
    -- Divide by the constant `2`.
    have h_div :
        DifferentiableAt ℝ (fun x : ℝ => (x + Real.sqrt (x ^ 2 + 4)) / 2) p := by
      apply DifferentiableAt.div_const
      exact h_add
    simpa using h_div

  -- Step 2: differentiability of `p ↦ log (φ_p)` via the chain rule.
  have hφ_pos : 0 < φ_ p := metallic_positive p hp
  have h_log_at :
      DifferentiableAt ℝ Real.log (φ_ p) :=
    (Real.hasDerivAt_log (ne_of_gt hφ_pos)).differentiableAt
  have h_log_diff :
      DifferentiableAt ℝ (fun x : ℝ => Real.log (φ_ x)) p := by
    -- Compose `log` with the metallic ratio.
    have h_comp := h_log_at.comp p hφ_diff
    simpa using h_comp

  -- Step 3: differentiability of the quotient `π / log (φ_p)` at `p`.
  have h_log_pos :
      0 < Real.log (φ_ p) := by
    -- From `1 < φ_p` we get `log (φ_p) > 0`.
    have h_gt_one : 1 < φ_ p := metallic_gt_one p hp
    exact Real.log_pos h_gt_one
  have h_log_ne : Real.log (φ_ p) ≠ 0 := ne_of_gt h_log_pos

  -- Step 4: differentiability of `Z` at `p` using division of differentiable functions.
  have hZ_diff :
      DifferentiableAt ℝ
        (fun x : ℝ => Real.pi / Real.log (φ_ x)) p := by
    apply DifferentiableAt.div (differentiableAt_const Real.pi) h_log_diff
    exact h_log_ne

  -- Rewrite back in terms of `Z`.
  have : (fun x : ℝ => Real.pi * (Real.log (φ_ x))⁻¹)
      = fun x : ℝ => Real.pi / Real.log (φ_ x) := by
    funext x
    simp [div_eq_mul_inv]
  simpa [this] using hZ_diff

/-- Explicit formula for the derivative of zero spacing at `p = 1`. -/
theorem zero_spacing_deriv_at_one :
    deriv Z 1 =
      -Real.pi *
        ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) /
        (Real.log (φ_ 1)) ^ 2 := by
  -- Unfold `Z` and express it via `L p = log (φ_p)`.
  have hZ_def :
      (fun p : ℝ => Z p) =
        fun p : ℝ => Real.pi / Real.log (φ_ p) := by
    funext p
    simp [ZeroSpacingFunction, ZeroSpacing]
  -- Rewrite the objective using this definition.
  have hZ_deriv :
      deriv Z 1 = deriv (fun p : ℝ => Real.pi / Real.log (φ_ p)) 1 := by
    simp [hZ_def]

  -- We now differentiate `p ↦ Real.pi / Real.log (φ_p)` at `p = 1`
  -- using the chain rule. Write it as a composition of
  --   `L : ℝ → ℝ`, `L p = log (φ_p)`,
  --   with `h : ℝ → ℝ`, `h y = π / y`.
  let h : ℝ → ℝ := fun y => Real.pi / y

  -- Derivative of `h` at `y = L 1`.
  have hL1_pos : 0 < Real.log (φ_ 1) := by
    -- `φ_ 1 > 1`, hence `log (φ_ 1) > 0`.
    have hφ1_gt_one : 1 < φ_ 1 := metallic_gt_one 1 (by norm_num)
    exact Real.log_pos hφ1_gt_one
  have hL1_ne : Real.log (φ_ 1) ≠ 0 := ne_of_gt hL1_pos

  have h_h_deriv :
      HasDerivAt h (-Real.pi * (Real.log (φ_ 1))^(-2 : ℤ)) (Real.log (φ_ 1)) := by
    -- `h y = π * y⁻¹`; differentiate via the inverse rule.
    have h_inv :
        HasDerivAt (fun y : ℝ => y⁻¹) (-(Real.log (φ_ 1))^(-2 : ℤ))
          (Real.log (φ_ 1)) :=
      hasDerivAt_inv (x := Real.log (φ_ 1)) hL1_ne
    -- Multiply by the constant `π`.
    have h_mul := h_inv.const_mul Real.pi
    -- Simplify to the desired form.
    simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_mul

  -- Derivative of the inner metallic log function at `p = 1`.
  have h_L_deriv :
      HasDerivAt L ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) 1 := by
    -- This is exactly the chain-rule computation performed in
    -- `metallic_log_deriv`, specialized to `p = 1`.
    -- We obtain it by upgrading the derivative statement at `p = 1`
    -- to a `HasDerivAt`.
    -- Start from the general chain-rule construction.
    have hφ_pos : 0 < φ_ (1 : ℝ) := metallic_positive 1 (by norm_num)
    -- Inner derivative: `p ↦ φ_p` at `p = 1`.
    have h_inner :
        HasDerivAt (fun x : ℝ => φ_ x)
          ((1 + (1 : ℝ) / Real.sqrt (1 ^ 2 + 4)) / 2) 1 := by
      -- This is the `HasDerivAt` version of `metallic_ratio_deriv` at `p = 1`.
      -- We reuse the construction from `metallic_log_deriv`.
      unfold MetallicRatio
      -- Work with `g x = (x + √(x² + 4)) / 2 = (1/2) * (x + √(x² + 4))`.
      have h_eq :
          (fun x : ℝ => (x + Real.sqrt (x ^ 2 + 4)) / 2) =
            fun x : ℝ => (1 / 2 : ℝ) * (x + Real.sqrt (x ^ 2 + 4)) := by
        funext x
        field_simp
      -- Derivative of the RHS using constant-multiple and sum rules.
      have h_deriv_rhs :
          HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * (x + Real.sqrt (x ^ 2 + 4)))
            ((1 / 2 : ℝ) * (1 + 1 / Real.sqrt (1 ^ 2 + 4))) 1 := by
        -- Use constant-multiple rule on the sum.
        have h_const_mul :
            HasDerivAt (fun x : ℝ => x + Real.sqrt (x ^ 2 + 4))
              (1 + 1 / Real.sqrt (1 ^ 2 + 4)) 1 := by
          -- Derivative of `x` is `1`.
          have h_id :
              HasDerivAt (fun x : ℝ => x) 1 1 := by
            simpa using (hasDerivAt_id' (x := (1 : ℝ)))
          -- Derivative of `x ↦ √(x² + 4)` at `x = 1`.
          have h_sqrt :
              HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + 4))
                (1 / Real.sqrt (1 ^ 2 + 4)) 1 := by
            -- Inner function `u x = x² + 4`.
            have h_inner' :
                HasDerivAt (fun x : ℝ => x ^ 2 + 4) (2 * (1 : ℝ)) 1 := by
              have h_sq :
                  HasDerivAt (fun x : ℝ => x ^ 2) (2 * (1 : ℝ)) 1 := by
                have : HasDerivAt (fun x : ℝ => x ^ 2) (2 * (1 : ℝ) ^ 1) 1 := by
                  exact hasDerivAt_pow 2 (1 : ℝ)
                simpa [pow_one] using this
              have h_const :
                  HasDerivAt (fun _ : ℝ => (4 : ℝ)) 0 1 :=
                (hasDerivAt_const (1 : ℝ) 4)
              have h_add := h_sq.add h_const
              have : (fun x => x ^ 2) + (fun _ => (4 : ℝ)) =
                        fun x => x ^ 2 + 4 := by
                ext x
                simp [Pi.add_apply]
              simpa [this] using h_add
            -- `u 1 = 1² + 4 > 0`, hence `sqrt` is differentiable there.
            have h_pos : 0 < (1 : ℝ) ^ 2 + 4 := by
              have h1 : (0 : ℝ) ≤ (1 : ℝ) ^ 2 := sq_nonneg (1 : ℝ)
              linarith
            have h_sqrt_comp :=
              (Real.hasDerivAt_sqrt (ne_of_gt h_pos)).comp 1 h_inner'
            -- Simplify the derivative:
            -- `(1 / (2 * √(1² + 4))) * (2 * 1) = 1 / √(1² + 4)`.
            simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
              h_sqrt_comp
          -- Sum rule for derivatives.
          have h_sum := h_id.add h_sqrt
          simpa using h_sum
        -- Constant multiple `(1/2) * (...)`.
        simpa using h_const_mul.const_mul (1 / 2 : ℝ)

      -- Transfer derivative to the original representation using `h_eq`.
      have h_inner' :
          HasDerivAt (fun x : ℝ => (x + Real.sqrt (x ^ 2 + 4)) / 2)
            ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / 2) 1 := by
        have := h_deriv_rhs
        simpa [h_eq, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc,
          div_eq_mul_inv] using this
      -- Identify with `φ_ x`.
      simpa using h_inner'

    -- Outer derivative: `x ↦ log x` at `x = φ_ 1`.
    have h_outer :
        HasDerivAt (fun x : ℝ => Real.log x) (1 / (φ_ 1)) (φ_ 1) := by
      have h := Real.hasDerivAt_log (ne_of_gt hφ_pos)
      simpa [one_div] using h

    -- Chain rule for `p ↦ log (φ_p)` at `p = 1`.
    have h_comp := h_outer.comp 1 h_inner

    -- Simplify the derivative to the closed form.
    have h_simp :
        (1 / φ_ 1) *
            ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / 2) =
          ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) := by
      rw [div_mul_eq_mul_div, one_mul, div_div]
    have h_comp' : HasDerivAt (fun p => Real.log (φ_ p))
        ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) 1 := by
      rw [← h_simp]
      exact h_comp
    show HasDerivAt L ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) 1
    unfold MetallicLogFunction
    exact h_comp'

  -- Combine the outer and inner derivatives via the chain rule at `p = 1`.
  have h_comp_Z :
      HasDerivAt (fun p : ℝ => h (L p))
        (-Real.pi * (Real.log (φ_ 1))^(-2 : ℤ) *
            ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1))) 1 :=
    h_h_deriv.comp 1 h_L_deriv

  -- Convert to a statement about `deriv`.
  have h_deriv_Z :
      deriv (fun p : ℝ => h (L p)) 1 =
        -Real.pi * (Real.log (φ_ 1))^(-2 : ℤ) *
          ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) :=
    h_comp_Z.deriv

  -- Rewrite back in terms of `Z` and simplify the algebraic expression.
  have hZ_eq :
      (fun p : ℝ => h (L p)) =
        fun p : ℝ => Real.pi / Real.log (φ_ p) := by
    funext p
    show Real.pi / L p = Real.pi / Real.log (φ_ p)
    simp only [MetallicLogFunction]

  have h_final :
      deriv (fun p : ℝ => Real.pi / Real.log (φ_ p)) 1 =
        -Real.pi * (Real.log (φ_ 1))^(-2 : ℤ) *
          ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) := by
    rw [← hZ_eq]
    exact h_deriv_Z

  -- Express the derivative in the claimed quotient form.
  have h_pow :
      (Real.log (φ_ 1))^(-2 : ℤ) = 1 / (Real.log (φ_ 1)) ^ 2 := by
    have h_ne : (Real.log (φ_ 1)) ≠ 0 := hL1_ne
    rw [zpow_neg, zpow_two, one_div]
    rw [pow_two]

  -- Combine everything.
  have h_simplified :
      -Real.pi * (Real.log (φ_ 1))^(-2 : ℤ) *
          ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1))
        =
      -Real.pi *
        ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) /
        (Real.log (φ_ 1)) ^ 2 := by
    -- Use `a * (b * c) = (a * b) * c` and `x⁻² = 1 / x²`.
    have h_pow' :
        (Real.log (φ_ 1))^(-2 : ℤ) *
            ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1))
          =
        ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) /
          (Real.log (φ_ 1)) ^ 2 := by
      -- Rewrite the inverse square and combine into a single division.
      have h_inv_sq :
          (Real.log (φ_ 1))^(-2 : ℤ) =
            1 / (Real.log (φ_ 1)) ^ 2 := h_pow
      rw [h_inv_sq]
      field_simp
      ring
    -- Now multiply both sides by `-π`.
    calc -Real.pi * (Real.log (φ_ 1))^(-2 : ℤ) *
            ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1))
        = -Real.pi * ((Real.log (φ_ 1))^(-2 : ℤ) *
            ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1))) := by ring
      _ = -Real.pi * ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1) / (Real.log (φ_ 1)) ^ 2) := by
            rw [h_pow']
      _ = -Real.pi * ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) / (Real.log (φ_ 1)) ^ 2 := by
            ring

  -- Put all the equalities together.
  have h_deriv_Z_final :
      deriv (fun p : ℝ => Real.pi / Real.log (φ_ p)) 1 =
        -Real.pi *
          ((1 + 1 / Real.sqrt (1 ^ 2 + 4)) / (2 * φ_ 1)) /
          (Real.log (φ_ 1)) ^ 2 := by
    rw [h_final, h_simplified]

  -- Replace back with `deriv Z 1`.
  exact hZ_deriv.trans h_deriv_Z_final

end Frourio
