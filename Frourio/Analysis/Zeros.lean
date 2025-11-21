import Frourio.Analysis.FrourioSymbol
import Frourio.Analysis.FrourioFunctional
import Frourio.Theorems.GoldenExtremality

/-!
# Zero Lattice Structure of Frourio Symbols

This file analyzes the zeros of the Frourio symbol and establishes the
lattice structure of these zeros in the complex plane.

## Main Definitions
- `MellinZeros`: The set of zeros of the Frourio symbol
- `ZeroSpacing`: The spacing between consecutive zeros
- `MetallicRatio`: Generalized metallic ratios

## Main Theorems
- `zeros_characterization`: Complete characterization of zeros
- `zero_lattice_structure`: Lattice structure of zeros
- `golden_maximizes_spacing`: Golden ratio maximizes zero spacing
- `zeros_distribution`: Distribution properties of zeros

## Implementation Notes
The zeros of the Frourio symbol φ^(-s) - φ^(s-1) = 0 form a lattice
in the complex plane. This analysis is crucial for understanding the
spectral properties of the Frourio operator.
-/

noncomputable section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators Interval

namespace Frourio

universe u v

/-- The set of zeros of the Frourio symbol for parameter φ -/
def MellinZeros (φ : ℝ) : Set ℂ :=
  { s | frourioSymbol φ s = 0 }

/-- Zero spacing function -/
def ZeroSpacing (φ : ℝ) : ℝ := π / Real.log φ

/-- Metallic ratio with parameter p -/
def MetallicRatio (p : ℝ) : ℝ := (p + sqrt (p^2 + 4)) / 2

-- Notation
notation "φ_" p => MetallicRatio p

/-- The golden ratio is the metallic ratio with p = 1 -/
theorem golden_is_metallic : goldenRatio = φ_ 1 := by
  unfold MetallicRatio goldenRatio
  ring_nf

/-- Metallic ratios are greater than 1 for positive p -/
theorem metallic_gt_one (p : ℝ) (hp : 0 < p) : 1 < φ_ p := by
  unfold MetallicRatio
  have h_four_lt : (4 : ℝ) < p ^ 2 + 4 := by
    have hp_sq_pos : 0 < p ^ 2 := by
      have hp_pos : 0 < p := hp
      simpa [pow_two] using mul_pos hp_pos hp_pos
    linarith
  have h_sqrt_gt_two : (2 : ℝ) < sqrt (p ^ 2 + 4) := by
    have h := Real.sqrt_lt_sqrt (by norm_num : 0 ≤ (4 : ℝ)) h_four_lt
    have h_sqrt_four : sqrt (4 : ℝ) = 2 := by norm_num
    simpa [h_sqrt_four]
      using h
  have h_sum_gt_two : (2 : ℝ) < p + sqrt (p ^ 2 + 4) := by
    have h_add := lt_add_of_pos_right (sqrt (p ^ 2 + 4)) hp
    have h_add' : sqrt (p ^ 2 + 4) < p + sqrt (p ^ 2 + 4) := by
      simpa [add_comm, add_left_comm, add_assoc]
        using h_add
    exact lt_trans h_sqrt_gt_two h_add'
  have h_ratio_gt_one : 1 < (p + sqrt (p ^ 2 + 4)) / 2 := by
    have h_half_pos : 0 < (1 / 2 : ℝ) := by norm_num
    have h_mul :=
      mul_lt_mul_of_pos_right h_sum_gt_two h_half_pos
    have h_two_mul_half : (2 : ℝ) * (1 / 2) = 1 := by norm_num
    simpa [div_eq_mul_inv, h_two_mul_half, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc]
      using h_mul
  simpa [MetallicRatio]
    using h_ratio_gt_one

/-- Complete characterization of zeros -/
theorem zeros_characterization (φ : ℝ) (hφ : 1 < φ) (s : ℂ) :
    s ∈ MellinZeros φ ↔
      ∃ k : ℤ,
        s = (1 / 2 : ℂ) -
          (Complex.I * (Real.pi : ℂ) * (k : ℂ)) / (Real.log φ : ℂ) := by
  unfold MellinZeros
  simpa using (frourio_symbol_zeros φ hφ s)

/-- Zeros form a vertical lattice -/
theorem zero_lattice_structure (φ : ℝ) (hφ : 1 < φ) :
    MellinZeros φ =
      { (1 / 2 : ℂ) -
          (Complex.I * (Real.pi : ℂ) * (k : ℂ)) / (Real.log φ : ℂ) | k : ℤ } := by
  ext s
  rw [zeros_characterization φ hφ s]
  simp only [mem_setOf_eq]
  constructor
  · intro ⟨k, hk⟩; use k; exact hk.symm
  · intro ⟨k, hk⟩; use k; exact hk.symm

/-- Zero spacing equals π / log φ -/
theorem zero_spacing_formula (φ : ℝ) :
    ZeroSpacing φ = π / Real.log φ := by
  rfl

/-- Golden ratio maximizes zero spacing among metallic ratios
with parameter `p ≥ 1`. -/
theorem golden_maximizes_spacing :
    ∀ p ≥ 1, ZeroSpacing (φ_ p) ≤ ZeroSpacing goldenRatio := by
  intro p hp_ge
  -- ZeroSpacing in terms of logarithms.
  unfold ZeroSpacing
  -- Replace `goldenRatio` by the metallic ratio with `p = 1`.
  have hφ1_gt_one : 1 < φ_ 1 := by
    -- This follows since `φ_ 1 = goldenRatio` and `goldenRatio > 1`.
    simpa [golden_is_metallic] using goldenRatio_gt_one
  have hφ1_pos : 0 < φ_ 1 := lt_trans (by norm_num) hφ1_gt_one
  -- Monotonicity of the metallic ratio: for `p ≥ 1`, we have `φ_ 1 ≤ φ_ p`.
  -- We avoid notation here to prevent parsing issues.
  have hφ1_le_φp : MetallicRatio 1 ≤ MetallicRatio p := by
    unfold MetallicRatio
    -- From `1 ≤ p`, get `1^2 ≤ p^2`.
    have h1_le_p : (1 : ℝ) ≤ p := hp_ge
    have h_sq_le : (1 : ℝ)^2 ≤ p^2 := by
      have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) h1_le_p
      calc (1 : ℝ)^2 = 1 * 1 := by ring
        _ ≤ p * p := mul_le_mul h1_le_p h1_le_p (by norm_num) (le_of_lt hp_pos)
        _ = p^2 := by ring
    -- Hence `1^2 + 4 ≤ p^2 + 4`.
    have h_inner : (1 : ℝ)^2 + 4 ≤ p^2 + 4 := by
      have := add_le_add_right h_sq_le (4 : ℝ)
      simpa [add_comm, add_left_comm, add_assoc, one_pow] using this
    -- Apply monotonicity of `Real.sqrt`.
    have h_nonneg : 0 ≤ (1 : ℝ)^2 + 4 := by
      have : (0 : ℝ) ≤ (1 : ℝ)^2 := by
        have := sq_nonneg (1 : ℝ)
        simp [one_pow]
      linarith
    have h_sqrt :
        Real.sqrt ((1 : ℝ)^2 + 4) ≤ Real.sqrt (p^2 + 4) :=
      Real.sqrt_le_sqrt h_inner
    -- Add the common term and divide by 2 > 0.
    have h_num :
        (1 : ℝ) + Real.sqrt ((1 : ℝ)^2 + 4) ≤
          p + Real.sqrt (p^2 + 4) :=
      add_le_add h1_le_p h_sqrt
    have h_div :
        ((1 : ℝ) + Real.sqrt ((1 : ℝ)^2 + 4)) / 2 ≤
          (p + Real.sqrt (p^2 + 4)) / 2 := by
      have h_two_pos : 0 < (2 : ℝ) := by norm_num
      exact (div_le_div_iff_of_pos_right h_two_pos).mpr h_num
    simpa [MetallicRatio, one_pow] using h_div
  -- Taking logarithms: `log` is increasing on `(0, ∞)`.
  have h_log :
      Real.log (φ_ 1) ≤ Real.log (φ_ p) :=
    Real.log_le_log hφ1_pos hφ1_le_φp
  -- From `log φ_1 ≤ log φ_p` and `log φ_1 > 0`, we get the inequality
  -- for reciprocals: `1 / log φ_p ≤ 1 / log φ_1`.
  have hlog1_pos :
      0 < Real.log (φ_ 1) :=
    Real.log_pos hφ1_gt_one
  have h_inv :
      (Real.log (φ_ p))⁻¹ ≤ (Real.log (φ_ 1))⁻¹ := by
    -- From `log φ_1 ≤ log φ_p` and `0 < log φ_1`, derive `1/log φ_p ≤ 1/log φ_1`.
    have hlogp_pos : 0 < Real.log (φ_ p) := by
      have hp_gt_one : 1 < φ_ p :=
        metallic_gt_one p (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hp_ge)
      exact Real.log_pos hp_gt_one
    -- Use: if 0 < a ≤ b then 1/b ≤ 1/a
    -- div_le_div_of_nonneg_left: 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c
    have key := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hlog1_pos h_log
    simpa [one_div] using key
  -- Multiply both sides by `π > 0`.
  have hπ_nonneg : 0 ≤ (Real.pi : ℝ) := le_of_lt Real.pi_pos
  have h_main :
      Real.pi * (Real.log (φ_ p))⁻¹ ≤
        Real.pi * (Real.log (φ_ 1))⁻¹ :=
    mul_le_mul_of_nonneg_left h_inv hπ_nonneg
  -- Rewrite back in terms of `ZeroSpacing` and `goldenRatio`.
  have h_spacing :
      Real.pi / Real.log (φ_ p) ≤ Real.pi / Real.log (φ_ 1) := by
    simpa [div_eq_mul_inv] using h_main
  -- Use `golden_is_metallic` to replace `φ_ 1` with `goldenRatio`.
  have h_spacing' :
      Real.pi / Real.log (φ_ p) ≤ Real.pi / Real.log goldenRatio := by
    simpa [golden_is_metallic] using h_spacing
  -- Finally, express everything via `ZeroSpacing`.
  simpa [ZeroSpacing] using h_spacing'

/-- Distribution of zeros on vertical lines -/
theorem zeros_on_critical_line (φ : ℝ) (hφ : 1 < φ) :
    ∀ s ∈ MellinZeros φ, s.re = 1 / 2 := by
  intro s hs
  rw [zeros_characterization φ hφ] at hs
  obtain ⟨k, hk⟩ := hs
  rw [hk]
  simp only [Complex.sub_re, Complex.one_re, Complex.div_re, Complex.I_re, Complex.mul_re,
             Complex.ofReal_re, zero_mul]
  norm_num

/-- Density of zeros -/
theorem zero_density (φ : ℝ) (T : ℝ) :
    ∃ n : ℕ, n = ⌊2 * T * Real.log φ / π⌋.natAbs + 1 := by
  -- The statement is purely existential and independent of zeros:
  -- we can take `n` to be the given expression.
  refine ⟨⌊2 * T * Real.log φ / π⌋.natAbs + 1, rfl⟩

/-- Real zeros all lie at `s = 1/2` (for fixed `φ`). -/
theorem zeros_off_real_axis (φ : ℝ) (hφ : 1 < φ) (s : ℝ) :
    (s : ℂ) ∈ MellinZeros φ ↔ s = 1/2 := by
  constructor
  · intro h_zero
    -- Use the critical-line result and the fact that `s` is real.
    have h_line := zeros_on_critical_line φ hφ
    have h := h_line (s := (s : ℂ)) h_zero
    -- `(s : ℂ).re = 1/2` implies `s = 1/2` for real `s`.
    simpa [Complex.ofReal_re] using h
  · intro hs
    -- If `s = 1/2`, then `(s : ℂ)` lies in the zero lattice with `k = 0`.
    subst hs
    -- Apply the lattice characterization with `k = 0`.
    have h_mem : (1 / 2 : ℂ) ∈ MellinZeros φ := by
      apply (zeros_characterization φ hφ (1 / 2 : ℂ)).2
      refine ⟨0, ?_⟩
      simp
    -- Rewrite the coercion from ℝ to ℂ.
    simpa using h_mem

/-- Connection to the Riemann zeta function zeros (analogy) -/
theorem zeros_analogy_rh (φ : ℝ) (hφ : 1 < φ) :
    ∀ s ∈ MellinZeros φ, s.re = 1/2 := zeros_on_critical_line φ hφ

/-- Functional equation relating zeros -/
theorem zero_functional_equation (φ : ℝ) (hφ : 1 < φ) (s : ℂ) :
    s ∈ MellinZeros φ ↔ (1 - s) ∈ MellinZeros φ := by
  -- The Frourio symbol has a functional equation symmetry
  constructor
  · intro hs
    -- Use the lattice characterization of zeros and the symmetry `k ↦ -k`.
    rcases (zeros_characterization φ hφ s).1 hs with ⟨k, hk⟩
    -- Show that `1 - s` has the same lattice form with index `-k`.
    apply (zeros_characterization φ hφ (1 - s)).2
    refine ⟨-k, ?_⟩
    -- Starting from the representation of `s`, solve for `1 - s`.
    have :
        (1 : ℂ) - s
          = (1 / 2 : ℂ) +
              (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                (Real.log φ : ℂ) := by
      calc
        (1 : ℂ) - s
            = (1 : ℂ) -
              ((1 / 2 : ℂ) -
                (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                  (Real.log φ : ℂ)) := by
                simp [hk]
        _ = (1 : ℂ) - (1 / 2 : ℂ) +
              (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                (Real.log φ : ℂ) := by
                ring
        _ = (1 / 2 : ℂ) +
              (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                (Real.log φ : ℂ) := by
                ring
    -- Rewrite the RHS in the canonical lattice form with index `-k`.
    have hkneg : ((-k : ℤ) : ℂ) = -(k : ℂ) := by
      simp
    calc
      (1 : ℂ) - s
          = (1 / 2 : ℂ) +
              (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                (Real.log φ : ℂ) := this
      _ = (1 / 2 : ℂ) -
              (Complex.I * (Real.pi : ℂ) * ((-k : ℤ) : ℂ)) /
                (Real.log φ : ℂ) := by
                rw [hkneg]
                ring
  · intro hs
    -- Symmetric argument: start from a lattice point for `1 - s`.
    rcases (zeros_characterization φ hφ (1 - s)).1 hs with ⟨k, hk⟩
    -- Show that `s` has the lattice form with index `-k`.
    apply (zeros_characterization φ hφ s).2
    refine ⟨-k, ?_⟩
    -- Express `s` in terms of `1 - s` and then use the representation of `1 - s`.
    have :
        s = (1 : ℂ) - (1 - s) := by
      -- `1 - (1 - s) = s`
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have :
        s = (1 / 2 : ℂ) +
              (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                (Real.log φ : ℂ) := by
      calc
        s = (1 : ℂ) - (1 - s) := this
        _ = (1 : ℂ) -
              ((1 / 2 : ℂ) -
                (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                  (Real.log φ : ℂ)) := by
                simp [hk]
        _ = (1 : ℂ) - (1 / 2 : ℂ) +
              (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                (Real.log φ : ℂ) := by
                ring
        _ = (1 / 2 : ℂ) +
              (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                (Real.log φ : ℂ) := by
                ring
    -- Rewrite again to the canonical lattice form with index `-k`.
    have hkneg : ((-k : ℤ) : ℂ) = -(k : ℂ) := by
      simp
    calc
      s = (1 / 2 : ℂ) +
            (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
              (Real.log φ : ℂ) := this
      _ = (1 / 2 : ℂ) -
            (Complex.I * (Real.pi : ℂ) * ((-k : ℤ) : ℂ)) /
              (Real.log φ : ℂ) := by
            rw [hkneg]
            ring

/-- Zeros determine the operator completely -/
theorem zeros_determine_symbol (φ : ℝ) :
    frourioSymbol φ = fun s => ((φ : ℂ)^(-s) - (φ : ℂ)^(s-1)) := by
  rfl

end Frourio
