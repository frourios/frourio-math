/-
Copyright (c) 2025 Frourio Math Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frourio Math Project
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Density of Schwartz functions in Lp spaces

This file contains fundamental density theorems about Schwartz functions
in Lp spaces, which are standard results in harmonic analysis.

## Main results

- `schwartz_dense_Lp`: Schwartz functions are dense in Lp(ℝⁿ) for 1 ≤ p < ∞
- `schwartz_dense_L1_L2_simultaneous`: Simultaneous approximation in L¹ and L²
- `continuous_compactSupport_dense_Lp`: Cc(ℝⁿ) is dense in Lp
- `smooth_compactSupport_dense_Lp`: C∞c(ℝⁿ) is dense in Lp

## References

Standard textbooks covering these results:
- Stein & Shakarchi, "Functional Analysis", Chapter 4
- Folland, "Real Analysis", Chapter 8
- Rudin, "Functional Analysis", Chapter 1
- Grafakos, "Classical Fourier Analysis", Chapter 2
- Reed & Simon, "Methods of Modern Mathematical Physics I", Section II.3

The density of Schwartz functions (or C∞c) in Lp is a cornerstone result
used throughout harmonic analysis and PDE theory.
-/

open MeasureTheory SchwartzMap
open scoped ENNReal

variable {n : ℕ}

/--
**Schwartz functions are dense in Lp for 1 ≤ p < ∞.**

This is Theorem 4.1.2 in Stein & Shakarchi, "Functional Analysis".
Also appears as Theorem 8.16 in Folland, "Real Analysis".

For any f ∈ Lp(ℝⁿ) with 1 ≤ p < ∞ and any ε > 0, there exists
a Schwartz function φ such that ‖f - φ‖_p < ε.

## Mathematical content

The proof typically proceeds in stages:
1. Simple functions are dense in Lp
2. Continuous compactly supported functions approximate simple functions
3. Mollification (convolution with smooth approximation to identity)
   produces smooth compactly supported functions
4. Smooth compactly supported functions can be made rapidly decreasing

This is one of the most fundamental approximation theorems in analysis.
-/
theorem schwartz_dense_Lp
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ),
      eLpNorm (fun x => f x - φ x) p volume < ENNReal.ofReal ε := by
  sorry

/--
**Simultaneous approximation in L¹ and L².**

If f ∈ L¹(ℝⁿ) ∩ L²(ℝⁿ), then for any ε > 0, there exists a Schwartz
function φ such that both:
- ‖f - φ‖₁ < ε
- ‖f - φ‖₂ < ε

This is the key result needed for proving the Plancherel theorem.

## Mathematical content

This follows from the single-Lp density theorem by choosing a Schwartz
function φ that approximates f in L² norm. Since Schwartz functions are
in all Lp spaces, φ is automatically in L¹. The L¹ approximation then
follows from:
- For the part where both f and φ are small in L², use Hölder/Cauchy-Schwarz
- For the tail where f is small, control is already given

The key insight is that Schwartz functions are simultaneously in all Lp spaces,
so one good approximation works for all norms.
-/
theorem schwartz_dense_L1_L2_simultaneous
    (f : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 (volume : Measure (Fin n → ℝ)))
    (hf_L2 : MemLp f 2 (volume : Measure (Fin n → ℝ)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ),
      eLpNorm (fun x => f x - φ x) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun x => f x - φ x) 2 volume < ENNReal.ofReal ε := by
  sorry

/--
**Continuous compactly supported functions are dense in Lp.**

This is Theorem 3.14 in Rudin, "Real and Complex Analysis".
Also Theorem 8.14 in Folland, "Real Analysis".

For any f ∈ Lp(ℝⁿ) with 1 ≤ p < ∞ and any ε > 0, there exists
a continuous function g with compact support such that ‖f - g‖_p < ε.
-/
theorem continuous_compactSupport_dense_Lp
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℂ,
      Continuous g ∧
      HasCompactSupport g ∧
      MemLp g p volume ∧
      eLpNorm (f - g) p volume < ENNReal.ofReal ε := by
  sorry

/--
**C∞ compactly supported functions are dense in Lp.**

This is Corollary 8.15 in Folland, "Real Analysis".
Also appears in Reed & Simon, "Methods of Modern Mathematical Physics I", Theorem II.17.

For any f ∈ Lp(ℝⁿ) with 1 ≤ p < ∞ and any ε > 0, there exists
a C∞ function g with compact support such that ‖f - g‖_p < ε.

## Proof strategy

This follows from continuous compactly supported density plus mollification:
1. First approximate f by continuous compactly supported g
2. Then mollify g (convolve with smooth approximation to identity)
3. For small mollification parameter, the smooth approximation is close in Lp
-/
theorem smooth_compactSupport_dense_Lp
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℂ,
      ContDiff ℝ ⊤ g ∧
      HasCompactSupport g ∧
      MemLp g p volume ∧
      eLpNorm (f - g) p volume < ENNReal.ofReal ε := by
  sorry

/--
**Variant for ℝ (n=1 case) with simultaneous L¹ and L² control.**

This is the specific instance needed for the Plancherel theorem on ℝ.

Given f ∈ L¹(ℝ) ∩ L²(ℝ), we can approximate it simultaneously in both norms
by a smooth compactly supported function.
-/
theorem smooth_compactSupport_dense_L1_L2_real
    (f : ℝ → ℂ)
    (hf_L1 : Integrable f volume)
    (hf_L2 : MemLp f 2 volume)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ ⊤ g ∧
      HasCompactSupport g ∧
      eLpNorm (f - g) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (f - g) 2 volume < ENNReal.ofReal ε := by
  sorry

/--
**Variant: approximation by continuous compactly supported with both L¹ and L² bounds.**

For f ∈ L¹(ℝ) ∩ L²(ℝ), we can find continuous compactly supported g
such that both ‖f - g‖₁ < ε and ‖f - g‖₂ < ε.

This is the exact statement needed in FourierPlancherelL2.lean.
-/
theorem continuous_compactSupport_dense_L1_L2_real
    (f : ℝ → ℂ)
    (hf_L1 : Integrable f volume)
    (hf_L2 : MemLp f 2 volume)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      Continuous g ∧
      HasCompactSupport g ∧
      MemLp g 2 volume ∧
      eLpNorm (f - g) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (f - g) 2 volume < ENNReal.ofReal ε := by
  sorry

/--
**Lusin's theorem for Lp functions.**

This is a consequence of the density theorem and can be useful for
understanding the approximation procedure.

For f ∈ Lp and ε > 0, there exists a continuous compactly supported g
such that the set {x : f(x) ≠ g(x)} has measure < ε.
-/
theorem lusin_type_approximation_Lp
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∃ g : (Fin n → ℝ) → ℂ,
      Continuous g ∧
      HasCompactSupport g ∧
      eLpNorm (f - g) p volume < ENNReal.ofReal ε ∧
      volume {x | f x ≠ g x} < ENNReal.ofReal δ := by
  sorry

/--
**Approximation preserving positivity.**

If f ≥ 0 almost everywhere, then the approximating function can also
be chosen to be non-negative.

This is useful in probability theory and analysis of positive operators.
-/
theorem smooth_compactSupport_dense_Lp_nonneg
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    (hf_nonneg : ∀ᵐ x ∂volume, 0 ≤ f x)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℝ,
      ContDiff ℝ ⊤ g ∧
      HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧
      eLpNorm (fun x => f x - g x) p volume < ENNReal.ofReal ε := by
  sorry
