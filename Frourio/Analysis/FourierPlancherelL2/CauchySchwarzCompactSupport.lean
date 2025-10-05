import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.Algebra.Support

/-!
# Cauchy-Schwarz inequality for compactly supported functions

This file contains the standard textbook result relating L¹ and L² norms
for functions with compact support.

## Main results

- `eLpNorm_one_le_eLpNorm_two_mul_sqrt_measure`: The fundamental inequality
  ‖f‖₁ ≤ ‖f‖₂ · √(μ(support f)) for compactly supported functions.

- `eLpNorm_one_le_eLpNorm_two_mul_sqrt_measure_set`: The same inequality
  restricted to a measurable set E with finite measure.

## References

This is a standard result found in:
- Rudin, "Real and Complex Analysis", Chapter 3
- Folland, "Real Analysis", Chapter 6
- Brezis, "Functional Analysis, Sobolev Spaces and Partial Differential Equations"

The general form is:
  ‖f‖_p ≤ ‖f‖_q · (μ(E))^(1/p - 1/q) for p < q and μ(E) < ∞

Our specific case is p=1, q=2 on the support of f.
-/

open MeasureTheory
open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/--
**Cauchy-Schwarz inequality for L^p spaces on sets of finite measure.**

For a function f supported on a set E with finite measure, we have:
  ‖f‖₁ ≤ ‖f‖₂ · √(μ(E))

This is the standard textbook result, a special case (p=1, q=2) of:
  ‖f‖_p ≤ ‖f‖_q · (μ(E))^(1/p - 1/q) for p ≤ q

## Mathematical content

Given:
- f : α → E, a measurable function
- E : Set α, a measurable set with μ(E) < ∞
- supp(f) ⊆ E (f is supported on E)

Then: ∫ ‖f‖ dμ ≤ (∫ ‖f‖² dμ)^(1/2) · √(μ(E))

## Proof strategy

Apply Hölder's inequality to f and the constant function 1:
  ∫_E |f · 1| dμ ≤ ‖f‖_L²(E) · ‖1‖_L²(E)
                = ‖f‖_L²(E) · √(μ(E))
-/
theorem eLpNorm_one_le_eLpNorm_two_mul_sqrt_measure_set
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    {s : Set α} (hs : MeasurableSet s) (hs_finite : μ s < ∞)
    (h_supp : ∀ x ∉ s, f x = 0) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ * ENNReal.ofReal ((μ s).toReal ^ (1 / 2 : ℝ)) := by
  sorry

/--
**Cauchy-Schwarz for compactly supported functions.**

If f has compact support, then:
  ‖f‖₁ ≤ ‖f‖₂ · √(vol(tsupport f))

This is a direct corollary of the previous theorem, using that
the topological support of a compactly supported function has finite measure.
-/
theorem eLpNorm_one_le_eLpNorm_two_mul_sqrt_tsupport
    [TopologicalSpace α] [BorelSpace α]
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    (hf_compact : HasCompactSupport f)
    (h_finite : μ (tsupport f) < ∞) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ * ENNReal.ofReal ((μ (tsupport f)).toReal ^ (1 / 2 : ℝ)) := by
  sorry

/--
**Variant with ENNReal for the measure term.**

Sometimes it's more convenient to work with ENNReal directly.
This version states:
  ‖f‖₁ ≤ ‖f‖₂ · (μ s)^(1/2)
where the exponentiation is in ENNReal.
-/
theorem eLpNorm_one_le_eLpNorm_two_mul_rpow_measure_set
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    {s : Set α} (hs : MeasurableSet s) (hs_finite : μ s < ∞)
    (h_supp : ∀ x ∉ s, f x = 0) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ * (μ s) ^ (1 / 2 : ℝ) := by
  sorry

/--
**Application: Bounding L¹ error by L² error for compact support.**

This is the form most directly useful for our density approximation:

Given:
- f, g both with compact support
- ‖f - g‖₂ ≤ ε
- The support of f - g is contained in a set of measure M

Then: ‖f - g‖₁ ≤ ε · √M

This is exactly what we need for the mollifier approximation theorem.
-/
theorem eLpNorm_sub_one_le_eLpNorm_sub_two_of_compact_support
    [TopologicalSpace α] [BorelSpace α]
    {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf_compact : HasCompactSupport f) (hg_compact : HasCompactSupport g)
    {ε : ℝ≥0∞} (h_L2 : eLpNorm (f - g) 2 μ ≤ ε)
    (h_supp_measure : μ (tsupport f ∪ tsupport g) < ∞) :
    eLpNorm (f - g) 1 μ ≤ ε * (μ (tsupport f ∪ tsupport g)) ^ (1 / 2 : ℝ) := by
  sorry

/--
**Quantitative version: if the measure is bounded by M, we can bound the L¹ norm.**

If μ(support) ≤ M and ‖f - g‖₂ ≤ ε, then ‖f - g‖₁ ≤ ε · √M.

This is the most practical form for applications where we know
an explicit bound on the support measure.
-/
theorem eLpNorm_sub_one_le_of_eLpNorm_sub_two_le_of_measure_le
    [TopologicalSpace α] [BorelSpace α]
    {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf_compact : HasCompactSupport f) (hg_compact : HasCompactSupport g)
    {ε M : ℝ} (hε_pos : 0 ≤ ε) (hM_pos : 0 ≤ M)
    (h_L2 : eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε)
    (h_measure : (μ (tsupport f ∪ tsupport g)).toReal ≤ M) :
    eLpNorm (f - g) 1 μ ≤ ENNReal.ofReal (ε * Real.sqrt M) := by
  sorry
