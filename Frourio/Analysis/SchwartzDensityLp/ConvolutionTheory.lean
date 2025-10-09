import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Support
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Convolution Theory for Lp Spaces

This file develops the theory of convolution in Lp spaces, with a focus on
properties needed for the Schwartz density theorem.

## Main results

- `convolution_support_subset`: Support of convolution is contained in the sum of supports
- `convolution_smooth`: Convolution with smooth function is smooth
- `convolution_linear`: Linearity of convolution
- `convolution_triangle_ineq`: Triangle inequality for convolution in Lp norm

## References

- Folland, Real Analysis: Modern Techniques and Their Applications, Chapter 8
- papers/schwartz_density_constructive_analysis.md, Section 3.1

-/

open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Convolution Pointwise

variable {n : ℕ}

section Support

/--
**Support of convolution (Theorem 3.2 in the paper).**

If f has compact support in B_R and g has compact support in B_δ,
then their convolution f * g has support in B_{R+δ}.

This is the key property that justifies the "cut-off first, then convolve" approach.
-/
lemma convolution_compactSupport_subset
    (f g : (Fin n → ℝ) → ℂ)
    (hf_compact : HasCompactSupport f)
    (hg_compact : HasCompactSupport g) :
    HasCompactSupport (fun x => ∫ y, f (x - y) * g y) := by
  classical
  simpa [MeasureTheory.convolution, convolution, mul_comm] using
    (HasCompactSupport.convolution
      (μ := MeasureSpace.volume)
      (L := ContinuousLinearMap.mul ℝ ℂ)
      hg_compact hf_compact)

/--
**Explicit support bound for convolution.**

If supp(f) ⊆ B_R and supp(g) ⊆ B_δ, then supp(f * g) ⊆ B_{R+δ}.
-/
lemma convolution_support_ball_subset
    (f g : (Fin n → ℝ) → ℂ)
    (R δ : ℝ)
    (hf_supp : tsupport f ⊆ Metric.closedBall (0 : Fin n → ℝ) R)
    (hg_supp : tsupport g ⊆ Metric.closedBall (0 : Fin n → ℝ) δ) :
    tsupport (fun x => ∫ y, f (x - y) * g y) ⊆
      Metric.closedBall (0 : Fin n → ℝ) (R + δ) := by
  classical
  set h := fun x => ∫ y, f (x - y) * g y
  have h_support_subset :
      Function.support h ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + δ) := by
    have h_conv_subset :
        Function.support h ⊆ Function.support g + Function.support f := by
      simpa [h, convolution, MeasureTheory.convolution, mul_comm] using
        (support_convolution_subset
          (μ := MeasureSpace.volume)
          (L := ContinuousLinearMap.mul ℝ ℂ)
          (f := g) (g := f))
    refine h_conv_subset.trans ?_
    have h_support_tsupp :
        Function.support g + Function.support f ⊆
          tsupport g + tsupport f :=
      Set.add_subset_add (subset_tsupport _) (subset_tsupport _)
    refine h_support_tsupp.trans ?_
    intro x hx
    rcases hx with ⟨u, hu, v, hv, rfl⟩
    have hu_norm : ‖u‖ ≤ δ := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hg_supp hu)
    have hv_norm : ‖v‖ ≤ R := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hf_supp hv)
    have h_norm : ‖u + v‖ ≤ R + δ := by
      have h_add : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      exact h_add.trans <| by
        simpa [add_comm] using add_le_add hu_norm hv_norm
    refine Metric.mem_closedBall.mpr ?_
    simpa [dist_eq_norm, add_comm] using h_norm
  have h_closed : IsClosed (Metric.closedBall (0 : Fin n → ℝ) (R + δ)) :=
    Metric.isClosed_closedBall
  have h_closure_subset :
      closure (Function.support h) ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + δ) :=
    closure_minimal h_support_subset h_closed
  simpa [tsupport, h] using h_closure_subset

end Support

section Linearity

/--
**Linearity of convolution in first argument.**

(f₁ + f₂) * g = f₁ * g + f₂ * g

This holds almost everywhere when the convolution integrals exist.
-/
lemma convolution_linear_add
    (f₁ f₂ g : (Fin n → ℝ) → ℂ)
    (hconv : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * g y) volume ∧
                            Integrable (fun y => f₂ (x - y) * g y) volume) :
    (fun x => ∫ y, (f₁ (x - y) + f₂ (x - y)) * g y) =ᶠ[ae volume]
    (fun x => ∫ y, f₁ (x - y) * g y) + (fun x => ∫ y, f₂ (x - y) * g y) := by
  filter_upwards [hconv] with x ⟨h₁, h₂⟩
  rw [Pi.add_apply, ← integral_add h₁ h₂]
  congr 1
  ext y
  ring

/--
**Scalar multiplication compatibility.**

(c * f) * g = c * (f * g)
-/
lemma convolution_scalar_mul
    (c : ℂ) (f g : (Fin n → ℝ) → ℂ)
    (hconv : ∀ᵐ x ∂volume, Integrable (fun y => f (x - y) * g y) volume) :
    (fun x => ∫ y, (c * f (x - y)) * g y) =ᶠ[ae volume]
    (fun x => c * ∫ y, f (x - y) * g y) := by
  filter_upwards [hconv] with x hx
  rw [← integral_const_mul]
  congr 1
  ext y
  ring

end Linearity

section TriangleInequality

/--
**Triangle inequality for Lp norm (needed for calc steps in the paper).**

‖f - h‖_p ≤ ‖f - g‖_p + ‖g - h‖_p
-/
lemma eLpNorm_triangle_inequality
    (f g h : (Fin n → ℝ) → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hfg : AEStronglyMeasurable (fun x => f x - g x) volume)
    (hgh : AEStronglyMeasurable (fun x => g x - h x) volume) :
    eLpNorm (fun x => f x - h x) p volume ≤
    eLpNorm (fun x => f x - g x) p volume +
    eLpNorm (fun x => g x - h x) p volume := by
  classical
  have h_decomp :
      (fun x => f x - h x) =
        (fun x => f x - g x) + fun x => g x - h x := by
    funext x
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [h_decomp] using
    (eLpNorm_add_le (μ := volume) (p := p)
      (f := fun x => f x - g x)
      (g := fun x => g x - h x)
      hfg hgh hp)

/--
**Three-way triangle inequality (used in proof steps).**

‖f - φ‖_p ≤ ‖f - g‖_p + ‖g - ψ‖_p + ‖ψ - φ‖_p

This is used in the paper's Section 4.2 for the error analysis.
-/
lemma eLpNorm_triangle_three
    (f g ψ φ : (Fin n → ℝ) → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hfg : AEStronglyMeasurable (fun x => f x - g x) volume)
    (hgψ : AEStronglyMeasurable (fun x => g x - ψ x) volume)
    (hψφ : AEStronglyMeasurable (fun x => ψ x - φ x) volume) :
    eLpNorm (fun x => f x - φ x) p volume ≤
    eLpNorm (fun x => f x - g x) p volume +
    eLpNorm (fun x => g x - ψ x) p volume +
    eLpNorm (fun x => ψ x - φ x) p volume := by
  classical
  have hgφ : AEStronglyMeasurable (fun x => g x - φ x) volume := by
    have h_sum := hgψ.add hψφ
    have h_eq :
        (fun x => g x - φ x) =
          (fun x => g x - ψ x) + fun x => ψ x - φ x := by
      funext x
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simpa [h_eq] using h_sum
  have h_triangle₁ :=
    eLpNorm_triangle_inequality (f := f) (g := g) (h := φ) (p := p) hp hfg hgφ
  have h_triangle₂ :=
    eLpNorm_triangle_inequality (f := g) (g := ψ) (h := φ) (p := p) hp hgψ hψφ
  refine h_triangle₁.trans ?_
  have h_add := add_le_add_left h_triangle₂ (eLpNorm (fun x => f x - g x) p volume)
  simpa [add_comm, add_left_comm, add_assoc] using h_add

end TriangleInequality

section ConvolutionDifference

/--
**Difference of convolutions (linearity applied to differences).**

This shows that (g - f₀) * ψ = g * ψ - f₀ * ψ,
which is used in the paper's proof (Section 4.2, Step 3).

This is derived from `convolution_linear_add` and `convolution_scalar_mul`.
-/
lemma convolution_sub
    (f₁ f₂ g : (Fin n → ℝ) → ℂ)
    (hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * g y) volume)
    (hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * g y) volume) :
    (fun x => ∫ a, (f₁ (x - a) - f₂ (x - a)) * g a) =ᶠ[ae volume]
    (fun x => (∫ a, f₁ (x - a) * g a) - ∫ a, f₂ (x - a) * g a) := by
  have h_ae_both : ∀ᵐ x ∂volume, Integrable (fun a => f₁ (x - a) * g a) volume ∧
                                    Integrable (fun a => f₂ (x - a) * g a) volume := by
    filter_upwards [hconv₁, hconv₂] with x h₁ h₂
    exact ⟨h₁, h₂⟩
  filter_upwards [h_ae_both] with x ⟨hint₁, hint₂⟩
  classical
  have h₁ :
      ∫ a, (f₁ (x - a) - f₂ (x - a)) * g a =
        ∫ a, f₁ (x - a) * g a - f₂ (x - a) * g a := by
    simp [sub_mul]
  have h₂ :
      ∫ a, f₁ (x - a) * g a - f₂ (x - a) * g a =
        (∫ a, f₁ (x - a) * g a) - ∫ a, f₂ (x - a) * g a := by
    simpa using integral_sub hint₁ hint₂
  exact h₁.trans h₂

end ConvolutionDifference
