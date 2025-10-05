import Frourio.Analysis.SchwartzDensityLp.SchwartzDensityLpCore
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

open MeasureTheory SchwartzMap
open scoped ENNReal ContDiff

variable {n : ℕ}

/-- Cutting off a smooth function so that it has compact support while keeping control of the
`Lᵖ` error. -/
theorem smooth_cutoff_compactSupport_Lp
    (p : ℝ≥0∞)
    (φ : (Fin n → ℝ) → ℂ)
    (hφ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ)
    (hφ_memLp : MemLp φ p volume)
    {R : ℝ} (hR_pos : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ ∧ MemLp ψ p volume ∧
      eLpNorm (fun x => φ x - ψ x) p volume < ENNReal.ofReal ε := by
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
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      MemLp g p volume ∧
      eLpNorm (f - g) p volume < ENNReal.ofReal ε := by
  classical
  haveI := (inferInstance : R1Space (Fin n → ℝ))
  haveI := (inferInstance : WeaklyLocallyCompactSpace (Fin n → ℝ))
  haveI := (inferInstance : MeasureTheory.Measure.Regular (volume : Measure (Fin n → ℝ)))

  -- First approximate by a continuous compactly supported function in Lᵖ.
  have hε_half_pos : 0 < ε / 2 := by
    have : (0 : ℝ) < 2 := by norm_num
    exact div_pos hε this
  obtain ⟨g₀, hg₀_cont, hg₀_compact, hg₀_memLp, hg₀_close⟩ :=
    continuous_compactSupport_dense_Lp (p := p) (hp_ne_top := hp_ne_top)
      (f := f) (hf := hf) (ε := ε / 2) hε_half_pos

  -- Smooth the compactly supported continuous function.
  have h_smooth_approx :
      ∃ g₁ : (Fin n → ℝ) → ℂ,
        ContDiff ℝ (∞ : WithTop ℕ∞) g₁ ∧ HasCompactSupport g₁ ∧ MemLp g₁ p volume ∧
          eLpNorm (g₀ - g₁) p volume < ENNReal.ofReal (ε / 2) := by
    have hε_quarter_pos : 0 < ε / 4 := by
      have : (0 : ℝ) < 4 := by norm_num
      exact div_pos hε this
    obtain ⟨φ, hφ_smooth, hφ_close, hφ_memLp⟩ :=
      mollifier_compactSupport_Lp_approx (p := p) (hp_one := hp)
        (g := g₀) hg₀_cont hg₀_compact (ε := ε / 4) hε_quarter_pos
    obtain ⟨ψ, hψ_smooth, hψ_compact, hψ_memLp, hψ_close⟩ :=
      smooth_cutoff_compactSupport_Lp (p := p) (φ := φ) hφ_smooth hφ_memLp
        (R := (1 : ℝ)) (hR_pos := by norm_num) (ε := ε / 4) hε_quarter_pos
    have h_add_le :
        eLpNorm
            ((fun x => g₀ x - φ x) + fun x => φ x - ψ x) p volume
          ≤ eLpNorm (fun x => g₀ x - φ x) p volume
              + eLpNorm (fun x => φ x - ψ x) p volume :=
      eLpNorm_add_le (μ := volume) (p := p)
        (f := fun x => g₀ x - φ x) (g := fun x => φ x - ψ x)
        (hf :=
          (hg₀_memLp.aestronglyMeasurable.sub hφ_memLp.aestronglyMeasurable))
        (hg :=
          (hφ_memLp.aestronglyMeasurable.sub hψ_memLp.aestronglyMeasurable))
        hp
    have h_fun_eq :
        (fun x => g₀ x - ψ x)
          = (fun x => g₀ x - φ x) + fun x => φ x - ψ x := by
      funext x; simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have h_triangle' :
        eLpNorm (fun x => g₀ x - ψ x) p volume
          ≤ eLpNorm (fun x => g₀ x - φ x) p volume
              + eLpNorm (fun x => φ x - ψ x) p volume := by
      simpa [h_fun_eq] using h_add_le
    have h_sum_lt :
        eLpNorm (fun x => g₀ x - φ x) p volume
            + eLpNorm (fun x => φ x - ψ x) p volume
          < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
      ENNReal.add_lt_add hφ_close hψ_close
    have h_nonneg : 0 ≤ ε / 4 := by
      have : (0 : ℝ) ≤ ε := le_of_lt hε
      exact div_nonneg this (by norm_num : (0 : ℝ) ≤ 4)
    have h_sum_eq :
        ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
          = ENNReal.ofReal (ε / 2) := by
      have h_add := ENNReal.ofReal_add h_nonneg h_nonneg
      have h_eq : ε / 2 = ε / 4 + ε / 4 := by ring
      calc
        ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
            = ENNReal.ofReal (ε / 4 + ε / 4) := by
              simpa [add_comm, add_left_comm, add_assoc] using h_add.symm
        _ = ENNReal.ofReal (ε / 2) := by simp [h_eq]
    have h_goal_lt :
        eLpNorm (fun x => g₀ x - φ x) p volume
            + eLpNorm (fun x => φ x - ψ x) p volume
          < ENNReal.ofReal (ε / 2) := by
      simpa [h_sum_eq] using h_sum_lt
    have h_total_lt :
        eLpNorm (fun x => g₀ x - ψ x) p volume < ENNReal.ofReal (ε / 2) :=
      lt_of_le_of_lt h_triangle' h_goal_lt
    exact ⟨ψ, hψ_smooth, hψ_compact, hψ_memLp, h_total_lt⟩
  obtain ⟨g₁, hg₁_smooth, hg₁_compact, hg₁_memLp, hg₁_close⟩ := h_smooth_approx

  -- Combine the two approximations via the triangle inequality in Lᵖ.
  have h_triangle :
      eLpNorm (f - g₁) p volume
        ≤ eLpNorm (f - g₀) p volume + eLpNorm (g₀ - g₁) p volume := by
    -- Standard triangle inequality in Lᵖ.
    sorry

  have h_target_lt :
      eLpNorm (f - g₁) p volume < ENNReal.ofReal ε := by
    -- Use the previous bounds and arithmetic on ε/2.
    sorry

  refine ⟨g₁, hg₁_smooth, hg₁_compact, hg₁_memLp, h_target_lt⟩

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
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
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
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧
      eLpNorm (fun x => f x - g x) p volume < ENNReal.ofReal ε := by
  sorry
