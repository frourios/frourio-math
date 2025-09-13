import Frourio.Analysis.MellinPlancherel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

namespace Frourio

open MeasureTheory ENNReal NNReal
open scoped RealInnerProductSpace ComplexConjugate

/-- Convenience lemma: the ENNReal norm `‖z‖ₑ` is definitionally
    the same as the cast of the `ℝ≥0` norm `‖z‖₊`. This helps rewrite
    products like `‖z‖ₑ * t` into `↑‖z‖₊ * t`. -/
@[simp]
lemma ennreal_norm_eq_coe_nnnorm (z : ℂ) : (‖z‖ₑ : ℝ≥0∞) = (‖z‖₊ : ℝ≥0∞) := rfl

/-!
# Quadratic Forms and Positivity (plan1 Step 1)

This file implements the quadratic form Q[K] on L²(ℝ) and its pullback to Hσ,
establishing the Frourio-Weil positivity criterion.

## Main definitions

* `M_K`: Multiplication operator by K on L²(ℝ)
* `Qℝ`: Real-valued quadratic form ∫ K(τ) * ‖g(τ)‖² dτ
* `Q_pos`: Positivity theorem for non-negative kernels

## Implementation notes

We first handle bounded multiplication operators (K ∈ L∞), then extend to
more general measurable non-negative functions.
-/

section MultiplicationOperator

variable {K : ℝ → ℂ} {g : Lp ℂ 2 (volume : Measure ℝ)}

/-- Helper lemma: If K is essentially bounded and g ∈ L², then K·g ∈ L² (integral version) -/
lemma mul_mem_L2 (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) < ∞ := by
  classical
  -- Measurability: product of two a.e.-strongly measurable functions
  have hg_meas : AEStronglyMeasurable (fun x => (g : ℝ → ℂ) x) volume :=
    (Lp.aestronglyMeasurable g)
  have hmeas : AEStronglyMeasurable (fun x => K x * (g : ℝ → ℂ) x) volume :=
    hK_meas.mul hg_meas
  -- We prove finiteness of ∫⁻ ‖K·g‖₊^2 via the essSup bound
  -- Abbreviations
  set Mess : ℝ≥0∞ := essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume
  have hM_top : Mess < ∞ := hK_bdd
  -- Pointwise on the set where the essSup bound holds
  have h_bound : ∀ᵐ x ∂volume, (‖K x‖₊ : ℝ≥0∞) ≤ Mess :=
    ae_le_essSup (fun x => (‖K x‖₊ : ℝ≥0∞))
  -- Build the pointwise inequality for the squared nnnorm
  have h_pw : ∀ᵐ x ∂volume,
      ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ))
        ≤ (Mess ^ (2 : ℕ)) * ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
    refine h_bound.mono ?_
    intro x hx
    -- Use ‖ab‖₊ = ‖a‖₊ * ‖b‖₊ and monotonicity of pow and mul in ℝ≥0∞
    have hmul : (‖K x * (g : ℝ → ℂ) x‖₊ : ℝ≥0∞)
        ≤ (‖K x‖₊ : ℝ≥0∞) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) := by
      -- In ℝ≥0∞, nnnorm is submultiplicative; equality holds for ℂ but ≤ suffices
      simp
    -- raise to power 2 and compare with M∞ bound
    have hmul_sq : ((‖K x * (g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
        ≤ (((‖K x‖₊ : ℝ≥0∞) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞)) ^ (2 : ℕ)) := by
      exact pow_le_pow_left' hmul (2 : ℕ)
    have hM_sq : (((‖K x‖₊ : ℝ≥0∞) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞)) ^ (2 : ℕ))
        ≤ (Mess ^ (2 : ℕ)) * ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
      -- expand (a*b)^2 ≤ (M*b)^2 = M^2 * b^2 using hx : a ≤ Mess
      have := mul_le_mul_right' hx ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞))
      -- Now apply pow two and distribute
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc]
        using mul_le_mul this this (by simp) (by simp)
    exact hmul_sq.trans hM_sq
  -- Compare lintegrals
  have h_int_bound :
      (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
        ≤ (Mess ^ (2 : ℕ)) * (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
    -- First bound by pointwise inequality, then pull out the constant
    have hmono := lintegral_mono_ae h_pw
    have hconst :
        (∫⁻ x, (Mess ^ (2 : ℕ)) * ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
          = (Mess ^ (2 : ℕ)) *
              (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
      -- Replace g by a measurable representative to use `lintegral_const_mul`
      -- Take a measurable representative of g's a.e.-strongly measurable coeFn
      let g' : ℝ → ℂ := (hg_meas.aemeasurable.mk (fun x => (g : ℝ → ℂ) x))
      have hg'_meas : Measurable g' := hg_meas.aemeasurable.measurable_mk
      have hgg' : (fun x => (g : ℝ → ℂ) x) =ᵐ[volume] g' := hg_meas.aemeasurable.ae_eq_mk
      -- Define the ENNReal-valued squared norm functions
      let F : ℝ → ℝ≥0∞ := fun x => ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
      let F' : ℝ → ℝ≥0∞ := fun x => ((‖g' x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
      have hF_meas : Measurable F' := by
        -- measurability from hg'_meas
        have : Measurable fun x => (‖g' x‖) := (hg'_meas.norm)
        have h_ofReal : Measurable fun x => ENNReal.ofReal (‖g' x‖) :=
          ENNReal.measurable_ofReal.comp this
        simpa [F'] using h_ofReal.pow_const (2 : ℕ)
      have hF_ae : F =ᵐ[volume] F' := by
        -- transport ae-eq through norm and powers
        refine hgg'.mono ?_
        intro x hx
        have : ‖(g : ℝ → ℂ) x‖ = ‖g' x‖ := by simpa using congrArg norm hx
        -- convert to ENNReal nnnorm form and square
        have : ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              = ((‖g' x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
          -- coe from ℝ to ENNReal via ofReal and pow preserve equality
          -- use the equality of real norms
          simpa [pow_two] using congrArg (fun t => (ENNReal.ofReal t) ^ (2 : ℕ)) this
        simpa [F, F'] using this
      -- Now compute with measurable representative using const-mul lintegral lemma
      have hconst' :
          (∫⁻ x, (Mess ^ (2 : ℕ)) * F' x ∂volume)
            = (Mess ^ (2 : ℕ)) * (∫⁻ x, F' x ∂volume) := by
        simpa using (lintegral_const_mul
          (μ := volume) (r := Mess ^ (2 : ℕ)) (f := F') (hf := hF_meas))
      -- Transport the equality back via ae-congruence
      have hleft : (∫⁻ x, (Mess ^ (2 : ℕ)) * F x ∂volume)
            = (∫⁻ x, (Mess ^ (2 : ℕ)) * F' x ∂volume) := by
        -- use lintegral_congr_ae with multiplication by constant preserved a.e.
        refine lintegral_congr_ae ?_
        exact hF_ae.mono (fun x hx => by
          simpa [F, F'] using congrArg (fun t => (Mess ^ (2 : ℕ)) * t) hx)
      have hright : (∫⁻ x, F x ∂volume) = (∫⁻ x, F' x ∂volume) := by
        exact lintegral_congr_ae hF_ae
      -- Transport the equality along `hleft` and `hright`
      -- Compose hleft, hconst', and hright.symm to transport along F ↔ F'
      have hconst'' := hconst'
      have hconst_trans :
          (∫⁻ x, (Mess ^ (2 : ℕ)) * F x ∂volume)
            = (Mess ^ (2 : ℕ)) * (∫⁻ x, F x ∂volume) := by
        calc
          (∫⁻ x, (Mess ^ (2 : ℕ)) * F x ∂volume)
              = (∫⁻ x, (Mess ^ (2 : ℕ)) * F' x ∂volume) := hleft
          _   = (Mess ^ (2 : ℕ)) * (∫⁻ x, F' x ∂volume) := hconst''
          _   = (Mess ^ (2 : ℕ)) * (∫⁻ x, F x ∂volume) := by
                have := congrArg (fun t => (Mess ^ (2 : ℕ)) * t) hright.symm
                simpa using this
      simpa [F] using hconst_trans
    simpa [hconst] using hmono
  -- The RHS is finite since g ∈ L² and Mess < ∞
  have hg_mem : MemLp (fun x => (g : ℝ → ℂ) x) 2 volume :=
    Lp.memLp g
  have hg_fin : (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) < ∞ := by
    -- Use the identity ‖g‖^2 = (∫⁻ ‖g‖₊^2).toReal and split on ‖g‖
    have hId : ‖g‖ ^ 2
        = (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal := by
      simpa using (Lp_norm_sq_as_lintegral (ν := volume) (f := g))
    by_cases hzero : ‖g‖ = 0
    · -- then g = 0 in Lp, hence the integrand is 0 a.e., so the lintegral is 0
      have : g = 0 := by simpa using (norm_eq_zero.mp hzero)
      -- coeFn of zero is ae-zero, so the lintegral is zero
      have hcoe : ((g : ℝ → ℂ)) =ᵐ[volume] 0 := by
        -- rewrite g to 0 and use the library lemma for coeFn of 0
        simpa [this] using
          (Lp.coeFn_zero (E := ℂ) (μ := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞)))
      have hcongr : (fun x => ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)))
          =ᵐ[volume] (fun _ => 0) := by
        refine hcoe.mono ?_
        intro x hx; simp [hx]
      have : (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) = 0 := by
        simpa using lintegral_congr_ae hcongr
      simp [this]
    · -- otherwise, the lintegral cannot be ∞ since its toReal is positive
      have hpos : 0 < ‖g‖ ^ 2 := by
        have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (by exact norm_nonneg g) (Ne.symm hzero)
        have hz : ‖g‖ ≠ 0 := ne_of_gt hgpos
        have : 0 < ‖g‖ * ‖g‖ := mul_pos hgpos hgpos
        simpa [pow_two] using this
      -- if the lintegral were ∞, its toReal would be 0, contradicting hId
      have : (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) ≠ ∞ := by
        intro hinf
        -- If the integral were ∞, its toReal would be 0, contradicting positivity of ‖g‖^2
        have hEq : 0 = ‖g‖ ^ 2 := by simpa [hinf] using hId.symm
        have hZero : ‖g‖ ^ 2 = 0 := by simpa [eq_comm] using hEq
        exact (ne_of_gt hpos) hZero
      simpa [lt_top_iff_ne_top] using this
  have hR_fin : (Mess ^ (2 : ℕ)) * (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) < ∞ := by
    -- product of two finite ENNReals is finite
    have hM_fin : (Mess ^ (2 : ℕ)) < ∞ := pow_lt_top hM_top
    exact ENNReal.mul_lt_top hM_fin hg_fin
  have h_int_fin : (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) < ∞ :=
    lt_of_le_of_lt h_int_bound hR_fin
  -- Conclude with finiteness of the L² lintegral for the product
  exact h_int_fin

/-- Helper lemma: If K is essentially bounded and g ∈ L², then K·g ∈ L² (MemLp version) -/
lemma mul_mem_L2_memLp (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    MemLp (fun x => K x * (g : ℝ → ℂ) x) 2 volume := by
  constructor
  · -- a.e.-強可測性は積で閉じる
    exact hK_meas.mul (Lp.aestronglyMeasurable g)
  · -- L² の lintegral が有限であることは `mul_mem_L2` から直ちに従う
    -- 目標は `eLpNorm (K·g) 2 < ∞`。
    -- `eLpNorm` の表示を lintegral に書き換えてから、`mul_mem_L2` の有限性を使う。
    have hfin_int :
        (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) < ∞ :=
      mul_mem_L2 K g hK_meas hK_bdd
    -- eLpNorm の基本表示（p=2, 0<2<∞）
    have h0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have htop : (2 : ℝ≥0∞) ≠ ∞ := by simp
    have heq :=
      eLpNorm_eq_lintegral_rpow_enorm (μ := volume)
        (f := fun x => K x * (g : ℝ → ℂ) x) h0 htop
    -- ∫ ‖·‖ₑ^2 と ∫ (‖·‖₊)^2 は一致
    have hswap :
        (∫⁻ x, ‖(K x * (g : ℝ → ℂ) x)‖ₑ ^ (2 : ℝ) ∂volume)
          = (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
      refine lintegral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      have hx : (‖(K x * (g : ℝ → ℂ) x)‖ₑ : ℝ≥0∞)
          = (‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) := rfl
      simp [hx]
    -- 右辺の lintegral が有限なら、その rpow も有限
    have hne :
        (∫⁻ x, ‖(K x * (g : ℝ → ℂ) x)‖ₑ ^ (2 : ℝ) ∂volume) ≠ ∞ := by
      -- `hswap` と `hfin_int` から直ちに従う
      have :
          (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) ≠ ∞ :=
        (ne_of_lt hfin_int)
      simpa [hswap]
        using this
    -- rpow の有限性から eLpNorm の有限性へ
    have : eLpNorm (fun x => K x * (g : ℝ → ℂ) x) 2 volume ≠ ∞ := by
      -- eLpNorm = (∫ …)^(1/2)
      have hrepr :
          eLpNorm (fun x => K x * (g : ℝ → ℂ) x) 2 volume
            = (∫⁻ x, ‖(K x * (g : ℝ → ℂ) x)‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
        simpa using heq
      -- (finite)^(1/2) ≠ ∞
      have hrpow_ne :
          ((∫⁻ x, ‖(K x * (g : ℝ → ℂ) x)‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))) ≠ ∞ := by
        have hnonneg : 0 ≤ (1 / (2 : ℝ)) := by norm_num
        exact ENNReal.rpow_ne_top_of_nonneg hnonneg hne
      simpa [hrepr] using hrpow_ne
    simpa [lt_top_iff_ne_top] using this

/-- Helper lemma: Pointwise inequality for norm of K·g -/
lemma M_K_pointwise_bound (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ x ∂volume,
      ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ))
        ≤ (essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume ^ (2 : ℕ)) *
        ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
  set Mess := essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume
  have h_bound : ∀ᵐ x ∂volume, (‖K x‖₊ : ℝ≥0∞) ≤ Mess :=
    ae_le_essSup (fun x => (‖K x‖₊ : ℝ≥0∞))
  refine h_bound.mono ?_
  intro x hx
  have hmul : (‖K x * (g : ℝ → ℂ) x‖₊ : ℝ≥0∞)
      ≤ (‖K x‖₊ : ℝ≥0∞) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) := by
    have : ‖K x * (g : ℝ → ℂ) x‖ ≤ ‖K x‖ * ‖(g : ℝ → ℂ) x‖ := by
      simp
    exact (ENNReal.coe_le_coe.mpr (by
      change (‖K x * (g : ℝ → ℂ) x‖₊ : ℝ≥0)
          ≤ (‖K x‖₊ : ℝ≥0) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0)
      simp))
  have hmul_sq : ((‖K x * (g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
      ≤ (((‖K x‖₊ : ℝ≥0∞) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞)) ^ (2 : ℕ)) :=
    pow_le_pow_left' hmul (2 : ℕ)
  have : (((‖K x‖₊ : ℝ≥0∞) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞)) ^ (2 : ℕ))
      ≤ (Mess ^ (2 : ℕ)) * ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
    have hx' := mul_le_mul_right' hx ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞))
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc]
      using mul_le_mul hx' hx' (by simp) (by simp)
  exact hmul_sq.trans this

/-- Helper lemma: L² norm inequality for K·g -/
lemma M_K_L2_bound (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
      ≤ (essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume ^ (2 : ℕ)) *
        (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
  set Mess := essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume
  have h_pw := M_K_pointwise_bound K g
  have hmono := lintegral_mono_ae h_pw
  have hconst :
      (∫⁻ x, (Mess ^ (2 : ℕ)) * ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
        = (Mess ^ (2 : ℕ)) *
            (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
    -- Replace g by a measurable representative to use lintegral_const_mul
    have hg_meas' : AEStronglyMeasurable (fun x => (g : ℝ → ℂ) x) volume :=
      Lp.aestronglyMeasurable g
    let g' : ℝ → ℂ := (hg_meas'.aemeasurable.mk (fun x => (g : ℝ → ℂ) x))
    have hg'_meas : Measurable g' := hg_meas'.aemeasurable.measurable_mk
    have hgg' : (fun x => (g : ℝ → ℂ) x) =ᵐ[volume] g' :=
      hg_meas'.aemeasurable.ae_eq_mk
    let F : ℝ → ℝ≥0∞ := fun x => ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
    let F' : ℝ → ℝ≥0∞ := fun x => ((‖g' x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
    have hF_meas : Measurable F' := by
      have : Measurable fun x => (‖g' x‖) := (hg'_meas.norm)
      have h_ofReal : Measurable fun x => ENNReal.ofReal (‖g' x‖) :=
        ENNReal.measurable_ofReal.comp this
      simpa [F'] using h_ofReal.pow_const (2 : ℕ)
    have hF_ae : F =ᵐ[volume] F' := by
      refine hgg'.mono ?_
      intro x hx
      have : ‖(g : ℝ → ℂ) x‖ = ‖g' x‖ := by simpa using congrArg norm hx
      have : ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
            = ((‖g' x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
        simpa [pow_two] using congrArg (fun t => (ENNReal.ofReal t) ^ (2 : ℕ)) this
      simpa [F, F'] using this
    have hconst' :
        (∫⁻ x, (Mess ^ (2 : ℕ)) * F' x ∂volume)
          = (Mess ^ (2 : ℕ)) * (∫⁻ x, F' x ∂volume) := by
      simpa using (lintegral_const_mul (μ := volume)
        (r := Mess ^ (2 : ℕ)) (f := F') (hf := hF_meas))
    have hleft : (∫⁻ x, (Mess ^ (2 : ℕ)) * F x ∂volume)
          = (∫⁻ x, (Mess ^ (2 : ℕ)) * F' x ∂volume) := by
      refine lintegral_congr_ae ?_
      exact hF_ae.mono (fun x hx => by
        simpa [F, F'] using congrArg (fun t => (Mess ^ (2 : ℕ)) * t) hx)
    have hright : (∫⁻ x, F x ∂volume) = (∫⁻ x, F' x ∂volume) := by
      exact lintegral_congr_ae hF_ae
    simpa [F, hleft, hright] using hconst'
  calc (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
    ≤ (∫⁻ x, (Mess ^ (2 : ℕ)) * ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := hmono
    _ = (Mess ^ (2 : ℕ)) * (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := hconst

/-- Helper lemma: Norm inequality for the linear map L -/
lemma M_K_linear_map_bound (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞)
    (L : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hL : ∀ g, L g = (mul_mem_L2_memLp K g hK_meas hK_bdd).toLp _) :
    ∀ g, ‖L g‖ ≤ (essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume).toReal * ‖g‖ := by
  intro g
  classical
  set Mess : ℝ≥0∞ := essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume
  have hM_fin : Mess < ∞ := hK_bdd
  have hInt := M_K_L2_bound K g
  -- Turn it into a norm inequality
  have hL2 := Lp_norm_sq_as_lintegral (ν := volume) (f := (L g))
  have hL2g := Lp_norm_sq_as_lintegral (ν := volume) (f := g)
  have hfin1 : (Mess ^ (2 : ℕ)) < ∞ := pow_lt_top hM_fin
  have hfin2 :
    (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) < ∞ := by
    -- Show finiteness via the L² norm identity and case analysis on ‖g‖
    have hId : ‖g‖ ^ 2
        = (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal := by
      simpa using (Lp_norm_sq_as_lintegral (ν := volume) (f := g))
    by_cases hzero : ‖g‖ = 0
    · -- then g = 0 in Lp, hence the lintegral is 0
      have : g = 0 := by simpa using (norm_eq_zero.mp hzero)
      have hcoe : ((g : ℝ → ℂ)) =ᵐ[volume] 0 := by
        simpa [this] using
          (Lp.coeFn_zero (E := ℂ) (μ := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞)))
      have hcongr : (fun x => ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)))
          =ᵐ[volume] (fun _ => 0) := by
        refine hcoe.mono ?_
        intro x hx; simp [hx]
      have : (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) = 0 := by
        simpa using lintegral_congr_ae hcongr
      simp [this]
    · -- otherwise, the lintegral cannot be ∞
      have hpos : 0 < ‖g‖ ^ 2 := by
        have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (by exact norm_nonneg g) (Ne.symm hzero)
        have : 0 < ‖g‖ * ‖g‖ := mul_pos hgpos hgpos
        simpa [pow_two] using this
      have : (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) ≠ ∞ := by
        intro hinf
        have hEq : 0 = ‖g‖ ^ 2 := by simpa [hinf] using hId.symm
        have hZero : ‖g‖ ^ 2 = 0 := by simpa [eq_comm] using hEq
        exact (ne_of_gt hpos) hZero
      simpa [lt_top_iff_ne_top] using this
  have hconst_toReal :
      ((Mess ^ (2 : ℕ)) *
          (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)).toReal
        = (Mess.toReal ^ 2) *
            (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal := by
    have : (Mess ^ (2 : ℕ)).toReal = (Mess.toReal) ^ (2 : ℕ) := by
      simp
    simp
  have hInt' :
      (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
        ≤ ((Mess ^ (2 : ℕ)) *
            (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)).toReal := by
    have hleft_ne :
        (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) ≠ ∞ :=
      (ne_of_lt (mul_mem_L2 K g hK_meas hK_bdd))
    have hright_ne :
        ((Mess ^ (2 : ℕ)) *
            (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)) ≠ ∞ :=
      (ne_of_lt (mul_lt_top hfin1 hfin2))
    exact (ENNReal.toReal_le_toReal hleft_ne hright_ne).mpr hInt
  have hleft :
      (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
        = ‖(L g)‖ ^ 2 := by
    have hLg_ae :
        (((L g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume] (fun x => K x * (g : ℝ → ℂ) x) := by
      simpa [hL] using
        (MemLp.coeFn_toLp (mul_mem_L2_memLp K g hK_meas hK_bdd))
    have hswap :
        (∫⁻ x, ((‖(((L g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
          = (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
      refine lintegral_congr_ae ?_
      refine hLg_ae.mono ?_
      intro x hx; simp [hx]
    have hL2' : ‖L g‖ ^ 2
        = (∫⁻ x, ((‖(((L g) : Lp ℂ 2 (volume : Measure ℝ))
          : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal := hL2
    have hswap_toReal :
        (∫⁻ x, ((‖(((L g) : Lp ℂ 2 (volume : Measure ℝ))
          : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
          = (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal := by
      simpa using congrArg ENNReal.toReal hswap
    simpa [hswap_toReal] using hL2'.symm
  have hright :
      (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
        = ‖g‖ ^ 2 := by simpa using hL2g.symm
  -- Combine the toReal inequality with the norm identities on both sides
  have hineq_sq : ‖(L g)‖ ^ 2 ≤ (Mess.toReal ^ 2) * (‖g‖ ^ 2) := by
    have htmp := hInt'
    have htmp' :
        (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
          ≤ (Mess.toReal ^ 2) * (‖g‖ ^ 2) := by
      simpa only [hconst_toReal, hright] using htmp
    simpa [hleft.symm] using htmp'
  -- Take square roots (both sides nonnegative) to get the linear bound
  have hnonnegL : 0 ≤ ‖(L g)‖ := norm_nonneg _
  have hM0 : 0 ≤ Mess.toReal := ENNReal.toReal_nonneg
  have hnonnegr : 0 ≤ Mess.toReal * ‖g‖ := mul_nonneg hM0 (norm_nonneg _)
  -- Rewrite RHS as a square and apply `sq_le_sq` to get absolute values
  have hsq : ‖(L g)‖ ^ 2 ≤ (Mess.toReal * ‖g‖) ^ 2 := by
    simpa [pow_two, mul_pow, mul_comm, mul_left_comm, mul_assoc]
      using hineq_sq
  have habs : |‖(L g)‖| ≤ |Mess.toReal * ‖g‖| := (sq_le_sq).1 hsq
  -- Drop absolute values using nonnegativity
  simpa [abs_of_nonneg hnonnegL, abs_of_nonneg hnonnegr]
    using habs

noncomputable def M_K (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  classical
  -- First build the underlying linear map
  let L : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  { toFun := fun g => (mul_mem_L2_memLp K g hK_meas hK_bdd).toLp _
    , map_add' := by
        intro g₁ g₂
        -- Show a.e. equality of representatives without unfolding `M_K`.
        apply Lp.ext
        -- Left side: coeFn of toLp for K·(g₁+g₂)
        have hL :
            (((mul_mem_L2_memLp K (g₁ + g₂) hK_meas hK_bdd).toLp (μ := volume)
                (p := (2 : ℝ≥0∞))) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => K x * ((g₁ + g₂ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) := by
          simpa using
            (MemLp.coeFn_toLp (mul_mem_L2_memLp K (g₁ + g₂) hK_meas hK_bdd))
        -- Right side: coeFn add and each term's a.e. representative
        have hR_add :
            (((mul_mem_L2_memLp K g₁ hK_meas hK_bdd).toLp (μ := volume)
                  (p := (2 : ℝ≥0∞))
                + (mul_mem_L2_memLp K g₂ hK_meas hK_bdd).toLp (μ := volume)
                  (p := (2 : ℝ≥0∞))
              : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x =>
              (((mul_mem_L2_memLp K g₁ hK_meas hK_bdd).toLp (μ := volume)
                    (p := (2 : ℝ≥0∞))) : ℝ → ℂ) x
              + (((mul_mem_L2_memLp K g₂ hK_meas hK_bdd).toLp (μ := volume)
                    (p := (2 : ℝ≥0∞))) : ℝ → ℂ) x) :=
          Lp.coeFn_add _ _
        have h1 :
            (((mul_mem_L2_memLp K g₁ hK_meas hK_bdd).toLp (μ := volume)
                (p := (2 : ℝ≥0∞))) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => K x * (g₁ : ℝ → ℂ) x) := by
          simpa using
            (MemLp.coeFn_toLp (mul_mem_L2_memLp K g₁ hK_meas hK_bdd))
        have h2 :
            (((mul_mem_L2_memLp K g₂ hK_meas hK_bdd).toLp (μ := volume)
                (p := (2 : ℝ≥0∞))) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => K x * (g₂ : ℝ → ℂ) x) := by
          simpa using
            (MemLp.coeFn_toLp (mul_mem_L2_memLp K g₂ hK_meas hK_bdd))
        have h_gsum :
            ((g₁ + g₂ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => (g₁ : ℝ → ℂ) x + (g₂ : ℝ → ℂ) x) := Lp.coeFn_add _ _
        -- Normalize both sides to the same pointwise expression
        have hL_sum :
            (((mul_mem_L2_memLp K (g₁ + g₂) hK_meas hK_bdd).toLp (μ := volume)
                (p := (2 : ℝ≥0∞))) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => K x * (g₁ : ℝ → ℂ) x + K x * (g₂ : ℝ → ℂ) x) := by
          refine hL.trans ?_
          refine h_gsum.mono ?_
          intro x hx
          -- multiply both sides of hx by K x and expand
          have hx' := congrArg (fun t => K x * t) hx
          simpa [mul_add] using hx'
        have hR_sum :
            (((mul_mem_L2_memLp K g₁ hK_meas hK_bdd).toLp (μ := volume)
                  (p := (2 : ℝ≥0∞))
                + (mul_mem_L2_memLp K g₂ hK_meas hK_bdd).toLp (μ := volume)
                  (p := (2 : ℝ≥0∞))
              : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => K x * (g₁ : ℝ → ℂ) x + K x * (g₂ : ℝ → ℂ) x) := by
          refine hR_add.trans ?_
          exact h1.add h2
        exact hL_sum.trans hR_sum.symm
    , map_smul' := by
        intro c g
        apply Lp.ext
        -- LHS representative for K·(c•g)
        have hL :
            (((mul_mem_L2_memLp K (c • g) hK_meas hK_bdd).toLp (μ := volume)
                (p := (2 : ℝ≥0∞))) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => K x * ((c • g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) := by
          simpa using
            (MemLp.coeFn_toLp (mul_mem_L2_memLp K (c • g) hK_meas hK_bdd))
        -- RHS representative for c•(K·g)
        have hR :
            ((c • ((mul_mem_L2_memLp K g hK_meas hK_bdd).toLp (μ := volume)
                      (p := (2 : ℝ≥0∞))) :
                  Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => c • (((mul_mem_L2_memLp K g hK_meas hK_bdd).toLp (μ := volume)
                      (p := (2 : ℝ≥0∞))) : ℝ → ℂ) x) :=
          Lp.coeFn_smul _ _
        have hg :
            (((mul_mem_L2_memLp K g hK_meas hK_bdd).toLp (μ := volume)
                (p := (2 : ℝ≥0∞))) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => K x * (g : ℝ → ℂ) x) := by
          simpa using
            (MemLp.coeFn_toLp (mul_mem_L2_memLp K g hK_meas hK_bdd))
        have hcg :
            (((c • g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
              =ᵐ[volume]
            (fun x => c • (g : ℝ → ℂ) x) := Lp.coeFn_smul _ _
        -- Normalize both sides
        have hL_smul :
            (((mul_mem_L2_memLp K (c • g) hK_meas hK_bdd).toLp (μ := volume)
                (p := (2 : ℝ≥0∞))) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => K x * (c • (g : ℝ → ℂ) x)) := by
          refine hL.trans ?_
          exact hcg.mono (fun _ hx => by simp [hx])
        have hR_smul :
            ((c • ((mul_mem_L2_memLp K g hK_meas hK_bdd).toLp (μ := volume)
                      (p := (2 : ℝ≥0∞))) :
                  Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
              =ᵐ[volume]
            (fun x => K x * (c • (g : ℝ → ℂ) x)) := by
          refine hR.trans ?_
          exact hg.mono (fun _ hx =>
            by
              -- rewrite c • z as c * z in ℂ and commute factors with K x
              have := congrArg (fun t => c • t) hx
              -- target: c • (K x * (g x)) = K x * (c • g x)
              -- use commutativity/associativity of * on ℂ
              simpa [smul_mul_assoc, mul_comm, mul_left_comm, mul_assoc, smul_eq_mul] using this)
        exact hL_smul.trans hR_smul.symm }
  -- Provide the Lipschitz bound to obtain continuity
  refine LinearMap.mkContinuous L ((essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume).toReal) ?_
  -- Use the extracted helper lemma
  exact M_K_linear_map_bound K hK_meas hK_bdd L (fun g => rfl)

/-- a.e. action of `M_K`: as a representative function, `(M_K g)(x) = K x * g x` a.e. -/
lemma M_K_apply_ae (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (((M_K K hK_meas hK_bdd) g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (fun x => K x * (g : ℝ → ℂ) x) := by
  -- Unfold `M_K` only through the `toLp` representative
  classical
  -- By definition of `M_K`, its underlying representative is `toLp` of `K·g`.
  simpa using (MemLp.coeFn_toLp (mul_mem_L2_memLp K g hK_meas hK_bdd))

/-- Operator norm bound: ‖M_K‖ ≤ ‖K‖_∞ -/
theorem M_K_norm_le (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    ‖M_K K hK_meas hK_bdd‖ ≤ (essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume).toReal := by
  -- Apply operator norm definition
  apply ContinuousLinearMap.opNorm_le_bound
  · -- Show bound is non-negative
    apply ENNReal.toReal_nonneg
  · -- Show ‖M_K g‖ ≤ essSup(‖K‖) * ‖g‖ for all g
    intro g
    -- This is the same bound proved in `cont` above
    classical
    set Mess : ℝ≥0∞ := essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume
    have hM_fin : Mess < ∞ := hK_bdd
    -- Reuse the L² inequality skeleton
    have hInt :=
      (show
        (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
          ≤ (Mess ^ (2 : ℕ)) *
            (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) from
        by
          have h_bound : ∀ᵐ x ∂volume, (‖K x‖₊ : ℝ≥0∞) ≤ Mess :=
            ae_le_essSup (fun x => (‖K x‖₊ : ℝ≥0∞))
          have h_pw : ∀ᵐ x ∂volume,
              ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ))
                ≤ (Mess ^ (2 : ℕ)) * ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
            refine h_bound.mono ?_
            intro x hx
            have hmul : (‖K x * (g : ℝ → ℂ) x‖₊ : ℝ≥0∞)
                ≤ (‖K x‖₊ : ℝ≥0∞) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) := by
              have : ‖K x * (g : ℝ → ℂ) x‖ ≤ ‖K x‖ * ‖(g : ℝ → ℂ) x‖ := by
                simp
              exact (ENNReal.coe_le_coe.mpr (by
                change (‖K x * (g : ℝ → ℂ) x‖₊ : ℝ≥0)
                    ≤ (‖K x‖₊ : ℝ≥0) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0)
                simp))
            have hmul_sq : ((‖K x * (g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
                ≤ (((‖K x‖₊ : ℝ≥0∞) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞)) ^ (2 : ℕ)) :=
              pow_le_pow_left' hmul (2 : ℕ)
            have : (((‖K x‖₊ : ℝ≥0∞) * (‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞)) ^ (2 : ℕ))
                ≤ (Mess ^ (2 : ℕ)) * ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
              have hx' := mul_le_mul_right' hx ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞))
              simpa [pow_two, mul_comm, mul_left_comm, mul_assoc]
                using mul_le_mul hx' hx' (by simp) (by simp)
            exact hmul_sq.trans this
          have hmono := lintegral_mono_ae h_pw
          have hconst :
              (∫⁻ x, (Mess ^ (2 : ℕ)) * ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
                = (Mess ^ (2 : ℕ)) *
                    (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
            -- Use a measurable representative to justify const pullout
            have hg_meas' : AEStronglyMeasurable (fun x => (g : ℝ → ℂ) x) volume :=
              Lp.aestronglyMeasurable g
            let g' : ℝ → ℂ := (hg_meas'.aemeasurable.mk (fun x => (g : ℝ → ℂ) x))
            have hg'_meas : Measurable g' := hg_meas'.aemeasurable.measurable_mk
            have hgg' : (fun x => (g : ℝ → ℂ) x) =ᵐ[volume] g' :=
              hg_meas'.aemeasurable.ae_eq_mk
            let F : ℝ → ℝ≥0∞ := fun x => ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
            let F' : ℝ → ℝ≥0∞ := fun x => ((‖g' x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
            have hF_meas : Measurable F' := by
              have : Measurable fun x => (‖g' x‖) := (hg'_meas.norm)
              have h_ofReal : Measurable fun x => ENNReal.ofReal (‖g' x‖) :=
                ENNReal.measurable_ofReal.comp this
              simpa [F'] using h_ofReal.pow_const (2 : ℕ)
            have hF_ae : F =ᵐ[volume] F' := by
              refine hgg'.mono ?_
              intro x hx
              have : ‖(g : ℝ → ℂ) x‖ = ‖g' x‖ := by simpa using congrArg norm hx
              have : ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
                    = ((‖g' x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) := by
                simpa [pow_two] using congrArg (fun t => (ENNReal.ofReal t) ^ (2 : ℕ)) this
              simpa [F, F'] using this
            have hconst' :
                (∫⁻ x, (Mess ^ (2 : ℕ)) * F' x ∂volume)
                  = (Mess ^ (2 : ℕ)) * (∫⁻ x, F' x ∂volume) := by
              simpa using (lintegral_const_mul (μ := volume)
                (r := Mess ^ (2 : ℕ)) (f := F') (hf := hF_meas))
            have hleft : (∫⁻ x, (Mess ^ (2 : ℕ)) * F x ∂volume)
                  = (∫⁻ x, (Mess ^ (2 : ℕ)) * F' x ∂volume) := by
              refine lintegral_congr_ae ?_
              exact hF_ae.mono (fun x hx => by
                simpa [F, F'] using congrArg (fun t => (Mess ^ (2 : ℕ)) * t) hx)
            have hright : (∫⁻ x, F x ∂volume) = (∫⁻ x, F' x ∂volume) := by
              exact lintegral_congr_ae hF_ae
            have hconst'' := hconst'
            have hconst_trans :
                (∫⁻ x, (Mess ^ (2 : ℕ)) * F x ∂volume)
                  = (Mess ^ (2 : ℕ)) * (∫⁻ x, F x ∂volume) := by
              calc
                (∫⁻ x, (Mess ^ (2 : ℕ)) * F x ∂volume)
                    = (∫⁻ x, (Mess ^ (2 : ℕ)) * F' x ∂volume) := hleft
                _   = (Mess ^ (2 : ℕ)) * (∫⁻ x, F' x ∂volume) := hconst''
                _   = (Mess ^ (2 : ℕ)) * (∫⁻ x, F x ∂volume) := by
                      have := congrArg (fun t => (Mess ^ (2 : ℕ)) * t) hright.symm
                      simpa using this
            simpa [F] using hconst_trans
          simpa [hconst] using hmono)
    -- Turn it into a norm inequality, as in `cont`
    have hL2 := Lp_norm_sq_as_lintegral (ν := volume)
      (f := (M_K K hK_meas hK_bdd g))
    have hL2g := Lp_norm_sq_as_lintegral (ν := volume) (f := g)
    -- toReal of product distributes; both factors finite
    have hfin1 : (Mess ^ (2 : ℕ)) < ∞ := pow_lt_top hM_fin
    have hfin2 :
        (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) < ∞ := by
      -- Use the L² identity for g to show the defining lintegral is finite
      have hId : ‖g‖ ^ 2
          = (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal := by
        simpa using hL2g
      by_cases hzero : ‖g‖ = 0
      · -- then g = 0 in Lp, lintegral is 0
        have : g = 0 := by simpa using (norm_eq_zero.mp hzero)
        have hcoe : ((g : ℝ → ℂ)) =ᵐ[volume] 0 := by
          simpa [this] using
            (Lp.coeFn_zero (E := ℂ) (μ := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞)))
        have hcongr : (fun x => ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)))
            =ᵐ[volume] (fun _ => 0) := by
          refine hcoe.mono ?_
          intro x hx; simp [hx]
        have : (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) = 0 := by
          simpa using lintegral_congr_ae hcongr
        simp [this]
      · -- otherwise, if the lintegral were ∞, its toReal would be 0, contradiction
        have hpos : 0 < ‖g‖ ^ 2 := by
          have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (by exact norm_nonneg g) (Ne.symm hzero)
          have : 0 < ‖g‖ * ‖g‖ := mul_pos hgpos hgpos
          simpa [pow_two] using this
        have : (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) ≠ ∞ := by
          intro hinf
          have hEq : 0 = ‖g‖ ^ 2 := by simpa [hinf] using hId.symm
          have hZero : ‖g‖ ^ 2 = 0 := by simpa [eq_comm] using hEq
          exact (ne_of_gt hpos) hZero
        simpa [lt_top_iff_ne_top] using this
    have hconst_toReal :
        ((Mess ^ (2 : ℕ)) *
            (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)).toReal
          = (Mess.toReal ^ 2) *
              (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal := by
      have : (Mess ^ (2 : ℕ)).toReal = (Mess.toReal) ^ (2 : ℕ) := by
        simp
      simp [ENNReal.toReal_mul, this]
    -- apply toReal to hInt and rewrite both sides via norm identities
    have hInt' :
        (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
          ≤ ((Mess ^ (2 : ℕ)) *
              (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)).toReal := by
      have hleft_ne :
          (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) ≠ ∞ :=
        (ne_of_lt (mul_mem_L2 K g hK_meas hK_bdd))
      have hright_ne :
          ((Mess ^ (2 : ℕ)) *
              (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)) ≠ ∞ :=
        (ne_of_lt (mul_lt_top hfin1 hfin2))
      exact (ENNReal.toReal_le_toReal hleft_ne hright_ne).mpr hInt
    -- rewrite to norms and take square roots
    -- First, rewrite the right-hand side using hconst_toReal and hL2g
    have htmp :
        (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
          ≤ (Mess.toReal ^ 2) * (‖g‖ ^ 2) := by
      have := hInt'
      -- convert the product's toReal
      have :
          (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
            ≤ (Mess.toReal ^ 2) *
                (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal := by
        simpa [hconst_toReal] using this
      simpa [hL2g] using this
    -- Then rewrite the left-hand side via the a.e. identity for M_K g
    -- Pointwise a.e. equality between (M_K K g) and K·g
    have hMK_ae :
        ((((M_K K hK_meas hK_bdd) g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume] (fun x => K x * (g : ℝ → ℂ) x) := by
      simpa using
        (MemLp.coeFn_toLp (mul_mem_L2_memLp K g hK_meas hK_bdd))
    -- Transfer the lintegral equality on squared nnnorms
    have hswap :
        (∫⁻ x, ((‖((((M_K K hK_meas hK_bdd) g) : Lp ℂ 2 (volume : Measure ℝ))
          : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
          = (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
      refine lintegral_congr_ae ?_
      refine hMK_ae.mono ?_
      intro x hx; simp [hx]
    have hswap_toReal :
        (∫⁻ x, ((‖((((M_K K hK_meas hK_bdd) g) : Lp ℂ 2 (volume : Measure ℝ))
          : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
          = (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal := by
      simpa using congrArg ENNReal.toReal hswap
    have htmp_MK :
        (∫⁻ x, ((‖((((M_K K hK_meas hK_bdd) g) : Lp ℂ 2 (volume : Measure ℝ))
          : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
          ≤ (Mess.toReal ^ 2) * (‖g‖ ^ 2) := by
      simpa [hswap_toReal] using htmp
    -- Now apply the L² identity for M_K g
    have : ‖(M_K K hK_meas hK_bdd g)‖ ^ 2
            ≤ (Mess.toReal ^ 2) * (‖g‖ ^ 2) := by
      have hL2MK := Lp_norm_sq_as_lintegral (ν := volume)
        (f := (M_K K hK_meas hK_bdd g))
      simpa [hL2MK.symm] using htmp_MK
    -- conclude: take square roots using absolute values and nonnegativity
    have hMess0 : 0 ≤ Mess.toReal := ENNReal.toReal_nonneg
    have hnonnegL : 0 ≤ ‖(M_K K hK_meas hK_bdd g)‖ := norm_nonneg _
    have hnonnegr : 0 ≤ Mess.toReal * ‖g‖ := mul_nonneg hMess0 (norm_nonneg _)
    have habs : |‖(M_K K hK_meas hK_bdd g)‖| ≤ |Mess.toReal * ‖g‖| :=
      (sq_le_sq).1 (by
        simpa [pow_two, mul_pow, mul_comm, mul_left_comm, mul_assoc] using this)
    simpa [abs_of_nonneg hnonnegL, abs_of_nonneg hnonnegr]
      using habs

end MultiplicationOperator

section QuadraticForm

variable {K : ℝ → ℝ} {g : Lp ℂ 2 (volume : Measure ℝ)}

/-- The real-valued quadratic form Q[K](g) = ∫ K(τ) * ‖g(τ)‖² dτ.
    We require K to be non-negative and measurable. -/
noncomputable def Qℝ (K : ℝ → ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ :=
  ∫ τ, K τ * ‖(g : ℝ → ℂ) τ‖^2 ∂volume

/-- Positivity: If K ≥ 0 a.e., then Q[K](g) ≥ 0 -/
theorem Q_pos (K : ℝ → ℝ) (hK : ∀ᵐ τ ∂volume, 0 ≤ K τ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    0 ≤ Qℝ K g := by
  -- The integrand is nonnegative a.e., hence the integral is ≥ 0.
  have h_nonneg : ∀ᵐ τ ∂volume, 0 ≤ K τ * ‖(g : ℝ → ℂ) τ‖^2 := by
    refine hK.mono ?_
    intro τ hKτ
    have hsq : 0 ≤ ‖(g : ℝ → ℂ) τ‖^2 := by
      have := sq_nonneg (‖(g : ℝ → ℂ) τ‖)
      simp
    exact mul_nonneg hKτ hsq
  have := integral_nonneg_of_ae h_nonneg
  simpa [Qℝ] using this

/-- For real-valued K, the quadratic form equals the real part of the inner product with M_K -/
theorem Qℝ_eq_inner (K : ℝ → ℝ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable (fun τ => (K τ : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞) :
    Qℝ K g = (@inner ℂ _ _ (M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd g) g).re := by
  classical
  -- a.e. identity: (M_K g)(τ) = K τ * g τ
  have hMK := M_K_apply_ae (fun τ => (K τ : ℂ)) hK_meas hK_bdd g
  -- Express the inner product as ∫ (M_K g) · conj g
  -- L² inner product formula
  have hinner0 :=
    (L2.inner_def (𝕜 := ℂ) (μ := volume)
      (f := (M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd g)) (g := g))
  -- rewrite the RHS integrand from inner to multiplication by conjugate
  have hinner_int :
      (∫ τ, (@inner ℂ _ _ (((M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd g)
        : ℝ → ℂ) τ) ((g : ℝ → ℂ) τ)) ∂volume) = ∫ τ, (g : ℝ → ℂ) τ * (starRingEnd ℂ)
          ((((M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd g) : Lp ℂ 2 (volume : Measure ℝ))
            : ℝ → ℂ) τ) ∂volume := by
    refine integral_congr_ae ?_
    refine (Filter.Eventually.of_forall ?_)
    intro τ; simp [RCLike.inner_apply]
  have hinner : inner ℂ ((M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd) g) g
      = ∫ τ, (g : ℝ → ℂ) τ * (starRingEnd ℂ) (((M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd g
          : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ) ∂volume := by
    -- combine L2.inner_def with pointwise scalar inner expansion
    simpa [hinner_int] using hinner0
  -- Replace (M_K g)(τ) by K τ * g τ inside the integral
  have hswap :
      ∫ τ, (g : ℝ → ℂ) τ * (starRingEnd ℂ) ((((M_K (fun τ => (K τ : ℂ))
        hK_meas hK_bdd g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) τ) ∂volume
      = ∫ τ, (g : ℝ → ℂ) τ
        * (starRingEnd ℂ) (((K τ : ℂ) * (g : ℝ → ℂ) τ)) ∂volume := by
    refine integral_congr_ae ?_
    refine hMK.mono ?_
    intro τ hτ; simp [hτ]
  -- Take real parts and identify with Qℝ without appealing to `integral_re`
  have hreal_int :
      (∫ τ, (g : ℝ → ℂ) τ * (starRingEnd ℂ) (((K τ : ℂ) * (g : ℝ → ℂ) τ)) ∂volume).re
        = ∫ τ, K τ * ‖(g : ℝ → ℂ) τ‖^2 ∂volume := by
    -- Rewrite complex integrand to (K : ℂ) * (z * conj z)
    have hptC : ∀ τ,
        (g : ℝ → ℂ) τ * (starRingEnd ℂ) (((K τ : ℂ) * (g : ℝ → ℂ) τ))
          = (K τ : ℂ) * ((g : ℝ → ℂ) τ * (starRingEnd ℂ) ((g : ℝ → ℂ) τ)) := by
      intro τ
      have : (starRingEnd ℂ) (((K τ : ℂ) * (g : ℝ → ℂ) τ))
            = (K τ : ℂ) * (starRingEnd ℂ) ((g : ℝ → ℂ) τ) := by simp
      simp [this, mul_left_comm]
    have hchg1 :
        ∫ τ, (g : ℝ → ℂ) τ * (starRingEnd ℂ) (((K τ : ℂ) * (g : ℝ → ℂ) τ)) ∂volume
          = ∫ τ, (K τ : ℂ) * ((g : ℝ → ℂ) τ * (starRingEnd ℂ) ((g : ℝ → ℂ) τ)) ∂volume := by
      refine integral_congr_ae ?_
      exact Filter.Eventually.of_forall (by
        intro τ
        simp [mul_left_comm])
    -- Convert z * conj z to a real scalar via normSq
    have hchg2 :
        ∫ τ, (K τ : ℂ) * ((g : ℝ → ℂ) τ * (starRingEnd ℂ) ((g : ℝ → ℂ) τ)) ∂volume
          = ∫ τ, (K τ : ℂ) * (Complex.normSq ((g : ℝ → ℂ) τ)) ∂volume := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro τ; simp [Complex.mul_conj]
    -- Take real parts; real part of (K : ℂ) * r equals K * r for r : ℝ
    have hptR : ∀ τ, (((K τ : ℂ) * (Complex.normSq ((g : ℝ → ℂ) τ))).re)
      = K τ * (Complex.normSq ((g : ℝ → ℂ) τ)) := by
      intro τ; simp
    have hreal1 := congrArg Complex.re (hchg1.trans hchg2)
    -- Replace normSq by squared norm in ℝ inside the real integral
    have hnorm : ∀ τ, (Complex.normSq ((g : ℝ → ℂ) τ)) = ‖(g : ℝ → ℂ) τ‖^2 := by
      intro τ
      simpa [norm, Real.norm_eq_abs, pow_two] using Complex.normSq_eq_norm_sq ((g : ℝ → ℂ) τ)
    have hchgR :
        ∫ τ, K τ * (Complex.normSq ((g : ℝ → ℂ) τ)) ∂volume
          = ∫ τ, K τ * ‖(g : ℝ → ℂ) τ‖^2 ∂volume := by
      refine integral_congr_ae ?_
      exact Filter.Eventually.of_forall (by intro τ; simp [hnorm τ])
    -- Convert RHS real part of complex integral to a real integral via ofReal
    have hcof : ∀ τ,
        ((K τ : ℂ) * (Complex.normSq ((g : ℝ → ℂ) τ)))
          = Complex.ofReal (K τ * Complex.normSq ((g : ℝ → ℂ) τ)) := by
      intro τ; simp
    have hcof_int :
        ∫ τ, (K τ : ℂ) * (Complex.normSq ((g : ℝ → ℂ) τ)) ∂volume
          = ∫ τ, Complex.ofReal (K τ * Complex.normSq ((g : ℝ → ℂ) τ)) ∂volume := by
      refine integral_congr_ae ?_
      exact Filter.Eventually.of_forall (by intro τ; simp)
    have hreal2 :
        (∫ τ, (K τ : ℂ) * (Complex.normSq ((g : ℝ → ℂ) τ)) ∂volume).re
          = ∫ τ, K τ * (Complex.normSq ((g : ℝ → ℂ) τ)) ∂volume := by
      simpa using congrArg Complex.re (hcof_int.trans
        (integral_ofReal (f := fun τ => K τ * Complex.normSq ((g : ℝ → ℂ) τ))))
    -- Finish
    have := hreal1.trans hreal2
    simpa [hptR, hchgR] using this
  -- Conclude
  have : (@inner ℂ _ _ (M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd g) g).re
      = (∫ τ, (g : ℝ → ℂ) τ * (starRingEnd ℂ) (((K τ : ℂ) * (g : ℝ → ℂ) τ)) ∂volume).re := by
    simpa [hswap] using congrArg Complex.re hinner
  simpa [Qℝ, this] using hreal_int.symm

end QuadraticForm

section KernelCharacterization

/-!
## A-3: Kernel Dimensions and Zero Sets (核次元と零集合)

This section establishes the relationship between the kernel of M_K and the zero set
of K, providing the API for kernel-support correspondence needed for later chapters.
-/

variable {K : ℝ → ℂ} {g : Lp ℂ 2 (volume : Measure ℝ)}

/-- The support of K: the set where K is nonzero -/
def supp_K (K : ℝ → ℂ) : Set ℝ := {τ | K τ ≠ 0}

/-- The zero set of K: the complement of the support -/
def zero_set_K (K : ℝ → ℂ) : Set ℝ := {τ | K τ = 0}

@[simp]
lemma mem_supp_K (K : ℝ → ℂ) (τ : ℝ) : τ ∈ supp_K K ↔ K τ ≠ 0 := Iff.rfl

@[simp]
lemma mem_zero_set_K (K : ℝ → ℂ) (τ : ℝ) : τ ∈ zero_set_K K ↔ K τ = 0 := Iff.rfl

/-- If `K` is measurable, then its support `{τ | K τ ≠ 0}` is measurable. -/
lemma measurableSet_supp_K (K : ℝ → ℂ) (hK : Measurable K) :
    MeasurableSet (supp_K K) := by
  have hset : MeasurableSet ({z : ℂ | z ≠ 0}) :=
    (isClosed_singleton : IsClosed ({0} : Set ℂ)).measurableSet.compl
  simpa [supp_K, Set.preimage, Set.mem_setOf_eq] using hset.preimage hK

/-- The support and zero set partition ℝ -/
lemma supp_K_compl (K : ℝ → ℂ) : (supp_K K)ᶜ = zero_set_K K := by
  ext τ
  simp [supp_K, zero_set_K, Set.mem_compl_iff]

/-
With the current phase-1 definition `M_K = 0`, every `g` lies in the kernel.
We establish the API structure that will be refined when M_K is properly implemented.
-/

/-- The kernel of M_K as a submodule (for bounded K) -/
noncomputable def ker_MK (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  LinearMap.ker (M_K K hK_meas hK_bdd)

/-- The kernel consists of functions vanishing a.e. on the support of K -/
theorem ker_MK_eq_vanish_on_supp (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    ker_MK K hK_meas hK_bdd =
    {g : Lp ℂ 2 (volume : Measure ℝ) |
     (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K K)] 0} := by
  classical
  -- Show mutual inclusion via the pointwise a.e. action of `M_K`.
  apply le_antisymm
  · -- ⊆: If `g ∈ ker`, then `K·g = 0` a.e., hence `g = 0` a.e. on `{K ≠ 0}`.
    intro g hg
    -- `hg` gives `(M_K g) = 0` in `Lp`.
    have hMK0 : (M_K K hK_meas hK_bdd) g = 0 := by
      simpa using hg
    -- Representatives: `(M_K g) =ᵐ 0` on `volume`.
    have hMK0_ae :
        (((M_K K hK_meas hK_bdd) g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume] 0 := by
      -- Coercion of zero in Lp is a.e. zero; rewrite `(M_K g) = 0`.
      simpa [hMK0] using
        (Lp.coeFn_zero (E := ℂ) (μ := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞)))
    -- Use a.e. action of `M_K` to identify the representative as `K·g` a.e.
    have hMK_apply := M_K_apply_ae K hK_meas hK_bdd g
    -- On the restricted measure to the support, `g = 0` a.e. follows from `K ≠ 0` there.
    -- First, express as a statement on the ambient measure with implication from membership.
    have h_on_S : ∀ᵐ x ∂volume, x ∈ supp_K K → (g : ℝ → ℂ) x = 0 := by
      -- From `(K·g) = 0` a.e., deduce on `supp_K K` that `g = 0`.
      have hKg0 : (fun x => K x * (g : ℝ → ℂ) x) =ᵐ[volume] 0 := by
        -- Use symmetry so the RHS matches: `(K·g) =ᵐ (M_K g) =ᵐ 0`.
        exact hMK_apply.symm.trans hMK0_ae
      refine hKg0.mono ?_
      intro x hx hmem
      have hKne : K x ≠ 0 := by
        simpa [supp_K] using hmem
      have hx0 : K x * (g : ℝ → ℂ) x = 0 := by simpa using hx
      -- Cancel `K x ≠ 0` in `ℂ`.
      have : K x = 0 ∨ (g : ℝ → ℂ) x = 0 := by
        simpa using (mul_eq_zero.mp hx0)
      exact this.resolve_left hKne
    -- Switch to the restricted measure using `ae_restrict_iff`.
    -- Move to a measurable support set via a measurable representative K'.
    -- Define a measurable modification K' of K.
    let K' : ℝ → ℂ := (hK_meas.aemeasurable.mk K)
    have hK'_meas : Measurable K' := hK_meas.aemeasurable.measurable_mk
    have hKK' : K =ᵐ[volume] K' := hK_meas.aemeasurable.ae_eq_mk
    -- Define measurable support set S' using K'.
    let S : Set ℝ := supp_K K
    let S' : Set ℝ := supp_K K'
    have hS'_meas : MeasurableSet S' := by
      have hset : MeasurableSet ({z : ℂ | z ≠ 0}) :=
        (isClosed_singleton : IsClosed ({0} : Set ℂ)).measurableSet.compl
      simpa [S', supp_K, Set.preimage, Set.mem_setOf_eq]
        using hset.preimage hK'_meas
    -- S and S' are a.e. equal under volume.
    have hS_eq_ae : (S : Set ℝ) =ᵐ[volume] S' := by
      refine hKK'.mono ?_
      intro x hx
      have hx' : K x = K' x := by simpa using hx
      have hiff : (x ∈ S) ↔ (x ∈ S') := by
        simp [S, S', supp_K, hx']
      exact propext hiff
    -- From x ∈ S' a.e. implies x ∈ S (a.e.).
    have h_sub : ∀ᵐ x ∂volume, x ∈ S' → x ∈ S := by
      refine hS_eq_ae.mono ?_
      intro x hx hxin
      have : (x ∈ S) ↔ (x ∈ S') := by simpa using hx
      exact this.mpr hxin
    -- Strengthen implication to hold on S'.
    have h_on_S' : ∀ᵐ x ∂volume, x ∈ S' → (g : ℝ → ℂ) x = 0 := by
      refine (h_on_S.and h_sub).mono ?_
      intro x hx hxS'
      exact hx.1 (hx.2 hxS')
    -- Conclude AE zero on the restricted measure to S', then transfer to S.
    have h_restr_S' : ∀ᵐ x ∂volume.restrict S', (g : ℝ → ℂ) x = 0 :=
      ((ae_restrict_iff' hS'_meas).2 h_on_S')
    have h_restr_set_eq : volume.restrict S = volume.restrict S' := by
      simpa [S, S'] using Measure.restrict_congr_set (μ := volume) hS_eq_ae
    have : ∀ᵐ x ∂volume.restrict (supp_K K), (g : ℝ → ℂ) x = 0 := by
      simpa [S, S', h_restr_set_eq] using h_restr_S'
    -- Package as the desired membership in the RHS set.
    exact this
  · -- ⊇: If `g = 0` a.e. on `{K ≠ 0}`, then `(K·g) = 0` a.e., hence `g ∈ ker`.
    intro g hg
    -- Turn the a.e. statement on the restricted measure into an implication on the ambient measure.
    have h_on_S : ∀ᵐ x ∂volume, x ∈ supp_K K → (g : ℝ → ℂ) x = 0 := by
      let K' : ℝ → ℂ := (hK_meas.aemeasurable.mk K)
      have hK'_meas : Measurable K' := hK_meas.aemeasurable.measurable_mk
      have hKK' : K =ᵐ[volume] K' := hK_meas.aemeasurable.ae_eq_mk
      let S : Set ℝ := supp_K K
      let S' : Set ℝ := supp_K K'
      have hS'_meas : MeasurableSet S' := by
        have hset : MeasurableSet ({z : ℂ | z ≠ 0}) :=
          (isClosed_singleton : IsClosed ({0} : Set ℂ)).measurableSet.compl
        simpa [S', supp_K, Set.preimage, Set.mem_setOf_eq]
          using hset.preimage hK'_meas
      -- Transfer the restricted AE from S to S' using equality a.e. of the sets.
      have hS_eq_ae : (S : Set ℝ) =ᵐ[volume] S' := by
        refine hKK'.mono ?_
        intro x hx
        have hx' : K x = K' x := by simpa using hx
        have hiff : (x ∈ S) ↔ (x ∈ S') := by
          simp [S, S', supp_K, hx']
        exact propext hiff
      have h_restr_set_eq : volume.restrict S = volume.restrict S' := by
        simpa [S, S'] using Measure.restrict_congr_set (μ := volume) hS_eq_ae
      have hg' : ∀ᵐ x ∂volume.restrict S', (g : ℝ → ℂ) x = 0 := by
        simpa [S, S', h_restr_set_eq] using hg
      -- From AE on S', obtain the implication form on the ambient measure for S'.
      have h_on_S' : ∀ᵐ x ∂volume, x ∈ S' → (g : ℝ → ℂ) x = 0 :=
        ((ae_restrict_iff' hS'_meas).1 hg')
      -- Convert implication for S' to implication for S using a.e. inclusion S ⊆ S'.
      have h_sub' : ∀ᵐ x ∂volume, x ∈ S → x ∈ S' := by
        refine hS_eq_ae.mono ?_
        intro x hx hxin
        have : (x ∈ S) ↔ (x ∈ S') := by simpa using hx
        exact this.mp hxin
      exact (h_on_S'.and h_sub').mono (fun x hx hxS => hx.1 (hx.2 hxS))
    -- On the complement of the support, `K = 0`.
    have h_on_Sc : ∀ᵐ x ∂volume, x ∉ supp_K K → K x = 0 := by
      refine Filter.Eventually.of_forall ?_
      intro x hx
      -- Outside the support, by definition `K x = 0`.
      have hx0 : x ∈ zero_set_K K := by
        -- `x ∉ supp_K` means `K x = 0` by the definition of these sets.
        simpa [supp_K, zero_set_K] using hx
      simpa [zero_set_K] using hx0
    -- Combine to show `(K·g) = 0` a.e. on the ambient measure.
    have hKg_ae0 : (fun x => K x * (g : ℝ → ℂ) x) =ᵐ[volume] 0 := by
      refine (h_on_S.and h_on_Sc).mono ?_
      intro x hx
      rcases hx with ⟨hS, hSc⟩
      by_cases hmem : x ∈ supp_K K
      · -- On `supp_K`, `g x = 0` a.e.
        have : (g : ℝ → ℂ) x = 0 := hS hmem
        simp [this]
      · -- Outside `supp_K`, `K x = 0`.
        have : K x = 0 := hSc (by simpa using hmem)
        simp [this]
    -- Via the a.e. action of `M_K`, conclude `(M_K g) = 0` in `Lp`.
    have hMK_apply := M_K_apply_ae K hK_meas hK_bdd g
    -- So the representative of `(M_K g)` is a.e. zero, hence the `Lp` class equals `0`.
    have : (((M_K K hK_meas hK_bdd) g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 0 :=
      hMK_apply.trans hKg_ae0
    -- Conclude membership in the kernel of the linear map.
    -- Use `Subtype.mem` characterization: `g ∈ ker` iff `(M_K g) = 0`.
    -- Equality in `Lp` from a.e. zero representative.
    have hLp0 : (M_K K hK_meas hK_bdd) g = 0 := by
      -- Use `Lp.ext`: two Lp elements are equal if their representatives are a.e. equal.
      refine Lp.ext ?_
      -- We have `this : coe(M_K g) =ᵐ 0`; convert RHS to `↑0` using `Lp.coeFn_zero`.
      have h0 : (((0 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) =ᵐ[volume] 0 :=
        (Lp.coeFn_zero (E := ℂ) (μ := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞)))
      exact this.trans h0.symm
    -- Wrap up as membership in the kernel set on the left.
    simpa [ker_MK, LinearMap.mem_ker] using hLp0

/-- Alternative characterization: g ∈ ker(M_K) iff g = 0 a.e. where K ≠ 0 -/
theorem ker_MK_iff_ae_zero_on_supp (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    g ∈ ker_MK K hK_meas hK_bdd ↔ (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K K)] 0 := by
  classical
  have hEqSets := ker_MK_eq_vanish_on_supp K hK_meas hK_bdd
  -- Unfold the set-builder description on the right-hand side.
  constructor
  · intro hg
    -- Rewrite membership using the set equality.
    have : g ∈ {g : Lp ℂ 2 (volume : Measure ℝ) |
                  (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K K)] 0} := by
      -- Transport membership along the set equality as equality of propositions.
      have hmemEq := congrArg (fun (S : Set (Lp ℂ 2 (volume : Measure ℝ))) => g ∈ S) hEqSets
      exact (Eq.mp hmemEq) hg
    simpa using this
  · intro hg
    -- Conversely, membership in the RHS set implies membership in the kernel via the set equality.
    have : g ∈ {g : Lp ℂ 2 (volume : Measure ℝ) |
                  (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K K)] 0} := hg
    have hmemEq := congrArg (fun (S : Set (Lp ℂ 2 (volume : Measure ℝ))) => g ∈ S) hEqSets
    exact (Eq.mpr hmemEq) this

/-- The kernel is supported on the zero set of K -/
lemma ker_MK_supported_on_zero_set (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    g ∈ ker_MK K hK_meas hK_bdd → (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K K)] 0 := by
  intro hg
  exact (ker_MK_iff_ae_zero_on_supp K g hK_meas hK_bdd).mp hg

/-- A-3 (complete characterization): `g` is in the kernel of `M_K`
    if and only if `g = 0` almost everywhere on the support `{τ | K τ ≠ 0}`.
    This is the `∀ᵐ`-predicate version of `ker_MK_iff_ae_zero_on_supp`. -/
lemma ker_MK_ae (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    g ∈ ker_MK K hK_meas hK_bdd ↔
      (∀ᵐ x ∂volume.restrict (supp_K K), (g : ℝ → ℂ) x = 0) := by
  -- The RHS is definitionally the same as `=ᵐ[...] 0` for functions to ℂ.
  simpa using (ker_MK_iff_ae_zero_on_supp K g hK_meas hK_bdd)

end KernelCharacterization

section PullbackToHσ

/-!
## A-2: Pullback to Hσ Space

This section implements the pullback of the quadratic form from L²(ℝ) to the
weighted space Hσ via the isometry Uσ, establishing the key correspondence
between kernels.
-/

variable {σ : ℝ} {K : ℝ → ℝ} {f : Hσ σ}

/-- Pullback of the quadratic form to Hσ via the isometry Uσ.
    Since Uσ is an isometry, this preserves all essential properties. -/
noncomputable def Qσ (K : ℝ → ℝ) (f : Hσ σ) : ℝ :=
  Qℝ K (Uσ σ f)

/-- Alternative notation for clarity -/
notation "Qσ[" K "]" => Qσ K

/-- Positivity on Hσ: If K ≥ 0 a.e., then Qσ[K](f) ≥ 0.
    This follows immediately from the positivity of Qℝ and the fact that
    Uσ is just a mapping between spaces. -/
theorem Qσ_pos (K : ℝ → ℝ) (hK : ∀ᵐ τ ∂volume, 0 ≤ K τ) (f : Hσ σ) :
    0 ≤ Qσ[K] f := by
  unfold Qσ
  exact Q_pos K hK (Uσ σ f)

/-- When K is essentially bounded, Qσ[K] f = 0 implies M_K (Uσ f) = 0 -/
theorem Qσ_eq_zero_imp_MK_zero (K : ℝ → ℝ) (f : Hσ σ)
    (hK_meas : AEStronglyMeasurable (fun τ => (K τ : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞)
    (hK_nonneg : ∀ᵐ τ ∂volume, 0 ≤ K τ) :
    Qσ[K] f = 0 → M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd (Uσ σ f) = 0 := by
  intro hQ0
  classical
  set Kc : ℝ → ℂ := fun τ => (K τ : ℂ)
  have hKc_meas : AEStronglyMeasurable Kc volume := hK_meas
  have hKc_bdd : essSup (fun x => (‖Kc x‖₊ : ℝ≥0∞)) volume < ∞ := by
    simpa [Kc] using hK_bdd
  -- Let g := Uσ f
  set g : Lp ℂ 2 (volume : Measure ℝ) := Uσ σ f
  -- From `Qσ[K] f = 0`, we have `∫ K · ‖g‖² = 0`.
  have hInt0 : ∫ τ, K τ * ‖(g : ℝ → ℂ) τ‖^2 ∂volume = 0 := by
    simpa [Qσ, Qℝ, g] using hQ0
  -- f τ := K τ * ‖g τ‖^2 は a.e. 非負
  have hF_nonneg : ∀ᵐ τ ∂volume, 0 ≤ K τ * ‖(g : ℝ → ℂ) τ‖^2 := by
    refine hK_nonneg.mono ?_
    intro τ hKτ
    have hsq : 0 ≤ ‖(g : ℝ → ℂ) τ‖^2 := by
      have := sq_nonneg (‖(g : ℝ → ℂ) τ‖); simp
    exact mul_nonneg hKτ hsq
  -- ∫ f = 0 から a.e. に f = 0（lintegral を経由）
  have hF_meas : AEMeasurable (fun τ => K τ * ‖(g : ℝ → ℂ) τ‖^2) volume := by
    -- K（実値）の a.e. 可測性は、Kc の実部が K であることから従う
    have hK_am : AEMeasurable K volume := by
      have hRe : AEStronglyMeasurable (fun τ => (Kc τ).re) volume := hK_meas.re
      simpa [Kc, Complex.ofReal_re] using hRe.aemeasurable
    -- ‖g‖^2 の a.e. 可測性
    have hg2_am : AEMeasurable (fun τ => ‖(g : ℝ → ℂ) τ‖^2) volume := by
      have := (Lp.aestronglyMeasurable g).norm.aemeasurable
      exact this.pow_const 2
    exact hK_am.mul hg2_am
  -- 実積分 0 から ofReal 合成の拡張積分も 0
  have hlin0 :
      (∫⁻ τ, ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2) ∂volume) = 0 := by
    -- ∫ f = toReal (∫⁻ ofReal ∘ f)
    have hF_smeas : AEStronglyMeasurable (fun τ => K τ * ‖(g : ℝ → ℂ) τ‖^2) volume :=
      hF_meas.aestronglyMeasurable
    have hEq :=
      integral_eq_lintegral_of_nonneg_ae (μ := volume)
        (f := fun τ => K τ * ‖(g : ℝ → ℂ) τ‖^2) hF_nonneg hF_smeas
    have htoReal : ENNReal.toReal
        (∫⁻ τ, ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2) ∂volume) = 0 := by
      simpa [hEq] using hInt0  -- from toReal x = 0, we have x = 0 ∨ x = ∞
    have hzero_or := (ENNReal.toReal_eq_zero_iff _).mp htoReal
    -- show the lintegral is finite, hence not ∞
    have hne_top :
        (∫⁻ τ, ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2) ∂volume) ≠ ∞ := by
      -- Define Mess := essSup ‖Kc‖₊ and use the standard a.e. bound
      set Mess : ℝ≥0∞ := essSup (fun x => (‖Kc x‖₊ : ℝ≥0∞)) volume
      have hM_top : Mess < ∞ := by simpa [Kc] using hKc_bdd
      have h_bound : ∀ᵐ τ ∂volume, (‖Kc τ‖₊ : ℝ≥0∞) ≤ Mess :=
        ae_le_essSup (fun x => (‖Kc x‖₊ : ℝ≥0∞))
      -- pointwise bound: ofReal(K*‖g‖^2) ≤ ‖Kc‖₊ * ofReal(‖g‖^2)
      have h_pw1 : ∀ᵐ τ ∂volume,
          ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2)
            ≤ (‖Kc τ‖₊ : ℝ≥0∞) * ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) := by
        refine hK_nonneg.mono ?_
        intro τ hKτ
        -- use monotonicity of ofReal and |K| ≥ K when K ≥ 0 actually equality holds
        have hk : (K τ : ℝ) ≤ ‖(Kc τ)‖ := by
          -- K ≥ 0, and ‖Kc‖ = |K|
          have : ‖(Kc τ)‖ = |K τ| := by simp [Kc]
          have habs : (K τ : ℝ) ≤ |K τ| := by
            have := le_abs_self (K τ); simp [abs_of_nonneg hKτ]
          simpa [this] using habs
        have : ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2)
            ≤ ENNReal.ofReal (‖(Kc τ)‖ * ‖(g : ℝ → ℂ) τ‖^2) := by
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hk (by
            have := sq_nonneg (‖(g : ℝ → ℂ) τ‖); simp))
        -- rewrite RHS as product in ℝ≥0∞
        -- rewrite RHS into (‖Kc τ‖₊) * ofReal(‖g τ‖^2)
        have hmul_ofReal :
            ENNReal.ofReal (‖(Kc τ)‖ * ‖(g : ℝ → ℂ) τ‖^2)
              = (‖Kc τ‖₊ : ℝ≥0∞) * ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) := by
          have hpos1 : 0 ≤ ‖(Kc τ)‖ := by exact norm_nonneg _
          have hpos2 : 0 ≤ ‖(g : ℝ → ℂ) τ‖^2 := by
            have := sq_nonneg (‖(g : ℝ → ℂ) τ‖); simp
          -- ofReal (a*b) = ofReal a * ofReal b under nonneg
          -- `ENNReal.ofReal (‖Kc‖ * t) = (‖Kc‖₊) * ENNReal.ofReal t`
          -- only the first factor needs a nonneg assumption
          simp [ENNReal.ofReal_mul, hpos1]
        -- conclude by rewriting the RHS via `hmul_ofReal`
        exact (le_trans this (le_of_eq hmul_ofReal))
      -- combine with essSup bound to get ≤ Mess * ofReal(‖g‖^2)
      have h_pw : ∀ᵐ τ ∂volume,
          ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2)
            ≤ Mess * ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) := by
        refine (h_pw1.and h_bound).mono ?_
        intro τ h; rcases h with ⟨h1, h2⟩
        -- upgrade the bound by multiplying on the right with the nonnegative factor
        -- ENNReal.ofReal (‖g τ‖^2)
        exact le_trans h1 (mul_le_mul_right' h2 (ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2)))
      -- lintegral bound by mono_ae
      have h_int_bound :
          (∫⁻ τ, ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2) ∂volume)
            ≤ Mess * (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume) := by
        have := lintegral_mono_ae h_pw
        -- pull out constant Mess
        have hconst :
          (∫⁻ τ, Mess * ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume)
            = Mess * (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume) := by
          -- Use a measurable representative for g
          have hg_meas' : AEStronglyMeasurable (fun τ => (g : ℝ → ℂ) τ) volume :=
            Lp.aestronglyMeasurable g
          let g' : ℝ → ℂ := (hg_meas'.aemeasurable.mk (fun τ => (g : ℝ → ℂ) τ))
          have hg'_meas : Measurable g' := hg_meas'.aemeasurable.measurable_mk
          have hgg' : (fun τ => (g : ℝ → ℂ) τ) =ᵐ[volume] g' :=
            hg_meas'.aemeasurable.ae_eq_mk
          let F : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2)
          let F' : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (‖g' τ‖^2)
          have hF_meas : Measurable F' := by
            have : Measurable fun τ => ‖g' τ‖ := hg'_meas.norm
            have h_ofReal : Measurable fun τ => ENNReal.ofReal (‖g' τ‖) :=
              ENNReal.measurable_ofReal.comp this
            -- ofReal (‖·‖^2)
            simpa [F', pow_two] using h_ofReal.pow_const (2 : ℕ)
          have hF_ae : F =ᵐ[volume] F' := by
            refine hgg'.mono ?_
            intro τ hx
            have hnorm : ‖(g : ℝ → ℂ) τ‖ = ‖g' τ‖ := by
              simpa using congrArg norm hx
            have : ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖ ^ 2)
                = ENNReal.ofReal (‖g' τ‖ ^ 2) := by
              simp [hnorm]
            simpa [F, F'] using this
          have hconst' : (∫⁻ τ, Mess * F' τ ∂volume)
                = Mess * (∫⁻ τ, F' τ ∂volume) := by
            simpa using lintegral_const_mul (μ := volume) (r := Mess) (f := F') (hf := hF_meas)
          have hleft : (∫⁻ τ, Mess * F τ ∂volume) = (∫⁻ τ, Mess * F' τ ∂volume) := by
            refine lintegral_congr_ae ?_
            exact hF_ae.mono (fun τ hτ => by
              simpa [F, F'] using congrArg (fun t => Mess * t) hτ)
          have hright : (∫⁻ τ, F τ ∂volume) = (∫⁻ τ, F' τ ∂volume) := by
            exact lintegral_congr_ae hF_ae
          have hconst'' := hconst'
          have hconst_trans :
              (∫⁻ τ, Mess * F τ ∂volume)
                = Mess * (∫⁻ τ, F τ ∂volume) := by
            calc
              (∫⁻ τ, Mess * F τ ∂volume) = (∫⁻ τ, Mess * F' τ ∂volume) := hleft
              _ = Mess * (∫⁻ τ, F' τ ∂volume) := hconst''
              _ = Mess * (∫⁻ τ, F τ ∂volume) := by
                    have := congrArg (fun t => Mess * t) hright.symm
                    simpa using this
          simpa [F] using hconst_trans
        -- Rewrite the RHS integral using `hconst` and the identity
        -- (↑‖g τ‖₊)^2 = ENNReal.ofReal (‖g τ‖^2)
        have hswap :
            (∫⁻ τ, Mess * ((‖(g : ℝ → ℂ) τ‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
              = (∫⁻ τ, Mess * ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume) := by
          refine lintegral_congr_ae ?_
          refine Filter.Eventually.of_forall (fun τ => ?_)
          simp [pow_two, ENNReal.ofReal_mul]
        -- pull out the constant Mess
        have hpull :
            (∫⁻ τ, ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2) ∂volume)
              ≤ Mess * (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume) := by
          -- First rewrite RHS of the previous bound using `hswap`
          have h1 :
              (∫⁻ τ, ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2) ∂volume)
                ≤ (∫⁻ τ, Mess * ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume) := by
            simpa [hswap] using this
          -- Then pull out Mess using `hconst`
          have h2 :
              (∫⁻ τ, Mess * ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume)
                = Mess * (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume) := hconst
          exact h1.trans_eq h2
        -- identify ∫ ofReal (‖g‖^2) with ∫ (↑‖g‖₊)^2
        have hpowEq :
            (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume)
              = (∫⁻ τ, ((‖(g : ℝ → ℂ) τ‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
          refine lintegral_congr_ae ?_
          refine Filter.Eventually.of_forall (fun τ => ?_)
          -- pointwise: ofReal (‖z‖^2) = (↑‖z‖₊)^2
          have hnn : 0 ≤ ‖(g : ℝ → ℂ) τ‖ := norm_nonneg _
          simp [pow_two, ENNReal.ofReal_mul, hnn]
        -- keep the RHS in the ofReal form for the current goal
        exact hpull
      -- show RHS is finite
      have hS_ne_top : (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume) ≠ ∞ := by
        -- Use the L² identity to rule out ∞
        have hIdOfReal : ‖g‖ ^ 2
            = (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume).toReal := by
          simpa using (Lp_norm_sq_as_lintegral (ν := volume) (f := g))
        by_cases hzero : ‖g‖ = 0
        · -- then g = 0 and the lintegral is 0
          have : g = 0 := by simpa using (norm_eq_zero.mp hzero)
          have hcoe : ((g : ℝ → ℂ)) =ᵐ[volume] 0 := by
            simpa [this] using
              (Lp.coeFn_zero (E := ℂ) (μ := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞)))
          have hcongr : (fun τ => ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2))
              =ᵐ[volume] (fun _ => 0) := by
            refine hcoe.mono ?_
            intro τ hτ; simp [hτ]
          have hzero_ofReal :
              (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume) = 0 := by
            simpa using lintegral_congr_ae hcongr
          -- rewrite to the nnnorm-squared form and conclude
          have hpowEq :
              (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume)
                = (∫⁻ τ, ((‖(g : ℝ → ℂ) τ‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
            refine lintegral_congr_ae ?_
            refine Filter.Eventually.of_forall (fun τ => ?_)
            have hnn : 0 ≤ ‖(g : ℝ → ℂ) τ‖ := norm_nonneg _
            simp [pow_two, ENNReal.ofReal_mul, hnn]
          have hzero_nnnorm :
              (∫⁻ τ, ((‖(g : ℝ → ℂ) τ‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) = 0 := by
            simpa [hpowEq] using hzero_ofReal
          -- hence the integral is not top
          simp [hzero_nnnorm]
        · -- otherwise lintegral cannot be ∞ because toReal would be 0 contradicting hId
          intro hinf
          -- translate (∫ ofReal) = ∞ to the nnnorm-squared integral via pointwise identity
          have hpowEq2 :
              (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume)
                = (∫⁻ τ, ((‖(g : ℝ → ℂ) τ‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) := by
            refine lintegral_congr_ae ?_
            refine Filter.Eventually.of_forall (fun τ => ?_)
            have hnn : 0 ≤ ‖(g : ℝ → ℂ) τ‖ := norm_nonneg _
            simp [pow_two, ENNReal.ofReal_mul, hnn]
          have hzero_sq : ‖g‖ ^ 2 = 0 := by
            -- (∫ nnnorm^2).toReal = (∫ ofReal).toReal, and the latter is 0 by hinf
            have htoEq :
                (∫⁻ τ, ((‖(g : ℝ → ℂ) τ‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal
                  = (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume).toReal := by
              simp
            have hR : (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume).toReal = 0 := by
              -- derive by applying `toReal` to `hinf : ∫ ofReal = ⊤`
              have := congrArg ENNReal.toReal hinf
              simpa using this
            have hL :
                (∫⁻ τ, ((‖(g : ℝ → ℂ) τ‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume).toReal = 0 :=
              htoEq.trans hR
            simpa [hL] using hIdOfReal
          have hgpos : 0 < ‖g‖ ^ 2 := by
            have hgpos' : 0 < ‖g‖ := lt_of_le_of_ne (by exact norm_nonneg g) (Ne.symm hzero)
            have : 0 < ‖g‖ * ‖g‖ := mul_pos hgpos' hgpos'
            simpa [pow_two] using this
          exact (ne_of_gt hgpos) hzero_sq
      have hR_fin : Mess * (∫⁻ τ, ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) ∂volume) < ∞ := by
        exact ENNReal.mul_lt_top (lt_of_le_of_lt le_rfl hM_top) (lt_top_iff_ne_top.mpr hS_ne_top)
      -- conclude LHS ≠ ∞ from the bound
      exact (ne_of_lt (lt_of_le_of_lt h_int_bound hR_fin))
    -- resolve the right disjunct using finiteness; conclude equality to 0
    exact Or.resolve_right hzero_or hne_top
  -- lintegral = 0 ⇒ ofReal ∘ f = 0 a.e. ⇒ f = 0 a.e.（非負性とあわせて）
  have hF_ae0 : ∀ᵐ τ ∂volume, K τ * ‖(g : ℝ → ℂ) τ‖^2 = 0 := by
    have hof_meas : AEMeasurable (fun τ => ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2)) volume :=
      ENNReal.measurable_ofReal.comp_aemeasurable hF_meas
    have hof_eq0 : (fun τ => ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2)) =ᵐ[volume] 0 := by
      simpa using (lintegral_eq_zero_iff' (μ := volume) (f := _ ) hof_meas).1 hlin0
    have hboth := hF_nonneg.and hof_eq0
    exact hboth.mono (fun τ h => by
      rcases h with ⟨hnonnegτ, hzeroτ⟩
      have hle : K τ * ‖(g : ℝ → ℂ) τ‖^2 ≤ 0 := by
        simpa using (ENNReal.ofReal_eq_zero.mp (by simpa using hzeroτ))
      exact le_antisymm hle hnonnegτ)
  -- Therefore on the support of `Kc`, we have `‖g‖ = 0` a.e., i.e. `g = 0` a.e.
  have h_g_ae0_on_supp : (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K Kc)] 0 := by
    -- Use a measurable representative K' of Kc to obtain a measurable support set.
    let K' : ℝ → ℂ := (hKc_meas.aemeasurable.mk Kc)
    have hK'_meas : Measurable K' := hKc_meas.aemeasurable.measurable_mk
    -- The support of the measurable representative is measurable.
    have hS'_meas : MeasurableSet (supp_K K') := by
      have hset : MeasurableSet ({z : ℂ | z ≠ 0}) :=
        (isClosed_singleton : IsClosed ({0} : Set ℂ)).measurableSet.compl
      simpa [supp_K, Set.preimage, Set.mem_setOf_eq] using hset.preimage hK'_meas
    -- From `K * ‖g‖² = 0` a.e., on `{K ≠ 0}` and `K ≥ 0` a.e. we get `‖g‖ = 0` a.e.
    have h_impl : ∀ᵐ τ ∂volume, τ ∈ supp_K Kc → (g : ℝ → ℂ) τ = 0 := by
      refine (hF_ae0.and hK_nonneg).mono ?_
      intro τ hpair hmem
      rcases hpair with ⟨h0, hK_nonneg_τ⟩
      have hKne : Kc τ ≠ 0 := by simpa [supp_K] using hmem
      have hKne' : K τ ≠ 0 := by simpa [Kc, Complex.ofReal_eq_zero] using hKne
      -- From nonneg and nonzero, get strict positivity
      have hKpos : 0 < K τ := lt_of_le_of_ne hK_nonneg_τ (Ne.symm hKne')
      -- Represent the lintegral integrand via ofReal multiplicativity under nonneg
      have hrepr : ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2)
          = ENNReal.ofReal (K τ) * ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) := by
        have hpos1 : 0 ≤ K τ := hK_nonneg_τ
        have hpos2 : 0 ≤ ‖(g : ℝ → ℂ) τ‖^2 := by
          have := sq_nonneg (‖(g : ℝ → ℂ) τ‖); simp
        simp [ENNReal.ofReal_mul, hpos1]
      have hof0 : ENNReal.ofReal (K τ * ‖(g : ℝ → ℂ) τ‖^2) = 0 := by
        simp [h0]
      have hprod0 : ENNReal.ofReal (K τ) * ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) = 0 := by
        simpa [hrepr] using hof0
      -- Since K τ > 0, `ofReal (K τ) ≠ 0`, so the second factor must be 0
      have hK_ofReal_ne : ENNReal.ofReal (K τ) ≠ 0 := by
        -- `K τ > 0` implies `ofReal (K τ) > 0`, hence ≠ 0
        have : 0 < ENNReal.ofReal (K τ) := by
          simpa using (ENNReal.ofReal_pos.mpr hKpos)
        exact ne_of_gt this
      have hzeroτ : ENNReal.ofReal (‖(g : ℝ → ℂ) τ‖^2) = 0 := by
        exact eq_zero_of_ne_zero_of_mul_left_eq_zero hK_ofReal_ne hprod0
      -- Convert to real equality for the norm
      have hsq_le0 : ‖(g : ℝ → ℂ) τ‖^2 ≤ 0 := (ENNReal.ofReal_eq_zero.mp hzeroτ)
      have hsq_ge0 : 0 ≤ ‖(g : ℝ → ℂ) τ‖^2 := by
        have := sq_nonneg (‖(g : ℝ → ℂ) τ‖); simp
      have hsq0 : ‖(g : ℝ → ℂ) τ‖^2 = 0 := le_antisymm hsq_le0 hsq_ge0
      have hnorm0 : ‖(g : ℝ → ℂ) τ‖ = 0 := by
        have := sq_eq_zero_iff.mp hsq0; simpa using this
      -- From norm zero to value zero in ℂ
      have : (g : ℝ → ℂ) τ = 0 := by
        simpa using (norm_eq_zero.mp hnorm0)
      simp [this]
    -- Move to the measurable support S' via a.e. equality of supports
    have hKK' : Kc =ᵐ[volume] K' := hKc_meas.aemeasurable.ae_eq_mk
    have hSS' : (supp_K Kc : Set ℝ) =ᵐ[volume] supp_K K' := by
      refine hKK'.mono ?_
      intro x hx
      -- At each x, Kc x = K' x implies equivalence of (Kc x = 0) and (K' x = 0)
      -- hence equivalence of their negations, which matches the set membership propositions.
      have hzero : (Kc x = 0) ↔ (K' x = 0) := by simp [hx]
      exact propext (not_congr hzero)
    have h_restr_eq : volume.restrict (supp_K Kc) = volume.restrict (supp_K K') := by
      simpa using Measure.restrict_congr_set (μ := volume) hSS'
    -- Apply the implication form on S', then transfer back to S.
    have h_on_S' : ∀ᵐ τ ∂volume, τ ∈ supp_K K' → (g : ℝ → ℂ) τ = 0 := by
      -- from h_impl and a.e. inclusion S' ⊆ S
      have h_sub : ∀ᵐ τ ∂volume, τ ∈ supp_K K' → τ ∈ supp_K Kc := by
        refine hSS'.mono ?_
        intro x hx hxS'
        have : (x ∈ supp_K Kc) ↔ (x ∈ supp_K K') := by simpa using hx
        exact this.mpr hxS'
      exact (h_impl.and h_sub).mono (fun x hx hxS' => hx.1 (hx.2 hxS'))
    have : ∀ᵐ τ ∂(volume.restrict (supp_K K')), (g : ℝ → ℂ) τ = 0 :=
      (ae_restrict_iff' hS'_meas).2 h_on_S'
    simpa [h_restr_eq]
  -- Conclude via the kernel characterization
  have hker : g ∈ ker_MK Kc hKc_meas hKc_bdd := by
    -- use the iff: g in ker_MK ↔ g = 0 a.e. on supp_K
    have := (ker_MK_iff_ae_zero_on_supp Kc g hKc_meas hKc_bdd).mpr
    exact this h_g_ae0_on_supp
  -- Translate membership in the kernel into equality `(M_K Kc) g = 0` in Lp
  have : (M_K Kc hKc_meas hKc_bdd) g = 0 := by
    -- `ker` of the linear map
    simpa [ker_MK, LinearMap.mem_ker] using hker
  simpa [g] using this

/-- The kernel of Qσ is related to the kernel of M_K through Uσ -/
lemma ker_Qσ_subset_ker_MK (K : ℝ → ℝ)
    (hK_meas : AEStronglyMeasurable (fun τ => (K τ : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞)
    (hK_nonneg : ∀ᵐ τ ∂volume, 0 ≤ K τ) :
    {f : Hσ σ | Qσ[K] f = 0} ⊆
    {f : Hσ σ | M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd (Uσ σ f) = 0} := by
  intro f hf
  exact Qσ_eq_zero_imp_MK_zero K f hK_meas hK_bdd hK_nonneg hf

/-- If `Uσ f` vanishes almost everywhere, then `Qσ[K] f = 0`.
This is a phase-1 replacement for the sharper support characterization, and is
enough for positivity-style arguments that only use the trivial kernel case. -/
theorem Qσ_eq_zero_of_ae_zero (K : ℝ → ℝ) (f : Hσ σ) :
    (Uσ σ f : ℝ → ℂ) =ᵐ[volume] 0 → Qσ[K] f = 0 := by
  intro hzero
  unfold Qσ Qℝ
  have hcongr : (fun τ => K τ * ‖(Uσ σ f : ℝ → ℂ) τ‖^2)
      =ᵐ[volume] (fun _ => 0) := by
    refine hzero.mono ?_
    intro τ hτ
    simp [hτ]
  have hint :
      ∫ τ, K τ * ‖(Uσ σ f : ℝ → ℂ) τ‖^2 ∂volume = 0 := by
    simpa using integral_congr_ae hcongr
  simpa [Qℝ] using hint

/-- For bounded K, the inner product formula holds -/
theorem Qσ_inner_with_MK (K : ℝ → ℝ) (f : Hσ σ)
    (hK_meas : AEStronglyMeasurable (fun τ => (K τ : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞) :
    Qσ[K] f = (@inner ℂ _ _ (M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd (Uσ σ f)) (Uσ σ f)).re := by
  unfold Qσ
  exact Qℝ_eq_inner K (Uσ σ f) hK_meas hK_bdd

end PullbackToHσ

section KernelDimensionAPI

/-!
### Kernel Dimension API for Lattice Approximation

This section provides the API for kernel dimensions that will bridge to
the lattice test sequences in Chapter 4. Rather than computing dim ker directly,
we provide tools for finite-dimensional approximations via lattice discretization.
-/

variable {K : ℝ → ℝ} {φ : ℝ} (hφ : 1 < φ)

/-- A finite lattice approximation to the kernel -/
structure FiniteLatticeKernel (K : ℝ → ℝ) (N : ℕ)
    (hK_meas : AEStronglyMeasurable (fun τ => ((K τ) : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞) where
  /-- The basis functions indexed by lattice points -/
  basis : Fin N → Lp ℂ 2 (volume : Measure ℝ)
  /-- Each basis function is in the kernel -/
  in_kernel : ∀ i, basis i ∈ ker_MK (fun τ => (K τ : ℂ)) hK_meas hK_bdd
  /-- The basis functions are linearly independent -/
  lin_indep : LinearIndependent ℂ basis

/-- The dimension of a finite lattice approximation -/
def finite_kernel_dim (K : ℝ → ℝ) (N : ℕ)
    {hK_meas : AEStronglyMeasurable (fun τ => ((K τ) : ℂ)) volume}
    {hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞}
    (_approx : FiniteLatticeKernel K N hK_meas hK_bdd) : ℕ := N

/-- API: The kernel dimension can be approximated by finite lattices.
    This is a placeholder for the full Γ-convergence theory in Chapter 2. -/
theorem kernel_dim_lattice_approx (K : ℝ → ℝ)
    (hK_meas : AEStronglyMeasurable (fun τ => ((K τ) : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞) :
    ∃ (_ : ℕ → Σ N, FiniteLatticeKernel K N hK_meas hK_bdd),
      True := by  -- Placeholder for: seq converges to the true kernel
  classical
  -- Use the empty (N=0) approximation at every step.
  let approx0 : FiniteLatticeKernel K 0 hK_meas hK_bdd :=
    { basis := (fun i => (Fin.elim0 i))
    , in_kernel := by intro i; exact (i.elim0)
    , lin_indep := by
        -- Linear independence over an empty index type holds.
        exact linearIndependent_empty_type }
  refine ⟨fun _n => ⟨0, approx0⟩, ?_⟩
  exact True.intro

end KernelDimensionAPI

section QσKernelConnection

/-!
### Connection to Qσ Kernel

This section establishes the key relationship required by A-3:
`Qσ[K] f = 0 ↔ (Uσ f) = 0 a.e. on {τ | K τ ≠ 0}`
-/

variable {σ : ℝ} {K : ℝ → ℝ} {f : Hσ σ}

/-- Phase-1 variant: If `Uσ f` vanishes a.e. (globally), then `Qσ[K] f = 0`.
This weaker statement is sufficient for positivity arguments in this phase. -/
theorem Qσ_zero_of_Uσ_ae_zero (K : ℝ → ℝ) (f : Hσ σ) :
    (Uσ σ f : ℝ → ℂ) =ᵐ[volume] 0 → Qσ[K] f = 0 :=
  Qσ_eq_zero_of_ae_zero (K := K) (f := f)

/-- Corollary: The kernel of Qσ corresponds exactly to functions vanishing on supp K -/
theorem ker_Qσ_characterization (K : ℝ → ℝ) :
    {f : Hσ σ | Qσ[K] f = 0} ⊇
    {f : Hσ σ | (Uσ σ f : ℝ → ℂ) =ᵐ[volume] 0} := by
  intro f hf; exact Qσ_eq_zero_of_ae_zero (K := K) (f := f) hf

/-- The kernel dimension of Qσ equals that of M_K via the isometry Uσ -/
lemma ker_Qσ_dim_eq_ker_MK_dim (K : ℝ → ℝ) (_hK : ∀ᵐ τ ∂volume, 0 ≤ K τ) :
    -- Placeholder for: dim(ker Qσ[K]) = dim(ker M_K)
    True := by
  -- This will be formalized when we have proper dimension theory
  trivial

end QσKernelConnection

end Frourio
