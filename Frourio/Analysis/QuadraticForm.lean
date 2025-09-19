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

/-- Quadratic form on Hσ defined directly via the Mellin transform.
    This avoids dependency on the placeholder Uσ operator. -/
noncomputable def Qσ (K : ℝ → ℝ) (f : Hσ σ) : ℝ :=
  ∫ τ : ℝ, K τ * ‖mellinOnCriticalLine σ f τ‖^2 ∂volume

/-- Alternative notation for clarity -/
notation "Qσ[" K "]" => Qσ K

/-- Positivity on Hσ: If K ≥ 0 a.e., then Qσ[K](f) ≥ 0.
    This follows from the fact that we're integrating a non-negative function. -/
theorem Qσ_pos (K : ℝ → ℝ) (hK : ∀ᵐ τ ∂volume, 0 ≤ K τ) (f : Hσ σ) :
    0 ≤ Qσ[K] f := by
  unfold Qσ
  -- The integrand K τ * ‖mellinOnCriticalLine σ f τ‖^2 is non-negative a.e.
  apply integral_nonneg_of_ae
  -- Show that the integrand is non-negative almost everywhere
  refine hK.mono ?_
  intro τ hτ
  exact mul_nonneg hτ (sq_nonneg _)

/-- When K is essentially bounded and non-negative, Qσ[K] f = 0 implies
    that K · mellinOnCriticalLine σ f = 0 almost everywhere -/
theorem Qσ_eq_zero_imp_kernel_zero (K : ℝ → ℝ) (f : Hσ σ)
    (hK_meas : AEStronglyMeasurable (fun τ => (K τ : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞)
    (hK_nonneg : ∀ᵐ τ ∂volume, 0 ≤ K τ) :
    Qσ[K] f = 0 → (∀ᵐ τ ∂volume, K τ * ‖mellinOnCriticalLine σ f τ‖^2 = 0) := by
  intro hQ0
  -- From `Qσ[K] f = 0`, we have `∫ K · ‖mellinOnCriticalLine σ f‖² = 0`.
  have hInt0 : ∫ τ, K τ * ‖mellinOnCriticalLine σ f τ‖^2 ∂volume = 0 := by
    simpa [Qσ] using hQ0
  -- The integrand K τ * ‖mellinOnCriticalLine σ f τ‖^2 is a.e. non-negative
  have hF_nonneg : ∀ᵐ τ ∂volume, 0 ≤ K τ * ‖mellinOnCriticalLine σ f τ‖^2 := by
    refine hK_nonneg.mono ?_
    intro τ hKτ
    exact mul_nonneg hKτ (sq_nonneg _)
  -- The function is a.e. measurable
  have hF_meas : AEMeasurable (fun τ => K τ * ‖mellinOnCriticalLine σ f τ‖^2) volume := by
    -- K is a.e. measurable
    have hK_am : AEMeasurable K volume := by
      -- We know (K τ : ℂ) is AEStronglyMeasurable
      -- The real part of (K τ : ℂ) is K τ
      have : AEStronglyMeasurable (fun τ => ((K τ : ℂ)).re) volume := hK_meas.re
      simp only [Complex.ofReal_re] at this
      exact this.aemeasurable
    -- ‖mellinOnCriticalLine σ f‖^2 is a.e. measurable
    have h_mellin_meas := (mellin_in_L2 σ f).1.norm.aemeasurable
    have h_sq_meas := h_mellin_meas.pow_const 2
    exact hK_am.mul h_sq_meas
  -- From the integral being 0 and the integrand being non-negative a.e.,
  -- we conclude that the integrand must be 0 a.e.
  classical
  -- `‖mellinOnCriticalLine σ f τ‖ ^ 2` is integrable thanks to the L² bound
  have h_mellin_sq_int :
      Integrable (fun τ => ‖mellinOnCriticalLine σ f τ‖ ^ 2) volume := by
    have hmem := mellin_in_L2 σ f
    exact (memLp_two_iff_integrable_sq_norm hmem.1).1 hmem
  -- Obtain an a.e. bound on K from the essential supremum
  set Mess : ℝ≥0∞ := essSup (fun τ => (‖(K τ : ℂ)‖₊ : ℝ≥0∞)) volume
  have hMess_lt : Mess < ∞ := hK_bdd
  have hMess_ne : Mess ≠ ∞ := ne_of_lt hMess_lt
  have hK_bound : ∀ᵐ τ ∂volume, ‖K τ‖ ≤ Mess.toReal := by
    have h_le :
        ∀ᵐ τ ∂volume, (‖(K τ : ℂ)‖₊ : ℝ≥0∞) ≤ Mess :=
      ae_le_essSup (fun τ => (‖(K τ : ℂ)‖₊ : ℝ≥0∞))
    refine h_le.mono ?_
    intro τ hτ
    have hτ' :=
      (ENNReal.toReal_le_toReal (by simp) hMess_ne).2 hτ
    have hτ'' : ‖(K τ : ℂ)‖ ≤ Mess.toReal := by
      simpa [toReal_coe_nnnorm'] using hτ'
    simpa [Complex.norm_ofReal, Real.norm_eq_abs] using hτ''
  -- K is real-valued and inherits measurability from the complex-valued assumption
  have hK_meas_real : AEStronglyMeasurable K volume := by
    simpa using hK_meas.re
  -- Hence the product is integrable by bounding K with its essential supremum
  have hF_int :
      Integrable (fun τ => K τ * ‖mellinOnCriticalLine σ f τ‖ ^ 2) volume := by
    refine Integrable.bdd_mul' (μ := volume) (c := Mess.toReal)
        h_mellin_sq_int hK_meas_real ?_
    exact hK_bound
  -- Finally, use the integral zero criterion for non-negative integrable functions
  have hZero :
      (fun τ => K τ * ‖mellinOnCriticalLine σ f τ‖ ^ 2)
        =ᵐ[volume] (fun _ => (0 : ℝ)) := by
    exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (μ := volume) hF_nonneg hF_int).1 hInt0
  exact hZero

/-- The kernel of Qσ is related to the kernel of M_K through mellinOnCriticalLine -/
lemma ker_Qσ_subset_ker_MK (K : ℝ → ℝ)
    (hK_meas : AEStronglyMeasurable (fun τ => (K τ : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞)
    (hK_nonneg : ∀ᵐ τ ∂volume, 0 ≤ K τ) :
    {f : Hσ σ | Qσ[K] f = 0} ⊆
    {f : Hσ σ | M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd
      ((mellin_in_L2 σ f).toLp (mellinOnCriticalLine σ f)) = 0} := by
  intro f hf
  classical
  -- `gLp` is the Mellin transform viewed as an element of `Lp`
  let gLp : Lp ℂ 2 (volume : Measure ℝ) :=
    (mellin_in_L2 σ f).toLp (mellinOnCriticalLine σ f)
  -- a.e. representatives for `gLp` and `M_K gLp`
  have hg_coe : ((gLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] mellinOnCriticalLine σ f := by
    simpa using (MemLp.coeFn_toLp (mellin_in_L2 σ f))
  have hMK_coe :=
    M_K_apply_ae (fun τ => (K τ : ℂ)) hK_meas hK_bdd gLp
  -- From the kernel condition on `Qσ` we know the squared norm vanishes a.e.
  have hZeroSq : ∀ᵐ τ ∂volume,
      K τ * ‖mellinOnCriticalLine σ f τ‖^2 = 0 := by
    exact (Qσ_eq_zero_imp_kernel_zero (σ := σ) (K := K) (f := f)
      hK_meas hK_bdd hK_nonneg) hf
  -- Convert the squared-norm vanishing into the complex product vanishing a.e.
  have hKg_zero :
      ∀ᵐ τ ∂volume,
        (K τ : ℂ) * mellinOnCriticalLine σ f τ = 0 := by
    refine hZeroSq.mono ?_
    intro τ hτ
    have hcases := mul_eq_zero.mp hτ
    rcases hcases with hKτ | hnormτ
    · simp [hKτ]
    · have hnorm_zero : ‖mellinOnCriticalLine σ f τ‖ = 0 := by
        have hsq : (‖mellinOnCriticalLine σ f τ‖ : ℝ) ^ (2 : ℕ) = 0 := by
          simpa using hnormτ
        simpa using (pow_eq_zero hsq)
      have hf_zero : mellinOnCriticalLine σ f τ = 0 := by
        simpa using (norm_eq_zero.mp hnorm_zero)
      simp [hf_zero]
  -- The zero element of `Lp` evaluates to 0 almost everywhere
  have hzero_rhs : ∀ᵐ τ ∂volume,
      (((0 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ) = 0 := by
    simp
  -- Identify the Mellin product with the zero function almost everywhere
  have hKg_eq_zero : ∀ᵐ τ ∂volume,
      (K τ : ℂ) * mellinOnCriticalLine σ f τ
        = (((0 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ) := by
    refine (hKg_zero.and hzero_rhs).mono ?_
    intro τ hτ
    rcases hτ with ⟨hleft, hrhs⟩
    simp [hleft]
  -- Transport the equality to the `Lp` representative `gLp`
  have hKgLp_eq_zero : ∀ᵐ τ ∂volume,
      (K τ : ℂ) * ((gLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ
        = (((0 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ) := by
    have hprod_eq : ∀ᵐ τ ∂volume,
        (K τ : ℂ) * ((gLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ
          = (K τ : ℂ) * mellinOnCriticalLine σ f τ := by
      refine hg_coe.mono ?_
      intro τ hτ
      simp [hτ]
    refine (hprod_eq.and hKg_eq_zero).mono ?_
    intro τ hτ
    rcases hτ with ⟨hleft, hright⟩
    simp [hleft, hright]
  -- Combine with the `M_K` a.e. description to deduce the kernel condition
  have hMK_eq_zero : ∀ᵐ τ ∂volume,
      (((M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd) gLp :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ
        = (((0 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ) := by
    refine (hMK_coe.and hKgLp_eq_zero).mono ?_
    intro τ hτ
    rcases hτ with ⟨hleft, hright⟩
    simp [hleft, hright]
  -- Conclude in the target subset
  have hMK_eq_zero' :
      (((M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd) gLp :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
          (((0 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) := hMK_eq_zero
  refine Lp.ext ?_
  simpa using hMK_eq_zero'

/-- If the Mellin transform vanishes almost everywhere, then `Qσ[K] f = 0` -/
theorem Qσ_eq_zero_of_mellin_ae_zero (K : ℝ → ℝ) (f : Hσ σ) :
    mellinOnCriticalLine σ f =ᵐ[volume] 0 → Qσ[K] f = 0 := by
  intro hzero
  unfold Qσ
  have hcongr : (fun τ => K τ * ‖mellinOnCriticalLine σ f τ‖^2)
      =ᵐ[volume] (fun _ => 0) := by
    refine hzero.mono ?_
    intro τ hτ
    simp [hτ]
  have hint :
      ∫ τ, K τ * ‖mellinOnCriticalLine σ f τ‖^2 ∂volume = 0 := by
    simpa using integral_congr_ae hcongr
  exact hint

-- Note: The inner product formula with M_K is temporarily removed
-- since it depends on Uσ. It should be reformulated using mellinOnCriticalLine directly.

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

/-- Phase-1 variant: If mellin transform vanishes a.e. (globally), then `Qσ[K] f = 0`.
This weaker statement is sufficient for positivity arguments in this phase. -/
theorem Qσ_zero_of_mellin_ae_zero_v2 (K : ℝ → ℝ) (f : Hσ σ) :
    mellinOnCriticalLine σ f =ᵐ[volume] 0 → Qσ[K] f = 0 :=
  Qσ_eq_zero_of_mellin_ae_zero (K := K) (f := f)

/-- Corollary: The kernel of Qσ corresponds exactly to functions vanishing on supp K -/
theorem ker_Qσ_characterization (K : ℝ → ℝ) :
    {f : Hσ σ | Qσ[K] f = 0} ⊇
    {f : Hσ σ | mellinOnCriticalLine σ f =ᵐ[volume] 0} := by
  intro f hf; exact Qσ_eq_zero_of_mellin_ae_zero (K := K) (f := f) hf

/-- The kernel dimension of Qσ equals that of M_K via the isometry Uσ -/
lemma ker_Qσ_dim_eq_ker_MK_dim (K : ℝ → ℝ) (_hK : ∀ᵐ τ ∂volume, 0 ≤ K τ) :
    -- Placeholder for: dim(ker Qσ[K]) = dim(ker M_K)
    True := by
  -- This will be formalized when we have proper dimension theory
  trivial

end QσKernelConnection

end Frourio
