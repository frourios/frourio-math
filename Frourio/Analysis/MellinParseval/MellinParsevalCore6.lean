import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore5
import Frourio.Analysis.HilbertSpaceCore
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

open MeasureTheory Measure Real Complex Set NNReal
open scoped ENNReal Topology FourierTransform

namespace Frourio
open Schwartz

section ClassicalParseval

/-- Forward rescaling map on Lp: takes an Lp function and applies the rescaling transformation. -/
noncomputable def rescaleForward_map : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ) :=
  fun f =>
    let g := (f : ℝ → ℂ)  -- Get the representative
    let g_rescaled := rescaleForward_fun g
    have hg : MeasureTheory.MemLp g 2 volume := MeasureTheory.Lp.memLp f
    have : MeasureTheory.MemLp g_rescaled 2 volume := rescaleForward_fun_memLp hg
    this.toLp g_rescaled

/-- Inverse rescaling map on Lp: takes an Lp function and applies the inverse rescaling. -/
noncomputable def rescaleInverse_map : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ) :=
  fun f =>
    let h := (f : ℝ → ℂ)
    let h_rescaled := rescaleInverse_fun h
    have hh : MeasureTheory.MemLp h 2 volume := MeasureTheory.Lp.memLp f
    have : MeasureTheory.MemLp h_rescaled 2 volume := rescaleInverse_fun_memLp hh
    this.toLp h_rescaled

lemma rescaleForward_map_add (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    rescaleForward_map (f + g) = rescaleForward_map f + rescaleForward_map g := by
  classical
  -- Work on representatives and use `Lp.ext` to prove equality.
  apply Lp.ext
  -- Step 1: identify the representative of `rescaleForward_map (f + g)`.
  have h_fg_mem :
      MeasureTheory.MemLp
        (rescaleForward_fun ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp (MeasureTheory.Lp.memLp (f + g))
  have h_coe_fg :
      (rescaleForward_map (f + g) : ℝ → ℂ)
        =ᵐ[volume]
      rescaleForward_fun ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleForward_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_fg_mem)
  -- Step 2: identify the representatives of `rescaleForward_map f` and `rescaleForward_map g`.
  have h_f_mem :
      MeasureTheory.MemLp
        (rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp (MeasureTheory.Lp.memLp f)
  have h_g_mem :
      MeasureTheory.MemLp
        (rescaleForward_fun ((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp (MeasureTheory.Lp.memLp g)
  have h_coe_f :
      (rescaleForward_map f : ℝ → ℂ)
        =ᵐ[volume]
      rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleForward_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_f_mem)
  have h_coe_g :
      (rescaleForward_map g : ℝ → ℂ)
        =ᵐ[volume]
      rescaleForward_fun ((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleForward_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_g_mem)
  -- Step 3: relate the argument of `rescaleForward_fun` for `f + g` to that of `f` and `g`.
  have h_add :
      ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      fun x => (f : ℝ → ℂ) x + (g : ℝ → ℂ) x :=
    MeasureTheory.Lp.coeFn_add f g
  -- Transport this a.e. equality through composition with `rescaleMap`.
  have h_add_comp :
      (fun τ => ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMap τ))
        =ᵐ[volume]
      (fun τ => ((fun x => (f : ℝ → ℂ) x + (g : ℝ → ℂ) x) (rescaleMap τ))) := by
    -- Use quasi measure preserving property of `rescaleMap`.
    simpa [Function.comp] using
      (rescaleMap_quasiMeasurePreserving.ae_eq h_add)
  -- Step 4: use linearity of `rescaleForward_fun` at the function level.
  have h_fun_add :
      rescaleForward_fun ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      (fun τ : ℝ =>
        rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ
        + rescaleForward_fun ((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ) := by
    -- Expand the definition and use the previous a.e. equality.
    refine h_add_comp.mono ?_
    intro τ hτ
    -- First, rewrite the inner argument using `hτ`.
    have hτ' :
        (((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMap τ) : ℂ)
          = (((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
            (rescaleMap τ) : ℂ) + (((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
            (rescaleMap τ) : ℂ) := by
      simpa [Function.comp] using hτ
    -- Apply scalar multiplication by `rescaleNorm⁻¹` and distribute over the sum.
    have h_smul :=
      congrArg (fun z : ℂ => (rescaleNorm : ℝ)⁻¹ • z) hτ'
    simpa [rescaleForward_fun, Function.comp, smul_add] using h_smul
  -- Step 5: combine all a.e. equalities.
  refine h_coe_fg.trans ?_
  -- Rewrite RHS in terms of `rescaleForward_map f` and `rescaleForward_map g`.
  have h_rhs :
      (fun τ : ℝ =>
        rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ
        + rescaleForward_fun ((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ)
        =ᵐ[volume]
      (fun τ : ℝ =>
        (rescaleForward_map f : ℝ → ℂ) τ
        + (rescaleForward_map g : ℝ → ℂ) τ) := by
    refine (h_coe_f.add h_coe_g).symm
  have h_sum_coe :=
    (MeasureTheory.Lp.coeFn_add (rescaleForward_map f) (rescaleForward_map g)).symm
  exact h_fun_add.trans (h_rhs.trans h_sum_coe)

lemma rescaleForward_map_smul (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    rescaleForward_map (c • f) = c • rescaleForward_map f := by
  classical
  -- Work on representatives and use `Lp.ext` to prove equality.
  apply Lp.ext
  -- Step 1: representative of `rescaleForward_map (c • f)`.
  have h_cf_mem :
      MeasureTheory.MemLp
        (rescaleForward_fun ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp (MeasureTheory.Lp.memLp (c • f))
  have h_coe_cf :
      (rescaleForward_map (c • f) : ℝ → ℂ)
        =ᵐ[volume]
      rescaleForward_fun ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleForward_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_cf_mem)
  -- Step 2: representative of `rescaleForward_map f`.
  have h_f_mem :
      MeasureTheory.MemLp
        (rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp (MeasureTheory.Lp.memLp f)
  have h_coe_f :
      (rescaleForward_map f : ℝ → ℂ)
        =ᵐ[volume]
      rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleForward_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_f_mem)
  -- Step 3: relate the argument of `rescaleForward_fun` for `c • f` to that of `f`.
  have h_smul_rep :
      ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      fun x => c • (f : ℝ → ℂ) x :=
    MeasureTheory.Lp.coeFn_smul c f
  -- Transport this a.e. equality through composition with `rescaleMap`.
  have h_smul_comp :
      (fun τ => ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMap τ))
        =ᵐ[volume]
      (fun τ => c • ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMap τ)) := by
    simpa [Function.comp] using
      (rescaleMap_quasiMeasurePreserving.ae_eq h_smul_rep)
  -- Step 4: linearity of `rescaleForward_fun` at the function level (scalar multiplication).
  have h_fun_smul :
      rescaleForward_fun ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      (fun τ : ℝ =>
        c • rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ) := by
    refine h_smul_comp.mono ?_
    intro τ hτ
    -- Rewrite the inner argument using `hτ`.
    have hτ' :
        (((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMap τ) : ℂ)
          = c • (((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
            (rescaleMap τ) : ℂ) := by
      simpa [Function.comp] using hτ
    -- Apply scalar multiplication by `rescaleNorm⁻¹` and rearrange.
    have h_smul' :=
      congrArg (fun z : ℂ => (rescaleNorm : ℝ)⁻¹ • z) hτ'
    -- Turn both sides into the desired expressions using `rescaleForward_fun`.
    -- Use `Real.smul_def` to rewrite real scalar multiplication as complex multiplication.
    simpa [rescaleForward_fun, Function.comp, Circle.smul_def,
      mul_comm, mul_left_comm, mul_assoc, smul_smul] using h_smul'
  -- Step 5: rewrite the RHS in terms of `c • rescaleForward_map f`.
  have h_rhs1 :
      (fun τ : ℝ =>
        c • rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ)
        =ᵐ[volume]
      (fun τ : ℝ =>
        c • (rescaleForward_map f : ℝ → ℂ) τ) := by
    refine h_coe_f.mono ?_
    intro τ hτ
    simp [hτ]
  have h_rhs2 :
      (fun τ : ℝ =>
        c • (rescaleForward_map f : ℝ → ℂ) τ)
        =ᵐ[volume]
      ((c • rescaleForward_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    (MeasureTheory.Lp.coeFn_smul c (rescaleForward_map f)).symm
  -- Step 6: combine all a.e. equalities.
  exact h_coe_cf.trans (h_fun_smul.trans (h_rhs1.trans h_rhs2))

lemma rescaleInverse_map_add (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    rescaleInverse_map (f + g) = rescaleInverse_map f + rescaleInverse_map g := by
  classical
  -- Work on representatives and use `Lp.ext` to prove equality.
  apply Lp.ext
  -- Step 1: representative of `rescaleInverse_map (f + g)`.
  have h_fg_mem :
      MeasureTheory.MemLp
        (rescaleInverse_fun ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleInverse_fun_memLp (MeasureTheory.Lp.memLp (f + g))
  have h_coe_fg :
      (rescaleInverse_map (f + g) : ℝ → ℂ)
        =ᵐ[volume]
      rescaleInverse_fun ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleInverse_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_fg_mem)
  -- Step 2: representatives of `rescaleInverse_map f` and `rescaleInverse_map g`.
  have h_f_mem :
      MeasureTheory.MemLp
        (rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleInverse_fun_memLp (MeasureTheory.Lp.memLp f)
  have h_g_mem :
      MeasureTheory.MemLp
        (rescaleInverse_fun ((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleInverse_fun_memLp (MeasureTheory.Lp.memLp g)
  have h_coe_f :
      (rescaleInverse_map f : ℝ → ℂ)
        =ᵐ[volume]
      rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleInverse_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_f_mem)
  have h_coe_g :
      (rescaleInverse_map g : ℝ → ℂ)
        =ᵐ[volume]
      rescaleInverse_fun ((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleInverse_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_g_mem)
  -- Step 3: relate the argument of `rescaleInverse_fun` for `f + g` to that of `f` and `g`.
  have h_add :
      ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      fun x => (f : ℝ → ℂ) x + (g : ℝ → ℂ) x :=
    MeasureTheory.Lp.coeFn_add f g
  -- Transport this a.e. equality through composition with `rescaleMapInv`.
  have h_add_comp :
      (fun τ => ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMapInv τ))
        =ᵐ[volume]
      (fun τ => ((fun x => (f : ℝ → ℂ) x + (g : ℝ → ℂ) x) (rescaleMapInv τ))) := by
    -- Use quasi measure preserving property of `rescaleMapInv`.
    simpa [Function.comp] using
      (rescaleMapInv_quasiMeasurePreserving.ae_eq h_add)
  -- Step 4: linearity of `rescaleInverse_fun` at the function level.
  have h_fun_add :
      rescaleInverse_fun ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      (fun τ : ℝ =>
        rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ
        + rescaleInverse_fun ((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ) := by
    -- Expand the definition and use the previous a.e. equality.
    refine h_add_comp.mono ?_
    intro τ hτ
    -- First, rewrite the inner argument using `hτ`.
    have hτ' :
        (((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMapInv τ) : ℂ)
          = (((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
            (rescaleMapInv τ) : ℂ) + (((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
            (rescaleMapInv τ) : ℂ) := by
      simpa [Function.comp] using hτ
    -- Apply scalar multiplication by `rescaleNorm` and distribute over the sum.
    have h_smul :=
      congrArg (fun z : ℂ => (rescaleNorm : ℝ) • z) hτ'
    simpa [rescaleInverse_fun, Function.comp, smul_add, Circle.smul_def,
      mul_comm, mul_left_comm, mul_assoc, smul_smul] using h_smul
  -- Step 5: combine all a.e. equalities.
  refine h_coe_fg.trans ?_
  -- Rewrite RHS in terms of `rescaleInverse_map f` and `rescaleInverse_map g`.
  have h_rhs :
      (fun τ : ℝ =>
        rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ
        + rescaleInverse_fun ((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ)
        =ᵐ[volume]
      (fun τ : ℝ =>
        (rescaleInverse_map f : ℝ → ℂ) τ
        + (rescaleInverse_map g : ℝ → ℂ) τ) := by
    refine (h_coe_f.add h_coe_g).symm
  have h_sum_coe :=
    (MeasureTheory.Lp.coeFn_add (rescaleInverse_map f) (rescaleInverse_map g)).symm
  exact h_fun_add.trans (h_rhs.trans h_sum_coe)

lemma rescaleInverse_map_smul (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    rescaleInverse_map (c • f) = c • rescaleInverse_map f := by
  classical
  -- Work on representatives and use `Lp.ext` to prove equality.
  apply Lp.ext
  -- Step 1: representative of `rescaleInverse_map (c • f)`.
  have h_cf_mem :
      MeasureTheory.MemLp
        (rescaleInverse_fun ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleInverse_fun_memLp (MeasureTheory.Lp.memLp (c • f))
  have h_coe_cf :
      (rescaleInverse_map (c • f) : ℝ → ℂ)
        =ᵐ[volume]
      rescaleInverse_fun ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleInverse_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_cf_mem)
  -- Step 2: representative of `rescaleInverse_map f`.
  have h_f_mem :
      MeasureTheory.MemLp
        (rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleInverse_fun_memLp (MeasureTheory.Lp.memLp f)
  have h_coe_f :
      (rescaleInverse_map f : ℝ → ℂ)
        =ᵐ[volume]
      rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleInverse_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_f_mem)
  -- Step 3: relate the argument of `rescaleInverse_fun` for `c • f` to that of `f`.
  have h_smul_rep :
      ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      fun x => c • (f : ℝ → ℂ) x :=
    MeasureTheory.Lp.coeFn_smul c f
  -- Transport this a.e. equality through composition with `rescaleMapInv`.
  have h_smul_comp :
      (fun τ => ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMapInv τ))
        =ᵐ[volume]
      (fun τ => c • ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMapInv τ)) := by
    simpa [Function.comp] using
      (rescaleMapInv_quasiMeasurePreserving.ae_eq h_smul_rep)
  -- Step 4: linearity of `rescaleInverse_fun` at the function level (scalar multiplication).
  have h_fun_smul :
      rescaleInverse_fun ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      (fun τ : ℝ =>
        c • rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ) := by
    refine h_smul_comp.mono ?_
    intro τ hτ
    -- Rewrite the inner argument using `hτ`.
    have hτ' :
        (((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (rescaleMapInv τ) : ℂ)
          = c • (((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
            (rescaleMapInv τ) : ℂ) := by
      simpa [Function.comp] using hτ
    -- Apply scalar multiplication by `rescaleNorm` and rearrange.
    have h_smul' :=
      congrArg (fun z : ℂ => (rescaleNorm : ℝ) • z) hτ'
    -- Convert both sides via `Real.smul_def` and `smul_smul`.
    simpa [rescaleInverse_fun, Function.comp, Circle.smul_def,
      mul_comm, mul_left_comm, mul_assoc, smul_smul] using h_smul'
  -- Step 5: rewrite the RHS in terms of `c • rescaleInverse_map f`.
  have h_rhs1 :
      (fun τ : ℝ =>
        c • rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) τ)
        =ᵐ[volume]
      (fun τ : ℝ =>
        c • (rescaleInverse_map f : ℝ → ℂ) τ) := by
    refine h_coe_f.mono ?_
    intro τ hτ
    simp [hτ]
  have h_rhs2 :
      (fun τ : ℝ =>
        c • (rescaleInverse_map f : ℝ → ℂ) τ)
        =ᵐ[volume]
      ((c • rescaleInverse_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    (MeasureTheory.Lp.coeFn_smul c (rescaleInverse_map f)).symm
  -- Step 6: combine all a.e. equalities.
  exact h_coe_cf.trans (h_fun_smul.trans (h_rhs1.trans h_rhs2))

lemma rescaleForward_rescaleInverse (f : Lp ℂ 2 (volume : Measure ℝ)) :
    rescaleForward_map (rescaleInverse_map f) = f := by
  classical
  -- Work on representatives and use `Lp.ext` to prove equality.
  apply Lp.ext
  -- Step 1: representative of `rescaleInverse_map f`.
  have h_inv_mem :
      MeasureTheory.MemLp
        (rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleInverse_fun_memLp (MeasureTheory.Lp.memLp f)
  have h_inv_coe :
      (rescaleInverse_map f : ℝ → ℂ)
        =ᵐ[volume]
      rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleInverse_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_inv_mem)
  -- Step 2: representative of `rescaleForward_map (rescaleInverse_map f)`.
  have h_fwd_mem :
      MeasureTheory.MemLp
        (rescaleForward_fun ((rescaleInverse_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp (MeasureTheory.Lp.memLp (rescaleInverse_map f))
  have h_fwd_coe :
      (rescaleForward_map (rescaleInverse_map f) : ℝ → ℂ)
        =ᵐ[volume]
      rescaleForward_fun ((rescaleInverse_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleForward_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_fwd_mem)
  -- Step 3: propagate the a.e. equality of the inner argument through `rescaleForward_fun`.
  have h_comp_ae :
      (fun τ => (rescaleInverse_map f : ℝ → ℂ) (rescaleMap τ))
        =ᵐ[volume]
      (fun τ =>
        rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          (rescaleMap τ)) := by
    -- Use quasi measure preserving property of `rescaleMap`.
    simpa [Function.comp] using
      (rescaleMap_quasiMeasurePreserving.ae_eq h_inv_coe)
  have h_fwd_ae :
      rescaleForward_fun ((rescaleInverse_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      rescaleForward_fun
        (rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) := by
    refine h_comp_ae.mono ?_
    intro τ hτ
    -- Rewrite the inner argument using `hτ`.
    have hτ' :
        (((rescaleInverse_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          (rescaleMap τ) : ℂ)
          =
        (rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          (rescaleMap τ) : ℂ) := by
      simpa [Function.comp] using hτ
    -- Apply scalar multiplication by `rescaleNorm⁻¹` and rearrange.
    have h_smul :=
      congrArg (fun z : ℂ => (rescaleNorm : ℝ)⁻¹ • z) hτ'
    simpa [rescaleForward_fun, Function.comp] using h_smul
  -- Step 4: identify the composition as the identity on representatives.
  have h_comp_id :
      rescaleForward_fun
        (rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        = ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    rescaleForward_fun_rescaleInverse_fun _
  have h_comp_id_ae :
      rescaleForward_fun
        (rescaleInverse_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        =ᵐ[volume]
      ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    Filter.Eventually.of_forall (fun τ => by simpa using congrArg (fun h => h τ) h_comp_id)
  -- Step 5: combine all a.e. equalities to deduce equality of `Lp` elements.
  have h_total :
      (rescaleForward_map (rescaleInverse_map f) : ℝ → ℂ)
        =ᵐ[volume]
      ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    h_fwd_coe.trans (h_fwd_ae.trans h_comp_id_ae)
  -- Conclude by `Lp.ext`.
  exact h_total

lemma rescaleInverse_rescaleForward (f : Lp ℂ 2 (volume : Measure ℝ)) :
    rescaleInverse_map (rescaleForward_map f) = f := by
  classical
  -- Work on representatives and use `Lp.ext` to prove equality.
  apply Lp.ext
  -- Step 1: representative of `rescaleForward_map f`.
  have h_fwd_mem :
      MeasureTheory.MemLp
        (rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp (MeasureTheory.Lp.memLp f)
  have h_fwd_coe :
      (rescaleForward_map f : ℝ → ℂ)
        =ᵐ[volume]
      rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleForward_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_fwd_mem)
  -- Step 2: representative of `rescaleInverse_map (rescaleForward_map f)`.
  have h_inv_mem :
      MeasureTheory.MemLp
        (rescaleInverse_fun
          ((rescaleForward_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        2 (volume : Measure ℝ) :=
    rescaleInverse_fun_memLp (MeasureTheory.Lp.memLp (rescaleForward_map f))
  have h_inv_coe :
      (rescaleInverse_map (rescaleForward_map f) : ℝ → ℂ)
        =ᵐ[volume]
      rescaleInverse_fun
        ((rescaleForward_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    simpa [rescaleInverse_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_inv_mem)
  -- Step 3: propagate the a.e. equality of the inner argument through `rescaleInverse_fun`.
  have h_comp_ae :
      (fun τ => (rescaleForward_map f : ℝ → ℂ) (rescaleMapInv τ))
        =ᵐ[volume]
      (fun τ =>
        rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          (rescaleMapInv τ)) := by
    -- Use quasi measure preserving property of `rescaleMapInv`.
    simpa [Function.comp] using
      (rescaleMapInv_quasiMeasurePreserving.ae_eq h_fwd_coe)
  have h_inv_ae :
      rescaleInverse_fun
        ((rescaleForward_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      rescaleInverse_fun
        (rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) := by
    refine h_comp_ae.mono ?_
    intro τ hτ
    -- Rewrite the inner argument using `hτ`.
    have hτ' :
        (((rescaleForward_map f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          (rescaleMapInv τ) : ℂ)
          =
        (rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          (rescaleMapInv τ) : ℂ) := by
      simpa [Function.comp] using hτ
    -- Apply scalar multiplication by `rescaleNorm` and rearrange.
    have h_smul :=
      congrArg (fun z : ℂ => (rescaleNorm : ℝ) • z) hτ'
    -- Convert both sides via `Real.smul_def` and `smul_smul`.
    simpa [rescaleInverse_fun, Function.comp, Circle.smul_def,
      mul_comm, mul_left_comm, mul_assoc, smul_smul] using h_smul
  -- Step 4: identify the composition as the identity on representatives.
  have h_comp_id :
      rescaleInverse_fun
        (rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        = ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    rescaleInverse_fun_rescaleForward_fun _
  have h_comp_id_ae :
      rescaleInverse_fun
        (rescaleForward_fun ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        =ᵐ[volume]
      ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    Filter.Eventually.of_forall
      (fun τ => by simpa using congrArg (fun h => h τ) h_comp_id)
  -- Step 5: combine all a.e. equalities to deduce equality of `Lp` elements.
  have h_total :
      (rescaleInverse_map (rescaleForward_map f) : ℝ → ℂ)
        =ᵐ[volume]
      ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    h_inv_coe.trans (h_inv_ae.trans h_comp_id_ae)
  -- Conclude by `Lp.ext`.
  exact h_total

lemma rescaleForward_map_norm (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖rescaleForward_map f‖ = ‖f‖ := by
  classical
  -- Choose a representative `g` of `f` and its L² membership.
  let g : ℝ → ℂ := (f : ℝ → ℂ)
  have hg : MeasureTheory.MemLp g 2 (volume : Measure ℝ) :=
    MeasureTheory.Lp.memLp f
  -- `rescaleForward_map f` is obtained from `rescaleForward_fun g` via `toLp`.
  have hg_rescaled :
      MeasureTheory.MemLp (rescaleForward_fun g) 2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp hg
  -- Identify the norm of `rescaleForward_map f` with the eLpNorm of its representative.
  have h_norm_rescaled :
      ‖rescaleForward_map f‖
        = (eLpNorm (rescaleForward_fun g) 2 (volume : Measure ℝ)).toReal := by
    -- This is just `Lp.norm_toLp` unfolded along the definition of `rescaleForward_map`.
    unfold rescaleForward_map
    exact Lp.norm_toLp (μ := (volume : Measure ℝ))
      (f := rescaleForward_fun g) hg_rescaled
  -- Identify the norm of `f` with the eLpNorm of its representative.
  have h_norm_f :
      ‖f‖ = (eLpNorm g 2 (volume : Measure ℝ)).toReal := by
    -- By definition of `g`, we have `g =ᵐ[volume] f`.
    -- Use the fact that Lp norm only depends on the ae class.
    have : (eLpNorm g 2 (volume : Measure ℝ)) = eLpNorm (f : ℝ → ℂ) 2 volume := by
      have : g =ᵐ[volume] (f : ℝ → ℂ) := by rfl
      exact eLpNorm_congr_ae this
    rw [this]
    exact (Lp.norm_def f).symm
  have h_eLp_eq :
      (eLpNorm (rescaleForward_fun g) 2 (volume : Measure ℝ)).toReal
        = (eLpNorm g 2 (volume : Measure ℝ)).toReal :=
    rescaleForward_fun_eLpNorm_eq g hg
  -- Combine all equalities.
  calc
    ‖rescaleForward_map f‖
        = (eLpNorm (rescaleForward_fun g) 2 (volume : Measure ℝ)).toReal :=
      h_norm_rescaled
    _ = (eLpNorm g 2 (volume : Measure ℝ)).toReal := h_eLp_eq
    _ = ‖f‖ := h_norm_f.symm

/-- Rescaling isometry equivalence on `Lp ℂ 2 (volume)`.

This represents the rescaling map `τ ↦ -τ / (2π)` (defined as `rescaleMap`)
with appropriate normalization to make it an L² isometry.

The mathematical structure:
- Forward map: `g ↦ rescaleNorm⁻¹ • (g ∘ rescaleMap)`
- Inverse map: `h ↦ rescaleNorm • (h ∘ rescaleMapInv)`
- Normalization: `rescaleNorm = √(2π)` compensates for the Jacobian `1/(2π)`

The rescaling corresponds to the change of variables in the Mellin-Fourier correspondence:
  M[f](σ + iτ) = F[LogPull σ f](rescaleMap τ) = F[LogPull σ f](-τ/(2π))

Properties:
- Isometry: ‖RescaleL2_equiv g‖₂ = ‖g‖₂
- Inverse: `RescaleL2_equiv⁻¹ = RescaleL2_equiv.symm` using `rescaleMapInv`
- Composition: `(RescaleL2_equiv g)(τ) ≈ rescaleNorm⁻¹ • g(rescaleMap τ)` a.e.
-/
noncomputable def RescaleL2_equiv :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  { toLinearEquiv :=
      { toFun := rescaleForward_map
        invFun := rescaleInverse_map
        map_add' := rescaleForward_map_add
        map_smul' := rescaleForward_map_smul
        left_inv := rescaleInverse_rescaleForward
        right_inv := rescaleForward_rescaleInverse }
    norm_map' := rescaleForward_map_norm }

/-- On L², the rescaling isometry `RescaleL2_equiv` agrees a.e. with the
normalized composition by `rescaleMap`.

The representative of `RescaleL2_equiv (toLp g)` is a.e. equal to
`rescaleForward_fun g = fun τ => rescaleNorm⁻¹ • g(rescaleMap τ)`

where `rescaleNorm⁻¹ = 1/√(2π) = √(rescaleJacobian)`.
-/
lemma RescaleL2_equiv_ae_eq_rescale
    (g : ℝ → ℂ) (hg_L2 : MeasureTheory.MemLp g 2 volume) :
    (RescaleL2_equiv (hg_L2.toLp g) : ℝ → ℂ)
      =ᵐ[volume] rescaleForward_fun g := by
  -- The definition of RescaleL2_equiv uses rescaleForward_map,
  -- which in turn is defined via rescaleForward_fun.
  -- The representative of the Lp function equals the defining function a.e.
  classical
  -- Step 1: identify the representative of `RescaleL2_equiv (hg_L2.toLp g)`.
  have h_mem :
      MeasureTheory.MemLp
        (rescaleForward_fun
          (((hg_L2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)))
        2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp (MeasureTheory.Lp.memLp (hg_L2.toLp g))
  have h_coe :
      (RescaleL2_equiv (hg_L2.toLp g) : ℝ → ℂ)
        =ᵐ[volume]
      rescaleForward_fun
        (((hg_L2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) := by
    simpa [RescaleL2_equiv, rescaleForward_map] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := volume) h_mem)

  -- Step 2: relate the inner argument to the original function `g`.
  have h_rep :
      (((hg_L2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        =ᵐ[volume] g :=
    MeasureTheory.MemLp.coeFn_toLp (μ := volume) hg_L2

  -- Transport this a.e. equality through composition with `rescaleMap`.
  have h_comp :
      (fun τ : ℝ =>
        ((hg_L2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          (rescaleMap τ))
        =ᵐ[volume]
      (fun τ : ℝ => g (rescaleMap τ)) := by
    simpa [Function.comp] using
      (rescaleMap_quasiMeasurePreserving.ae_eq h_rep)

  -- Step 3: propagate the a.e. equality through `rescaleForward_fun`.
  have h_rescale :
      rescaleForward_fun
        (((hg_L2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        =ᵐ[volume]
      rescaleForward_fun g := by
    refine h_comp.mono ?_
    intro τ hτ
    -- Rewrite the inner argument using `hτ`.
    have hτ' :
        (((hg_L2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          (rescaleMap τ) : ℂ)
          = (g (rescaleMap τ) : ℂ) := by
      simpa [Function.comp] using hτ
    -- Apply scalar multiplication by `rescaleNorm⁻¹` and rearrange.
    have h_smul :=
      congrArg (fun z : ℂ => (rescaleNorm : ℝ)⁻¹ • z) hτ'
    simpa [rescaleForward_fun, Function.comp] using h_smul

  -- Step 4: combine the a.e. equalities.
  exact h_coe.trans h_rescale

noncomputable def Vσ_forward (σ : ℝ) :
    Hσ σ →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  RescaleL2_equiv.toLinearIsometry.comp
    (fourierL2_isometry.comp (Uσ_linIso σ))

/-- Forward map preserves norms (by construction as a composition of isometries). -/
lemma Vσ_forward_norm (σ : ℝ) (f : Hσ σ) :
    ‖Vσ_forward σ f‖ = ‖f‖ := by
  classical
  -- Norm is preserved successively by `Uσ_linIso`, `fourierL2_isometry`, and `RescaleL2_equiv`.
  have h₁ : ‖RescaleL2_equiv.toLinearIsometry
      (fourierL2_isometry ((Uσ_linIso σ) f))‖
        = ‖fourierL2_isometry ((Uσ_linIso σ) f)‖ :=
    RescaleL2_equiv.toLinearIsometry.norm_map _
  have h₂ : ‖fourierL2_isometry ((Uσ_linIso σ) f)‖
      = ‖(Uσ_linIso σ) f‖ :=
    fourierL2_isometry_norm _
  have h₃ : ‖(Uσ_linIso σ) f‖ = ‖f‖ :=
    (Uσ_linIso σ).norm_map f
  -- Unfold `Vσ_forward` and chain the equalities.
  simp [Vσ_forward, LinearIsometry.comp_apply, h₁, h₂, h₃]

/-- A.e. identity: Mellin transform equals the Fourier transform of
the log-pulled function, up to the standard angular-frequency rescaling and normalization.
This identifies the pointwise representative of `Vσ_forward σ f` with the
Mellin transform values, with the normalization factor rescaleNorm⁻¹ = 1/√(2π).
The rescaling τ ↦ -τ/(2π) and the normalization are built into Vσ_forward via RescaleL2_equiv. -/
lemma mellin_equals_forward_ae (σ : ℝ) (f : Hσ σ)
    (hL1 : Integrable (LogPull σ f)) :
    (fun τ : ℝ => rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ))
      =ᵐ[volume] (Vσ_forward σ f : ℝ → ℂ) := by
  classical
  -- The log-pulled function lies in L²(ℝ)
  have hg_mem : MemLp (LogPull σ f) 2 (volume : Measure ℝ) := mellin_in_L2 σ f
  -- Pointwise identity: Mellin f(σ+iτ) = Fourier[g](-τ/(2π))
  have h_point :
      ∀ τ : ℝ,
        mellinTransform (f : ℝ → ℂ) (σ + I * τ)
          = fourierIntegral (LogPull σ f) (-τ / (2 * Real.pi)) := by
    intro τ
    have := mellin_logpull_fourierIntegral σ τ f
    convert this using 2
  have h_ae_to_fourier :
      (fun τ : ℝ =>
        mellinTransform (f : ℝ → ℂ) (σ + I * τ))
        =ᵐ[volume]
      (fun τ : ℝ => fourierIntegral (LogPull σ f) (-τ / (2 * Real.pi))) :=
    Filter.Eventually.of_forall h_point
  -- Multiply both sides by rescaleNorm⁻¹
  have h_ae_to_fourier_scaled :
      (fun τ : ℝ => rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ))
        =ᵐ[volume]
      (fun τ : ℝ => rescaleNorm⁻¹ • fourierIntegral (LogPull σ f) (-τ / (2 * Real.pi))) := by
    refine h_ae_to_fourier.mono ?_
    intro τ hτ
    simp only
    congr 1
  -- Identify the L² representative of the Fourier transform with Vσ_forward σ f.
  -- Vσ_forward includes RescaleL2_equiv which applies rescaleMap and rescaleNorm⁻¹.
  have h_fourier_to_V :
      (fun τ : ℝ => rescaleNorm⁻¹ • fourierIntegral (LogPull σ f) (-τ / (2 * Real.pi)))
        =ᵐ[volume] (Vσ_forward σ f : ℝ → ℂ) := by
    -- Work with g := LogPull σ f.
    set g : ℝ → ℂ := LogPull σ f with hg_def
    -- L² and L¹ hypotheses for g.
    have hg_L2 : MemLp g 2 volume := by simpa [g, hg_def] using hg_mem
    have hg_L1 : Integrable g := by
      simpa [g, hg_def] using hL1
    -- On L¹ ∩ L², the extended L² Fourier isometry agrees a.e. with the Fourier integral.
    have h_ae_Lp :
        (fun ξ : ℝ =>
          (fourierL2_isometry ((Uσ_linIso σ) f) : ℝ → ℂ) ξ)
          =ᵐ[volume]
        fun ξ : ℝ => fourierIntegral g ξ := by
      -- Identify `(Uσ_linIso σ f)` with `hg_L2.toLp g`.
      have h_U :
          (Uσ_linIso σ f) = hg_L2.toLp g := by
        simp [Uσ_linIso, g, hg_def, mellin_in_L2] -- skeletal simp justification
      -- Apply the L² Fourier isometry a.e. identification and rewrite via `h_U`.
      simpa [h_U] using
        (fourierL2_isometry_ae_eq_fourierIntegral g hg_L1 hg_L2)
    -- Transport the a.e. equality along the rescaling τ ↦ -τ/(2π).
    have h_rescale' :
        (fun τ : ℝ =>
          (fourierL2_isometry ((Uσ_linIso σ) f) : ℝ → ℂ)
            (-τ / (2 * Real.pi)))
          =ᵐ[volume]
        (fun τ : ℝ =>
          fourierIntegral g (-τ / (2 * Real.pi))) := by
      have h_comp' :
          (fun τ : ℝ =>
            (fourierL2_isometry ((Uσ_linIso σ) f) : ℝ → ℂ)
              (rescaleMap τ))
            =ᵐ[volume]
          (fun τ : ℝ => fourierIntegral g (rescaleMap τ)) :=
        rescaleMap_quasiMeasurePreserving.ae_eq h_ae_Lp
      simpa [Function.comp, rescaleMap] using h_comp'
    -- Multiply both sides of `h_rescale'` by `rescaleNorm⁻¹`.
    have h_rescale_scaled :
        (fun τ : ℝ =>
          rescaleNorm⁻¹ • fourierIntegral g (-τ / (2 * Real.pi)))
          =ᵐ[volume]
        (fun τ : ℝ =>
          rescaleNorm⁻¹ •
            (fourierL2_isometry ((Uσ_linIso σ) f) : ℝ → ℂ)
              (-τ / (2 * Real.pi))) := by
      refine h_rescale'.symm.mono ?_
      intro τ hτ
      simp [hτ]
    -- Describe the pointwise representative of `Vσ_forward σ f`.
    have h_V :
        (fun τ : ℝ =>
          rescaleNorm⁻¹ •
            (fourierL2_isometry ((Uσ_linIso σ) f) : ℝ → ℂ)
              (-τ / (2 * Real.pi)))
          =ᵐ[volume]
        (Vσ_forward σ f : ℝ → ℂ) := by
      -- `Vσ_forward σ f` is `RescaleL2_equiv` applied to the L² Fourier image.
      -- Unfold the rescaling isometry to identify its representative.
      have hF_mem :
          MeasureTheory.MemLp
            (rescaleForward_fun
              ((fourierL2_isometry ((Uσ_linIso σ) f)
                : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
            2 (volume : Measure ℝ) :=
        rescaleForward_fun_memLp
          (MeasureTheory.Lp.memLp (fourierL2_isometry ((Uσ_linIso σ) f)))
      have h_coe_V :
          (Vσ_forward σ f : ℝ → ℂ)
            =ᵐ[volume]
          rescaleForward_fun
            ((fourierL2_isometry ((Uσ_linIso σ) f)
              : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
        simpa [Vσ_forward, LinearIsometry.comp_apply,
          RescaleL2_equiv, rescaleForward_map] using
          (MeasureTheory.MemLp.coeFn_toLp (μ := volume) hF_mem)
      -- Rewrite the RHS using the explicit formula for `rescaleForward_fun`.
      refine h_coe_V.symm.mono ?_
      intro τ hτ
      simpa [rescaleForward_fun, Function.comp, rescaleMap] using hτ
    -- Combine the scaled rescaling identity with the description of `Vσ_forward`.
    exact h_rescale_scaled.trans h_V
  exact h_ae_to_fourier_scaled.trans h_fourier_to_V

/-- A.e. identity for the full forward map: the normalized Mellin transform
agrees a.e. with the image of `f` under `Vσ_forward`. -/
lemma mellin_equals_full_ae (σ : ℝ) (f : Hσ σ)
    (hL1 : Integrable (LogPull σ f)) :
    (fun τ : ℝ => rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ))
      =ᵐ[volume] (Vσ_forward σ f : ℝ → ℂ) := by
  -- This is exactly `mellin_equals_forward_ae`.
  simpa using mellin_equals_forward_ae σ f hL1

/-- Construct a linear isometry equivalence from a linear isometry with dense range.
This is a placeholder that uses classical choice to construct the inverse.
In the full development, this would use the fact that a surjective linear isometry
between Hilbert spaces has a unique inverse that is also a linear isometry. -/
noncomputable def linearIsometryToEquiv (σ : ℝ)
    (U : Hσ σ →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (h_surj : Function.Surjective U) :
    Hσ σ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  classical
  -- Construct the inverse using classical choice from surjectivity
  -- For each g in Lp, choose some f such that U f = g
  let inv_fun : Lp ℂ 2 (volume : Measure ℝ) → Hσ σ := fun g =>
    Classical.choose (h_surj g)
  -- Verify that U (inv_fun g) = g
  have h_inv_right : ∀ g, U (inv_fun g) = g := fun g =>
    Classical.choose_spec (h_surj g)
  -- Construct the equivalence
  refine LinearIsometryEquiv.mk
    { toFun := U
      invFun := inv_fun
      left_inv := ?_
      right_inv := h_inv_right
      map_add' := U.map_add
      map_smul' := U.map_smul }
    (fun f => U.norm_map f)
  -- Prove left inverse: inv_fun (U f) = f
  intro f
  -- By injectivity of U (which follows from isometry): if U x = U f then x = f
  -- An isometry preserves norms, so ‖U x - U y‖ = ‖x - y‖, hence U is injective
  have h_inj : Function.Injective U := by
    intro x y hxy
    -- From hxy: U x = U y, we need to show x = y
    -- Use: ‖U (x - y)‖ = ‖x - y‖ (from isometry)
    have h_norm : ‖U (x - y)‖ = ‖x - y‖ := U.norm_map (x - y)
    rw [U.map_sub, hxy] at h_norm
    have : (U y : Lp ℂ 2 volume) - U y = 0 := _root_.sub_self (U y)
    rw [this, norm_zero] at h_norm
    exact eq_of_sub_eq_zero (norm_eq_zero.mp h_norm.symm)
  exact h_inj (h_inv_right (U f))

/-- Inverse change-of-variables for the logarithmic map.

For a given measurable `h : ℝ → ℂ`, consider the inverse-log pullback
`f_raw x = exp(-σ log x) * h (log x)` on `(0,∞)` (extended by `0` outside),
with the Mellin weight `x^(2σ-1)` on `(0,∞)`. Then the weighted L² integral
of `f_raw` over `(0,∞)` matches the unweighted L² integral of `h` on `ℝ`.

This mirrors `LogPull_sq_integral_eq` but in the inverse direction. -/
lemma inverseLogPull_sq_integral_eq (σ : ℝ) (h : ℝ → ℂ)
    (h_meas : Measurable h) :
    let f_raw : ℝ → ℂ :=
      fun x =>
        if 0 < x then
          (Real.exp (-σ * Real.log x) : ℂ) * h (Real.log x)
        else
          0
    let μσ : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))
    let If : ℝ≥0∞ :=
      ∫⁻ x, ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂μσ
    let Ih : ℝ≥0∞ :=
      ∫⁻ t, ((‖h t‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(volume : Measure ℝ)
    If = Ih := by
  classical
  intro f_raw μσ If Ih
  -- It suffices to prove the equality for the underlying lintegrals, then
  -- unfold the abbreviations `If` and `Ih`.
  have h_goal :
      ∫⁻ x, ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂μσ
        = ∫⁻ t, ((‖h t‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(volume : Measure ℝ) := by
    -- Step 1: rewrite the left-hand side using the withDensity description of μσ.
    -- On the base measure `volume.restrict (0,∞)`, the density is
    --   x ↦ ofReal (x^(2σ-1)).
    have h_weight_meas :
        Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)) :=
      ENNReal.measurable_ofReal.comp (measurable_id.pow_const (2 * σ - 1))
    -- Measurability of f_raw and of its squared nnnorm.
    have h_exp_meas :
        Measurable fun x : ℝ =>
          (Real.exp (-σ * Real.log x) : ℂ) := by
      -- Real-valued part: x ↦ exp(-σ * log x)
      have h_arg :
          Measurable fun x : ℝ => -σ * Real.log x := by
        simpa [mul_comm] using
          ((measurable_const : Measurable fun _ : ℝ => (-σ : ℝ)).mul
            Real.measurable_log)
      have h_real :
          Measurable fun x : ℝ => Real.exp (-σ * Real.log x) :=
        Real.measurable_exp.comp h_arg
      exact Complex.measurable_ofReal.comp h_real
    have h_comp_meas :
        Measurable fun x : ℝ => h (Real.log x) :=
      h_meas.comp Real.measurable_log
    have h_prod_meas :
        Measurable fun x : ℝ =>
          (Real.exp (-σ * Real.log x) : ℂ) * h (Real.log x) :=
      h_exp_meas.mul h_comp_meas
    have h_set_meas : MeasurableSet {x : ℝ | 0 < x} := by
      simpa [Set.Ioi] using (measurableSet_Ioi (a := (0 : ℝ)))
    have hf_raw_meas : Measurable f_raw := by
      classical
      refine Measurable.ite h_set_meas ?_ ?_
      · simpa using h_prod_meas
      · exact measurable_const
    have h_sq_meas :
        Measurable fun x : ℝ =>
          ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) :=
      (hf_raw_meas.nnnorm : Measurable fun x => (‖f_raw x‖₊ : ℝ≥0)).coe_nnreal_ennreal.pow_const _

    -- Expand μσ using withDensity, giving an integral over (0,∞) with weight x^(2σ-1).
    have h_lhs :
        ∫⁻ x, ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂μσ
          = ∫⁻ x, ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              * ENNReal.ofReal (x ^ (2 * σ - 1))
              ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa [μσ, mul_comm] using
        (lintegral_withDensity_eq_lintegral_mul
          (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * σ - 1)))
          (h_mf := h_weight_meas)
          h_sq_meas)

    -- On (0,∞), identify the weighted integrand in terms of h(log x) and x⁻¹.
    -- At a positive point x, we have:
    --   ‖f_raw x‖² · x^(2σ-1) = ‖h(log x)‖² · x⁻¹.
    have h_integrand_change :
        (fun x : ℝ =>
          ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
            * ENNReal.ofReal (x ^ (2 * σ - 1)))
          =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun x : ℝ =>
          ENNReal.ofReal (‖h (Real.log x)‖^2) *
            ENNReal.ofReal (x⁻¹)) := by
      -- Reduce to a pointwise computation on x > 0.
      refine (ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      have hxpos : 0 < x := hx
      have hx_nonneg : 0 ≤ x := hxpos.le
      -- Compute the squared norm of f_raw x.
      set a : ℝ := Real.exp (-σ * Real.log x) with ha
      have ha_nonneg : 0 ≤ a := by
        have : 0 < a := by
          simpa [ha] using Real.exp_pos (-σ * Real.log x)
        exact this.le
      have h_f_raw_def :
          f_raw x = (a : ℂ) * h (Real.log x) := by
        simp [f_raw, hxpos, ha]
      have hnorm :
          ‖f_raw x‖ = a * ‖h (Real.log x)‖ := by
        -- Norm of a real scalar times a complex is the product of norms.
        have hnorm_mul :
            ‖f_raw x‖ = ‖(a : ℂ)‖ * ‖h (Real.log x)‖ := by
          simp [h_f_raw_def]
        have hnorm_a : ‖(a : ℂ)‖ = a := by
          simp [Complex.norm_real, abs_of_nonneg ha_nonneg]
        rw [hnorm_a] at hnorm_mul
        simpa [mul_comm] using hnorm_mul
      have hnorm_sq :
          ‖f_raw x‖^2 = a^2 * ‖h (Real.log x)‖^2 := by
        have := congrArg (fun r : ℝ => r ^ 2) hnorm
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      -- Relate a^2 to an exponential.
      have ha_sq :
          a ^ 2 = Real.exp ((-2 * σ) * Real.log x) := by
        have hsum : (-σ * Real.log x) + (-σ * Real.log x)
            = (-2 * σ) * Real.log x := by ring
        calc
          a ^ 2 = Real.exp (-σ * Real.log x) * Real.exp (-σ * Real.log x) := by
            simp [ha, pow_two]
          _ = Real.exp ((-σ * Real.log x) + (-σ * Real.log x)) := by
            simpa [mul_comm] using
              (Real.exp_add (-σ * Real.log x) (-σ * Real.log x)).symm
          _ = Real.exp ((-2 * σ) * Real.log x) := by
            rw [hsum]
      -- Combine hnorm_sq with the Mellin weight x^(2σ-1).
      have h_real_eq :
          ‖f_raw x‖^2 * x ^ (2 * σ - 1)
            = ‖h (Real.log x)‖^2 * x⁻¹ := by
        have hx_pow_pos : 0 ≤ x ^ (2 * σ - 1) :=
          Real.rpow_nonneg hx_nonneg _
        have hx_pow_exp :
            x ^ (2 * σ - 1)
              = Real.exp ((2 * σ - 1) * Real.log x) := by
          rw [Real.rpow_def_of_pos hxpos, mul_comm]
        calc
          ‖f_raw x‖^2 * x ^ (2 * σ - 1)
              = (a ^ 2 * ‖h (Real.log x)‖^2) * x ^ (2 * σ - 1) := by
                simp [hnorm_sq, mul_comm, mul_left_comm, mul_assoc]
          _ = a ^ 2 * (‖h (Real.log x)‖^2 * x ^ (2 * σ - 1)) := by
                ring_nf
          _ = Real.exp ((-2 * σ) * Real.log x)
                * (‖h (Real.log x)‖^2 * x ^ (2 * σ - 1)) := by
                simp [ha_sq]
          _ = ‖h (Real.log x)‖^2 *
                Real.exp (((-2 * σ) + (2 * σ - 1)) * Real.log x) := by
                rw [hx_pow_exp]
                have h1 : Real.exp ((-2 * σ) * Real.log x)
                      * (‖h (Real.log x)‖ ^ 2 * Real.exp ((2 * σ - 1) * Real.log x))
                    = ‖h (Real.log x)‖ ^ 2 * (Real.exp ((-2 * σ) * Real.log x)
                      * Real.exp ((2 * σ - 1) * Real.log x)) := by ring
                rw [h1, ← Real.exp_add]
                congr 1
                ring_nf
          _ = ‖h (Real.log x)‖^2 *
                Real.exp ((-1) * Real.log x) := by
                congr 1
                have : (-2 * σ) + (2 * σ - 1) = (-1 : ℝ) := by ring
                rw [this]
          _ = ‖h (Real.log x)‖^2 * x⁻¹ := by
                have : Real.exp ((-1) * Real.log x) = x⁻¹ := by
                  -- For x > 0, x⁻¹ = exp(-log x).
                  rw [show (-1) * Real.log x = -Real.log x by ring]
                  rw [show x⁻¹ = x ^ (-1 : ℝ) by rw [Real.rpow_neg_one]]
                  rw [Real.rpow_def_of_pos hxpos]
                  ring_nf
                rw [this]
      -- Move to ENNReal-level equality of the weighted integrands.
      have h_nonneg_left :
          0 ≤ ‖f_raw x‖^2 * x ^ (2 * σ - 1) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx_nonneg _)
      have h_nonneg_right :
          0 ≤ ‖h (Real.log x)‖^2 * x⁻¹ := by
        have hx_pos' : 0 < x := hxpos
        have hx_nonneg' : 0 ≤ x⁻¹ := by
          exact inv_nonneg.mpr hx_nonneg
        exact mul_nonneg (sq_nonneg _) hx_nonneg'
      -- First convert the left side to the ofReal form.
      have h_left :
          ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
            * ENNReal.ofReal (x ^ (2 * σ - 1))
            = ENNReal.ofReal (‖f_raw x‖^2 * x ^ (2 * σ - 1)) := by
        -- As in `LogPull_sq_integral_eq`, rewrite via ofReal.
        have hsq :
            (ENNReal.ofReal ‖f_raw x‖) ^ (2 : ℕ)
              = ENNReal.ofReal (‖f_raw x‖^2) := by
          rw [pow_two, pow_two]
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
        calc
          ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
                * ENNReal.ofReal (x ^ (2 * σ - 1))
              = (ENNReal.ofReal ‖f_raw x‖) ^ (2 : ℕ)
                  * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
                    -- replace nnnorm by ofReal ‖·‖
                    congr 1
                    simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
                    rw [← ENNReal.coe_pow]
                    norm_cast
          _ = ENNReal.ofReal (‖f_raw x‖^2)
                  * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
                    rw [hsq]
          _ = ENNReal.ofReal (‖f_raw x‖^2 * x ^ (2 * σ - 1)) := by
                    rw [ENNReal.ofReal_mul (sq_nonneg _)]
      -- Now convert the right side using h_real_eq.
      have h_right :
          ENNReal.ofReal (‖h (Real.log x)‖^2 * x⁻¹)
            = ENNReal.ofReal (‖h (Real.log x)‖^2) *
                ENNReal.ofReal (x⁻¹) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
      -- Put everything together.
      have := congrArg ENNReal.ofReal h_real_eq
      -- Replace ofReal of the product on both sides using h_left and h_right.
      -- From h_real_eq and the above identities we deduce the desired equality.
      have :
          ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              * ENNReal.ofReal (x ^ (2 * σ - 1))
            = ENNReal.ofReal (‖h (Real.log x)‖^2) *
                ENNReal.ofReal (x⁻¹) := by
        -- Using h_left, h_right and h_real_eq
        have := h_real_eq
        -- Rewrite both sides using ofReal-multiplicativity.
        have h_left' :
            ENNReal.ofReal (‖f_raw x‖^2 * x ^ (2 * σ - 1))
              = ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
                  * ENNReal.ofReal (x ^ (2 * σ - 1)) := by
          simp [h_left]
        have h_right' :
            ENNReal.ofReal (‖h (Real.log x)‖^2 * x⁻¹)
              = ENNReal.ofReal (‖h (Real.log x)‖^2) *
                  ENNReal.ofReal (x⁻¹) := by
          exact h_right
        -- Convert using h_real_eq.
        have h_ofReal_eq :
            ENNReal.ofReal (‖f_raw x‖^2 * x ^ (2 * σ - 1))
              = ENNReal.ofReal (‖h (Real.log x)‖^2 * x⁻¹) := by
          simpa using congrArg ENNReal.ofReal h_real_eq
        -- Substitute.
        simpa [h_left', h_right'] using h_ofReal_eq
      simp [this]

    -- Now use `lintegral_congr_ae` to replace the integrand on the LHS.
    have h_lhs' :
        ∫⁻ x, ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              * ENNReal.ofReal (x ^ (2 * σ - 1))
              ∂(volume.restrict (Set.Ioi (0 : ℝ)))
          = ∫⁻ x, ENNReal.ofReal (‖h (Real.log x)‖^2) *
              ENNReal.ofReal (x⁻¹)
              ∂(volume.restrict (Set.Ioi (0 : ℝ))) :=
      lintegral_congr_ae h_integrand_change

    -- Step 2: change variables x = exp t using the logarithmic substitution.
    -- We invoke the dedicated substitution lemma for α = -1:
    --   ∫₀^∞ f(log x) x⁻¹ dx = ∫ f(t) dt.
    set F : ℝ → ℝ≥0∞ :=
      fun t => ENNReal.ofReal (‖h t‖^2) with hF
    have hF_meas : Measurable F := by
      -- measurability of ‖h t‖^2 and ofReal
      have h_norm : Measurable fun t : ℝ => ‖h t‖ :=
        h_meas.norm
      have h_sq : Measurable fun t : ℝ => ‖h t‖^2 := by
        simpa [pow_two] using h_norm.mul h_norm
      simpa [F, hF] using (ENNReal.measurable_ofReal.comp h_sq)

    have h_change :
        ∫⁻ x in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (‖h (Real.log x)‖^2) *
              ENNReal.ofReal (x⁻¹)
            ∂(volume.restrict (Set.Ioi (0 : ℝ)))
          = ∫⁻ t, ENNReal.ofReal (‖h t‖^2)
              ∂(volume : Measure ℝ) := by
      -- This is exactly lintegral_log_substitute with f = F.
      have := lintegral_log_substitute (f := F) hF_meas
      -- Expand F and simplify.
      simpa [F, hF] using this

    -- Combine the two descriptions of the LHS and the change-of-variables lemma.
    -- First rewrite the integral over μσ in terms of F(log x) * x⁻¹.
    have h_lhs_full :
        ∫⁻ x, ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂μσ
          = ∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖h (Real.log x)‖^2) *
                ENNReal.ofReal (x⁻¹)
              ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
      -- Start from h_lhs and then use h_lhs'.
      simpa [h_lhs] using h_lhs'

    -- Step 3: rewrite the RHS integral in terms of ENNReal.ofReal ‖h t‖².
    have h_rhs :
        ∫⁻ t, ((‖h t‖₊ : ℝ≥0∞) ^ (2 : ℕ))
            ∂(volume : Measure ℝ)
          = ∫⁻ t, ENNReal.ofReal (‖h t‖^2)
              ∂(volume : Measure ℝ) := by
      -- Pointwise equality of integrands.
      have h_integrand_eq :
          (fun t : ℝ =>
            ((‖h t‖₊ : ℝ≥0∞) ^ (2 : ℕ))) =
          (fun t : ℝ =>
            ENNReal.ofReal (‖h t‖^2)) := by
        funext t
        -- As in `LogPull_sq_integral_eq`, relate (‖·‖₊)^2 to ofReal(‖·‖²).
        have hsq :
            (ENNReal.ofReal ‖h t‖) ^ (2 : ℕ)
              = ENNReal.ofReal (‖h t‖^2) := by
          rw [pow_two, pow_two]
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
        calc
          ((‖h t‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              = (ENNReal.ofReal ‖h t‖) ^ (2 : ℕ) := by
                -- coe of NNReal and power commute; nnnorm is the NNReal norm
                simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
                rw [← ENNReal.coe_pow]
                norm_cast
          _ = ENNReal.ofReal (‖h t‖^2) := hsq
      simp [h_integrand_eq]

    -- Finally, put everything together.
    calc
      ∫⁻ x, ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂μσ
          = ∫⁻ x in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (‖h (Real.log x)‖^2) *
                ENNReal.ofReal (x⁻¹)
              ∂(volume.restrict (Set.Ioi (0 : ℝ))) := h_lhs_full
      _ = ∫⁻ t, ENNReal.ofReal (‖h t‖^2)
              ∂(volume : Measure ℝ) := h_change
      _ = ∫⁻ t, ((‖h t‖₊ : ℝ≥0∞) ^ (2 : ℕ))
              ∂(volume : Measure ℝ) := h_rhs.symm

  -- Unfold If and Ih to conclude.
  simpa [If, Ih] using h_goal

/-- Skeleton: a.e. inverse relation between `LogPull` and the inverse-log
construction used in `Uσ_linIso_surjective`.

For the specific `f` built from a representative `h` via the inverse
logarithmic change of variables (as in the proof of
`Uσ_linIso_surjective`), `LogPull σ f` should agree a.e. with `h` on `ℝ`.
Here we register this as a placeholder lemma; the eventual proof will use
the explicit formulas for `LogPull` and the change-of-variables identity
from `inverseLogPull_sq_integral_eq`. -/
lemma inverseLogPull_LogPull_ae
    (σ : ℝ) (h : ℝ → ℂ) (f : Hσ σ)
    (h_meas : Measurable h)
    (hf :
      (Hσ.toFun f)
        =ᵐ[(volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x =>
        if 0 < x then
          (Real.exp (-σ * Real.log x) : ℂ) * h (Real.log x)
        else 0)) :
    (LogPull σ f : ℝ → ℂ) =ᵐ[volume] h := by
  classical
  -- Work with the difference `h_diff := LogPull σ f - h`.
  let h_diff : ℝ → ℂ := fun t => LogPull σ f t - h t
  have h_diff_meas : Measurable h_diff := by
    refine (LogPull_measurable σ f).sub h_meas

  -- Abbreviation for the Mellin weight measure on `(0,∞)`.
  let μσ : Measure ℝ :=
    (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))

  -- Apply the inverse logarithmic change-of-variables identity to `h_diff`.
  -- This identifies the squared L² norm of the inverse-log pullback of `h_diff`
  -- with the squared L² norm of `h_diff` itself.
  have h_inverse :=
    (inverseLogPull_sq_integral_eq (σ := σ) (h := h_diff) h_diff_meas)

  -- Unfold the `let` bindings in `inverseLogPull_sq_integral_eq` to obtain
  -- an explicit equality between lintegrals.
  have h_inv_explicit :
      ∫⁻ x,
          ((‖(if 0 < x then
                (Real.exp (-σ * Real.log x) : ℂ) * h_diff (Real.log x)
              else 0)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂μσ
        =
      ∫⁻ t, ((‖h_diff t‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(volume : Measure ℝ) := by
    simpa [h_diff, μσ] using h_inverse

  -- Show that the inverse-log pullback of `h_diff` vanishes μσ-a.e., using `hf`.
  have h_inv_pullback_ae_zero :
      (fun x : ℝ =>
        if 0 < x then
          (Real.exp (-σ * Real.log x) : ℂ) * h_diff (Real.log x)
        else 0)
        =ᵐ[μσ] (fun _ => (0 : ℂ)) := by
    -- Start from the a.e. description of `Hσ.toFun f`.
    refine hf.mono ?_
    intro x hx
    -- hx : Hσ.toFun f x = if 0 < x then exp(-σ log x) * h (log x) else 0
    by_cases hx_pos : 0 < x
    · -- On `(0,∞)`, compute explicitly and use the defining relation for `LogPull`.
      have hx_form :
          Hσ.toFun f x
            = (Real.exp (-σ * Real.log x) : ℂ) * h (Real.log x) := by
        simpa [hx_pos] using hx
      have h_logpull :
          LogPull σ f (Real.log x)
            = (Real.exp (σ * Real.log x) : ℂ)
                * Hσ.toFun f (Real.exp (Real.log x)) := by
        simp [LogPull, LogPull_apply]
      -- On `(0,∞)`, `exp (log x) = x`.
      have h_logpull' :
          LogPull σ f (Real.log x)
            = (Real.exp (σ * Real.log x) : ℂ) * Hσ.toFun f x := by
        rw [h_logpull, Real.exp_log hx_pos]
      -- Substitute the explicit expression for `Hσ.toFun f x` from `hx_form`.
      have h_logpull_eq_h :
          LogPull σ f (Real.log x) = h (Real.log x) := by
        have h_real_prod :
            Real.exp (σ * Real.log x) * Real.exp (-σ * Real.log x)
              = 1 := by
          have hsum :
              (σ * Real.log x) + (-σ * Real.log x) = 0 := by
            ring
          have h_exp_mul :
              Real.exp (σ * Real.log x) * Real.exp (-σ * Real.log x)
                = Real.exp ((σ * Real.log x) + (-σ * Real.log x)) := by
            simpa using
              (Real.exp_add (σ * Real.log x) (-σ * Real.log x)).symm
          have h_exp_zero :
              Real.exp (σ * Real.log x) * Real.exp (-σ * Real.log x)
                = Real.exp 0 := by
            simpa [hsum] using h_exp_mul
          simpa using h_exp_zero
        have h_complex_prod :
            ((Real.exp (σ * Real.log x) : ℂ)
              * (Real.exp (-σ * Real.log x) : ℂ))
              = (1 : ℂ) := by
          -- View the product in ℝ and coerce to ℂ.
          simp only [← Complex.ofReal_mul, h_real_prod, Complex.ofReal_one]
        calc
          LogPull σ f (Real.log x)
              = (Real.exp (σ * Real.log x) : ℂ) * Hσ.toFun f x := h_logpull'
          _ = (Real.exp (σ * Real.log x) : ℂ) *
                ((Real.exp (-σ * Real.log x) : ℂ) * h (Real.log x)) := by
                simp [hx_form]
          _ = ((Real.exp (σ * Real.log x) : ℂ)
                * (Real.exp (-σ * Real.log x) : ℂ))
                * h (Real.log x) := by
                ring_nf
          _ = (1 : ℂ) * h (Real.log x) := by
                rw [h_complex_prod]
          _ = h (Real.log x) := by simp
      -- With `LogPull σ f (log x) = h (log x)`, the inverse-log pullback is zero.
      have h_diff_logx_zero : h_diff (Real.log x) = 0 := by
        simp only [h_diff]
        rw [h_logpull_eq_h]
        ring
      simp only [h_diff, h_diff_logx_zero]
      simp
    · -- On the non-positive half-line, the inverse-log pullback is identically zero.
      simp [h_diff, hx_pos]

  -- Hence the squared nnnorm integrand is zero μσ-a.e., so its lintegral is zero.
  have h_integrand_ae_zero :
      (fun x : ℝ =>
        ((‖(if 0 < x then
              (Real.exp (-σ * Real.log x) : ℂ) * h_diff (Real.log x)
            else 0)‖₊ : ℝ≥0∞) ^ (2 : ℕ)))
        =ᵐ[μσ] (fun _ => (0 : ℝ≥0∞)) := by
    refine h_inv_pullback_ae_zero.mono ?_
    intro x hx
    -- If the inverse-log pullback is zero, so is its squared nnnorm.
    simp only [hx, nnnorm_zero, ENNReal.coe_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

  have h_lintegral_left_zero :
      ∫⁻ x,
          ((‖(if 0 < x then
                (Real.exp (-σ * Real.log x) : ℂ) * h_diff (Real.log x)
              else 0)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂μσ
        = 0 := by
    have :=
      lintegral_congr_ae (μ := μσ) h_integrand_ae_zero
    simpa using this

  -- By the change-of-variables identity, the squared L² norm of `h_diff` on ℝ is zero.
  have h_lintegral_hdiff_zero :
      ∫⁻ t, ((‖h_diff t‖₊ : ℝ≥0∞) ^ (2 : ℕ))
        ∂(volume : Measure ℝ) = 0 := by
    -- `h_inv_explicit` identifies the RHS with the LHS, which is zero.
    rw [← h_inv_explicit, h_lintegral_left_zero]

  -- Rewrite the integrand as `ofReal (‖h_diff t‖^2)` to apply
  -- the standard zero-lintegral criterion.
  have h_integrand_eq :
      (fun t : ℝ =>
        ((‖h_diff t‖₊ : ℝ≥0∞) ^ (2 : ℕ)))
        =
      (fun t : ℝ =>
        ENNReal.ofReal (‖h_diff t‖^2)) := by
    funext t
    -- As in `inverseLogPull_sq_integral_eq`, relate (‖·‖₊)^2 to ofReal(‖·‖²).
    have hsq :
        (ENNReal.ofReal ‖h_diff t‖) ^ (2 : ℕ)
          = ENNReal.ofReal (‖h_diff t‖^2) := by
      rw [pow_two, pow_two]
      rw [ENNReal.ofReal_mul (norm_nonneg _)]
    calc
      ((‖h_diff t‖₊ : ℝ≥0∞) ^ (2 : ℕ))
          = (ENNReal.ofReal ‖h_diff t‖) ^ (2 : ℕ) := by
                -- coe of NNReal and power commute; nnnorm is the NNReal norm
                simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
                rw [← ENNReal.coe_pow]
                norm_cast
      _ = ENNReal.ofReal (‖h_diff t‖^2) := hsq

  have h_lintegral_ofReal_zero :
      ∫⁻ t, ENNReal.ofReal (‖h_diff t‖^2)
        ∂(volume : Measure ℝ) = 0 := by
    have :=
      lintegral_congr_ae
        (μ := (volume : Measure ℝ))
        (Filter.Eventually.of_forall (fun t => by simpa [h_integrand_eq]))
    -- This shows the two lintegrals coincide; combine with `h_lintegral_hdiff_zero`.
    simpa [h_integrand_eq, h_lintegral_hdiff_zero] using this.symm

  -- Apply `lintegral_eq_zero_iff'` to deduce `‖h_diff t‖^2 = 0` a.e.
  have h_aemeas :
      AEMeasurable (fun t : ℝ => ENNReal.ofReal (‖h_diff t‖^2))
        (volume : Measure ℝ) := by
    have h_meas_sq :
        Measurable fun t : ℝ => ‖h_diff t‖^2 := by
      have h_meas_norm : Measurable fun t : ℝ => ‖h_diff t‖ :=
        h_diff_meas.norm
      simpa [pow_two] using h_meas_norm.mul h_meas_norm
    exact (h_meas_sq.ennreal_ofReal).aemeasurable

  have h_ofReal_zero :
      (fun t : ℝ => ENNReal.ofReal (‖h_diff t‖^2))
        =ᵐ[volume] fun _ => (0 : ℝ≥0∞) :=
    (lintegral_eq_zero_iff' h_aemeas).1 h_lintegral_ofReal_zero

  -- Turn this into `h_diff = 0` a.e.
  have h_diff_ae_zero :
      h_diff =ᵐ[volume] fun _ => (0 : ℂ) := by
    refine h_ofReal_zero.mono ?_
    intro t ht
    -- From `ofReal (‖h_diff t‖^2) = 0` and nonnegativity, deduce `‖h_diff t‖^2 = 0`.
    have h_sq_le_zero :
        ‖h_diff t‖^2 ≤ 0 :=
      (ENNReal.ofReal_eq_zero.1 (by simpa using ht))
    have h_sq_ge_zero : 0 ≤ ‖h_diff t‖^2 := sq_nonneg _
    have h_sq_zero : ‖h_diff t‖^2 = 0 :=
      le_antisymm h_sq_le_zero h_sq_ge_zero
    have h_norm_zero : ‖h_diff t‖ = 0 := by
      -- Use the fact that `a^2 = 0` implies `a = 0` in ℝ.
      rw [pow_two] at h_sq_zero
      exact mul_self_eq_zero.mp h_sq_zero
    -- Finally, use `norm_eq_zero` to conclude `h_diff t = 0`.
    simpa [h_diff] using (norm_eq_zero.mp h_norm_zero)

  -- Translate `h_diff = 0` a.e. into `LogPull σ f = h` a.e.
  have h_ae_eq_zero :
      (fun t : ℝ => LogPull σ f t - h t)
        =ᵐ[volume] fun _ => (0 : ℂ) := h_diff_ae_zero
  refine h_ae_eq_zero.mono ?_
  intro t ht
  exact sub_eq_zero.mp ht

/-- Placeholder: surjectivity of the core log-pull isometry into L²(ℝ).
In the completed development this will be proved from the Mellin–Plancherel
theory (dense range plus closed range for an isometry). -/
lemma Uσ_linIso_surjective (σ : ℝ) :
    Function.Surjective (Uσ_linIso σ) := by
  classical
  -- Goal: for every `g : Lp ℂ 2`, construct `f : Hσ σ` with `Uσ_linIso σ f = g`.
  intro g
  -- Skeleton of the future construction:
  -- Step 1: choose a representative `h : ℝ → ℂ` of `g` in L²(ℝ).
  let h : ℝ → ℂ := (g : ℝ → ℂ)
  have h_mem : MeasureTheory.MemLp h 2 (volume : Measure ℝ) :=
    MeasureTheory.Lp.memLp g
  -- Step 2: use the inverse logarithmic change of variables to define
  --    a candidate function on (0,∞) with the Mellin weight.
  -- On (0,∞) this should invert `LogPull σ`:
  --   `(LogPull σ f)(t) = exp(σ t) * f (exp t)`
  -- so formally we want `f(x) = x^(-σ) * h(log x)` for `x > 0`.
  let f_raw : ℝ → ℂ :=
    fun x =>
      if hx : 0 < x then
        (Real.exp (-σ * Real.log x) : ℂ) * h (Real.log x)
       else
         0
  -- Step 3: show this candidate is in `Hσ σ`, obtaining `f : Hσ σ`.
  -- We will later prove that `f_raw` belongs to the weighted L² space,
  -- and use `MemLp.toLp` to package it as an element of `Hσ σ`.
  have f_mem :
      MeasureTheory.MemLp f_raw 2
        ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) := by
    -- Target: `f_raw ∈ L²((0,∞), x^(2σ-1)dx)`. This should follow from
      -- `h_mem : MemLp h 2 volume` via the inverse logarithmic change of variables
    -- `x = exp t` (the inverse of `LogPull σ`).
    --
    -- Skeleton of the argument:
    -- * prove measurability of `f_raw` on ℝ;
    -- * compute the weighted L² integral of `f_raw` on (0,∞) by changing
    --   variables to the L² integral of `h` on ℝ;
    -- * conclude finiteness from `h_mem`.
    refine ⟨?meas, ?fin⟩
    · -- Step 3a: measurability / a.e. strong measurability of `f_raw`.
      -- First, record measurability of the representative `h`.
      have h_sm : StronglyMeasurable h := by
        -- `h` is the standard representative of `g` in `Lp`, which is strongly
        -- measurable by construction.
        simpa [h] using (Lp.stronglyMeasurable (f := g))
      have h_meas : Measurable h := h_sm.measurable
      -- Measurability of the weight factor `x ↦ exp(-σ * log x)` (as ℝ → ℂ).
      have h_exp_meas :
          Measurable fun x : ℝ =>
            (Real.exp (-σ * Real.log x) : ℂ) := by
        -- First treat the real-valued function `x ↦ Real.exp (-σ * Real.log x)`.
        have h_arg :
            Measurable fun x : ℝ => -σ * Real.log x := by
          -- constant `-σ` times measurable `log x`
          simpa [mul_comm] using
            ((measurable_const : Measurable fun _ : ℝ => (-σ : ℝ)).mul
              Real.measurable_log)
        have h_real :
            Measurable fun x : ℝ => Real.exp (-σ * Real.log x) :=
          Real.measurable_exp.comp h_arg
        -- Then embed into ℂ via `ofReal`.
        exact Complex.measurable_ofReal.comp h_real
      -- Measurability of the composed representative `x ↦ h (log x)`.
      have h_comp_meas :
          Measurable fun x : ℝ => h (Real.log x) :=
        h_meas.comp Real.measurable_log
      -- Measurability of the product on the positive half-line.
      have h_prod_meas :
          Measurable fun x : ℝ =>
            (Real.exp (-σ * Real.log x) : ℂ) * h (Real.log x) :=
        h_exp_meas.mul h_comp_meas
      -- The domain `{x | 0 < x}` is measurable (it is `Ioi 0`).
      have h_set_meas : MeasurableSet {x : ℝ | 0 < x} := by
        simpa [Set.Ioi] using (measurableSet_Ioi (a := (0 : ℝ)))
      -- Put everything together for the piecewise definition of `f_raw`.
      have hf_meas : Measurable f_raw := by
        classical
        refine Measurable.ite h_set_meas ?_ ?_
        · -- branch on `{x | 0 < x}`
          simpa using h_prod_meas
        · -- branch on `{x | ¬ 0 < x}`: constant function
          exact measurable_const
      -- Turn measurability into a.e. strong measurability for the
      -- weighted measure defining `Hσ σ`.
      exact hf_meas.aestronglyMeasurable
    · -- Step 3b: finiteness of the L² norm of `f_raw` with respect to
      -- the weighted measure. Using the explicit formula for `f_raw` and
      -- the weight `x^(2σ-1)`, the integrand can be rewritten to match
      -- `‖h(t)‖²` after the substitution `x = exp t`. Then
      -- `h_mem : MemLp h 2 volume` yields finiteness.
      --
      -- In the completed development, this will parallel the proof of
      -- `mellin_in_L2` but for the inverse logarithmic change of variables.
      -- We outline the argument and leave the change-of-variables steps as TODOs.
      have : eLpNorm f_raw 2
          (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
            (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))) < ∞ := by
        -- Work with the weighted measure defining `Hσ σ`.
        set μσ :
            Measure ℝ :=
          (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
            (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) with hμσ
        have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
        have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
        -- Define the squared-norm lintegrals for `f_raw` and `h`.
        set If : ℝ≥0∞ :=
          ∫⁻ x, ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂μσ with hIf
        set Ih : ℝ≥0∞ :=
          ∫⁻ t, ((‖h t‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(volume : Measure ℝ) with hIh
        -- Change of variables x = exp t: the weighted integral for `f_raw`
        -- equals the unweighted L² integral of `h` on ℝ.
        have hIf_eq_Ih : If = Ih := by
          -- Use the global inverse change-of-variables lemma,
          -- which mirrors `LogPull_sq_integral_eq` but in reverse.
          -- First, record measurability of h.
          have h_sm : StronglyMeasurable h := by
            -- `h` is the standard representative of `g` in `Lp`, which is strongly
            -- measurable by construction.
            simpa [h] using (Lp.stronglyMeasurable (f := g))
          have h_meas : Measurable h := h_sm.measurable
          have h_global :=
            inverseLogPull_sq_integral_eq (σ := σ) (h := h) h_meas
          -- Unfold the local definitions so that the two sides match.
          simpa [If, Ih, μσ, f_raw] using h_global
        -- From `h_mem : MemLp h 2 volume`, deduce finiteness of Ih.
        have hIh_fin : Ih < ∞ := by
          -- Use the standard characterization of `MemLp` at p = 2.
          have hInt_sq : Integrable (fun t : ℝ => ‖h t‖ ^ 2)
              (volume : Measure ℝ) := by
            -- `memLp_two_iff_integrable_sq_norm` gives integrability of ‖h‖².
            have := (memLp_two_iff_integrable_sq_norm h_mem.1).1 h_mem
            -- Rewrite in terms of the usual (real) norm.
            simpa [pow_two] using this
          -- The Bochner integral of ‖h‖² is finite, hence so is the
          -- corresponding lintegral of the squared nnnorm.
          have h_nonneg :
              0 ≤ᵐ[volume] fun t : ℝ => ‖h t‖ ^ 2 :=
            Filter.Eventually.of_forall (fun _ => sq_nonneg _)
          have hOfReal :=
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt_sq h_nonneg
          -- Convert from `ofReal` to the nnnorm expression used in Ih.
          have h_lintegral_fin :
              (∫⁻ t, ((‖h t‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂(volume : Measure ℝ)) < ∞ := by
            -- First, finiteness for the lintegral of `ENNReal.ofReal (‖h t‖^2)`.
            have h_lint_ofReal_fin :
                (∫⁻ t, ENNReal.ofReal (‖h t‖ ^ 2) ∂(volume : Measure ℝ)) < ∞ := by
              -- From `hOfReal`, this lintegral equals the (finite) real integral
              -- of a nonnegative function.
              rw [← hOfReal]
              -- The integral is finite, use ENNReal.ofReal_lt_top
              apply ENNReal.ofReal_lt_top
            -- Now use the pointwise equality between `ofReal ‖h‖` and `‖h‖₊`.
            have h_integrand_eq :
                (fun t : ℝ =>
                  ENNReal.ofReal (‖h t‖ ^ 2)) =
                (fun t : ℝ =>
                  ((‖h t‖₊ : ℝ≥0∞) ^ (2 : ℕ))) := by
              funext t
              -- This is exactly the computation used in `mellin_plancherel_formula`.
              have hnn : 0 ≤ ‖h t‖ := norm_nonneg _
              simp [pow_two, ENNReal.ofReal_mul, hnn]
            -- Transport finiteness along the a.e. equality of integrands.
            have := h_lint_ofReal_fin
            simpa [Ih, h_integrand_eq] using this
          simpa [Ih] using h_lintegral_fin
        have hIf_fin : If < ∞ := by
          simpa [hIf_eq_Ih] using hIh_fin
        -- Finally, express eLpNorm via the lintegral and use finiteness of If.
        -- This step is analogous to the last part of `mellin_in_L2`.
        -- TODO: show that finiteness of `If` implies `eLpNorm f_raw 2 μσ < ∞`
        -- by rewriting `eLpNorm` as a root of the lintegral of ‖f_raw‖ₑ²,
        -- and relating that lintegral to `If` via an `enorm`→`nnnorm` lemma
        -- for the measure `μσ`.
        have h_enorm_lt_top :
            (∫⁻ x, ‖f_raw x‖ₑ ^ (2 : ℝ) ∂μσ) < ∞ := by
          -- Relate the ENNReal norm integrand to the squared nnnorm integrand.
          have h_integrand_eq :
              (fun x : ℝ => ‖f_raw x‖ₑ ^ (2 : ℝ)) =
              (fun x : ℝ => ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ))) := by
            funext x
            -- As in `Lp_norm_sq_as_lintegral`, `‖·‖ₑ` and `‖·‖₊` coincide as ENNReal.
            have hx : (‖f_raw x‖ₑ : ℝ≥0∞) = (‖f_raw x‖₊ : ℝ≥0∞) := rfl
            simp [hx]
          -- Therefore the lintegral of `‖f_raw‖ₑ²` equals `If`.
          have h_int_eq_If :
              (∫⁻ x, ‖f_raw x‖ₑ ^ (2 : ℝ) ∂μσ) = If := by
            have h_int_eq :
                (∫⁻ x, ‖f_raw x‖ₑ ^ (2 : ℝ) ∂μσ)
                  = ∫⁻ x, ((‖f_raw x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂μσ := by
              simp [h_integrand_eq]
            -- Rewrite the right-hand side via the definition of `If`.
            simp [If]
          -- Transport finiteness from `If` to the ENNReal norm lintegral.
          simpa [h_int_eq_If] using hIf_fin
        have : eLpNorm f_raw 2 μσ < ∞ := by
          -- Rewrite the extended L² norm via the lintegral of the ENNReal norm.
          rw [eLpNorm_eq_lintegral_rpow_enorm (μ := μσ) (f := f_raw)
                hp_ne_zero hp_ne_top]
          simp only [ENNReal.toReal_ofNat, one_div]
          -- It remains to show the 1/2 power of the lintegral is finite.
          have : (∫⁻ x, ‖f_raw x‖ₑ ^ (2 : ℝ) ∂μσ) ^ (2 : ℝ)⁻¹ < ∞ := by
            apply ENNReal.rpow_lt_top_of_nonneg
            · simp
            · exact h_enorm_lt_top.ne
          exact this
        exact this
      simpa using this
  let f : Hσ σ := f_mem.toLp f_raw
  -- Step 4: check that `Uσ_linIso σ f` agrees a.e. with `g`, hence equals `g` in `Lp`.
  -- First, relate `Uσ_linIso σ f` to `LogPull σ f` as Lp elements.
  have hU_logpull_ae :
      ((Uσ_linIso σ f) : ℝ → ℂ)
        =ᵐ[volume] LogPull σ f := by
    -- By definition, `Uσ_linIso` is built from `mellin_in_L2` and `LogPull`.
    -- The representative of `toLp` is a.e. equal to the underlying function.
    simpa [Uσ_linIso] using
      (MeasureTheory.MemLp.coeFn_toLp
        (μ := (volume : Measure ℝ)) (mellin_in_L2 σ f))
  -- Next, identify `LogPull σ f` a.e. with the chosen representative `h`.
  have h_logpull_ae :
      (LogPull σ f : ℝ → ℂ) =ᵐ[volume] h := by
    -- Placeholder: a.e. inverse relation between `LogPull` and the
    -- inverse-log construction used to define `f` from `h`.
    -- In the completed development this will follow from a pointwise
    -- computation and the change-of-variables identity
    -- `inverseLogPull_sq_integral_eq`.
    have h_sm : StronglyMeasurable h := by
      simpa [h] using (Lp.stronglyMeasurable (f := g))
    have h_meas : Measurable h := h_sm.measurable
    have hf : (Hσ.toFun f)
        =ᵐ[(volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))]
      (fun x =>
        if 0 < x then
          (Real.exp (-σ * Real.log x) : ℂ) * h (Real.log x)
        else 0) := by
      -- f was constructed as toLp f_raw, so Hσ.toFun f =ᵐ f_raw
      simpa [f, f_raw] using MeasureTheory.MemLp.coeFn_toLp f_mem
    exact inverseLogPull_LogPull_ae (σ := σ) (h := h) (f := f) h_meas hf
  have hU_ae :
      ((Uσ_linIso σ f) : ℝ → ℂ)
        =ᵐ[volume] h :=
    hU_logpull_ae.trans h_logpull_ae
  -- Finally, compare `h` with the original representative of `g`.
  have hg_ae : (g : ℝ → ℂ) =ᵐ[volume] h := by
    -- This is immediate from the definition `h := (g : ℝ → ℂ)`.
    simp [h]
  have h_eq :
      Uσ_linIso σ f = g := by
    -- Two `Lp` elements are equal if their representatives coincide a.e.
    apply Lp.ext (μ := (volume : Measure ℝ))
    exact hU_ae.trans hg_ae.symm
  exact ⟨f, h_eq⟩

lemma vσ_forward_surjective (σ : ℝ) : Function.Surjective (Vσ_forward σ) := by
  classical
  have hU : Function.Surjective (Uσ_linIso σ) :=
    Uσ_linIso_surjective σ
  -- The L² Fourier and Rescale legs are actual isometric equivalences, hence surjective.
  have hFourier : Function.Surjective (FourierL2_equiv.toLinearIsometry) := by
    intro g; exact ⟨FourierL2_equiv.symm g, LinearIsometryEquiv.apply_symm_apply _ g⟩
  have hRescale : Function.Surjective (RescaleL2_equiv.toLinearIsometry) := by
    intro g; exact ⟨RescaleL2_equiv.symm g, LinearIsometryEquiv.apply_symm_apply _ g⟩
  -- Compose surjections: Uσ → Fourier → Rescale
  have hForward : Function.Surjective (Vσ_forward σ) := by
    -- We use surjectivity of each leg in the composition
    -- `Uσ_linIso σ` → `fourierL2_isometry` → `RescaleL2_equiv`.
    intro g
    -- Step 1: fourierL2_isometry is surjective, with inverse invFourierL2_isometry.
    have hFourierIso : Function.Surjective fourierL2_isometry := by
      intro h
      refine ⟨invFourierL2_isometry h, ?_⟩
      simpa using invFourierL2_isometry_right_inv h
    -- Step 2: take a preimage of g under the rescaling isometry.
    obtain ⟨g₁, hg₁⟩ := hRescale g
    -- Step 3: take a preimage of g₁ under the L² Fourier isometry.
    obtain ⟨g₂, hg₂⟩ := hFourierIso g₁
    -- Step 4: take a preimage of g₂ under Uσ_linIso.
    obtain ⟨f, hf⟩ := hU g₂
    refine ⟨f, ?_⟩
    -- Step 5: unravel Vσ_forward and compose the equalities.
    calc
      Vσ_forward σ f
          = RescaleL2_equiv.toLinearIsometry
              (fourierL2_isometry (Uσ_linIso σ f)) := by
            simp [Vσ_forward, LinearIsometry.comp_apply]
      _ = RescaleL2_equiv.toLinearIsometry
              (fourierL2_isometry g₂) := by
            simp [hf]
      _ = RescaleL2_equiv.toLinearIsometry g₁ := by
            simp [hg₂]
      _ = g := hg₁
  exact hForward

/-- The Mellin transform is unitarily equivalent to Fourier transform.
The unitary map V sends f ∈ Hσ(σ) to its Fourier transform in L²(ℝ) after
logarithmic change of variables. The Mellin transform M[f](σ+iτ) equals
(up to normalization) the Fourier transform of the log-pulled function. -/
theorem mellin_fourier_unitary_equivalence (σ : ℝ) :
    ∃ (V : Hσ σ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ)),
    ∀ (f : Hσ σ), Integrable (LogPull σ f) →
    (fun τ : ℝ => rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ))
      =ᵐ[volume] (V f : ℝ → ℂ) := by
  classical
  -- Use the concrete construction of the Mellin-Fourier equivalence
  set V : Hσ σ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
    linearIsometryToEquiv σ (Vσ_forward σ) (vσ_forward_surjective σ)
  refine ⟨V, ?_⟩
  intro f hL1
  -- A.e. identification with the Mellin transform via the forward map,
  -- then transport along the equality `V f = Vσ_forward σ f`.
  have h_forward :
      (fun τ : ℝ => rescaleNorm⁻¹ • mellinTransform (f : ℝ → ℂ) (σ + I * τ))
        =ᵐ[volume] (Vσ_forward σ f : ℝ → ℂ) :=
    mellin_equals_full_ae σ f hL1
  have h_matchV :
      (V f : ℝ → ℂ) =ᵐ[volume] (Vσ_forward σ f : ℝ → ℂ) := by
    -- By construction, mellin_fourier_equiv is built from Vσ_forward,
    -- so they agree a.e. as representatives in L²(ℝ).
    unfold V
    rfl
  exact h_forward.trans h_matchV.symm

end ClassicalParseval

end Frourio
