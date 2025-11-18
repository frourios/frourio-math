import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
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

/-- A.e. identity (skeleton): Mellin transform equals the Fourier transform of
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
      -- From `h_mem` we know that `h` is a.e. strongly measurable on ℝ.
      have h_ae_strong :
          AEStronglyMeasurable h (volume : Measure ℝ) :=
        h_mem.aestronglyMeasurable
      -- Using this, we may pick a strongly measurable representative of `h`
      -- (skeleton; details omitted) and deduce that `f_raw` is measurable,
      -- since it is built from compositions of `Real.log`, exponentials,
      -- and scalar multiplication, glued with an `if` over the open set `{x | 0 < x}`.
      have hf_meas : Measurable f_raw := by
        -- TODO: construct `hf_meas` explicitly from `h_ae_strong`
        -- via a measurable representative of `h` and standard
        -- measurability lemmas for `Real.log` and `Real.exp`.
        sorry
      -- Turn measurability into a.e. strong measurability for the
      -- weighted measure defining `Hσ σ`.
      exact hf_meas.aestronglyMeasurable
    · -- Step 3b: finiteness of the L² norm of `f_raw` with respect to
      -- the weighted measure. Using the explicit formula for `f_raw` and
      -- the weight `x^(2σ-1)`, the integrand can be rewritten to match
      -- `‖h(t)‖²` after the substitution `x = exp t`. Then
      -- `h_mem : MemLp h 2 volume` yields finiteness.
      -- TODO: implement the change-of-variables calculation and bound.
      sorry
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
    -- TODO: show that the inverse construction `f_raw ↦ f` really inverts `LogPull σ`
    -- at the level of representatives, using the explicit formulas and
    -- change-of-variables in the Mellin–Plancherel theory.
    sorry
  have hU_ae :
      ((Uσ_linIso σ f) : ℝ → ℂ)
        =ᵐ[volume] h :=
    hU_logpull_ae.trans h_logpull_ae
  -- Finally, compare `h` with the original representative of `g`.
  have hg_ae : (g : ℝ → ℂ) =ᵐ[volume] h := by
    -- This is immediate from the definition `h := (g : ℝ → ℂ)`.
    simpa [h] using
      (Filter.Eventually.of_forall (fun x : ℝ => rfl))
  have h_eq :
      Uσ_linIso σ f = g := by
    -- Two `Lp` elements are equal if their representatives coincide a.e.
    apply Lp.ext (μ := (volume : Measure ℝ))
    exact hU_ae.trans hg_ae.symm
  exact ⟨f, h_eq⟩

/-- Placeholder: the forward map Vσ_forward is surjective.
This would be proved by showing that:
1. LogPull (Uσ) has dense range in L²(ℝ)
2. Fourier transform is surjective on L²(ℝ)
3. Rescaling is surjective
Therefore the composition is surjective. -/
  lemma vσ_forward_surjective (σ : ℝ) : Function.Surjective (Vσ_forward σ) := by
  classical
  -- Placeholder: surjectivity of the core log-pull isometry into L²(ℝ).
  -- In the completed development this follows from the Mellin–Plancherel theory
  -- (dense range + closed range for an isometry). We register it here as an
  -- placeholder statement via the helper lemma `Uσ_linIso_surjective`.
  have hU : Function.Surjective (Uσ_linIso σ) :=
    Uσ_linIso_surjective σ
  -- The L² Fourier and Rescale legs are actual isometric equivalences, hence surjective.
  have hFourier : Function.Surjective (FourierL2_equiv.toLinearIsometry) := by
    intro g; exact ⟨FourierL2_equiv.symm g, LinearIsometryEquiv.apply_symm_apply _ g⟩
  have hRescale : Function.Surjective (RescaleL2_equiv.toLinearIsometry) := by
    intro g; exact ⟨RescaleL2_equiv.symm g, LinearIsometryEquiv.apply_symm_apply _ g⟩
  -- Compose surjections: Uσ → Fourier → Rescale
  have hForward : Function.Surjective (Vσ_forward σ) := by
    intro g
    obtain ⟨f, hf⟩ := hRescale g
    obtain ⟨h, hh⟩ := hFourier f
    obtain ⟨k, hk⟩ := hU h
    use k
    simp only [Vσ_forward, LinearIsometry.coe_comp, Function.comp_apply]
    rw [hk]
    -- Need to show: RescaleL2_equiv.toLinearIsometry (fourierL2_isometry h) = g
    -- We have: FourierL2_equiv.toLinearIsometry h = f and RescaleL2_equiv.toLinearIsometry f = g
    have : fourierL2_isometry h = FourierL2_equiv.toLinearIsometry h := by
      -- This follows from the definition of fourierL2_isometry
      -- as the underlying isometry of FourierL2_equiv
      sorry
    rw [this, hh]
    exact hf
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

section Applications

/-- Mellin-Parseval identity for inner products.
The inner product in frequency space (Mellin transforms) equals the inner product
in the original weighted space Hσ(σ). The normalization depends on the Fourier
kernel convention: with kernel e^(-2πiξt), the coefficient is 1. -/
theorem mellin_parseval_inner_product (σ : ℝ) (f g : Hσ σ) :
    ∫ τ : ℝ, mellinTransform (f : ℝ → ℂ) (σ + I * τ) *
      starRingEnd ℂ (mellinTransform (g : ℝ → ℂ) (σ + I * τ)) ∂volume
    = ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℂ) x *
      starRingEnd ℂ ((g : ℝ → ℂ) x) * (x : ℂ) ^ (2 * σ - 1 : ℂ) ∂volume := by
  -- This is the Mellin-Parseval identity for inner products:
  -- ∫ M_f(σ+iτ) · conj(M_g(σ+iτ)) dτ = ∫ f(x) · conj(g(x)) · x^(2σ-1) dx
  -- Proof outline:
  -- 1. Use change of variables x = e^t to convert RHS to L²(ℝ) inner product
  -- 2. Apply Fourier-Plancherel identity (with angular frequency normalization)
  -- 3. Use the relation M[f](σ+iτ) = F[LogPull(σ,f)](τ/2π) with proper normalization
  sorry

/-- Energy conservation in Mellin space (Plancherel theorem for Mellin transform).
The L² norm in the weighted space Hσ(σ) is preserved (up to a constant factor)
under the Mellin transform. The factor 2π comes from the angular frequency
normalization in the Fourier kernel e^(-2πiξt). -/
theorem mellin_energy_conservation (σ : ℝ) (f : Hσ σ) :
    (2 * Real.pi) * ∫ x in Set.Ioi (0 : ℝ), ‖(f : ℝ → ℂ) x‖ ^ 2 * (x : ℝ) ^ (2 * σ - 1) ∂volume
    = ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume := by
  -- Proof outline:
  -- 1. LHS = 2π · ∫ |f(x)|² x^(2σ-1) dx = 2π · ‖f‖²_{Hσ(σ)}
  -- 2. Change of variables x = e^t: LHS = 2π · ∫ |LogPull(σ,f)(t)|² dt
  -- 3. M[f](σ+iτ) = F[LogPull(σ,f)](τ/2π) where F uses kernel e^(-2πiξt)
  -- 4. Variable change τ ↔ ξ = τ/2π in RHS gives Fourier-Plancherel
  -- 5. ∫ |M[f](σ+iτ)|² dτ = 2π · ∫ |F[LogPull](ξ)|² dξ = 2π · ‖LogPull(σ,f)‖²
  sorry

end Applications

end Frourio
