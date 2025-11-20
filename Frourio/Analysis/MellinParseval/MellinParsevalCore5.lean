import Frourio.Analysis.FourierPlancherel
import Frourio.Analysis.FourierPlancherelL2.FourierPlancherelL2
import Frourio.Analysis.MellinPlancherel
import Frourio.Analysis.MellinParseval.MellinParsevalCore4
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

/-- Connection between Mellin-Parseval and Fourier-Parseval.
The weighted L² norm on (0,∞) with weight x^(2σ-1)dx equals the unweighted
L² norm on ℝ after logarithmic change of variables with appropriate weight. -/
theorem mellin_fourier_parseval_connection (σ : ℝ) (f : Hσ σ) :
    let g := LogPull σ f
    ∃ (hg : MemLp g 2 volume), ‖f‖ ^ 2 = ‖MemLp.toLp g hg‖ ^ 2 := by
  classical
  set g : ℝ → ℂ := LogPull σ f with hg_def
  have hg_mem : MemLp g 2 (volume : Measure ℝ) := mellin_in_L2 σ f
  refine ⟨hg_mem, ?_⟩
  -- Step 2: compute the eLpNorm via the weighted Hσ norm of f.
  have h_eLp_sq : ((eLpNorm g 2 (volume : Measure ℝ)).toReal) ^ 2 = ‖f‖ ^ 2 := by
    -- The change of variables x = e^t gives the isometry between
    -- Hσ(σ) (with measure x^(2σ-1)dx on (0,∞)) and L²(ℝ) via LogPull.
    -- This is exactly the content of the Mellin-Plancherel formula.
    -- Step A: Use Mellin-Plancherel to relate the L² integral of g to ‖f‖²
    have h_pl : ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂volume = ‖f‖ ^ 2 := by
      simp only [g, hg_def]
      exact mellin_plancherel_formula (σ := σ) (f := f)
    -- Step B: express the square of eLpNorm g via the integral of ‖g‖²
    have h_norm_sq : ((eLpNorm g 2 (volume : Measure ℝ)).toReal) ^ 2
          = ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂volume := by
      have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
      have h₁ :=
        congrArg ENNReal.toReal
          (MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
            (f := g) hp0 hp_top hg_mem)
      set B : ℝ :=
          (∫ τ : ℝ, ‖g τ‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
            ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ with hB
      have h_two : ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) := by simp
      have h_base_nonneg :
          0 ≤ ∫ τ : ℝ, ‖g τ‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume := by
        refine integral_nonneg ?_
        intro τ
        have := sq_nonneg ‖g τ‖
        simpa [h_two, pow_two] using this
      have hB_nonneg : 0 ≤ B := by
        have h_rpow_nonneg :
            0 ≤
                (∫ τ : ℝ, ‖g τ‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
                  ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ :=
          Real.rpow_nonneg h_base_nonneg _
        simpa [B, hB] using h_rpow_nonneg
      have h_toReal_ofReal :
          (eLpNorm g 2 volume).toReal
            = (ENNReal.ofReal B).toReal := by
        simpa [B, hB] using h₁
      have h_toReal : (eLpNorm g 2 volume).toReal = B := by
        simpa [ENNReal.toReal_ofReal, hB_nonneg] using h_toReal_ofReal
      have hB_simpl :
          B = (∫ τ : ℝ, ‖g τ‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
        simp [B, hB, h_two, one_div]
      have h_nonneg : 0 ≤ ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂volume := by
        simpa [h_two, pow_two] using h_base_nonneg
      have h_sq' :
          ((∫ τ : ℝ, ‖g τ‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^ 2
            = ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂volume := by
        have := Real.mul_self_sqrt h_nonneg
        simpa [pow_two, Real.sqrt_eq_rpow, one_div] using this
      calc
        (eLpNorm g 2 volume).toReal ^ 2
            = (B) ^ 2 := by simp [h_toReal]
        _ = ((∫ τ : ℝ, ‖g τ‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^ 2 := by
              simp [hB_simpl]
        _ = ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂volume := h_sq'
    -- Conclude by combining the two equalities
    calc
      ((eLpNorm g 2 (volume : Measure ℝ)).toReal) ^ 2
          = ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂volume := h_norm_sq
      _ = ‖f‖ ^ 2 := h_pl
  -- Conclude: ‖f‖² = ‖toLp g‖²
  calc
    ‖f‖ ^ 2 = ((eLpNorm g 2 (volume : Measure ℝ)).toReal) ^ 2 := by simpa using h_eLp_sq.symm
    _ = ‖MemLp.toLp g hg_mem‖ ^ 2 := by simp

/-- Forward Plancherel isometry `Uσ` as a linear isometry into `L²(ℝ)`.
It sends `f ∈ Hσ` to its logarithmic pullback `(LogPull σ f)` represented in `Lp`.
This isolates the first leg of the Mellin–Fourier equivalence. -/
noncomputable def Uσ_linIso (σ : ℝ) : Hσ σ →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  { toLinearMap :=
      { toFun := fun f => (mellin_in_L2 σ f).toLp (LogPull σ f)
        map_add' := by
          intro f g; simpa using logPull_toLp_add σ f g
        map_smul' := by
          intro c f; simpa using logPull_map_smul σ c f }
    norm_map' := by
      intro f
      simpa using (logPull_toLp_norm_eq (σ := σ) (h := f)) }

/-!
# Construction of L² Fourier Transform

This section implements the L² Fourier transform as a unitary operator on L²(ℝ)
via the following three steps:

## Step 1: Fourier transform on L¹ ∩ L²
- Define fourierL1L2_toLp: maps integrable L² functions to their Fourier transforms
- Prove it's an isometry using fourier_plancherel_L1_L2

## Step 2: Extension to all of L²
- Show L¹ ∩ L² is dense in L² (l1_inter_l2_dense)
- Extend by continuity to get fourierL2_isometry on all of L²

## Step 3: Bijectivity via inverse transform
- Construct inverse Fourier transform similarly
- Prove left and right inverse properties (Fourier inversion formula)
- Build fourierL2_linearIsometryEquiv as a LinearIsometryEquiv

The final result is FourierL2_equiv, the Plancherel unitary operator.
-/

/-- Step 1: Fourier transform on L¹ ∩ L² as an L² element.
For g that is both integrable and in L², the Fourier transform fourierIntegral g
is also in L² by Plancherel, so we can represent it as an Lp element. -/
noncomputable def fourierL1L2_toLp (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    Lp ℂ 2 (volume : Measure ℝ) := by
  -- The Fourier transform of g is in L² by Plancherel
  have hFg_L2 : MemLp (fun ξ => fourierIntegral g ξ) 2 volume :=
    fourierIntegral_memLp_L1_L2 hg_L1 hg_L2
  exact hFg_L2.toLp (fun ξ => fourierIntegral g ξ)

/-- Step 1: The Fourier map on L¹ ∩ L² is an isometry (preserves norms). -/
lemma fourierL1L2_isometry (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    ‖fourierL1L2_toLp g hg_L1 hg_L2‖ = ‖hg_L2.toLp g‖ := by
  -- This follows directly from fourier_plancherel_L1_L2
  have h_plancherel := fourier_plancherel_L1_L2 g hg_L1 hg_L2
  -- ‖toLp f‖² = ∫ ‖f‖² for both sides
  -- From Plancherel: ∫ ‖g‖² = ∫ ‖fourierIntegral g‖²
  classical
  -- Express both norms via eLpNorm and integrals for p = 2
  have hF_mem : MemLp (fun ξ => fourierIntegral g ξ) 2 volume :=
    fourierIntegral_memLp_L1_L2 hg_L1 hg_L2
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
  -- For the Fourier side
  have hF_eLp_eq :
      (eLpNorm (fun ξ => fourierIntegral g ξ) 2 volume).toReal
        = (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    -- Start from the general formula for eLpNorm at p = 2
    have h₁ :=
      congrArg ENNReal.toReal
        (MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
          (f := fun ξ => fourierIntegral g ξ) hp0 hp_top hF_mem)
    set B : ℝ :=
        (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
          ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ with hB
    have h_two : ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) := by simp
    have h_base_nonneg :
        0 ≤ ∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume := by
      refine integral_nonneg ?_
      intro ξ; simpa [h_two, pow_two] using sq_nonneg ‖fourierIntegral g ξ‖
    have hB_nonneg : 0 ≤ B := by
      have h_rpow_nonneg :
          0 ≤
              (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
                ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ :=
        Real.rpow_nonneg h_base_nonneg _
      simpa [B, hB] using h_rpow_nonneg
    have h_toReal_ofReal :
        (eLpNorm (fun ξ => fourierIntegral g ξ) 2 volume).toReal
          = (ENNReal.ofReal B).toReal := by
      simpa [B, hB] using h₁
    have h_toReal :
        (eLpNorm (fun ξ => fourierIntegral g ξ) 2 volume).toReal = B := by
      simpa [ENNReal.toReal_ofReal, hB_nonneg] using h_toReal_ofReal
    have hB_simpl :
        B = (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
      simp [B, hB, h_two, one_div]
    simp [h_toReal, hB_simpl]
  -- For the time side
  have hG_eLp_eq :
      (eLpNorm g 2 volume).toReal
        = (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    have h₁ :=
      congrArg ENNReal.toReal
        (MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
          (f := g) hp0 hp_top hg_L2)
    set B : ℝ :=
        (∫ t : ℝ, ‖g t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
          ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ with hB
    have h_two : ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) := by simp
    have h_base_nonneg :
        0 ≤ ∫ t : ℝ, ‖g t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume := by
      refine integral_nonneg ?_
      intro t; simpa [h_two, pow_two] using sq_nonneg ‖g t‖
    have hB_nonneg : 0 ≤ B := by
      have h_rpow_nonneg :
          0 ≤
              (∫ t : ℝ, ‖g t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂volume)
                ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ :=
        Real.rpow_nonneg h_base_nonneg _
      simpa [B, hB] using h_rpow_nonneg
    have h_toReal_ofReal : (eLpNorm g 2 volume).toReal = (ENNReal.ofReal B).toReal := by
      simpa [B, hB] using h₁
    have h_toReal : (eLpNorm g 2 volume).toReal = B := by
      simpa [ENNReal.toReal_ofReal, hB_nonneg] using h_toReal_ofReal
    have hB_simpl : B = (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
      simp [B, hB, h_two, one_div]
    simp [h_toReal, hB_simpl]
  -- Conclude: rewrite both norms and use Plancherel
  have h_left :
      ‖fourierL1L2_toLp g hg_L1 hg_L2‖
        = (∫ ξ : ℝ, ‖fourierIntegral g ξ‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    -- unfold and apply norm_toLp
    simp [fourierL1L2_toLp, Lp.norm_toLp, hF_eLp_eq]
  have h_right : ‖hg_L2.toLp g‖ = (∫ t : ℝ, ‖g t‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    simp [Lp.norm_toLp, hG_eLp_eq]
  -- Apply Plancherel to identify the integrals
  simp [h_left, h_right, h_plancherel, one_div]

/-- Step 2: L¹ ∩ L² is dense in L².
This is a standard result: integrable functions with compact support (which are in L¹ ∩ L²)
are dense in L². -/
lemma l1_inter_l2_dense :
    Dense {f : Lp ℂ 2 (volume : Measure ℝ) |
           ∃ (g : ℝ → ℂ) (_ : Integrable g) (hg_L2 : MemLp g 2 volume),
           f = hg_L2.toLp g} := by
  classical
  -- Let `S` be the set of `Lp` elements arising from L¹ ∩ L² representatives.
  set S : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
    {f : Lp ℂ 2 (volume : Measure ℝ) |
      ∃ (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume),
        f = hg_L2.toLp g} with hS_def
  -- Schwartz functions embed into `S` since they are both integrable and L².
  have h_range_subset_S :
      Set.range
          (fun φ : SchwartzMap ℝ ℂ =>
            (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
              (fun t : ℝ => φ t))
        ⊆ S := by
    intro f hf
    rcases hf with ⟨φ, rfl⟩
    refine ⟨(fun t : ℝ => φ t), schwartz_integrable φ,
      (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)), rfl⟩
  -- The range of Schwartz functions is dense in L²(ℝ) as `Lp`.
  have h_dense_range := denseRange_schwartz_toLp_L2
  have h_closure_univ :
      closure
          (Set.range
            (fun φ : SchwartzMap ℝ ℂ =>
              (SchwartzMap.memLp φ (p := (2 : ℝ≥0∞)) (μ := volume)).toLp
                (fun t : ℝ => φ t)))
        = Set.univ :=
    (denseRange_iff_closure_range).1 h_dense_range
  -- Monotonicity of closure gives `Set.univ ⊆ closure S`.
  have h_univ_subset :
      (Set.univ : Set (Lp ℂ 2 (volume : Measure ℝ))) ⊆ closure S := by
    have := closure_mono h_range_subset_S
    simpa [h_closure_univ, hS_def] using this
  -- Conclude `closure S = univ`, hence `S` is dense.
  have h_closure_eq_univ : closure S = (Set.univ : Set (Lp ℂ 2 (volume : Measure ℝ))) := by
    apply le_antisymm
    · intro x _; trivial
    · exact h_univ_subset
  -- Turn the closure equality into `Dense S` using `Dense s ↔ closure s = univ`.
  simpa [hS_def] using (dense_iff_closure_eq.2 h_closure_eq_univ)

-- The subset of L² consisting of equivalence classes represented by L¹ ∩ L² functions.
def L1L2Set : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  {f : Lp ℂ 2 (volume : Measure ℝ) |
    ∃ (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume),
      f = hg_L2.toLp g}

-- This set is dense in L² (wrapper of `l1_inter_l2_dense`).
lemma L1L2Set_dense :
    Dense (L1L2Set) := by
  -- Signature only; the proof is `by simpa [L1L2Set] using l1_inter_l2_dense`.
  simpa [L1L2Set] using l1_inter_l2_dense

-- Zero belongs to the set (represented by the zero function).
lemma L1L2Set_zero_mem :
    (0 : Lp ℂ 2 (volume : Measure ℝ)) ∈ L1L2Set := by
  refine ⟨(fun _ : ℝ => (0 : ℂ)), by simp,
    (MemLp.zero : MemLp (fun _ : ℝ => (0 : ℂ)) 2 volume), ?_⟩
  rfl

-- Closed under addition: if f,g come from L¹ ∩ L², then so does f+g.
lemma L1L2Set_add_mem {f g : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : f ∈ L1L2Set) (hg : g ∈ L1L2Set) : f + g ∈ L1L2Set := by
  classical
  rcases hf with ⟨g₁, hg₁_L1, hg₁_L2, rfl⟩
  rcases hg with ⟨g₂, hg₂_L1, hg₂_L2, rfl⟩
  refine ⟨(fun t : ℝ => g₁ t + g₂ t), hg₁_L1.add hg₂_L1, hg₁_L2.add hg₂_L2, ?_⟩
  -- Show equality in Lp by a.e. equality of representatives
  apply Lp.ext (μ := (volume : Measure ℝ))
  have h₁ := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hg₁_L2
  have h₂ := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hg₂_L2
  have hsum := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) (hg₁_L2.add hg₂_L2)
  calc
    ((MemLp.toLp (fun t : ℝ => g₁ t + g₂ t) (hg₁_L2.add hg₂_L2)) :
        Lp ℂ 2 (volume : Measure ℝ))
        =ᵐ[volume] (fun t : ℝ => g₁ t + g₂ t) := hsum
    _ =ᵐ[volume]
        (MemLp.toLp g₁ hg₁_L2 : Lp ℂ 2 (volume : Measure ℝ))
        + (MemLp.toLp g₂ hg₂_L2 : Lp ℂ 2 (volume : Measure ℝ)) := (h₁.add h₂).symm
    _ =ᵐ[volume]
        ((MemLp.toLp g₁ hg₁_L2 + MemLp.toLp g₂ hg₂_L2 :
          Lp ℂ 2 (volume : Measure ℝ))) := (Lp.coeFn_add _ _).symm

-- Closed under scalar multiplication.
lemma L1L2Set_smul_mem (c : ℂ) {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : f ∈ L1L2Set) : c • f ∈ L1L2Set := by
  classical
  rcases hf with ⟨g, hg_L1, hg_L2, rfl⟩
  refine ⟨(fun t : ℝ => c • g t), hg_L1.smul c, hg_L2.const_smul c, ?_⟩
  -- Show equality in Lp by a.e. equality of representatives
  rfl

-- Well-definedness w.r.t. almost-everywhere equality of representatives.
lemma fourierL1L2_toLp_congr_ae (g h : ℝ → ℂ)
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume)
    (hh_L1 : Integrable h) (hh_L2 : MemLp h 2 volume)
    (h_ae : g =ᵐ[volume] h) :
    fourierL1L2_toLp g hg_L1 hg_L2 = fourierL1L2_toLp h hh_L1 hh_L2 := by
  classical
  -- Compare the `Lp` classes via `toLp_eq_toLp_iff` and show a.e. equality
  -- of the representing Fourier transforms as functions of the frequency.
  refine
    (MemLp.toLp_eq_toLp_iff
        (fourierIntegral_memLp_L1_L2 hg_L1 hg_L2)
        (fourierIntegral_memLp_L1_L2 hh_L1 hh_L2)).mpr ?_;
  -- For every frequency ξ, the Fourier integrals coincide since the integrands
  -- are a.e. equal in t by `h_ae`.
  refine ae_of_all _ (fun ξ => ?_)
  have hmul :
      (fun t : ℝ => fourierKernel ξ t * g t)
        =ᵐ[volume]
      (fun t : ℝ => fourierKernel ξ t * h t) :=
    h_ae.mono (by
      intro t ht
      simp [ht])
  simpa [fourierL1L2_toLp, fourierIntegral]
    using (MeasureTheory.integral_congr_ae hmul)

-- Additivity of the L¹ ∩ L² Fourier map at the Lp level.
lemma fourierL1L2_toLp_add (g h : ℝ → ℂ)
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume)
    (hh_L1 : Integrable h) (hh_L2 : MemLp h 2 volume) :
    fourierL1L2_toLp (fun t => g t + h t)
      (hg_L1.add hh_L1) (hg_L2.add hh_L2)
    = fourierL1L2_toLp g hg_L1 hg_L2
      + fourierL1L2_toLp h hh_L1 hh_L2 := by
  classical
  -- Unfold definitions and compare representatives a.e.
  apply Lp.ext (μ := (volume : Measure ℝ))
  -- MemLp witnesses for coeFn_toLp
  set FsumMem := fourierIntegral_memLp_L1_L2 (hg_L1.add hh_L1) (hg_L2.add hh_L2)
  set FgMem := fourierIntegral_memLp_L1_L2 hg_L1 hg_L2
  set FhMem := fourierIntegral_memLp_L1_L2 hh_L1 hh_L2
  have h_sum := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) FsumMem
  have hg_coe := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) FgMem
  have hh_coe := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) FhMem
  -- Assemble the a.e. equality chain
  calc
    ((MemLp.toLp (fun ξ : ℝ => fourierIntegral (fun t => g t + h t) ξ) FsumMem) :
        Lp ℂ 2 (volume : Measure ℝ))
        =ᵐ[volume] (fun ξ : ℝ => fourierIntegral (fun t => g t + h t) ξ) := h_sum
    _ =ᵐ[volume]
        (fun ξ : ℝ => fourierIntegral g ξ + fourierIntegral h ξ) :=
          ae_of_all _ (fun ξ => by simpa using fourierIntegral_add (hf := hg_L1) (hg := hh_L1) ξ)
    _ =ᵐ[volume]
        ((MemLp.toLp (fun ξ => fourierIntegral g ξ) FgMem : Lp ℂ 2 (volume : Measure ℝ))
          + (MemLp.toLp (fun ξ => fourierIntegral h ξ) FhMem : Lp ℂ 2 (volume : Measure ℝ))) :=
          (hg_coe.add hh_coe).symm
    _ =ᵐ[volume]
        (fun ξ : ℝ => (((MemLp.toLp (fun ξ => fourierIntegral g ξ) FgMem :
            Lp ℂ 2 (volume : Measure ℝ))
          + (MemLp.toLp (fun ξ => fourierIntegral h ξ) FhMem :
            Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ) := by
          -- Convert sum of coeFns to the coeFn of the sum
          have hx :=
            (Lp.coeFn_add (μ := (volume : Measure ℝ))
              (MemLp.toLp (fun ξ => fourierIntegral g ξ) FgMem)
              (MemLp.toLp (fun ξ => fourierIntegral h ξ) FhMem)).symm
          -- Adjust shape to an explicit lambda
          exact hx.mono (by intro ξ hξ; simp)
    _ =ᵐ[volume]
        (fun ξ : ℝ => (((fourierL1L2_toLp g hg_L1 hg_L2)
            + (fourierL1L2_toLp h hh_L1 hh_L2)) : ℝ → ℂ) ξ) := by
          simp [fourierL1L2_toLp]
    _ =ᵐ[volume]
        (↑↑((fourierL1L2_toLp g hg_L1 hg_L2)
          + (fourierL1L2_toLp h hh_L1 hh_L2)) : ℝ → ℂ) := by
          simpa using
            (Lp.coeFn_add (μ := (volume : Measure ℝ))
              (fourierL1L2_toLp g hg_L1 hg_L2)
              (fourierL1L2_toLp h hh_L1 hh_L2)).symm

-- Scalar multiplication compatibility of the L¹ ∩ L² Fourier map at the Lp level.
lemma fourierL1L2_toLp_smul (c : ℂ) (g : ℝ → ℂ)
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    fourierL1L2_toLp (fun t => c • g t)
      (hg_L1.smul c) (hg_L2.const_smul c)
    = c • fourierL1L2_toLp g hg_L1 hg_L2 := by
  classical
  -- Compare representatives a.e. and use `Lp.ext`.
  apply Lp.ext (μ := (volume : Measure ℝ))
  -- MemLp witnesses for coeFn_toLp
  set FcMem :=
    fourierIntegral_memLp_L1_L2 (hg_L1.smul c) (hg_L2.const_smul c)
  set FgMem := fourierIntegral_memLp_L1_L2 hg_L1 hg_L2
  have hc_coe := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) FcMem
  have hg_coe := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) FgMem
  have hcoe_smul :=
    (Lp.coeFn_smul (μ := (volume : Measure ℝ)) c
      (MemLp.toLp (fun ξ => fourierIntegral g ξ) FgMem)).symm
  -- Assemble the a.e. equality chain
  calc
    ((MemLp.toLp (fun ξ : ℝ => fourierIntegral (fun t => c • g t) ξ) FcMem) :
        Lp ℂ 2 (volume : Measure ℝ))
        =ᵐ[volume] (fun ξ : ℝ => fourierIntegral (fun t => c • g t) ξ) := hc_coe
    _ =ᵐ[volume]
        (fun ξ : ℝ => c * fourierIntegral g ξ) :=
          ae_of_all _ (fun ξ => by
            simpa [Circle.smul_def] using fourierIntegral_smul c hg_L1 ξ)
    _ =ᵐ[volume]
        (fun ξ : ℝ => c * (((MemLp.toLp (fun ξ => fourierIntegral g ξ) FgMem :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ)) :=
          hg_coe.mono (by intro ξ hξ; simp [hξ])
    _ =ᵐ[volume]
        (fun ξ : ℝ => c • (((MemLp.toLp (fun ξ => fourierIntegral g ξ) FgMem :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ)) :=
          ae_of_all _ (fun _ => by simp [Circle.smul_def])
    _ =ᵐ[volume]
        (fun ξ : ℝ => ((c • (MemLp.toLp (fun ξ => fourierIntegral g ξ) FgMem :
            Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ) := by
          simp
    _ =ᵐ[volume]
        (fun ξ : ℝ => ((c • (fourierL1L2_toLp g hg_L1 hg_L2)) : ℝ → ℂ) ξ) := by
          -- Unfold the declaration of `fourierL1L2_toLp`
          simp [fourierL1L2_toLp]
    _ =ᵐ[volume]
        (↑↑(c • fourierL1L2_toLp g hg_L1 hg_L2) : ℝ → ℂ) := by
          simpa using
            (Lp.coeFn_smul (μ := (volume : Measure ℝ))
              c (fourierL1L2_toLp g hg_L1 hg_L2)).symm

-- Package the set as a submodule to inherit algebraic structure on the domain.
noncomputable def L1L2Submodule :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  { carrier := L1L2Set
  , zero_mem' := by simpa using L1L2Set_zero_mem
  , add_mem' := by
      intro a b ha hb; exact L1L2Set_add_mem ha hb
  , smul_mem' := by
      intro c x hx; exact L1L2Set_smul_mem c hx }

-- Construct a linear map on the submodule induced by `fourierL1L2_toLp`.
noncomputable def T0_on_L1L2 :
    L1L2Submodule →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  classical
  refine
    { toFun := ?toFun
    , map_add' := ?map_add
    , map_smul' := ?map_smul };
  · -- definition on generators: pick a representative noncomputably via choice
    -- Avoid eliminating an `∃` into data by using `Classical.choose`.
    intro f
    -- Convert membership of the submodule into the existential defining L1L2Set
    have hmemf : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
      simp [L1L2Submodule]
    -- hmemf : ∃ g, Integrable g ∧ MemLp g 2 ∧ f = toLp g
    let g : ℝ → ℂ := Classical.choose hmemf
    let ex1 := Classical.choose_spec hmemf
    let hg_L1 : Integrable g := Classical.choose ex1
    let ex2 := Classical.choose_spec ex1
    let hg_L2 : MemLp g 2 (volume : Measure ℝ) := Classical.choose ex2
    -- let hf : (f : Lp ℂ 2 (volume : Measure ℝ)) = hg_L2.toLp g := Classical.choose_spec ex2
    exact fourierL1L2_toLp g hg_L1 hg_L2
  · -- additivity
    intro f g
    rcases f.property with ⟨g₁, hg₁_L1, hg₁_L2, hf⟩
    rcases g.property with ⟨g₂, hg₂_L1, hg₂_L2, hg⟩
    -- Unfold the definition on f, g, and f+g
    -- Chosen representative for f + g
    -- Repackage membership proofs needed for add_mem
    have hf_mem : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set :=
      ⟨g₁, hg₁_L1, hg₁_L2, hf⟩
    have hg_mem : ((g : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set :=
      ⟨g₂, hg₂_L1, hg₂_L2, hg⟩
    have h_sum_rep : ((f + g : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ)) ∈ L1L2Set :=
      (L1L2Set_add_mem hf_mem hg_mem)
    rcases h_sum_rep with ⟨gs, hs_L1, hs_L2, hfg_eq⟩
    -- Show the chosen rep gs agrees a.e. with g₁+g₂, by comparing two toLp representations
    have h_sum_toLp_eq :
        (hs_L2.toLp gs : Lp ℂ 2 (volume : Measure ℝ))
          = (hg₁_L2.toLp g₁ + hg₂_L2.toLp g₂) := by
      -- From hfg_eq and hf, hg
      -- First, identify (hg₁+hg₂).toLp (g₁+g₂) with the sum of toLp's
      have h_canon :
          ((hg₁_L2.add hg₂_L2).toLp (fun t : ℝ => g₁ t + g₂ t)
            : Lp ℂ 2 (volume : Measure ℝ))
            = (hg₁_L2.toLp g₁ + hg₂_L2.toLp g₂) := by
        -- This is exactly the equality proved in L1L2Set_add_mem's calc
        -- We re-establish it here via a.e. equality of coeFns
        apply Lp.ext (μ := (volume : Measure ℝ))
        have h₁ := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hg₁_L2
        have h₂ := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hg₂_L2
        have hsum := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) (hg₁_L2.add hg₂_L2)
        calc
          ((MemLp.toLp (fun t : ℝ => g₁ t + g₂ t) (hg₁_L2.add hg₂_L2)) :
              Lp ℂ 2 (volume : Measure ℝ))
              =ᵐ[volume] (fun t : ℝ => g₁ t + g₂ t) := hsum
          _ =ᵐ[volume]
              (MemLp.toLp g₁ hg₁_L2 : Lp ℂ 2 (volume : Measure ℝ))
                + (MemLp.toLp g₂ hg₂_L2 : Lp ℂ 2 (volume : Measure ℝ)) := (h₁.add h₂).symm
          _ =ᵐ[volume]
              ((MemLp.toLp g₁ hg₁_L2 + MemLp.toLp g₂ hg₂_L2 :
                Lp ℂ 2 (volume : Measure ℝ))) := (Lp.coeFn_add _ _).symm
      -- Now compare with the chosen representation for f+g, using hfg_eq and hf, hg
      -- From hf, hg: f = toLp g₁, g = toLp g₂
      have hfg_sum :
          (hg₁_L2.toLp g₁ + hg₂_L2.toLp g₂ : Lp ℂ 2 (volume : Measure ℝ))
            = ((f + g : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ)) := by
        -- equality in the subtype coerces to equality in the ambient Lp
        -- but we only need equality in Lp
        -- Coe out of the subtype
        have : ((f + g : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ))
            = (f : Lp ℂ 2 (volume : Measure ℝ)) + (g : Lp ℂ 2 (volume : Measure ℝ)) := rfl
        rw [this, hf, hg]
      -- Meanwhile, hfg_eq: ↑(f + g) = (hs_L2.toLp gs)
      -- Combine to eliminate (f+g)
      rw [← hfg_eq, hfg_sum]
    -- From equality of toLp, deduce a.e. equality of the functions
    have hgs_ae : (fun t => gs t) =ᵐ[volume] (fun t => g₁ t + g₂ t) := by
      -- Use toLp_eq_toLp_iff with the two MemLp witnesses
      exact (MemLp.toLp_eq_toLp_iff hs_L2 (hg₁_L2.add hg₂_L2)).1 h_sum_toLp_eq
    -- Now apply the additivity lemma and the congruence on a.e.-equal reps
    -- Left side: T0_on_L1L2 (f + g)
    -- equals fourierL1L2_toLp gs ...; replace by g₁+g₂
    have h_left :
        fourierL1L2_toLp gs hs_L1 hs_L2
          = fourierL1L2_toLp (fun t => g₁ t + g₂ t)
              (hg₁_L1.add hg₂_L1) (hg₁_L2.add hg₂_L2) :=
      fourierL1L2_toLp_congr_ae gs (fun t => g₁ t + g₂ t)
        hs_L1 hs_L2 (hg₁_L1.add hg₂_L1) (hg₁_L2.add hg₂_L2) hgs_ae
    -- Bridge: identify T0_on_L1L2 (f + g) with the chosen rep `gs` via choice
    -- Choice witnesses for (f + g) through membership in L1L2Set
    have hmem_fg : ((f + g : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
      simpa [L1L2Submodule] using (f + g).property
    let gch : ℝ → ℂ := Classical.choose hmem_fg
    let ex1c := Classical.choose_spec hmem_fg
    let hL1c : Integrable gch := Classical.choose ex1c
    let ex2c := Classical.choose_spec ex1c
    let hL2c : MemLp gch 2 (volume : Measure ℝ) := Classical.choose ex2c
    have hfg_eq_choice : ((f + g : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ))
        = hL2c.toLp gch := by
      -- rewrite (f+g).property to L1L2Set membership to access choose_spec
      exact Classical.choose_spec ex2c
    -- A.e. equality between the two chosen reps for f+g
    have h_ae_sum : (fun t => gs t) =ᵐ[volume] gch := by
      have : (hs_L2.toLp gs : Lp ℂ 2 (volume : Measure ℝ)) = hL2c.toLp gch := by
        -- both sides equal the same element (f + g)
        exact (hfg_eq.symm.trans hfg_eq_choice)
      exact (MemLp.toLp_eq_toLp_iff hs_L2 hL2c).1 this
    -- Convert this into equality of Fourier Lp images using congr_ae
    have h_sum_congr :
        fourierL1L2_toLp gs hs_L1 hs_L2
          = fourierL1L2_toLp gch hL1c hL2c :=
      fourierL1L2_toLp_congr_ae gs gch hs_L1 hs_L2 hL1c hL2c h_ae_sum
    -- Similarly bridge for f and g individually to align with T0_on_L1L2 definitions
    -- Choice witnesses for f
    have hmem_f : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
      simp [L1L2Submodule]
    let gf : ℝ → ℂ := Classical.choose hmem_f
    let ex1f := Classical.choose_spec hmem_f
    let hL1f : Integrable gf := Classical.choose ex1f
    let ex2f := Classical.choose_spec ex1f
    let hL2f : MemLp gf 2 (volume : Measure ℝ) := Classical.choose ex2f
    have hf_choice : ((f : Lp ℂ 2 (volume : Measure ℝ))) = hL2f.toLp gf :=
      Classical.choose_spec ex2f
    have h_ae_f : (fun t => gf t) =ᵐ[volume] g₁ := by
      have : (hL2f.toLp gf : Lp ℂ 2 (volume : Measure ℝ)) = hg₁_L2.toLp g₁ := by
        rw [← hf_choice, hf]
      exact (MemLp.toLp_eq_toLp_iff hL2f hg₁_L2).1 this
    have h_f_congr :
        fourierL1L2_toLp gf hL1f hL2f
          = fourierL1L2_toLp g₁ hg₁_L1 hg₁_L2 :=
      fourierL1L2_toLp_congr_ae gf g₁ hL1f hL2f hg₁_L1 hg₁_L2 h_ae_f
    -- Choice witnesses for g
    have hmem_g : ((g : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
      simp [L1L2Submodule]
    let gg : ℝ → ℂ := Classical.choose hmem_g
    let ex1g := Classical.choose_spec hmem_g
    let hL1g : Integrable gg := Classical.choose ex1g
    let ex2g := Classical.choose_spec ex1g
    let hL2g : MemLp gg 2 (volume : Measure ℝ) := Classical.choose ex2g
    have hg_choice : ((g : Lp ℂ 2 (volume : Measure ℝ))) = hL2g.toLp gg :=
      Classical.choose_spec ex2g
    have h_ae_g : (fun t => gg t) =ᵐ[volume] g₂ := by
      have : (hL2g.toLp gg : Lp ℂ 2 (volume : Measure ℝ)) = hg₂_L2.toLp g₂ := by
        rw [← hg_choice, hg]
      exact (MemLp.toLp_eq_toLp_iff hL2g hg₂_L2).1 this
    have h_g_congr :
        fourierL1L2_toLp gg hL1g hL2g
          = fourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 :=
      fourierL1L2_toLp_congr_ae gg g₂ hL1g hL2g hg₂_L1 hg₂_L2 h_ae_g
    -- Now assemble all pieces, rewriting both sides to the `choose`-based definitions
    -- of T0_on_L1L2 and then applying additivity on representatives
    have h_gch_eq :
        fourierL1L2_toLp gch hL1c hL2c
          = fourierL1L2_toLp g₁ hg₁_L1 hg₁_L2
            + fourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 := by
      -- start from gs, go to sum, then additivity
      calc fourierL1L2_toLp gch hL1c hL2c
          = fourierL1L2_toLp gs hs_L1 hs_L2 := h_sum_congr.symm
        _ = fourierL1L2_toLp (fun t => g₁ t + g₂ t)
            (hg₁_L1.add hg₂_L1) (hg₁_L2.add hg₂_L2) := h_left
        _ = fourierL1L2_toLp g₁ hg₁_L1 hg₁_L2 + fourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 :=
              fourierL1L2_toLp_add g₁ g₂ hg₁_L1 hg₁_L2 hg₂_L1 hg₂_L2
    calc
      fourierL1L2_toLp gch hL1c hL2c
          = fourierL1L2_toLp g₁ hg₁_L1 hg₁_L2
            + fourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 := h_gch_eq
      _ = fourierL1L2_toLp gf hL1f hL2f
            + fourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 := by simp [h_f_congr]
      _ = fourierL1L2_toLp gf hL1f hL2f
            + fourierL1L2_toLp gg hL1g hL2g := by simp [h_g_congr]
  · -- scalar multiplication
    intro c f
    rcases f.property with ⟨g, hg_L1, hg_L2, hf⟩
    -- Representative for c • f
    have hf_mem : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set :=
      ⟨g, hg_L1, hg_L2, hf⟩
    have h_smul_rep : ((c • f : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ)) ∈ L1L2Set :=
      L1L2Set_smul_mem c hf_mem
    rcases h_smul_rep with ⟨gs, hs_L1, hs_L2, hcf_eq⟩
    -- Show chosen rep gs agrees a.e. with c • g
    have hcf_toLp_eq :
        (hs_L2.toLp gs : Lp ℂ 2 (volume : Measure ℝ))
          = (c • hg_L2.toLp g) := by
      -- From the construction in L1L2Set_smul_mem (proved via Lp.ext)
      -- and hf
      rw [← hf]
      exact hcf_eq.symm
    have hgs_ae : (fun t => gs t) =ᵐ[volume] (fun t => c • g t) := by
      exact (MemLp.toLp_eq_toLp_iff hs_L2 (hg_L2.const_smul c)).1 hcf_toLp_eq
    -- Replace the left with the canonical rep (c • g), then use smul lemma
    have h_left :
        fourierL1L2_toLp gs hs_L1 hs_L2
          = fourierL1L2_toLp (fun t => c • g t)
              (hg_L1.smul c) (hg_L2.const_smul c) :=
      fourierL1L2_toLp_congr_ae gs (fun t => c • g t)
        hs_L1 hs_L2 (hg_L1.smul c) (hg_L2.const_smul c) hgs_ae
    -- Bridge for (c • f) with the `choose` witnesses of its property
    have hmem_cf : (((c • f : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
      simpa [L1L2Submodule] using (c • f).property
    let gch : ℝ → ℂ := Classical.choose hmem_cf
    let ex1c := Classical.choose_spec hmem_cf
    let hL1c : Integrable gch := Classical.choose ex1c
    let ex2c := Classical.choose_spec ex1c
    let hL2c : MemLp gch 2 (volume : Measure ℝ) := Classical.choose ex2c
    have hcf_eq_choice : ((c • f : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ))
        = hL2c.toLp gch := by
      exact Classical.choose_spec ex2c
    have h_ae_cf : (fun t => gs t) =ᵐ[volume] gch := by
      have : (hs_L2.toLp gs : Lp ℂ 2 (volume : Measure ℝ)) = hL2c.toLp gch := by
        exact (hcf_eq.symm.trans hcf_eq_choice)
      exact (MemLp.toLp_eq_toLp_iff hs_L2 hL2c).1 this
    have h_cf_congr :
        fourierL1L2_toLp gs hs_L1 hs_L2
          = fourierL1L2_toLp gch hL1c hL2c :=
      fourierL1L2_toLp_congr_ae gs gch hs_L1 hs_L2 hL1c hL2c h_ae_cf
    -- Choice witnesses for f itself
    have hmem_f : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
      simp [L1L2Submodule]
    let gf : ℝ → ℂ := Classical.choose hmem_f
    let ex1f := Classical.choose_spec hmem_f
    let hL1f : Integrable gf := Classical.choose ex1f
    let ex2f := Classical.choose_spec ex1f
    let hL2f : MemLp gf 2 (volume : Measure ℝ) := Classical.choose ex2f
    have hf_choice : ((f : Lp ℂ 2 (volume : Measure ℝ))) = hL2f.toLp gf :=
      Classical.choose_spec ex2f
    have h_ae_f : (fun t => gf t) =ᵐ[volume] g := by
      have : (hL2f.toLp gf : Lp ℂ 2 (volume : Measure ℝ)) = hg_L2.toLp g := by
        rw [← hf_choice, hf]
      exact (MemLp.toLp_eq_toLp_iff hL2f hg_L2).1 this
    have h_f_congr :
        fourierL1L2_toLp gf hL1f hL2f
          = fourierL1L2_toLp g hg_L1 hg_L2 :=
      fourierL1L2_toLp_congr_ae gf g hL1f hL2f hg_L1 hg_L2 h_ae_f
    -- Now assemble smul equality
    have h_gch_eq : fourierL1L2_toLp gch hL1c hL2c
        = c • fourierL1L2_toLp g hg_L1 hg_L2 := by
      calc fourierL1L2_toLp gch hL1c hL2c
          = fourierL1L2_toLp gs hs_L1 hs_L2 := h_cf_congr.symm
        _ = fourierL1L2_toLp (fun t => c • g t) (hg_L1.smul c) (hg_L2.const_smul c) := h_left
        _ = c • fourierL1L2_toLp g hg_L1 hg_L2 := fourierL1L2_toLp_smul c g hg_L1 hg_L2
    -- The final equality uses the same approach as map_add
    calc
      fourierL1L2_toLp gch hL1c hL2c
          = c • fourierL1L2_toLp g hg_L1 hg_L2 := h_gch_eq
      _ = c • fourierL1L2_toLp gf hL1f hL2f := by simp [h_f_congr]

lemma T0_on_L1L2_isometry
    (f : L1L2Submodule) :
    ‖T0_on_L1L2 f‖ = ‖(f : Lp ℂ 2 (volume : Measure ℝ))‖ := by
  classical
  rcases f.property with ⟨g, hg_L1, hg_L2, hf⟩
  -- Reduce definition of T0_on_L1L2 on this representative
  -- Bridge via the choice witnesses used in `T0_on_L1L2`
  have hmem_f : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
    simp [L1L2Submodule]
  let gf : ℝ → ℂ := Classical.choose hmem_f
  let ex1f := Classical.choose_spec hmem_f
  let hL1f : Integrable gf := Classical.choose ex1f
  let ex2f := Classical.choose_spec ex1f
  let hL2f : MemLp gf 2 (volume : Measure ℝ) := Classical.choose ex2f
  have hf_choice : ((f : Lp ℂ 2 (volume : Measure ℝ))) = hL2f.toLp gf :=
    Classical.choose_spec ex2f
  have h_ae_f : (fun t => gf t) =ᵐ[volume] g := by
    have : (hL2f.toLp gf : Lp ℂ 2 (volume : Measure ℝ)) = hg_L2.toLp g := by
      rw [← hf_choice, hf]
    exact (MemLp.toLp_eq_toLp_iff hL2f hg_L2).1 this
  have hT : T0_on_L1L2 f = fourierL1L2_toLp g hg_L1 hg_L2 := by
    -- unfold to the `choose`-based representative, then switch by a.e. congruence
    have : T0_on_L1L2 f = fourierL1L2_toLp gf hL1f hL2f := rfl
    rw [this, fourierL1L2_toLp_congr_ae gf g hL1f hL2f hg_L1 hg_L2 h_ae_f]
  calc
    ‖T0_on_L1L2 f‖
        = ‖fourierL1L2_toLp g hg_L1 hg_L2‖ := by simp [hT]
    _ = ‖hg_L2.toLp g‖ := fourierL1L2_isometry g hg_L1 hg_L2
    _ = ‖(f : Lp ℂ 2 (volume : Measure ℝ))‖ := by simp [hf]

-- General extension lemma: extend a linear isometry from a dense submodule to all of V.
lemma extend_linear_isometry_of_dense
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (P : Submodule ℂ V) (hP : Dense (P : Set V))
    (T0 : P →ₗ[ℂ] W)
    (hIso : ∀ x : P, ‖T0 x‖ = ‖(x : V)‖) :
    ∃ T : V →L[ℂ] W,
      (∀ x : P, T x = T0 x) ∧ ∀ v : V, ‖T v‖ = ‖v‖ := by
  classical
  -- Bundle `T0` as a linear isometry on the dense submodule.
  let e0 : P →ₗᵢ[ℂ] W :=
    { toLinearMap := T0
      norm_map' := by
        intro x; simpa using hIso x }
  -- Convert density of the carrier set to DenseRange of the inclusion map.
  have hRange_eq : Set.range (fun x : P => (x : V)) = (P : Set V) := by
    ext v; constructor
    · intro h; rcases h with ⟨x, rfl⟩; exact x.property
    · intro hv; exact ⟨⟨v, hv⟩, rfl⟩
  have hDR' : DenseRange (fun x : P => (x : V)) := by
    intro v; simpa [hRange_eq] using hP v
  have hDR : DenseRange (Submodule.subtypeL P : P →L[ℂ] V) := by
    convert hDR'
  -- Extend to a continuous linear map on all of `V` using density and completeness of `W`.
  -- We use `ContinuousLinearMap.extend` along the inclusion `Submodule.subtypeL`.
  have h_ui : IsUniformInducing (Submodule.subtypeL P) := by
    -- The inclusion of a subtype is a uniform embedding.
    simpa [Submodule.coe_subtypeL', Submodule.coe_subtype]
      using (isUniformInducing_val (P : Set V))
  let T : V →L[ℂ] W :=
    ContinuousLinearMap.extend (f := e0.toContinuousLinearMap)
      (e := Submodule.subtypeL P) (h_dense := hDR) (h_e := h_ui)
  refine ⟨T, ?hAgree, ?hIso⟩
  · -- Agreement on the dense submodule
    intro x
    -- `extend` agrees on the range of the embedding.
    -- Here `x : P`, and `Submodule.subtypeL P x = (x : V)`.
    have hx :=
      ContinuousLinearMap.extend_eq (f := e0.toContinuousLinearMap)
        (e := Submodule.subtypeL P) (h_dense := hDR) (h_e := h_ui) x
    -- Rewrite to the statement form.
    simpa [T] using hx
  · -- Isometry on all of V: prove by closedness + density.
    intro v
    -- Define the closed property `p y := ‖T y‖ = ‖y‖`.
    -- Show it holds on the range of the dense embedding, then use density.
    have h_closed : IsClosed {y : V | ‖T y‖ = ‖y‖} :=
      isClosed_eq (T.continuous.norm) continuous_norm
    -- On the range: for `x : P`, it follows from agreement and `hIso`.
    have h_on_range : ∀ x : P, ‖T (x : V)‖ = ‖(x : V)‖ := by
      intro x
      -- Use agreement `T x = T0 x` (from `extend_eq`) and the isometry property of `T0`.
      have hx :=
        ContinuousLinearMap.extend_eq (f := e0.toContinuousLinearMap)
          (e := Submodule.subtypeL P) (h_dense := hDR) (h_e := h_ui) x
      have hx' : T (x : V) = T0 x := by simpa [T] using hx
      calc
        ‖T (x : V)‖ = ‖T0 x‖ := by simp [hx']
        _ = ‖(x : V)‖ := hIso x
    -- Apply density induction.
    have : {y : V | ‖T y‖ = ‖y‖} v :=
      (DenseRange.induction_on hDR v h_closed h_on_range)
    simpa using this

/-- Auxiliary existence with agreement on L¹ ∩ L²: there exists a continuous
linear isometry on L² that agrees with the L¹ ∩ L² Fourier map. -/
lemma exists_fourierL2_isometryCLM_agrees :
    ∃ F : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      (∀ g : Lp ℂ 2 (volume : Measure ℝ), ‖F g‖ = ‖g‖) ∧
      (∀ (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume),
        F (hg_L2.toLp g) = fourierL1L2_toLp g hg_L1 hg_L2) := by
  classical
  -- Extend the linear isometry `T0_on_L1L2` from the dense submodule to all of L².
  have hDense : Dense ((L1L2Submodule : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
      Set (Lp ℂ 2 (volume : Measure ℝ))) := by
    -- By construction, the carrier set of `L1L2Submodule` is `L1L2Set`.
    simpa [L1L2Submodule, L1L2Set]
      using (L1L2Set_dense : Dense L1L2Set)
  obtain ⟨T, hAgree, hNorm⟩ :=
    extend_linear_isometry_of_dense
      (P := L1L2Submodule)
      (hP := hDense)
      (T0 := T0_on_L1L2)
      (hIso := T0_on_L1L2_isometry)
  refine ⟨T, ?hn, ?hag⟩
  · -- Norm preservation on all of L²
    intro g; simpa using hNorm g
  · -- Agreement on L¹ ∩ L² representatives
    intro g hg_L1 hg_L2
    -- Package `hg_L2.toLp g` as an element of the submodule
    have hx_mem : (hg_L2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) ∈ L1L2Set :=
      ⟨g, hg_L1, hg_L2, rfl⟩
    let x : L1L2Submodule := ⟨hg_L2.toLp g, hx_mem⟩
    -- Use the extension agreement property and definition of T0_on_L1L2
    have hx : T x = T0_on_L1L2 x := hAgree x
    -- T0_on_L1L2 x uses Classical.choose on x's membership proof
    -- By construction, the chosen representative will be related to g
    have : T0_on_L1L2 x = fourierL1L2_toLp g hg_L1 hg_L2 := by
      -- The definition of T0_on_L1L2 applied to x
      -- Since x = ⟨hg_L2.toLp g, hx_mem⟩ and hx_mem uses g directly,
      -- the Classical.choose should pick g (or something a.e. equal)
      -- This requires showing the chosen witnesses match
      -- Reproduce the choice made in the definition and switch by a.e. equality
      have hmemx : ((x : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
        simp [L1L2Submodule]
      let gx : ℝ → ℂ := Classical.choose hmemx
      let ex1x := Classical.choose_spec hmemx
      let hL1x : Integrable gx := Classical.choose ex1x
      let ex2x := Classical.choose_spec ex1x
      let hL2x : MemLp gx 2 (volume : Measure ℝ) := Classical.choose ex2x
      have hx_choice : ((x : Lp ℂ 2 (volume : Measure ℝ))) = hL2x.toLp gx :=
        Classical.choose_spec ex2x
      have hx_coe : ((x : Lp ℂ 2 (volume : Measure ℝ))) = hg_L2.toLp g := rfl
      have h_toLp_eq : (hL2x.toLp gx : Lp ℂ 2 (volume : Measure ℝ))
            = hg_L2.toLp g := by
        simpa [hx_coe] using hx_choice.symm
      have h_ae : (fun t => gx t) =ᵐ[volume] g :=
        (MemLp.toLp_eq_toLp_iff hL2x hg_L2).1 h_toLp_eq
      have h_congr :=
        fourierL1L2_toLp_congr_ae gx g hL1x hL2x hg_L1 hg_L2 h_ae
      -- Unfold T0_on_L1L2 at x to the chosen representative `gx`
      have hT : T0_on_L1L2 x = fourierL1L2_toLp gx hL1x hL2x := rfl
      simpa [hT] using h_congr
    rw [← this, ← hx]

noncomputable def fourierL2_isometryCLM_choice :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Classical.choose exists_fourierL2_isometryCLM_agrees

lemma fourierL2_isometryCLM_choice_norm
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖fourierL2_isometryCLM_choice f‖ = ‖f‖ := by
  classical
  have h := Classical.choose_spec exists_fourierL2_isometryCLM_agrees
  exact h.1 f

lemma fourierL2_isometryCLM_choice_agree (g : ℝ → ℂ)
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    fourierL2_isometryCLM_choice (hg_L2.toLp g) =
      fourierL1L2_toLp g hg_L1 hg_L2 := by
  classical
  have h := Classical.choose_spec exists_fourierL2_isometryCLM_agrees
  exact h.2 g hg_L1 hg_L2

/-- Step 2: Extend the Fourier isometry from L¹ ∩ L² to all of L² by continuity.
Given an L² function f, we approximate it by a sequence of L¹ ∩ L² functions,
apply the Fourier transform to each, and take the limit.
The result is a linear isometry on all of L². -/
noncomputable def fourierL2_isometry :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  classical
  -- Use the continuous linear map constructed in `fourierL2_isometryCLM_choice`
  -- and upgrade it to a linear isometry via its norm-preserving property.
  refine
    { toLinearMap := fourierL2_isometryCLM_choice
    , norm_map' := ?_ }
  intro f
  simpa using fourierL2_isometryCLM_choice_norm f

/-- Step 2: The extended Fourier map is indeed an isometry. -/
lemma fourierL2_isometry_norm (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖fourierL2_isometry f‖ = ‖f‖ := by
  -- Immediate from the defining property of `fourierL2_isometryCLM_choice`.
  simpa [fourierL2_isometry] using fourierL2_isometryCLM_choice_norm f

/-- On L¹ ∩ L², the extended L² Fourier isometry agrees a.e. with the
classical Fourier integral as a function of the frequency variable. -/
lemma fourierL2_isometry_ae_eq_fourierIntegral
    (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    (fourierL2_isometry (hg_L2.toLp g) : ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ => fourierIntegral g ξ := by
  classical
  -- First, on L¹ ∩ L² we know the underlying continuous linear map agrees
  -- with the L¹ ∩ L² Fourier map `fourierL1L2_toLp`.
  have h_agree :
      fourierL2_isometryCLM_choice (hg_L2.toLp g)
        = fourierL1L2_toLp g hg_L1 hg_L2 :=
    fourierL2_isometryCLM_choice_agree g hg_L1 hg_L2

  -- By construction, `fourierL2_isometry` is the linear isometry built from
  -- `fourierL2_isometryCLM_choice`, so they coincide on all inputs.
  have h_isometry_agree :
      fourierL2_isometry (hg_L2.toLp g)
        = fourierL1L2_toLp g hg_L1 hg_L2 := by
    -- Unfold the definition and simplify.
    simpa [fourierL2_isometry] using h_agree

  -- The `Lp` representative `fourierL1L2_toLp g hg_L1 hg_L2` is built from
  -- the function `ξ ↦ fourierIntegral g ξ`, so its canonical representative
  -- is a.e. equal to that Fourier integral.
  have h_coeFn :
      (fourierL1L2_toLp g hg_L1 hg_L2 : ℝ → ℂ)
        =ᵐ[volume] fourierIntegral g :=
    MemLp.coeFn_toLp (fourierIntegral_memLp_L1_L2 hg_L1 hg_L2)

  -- Transport the a.e. equality along the identification of `Lp` elements.
  simpa [h_isometry_agree] using h_coeFn

/-
Step 3: Inverse Fourier transform on L² and construction of the unitary equivalence.

We construct the inverse Fourier transform following the same pattern as the forward transform:
1. Define it on L¹ ∩ L² using the classical inverse Fourier integral
2. Show it's an isometry using the Fourier inversion formula
3. Extend by continuity to all of L²
4. Prove left and right inverse properties to build the LinearIsometryEquiv
-/

/-- Step 3.1: Inverse Fourier transform on L¹ ∩ L² as an L² element.
For g that is both integrable and in L², the inverse Fourier integral
recovers the original function in L² by Plancherel.

TODO: Complete this definition using the inverse Fourier Plancherel theorem.
The key insight is that the inverse Fourier transform has the same L² norm
preservation property as the forward transform. -/
noncomputable def invFourierL1L2_toLp (g : ℝ → ℂ)
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    Lp ℂ 2 (volume : Measure ℝ) := by
  -- The inverse Fourier transform of g is in L² by Plancherel
  have hInvFg_L2 : MemLp (fun t => Real.fourierIntegralInv g t) 2 volume := by
    -- First, the forward real Fourier transform of g is in L².
    have h_fwd :
        MemLp (fun t : ℝ => Real.fourierIntegral g t) 2 volume := by
      -- Use the L² membership for the (project) Fourier transform on L¹ ∩ L²,
      -- then convert to `Real.fourierIntegral`.
      have h :=
        (fourierIntegral_memLp_L1_L2 (g := g) hg_L1 hg_L2)
      simpa [fourierIntegral_eq_real] using h
    -- The inverse transform is the forward transform evaluated at `-t`.
    have h_eq :
        (fun t : ℝ => Real.fourierIntegralInv g t)
          = fun t : ℝ => Real.fourierIntegral g (-t) := by
      funext t
      simp [fourierIntegralInv_eq_fourierIntegral_neg]
    -- Precomposition with reflection `t ↦ -t` preserves L² membership.
    have h_comp :
        MemLp (fun t : ℝ => Real.fourierIntegral g (-t)) 2 volume := by
      simpa using
        h_fwd.comp_measurePreserving
          (Measure.measurePreserving_neg (volume : Measure ℝ))
    -- Conclude using the identification with the inverse Fourier transform.
    simpa [h_eq] using h_comp
  exact hInvFg_L2.toLp (fun t => Real.fourierIntegralInv g t)

/-- Step 3.2: The inverse Fourier transform on L¹ ∩ L² is an isometry.
TODO: Prove using Plancherel's theorem for inverse Fourier transform. -/
lemma invFourierL1L2_isometry_norm
    (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    ‖invFourierL1L2_toLp g hg_L1 hg_L2‖ = ‖hg_L2.toLp g‖ := by
  classical
  -- Express the norm of the inverse transform via its `eLpNorm`.
  have h_inv_norm :
      ‖invFourierL1L2_toLp g hg_L1 hg_L2‖
        = (eLpNorm (fun t : ℝ => Real.fourierIntegralInv g t) 2 volume).toReal := by
    simp [invFourierL1L2_toLp, Lp.norm_toLp]
  -- Express the norm of the forward transform via its `eLpNorm`.
  have h_fwd_norm :
      ‖fourierL1L2_toLp g hg_L1 hg_L2‖
        = (eLpNorm (fun ξ : ℝ => fourierIntegral g ξ) 2 volume).toReal := by
    simp [fourierL1L2_toLp, Lp.norm_toLp]

  -- L² membership of the real Fourier transform.
  have hF_kernel_mem :
      MemLp (fun ξ : ℝ => fourierIntegral g ξ) 2 volume :=
    fourierIntegral_memLp_L1_L2 hg_L1 hg_L2
  have hF_real_mem :
      MemLp (fun t : ℝ => Real.fourierIntegral g t) 2 volume := by
    simpa [fourierIntegral_eq_real] using hF_kernel_mem
  have h_meas_real :
      AEStronglyMeasurable (fun t : ℝ => Real.fourierIntegral g t) volume :=
    hF_real_mem.1

  -- Identify the inverse transform as the forward transform evaluated at `-t`.
  have h_inv_as_fwd :
      (fun t : ℝ => Real.fourierIntegralInv g t)
        = fun t : ℝ => Real.fourierIntegral g (-t) := by
    funext t
    simp [fourierIntegralInv_eq_fourierIntegral_neg]

  -- Composition with the reflection `t ↦ -t` preserves the L² norm.
  have h_eLp_inv_eq_real :
      eLpNorm (fun t : ℝ => Real.fourierIntegralInv g t) 2 volume
        = eLpNorm (fun t : ℝ => Real.fourierIntegral g t) 2 volume := by
    have h :=
      eLpNorm_comp_measurePreserving (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞))
        (f := fun t : ℝ => -t)
        (g := fun t : ℝ => Real.fourierIntegral g t)
        h_meas_real (Measure.measurePreserving_neg (volume : Measure ℝ))
    simpa [Function.comp, h_inv_as_fwd] using h

  -- Switch from `Real.fourierIntegral` to our kernel-based Fourier integral.
  have h_real_to_kernel :
      eLpNorm (fun t : ℝ => Real.fourierIntegral g t) 2 volume
        = eLpNorm (fun t : ℝ => fourierIntegral g t) 2 volume := by
    simp [fourierIntegral_eq_real]

  have h_eLp_inv_eq_kernel :
      eLpNorm (fun t : ℝ => Real.fourierIntegralInv g t) 2 volume
        = eLpNorm (fun t : ℝ => fourierIntegral g t) 2 volume := by
    simpa [h_real_to_kernel] using h_eLp_inv_eq_real

  -- Chain the equalities and invoke the forward L¹ ∩ L² isometry.
  calc
    ‖invFourierL1L2_toLp g hg_L1 hg_L2‖
        = (eLpNorm (fun t : ℝ => Real.fourierIntegralInv g t) 2 volume).toReal := h_inv_norm
    _ = (eLpNorm (fun t : ℝ => fourierIntegral g t) 2 volume).toReal := by
          simp [h_eLp_inv_eq_kernel]
    _ = ‖fourierL1L2_toLp g hg_L1 hg_L2‖ := h_fwd_norm.symm
    _ = ‖hg_L2.toLp g‖ := fourierL1L2_isometry g hg_L1 hg_L2

-- Well-definedness of inverse Fourier transform w.r.t. almost-everywhere equality.
lemma invFourierL1L2_toLp_congr_ae (g h : ℝ → ℂ)
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume)
    (hh_L1 : Integrable h) (hh_L2 : MemLp h 2 volume)
    (h_ae : g =ᵐ[volume] h) :
    invFourierL1L2_toLp g hg_L1 hg_L2 = invFourierL1L2_toLp h hh_L1 hh_L2 := by
  classical
  -- Build the L² membership witnesses from the definition
  have hInvFg_L2 : MemLp (fun t => Real.fourierIntegralInv g t) 2 volume := by
    have h_fwd : MemLp (fun t : ℝ => Real.fourierIntegral g t) 2 volume := by
      have h := fourierIntegral_memLp_L1_L2 (g := g) hg_L1 hg_L2
      simpa [fourierIntegral_eq_real] using h
    have h_eq : (fun t : ℝ => Real.fourierIntegralInv g t)
        = fun t : ℝ => Real.fourierIntegral g (-t) := by
      funext t; simp [fourierIntegralInv_eq_fourierIntegral_neg]
    simpa [h_eq] using h_fwd.comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hInvFh_L2 : MemLp (fun t => Real.fourierIntegralInv h t) 2 volume := by
    have h_fwd : MemLp (fun t : ℝ => Real.fourierIntegral h t) 2 volume := by
      have h := fourierIntegral_memLp_L1_L2 (g := h) hh_L1 hh_L2
      simpa [fourierIntegral_eq_real] using h
    have h_eq : (fun t : ℝ => Real.fourierIntegralInv h t)
        = fun t : ℝ => Real.fourierIntegral h (-t) := by
      funext t; simp [fourierIntegralInv_eq_fourierIntegral_neg]
    simpa [h_eq] using h_fwd.comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  -- The inverse Fourier integrals are a.e. equal since g =ᵐ h
  have h_invF_ae :
      (fun t : ℝ => Real.fourierIntegralInv g t)
        =ᵐ[volume]
      (fun t : ℝ => Real.fourierIntegralInv h t) := by
    filter_upwards with t
    unfold Real.fourierIntegralInv
    apply integral_congr_ae
    filter_upwards [h_ae] with s hs
    simp only [hs]
  exact (MemLp.toLp_eq_toLp_iff hInvFg_L2 hInvFh_L2).mpr h_invF_ae

-- Additivity of the inverse Fourier transform on L¹ ∩ L².
lemma invFourierL1L2_toLp_add (g h : ℝ → ℂ)
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume)
    (hh_L1 : Integrable h) (hh_L2 : MemLp h 2 volume) :
    invFourierL1L2_toLp (fun t => g t + h t)
      (hg_L1.add hh_L1) (hg_L2.add hh_L2)
    = invFourierL1L2_toLp g hg_L1 hg_L2
      + invFourierL1L2_toLp h hh_L1 hh_L2 := by
  classical
  -- Unfold definitions and compare representatives a.e.
  apply Lp.ext (μ := (volume : Measure ℝ))
  -- Get the L² membership witnesses
  have hInvFsum_mem : MemLp (fun t => Real.fourierIntegralInv (fun s => g s + h s) t) 2 volume := by
    have h_fwd : MemLp (fun t : ℝ => Real.fourierIntegral (fun s => g s + h s) t) 2 volume := by
      have h :=
        fourierIntegral_memLp_L1_L2 (g := fun s => g s + h s) (hg_L1.add hh_L1) (hg_L2.add hh_L2)
      simpa [fourierIntegral_eq_real] using h
    have h_eq : (fun t : ℝ => Real.fourierIntegralInv (fun s => g s + h s) t)
        = fun t : ℝ => Real.fourierIntegral (fun s => g s + h s) (-t) := by
      funext t; simp [fourierIntegralInv_eq_fourierIntegral_neg]
    simpa [h_eq] using h_fwd.comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hInvFg_mem : MemLp (fun t => Real.fourierIntegralInv g t) 2 volume := by
    have h_fwd : MemLp (fun t : ℝ => Real.fourierIntegral g t) 2 volume := by
      have h := fourierIntegral_memLp_L1_L2 (g := g) hg_L1 hg_L2
      simpa [fourierIntegral_eq_real] using h
    have h_eq : (fun t : ℝ => Real.fourierIntegralInv g t)
        = fun t : ℝ => Real.fourierIntegral g (-t) := by
      funext t; simp [fourierIntegralInv_eq_fourierIntegral_neg]
    simpa [h_eq] using h_fwd.comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hInvFh_mem : MemLp (fun t => Real.fourierIntegralInv h t) 2 volume := by
    have h_fwd : MemLp (fun t : ℝ => Real.fourierIntegral h t) 2 volume := by
      have h := fourierIntegral_memLp_L1_L2 (g := h) hh_L1 hh_L2
      simpa [fourierIntegral_eq_real] using h
    have h_eq : (fun t : ℝ => Real.fourierIntegralInv h t)
        = fun t : ℝ => Real.fourierIntegral h (-t) := by
      funext t; simp [fourierIntegralInv_eq_fourierIntegral_neg]
    simpa [h_eq] using h_fwd.comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  -- Use coeFn_toLp to get a.e. equalities
  have h_sum := MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hInvFsum_mem
  have hg_coe := MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hInvFg_mem
  have hh_coe := MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hInvFh_mem
  -- Show a.e. equality of the coerced functions
  calc
    (invFourierL1L2_toLp (fun t => g t + h t) (hg_L1.add hh_L1) (hg_L2.add hh_L2) :
        Lp ℂ 2 (volume : Measure ℝ))
        =ᵐ[volume] (fun t : ℝ => Real.fourierIntegralInv (fun s => g s + h s) t) := by
          simp [invFourierL1L2_toLp]; exact h_sum
    _ =ᵐ[volume]
        (fun t : ℝ => Real.fourierIntegralInv g t + Real.fourierIntegralInv h t) := by
          refine ae_of_all _ (fun t => ?_)
          unfold Real.fourierIntegralInv VectorFourier.fourierIntegral
          simp only [Pi.add_apply]
          rw [← integral_add]
          · congr 1
            funext ξ
            simp only [smul_add]
          · exact (VectorFourier.fourierIntegral_convergent_iff
              (e := Real.fourierChar) (μ := volume) (L := -innerₗ ℝ)
              continuous_fourierChar (by continuity) (f := g) t).mpr hg_L1
          · exact (VectorFourier.fourierIntegral_convergent_iff
              (e := Real.fourierChar) (μ := volume) (L := -innerₗ ℝ)
              continuous_fourierChar (by continuity) (f := h) t).mpr hh_L1
    _ =ᵐ[volume]
        (invFourierL1L2_toLp g hg_L1 hg_L2 : Lp ℂ 2 (volume : Measure ℝ))
          + (invFourierL1L2_toLp h hh_L1 hh_L2 : Lp ℂ 2 (volume : Measure ℝ)) := by
          have this1 : (fun t : ℝ => Real.fourierIntegralInv g t + Real.fourierIntegralInv h t)
              =ᵐ[volume]
              (fun t : ℝ =>
                ((invFourierL1L2_toLp g hg_L1 hg_L2 : Lp ℂ 2 (volume : Measure ℝ)) t)
                + ((invFourierL1L2_toLp h hh_L1 hh_L2 : Lp ℂ 2 (volume : Measure ℝ)) t)) := by
            have hg_eq := hg_coe.symm
            have hh_eq := hh_coe.symm
            exact hg_eq.add hh_eq
          have this2 : (fun t => (invFourierL1L2_toLp g hg_L1 hg_L2 : Lp ℂ 2 (volume : Measure ℝ)) t
                + (invFourierL1L2_toLp h hh_L1 hh_L2 : Lp ℂ 2 (volume : Measure ℝ)) t)
              =ᵐ[volume]
              ((invFourierL1L2_toLp g hg_L1 hg_L2 : Lp ℂ 2 (volume : Measure ℝ))
                + (invFourierL1L2_toLp h hh_L1 hh_L2 : Lp ℂ 2 (volume : Measure ℝ))) := by
            apply ae_of_all
            intro t
            rfl
          exact this1.trans this2
    _ =ᵐ[volume]
        ((invFourierL1L2_toLp g hg_L1 hg_L2 + invFourierL1L2_toLp h hh_L1 hh_L2 :
          Lp ℂ 2 (volume : Measure ℝ))) := by
      filter_upwards [Lp.coeFn_add (invFourierL1L2_toLp g hg_L1 hg_L2)
        (invFourierL1L2_toLp h hh_L1 hh_L2)] with t ht
      exact ht.symm

-- Scalar multiplication compatibility of the inverse Fourier transform.
lemma invFourierL1L2_toLp_smul (c : ℂ) (g : ℝ → ℂ)
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    invFourierL1L2_toLp (fun t => c • g t)
      (hg_L1.smul c) (hg_L2.const_smul c)
    = c • invFourierL1L2_toLp g hg_L1 hg_L2 := by
  classical
  -- Unfold definitions and compare representatives a.e.
  apply Lp.ext (μ := (volume : Measure ℝ))
  -- Get the L² membership witnesses
  have hInvFcg_mem : MemLp (fun t => Real.fourierIntegralInv (fun s => c • g s) t) 2 volume := by
    have h_fwd : MemLp (fun t : ℝ => Real.fourierIntegral (fun s => c • g s) t) 2 volume := by
      have h :=
        fourierIntegral_memLp_L1_L2 (g := fun s => c • g s) (hg_L1.smul c) (hg_L2.const_smul c)
      simpa [fourierIntegral_eq_real] using h
    have h_eq : (fun t : ℝ => Real.fourierIntegralInv (fun s => c • g s) t)
        = fun t : ℝ => Real.fourierIntegral (fun s => c • g s) (-t) := by
      funext t; simp [fourierIntegralInv_eq_fourierIntegral_neg]
    rw [h_eq]
    exact h_fwd.comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hInvFg_mem : MemLp (fun t => Real.fourierIntegralInv g t) 2 volume := by
    have h_fwd : MemLp (fun t : ℝ => Real.fourierIntegral g t) 2 volume := by
      have h := fourierIntegral_memLp_L1_L2 (g := g) hg_L1 hg_L2
      simpa [fourierIntegral_eq_real] using h
    have h_eq : (fun t : ℝ => Real.fourierIntegralInv g t)
        = fun t : ℝ => Real.fourierIntegral g (-t) := by
      funext t; simp [fourierIntegralInv_eq_fourierIntegral_neg]
    simpa [h_eq] using h_fwd.comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  -- Use coeFn_toLp to get a.e. equalities
  have h_cg := MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hInvFcg_mem
  have hg_coe := MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hInvFg_mem
  -- Show a.e. equality
  calc
    (invFourierL1L2_toLp (fun t => c • g t) (hg_L1.smul c) (hg_L2.const_smul c) :
        Lp ℂ 2 (volume : Measure ℝ))
        =ᵐ[volume] (fun t : ℝ => Real.fourierIntegralInv (fun s => c • g s) t) := by
          simp [invFourierL1L2_toLp]; exact h_cg
    _ =ᵐ[volume]
        (fun t : ℝ => c • Real.fourierIntegralInv g t) := by
          refine ae_of_all _ (fun t => ?_)
          unfold Real.fourierIntegralInv VectorFourier.fourierIntegral
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [← integral_const_mul]
          congr 1
          funext s
          show 𝐞 (-((-innerₗ ℝ) s) t) • (c * g s) = c * (𝐞 (-((-innerₗ ℝ) s) t) • g s)
          rw [← mul_smul_comm]
    _ =ᵐ[volume]
        (fun t : ℝ => ((c • (invFourierL1L2_toLp g hg_L1 hg_L2 :
            Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) t) := by
          have this1 : (fun t : ℝ => c • Real.fourierIntegralInv g t)
              =ᵐ[volume]
              (fun t : ℝ => c • (MemLp.toLp (fun t => Real.fourierIntegralInv g t)
                hInvFg_mem : Lp ℂ 2 (volume : Measure ℝ)) t) := by
            filter_upwards [hg_coe.symm] with t ht
            rw [ht]
          have this2 :
              (fun t => c • (MemLp.toLp
                (fun t => Real.fourierIntegralInv g t) hInvFg_mem : Lp ℂ 2 (volume : Measure ℝ)) t)
              =ᵐ[volume] (fun t => c • (invFourierL1L2_toLp g hg_L1 hg_L2 : Lp ℂ 2
                (volume : Measure ℝ)) t) := by
            apply ae_of_all
            intro t
            rfl
          exact this1.trans this2
    _ =ᵐ[volume]
        (↑↑(c • invFourierL1L2_toLp g hg_L1 hg_L2) : ℝ → ℂ) := by
      filter_upwards [Lp.coeFn_smul c (invFourierL1L2_toLp g hg_L1 hg_L2)] with t ht
      simp only [Pi.smul_apply]
      exact ht.symm

/-- Linear map on L¹ ∩ L² that applies the inverse Fourier transform. -/
noncomputable def invT0_on_L1L2 :
    L1L2Submodule →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  classical
  refine
    { toFun := fun x => by
        -- Extract the witness that x is in L¹ ∩ L²
        have hx_mem : ((x : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := x.property
        -- Choose a representative function
        let g : ℝ → ℂ := Classical.choose hx_mem
        let ex1 := Classical.choose_spec hx_mem
        let hL1 : Integrable g := Classical.choose ex1
        let ex2 := Classical.choose_spec ex1
        let hL2 : MemLp g 2 volume := Classical.choose ex2
        exact invFourierL1L2_toLp g hL1 hL2
    , map_add' := by
        intro f g
        rcases f.property with ⟨g₁, hg₁_L1, hg₁_L2, hf⟩
        rcases g.property with ⟨g₂, hg₂_L1, hg₂_L2, hg⟩
        have hf_mem : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set :=
          ⟨g₁, hg₁_L1, hg₁_L2, hf⟩
        have hg_mem : ((g : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set :=
          ⟨g₂, hg₂_L1, hg₂_L2, hg⟩
        have h_sum_rep : ((f + g : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ)) ∈ L1L2Set :=
          (L1L2Set_add_mem hf_mem hg_mem)
        rcases h_sum_rep with ⟨gs, hs_L1, hs_L2, hfg_eq⟩
        have h_sum_toLp_eq :
            (hs_L2.toLp gs : Lp ℂ 2 (volume : Measure ℝ))
              = (hg₁_L2.toLp g₁ + hg₂_L2.toLp g₂) := by
          have h_canon :
              ((hg₁_L2.add hg₂_L2).toLp (fun t : ℝ => g₁ t + g₂ t)
                : Lp ℂ 2 (volume : Measure ℝ))
                = (hg₁_L2.toLp g₁ + hg₂_L2.toLp g₂) := by
            apply Lp.ext (μ := (volume : Measure ℝ))
            have h₁ := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hg₁_L2
            have h₂ := MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) hg₂_L2
            have hsum :=
              MeasureTheory.MemLp.coeFn_toLp (μ := (volume : Measure ℝ)) (hg₁_L2.add hg₂_L2)
            calc
              ((MemLp.toLp (fun t : ℝ => g₁ t + g₂ t) (hg₁_L2.add hg₂_L2)) :
                  Lp ℂ 2 (volume : Measure ℝ))
                  =ᵐ[volume] (fun t : ℝ => g₁ t + g₂ t) := hsum
              _ =ᵐ[volume]
                  (MemLp.toLp g₁ hg₁_L2 : Lp ℂ 2 (volume : Measure ℝ))
                    + (MemLp.toLp g₂ hg₂_L2 : Lp ℂ 2 (volume : Measure ℝ)) := (h₁.add h₂).symm
              _ =ᵐ[volume]
                  ((MemLp.toLp g₁ hg₁_L2 + MemLp.toLp g₂ hg₂_L2 :
                    Lp ℂ 2 (volume : Measure ℝ))) := (Lp.coeFn_add _ _).symm
          have hfg_sum :
              (hg₁_L2.toLp g₁ + hg₂_L2.toLp g₂ : Lp ℂ 2 (volume : Measure ℝ))
                = ((f + g : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ)) := by
            have : ((f + g : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ))
                = (f : Lp ℂ 2 (volume : Measure ℝ)) + (g : Lp ℂ 2 (volume : Measure ℝ)) := rfl
            rw [this, hf, hg]
          rw [← hfg_eq, hfg_sum]
        have hgs_ae : (fun t => gs t) =ᵐ[volume] (fun t => g₁ t + g₂ t) := by
          exact (MemLp.toLp_eq_toLp_iff hs_L2 (hg₁_L2.add hg₂_L2)).1 h_sum_toLp_eq
        have h_left :
            invFourierL1L2_toLp gs hs_L1 hs_L2
              = invFourierL1L2_toLp (fun t => g₁ t + g₂ t)
                  (hg₁_L1.add hg₂_L1) (hg₁_L2.add hg₂_L2) :=
          invFourierL1L2_toLp_congr_ae gs (fun t => g₁ t + g₂ t)
            hs_L1 hs_L2 (hg₁_L1.add hg₂_L1) (hg₁_L2.add hg₂_L2) hgs_ae
        have hmem_fg : ((f + g : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
          simpa [L1L2Submodule] using (f + g).property
        let gch : ℝ → ℂ := Classical.choose hmem_fg
        let ex1c := Classical.choose_spec hmem_fg
        let hL1c : Integrable gch := Classical.choose ex1c
        let ex2c := Classical.choose_spec ex1c
        let hL2c : MemLp gch 2 (volume : Measure ℝ) := Classical.choose ex2c
        have hfg_eq_choice : ((f + g : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ))
            = hL2c.toLp gch := by
          exact Classical.choose_spec ex2c
        have h_ae_sum : (fun t => gs t) =ᵐ[volume] gch := by
          have : (hs_L2.toLp gs : Lp ℂ 2 (volume : Measure ℝ)) = hL2c.toLp gch := by
            exact (hfg_eq.symm.trans hfg_eq_choice)
          exact (MemLp.toLp_eq_toLp_iff hs_L2 hL2c).1 this
        have h_sum_congr :
            invFourierL1L2_toLp gs hs_L1 hs_L2
              = invFourierL1L2_toLp gch hL1c hL2c :=
          invFourierL1L2_toLp_congr_ae gs gch hs_L1 hs_L2 hL1c hL2c h_ae_sum
        have hmem_f : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
          simp [L1L2Submodule]
        let gf : ℝ → ℂ := Classical.choose hmem_f
        let ex1f := Classical.choose_spec hmem_f
        let hL1f : Integrable gf := Classical.choose ex1f
        let ex2f := Classical.choose_spec ex1f
        let hL2f : MemLp gf 2 (volume : Measure ℝ) := Classical.choose ex2f
        have hf_choice : ((f : Lp ℂ 2 (volume : Measure ℝ))) = hL2f.toLp gf :=
          Classical.choose_spec ex2f
        have h_ae_f : (fun t => gf t) =ᵐ[volume] g₁ := by
          have : (hL2f.toLp gf : Lp ℂ 2 (volume : Measure ℝ)) = hg₁_L2.toLp g₁ := by
            rw [← hf_choice, hf]
          exact (MemLp.toLp_eq_toLp_iff hL2f hg₁_L2).1 this
        have h_f_congr :
            invFourierL1L2_toLp gf hL1f hL2f
              = invFourierL1L2_toLp g₁ hg₁_L1 hg₁_L2 :=
          invFourierL1L2_toLp_congr_ae gf g₁ hL1f hL2f hg₁_L1 hg₁_L2 h_ae_f
        have hmem_g : ((g : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
          simp [L1L2Submodule]
        let gg : ℝ → ℂ := Classical.choose hmem_g
        let ex1g := Classical.choose_spec hmem_g
        let hL1g : Integrable gg := Classical.choose ex1g
        let ex2g := Classical.choose_spec ex1g
        let hL2g : MemLp gg 2 (volume : Measure ℝ) := Classical.choose ex2g
        have hg_choice : ((g : Lp ℂ 2 (volume : Measure ℝ))) = hL2g.toLp gg :=
          Classical.choose_spec ex2g
        have h_ae_g : (fun t => gg t) =ᵐ[volume] g₂ := by
          have : (hL2g.toLp gg : Lp ℂ 2 (volume : Measure ℝ)) = hg₂_L2.toLp g₂ := by
            rw [← hg_choice, hg]
          exact (MemLp.toLp_eq_toLp_iff hL2g hg₂_L2).1 this
        have h_g_congr :
            invFourierL1L2_toLp gg hL1g hL2g
              = invFourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 :=
          invFourierL1L2_toLp_congr_ae gg g₂ hL1g hL2g hg₂_L1 hg₂_L2 h_ae_g
        have h_gch_eq :
            invFourierL1L2_toLp gch hL1c hL2c
              = invFourierL1L2_toLp g₁ hg₁_L1 hg₁_L2
                + invFourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 := by
          calc invFourierL1L2_toLp gch hL1c hL2c
              = invFourierL1L2_toLp gs hs_L1 hs_L2 := h_sum_congr.symm
            _ = invFourierL1L2_toLp (fun t => g₁ t + g₂ t)
                (hg₁_L1.add hg₂_L1) (hg₁_L2.add hg₂_L2) := h_left
            _ = invFourierL1L2_toLp g₁ hg₁_L1 hg₁_L2 + invFourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 :=
                  invFourierL1L2_toLp_add g₁ g₂ hg₁_L1 hg₁_L2 hg₂_L1 hg₂_L2
        calc
          invFourierL1L2_toLp gch hL1c hL2c
              = invFourierL1L2_toLp g₁ hg₁_L1 hg₁_L2
                + invFourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 := h_gch_eq
          _ = invFourierL1L2_toLp gf hL1f hL2f
                + invFourierL1L2_toLp g₂ hg₂_L1 hg₂_L2 := by simp [h_f_congr]
          _ = invFourierL1L2_toLp gf hL1f hL2f
                + invFourierL1L2_toLp gg hL1g hL2g := by simp [h_g_congr]
    , map_smul' := by
        intro c f
        rcases f.property with ⟨g, hg_L1, hg_L2, hf⟩
        have hf_mem : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set :=
          ⟨g, hg_L1, hg_L2, hf⟩
        have h_smul_rep : ((c • f : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ)) ∈ L1L2Set :=
          L1L2Set_smul_mem c hf_mem
        rcases h_smul_rep with ⟨gs, hs_L1, hs_L2, hcf_eq⟩
        have hcf_toLp_eq :
            (hs_L2.toLp gs : Lp ℂ 2 (volume : Measure ℝ))
              = (c • hg_L2.toLp g) := by
          rw [← hf]
          exact hcf_eq.symm
        have hgs_ae : (fun t => gs t) =ᵐ[volume] (fun t => c • g t) := by
          exact (MemLp.toLp_eq_toLp_iff hs_L2 (hg_L2.const_smul c)).1 hcf_toLp_eq
        have h_left :
            invFourierL1L2_toLp gs hs_L1 hs_L2
              = invFourierL1L2_toLp (fun t => c • g t)
                  (hg_L1.smul c) (hg_L2.const_smul c) :=
          invFourierL1L2_toLp_congr_ae gs (fun t => c • g t)
            hs_L1 hs_L2 (hg_L1.smul c) (hg_L2.const_smul c) hgs_ae
        have hmem_cf : (((c • f : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
          simpa [L1L2Submodule] using (c • f).property
        let gch : ℝ → ℂ := Classical.choose hmem_cf
        let ex1c := Classical.choose_spec hmem_cf
        let hL1c : Integrable gch := Classical.choose ex1c
        let ex2c := Classical.choose_spec ex1c
        let hL2c : MemLp gch 2 (volume : Measure ℝ) := Classical.choose ex2c
        have hcf_eq_choice : ((c • f : L1L2Submodule) : Lp ℂ 2 (volume : Measure ℝ))
            = hL2c.toLp gch := by
          exact Classical.choose_spec ex2c
        have h_ae_cf : (fun t => gs t) =ᵐ[volume] gch := by
          have : (hs_L2.toLp gs : Lp ℂ 2 (volume : Measure ℝ)) = hL2c.toLp gch := by
            exact (hcf_eq.symm.trans hcf_eq_choice)
          exact (MemLp.toLp_eq_toLp_iff hs_L2 hL2c).1 this
        have h_cf_congr :
            invFourierL1L2_toLp gs hs_L1 hs_L2
              = invFourierL1L2_toLp gch hL1c hL2c :=
          invFourierL1L2_toLp_congr_ae gs gch hs_L1 hs_L2 hL1c hL2c h_ae_cf
        have hmem_f : ((f : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
          simp [L1L2Submodule]
        let gf : ℝ → ℂ := Classical.choose hmem_f
        let ex1f := Classical.choose_spec hmem_f
        let hL1f : Integrable gf := Classical.choose ex1f
        let ex2f := Classical.choose_spec ex1f
        let hL2f : MemLp gf 2 (volume : Measure ℝ) := Classical.choose ex2f
        have hf_choice : ((f : Lp ℂ 2 (volume : Measure ℝ))) = hL2f.toLp gf :=
          Classical.choose_spec ex2f
        have h_ae_f : (fun t => gf t) =ᵐ[volume] g := by
          have : (hL2f.toLp gf : Lp ℂ 2 (volume : Measure ℝ)) = hg_L2.toLp g := by
            rw [← hf_choice, hf]
          exact (MemLp.toLp_eq_toLp_iff hL2f hg_L2).1 this
        have h_f_congr :
            invFourierL1L2_toLp gf hL1f hL2f
              = invFourierL1L2_toLp g hg_L1 hg_L2 :=
          invFourierL1L2_toLp_congr_ae gf g hL1f hL2f hg_L1 hg_L2 h_ae_f
        have h_gch_eq : invFourierL1L2_toLp gch hL1c hL2c
            = c • invFourierL1L2_toLp g hg_L1 hg_L2 := by
          calc invFourierL1L2_toLp gch hL1c hL2c
              = invFourierL1L2_toLp gs hs_L1 hs_L2 := h_cf_congr.symm
            _ = invFourierL1L2_toLp (fun t => c • g t) (hg_L1.smul c) (hg_L2.const_smul c) := h_left
            _ = c • invFourierL1L2_toLp g hg_L1 hg_L2 := invFourierL1L2_toLp_smul c g hg_L1 hg_L2
        calc
          invFourierL1L2_toLp gch hL1c hL2c
              = c • invFourierL1L2_toLp g hg_L1 hg_L2 := h_gch_eq
          _ = c • invFourierL1L2_toLp gf hL1f hL2f := by simp [h_f_congr]
    }

/-- The inverse Fourier transform on L¹ ∩ L² is an isometry. -/
lemma invT0_on_L1L2_isometry (x : L1L2Submodule) :
    ‖invT0_on_L1L2 x‖ = ‖(x : Lp ℂ 2 (volume : Measure ℝ))‖ := by
  classical
  have hx_mem : ((x : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := x.property
  let g : ℝ → ℂ := Classical.choose hx_mem
  let ex1 := Classical.choose_spec hx_mem
  let hL1 : Integrable g := Classical.choose ex1
  let ex2 := Classical.choose_spec ex1
  let hL2 : MemLp g 2 volume := Classical.choose ex2
  have hx_eq : ((x : Lp ℂ 2 (volume : Measure ℝ))) = hL2.toLp g :=
    Classical.choose_spec ex2
  calc
    ‖invT0_on_L1L2 x‖ = ‖invFourierL1L2_toLp g hL1 hL2‖ := rfl
    _ = ‖hL2.toLp g‖ := invFourierL1L2_isometry_norm g hL1 hL2
    _ = ‖(x : Lp ℂ 2 (volume : Measure ℝ))‖ := by simp [hx_eq]

/-- Auxiliary existence: there exists a continuous linear isometry on L² that
agrees with the L¹ ∩ L² inverse Fourier map. -/
lemma exists_invFourierL2_isometryCLM_agrees :
    ∃ F : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      (∀ g : Lp ℂ 2 (volume : Measure ℝ), ‖F g‖ = ‖g‖) ∧
      (∀ (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume),
        F (hg_L2.toLp g) = invFourierL1L2_toLp g hg_L1 hg_L2) := by
  classical
  -- Extend from the dense submodule using the same pattern as forward Fourier
  have hDense : Dense ((L1L2Submodule : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
      Set (Lp ℂ 2 (volume : Measure ℝ))) := by
    simpa [L1L2Submodule, L1L2Set] using (L1L2Set_dense : Dense L1L2Set)
  obtain ⟨T, hAgree, hNorm⟩ :=
    extend_linear_isometry_of_dense
      (P := L1L2Submodule)
      (hP := hDense)
      (T0 := invT0_on_L1L2)
      (hIso := invT0_on_L1L2_isometry)
  refine ⟨T, ?hn, ?hag⟩
  · intro g; simpa using hNorm g
  · intro g hg_L1 hg_L2
    have hx_mem : (hg_L2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) ∈ L1L2Set :=
      ⟨g, hg_L1, hg_L2, rfl⟩
    let x : L1L2Submodule := ⟨hg_L2.toLp g, hx_mem⟩
    have hx : T x = invT0_on_L1L2 x := hAgree x
    -- invT0_on_L1L2 x should equal invFourierL1L2_toLp g hg_L1 hg_L2
    -- by construction (modulo a.e. equality of representatives)
    have : invT0_on_L1L2 x = invFourierL1L2_toLp g hg_L1 hg_L2 := by
      have hmemx : ((x : Lp ℂ 2 (volume : Measure ℝ))) ∈ L1L2Set := by
        simp [L1L2Submodule]
      let gx : ℝ → ℂ := Classical.choose hmemx
      let ex1x := Classical.choose_spec hmemx
      let hL1x : Integrable gx := Classical.choose ex1x
      let ex2x := Classical.choose_spec ex1x
      let hL2x : MemLp gx 2 (volume : Measure ℝ) := Classical.choose ex2x
      have hx_choice : ((x : Lp ℂ 2 (volume : Measure ℝ))) = hL2x.toLp gx :=
        Classical.choose_spec ex2x
      have hx_coe : ((x : Lp ℂ 2 (volume : Measure ℝ))) = hg_L2.toLp g := rfl
      have h_toLp_eq : (hL2x.toLp gx : Lp ℂ 2 (volume : Measure ℝ))
            = hg_L2.toLp g := by
        simpa [hx_coe] using hx_choice.symm
      have h_ae : (fun t => gx t) =ᵐ[volume] g :=
        (MemLp.toLp_eq_toLp_iff hL2x hg_L2).1 h_toLp_eq
      have h_congr :=
        invFourierL1L2_toLp_congr_ae gx g hL1x hL2x hg_L1 hg_L2 h_ae
      have hT : invT0_on_L1L2 x = invFourierL1L2_toLp gx hL1x hL2x := rfl
      simpa [hT] using h_congr
    rw [← this, ← hx]

noncomputable def invFourierL2_isometryCLM_choice :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Classical.choose exists_invFourierL2_isometryCLM_agrees

lemma invFourierL2_isometryCLM_choice_norm
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖invFourierL2_isometryCLM_choice f‖ = ‖f‖ := by
  classical
  have h := Classical.choose_spec exists_invFourierL2_isometryCLM_agrees
  exact h.1 f

lemma invFourierL2_isometryCLM_choice_agree (g : ℝ → ℂ)
    (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume) :
    invFourierL2_isometryCLM_choice (hg_L2.toLp g) =
      invFourierL1L2_toLp g hg_L1 hg_L2 := by
  classical
  have h := Classical.choose_spec exists_invFourierL2_isometryCLM_agrees
  exact h.2 g hg_L1 hg_L2

/-- Step 3.3: Inverse Fourier isometry on all of L².
Extend the inverse Fourier transform from L¹ ∩ L² to all of L² by continuity. -/
noncomputable def invFourierL2_isometry :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  classical
  refine
    { toLinearMap := invFourierL2_isometryCLM_choice
    , norm_map' := ?_ }
  intro f
  simpa using invFourierL2_isometryCLM_choice_norm f

/-- Step 3.4: The inverse Fourier isometry is a left inverse of the forward
Fourier isometry. This uses the Fourier inversion formula: invF(F(g)) = g
for g ∈ L¹ ∩ L², proved in `fourierIntegralInv_fourierIntegral_ae_of_L1_L2`.
TODO: Extend this a.e. equality to L² equality and then to all of L² by density. -/
lemma invFourierL2_isometry_left_inv :
    ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      invFourierL2_isometry (fourierL2_isometry f) = f := by
  classical
  intro f
  -- Use density: L¹ ∩ L² is dense in L²
  have hDense : Dense L1L2Set := L1L2Set_dense
  -- The equalizer {f | invFourierL2 (fourierL2 f) = f} is closed
  have hClosed : IsClosed {f : Lp ℂ 2 (volume : Measure ℝ) |
      invFourierL2_isometry (fourierL2_isometry f) = f} := by
    apply isClosed_eq
    · exact (invFourierL2_isometry.continuous.comp fourierL2_isometry.continuous)
    · exact continuous_id
  -- It suffices to show the equalizer contains the dense subset L¹ ∩ L²
  suffices h : ∀ (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume),
      invFourierL2_isometry (fourierL2_isometry (hg_L2.toLp g)) = hg_L2.toLp g by
    -- Apply density: if a closed set contains a dense subset, it's everything
    have hContains : L1L2Set ⊆ {f : Lp ℂ 2 (volume : Measure ℝ) |
        invFourierL2_isometry (fourierL2_isometry f) = f} := by
      intro x ⟨g, hg_L1, hg_L2, hg_eq⟩
      simp only [Set.mem_setOf_eq]
      subst hg_eq
      exact h g hg_L1 hg_L2
    -- Use the closure equals all of the space
    have hEq : closure L1L2Set = Set.univ := hDense.closure_eq
    have hMem : f ∈ closure L1L2Set := by
      rw [hEq]
      trivial
    have : f ∈ {f : Lp ℂ 2 (volume : Measure ℝ) |
        invFourierL2_isometry (fourierL2_isometry f) = f} := by
      apply closure_minimal hContains hClosed hMem
    exact this
  intro g hg_L1 hg_L2
  -- Step 1: Approximate g by Schwartz functions in L¹ ∩ L².
  obtain ⟨φ, hφ_L1, hφ_L2, hφ_tendsto_L1, hφ_tendsto_L2⟩ :=
    Frourio.exists_schwartz_L1_L2_approx g hg_L1 hg_L2

  -- Step 2: Show convergence of φ_n to g in L².
  have h_phi_to_g :
      Filter.Tendsto (fun n => (hφ_L2 n).toLp (φ n)) Filter.atTop (𝓝 (hg_L2.toLp g)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    convert hφ_tendsto_L2 using 1
    ext n
    rw [← eLpNorm_neg]
    rw [neg_sub]
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (hg_L2.toLp g) ((hφ_L2 n).toLp (φ n)),
                    MemLp.coeFn_toLp (hφ_L2 n),
                    MemLp.coeFn_toLp hg_L2] with x h_sub h_phi h_g
    simp only [Pi.sub_apply, h_g, h_phi]

  -- Step 3: Show convergence of F(φ_n) to F(g) in L².
  have h_Fphi_to_Fg : Filter.Tendsto (fun n => fourierL2_isometry ((hφ_L2 n).toLp (φ n)))
      Filter.atTop (𝓝 (fourierL2_isometry (hg_L2.toLp g))) :=
    (fourierL2_isometry.continuous.tendsto (hg_L2.toLp g)).comp h_phi_to_g

  -- Step 4: Show that for Schwartz functions, invF(F(φ_n)) = φ_n.
  have h_inv_F_phi : ∀ n, invFourierL2_isometry (fourierL2_isometry ((hφ_L2 n).toLp (φ n)))
      = (hφ_L2 n).toLp (φ n) := by
    intro n
    let ψ := φ n
    have hψ_S : SchwartzMap ℝ ℂ := φ n
    let hFψ_S : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ ψ
    have hFψ_L1 : Integrable hFψ_S := hFψ_S.integrable
    have hFψ_L2 : MemLp hFψ_S 2 volume := hFψ_S.memLp 2

    -- fourierL2_isometry agrees with fourierIntegral on L¹ ∩ L²
    have h_F_eq : fourierL2_isometry ((hφ_L2 n).toLp ψ) = hFψ_L2.toLp hFψ_S := by
      apply Lp.ext (μ := volume)
      have h1 := fourierL2_isometry_ae_eq_fourierIntegral ψ (hφ_L1 n) (hφ_L2 n)
      have h2 := MemLp.coeFn_toLp hFψ_L2
      have h_eq_pt : (fun ξ => fourierIntegral ψ ξ) = hFψ_S := by
        ext ξ
        rw [← fourierIntegral_eq_real]
        rw [SchwartzMap.fourierTransformCLM_apply]
      rw [h_eq_pt] at h1
      exact h1.trans h2.symm
    rw [h_F_eq]

    -- invFourierL2_isometry agrees with invFourierL1L2_toLp on L¹ ∩ L²
    have h_inv_eq : invFourierL2_isometry (hFψ_L2.toLp hFψ_S)
        = invFourierL1L2_toLp hFψ_S hFψ_L1 hFψ_L2 := by
      apply invFourierL2_isometryCLM_choice_agree
    rw [h_inv_eq]

    -- invFourierL1L2_toLp corresponds to the inverse Fourier integral
    apply Lp.ext (μ := volume)
    unfold invFourierL1L2_toLp
    refine (MemLp.coeFn_toLp _).trans ?_
    refine (Filter.EventuallyEq.trans ?_ (MemLp.coeFn_toLp (hφ_L2 n)).symm)
    filter_upwards with t
    have h_inv := fourierIntegralInv_fourierIntegral_schwartz ψ
    rw [← congr_fun h_inv t]
    congr 1
    ext ξ
    show hFψ_S ξ = fourierIntegral (fun t ↦ ψ t) ξ
    rw [← fourierIntegral_eq_real]
    rfl

  -- Step 5: Conclusion by uniqueness of limits.
  -- LHS converges to invFourierL2_isometry (F(g))
  have h_lim_lhs :
      Filter.Tendsto (fun n => invFourierL2_isometry (fourierL2_isometry ((hφ_L2 n).toLp (φ n))))
      Filter.atTop (𝓝 (invFourierL2_isometry (fourierL2_isometry (hg_L2.toLp g)))) :=
    (invFourierL2_isometry.continuous.tendsto _).comp h_Fphi_to_Fg

  -- RHS converges to g
  have h_lim_rhs :
      Filter.Tendsto (fun n => invFourierL2_isometry (fourierL2_isometry ((hφ_L2 n).toLp (φ n))))
      Filter.atTop (𝓝 (hg_L2.toLp g)) := by
    simp only [h_inv_F_phi]
    exact h_phi_to_g

  exact tendsto_nhds_unique h_lim_lhs h_lim_rhs

/-- Step 3.5: The inverse Fourier isometry is a right inverse of the forward
Fourier isometry. This follows by symmetry from the left inverse property.
TODO: Use the dual inversion formula F(invF(g)) = g. -/
lemma invFourierL2_isometry_right_inv :
    ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      fourierL2_isometry (invFourierL2_isometry f) = f := by
  classical
  intro f
  -- Use density: L¹ ∩ L² is dense in L²
  have hDense : Dense L1L2Set := L1L2Set_dense
  -- The equalizer {f | F(invF(f)) = f} is closed
  have hClosed : IsClosed {f : Lp ℂ 2 (volume : Measure ℝ) |
      fourierL2_isometry (invFourierL2_isometry f) = f} := by
    apply isClosed_eq
    · exact (fourierL2_isometry.continuous.comp invFourierL2_isometry.continuous)
    · exact continuous_id
  -- It suffices to show the equalizer contains the dense subset L¹ ∩ L²
  suffices h : ∀ (g : ℝ → ℂ) (hg_L1 : Integrable g) (hg_L2 : MemLp g 2 volume),
      fourierL2_isometry (invFourierL2_isometry (hg_L2.toLp g)) = hg_L2.toLp g by
    -- Apply density
    have hContains : L1L2Set ⊆ {f : Lp ℂ 2 (volume : Measure ℝ) |
        fourierL2_isometry (invFourierL2_isometry f) = f} := by
      intro x ⟨g, hg_L1, hg_L2, hg_eq⟩
      simp only [Set.mem_setOf_eq]
      subst hg_eq
      exact h g hg_L1 hg_L2
    apply closure_minimal hContains hClosed (hDense.closure_eq ▸ Set.mem_univ f)

  intro g hg_L1 hg_L2
  -- Step 1: Approximate g by Schwartz functions in L¹ ∩ L².
  obtain ⟨φ, hφ_L1, hφ_L2, hφ_tendsto_L1, hφ_tendsto_L2⟩ :=
    Frourio.exists_schwartz_L1_L2_approx g hg_L1 hg_L2

  -- Step 2: Show convergence of φ_n to g in L².
  have h_phi_to_g :
      Filter.Tendsto (fun n => (hφ_L2 n).toLp (φ n)) Filter.atTop (𝓝 (hg_L2.toLp g)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    convert hφ_tendsto_L2 using 1
    ext n
    rw [← eLpNorm_neg]
    rw [neg_sub]
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (hg_L2.toLp g) ((hφ_L2 n).toLp (φ n)),
                    MemLp.coeFn_toLp (hφ_L2 n),
                    MemLp.coeFn_toLp hg_L2] with x h_sub h_phi h_g
    simp only [Pi.sub_apply, h_g, h_phi]

  -- Step 3: Show convergence of invF(φ_n) to invF(g) in L².
  have h_invFphi_to_invFg : Filter.Tendsto (fun n => invFourierL2_isometry ((hφ_L2 n).toLp (φ n)))
      Filter.atTop (𝓝 (invFourierL2_isometry (hg_L2.toLp g))) :=
    (invFourierL2_isometry.continuous.tendsto (hg_L2.toLp g)).comp h_phi_to_g

  -- Step 4: Show that for Schwartz functions, F(invF(φ_n)) = φ_n.
  have h_F_invF_phi : ∀ n, fourierL2_isometry (invFourierL2_isometry ((hφ_L2 n).toLp (φ n)))
      = (hφ_L2 n).toLp (φ n) := by
    intro n
    let ψ := φ n
    -- invFourierL2_isometry agrees with invFourierL1L2_toLp on L¹ ∩ L²
    have h_inv_eq : invFourierL2_isometry ((hφ_L2 n).toLp ψ)
        = invFourierL1L2_toLp ψ (hφ_L1 n) (hφ_L2 n) := by
      apply invFourierL2_isometryCLM_choice_agree

    -- invFourierL1L2_toLp corresponds to the inverse Fourier integral
    -- Let invPsi = Real.fourierIntegralInv ψ
    let invPsi := fun t => Real.fourierIntegralInv (fun x => ψ x) t

    -- invPsi is in L2 because it's the inverse Fourier transform of a Schwartz function
    have h_invPsi_L2 : MemLp invPsi 2 volume := by
      have h_eq : invPsi = fun t => Real.fourierIntegral (fun x => ψ x) (-t) := by
          funext t; simp [invPsi, fourierIntegralInv_eq_fourierIntegral_neg]
      rw [h_eq]
      let hF_S : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ ψ
      have hF_L2 : MemLp hF_S 2 volume := hF_S.memLp 2
      have h_eq2 : (fun t => Real.fourierIntegral (fun x => ψ x) (-t)) = (fun t => hF_S (-t)) := by
        ext t
        show 𝓕 (fun x => ψ x) (-t) = hF_S (-t)
        simp only [hF_S]
        rfl
      rw [h_eq2]
      exact hF_L2.comp_measurePreserving (Measure.measurePreserving_neg volume)

    have h_inv_Lp_eq : invFourierL1L2_toLp ψ (hφ_L1 n) (hφ_L2 n) = h_invPsi_L2.toLp invPsi := by
      -- Both sides are toLp of the same function (invPsi), just with different MemLp proofs
      -- So they are equal in Lp
      apply Lp.ext (μ := volume)
      unfold invFourierL1L2_toLp
      -- The definition gives us some MemLp proof and toLp of (fun t => Real.fourierIntegralInv ψ t)
      -- which is exactly invPsi
      refine (MemLp.coeFn_toLp _).trans ?_
      refine (Filter.EventuallyEq.trans ?_ (MemLp.coeFn_toLp h_invPsi_L2).symm)
      filter_upwards with t
      -- Both are the same value: Real.fourierIntegralInv ψ t
      show Real.fourierIntegralInv (fun x => ψ x) t = invPsi t
      rfl

    rw [h_inv_eq, h_inv_Lp_eq]

    -- Now apply fourierL2_isometry
    -- Since invPsi is in L1 (it's Schwartz), we can use fourierL2_isometry_ae_eq_fourierIntegral

    have h_invPsi_L1 : Integrable invPsi volume := by
      have h_eq : invPsi = fun t => Real.fourierIntegral (fun x => ψ x) (-t) := by
        funext t; simp [invPsi, fourierIntegralInv_eq_fourierIntegral_neg]
      rw [h_eq]
      let hF_S : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ ψ
      have hF_L1 : Integrable hF_S volume := hF_S.integrable
      have h_eq2 : (fun t => Real.fourierIntegral (fun x => ψ x) (-t)) = (fun t => hF_S (-t)) := by
        ext t; rfl
      rw [h_eq2]
      have : Integrable (hF_S ∘ Neg.neg) volume := by
        have h_mp := Measure.measurePreserving_neg (volume : Measure ℝ)
        exact (h_mp.integrable_comp hF_L1.aestronglyMeasurable).mpr hF_L1
      exact this

    have h_F_inv_eq : fourierL2_isometry (h_invPsi_L2.toLp invPsi)
        = (fourierIntegral_memLp_L1_L2 h_invPsi_L1 h_invPsi_L2).toLp (fourierIntegral invPsi) := by
      apply Lp.ext (μ := volume)
      have h1 := fourierL2_isometry_ae_eq_fourierIntegral invPsi h_invPsi_L1 h_invPsi_L2
      have h2 := MemLp.coeFn_toLp (fourierIntegral_memLp_L1_L2 h_invPsi_L1 h_invPsi_L2)
      exact h1.trans h2.symm

    rw [h_F_inv_eq]

    -- Now show fourierIntegral invPsi = ψ
    apply Lp.ext (μ := volume)
    refine (MemLp.coeFn_toLp _).trans ?_
    refine (Filter.EventuallyEq.trans ?_ (MemLp.coeFn_toLp (hφ_L2 n)).symm)
    filter_upwards with t

    -- Prove fourierIntegral invPsi t = ψ t
    rw [← fourierIntegral_eq_real]
    have h_inv_eq_neg : invPsi = fun x => Real.fourierIntegral (fun s => ψ s) (-x) := by
       funext x; simp [invPsi, fourierIntegralInv_eq_fourierIntegral_neg]
    rw [h_inv_eq_neg]

    -- F(F(ψ) o neg)(t) = F(F(ψ))(-t)
    have h_comp_neg : Real.fourierIntegral (fun x => Real.fourierIntegral (fun s => ψ s) (-x)) t
        = Real.fourierIntegral (Real.fourierIntegral (fun s => ψ s)) (-t) := by
      simp only [Real.fourierIntegral, VectorFourier.fourierIntegral, smul_eq_mul]
      have h_map := Measure.measurePreserving_neg (volume : Measure ℝ)
      have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
      convert MeasurePreserving.integral_comp h_map h_emb
        (fun u => 𝐞 (-innerₗ ℝ u (-t)) * Real.fourierIntegral (fun s => ψ s) u) using 1
      congr 1
      ext x
      simp only [Function.comp_apply, innerₗ_apply]
      simp [inner]
      have h_smul : ∀ (c : Circle) (z : ℂ), c • z = (c : ℂ) * z := fun c z => rfl
      simp only [h_smul]
      congr 1
      simp only [Real.fourierIntegral, VectorFourier.fourierIntegral, innerₗ_apply]
      simp [inner]
      simp only [h_smul]

    rw [h_comp_neg]

    -- Use fourierIntegralInv_fourierIntegral_schwartz: invF(F(ψ)) = ψ
    -- invF(g)(x) = F(g)(-x)
    -- So F(F(ψ))(-t) = invF(F(ψ))(t) = ψ(t)
    have h_inv_inv : Real.fourierIntegral (Real.fourierIntegral (fun s => ψ s)) (-t) = ψ t := by
      have h := fourierIntegralInv_fourierIntegral_schwartz ψ
      have h_val := congr_fun h t
      simp only [fourierIntegralInv_eq_fourierIntegral_neg] at h_val
      rw [← h_val]
      congr 2
      ext ξ
      rw [fourierIntegral_eq_real]

    exact h_inv_inv

  -- Step 5: Conclusion by uniqueness of limits.
  -- LHS converges to F(invF(g))
  have h_lim_lhs :
      Filter.Tendsto (fun n => fourierL2_isometry (invFourierL2_isometry ((hφ_L2 n).toLp (φ n))))
      Filter.atTop (𝓝 (fourierL2_isometry (invFourierL2_isometry (hg_L2.toLp g)))) :=
    (fourierL2_isometry.continuous.tendsto _).comp h_invFphi_to_invFg

  -- RHS converges to g
  have h_lim_rhs :
      Filter.Tendsto (fun n => fourierL2_isometry (invFourierL2_isometry ((hφ_L2 n).toLp (φ n))))
      Filter.atTop (𝓝 (hg_L2.toLp g)) := by
    simp only [h_F_invF_phi]
    exact h_phi_to_g

  exact tendsto_nhds_unique h_lim_lhs h_lim_rhs

/-- Step 3: L² Fourier isometry equivalence.
The genuine construction of the inverse Fourier isometry and the proof that it
is inverse to `fourierL2_isometry`, making this a proper unitary operator
on L²(ℝ) as described in the Frourio papers (論文第III, IV).

**Theory (from 第IV論文)**:
The normalized scale group $\mathcal{U}^{(\sigma)}_t f(x) := e^{\sigma t} f(e^t x)$
is unitary on $H_\sigma$. The Mellin transform $U_\sigma: H_\sigma \to L^2(\mathbb{R})$
provides a unitary equivalence (ユニタリ同値) as stated in equation:
$$\boxed{\ U_\sigma: H_\sigma \to L^2(\mathbb{R})\ }$$
where $U_\sigma$ is the Fourier transform on the logarithmic scale.

**Implementation**:
This is constructed as a `LinearIsometryEquiv` by combining the forward
Fourier isometry `fourierL2_isometry` with its inverse `invFourierL2_isometry`,
and proving they satisfy the Fourier inversion formula on L²(ℝ). -/
noncomputable def fourierL2_linearIsometryEquiv :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  refine
    { toLinearEquiv :=
        { toFun := fourierL2_isometry
        , invFun := invFourierL2_isometry
        , left_inv := invFourierL2_isometry_left_inv
        , right_inv := invFourierL2_isometry_right_inv
        , map_add' := fun f g => by simp [LinearIsometry.map_add]
        , map_smul' := fun c f => by simp [LinearIsometry.map_smul] }
    , norm_map' := fun f => fourierL2_isometry_norm f }

/-- L² Fourier isometry equivalence on `Lp ℂ 2 (volume)`.
This is the Plancherel unitary on `L²(ℝ)`.

IMPLEMENTATION: Uses the three-step construction:
1. ✓ Fourier transform on L¹ ∩ L² (using fourier_plancherel_L1_L2)
2. ✓ Extension by continuity to all of L² (using l1_inter_l2_dense)
3. ✓ Bijectivity from inverse Fourier transform

The Fourier transform satisfies:
- For g ∈ L¹ ∩ L², (FourierL2_equiv g) has a.e. representative τ ↦ fourierIntegral g τ
- Plancherel identity: ‖FourierL2_equiv g‖₂ = ‖g‖₂
- Inverse: (FourierL2_equiv)^(-1) is the inverse Fourier transform
-/
noncomputable def FourierL2_equiv :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  fourierL2_linearIsometryEquiv

/-- The rescaling function τ ↦ -τ / (2π) used in the Mellin-Fourier correspondence. -/
noncomputable def rescaleMap (τ : ℝ) : ℝ := -τ / (2 * Real.pi)

/-- The inverse of the rescaling function: τ ↦ -2πτ -/
noncomputable def rescaleMapInv (τ : ℝ) : ℝ := -2 * Real.pi * τ

lemma rescaleMap_inv_left (τ : ℝ) : rescaleMapInv (rescaleMap τ) = τ := by
  unfold rescaleMap rescaleMapInv
  have h2π_ne : (2 * Real.pi) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  field_simp [h2π_ne]

lemma rescaleMap_inv_right (τ : ℝ) : rescaleMap (rescaleMapInv τ) = τ := by
  unfold rescaleMap rescaleMapInv
  have h2π_ne : (2 * Real.pi) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  field_simp [h2π_ne]

/-- The Jacobian factor |d(rescaleMap)/dτ| = 1/(2π) -/
noncomputable def rescaleJacobian : ℝ := 1 / (2 * Real.pi)

lemma rescaleJacobian_pos : 0 < rescaleJacobian := by
  unfold rescaleJacobian
  apply div_pos
  · norm_num
  · exact mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos

/-- The normalization constant for the rescaling transformation to be an L² isometry.
Since the Jacobian of τ ↦ -τ/(2π) has absolute value 1/(2π), we need √(2π) to preserve norms. -/
noncomputable def rescaleNorm : ℝ := Real.sqrt (2 * Real.pi)

lemma rescaleNorm_pos : 0 < rescaleNorm := by
  unfold rescaleNorm
  apply Real.sqrt_pos.mpr
  apply mul_pos
  · norm_num
  · exact Real.pi_pos

lemma rescaleNorm_sq : rescaleNorm ^ 2 = 2 * Real.pi := by
  unfold rescaleNorm
  rw [sq]
  rw [Real.mul_self_sqrt]
  apply mul_nonneg
  · norm_num
  · exact Real.pi_pos.le

lemma rescaleNorm_inv : rescaleNorm⁻¹ = Real.sqrt (rescaleJacobian) := by
  unfold rescaleNorm rescaleJacobian
  have h2π_pos : 0 < 2 * Real.pi := mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos
  have h_sqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr h2π_pos
  rw [inv_eq_one_div, one_div]
  rw [show (Real.sqrt (2 * Real.pi))⁻¹ = Real.sqrt ((2 * Real.pi)⁻¹) by
    rw [Real.sqrt_inv]]
  congr 1
  rw [inv_eq_one_div]

lemma rescaleMap_measurable : Measurable rescaleMap := by
  unfold rescaleMap
  apply Measurable.div_const
  exact measurable_id.neg

lemma rescaleMap_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving rescaleMap
      (volume : Measure ℝ) (volume : Measure ℝ) := by
  classical
  -- View `rescaleMap` as multiplication by a nonzero constant `a`.
  let a : ℝ := - (2 * Real.pi)⁻¹
  have h_rescale_eq_mul : rescaleMap = fun t : ℝ => a * t := by
    funext t
    unfold rescaleMap a
    -- both sides reduce to `-(t * (2 * Real.pi)⁻¹)`
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, neg_mul, mul_neg]
  -- Pushforward of Lebesgue measure under `rescaleMap`.
  have ha_ne : a ≠ 0 := by
    have h2π_ne : (2 * Real.pi : ℝ) ≠ 0 := by
      exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
    have ha' : (2 * Real.pi : ℝ)⁻¹ ≠ 0 := inv_ne_zero h2π_ne
    exact neg_ne_zero.mpr ha'
  have h_map_rescale :
      Measure.map rescaleMap (volume : Measure ℝ)
        = ENNReal.ofReal (abs a⁻¹) • (volume : Measure ℝ) := by
    have h_map_mul :
        Measure.map (fun t : ℝ => a * t) (volume : Measure ℝ)
          = ENNReal.ofReal (abs a⁻¹) • (volume : Measure ℝ) :=
      map_volume_mul_left (a := a) ha_ne
    simpa [h_rescale_eq_mul] using h_map_mul
  -- Absolute continuity of the pushforward measure.
  have h_ac :
      (Measure.map rescaleMap (volume : Measure ℝ))
        ≪ (volume : Measure ℝ) := by
    have : ENNReal.ofReal (abs a⁻¹) • (volume : Measure ℝ) ≪ (volume : Measure ℝ) :=
      Measure.smul_absolutelyContinuous (μ := (volume : Measure ℝ))
    simpa [h_map_rescale] using this
  -- Package measurability and absolute continuity into a quasi-measure-preserving map.
  refine ⟨rescaleMap_measurable, ?_⟩
  simpa using h_ac

lemma rescaleMapInv_measurable : Measurable rescaleMapInv := by
  unfold rescaleMapInv
  exact measurable_id.const_mul (-2 * Real.pi)

lemma rescaleMapInv_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving rescaleMapInv
      (volume : Measure ℝ) (volume : Measure ℝ) := by
  classical
  -- View `rescaleMapInv` as multiplication by a nonzero constant `b`.
  let b : ℝ := -2 * Real.pi
  have h_rescale_eq_mul : rescaleMapInv = fun t : ℝ => b * t := by
    funext t
    unfold rescaleMapInv b
    -- both sides reduce to `-(2 * Real.pi * t)`
    simp [mul_comm, mul_left_comm, mul_assoc]
  -- Pushforward of Lebesgue measure under `rescaleMapInv`.
  have hb_ne : b ≠ 0 := by
    -- b = (-2) * π, so nonzero since both factors are nonzero
    simpa [b] using
      mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) Real.pi_ne_zero
  have h_map_rescale :
      Measure.map rescaleMapInv (volume : Measure ℝ)
        = ENNReal.ofReal (abs b⁻¹) • (volume : Measure ℝ) := by
    have h_map_mul :
        Measure.map (fun t : ℝ => b * t) (volume : Measure ℝ)
          = ENNReal.ofReal (abs b⁻¹) • (volume : Measure ℝ) :=
      map_volume_mul_left (a := b) hb_ne
    simpa [h_rescale_eq_mul] using h_map_mul
  -- Absolute continuity of the pushforward measure.
  have h_ac :
      (Measure.map rescaleMapInv (volume : Measure ℝ))
        ≪ (volume : Measure ℝ) := by
    have : ENNReal.ofReal (abs b⁻¹) • (volume : Measure ℝ) ≪ (volume : Measure ℝ) :=
      Measure.smul_absolutelyContinuous (μ := (volume : Measure ℝ))
    simpa [h_map_rescale] using this
  -- Package measurability and absolute continuity into a quasi-measure-preserving map.
  refine ⟨rescaleMapInv_measurable, ?_⟩
  simpa using h_ac

lemma rescaleMap_continuous : Continuous rescaleMap := by
  unfold rescaleMap
  continuity

lemma rescaleMapInv_continuous : Continuous rescaleMapInv := by
  unfold rescaleMapInv
  continuity

/-- The composition `g ∘ rescaleMap` preserves L² membership (up to normalization).
Since rescaleMap has Jacobian `1/(2π)`, the L² norm changes by a factor of `√(2π)`.

This is a key technical lemma that requires:
1. Proving AE strong measurability of the composition
2. Applying the change of variables formula for integrals
3. Using the Jacobian determinant to relate the norms

The full proof would use Measure.map and the pushforward properties of rescaleMap.
-/
lemma memLp_comp_rescaleMap {g : ℝ → ℂ} (hg : MeasureTheory.MemLp g 2 volume) :
    MeasureTheory.MemLp (g ∘ rescaleMap) 2 volume := by
  classical
  -- We view `rescaleMap` as multiplication by a nonzero constant `a`.
  let a : ℝ := - (2 * Real.pi)⁻¹
  have h_rescale_eq_mul : rescaleMap = fun t : ℝ => a * t := by
    funext t
    unfold rescaleMap a
    -- both sides reduce to `-(t * (2 * Real.pi)⁻¹)`
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, neg_mul, mul_neg]
  -- Pushforward of Lebesgue measure under `rescaleMap`.
  have ha_ne : a ≠ 0 := by
    have h2π_ne : (2 * Real.pi : ℝ) ≠ 0 := by
      exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
    have ha' : (2 * Real.pi : ℝ)⁻¹ ≠ 0 := inv_ne_zero h2π_ne
    exact neg_ne_zero.mpr ha'
  have h_map_rescale :
      Measure.map rescaleMap (volume : Measure ℝ)
        = ENNReal.ofReal (abs a⁻¹) • (volume : Measure ℝ) := by
    have h_map_mul :
        Measure.map (fun t : ℝ => a * t) (volume : Measure ℝ)
          = ENNReal.ofReal (abs a⁻¹) • (volume : Measure ℝ) :=
      map_volume_mul_left (a := a) ha_ne
    simpa [h_rescale_eq_mul] using h_map_mul
  -- From `g ∈ L²(volume)` deduce `g ∈ L²(map rescaleMap volume)` using the measure scaling.
  have hg_smul :
      MeasureTheory.MemLp g 2 (Measure.map rescaleMap (volume : Measure ℝ)) := by
    -- `MemLp.smul_measure` with `μ := volume`.
    have hg_smul' :
        MeasureTheory.MemLp g 2
          (ENNReal.ofReal (abs a⁻¹) • (volume : Measure ℝ)) :=
      (MeasureTheory.MemLp.smul_measure
        (μ := (volume : Measure ℝ)) (p := 2) (f := g)
        hg (by simp)) -- `ENNReal.ofReal _ ≠ ∞`
    simpa [h_map_rescale] using hg_smul'
  -- Now use the general `memLp_map_measure_iff` for the map `rescaleMap`.
  have hg_aestrong :
      AEStronglyMeasurable g (Measure.map rescaleMap (volume : Measure ℝ)) :=
    hg_smul.aestronglyMeasurable
  -- Apply the equivalence `MemLp g (map f μ) ↔ MemLp (g ∘ f) μ`.
  have :=
    (MeasureTheory.memLp_map_measure_iff
      (μ := (volume : Measure ℝ))
      (f := rescaleMap) (g := g)
      hg_aestrong rescaleMap_measurable.aemeasurable).1 hg_smul
  simpa [Function.comp] using this

/-- The composition `h ∘ rescaleMapInv` preserves L² membership (up to normalization).

Similar to `memLp_comp_rescaleMap`, but for the inverse transformation.
The Jacobian of rescaleMapInv is 2π, so the norm changes by a factor of 1/√(2π).
-/
lemma memLp_comp_rescaleMapInv {h : ℝ → ℂ} (hh : MeasureTheory.MemLp h 2 volume) :
    MeasureTheory.MemLp (h ∘ rescaleMapInv) 2 volume := by
  classical
  -- View `rescaleMapInv` as multiplication by a nonzero constant `b`.
  let b : ℝ := -2 * Real.pi
  have h_rescale_eq_mul : rescaleMapInv = fun t : ℝ => b * t := by
    funext t
    unfold rescaleMapInv b
    -- both sides reduce to `-(2 * Real.pi * t)`
    simp [mul_comm, mul_left_comm, mul_assoc]
  -- Pushforward of Lebesgue measure under `rescaleMapInv`.
  have h2π_ne : (2 * Real.pi : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  have hb_ne : b ≠ 0 := by
    -- b = (-2) * π, so nonzero since both factors are nonzero
    simpa [b] using
      mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) Real.pi_ne_zero
  have h_map_rescale :
      Measure.map rescaleMapInv (volume : Measure ℝ)
        = ENNReal.ofReal (abs b⁻¹) • (volume : Measure ℝ) := by
    have h_map_mul :
        Measure.map (fun t : ℝ => b * t) (volume : Measure ℝ)
          = ENNReal.ofReal (abs b⁻¹) • (volume : Measure ℝ) :=
      map_volume_mul_left (a := b) hb_ne
    simpa [h_rescale_eq_mul] using h_map_mul
  -- From `h ∈ L²(volume)` deduce `h ∈ L²(map rescaleMapInv volume)` using the measure scaling.
  have hh_smul :
      MeasureTheory.MemLp h 2 (Measure.map rescaleMapInv (volume : Measure ℝ)) := by
    have hh_smul' :
        MeasureTheory.MemLp h 2
          (ENNReal.ofReal (abs b⁻¹) • (volume : Measure ℝ)) :=
      (MeasureTheory.MemLp.smul_measure
        (μ := (volume : Measure ℝ)) (p := 2) (f := h)
        hh (by simp)) -- `ENNReal.ofReal _ ≠ ∞`
    simpa [h_map_rescale] using hh_smul'
  -- Now use the general `memLp_map_measure_iff` for the map `rescaleMapInv`.
  have hh_aestrong :
      AEStronglyMeasurable h (Measure.map rescaleMapInv (volume : Measure ℝ)) :=
    hh_smul.aestronglyMeasurable
  have :=
    (MeasureTheory.memLp_map_measure_iff
      (μ := (volume : Measure ℝ))
      (f := rescaleMapInv) (g := h)
      hh_aestrong rescaleMapInv_measurable.aemeasurable).1 hh_smul
  simpa [Function.comp] using this

/-- Apply rescaling to a function: `g ↦ rescaleNorm⁻¹ • (g ∘ rescaleMap)`.
This is the pointwise operation underlying the forward rescaling map. -/
noncomputable def rescaleForward_fun (g : ℝ → ℂ) : ℝ → ℂ :=
  fun τ => rescaleNorm⁻¹ • (g (rescaleMap τ))

/-- Apply inverse rescaling to a function: `h ↦ rescaleNorm • (h ∘ rescaleMapInv)`.
This is the pointwise operation underlying the inverse rescaling map. -/
noncomputable def rescaleInverse_fun (h : ℝ → ℂ) : ℝ → ℂ :=
  fun τ => rescaleNorm • (h (rescaleMapInv τ))

lemma rescaleForward_fun_memLp {g : ℝ → ℂ} (hg : MeasureTheory.MemLp g 2 volume) :
    MeasureTheory.MemLp (rescaleForward_fun g) 2 volume := by
  unfold rescaleForward_fun
  -- The scalar multiplication by rescaleNorm⁻¹ preserves L² membership
  have h_comp := memLp_comp_rescaleMap hg
  -- Apply scalar multiplication
  simpa [Function.comp] using
    (MeasureTheory.MemLp.const_smul
      (μ := (volume : Measure ℝ)) (p := 2)
      (f := g ∘ rescaleMap) h_comp (rescaleNorm⁻¹ : ℂ))

lemma rescaleInverse_fun_memLp {h : ℝ → ℂ} (hh : MeasureTheory.MemLp h 2 volume) :
    MeasureTheory.MemLp (rescaleInverse_fun h) 2 volume := by
  unfold rescaleInverse_fun
  have h_comp := memLp_comp_rescaleMapInv hh
  simpa [Function.comp] using
    (MeasureTheory.MemLp.const_smul
      (μ := (volume : Measure ℝ)) (p := 2)
      (f := h ∘ rescaleMapInv) h_comp (rescaleNorm : ℂ))

lemma rescaleForward_fun_rescaleInverse_fun (g : ℝ → ℂ) :
    rescaleForward_fun (rescaleInverse_fun g) = g := by
  classical
  funext τ
  -- Expand both definitions and use that rescaleMapInv ∘ rescaleMap = id.
  simp only [rescaleForward_fun, rescaleInverse_fun, Function.comp,
    rescaleMap_inv_left, smul_smul, Circle.smul_def]
  field_simp [ne_of_gt rescaleNorm_pos]

lemma rescaleNorm_inv_sq :
    (rescaleNorm⁻¹ : ℝ) ^ 2 = rescaleJacobian := by
  -- rescaleNorm² = 2π, so its inverse square is 1/(2π) = rescaleJacobian.
  unfold rescaleJacobian
  have h2π_ne : (2 * Real.pi : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  have h_rescale_sq : rescaleNorm ^ 2 = 2 * Real.pi := rescaleNorm_sq
  -- Take inverses on both sides and simplify.
  have h_inv_sq :
      (rescaleNorm ^ 2)⁻¹ = (2 * Real.pi : ℝ)⁻¹ := by
    simp [h_rescale_sq]
  -- Rewrite (rescaleNorm⁻¹)² as (rescaleNorm²)⁻¹.
  have h_left :
      (rescaleNorm⁻¹ : ℝ) ^ 2 = (rescaleNorm ^ 2)⁻¹ := by
    rw [inv_pow]
  -- Combine the equalities.
  have h' : (rescaleNorm⁻¹ : ℝ) ^ 2 = (2 * Real.pi : ℝ)⁻¹ := by
    simpa [h_left] using h_inv_sq
  -- Finish: (2π)⁻¹ = 1 / (2π).
  simpa [one_div] using h'

lemma rescaleForward_fun_integral_sq
    (g : ℝ → ℂ) (hg : MeasureTheory.MemLp g 2 volume) :
    ∫ τ : ℝ, ‖rescaleForward_fun g τ‖ ^ 2 ∂(volume : Measure ℝ)
      = ∫ t : ℝ, ‖g t‖ ^ 2 ∂(volume : Measure ℝ) := by
  classical
  -- Abbreviations for the squared norms before and after rescaling.
  set Fτ : ℝ → ℝ := fun τ => ‖rescaleForward_fun g τ‖ ^ 2 with hFτ_def
  set Fξ : ℝ → ℝ := fun t => ‖g t‖ ^ 2 with hFξ_def

  -- Step 1: integrability of Fξ and Fτ (since g and rescaleForward_fun g are in L²).
  have hMem_g : MeasureTheory.MemLp g 2 (volume : Measure ℝ) := hg
  have h_int_Fξ :
      Integrable Fξ (volume : Measure ℝ) := by
    -- MemLp with p = 2 implies integrable of the square of the norm.
    have h_int_sq :=
      (memLp_two_iff_integrable_sq_norm (μ := volume) (f := g) hMem_g.1).1 hMem_g
    simpa [Fξ, hFξ_def, pow_two] using h_int_sq

  have hMem_rescaled :
      MeasureTheory.MemLp (rescaleForward_fun g) 2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp hg
  have h_int_Fτ :
      Integrable Fτ (volume : Measure ℝ) := by
    have h_int_sq :=
      (memLp_two_iff_integrable_sq_norm
        (μ := volume) (f := rescaleForward_fun g) hMem_rescaled.1).1
        hMem_rescaled
    simpa [Fτ, hFτ_def, pow_two] using h_int_sq

  -- Step 2: nonnegativity of the squared norms.
  have h_nonneg_Fξ : 0 ≤ᵐ[volume] fun t => Fξ t :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have h_nonneg_Fτ : 0 ≤ᵐ[volume] fun τ => Fτ τ :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)

  -- Step 3: identify the real integrals with toReal of appropriate lintegrals.
  have hOfReal_Fξ :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_Fξ h_nonneg_Fξ
  have hOfReal_Fτ :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_Fτ h_nonneg_Fτ

  have hIntegral_Fξ_eq :
      ∫ t : ℝ, Fξ t ∂(volume : Measure ℝ)
        = (∫⁻ t : ℝ, ENNReal.ofReal (Fξ t) ∂(volume : Measure ℝ)).toReal := by
    have := congrArg ENNReal.toReal hOfReal_Fξ
    have hge :
        0 ≤ ∫ t : ℝ, Fξ t ∂(volume : Measure ℝ) :=
      integral_nonneg (fun _ => sq_nonneg _)
    simpa [hge, ENNReal.toReal_ofReal] using this

  have hIntegral_Fτ_eq :
      ∫ τ : ℝ, Fτ τ ∂(volume : Measure ℝ)
        = (∫⁻ τ : ℝ, ENNReal.ofReal (Fτ τ) ∂(volume : Measure ℝ)).toReal := by
    have := congrArg ENNReal.toReal hOfReal_Fτ
    have hge :
        0 ≤ ∫ τ : ℝ, Fτ τ ∂(volume : Measure ℝ) :=
      integral_nonneg (fun _ => sq_nonneg _)
    simpa [hge, ENNReal.toReal_ofReal] using this

  -- Step 4: compute the ENNReal integrals and show they are equal.
  -- 4a. Express `ofReal (Fτ τ)` in terms of `ofReal (‖g (rescaleMap τ)‖^2)`
  have h_ofReal_Fτ :
      (fun τ : ℝ => ENNReal.ofReal (Fτ τ))
        = fun τ : ℝ =>
            ENNReal.ofReal rescaleJacobian
              * ENNReal.ofReal (‖g (rescaleMap τ)‖ ^ 2) := by
    funext τ
    simp only [Fτ, hFτ_def, rescaleForward_fun]
    -- Expand the norm of scalar multiplication
    have h_expand : ‖rescaleNorm⁻¹ • g (rescaleMap τ)‖ ^ 2
        = (rescaleNorm⁻¹ ^ 2) * ‖g (rescaleMap τ)‖ ^ 2 := by
      have h_rescale_norm : ‖(rescaleNorm : ℝ)‖ = rescaleNorm := by
        exact _root_.abs_of_nonneg (le_of_lt rescaleNorm_pos)
      have h1 : ‖(rescaleNorm⁻¹ : ℂ)‖ = rescaleNorm⁻¹ := by
        rw [norm_inv, Complex.norm_real, h_rescale_norm]
      have h2 : ‖(rescaleNorm⁻¹ : ℝ)‖ = rescaleNorm⁻¹ := by
        rw [norm_inv, h_rescale_norm]
      calc ‖rescaleNorm⁻¹ • g (rescaleMap τ)‖ ^ 2
          = ‖(rescaleNorm⁻¹ : ℝ)‖ ^ 2 * ‖g (rescaleMap τ)‖ ^ 2 := by
            rw [norm_smul, mul_pow]
        _ = rescaleNorm⁻¹ ^ 2 * ‖g (rescaleMap τ)‖ ^ 2 := by rw [h2]
    rw [h_expand, rescaleNorm_inv_sq, rescaleJacobian, one_div, pow_two]
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity))]

  have h_ofReal_Fξ :
      (fun t : ℝ => ENNReal.ofReal (Fξ t))
        = fun t : ℝ => ENNReal.ofReal (‖g t‖ ^ 2) := by
    funext t
    simp [Fξ, hFξ_def]

  -- 4b. Change variables τ ↦ rescaleMap τ on the lintegral side.
  have h_g_aesm : AEStronglyMeasurable g (volume : Measure ℝ) :=
    hMem_g.aestronglyMeasurable
  have h_f_aemeas :
      AEMeasurable (fun t : ℝ => ENNReal.ofReal (‖g t‖ ^ 2))
        (volume : Measure ℝ) := by
    have h_norm_sq :
        AEMeasurable (fun t : ℝ => ‖g t‖ ^ 2) (volume : Measure ℝ) :=
      (h_g_aesm.aemeasurable.norm.pow_const 2)
    exact h_norm_sq.ennreal_ofReal

  -- View rescaleMap as multiplication by a constant a.
  let a : ℝ := - (2 * Real.pi)⁻¹
  have h_rescale_eq_mul : rescaleMap = fun t : ℝ => a * t := by
    funext t
    unfold rescaleMap a
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, neg_mul, mul_neg]

  have ha_ne : a ≠ 0 := by
    have h2π_ne : (2 * Real.pi : ℝ) ≠ 0 := by
      exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
    have ha' : (2 * Real.pi : ℝ)⁻¹ ≠ 0 := inv_ne_zero h2π_ne
    exact neg_ne_zero.mpr ha'

  -- Apply the general 1D scaling lemma for lintegrals.
  have h_scale :
      ∫⁻ τ : ℝ, ENNReal.ofReal (‖g (rescaleMap τ)‖ ^ 2) ∂(volume : Measure ℝ)
        = ENNReal.ofReal (abs (a⁻¹))
            * ∫⁻ t : ℝ, ENNReal.ofReal (‖g t‖ ^ 2) ∂(volume : Measure ℝ) := by
    have :=
      Measure.lintegral_comp_mul_left
        (a := a) ha_ne
        (f := fun t : ℝ => ENNReal.ofReal (‖g t‖ ^ 2)) h_f_aemeas
    -- The lemma is stated for the map `x ↦ a * x`; rewrite rescaleMap accordingly.
    simpa [h_rescale_eq_mul] using this

  -- 4c. Put everything together at the ENNReal level.
  have h_lint_Fτ :
      ∫⁻ τ : ℝ, ENNReal.ofReal (Fτ τ) ∂(volume : Measure ℝ)
        = ENNReal.ofReal rescaleJacobian
            * (ENNReal.ofReal (abs (a⁻¹))
                * ∫⁻ t : ℝ, ENNReal.ofReal (‖g t‖ ^ 2) ∂(volume : Measure ℝ)) := by
    -- Use the expression of `ofReal Fτ` and factor out the constant rescaleJacobian.
    have :
        ∫⁻ τ : ℝ, ENNReal.ofReal (Fτ τ) ∂(volume : Measure ℝ)
          = ENNReal.ofReal rescaleJacobian
              * ∫⁻ τ : ℝ, ENNReal.ofReal (‖g (rescaleMap τ)‖ ^ 2)
                  ∂(volume : Measure ℝ) := by
      -- Factor out the constant using `lintegral_const_mul'`.
      have h_eq :
          (fun τ : ℝ => ENNReal.ofReal (Fτ τ))
            = fun τ : ℝ =>
                ENNReal.ofReal rescaleJacobian
                  * ENNReal.ofReal (‖g (rescaleMap τ)‖ ^ 2) := h_ofReal_Fτ
      simp [h_eq, lintegral_const_mul']  -- uses `ENNReal.ofReal rescaleJacobian ≠ ∞`
    -- Substitute the scaling identity for the inner lintegral.
    simpa [this, mul_assoc] using congrArg (fun z =>
      ENNReal.ofReal rescaleJacobian * z) h_scale

  -- Evaluate the product of scaling constants:
  --   rescaleJacobian * |a⁻¹| = 1.
  have h_const_one :
      ENNReal.ofReal rescaleJacobian * ENNReal.ofReal (abs (a⁻¹))
        = (1 : ℝ≥0∞) := by
    -- Compute a⁻¹ explicitly: a = - (2π)⁻¹, so a⁻¹ = - 2π.
    have h_inv : (a⁻¹ : ℝ) = -(2 * Real.pi) := by
      unfold a
      have h2π_ne : (2 * Real.pi : ℝ) ≠ 0 :=
        mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
      rw [neg_inv, inv_inv]
    have h_abs :
        abs (a⁻¹ : ℝ) = 2 * Real.pi := by
      have hpos : 0 ≤ 2 * Real.pi := by
        have : 0 ≤ (2 : ℝ) := by norm_num
        exact mul_nonneg this Real.pi_pos.le

      simp [h_inv, abs_neg, abs_of_nonneg hpos]
    -- Now use that rescaleJacobian = 1/(2π).
    have h_mul :
        rescaleJacobian * abs (a⁻¹ : ℝ)
          = (1 : ℝ) := by
      unfold rescaleJacobian
      have h2π_ne : (2 * Real.pi : ℝ) ≠ 0 :=
        mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
      -- 1/(2π) * (2π) = 1.
      rw [h_abs]
      field_simp
    -- Lift the real identity to ENNReal via ofReal.
    have h_nonneg :
        0 ≤ rescaleJacobian * abs (a⁻¹ : ℝ) := by
      have h1 : 0 ≤ rescaleJacobian := rescaleJacobian_pos.le
      have h2 : 0 ≤ abs (a⁻¹ : ℝ) := by exact abs_nonneg _
      exact mul_nonneg h1 h2
    -- Use ofReal_mul and the fact that the product equals 1.
    have :
        ENNReal.ofReal (rescaleJacobian * abs (a⁻¹ : ℝ))
          = (1 : ℝ≥0∞) := by
      -- Since the product is exactly 1 and nonnegative.
      have h1' : rescaleJacobian * abs (a⁻¹ : ℝ) = (1 : ℝ) := h_mul
      have h1_nonneg : 0 ≤ (1 : ℝ) := by norm_num
      simp [h1', ENNReal.ofReal_one]
    -- Rewrite the product of ofReal's as ofReal of the product.
    have h_prod :
        ENNReal.ofReal rescaleJacobian * ENNReal.ofReal (abs (a⁻¹ : ℝ))
          = ENNReal.ofReal (rescaleJacobian * abs (a⁻¹ : ℝ)) := by
      have h1 : 0 ≤ rescaleJacobian :=
        rescaleJacobian_pos.le
      have h2 : 0 ≤ abs (a⁻¹ : ℝ) :=
        abs_nonneg _
      simp [ENNReal.ofReal_mul, h1, h2]
    simpa [h_prod] using this

  -- Replace the constants using h_const_one.
  have h_lint_Fτ_simpl :
      ∫⁻ τ : ℝ, ENNReal.ofReal (Fτ τ) ∂(volume : Measure ℝ)
        = ∫⁻ t : ℝ, ENNReal.ofReal (‖g t‖ ^ 2) ∂(volume : Measure ℝ) := by
    -- Expand the right-hand side of h_lint_Fτ and simplify constants.
    have h := h_lint_Fτ
    -- h has the form ofReal(J) * (ofReal |a⁻¹| * lintegral) = ...
    -- Use associativity and the fact that the product of constants is 1.
    -- (ofReal rescaleJacobian) * (ofReal |a⁻¹|) = 1, so we can cancel it.
    -- First rewrite the scalar product explicitly.
    have h_rw :
        ENNReal.ofReal rescaleJacobian
            * (ENNReal.ofReal (abs (a⁻¹))
                * ∫⁻ t : ℝ, ENNReal.ofReal (‖g t‖ ^ 2) ∂volume)
          = (ENNReal.ofReal rescaleJacobian
              * ENNReal.ofReal (abs (a⁻¹)))
              * ∫⁻ t : ℝ, ENNReal.ofReal (‖g t‖ ^ 2) ∂volume := by
      simp [mul_assoc]
    -- Combine with the computation of the product of constants.
    have h_rw' :
        ENNReal.ofReal rescaleJacobian
            * (ENNReal.ofReal (abs (a⁻¹))
                * ∫⁻ t : ℝ, ENNReal.ofReal (‖g t‖ ^ 2) ∂volume)
          = ∫⁻ t : ℝ, ENNReal.ofReal (‖g t‖ ^ 2) ∂volume := by
      simp [h_rw, h_const_one, one_mul]
    simpa [h_rw'] using h

  -- 4d. Identify the ξ-side lintegral with Fξ.
  have h_lint_Fξ :
      ∫⁻ t : ℝ, ENNReal.ofReal (Fξ t) ∂(volume : Measure ℝ)
        = ∫⁻ t : ℝ, ENNReal.ofReal (‖g t‖ ^ 2) ∂(volume : Measure ℝ) := by
    simp [h_ofReal_Fξ]

  -- Step 5: convert back from lintegrals to real integrals.
  -- We have equality of the lintegrals, hence equality of the real integrals.
  have h_lint_eq :
      ∫⁻ τ : ℝ, ENNReal.ofReal (Fτ τ) ∂(volume : Measure ℝ)
        = ∫⁻ t : ℝ, ENNReal.ofReal (Fξ t) ∂(volume : Measure ℝ) := by
    simpa [h_lint_Fξ] using h_lint_Fτ_simpl

  -- Finally, compare the original real integrals via their toReal expressions.
  calc
    ∫ τ : ℝ, ‖rescaleForward_fun g τ‖ ^ 2 ∂(volume : Measure ℝ)
        = (∫⁻ τ : ℝ, ENNReal.ofReal (Fτ τ) ∂(volume : Measure ℝ)).toReal := by
          simpa [Fτ, hFτ_def] using hIntegral_Fτ_eq
    _ = (∫⁻ t : ℝ, ENNReal.ofReal (Fξ t) ∂(volume : Measure ℝ)).toReal := by
          simp [h_lint_eq]
    _ = ∫ t : ℝ, ‖g t‖ ^ 2 ∂(volume : Measure ℝ) := by
          simpa [Fξ, hFξ_def] using hIntegral_Fξ_eq.symm

lemma rescaleForward_fun_eLpNorm_eq
    (g : ℝ → ℂ) (hg : MeasureTheory.MemLp g 2 volume) :
    (eLpNorm (rescaleForward_fun g) 2 (volume : Measure ℝ)).toReal
      = (eLpNorm g 2 (volume : Measure ℝ)).toReal := by
  classical
  -- Express both eLpNorms via their squared integrals.
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by simp

  have h_mem_rescaled :
      MeasureTheory.MemLp (rescaleForward_fun g) 2 (volume : Measure ℝ) :=
    rescaleForward_fun_memLp hg

  -- General formula for eLpNorm at p = 2.
  have h_rescaled_eLp_eq :
      (eLpNorm (rescaleForward_fun g) 2 (volume : Measure ℝ)).toReal
        = (∫ τ : ℝ, ‖rescaleForward_fun g τ‖ ^ 2 ∂(volume : Measure ℝ))
            ^ (1 / 2 : ℝ) := by
    -- Adapt the argument from `mellin_fourier_parseval_connection`.
    have h₁ :=
      congrArg ENNReal.toReal
        (MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
          (f := rescaleForward_fun g) hp0 hp_top h_mem_rescaled)
    set B : ℝ :=
        (∫ τ : ℝ, ‖rescaleForward_fun g τ‖
              ^ ENNReal.toReal (2 : ℝ≥0∞) ∂(volume : Measure ℝ))
          ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ with hB
    have h_two : ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) := by simp
    have h_base_nonneg :
        0 ≤
          ∫ τ : ℝ, ‖rescaleForward_fun g τ‖
              ^ ENNReal.toReal (2 : ℝ≥0∞) ∂(volume : Measure ℝ) := by
      refine integral_nonneg ?_
      intro τ
      have := sq_nonneg ‖rescaleForward_fun g τ‖
      simpa [h_two, pow_two] using this
    have hB_nonneg : 0 ≤ B := by
      have h_rpow_nonneg :
          0 ≤
              (∫ τ : ℝ, ‖rescaleForward_fun g τ‖
                  ^ ENNReal.toReal (2 : ℝ≥0∞) ∂(volume : Measure ℝ))
                ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ :=
        Real.rpow_nonneg h_base_nonneg _
      simpa [B, hB] using h_rpow_nonneg
    have h_toReal_ofReal :
        (eLpNorm (rescaleForward_fun g) 2 (volume : Measure ℝ)).toReal
          = (ENNReal.ofReal B).toReal := by
      simpa [B, hB] using h₁
    have h_toReal :
        (eLpNorm (rescaleForward_fun g) 2 (volume : Measure ℝ)).toReal = B := by
      simpa [ENNReal.toReal_ofReal, hB_nonneg] using h_toReal_ofReal
    have hB_simpl :
        B = (∫ τ : ℝ, ‖rescaleForward_fun g τ‖ ^ 2 ∂(volume : Measure ℝ))
              ^ (1 / 2 : ℝ) := by
      simp [B, hB, h_two, one_div]
    simp [h_toReal, hB_simpl]

  have h_g_eLp_eq :
      (eLpNorm g 2 (volume : Measure ℝ)).toReal
        = (∫ t : ℝ, ‖g t‖ ^ 2 ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ) := by
    have h₁ :=
      congrArg ENNReal.toReal
        (MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume)
          (f := g) hp0 hp_top hg)
    set B : ℝ :=
        (∫ t : ℝ, ‖g t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂(volume : Measure ℝ))
          ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ with hB
    have h_two : ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) := by simp
    have h_base_nonneg :
        0 ≤ ∫ t : ℝ, ‖g t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂(volume : Measure ℝ) := by
      refine integral_nonneg ?_
      intro t
      have := sq_nonneg ‖g t‖
      simpa [h_two, pow_two] using this
    have hB_nonneg : 0 ≤ B := by
      have h_rpow_nonneg :
          0 ≤
              (∫ t : ℝ, ‖g t‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂(volume : Measure ℝ))
                ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ :=
        Real.rpow_nonneg h_base_nonneg _
      simpa [B, hB] using h_rpow_nonneg
    have h_toReal_ofReal :
        (eLpNorm g 2 (volume : Measure ℝ)).toReal
          = (ENNReal.ofReal B).toReal := by
      simpa [B, hB] using h₁
    have h_toReal :
        (eLpNorm g 2 (volume : Measure ℝ)).toReal = B := by
      simpa [ENNReal.toReal_ofReal, hB_nonneg] using h_toReal_ofReal
    have hB_simpl :
        B = (∫ t : ℝ, ‖g t‖ ^ 2 ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ) := by
      simp [B, hB, h_two, one_div]
    simp [h_toReal, hB_simpl]

  -- Use the integral identity from `rescaleForward_fun_integral_sq`.
  have h_int_eq :
      ∫ τ : ℝ, ‖rescaleForward_fun g τ‖ ^ 2 ∂(volume : Measure ℝ)
        = ∫ t : ℝ, ‖g t‖ ^ 2 ∂(volume : Measure ℝ) :=
    rescaleForward_fun_integral_sq g hg

  -- Conclude that the two eLpNorms coincide.
  calc
    (eLpNorm (rescaleForward_fun g) 2 (volume : Measure ℝ)).toReal
        = (∫ τ : ℝ, ‖rescaleForward_fun g τ‖ ^ 2 ∂(volume : Measure ℝ))
            ^ (1 / 2 : ℝ) := h_rescaled_eLp_eq
    _ = (∫ t : ℝ, ‖g t‖ ^ 2 ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ) := by
          simp [h_int_eq]
    _ = (eLpNorm g 2 (volume : Measure ℝ)).toReal := h_g_eLp_eq.symm

lemma rescaleInverse_fun_rescaleForward_fun (g : ℝ → ℂ) :
    rescaleInverse_fun (rescaleForward_fun g) = g := by
  classical
  funext τ
  -- Expand both definitions and use that rescaleMap ∘ rescaleMapInv = id.
  simp only [rescaleForward_fun, rescaleInverse_fun, Function.comp,
    rescaleMap_inv_right, smul_smul, Circle.smul_def]
  field_simp [ne_of_gt rescaleNorm_pos]

end ClassicalParseval

end Frourio
