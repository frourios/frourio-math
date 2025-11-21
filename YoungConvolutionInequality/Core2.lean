import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.LiminfLimsup
import YoungConvolutionInequality.Core1

noncomputable section

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter NNReal

section MapMeasureHelpers

variable {X : Type*} [MeasurableSpace X]

lemma map_le_smul_map_of_le_smul
    {T : X → X} (hT : Measurable T)
    (μ₁ μ₂ : Measure X) (c : ℝ≥0∞)
    (hμ₁_le : μ₁ ≤ c • μ₂) :
    Measure.map T μ₁ ≤ c • Measure.map T μ₂ := by
  intro S
  classical
  -- Replace S by a measurable superset for the right-hand measure.
  set S' : Set X := toMeasurable (c • Measure.map T μ₂) S with hS'_def
  have hS'_meas : MeasurableSet S' := measurableSet_toMeasurable _ _
  have hS_subset : S ⊆ S' := by
    simpa [S', hS'_def] using subset_toMeasurable (c • Measure.map T μ₂) S
  -- Monotonicity on the left to move from S to S'.
  have h_left_mono : (Measure.map T μ₁) S ≤ (Measure.map T μ₁) S' :=
    measure_mono hS_subset
  -- Evaluate both sides on the measurable set S' via the preimage.
  have h_core : (Measure.map T μ₁) S' ≤ (c • Measure.map T μ₂) S' := by
    -- Rewrite using map_apply and smul_apply on the measurable set S'.
    have hL : (Measure.map T μ₁) S' = μ₁ (T ⁻¹' S') := by
      simpa using Measure.map_apply (μ := μ₁) hT hS'_meas
    have hR : (c • Measure.map T μ₂) S' = (c • μ₂) (T ⁻¹' S') := by
      simp [Measure.smul_apply, Measure.map_apply (μ := μ₂) hT hS'_meas]
    -- Apply the assumed domination on the preimage.
    simpa [hL, hR] using hμ₁_le (T ⁻¹' S')
  -- Identify the right-hand side on S' with the original S.
  have h_right_eq : (c • Measure.map T μ₂) S' = (c • Measure.map T μ₂) S := by
    -- toMeasurable leaves the measure unchanged.
    simp [S', hS'_def]
  -- Chain the inequalities/equalities.
  calc
    (Measure.map T μ₁) S ≤ (Measure.map T μ₁) S' := h_left_mono
    _ ≤ (c • Measure.map T μ₂) S' := h_core
    _ = (c • Measure.map T μ₂) S := h_right_eq

end MapMeasureHelpers

/-!
Finiteness lemma for the product lintegral of a shifted product kernel on a
finite measure. This abstracts the local goal `hH_lt_top` used in the partial
measure argument, so the main proof can refer to a single lemma.
-/

-- (Moved finiteness helper lemma after additive structure is introduced.)

variable {G : Type*}
variable [MeasurableSpace G]
variable (μ : Measure G) [SFinite μ]
variable [NormedAddCommGroup G]
variable [μ.IsAddRightInvariant] [μ.IsNegInvariant]
variable [MeasurableAdd₂ G] [MeasurableNeg G]

/-- Change-of-variables identity for the trilinear kernel appearing in Young's inequality.
This lemma records the common goal needed in several places where we compare
the shear-transformed kernel with the standard |f x|·|g y|·|φ (x + y)| kernel.
The proof will be supplied later in this file alongside the finiteness analysis. -/
lemma lintegral_triple_kernel_shear
    (f g φ : G → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ)
    (hφ : AEStronglyMeasurable φ μ) :
    ∫⁻ p : G × G,
        ENNReal.ofReal (|f (p.2 - p.1)| * |g p.1| * |φ p.2|) ∂(μ.prod μ)
      = ∫⁻ p : G × G,
          ENNReal.ofReal (|f p.1| * |g p.2| * |φ (p.1 + p.2)|) ∂(μ.prod μ) := by
  classical
  -- Define the shear map τ(y, x) = (x − y, y) after swapping coordinates.
  set τ : G × G → G × G := fun q => (q.2 - q.1, q.1)
  have hτ_pres : MeasurePreserving τ (μ.prod μ) (μ.prod μ) := by
    have h_sub :
        MeasurePreserving (fun q : G × G => (q.1 - q.2, q.2)) (μ.prod μ) (μ.prod μ) :=
      measurePreserving_sub_prod (μ := μ) (ν := μ)
    have h_swap :
        MeasurePreserving Prod.swap (μ.prod μ) (μ.prod μ) :=
      (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    simpa [τ, Prod.swap] using h_sub.comp h_swap
  -- Right-hand side kernel on G × G.
  set F : G × G → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (|f p.1| * |g p.2| * |φ (p.1 + p.2)|)
  -- A.E.-measurability of F on μ × μ.
  have hf_ae : AEMeasurable f μ := hf.aemeasurable
  have hg_ae : AEMeasurable g μ := hg.aemeasurable
  have hφ_ae : AEMeasurable φ μ := hφ.aemeasurable
  have hF_aemeas_prod : AEMeasurable F (μ.prod μ) := by
    -- Build AEMeasurable pieces |f p.1|, |g p.2|, |φ (p.1 + p.2)| and multiply.
    have hf_prod :
        AEMeasurable (fun p : G × G => |f p.1|) (μ.prod μ) :=
      (hf_ae.norm).comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
    have hg_prod :
        AEMeasurable (fun p : G × G => |g p.2|) (μ.prod μ) :=
      (hg_ae.norm).comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
    have hφ_sum :
        AEMeasurable (fun p : G × G => |φ (p.1 + p.2)|) (μ.prod μ) := by
      classical
      have h_add : Measurable (fun p : G × G => p.1 + p.2) :=
        measurable_fst.add measurable_snd
      set φ0 : G → ℝ := hφ.mk φ with hφ0_def
      have hφ0_meas : StronglyMeasurable φ0 := hφ.stronglyMeasurable_mk
      have h0_sm : StronglyMeasurable (fun p : G × G => φ0 (p.1 + p.2)) :=
        hφ0_meas.comp_measurable h_add
      -- Quasi-measure-preserving addition map via subtraction shear + negation.
      have h_add_qmp :
          Measure.QuasiMeasurePreserving (fun p : G × G => p.1 + p.2)
            (μ.prod μ) μ := by
        have h_sub_prod :
            MeasurePreserving (fun q : G × G => (q.1 - q.2, q.2))
              (μ.prod μ) (μ.prod μ) :=
          measurePreserving_sub_prod (μ := μ) (ν := μ)
        have h_fst_qmp :
            Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
              (μ.prod μ) μ :=
          MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
        have h_sub_qmp :
            Measure.QuasiMeasurePreserving (fun q : G × G => q.1 - q.2)
              (μ.prod μ) μ := by
          simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
            using h_fst_qmp.comp h_sub_prod.quasiMeasurePreserving
        have h_neg_prod :
            MeasurePreserving (fun q : G × G => (q.1, -q.2))
              (μ.prod μ) (μ.prod μ) := by
          simpa using
            (MeasureTheory.MeasurePreserving.prod
              (μa := μ) (μb := μ) (μc := μ) (μd := μ)
              (hf := MeasureTheory.MeasurePreserving.id (μ := μ))
              (hg := Measure.measurePreserving_neg (μ := μ)))
        have h_eq_fun :
            (fun z : G × G => z.1 + z.2)
              = (fun z : G × G => z.1 - z.2) ∘ (fun q : G × G => (q.1, -q.2)) := by
          funext q; simp [Function.comp, sub_eq_add_neg]
        simpa [h_eq_fun] using h_sub_qmp.comp h_neg_prod.quasiMeasurePreserving
      have h_eq_prod :
          (fun p : G × G => φ (p.1 + p.2))
            =ᵐ[μ.prod μ]
              (fun p : G × G => φ0 (p.1 + p.2)) := by
        simpa using h_add_qmp.ae_eq_comp (hφ.ae_eq_mk)
      have hφ_sum_sm : AEStronglyMeasurable
          (fun p : G × G => φ (p.1 + p.2)) (μ.prod μ) :=
        (h0_sm.aestronglyMeasurable.congr h_eq_prod.symm)
      simpa [Real.norm_eq_abs] using (hφ_sum_sm.norm.aemeasurable)
    have h_mul :
        AEMeasurable (fun p : G × G =>
          |f p.1| * |g p.2| * |φ (p.1 + p.2)|) (μ.prod μ) :=
      (hf_prod.mul hg_prod).mul hφ_sum
    simpa [F] using h_mul.ennreal_ofReal
  -- A.E.-measurability transported to the pushforward measure by τ.
  have hF_aemeas_map :
      AEMeasurable F (Measure.map τ (μ.prod μ)) := by
    simpa [hτ_pres.map_eq] using hF_aemeas_prod
  -- Apply change-of-variables for lintegrals along τ.
  have h_change :=
    lintegral_map'
      (μ := μ.prod μ) (f := F) (g := τ)
      hF_aemeas_map (aemeasurable_id'.comp_measurable hτ_pres.measurable)
  -- Unfold F ∘ τ and simplify the algebraic identity (p.2 - p.1) + p.1 = p.2.
  have h_comp : (fun p : G × G => F (τ p))
      = fun p : G × G =>
          ENNReal.ofReal (|f (p.2 - p.1)| * |g p.1| * |φ p.2|) := by
    funext p; simp [F, τ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- Rearrange to match the requested orientation.
  calc
    ∫⁻ p : G × G,
        ENNReal.ofReal (|f (p.2 - p.1)| * |g p.1| * |φ p.2|) ∂(μ.prod μ)
        = ∫⁻ p : G × G, (fun p => F (τ p)) p ∂(μ.prod μ) := by
          simp [h_comp]
    _ = ∫⁻ p : G × G, F p ∂(Measure.map τ (μ.prod μ)) := h_change.symm
    _ = ∫⁻ p : G × G, F p ∂(μ.prod μ) := by simp [hτ_pres.map_eq]
    _ = ∫⁻ p : G × G,
          ENNReal.ofReal (|f p.1| * |g p.2| * |φ (p.1 + p.2)|) ∂(μ.prod μ) := rfl

-- (Removed: L¹-finiteness helper lemmas; avoid adding L¹ assumptions.)

/-!
Auxiliary finiteness lemma on a finite measure, matching the local goal where
we use only the product of finite L¹ norms of `Af` and `Ag`. For now we provide
the statement earlier in the file (so downstream proofs can reference it) and
defer the full proof with a placeholder. This keeps build order consistent.
-/
section PartialProductBounds

variable {G : Type*}
variable [MeasurableSpace G]
variable [NormedAddCommGroup G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]

lemma lintegral_mul_shift_lt_top_of_finite
    (μ ν : Measure G) [SFinite μ] [IsFiniteMeasure ν]
    [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (c : ℝ≥0∞)
    (h_prod_le : (ν.prod ν) ≤ c • (μ.prod μ)) (hc_lt_top : c < ∞)
    (f g : G → ℝ)
    (p q : ℝ≥0∞) (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hf1 : MemLp f 1 μ) (hg1 : MemLp g 1 μ) :
    (∫⁻ q : G × G,
        ‖f (q.1 - q.2)‖ₑ * ‖g q.2‖ₑ ∂ (ν.prod ν)) < ∞ := by
  -- Step 1: Compare the product measures and pull the scalar outside the lintegral.
  -- Define the nonnegative kernel we integrate on the product space.
  set H : G × G → ℝ≥0∞ :=
    fun q => ‖f (q.1 - q.2)‖ₑ * ‖g q.2‖ₑ with hH_def
  -- Monotonicity in the measure together with the given domination.
  have h_step1 :
      (∫⁻ q, H q ∂ (ν.prod ν))
        ≤ ∫⁻ q, H q ∂ (c • (μ.prod μ)) :=
    lintegral_mono' h_prod_le (by intro _; exact le_rfl)
  -- Pull out the scalar factor c from the outer measure.
  have h_scale :
      (∫⁻ q, H q ∂ (c • (μ.prod μ)))
        = c * (∫⁻ q, H q ∂ (μ.prod μ)) := by
    simp [lintegral_smul_measure, mul_comm, mul_left_comm, mul_assoc]
  have h_bound :
      (∫⁻ q, H q ∂ (ν.prod ν))
        ≤ c * (∫⁻ q, H q ∂ (μ.prod μ)) := by
    simpa [h_scale]
      using h_step1
  -- Step 2: it suffices to show the RHS is finite.
  -- The remaining finiteness on μ × μ will be provided downstream
  -- (via change of variables and product bounds). We record the reduction.
  have h_rhs_fin : c * (∫⁻ q, H q ∂ (μ.prod μ)) < ∞ := by
    classical
    -- If the scalar is zero, the product is trivially finite.
    by_cases hc0 : c = 0
    · have h0 : (0 : ℝ≥0∞) < ∞ := by simp [lt_top_iff_ne_top]
      simp [hc0]
    -- Otherwise, reduce to showing both factors are finite; this will be supplied below.
    have h_int_fin : (∫⁻ q, H q ∂ (μ.prod μ)) < ∞ := by
      classical
      -- Write the product lintegral as an iterated integral and pull out the |g y| factor.
      -- A.E.-measurability of H on μ × μ.
      have hf_ae : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
      have hg_ae : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
      have hAf_aemeas : AEMeasurable (fun x => ‖f x‖ₑ) μ := hf_ae.enorm
      have hAg_aemeas : AEMeasurable (fun y => ‖g y‖ₑ) μ := hg_ae.enorm
      -- Quasi-measure-preserving map (x, y) ↦ x − y with respect to μ × μ → μ.
      have h_sub_qmp :
          Measure.QuasiMeasurePreserving (fun p : G × G => p.1 - p.2)
            (μ.prod μ) μ := by
        have h_sub_prod :
            MeasurePreserving (fun q : G × G => (q.1 - q.2, q.2))
              (μ.prod μ) (μ.prod μ) :=
          measurePreserving_sub_prod (μ := μ) (ν := μ)
        have h_fst_qmp :
            Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
              (μ.prod μ) μ :=
          MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
        simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
          using h_fst_qmp.comp h_sub_prod.quasiMeasurePreserving
      have hAf_comp_aemeas :
          AEMeasurable (fun q : G × G => ‖f (q.1 - q.2)‖ₑ) (μ.prod μ) :=
        (hAf_aemeas.comp_quasiMeasurePreserving h_sub_qmp)
      have hAg_comp_aemeas :
          AEMeasurable (fun q : G × G => ‖g q.2‖ₑ) (μ.prod μ) :=
        (hAg_aemeas.comp_quasiMeasurePreserving
          (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)))
      have hH_aemeas : AEMeasurable H (μ.prod μ) :=
        (hAf_comp_aemeas.mul hAg_comp_aemeas)
      -- Tonelli for the nonnegative kernel H, then swap the iterated integrals.
      have h_prod_eq :
          ∫⁻ q : G × G, H q ∂ (μ.prod μ)
            = ∫⁻ x, ∫⁻ y, H (x, y) ∂ μ ∂ μ := by
        simpa using
          (MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
            (f := fun p : G × G => H p) hH_aemeas)
      have h_swap :
          ∫⁻ x, ∫⁻ y, H (x, y) ∂ μ ∂ μ
            = ∫⁻ y, ∫⁻ x, H (x, y) ∂ μ ∂ μ := by
        simpa [Function.uncurry]
          using
            (MeasureTheory.lintegral_lintegral_swap (μ := μ) (ν := μ)
              (f := fun x y => H (x, y)) hH_aemeas)
      -- Pull the |g y| factor out of the inner lintegral.
      have h_pull (y : G) :
          ∫⁻ x, H (x, y) ∂ μ
            = (‖g y‖ₑ) * (∫⁻ x, ‖f (x - y)‖ₑ ∂ μ) := by
        -- A.E.-measurability of the inner integrand in x for each fixed y.
        have h_sub_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
          have h_add_neg : MeasurePreserving (fun x : G => x + (-y)) μ μ :=
            measurePreserving_add_right (μ := μ) (-y)
          simpa [sub_eq_add_neg] using h_add_neg
        have hf_tr : AEStronglyMeasurable (fun x => f (x - y)) μ :=
          hf_ae.comp_measurePreserving h_sub_pres
        have hf_tr_enorm : AEMeasurable (fun x => ‖f (x - y)‖ₑ) μ := hf_tr.enorm
        -- Use lintegral_const_mul'' to factor the constant ‖g y‖ₑ.
        have :=
          lintegral_const_mul'' (μ := μ)
            (r := ‖g y‖ₑ) (f := fun x => ‖f (x - y)‖ₑ) hf_tr_enorm
        -- This yields: ∫ x, ‖g y‖ₑ * ‖f (x - y)‖ₑ = ‖g y‖ₑ * ∫ x, ‖f (x - y)‖ₑ.
        -- Rewrite the left-hand side to match H (x, y).
        simpa [H, hH_def, mul_comm, mul_left_comm, mul_assoc] using this
      -- Change of variables for the inner integral: translation invariance of μ.
      have h_change (y : G) :
          ∫⁻ x, ‖f (x - y)‖ₑ ∂ μ = ∫⁻ x, ‖f x‖ₑ ∂ μ := by
        -- Define the translation τ(x) = x − y and apply lintegral_map'.
        set τ : G → G := fun x => x - y
        have h_pres : MeasurePreserving τ μ μ := by
          have h_add_neg : MeasurePreserving (fun x : G => x + (-y)) μ μ :=
            measurePreserving_add_right (μ := μ) (-y)
          simpa [τ, sub_eq_add_neg] using h_add_neg
        set h0 : G → ℝ≥0∞ := fun z => ‖f z‖ₑ with hh0
        -- h0 is a.e.-measurable with respect to map τ μ = μ.
        have h0_aemeas_map : AEMeasurable h0 (Measure.map τ μ) := by
          simpa [h0, h_pres.map_eq] using hAf_aemeas
        have h_map :=
          lintegral_map' (μ := μ) (f := h0) (g := τ)
            h0_aemeas_map (aemeasurable_id'.comp_measurable h_pres.measurable)
        -- Change-of-variables for the lintegral along τ and rewrite using map_eq.
        have h_cv :
            ∫⁻ x, (fun z => ‖f z‖ₑ) (τ x) ∂ μ
              = ∫⁻ z, ‖f z‖ₑ ∂ μ := by
          simpa [h_pres.map_eq] using h_map.symm
        -- Unfold τ and h0.
        simpa [τ, sub_eq_add_neg] using h_cv
      -- Put the pieces together: the inner integral is independent of y.
      have h_iter :
          ∫⁻ y, ∫⁻ x, H (x, y) ∂ μ ∂ μ
            = (∫⁻ x, ‖f x‖ₑ ∂ μ) * (∫⁻ y, ‖g y‖ₑ ∂ μ) := by
        -- Replace the inner integral by the constant and pull the constant outside.
        have h_inner_eq :
            ∀ᵐ y ∂ μ,
              ∫⁻ x, H (x, y) ∂ μ
                = (‖g y‖ₑ) * (∫⁻ x, ‖f x‖ₑ ∂ μ) := by
          refine Filter.Eventually.of_forall (fun y => ?_)
          simpa [h_change y, mul_comm, mul_left_comm, mul_assoc]
            using h_pull y
        -- Pull out the constant factor ∫ ‖f‖ₑ.
        have h_const :
            ∫⁻ y, (‖g y‖ₑ) * (∫⁻ x, ‖f x‖ₑ ∂ μ) ∂ μ
              = (∫⁻ x, ‖f x‖ₑ ∂ μ) * (∫⁻ y, ‖g y‖ₑ ∂ μ) := by
          -- Use the a.e.-measurable version lintegral_const_mul''.
          have h_mul_aemeas :
              AEMeasurable (fun y => (‖g y‖ₑ)) μ := hAg_aemeas
          have :=
            lintegral_const_mul'' (μ := μ)
              (r := (∫⁻ x, ‖f x‖ₑ ∂ μ))
              (f := fun y => (‖g y‖ₑ)) h_mul_aemeas
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        -- Combine the pointwise equality with lintegral_congr_ae.
        refine (lintegral_congr_ae h_inner_eq).trans ?_
        exact h_const
      -- Now express the product integral in separated form.
      have h_sep :
          ∫⁻ q : G × G, H q ∂ (μ.prod μ)
            = (∫⁻ x, ‖f x‖ₑ ∂ μ) * (∫⁻ y, ‖g y‖ₑ ∂ μ) := by
        -- Use the chain: ∫ H d(μ×μ) = ∫x∫y H = ∫y∫x H, then apply h_iter.
        simpa [h_prod_eq, h_swap] using h_iter
      -- Reduce finiteness to finiteness of the separated L¹ norms, supplied as assumptions.
      have hf_L1_fin : (∫⁻ x, ‖f x‖ₑ ∂ μ) < ∞ := by
        simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm] using hf1.eLpNorm_lt_top
      have hg_L1_fin : (∫⁻ y, ‖g y‖ₑ ∂ μ) < ∞ := by
        simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm] using hg1.eLpNorm_lt_top
      -- Conclude finiteness of the product.
      simpa [h_sep] using ENNReal.mul_lt_top hf_L1_fin hg_L1_fin
    exact ENNReal.mul_lt_top hc_lt_top h_int_fin
  exact lt_of_le_of_lt h_bound h_rhs_fin

end PartialProductBounds
