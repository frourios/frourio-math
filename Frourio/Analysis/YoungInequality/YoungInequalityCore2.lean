import Frourio.Analysis.HolderInequality.HolderInequality
import Frourio.Analysis.SchwartzDensityLp.FubiniSection
import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
import Frourio.Analysis.SchwartzDensityLp.LpDuality
import Frourio.Analysis.SchwartzDensityLp.TonelliTheorem
import Frourio.Analysis.YoungInequality.YoungInequalityCore1
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.LiminfLimsup

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

/-!
σ-有限切り出しで使う補題群（署名のみ）。
これらは `h_fin_shear` の実装で参照する下支えで、後で独立に証明を与える。
-/
section SigmaFiniteExhaustionShear

variable {G : Type*}
variable [MeasurableSpace G]
variable (μ : Measure G) [SFinite μ]
variable [NormedAddCommGroup G]
variable [μ.IsAddRightInvariant] [μ.IsNegInvariant]
variable [MeasurableAdd₂ G] [MeasurableNeg G]

-- 有限測度版：右座標を有限測度で制限した場合の sheared triple kernel の有限性
lemma lintegral_sheared_triple_kernel_restrict_right_lt_top_of_finite
    (f g φ : G → ℝ)
    (r rC : ℝ≥0∞)
    (hr_one_lt : 1 < r) (hr_ne_top : r ≠ ∞)
    (hrc : IsConjugateExponent r rC)
    (hfr : MemLp f r μ) (hg1 : MemLp g 1 μ)
    (hφ : MemLp φ rC μ)
    {K : Set G} (hKmeas : MeasurableSet K) (hKfin : μ K < ∞) :
    (∫⁻ p : G × G,
        ENNReal.ofReal (|f (p.2 - p.1)| * |g p.1| * |φ p.2|)
      ∂ (μ.prod (μ.restrict K))) < ∞ := by
  classical
  -- 設定：右座標の有限測度制限 ν = μ|_K
  set ν : Measure G := μ.restrict K with hν
  -- 移し替え：積分核と分解用の関数
  set F : G × G → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (|f (p.2 - p.1)| * |g p.1| * |φ p.2|) with hF
  set A : G → ℝ≥0∞ := fun z => ENNReal.ofReal (|φ z|) with hA
  set B : G → ℝ≥0∞ :=
    fun z => ∫⁻ y, ENNReal.ofReal (|f (z - y)| * |g y|) ∂ μ with hB
  -- Tonelli による反復積分への書き換え（測度は μ × ν）。
  have h_iter :
      (∫⁻ p : G × G, F p ∂ (μ.prod ν))
        = ∫⁻ z, (A z) * (B z) ∂ ν := by
    -- Placeholder: this step follows from Tonelli/Fubini with the kernel F
    -- and the sectionwise constant-factor pullout.
    -- A detailed proof is provided in the analysis document and will be
    -- filled in after adjacent lemmas are finalised.
    sorry
    -- (details elided)
  -- 右辺の有限性を示す。戦略：Hölder(r, rC) on ν による評価。
  -- φ 側（A）の L^{rC}(ν) 有界性。
  have hA_LrC_fin : (∫⁻ z, (A z) ^ rC.toReal ∂ ν) < ∞ := by
    -- φ ∈ L^{rC}(μ) かつ ν = μ|_K ≤ μ, K が可測。制限測度での L^{rC} 有限性。
    -- 具体的には、∫_K |φ|^{rC} dμ ≤ ∫ |φ|^{rC} dμ < ∞。
    -- これにより eLpNorm φ rC ν < ∞。
    sorry
  -- 内側（B）の L^r(ν) 有界性。Minkowski と平行移動不変性＋ hfr, hg1 で確保。
  have hB_Lr_fin : (∫⁻ z, (B z) ^ r.toReal ∂ ν) < ∞ := by
    -- 大枠：
    --   B(z) = ∫ |g y| · ofReal(|f(z-y)|) dμ(y)
    -- Minkowski: ‖B‖_{L^r(ν)} ≤ ∫ |g y| · ‖ ofReal(|f(·-y)|) ‖_{L^r(ν)} dμ(y).
    -- 平行移動不変性（右加法不変）より
    --   ‖ f(·-y) ‖_{L^r(ν)} ≤ ‖ f ‖_{L^r(μ)}
    -- かつ hg1 から ∫ |g| dμ < ∞。よって ‖B‖_{L^r(ν)} < ∞。
    sorry
  -- Hölder(r, rC) on ν で A·B の積分の有限性を導く。
  have h_holder_fin :
      (∫⁻ z, (A z) * (B z) ∂ ν) < ∞ := by
    -- IsConjugateExponent r rC と直前の r, rC ノルム有限性から従う。
    -- 形式的には eLpNorm_mul_le_mul_eLpNorm を利用する見込み。
    sorry
  -- 反復積分の等式と組み合わせて結論。
  simpa [hν, hF, hA, hB] using h_iter.trans_lt h_holder_fin

-- σ-有限の有限測度による増大列（全空間の被覆）
lemma exists_exhaustion_by_finite_measurable_sets [SigmaFinite μ] :
    ∃ (K : ℕ → Set G), (Monotone K) ∧ (∀ n, MeasurableSet (K n)) ∧
      (⋃ n, K n) = Set.univ ∧ (∀ n, μ (K n) < ∞) := by
  classical
  -- Use the standard spanning sets provided by the σ-finite structure.
  refine ⟨spanningSets μ, ?_, ?_, ?_, ?_⟩
  · -- Monotonicity
    simpa using monotone_spanningSets (μ := μ)
  · -- Measurability
    intro n; simpa using measurableSet_spanningSets (μ := μ) n
  · -- Cover the whole space
    simpa using iUnion_spanningSets (μ := μ)
  · -- Each piece has finite measure
    intro n; simpa using measure_spanningSets_lt_top (μ := μ) n

-- 右座標の有限測度制限を単調に外していくと、全空間の積分に収束
lemma lintegral_restrict_right_tendsto_unrestrict
    (f g φ : G → ℝ)
    (K : ℕ → Set G) (hKmono : Monotone K)
    (hKmeas : ∀ n, MeasurableSet (K n))
    (hKcover : (⋃ n, K n) = (Set.univ : Set G)) :
    Tendsto (fun n =>
      ∫⁻ p : G × G,
          ENNReal.ofReal (|f (p.2 - p.1)| * |g p.1| * |φ p.2|)
        ∂ (μ.prod (μ.restrict (K n))))
      atTop
      (𝓝 (∫⁻ p : G × G,
              ENNReal.ofReal (|f (p.2 - p.1)| * |g p.1| * |φ p.2|)
            ∂ (μ.prod μ))) := by
  classical
  -- Monotone convergence of measures (restrict K n ↑ to μ) on the product, applied to
  -- the nonnegative kernel. Proof deferred.
  sorry

end SigmaFiniteExhaustionShear

/-! ## ENNReal limit helpers (signatures) -/

section ENNRealLimitHelpers

open Filter

lemma lt_top_of_tendsto_of_all_lt_top
    {s : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (hs : Tendsto s atTop (𝓝 L)) (hfin : ∀ n, s n < ∞) :
    L < ∞ := by
  classical
  -- Placeholder: conclude finiteness of the limit from finiteness of terms.
  -- A specific quantitative bound will be supplied where used.
  sorry

end ENNRealLimitHelpers

lemma young_pairing_bound [SigmaFinite μ]
    (f g φ : G → ℝ)
    (p q r rC : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 < q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_one_lt : 1 < r) (hr_ne_top : r ≠ ∞)
    (hrc : IsConjugateExponent r rC)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hf1 : MemLp f 1 μ) (hg1 : MemLp g 1 μ)
    (hφ : MemLp φ rC μ) :
    ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
      ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal *
        (eLpNorm φ rC μ).toReal := by
  classical
  -- Basic measurability facts from MemLp
  have hf_ae : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hg_ae : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hφ_ae : AEStronglyMeasurable φ μ := hφ.aestronglyMeasurable

  -- Finite eLpNorms for algebra on toReal
  have hf_lt_top : eLpNorm f p μ < ∞ := hf.eLpNorm_lt_top
  have hg_lt_top : eLpNorm g q μ < ∞ := hg.eLpNorm_lt_top
  have hφ_lt_top : eLpNorm φ rC μ < ∞ := hφ.eLpNorm_lt_top
  have hf_ne_top : eLpNorm f p μ ≠ ∞ := ne_of_lt hf_lt_top
  have hg_ne_top : eLpNorm g q μ ≠ ∞ := ne_of_lt hg_lt_top
  have hφ_ne_top : eLpNorm φ rC μ ≠ ∞ := ne_of_lt hφ_lt_top

  -- Real-side nonnegative kernel on the product space
  set F₁ : G × G → ℝ :=
    fun p => |f p.1| * |g p.2| * |φ (p.1 + p.2)| with hF₁_def
  -- ENNReal version of the kernel
  set H₁ : G × G → ℝ≥0∞ := fun p => ENNReal.ofReal (F₁ p) with hH₁_def

  -- Sheared kernel (matches the change-of-variables lemma lintegral_triple_kernel_shear)
  set H₂ : G × G → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (|f (p.2 - p.1)| * |g p.1| * |φ p.2|) with hH₂_def

  -- Step 1: Identify the double real integral with the product-measure real integral
  have h_prod_real :
      ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
        = ∫ p : G × G, F₁ p ∂ (μ.prod μ) := by
    -- Skeleton: identify both sides with the same ENNReal lintegral toReal,
    -- then apply Tonelli on the ENNReal side (safe route A in the guide).
    -- Define the ENNReal kernel on sections (x,y).
    have hH₁_iter :
        ∫⁻ x, ∫⁻ y, H₁ (x, y) ∂ μ ∂ μ
          = ∫⁻ p : G × G, H₁ p ∂ (μ.prod μ) := by
      -- Tonelli for nonnegative ENNReal kernels on product measures.
      -- `H₁` is measurable as ofReal of a.e.-measurable real function.
      -- We keep the measurability justification concise here.
      have hH₁_meas : AEMeasurable H₁ (μ.prod μ) := by
        classical
        -- Build pieces: |f ∘ fst|, |g ∘ snd|, |φ ∘ (add)| on G×G
        have hf_ae' : AEMeasurable f μ := hf_ae.aemeasurable
        have hg_ae' : AEMeasurable g μ := hg_ae.aemeasurable
        have hφ_ae' : AEMeasurable φ μ := hφ_ae.aemeasurable
        have hf_prod :
            AEMeasurable (fun p : G × G => ‖f p.1‖) (μ.prod μ) :=
          (hf_ae'.norm).comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
        have hg_prod :
            AEMeasurable (fun p : G × G => ‖g p.2‖) (μ.prod μ) :=
          (hg_ae'.norm).comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
        -- Quasi-measure-preserving addition map (p ↦ p.1 + p.2)
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
        have hφ_sum :
            AEMeasurable (fun p : G × G => ‖φ (p.1 + p.2)‖) (μ.prod μ) := by
          simpa using ((hφ_ae').comp_quasiMeasurePreserving h_add_qmp).norm
        -- Combine the pieces and lift to ENNReal via ofReal
        have h_mul :
            AEMeasurable (fun p : G × G =>
              ‖f p.1‖ * ‖g p.2‖ * ‖φ (p.1 + p.2)‖) (μ.prod μ) :=
          (hf_prod.mul hg_prod).mul hφ_sum
        simpa [H₁, hH₁_def, F₁, hF₁_def, Real.norm_eq_abs]
          using h_mul.ennreal_ofReal
      simpa using
        (MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
          (f := H₁) hH₁_meas).symm

    -- Real↔ENNReal bridge on the product space (right-hand real integral)
    have h_right_toReal :
        ∫ p : G × G, F₁ p ∂ (μ.prod μ)
          = (∫⁻ p : G × G, H₁ p ∂ (μ.prod μ)).toReal := by
      -- Apply `integral_eq_lintegral_of_nonneg_ae` to the nonnegative real kernel F₁.
      -- Nonnegativity is obvious; measurability follows from hf/hg/hφ and addition.
      -- Placeholder for the explicit measurability proof.
      have h_nonneg : 0 ≤ᵐ[μ.prod μ] fun p : G × G => F₁ p :=
        Filter.Eventually.of_forall (fun p => by
          have h1 : 0 ≤ |f p.1| := abs_nonneg _
          have h2 : 0 ≤ |g p.2| := abs_nonneg _
          have h3 : 0 ≤ |φ (p.1 + p.2)| := abs_nonneg _
          exact mul_nonneg (mul_nonneg h1 h2) h3)
      have h_meas : AEStronglyMeasurable F₁ (μ.prod μ) := by
        classical
        -- Choose strongly measurable representatives on G
        set f0 : G → ℝ := hf_ae.mk f with hf0_def
        have hf0_sm : StronglyMeasurable f0 := hf_ae.stronglyMeasurable_mk
        have hf_eq : f =ᵐ[μ] f0 := hf_ae.ae_eq_mk
        set g0 : G → ℝ := hg_ae.mk g with hg0_def
        have hg0_sm : StronglyMeasurable g0 := hg_ae.stronglyMeasurable_mk
        have hg_eq : g =ᵐ[μ] g0 := hg_ae.ae_eq_mk
        set φ0 : G → ℝ := hφ_ae.mk φ with hφ0_def
        have hφ0_sm : StronglyMeasurable φ0 := hφ_ae.stronglyMeasurable_mk
        have hφ_eq : φ =ᵐ[μ] φ0 := hφ_ae.ae_eq_mk
        -- Lift the a.e. equalities to the product via quasi-measure-preserving maps.
        have hf_comp :
            (fun p : G × G => f p.1) =ᵐ[μ.prod μ]
              (fun p : G × G => f0 p.1) := by
          simpa using
            ((MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp hf_eq)
        have hg_comp :
            (fun p : G × G => g p.2) =ᵐ[μ.prod μ]
              (fun p : G × G => g0 p.2) := by
          simpa using
            ((MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp hg_eq)
        -- Addition map quasi-measure-preserving as in the shear lemma
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
        have hφ_comp :
            (fun p : G × G => φ (p.1 + p.2)) =ᵐ[μ.prod μ]
              (fun p : G × G => φ0 (p.1 + p.2)) := by
          simpa using h_add_qmp.ae_eq_comp hφ_eq
        -- Turn a.e. equalities into equalities of norms
        have hf_comp_norm :
            (fun p : G × G => ‖f p.1‖) =ᵐ[μ.prod μ]
              (fun p : G × G => ‖f0 p.1‖) :=
          hf_comp.mono (fun p hp => by simp [hp])
        have hg_comp_norm :
            (fun p : G × G => ‖g p.2‖) =ᵐ[μ.prod μ]
              (fun p : G × G => ‖g0 p.2‖) :=
          hg_comp.mono (fun p hp => by simp [hp])
        have hφ_comp_norm :
            (fun p : G × G => ‖φ (p.1 + p.2)‖) =ᵐ[μ.prod μ]
              (fun p : G × G => ‖φ0 (p.1 + p.2)‖) :=
          hφ_comp.mono (fun p hp => by simp [hp])
        -- Strong measurability of the representative kernel on the product
        have h_add : Measurable (fun p : G × G => p.1 + p.2) :=
          measurable_fst.add measurable_snd
        have hf0_prod_sm :
            StronglyMeasurable (fun p : G × G => ‖f0 p.1‖) :=
          (hf0_sm.comp_measurable measurable_fst).norm
        have hg0_prod_sm :
            StronglyMeasurable (fun p : G × G => ‖g0 p.2‖) :=
          (hg0_sm.comp_measurable measurable_snd).norm
        have hφ0_sum_sm :
            StronglyMeasurable (fun p : G × G => ‖φ0 (p.1 + p.2)‖) :=
          (hφ0_sm.comp_measurable h_add).norm
        have hF0_sm : StronglyMeasurable
            (fun p : G × G => ‖f0 p.1‖ * ‖g0 p.2‖ * ‖φ0 (p.1 + p.2)‖) :=
          (hf0_prod_sm.mul hg0_prod_sm).mul hφ0_sum_sm
        -- Identify F₁ with the norm-based expression pointwise
        have hF₁_norm :
            (fun p : G × G => F₁ p)
              = (fun p : G × G => ‖f p.1‖ * ‖g p.2‖ * ‖φ (p.1 + p.2)‖) := by
          funext p; simp [F₁, hF₁_def, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc]
        -- Transfer a.e. equalities to the product of norms
        have h_prod_norm_eq :
            (fun p : G × G => ‖f p.1‖ * ‖g p.2‖ * ‖φ (p.1 + p.2)‖)
              =ᵐ[μ.prod μ]
            (fun p : G × G => ‖f0 p.1‖ * ‖g0 p.2‖ * ‖φ0 (p.1 + p.2)‖) := by
          refine (hf_comp_norm.and (hg_comp_norm.and hφ_comp_norm)).mono ?_
          intro p h
          rcases h with ⟨hf_eq', hrest⟩
          rcases hrest with ⟨hg_eq', hφ_eq'⟩
          simp [hf_eq', hg_eq', hφ_eq', mul_comm, mul_left_comm, mul_assoc]
        -- Conclude AEStronglyMeasurable for F₁ by congruence with a strongly measurable kernel
        refine (hF0_sm.aestronglyMeasurable.congr ?_)
        simpa [hF₁_norm] using h_prod_norm_eq.symm
      simpa [H₁, hH₁_def]
        using
          (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
            (μ := μ.prod μ) (f := F₁) h_nonneg h_meas)

    -- Real↔ENNReal bridge for the iterated real integral (left-hand side)
    have h_left_toReal :
        ∫ x, ∫ y, F₁ (x, y) ∂ μ ∂ μ
          = (∫⁻ x, ∫⁻ y, H₁ (x, y) ∂ μ ∂ μ).toReal := by
      -- Bridge the outer real integral to an ENNReal iterated lintegral.
      -- Define the outer integrand Ix(x) = ∫ y, F₁ (x, y) dμ.
      set Ix : G → ℝ := fun x => ∫ y, F₁ (x, y) ∂ μ with hIx_def
      -- Measurability of Ix from AEStronglyMeasurable on the product.
      have hIx_meas : AEStronglyMeasurable Ix μ := by
        classical
        -- First, build AEStronglyMeasurable for F₁ on μ×μ (as above), then pushforward.
        -- Choose strongly measurable representatives for f, g, φ.
        set f0 : G → ℝ := hf_ae.mk f with hf0_def
        have hf0_sm : StronglyMeasurable f0 := hf_ae.stronglyMeasurable_mk
        have hf_eq : f =ᵐ[μ] f0 := hf_ae.ae_eq_mk
        set g0 : G → ℝ := hg_ae.mk g with hg0_def
        have hg0_sm : StronglyMeasurable g0 := hg_ae.stronglyMeasurable_mk
        have hg_eq : g =ᵐ[μ] g0 := hg_ae.ae_eq_mk
        set φ0 : G → ℝ := hφ_ae.mk φ with hφ0_def
        have hφ0_sm : StronglyMeasurable φ0 := hφ_ae.stronglyMeasurable_mk
        have hφ_eq : φ =ᵐ[μ] φ0 := hφ_ae.ae_eq_mk
        -- Lift a.e. equalities to the product via quasi-measure-preserving maps.
        have hf_comp :
            (fun p : G × G => f p.1) =ᵐ[μ.prod μ]
              (fun p : G × G => f0 p.1) := by
          simpa using
            ((MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp hf_eq)
        have hg_comp :
            (fun p : G × G => g p.2) =ᵐ[μ.prod μ]
              (fun p : G × G => g0 p.2) := by
          simpa using
            ((MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp hg_eq)
        -- Addition map quasi-measure-preserving (same construction as earlier).
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
        have hφ_comp :
            (fun p : G × G => φ (p.1 + p.2)) =ᵐ[μ.prod μ]
              (fun p : G × G => φ0 (p.1 + p.2)) := by
          simpa using h_add_qmp.ae_eq_comp hφ_eq
        -- Convert to norms and combine.
        have hf_comp_norm :
            (fun p : G × G => ‖f p.1‖) =ᵐ[μ.prod μ]
              (fun p : G × G => ‖f0 p.1‖) :=
          hf_comp.mono (fun p hp => by simp [hp])
        have hg_comp_norm :
            (fun p : G × G => ‖g p.2‖) =ᵐ[μ.prod μ]
              (fun p : G × G => ‖g0 p.2‖) :=
          hg_comp.mono (fun p hp => by simp [hp])
        have hφ_comp_norm :
            (fun p : G × G => ‖φ (p.1 + p.2)‖) =ᵐ[μ.prod μ]
              (fun p : G × G => ‖φ0 (p.1 + p.2)‖) :=
          hφ_comp.mono (fun p hp => by simp [hp])
        -- Strongly measurable representative of F₁ on the product.
        have h_add : Measurable (fun p : G × G => p.1 + p.2) :=
          measurable_fst.add measurable_snd
        have hf0_prod_sm :
            StronglyMeasurable (fun p : G × G => ‖f0 p.1‖) :=
          (hf0_sm.comp_measurable measurable_fst).norm
        have hg0_prod_sm :
            StronglyMeasurable (fun p : G × G => ‖g0 p.2‖) :=
          (hg0_sm.comp_measurable measurable_snd).norm
        have hφ0_sum_sm :
            StronglyMeasurable (fun p : G × G => ‖φ0 (p.1 + p.2)‖) :=
          (hφ0_sm.comp_measurable h_add).norm
        have hF0_sm : StronglyMeasurable
            (fun p : G × G => ‖f0 p.1‖ * ‖g0 p.2‖ * ‖φ0 (p.1 + p.2)‖) :=
          (hf0_prod_sm.mul hg0_prod_sm).mul hφ0_sum_sm
        -- Identify F₁ pointwise with the norm expression.
        have hF₁_norm :
            (fun p : G × G => F₁ p)
              = (fun p : G × G => ‖f p.1‖ * ‖g p.2‖ * ‖φ (p.1 + p.2)‖) := by
          funext p; simp [F₁, hF₁_def, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc]
        have h_prod_norm_eq :
            (fun p : G × G => ‖f p.1‖ * ‖g p.2‖ * ‖φ (p.1 + p.2)‖)
              =ᵐ[μ.prod μ]
            (fun p : G × G => ‖f0 p.1‖ * ‖g0 p.2‖ * ‖φ0 (p.1 + p.2)‖) := by
          refine (hf_comp_norm.and (hg_comp_norm.and hφ_comp_norm)).mono ?_
          intro p h; rcases h with ⟨hf_eq', hrest⟩; rcases hrest with ⟨hg_eq', hφ_eq'⟩
          simp [hf_eq', hg_eq', hφ_eq', mul_comm, mul_left_comm, mul_assoc]
        have hF₁_AEstrong : AEStronglyMeasurable F₁ (μ.prod μ) := by
          refine (hF0_sm.aestronglyMeasurable.congr ?_)
          simpa [hF₁_norm] using h_prod_norm_eq.symm
        -- Now apply the product→section measurability lemma.
        have : AEStronglyMeasurable (fun x => ∫ y, F₁ (x, y) ∂ μ) μ := by
          simpa using
            (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
              (μ := μ) (ν := μ) (E := ℝ) (f := F₁) hF₁_AEstrong)
        simpa [Ix, hIx_def] using this
      -- Nonnegativity of Ix.
      have hIx_nonneg : 0 ≤ᵐ[μ] Ix := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        have h_nonneg_y : 0 ≤ᵐ[μ] fun y => F₁ (x, y) :=
          Filter.Eventually.of_forall (fun y => by
            have h1 : 0 ≤ |f x| := abs_nonneg _
            have h2 : 0 ≤ |g y| := abs_nonneg _
            have h3 : 0 ≤ |φ (x + y)| := abs_nonneg _
            simpa [F₁, hF₁_def, mul_comm, mul_left_comm, mul_assoc]
              using mul_nonneg (mul_nonneg h1 h2) h3)
        simpa [Ix, hIx_def]
          using integral_nonneg_of_ae (μ := μ) h_nonneg_y
      -- Apply the real↔ENNReal bridge to the outer integral.
      have h_bridge_outer :
          ∫ x, Ix x ∂ μ = (∫⁻ x, ENNReal.ofReal (Ix x) ∂ μ).toReal := by
        simpa [Ix, hIx_def]
          using (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
            (μ := μ) (f := Ix) hIx_nonneg hIx_meas)
      -- Identify the inner ENNReal integrand with the inner lintegral (a.e.).
      have h_section_bridge :
          (fun x => ENNReal.ofReal (Ix x))
            =ᵐ[μ]
              (fun x => ∫⁻ y, H₁ (x, y) ∂ μ) := by
        classical
        -- Fibrewise real↔ENNReal bridge, justified a.e. by Tonelli (finite sections).
        -- Step 1: a.e. equality on ℝ: Ix x = (∫⁻ y, H₁ (x,y) ∂μ).toReal
        have h_sec_toReal :
            (fun x => Ix x)
              =ᵐ[μ]
                (fun x => (∫⁻ y, H₁ (x, y) ∂ μ).toReal) := by
          -- Apply integral_eq_lintegral_of_nonneg_ae to each section in y.
          refine Filter.Eventually.of_forall (fun x => ?_)
          -- Nonnegativity of the section kernel in y.
          have h_nonneg_y : 0 ≤ᵐ[μ] fun y => F₁ (x, y) :=
            Filter.Eventually.of_forall (fun y => by
              have h1 : 0 ≤ |f x| := abs_nonneg _
              have h2 : 0 ≤ |g y| := abs_nonneg _
              have h3 : 0 ≤ |φ (x + y)| := abs_nonneg _
              simpa [F₁, hF₁_def, mul_comm, mul_left_comm, mul_assoc]
                using mul_nonneg (mul_nonneg h1 h2) h3)
          -- Section measurability; obtained from product-side AEStronglyMeasurable of F₁.
          have h_meas_y : AEStronglyMeasurable (fun y => F₁ (x, y)) μ := by
            -- Build AEStronglyMeasurable pieces and multiply.
            have hf_const : AEStronglyMeasurable (fun _ : G => ‖f x‖) μ := by
              simpa using
                (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : G => ‖f x‖) μ)
            have hg_norm : AEStronglyMeasurable (fun y : G => ‖g y‖) μ := hg_ae.norm
            -- Compose φ with the add-right map y ↦ y + x (measure-preserving).
            have h_add_pres : MeasurePreserving (fun y : G => y + x) μ μ :=
              measurePreserving_add_right (μ := μ) x
            have hφ_norm : AEStronglyMeasurable (fun y : G => ‖φ (x + y)‖) μ := by
              -- Compose with y ↦ y + x, then commute addition.
              simpa [add_comm] using ((hφ_ae.comp_measurePreserving h_add_pres).norm)
            have h_all : AEStronglyMeasurable
                (fun y : G => ‖f x‖ * ‖g y‖ * ‖φ (x + y)‖) μ :=
              (hf_const.mul hg_norm).mul hφ_norm
            simpa [F₁, hF₁_def, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc]
              using h_all
          -- Real↔ENNReal bridge on μ for the section at x.
          simpa [Ix, hIx_def, H₁, hH₁_def]
            using (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
              (μ := μ) (f := fun y => F₁ (x, y)) h_nonneg_y h_meas_y)
        -- Step 2: a.e. finiteness of the inner ENNReal lintegral for ofReal_toReal.
        have h_sec_lt_top :
            ∀ᵐ x ∂ μ, ∫⁻ y, H₁ (x, y) ∂ μ < ∞ := by
          -- Tonelli consequence for nonnegative kernels on μ×μ.
          -- We will supply measurability and product finiteness for H₁ downstream.
          -- Skeleton:
          -- A.E.-measurability of H₁ on μ×μ (sufficient for the AEMeas version of Tonelli).
          have hH₁_meas : AEMeasurable H₁ (μ.prod μ) := by
            classical
            -- Build AEMeasurable pieces |f ∘ fst|, |g ∘ snd|, |φ ∘ (+)| and multiply.
            have hf_ae' : AEMeasurable f μ := hf_ae.aemeasurable
            have hg_ae' : AEMeasurable g μ := hg_ae.aemeasurable
            have hφ_ae' : AEMeasurable φ μ := hφ_ae.aemeasurable
            have hf_prod :
                AEMeasurable (fun p : G × G => ‖f p.1‖) (μ.prod μ) :=
              (hf_ae'.norm).comp_quasiMeasurePreserving
                (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
            have hg_prod :
                AEMeasurable (fun p : G × G => ‖g p.2‖) (μ.prod μ) :=
              (hg_ae'.norm).comp_quasiMeasurePreserving
                (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
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
            have hφ_sum :
                AEMeasurable (fun p : G × G => ‖φ (p.1 + p.2)‖) (μ.prod μ) := by
              simpa using ((hφ_ae').comp_quasiMeasurePreserving h_add_qmp).norm
            have h_mul :
                AEMeasurable (fun p : G × G =>
                  ‖f p.1‖ * ‖g p.2‖ * ‖φ (p.1 + p.2)‖) (μ.prod μ) :=
              (hf_prod.mul hg_prod).mul hφ_sum
            simpa [H₁, hH₁_def, F₁, hF₁_def, Real.norm_eq_abs]
              using h_mul.ennreal_ofReal
          have h_prod_lt_top :
              (∫⁻ p : G × G, H₁ p ∂ (μ.prod μ)) < ∞ := by
            classical
            -- Step A: reduce to the sheared kernel H₂ via change of variables (no estimates yet).
            have h_shear_eq :
                ∫⁻ p : G × G, H₁ p ∂ (μ.prod μ)
                  = ∫⁻ p : G × G, H₂ p ∂ (μ.prod μ) := by
              have :=
                lintegral_triple_kernel_shear (μ := μ)
                  (f := f) (g := g) (φ := φ) hf_ae hg_ae hφ_ae
              simpa [H₁, hH₁_def, H₂, hH₂_def, F₁, hF₁_def]
                using this.symm
            -- Step B: σ-有限切り出し（z 方向）＋ Tonelli 分解で有限性を確保するルート。
            -- 具体的には、有限測度部分集合 K ⊂ G への制限
            --   z ↦ ‖φ z‖ · ∫_y ‖f (z−y)‖‖g y‖
            -- を考え、部分空間での Hölder（r,rC）と既存の積分分解
            --   ∫_y ‖f (z−y)‖‖g y‖ = (∫ ‖f‖)·(∫ ‖g‖)
            -- を使って、
            --   ∫_{z∈K} ‖φ z‖ · (∫_y …) < ∞
            -- を得る。これを有限測度の増大列 K_n で単調極限して全空間へ拡張する。
            -- なお、この手順は Young/HBL 本体の評価を用いない（非循環）。
            -- 実装詳細は別補題に委ね、ここでは有限性主張を記録する。
            have h_fin_shear :
                (∫⁻ p : G × G, H₂ p ∂ (μ.prod μ)) < ∞ := by
              classical
              -- Choose an exhaustion by finite-measure sets on the right coordinate.
              obtain ⟨K, hKmono, hKmeas, hKcover, hKfin⟩ :=
                exists_exhaustion_by_finite_measurable_sets (μ := μ)
              -- Each restricted integral over μ.prod (μ.restrict (K n)) is finite.
              have h_each : ∀ n,
                  (∫⁻ p : G × G, H₂ p ∂ (μ.prod (μ.restrict (K n)))) < ∞ := by
                intro n
                have hKm := hKmeas n; have hKf := hKfin n
                -- Apply the finite-measure restricted sheared-kernel finiteness lemma
                -- in its special (non-circular) form, assuming f ∈ L^r.
                -- We record the needed L^r membership locally.
                have hfr : MemLp f r μ := by
                  -- This assumption will be supplied or derived upstream in the
                  -- specialized path; for now we keep it as a placeholder.
                  -- Possible route: deduce from additional hypotheses when available.
                  sorry
                have :=
                  lintegral_sheared_triple_kernel_restrict_right_lt_top_of_finite
                    (μ := μ)
                    (f := f) (g := g) (φ := φ)
                    (r := r) (rC := rC)
                    hr_one_lt hr_ne_top hrc hfr hg1 hφ
                    (K := K n) hKm hKf
                simpa [H₂, hH₂_def] using this
              -- As n → ∞, the restricted integrals tend to the full integral.
              have h_tendsto :=
                lintegral_restrict_right_tendsto_unrestrict (μ := μ)
                  (f := f) (g := g) (φ := φ)
                  K hKmono hKmeas hKcover
              -- Conclude finiteness of the limit from finiteness of terms.
              exact
                lt_top_of_tendsto_of_all_lt_top h_tendsto h_each
            -- Back to H₁ via the shear identity.
            simpa [h_shear_eq] using h_fin_shear
          simpa using
            (MeasureTheory.tonelli_ae_section_lt_top_of_aemeasurable_left (μ := μ)
              (f := H₁) hH₁_meas h_prod_lt_top)
        -- Step 3: upgrade to ENNReal by ofReal_toReal on finite sections.
        refine (h_sec_toReal.and h_sec_lt_top).mono ?_
        intro x hx
        rcases hx with ⟨hx_eq, hx_fin⟩
        have hne : (∫⁻ y, H₁ (x, y) ∂ μ) ≠ ∞ := ne_of_lt hx_fin
        simp [Ix, hIx_def, H₁, hH₁_def, hx_eq, ENNReal.ofReal_toReal hne]
      -- Convert the ENNReal integral using the a.e. equality.
      have h_iter_lintegral :
          ∫⁻ x, ENNReal.ofReal (Ix x) ∂ μ
            = ∫⁻ x, ∫⁻ y, H₁ (x, y) ∂ μ ∂ μ := by
        simpa using lintegral_congr_ae h_section_bridge
      -- Assemble the chain.
      calc
        ∫ x, ∫ y, F₁ (x, y) ∂ μ ∂ μ
            = ∫ x, Ix x ∂ μ := by simp [Ix, hIx_def]
        _ = (∫⁻ x, ENNReal.ofReal (Ix x) ∂ μ).toReal := h_bridge_outer
        _ = (∫⁻ x, ∫⁻ y, H₁ (x, y) ∂ μ ∂ μ).toReal := by simp [h_iter_lintegral]

    -- Conclude by chaining the equalities
    calc
      ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
          = ∫ x, ∫ y, F₁ (x, y) ∂ μ ∂ μ := by rfl
      _ = (∫⁻ x, ∫⁻ y, H₁ (x, y) ∂ μ ∂ μ).toReal := h_left_toReal
      _ = (∫⁻ p : G × G, H₁ p ∂ (μ.prod μ)).toReal := by simp [hH₁_iter]
      _ = ∫ p : G × G, F₁ p ∂ (μ.prod μ) := h_right_toReal.symm

  -- Step 2: Bridge to ENNReal on the product space
  have h_bridge :
      ∫ p : G × G, F₁ p ∂ (μ.prod μ)
        = (∫⁻ p : G × G, H₁ p ∂ (μ.prod μ)).toReal := by
    -- Use ofReal_integral_eq_lintegral_ofReal on the product space for a nonnegative kernel.
    -- This avoids inner toReal bridges and stays on (μ×μ).
    -- See young_pairing_exponent_analysis.md for the recommended pattern.
    sorry

  -- Step 3: Change of variables (shear) on the product lintegral
  have h_shear :
      ∫⁻ p : G × G, H₁ p ∂ (μ.prod μ)
        = ∫⁻ p : G × G, H₂ p ∂ (μ.prod μ) := by
    -- Apply the prepared shear lemma lintegral_triple_kernel_shear
    -- after unrolling H₁ and H₂.
    have :=
      lintegral_triple_kernel_shear (μ := μ)
        (f := f) (g := g) (φ := φ) hf_ae hg_ae hφ_ae
    -- Rearrange definitions to match H₁ and H₂
    simpa [H₁, hH₁_def, H₂, hH₂_def, F₁, hF₁_def]
      using this.symm

  -- Step 4: Core HBL-type bound on the sheared kernel (ENNReal side)
  have h_HBL :
      ∫⁻ p : G × G, H₂ p ∂ (μ.prod μ)
        ≤ (eLpNorm f p μ) * (eLpNorm g q μ) * (eLpNorm φ rC μ) := by
    -- This is the central pairing (Young/HBL) estimate on μ×μ:
    -- ∬ ofReal(|f(z−y)|·|g y|·|φ z|)
    --   ≤ ‖f‖_p · ‖g‖_q · ‖φ‖_{rC}
    -- Proof outline (not fully expanded here):
    --   • Use Hölder on (μ×μ) with exponents (r, rC) splitting off the φ-part.
    --   • Control the remaining L^r-norm of |f(z−y)|·|g y| via Hölder (p,q)
    --     and the Young exponent relation 1/p + 1/q = 1 + 1/r.
    --   • Invariance (add-right, neg) gives that translations preserve L^p norms.
    --   • σ-有限切り出し in y removes any finiteness obstruction; then apply
    --     monotone convergence to pass to g.
    -- All of this is detailed in young_pairing_exponent_analysis.md.
    -- We record the bound as a placeholder to keep downstream structure intact.
    sorry

  -- Step 5: Assemble the inequalities back on the real side
  have h_toReal_mono :
      (∫⁻ p : G × G, H₂ p ∂ (μ.prod μ)).toReal
        ≤ ((eLpNorm f p μ) * (eLpNorm g q μ) * (eLpNorm φ rC μ)).toReal := by
    -- Use toReal_le_toReal with the bound and finiteness
    have h_rhs_ne_top : (eLpNorm f p μ) * (eLpNorm g q μ) * (eLpNorm φ rC μ) ≠ ∞ := by
      apply ENNReal.mul_ne_top
      apply ENNReal.mul_ne_top hf_ne_top hg_ne_top
      exact hφ_ne_top
    have h_lhs_ne_top : ∫⁻ p : G × G, H₂ p ∂ (μ.prod μ) ≠ ∞ := by
      exact ne_of_lt (lt_of_le_of_lt h_HBL (lt_top_iff_ne_top.mpr h_rhs_ne_top))
    exact (ENNReal.toReal_le_toReal h_lhs_ne_top h_rhs_ne_top).mpr h_HBL

  -- Algebra on toReal for the finite constants
  have h_toReal_prod :
      ((eLpNorm f p μ) * (eLpNorm g q μ) * (eLpNorm φ rC μ)).toReal
        = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal *
            (eLpNorm φ rC μ).toReal := by
    -- Use toReal_mul repeatedly; all norms are finite (from MemLp assumptions)
    have hfg_toReal :
        ((eLpNorm f p μ) * (eLpNorm g q μ)).toReal
          = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
      simp [ENNReal.toReal_mul, hf_ne_top, hg_ne_top]
    have h_all :
        (((eLpNorm f p μ) * (eLpNorm g q μ)) * (eLpNorm φ rC μ)).toReal
          = ((eLpNorm f p μ) * (eLpNorm g q μ)).toReal * (eLpNorm φ rC μ).toReal := by
      simp [ENNReal.toReal_mul, hφ_ne_top, mul_comm, mul_left_comm, mul_assoc]
    simp [hfg_toReal, mul_comm, mul_left_comm, mul_assoc]

  -- Final chaining: real double integral ≤ product of toReal norms
  calc
    ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
        = ∫ p : G × G, F₁ p ∂ (μ.prod μ) := h_prod_real
    _ = (∫⁻ p : G × G, H₁ p ∂ (μ.prod μ)).toReal := h_bridge
    _ = (∫⁻ p : G × G, H₂ p ∂ (μ.prod μ)).toReal := by simp [h_shear]
    _ ≤ ((eLpNorm f p μ) * (eLpNorm g q μ) * (eLpNorm φ rC μ)).toReal := h_toReal_mono
    _ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal *
          (eLpNorm φ rC μ).toReal := h_toReal_prod

lemma lintegral_convolution_norm_bound
    (μ : Measure G) [SFinite μ] [SigmaFinite μ]
    [NormedAddCommGroup G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (f g : G → ℂ) (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 < q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_one_lt : 1 < r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hf1 : MemLp f 1 μ) (hg1 : MemLp g 1 μ) :
    ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal ∂ μ ≤
      (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal := by
  classical
  -- Outline (following lintegral_convolution_norm_bound.md):
  -- 1) Define the convolution-like kernel K(x) = ∫ ‖f (x - y)‖ ‖g y‖ dμ(y).
  -- 2) Record measurability/nonnegativity facts for later use.
  -- 3) Set up truncations and the duality step; the core trilinear bound will be proved next.

  -- Step 1: define the kernel K
  set K : G → ℝ := fun x => ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ with hK

  -- Basic measurability for f and g
  have hf_ae : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hg_ae : AEStronglyMeasurable g μ := hg.aestronglyMeasurable

  -- Nonnegativity of the integrand and of K
  have h_nonneg : ∀ x y, 0 ≤ ‖f (x - y)‖ * ‖g y‖ := by
    intro x y
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hK_nonneg : ∀ x, 0 ≤ K x := by
    intro x
    have h_ae : 0 ≤ᵐ[μ] fun y => ‖f (x - y)‖ * ‖g y‖ :=
      Filter.Eventually.of_forall (fun y => h_nonneg x y)
    simpa [hK] using integral_nonneg_of_ae (μ := μ) h_ae

  -- Step 2: measurability facts for the integrand and K
  -- For fixed x, y ↦ x - y is measurable, hence y ↦ ‖f (x - y)‖ is AEStronglyMeasurable.
  have h_meas_integrand (x : G) :
      AEStronglyMeasurable (fun y => ‖f (x - y)‖ * ‖g y‖) μ := by
    -- Use measure-preserving maps to compose under μ
    have h_sub_pres : MeasurePreserving (fun y : G => x - y) μ μ := by
      have h_neg : MeasurePreserving (fun y : G => -y) μ μ :=
        Measure.measurePreserving_neg (μ := μ)
      have h_add : MeasurePreserving (fun y : G => y + x) μ μ :=
        measurePreserving_add_right (μ := μ) x
      simpa [Function.comp, sub_eq_add_neg, add_comm]
        using h_add.comp h_neg
    have hf' : AEStronglyMeasurable (fun y => f (x - y)) μ :=
      hf_ae.comp_measurePreserving h_sub_pres
    have hf'' : AEStronglyMeasurable (fun y => ‖f (x - y)‖) μ :=
      hf'.norm
    have hg' : AEStronglyMeasurable (fun y => ‖g y‖) μ := hg_ae.norm
    exact hf''.mul hg'

  -- Using Fubini/Tonelli later will require σ/s‑finiteness, which we have.
  -- We also note r.toReal > 1 from hr_one_lt and hr_ne_top.
  have hr_pos : 0 < r.toReal := by
    -- From 1 < r we get r ≠ 0, hence toReal is positive since also r ≠ ∞.
    have hr_ne_zero : r ≠ 0 := by
      have : (0 : ℝ≥0∞) < r := lt_trans (by simp : (0 : ℝ≥0∞) < 1) hr_one_lt
      exact ne_of_gt this
    exact ENNReal.toReal_pos hr_ne_zero hr_ne_top

  -- Step 3: skeleton for truncations and duality
  -- Define a σ‑finite exhaustion and truncated functions g_n if needed.
  -- This helps justify Fubini steps and use of duality with uniformly bounded norms.
  -- For now we only set up the notations; the detailed properties will follow.
  classical
  -- Placeholder: choose any truncation scheme `gN : ℕ → G → ℂ` with
  -- (a) gN ∈ L^q and ‖gN‖_q ≤ ‖g‖_q, (b) gN → g in L^q (or a.e.).
  -- This can be implemented by cutting g on finite‑measure pieces.
  -- We will use these in the pairing/duality argument.
  have exists_truncation : ∃ (gN : ℕ → G → ℂ), True := by
    -- Construction deferred to the subsequent step.
    refine ⟨fun _ => g, trivial⟩

  -- Duality reduction: the desired bound is equivalent to an L^r bound on K,
  -- which will follow from testing against functions in the dual space L^{r'}.
  -- We set up the statement to be proved next.
  -- Let rC be the conjugate exponent of r (in ℝ≥0∞ sense).
  -- For any φ with ‖φ‖_{rC} ≤ 1 we will show
  --   ∬ K x · |φ x| dμ(x) ≤ ‖f‖_p ‖g‖_q.
  -- This is the core trilinear pairing estimate (Young/HBL).
  have pairing_bound :
      ∀ (rC : ℝ≥0∞), IsConjugateExponent r rC →
        ∀ φ : G → ℝ, MemLp φ rC μ →
          (eLpNorm φ rC μ ≤ 1) →
            ∫ x, K x * |φ x| ∂ μ ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
    intro rC hrc φ hφ hφ_le
    -- Strategy: rewrite ∫ K x * |φ x| as a double integral, then apply young_pairing_bound.
    -- Key observation: K x = ∫ y, ‖f (x - y)‖ * ‖g y‖ dμ(y)
    -- Hence ∫ K x * |φ x| dμ(x) = ∫∫ ‖f (x - y)‖ * ‖g y‖ * |φ x| dμ(y) dμ(x).
    -- By change of variables z = x - y (or x = z + y), this becomes
    -- ∫∫ ‖f z‖ * ‖g y‖ * |φ (z + y)| dμ(z) dμ(y), which matches young_pairing_bound.

    -- Step 1: Convert f, g from ℂ to ℝ (using norms).
    set f_norm : G → ℝ := fun x => ‖f x‖ with hf_norm_def
    set g_norm : G → ℝ := fun y => ‖g y‖ with hg_norm_def

    -- Step 2: Establish MemLp for the norm functions.
    have hf_norm_memLp : MemLp f_norm p μ := by
      have h := hf.norm
      simpa [f_norm, hf_norm_def] using h
    have hg_norm_memLp : MemLp g_norm q μ := by
      have h := hg.norm
      simpa [g_norm, hg_norm_def] using h

    -- Step 3: Norm preservation for eLpNorm.
    have hf_norm_eLpNorm : eLpNorm f_norm p μ = eLpNorm f p μ := by
      simp [f_norm, hf_norm_def]
    have hg_norm_eLpNorm : eLpNorm g_norm q μ = eLpNorm g q μ := by
      simp [g_norm, hg_norm_def]

    -- Step 4: Apply young_pairing_bound.
    have hf_norm_memLp1 : MemLp f_norm 1 μ := by
      -- From hf1 and norm preservation.
      have := hf1.norm
      simpa [f_norm, hf_norm_def] using this
    have hg_norm_memLp1 : MemLp g_norm 1 μ := by
      have := hg1.norm
      simpa [g_norm, hg_norm_def] using this
    have h_young :=
      young_pairing_bound (μ := μ)
        (f := f_norm) (g := g_norm) (φ := φ)
        (p := p) (q := q) (r := r) (rC := rC)
        hp hq hpqr hr_one_lt hr_ne_top hrc
        hf_norm_memLp hg_norm_memLp hf_norm_memLp1 hg_norm_memLp1 hφ

    -- Step 5: The bound from young_pairing_bound gives us:
    -- ∫ x, ∫ y, |f_norm x| * |g_norm y| * |φ (x + y)| ≤ ‖f_norm‖_p * ‖g_norm‖_q * ‖φ‖_rC
    -- Since |f_norm x| = ‖f x‖ and |g_norm y| = ‖g y‖, this is:
    -- ∫ x, ∫ y, ‖f x‖ * ‖g y‖ * |φ (x + y)| ≤ ‖f‖_p * ‖g‖_q * ‖φ‖_rC

    -- Step 6: By Fubini and change of variables x = z + y, we have
    -- ∫ K z * |φ z| = ∫ z, (∫ y, ‖f (z - y)‖ * ‖g y‖ dμ) * |φ z| dμ
    --                = ∫ z, ∫ y, ‖f (z - y)‖ * ‖g y‖ * |φ z| dμ dμ
    --                = ∫ y, ∫ z, ‖f (z - y)‖ * |φ z| * ‖g y‖ dμ dμ  (by Tonelli)
    --                = ∫ y, ∫ x, ‖f x‖ * |φ (x + y)| * ‖g y‖ dμ dμ  (change vars z = x + y)
    --                = ∫ x, ∫ y, ‖f x‖ * ‖g y‖ * |φ (x + y)| dμ dμ  (by Tonelli)

    -- This last expression is exactly what young_pairing_bound bounds.
    -- We need to show: ∫ x, K x * |φ x| = ∫ x, ∫ y, ‖f x‖ * ‖g y‖ * |φ (x + y)|
    -- where K x = ∫ y, ‖f (x - y)‖ * ‖g y‖.

    -- Strategy: use Fubini to rewrite K x * |φ x| as a double integral, then change variables.
    have h_rewrite_K :
        ∫ x, K x * |φ x| ∂ μ = ∫ x, ∫ y, ‖f x‖ * ‖g y‖ * |φ (x + y)| ∂μ ∂μ := by
      -- Step 1: Expand K x and swap the order of integration.
      have h_expand :
          ∫ x, K x * |φ x| ∂ μ = ∫ x, (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ) * |φ x| ∂μ := by
        simp [K, hK]

      -- Step 2: Bring |φ x| inside the inner integral.
      have h_fubini :
          ∫ x, (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ) * |φ x| ∂μ
            = ∫ x, ∫ y, ‖f (x - y)‖ * ‖g y‖ * |φ x| ∂μ ∂μ := by
        sorry -- Technical: pull constant outside integral

      -- Step 3: Apply Tonelli/Fubini to swap the order of integration.
      have h_swap :
          ∫ x, ∫ y, ‖f (x - y)‖ * ‖g y‖ * |φ x| ∂μ ∂μ
            = ∫ y, ∫ x, ‖f (x - y)‖ * ‖g y‖ * |φ x| ∂μ ∂μ := by
        sorry -- Tonelli/Fubini for nonnegative functions (technical)

      -- Step 4: Change variables in the inner integral: z = x - y, so x = z + y.
      have h_change_vars :
          ∫ y, ∫ x, ‖f (x - y)‖ * ‖g y‖ * |φ x| ∂μ ∂μ
            = ∫ y, ∫ z, ‖f z‖ * ‖g y‖ * |φ (z + y)| ∂μ ∂μ := by
        sorry -- Change of variables (technical)

      -- Step 5: Swap back the order of integration.
      have h_swap_back :
          ∫ y, ∫ z, ‖f z‖ * ‖g y‖ * |φ (z + y)| ∂μ ∂μ
            = ∫ z, ∫ y, ‖f z‖ * ‖g y‖ * |φ (z + y)| ∂μ ∂μ := by
        sorry -- Tonelli/Fubini for nonnegative functions (technical)

      -- Step 6: Rearrange to match the target.
      have h_rearrange :
          ∫ z, ∫ y, ‖f z‖ * ‖g y‖ * |φ (z + y)| ∂μ ∂μ
            = ∫ x, ∫ y, ‖f x‖ * ‖g y‖ * |φ (x + y)| ∂μ ∂μ := by
        rfl -- Just renaming z to x

      calc
        ∫ x, K x * |φ x| ∂ μ
            = ∫ x, (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ) * |φ x| ∂μ := h_expand
        _ = ∫ x, ∫ y, ‖f (x - y)‖ * ‖g y‖ * |φ x| ∂μ ∂μ := h_fubini
        _ = ∫ y, ∫ x, ‖f (x - y)‖ * ‖g y‖ * |φ x| ∂μ ∂μ := h_swap
        _ = ∫ y, ∫ z, ‖f z‖ * ‖g y‖ * |φ (z + y)| ∂μ ∂μ := h_change_vars
        _ = ∫ z, ∫ y, ‖f z‖ * ‖g y‖ * |φ (z + y)| ∂μ ∂μ := h_swap_back
        _ = ∫ x, ∫ y, ‖f x‖ * ‖g y‖ * |φ (x + y)| ∂μ ∂μ := h_rearrange

    calc
      ∫ x, K x * |φ x| ∂ μ
          = ∫ x, ∫ y, ‖f x‖ * ‖g y‖ * |φ (x + y)| ∂μ ∂μ := h_rewrite_K
      _ ≤ (eLpNorm f_norm p μ).toReal * (eLpNorm g_norm q μ).toReal *
            (eLpNorm φ rC μ).toReal := by
              have h_abs : ∀ x, |f_norm x| = ‖f x‖ := by
                intro x; simp [f_norm, hf_norm_def]
              have h_abs' : ∀ y, |g_norm y| = ‖g y‖ := by
                intro y; simp [g_norm, hg_norm_def]
              simpa [h_abs, h_abs'] using h_young
      _ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal *
            (eLpNorm φ rC μ).toReal := by
              rw [hf_norm_eLpNorm, hg_norm_eLpNorm]
      _ ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
              have : (eLpNorm φ rC μ).toReal ≤ 1 := by
                exact ENNReal.toReal_mono (by simp) hφ_le
              have h_nonneg : 0 ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
                exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
              calc
                (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal *
                  (eLpNorm φ rC μ).toReal
                    ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal * 1 := by
                        exact mul_le_mul_of_nonneg_left this h_nonneg
                _ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by ring

  -- From pairing_bound and L^r duality, we will deduce the desired L^r bound.
  -- Strategy:
  -- 1. Use Lp duality: ‖K‖_Lr^r = sup_{‖φ‖_LrC ≤ 1} (∫ K·φ)^r (approximately)
  -- 2. Apply pairing_bound to get the bound on ∫ K·φ
  -- 3. Convert to the lintegral form

  -- Step 1: Establish that K is in Lr.
  -- We will show that ∫⁻ x, (ofReal (K x))^r.toReal ≤ (‖f‖_p * ‖g‖_q)^r.toReal.

  -- First, note that K x = ∫ y, ‖f (x - y)‖ * ‖g y‖, which is exactly what we want.
  have h_K_eq : ∀ x, K x = ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ := by
    intro x
    simp [K, hK]

  -- Step 2: The target is to show:
  -- ∫⁻ x, (ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖))^r.toReal ≤ (eLpNorm f p μ * eLpNorm g q μ)^r.toReal

  -- By Lp duality, we know that for r > 1:
  -- ‖K‖_Lr = sup_{φ ∈ LrC, ‖φ‖_LrC ≤ 1} ∫ K·|φ|
  -- And from pairing_bound, each such integral is bounded by ‖f‖_p * ‖g‖_q.

  -- The detailed implementation requires:
  -- (a) Establishing K ∈ Lr using the dual characterization
  -- (b) Converting between integral and lintegral forms
  -- (c) Handling the r.toReal power

  -- This is a substantial proof that requires several Mathlib lemmas about Lp duality.
  -- The key components are:
  -- - MeasureTheory.Lp.duality theory for 1 < r < ∞
  -- - Conversion between eLpNorm and lintegral
  -- - Properties of ENNReal.rpow

  -- Given the complexity and the need for specific Lp duality lemmas that may not
  -- be readily available in the current form, we leave this as a structured sorry
  -- with clear documentation of what needs to be done.

  -- Attempt a direct proof using the structure we have.
  -- The key insight is that we need to relate lintegral and eLpNorm.

  -- For r > 1, we have:
  -- eLpNorm K r μ = (∫⁻ x, ‖K x‖ₑ ^ r.toReal ∂μ) ^ (1 / r).toReal

  -- From pairing_bound, we can deduce (via duality) that:
  -- eLpNorm K r μ ≤ eLpNorm f p μ * eLpNorm g q μ

  -- Taking both sides to the power r.toReal:
  -- (eLpNorm K r μ) ^ r.toReal ≤ (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal

  -- And using the definition of eLpNorm:
  -- ∫⁻ x, ‖K x‖ₑ ^ r.toReal ∂μ ≤ (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal

  -- Finally, since K x ≥ 0, we have ‖K x‖ₑ = ENNReal.ofReal (K x), so:
  -- ∫⁻ x, (ENNReal.ofReal (K x)) ^ r.toReal ∂μ ≤ (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal

  -- Using h_K_eq, we can substitute K x = ∫ y, ‖f (x - y)‖ * ‖g y‖:
  -- ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ)) ^ r.toReal ∂μ
  --   ≤ (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal

  -- This is exactly our target!

  -- However, the missing link is the application of Lp duality to go from
  -- pairing_bound (which gives bounds on integrals ∫ K·φ) to a bound on eLpNorm K r μ.

  -- For 1 < r < ∞, there should be a theorem stating:
  -- If ∀ φ with ‖φ‖_LrC ≤ 1, we have ∫ K·|φ| ≤ C, then ‖K‖_Lr ≤ C.

  -- This is the dual characterization of Lr norms.
  -- In Mathlib, this might be available as part of the Lp.duality theory.

  -- Since this specific form may require additional lemmas not readily available,
  -- we mark this as a structured sorry with the complete proof outline.

  -- Step 3: We need to pick a conjugate exponent rC for r.
  -- From hr_one_lt : 1 < r and hr_ne_top : r ≠ ∞, we can construct rC.

  -- First, establish the existence of rC.
  have h_conj_exists : ∃ rC, IsConjugateExponent r rC := by
    sorry -- Standard: for 1 < r < ∞, conjugate exponent exists

  obtain ⟨rC, hrc⟩ := h_conj_exists

  -- From conjugacy, we have 1 < rC.
  have hrC_one_lt : 1 < rC := by
    sorry -- From IsConjugateExponent and 1 < r < ∞

  -- Step 4: Establish that K satisfies the dual characterization.
  -- We need to show K ∈ Lr and bound its norm using pairing_bound.

  -- First, we need K : G → ℝ to be in MemLp with the appropriate bound.
  -- The key is to use SchwartzDensityLp.eLpNorm_le_of_dual_bound.

  -- However, eLpNorm_le_of_dual_bound requires K ∈ MemLp r μ as a prerequisite.
  -- Establishing this requires showing the lintegral is finite, which is circular.

  -- Alternative approach: Work directly with the lintegral bound.
  -- From the definition of eLpNorm and the dual characterization,
  -- if we can bound ∫ K·φ for all test functions φ, we get a bound on ‖K‖_Lr.

  -- The precise form needed is:
  -- ∫⁻ x, (ofReal (K x))^r.toReal ∂μ ≤ (C)^r.toReal
  -- where C = ‖f‖_p * ‖g‖_q.

  -- This follows from:
  -- 1. pairing_bound gives us: ∀ φ with ‖φ‖_rC ≤ 1, ∫ K·|φ| ≤ C
  -- 2. Lp duality gives: ‖K‖_r ≤ C (using the dual characterization)
  -- 3. Definition of eLpNorm relates to lintegral

  sorry -- Final assembly: Apply Lp duality and convert
        -- (eLpNorm_le_of_dual_bound)
        -- Currently blocked on:
        -- (a) Proving K ∈ MemLp r μ without circular reasoning
        -- (b) Adapting pairing_bound (which uses |φ|) to the form
        --     needed by eLpNorm_le_of_dual_bound
        -- (c) Converting the eLpNorm bound to lintegral form
        --
        -- These are all technically achievable but require careful
        -- setup of the dual characterization machinery.
