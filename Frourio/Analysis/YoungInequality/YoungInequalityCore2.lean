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

variable {G : Type*}
variable [MeasurableSpace G]
variable (μ : Measure G) [SFinite μ]
variable [NormedAddCommGroup G]
variable [μ.IsAddRightInvariant] [μ.IsNegInvariant]
variable [MeasurableAdd₂ G] [MeasurableNeg G]

/-!
Auxiliary pairing-style Young/HBL inequality used to bound pairings that arise in the
duality step of the `lintegral_convolution_norm_bound` proof. The fully detailed proof will
follow the blueprint in `lintegral_convolution_norm_bound.md`.

The statement controls the trilinear pairing
  ∬ |f z| |g y| |φ (z + y)| dμ(y) dμ(z)
by the product of `Lp` norms under the exponent relation 1/p + 1/q = 1 + 1/r with 1 < r < ∞.
-/
lemma young_pairing_bound
    (f g φ : G → ℝ)
    (p q r rC : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 < q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_one_lt : 1 < r) (hr_ne_top : r ≠ ∞)
    (hrc : IsConjugateExponent r rC)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hφ : MemLp φ rC μ) :
    ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
      ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal *
        (eLpNorm φ rC μ).toReal := by
  classical
  -- Basic measurability and invariance setup
  have hf_ae : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hg_ae : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hφ_ae : AEStronglyMeasurable φ μ := hφ.aestronglyMeasurable
  -- Translation invariance of the `rC`-seminorm for `φ`.
  have hφ_translate_norm (y : G) :
      eLpNorm (fun x => φ (x + y)) rC μ = eLpNorm φ rC μ := by
    simpa using
      (eLpNorm_comp_add_right (μ := μ) (f := φ) (y := y) (p := rC) hφ_ae)
  -- Each translate is in `MemLp rC` with the same seminorm bound.
  have hφ_translate_mem (y : G) : MemLp (fun x => φ (x + y)) rC μ := by
    have h_meas : AEStronglyMeasurable (fun x => φ (x + y)) μ := by
      have h_pres : MeasurePreserving (fun x : G => x + y) μ μ :=
        measurePreserving_add_right (μ := μ) y
      exact hφ_ae.comp_measurePreserving h_pres
    have h_lt_top : eLpNorm (fun x => φ (x + y)) rC μ < ∞ := by
      simpa [hφ_translate_norm y] using hφ.eLpNorm_lt_top
    exact ⟨h_meas, h_lt_top⟩
  -- Introduce the convolution-like kernel K(z) = ∫ |f(z - y)| |g y| dμ(y).
  set K : G → ℝ := fun z => ∫ y, |f (z - y)| * |g y| ∂μ with hK
  -- Nonnegativity of the basic kernels.
  have h_nonneg : ∀ x y, 0 ≤ |f x| * |g y| * |φ (x + y)| := by
    intro x y; exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hK_nonneg : ∀ z, 0 ≤ K z := by
    intro z
    have : 0 ≤ᵐ[μ] fun y => |f (z - y)| * |g y| :=
      Filter.Eventually.of_forall (fun y => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    simpa [hK] using integral_nonneg_of_ae (μ := μ) this
  -- Apply Hölder with exponents r and rC to the pairing ∫ K(z) |φ(z)| dμ(z).
  -- From conjugacy, 1 ≤ r and 1 ≤ rC.
  have hr_le : 1 ≤ r := le_of_lt hr_one_lt
  have h_conj : 1 / r + 1 / rC = 1 := by
    classical
    rcases hrc with hrc₁ | hrc₂ | hrc₃
    · rcases hrc₁ with ⟨hr_eq, _⟩
      -- If r = 1, then 1 < r is false
      exfalso
      rw [hr_eq] at hr_one_lt
      exact lt_irrefl 1 hr_one_lt
    · rcases hrc₂ with ⟨hr_eq, _⟩
      -- If r = ∞, then r ≠ ∞ is false
      exfalso
      exact hr_ne_top hr_eq
    · exact hrc₃.2.2.2.2
  have hrC_one_lt : 1 < rC := by
    classical
    rcases hrc with hrc₁ | hrc₂ | hrc₃
    · rcases hrc₁ with ⟨hr_eq, _⟩
      -- If r = 1, then 1 < r is false
      exfalso
      rw [hr_eq] at hr_one_lt
      exact lt_irrefl 1 hr_one_lt
    · rcases hrc₂ with ⟨hr_eq, _⟩
      -- If r = ∞, then r ≠ ∞ is false
      exfalso
      exact hr_ne_top hr_eq
    · exact hrc₃.2.2.1
  have hrC_le : 1 ≤ rC := le_of_lt hrC_one_lt
  -- Rewrite the trilinear pairing via the kernel K and a change of variables (z = x + y).
  have h_rewrite :
      ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
        = ∫ z, K z * |φ z| ∂μ := by
    classical
    -- For fixed y, change variables x ↦ z - y inside the inner integral.
    have h_inner_change (y : G) :
        ∫ x, |f x| * |φ (x + y)| ∂μ = ∫ z, |f (z - y)| * |φ z| ∂μ := by
      -- Express both sides via `lintegral` and use translation invariance.
      have h_nonneg₁ : 0 ≤ᵐ[μ] fun x => |f x| * |φ (x + y)| :=
        Filter.Eventually.of_forall (fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have h_nonneg₂ : 0 ≤ᵐ[μ] fun z => |f (z - y)| * |φ z| :=
        Filter.Eventually.of_forall (fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have h_meas₁ : AEStronglyMeasurable (fun x => |f x| * |φ (x + y)|) μ := by
        have hφ_tr : AEStronglyMeasurable (fun x => φ (x + y)) μ := by
          have h_pres : MeasurePreserving (fun x : G => x + y) μ μ :=
            measurePreserving_add_right (μ := μ) y
          exact hφ_ae.comp_measurePreserving h_pres
        exact (hf_ae.norm).mul hφ_tr.norm
      have h_meas₂ : AEStronglyMeasurable (fun z => |f (z - y)| * |φ z|) μ := by
        have h_sub_pres : MeasurePreserving (fun z : G => z - y) μ μ := by
          -- z - y = z + (-y), which is add_right
          have h_add_neg_y : MeasurePreserving (fun z : G => z + (-y)) μ μ :=
            measurePreserving_add_right (μ := μ) (-y)
          simpa [sub_eq_add_neg] using h_add_neg_y
        have hf_tr : AEStronglyMeasurable (fun z => f (z - y)) μ :=
          hf_ae.comp_measurePreserving h_sub_pres
        exact hf_tr.norm.mul (hφ_ae.norm)
      have h_eq₁ :=
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg₁ h_meas₁
      have h_eq₂ :=
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg₂ h_meas₂
      -- Show equality of the corresponding `lintegral`s using a translation.
      have h_change_vars :
          ∫⁻ x, ENNReal.ofReal (|f x| * |φ (x + y)|) ∂μ
            = ∫⁻ z, ENNReal.ofReal (|f (z - y)| * |φ z|) ∂μ := by
        -- Define the translation `τ(x) = x + y`.
        set τ : G → G := fun x => x + y
        have h_pres : MeasurePreserving τ μ μ :=
          measurePreserving_add_right (μ := μ) y
        set h₀ : G → ℝ≥0∞ := fun z => ENNReal.ofReal (|f (z - y)| * |φ z|) with hh₀
        have hh₀_comp : (fun x => ENNReal.ofReal (|f x| * |φ (x + y)|)) = fun x => h₀ (τ x) := by
          funext x
          simp [h₀, τ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        -- `h₀` is a.e.-measurable with respect to `map τ μ = μ`.
        have h₀_aemeas_map :
            AEMeasurable h₀ (Measure.map τ μ) := by
          rw [h_pres.map_eq]
          have h_sub : AEStronglyMeasurable (fun z => f (z - y)) μ :=
            hf_ae.comp_measurePreserving
              (by
                -- z - y = z + (-y)
                have h_add_neg_y : MeasurePreserving (fun z : G => z + (-y)) μ μ :=
                  measurePreserving_add_right (μ := μ) (-y)
                simpa [sub_eq_add_neg] using h_add_neg_y)
          have h_prod : AEStronglyMeasurable (fun z => |f (z - y)| * |φ z|) μ :=
            h_sub.norm.mul hφ_ae.norm
          exact ENNReal.measurable_ofReal.comp_aemeasurable h_prod.aemeasurable
        -- Apply `lintegral_map'` to transport along the translation.
        have h_map :=
          lintegral_map' h₀_aemeas_map
            (aemeasurable_id'.comp_measurable h_pres.measurable)
        -- Unfold the definitions and use `map_eq`.
        simpa [hh₀_comp, h_pres.map_eq]
          using h_map.symm
      simp [h_eq₁, h_eq₂, h_change_vars]
    -- Now integrate in y and pull out the |g y| factor.
    have h_nonneg_kernel : ∀ x y, 0 ≤ |f (x - y)| * |φ x| * |g y| := by
      intro x y; exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
    -- Use Fubini/Tonelli for the nonnegative kernel to swap the order and rewrite.
    have h_swap :
        ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
          = ∫ y, ∫ x, |f x| * |φ (x + y)| * |g y| ∂μ ∂μ := by
      classical
      -- Use Tonelli on the nonnegative kernel by moving to ENNReal and back.
      -- Define the ℝ≥0∞-valued kernel
      set H : G × G → ℝ≥0∞ :=
        fun p => ENNReal.ofReal (|f p.1| * |g p.2| * |φ (p.1 + p.2)|) with hH_def
      -- AEmesurability of the kernel on the product
      have hH_aemeas :
          AEMeasurable H (μ.prod μ) := by
        have hf_prod :
            AEMeasurable (fun p : G × G => |f p.1|) (μ.prod μ) :=
          (hf_ae.norm.aemeasurable).comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
        have hg_prod :
            AEMeasurable (fun p : G × G => |g p.2|) (μ.prod μ) :=
          (hg_ae.norm.aemeasurable).comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
        have hφ_sum :
            AEMeasurable (fun p : G × G => |φ (p.1 + p.2)|) (μ.prod μ) := by
          classical
          have h_add : Measurable (fun p : G × G => p.1 + p.2) :=
            measurable_fst.add measurable_snd
          set φ0 : G → ℝ := hφ_ae.mk φ with hφ0_def
          have hφ0_meas : StronglyMeasurable φ0 := hφ_ae.stronglyMeasurable_mk
          have h0_sm : StronglyMeasurable (fun p : G × G => φ0 (p.1 + p.2)) :=
            hφ0_meas.comp_measurable h_add
          -- For every y, translation preserves a.e. equality φ = φ0 on μ.
          have h_fiber : ∀ y : G,
              (fun x => φ (x + y)) =ᵐ[μ] (fun x => φ0 (x + y)) := by
            intro y
            exact
              (measurePreserving_add_right (μ := μ) y).quasiMeasurePreserving.ae_eq_comp
                (hφ_ae.ae_eq_mk)
          -- Transfer the a.e. equality φ = φ0 along the quasi-measure-preserving
          -- map (x, y) ↦ x + y from μ.prod μ to μ, obtained by composing the
          -- subtraction map with negation on the second coordinate.
          have h_add_qmp :
              Measure.QuasiMeasurePreserving (fun p : G × G => p.1 + p.2)
                (μ.prod μ) μ := by
            -- Obtain quasi-measure-preserving for (x, y) ↦ x - y
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
            -- Compose with negation on the second coordinate to turn subtraction into addition.
            have h_neg_prod :
                MeasurePreserving (fun q : G × G => (q.1, -q.2))
                  (μ.prod μ) (μ.prod μ) := by
              -- Build as a product of measure-preserving maps on each factor
              -- (id on the first coordinate, negation on the second).
              -- Use `MeasurePreserving.prod` on `Prod.map` and then `simpa` the goal.
              simpa using
                (MeasureTheory.MeasurePreserving.prod
                  (μa := μ) (μc := μ) (μb := μ) (μd := μ)
                  (hf := MeasureTheory.MeasurePreserving.id (μ := μ))
                  (hg := Measure.measurePreserving_neg (μ := μ)))
            -- Now compose and identify with the addition map by extensionality.
            have h_eq_fun :
                (fun p : G × G => p.1 + p.2)
                  = (fun p : G × G => p.1 - p.2) ∘ (fun q : G × G => (q.1, -q.2)) := by
              funext q; simp [Function.comp, sub_eq_add_neg]
            simpa [h_eq_fun]
              using h_sub_qmp.comp h_neg_prod.quasiMeasurePreserving
          -- Use ae_eq_mk and transport along the addition map
          have h_eq_prod :
              (fun p : G × G => φ (p.1 + p.2))
                =ᵐ[μ.prod μ]
                (fun p : G × G => φ0 (p.1 + p.2)) := by
            have hφ_eq : φ =ᵐ[μ] φ0 := hφ_ae.ae_eq_mk
            simpa using h_add_qmp.ae_eq_comp hφ_eq
          -- Conclude AEMeasurable via the strongly measurable representative.
          have hφ_sum_meas :
              AEMeasurable (fun p : G × G => φ (p.1 + p.2)) (μ.prod μ) :=
            h0_sm.aemeasurable.congr h_eq_prod.symm
          -- Get AEMeasurable for |φ (p.1 + p.2)|
          have hφ_sum_sm : AEStronglyMeasurable (fun p : G × G => φ (p.1 + p.2)) (μ.prod μ) :=
            h0_sm.aestronglyMeasurable.congr h_eq_prod.symm
          exact hφ_sum_sm.norm.aemeasurable
        have h_mul :
            AEMeasurable
              (fun p : G × G => |f p.1| * |g p.2| * |φ (p.1 + p.2)|)
              (μ.prod μ) :=
          (hf_prod.mul hg_prod).mul hφ_sum
        simpa [H, hH_def] using h_mul.ennreal_ofReal
      -- Convert each iterated real integral into a `toReal` of a lintegral and use symmetry.
      have h_nonneg : ∀ x y, 0 ≤ |f x| * |g y| * |φ (x + y)| := by
        intro x y; exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
      -- Left side to lintegral
      have h_left :
          ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
            = (∫⁻ x, ∫⁻ y, H (x, y) ∂μ ∂μ).toReal := by
        -- pointwise in x, identify the inner integral with a lintegral
        have h_eq_ae :
            (fun x => ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ)
              =ᵐ[μ]
                (fun x => (∫⁻ y, H (x, y) ∂μ).toReal) := by
          refine Filter.Eventually.of_forall ?_
          intro x
          have h_meas :
              AEStronglyMeasurable (fun y => |f x| * |g y| * |φ (x + y)|) μ := by
            have hφ_tr : AEStronglyMeasurable (fun y => φ (x + y)) μ := by
              -- φ(x + y) = φ(y + x) by commutativity
              have h_comm : (fun y => φ (x + y)) = (fun y => φ (y + x)) := by
                funext y; simp [add_comm]
              rw [h_comm]
              exact hφ_ae.comp_measurePreserving (measurePreserving_add_right (μ := μ) x)
            have h_const : AEStronglyMeasurable (fun _ : G => |f x|) μ :=
              aestronglyMeasurable_const
            exact (h_const.mul (hg_ae.norm)).mul (hφ_tr.norm)
          have h_nonneg_ae : 0 ≤ᵐ[μ]
              fun y => |f x| * |g y| * |φ (x + y)| :=
            Filter.Eventually.of_forall (fun y => h_nonneg x y)
          have h_eq :=
            MeasureTheory.integral_eq_lintegral_of_nonneg_ae
              (μ := μ) (f := fun y => |f x| * |g y| * |φ (x + y)|)
              h_nonneg_ae h_meas
          simpa [H, hH_def, mul_comm, mul_left_comm, mul_assoc]
            using h_eq
        -- Establish a.e.-finiteness of sections via Tonelli from product finiteness.
        have h_fin : ∀ᵐ x ∂μ, (∫⁻ y, H (x, y) ∂μ) < ∞ := by
          -- It suffices to know the product lintegral is finite;
          -- then apply the Tonelli section lemma.
          have h_prod_fin : ∫⁻ p : G × G, H p ∂(μ.prod μ) < ∞ := by
            -- This product finiteness is proved later in the argument via a change of variables
            -- and standard Hölder-type bounds for the triple kernel.
            -- We leave it as a local placeholder to avoid circularity here; it will be
            -- discharged alongside the symmetric argument for `h_right` below.
            sorry
          simpa using
            (MeasureTheory.tonelli_ae_section_lt_top_of_aemeasurable_left
              (μ := μ) (f := H) hH_aemeas h_prod_fin)
        -- Now convert the outer integral to lintegral
        calc ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
            = ∫ x, (∫⁻ y, H (x, y) ∂μ).toReal ∂μ := integral_congr_ae h_eq_ae
          _ = (∫⁻ x, ∫⁻ y, H (x, y) ∂μ ∂μ).toReal := by
              -- Convert the outer real integral into the toReal of a lintegral by
              -- applying `integral_toReal` to the ℝ≥0∞–valued map
              --   x ↦ ∫⁻ y, H (x, y) ∂μ.
              -- First, record a.e. measurability of this map.
              have h_aemeas :
                  AEMeasurable (fun x => ∫⁻ y, H (x, y) ∂μ) μ :=
                hH_aemeas.lintegral_prod_right'
              simpa using (MeasureTheory.integral_toReal h_aemeas h_fin)
      -- Right side to lintegral
      have h_right :
          ∫ y, ∫ x, |f x| * |φ (x + y)| * |g y| ∂μ ∂μ
            = (∫⁻ y, ∫⁻ x, H (x, y) ∂μ ∂μ).toReal := by
        have h_eq_ae :
            (fun y => ∫ x, |f x| * |φ (x + y)| * |g y| ∂μ)
              =ᵐ[μ]
                (fun y => (∫⁻ x, H (x, y) ∂μ).toReal) := by
          refine Filter.Eventually.of_forall ?_
          intro y
          have h_meas :
              AEStronglyMeasurable (fun x => |f x| * |φ (x + y)| * |g y|) μ := by
            have hφ_tr : AEStronglyMeasurable (fun x => φ (x + y)) μ :=
              hφ_ae.comp_measurePreserving (measurePreserving_add_right (μ := μ) y)
            have h_const : AEStronglyMeasurable (fun _ : G => |g y|) μ :=
              aestronglyMeasurable_const
            exact ((hf_ae.norm).mul (hφ_tr.norm)).mul h_const
          have h_nonneg_ae : 0 ≤ᵐ[μ]
              fun x => |f x| * |φ (x + y)| * |g y| :=
            Filter.Eventually.of_forall (fun x => by
              -- Need to show 0 ≤ |f x| * |φ (x + y)| * |g y|
              exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
          have h_eq :=
            MeasureTheory.integral_eq_lintegral_of_nonneg_ae
              (μ := μ) (f := fun x => |f x| * |φ (x + y)| * |g y|)
              h_nonneg_ae h_meas
          simpa [H, hH_def, mul_comm, mul_left_comm, mul_assoc]
            using h_eq
        -- Now convert the outer integral to lintegral
        calc ∫ y, ∫ x, |f x| * |φ (x + y)| * |g y| ∂μ ∂μ
            = ∫ y, (∫⁻ x, H (x, y) ∂μ).toReal ∂μ := integral_congr_ae h_eq_ae
          _ = (∫⁻ y, ∫⁻ x, H (x, y) ∂μ ∂μ).toReal := by
              -- Convert outer integral to lintegral
              -- applying `integral_toReal` to the ℝ≥0∞–valued map
              --   y ↦ ∫⁻ x, H (x, y) ∂μ.
              -- First, record a.e. measurability of this map.
              have h_aemeas :
                  AEMeasurable (fun y => ∫⁻ x, H (x, y) ∂μ) μ :=
                hH_aemeas.lintegral_prod_left'
              sorry
      -- Symmetry of the iterated lintegrals
      have h_symm :
          ∫⁻ x, ∫⁻ y, H (x, y) ∂μ ∂μ
            = ∫⁻ y, ∫⁻ x, H (x, y) ∂μ ∂μ := by
        simpa [Function.uncurry]
          using
            MeasureTheory.lintegral_lintegral_swap (μ := μ) (ν := μ)
              (f := fun x y => H (x, y)) hH_aemeas
      -- Put everything together
      simp [h_left, h_right, h_symm]
    -- Final rewrite: ∫y ∫x ... = ∫z K z |φ z|.
    -- Using the definition of K and rearranging products.
    refine by
      -- Rewrite the inner integral using change of variables and pull out |g y|.
      have h2 :
          ∀ᵐ y ∂μ,
            ∫ x, |f (x - y)| * |φ x| * |g y| ∂μ
              = |g y| * ∫ z, |f (z - y)| * |φ z| ∂μ := by
        refine Filter.Eventually.of_forall ?_
        intro y
        -- Move the constant factor |g y| outside the inner integral and
        -- identify the remaining integral by change of variables.
        have h_change :
            ∫ x, |f (x - y)| * |φ x| ∂μ
              = ∫ z, |f z| * |φ (z + y)| ∂μ := by
          -- This is the inverse orientation of `h_inner_change`.
          -- From `h_inner_change y` we have
          --   ∫ x, |f x| * |φ (x + y)| = ∫ z, |f (z - y)| * |φ z|.
          -- Renaming bound variables, this is equivalent to the desired identity.
          simpa using (h_inner_change y).symm
        calc
          ∫ x, |f (x - y)| * |φ x| * |g y| ∂μ
              = ∫ x, |g y| * (|f (x - y)| * |φ x|) ∂μ := by
                  simp [mul_comm, mul_left_comm, mul_assoc]
          _ = |g y| * ∫ x, |f (x - y)| * |φ x| ∂μ := by
                  -- pull the constant outside
                  simp [integral_const_mul]
          _ = |g y| * ∫ z, |f z| * |φ (z + y)| ∂μ := by
                  rw [h_change]
          _ = |g y| * ∫ z, |f (z - y)| * |φ z| ∂μ := by
                  -- apply the change-of-variables identity once more
                  rw [h_inner_change y]
      -- Replace the inner integral using `h2` and apply Fubini/Tonelli to identify K.
      have h3 := integral_congr_ae h2
      -- Convert to a double integral and swap the order (Tonelli for nonnegative kernels).
      have h_swap' :
          ∫ y, |g y| * ∫ z, |f (z - y)| * |φ z| ∂μ ∂μ
            = ∫ z, |φ z| * ∫ y, |f (z - y)| * |g y| ∂μ ∂μ := by
        -- Both sides are equal to ∬ |f (z - y)| * |φ z| * |g y| dμ(z) dμ(y).
        have hL :
            ∀ᵐ y ∂μ,
              |g y| * ∫ z, |f (z - y)| * |φ z| ∂μ
                = ∫ z, |f (z - y)| * |φ z| * |g y| ∂μ := by
          refine Filter.Eventually.of_forall ?_
          intro y
          simp [mul_comm, mul_left_comm, mul_assoc, integral_const_mul]
        have hR :
            ∀ᵐ z ∂μ,
              |φ z| * ∫ y, |f (z - y)| * |g y| ∂μ
                = ∫ y, |f (z - y)| * |g y| * |φ z| ∂μ := by
          refine Filter.Eventually.of_forall ?_
          intro z
          rw [← integral_const_mul]
          congr 1 with y
          ring
        have hL_int := integral_congr_ae hL
        have hR_int := integral_congr_ae hR
        -- Now apply Tonelli to the nonnegative kernel to swap the iterated integrals.
        have h_symm :
            ∫⁻ y, ∫⁻ z, ENNReal.ofReal (|f (z - y)| * |φ z| * |g y|) ∂μ ∂μ
              = ∫⁻ z, ∫⁻ y, ENNReal.ofReal (|f (z - y)| * |φ z| * |g y|) ∂μ ∂μ := by
          simpa [Function.uncurry, mul_comm, mul_left_comm, mul_assoc]
            using
              MeasureTheory.lintegral_lintegral_swap (μ := μ) (ν := μ)
                (f := fun y z => ENNReal.ofReal (|f (z - y)| * |φ z| * |g y|))
                (by
                  -- a.e.-measurability of the positive kernel
                  -- lintegral_lintegral_swap expects f : α → β → ℝ≥0∞
                  -- which becomes Function.uncurry f : α × β → ℝ≥0∞
                  -- Here α = β = G, f = fun y z => ENNReal.ofReal (|f (z - y)| * |φ z| * |g y|)
                  have hf_sub :
                      AEMeasurable (fun p : G × G => |f (p.2 - p.1)|) (μ.prod μ) := by
                    -- Use the strongly measurable representative of f
                    have h_sub : Measurable (fun p : G × G => p.2 - p.1) :=
                      measurable_snd.sub measurable_fst
                    set f₀ := hf_ae.mk f with hf₀_def
                    have hf₀_meas : StronglyMeasurable f₀ := hf_ae.stronglyMeasurable_mk
                    have hf₀_eq : f =ᵐ[μ] f₀ := hf_ae.ae_eq_mk
                    have h_ae :
                        AEStronglyMeasurable (fun p : G × G => f (p.2 - p.1)) (μ.prod μ) := by
                      have : (fun p : G × G => f (p.2 - p.1))
                          =ᵐ[μ.prod μ]
                          (fun p => f₀ (p.2 - p.1)) := by
                        -- Transport the a.e. equality f = f₀ along the quasi-measure-preserving map
                        -- p ↦ p.2 - p.1 from μ×μ to μ.
                        have h_sub_prod' :
                            MeasurePreserving (fun q : G × G => (q.2 - q.1, q.1))
                              (μ.prod μ) (μ.prod μ) :=
                          (measurePreserving_sub_prod (μ := μ) (ν := μ)).comp
                            (Measure.measurePreserving_swap (μ := μ) (ν := μ))
                        have h_fst_qmp' :
                            Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
                              (μ.prod μ) μ :=
                          MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
                        have h_qmp :
                            Measure.QuasiMeasurePreserving (fun p : G × G => p.2 - p.1)
                              (μ.prod μ) μ := by
                          simpa [Function.comp]
                            using h_fst_qmp'.comp h_sub_prod'.quasiMeasurePreserving
                        exact h_qmp.ae_eq_comp hf₀_eq
                      exact (hf₀_meas.comp_measurable h_sub).aestronglyMeasurable.congr this.symm
                    exact h_ae.norm.aemeasurable
                  have hg_fst :
                      AEMeasurable (fun p : G × G => |g p.1|) (μ.prod μ) :=
                    (hg_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
                  have hφ_snd :
                      AEMeasurable (fun p : G × G => |φ p.2|) (μ.prod μ) :=
                    (hφ_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
                  have h_prod : AEMeasurable (fun p : G × G =>
                      |f (p.2 - p.1)| * |φ p.2| * |g p.1|) (μ.prod μ) :=
                    (hf_sub.mul hφ_snd).mul hg_fst
                  exact h_prod.ennreal_ofReal)
        -- Bridge back from lintegrals to real integrals using nonnegativity and the congruences.
        -- Use hL_int and hR_int to rewrite both sides, then use h_symm.
        calc
          ∫ y, |g y| * ∫ z, |f (z - y)| * |φ z| ∂μ ∂μ
              = ∫ y, ∫ z, |f (z - y)| * |φ z| * |g y| ∂μ ∂μ := hL_int
          _ = ∫ z, ∫ y, |f (z - y)| * |g y| * |φ z| ∂μ ∂μ := by
              -- Use Tonelli via h_symm after converting to/from lintegral
              classical
              -- Package the nonnegative kernel as an ℝ≥0∞-valued function on the product.
              set H : G × G → ℝ≥0∞ :=
                fun p => ENNReal.ofReal (|f (p.2 - p.1)| * |φ p.2| * |g p.1|) with hH_def
              -- Left side: convert the inner real integral to the toReal of a lintegral,
              -- then the outer integral via `integral_toReal`.
              have h_left :
                  ∫ y, ∫ z, |f (z - y)| * |φ z| * |g y| ∂μ ∂μ
                    = (∫⁻ y, ∫⁻ z, H (y, z) ∂μ ∂μ).toReal := by
                -- Pointwise in y: bridge to lintegral.
                have h_eq_ae :
                    (fun y => ∫ z, |f (z - y)| * |φ z| * |g y| ∂μ)
                      =ᵐ[μ]
                        (fun y => (∫⁻ z, H (y, z) ∂μ).toReal) := by
                  refine Filter.Eventually.of_forall ?_
                  intro y
                  -- Measurability and nonnegativity in z for fixed y.
                  have h_meas :
                      AEStronglyMeasurable (fun z => |f (z - y)| * |φ z| * |g y|) μ := by
                    have hf_tr : AEStronglyMeasurable (fun z => f (z - y)) μ :=
                      hf_ae.comp_measurePreserving
                        (by
                          have h_add_neg_y :
                              MeasurePreserving (fun z : G => z + (-y)) μ μ :=
                            measurePreserving_add_right (μ := μ) (-y)
                          simpa [sub_eq_add_neg] using h_add_neg_y)
                    have h_const : AEStronglyMeasurable (fun _ : G => |g y|) μ :=
                      aestronglyMeasurable_const
                    exact ((hf_tr.norm.mul (hφ_ae.norm))).mul h_const
                  have h_nonneg_ae : 0 ≤ᵐ[μ]
                      fun z => |f (z - y)| * |φ z| * |g y| :=
                    Filter.Eventually.of_forall (fun _ =>
                      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
                  have h_eq :=
                    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
                      (μ := μ)
                      (f := fun z => |f (z - y)| * |φ z| * |g y|)
                      h_nonneg_ae h_meas
                  simpa [H, hH_def, mul_comm, mul_left_comm, mul_assoc]
                    using h_eq
                -- First, establish AEMeasurable H on μ.prod μ (needed in multiple places).
                have hH_aemeas : AEMeasurable H (μ.prod μ) := by
                  have hf_sub :
                      AEMeasurable (fun p : G × G => |f (p.2 - p.1)|) (μ.prod μ) := by
                    -- Use a strongly measurable representative of f and transport
                    -- along the quasi-measure-preserving map p ↦ p.2 - p.1.
                    have h_sub : Measurable (fun p : G × G => p.2 - p.1) :=
                      measurable_snd.sub measurable_fst
                    set f₀ := hf_ae.mk f with hf₀_def
                    have hf₀_meas : StronglyMeasurable f₀ := hf_ae.stronglyMeasurable_mk
                    have hf₀_eq : f =ᵐ[μ] f₀ := hf_ae.ae_eq_mk
                    have h_ae :
                        AEStronglyMeasurable (fun p : G × G => f (p.2 - p.1)) (μ.prod μ) := by
                      have : (fun p : G × G => f (p.2 - p.1))
                          =ᵐ[μ.prod μ]
                          (fun p => f₀ (p.2 - p.1)) := by
                        -- Transport a.e. equality along quasi-measure-preserving p ↦ p.2 - p.1
                        have h_sub_prod' :
                            MeasurePreserving (fun q : G × G => (q.2 - q.1, q.1))
                              (μ.prod μ) (μ.prod μ) :=
                          (measurePreserving_sub_prod (μ := μ) (ν := μ)).comp
                            (Measure.measurePreserving_swap (μ := μ) (ν := μ))
                        have h_fst_qmp' :
                            Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
                              (μ.prod μ) μ :=
                          MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
                        have h_qmp :
                            Measure.QuasiMeasurePreserving (fun p : G × G => p.2 - p.1)
                              (μ.prod μ) μ := by
                          simpa [Function.comp]
                            using h_fst_qmp'.comp h_sub_prod'.quasiMeasurePreserving
                        exact h_qmp.ae_eq_comp hf₀_eq
                      exact (hf₀_meas.comp_measurable h_sub).aestronglyMeasurable.congr this.symm
                    exact h_ae.norm.aemeasurable
                  have hg_fst :
                      AEMeasurable (fun p : G × G => |g p.1|) (μ.prod μ) :=
                    (hg_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
                  have hφ_snd :
                      AEMeasurable (fun p : G × G => |φ p.2|) (μ.prod μ) :=
                    (hφ_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
                  have h_prod :
                      AEMeasurable (fun p : G × G =>
                        |f (p.2 - p.1)| * |φ p.2| * |g p.1|) (μ.prod μ) :=
                    (hf_sub.mul hφ_snd).mul hg_fst
                  simpa [H, hH_def] using h_prod.ennreal_ofReal
                -- Outer integral: apply `integral_toReal` to y ↦ ∫⁻ z, H (y, z).
                have h_aemeas :
                    AEMeasurable (fun y => ∫⁻ z, H (y, z) ∂μ) μ :=
                  hH_aemeas.lintegral_prod_right'
                -- a.e.-finiteness via Tonelli's theorem and product finiteness of H.
                have h_fin : ∀ᵐ y ∂μ, (∫⁻ z, H (y, z) ∂μ) < ∞ := by
                  -- Obtain product finiteness by a change of variables to the (x, y) kernel
                  -- and apply the triple Hölder finiteness lemma.
                  have h_prod_fin :
                      ∫⁻ p : G × G, H p ∂(μ.prod μ) < ∞ := by
                    -- Change of variables (y, z) ↦ (z - y, y)
                    have h_pres :
                        MeasurePreserving (fun q : G × G => (q.2 - q.1, q.1))
                          (μ.prod μ) (μ.prod μ) :=
                      (measurePreserving_sub_prod (μ := μ) (ν := μ)).comp
                        (Measure.measurePreserving_swap (μ := μ) (ν := μ))
                    -- Pull back to the standard triple-product kernel
                    have h_map_eq :
                        ∫⁻ p : G × G, H p ∂(μ.prod μ)
                          = ∫⁻ p : G × G,
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|) ∂(μ.prod μ) := by
                      -- Evaluate H on the image of the shear
                      -- Use change of variables via the shear τ(y, z) = (z − y, y).
                      -- Build the `lintegral_map'` identity for the RHS kernel composed with τ.
                      have h_map :
                          ∫⁻ p : G × G,
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|)
                            ∂(Measure.map (fun q : G × G => (q.2 - q.1, q.1)) (μ.prod μ))
                            = ∫⁻ p : G × G,
                                ENNReal.ofReal
                                  (|f (p.2 - p.1)| * |g p.1| * |φ p.2|)
                              ∂(μ.prod μ) := by
                        -- Measurability of the RHS kernel on μ × μ, transported to map τ (μ×μ).
                        have hf_prod :
                            AEMeasurable (fun p : G × G => |f p.1|) (μ.prod μ) :=
                          (hf_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                            (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
                        have hg_prod :
                            AEMeasurable (fun p : G × G => |g p.2|) (μ.prod μ) :=
                          (hg_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                            (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
                        have hφ_sum :
                            AEMeasurable (fun p : G × G => |φ (p.1 + p.2)|) (μ.prod μ) := by
                          classical
                          have h_add : Measurable (fun p : G × G => p.1 + p.2) :=
                            measurable_fst.add measurable_snd
                          set φ0 : G → ℝ := hφ_ae.mk φ with hφ0_def
                          have hφ0_meas : StronglyMeasurable φ0 := hφ_ae.stronglyMeasurable_mk
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
                                  = (fun z : G × G => z.1 - z.2) ∘
                                      (fun q : G × G => (q.1, -q.2)) := by
                              funext q; simp [Function.comp, sub_eq_add_neg]
                            simpa [h_eq_fun]
                              using h_sub_qmp.comp h_neg_prod.quasiMeasurePreserving
                          have h_eq_prod :
                              (fun p : G × G => φ (p.1 + p.2))
                                =ᵐ[μ.prod μ]
                                  (fun p => φ0 (p.1 + p.2)) := by
                            simpa using h_add_qmp.ae_eq_comp (hφ_ae.ae_eq_mk)
                          have hφ_sum_sm : AEStronglyMeasurable
                              (fun p : G × G => φ (p.1 + p.2)) (μ.prod μ) :=
                            (h0_sm.aestronglyMeasurable.congr h_eq_prod.symm)
                          simpa [Real.norm_eq_abs]
                            using (hφ_sum_sm.norm.aemeasurable)
                        have hRHS_aemeas :
                            AEMeasurable (fun p : G × G =>
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|))
                              (Measure.map (fun q : G × G => (q.2 - q.1, q.1)) (μ.prod μ)) := by
                          have : AEMeasurable (fun p : G × G =>
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|)) (μ.prod μ) := by
                            have h_mul :
                                AEMeasurable (fun p : G × G =>
                                  |f p.1| * |g p.2| * |φ (p.1 + p.2)|) (μ.prod μ) :=
                              (hf_prod.mul hg_prod).mul hφ_sum
                            simpa using h_mul.ennreal_ofReal
                          simpa [h_pres.map_eq] using this
                        -- Apply lintegral_map' with τ and the a.e.-measurable RHS kernel.
                        simpa using
                          (lintegral_map'
                            (μ := μ.prod μ)
                            (f := fun p : G × G =>
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|))
                            (g := fun q : G × G => (q.2 - q.1, q.1))
                            hRHS_aemeas
                            (aemeasurable_id'.comp_measurable h_pres.measurable))
                      -- Unfold H and use the shear map to rewrite
                      -- ∫ H d(μ×μ) = ∫ (|f x| |g y| |φ (x+y)|) d(μ×μ)
                      -- We can extract this identity more directly by `simpa`.
                      -- To avoid redoing the measurability proof above, just use simp.
                      -- Note: h_map states ∫ H d(map τ μ×μ) = ∫ H ∘ τ d(μ×μ);
                      -- use map_eq for τ and expand H ∘ τ.
                      have :
                          (fun p : G × G => H p)
                            = fun p : G × G =>
                                ENNReal.ofReal
                                  (|f (p.2 - p.1)| * |φ p.2| * |g p.1|) := rfl
                      -- Using map_eq, the change of variables identity is immediate by simp.
                      -- Provide the final identity directly:
                      -- ∫ H = ∫ ofReal (|f x| |g y| |φ (x+y)|) using the inverse shear.
                      -- We can instead appeal to the previously established identity via
                      -- `measurePreserving_sub_prod` symmetry as in earlier parts of the proof.
                      -- For brevity, we establish it by rewriting the integrand and using map_eq.
                      calc
                        ∫⁻ p : G × G, H p ∂(μ.prod μ)
                            = ∫⁻ p : G × G,
                                ENNReal.ofReal
                                  (|f (p.2 - p.1)| * |g p.1| * |φ p.2|)
                              ∂(μ.prod μ) := by
                                congr 1 with p
                                simp [H, hH_def, mul_comm, mul_left_comm, mul_assoc]
                        _ = ∫⁻ p : G × G,
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|)
                            ∂(Measure.map (fun q : G × G => (q.2 - q.1, q.1)) (μ.prod μ)) :=
                            h_map.symm
                        _ = ∫⁻ p : G × G,
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|)
                            ∂(μ.prod μ) := by rw [h_pres.map_eq]
                    sorry
                  -- Tonelli consequence: sections are a.e. finite on the left.
                  simpa using
                    (MeasureTheory.tonelli_ae_section_lt_top_of_aemeasurable_left
                      (μ := μ) (f := H) hH_aemeas h_prod_fin)
                -- Apply the bridge lemma identifying the outer integral.
                calc
                  ∫ y, ∫ z, |f (z - y)| * |φ z| * |g y| ∂μ ∂μ
                      = ∫ y, (∫⁻ z, H (y, z) ∂μ).toReal ∂μ :=
                        integral_congr_ae h_eq_ae
                  _ = (∫⁻ y, ∫⁻ z, H (y, z) ∂μ ∂μ).toReal := by
                        simpa using (MeasureTheory.integral_toReal h_aemeas h_fin)
              -- Right side: the same conversion with y and z swapped.
              have h_right :
                  ∫ z, ∫ y, |f (z - y)| * |g y| * |φ z| ∂μ ∂μ
                    = (∫⁻ z, ∫⁻ y, H (y, z) ∂μ ∂μ).toReal := by
                -- Pointwise in z: bridge to lintegral.
                have h_eq_ae :
                    (fun z => ∫ y, |f (z - y)| * |g y| * |φ z| ∂μ)
                      =ᵐ[μ]
                        (fun z => (∫⁻ y, H (y, z) ∂μ).toReal) := by
                  refine Filter.Eventually.of_forall ?_
                  intro z
                  have h_meas :
                      AEStronglyMeasurable (fun y => |f (z - y)| * |g y| * |φ z|) μ := by
                    have hg_tr : AEStronglyMeasurable (fun y => g y) μ := hg_ae
                    have h_const : AEStronglyMeasurable (fun _ : G => |φ z|) μ :=
                      aestronglyMeasurable_const
                    have hf_tr : AEStronglyMeasurable (fun y => f (z - y)) μ := by
                      -- z - y = -(y - z) = -(y + (-z))
                      have h_neg : MeasurePreserving (fun y : G => -y) μ μ :=
                        Measure.measurePreserving_neg (μ := μ)
                      have h_add_neg_z : MeasurePreserving (fun y : G => y + (-z)) μ μ :=
                        measurePreserving_add_right (μ := μ) (-z)
                      have h_comp : MeasurePreserving (fun y : G => -(y + (-z))) μ μ :=
                        h_neg.comp h_add_neg_z
                      have : (fun y : G => f (z - y)) = (fun y : G => f (-(y + (-z)))) := by
                        funext y; simp [sub_eq_add_neg, neg_add_rev, add_comm]
                      rw [this]
                      exact hf_ae.comp_measurePreserving h_comp
                    exact ((hf_tr.norm.mul (hg_tr.norm))).mul h_const
                  have h_nonneg_ae : 0 ≤ᵐ[μ]
                      fun y => |f (z - y)| * |g y| * |φ z| :=
                    Filter.Eventually.of_forall (fun _ =>
                      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
                  have h_eq :=
                    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
                      (μ := μ)
                      (f := fun y => |f (z - y)| * |g y| * |φ z|)
                      h_nonneg_ae h_meas
                  simpa [H, hH_def, mul_comm, mul_left_comm, mul_assoc]
                    using h_eq
                -- First, establish AEMeasurable H on μ.prod μ (reusing for multiple places).
                have hH_aemeas : AEMeasurable H (μ.prod μ) := by
                  have hf_sub :
                      AEMeasurable (fun p : G × G => |f (p.2 - p.1)|) (μ.prod μ) := by
                    -- As above for the left side.
                    have h_sub : Measurable (fun p : G × G => p.2 - p.1) :=
                      measurable_snd.sub measurable_fst
                    set f₀ := hf_ae.mk f with hf₀_def
                    have hf₀_meas : StronglyMeasurable f₀ := hf_ae.stronglyMeasurable_mk
                    have hf₀_eq : f =ᵐ[μ] f₀ := hf_ae.ae_eq_mk
                    have h_ae :
                        AEStronglyMeasurable (fun p : G × G => f (p.2 - p.1)) (μ.prod μ) := by
                      have : (fun p : G × G => f (p.2 - p.1))
                          =ᵐ[μ.prod μ]
                          (fun p => f₀ (p.2 - p.1)) := by
                        have h_sub_prod' :
                            MeasurePreserving (fun q : G × G => (q.2 - q.1, q.1))
                              (μ.prod μ) (μ.prod μ) :=
                          (measurePreserving_sub_prod (μ := μ) (ν := μ)).comp
                            (Measure.measurePreserving_swap (μ := μ) (ν := μ))
                        have h_fst_qmp' :
                            Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
                              (μ.prod μ) μ :=
                          MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
                        have h_qmp :
                            Measure.QuasiMeasurePreserving (fun p : G × G => p.2 - p.1)
                              (μ.prod μ) μ := by
                          simpa [Function.comp]
                            using h_fst_qmp'.comp h_sub_prod'.quasiMeasurePreserving
                        exact h_qmp.ae_eq_comp hf₀_eq
                      exact (hf₀_meas.comp_measurable h_sub).aestronglyMeasurable.congr this.symm
                    exact h_ae.norm.aemeasurable
                  have hg_fst :
                      AEMeasurable (fun p : G × G => |g p.1|) (μ.prod μ) :=
                    (hg_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
                  have hφ_snd :
                      AEMeasurable (fun p : G × G => |φ p.2|) (μ.prod μ) :=
                    (hφ_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
                  have h_prod :
                      AEMeasurable (fun p : G × G =>
                        |f (p.2 - p.1)| * |φ p.2| * |g p.1|) (μ.prod μ) :=
                    (hf_sub.mul hφ_snd).mul hg_fst
                  simpa [H, hH_def] using h_prod.ennreal_ofReal
                -- Outer integral: apply `integral_toReal` to z ↦ ∫⁻ y, H (y, z).
                have h_aemeas :
                    AEMeasurable (fun z => ∫⁻ y, H (y, z) ∂μ) μ :=
                  -- H (y, z) = ofReal (|f (z - y)| * |φ z| * |g y|)
                  -- We need AEMeasurable (fun z ↦ ∫⁻ y, H (y, z) ∂μ) μ
                  -- which is lintegral_prod_left' applied to the transposed kernel
                  hH_aemeas.lintegral_prod_left'
                have h_fin : ∀ᵐ z ∂μ, (∫⁻ y, H (y, z) ∂μ) < ∞ := by
                  -- Same finiteness of sections, now for the right fibres.
                  have h_prod_fin :
                      ∫⁻ p : G × G, H p ∂(μ.prod μ) < ∞ := by
                    -- As above via the shear and the triple Hölder finiteness lemma.
                    have h_pres :
                        MeasurePreserving (fun q : G × G => (q.2 - q.1, q.1))
                          (μ.prod μ) (μ.prod μ) :=
                      (measurePreserving_sub_prod (μ := μ) (ν := μ)).comp
                        (Measure.measurePreserving_swap (μ := μ) (ν := μ))
                    have h_map_eq :
                        ∫⁻ p : G × G, H p ∂(μ.prod μ)
                          = ∫⁻ p : G × G,
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|) ∂(μ.prod μ) := by
                      -- This is the same change-of-variables identity as in h_left.
                      -- Reproduce it here via lintegral_map' and the shear τ(y,z) = (z − y, y).
                      -- Build the `lintegral_map'` identity for the RHS kernel composed with τ.
                      have h_map :
                          ∫⁻ p : G × G,
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|)
                            ∂(Measure.map (fun q : G × G => (q.2 - q.1, q.1)) (μ.prod μ))
                            = ∫⁻ p : G × G,
                                ENNReal.ofReal
                                  (|f (p.2 - p.1)| * |g p.1| * |φ p.2|)
                              ∂(μ.prod μ) := by
                        -- AEMeasurability of the RHS kernel on μ × μ, transported to map τ (μ×μ).
                        have hf_prod :
                            AEMeasurable (fun p : G × G => |f p.1|) (μ.prod μ) :=
                          (hf_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                            (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
                        have hg_prod :
                            AEMeasurable (fun p : G × G => |g p.2|) (μ.prod μ) :=
                          (hg_ae.norm.aemeasurable).comp_quasiMeasurePreserving
                            (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
                        have hφ_sum :
                            AEMeasurable (fun p : G × G => |φ (p.1 + p.2)|) (μ.prod μ) := by
                          classical
                          have h_add : Measurable (fun p : G × G => p.1 + p.2) :=
                            measurable_fst.add measurable_snd
                          set φ0 : G → ℝ := hφ_ae.mk φ with hφ0_def
                          have hφ0_meas : StronglyMeasurable φ0 := hφ_ae.stronglyMeasurable_mk
                          have h0_sm : StronglyMeasurable (fun p : G × G => φ0 (p.1 + p.2)) :=
                            hφ0_meas.comp_measurable h_add
                          -- Quasi-measure-preserving addition via subtraction shear + negation.
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
                                  = (fun z : G × G => z.1 - z.2) ∘
                                      (fun q : G × G => (q.1, -q.2)) := by
                              funext q; simp [Function.comp, sub_eq_add_neg]
                            simpa [h_eq_fun]
                              using h_sub_qmp.comp h_neg_prod.quasiMeasurePreserving
                          have h_eq_prod :
                              (fun p : G × G => φ (p.1 + p.2))
                                =ᵐ[μ.prod μ]
                                  (fun p => φ0 (p.1 + p.2)) := by
                            simpa using h_add_qmp.ae_eq_comp (hφ_ae.ae_eq_mk)
                          have hφ_sum_sm : AEStronglyMeasurable
                              (fun p : G × G => φ (p.1 + p.2)) (μ.prod μ) :=
                            (h0_sm.aestronglyMeasurable.congr h_eq_prod.symm)
                          simpa [Real.norm_eq_abs]
                            using (hφ_sum_sm.norm.aemeasurable)
                        have hRHS_aemeas :
                            AEMeasurable (fun p : G × G =>
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|))
                              (Measure.map (fun q : G × G => (q.2 - q.1, q.1)) (μ.prod μ)) := by
                          have : AEMeasurable (fun p : G × G =>
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|)) (μ.prod μ) := by
                            have h_mul :
                                AEMeasurable (fun p : G × G =>
                                  |f p.1| * |g p.2| * |φ (p.1 + p.2)|) (μ.prod μ) :=
                              (hf_prod.mul hg_prod).mul hφ_sum
                            simpa using h_mul.ennreal_ofReal
                          simpa [h_pres.map_eq] using this
                        -- Apply lintegral_map' with τ and the a.e.-measurable RHS kernel.
                        simpa using
                          (lintegral_map'
                            (μ := μ.prod μ)
                            (f := fun p : G × G =>
                              ENNReal.ofReal
                                (|f p.1| * |g p.2| * |φ (p.1 + p.2)|))
                            (g := fun q : G × G => (q.2 - q.1, q.1))
                            hRHS_aemeas
                            (aemeasurable_id'.comp_measurable h_pres.measurable))
                      -- Conclude the desired identity by using h_map and h_pres.map_eq.
                      -- This is the same pattern as in h_left (lines 752-767).
                      -- We need to combine h_map with h_pres.map_eq to get the result.
                      calc
                        ∫⁻ p : G × G, H p ∂(μ.prod μ)
                            = ∫⁻ p : G × G,
                                ENNReal.ofReal (|g p.1| * (|φ p.2| * |f (p.2 - p.1)|))
                              ∂(μ.prod μ) := by
                                congr 1 with p
                                simp [H, hH_def, mul_comm, mul_left_comm, mul_assoc]
                        _ = ∫⁻ p : G × G,
                              ENNReal.ofReal (|f (p.2 - p.1)| * |g p.1| * |φ p.2|)
                            ∂(μ.prod μ) := by
                              congr 1 with p
                              simp [mul_comm, mul_left_comm, mul_assoc]
                        _ = ∫⁻ p : G × G,
                              ENNReal.ofReal (|f p.1| * |g p.2| * |φ (p.1 + p.2)|)
                            ∂(Measure.map (fun q : G × G => (q.2 - q.1, q.1)) (μ.prod μ)) :=
                            h_map.symm
                        _ = ∫⁻ p : G × G,
                              ENNReal.ofReal (|f p.1| * |g p.2| * |φ (p.1 + p.2)|)
                            ∂(μ.prod μ) := by rw [h_pres.map_eq]
                    sorry
                  simpa using
                    (MeasureTheory.tonelli_ae_section_lt_top_of_aemeasurable_right
                      (μ := μ) (f := H) hH_aemeas h_prod_fin)
                calc
                  ∫ z, ∫ y, |f (z - y)| * |g y| * |φ z| ∂μ ∂μ
                      = ∫ z, (∫⁻ y, H (y, z) ∂μ).toReal ∂μ :=
                        integral_congr_ae h_eq_ae
                  _ = (∫⁻ z, ∫⁻ y, H (y, z) ∂μ ∂μ).toReal := by
                        simpa using (MeasureTheory.integral_toReal h_aemeas h_fin)
              -- Conclude by symmetry on ℝ≥0∞ via h_symm and apply toReal.
              have := congrArg ENNReal.toReal h_symm
              simpa [h_left, h_right]
                using this
          _ = ∫ z, |φ z| * ∫ y, |f (z - y)| * |g y| ∂μ ∂μ := hR_int.symm
      -- Assemble the pieces: substitute `h2`, swap, and identify `K`.
      have : ∫ y, ∫ x, |f (x - y)| * |φ x| * |g y| ∂μ ∂μ
            = ∫ z, |φ z| * ∫ y, |f (z - y)| * |g y| ∂μ ∂μ := by
        rw [h3]
        exact h_swap'
      -- Identify the inner integral with `K` and combine with h_swap.
      calc
        ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
            = ∫ y, ∫ x, |f x| * |φ (x + y)| * |g y| ∂μ ∂μ := h_swap
        _ = ∫ y, ∫ x, |f (x - y)| * |φ x| * |g y| ∂μ ∂μ := by
            -- For each y, rewrite the inner integral by pulling out |g y| and
            -- applying the change of variables x ↦ x + y (previously proved as h_inner_change).
            refine integral_congr_ae ?_
            refine Filter.Eventually.of_forall ?_
            intro y
            calc
              ∫ x, |f x| * |φ (x + y)| * |g y| ∂μ
                  = ∫ x, (|g y| * (|f x| * |φ (x + y)|)) ∂μ := by
                    congr 1 with x; ring
              _ = |g y| * ∫ x, |f x| * |φ (x + y)| ∂μ := by
                    rw [integral_const_mul]
              _ = |g y| * ∫ z, |f (z - y)| * |φ z| ∂μ := by
                    simp [h_inner_change y]
              _ = ∫ z, |f (z - y)| * |φ z| * |g y| ∂μ := by
                    simp [integral_const_mul, mul_comm, mul_left_comm, mul_assoc]
              _ = ∫ x, |f (x - y)| * |φ x| * |g y| ∂μ := by
                    simp
        _ = ∫ z, |φ z| * ∫ y, |f (z - y)| * |g y| ∂μ ∂μ := this
        _ = ∫ z, K z * |φ z| ∂μ := by
            congr 1 with z
            rw [hK, mul_comm]
  -- We will need that K ∈ L^r(μ).
  have hK_mem : MemLp K r μ := by
    -- First, record a.e.-strong measurability of the kernel on the product and infer
    -- measurability of x ↦ ∫ |f (x - y)| |g y| dμ(y).
    classical
    -- AEmesurability of (p.1 - p.2) under μ.prod μ ⇒ a.e. measurability of f(p.1 - p.2)
    have h_sub_prod :
        MeasurePreserving (fun q : G × G => (q.1 - q.2, q.2)) (μ.prod μ) (μ.prod μ) :=
      measurePreserving_sub_prod (μ := μ) (ν := μ)
    have h_fst_qmp :
        Measure.QuasiMeasurePreserving (fun q : G × G => q.1) (μ.prod μ) μ :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
    have h_sub_qmp :
        Measure.QuasiMeasurePreserving (fun p : G × G => p.1 - p.2) (μ.prod μ) μ := by
      simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
        using h_fst_qmp.comp h_sub_prod.quasiMeasurePreserving
    have hf_prod :
        AEStronglyMeasurable (fun p : G × G => |f (p.1 - p.2)|) (μ.prod μ) := by
      have := (hf_ae.norm).comp_quasiMeasurePreserving h_sub_qmp
      simpa using this
    have hg_prod :
        AEStronglyMeasurable (fun p : G × G => |g p.2|) (μ.prod μ) := by
      exact (hg_ae.norm).comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
    have h_kernel_aemeas :
        AEStronglyMeasurable (fun p : G × G => |f (p.1 - p.2)| * |g p.2|) (μ.prod μ) :=
      (hf_prod.mul hg_prod)
    have hK_aesm : AEStronglyMeasurable K μ := by
      -- Use the product measurability lemma for Bochner integrals along the second coordinate.
      have :=
        MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := μ) (ν := μ) (f := fun p : G × G => (|f (p.1 - p.2)| * |g p.2|))
          h_kernel_aemeas
      simpa [K, hK] using this
    sorry
  have h_holder : ∫ z, K z * |φ z| ∂μ ≤
      (eLpNorm K r μ).toReal * (eLpNorm φ rC μ).toReal := by
    -- Apply Hölder to real-valued functions using norms = abs.
    -- Since K is nonnegative, |K z| = K z.
    have h_eq : ∫ z, K z * |φ z| ∂μ = ∫ z, |K z| * |φ z| ∂μ := by
      congr 1 with z
      rw [abs_of_nonneg (hK_nonneg z)]
    rw [h_eq]
    simpa [Real.norm_eq_abs] using
      (holder_integral_norm_mul_le (μ := μ) (p := r) (q := rC)
        hr_le hrC_le h_conj K φ hK_mem hφ)
  -- Use Lp duality to bound ‖K‖_r via pairings against the unit ball of L^{rC}.
  have hK_toReal_le : (eLpNorm K r μ).toReal ≤
      (eLpNorm (fun x => f x) p μ * eLpNorm (fun y => g y) q μ).toReal := by
    -- Apply the duality lemma with p = r, q = rC and f := K.
    -- We supply the pairing bound using the trilinear Young/HBL estimate specialized
    -- to φ with (eLpNorm φ rC μ).toReal ≤ 1.
    refine
      SchwartzDensityLp.eLpNorm_le_of_dual_bound
        (μ := μ)
        (p := r) (q := rC)
        ?hp_one_lt ?hq_one_lt hrc
        (hp_ne_top := hr_ne_top)
        (f := K) hK_mem
        (C := (eLpNorm (fun x => f x) p μ * eLpNorm (fun y => g y) q μ).toReal) ?h_pairing_bound
    · exact hr_one_lt
    · exact hrC_one_lt
    · -- Pairing bound: for any ψ ∈ L^{rC} with norm ≤ 1, control |∫ K ψ|.
      intro ψ hψ_mem hψ_norm_le
      -- First, `K·ψ` is integrable by Hölder (product of L^r and L^{rC}).
      have h_mul_int : Integrable (fun x => K x * ψ x) μ :=
        memLp_mul_of_memLp_conjugate (μ := μ) (p := r) (q := rC) hrc K ψ hK_mem hψ_mem
      -- Reduce to a nonnegative pairing using |ψ| and the nonnegativity of K.
      have h_abs_int :
          |∫ x, K x * ψ x ∂μ| ≤ ∫ x, K x * |ψ x| ∂μ := by
        -- abs ∫ ≤ ∫ abs, and |K·ψ| = K·|ψ| since K ≥ 0.
        calc
          |∫ x, K x * ψ x ∂μ|
              ≤ ∫ x, |K x * ψ x| ∂μ := by
                    simpa using (abs_integral_le_integral_abs (μ := μ)
                      (f := fun x => K x * ψ x))
          _ = ∫ x, K x * |ψ x| ∂μ := by
                have h_eq : (fun x => |K x * ψ x|) = fun x => K x * |ψ x| := by
                  funext x
                  have := abs_mul (K x) (ψ x)
                  have hKabs : |K x| = K x := by simp [abs_of_nonneg (hK_nonneg x)]
                  simpa [hKabs, mul_comm, mul_left_comm, mul_assoc] using this
                simp [h_eq]
      -- Bound the nonnegative pairing by the trilinear Young bound with φ := |ψ| and
      -- using (eLpNorm |ψ| rC μ).toReal = (eLpNorm ψ rC μ).toReal ≤ 1.
      have hψ_abs_mem : MemLp (fun x => |ψ x|) rC μ := hψ_mem.abs
      sorry
  have h_prod_toReal :
      (eLpNorm (fun x => f x) p μ * eLpNorm (fun y => g y) q μ).toReal
        = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
    -- Simplify `toReal` of a finite product.
    have hf_ne_top : eLpNorm f p μ ≠ ∞ := ne_of_lt hf.eLpNorm_lt_top
    have hg_ne_top : eLpNorm g q μ ≠ ∞ := ne_of_lt hg.eLpNorm_lt_top
    simp [ENNReal.toReal_mul, hf_ne_top, hg_ne_top]
  -- Final estimate.
  calc
    ∫ x, ∫ y, |f x| * |g y| * |φ (x + y)| ∂μ ∂μ
        = ∫ z, K z * |φ z| ∂μ := h_rewrite
    _ ≤ (eLpNorm K r μ).toReal * (eLpNorm φ rC μ).toReal := h_holder
    _ ≤ ((eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal) * (eLpNorm φ rC μ).toReal := by
      have hK_toReal_le' :
          (eLpNorm K r μ).toReal ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
        rw [← h_prod_toReal]
        exact hK_toReal_le
      exact mul_le_mul_of_nonneg_right hK_toReal_le' (ENNReal.toReal_nonneg)

lemma lintegral_convolution_norm_bound
    (μ : Measure G) [SFinite μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (f g : G → ℂ) (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 < q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_one_lt : 1 < r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
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
  have pairing_bound_skeleton :
      ∀ (rC : ℝ≥0∞), IsConjugateExponent r rC →
        ∀ φ : G → ℝ, MemLp φ rC μ →
          (eLpNorm φ rC μ ≤ 1) →
            ∫ x, K x * |φ x| ∂ μ ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
    intro rC hrc φ hφ hφ_le
    -- This will be proved by Fubini + the trilinear bound established in young_pairing_bound
    -- after rewriting K and changing variables x ↦ x + y or x ↦ x - y.
    -- Implementation deferred to the next step.
    sorry

  -- From pairing_bound_skeleton and L^r duality, we will deduce the desired L^r bound.
  -- We record the intended final step here and leave its invocation for the next patch.
  -- TODO: apply Lp duality with r and rC, then raise both sides to r.toReal.
  -- The following `sorry` marks the remaining half of the proof.
  sorry
