import Frourio.Analysis.HolderInequality.HolderInequality
import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
import Frourio.Analysis.SchwartzDensityLp.FubiniSection
import Frourio.Analysis.YoungInequality.YoungInequalityCore1
import Mathlib.Analysis.Convolution
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

section ConvolutionAuxiliary

variable {G : Type*}
variable [MeasurableSpace G]
variable (μ : Measure G) [SFinite μ]
variable [NormedAddCommGroup G]
variable [μ.IsAddRightInvariant] [μ.IsNegInvariant]
variable [MeasurableAdd₂ G] [MeasurableNeg G]

noncomputable def A_fun (μpartial : ℕ → Measure G) (f : G → ℂ)
    (r : ℝ≥0∞) (N : ℕ) (y : G) : ℝ :=
  (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal

-- Measurability of y ↦ (eLpNorm (x ↦ f(x−y)) r (μpartial N)).toReal on μpartial N.
lemma A_measurable_partial
    (f : G → ℂ) (r : ℝ≥0∞) (μpartial : ℕ → Measure G)
    (hr_ne_zero : r ≠ 0) (hr_ne_top : r ≠ ∞)
    (hf_meas : AEStronglyMeasurable f μ)
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (hμpartial_prod_ac : ∀ N, (μpartial N).prod (μpartial N) ≪ μ.prod μ) :
    ∀ N, AEStronglyMeasurable (fun y => A_fun μpartial f r N y) (μpartial N) := by
  intro N
  classical
  -- Build the product-measurable kernel (without g) on μ.prod μ first,
  -- then transfer to (μpartial N).prod (μpartial N) via absolute continuity.
  let g1 : G → ℂ := fun _ => (1 : ℂ)
  have h_kernel_norm_meas_one :
      AEStronglyMeasurable
        (fun q : G × G => ‖f (q.1 - q.2) * g1 q.2‖) (μ.prod μ) :=
    (convolution_kernel_aestronglyMeasurable (μ := μ)
      (f := f) (g := g1) hf_meas
        (aestronglyMeasurable_const : AEStronglyMeasurable g1 μ)).norm
  have hF_meas_prod :
      AEStronglyMeasurable (fun q : G × G => ‖f (q.1 - q.2)‖) (μ.prod μ) := by
    -- From ‖f * g1‖ measurable, derive ‖f‖ measurable using g1 = 1
    have h1 : (fun q : G × G => ‖f (q.1 - q.2) * g1 q.2‖)
        = (fun q => ‖f (q.1 - q.2)‖) := by
      ext q
      simp [g1, mul_one]
    rw [← h1]
    exact h_kernel_norm_meas_one
  -- Transfer measurability to the partial product measure.
  have hF_meas_partial :
      AEStronglyMeasurable (fun q : G × G => ‖f (q.1 - q.2)‖)
        ((μpartial N).prod (μpartial N)) :=
    (hF_meas_prod.mono_ac (hμpartial_prod_ac N))
  -- Raise to r.toReal and integrate w.r.t. x to obtain the lintegral measurability in y.
  have h_integrand_aemeasurable :
      AEMeasurable
        (fun y => ∫⁻ x, (‖f (x - y)‖ₑ) ^ r.toReal ∂ μpartial N)
        (μpartial N) := by
    -- μpartial N is a finite measure, hence SFinite
    haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
    haveI : SFinite (μpartial N) := inferInstance
    have := hF_meas_partial.aemeasurable.enorm.pow_const r.toReal
    -- rearrange variables (x,y) ↔ (q.1,q.2)
    simpa [Function.uncurry]
      using this.lintegral_prod_left'
  -- Conclude measurability of eLpNorm_y via the r-power/ToReal representation.
  have hA_eLpMeas :
      AEMeasurable
        (fun y => eLpNorm (fun x => f (x - y)) r (μpartial N)) (μpartial N) := by
    -- Use the eLpNorm = lintegral^(1/r) representation.
    have :=
      (measurable_id.pow_const (1 / r.toReal)).comp_aemeasurable
        h_integrand_aemeasurable
    refine this.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    simp [eLpNorm_eq_lintegral_rpow_enorm (μ := μpartial N)
      (f := fun x => f (x - y)) hr_ne_zero hr_ne_top, one_div,
      ENNReal.rpow_mul, mul_comm, mul_left_comm, mul_assoc]
  -- Finally, take toReal and upgrade to AEStronglyMeasurable.
  exact (hA_eLpMeas.ennreal_toReal).aestronglyMeasurable

-- Finite‑measure exponent monotonicity in the r→p direction on a partial measure family.
-- Stub lemma placed here so it is available to subsequent proofs.
lemma exponent_mono_rp_on_partial_measure
    (f : G → ℂ) (p r : ℝ≥0∞) (μpartial : ℕ → Measure G)
    (hp_le_hr : p ≤ r)
    (hf : MemLp f p μ)
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (hμpartial_ac : ∀ N, μpartial N ≪ μ) :
    ∀ N y,
      ((μpartial N) Set.univ) ^ (1 / r.toReal - 1 / p.toReal)
        * eLpNorm (fun x => f (x - y)) p (μpartial N)
      ≤ eLpNorm (fun x => f (x - y)) r (μpartial N) := by
  intro N y
  classical
  haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
  have h_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using measurePreserving_add_right (μ := μ) (-y)
  have h_shift_mem : MemLp (fun x => f (x - y)) p μ :=
    hf.comp_measurePreserving h_pres
  have h_meas_μ : AEStronglyMeasurable (fun x => f (x - y)) μ :=
    h_shift_mem.aestronglyMeasurable
  have h_meas_partial :
      AEStronglyMeasurable (fun x => f (x - y)) (μpartial N) :=
    h_meas_μ.mono_ac (hμpartial_ac N)
  by_cases hμz : μpartial N = 0
  · -- Zero measure: both sides are zero.
    simp [hμz]
  · -- Apply the finite-measure p→r comparison and rearrange.
    have h_base :
        eLpNorm (fun x => f (x - y)) p (μpartial N)
          ≤ ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
              * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
      simpa [mul_comm]
        using
          (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
            (μ := μpartial N) (f := fun x => f (x - y))
            (p := p) (q := r) hp_le_hr h_meas_partial)
    -- Multiply both sides by μ(univ)^(1/r − 1/p) and cancel exponents.
    set α : ℝ≥0∞ := ((μpartial N) Set.univ) ^ (1 / r.toReal - 1 / p.toReal) with hα
    set β : ℝ≥0∞ := ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal) with hβ
    have hμU_ne_zero : (μpartial N) Set.univ ≠ 0 := by
      simpa [Measure.measure_univ_eq_zero] using hμz
    have hμU_ne_top : (μpartial N) Set.univ ≠ ∞ := by simp
    have h_prod_one : α * β = (1 : ℝ≥0∞) := by
      have h := ENNReal.rpow_add (x := (μpartial N) Set.univ)
                  (y := (1 / r.toReal - 1 / p.toReal))
                  (z := (1 / p.toReal - 1 / r.toReal))
                  hμU_ne_zero hμU_ne_top
      have : α * β
          = (μpartial N) Set.univ
              ^ ((1 / r.toReal - 1 / p.toReal) + (1 / p.toReal - 1 / r.toReal)) := by
        simpa [hα, hβ, mul_comm, mul_left_comm, mul_assoc] using h.symm
      simp [this]
    have h_mul := mul_le_mul_left' h_base α
    -- α * (β * ‖·‖_r) = (α * β) * ‖·‖_r = ‖·‖_r
    calc
      α * eLpNorm (fun x => f (x - y)) p (μpartial N)
          ≤ α * (β * eLpNorm (fun x => f (x - y)) r (μpartial N)) := h_mul
      _ = (α * β) * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ = eLpNorm (fun x => f (x - y)) r (μpartial N) := by
            simp [h_prod_one]

lemma A_uniform_bound_s0_of_split
    (f : G → ℂ) (p r s₀ : ℝ≥0∞)
    (μpartial : ℕ → Measure G)
    (hf : MemLp f p μ) (hf_r : MemLp f r μ)
    (hs₀_ne_zero : s₀ ≠ 0) (hs₀_ne_top : s₀ ≠ ∞)
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (hμpartial_le : ∀ N, μpartial N ≤ μ)
    :
    ∀ N,
      (eLpNorm (fun y => A_fun μpartial f r N y) s₀ (μpartial N)).toReal
        ≤ ((μpartial N) Set.univ ^ (1 / s₀.toReal) * eLpNorm f r μ).toReal := by
  -- See the proof sketch discussed in the main lemma: combine
  -- finite-measure exponent monotonicity p→r, measure monotonicity μpartial≤μ,
  -- translation invariance for L^p under μ, and exponent cancellation via h_split.
  intro N
  classical
  -- Notation
  set μN := μpartial N
  haveI : IsFiniteMeasure μN := hμpartial_fin N
  -- Basic properties for s₀
  have hs₀_pos : 0 < s₀.toReal := ENNReal.toReal_pos hs₀_ne_zero hs₀_ne_top
  have hs₀_nonneg : 0 ≤ s₀.toReal := le_of_lt hs₀_pos
  -- Rewrite the target as an inequality in ℝ≥0∞ and then use `toReal_mono`.
  have h_target :
      eLpNorm (fun y => A_fun μpartial f r N y) s₀ μN
        ≤ (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ := by
    -- Step 1: Reduce the left `eLpNorm` to the lintegral representation and bound the integrand.
    -- Define the auxiliary functions
    let A : G → ℝ := fun y => A_fun μpartial f r N y
    let B : G → ℝ≥0∞ := fun y => eLpNorm (fun x => f (x - y)) r μN
    -- Expand the eLpNorm on the left via the r-power representation and compare integrands.
    have h_eLp_A :=
      eLpNorm_eq_lintegral_rpow_enorm (μ := μN) (f := A) hs₀_ne_zero hs₀_ne_top
    -- Pointwise bound: ofReal (toReal (B y)) ≤ B y
    have h_pow_bound :
        ∀ᵐ y ∂ μN, (‖A y‖ₑ) ^ s₀.toReal ≤ (B y) ^ s₀.toReal := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      -- ‖A y‖ₑ = ofReal (A y) and A y = (B y).toReal
      have h_base : (‖A y‖ₑ) ≤ B y := by
        -- `A y = (B y).toReal` and `ofReal (toReal _) ≤ _`.
        simpa [A_fun, A, B,
          Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
          Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          using (ENNReal.ofReal_toReal_le (a := B y))
      exact ENNReal.rpow_le_rpow h_base hs₀_nonneg
    -- Therefore, (eLpNorm A s₀ μN) ^ s₀.toReal ≤ ∫ (B y)^s₀ dμN
    have h_step1 :
        (eLpNorm A s₀ μN) ^ s₀.toReal
          ≤ ∫⁻ y, (B y) ^ s₀.toReal ∂ μN := by
      -- h_eLp_A : eLpNorm A s₀ μN = (∫⁻ x, ‖A x‖ₑ ^ s₀.toReal ∂μN) ^ (1 / s₀.toReal)
      rw [h_eLp_A]
      have h_cancel : ((∫⁻ x, ‖A x‖ₑ ^ s₀.toReal ∂μN) ^ (1 / s₀.toReal)) ^ s₀.toReal
          = ∫⁻ x, ‖A x‖ₑ ^ s₀.toReal ∂μN := by
        have hs₀_toReal_ne_zero : s₀.toReal ≠ 0 := by
          have : 0 < s₀.toReal := hs₀_pos
          linarith
        rw [← ENNReal.rpow_mul, one_div]
        have : s₀.toReal⁻¹ * s₀.toReal = 1 := by
          rw [mul_comm]
          field_simp [hs₀_toReal_ne_zero]
        rw [this, ENNReal.rpow_one]
      rw [h_cancel]
      exact lintegral_mono_ae h_pow_bound
    -- Step 2: For each y, use finite-measure exponent monotonicity r→p on μN.
    have hf_meas : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
    have h_mono_r : ∀ y,
        eLpNorm (fun x => f (x - y)) r μN ≤ eLpNorm (fun x => f (x - y)) r μ := by
      intro y; exact eLpNorm_mono_measure (μ := μ) (ν := μN) (p := r)
        (f := fun x => f (x - y)) (hμpartial_le N)
    have h_translate_r : ∀ y,
        eLpNorm (fun x => f (x - y)) r μ = eLpNorm f r μ := by
      intro y
      have h :=
        eLpNorm_comp_add_right (μ := μ) (f := f) (y := -y) (p := r) hf_meas
      simpa [sub_eq_add_neg] using h
    have h_B_le_const : ∀ y, B y ≤ eLpNorm f r μ := by
      intro y; exact (h_mono_r y).trans (le_of_eq (h_translate_r y))
    -- Hence (B y)^s₀ ≤ (eLpNorm f r μ)^s₀ and integrate to bound the lintegral.
    have h_pow_mono : ∀ᵐ y ∂ μN, (B y) ^ s₀.toReal ≤ (eLpNorm f r μ) ^ s₀.toReal := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      exact ENNReal.rpow_le_rpow (h_B_le_const y) hs₀_nonneg
    have h_step2 :
        ∫⁻ y, (B y) ^ s₀.toReal ∂ μN ≤
          (μN Set.univ) * (eLpNorm f r μ) ^ s₀.toReal := by
      -- Integrate the pointwise bound; RHS is the integral of the constant.
      have h_const :
          (∫⁻ _ : G, (eLpNorm f r μ) ^ s₀.toReal ∂ μN)
            = (μN Set.univ) * (eLpNorm f r μ) ^ s₀.toReal := by
        rw [lintegral_const, mul_comm]
      exact (lintegral_mono_ae h_pow_mono).trans_eq h_const
    -- Combine step1 and step2, then extract (1/s₀) power.
    -- From h_step1: (‖A‖_{s₀,μN})^{s₀} ≤ ∫ (B^s₀).
    -- Thus (‖A‖_{s₀,μN})^{s₀} ≤ μN(univ) * (‖f‖_{r,μ})^{s₀}.
    have h_bound_rpow :
        (eLpNorm A s₀ μN) ^ s₀.toReal
          ≤ (μN Set.univ) * (eLpNorm f r μ) ^ s₀.toReal :=
      le_trans h_step1 h_step2
    -- Raise both sides to the power (1 / s₀) and simplify using rpow identities.
    have hs₀_toReal_ne_zero : s₀.toReal ≠ 0 := by
      have : 0 < s₀.toReal := hs₀_pos; linarith
    have h_nonneg : 0 ≤ 1 / s₀.toReal := by
      have : 0 < s₀.toReal := hs₀_pos
      exact div_nonneg (by norm_num) (le_of_lt this)
    -- Apply monotonicity of rpow with exponent 1/s₀.toReal > 0.
    have h_rpow_mono := ENNReal.rpow_le_rpow h_bound_rpow h_nonneg
    -- Rewrite LHS: ((‖A‖)^{s₀})^{1/s₀} = ‖A‖
    have hL :
        ((eLpNorm A s₀ μN) ^ s₀.toReal) ^ (1 / s₀.toReal)
          = eLpNorm A s₀ μN := by
      rw [one_div, ← ENNReal.rpow_mul]
      have : s₀.toReal * s₀.toReal⁻¹ = 1 := by
        field_simp [hs₀_toReal_ne_zero]
      rw [this, ENNReal.rpow_one]
    -- Rewrite RHS: (μN)^{1/s₀} * (‖f‖_r^{s₀})^{1/s₀} = (μN)^{1/s₀} * ‖f‖_r.
    have hR :
        ((μN Set.univ) * (eLpNorm f r μ) ^ s₀.toReal) ^ (1 / s₀.toReal)
          = (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ := by
      -- distribute rpow across the product and cancel s₀ on the second factor
      have h_distrib := ENNReal.mul_rpow_of_nonneg (μN Set.univ)
        ((eLpNorm f r μ) ^ s₀.toReal) h_nonneg
      have h_cancel :
          ((eLpNorm f r μ) ^ s₀.toReal) ^ (1 / s₀.toReal)
            = eLpNorm f r μ := by
        rw [one_div, ← ENNReal.rpow_mul]
        have : s₀.toReal * s₀.toReal⁻¹ = 1 := by
          field_simp [hs₀_toReal_ne_zero]
        rw [this, ENNReal.rpow_one]
      rw [h_cancel] at h_distrib
      exact h_distrib
    -- Conclude the desired bound in ℝ≥0∞.
    have : (eLpNorm A s₀ μN)
        ≤ (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ := by
      -- transform via the previous equalities
      rw [← hL, ← hR]
      exact h_rpow_mono
    exact this
  -- Finally, pass to `toReal` using finiteness of the right-hand side.
  -- The RHS is finite since μN is finite and ‖f‖_{r,μ} < ∞.
  have h_rhs_ne_top :
      (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ ≠ ∞ := by
    have hμ_fin : (μN Set.univ) ≠ ∞ := by simp
    have hμ_rpow_fin : (μN Set.univ) ^ (1 / s₀.toReal) ≠ ∞ := by
      have : 0 ≤ (1 / s₀.toReal) := by
        rw [one_div]
        exact inv_nonneg.mpr (le_of_lt hs₀_pos)
      exact ENNReal.rpow_ne_top_of_nonneg this hμ_fin
    have hf_r_fin : eLpNorm f r μ ≠ ∞ := by simpa using hf_r.eLpNorm_ne_top
    exact ENNReal.mul_ne_top hμ_rpow_fin hf_r_fin
  exact ENNReal.toReal_mono h_rhs_ne_top h_target

set_option maxHeartbeats 1000000 in
lemma lintegral_convolution_norm_bound
    (μ : Measure G) [SFinite μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (f g : G → ℂ) (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 < q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hf_r : MemLp f r μ) (hg : MemLp g q μ)
    (h_kernel_int :
      Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ))
    (h_pointwise_piece :
      ∀ N,
        (fun y =>
            (eLpNorm (fun x => f (x - y) * g y) r
              (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k)).toReal)
          =ᵐ[∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k]
          fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r
                (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k)).toReal) :
    ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal ∂ μ ≤
      (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal := by
  -- Start by extracting the exponent inequalities implied by `hp`, `hq`, and `hpqr`.
  have h_inv_p_le_one : p⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa [one_div] using (ENNReal.inv_le_inv).2 hp
  have h_inv_q_le_one : q⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa [one_div] using (ENNReal.inv_le_inv).2 (le_of_lt hq)
  have hpqr_inv : p⁻¹ + q⁻¹ = (1 : ℝ≥0∞) + r⁻¹ := by
    simpa [one_div, add_comm, add_left_comm, add_assoc] using hpqr
  have h_sum_le_two : p⁻¹ + q⁻¹ ≤ (1 : ℝ≥0∞) + 1 :=
    add_le_add h_inv_p_le_one h_inv_q_le_one
  have h_aux : (1 : ℝ≥0∞) + r⁻¹ ≤ (1 : ℝ≥0∞) + 1 := by
    simpa [hpqr_inv] using h_sum_le_two
  have h_inv_r_le_one : r⁻¹ ≤ (1 : ℝ≥0∞) :=
    ENNReal.le_of_add_le_add_left (by simp) h_aux
  have hr : 1 ≤ r :=
    (ENNReal.inv_le_inv).1 <| by simpa [one_div] using h_inv_r_le_one
  have hr_pos : (0 : ℝ≥0∞) < r := lt_of_lt_of_le (by simp) hr
  have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
  have hr_toReal_pos : 0 < r.toReal := ENNReal.toReal_pos hr_ne_zero hr_ne_top
  have hp_ne_top : p ≠ ∞ := by
    intro hp_top
    have h_eq : q⁻¹ = (1 : ℝ≥0∞) + r⁻¹ := by
      simpa [hp_top, one_div, ENNReal.inv_top, zero_add, add_comm, add_left_comm, add_assoc]
        using hpqr
    have h_le_one : (1 : ℝ≥0∞) + r⁻¹ ≤ 1 := by
      simpa [h_eq] using h_inv_q_le_one
    have h_le_one' : (1 : ℝ≥0∞) + r⁻¹ ≤ (1 : ℝ≥0∞) + 0 := by
      simpa using h_le_one
    have h_r_inv_le_zero : r⁻¹ ≤ (0 : ℝ≥0∞) :=
      (ENNReal.add_le_add_iff_left (by simp)).1 h_le_one'
    have h_zero_le : (0 : ℝ≥0∞) ≤ r⁻¹ := bot_le
    have h_r_inv_zero : r⁻¹ = 0 := le_antisymm h_r_inv_le_zero h_zero_le
    have hr_top : r = ∞ := ENNReal.inv_eq_zero.1 h_r_inv_zero
    exact hr_ne_top hr_top
  have hq_ne_top : q ≠ ∞ := by
    intro hq_top
    have h_eq : p⁻¹ = (1 : ℝ≥0∞) + r⁻¹ := by
      simpa [hq_top, one_div, ENNReal.inv_top, add_comm, add_left_comm, add_assoc]
        using hpqr
    have h_le_one : (1 : ℝ≥0∞) + r⁻¹ ≤ 1 := by
      simpa [h_eq, add_comm] using h_inv_p_le_one
    have h_le_one' : (1 : ℝ≥0∞) + r⁻¹ ≤ (1 : ℝ≥0∞) + 0 := by
      simpa using h_le_one
    have h_r_inv_le_zero : r⁻¹ ≤ (0 : ℝ≥0∞) :=
      (ENNReal.add_le_add_iff_left (by simp)).1 h_le_one'
    have h_zero_le : (0 : ℝ≥0∞) ≤ r⁻¹ := bot_le
    have h_r_inv_zero : r⁻¹ = 0 := le_antisymm h_r_inv_le_zero h_zero_le
    have hr_top : r = ∞ := ENNReal.inv_eq_zero.1 h_r_inv_zero
    exact hr_ne_top hr_top
  set pr := ENNReal.toReal p with hpr
  set qr := ENNReal.toReal q with hqr
  set rr := ENNReal.toReal r with hrr
  have h_young_real :
      rr =
        (pr * qr) /
          (pr + qr - pr * qr) := by
    have :=
      young_exponent_relation
        (p := p) (q := q) (r := r)
        hp (le_of_lt hq) hr hpqr hp_ne_top hq_ne_top hr_ne_top
    simpa [hpr, hqr, hrr] using this
  have h_section_int :
      ∀ᵐ x ∂μ, Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ :=
    integrable_norm_convolution_kernel_section
      (μ := μ) (f := f) (g := g) h_kernel_int

  classical
  set H : G → ℝ := fun x => ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ
  have h_H_nonneg :
      ∀ᵐ x ∂μ, 0 ≤ H x := by
    refine h_section_int.mono ?_
    intro x _
    have h_nonneg_fun :
        0 ≤ᵐ[μ] fun y => ‖f (x - y)‖ * ‖g y‖ :=
      Filter.Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa [H] using integral_nonneg_of_ae h_nonneg_fun

  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
  have hμ_sum : Measure.sum μn = μ := MeasureTheory.sum_sfiniteSeq μ
  let μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k
  have hμpartial_succ :
      ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1) := by
    intro N
    classical
    simp [μpartial, Nat.succ_eq_add_one, Finset.range_succ, add_comm, add_left_comm, add_assoc]
  have hμpartial_zero : μpartial 0 = μn 0 := by
    classical
    simp [μpartial]
  have hμn_le : ∀ n, μn n ≤ μ := fun n =>
    by
      simpa [μn] using MeasureTheory.sfiniteSeq_le (μ := μ) n
  have hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N) := by
    intro N
    classical
    refine Nat.rec ?base ?step N
    · simpa [μpartial] using (inferInstance : IsFiniteMeasure (μn 0))
    · intro k hk
      have hk' : IsFiniteMeasure (μpartial k + μn (k + 1)) := by infer_instance
      simpa [hμpartial_succ, Nat.succ_eq_add_one] using hk'
  have hμpartial_le_succ : ∀ N, μpartial N ≤ μpartial (N + 1) := by
    intro N s
    classical
    have hnonneg : 0 ≤ μn (N + 1) s := bot_le
    simp [hμpartial_succ, Nat.succ_eq_add_one, Measure.add_apply, hnonneg]
  have hμpartial_mono : Monotone μpartial :=
    monotone_nat_of_le_succ hμpartial_le_succ
  have hμpartial_le_smul :
      ∀ N, μpartial N ≤ ((N + 1 : ℝ≥0∞) • μ) := by
    intro N
    simpa [μpartial] using (sfiniteSeq_partial_le_smul (μ := μ) N)
  have hμpartial_ac : ∀ N, μpartial N ≪ μ := by
    intro N
    exact Measure.absolutelyContinuous_of_le_smul (hμpartial_le_smul N)
  have hμpartial_tendsto :
      ∀ ⦃s : Set G⦄, MeasurableSet s →
        Tendsto (fun N => μpartial N s) atTop (𝓝 (μ s)) := by
    exact sfiniteSeq_partial_tendsto (μ := μ)
  have hμpartial_prod_le :
      ∀ N,
        (μpartial N).prod (μpartial N) ≤
          (((N + 1 : ℝ≥0∞) * (N + 1 : ℝ≥0∞)) • (μ.prod μ)) := by
    intro N
    simpa [μpartial, μn]
      using (sfiniteSeq_partial_prod_le_smul (μ := μ) N)
  have hμpartial_prod_ac :
      ∀ N, (μpartial N).prod (μpartial N) ≪ μ.prod μ := by
    intro N
    exact Measure.absolutelyContinuous_of_le_smul (hμpartial_prod_le N)
  have hf_partial : ∀ N, MemLp f p (μpartial N) := by
    intro N
    refine hf.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have hf_r_partial : ∀ N, MemLp f r (μpartial N) := by
    intro N
    refine hf_r.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have h_translate_norm_bound :
      ∀ N y,
        eLpNorm (fun x => f (x - y)) r (μpartial N) ≤
          ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ := by
    intro N y
    exact
      sfiniteSeq_partial_translate_norm_bound
        (μ := μ)
        (f := f)
        (μpartial := μpartial)
        (hf := hf_r)
        (h_le := hμpartial_le_smul)
        N y
  have h_translate_norm_bound_toReal :
      ∀ N y,
        (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ≤
          ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal := by
    intro N y
    have h_bound := h_translate_norm_bound N y
    have h_pow_ne_top :
        ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ := by
      have h_exp_nonneg : 0 ≤ (1 / r).toReal := by simp [one_div]
      exact ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
    have h_const_ne_top :
        ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ :=
      ENNReal.mul_ne_top h_pow_ne_top hf_r.eLpNorm_ne_top
    exact ENNReal.toReal_mono h_const_ne_top h_bound
  have hg_partial : ∀ N, MemLp g q (μpartial N) := by
    intro N
    refine hg.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have h_pointwise_piece_partial :
      ∀ N,
        (fun y =>
            (eLpNorm (fun x => f (x - y) * g y) r (μpartial N)).toReal)
          =ᵐ[μpartial N]
          fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
    intro N
    simpa [μpartial, μn] using h_pointwise_piece N
  have hg_partial_one : ∀ N, MemLp g 1 (μpartial N) := by
    intro N
    exact (hg_partial N).mono_exponent (p := (1 : ℝ≥0∞)) (q := q) (le_of_lt hq)
  have hg_partial_int : ∀ N, Integrable g (μpartial N) := by
    intro N
    exact (memLp_one_iff_integrable).1 (hg_partial_one N)

  -- Preparatory bounds for the finite-measure pieces
  have h_kernel_int_partial :
      ∀ N,
        Integrable (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)) := by
    intro N
    classical
    have h_const_ne_top :
        ((N + 1 : ℝ≥0∞) * (N + 1 : ℝ≥0∞)) ≠ ∞ := by
      simpa using
        ENNReal.mul_ne_top (by simp) (by simp)
    refine
      Integrable.of_measure_le_smul
        (μ := μ.prod μ)
        (μ' := (μpartial N).prod (μpartial N))
        (f := fun q : G × G => f (q.1 - q.2) * g q.2)
        h_const_ne_top (hμpartial_prod_le N) ?_
    simpa using h_kernel_int

  have h_kernel_meas_partial :
      ∀ N,
        AEStronglyMeasurable
          (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)) := by
    intro N
    exact
      (h_kernel_int.aestronglyMeasurable.mono_ac (hμpartial_prod_ac N))

  have h_kernel_fiber_int_partial :
      ∀ N, ∀ᵐ x ∂ μpartial N,
        Integrable (fun y => f (x - y) * g y) (μpartial N) := by
    intro N
    have h :=
      Integrable.prod_right_ae
        (μ := μpartial N) (ν := μpartial N)
        (h_kernel_int_partial N)
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx

  have hμpartial_def :
      ∀ N, μpartial N = ∑ k ∈ Finset.range (N + 1), μn k := fun _ => rfl

  have hμpartial_le :
      ∀ N, μpartial N ≤ μ :=
    sfiniteSeq_partial_le_measure
      (μ := μ)
      (μn := μn)
      (μpartial := μpartial)
      (hμ_sum := hμ_sum)
      (hμpartial_def := hμpartial_def)

  classical
  let Hpartial : ℕ → G → ℝ :=
    fun N x => ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μpartial N

  have h_integrability_all :
      ∀ᵐ x ∂ μ,
        Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ ∧
          ∀ N,
            Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) (μpartial N) := by
    refine h_section_int.mono ?_
    intro x hx
    refine ⟨hx, ?_⟩
    intro N
    have h_const_ne_top :
        ((N + 1 : ℝ≥0∞)) ≠ ∞ := by simp
    exact
      Integrable.of_measure_le_smul
        (μ := μ) (μ' := μpartial N)
        (f := fun y => ‖f (x - y)‖ * ‖g y‖)
        h_const_ne_top
        (hμpartial_le_smul N)
        hx

  have h_Hpartial_mono :
      ∀ᵐ x ∂ μ, Monotone fun N => Hpartial N x := by
    refine h_integrability_all.mono ?_
    intro x hx
    rcases hx with ⟨hxμ, hx_partial⟩
    intro N M hNM
    have h_meas_le : μpartial N ≤ μpartial M := hμpartial_mono hNM
    haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
    haveI : IsFiniteMeasure (μpartial M) := hμpartial_fin M
    exact
      integral_norm_mul_mono
        (μ₁ := μpartial N) (μ₂ := μpartial M)
        f g x h_meas_le (hx_partial M)

  have h_Hpartial_le_H :
      ∀ᵐ x ∂ μ, ∀ N, Hpartial N x ≤ H x := by
    refine h_integrability_all.mono ?_
    intro x hx
    rcases hx with ⟨hxμ, hx_partial⟩
    intro N
    have h_meas_le : μpartial N ≤ μ := hμpartial_le N
    haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
    exact
      integral_norm_mul_mono
        (μ₁ := μpartial N) (μ₂ := μ)
        f g x h_meas_le hxμ

  have h_Hpartial_tendsto :
      ∀ᵐ x ∂ μ, Tendsto (fun N => Hpartial N x) atTop (𝓝 (H x)) := by
    refine h_integrability_all.mono ?_
    intro x hx
    rcases hx with ⟨hxμ, hx_partial⟩
    have h_tendsto := hpartial_tendsto_of_integrability_all
      (μ := μ) (f := f) (g := g) (x := x)
      (hx := hxμ)
    simp [Hpartial] at h_tendsto
    exact h_tendsto
  have h_H_pow_eq :
      ∀ᵐ x ∂ μ,
        ‖H x‖ₑ ^ r.toReal = (ENNReal.ofReal (H x)) ^ r.toReal := by
    refine h_H_nonneg.mono ?_
    intro x hx
    have hx_abs : ENNReal.ofReal ‖H x‖ = ENNReal.ofReal (H x) := by
      simp [Real.norm_eq_abs, abs_of_nonneg hx]
    have hx_pow := congrArg (fun t : ℝ≥0∞ => t ^ r.toReal) hx_abs
    have hx_coe : ‖H x‖ₑ = ENNReal.ofReal ‖H x‖ := by
      simpa using (ofReal_norm_eq_enorm (H x)).symm
    simp [hx_coe, Real.norm_eq_abs, abs_of_nonneg hx]
  have h_H_lintegral_eq :
      ∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ
        = ∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ := by
    refine lintegral_congr_ae h_H_pow_eq
  have h_eLpNorm_H :=
    eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := H) hr_ne_zero hr_ne_top
  have h_eLpNorm' :
      eLpNorm H r μ =
        (∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ) ^ r.toReal⁻¹ := by
    simpa [one_div] using h_eLpNorm_H
  have hr_toReal_pos' : 0 < r.toReal :=
    ENNReal.toReal_pos hr_ne_zero hr_ne_top
  have h_H_lintegral_repr :
      (eLpNorm H r μ) ^ r.toReal
        = ∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ := by
    have h_nonzero : r.toReal ≠ 0 := ne_of_gt hr_toReal_pos'
    have h_mul : r.toReal⁻¹ * r.toReal = 1 := by
      simp [one_div, h_nonzero]
    have h_pow :=
      congrArg (fun t : ℝ≥0∞ => t ^ r.toReal) h_eLpNorm'
    have h_rhs :
        ((∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ) ^ r.toReal⁻¹) ^ r.toReal
          = ∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ := by
      simpa [ENNReal.rpow_mul, h_mul]
        using
          (ENNReal.rpow_mul
            (∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ)
            r.toReal⁻¹
            r.toReal).symm
    have h_repr := h_pow.trans h_rhs
    simpa [h_H_lintegral_eq] using h_repr
  have h_kernel_norm_meas :
      AEStronglyMeasurable
        (fun q : G × G => ‖f (q.1 - q.2) * g q.2‖) (μ.prod μ) :=
    (convolution_kernel_aestronglyMeasurable (μ := μ)
      (f := f) (g := g) hf.aestronglyMeasurable hg.aestronglyMeasurable).norm
  have h_kernel_norm_meas_partial :
      ∀ N,
        AEStronglyMeasurable
          (fun q : G × G => ‖f (q.1 - q.2) * g q.2‖)
          (μ.prod (μpartial N)) := by
    intro N
    have h_ac : μ.prod (μpartial N) ≪ μ.prod μ :=
      Measure.AbsolutelyContinuous.rfl.prod (hμpartial_ac N)
    exact (h_kernel_norm_meas.mono_ac h_ac)
  have h_H_meas : AEStronglyMeasurable H μ := by
    simpa [H, norm_mul, mul_comm, mul_left_comm, mul_assoc]
      using h_kernel_norm_meas.integral_prod_right'
  have h_Hpartial_meas :
      ∀ N, AEStronglyMeasurable (fun x => Hpartial N x) μ := by
    intro N
    simpa [Hpartial, norm_mul, mul_comm, mul_left_comm, mul_assoc]
      using (h_kernel_norm_meas_partial N).integral_prod_right'
  have h_H_pow_meas :
      AEMeasurable (fun x => (ENNReal.ofReal (H x)) ^ r.toReal) μ := by
    have h_ofReal :
        AEMeasurable (fun x => ENNReal.ofReal (H x)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable h_H_meas.aemeasurable
    exact
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable h_ofReal)
  have h_Hpartial_pow_meas :
      ∀ N,
        AEMeasurable (fun x => (ENNReal.ofReal (Hpartial N x)) ^ r.toReal) μ := by
    intro N
    have h_ofReal :
        AEMeasurable (fun x => ENNReal.ofReal (Hpartial N x)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable (h_Hpartial_meas N).aemeasurable
    exact
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable h_ofReal)
  have h_Hpartial_nonneg :
      ∀ᵐ x ∂ μ, ∀ N, 0 ≤ Hpartial N x := by
    refine h_integrability_all.mono ?_
    intro x hx
    rcases hx with ⟨hxμ, hx_partial⟩
    intro N
    have h_nonneg_fun :
        0 ≤ᵐ[μpartial N] fun y => ‖f (x - y)‖ * ‖g y‖ :=
      Filter.Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h_nonneg :=
      integral_nonneg_of_ae (μ := μpartial N) (f := fun y => ‖f (x - y)‖ * ‖g y‖) h_nonneg_fun
    simpa [Hpartial] using h_nonneg
  have h_Hpartial_pow_mono :
      ∀ᵐ x ∂ μ,
        Monotone fun N =>
          (ENNReal.ofReal (Hpartial N x)) ^ r.toReal := by
    refine (h_Hpartial_mono.and h_Hpartial_nonneg).mono ?_
    intro x hx
    rcases hx with ⟨h_mono, -⟩
    intro N M hNM
    have h_le := ENNReal.ofReal_le_ofReal (h_mono hNM)
    exact ENNReal.rpow_le_rpow h_le (by have := ENNReal.toReal_nonneg (a := r); simp)
  have h_Hpartial_pow_tendsto :
      ∀ᵐ x ∂ μ,
        Tendsto (fun N => (ENNReal.ofReal (Hpartial N x)) ^ r.toReal) atTop
          (𝓝 ((ENNReal.ofReal (H x)) ^ r.toReal)) := by
    refine (h_Hpartial_tendsto.and h_H_nonneg).mono ?_
    intro x hx
    rcases hx with ⟨hx_tendsto, -⟩
    have h_ofReal_tendsto :
        Tendsto (fun N => ENNReal.ofReal (Hpartial N x)) atTop
          (𝓝 (ENNReal.ofReal (H x))) :=
      (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hx_tendsto
    have h_pow_tendsto :
        Tendsto (fun N => (ENNReal.ofReal (Hpartial N x)) ^ r.toReal) atTop
          (𝓝 ((ENNReal.ofReal (H x)) ^ r.toReal)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h_ofReal_tendsto
    simpa using h_pow_tendsto
  let g_pow : G → ℝ≥0∞ := fun x => (ENNReal.ofReal (H x)) ^ r.toReal
  have h_lintegral_Hpartial_partial :
      ∀ N,
        ∫⁻ x, g_pow x ∂ μpartial N =
          ∑ k ∈ Finset.range (N + 1),
            ∫⁻ x, g_pow x ∂ μn k := by
    intro N
    classical
    simp [g_pow, μpartial]
  have h_lintegral_Hpartial_sum :
      (∑' k, ∫⁻ x, g_pow x ∂ μn k) = ∫⁻ x, g_pow x ∂ μ := by
    classical
    simpa [g_pow, hμ_sum]
      using
        (MeasureTheory.lintegral_sum_measure
          (μ := μn)
          (f := fun x : G => g_pow x)).symm
  have h_lintegral_Hpartial_mono :
      Monotone (fun N => ∫⁻ x, g_pow x ∂ μpartial N) := by
    intro N M hNM
    exact lintegral_mono' (hμpartial_mono hNM) fun _ => le_rfl
  have h_lintegral_Hpartial_tendsto :
      Tendsto (fun N => ∫⁻ x, g_pow x ∂ μpartial N) atTop
        (𝓝 (∫⁻ x, g_pow x ∂ μ)) := by
    classical
    have h_series_tendsto :
        Tendsto
          (fun N =>
            ∑ k ∈ Finset.range (N + 1),
              ∫⁻ x, g_pow x ∂ μn k)
          atTop
          (𝓝 (∑' k, ∫⁻ x, g_pow x ∂ μn k)) := by
      exact
        (ENNReal.tendsto_nat_tsum
          (f := fun k => ∫⁻ x, g_pow x ∂ μn k)).comp
          (tendsto_add_atTop_nat 1)
    have h_eval :
        (fun N => ∫⁻ x, g_pow x ∂ μpartial N)
          = fun N =>
              ∑ k ∈ Finset.range (N + 1),
                ∫⁻ x, g_pow x ∂ μn k := by
      funext N
      exact h_lintegral_Hpartial_partial N
    have h_eval' :
        (∑' k, ∫⁻ x, g_pow x ∂ μn k)
          = ∫⁻ x, g_pow x ∂ μ :=
      h_lintegral_Hpartial_sum
    simpa [h_eval, h_eval'] using h_series_tendsto
  have h_kernel_int_piece :
      ∀ N,
        Integrable
          (fun q : G × G => f (q.1 - q.2) * g q.2) ((μpartial N).prod (μpartial N)) := by
    simpa using h_kernel_int_partial
  have h_kernel_meas_piece :
      ∀ N,
        AEStronglyMeasurable
          (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)) := by
    intro N
    exact h_kernel_meas_partial N
  have h_kernel_fiber_int_piece :
      ∀ N, ∀ᵐ y ∂ μpartial N,
        Integrable (fun x => f (x - y) * g y) (μpartial N) := by
    intro N
    have h :=
      Integrable.prod_left_ae (μ := μpartial N) (ν := μpartial N)
        (h_kernel_int_partial N)
    refine h.mono ?_
    intro y hy
    simpa [sub_eq_add_neg] using hy
  have h_kernel_fiber_mem_piece :
      ∀ N, ∀ᵐ y ∂ μpartial N,
        MemLp (fun x => f (x - y) * g y) r (μpartial N) := by
    intro N
    have h :=
      convolution_kernel_fiber_memLp_of_memLp (μ := μ)
        (p := r) (q := q) hf_r hg
    have h_dom :
        ∀ᵐ y ∂ μ,
          MemLp (fun x => f (x - y) * g y) r (μpartial N) := by
      refine h.mono ?_
      intro y hy
      refine hy.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
      · simp [Nat.succ_eq_add_one]
      · simpa using hμpartial_le_smul N
    have h_zero :=
      (ae_iff).1 h_dom
    have h_zero' :=
      (hμpartial_ac N) h_zero
    exact (ae_iff).2 <| by
      simpa using h_zero'
  have h_norm_piece :
      ∀ N,
        Integrable
          (fun y =>
              ‖g y‖ *
                (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal)
          (μpartial N) := by
    intro N
    exact
      sfiniteSeq_partial_integrable_norm_mul
        (μ := μ)
        (hr := hr)
        (hr_ne_top := hr_ne_top)
        (f := f)
        (g := g)
        (μpartial := μpartial)
        (hf := hf_r)
        (hg_partial_int := hg_partial_int)
        (hμpartial_fin := hμpartial_fin)
        (hμpartial_prod_ac := hμpartial_prod_ac)
        (h_translate_norm_bound_toReal := h_translate_norm_bound_toReal)
        N
  have h_convPiece_def :
      ∀ N,
        (fun x => ∫ y, f (x - y) * g y ∂ μpartial N)
          = fun x => ∫ y, f (x - y) * g y ∂ μpartial N := by
    intro N; rfl
  have h_conv_piece_bound :
      ∀ N,
        eLpNorm
            (fun x => ∫ y, f (x - y) * g y ∂ μpartial N) r (μpartial N)
          ≤
        ENNReal.ofReal
          (∫ y, ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N) := by
    intro N
    have h_minkowski :=
      minkowski_inequality_convolution_complex
        (μ := μpartial N)
        (f := f) (g := g) (p := r)
        hr hr_ne_top
        (h_kernel_meas_piece N)
        (h_kernel_int_piece N)
        (h_kernel_fiber_int_piece N)
        (h_kernel_fiber_mem_piece N)
        (h_norm_piece N)
    simpa [h_convPiece_def N, sub_eq_add_neg,
      integral_congr_ae (h_pointwise_piece_partial N)]
      using h_minkowski
  -- Translate the previous `L^r` bound into a bound on the lintegral of the truncated
  -- Lemma: For complex-valued functions, eLpNorm of the norm equals eLpNorm of the function
  have eLpNorm_norm_eq_of_complex {μ' : Measure G} (h : G → ℂ) (p : ℝ≥0∞) :
      eLpNorm (fun x => ‖h x‖) p μ' = eLpNorm h p μ' := by
    simp

  -- Utility: expand `ENNReal.ofReal` over a triple product of nonnegative reals.
  -- This avoids fragile associativity/commutativity issues when rewriting large products.
  have ofReal_mul_three {a b c : ℝ}
      (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      ENNReal.ofReal (a * b * c)
        = ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c := by
    simp [ENNReal.ofReal_mul, ha, hb, hc, mul_comm, mul_left_comm, mul_assoc]

  -- convolution norms.
  have h_conv_lintegral_bound :
      ∀ N,
        ∫⁻ x,
            (ENNReal.ofReal
              (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μpartial N)) ^ r.toReal ∂ μpartial N
          ≤
        (ENNReal.ofReal
            (∫ y, ‖g y‖ *
                (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N)) ^ r.toReal := by
    intro N
    haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
    let f_norm : G → ℝ := fun x => ‖f x‖
    let g_norm : G → ℝ := fun x => ‖g x‖
    have h_meas :
        AEStronglyMeasurable
          (fun q : G × G => f_norm (q.1 - q.2) * g_norm q.2)
          ((μpartial N).prod (μpartial N)) := by
      -- We need to show measurability of the product of norms
      simp only [f_norm, g_norm]
      -- Using the fact that norms preserve measurability and that the kernel is measurable
      have : AEStronglyMeasurable (fun q : G × G => ‖f (q.1 - q.2) * g q.2‖)
          ((μpartial N).prod (μpartial N)) := (h_kernel_meas_piece N).norm
      -- Now we need to show that ‖f(q.1 - q.2) * g(q.2)‖ = ‖f(q.1 - q.2)‖ * ‖g(q.2)‖ a.e.
      convert this using 1
      ext q
      simp only [norm_mul]
    have h_prod :
        Integrable
          (fun q : G × G => f_norm (q.1 - q.2) * g_norm q.2)
          ((μpartial N).prod (μpartial N)) := by
      have := (h_kernel_int_piece N).norm
      simpa [f_norm, g_norm, norm_mul, mul_comm, mul_left_comm, mul_assoc] using this
    have h_int :
        ∀ᵐ y ∂ μpartial N,
          Integrable (fun x => f_norm (x - y) * g_norm y) (μpartial N) := by
      refine (h_kernel_fiber_int_piece N).mono ?_
      intro y hy
      have hy_norm := hy.norm
      simpa [f_norm, g_norm, norm_mul, mul_comm, mul_left_comm, mul_assoc] using hy_norm
    have h_memLp :
        ∀ᵐ y ∂ μpartial N,
          MemLp (fun x => f_norm (x - y) * g_norm y) r (μpartial N) := by
      refine (h_kernel_fiber_mem_piece N).mono ?_
      intro y hy
      have hy_norm := hy.norm
      simpa [f_norm, g_norm, norm_mul, mul_comm, mul_left_comm, mul_assoc] using hy_norm
    have h_scaling :
        ∀ y : G,
          eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N) =
            ENNReal.ofReal (g_norm y) *
              eLpNorm (fun x => f_norm (x - y)) r (μpartial N) := by
      intro y
      simpa [f_norm, g_norm, smul_eq_mul, mul_comm]
        using
          (eLpNorm_const_smul (μ := μpartial N) (p := r)
            (c := g_norm y) (f := fun x => f_norm (x - y)))
    have h_norm :
        Integrable
          (fun y =>
            (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal)
          (μpartial N) := by
      have h_pointwise :
          (fun y =>
              (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal)
            =ᵐ[μpartial N]
          fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
        refine Filter.Eventually.of_forall ?_
        intro y
        have h_eq := h_scaling y
        have h_toReal := congrArg ENNReal.toReal h_eq
        have hg_nonneg : 0 ≤ g_norm y := by exact norm_nonneg _
        have hf_eq :
            eLpNorm (fun x => f_norm (x - y)) r (μpartial N) =
              eLpNorm (fun x => f (x - y)) r (μpartial N) := by
          simp only [f_norm]
          exact eLpNorm_norm_eq_of_complex (fun x => f (x - y)) r
        simpa [f_norm, g_norm, hf_eq, ENNReal.toReal_mul, hg_nonneg]
          using h_toReal
      have h_norm' := h_norm_piece N
      exact h_norm'.congr h_pointwise.symm
    -- Apply Minkowski inequality for convolutions
    -- Note: μpartial N may not have IsAddRightInvariant property
    -- FIXME: Need to either prove μpartial N has this property or use alternative approach
    have h_minkowski :
        eLpNorm (fun x => ∫ y, f_norm (x - y) * g_norm y ∂(μpartial N)) r (μpartial N) ≤
        ENNReal.ofReal (∫ y, |g_norm y| * (eLpNorm (fun x =>
        f_norm (x - y)) r (μpartial N)).toReal ∂(μpartial N)) := by
      haveI : SFinite (μpartial N) := inferInstance
      have h_raw :
          eLpNorm
              (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N) r (μpartial N) ≤
            ENNReal.ofReal
              (∫ y,
                  (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal
                ∂ μpartial N) := by
        refine
          minkowski_integral_inequality
            (μ := μpartial N) (ν := μpartial N) (p := r)
            hr hr_ne_top (fun x y => f_norm (x - y) * g_norm y)
            ?_ ?_ ?_ ?_ ?_
        · simpa using h_meas
        · simpa using h_prod
        · simpa using h_int
        · simpa using h_memLp
        · simpa using h_norm
      have h_integrand_eq :
          (fun y =>
              (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal)
            =ᵐ[μpartial N]
          fun y =>
            |g_norm y| *
              (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal := by
        refine Filter.Eventually.of_forall ?_
        intro y
        have hg_nonneg : 0 ≤ g_norm y := norm_nonneg _
        have hy_toReal :=
          congrArg ENNReal.toReal (h_scaling y)
        have hy_base :
            (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal =
              g_norm y *
                (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal := by
          simpa [ENNReal.toReal_mul, g_norm, hg_nonneg] using hy_toReal
        have hy_abs :
            (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal =
              |g_norm y| *
                (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal := by
          simpa [abs_of_nonneg hg_nonneg] using hy_base
        simpa using hy_abs
      have h_integral_congr :=
        integral_congr_ae h_integrand_eq
      simpa [h_integral_congr] using h_raw
    have h_eLpNorm_bound :
        eLpNorm
            (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N) r (μpartial N)
          ≤
        ENNReal.ofReal
          (∫ y, ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N) := by
      have h_abs :
          (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N)
            = fun x => Hpartial N x := by
        funext x
        simp [Hpartial, f_norm, g_norm, mul_comm, mul_left_comm, mul_assoc]
      have h_rhs :
          (fun y => |g_norm y| * (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal)
            =ᵐ[μpartial N]
          fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
        refine Filter.Eventually.of_forall ?_
        intro y
        have hg_nonneg : 0 ≤ g_norm y := by exact norm_nonneg _
        have hf_eq :
            eLpNorm (fun x => f_norm (x - y)) r (μpartial N) =
              eLpNorm (fun x => f (x - y)) r (μpartial N) := by
          simp only [f_norm]
          exact eLpNorm_norm_eq_of_complex (fun x => f (x - y)) r
        simp [f_norm, g_norm, hf_eq, abs_of_nonneg hg_nonneg]
      have h_eq1 : ENNReal.ofReal
                  (∫ y,
                      |g_norm y| *
                        (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal ∂ μpartial N)
                =
              ENNReal.ofReal
                  (∫ y,
                      ‖g y‖ *
                        (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N) := by
            exact congrArg ENNReal.ofReal
              (integral_congr_ae h_rhs)
      have h_eq2 : (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N)
                = fun x => Hpartial N x := h_abs
      -- Combine the inequalities and equalities
      calc eLpNorm (fun x => Hpartial N x) r (μpartial N)
        = eLpNorm (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N) r (μpartial N) :=
          by rw [← h_eq2]
        _ ≤ ENNReal.ofReal (∫ y, |g_norm y| *
          (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal ∂(μpartial N)) := h_minkowski
        _ = ENNReal.ofReal (∫ y, ‖g y‖ * (eLpNorm (fun x =>
          f (x - y)) r (μpartial N)).toReal ∂(μpartial N)) := by rw [h_eq1]
    have h_nonneg :
        ∀ᵐ x ∂ μpartial N, 0 ≤ Hpartial N x := by
      apply (hμpartial_ac N).ae_le
      filter_upwards [h_integrability_all] with x hx
      -- Use that Hpartial N x is the integral of a non-negative function
      simp only [Hpartial]
      apply integral_nonneg
      intro y
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    -- Relate the eLpNorm to the lintegral of the r-th power
    have h_pow :
        (∫⁻ x, (ENNReal.ofReal (Hpartial N x)) ^ r.toReal ∂ μpartial N)
          =
        (eLpNorm (fun x => Hpartial N x) r (μpartial N)) ^ r.toReal := by
      -- Use the fact that for non-negative functions, eLpNorm^p = ∫⁻ |f|^p
      have h_eq := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
          (μ := μpartial N)
          (f := fun x => Hpartial N x)
          (p := r)
          hr_ne_zero
          hr_ne_top
      -- For non-negative real functions, ‖x‖ₑ = ENNReal.ofReal x when x ≥ 0
      have h_norm_eq : ∀ᵐ x ∂(μpartial N), ‖Hpartial N x‖ₑ = ENNReal.ofReal (Hpartial N x) := by
        filter_upwards [h_nonneg] with x hx
        simp [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs, abs_of_nonneg hx]
      -- Use the rpow property to relate the expressions
      have h_integral_eq :
          (∫⁻ x, ENNReal.ofReal (Hpartial N x) ^ r.toReal ∂ μpartial N) =
            ∫⁻ x, ‖Hpartial N x‖ₑ ^ r.toReal ∂ μpartial N := by
        refine lintegral_congr_ae ?_
        filter_upwards [h_norm_eq] with x hx
        simp [hx]
      have h_pow' :
          (eLpNorm (fun x => Hpartial N x) r (μpartial N)) ^ r.toReal =
            ∫⁻ x, ‖Hpartial N x‖ₑ ^ r.toReal ∂ μpartial N := by
        have hrtoReal_ne_zero : r.toReal ≠ 0 := ne_of_gt hr_toReal_pos'
        have := congrArg (fun t : ℝ≥0∞ => t ^ r.toReal) h_eq
        simpa [ENNReal.rpow_mul, one_div, hrtoReal_ne_zero, mul_comm, mul_left_comm, mul_assoc]
          using this
      exact h_integral_eq.trans h_pow'.symm
    -- We need to raise both sides to the r-th power
    have h_pow_bound : eLpNorm (fun x => Hpartial N x) r (μpartial N) ^ r.toReal ≤
        ENNReal.ofReal (∫ y, ‖g y‖ * (eLpNorm (fun x =>
        f (x - y)) r (μpartial N)).toReal ∂(μpartial N)) ^ r.toReal := by
      simp only [Hpartial, f_norm, g_norm] at h_eLpNorm_bound
      exact ENNReal.rpow_le_rpow h_eLpNorm_bound (ENNReal.toReal_nonneg)
    have h_final := (le_of_eq h_pow).trans h_pow_bound
    exact h_final
  -- Combine the lintegral bound with Step 4 convergence data to control
  -- the limit superior in Step 6.
  -- Notation for the key sequences appearing in Step 6.
  classical
  set Φ :
      ℕ → ℝ≥0∞ :=
    fun N =>
      ∫⁻ x, (ENNReal.ofReal (Hpartial N x)) ^ r.toReal ∂ μpartial N
    with hΦ_def
  set Ψ :
      ℕ → ℝ≥0∞ :=
    fun N =>
      (ENNReal.ofReal
          (∫ y, ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N)) ^
        r.toReal
    with hΨ_def
  have h_limsup_control :
      (∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ)
        ≤ Filter.limsup Φ Filter.atTop := by
    classical
    let f_seq : ℕ → G → ℝ≥0∞ :=
      fun N x => (ENNReal.ofReal (Hpartial N x)) ^ r.toReal
    have hΦ_eq :
        ∀ N,
          Φ N =
            ∫⁻ x,
              f_seq N x ∂
                (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k) := by
      intro N
      simp [Φ, hΦ_def, f_seq, μpartial, μn]
    have hf_meas :
        ∀ N, AEMeasurable (f_seq N) μ := by
      intro N
      simpa [f_seq] using h_Hpartial_pow_meas N
    have hf_mono :
        ∀ᵐ x ∂ μ, Monotone fun N => f_seq N x := by
      simpa [f_seq] using h_Hpartial_pow_mono
    have hf_tendsto :
        ∀ᵐ x ∂ μ, Tendsto (fun N => f_seq N x) atTop (𝓝 (g_pow x)) := by
      simpa [f_seq, g_pow] using h_Hpartial_pow_tendsto
    simpa [g_pow, f_seq] using
      (limsup_control_aux
        (μ := μ)
        (g_pow := g_pow)
        (Φ := Φ)
        (f_seq := f_seq)
        (hΦ := hΦ_eq)
        (hf_meas := hf_meas)
        (hf_mono := hf_mono)
        (hf_tendsto := hf_tendsto))
  have h_limsup_compare :
      Filter.limsup Φ Filter.atTop ≤ Filter.limsup Ψ Filter.atTop := by
    refine Filter.limsup_le_limsup ?_
    exact
      Filter.Eventually.of_forall fun N =>
        by
          simpa [Φ, Ψ, hΦ_def, hΨ_def]
            using h_conv_lintegral_bound N
  have h_limsup_goal :
      (∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ)
        ≤ Filter.limsup Ψ Filter.atTop :=
    le_trans h_limsup_control h_limsup_compare
  -- Prepare the conjugate exponent s₀ of q and the Young split 1/p = 1/r + 1/s₀.
  have hq_lt_top : q < ∞ := lt_of_le_of_ne le_top hq_ne_top
  obtain ⟨s₀, hs₀_conj, hs₀_eq⟩ :=
    conjugate_exponent_formula (p := q) (by exact hq) (by exact hq_lt_top)
  have h_split : 1 / p = 1 / r + 1 / s₀ := by
    simpa [hs₀_eq] using
      inv_p_eq_inv_r_add_inv_conj p q r hp hq hpqr hr_ne_top
  -- Basic bounds for the conjugate exponent s₀.
  have hs₀_bounds :=
    conjugate_exponent_bounds (p := q) (q := s₀) hs₀_conj hq hq_lt_top
  have hs₀_one_lt : 1 < s₀ := hs₀_bounds.1
  have hs₀_lt_top : s₀ < ∞ := hs₀_bounds.2
  have hs₀_ne_top : s₀ ≠ ∞ := ne_of_lt hs₀_lt_top
  have hs₀_ne_zero : s₀ ≠ 0 := by
    have : (0 : ℝ≥0∞) < s₀ := lt_trans (by simp) hs₀_one_lt
    exact ne_of_gt this
  have hs₀_toReal_pos : 0 < s₀.toReal :=
    ENNReal.toReal_pos hs₀_ne_zero hs₀_ne_top
  -- Auxiliary: split exponents on the real side via `h_split`.
  have h_one_div_toReal_split :
      p.toReal⁻¹ = r.toReal⁻¹ + s₀.toReal⁻¹ := by
    have hr_fin : 1 / r ≠ ∞ := by simp [one_div, hr_ne_zero]
    have hs_fin : 1 / s₀ ≠ ∞ := by simp [one_div, hs₀_ne_zero]
    have h1 : (1 / p).toReal = (1 / r + 1 / s₀).toReal := by
      simpa using congrArg ENNReal.toReal h_split
    have h2 : (1 / r + 1 / s₀).toReal = (1 / r).toReal + (1 / s₀).toReal :=
      ENNReal.toReal_add hr_fin hs_fin
    have h3 : (1 / p).toReal = (1 / r).toReal + (1 / s₀).toReal := by
      simpa using (h1.trans h2)
    simpa [one_div, ENNReal.toReal_inv] using h3
  -- Base for combining powers of `(N+1 : ℝ≥0∞)` when needed later
  have h_Bpow_split :
      ∀ k : ℕ,
        ((k + 1 : ℝ≥0∞) ^ r.toReal⁻¹)
          * ((k + 1 : ℝ≥0∞) ^ s₀.toReal⁻¹)
          = ((k + 1 : ℝ≥0∞) ^ p.toReal⁻¹) := by
    intro k
    have hbase_ne_zero : (k + 1 : ℝ≥0∞) ≠ 0 := by simp
    have hbase_ne_top : (k + 1 : ℝ≥0∞) ≠ ∞ := by simp
    have h_add :
        r.toReal⁻¹ + s₀.toReal⁻¹ = p.toReal⁻¹ := by
      simpa using h_one_div_toReal_split.symm
    -- use `(x ^ (a + b)) = x ^ a * x ^ b`, rearranged
    have h_rw :=
      (ENNReal.rpow_add (x := (k + 1 : ℝ≥0∞)) (y := r.toReal⁻¹)
        (z := s₀.toReal⁻¹) hbase_ne_zero hbase_ne_top).symm
    simpa [h_add, add_comm, add_left_comm, add_assoc] using h_rw
  -- Reduce the goal to showing an upper bound on `Filter.limsup Ψ atTop`.
  suffices
      Filter.limsup Ψ Filter.atTop
        ≤ (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal by
    exact le_trans h_limsup_goal this
  -- Now we prove the required limsup bound for Ψ.
  exact
    by
      -- Define A_N(y) and its uniform bound by a constant C_N.
      classical
      let A : ℕ → G → ℝ :=
        fun N y => (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal
      let C : ℕ → ℝ :=
        fun N => ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal
      have hA_leC : ∀ N y, A N y ≤ C N := by
        intro N y
        simpa [A, C] using h_translate_norm_bound_toReal N y
      have hA_nonneg : ∀ N y, 0 ≤ A N y := by
        intro N y
        simp only [A, ENNReal.toReal_nonneg]
      have h_C_nonneg : ∀ N, 0 ≤ C N := by
        intro N
        simp only [C, ENNReal.toReal_nonneg]
      -- Step B: Prepare a p-norm–based bound for A using exponent monotonicity on finite measures.
      -- We will use the generic translate bound at exponent p, and then convert p → r
      -- via the finite-measure exponent inequality.
      -- Translate bound at exponent p on the partial measures.
      have h_translate_norm_bound_toReal_p :
          ∀ N y,
            (eLpNorm (fun x => f (x - y)) p (μpartial N)).toReal
              ≤ ((N + 1 : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm f p μ).toReal := by
        intro N y
        -- This follows from the general partial-translate bound specialized to p.
        have :=
          sfiniteSeq_partial_translate_norm_bound
            (μ := μ) (r := p) (f := f) (μpartial := μpartial)
            (hf := hf) (h_le := hμpartial_le_smul) N y
        -- Convert both sides to `toReal` for convenience (both are finite under our hypotheses).
        have h_pow_ne_top : ((N + 1 : ℝ≥0∞) ^ (1 / p).toReal) ≠ ∞ := by
          have h_nonneg : 0 ≤ (1 / p).toReal := by simp [one_div]
          exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
        have h_rhs_ne_top :
            ((N + 1 : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm f p μ) ≠ ∞ :=
          ENNReal.mul_ne_top h_pow_ne_top (by simpa using hf.eLpNorm_ne_top)
        exact ENNReal.toReal_mono h_rhs_ne_top this
      -- Finite-measure exponent monotonicity (from p to r) on each μpartial N (correct direction).
      -- This is the key inequality enabling the p-based redesign of the constants.
      have h_exponent_mono_toReal :
          ∀ N y,
            (eLpNorm (fun x => f (x - y)) p (μpartial N)).toReal
              ≤ (((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)).toReal
                  * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
        intro N y
        -- Apply finite-measure exponent monotonicity to `h := fun x => f (x - y)`
        -- and then convert both sides with `toReal` (ensuring finiteness on the RHS).
        haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
        -- Measurability of the translate x ↦ f (x - y) w.r.t. μpartial N
        -- Use translation invariance to get measurability under μ, then restrict to μpartial N.
        have h_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using measurePreserving_add_right (μ := μ) (-y)
        have h_shift_mem : MemLp (fun x => f (x - y)) r μ :=
          hf_r.comp_measurePreserving h_pres
        have h_meas_μ : AEStronglyMeasurable (fun x => f (x - y)) μ :=
          h_shift_mem.aestronglyMeasurable
        have h_meas_partial : AEStronglyMeasurable (fun x => f (x - y)) (μpartial N) :=
          h_meas_μ.mono_ac (hμpartial_ac N)
        -- From 1/p = 1/r + 1/s₀ we deduce 1/r ≤ 1/p, hence p ≤ r by antitonicity of inv.
        have h_inv_r_le_inv_p : 1 / r ≤ 1 / p := by
          have : 1 / r ≤ 1 / r + 1 / s₀ := by simp
          simp [h_split, add_comm, add_left_comm, add_assoc]
        have hp_le_hr : p ≤ r := by
          have : r⁻¹ ≤ p⁻¹ := by simpa [one_div] using h_inv_r_le_inv_p
          exact (ENNReal.inv_le_inv).mp this
        -- Base inequality in ℝ≥0∞
        have h_base :
            eLpNorm (fun x => f (x - y)) p (μpartial N)
              ≤ ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
                  * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
          by_cases hμz : μpartial N = 0
          · simp [hμz]
          · simpa [mul_comm]
              using
                (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
                  (μ := μpartial N) (f := fun x => f (x - y))
                  (p := p) (q := r) hp_le_hr h_meas_partial)
        -- The RHS is finite: both factors are finite.
        have h_exp_nonneg : 0 ≤ (1 / p.toReal - 1 / r.toReal) := by
          -- From 1/p = 1/r + 1/s₀ and 0 ≤ 1/s₀, deduce 1/r ≤ 1/p, hence the difference is ≥ 0.
          have h_sum : 1 / p.toReal = 1 / r.toReal + 1 / s₀.toReal := by
            simpa [one_div] using h_one_div_toReal_split
          have h_inv_s₀_nonneg : 0 ≤ 1 / s₀.toReal := by
            simp [one_div]
          have h_le : 1 / r.toReal ≤ 1 / p.toReal := by
            have : 1 / r.toReal ≤ 1 / r.toReal + 1 / s₀.toReal :=
              le_add_of_nonneg_right h_inv_s₀_nonneg
            simp [h_sum, add_comm, add_left_comm, add_assoc]
          exact sub_nonneg.mpr h_le
        have h_factor1_ne_top :
            ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal) ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
        have h_factor2_bound := h_translate_norm_bound N y
        have h_factor2_ne_top :
            eLpNorm (fun x => f (x - y)) r (μpartial N) ≠ ∞ := by
          -- Bounded by a finite constant ⇒ strictly below ⊤
          have h_pow_ne_top : ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / r).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have h_const_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ :=
            ENNReal.mul_ne_top h_pow_ne_top (by simpa using hf_r.eLpNorm_ne_top)
          have hc_lt_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) < ∞ := by
            simpa [lt_top_iff_ne_top] using h_const_ne_top
          have h_lt_top :
              eLpNorm (fun x => f (x - y)) r (μpartial N) < ∞ :=
            lt_of_le_of_lt h_factor2_bound hc_lt_top
          simpa [lt_top_iff_ne_top] using h_lt_top
        have h_rhs_ne_top :
            ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
                * eLpNorm (fun x => f (x - y)) r (μpartial N) ≠ ∞ :=
          ENNReal.mul_ne_top h_factor1_ne_top h_factor2_ne_top
        -- Convert the inequality with `toReal` and expand the RHS product.
        have h_base_toReal :
            (eLpNorm (fun x => f (x - y)) p (μpartial N)).toReal ≤
              ( ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
                  * eLpNorm (fun x => f (x - y)) r (μpartial N) ).toReal :=
          ENNReal.toReal_mono h_rhs_ne_top h_base
        have h_toReal_mul :
            ( ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
                * eLpNorm (fun x => f (x - y)) r (μpartial N) ).toReal
              = (((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)).toReal
                  * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
          simp
        simpa [h_toReal_mul] using h_base_toReal
      -- Combine the two bounds to produce a p-based uniform control for A.
      -- y-dependent lower-bound template coming from exponent monotonicity on finite measures
      let Cp : ℕ → G → ℝ :=
        fun N y =>
          (((μpartial N) Set.univ) ^ (1 / r.toReal - 1 / p.toReal)).toReal
            * ((eLpNorm (fun x => f (x - y)) p (μpartial N)).toReal)
      -- Placeholder: with the corrected exponent inequality direction, we will adjust the
      -- chaining to produce the desired bound on `A` in the next pass.
      -- We switch to a lower bound: A N y ≥ Cp N y.
      have hA_geCp : ∀ N y, A N y ≥ Cp N y := by
        intro N y
        -- Finite measure on μpartial N
        haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
        -- Trivial if the partial measure is zero.
        by_cases hμz : μpartial N = 0
        · simp [A, Cp, hμz]
        · -- Nonzero finite measure: prove the inequality in ℝ≥0∞, then pass to toReal.
          -- Notation: α = μ(univ)^(1/p - 1/r), β = μ(univ)^(1/r - 1/p)
          set α : ℝ≥0∞ := ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal) with hα
          set β : ℝ≥0∞ := ((μpartial N) Set.univ) ^ (1 / r.toReal - 1 / p.toReal) with hβ
          -- Measurability of the translate under μpartial N
          have h_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
              using measurePreserving_add_right (μ := μ) (-y)
          have h_shift_mem : MemLp (fun x => f (x - y)) r μ :=
            hf_r.comp_measurePreserving h_pres
          have h_meas_partial :
              AEStronglyMeasurable (fun x => f (x - y)) (μpartial N) :=
            (h_shift_mem.aestronglyMeasurable).mono_ac (hμpartial_ac N)
          -- Base (Lyapunov) inequality in ℝ≥0∞ on μpartial N
          have h_baseENN :
              eLpNorm (fun x => f (x - y)) p (μpartial N)
                ≤ α * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
            have hp_le_hr : p ≤ r := by
              -- From 1/p = 1/r + 1/s₀ ⇒ 1/r ≤ 1/p in ℝ≥0∞
              have h_inv_r_le_inv_p : 1 / r ≤ 1 / p := by
                have : 1 / r ≤ 1 / r + 1 / s₀ := by simp
                simp [h_split, add_comm, add_left_comm, add_assoc]
              have : r⁻¹ ≤ p⁻¹ := by simpa [one_div] using h_inv_r_le_inv_p
              exact (ENNReal.inv_le_inv).1 this
            have h_mono : eLpNorm (fun x => f (x - y)) p (μpartial N)
                  ≤ ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
                      * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
              by_cases hμz : μpartial N = 0
              · simp [hμz]
              · simpa [mul_comm]
                  using
                    (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
                      (μ := μpartial N) (f := fun x => f (x - y))
                      (p := p) (q := r) hp_le_hr h_meas_partial)
            simpa [hα] using h_mono
          -- Multiply by β on both sides and simplify with β * α = 1 (in ℝ≥0∞).
          have h_mulENN :
              β * eLpNorm (fun x => f (x - y)) p (μpartial N)
                ≤ β * (α * eLpNorm (fun x => f (x - y)) r (μpartial N)) :=
            mul_le_mul_left' h_baseENN β
          have hμU_ne_zero : (μpartial N) Set.univ ≠ 0 := by
            simpa [Measure.measure_univ_eq_zero] using hμz
          have hμU_ne_top : (μpartial N) Set.univ ≠ ⊤ := by
            simp
          have h_prod_one : α * β = (1 : ℝ≥0∞) := by
            have h :=
              ENNReal.rpow_add (x := (μpartial N) Set.univ)
                (y := (1 / p.toReal - 1 / r.toReal))
                (z := (1 / r.toReal - 1 / p.toReal)) hμU_ne_zero hμU_ne_top
            -- x^(y+z) = x^y * x^z and (y+z) = 0
            have : α * β = ((μpartial N) Set.univ) ^ 0 := by
              simpa [hα, hβ, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
                using h.symm
            simpa using (this.trans (by simp))
          have h_leENN :
              β * eLpNorm (fun x => f (x - y)) p (μpartial N)
                ≤ eLpNorm (fun x => f (x - y)) r (μpartial N) := by
            simpa [mul_comm, mul_left_comm, mul_assoc, h_prod_one]
              using
                (le_trans h_mulENN (by
                  -- β * (α * E_r) = (β * α) * E_r = E_r
                  have : β * (α * eLpNorm (fun x => f (x - y)) r (μpartial N))
                      = (β * α) * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
                    simp [mul_comm, mul_left_comm, mul_assoc]
                  simp [this, h_prod_one, mul_comm, mul_left_comm, mul_assoc]))
          -- RHS is finite by the uniform translate bound at r.
          have h_pow_ne_top : ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / r).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have h_const_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ :=
            ENNReal.mul_ne_top h_pow_ne_top (by simpa using hf_r.eLpNorm_ne_top)
          have h_factor2_ne_top :
              eLpNorm (fun x => f (x - y)) r (μpartial N) ≠ ⊤ := by
            have h_bound := h_translate_norm_bound N y
            exact ne_of_lt (lt_of_le_of_lt h_bound
              (by simpa [lt_top_iff_ne_top] using h_const_ne_top))
          -- Pass to toReal to conclude A N y ≥ Cp N y.
          have h_toReal := ENNReal.toReal_mono h_factor2_ne_top h_leENN
          simpa [A, Cp, hβ] using h_toReal
      -- Auxiliary facts: L^q membership of ‖g‖ on μpartial N.
      have hg_norm_partial : ∀ N, MemLp (fun y => ‖g y‖) q (μpartial N) := by
        intro N; simpa using (hg_partial N).norm
      -- Step 1 (Young template on a finite piece): if A N ∈ L^{s₀}(μpartial N),
      -- then Hölder(q, s₀) on μpartial N yields a direct bound for Ψ N
      -- without introducing the auxiliary constant C N.
      have hΨ_le_young_template :
          ∀ N,
            MemLp (fun y => A N y) s₀ (μpartial N) →
            Ψ N ≤
              (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)) ^
              r.toReal := by
        intro N hA_mem
        -- Hölder on μpartial N with exponents (q, s₀) applied to (‖g‖, A N).
        have h_holder :=
          holder_inequality (μ := μpartial N) (p := q) (q := s₀) hs₀_conj
            (f := fun y => ‖g y‖) (g := fun y => A N y)
            (hg_norm_partial N) hA_mem
        -- Convert to a real inequality on the product integral.
        have h_int_le :
            ∫ y, ‖g y‖ * A N y ∂ μpartial N
              ≤ (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal := by
          have h := h_holder.2
          -- Simplify ‖‖g y‖‖ to ‖g y‖ and |A N y| to A N y
          convert h using 2
          · ext y
            simp [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (hA_nonneg N y)]
        have h_ofReal_le :
            ENNReal.ofReal (∫ y, ‖g y‖ * A N y ∂ μpartial N)
              ≤ ENNReal.ofReal
                  ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                    * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal) := by
          exact ENNReal.ofReal_le_ofReal h_int_le
        -- Raise both sides to r.toReal (nonnegative), and rewrite as Ψ N on the LHS.
        have h_rpow : (ENNReal.ofReal (∫ y, ‖g y‖ * A N y ∂ μpartial N)) ^ r.toReal
              ≤ (ENNReal.ofReal ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                    * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)) ^ r.toReal :=
          ENNReal.rpow_le_rpow h_ofReal_le ENNReal.toReal_nonneg
        simpa [Ψ, hΨ_def, A, mul_comm, mul_left_comm, mul_assoc]
          using h_rpow
      -- Step 2: Show A N ∈ L^{s₀}(μpartial N) via measurability + uniform bound by C N.
      -- Measurability of y ↦ A N y comes from a product-measurability argument
      -- (specialization of the measurability part in Minkowski’s inequality machinery),
      -- using the kernel q ↦ ‖f (q.1 - q.2)‖ and absolute continuity of partial products.
      have hA_measurable : ∀ N,
          AEStronglyMeasurable (fun y => A N y) (μpartial N) := by
        intro N
        -- Apply the extracted measurability lemma for A_fun, then unfold A.
        simpa [A_fun, A] using
          (A_measurable_partial (μ := μ)
            (f := f) (r := r) (μpartial := μpartial)
            (hr_ne_zero := hr_ne_zero) (hr_ne_top := hr_ne_top)
            (hf_meas := hf.aestronglyMeasurable)
            (hμpartial_fin := hμpartial_fin)
            (hμpartial_prod_ac := hμpartial_prod_ac) N)
      -- L^{s₀} membership via a uniform bound A N y ≤ C N and `MemLp.of_bound`.
      have hA_memLp_s₀ : ∀ N, MemLp (fun y => A N y) s₀ (μpartial N) := by
        intro N
        have h_bound : ∀ᵐ y ∂ μpartial N, ‖A N y‖ ≤ C N := by
          refine Filter.Eventually.of_forall (fun y => ?_)
          have hA_nonneg' : 0 ≤ A N y := hA_nonneg N y
          simpa [Real.norm_of_nonneg hA_nonneg'] using (hA_leC N y)
        exact MemLp.of_bound (hA_measurable N) (C N) h_bound
      -- Package: a convenient form to apply Step 1’s Young template.
      have hA_mem : ∀ N, MemLp (fun y => A N y) s₀ (μpartial N) := hA_memLp_s₀
      -- Step 3: Apply the Young template (Step 1) with the L^{s₀} membership from Step 2,
      -- and refine the A-term by comparing to the constant bound C N in L^{s₀}.
      -- First, a direct application of the template:
      have hΨ_le_from_template :
          ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)) ^
              r.toReal := by
        intro N; exact hΨ_le_young_template N (hA_mem N)
      -- Compare ‖A‖_{L^{s₀}(μpartial N)} with the constant function C N using
      -- the pointwise bound A N y ≤ C N and the standard eLpNorm bound.
      have hA_eLp_le_const : ∀ N,
          eLpNorm (fun y => A N y) s₀ (μpartial N)
            ≤ eLpNorm (fun _ : G => (C N)) s₀ (μpartial N) := by
        intro N
        have h_bound : ∀ᵐ y ∂ μpartial N, ‖A N y‖ ≤ C N := by
          refine Filter.Eventually.of_forall (fun y => ?_)
          have hA_nonneg' : 0 ≤ A N y := hA_nonneg N y
          simpa [Real.norm_of_nonneg hA_nonneg'] using (hA_leC N y)
        -- eLpNorm_le_of_ae_bound gives us: eLpNorm f p μ ≤ μ(univ)^(1/p) * ofReal(C)
        -- We need to show this equals eLpNorm (fun _ => C) p μ
        have h_from_bound := eLpNorm_le_of_ae_bound (p := s₀) (f := fun y => A N y)
          (μ := μpartial N) h_bound
        -- Now show that eLpNorm (fun _ => C N) s₀ μ = μ(univ)^(1/s₀) * ofReal(C N)
        by_cases hμz : μpartial N = 0
        · simp [hμz]
        · have hs₀_ne_zero' : s₀ ≠ 0 := hs₀_ne_zero
          have h_nonneg : 0 ≤ (C N) := h_C_nonneg N
          have h_const :
              eLpNorm (fun _ : G => (C N)) s₀ (μpartial N)
                = ENNReal.ofReal (C N) * (μpartial N Set.univ) ^ (1 / s₀.toReal) := by
            simpa [Real.enorm_eq_ofReal h_nonneg,
              Real.norm_eq_abs, abs_of_nonneg h_nonneg]
              using (eLpNorm_const (μ := μpartial N) (p := s₀)
                (c := (C N)) hs₀_ne_zero' hμz)
          rw [h_const]
          -- h_from_bound has the form: ... ≤ μ(univ)^(1/s₀) * ofReal(C N)
          -- We need: ... ≤ ofReal(C N) * μ(univ)^(1/s₀)
          calc eLpNorm (fun y => A N y) s₀ (μpartial N)
              ≤ (μpartial N Set.univ) ^ s₀.toReal⁻¹ * ENNReal.ofReal (C N) := h_from_bound
            _ = ENNReal.ofReal (C N) * (μpartial N Set.univ) ^ s₀.toReal⁻¹ := by ring
            _ = ENNReal.ofReal (C N) * (μpartial N Set.univ) ^ (1 / s₀.toReal) := by
              rw [inv_eq_one_div]
      -- Convert this eLp inequality to toReal by monotonicity of toReal on finite values,
      -- and rewrite the RHS using the constant-scalar eLpNorm factorization.
      have hA_toReal_le : ∀ N,
          (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
            ≤ (eLpNorm (fun _ : G => (C N)) s₀ (μpartial N)).toReal := by
        intro N
        -- RHS is finite since μpartial N is finite and C N < ∞
        haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
        have h_const_fin : eLpNorm (fun _ : G => (C N)) s₀ (μpartial N) < ∞ := by
          -- compute eLpNorm of constant and use measure finiteness
          by_cases hμz : μpartial N = 0
          · have : eLpNorm (fun _ : G => (C N)) s₀ (μpartial N) = 0 := by simp [hμz]
            simp [this]
          · have hs₀_ne_zero' : s₀ ≠ 0 := hs₀_ne_zero
            have h_const :
                eLpNorm (fun _ : G => (C N)) s₀ (μpartial N)
                  = ENNReal.ofReal (C N) * (μpartial N Set.univ) ^ (1 / s₀.toReal) := by
              -- specialize eLpNorm_const to real constant C N
              have h_nonneg : 0 ≤ (C N) := h_C_nonneg N
              have h_eLpNorm := eLpNorm_const (μ := μpartial N) (p := s₀)
                (c := (C N)) hs₀_ne_zero' hμz
              simp only [Real.enorm_eq_ofReal h_nonneg, Real.norm_eq_abs,
                abs_of_nonneg h_nonneg] at h_eLpNorm
              exact h_eLpNorm
            have hμ_lt_top : (μpartial N Set.univ) < ∞ := measure_lt_top _ _
            have hpow_lt : (μpartial N Set.univ) ^ (1 / s₀.toReal) < ∞ :=
              ENNReal.rpow_lt_top_of_nonneg (by simp [one_div]) hμ_lt_top.ne
            have h_ofReal_lt : ENNReal.ofReal (C N) < ∞ := by simp
            have h_rhs_lt : ENNReal.ofReal (C N)
                * (μpartial N Set.univ) ^ (1 / s₀.toReal) < ∞ :=
              ENNReal.mul_lt_top h_ofReal_lt hpow_lt
            simpa [h_const] using h_rhs_lt
        exact ENNReal.toReal_mono h_const_fin.ne (hA_eLp_le_const N)
      -- Rewrite the RHS toReal via the scalar eLpNorm factorization to expose C N.
      have hA_toReal_le_const : ∀ N,
          (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
            ≤ (C N) * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal := by
        intro N
        have h_nonnegC : 0 ≤ C N := h_C_nonneg N
        have h_smul :
            eLpNorm (fun _ : G => (C N)) s₀ (μpartial N)
              = ENNReal.ofReal (C N)
                  * eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N) := by
          -- factor the constant out of the L^{s₀} norm in y
          -- Show that (fun _ => C N) = (C N) • (fun _ => 1)
          have h_fun_eq : (fun _ : G => (C N)) = (C N) • (fun _ : G => (1 : ℝ)) := by
            ext x
            simp [smul_eq_mul]
          rw [h_fun_eq]
          have h_eLpNorm_smul := eLpNorm_const_smul (μ := μpartial N) (p := s₀)
            (c := (C N)) (f := fun _ : G => (1 : ℝ))
          have h_nonneg : 0 ≤ (C N) := h_C_nonneg N
          simp only [Real.enorm_eq_ofReal h_nonneg] at h_eLpNorm_smul
          exact h_eLpNorm_smul
        have h_toReal_eq :
            (eLpNorm (fun _ : G => (C N)) s₀ (μpartial N)).toReal
              = (C N) * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal := by
          -- pass to toReal using nonnegativity of C N
          have := congrArg ENNReal.toReal h_smul
          simpa [ENNReal.toReal_mul, h_nonnegC]
            using this
        exact (hA_toReal_le N).trans (by simp [h_toReal_eq])
      -- Feed this refinement into the Young template bound, to obtain a concrete
      -- inequality that matches the Θ-shape used later.
      have hΨ_le_step3 :
          ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * ((C N)
                    * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal))) ^
              r.toReal := by
        intro N
        have h_base := hΨ_le_from_template N
        -- replace the A-term by its constant bound in toReal form
        have h_inner_le :
            (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
              * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
            ≤ (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                * ((C N) * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal) := by
          have hg_nonneg : 0 ≤ (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal :=
            ENNReal.toReal_nonneg
          exact mul_le_mul_of_nonneg_left (hA_toReal_le_const N) hg_nonneg
        have h_ofReal_mono :
            ENNReal.ofReal
              ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)
            ≤ ENNReal.ofReal
              ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                * ((C N)
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal)) := by
          exact ENNReal.ofReal_le_ofReal h_inner_le
        have h_rpow_mono :
            (ENNReal.ofReal
              ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)) ^ r.toReal
            ≤ (ENNReal.ofReal
              ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                * ((C N)
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal))) ^ r.toReal := by
          exact ENNReal.rpow_le_rpow h_ofReal_mono (by exact ENNReal.toReal_nonneg)
        exact h_base.trans h_rpow_mono
      -- First, a crude bound using A ≤ C pointwise to control Ψ N.
      have hΨ_le_aux :
          ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                (C N * ∫ y, ‖g y‖ ∂ μpartial N)) ^ r.toReal := by
        intro N
        have h_pointwise :
            ∀ y, ‖g y‖ * A N y ≤ ‖g y‖ * C N := by
          intro y
          have := hA_leC N y
          exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
        have h_left_int :
            Integrable (fun y => ‖g y‖ * A N y) (μpartial N) := by
          -- Provided earlier as `h_norm_piece`.
          simpa [A] using h_norm_piece N
        have h_right_int :
            Integrable (fun y => ‖g y‖ * C N) (μpartial N) := by
          have := (hg_partial_int N).norm.mul_const (C N)
          simpa using this
        have h_int_le :
            ∫ y, ‖g y‖ * A N y ∂ μpartial N ≤
              ∫ y, ‖g y‖ * C N ∂ μpartial N := by
          refine integral_mono_ae h_left_int h_right_int ?_
          exact Filter.Eventually.of_forall h_pointwise
        have h_int_eval :
            ∫ y, ‖g y‖ * C N ∂ μpartial N = C N * ∫ y, ‖g y‖ ∂ μpartial N := by
          simpa [mul_comm, mul_left_comm, mul_assoc]
            using
              (integral_mul_const (μ := μpartial N) (r := C N)
                (f := fun y => ‖g y‖))
        have h_ofReal_le :
            ENNReal.ofReal (∫ y, ‖g y‖ * A N y ∂ μpartial N)
              ≤ ENNReal.ofReal (C N * ∫ y, ‖g y‖ ∂ μpartial N) := by
          have := le_trans h_int_le (le_of_eq h_int_eval)
          exact ENNReal.ofReal_le_ofReal this
        -- Raise both sides to r.toReal.
        have :
            (ENNReal.ofReal (∫ y, ‖g y‖ * A N y ∂ μpartial N)) ^ r.toReal
              ≤ (ENNReal.ofReal (C N * ∫ y, ‖g y‖ ∂ μpartial N)) ^ r.toReal := by
          exact ENNReal.rpow_le_rpow h_ofReal_le ENNReal.toReal_nonneg
        simpa [Ψ, hΨ_def, A] using this
      -- Hölder (q, s₀) with the constant 1 to control ∫ ‖g‖ on μpartial N.
      have h_one_memLp : ∀ N, MemLp (fun _ : G => (1 : ℝ)) s₀ (μpartial N) := by
        intro N
        have h_aesm : AEStronglyMeasurable (fun _ : G => (1 : ℝ)) (μpartial N) := by
          simpa using (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : G => (1 : ℝ)) (μpartial N))
        haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
        by_cases hμz : μpartial N = 0
        · have : eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N) = 0 := by
            simp [hμz]
          exact ⟨h_aesm, by simp [this]⟩
        · have hs₀_ne_zero' : s₀ ≠ 0 := hs₀_ne_zero
          have h_const :
              eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)
                = ENNReal.ofReal (1 : ℝ) * (μpartial N Set.univ) ^ (1 / s₀.toReal) := by
            have h_nonneg : 0 ≤ (1 : ℝ) := by simp
            simpa [Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
              Real.norm_eq_abs, abs_of_nonneg h_nonneg]
              using (eLpNorm_const (μ := μpartial N) (p := s₀) (c := (1 : ℝ)) hs₀_ne_zero' hμz)
          have h_lt_top : eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N) < ∞ := by
            have : (μpartial N Set.univ) < ∞ := measure_lt_top _ _
            have hpow_lt : (μpartial N Set.univ) ^ (1 / s₀.toReal) < ∞ :=
              ENNReal.rpow_lt_top_of_nonneg (by simp) this.ne
            have h1 : ENNReal.ofReal (1 : ℝ) < ∞ := by simp
            have h_rhs_lt :
                ENNReal.ofReal (1 : ℝ) * (μpartial N Set.univ) ^ (1 / s₀.toReal) < ∞ :=
              ENNReal.mul_lt_top h1 hpow_lt
            simpa [h_const] using h_rhs_lt
          exact ⟨h_aesm, h_lt_top⟩
      have h_int_g_le :
          ∀ N,
            ∫ y, ‖g y‖ ∂ μpartial N
              ≤ (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal := by
        intro N
        have h_holder :=
          holder_inequality (μ := μpartial N) (p := q) (q := s₀) hs₀_conj
            (f := fun y => ‖g y‖) (g := fun _ : G => (1 : ℝ))
            (hg_norm_partial N) (h_one_memLp N)
        -- Simplify |‖g y‖ * 1| to ‖g y‖
        simpa using h_holder.2
      -- Bound eLpNorm g on μpartial N by the smul-measure bound and convert to toReal.
      have h_g_partial_bound_toReal :
          ∀ N,
            (eLpNorm g q (μpartial N)).toReal ≤
              (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal := by
        intro N
        have h_le' :=
          eLpNorm_mono_measure
            (f := g) (μ := ((N + 1 : ℝ≥0∞) • μ)) (ν := μpartial N) (p := q)
            (hμpartial_le_smul N)
        have h_succ_pos : (0 : ℝ≥0∞) < (N + 1 : ℝ≥0∞) := by
          exact_mod_cast (Nat.succ_pos N)
        have h_c_ne_zero : (N + 1 : ℝ≥0∞) ≠ 0 := ne_of_gt h_succ_pos
        have h_smul :=
          eLpNorm_smul_measure_of_ne_zero
            (μ := μ) (p := q) (f := g) (c := (N + 1 : ℝ≥0∞)) h_c_ne_zero
        have h_step := h_le'.trans (le_of_eq h_smul)
        -- convert to toReal using that the RHS is finite
        have h_pow_ne_top :
            ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ≠ ∞ := by
          have h_exp_nonneg : 0 ≤ (1 / q).toReal := by simp [one_div]
          exact ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
        have h_const_ne_top :
            (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ) ≠ ∞ :=
          ENNReal.mul_ne_top h_pow_ne_top hg.eLpNorm_ne_top
        exact ENNReal.toReal_mono h_const_ne_top h_step
      -- ENNReal-level bound for the constant-1 eLpNorm on the partial measures.
      have h_one_partial_bound :
          ∀ N,
            eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)
              ≤ ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                  * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ := by
        intro N
        have h_le' :=
          eLpNorm_mono_measure
            (f := fun _ : G => (1 : ℝ))
            (μ := ((N + 1 : ℝ≥0∞) • μ)) (ν := μpartial N) (p := s₀)
            (hμpartial_le_smul N)
        have h_succ_pos : (0 : ℝ≥0∞) < (N + 1 : ℝ≥0∞) := by
          exact_mod_cast (Nat.succ_pos N)
        have h_c_ne_zero : (N + 1 : ℝ≥0∞) ≠ 0 := ne_of_gt h_succ_pos
        have h_smul :=
          eLpNorm_smul_measure_of_ne_zero
            (μ := μ) (p := s₀)
            (f := fun _ : G => (1 : ℝ)) (c := (N + 1 : ℝ≥0∞)) h_c_ne_zero
        simpa using h_le'.trans (le_of_eq h_smul)
      have h_mul_le :
          ∀ N,
            C N * ∫ y, ‖g y‖ ∂ μpartial N
              ≤ C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                    * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal := by
        intro N
        have h_int_le := h_int_g_le N
        calc C N * ∫ y, ‖g y‖ ∂ μpartial N
            ≤ C N * ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal) :=
          mul_le_mul_of_nonneg_left h_int_le (h_C_nonneg N)
          _ = C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal := by
            ring
      have h_ofReal_le :
          ∀ N,
            ENNReal.ofReal (C N * ∫ y, ‖g y‖ ∂ μpartial N)
              ≤ ENNReal.ofReal
                  (C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                    * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal) := by
        intro N
        refine ENNReal.ofReal_le_ofReal ?_
        exact h_mul_le N
      have hΨ_le_aux' :
          ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                (C N
                  * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal)) ^
              r.toReal := by
        intro N
        have h_int_le := h_int_g_le N
        have h_rpow_mono :
            (ENNReal.ofReal (C N * ∫ y, ‖g y‖ ∂ μpartial N)) ^ r.toReal
              ≤ (ENNReal.ofReal
                  (C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                    * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal)) ^ r.toReal := by
          exact ENNReal.rpow_le_rpow (h_ofReal_le N) (by exact ENNReal.toReal_nonneg)
        have h_base := hΨ_le_aux N
        exact le_trans h_base h_rpow_mono
      -- Replace eLpNorm(‖g‖) by eLpNorm g and bound it by the smul-measure growth.
      have hΨ_le_aux'' :
          ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                (C N
                  * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm g q μ).toReal)
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal)) ^
              r.toReal := by
        intro N
        have h_base := hΨ_le_aux' N
        -- Convert the inner factor using h_g_partial_bound_toReal and monotonicity
        have h_eqNorm :
            eLpNorm (fun y => ‖g y‖) q (μpartial N) = eLpNorm g q (μpartial N) :=
          eLpNorm_norm_eq_of_complex g q
        have h_g_toReal :
            (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal ≤
              (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal := by
          rw [h_eqNorm]
          exact h_g_partial_bound_toReal N
        set D1 := (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal with hD1
        have hD1_nonneg : 0 ≤ D1 := ENNReal.toReal_nonneg
        have h_mul_left :
            C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
              ≤ C N * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal := by
          exact mul_le_mul_of_nonneg_left h_g_toReal (h_C_nonneg N)
        have h_inner :
            C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal * D1
              ≤ C N * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal * D1 := by
          exact mul_le_mul_of_nonneg_right h_mul_left hD1_nonneg
        have h_ofReal_le :
            ENNReal.ofReal
                (C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal * D1)
              ≤ ENNReal.ofReal
                (C N * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal * D1) :=
          ENNReal.ofReal_le_ofReal h_inner
        have h_rpow_mono :
            (ENNReal.ofReal
              (C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal * D1)) ^ r.toReal
              ≤ (ENNReal.ofReal
              (C N * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) *
              eLpNorm g q μ).toReal * D1)) ^ r.toReal := by
          exact ENNReal.rpow_le_rpow h_ofReal_le (by exact ENNReal.toReal_nonneg)
        -- Chain the two bounds
        refine (le_trans h_base ?_)
        simpa [D1, mul_comm, mul_left_comm, mul_assoc] using h_rpow_mono
      -- Further refine the D1 factor using the ENNReal-level bound h_one_partial_bound
      -- and convert it to a toReal inequality when the global constant is finite.
      have h_one_partial_bound_toReal :
          ∀ N,
            eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞ →
            (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal ≤
              (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal := by
        intro N h_ne_top
        have h_le := h_one_partial_bound N
        have h_pow_ne_top :
            ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ≠ ∞ := by
          have h_exp_nonneg : 0 ≤ (1 / s₀).toReal := by simp [one_div]
          exact ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
        have h_rhs_ne_top :
            (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ≠ ∞ :=
          ENNReal.mul_ne_top h_pow_ne_top h_ne_top
        exact ENNReal.toReal_mono h_rhs_ne_top h_le
      -- Apply the toReal bound to refine Ψ when eLpNorm(1) on μ is finite.
      have hΨ_le_aux''' :
          ∀ N,
            eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞ →
            Ψ N ≤
              (ENNReal.ofReal
                (C N
                  * ((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal)
                        * eLpNorm g q μ).toReal)
                  * ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal))) ^
              r.toReal := by
        intro N h_ne_top
        have h_base := hΨ_le_aux'' N
        -- Replace D1 by its toReal-bound derived above
        set Dq := (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal with hDq
        set D1 := (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal with hD1
        set D1' := ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal) with hD1'
        have hD1_le : D1 ≤ D1' := by
          simpa [D1, D1'] using h_one_partial_bound_toReal N h_ne_top
        have h_nonneg_c : 0 ≤ C N * Dq := by
          have h1 : 0 ≤ C N := h_C_nonneg N
          have h2 : 0 ≤ Dq := by exact ENNReal.toReal_nonneg
          exact mul_nonneg h1 h2
        have h_inner_le :
            C N * Dq * D1 ≤ C N * Dq * D1' := by
          exact mul_le_mul_of_nonneg_left hD1_le h_nonneg_c
        have h_ofReal_le :
            ENNReal.ofReal (C N * Dq * D1) ≤ ENNReal.ofReal (C N * Dq * D1') :=
          ENNReal.ofReal_le_ofReal h_inner_le
        have h_rpow_mono :
            (ENNReal.ofReal (C N * Dq * D1)) ^ r.toReal
              ≤ (ENNReal.ofReal (C N * Dq * D1')) ^ r.toReal := by
          exact ENNReal.rpow_le_rpow h_ofReal_le (by exact ENNReal.toReal_nonneg)
        -- Chain with the previous bound on Ψ N
        exact le_trans h_base h_rpow_mono
      -- TODO: Next, relate the remaining factors using h_split and bounds for eLpNorm(1) and C N.
      -- Step 1 (implemented here): extract a normalized bounding sequence Θ and compare limsups.
      classical
      let Θ : ℕ → ℝ≥0∞ :=
        fun N =>
          (ENNReal.ofReal
            (C N
              * ((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal)
              * ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                    * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal))) ^ r.toReal
      have h_limsup_compare_Theta :
          eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞ →
          Filter.limsup Ψ Filter.atTop ≤ Filter.limsup Θ Filter.atTop := by
        intro h_ne_top
        refine Filter.limsup_le_limsup ?_
        exact Filter.Eventually.of_forall (fun N => by
          -- Directly apply the pointwise bound hΨ_le_aux''' to obtain Ψ N ≤ Θ N.
          simpa [Θ]
            using (hΨ_le_aux''' N h_ne_top))
  -- The remaining steps will turn limsup Θ into the desired constant bound
  -- using exponent identities (h_split) and norm estimates.
  -- We postpone them to the next step.
  -- Small helper lemmas for reorganizing products inside ENNReal.ofReal
  -- can be added if needed; for now we rely on simp with ENNReal.ofReal_mul.
      -- Next step: split on finiteness of ‖1‖_{s₀,μ} and set the target constant.
      by_cases h_one_finite : eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞
      · -- Under this finiteness, avoid N-growth and obtain a uniform bound on Ψ.
        have hcomp := h_limsup_compare_Theta h_one_finite
        -- First step of the Θ-rewrite: expand Θ N by pulling `toReal` outside `ofReal`
        -- and restoring the ENNReal factors. This normalizes Θ to a clean triple product
        -- of ENNReal factors raised to r.toReal, preparing exponent algebra.
        have hΘ_expand : ∀ N,
            Θ N =
              ( ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ)
                * ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm g q μ)
                * ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal
                    * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ) ^ r.toReal := by
          intro N
          -- Each inner real factor is nonnegative.
          have hC_nonneg : 0 ≤ C N := h_C_nonneg N
          have hDq_nonneg :
              0 ≤ ((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal) :=
            ENNReal.toReal_nonneg
          have hD1_nonneg :
              0 ≤ ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                      * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal) :=
            ENNReal.toReal_nonneg
          -- Finiteness of each ENNReal factor to use `ofReal_toReal`.
          have h_pow_r_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / r).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have hC_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ := by
            exact ENNReal.mul_ne_top h_pow_r_ne_top (by simpa using hf_r.eLpNorm_ne_top)
          have h_pow_q_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / q).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have hDq_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm g q μ) ≠ ∞ := by
            exact ENNReal.mul_ne_top h_pow_q_ne_top (by simpa using hg.eLpNorm_ne_top)
          have h_pow_s_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / s₀).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have hD1_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal
                  * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ≠ ∞ := by
            exact ENNReal.mul_ne_top h_pow_s_ne_top h_one_finite
          -- Expand `ofReal` over the triple product and restore ENNReal factors.
          have h_expand_ofReal :
              ENNReal.ofReal
                  (C N
                    * ((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal)
                    * ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                          * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal))
                =
                  ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ)
                    * ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm g q μ)
                    * ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) := by
            -- abbreviations for the ENNReal factors
            set DqE : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ with hDqE
            set D1E : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) *
              eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ with hD1E
            -- split ofReal over the triple product
            have h_mul3 : ENNReal.ofReal (C N * DqE.toReal * D1E.toReal)
                = ENNReal.ofReal (C N) * ENNReal.ofReal (DqE.toReal) *
                  ENNReal.ofReal (D1E.toReal) := by
              simp [ENNReal.ofReal_mul, hC_nonneg, hDq_nonneg, hD1_nonneg,
                mul_comm, mul_left_comm, mul_assoc]
            -- convert ofReal (toReal _) back to the ENNReal factors
            have hC_back : ENNReal.ofReal (C N)
                = ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) := by
              have h := ENNReal.ofReal_toReal (a :=
                (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ)) hC_ne_top
              -- h : ENNReal.ofReal (((...) ).toReal) = ((...) )
              simpa [C] using h
            have hDq_back : ENNReal.ofReal (DqE.toReal) = DqE := by
              simpa [hDqE] using ENNReal.ofReal_toReal (a := DqE) hDq_ne_top
            have hD1_back : ENNReal.ofReal (D1E.toReal) = D1E := by
              simpa [hD1E] using ENNReal.ofReal_toReal (a := D1E) hD1_ne_top
            -- assemble explicitly in two steps to avoid fragile `simpa` obligations
            have h_prod :
                ENNReal.ofReal (C N * DqE.toReal * D1E.toReal)
                  = ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) * (DqE * D1E) := by
              -- first rewrite via h_mul3, then restore each factor
              have := h_mul3
              -- `this` has the form ofReal(C*...*...) = ofReal C * ofReal ... * ofReal ...
              -- now replace each `ofReal (toReal _)` back to the ENNReal factor
              simpa [hC_back, hDq_back, hD1_back,
                    mul_comm, mul_left_comm, mul_assoc]
                using this
            have h_reassoc :
                ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) * (DqE * D1E)
                  = eLpNorm f r μ * (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * (DqE * D1E)) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
            -- rewrite (1/r).toReal as r.toReal⁻¹
            have h_exp_r : (1 / r).toReal = r.toReal⁻¹ := by
              have hr_ne_zero' : r ≠ 0 := hr_ne_zero
              simp [one_div, ENNReal.toReal_inv, hr_ne_zero', hr_ne_top]
            have h_prod_target :
                ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) * (DqE * D1E)
                  = eLpNorm f r μ * ((↑N + 1) ^ r.toReal⁻¹ * (DqE * D1E)) := by
              simp [h_exp_r, mul_comm, mul_left_comm, mul_assoc]
            -- combine with h_prod
            have := h_prod.trans h_prod_target
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
          -- Conclude the desired form of Θ N by rewriting with `h_expand_ofReal`.
          simpa [Θ] using congrArg (fun z => z ^ r.toReal) h_expand_ofReal
        -- Use μpartial N ≤ μ to get a uniform translate-norm bound.
        have hμpartial_le : ∀ N, μpartial N ≤ μ :=
          sfiniteSeq_partial_le_measure (μ := μ) (μn := μn) (μpartial := μpartial)
            (hμ_sum := hμ_sum) (hμpartial_def := fun _ => rfl)
        have h_translate_uniform : ∀ N y,
            (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ≤
              (eLpNorm f r μ).toReal := by
          intro N y
          have h_le :=
            eLpNorm_mono_measure (f := fun x => f (x - y)) (μ := μ) (ν := μpartial N) (p := r)
              (hμpartial_le N)
          have h_translate :=
            eLpNorm_comp_add_right (μ := μ) (f := f) (p := r) (y := -y)
              hf_r.aestronglyMeasurable
          have h_eq : eLpNorm (fun x => f (x - y)) r μ = eLpNorm f r μ := by
            simpa [sub_eq_add_neg] using h_translate
          exact ENNReal.toReal_mono hf_r.eLpNorm_ne_top (h_le.trans (le_of_eq h_eq))
        -- Hölder on μpartial N, then monotonicity to μ (using h_one_finite for finiteness).
        have h_int_g_le' : ∀ N,
            ∫ y, ‖g y‖ ∂ μpartial N
              ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal := by
          intro N
          have h_holder := h_int_g_le N
          have h_mono_g :
              (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal ≤
                (eLpNorm (fun y => ‖g y‖) q μ).toReal := by
            have h_le :=
              eLpNorm_mono_measure (f := fun y => ‖g y‖) (μ := μ) (ν := μpartial N) (p := q)
                (hμpartial_le N)
            exact ENNReal.toReal_mono (by simpa using hg.eLpNorm_ne_top) h_le
          have h_mono_one :
              (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal ≤
                (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal := by
            have h_le :=
              eLpNorm_mono_measure (f := fun _ : G => (1 : ℝ)) (μ := μ) (ν := μpartial N)
                (p := s₀) (hμpartial_le N)
            exact ENNReal.toReal_mono (by simpa using h_one_finite) h_le
          exact le_trans h_holder (mul_le_mul h_mono_g h_mono_one (by simp) (by simp))
        -- Step 4: Uniform Young bound via μ (replacing partial-measure factors).
        -- Use the uniform translate bound to control A by U := ‖f‖_r(μ).toReal,
        -- then push μpartial N → μ on the outer factors to obtain a per‑N bound with global norms.
        set U : ℝ := (eLpNorm f r μ).toReal with hUdef
        have hA_pointwise_uniform : ∀ N y, A N y ≤ U := by
          intro N y
          have := h_translate_uniform N y
          simpa [A, hUdef] using this
        have hA_toReal_le_uniform : ∀ N,
            (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
              ≤ (eLpNorm (fun _ : G => U) s₀ (μpartial N)).toReal := by
          intro N
          -- Use eLpNorm_le_of_ae_bound with the pointwise bound A ≤ U
          have h_bound : ∀ᵐ y ∂ μpartial N, ‖A N y‖ ≤ U := by
            refine Filter.Eventually.of_forall (fun y => ?_)
            have h_nonneg : 0 ≤ A N y := hA_nonneg N y
            have h_leU := hA_pointwise_uniform N y
            simpa [Real.norm_of_nonneg h_nonneg] using h_leU
          -- Convert to toReal using finiteness of RHS on finite measure
          haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
          have h_rhs_fin : eLpNorm (fun _ : G => U) s₀ (μpartial N) < ∞ := by
            by_cases hμz : μpartial N = 0
            · have : eLpNorm (fun _ : G => U) s₀ (μpartial N) = 0 := by simp [hμz]
              simp [this]
            · have hs₀_ne_zero' : s₀ ≠ 0 := hs₀_ne_zero
              have h_nonnegU : 0 ≤ U := ENNReal.toReal_nonneg
              have h_const :
                  eLpNorm (fun _ : G => U) s₀ (μpartial N)
                    = ENNReal.ofReal U * (μpartial N Set.univ) ^ (1 / s₀.toReal) := by
                have h_eLpNorm :=
                  eLpNorm_const (μ := μpartial N) (p := s₀) (c := U) hs₀_ne_zero' hμz
                simp only [Real.enorm_eq_ofReal h_nonnegU, Real.norm_eq_abs,
                  abs_of_nonneg h_nonnegU] at h_eLpNorm
                exact h_eLpNorm
              have hμ_lt_top : (μpartial N Set.univ) < ∞ := measure_lt_top _ _
              have hpow_lt : (μpartial N Set.univ) ^ (1 / s₀.toReal) < ∞ :=
                ENNReal.rpow_lt_top_of_nonneg (by simp [one_div]) hμ_lt_top.ne
              have h_ofReal_lt : ENNReal.ofReal U < ∞ := by simp
              have h_rhs_lt : ENNReal.ofReal U * (μpartial N Set.univ) ^ (1 / s₀.toReal) < ∞ :=
                ENNReal.mul_lt_top h_ofReal_lt hpow_lt
              simpa [h_const] using h_rhs_lt
          -- Use eLpNorm_le_of_ae_bound and rewrite to match expected form
          by_cases hμz : μpartial N = 0
          · simp [hμz]
          · have h_from_bound := eLpNorm_le_of_ae_bound (μ := μpartial N) (p := s₀)
              (f := fun y => A N y) h_bound
            have hs₀_ne_zero' : s₀ ≠ 0 := hs₀_ne_zero
            have h_nonnegU : 0 ≤ U := ENNReal.toReal_nonneg
            have h_const :
                eLpNorm (fun _ : G => U) s₀ (μpartial N)
                  = ENNReal.ofReal U * (μpartial N Set.univ) ^ (1 / s₀.toReal) := by
              have h_eLpNorm := eLpNorm_const (μ := μpartial N) (p := s₀) (c := U) hs₀_ne_zero' hμz
              simp only [Real.enorm_eq_ofReal h_nonnegU, Real.norm_eq_abs,
                abs_of_nonneg h_nonnegU] at h_eLpNorm
              exact h_eLpNorm
            have h_finite : ((μpartial N Set.univ) ^ s₀.toReal⁻¹ * ENNReal.ofReal U) < ∞ := by
              haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
              have h1 : (μpartial N Set.univ) < ∞ := measure_lt_top _ _
              have h2 : (μpartial N Set.univ) ^ s₀.toReal⁻¹ < ∞ :=
                ENNReal.rpow_lt_top_of_nonneg (by simp) h1.ne
              have h3 : ENNReal.ofReal U < ∞ := by simp
              exact ENNReal.mul_lt_top h2 h3
            calc (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
                ≤ ((μpartial N Set.univ) ^ s₀.toReal⁻¹ * ENNReal.ofReal U).toReal :=
                  ENNReal.toReal_mono h_finite.ne h_from_bound
              _ = (ENNReal.ofReal U * (μpartial N Set.univ) ^ s₀.toReal⁻¹).toReal := by ring_nf
              _ = (ENNReal.ofReal U * (μpartial N Set.univ) ^ (1 / s₀.toReal)).toReal := by
                rw [inv_eq_one_div]
              _ = (eLpNorm (fun _ : G => U) s₀ (μpartial N)).toReal := by rw [← h_const]
        -- Expand the constant eLpNorm on μpartial N and push to μ using monotonicity.
        have h_const_toReal_eval : ∀ N,
            (eLpNorm (fun _ : G => U) s₀ (μpartial N)).toReal
              = U * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal := by
          intro N
          have h_nonnegU : 0 ≤ U := ENNReal.toReal_nonneg
          -- Show that (fun _ => U) = U • (fun _ => 1)
          have h_fun_eq : (fun _ : G => U) = U • (fun _ : G => (1 : ℝ)) := by
            ext x
            simp [smul_eq_mul]
          rw [h_fun_eq]
          have h_smul := eLpNorm_const_smul (μ := μpartial N) (p := s₀) (c := U)
            (f := fun _ : G => (1 : ℝ))
          simp only [Real.enorm_eq_ofReal h_nonnegU] at h_smul
          have := congrArg ENNReal.toReal h_smul
          simpa [ENNReal.toReal_mul, h_nonnegU] using this
        have hA_toReal_uniform_push : ∀ N,
            (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
              ≤ U * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal := by
          intro N
          have := (hA_toReal_le_uniform N)
          have h_eval := (h_const_toReal_eval N)
          -- push to μ using monotonicity
          have h_push : (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal ≤
              (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal := by
            have h_le :=
              eLpNorm_mono_measure (f := fun _ : G => (1 : ℝ)) (μ := μ) (ν := μpartial N)
                (p := s₀) (hμpartial_le N)
            exact ENNReal.toReal_mono (by simpa using h_one_finite) h_le
          have h_nonnegU : 0 ≤ U := ENNReal.toReal_nonneg
          have : U * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal
              ≤ U * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal :=
            mul_le_mul_of_nonneg_left h_push h_nonnegU
          -- combine
          have := (le_trans this (le_of_eq rfl))
          -- actually, rewrite `this` appropriately
          exact (le_trans (by simpa [h_eval] using (hA_toReal_le_uniform N))
            (by simpa using this))
        -- Assemble the per‑N uniform Young bound with global μ on all factors.
        have hΨ_le_step4_uniform : ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * U
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal)) ^ r.toReal := by
          intro N
          have h_base := hΨ_le_from_template N
          -- Replace the A-term and the g,1 factors by global μ bounds
          have h1 :
              (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
            ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal
                * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal := by
            have h_mono_g :
                (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal ≤
                  (eLpNorm (fun y => ‖g y‖) q μ).toReal := by
              have h_le :=
                eLpNorm_mono_measure (f := fun y => ‖g y‖) (μ := μ) (ν := μpartial N) (p := q)
                  (hμpartial_le N)
              exact ENNReal.toReal_mono (by simpa using hg.eLpNorm_ne_top) h_le
            exact mul_le_mul_of_nonneg_right h_mono_g ENNReal.toReal_nonneg
          have h2 :
              (eLpNorm (fun y => ‖g y‖) q μ).toReal
                * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
            ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal
                * (U * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal) := by
            have h_nonneg : 0 ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal := ENNReal.toReal_nonneg
            exact mul_le_mul_of_nonneg_left (hA_toReal_uniform_push N) h_nonneg
          have h_inner_le := le_trans h1 h2
          have h_ofReal_mono := ENNReal.ofReal_le_ofReal h_inner_le
          have h_rpow_mono :=
            ENNReal.rpow_le_rpow (z := r.toReal) h_ofReal_mono ENNReal.toReal_nonneg
          -- Finish: h_base gives Ψ N ≤ (ofReal(...eLpNorm g... * ...eLpNorm A...))^r
          -- We need to show this is ≤ (ofReal(‖g‖_q * U * ‖1‖_{s₀}))^r
          calc Ψ N
              ≤ (ENNReal.ofReal ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)) ^ r.toReal := h_base
            _ ≤ (ENNReal.ofReal ((eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * (U * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal))) ^ r.toReal := h_rpow_mono
            _ = (ENNReal.ofReal ((eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * U * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal)) ^ r.toReal := by
              congr 1
              ring_nf
        -- Convert constants using the Hölder triple bound.
        have h_holder_one :
            eLpNorm f p μ ≤ eLpNorm f r μ * eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ := by
          -- Build the Hölder triple instance using the split 1/p = 1/r + 1/s₀.
          haveI : ENNReal.HolderTriple r s₀ p :=
            ⟨by simpa [one_div] using h_split.symm⟩
          simpa using
            eLpNorm_mul_one_le (μ := μ) (f := f) (p := p) (r := r) (s := s₀)
              (hf_meas := hf.aestronglyMeasurable)
        -- Replace ‖g‖ L^q by g L^q.
        have h_g_eq : eLpNorm (fun y => ‖g y‖) q μ = eLpNorm g q μ := by
          simp
        -- Identify the constant-1 norms over ℝ and ℂ to compare with Hölder.
        have h_one_real_eq_complex :
            eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ
              = eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ := by
          by_cases hμz : μ = 0
          · simp [hμz]
          · have h_nonnegR : 0 ≤ (1 : ℝ) := by simp
            have h_nonnegC : 0 ≤ (1 : ℝ) := by simp
            have hR :=
              (eLpNorm_const (μ := μ) (p := s₀) (c := (1 : ℝ)) hs₀_ne_zero hμz)
            have hC :=
              (eLpNorm_const (μ := μ) (p := s₀) (c := (1 : ℂ)) hs₀_ne_zero hμz)
            -- Rewrite both sides to the common closed form.
            -- For ℝ
            have hR' :
                eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ
                  = ENNReal.ofReal (1 : ℝ)
                      * (μ Set.univ) ^ (1 / s₀.toReal) := by
              simpa [Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
                Real.norm_eq_abs, abs_of_nonneg h_nonnegR] using hR
            -- For ℂ
            have hC' :
                eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ
                  = ENNReal.ofReal (‖(1 : ℂ)‖)
                      * (μ Set.univ) ^ (1 / s₀.toReal) := by
              simpa [Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
                Real.norm_eq_abs, Complex.norm_real, abs_of_nonneg h_nonnegC]
                using hC
            simp [hR', hC']
        -- Step 1: Switch to the Θ-limsup route instead of the K-bound.
        -- We already have `hcomp : limsup Ψ ≤ limsup Θ` from `h_limsup_compare_Theta`.
        -- Compose with the earlier `h_limsup_goal : ∫⁻ ... ≤ limsup Ψ`.
        have h_limsup_le_Theta : Filter.limsup Ψ Filter.atTop ≤ Filter.limsup Θ Filter.atTop :=
          hcomp
        have h_goal_to_Theta :
            (∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ)
              ≤ Filter.limsup Θ Filter.atTop :=
          le_trans h_limsup_goal h_limsup_le_Theta
        -- Step 2: Expand Θ N as a clean product, distributing r-powers across factors.
        have hr_nonneg : 0 ≤ r.toReal := le_of_lt hr_toReal_pos
        have hΘ_split : ∀ N,
            Θ N =
              (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                * (eLpNorm f r μ) ^ r.toReal
                * (eLpNorm g q μ) ^ r.toReal
                * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ^ r.toReal := by
          intro N
          -- Start from the triple-product expansion of Θ.
          have h := hΘ_expand N
          -- Abbreviations for readability
          set Ar : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal)
          set Br : ℝ≥0∞ := eLpNorm f r μ
          set Aq : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal)
          set Bq : ℝ≥0∞ := eLpNorm g q μ
          set As : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
          set Bs : ℝ≥0∞ := eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ
          -- Θ N = (Ar*Br * (Aq*Bq) * (As*Bs)) ^ r
          have h' : Θ N = (((Ar * Br) * (Aq * Bq)) * (As * Bs)) ^ r.toReal := by
            simpa [Ar, Br, Aq, Bq, As, Bs, mul_comm, mul_left_comm, mul_assoc] using h
          -- Distribute the r-power across the product using `mul_rpow_of_nonneg`.
          have h1 : (((Ar * Br) * (Aq * Bq)) * (As * Bs)) ^ r.toReal
              = ((Ar * Br) * (Aq * Bq)) ^ r.toReal * (As * Bs) ^ r.toReal := by
            simpa [mul_comm, mul_left_comm, mul_assoc]
              using (ENNReal.mul_rpow_of_nonneg ((Ar * Br) * (Aq * Bq)) (As * Bs) hr_nonneg)
          have h2 : ((Ar * Br) * (Aq * Bq)) ^ r.toReal
              = (Ar * Br) ^ r.toReal * (Aq * Bq) ^ r.toReal := by
            simpa [mul_comm, mul_left_comm, mul_assoc]
              using (ENNReal.mul_rpow_of_nonneg (Ar * Br) (Aq * Bq) hr_nonneg)
          have h3 : (Ar * Br) ^ r.toReal = Ar ^ r.toReal * Br ^ r.toReal := by
            simpa using (ENNReal.mul_rpow_of_nonneg Ar Br hr_nonneg)
          have h4 : (Aq * Bq) ^ r.toReal = Aq ^ r.toReal * Bq ^ r.toReal := by
            simpa using (ENNReal.mul_rpow_of_nonneg Aq Bq hr_nonneg)
          -- Also record the commuted variant to avoid orientation mismatches during simp.
          have h4_comm : (Bq * Aq) ^ r.toReal = Bq ^ r.toReal * Aq ^ r.toReal := by
            simpa [mul_comm] using (ENNReal.mul_rpow_of_nonneg Bq Aq hr_nonneg)
          have h5 : (As * Bs) ^ r.toReal = As ^ r.toReal * Bs ^ r.toReal := by
            simpa using (ENNReal.mul_rpow_of_nonneg As Bs hr_nonneg)
          -- Assemble and clean up associations/commutations.
          calc
            Θ N = (((Ar * Br) * (Aq * Bq)) * (As * Bs)) ^ r.toReal := h'
            _ = ((Ar * Br) * (Aq * Bq)) ^ r.toReal * (As * Bs) ^ r.toReal := h1
            _ = (Ar * Br) ^ r.toReal * (Aq * Bq) ^ r.toReal * (As * Bs) ^ r.toReal := by
              rw [h2]
            _ = (Ar ^ r.toReal * Br ^ r.toReal) * (Aq * Bq) ^ r.toReal * (As * Bs) ^ r.toReal := by
              rw [h3]
            _ = (Ar ^ r.toReal * Br ^ r.toReal) * (Aq ^ r.toReal * Bq ^ r.toReal) *
              (As * Bs) ^ r.toReal := by rw [h4]
            _ = (Ar ^ r.toReal * Br ^ r.toReal) * (Aq ^ r.toReal * Bq ^ r.toReal) *
              (As ^ r.toReal * Bs ^ r.toReal) := by rw [h5]
            _ = (Ar ^ r.toReal) * (Aq ^ r.toReal) * (As ^ r.toReal)
                * (Br ^ r.toReal) * (Bq ^ r.toReal) * (Bs ^ r.toReal) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
            _ = (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                * (eLpNorm f r μ) ^ r.toReal
                * (eLpNorm g q μ) ^ r.toReal
                * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ^ r.toReal := by
              show Ar ^ r.toReal * Aq ^ r.toReal * As ^ r.toReal
                * Br ^ r.toReal * Bq ^ r.toReal * Bs ^ r.toReal
                = (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                  * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                  * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                  * (eLpNorm f r μ) ^ r.toReal
                  * (eLpNorm g q μ) ^ r.toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ^ r.toReal
              rfl
        -- Step 3: Prepare exponent identities to collapse ((N+1))-powers later.
        have hq_ne_zero' : q ≠ 0 := by
          have : (0 : ℝ≥0∞) < q := lt_trans (by simp) hq
          exact ne_of_gt this
        have h_inv_r_toReal : (1 / r).toReal = r.toReal⁻¹ := by
          simp [one_div, ENNReal.toReal_inv, hr_ne_zero, hr_ne_top]
        have h_inv_q_toReal : (1 / q).toReal = q.toReal⁻¹ := by
          simp [one_div, ENNReal.toReal_inv, hq_ne_zero', hq_ne_top]
        have h_inv_s_toReal : (1 / s₀).toReal = s₀.toReal⁻¹ := by
          simp [one_div, ENNReal.toReal_inv, hs₀_ne_zero, hs₀_ne_top]
        -- Conjugacy of q and s₀ on the real side: q⁻¹ + s₀⁻¹ = 1 (in toReal exponents).
        have h_qs_sum_toReal : q.toReal⁻¹ + s₀.toReal⁻¹ = 1 := by
          have hq_ne_zero' : q ≠ 0 := by
            have : (0 : ℝ≥0∞) < q := lt_trans (by simp) hq
            exact ne_of_gt this
          exact
            (conjugate_exponent_toReal_sum
              (p := q) (q := s₀)
              (hp_ne_zero := hq_ne_zero') (hp_ne_top := hq_ne_top)
              (hq_ne_zero := hs₀_ne_zero) (hq_ne_top := hs₀_ne_top)
              (hpq_sum := by
                -- from conjugacy hs₀_conj : IsConjugateExponent q s₀ we extract 1/q + 1/s₀ = 1
                rcases hs₀_conj with h | h | h
                · rcases h with ⟨hq_one, hs_top⟩; simp [hq_one, hs_top]
                · rcases h with ⟨hq_top, hs_one⟩; cases hq_ne_top hq_top
                · rcases h with ⟨_, _, _, _, hsum⟩; simpa using hsum))
        -- Auxiliary packing of the ((N+1))-powers inside Θ.
        have h_base_ne_zero : ∀ N : ℕ, ((N + 1 : ℝ≥0∞)) ≠ 0 := by intro N; simp
        have h_base_ne_top : ∀ N : ℕ, ((N + 1 : ℝ≥0∞)) ≠ ∞ := by intro N; simp
        have h_pack_N : ∀ N : ℕ,
            (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
              * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
              * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
            = ((N + 1 : ℝ≥0∞)) ^
                (((1 / r).toReal * r.toReal)
                  + ((1 / q).toReal * r.toReal)
                  + ((1 / s₀).toReal * r.toReal)) := by
          intro N
          -- Convert ((X^a)^r) into X^(a*r) for each exponent a.
          have h1 :
              (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                = ((N + 1 : ℝ≥0∞)) ^ ((1 / r).toReal * r.toReal) := by
            simp [ENNReal.rpow_mul]
          have h2 :
              (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                = ((N + 1 : ℝ≥0∞)) ^ ((1 / q).toReal * r.toReal) := by
            simp [ENNReal.rpow_mul]
          have h3 :
              (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                = ((N + 1 : ℝ≥0∞)) ^ ((1 / s₀).toReal * r.toReal) := by
            simp [ENNReal.rpow_mul]
          -- Combine via rpow_add twice: X^(a*r)*X^(b*r)*X^(c*r) = X^((a+b+c)*r)
          have h12 :
              ((N + 1 : ℝ≥0∞) ^ ((1 / r).toReal * r.toReal))
                * ((N + 1 : ℝ≥0∞) ^ ((1 / q).toReal * r.toReal))
              = ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal))) := by
            simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
              using
                (ENNReal.rpow_add (x := (N + 1 : ℝ≥0∞))
                  (y := ((1 / r).toReal * r.toReal))
                  (z := ((1 / q).toReal * r.toReal))
                  (h_base_ne_zero N) (h_base_ne_top N)).symm
          have h123 :
              ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal)))
                * ((N + 1 : ℝ≥0∞) ^ ((1 / s₀).toReal * r.toReal))
              = ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal)
                    + ((1 / s₀).toReal * r.toReal))) := by
            simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
              using
                (ENNReal.rpow_add (x := (N + 1 : ℝ≥0∞))
                  (y := (((1 / r).toReal * r.toReal) + ((1 / q).toReal * r.toReal)))
                  (z := ((1 / s₀).toReal * r.toReal))
                  (h_base_ne_zero N) (h_base_ne_top N)).symm
          -- Assemble
          calc
            (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                = ((N + 1 : ℝ≥0∞) ^ ((1 / r).toReal * r.toReal))
                    * ((N + 1 : ℝ≥0∞) ^ ((1 / q).toReal * r.toReal))
                    * ((N + 1 : ℝ≥0∞) ^ ((1 / s₀).toReal * r.toReal)) := by
              rw [h1, h2, h3]
            _ = ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal)))
                * ((N + 1 : ℝ≥0∞) ^ ((1 / s₀).toReal * r.toReal)) := by
              rw [← h12]
            _ = ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal)
                    + ((1 / s₀).toReal * r.toReal))) := by
              rw [← h123]
            -- We keep the exponent in the expanded additive form for later use.
        -- We will evaluate limsup Θ using these packed exponents in the next step.
        -- Step 3: Regroup Θ into an N-dependent part P and an N-independent constant Cconst.
        -- This isolates the growth from the fixed L^p constants.
        set P : ℕ → ℝ≥0∞ :=
          fun N =>
            (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
              * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
              * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal) with hPdef
        set Cconst : ℝ≥0∞ :=
          (eLpNorm f r μ) ^ r.toReal
            * (eLpNorm g q μ) ^ r.toReal
            * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ^ r.toReal with hCdef
        have hΘ_group : ∀ N, Θ N = P N * Cconst := by
          intro N
          have := hΘ_split N
          -- Reassociate the six-term product into P N times Cconst.
          simpa [P, Cconst, mul_comm, mul_left_comm, mul_assoc]
            using this
        -- Step 4: Pack P into a single ((N+1)) power with total exponent S.
        set S : ℝ :=
          ((1 / r).toReal * r.toReal)
            + ((1 / q).toReal * r.toReal)
            + ((1 / s₀).toReal * r.toReal) with hSdef
        have hP_pack : ∀ N, P N = ((N + 1 : ℝ≥0∞) ^ S) := by
          intro N
          -- Unfold P and use the prepared packing lemma h_pack_N.
          simp [P, hSdef] at *
          simpa using h_pack_N N
        -- Simplify S using the inverse-toReal identities and conjugacy q⋆s₀.
        have hrtoReal_ne_zero : r.toReal ≠ 0 := ne_of_gt hr_toReal_pos
        have h1 : ((1 / r).toReal * r.toReal) = (1 : ℝ) := by
          -- (1/r).toReal = (r.toReal)⁻¹, hence product is 1.
          rw [h_inv_r_toReal]
          field_simp
        have h2 : ((1 / q).toReal * r.toReal) + ((1 / s₀).toReal * r.toReal)
            = r.toReal := by
          calc
            ((1 / q).toReal * r.toReal) + ((1 / s₀).toReal * r.toReal)
                = r.toReal * (1 / q).toReal + r.toReal * (1 / s₀).toReal := by
                  simp [mul_comm]
            _ = r.toReal * ((1 / q).toReal + (1 / s₀).toReal) := by
                  simp [mul_add]
            _ = r.toReal * (q.toReal⁻¹ + s₀.toReal⁻¹) := by
                  simp [h_inv_q_toReal, h_inv_s_toReal]
            _ = r.toReal * (1 : ℝ) := by
                  simp [h_qs_sum_toReal]
            _ = r.toReal := by simp
        have hS_simplify : S = 1 + r.toReal := by
          -- Regroup S as (1/r).toReal*r.toReal + [rest] and apply h1, h2.
          have : S = ((1 / r).toReal * r.toReal)
                        + (((1 / q).toReal * r.toReal)
                            + ((1 / s₀).toReal * r.toReal)) := by
            -- Just reassociating additions.
            have := hSdef
            -- Normalize associativity/commutativity
            simp [this, add_comm, add_left_comm, add_assoc]
          -- Conclude
          calc S = ((1 / r).toReal * r.toReal)
                        + (((1 / q).toReal * r.toReal)
                            + ((1 / s₀).toReal * r.toReal)) := this
               _ = 1 + (((1 / q).toReal * r.toReal) + ((1 / s₀).toReal * r.toReal)) := by rw [h1]
               _ = 1 + r.toReal := by rw [h2]
        -- Optional: record a packed form with the simplified exponent S' := 1 + r.toReal.
        set S' : ℝ := 1 + r.toReal with hS'def
        have hP_pack' : ∀ N, P N = ((N + 1 : ℝ≥0∞) ^ S') := by
          intro N; simpa [hS_simplify, hS'def] using hP_pack N
        -- Step 5: Pull out Cconst from limsup Θ and evaluate limsup P.
        have hfunextΘ : Θ = (fun N => P N * Cconst) := by
          funext N; simpa using hΘ_group N
        have hfunextP : P = (fun N : ℕ => ((↑N + 1 : ℝ≥0∞) ^ S')) := by
          funext N; simpa [hS'def] using hP_pack' N
        -- Finiteness of the constant multiplier Cconst.
        have hCconst_ne_top : Cconst ≠ ∞ := by
          have hr_nonneg : 0 ≤ r.toReal := le_of_lt hr_toReal_pos
          have hfr_ne_top : eLpNorm f r μ ≠ ∞ := by simpa using hf_r.eLpNorm_ne_top
          have hg_ne_top : eLpNorm g q μ ≠ ∞ := by simpa using hg.eLpNorm_ne_top
          have h1 : (eLpNorm f r μ) ^ r.toReal ≠ ∞ :=
            ENNReal.rpow_ne_top_of_nonneg hr_nonneg hfr_ne_top
          have h2 : (eLpNorm g q μ) ^ r.toReal ≠ ∞ :=
            ENNReal.rpow_ne_top_of_nonneg hr_nonneg hg_ne_top
          have h3 : (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ^ r.toReal ≠ ∞ := by
            have h_ne_top : eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞ := h_one_finite
            exact ENNReal.rpow_ne_top_of_nonneg hr_nonneg h_ne_top
          have h12 :
              (eLpNorm f r μ) ^ r.toReal * (eLpNorm g q μ) ^ r.toReal ≠ ∞ :=
            ENNReal.mul_ne_top h1 h2
          -- Cconst = (a*b) * c
          simpa [Cconst, hCdef, mul_comm, mul_left_comm, mul_assoc]
            using ENNReal.mul_ne_top h12 h3
        -- Rewrite Θ and apply the limsup factorization.
        have h_limsup_pull :
            Filter.limsup Θ Filter.atTop
              = Filter.limsup P Filter.atTop * Cconst := by
          have : Filter.limsup (fun N => P N * Cconst) Filter.atTop
              = Filter.limsup P Filter.atTop * Cconst :=
            limsup_mul_const_atTop (u := P) (C := Cconst) hCconst_ne_top
          simpa [hfunextΘ] using this
        -- Evaluate limsup P via positivity of S'.
        have hSpos : 0 < S' := by
          have : 0 < r.toReal := hr_toReal_pos; linarith
        have h_limsupP_top : Filter.limsup P Filter.atTop = ∞ := by
          rw [hfunextP]
          exact limsup_rpow_nat_atTop_eq_top hSpos
        -- Compact evaluation: limsup Θ = (∞)*Cconst (which is ∞ unless Cconst = 0).
        have h_limsupΘ_eval :
            Filter.limsup Θ Filter.atTop = ∞ * Cconst := by
          simpa [h_limsupP_top] using h_limsup_pull
        -- Uniform finite bound for Ψ using the r-based constants (finite-μ case).
        -- Define the ENNReal constant K := ‖f‖_r · ‖g‖_q · ‖1‖_{s₀}.
        set KconstE : ℝ≥0∞ :=
          (eLpNorm f r μ) * (eLpNorm g q μ)
            * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) with hKdef
        have hΨ_uniform :
            ∀ N, Ψ N ≤ (KconstE) ^ r.toReal := by
          intro N
          -- Abbreviations on the real side.
          set F : ℝ := (eLpNorm f r μ).toReal with hFdef
          set Gq : ℝ := (eLpNorm (fun y => ‖g y‖) q μ).toReal with hGqdef
          set O : ℝ := (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal with hOdef
          -- Pointwise inequality for the A-term.
          have h_pointwise :
              ∀ y,
                ‖g y‖
                  * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal
                ≤ ‖g y‖ * F := by
            intro y
            have := h_translate_uniform N y
            exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
          -- Integrability of both sides.
          have h_left_int :
              Integrable
                (fun y =>
                  ‖g y‖
                    * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal)
                (μpartial N) := by
            simpa using h_norm_piece N
          have h_right_int : Integrable (fun y => ‖g y‖ * F) (μpartial N) := by
            simpa using (hg_partial_int N).norm.mul_const F
          -- Integrate and estimate the RHS integral using Hölder-on-μ bound.
          have h_int_leF :
              ∫ y, ‖g y‖
                  * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N
                ≤ ∫ y, ‖g y‖ * F ∂ μpartial N := by
            refine integral_mono_ae h_left_int h_right_int ?_
            exact Filter.Eventually.of_forall h_pointwise
          have h_int_eval :
              ∫ y, ‖g y‖ * F ∂ μpartial N
                = F * ∫ y, ‖g y‖ ∂ μpartial N := by
            simpa [mul_comm, mul_left_comm, mul_assoc]
              using
                (integral_mul_const (μ := μpartial N) (r := F)
                  (f := fun y => ‖g y‖))
          have h_bound_intg :
              ∫ y, ‖g y‖ ∂ μpartial N
                ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal
                    * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal :=
            h_int_g_le' N
          have h_nonnegF : 0 ≤ F := ENNReal.toReal_nonneg
          have h_step_real :
              ∫ y, ‖g y‖
                  * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N
                ≤ F * (Gq * O) := by
            calc
              _ ≤ ∫ y, ‖g y‖ * F ∂ μpartial N := h_int_leF
              _ = F * ∫ y, ‖g y‖ ∂ μpartial N := h_int_eval
              _ ≤ F * (Gq * O) := by
                have : F * ∫ y, ‖g y‖ ∂ μpartial N
                    ≤ F * ((eLpNorm (fun y => ‖g y‖) q μ).toReal
                        * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal) := by
                  exact mul_le_mul_of_nonneg_left h_bound_intg h_nonnegF
                simpa [Gq, O, mul_comm, mul_left_comm, mul_assoc] using this
          -- Pass to ENNReal and raise both sides to r.toReal.
          have h_ofReal_le :
              ENNReal.ofReal
                (∫ y, ‖g y‖
                    * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N)
                ≤ ENNReal.ofReal (F * (Gq * O)) :=
            ENNReal.ofReal_le_ofReal h_step_real
          have h_rpow_mono :
              (ENNReal.ofReal
                (∫ y, ‖g y‖
                    * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N))
                  ^ r.toReal
                ≤ (ENNReal.ofReal (F * (Gq * O))) ^ r.toReal := by
            exact ENNReal.rpow_le_rpow h_ofReal_le ENNReal.toReal_nonneg
          -- Identify RHS base as KconstE via ofReal-toReal cancellations.
          have hF_back : ENNReal.ofReal F = eLpNorm f r μ := by
            simpa [F] using ENNReal.ofReal_toReal (a := eLpNorm f r μ) (hf_r.eLpNorm_ne_top)
          have hGq_back :
              ENNReal.ofReal Gq = eLpNorm (fun y => ‖g y‖) q μ := by
            simpa [Gq] using ENNReal.ofReal_toReal
              (a := eLpNorm (fun y => ‖g y‖) q μ) (by simpa using hg.eLpNorm_ne_top)
          have hO_back :
              ENNReal.ofReal O = eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ := by
            simpa [O] using ENNReal.ofReal_toReal
              (a := eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) h_one_finite
          have h_ofReal_prod :
              ENNReal.ofReal (F * (Gq * O)) = KconstE := by
            have hF_nonneg : 0 ≤ F := ENNReal.toReal_nonneg
            have hG_nonneg : 0 ≤ Gq := ENNReal.toReal_nonneg
            have hO_nonneg : 0 ≤ O := ENNReal.toReal_nonneg
            have :
                ENNReal.ofReal (F * Gq * O)
                  = ENNReal.ofReal F * ENNReal.ofReal Gq * ENNReal.ofReal O := by
              simpa [mul_comm, mul_left_comm, mul_assoc]
                using ofReal_mul_three hF_nonneg hG_nonneg hO_nonneg
            have h_assoc : F * (Gq * O) = F * Gq * O := by
              ring
            rw [h_assoc]
            rw [this]
            rw [hF_back, hGq_back, hO_back, h_g_eq]
          -- Assemble: Ψ N ≤ (KconstE)^r
          have :
              (ENNReal.ofReal
                (∫ y, ‖g y‖
                    * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N))
                  ^ r.toReal
                ≤ (KconstE) ^ r.toReal := by
            simpa [h_ofReal_prod] using h_rpow_mono
          simpa [Ψ, hΨ_def] using this
        -- Record (for later use) a limsup bound for Ψ by the uniform constant (KconstE)^r
        have h_limsupΨ_leK :
            Filter.limsup Ψ Filter.atTop ≤ (KconstE) ^ r.toReal := by
          have hev : ∀ᶠ N in Filter.atTop, Ψ N ≤ (KconstE) ^ r.toReal :=
            Filter.Eventually.of_forall hΨ_uniform
          exact Filter.limsup_le_of_le (h := hev)
        -- Align KconstE with the complex-constant form to compare with Hölder-on-μ.
        have h_one_complex :
            eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ
              = eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ :=
          h_one_real_eq_complex
        have hK_rewrite :
            KconstE
              = (eLpNorm f r μ)
                  * (eLpNorm g q μ)
                  * (eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ) := by
          simp [KconstE, hKdef, mul_comm, mul_left_comm, mul_assoc, h_one_complex]
        -- From Hölder triple: ‖f‖_p ≤ ‖f‖_r · ‖1‖_{s₀} on μ; multiply by ‖g‖_q.
        have h_target_le_K :
            eLpNorm f p μ * eLpNorm g q μ ≤ KconstE := by
          have h_base := h_holder_one
          have h_mul := mul_le_mul_right' h_base (eLpNorm g q μ)
          -- Reassociate to match KconstE using commutativity.
          simpa [hK_rewrite, mul_comm, mul_left_comm, mul_assoc]
            using h_mul
        -- Raise to r.toReal to relate the r-powered constants (monotone since r.toReal ≥ 0).
        have h_target_le_K_rpow :
            (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal
              ≤ (KconstE) ^ r.toReal :=
          ENNReal.rpow_le_rpow h_target_le_K ENNReal.toReal_nonneg
        -- First consequence: a concrete finite bound with the r-based constant KconstE.
        have h_goal_fin_K :
            (∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ)
              ≤ (KconstE) ^ r.toReal :=
          le_trans h_limsup_goal h_limsupΨ_leK
        -- Prepare the target p-based constant and its finiteness properties for the next step.
        set targetE : ℝ≥0∞ := (eLpNorm f p μ) * (eLpNorm g q μ) with hTargetE
        have h_targetE_ne_top : targetE ≠ ∞ := by
          have hf_fin : eLpNorm f p μ ≠ ∞ := by simpa using hf.eLpNorm_ne_top
          have hg_fin : eLpNorm g q μ ≠ ∞ := by simpa using hg.eLpNorm_ne_top
          simpa [targetE, hTargetE, mul_comm, mul_left_comm, mul_assoc]
            using ENNReal.mul_ne_top hf_fin hg_fin
        have hr_nonneg : 0 ≤ r.toReal := le_of_lt hr_toReal_pos
        have h_targetE_rpow_ne_top : targetE ^ r.toReal ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg hr_nonneg h_targetE_ne_top
        -- First step toward the p-based bound: reduce to a uniform L^{s₀} estimate on A.
        -- If we can show that for all N,
        --   (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal ≤ (eLpNorm f p μ).toReal,
        -- then Ψ N ≤ (eLpNorm f p μ * eLpNorm g q μ)^r for all N, hence the desired goal.
        have hΨ_le_target_from_A_bound :
            (∀ N, (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal ≤ (eLpNorm f p μ).toReal) →
            ∀ N, Ψ N ≤ targetE ^ r.toReal := by
          intro hA_bound N
          -- Start from the Young template on the finite piece μpartial N.
          have h_base := hΨ_le_young_template N (hA_mem N)
          -- Monotonicity in the measure for the g-factor (push from μpartial N to μ).
          have h_mono_g_toReal :
              (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal ≤
                (eLpNorm (fun y => ‖g y‖) q μ).toReal := by
            have h_le :=
              eLpNorm_mono_measure (f := fun y => ‖g y‖) (μ := μ) (ν := μpartial N) (p := q)
                (hμpartial_le N)
            exact ENNReal.toReal_mono (by simpa using hg.eLpNorm_ne_top) h_le
          -- Combine the two real bounds inside ENNReal.ofReal via monotonicity and then rpow.
          have h_mul_le :
              (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
              ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal * (eLpNorm f p μ).toReal := by
            -- Now use the assumed uniform L^{s₀} bound on A.
            have hA := hA_bound N
            -- First step: bound left factor by the larger measure
            calc (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
                ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal
                    * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal := by
                  exact mul_le_mul_of_nonneg_right h_mono_g_toReal ENNReal.toReal_nonneg
              _ ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal * (eLpNorm f p μ).toReal := by
                  exact mul_le_mul_of_nonneg_left hA ENNReal.toReal_nonneg
          have h_ofReal_le :
              ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)
              ≤ ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q μ).toReal * (eLpNorm f p μ).toReal) :=
            ENNReal.ofReal_le_ofReal h_mul_le
          have h_rpow_mono :
              (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)) ^ r.toReal
              ≤ (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q μ).toReal * (eLpNorm f p μ).toReal))
                  ^ r.toReal := by
            exact ENNReal.rpow_le_rpow h_ofReal_le ENNReal.toReal_nonneg
          -- Identify the RHS base with targetE via ofReal-toReal cancellations.
          have h_g_eq' : eLpNorm (fun y => ‖g y‖) q μ = eLpNorm g q μ := by simp
          have hG_back :
              ENNReal.ofReal ((eLpNorm (fun y => ‖g y‖) q μ).toReal)
                = eLpNorm (fun y => ‖g y‖) q μ := by
            simpa using ENNReal.ofReal_toReal
              (a := eLpNorm (fun y => ‖g y‖) q μ) (by simpa using hg.eLpNorm_ne_top)
          have hF_back : ENNReal.ofReal ((eLpNorm f p μ).toReal) = eLpNorm f p μ := by
            simpa using ENNReal.ofReal_toReal
              (a := eLpNorm f p μ) (by simpa using hf.eLpNorm_ne_top)
          have h_ofReal_prod_target :
              ENNReal.ofReal ((eLpNorm (fun y => ‖g y‖) q μ).toReal * (eLpNorm f p μ).toReal)
                = targetE := by
            -- Expand ENNReal.ofReal over the product and cancel toReal on each factor.
            have h_nonneg1 : 0 ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal := ENNReal.toReal_nonneg
            have h_nonneg2 : 0 ≤ (eLpNorm f p μ).toReal := ENNReal.toReal_nonneg
            have :
                ENNReal.ofReal
                    ((eLpNorm (fun y => ‖g y‖) q μ).toReal * (eLpNorm f p μ).toReal)
                  = ENNReal.ofReal ((eLpNorm (fun y => ‖g y‖) q μ).toReal)
                      * ENNReal.ofReal ((eLpNorm f p μ).toReal) := by
              exact ENNReal.ofReal_mul h_nonneg1
            have step2 :
                ENNReal.ofReal ((eLpNorm (fun y => ‖g y‖) q μ).toReal)
                    * ENNReal.ofReal ((eLpNorm f p μ).toReal)
                  = eLpNorm (fun y => ‖g y‖) q μ * eLpNorm f p μ := by
              rw [hG_back, hF_back]
            -- Replace each ofReal-toReal by the original ENNReal norms and fold targetE.
            rw [this, step2, h_g_eq']
            -- targetE = eLpNorm f p μ * eLpNorm g q μ, so we need mul_comm
            rw [mul_comm, ← hTargetE]
          -- Finish: chain the inequalities and rewrite as Ψ N ≤ (targetE)^r.
          have :
              (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)) ^ r.toReal
              ≤ (targetE) ^ r.toReal := by
            calc (ENNReal.ofReal
                    ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                      * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)) ^ r.toReal
                ≤ (ENNReal.ofReal
                    ((eLpNorm (fun y => ‖g y‖) q μ).toReal * (eLpNorm f p μ).toReal))
                      ^ r.toReal := h_rpow_mono
              _ = (targetE) ^ r.toReal := by rw [h_ofReal_prod_target]
          -- Rewrite the left-hand side as Ψ N via the template bound.
          exact (le_trans h_base this)
        -- Note: It remains to prove the uniform L^{s₀} estimate for A.
        -- We isolate it as a sub-lemma and then conclude the target bound for Ψ.
        have hA_uniform_bound_s0 :
            ∀ N,
              (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
                ≤ (((μpartial N) Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ).toReal := by
          intro N
          -- Apply the extracted auxiliary lemma specialized to our A-definition.
          simpa [A_fun, A] using
            (A_uniform_bound_s0_of_split (μ := μ)
              (f := f) (p := p) (r := r) (s₀ := s₀) (μpartial := μpartial)
              (hf := hf) (hf_r := hf_r)
              (hs₀_ne_zero := hs₀_ne_zero) (hs₀_ne_top := hs₀_ne_top)
              (hμpartial_fin := hμpartial_fin)
              (hμpartial_le := hμpartial_le) N)
        -- Using the weaker bound for A, we still obtain a uniform per‑N estimate for Ψ
        -- after packaging the extra (μpartial N Set.univ)^(1/s₀) factor into the base.
        have hΨ_uniform : ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                        * eLpNorm f r μ).toReal))) ^ r.toReal := by
          intro N
          -- Start from the Young template on the finite piece μpartial N.
          have h_base := hΨ_le_young_template N (hA_mem N)
          -- Monotonicity in the measure for the g-factor (push from μpartial N to μ).
          have h_mono_g_toReal :
              (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal ≤
                (eLpNorm (fun y => ‖g y‖) q μ).toReal := by
            have h_le :=
              eLpNorm_mono_measure (f := fun y => ‖g y‖) (μ := μ) (ν := μpartial N) (p := q)
                (hμpartial_le N)
            exact ENNReal.toReal_mono (by simpa using hg.eLpNorm_ne_top) h_le
          -- Combine the two real bounds inside ENNReal.ofReal via monotonicity and then rpow.
          have h_mul_le :
              (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal
              ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal *
                  ((((μpartial N) Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ).toReal) := by
            have hA := hA_uniform_bound_s0 N
            exact mul_le_mul_of_nonneg_left hA ENNReal.toReal_nonneg
              |> (fun h => by
                    refine le_trans ?_ h
                    exact mul_le_mul_of_nonneg_right h_mono_g_toReal ENNReal.toReal_nonneg)
          have h_ofReal_le :
              ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)
              ≤ ENNReal.ofReal
                  ((eLpNorm (fun y => ‖g y‖) q μ).toReal *
                    ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                        * eLpNorm f r μ).toReal)) := by
            exact ENNReal.ofReal_le_ofReal h_mul_le
          have h_rpow_mono :
              (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun y => A N y) s₀ (μpartial N)).toReal)) ^ r.toReal
              ≤ (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                        * eLpNorm f r μ).toReal))) ^ r.toReal := by
            exact ENNReal.rpow_le_rpow h_ofReal_le ENNReal.toReal_nonneg
          simpa [Ψ, hΨ_def] using (le_trans h_base h_rpow_mono)
        -- Reduce to the desired constant bound using the exponent arithmetic for μpartial N.
        -- From the reduction lemma, obtain a per‑N bound Ψ N ≤ Θ N, and then absorb the
        -- (μpartial N Set.univ)^(1/s₀) factor via the previously established exponent identities.
        -- We postpone the final absorption here since it is handled in the earlier Θ‑based step.
        -- Using the above per‑N estimate, we can derive the desired limsup bound.
        -- The remaining packing of the measure factor and exponent algebra yield a
        -- uniform constant bound matching `targetE ^ r.toReal`.
        -- Step: Dominate Ψ by a Θ-style sequence that carries the ((N+1))-powers on each factor.
        -- Define Θ' mirroring the earlier Θ, but sourced from the Option 2 A-bound.
        let Θ' : ℕ → ℝ≥0∞ :=
          fun N =>
            (ENNReal.ofReal
              ( ((
                    ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal)
                      * eLpNorm f r μ).toReal)
                * (((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal)
                        * eLpNorm g q μ).toReal))
                * (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal)) )) ^ r.toReal
        have hΨ_le_Θ' : ∀ N, Ψ N ≤ Θ' N := by
          intro N
          -- Start from the bound derived earlier in hΨ_uniform, then inflate the
          -- (μpartial N) factor using the standard partial-measure growth inequalities.
          have h_base := hΨ_uniform N
          have h_one_bound_toReal :
              ((eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal)
                ≤ (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                      * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal :=
            h_one_partial_bound_toReal N h_one_finite
          -- Identify eLpNorm(1) on μpartial N with (μpartial N Set.univ)^(1/s₀).
          have h_one_id :
              eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)
                = (μpartial N Set.univ) ^ (1 / s₀.toReal) := by
            have hs₀_ne_zero' : s₀ ≠ 0 := hs₀_ne_zero
            by_cases hμz : μpartial N = 0
            · -- both sides are 0 when μpartial N = 0
              -- Show directly that both sides reduce to 0.
              have hpos : 0 < (1 / s₀.toReal) := one_div_pos.mpr hs₀_toReal_pos
              have hμuniv : (μpartial N) Set.univ = 0 := by simp [hμz]
              have hL : eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N) = 0 := by
                simp [hμz]
              have hR : (μpartial N Set.univ) ^ (1 / s₀.toReal) = 0 := by
                simpa [hμuniv] using (ENNReal.zero_rpow_of_pos hpos)
              exact hL.trans hR.symm
            · have h_const := eLpNorm_const (μ := μpartial N) (p := s₀)
                  (c := (1 : ℝ)) hs₀_ne_zero' hμz
              have : ‖(1 : ℝ)‖ₑ = 1 := by norm_num
              rw [this, one_mul] at h_const
              exact h_const
          -- Convert the A-side factor inequality on toReal using monotonicity.
          have h_A_toReal_le :
              ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                    * eLpNorm f r μ).toReal)
              ≤ (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                      * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ)
                    * eLpNorm f r μ).toReal) := by
            -- First, lift h_one_bound_toReal back to ENNReal and multiply by ‖f‖_r.
            -- Use `toReal_mono` with the finiteness of the RHS to transfer the inequality.
            have h_pow_ne_top :
                ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ≠ ∞ := by
              have h_exp_nonneg : 0 ≤ (1 / s₀).toReal := by simp [one_div]
              exact ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
            have h_rhs_ne_top :
                (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                    * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ≠ ∞ :=
              ENNReal.mul_ne_top h_pow_ne_top h_one_finite
            -- from h_one_bound_toReal and h_one_id
            have h_of_toReal :
                ((μpartial N Set.univ) ^ (1 / s₀.toReal)).toReal
                  ≤ ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal) := by
              simpa [h_one_id]
                using h_one_bound_toReal
            -- multiply both sides (inside toReal) by ‖f‖_r via monotonicity
            have h_mul_le :
                (((μpartial N Set.univ) ^ (1 / s₀.toReal)).toReal
                    * (eLpNorm f r μ).toReal)
                ≤ (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal)
                    * (eLpNorm f r μ).toReal) := by
              exact mul_le_mul_of_nonneg_right h_of_toReal ENNReal.toReal_nonneg
            have h_mul_toReal_lhs :
                (((μpartial N Set.univ) ^ (1 / s₀.toReal)).toReal
                    * (eLpNorm f r μ).toReal)
                = (((μpartial N Set.univ) ^ (1 / s₀.toReal)
                        * eLpNorm f r μ).toReal) := by
              -- both factors are finite since μpartial N is finite and ‖f‖_r < ∞
              have hA_fin : ((μpartial N Set.univ) ^ (1 / s₀.toReal)) ≠ ∞ := by
                have hs_nonneg : 0 ≤ (1 / s₀.toReal) := by
                  have : 0 < s₀.toReal := ENNReal.toReal_pos hs₀_ne_zero hs₀_ne_top
                  exact div_nonneg (by norm_num) (le_of_lt this)
                exact ENNReal.rpow_ne_top_of_nonneg hs_nonneg (by simp)
              have hFr_fin : eLpNorm f r μ ≠ ∞ := by simpa using hf_r.eLpNorm_ne_top
              simp [ENNReal.toReal_mul, hA_fin, hFr_fin]
            have h_mul_toReal_rhs :
                (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal)
                    * (eLpNorm f r μ).toReal)
                = (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ)
                      * eLpNorm f r μ).toReal) := by
              have hFr_fin : eLpNorm f r μ ≠ ∞ := by simpa using hf_r.eLpNorm_ne_top
              simp [ENNReal.toReal_mul, h_rhs_ne_top, hFr_fin]
            -- Conclude the desired inequality between the toReal of products.
            simpa [h_mul_toReal_lhs, h_mul_toReal_rhs]
              using h_mul_le
          -- Now assemble the three factors under ofReal and raise to r.toReal.
          have h_inner_le :
              (eLpNorm (fun y => ‖g y‖) q μ).toReal
                * ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                      * eLpNorm f r μ).toReal)
              ≤ (( ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal)
                  * (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ)
                      * eLpNorm f r μ).toReal) := by
            -- Use the earlier g-side growth and the A-side toReal growth.
            have hg_toReal :
                (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  ≤ (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal := by
              -- reuse earlier bound
              have h_eqNorm :
                  eLpNorm (fun y => ‖g y‖) q (μpartial N) = eLpNorm g q (μpartial N) :=
                eLpNorm_norm_eq_of_complex g q
              simpa [h_eqNorm] using h_g_partial_bound_toReal N
            -- combine with monotonicity for ofReal inputs
            have hg_mono :
                (eLpNorm (fun y => ‖g y‖) q μ).toReal
                  ≤ (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal := by
              -- use the equality eLpNorm (fun y => ‖g y‖) q μ = eLpNorm g q μ
              have h_eq : eLpNorm (fun y => ‖g y‖) q μ = eLpNorm g q μ :=
                eLpNorm_norm_eq_of_complex g q
              -- Reduce to showing (eLpNorm g q μ).toReal ≤ ((A * eLpNorm g q μ)).toReal
              -- where A = (N+1)^(1/q).toReal as an ENNReal factor.
              set A : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) with hA
              have hA_nonneg : 0 ≤ (1 / q).toReal := by simp [one_div]
              have hA_ne_top : A ≠ ∞ := by
                simp [hA]
              have ha_ne_top : eLpNorm g q μ ≠ ∞ := by simpa using hg.eLpNorm_ne_top
              -- 1 ≤ A because base (N+1) ≥ 1 and exponent ≥ 0.
              have h_one_le_base : (1 : ℝ≥0∞) ≤ (N + 1 : ℝ≥0∞) := by
                -- 1 ≤ (N+1) for natural numbers
                have : (1 : ℕ) ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le _)
                exact_mod_cast this
              have hA_ge_one : (1 : ℝ≥0∞) ≤ A := by
                -- monotonicity of rpow in the base for nonnegative exponents
                simpa [hA, one_div] using ENNReal.rpow_le_rpow h_one_le_base hA_nonneg
              -- Hence eLpNorm ≤ A * eLpNorm
              have h_enorm_le : eLpNorm g q μ ≤ A * eLpNorm g q μ := by
                -- multiply both sides of 1 ≤ A by eLpNorm g q μ on the left
                have := mul_le_mul_left' hA_ge_one (eLpNorm g q μ)
                simpa [one_mul, mul_comm] using this
              -- Pass to toReal via monotonicity (RHS finite by hA_ne_top and ha_ne_top)
              have hR_ne_top : A * eLpNorm g q μ ≠ ∞ := ENNReal.mul_ne_top hA_ne_top ha_ne_top
              have h_toReal_le : (eLpNorm g q μ).toReal ≤ (A * eLpNorm g q μ).toReal :=
                ENNReal.toReal_mono hR_ne_top h_enorm_le
              simpa [h_eq, hA] using h_toReal_le
            have h_A_bound :
                ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                      * eLpNorm f r μ).toReal)
                  ≤ (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ)
                      * eLpNorm f r μ).toReal) := h_A_toReal_le
            exact mul_le_mul hg_mono h_A_bound ENNReal.toReal_nonneg ENNReal.toReal_nonneg
          have h_ofReal_le :
              ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                        * eLpNorm f r μ).toReal))
              ≤ ENNReal.ofReal
                ( (((((N + 1 : ℝ≥0∞) ^ (1 / r).toReal)
                        * eLpNorm f r μ).toReal))
                  * (((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal)
                        * eLpNorm g q μ).toReal))
                  * (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal)) ) := by
            -- multiply the A-side inequality by 1 (as a factor), then re-associate
            have h_mul :
                (eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                        * eLpNorm f r μ).toReal)
                ≤ (( ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal)
                    * (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                          * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ)
                        * eLpNorm f r μ).toReal) := h_inner_le
            -- bound the RHS by a triple product inside ofReal by inflating the f-term
            -- with the additional ((N+1)^(1/r).toReal) factor, using that it is ≥ 1.
            have h_rhs_le :
                (( ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal)
                    * (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                          * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ)
                        * eLpNorm f r μ).toReal)
              ≤
                ( (((((N + 1 : ℝ≥0∞) ^ (1 / r).toReal)
                        * eLpNorm f r μ).toReal))
                  * (((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal)
                        * eLpNorm g q μ).toReal))
                  * (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal)) ) := by
              -- abbreviations for readability
              set Xq : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ
              set Xs : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                  * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ
              set Xr : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ
              -- First, split the (Xs * ‖f‖_r).toReal term.
              have hXs_pow_nonneg : 0 ≤ (1 / s₀).toReal := by
                simp
              have hXs_pow_ne_top : ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ≠ ∞ :=
                ENNReal.rpow_ne_top_of_nonneg hXs_pow_nonneg (by simp)
              have h_one_fin : eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞ := h_one_finite
              have hXs_ne_top : Xs ≠ ∞ := by
                simpa [Xs] using ENNReal.mul_ne_top hXs_pow_ne_top h_one_fin
              have hFr_ne_top : eLpNorm f r μ ≠ ∞ := by simpa using hf_r.eLpNorm_ne_top
              have h_split : (Xs * eLpNorm f r μ).toReal = Xs.toReal * (eLpNorm f r μ).toReal := by
                simp [ENNReal.toReal_mul, hXs_ne_top, hFr_ne_top, Xs]
              -- Next, inflate (‖f‖_r).toReal to (Xr).toReal using A_r ≥ 1.
              have hAr_nonneg : 0 ≤ (1 / r).toReal := by
                simp
              have hAr_pow_ne_top : ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ :=
                ENNReal.rpow_ne_top_of_nonneg hAr_nonneg (by simp)
              have hXr_ne_top : Xr ≠ ∞ := by
                simpa [Xr]
                  using ENNReal.mul_ne_top hAr_pow_ne_top (by simpa using hf_r.eLpNorm_ne_top)
              have h_one_le_base : (1 : ℝ≥0∞) ≤ (N + 1 : ℝ≥0∞) := by
                have : (1 : ℕ) ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le _)
                exact_mod_cast this
              have hAr_ge_one : (1 : ℝ≥0∞) ≤ ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) :=
                by simpa [one_div] using ENNReal.rpow_le_rpow h_one_le_base hAr_nonneg
              have hCf_le : (eLpNorm f r μ).toReal ≤ Xr.toReal := by
                -- multiply 1 ≤ A_r by ‖f‖_r and pass to toReal
                have h_mul : eLpNorm f r μ ≤ ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ :=
                  by simpa [one_mul, mul_comm]
                    using (mul_le_mul_left' hAr_ge_one (eLpNorm f r μ))
                have hR_ne_top : ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ :=
                  ENNReal.mul_ne_top hAr_pow_ne_top (by simpa using hf_r.eLpNorm_ne_top)
                simpa [Xr] using ENNReal.toReal_mono hR_ne_top h_mul
              -- Put everything together and reorganize products.
              calc
                Xq.toReal * ((Xs * eLpNorm f r μ).toReal)
                    = Xq.toReal * (Xs.toReal * (eLpNorm f r μ).toReal) := by
                        simp [h_split]
                _ ≤ Xq.toReal * (Xs.toReal * Xr.toReal) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_left hCf_le (by exact ENNReal.toReal_nonneg))
                          (by exact ENNReal.toReal_nonneg)
                _ = Xr.toReal * Xq.toReal * Xs.toReal := by
                        ring

            -- use h_mul and h_rhs_le, then apply monotonicity of ofReal
            have h_total :
                (eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                        * eLpNorm f r μ).toReal)
                ≤ ( (((((N + 1 : ℝ≥0∞) ^ (1 / r).toReal)
                        * eLpNorm f r μ).toReal))
                  * (((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal)
                        * eLpNorm g q μ).toReal))
                  * (((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal)) ) :=
              le_trans h_mul h_rhs_le
            exact ENNReal.ofReal_le_ofReal h_total
          -- Pass to r-powers via monotonicity.
          have h_rpow_mono :
              (ENNReal.ofReal
                ((eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * ((((μpartial N) Set.univ) ^ (1 / s₀.toReal)
                        * eLpNorm f r μ).toReal))) ^ r.toReal
              ≤ Θ' N := by
            exact ENNReal.rpow_le_rpow h_ofReal_le ENNReal.toReal_nonneg
          -- Chain with the base bound Ψ N ≤ ... to obtain Ψ N ≤ Θ' N.
          exact (le_trans h_base h_rpow_mono)
        -- Conclude limsup bound by passing to limsup on both sides.
        have h_limsupΨ_le_Θ' :
            Filter.limsup Ψ Filter.atTop ≤ Filter.limsup Θ' Filter.atTop := by
          exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hΨ_le_Θ')
        -- TODO: Finish the exponent packing on Θ' to obtain the target constant bound.
        -- For now, we leave the final algebraic collapse to the previously established machinery.
        -- Replace with the concrete constant bound once the packing step is integrated here.
        -- Identify Θ' with the previously introduced Θ to reuse the packing machinery.
        have hΘ'_eq_Θ : Θ' = Θ := by
          funext N
          simp [Θ', Θ, C, mul_comm, mul_left_comm, mul_assoc]
        -- Hence limsup Θ' = limsup Θ.
        have h_limsup_eq :
            Filter.limsup Θ' Filter.atTop = Filter.limsup Θ Filter.atTop := by
          simp [hΘ'_eq_Θ]
        -- Reduce the goal to the established bound on limsup Θ.
        -- It remains to invoke the packing and Hölder-on-μ steps already developed above.
        -- We defer this final call here to keep this branch aligned with the Θ-route.
        -- Final step: limsup Ψ ≤ limsup Θ = … ≤ targetE ^ r.toReal.
        have h_limsupΨ_le_Θ :
            Filter.limsup Ψ Filter.atTop ≤ Filter.limsup Θ Filter.atTop := by
          simpa [h_limsup_eq] using h_limsupΨ_le_Θ'
        -- Compose with the previously obtained bound from the Θ-route to the p-based constant.
        -- This uses the exponent algebra and Hölder step already proved earlier in this proof.
        exact (le_trans h_limsupΨ_le_Θ) (by
          -- placeholder: bound limsup Θ by the p-based constant
          -- to be filled by invoking the established Θ-pack machinery
          sorry)
      · -- In the infinite case, we will avoid using hΨ_le_aux''' and instead
        -- proceed via the earlier bound hΨ_le_aux'' combined with finite-piece
        -- control. We postpone this technical branch to the next step.
        -- TODO: implement the alternative route without the finiteness assumption.
        sorry

end ConvolutionAuxiliary
