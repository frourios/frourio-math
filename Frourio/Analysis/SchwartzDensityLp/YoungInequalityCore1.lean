import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
import Frourio.Analysis.SchwartzDensityLp.FubiniSection
import Frourio.Analysis.SchwartzDensityLp.YoungInequalityCore0
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Measure.Haar.Basic

noncomputable section

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter

variable {G α : Type*}

section ConvolutionAuxiliary

variable {G : Type*}
variable [NormedAddCommGroup G] [MeasurableSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]
variable (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]

lemma lintegral_convolution_norm_bound
    (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (f g : G → ℂ) (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (h_kernel_int : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)) :
    ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal ∂ μ ≤
      (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal := by
  -- The key insight: by Young's inequality (or more specifically, the integral bound),
  -- for each x: ∫ y, ‖f (x - y)‖ * ‖g y‖ ≤ C (where C = eLpNorm f p μ * eLpNorm g q μ)
  -- Then raising to power r and integrating gives the result

  -- From the index relation, we can derive 1 ≤ r
  have h_inv_p_le_one : p⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa [one_div] using (ENNReal.inv_le_inv).2 hp
  have h_inv_q_le_one : q⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa [one_div] using (ENNReal.inv_le_inv).2 hq
  have h_sum_le_two : p⁻¹ + q⁻¹ ≤ (1 : ℝ≥0∞) + 1 :=
    add_le_add h_inv_p_le_one h_inv_q_le_one
  have h_eq : p⁻¹ + q⁻¹ = (1 : ℝ≥0∞) + r⁻¹ := by
    simpa [one_div, add_comm, add_left_comm, add_assoc] using hpqr
  have h_aux : (1 : ℝ≥0∞) + r⁻¹ ≤ (1 : ℝ≥0∞) + 1 := by
    simpa [h_eq] using h_sum_le_two
  have h_inv_r_le_one : r⁻¹ ≤ (1 : ℝ≥0∞) :=
    ENNReal.le_of_add_le_add_left (by simp) h_aux
  have hr : 1 ≤ r :=
    (ENNReal.inv_le_inv).1 <| by
      simpa [one_div] using h_inv_r_le_one

  have hr_ne_zero : r ≠ 0 := by
    have : (0 : ℝ≥0∞) < r := lt_of_lt_of_le (by simp) hr
    exact ne_of_gt this

  -- Record the fibrewise integrability of the norm kernel; this will be used
  -- both to justify measurability statements and to ensure that the inner
  -- integral is finite for μ-a.e. x.
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

  -- Exhaust the s-finite measure by finite pieces and record the basic properties
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
  have hg_partial : ∀ N, MemLp g q (μpartial N) := by
    intro N
    refine hg.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N

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
    classical
    rcases hx with ⟨hxμ, hx_partial⟩
    set hxFun : G → ℝ := fun y => ‖f (x - y)‖ * ‖g y‖ with hxFun_def
    have hxμ_int : Integrable hxFun μ := by
      simpa [hxFun_def] using hxμ
    have hx_partial_int :
        ∀ N, Integrable hxFun (μpartial N) := by
      intro N
      have := hx_partial N
      simpa [hxFun_def] using this
    have hx_piece_int :
        ∀ n, Integrable hxFun (μn n) := by
      intro n
      refine hxμ_int.of_measure_le_smul (μ := μ) (μ' := μn n)
          (c := (1 : ℝ≥0∞)) ?_ ?_
      · simp
      · simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n
    have hx_Hpartial_def :
        ∀ N, Hpartial N x = ∫ y, hxFun y ∂ μpartial N := by
      intro N
      simp [Hpartial, hxFun_def]
    have hx_H_def : H x = ∫ y, hxFun y ∂ μ := by
      simp [H, hxFun_def]
    have hx_Hpartial_succ :
        ∀ N,
          Hpartial (N + 1) x =
            Hpartial N x + ∫ y, hxFun y ∂ μn (N + 1) := by
      intro N
      have hx_add :=
        MeasureTheory.integral_add_measure
          (μ := μpartial N) (ν := μn (N + 1))
          (f := hxFun)
          (hx_partial_int N)
          (hx_piece_int (N + 1))
      simpa [hx_Hpartial_def, hxFun_def, hμpartial_succ,
        Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc]
        using hx_add
    have hx_Hpartial_sum :
        ∀ N,
          Hpartial N x =
            ∑ k ∈ Finset.range (N + 1),
              ∫ y, hxFun y ∂ μn k := by
      intro N
      induction' N with N hN
      · simp [hx_Hpartial_def, hxFun_def, μpartial, hμpartial_zero,
          Finset.range_one]
      · have hx_step := hx_Hpartial_succ N
        calc
          Hpartial (N + 1) x
              = Hpartial N x + ∫ y, hxFun y ∂ μn (N + 1) := hx_step
          _ = (∑ k ∈ Finset.range (N + 1), ∫ y, hxFun y ∂ μn k)
                + ∫ y, hxFun y ∂ μn (N + 1) := by simp [hN]
          _ = ∑ k ∈ Finset.range (N + 1 + 1), ∫ y, hxFun y ∂ μn k := by
                simp [Finset.sum_range_succ, Nat.succ_eq_add_one, add_comm,
                  add_left_comm, add_assoc]
    have hx_hasSum :
        HasSum (fun n => ∫ y, hxFun y ∂ μn n)
          (∫ y, hxFun y ∂ μ) := by
      have hx_int_sum : Integrable hxFun (Measure.sum μn) := by
        simpa [hxFun_def, hμ_sum] using hxμ_int
      have hx_hasSum_aux :=
        MeasureTheory.hasSum_integral_measure
          (μ := μn) (f := hxFun) (hf := hx_int_sum)
      simpa [hxFun_def, hμ_sum]
        using hx_hasSum_aux
    have hx_tendsto_range :
        Tendsto (fun N => ∑ k ∈ Finset.range N, ∫ y, hxFun y ∂ μn k)
          atTop (𝓝 (∫ y, hxFun y ∂ μ)) :=
      hx_hasSum.tendsto_sum_nat
    have hx_tendsto :
        Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
            ∫ y, hxFun y ∂ μn k) atTop (𝓝 (∫ y, hxFun y ∂ μ)) :=
      hx_tendsto_range.comp (tendsto_add_atTop_nat 1)
    have hx_eventually :
        (fun N =>
            ∑ k ∈ Finset.range (N + 1),
              ∫ y, hxFun y ∂ μn k)
          =ᶠ[Filter.atTop]
            fun N => Hpartial N x :=
      Filter.Eventually.of_forall fun N => (hx_Hpartial_sum N).symm
    have hx_tendsto_Hpartial :
        Tendsto (fun N => Hpartial N x) atTop
          (𝓝 (∫ y, hxFun y ∂ μ)) :=
      hx_tendsto.congr' hx_eventually
    simpa [hx_H_def] using hx_tendsto_Hpartial
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
  have hr_toReal_pos : 0 < r.toReal :=
    ENNReal.toReal_pos hr_ne_zero hr_ne_top
  have h_H_lintegral_repr :
      (eLpNorm H r μ) ^ r.toReal
        = ∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ := by
    have h_nonzero : r.toReal ≠ 0 := ne_of_gt hr_toReal_pos
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
          (fun q : G × G => ‖f (q.1 - q.2) * g q.2‖) (μ.prod (μpartial N)) := by
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
  let g : G → ℝ≥0∞ := fun x => (ENNReal.ofReal (H x)) ^ r.toReal
  have h_lintegral_Hpartial_partial :
      ∀ N,
        ∫⁻ x, g x ∂ μpartial N =
          ∑ k ∈ Finset.range (N + 1),
            ∫⁻ x, g x ∂ μn k := by
    intro N
    classical
    simp [g, μpartial]
  have h_lintegral_Hpartial_sum :
      (∑' k, ∫⁻ x, g x ∂ μn k) = ∫⁻ x, g x ∂ μ := by
    classical
    simpa [g, hμ_sum]
      using
        (MeasureTheory.lintegral_sum_measure
          (μ := μn)
          (f := fun x : G => g x)).symm
  have h_lintegral_Hpartial_mono :
      Monotone (fun N => ∫⁻ x, g x ∂ μpartial N) := by
    intro N M hNM
    exact lintegral_mono' (hμpartial_mono hNM) fun _ => le_rfl
  have h_lintegral_Hpartial_tendsto :
      Tendsto (fun N => ∫⁻ x, g x ∂ μpartial N) atTop
        (𝓝 (∫⁻ x, g x ∂ μ)) := by
    classical
    have h_series_tendsto :
        Tendsto
          (fun N =>
            ∑ k ∈ Finset.range (N + 1),
              ∫⁻ x, g x ∂ μn k)
          atTop
          (𝓝 (∑' k, ∫⁻ x, g x ∂ μn k)) := by
      exact
        (ENNReal.tendsto_nat_tsum
          (f := fun k => ∫⁻ x, g x ∂ μn k)).comp
          (tendsto_add_atTop_nat 1)
    have h_eval :
        (fun N => ∫⁻ x, g x ∂ μpartial N)
          = fun N =>
              ∑ k ∈ Finset.range (N + 1),
                ∫⁻ x, g x ∂ μn k := by
      funext N
      exact h_lintegral_Hpartial_partial N
    have h_eval' :
        (∑' k, ∫⁻ x, g x ∂ μn k)
          = ∫⁻ x, g x ∂ μ :=
      h_lintegral_Hpartial_sum
    simpa [h_eval, h_eval'] using h_series_tendsto
  sorry

lemma convolution_memLp_of_memLp
    (f g : G → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hf_r : MemLp f r μ) (hg : MemLp g q μ)
    (h_kernel_int : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)) :
    MemLp (fun x => ∫ y, f (x - y) * g y ∂μ) r μ := by
  classical
  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
  have hμn_fin : ∀ n, IsFiniteMeasure (μn n) := fun n => inferInstance
  have hμ_sum : Measure.sum μn = μ := MeasureTheory.sum_sfiniteSeq μ
  let μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k
  have hμpartial_succ : ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1) := by
    intro N
    classical
    simp [μpartial, Nat.succ_eq_add_one, Finset.range_succ, add_comm, add_left_comm, add_assoc]
  have hμpartial_def :
      ∀ N, μpartial N = ∑ k ∈ Finset.range (N + 1), μn k := fun _ => rfl
  have hμpartial_zero : μpartial 0 = μn 0 := by
    classical
    simp [μpartial]
  have hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N) := by
    intro N
    classical
    refine Nat.rec ?base ?step N
    · simpa [μpartial] using hμn_fin 0
    · intro k hk
      have hk_add : IsFiniteMeasure (μpartial k + μn (k + 1)) := by infer_instance
      simpa [hμpartial_succ, Nat.succ_eq_add_one] using hk_add
  have hμpartial_le_succ : ∀ N, μpartial N ≤ μpartial (N + 1) := by
    intro N s
    classical
    have hnonneg : 0 ≤ μn (N + 1) s := bot_le
    simp [hμpartial_succ, Nat.succ_eq_add_one, Measure.add_apply]
  have hμpartial_mono : Monotone μpartial :=
    monotone_nat_of_le_succ hμpartial_le_succ
  have hμpartial_le_smul : ∀ N, μpartial N ≤ ((N + 1 : ℝ≥0∞) • μ) := by
    intro N
    simpa [μpartial] using (sfiniteSeq_partial_le_smul (μ := μ) N)
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
  have hg_partial : ∀ N, MemLp g q (μpartial N) := by
    intro N
    refine hg.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have hμpartial_ac : ∀ N, μpartial N ≪ μ := by
    intro N
    exact Measure.absolutelyContinuous_of_le_smul (hμpartial_le_smul N)
  have hμpartial_tendsto :
      ∀ ⦃s : Set G⦄, MeasurableSet s →
        Tendsto (fun N => μpartial N s) atTop (𝓝 (μ s)) := by
    exact sfiniteSeq_partial_tendsto (μ := μ)
  have h_inv_p_le_one : p⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv).2 hp
  have h_inv_q_le_one : q⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv).2 hq
  have h_inv_r_le_one : r⁻¹ ≤ (1 : ℝ≥0∞) := by
    have h_sum_le_two : p⁻¹ + q⁻¹ ≤ (1 : ℝ≥0∞) + 1 :=
      add_le_add h_inv_p_le_one h_inv_q_le_one
    have h_eq : p⁻¹ + q⁻¹ = (1 : ℝ≥0∞) + r⁻¹ := by
      simpa [one_div, add_comm, add_left_comm, add_assoc] using hpqr
    have h_aux : (1 : ℝ≥0∞) + r⁻¹ ≤ (1 : ℝ≥0∞) + 1 := by
      simpa [h_eq] using h_sum_le_two
    exact ENNReal.le_of_add_le_add_left (by simp) h_aux
  have hr : 1 ≤ r :=
    (ENNReal.inv_le_inv).1 (by simpa using h_inv_r_le_one)
  have h_kernel_fiber_int :
      ∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ := by
    have h := Integrable.prod_right_ae (μ := μ) (ν := μ) h_kernel_int
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have h_kernel_fiber_int_left :
      ∀ᵐ y ∂μ, Integrable (fun x => f (x - y) * g y) μ := by
    have h := Integrable.prod_left_ae (μ := μ) (ν := μ) h_kernel_int
    refine h.mono ?_
    intro y hy
    simpa [sub_eq_add_neg] using hy
  have h_kernel_meas :
      AEStronglyMeasurable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) :=
    h_kernel_int.aestronglyMeasurable
  set conv : G → ℂ := fun x => ∫ y, f (x - y) * g y ∂μ
  have h_conv_meas : AEStronglyMeasurable conv μ := by
    simpa [conv] using
      aestronglyMeasurable_convolution (μ := μ)
        (f := f) (g := g) h_kernel_int h_kernel_fiber_int
  have hf_n : ∀ n, MemLp f p (μn n) := fun n =>
    hf.of_measure_le_smul (μ' := μn n) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n)
  have hg_n : ∀ n, MemLp g q (μn n) := fun n =>
    hg.of_measure_le_smul (μ' := μn n) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n)
  have hμpartial_tendsto_univ :
      Tendsto (fun N => μpartial N Set.univ) atTop (𝓝 (μ Set.univ)) :=
    hμpartial_tendsto MeasurableSet.univ
  set convPartial : ℕ → G → ℂ := fun N x => ∫ y, f (x - y) * g y ∂μpartial N
  have hconvPartial_tendsto_measure := hμpartial_tendsto_univ
  have h_prod_le :
      ∀ N,
        (μpartial N).prod (μpartial N) ≤
          (((N + 1 : ℝ≥0∞) * (N + 1 : ℝ≥0∞)) • (μ.prod μ)) := by
    intro N
    simpa [μpartial, μn]
      using (sfiniteSeq_partial_prod_le_smul (μ := μ) N)
  have h_kernel_int_partial :
      ∀ N,
        Integrable (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)) := by
    intro N
    classical
    have h_const_ne_top :
        ((N + 1 : ℝ≥0∞) * (N + 1 : ℝ≥0∞)) ≠ ∞ := by
      simpa using ENNReal.mul_ne_top (by simp) (by simp)
    refine
      Integrable.of_measure_le_smul
        (μ := μ.prod μ)
        (μ' := (μpartial N).prod (μpartial N))
        (f := fun q : G × G => f (q.1 - q.2) * g q.2)
        h_const_ne_top (h_prod_le N) ?_
    simpa using h_kernel_int
  have hμpartial_prod_ac :
      ∀ N,
        ((μpartial N).prod (μpartial N)) ≪ (μ.prod μ) := by
    intro N
    refine
      (Measure.absolutelyContinuous_of_le_smul
        (μ := μ.prod μ)
        (μ' := (μpartial N).prod (μpartial N))
        (c := ((N + 1 : ℝ≥0∞) * (N + 1 : ℝ≥0∞))) ?_)
    simpa using h_prod_le N
  have h_kernel_meas_partial :
      ∀ N,
        AEStronglyMeasurable
          (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)) := by
    intro N
    refine
      MeasureTheory.AEStronglyMeasurable.mono_ac
        (μ := μ.prod μ)
        (ν := (μpartial N).prod (μpartial N))
        (f := fun q : G × G => f (q.1 - q.2) * g q.2)
        (h := hμpartial_prod_ac N)
        h_kernel_meas
  refine ⟨h_conv_meas, ?_⟩
  have h_kernel_fiber_int_partial :
      ∀ N, ∀ᵐ x ∂ μpartial N, Integrable (fun y => f (x - y) * g y) (μpartial N) := by
    intro N
    have h :=
      Integrable.prod_right_ae (μ := μpartial N) (ν := μpartial N)
        (h_kernel_int_partial N)
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have h_convPartial_meas :
      ∀ N, AEStronglyMeasurable (convPartial N) (μpartial N) := by
    intro N
    have :=
      aestronglyMeasurable_convolution (μ := μpartial N)
        (f := f) (g := g) (h_kernel := h_kernel_int_partial N)
        (h_fiber := h_kernel_fiber_int_partial N)
    simpa [convPartial] using this
  have h_translate_norm_bound :
      ∀ N y,
        eLpNorm (fun x => f (x - y)) r (μpartial N) ≤
          ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ := by
    intro N y
    classical
    exact
      sfiniteSeq_partial_translate_norm_bound
        (μ := μ) (r := r) (f := f)
        (μpartial := μpartial)
        (hf := hf_r)
        (h_le := hμpartial_le_smul) N y
  have h_translate_norm_bound_toReal :
      ∀ N y,
        (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ≤
          ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal := by
    intro N y
    have h_bound := h_translate_norm_bound N y
    have h_pow_ne_top :
        ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ := by
      have h_exp_nonneg : 0 ≤ (1 / r).toReal := by
        simp [one_div]
      exact ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
    have h_const_ne_top :
        ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ :=
      ENNReal.mul_ne_top h_pow_ne_top hf_r.eLpNorm_ne_top
    exact ENNReal.toReal_mono h_const_ne_top h_bound
  have hg_partial_one : ∀ N, MemLp g 1 (μpartial N) := by
    intro N
    exact (hg_partial N).mono_exponent (p := (1 : ℝ≥0∞)) (q := q) hq
  have hg_partial_int : ∀ N, Integrable g (μpartial N) := by
    intro N
    exact (memLp_one_iff_integrable).1 (hg_partial_one N)
  have h_kernel_fiber_mem_partial :
      ∀ N, ∀ᵐ y ∂ μ, MemLp (fun x => f (x - y) * g y) r (μpartial N) := by
    intro N
    have h :=
      convolution_kernel_fiber_memLp_of_memLp (μ := μ)
        (p := r) (q := q) hf_r hg
    refine h.mono ?_
    intro y hy
    refine hy.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have h_kernel_fiber_int_partial' :
      ∀ N, ∀ᵐ y ∂ μ,
          Integrable (fun x => f (x - y) * g y) (μpartial N) := by
    intro N
    have h := h_kernel_fiber_int_left
    refine h.mono ?_
    intro y hy
    refine hy.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have h_kernel_fiber_mem_partial_ae :
      ∀ N, ∀ᵐ y ∂ μpartial N, MemLp (fun x => f (x - y) * g y) r (μpartial N) := by
    intro N
    have h_zero :=
      (ae_iff).1 (h_kernel_fiber_mem_partial N)
    have h_zero' :=
      (hμpartial_ac N) h_zero
    exact (ae_iff).2 <| by simpa using h_zero'
  have h_kernel_fiber_int_partial :
      ∀ N, ∀ᵐ y ∂ μpartial N,
          Integrable (fun x => f (x - y) * g y) (μpartial N) := by
    intro N
    have h_zero :=
      (ae_iff).1 (h_kernel_fiber_int_partial' N)
    have h_zero' :=
      (hμpartial_ac N) h_zero
    exact (ae_iff).2 <| by simpa using h_zero'
  have h_norm_partial :=
    sfiniteSeq_partial_integrable_norm_mul
      (μ := μ) (hr := hr) (hr_ne_top := hr_ne_top)
      (f := f) (g := g) (μpartial := μpartial)
      (hf := hf_r)
      (hg_partial_int := hg_partial_int)
      (hμpartial_fin := hμpartial_fin)
      (hμpartial_prod_ac := hμpartial_prod_ac)
      (h_translate_norm_bound_toReal := h_translate_norm_bound_toReal)
  have h_norm_partial_le :=
    sfiniteSeq_partial_integral_norm_mul_le
      (μ := μ) (r := r) (f := f) (g := g) (μpartial := μpartial)
      (hg_partial_int := hg_partial_int)
      (h_norm_partial := h_norm_partial)
      (h_translate_norm_bound_toReal := h_translate_norm_bound_toReal)
  have h_convPartial_def :
      ∀ N, convPartial N = fun x => ∫ y, f (x - y) * g y ∂ μpartial N := by
    intro N
    rfl
  have h_minkowski_partial :=
    convPartial_minkowski_bound
      (μpartial := μpartial) (f := f) (g := g) (r := r)
      (convPartial := convPartial)
      (h_convPartial := h_convPartial_def)
      (hr := hr) (hr_ne_top := hr_ne_top)
      (hμpartial_fin := hμpartial_fin)
      (h_kernel_meas_partial := h_kernel_meas_partial)
      (h_kernel_int_partial := h_kernel_int_partial)
      (h_kernel_fiber_int_partial := h_kernel_fiber_int_partial)
      (h_kernel_fiber_mem_partial := h_kernel_fiber_mem_partial_ae)
      (h_norm_partial := h_norm_partial)
  have h_convPartial_bound :=
    convPartial_bound
      (μ := μ)
      (μpartial := μpartial)
      (f := f)
      (g := g)
      (r := r)
      (convPartial := convPartial)
      (h_minkowski_partial := h_minkowski_partial)
      (h_norm_partial_le := h_norm_partial_le)
  have h_convPartial_mem :
      ∀ N, MemLp (convPartial N) r (μpartial N) := by
    intro N
    classical
    refine ⟨h_convPartial_meas N, ?_⟩
    have h_bound := h_convPartial_bound N
    have h_lt_top :
        ENNReal.ofReal
          ((((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal) *
            ∫ y, ‖g y‖ ∂ μpartial N) < ∞ := by
      simp
    exact lt_of_le_of_lt h_bound h_lt_top
  set convPiece : ℕ → G → ℂ := fun n x => ∫ y, f (x - y) * g y ∂ μn n
  have h_kernel_fiber_int_mu :
      ∀ᵐ x ∂ μ, Integrable (fun y => f (x - y) * g y) μ :=
    h_kernel_fiber_int
  have h_kernel_fiber_int_partial_measure :
      ∀ N, ∀ᵐ x ∂ μ, Integrable (fun y => f (x - y) * g y) (μpartial N) := by
    intro N
    have h := h_kernel_fiber_int_mu
    refine h.mono ?_
    intro x hx
    refine hx.of_measure_le_smul (μ := μ) (μ' := μpartial N)
        (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have h_kernel_fiber_int_piece :
      ∀ n, ∀ᵐ x ∂ μ, Integrable (fun y => f (x - y) * g y) (μn n) := by
    intro n
    have h := h_kernel_fiber_int_mu
    refine h.mono ?_
    intro x hx
    refine hx.of_measure_le_smul (μ := μ) (μ' := μn n) (c := (1 : ℝ≥0∞)) ?_ ?_
    · simp
    · simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n
  have h_convPiece_def :
      ∀ n, convPiece n = fun x => ∫ y, f (x - y) * g y ∂ μn n := by
    intro n
    rfl
  have h_convPartial_sum :=
    convPartial_sum_eq
      (μ := μ)
      (μpartial := μpartial)
      (μn := μn)
      (f := f)
      (g := g)
      (convPartial := convPartial)
      (convPiece := convPiece)
      (h_convPartial := h_convPartial_def)
      (h_convPiece := h_convPiece_def)
      (hμpartial_zero := hμpartial_zero)
      (hμpartial_succ := hμpartial_succ)
      (h_kernel_fiber_int_partial_measure := h_kernel_fiber_int_partial_measure)
      (h_kernel_fiber_int_piece := h_kernel_fiber_int_piece)
  have h_convPartial_partialSum :
      ∀ N,
        convPartial N
          =ᵐ[μ]
            fun x => ∑ k ∈ Finset.range (N + 1), convPiece k x :=
    h_convPartial_sum
  have hμn_le : ∀ n, μn n ≤ μ := fun n =>
    by simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n
  have hμn_prod_le : ∀ n, (μn n).prod (μn n) ≤ μ.prod μ := by
    intro n
    simpa [μn] using sfiniteSeq_prod_le (μ := μ) n
  have hμn_ac : ∀ n, μn n ≪ μ := by
    intro n
    exact Measure.absolutelyContinuous_of_le_smul
      (μ := μ)
      (μ' := μn n)
      (c := (1 : ℝ≥0∞))
      (by simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n)
  have hμn_prod_ac :
      ∀ n, (μn n).prod (μn n) ≪ μ.prod μ := by
    intro n
    exact Measure.absolutelyContinuous_of_le_smul
      (μ := μ.prod μ)
      (μ' := (μn n).prod (μn n))
      (c := (1 : ℝ≥0∞))
      (by simpa [one_smul] using hμn_prod_le n)
  have h_kernel_int_piece :
      ∀ n,
        Integrable (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μn n).prod (μn n)) := by
    intro n
    classical
    refine Integrable.of_measure_le_smul
        (μ := μ.prod μ)
        (μ' := (μn n).prod (μn n))
        (f := fun q : G × G => f (q.1 - q.2) * g q.2)
        (c := (1 : ℝ≥0∞))
        (by simp)
        (by simpa [one_smul] using hμn_prod_le n)
        ?_
    simpa using h_kernel_int
  have h_kernel_meas_piece :
      ∀ n,
        AEStronglyMeasurable
          (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μn n).prod (μn n)) := by
    intro n
    refine
      MeasureTheory.AEStronglyMeasurable.mono_ac
        (μ := μ.prod μ)
        (ν := (μn n).prod (μn n))
        (f := fun q : G × G => f (q.1 - q.2) * g q.2)
        (h := hμn_prod_ac n)
        h_kernel_meas
  have h_kernel_fiber_int_piece :
      ∀ n, ∀ᵐ x ∂ μn n,
          Integrable (fun y => f (x - y) * g y) (μn n) := by
    intro n
    have h :=
      Integrable.prod_right_ae (μ := μn n) (ν := μn n)
        (h_kernel_int_piece n)
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have h_kernel_fiber_int_piece_left :
      ∀ n, ∀ᵐ y ∂ μn n,
          Integrable (fun x => f (x - y) * g y) (μn n) := by
    intro n
    have h :=
      Integrable.prod_left_ae (μ := μn n) (ν := μn n)
        (h_kernel_int_piece n)
    refine h.mono ?_
    intro y hy
    simpa [sub_eq_add_neg] using hy
  have h_convPiece_meas_partial :
      ∀ n, AEStronglyMeasurable (convPiece n) (μn n) := by
    intro n
    have :=
      aestronglyMeasurable_convolution (μ := μn n)
        (f := f) (g := g)
        (h_kernel := h_kernel_int_piece n)
        (h_fiber := h_kernel_fiber_int_piece n)
    simpa [convPiece, sub_eq_add_neg] using this
  have hg_piece : ∀ n, MemLp g q (μn n) := by
    intro n
    refine hg.of_measure_le_smul (μ' := μn n) (c := (1 : ℝ≥0∞)) ?_ ?_
    · simp
    · simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n
  have hg_piece_one : ∀ n, MemLp g 1 (μn n) := by
    intro n
    exact (hg_piece n).mono_exponent (p := (1 : ℝ≥0∞)) (q := q) hq
  have hg_piece_int : ∀ n, Integrable g (μn n) := by
    intro n
    exact (memLp_one_iff_integrable).1 (hg_piece_one n)
  have h_translate_norm_bound_piece :
      ∀ n y,
        eLpNorm (fun x => f (x - y)) r (μn n) ≤ eLpNorm f r μ := by
    intro n y
    classical
    have h_le :=
      eLpNorm_mono_measure
        (f := fun x => f (x - y))
        (μ := μ)
        (ν := μn n)
        (p := r)
        (hμn_le n)
    have h_translate :=
      eLpNorm_comp_add_right
        (μ := μ) (f := f) (p := r) (y := -y) hf_r.aestronglyMeasurable
    have h_translate' :
        eLpNorm (fun x => f (x - y)) r μ = eLpNorm f r μ := by
      simpa [sub_eq_add_neg] using h_translate
    simpa using h_le.trans (le_of_eq h_translate')
  have h_translate_norm_bound_toReal_piece :
      ∀ n y,
        (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ≤
          (eLpNorm f r μ).toReal := by
    intro n y
    have h_bound := h_translate_norm_bound_piece n y
    have h_ne_top : eLpNorm f r μ ≠ ∞ := hf_r.eLpNorm_ne_top
    exact ENNReal.toReal_mono h_ne_top h_bound
  have h_kernel_fiber_mem_piece :
      ∀ n, ∀ᵐ y ∂ μn n,
          MemLp (fun x => f (x - y) * g y) r (μn n) := by
    intro n
    have h_aux :=
      convolution_kernel_fiber_memLp_of_memLp (μ := μ)
        (p := r) (q := q) hf_r hg
    have h_aux' :
        ∀ᵐ y ∂ μ, MemLp (fun x => f (x - y) * g y) r (μn n) :=
      h_aux.mono fun y hy =>
        hy.of_measure_le_smul (μ := μ) (μ' := μn n) (c := (1 : ℝ≥0∞))
          (by simp)
          (by
            simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n)
    have h_zero := (ae_iff).1 h_aux'
    have h_zero' := (hμn_ac n) h_zero
    exact (ae_iff).2 <| by simpa using h_zero'
  have hf_r_n : ∀ n, MemLp f r (μn n) := fun n =>
    hf_r.of_measure_le_smul (μ := μ) (μ' := μn n) (c := (1 : ℝ≥0∞))
      (by simp)
      (by
        simpa [μn, one_smul] using MeasureTheory.sfiniteSeq_le (μ := μ) n)
  have h_norm_piece :=
    sfiniteSeq_piece_integrable_norm_mul
      (μ := μ) (r := r)
      (hr := hr) (hr_ne_top := hr_ne_top)
      (f := f) (g := g) (μn := μn)
      (hf_r := hf_r)
      (hg_piece_int := hg_piece_int)
      (hμn_fin := hμn_fin)
      (hμn_prod_ac := hμn_prod_ac)
      (h_translate_norm_bound_toReal_piece := h_translate_norm_bound_toReal_piece)
  have h_convPiece_def :
      ∀ n, convPiece n = fun x => ∫ y, f (x - y) * g y ∂ μn n := by
    intro n
    rfl
  have h_pointwise_piece :
      ∀ n,
        (fun y =>
            (eLpNorm (fun x => f (x - y) * g y) r (μn n)).toReal)
          =ᵐ[μn n]
          fun y =>
            ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μn n)).toReal := by
    intro n
    refine Filter.Eventually.of_forall ?_
    intro y
    have h_scaling :
        eLpNorm (fun x => f (x - y) * g y) r (μn n) =
          ENNReal.ofReal ‖g y‖ *
            eLpNorm (fun x => f (x - y)) r (μn n) := by
      have h_smul :
          (fun x : G => f (x - y) * g y) =
            fun x : G => (g y) • f (x - y) := by
        funext x
        simp [mul_comm, smul_eq_mul, sub_eq_add_neg]
      simpa [h_smul] using
        eLpNorm_const_smul (μ := μn n) (p := r)
          (c := g y) (f := fun x => f (x - y))
    have h_toReal := congrArg ENNReal.toReal h_scaling
    have h_nonneg : 0 ≤ ‖g y‖ := norm_nonneg _
    simpa [ENNReal.toReal_ofReal_mul, h_nonneg]
      using h_toReal
  have h_norm_piece_pointwise :
      ∀ n,
        Integrable
          (fun y =>
            (eLpNorm (fun x => f (x - y) * g y) r (μn n)).toReal)
          (μn n) := by
    intro n
    refine (h_norm_piece n).congr ?_
    simpa using (h_pointwise_piece n).symm
  have h_minkowski_piece :=
    sfiniteSeq_piece_minkowski_bound
      (μ := μ) (r := r)
      (hr := hr) (hr_ne_top := hr_ne_top)
      (f := f) (g := g) (μn := μn)
      (convPiece := convPiece)
      (hμn_fin := hμn_fin)
      (h_kernel_meas_piece := h_kernel_meas_piece)
      (h_kernel_int_piece := h_kernel_int_piece)
      (h_kernel_fiber_int_piece_left := h_kernel_fiber_int_piece_left)
      (h_kernel_fiber_mem_piece := h_kernel_fiber_mem_piece)
      (h_norm_piece := h_norm_piece_pointwise)
      (h_pointwise := h_pointwise_piece)
      (h_convPiece_def := h_convPiece_def)
  have h_convPiece_mem_piece :
      ∀ n, MemLp (convPiece n) r (μn n) := by
    intro n
    classical
    haveI := hμn_fin n
    have h_bound := h_minkowski_piece n
    have h_rhs_lt_top :
        ENNReal.ofReal
            (∫ y, ‖g y‖ *
                (eLpNorm (fun x => f (x - y)) r (μn n)).toReal ∂ μn n) < ∞ := by
      simp
    exact ⟨h_convPiece_meas_partial n, lt_of_le_of_lt h_bound h_rhs_lt_top⟩
  have h_convPartial_partialSum' :
      ∀ N,
        convPartial N
          =ᵐ[μpartial N]
            fun x => ∑ k ∈ Finset.range (N + 1), convPiece k x := by
    intro N
    have h := h_convPartial_partialSum N
    exact (hμpartial_ac N) h
  have h_convPartial_mem_sum :
      ∀ N, MemLp (fun x => ∑ k ∈ Finset.range (N + 1), convPiece k x) r (μpartial N) :=
    by
    intro N
    classical
    obtain ⟨h_meas, h_lt_top⟩ := h_convPartial_mem N
    have h_ae :
        (fun x => ∑ k ∈ Finset.range (N + 1), convPiece k x) =ᵐ[μpartial N]
          convPartial N := (h_convPartial_partialSum' N).symm
    refine ⟨h_meas.congr h_ae.symm, ?_⟩
    have h_eLp :=
      eLpNorm_congr_ae (μ := μpartial N) (p := r) h_ae
    simpa [h_eLp.symm] using h_lt_top
  have h_integral_norm_partial :=
    sfiniteSeq_partial_integral_norm
      (g := g)
      (μpartial := μpartial)
      (μn := μn)
      (hμpartial_zero := hμpartial_zero)
      (hμpartial_succ := hμpartial_succ)
      (hg_partial_int := hg_partial_int)
      (hg_piece_int := hg_piece_int)
  have h_convPartial_bound_sum :
      ∀ N,
        eLpNorm (convPartial N) r (μpartial N) ≤
          ENNReal.ofReal
            ((((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal) *
              ∑ k ∈ Finset.range (N + 1), ∫ y, ‖g y‖ ∂ μn k) := by
    intro N
    classical
    simpa [h_integral_norm_partial N, mul_comm, mul_left_comm, mul_assoc]
      using h_convPartial_bound N
  have hμpartial_le :=
    sfiniteSeq_partial_le_measure
      (μ := μ)
      (μn := μn)
      (μpartial := μpartial)
      (hμ_sum := hμ_sum)
      (hμpartial_def := hμpartial_def)
  have h_lintegral_norm_le :
      ∀ N,
        ∫⁻ y, ‖g y‖ₑ ∂ μpartial N ≤ ∫⁻ y, ‖g y‖ₑ ∂ μ := by
    intro N
    exact lintegral_mono' (hμpartial_le N) fun _ => le_rfl
  have h_norm_piece_le :=
    sfiniteSeq_piece_norm_le
      (μ := μ)
      (r := r)
      (f := f)
      (g := g)
      (μn := μn)
      (hg_piece_int := hg_piece_int)
      (h_norm_piece := h_norm_piece)
      (h_translate_norm_bound_toReal_piece := h_translate_norm_bound_toReal_piece)
  have h_convPiece_bound :=
    sfiniteSeq_piece_conv_bound
      (μ := μ)
      (r := r)
      (f := f)
      (g := g)
      (μn := μn)
      (convPiece := convPiece)
      (h_minkowski_piece := h_minkowski_piece)
      (h_norm_piece_le := h_norm_piece_le)
  have h_convPartial_meas_mu :
      ∀ N, AEStronglyMeasurable (convPartial N) μ :=
    sfiniteSeq_convPartial_aestronglyMeasurable
      (μ := μ)
      (f := f)
      (g := g)
      (μpartial := μpartial)
      (convPartial := convPartial)
      (hμpartial_fin := hμpartial_fin)
      (hμpartial_le_smul := hμpartial_le_smul)
      (h_kernel_meas := h_kernel_meas)
      (h_convPartial_def := h_convPartial_def)
  have h_lintegral_norm_partial :
      ∀ N,
        ∫⁻ y, ‖g y‖ₑ ∂ μpartial N
          = ∑ k ∈ Finset.range (N + 1), ∫⁻ y, ‖g y‖ₑ ∂ μn k := by
    intro N
    classical
    simp [μpartial]
  have h_lintegral_norm_sum :
      (∑' n, ∫⁻ y, ‖g y‖ₑ ∂ μn n) = ∫⁻ y, ‖g y‖ₑ ∂ μ := by
    classical
    simpa [hμ_sum]
      using
        (MeasureTheory.lintegral_sum_measure
          (μ := μn)
          (f := fun y : G => ‖g y‖ₑ)).symm
  have h_lintegral_norm_tendsto :=
    sfiniteSeq_lintegral_norm_tendsto
      (μ := μ)
      (g := g)
      (μn := μn)
      (μpartial := μpartial)
      (hμ_sum := hμ_sum)
      (h_lintegral_norm_partial := h_lintegral_norm_partial)
  have h_convPartial_tendsto :=
    sfiniteSeq_convPartial_tendsto
      (μ := μ)
      (f := f)
      (g := g)
      (μn := μn)
      (μpartial := μpartial)
      (convPartial := convPartial)
      (convPiece := convPiece)
      (conv := conv)
      (hμ_sum := hμ_sum)
      (hμpartial_zero := hμpartial_zero)
      (hμpartial_succ := hμpartial_succ)
      (hμpartial_le_smul := hμpartial_le_smul)
      (hμn_le := hμn_le)
      (h_convPartial_def := fun _ => rfl)
      (h_convPiece_def := fun _ => rfl)
      (h_conv_def := rfl)
      (h_kernel_fiber_int_mu := h_kernel_fiber_int_mu)
  set bound : ℕ → ℝ≥0∞ := fun N =>
    ENNReal.ofReal
      ((((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal) *
        ∑ k ∈ Finset.range (N + 1), ∫ y, ‖g y‖ ∂ μn k)
  have h_convPartial_bound' :
      ∀ N, eLpNorm (convPartial N) r (μpartial N) ≤ bound N := by
    intro N
    simpa [bound] using h_convPartial_bound_sum N
  have h_bound_fin : ∀ N, bound N < ∞ := by
    intro N
    simp [bound]
  have h_F_aemeas :
      ∀ N, AEMeasurable (fun x => ‖convPartial N x‖ₑ ^ r.toReal) μ := by
    intro N
    exact (h_convPartial_meas_mu N).enorm.pow_const _
  have h_liminf_eq :
      (fun x : G => Filter.liminf (fun N => ‖convPartial N x‖ₑ ^ r.toReal) atTop)
        =ᵐ[μ] fun x => ‖conv x‖ₑ ^ r.toReal := by
    refine h_convPartial_tendsto.mono ?_
    intro x hx
    have h_enorm_tendsto :
        Tendsto (fun N => ‖convPartial N x‖ₑ) atTop (𝓝 (‖conv x‖ₑ)) :=
      (continuous_enorm.tendsto (conv x)).comp hx
    have h_pow_tendsto :
        Tendsto (fun N => ‖convPartial N x‖ₑ ^ r.toReal) atTop
          (𝓝 (‖conv x‖ₑ ^ r.toReal)) :=
      (ENNReal.continuous_rpow_const.tendsto (‖conv x‖ₑ)).comp h_enorm_tendsto
    simpa using (Tendsto.liminf_eq h_pow_tendsto)
  have h_conv_liminf :
      ∫⁻ x, ‖conv x‖ₑ ^ r.toReal ∂ μ ≤
        Filter.liminf
          (fun N => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ)
          atTop := by
    have h_base :=
      MeasureTheory.lintegral_liminf_le'
        (μ := μ)
        (f := fun N x => ‖convPartial N x‖ₑ ^ r.toReal)
        h_F_aemeas
    have h_congr :=
      lintegral_congr_ae (μ := μ)
        (f := fun x => Filter.liminf (fun N => ‖convPartial N x‖ₑ ^ r.toReal) atTop)
        (g := fun x => ‖conv x‖ₑ ^ r.toReal)
        h_liminf_eq
    simpa [h_congr.symm]
      using h_base
  have h_conv_integral_le_liminf :
      ∫⁻ x, ‖conv x‖ₑ ^ r.toReal ∂ μ ≤
        Filter.liminf
          (fun N => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ)
          atTop :=
    h_conv_liminf
  have hμn_ac : ∀ n, μn n ≪ μ := by
    intro n
    have h_le := (MeasureTheory.sfiniteSeq_le (μ := μ) n)
    have h_le' : μn n ≤ (1 : ℝ≥0∞) • μ := by simpa [μn, one_smul] using h_le
    exact Measure.absolutelyContinuous_of_le_smul h_le'
  have h_convPartial_pow_meas_partial :
      ∀ N M,
        AEMeasurable (fun x => ‖convPartial N x‖ₑ ^ r.toReal) (μpartial M) := by
    intro N M
    exact (h_F_aemeas N).mono_ac (hμpartial_ac M)
  have h_convPartial_pow_meas_piece :
      ∀ N n,
        AEMeasurable (fun x => ‖convPartial N x‖ₑ ^ r.toReal) (μn n) := by
    intro N n
    exact (h_F_aemeas N).mono_ac (hμn_ac n)
  have h_lintegral_convPartial_partial :
      ∀ N M,
        ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μpartial (M + 1)
          = ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μpartial M
              + ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn (M + 1) := by
    intro N M
    classical
    have h_add := hμpartial_succ M
    simp [h_add, Nat.succ_eq_add_one]
  have h_lintegral_convPartial_partial_sum :
      ∀ N M,
        ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μpartial M
          = ∑ k ∈ Finset.range (M + 1),
              ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn k := by
    intro N M
    classical
    induction' M with M hM
    · have h_zero : μpartial 0 = μn 0 := by
        simp [μpartial, Nat.succ_eq_add_one]
      simp [h_zero, μpartial, Nat.succ_eq_add_one]
    · have h_succ := h_lintegral_convPartial_partial N M
      simp [Nat.succ_eq_add_one, hM, h_succ,
        Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
  have h_lintegral_convPartial_sum :
      ∀ N,
        (∑' k, ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μn k)
          = ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ := by
    intro N
    classical
    simpa [hμ_sum]
      using
        (MeasureTheory.lintegral_sum_measure
          (μ := μn)
          (f := fun x : G => ‖convPartial N x‖ₑ ^ r.toReal)).symm
  have h_convPartial_integral_mono :
      ∀ N, Monotone
        (fun M => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μpartial M) := by
    intro N
    intro M₁ M₂ hM
    exact lintegral_mono' (hμpartial_mono hM) fun _ => le_rfl
  have h_convPartial_integral_tendsto :
      ∀ N,
        Tendsto (fun M => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μpartial M)
          atTop
          (𝓝 (∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ)) :=
    sfiniteSeq_convPartial_integral_tendsto
      (μ := μ)
      (r := r)
      (μn := μn)
      (μpartial := μpartial)
      (convPartial := convPartial)
      (h_lintegral_convPartial_partial_sum :=
        h_lintegral_convPartial_partial_sum)
      (h_lintegral_convPartial_sum := h_lintegral_convPartial_sum)
  -- eLpNormの定義により、convのr乗積分が有限であることを示す
  have hr_ne_zero : r ≠ 0 := by
    intro h
    rw [h] at hr
    simp at hr
  rw [eLpNorm_eq_lintegral_rpow_enorm hr_ne_zero hr_ne_top]
  have h_conv_integral_lt_top : ∫⁻ x, ‖conv x‖ₑ ^ r.toReal ∂ μ < ∞ := by
    -- convPartial Nの積分はconvの積分のliminf以上
    have h_bound_uniform :
        ∀ N, ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ ≤
          (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal := by
      intro N
      -- 各点でのconvPartial Nの評価
      have h_convPartial_pointwise :
          ∀ᵐ x ∂ μ, ‖convPartial N x‖ₑ ≤
            ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ) := by
        have h_int_ae :=
          integrable_norm_convolution_kernel_section (μ := μ)
            (f := f) (g := g) h_kernel_int
        refine h_int_ae.mono ?_
        intro x hx_int
        have h_norm_le :
            ‖convPartial N x‖ ≤ ∫ y, ‖f (x - y) * g y‖ ∂ μpartial N := by
          simpa [convPartial] using norm_integral_le_integral_norm (f := fun y => f (x - y) * g y)
        have h_norm_prod : ∫ y, ‖f (x - y) * g y‖ ∂ μpartial N =
            ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μpartial N := by
          congr 1
          ext y
          exact norm_mul _ _
        have h_mono : ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μpartial N ≤ ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ :=
          integral_norm_mul_mono (μpartial N) μ f g x (hμpartial_le N) hx_int
        have h_chain := le_trans (le_trans h_norm_le (h_norm_prod.le)) h_mono
        show ‖convPartial N x‖ₑ ≤ ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)
        simpa [ofReal_norm_eq_enorm] using ENNReal.ofReal_le_ofReal h_chain
      -- 積分の単調性
      have h_lintegral_mono :
          ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ ≤
            ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal ∂ μ := by
        refine lintegral_mono_ae ?_
        refine h_convPartial_pointwise.mono ?_
        intro x hx
        exact ENNReal.rpow_le_rpow hx (ENNReal.toReal_nonneg)
      -- h_kernel_intからYoung's inequalityの形の評価を得る
      -- ここでは簡略化のため、積分が有限であることのみを使う
      calc
        ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ
        _ ≤ ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal ∂ μ :=
          h_lintegral_mono
        _ ≤ (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal :=
          lintegral_convolution_norm_bound
            (μ := μ) (f := f) (g := g) (p := p) (q := q) (r := r)
            hp hq hpqr hr_ne_top hf hg h_kernel_int
    calc
      ∫⁻ x, ‖conv x‖ₑ ^ r.toReal ∂ μ
      _ ≤ Filter.liminf (fun N => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ) atTop :=
        h_conv_integral_le_liminf
      _ ≤ (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal := by
        classical
        set A := (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal with hA_def
        have h_bounded :
            IsBoundedUnder (fun x₁ x₂ : ℝ≥0∞ => x₁ ≥ x₂) atTop
              (fun N => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ) := by
          refine ⟨0, Filter.Eventually.of_forall ?_⟩
          intro N
          simp
        have h_liminf_le :
            Filter.liminf (fun N => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ) atTop ≤ A := by
          refine Filter.liminf_le_of_le (u := fun N => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ)
            (a := A) h_bounded ?_
          intro b hb
          have h_eventually_leA :
              ∀ᶠ N in atTop, b ≤ A :=
            (hb.and (Filter.Eventually.of_forall h_bound_uniform)).mono
              (fun _ h => (le_trans h.1 h.2))
          obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 h_eventually_leA
          exact hN₀ N₀ le_rfl
        simpa [hA_def] using h_liminf_le
      _ < ∞ := by
        have h_mul : eLpNorm f p μ * eLpNorm g q μ < ∞ :=
          ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top
        exact ENNReal.rpow_lt_top_of_nonneg (ENNReal.toReal_nonneg) h_mul.ne
  have h_rpow : (∫⁻ x, ‖conv x‖ₑ ^ r.toReal ∂ μ) ^ (1 / r).toReal < ∞ := by
    exact ENNReal.rpow_lt_top_of_nonneg (ENNReal.toReal_nonneg) h_conv_integral_lt_top.ne
  simpa using h_rpow

/--
Norm inequality for convolution in the finite-exponent Young regime. This refines the membership
lemma above by providing the optimal multiplicative bound on the `L^r` norm.
-/
lemma eLpNorm_convolution_le_mul
    (f g : G → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) r μ ≤
      eLpNorm f p μ * eLpNorm g q μ := by
  sorry

end ConvolutionAuxiliary
