import Frourio.Analysis.HolderInequality.HolderInequality
import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
import Frourio.Analysis.SchwartzDensityLp.FubiniSection
import Frourio.Analysis.YoungInequality.YoungInequalityCore2
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Measure.Haar.Basic

noncomputable section

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter NNReal

section ConvolutionAuxiliary

variable {G : Type*}
variable [NormedAddCommGroup G] [MeasurableSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]
variable (μ : Measure G) [SFinite μ] [SigmaFinite μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]

lemma convPartial_pointwise_bound
    (f g : G → ℂ)
    (convPartial : ℕ → G → ℂ)
    (μpartial : ℕ → Measure G)
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (h_convPartial_def : ∀ N, convPartial N = fun x => ∫ y, f (x - y) * g y ∂μpartial N)
    (hμpartial_le : ∀ N, μpartial N ≤ μ)
    (h_kernel_int : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)) :
    ∀ N, ∀ᵐ x ∂ μ, ‖convPartial N x‖ₑ ≤
      ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ) := by
  intro N
  haveI := hμpartial_fin N
  have h_int_ae :=
    integrable_norm_convolution_kernel_section (μ := μ)
      (f := f) (g := g) h_kernel_int
  refine h_int_ae.mono ?_
  intro x hx_int
  have h_norm_le :
      ‖convPartial N x‖ ≤ ∫ y, ‖f (x - y) * g y‖ ∂ μpartial N := by
    simpa [h_convPartial_def] using norm_integral_le_integral_norm (f := fun y => f (x - y) * g y)
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

lemma conv_lintegral_rpow_lt_top
    (f g : G → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 < q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hf1 : MemLp f 1 μ) (hg1 : MemLp g 1 μ)
    (conv : G → ℂ)
    (convPartial : ℕ → G → ℂ)
    (h_conv_integral_le_liminf :
      ∫⁻ x, ‖conv x‖ₑ ^ r.toReal ∂ μ ≤
        Filter.liminf (fun N => ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ) atTop)
    (h_convPartial_pointwise :
      ∀ N, ∀ᵐ x ∂ μ, ‖convPartial N x‖ₑ ≤
        ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) :
    ∫⁻ x, ‖conv x‖ₑ ^ r.toReal ∂ μ < ∞ := by
  have h_inv_p_le_one : p⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv).2 hp
  have h_inv_q_le_one : q⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv).2 (le_of_lt hq)
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
  -- convPartial Nの積分はconvの積分のliminf以上
  have h_bound_uniform :
      ∀ N, ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ ≤
        (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal := by
    intro N
    -- 各点でのconvPartial Nの評価
    have h_convPartial_pointwise_N := h_convPartial_pointwise N
    -- 積分の単調性
    have h_lintegral_mono :
        ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ ≤
          ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal ∂ μ := by
      refine lintegral_mono_ae ?_
      refine h_convPartial_pointwise_N.mono ?_
      intro x hx
      exact ENNReal.rpow_le_rpow hx (ENNReal.toReal_nonneg)
    -- h_kernel_intからYoung's inequalityの形の評価を得る
    -- ここでは簡略化のため、積分が有限であることのみを使う
    -- まず、指数関係から 1 < r を導出する
    -- work with `1 / p` and `1 / q` consistently
    have h_inv_p_le_one' : 1 / p ≤ (1 : ℝ≥0∞) := by
      simpa [one_div] using (ENNReal.inv_le_inv).2 hp
    have h_inv_q_le_one' : 1 / q ≤ (1 : ℝ≥0∞) := by
      simpa [one_div] using (ENNReal.inv_le_inv).2 (le_of_lt hq)
    have h_inv_q_ne_one' : 1 / q ≠ (1 : ℝ≥0∞) := by
      have hq_ne_one : q ≠ 1 := by
        simpa [eq_comm] using (ne_of_gt hq)
      intro h
      have : q = 1 := ENNReal.inv_eq_one.mp (by simpa [one_div] using h)
      exact hq_ne_one this
    have h_inv_q_lt_one : 1 / q < (1 : ℝ≥0∞) :=
      lt_of_le_of_ne h_inv_q_le_one' h_inv_q_ne_one'
    -- pass to real numbers via `toReal` to avoid strict-add monotonicity on `ℝ≥0∞`
    have h_inv_p_ne_top : 1 / p ≠ ∞ := by
      have : 1 / p < ∞ := lt_of_le_of_lt h_inv_p_le_one' (by simp)
      exact ne_of_lt this
    have h_inv_q_ne_top : 1 / q ≠ ∞ := by
      have : 1 / q < ∞ := lt_of_le_of_lt h_inv_q_le_one' (by simp)
      exact ne_of_lt this
    have h_inv_r_le_one_alt : 1 / r ≤ (1 : ℝ≥0∞) := by
      -- from earlier `hr` proof we know `r⁻¹ ≤ 1`
      simpa [one_div] using h_inv_r_le_one
    have h_inv_r_ne_top : 1 / r ≠ ∞ := by
      have : 1 / r < ∞ := lt_of_le_of_lt h_inv_r_le_one_alt (by simp)
      exact ne_of_lt this
    have h_toReal_sum : (1 / p + 1 / q).toReal = (1 / p).toReal + (1 / q).toReal := by
      simpa using ENNReal.toReal_add h_inv_p_ne_top h_inv_q_ne_top
    have h_inv_p_toReal_le_one : (1 / p).toReal ≤ 1 := by
      have h1 : (1 : ℝ≥0∞) ≠ ∞ := by simp
      have := (ENNReal.toReal_le_toReal h_inv_p_ne_top h1).2 h_inv_p_le_one'
      simpa using this
    have h_inv_q_toReal_lt_one : (1 / q).toReal < 1 := by
      have h1 : (1 : ℝ≥0∞) ≠ ∞ := by simp
      have := (ENNReal.toReal_lt_toReal h_inv_q_ne_top h1).2 h_inv_q_lt_one
      simpa using this
    have h_inv_p_toReal_le_one' : p.toReal⁻¹ ≤ 1 := by
      simpa [one_div, ENNReal.toReal_inv] using h_inv_p_toReal_le_one
    have h_inv_q_toReal_lt_one' : q.toReal⁻¹ < 1 := by
      simpa [one_div, ENNReal.toReal_inv] using h_inv_q_toReal_lt_one
    have h_sum_toReal_lt_two : p.toReal⁻¹ + q.toReal⁻¹ < 2 := by
      simpa [one_add_one_eq_two] using
        (add_lt_add_of_le_of_lt h_inv_p_toReal_le_one' h_inv_q_toReal_lt_one')
    have hr_ne_one : r ≠ 1 := by
      intro hr_eq
      -- from `r = 1`, the exponent identity yields `1/p + 1/q = 2`
      have h_eq2 : 1 / p + 1 / q = (2 : ℝ≥0∞) := by
        simpa [hr_eq, one_div, inv_one, one_add_one_eq_two] using hpqr
      -- apply `toReal` and use additivity on finite terms
      have h_sum_toReal_eq_two : p.toReal⁻¹ + q.toReal⁻¹ = 2 := by
        have ht : (1 / p + 1 / q).toReal = 2 := by
          have htmp := congrArg ENNReal.toReal h_eq2
          simpa using htmp
        have hsum := ENNReal.toReal_add h_inv_p_ne_top h_inv_q_ne_top
        calc
          p.toReal⁻¹ + q.toReal⁻¹
              = (1 / p).toReal + (1 / q).toReal := by
                    simp [one_div, ENNReal.toReal_inv]
          _ = (1 / p + 1 / q).toReal := by
                    simpa using hsum.symm
          _ = 2 := ht
      exact (ne_of_lt h_sum_toReal_lt_two) h_sum_toReal_eq_two
    have hr_one_lt : (1 : ℝ≥0∞) < r :=
      lt_of_le_of_ne hr (by simpa [eq_comm] using hr_ne_one)
    calc
      ∫⁻ x, ‖convPartial N x‖ₑ ^ r.toReal ∂ μ
      _ ≤ ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal ∂ μ :=
        h_lintegral_mono
      _ ≤ (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal :=
        lintegral_convolution_norm_bound
          (μ := μ) (f := f) (g := g) (p := p) (q := q) (r := r)
          hp hq hpqr hr_one_lt hr_ne_top hf hg hf1 hg1
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

lemma convolution_memLp_of_memLp
    (f g : G → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 < q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hf_r : MemLp f r μ) (hg : MemLp g q μ)
    (hf1 : MemLp f 1 μ) (hg1 : MemLp g 1 μ)
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
    simpa using (ENNReal.inv_le_inv).2 (le_of_lt hq)
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
        (c := ((N + 1 : ℝ≥0∞) * (N + 1 : ℝ≥0∞)))
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
    exact (hg_partial N).mono_exponent (p := (1 : ℝ≥0∞)) (q := q) (le_of_lt hq)
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
  have h_pointwise_piece :
      ∀ N,
        (fun y =>
            (eLpNorm (fun x => f (x - y) * g y) r (μpartial N)).toReal)
          =ᵐ[μpartial N]
          fun y =>
            ‖g y‖ * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
    intro N
    refine Filter.Eventually.of_forall ?_
    intro y
    have h_scaling :
        eLpNorm (fun x => f (x - y) * g y) r (μpartial N) =
          ENNReal.ofReal ‖g y‖ * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
      have h_smul :
          (fun x : G => f (x - y) * g y) =
            fun x : G => (g y) • f (x - y) := by
        funext x
        simp [mul_comm, smul_eq_mul, sub_eq_add_neg]
      simpa [h_smul] using
        eLpNorm_const_smul (μ := μpartial N) (p := r) (c := g y)
          (f := fun x => f (x - y))
    have h_toReal := congrArg ENNReal.toReal h_scaling
    have h_nonneg : 0 ≤ ‖g y‖ := norm_nonneg _
    simpa [ENNReal.toReal_ofReal_mul, h_nonneg] using h_toReal
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
    exact (hg_piece n).mono_exponent (p := (1 : ℝ≥0∞)) (q := q) (le_of_lt hq)
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
  have h_pointwise_piece_piece :
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
    simpa using (h_pointwise_piece_piece n).symm
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
      (h_pointwise := h_pointwise_piece_piece)
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
  -- h_convPartial_pointwise を補題で構築
  have h_convPartial_pointwise :
      ∀ N, ∀ᵐ x ∂ μ, ‖convPartial N x‖ₑ ≤
        ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ) :=
    convPartial_pointwise_bound
      (μ := μ) (f := f) (g := g)
      convPartial μpartial
      hμpartial_fin
      (fun _ => rfl)
      hμpartial_le
      h_kernel_int
  -- conv_lintegral_rpow_lt_top 補題を使う
  have h_conv_integral_lt_top : ∫⁻ x, ‖conv x‖ₑ ^ r.toReal ∂ μ < ∞ :=
    conv_lintegral_rpow_lt_top
      (μ := μ) (f := f) (g := g) (p := p) (q := q) (r := r)
      hp hq hpqr hr_ne_top hf hg hf1 hg1
      conv convPartial
      h_conv_integral_le_liminf
      h_convPartial_pointwise
  have h_rpow : (∫⁻ x, ‖conv x‖ₑ ^ r.toReal ∂ μ) ^ (1 / r).toReal < ∞ := by
    exact ENNReal.rpow_lt_top_of_nonneg (ENNReal.toReal_nonneg) h_conv_integral_lt_top.ne
  simpa using h_rpow

/--
**Young's convolution inequality (complete version).**

For σ-finite additive commutative normed group (G,μ) and complex-valued functions f,g : G → ℂ,
with exponents 1 ≤ p, q ≤ ∞ and 1 ≤ r < ∞ satisfying 1/p + 1/q = 1 + 1/r:
- If f ∈ Lᵖ(μ) and g ∈ Lᵍ(μ), then the convolution f*g belongs to Lʳ(μ), and
- ‖f*g‖_{Lʳ} ≤ ‖f‖_{Lᵖ} * ‖g‖_{Lᵍ}

This is the full version matching the documentation in eLpNorm_convolution_le_mul.md.
-/
-- 指数関係から p ≤ r を導出する補助補題（修正版）
-- 注：元の主張 r ≤ p は数学的に誤りでした。正しくは p ≤ r です。
lemma young_exponent_p_le_r
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    p ≤ r := by
  -- Setup: basic bounds on inverse exponents from hp, hq
  have h_inv_p_le_one : p⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv).2 hp
  have h_inv_q_le_one : q⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv).2 hq
  -- From the exponent identity, compare r⁻¹ and p⁻¹
  -- Idea: 1/p + 1/q = 1 + 1/r and 1/q ≤ 1 ⇒ 1/r ≤ 1/p, i.e. r⁻¹ ≤ p⁻¹
  have h_inv_r_le_inv_p : r⁻¹ ≤ p⁻¹ := by
    -- From `hq`, get `1 / q ≤ 1`
    have h_inv_q_le_one' : 1 / q ≤ (1 : ℝ≥0∞) := by simpa [one_div] using h_inv_q_le_one
    -- Rewrite the exponent identity to `1/p + 1/q = 1 + 1/r`
    have h_eq : 1 / p + 1 / q = 1 + 1 / r := by
      simpa [one_div, add_comm, add_left_comm, add_assoc] using hpqr
    -- From `1/p + 1/q = 1 + 1/r` and `1/q ≤ 1`, derive `1 + 1/r ≤ 1 + 1/p`
    have h_aux : 1 + 1 / r ≤ 1 + 1 / p := by
      rw [← h_eq]
      calc 1 / p + 1 / q
          ≤ 1 / p + 1 := add_le_add le_rfl h_inv_q_le_one'
        _ = 1 + 1 / p := add_comm _ _
    -- Cancel the `+ 1` on both sides
    have h_one_ne_top : (1 : ℝ≥0∞) ≠ ∞ := by simp
    calc r⁻¹
        = 1 / r := by simp [one_div]
      _ ≤ 1 / p := ENNReal.le_of_add_le_add_left h_one_ne_top h_aux
      _ = p⁻¹ := by simp [one_div]
  -- Convert inverse inequality to the order on exponents
  -- We have proven r⁻¹ ≤ p⁻¹, which gives us p ≤ r
  exact (ENNReal.inv_le_inv).1 h_inv_r_le_inv_p

-- 指数関係から q ≤ r を導出する補助補題（修正版）
-- 注：元の主張 r ≤ q は数学的に誤りでした。正しくは q ≤ r です。
lemma young_exponent_q_le_r
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    q ≤ r := by
  -- Similar to young_exponent_p_le_r, but for q
  have h_inv_p_le_one : p⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv).2 hp
  have h_inv_q_le_one : q⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv).2 hq
  -- From the exponent identity, compare r⁻¹ and q⁻¹
  -- Idea: 1/p + 1/q = 1 + 1/r and 1/p ≤ 1 ⇒ 1/r ≤ 1/q, i.e. r⁻¹ ≤ q⁻¹
  have h_inv_r_le_inv_q : r⁻¹ ≤ q⁻¹ := by
    -- From `hp`, get `1 / p ≤ 1`
    have h_inv_p_le_one' : 1 / p ≤ (1 : ℝ≥0∞) := by simpa [one_div] using h_inv_p_le_one
    -- Rewrite the exponent identity to `1/p + 1/q = 1 + 1/r`
    have h_eq : 1 / p + 1 / q = 1 + 1 / r := by
      simpa [one_div, add_comm, add_left_comm, add_assoc] using hpqr
    -- From `1/p + 1/q = 1 + 1/r` and `1/p ≤ 1`, derive `1 + 1/r ≤ 1 + 1/q`
    have h_aux : 1 + 1 / r ≤ 1 + 1 / q := by
      rw [← h_eq]
      exact add_le_add h_inv_p_le_one' le_rfl
    -- Cancel the `+ 1` on both sides
    have h_one_ne_top : (1 : ℝ≥0∞) ≠ ∞ := by simp
    calc r⁻¹
        = 1 / r := by simp [one_div]
      _ ≤ 1 / q := ENNReal.le_of_add_le_add_left h_one_ne_top h_aux
      _ = q⁻¹ := by simp [one_div]
  -- Convert inverse inequality to the order on exponents
  -- We have proven r⁻¹ ≤ q⁻¹, which gives us q ≤ r
  exact (ENNReal.inv_le_inv).1 h_inv_r_le_inv_q

lemma finset_sum_isAddRightInvariant
    (μs : ℕ → Measure G)
    (s : Finset ℕ)
    (h : ∀ k ∈ s, (μs k).IsAddRightInvariant) :
    (∑ k ∈ s, μs k).IsAddRightInvariant := by
  -- 有限和測度の不変性を示すのは非自明
  -- 必要な補題：
  -- 1. (0 : Measure G).IsAddRightInvariant (空集合の場合)
  -- 2. μ₁.IsAddRightInvariant → μ₂.IsAddRightInvariant →
  --    (μ₁ + μ₂).IsAddRightInvariant (和の不変性)
  sorry

lemma finset_sum_isNegInvariant
    (μs : ℕ → Measure G)
    (s : Finset ℕ)
    (h : ∀ k ∈ s, (μs k).IsNegInvariant) :
    (∑ k ∈ s, μs k).IsNegInvariant := by
  -- 有限和測度の反転不変性を示すのは非自明
  -- 必要な補題：
  -- 1. (0 : Measure G).IsNegInvariant (空集合の場合)
  -- 2. μ₁.IsNegInvariant → μ₂.IsNegInvariant →
  --    (μ₁ + μ₂).IsNegInvariant (和の不変性)
  sorry

/--
**Young's convolution inequality for finite measures (Proposition 3.1).**

For a finite measure space (G, μ) with μ being IsFiniteMeasure, and complex-valued
functions f, g : G → ℂ, with exponents 1 ≤ p, q and 1 ≤ r < ∞ satisfying
1/p + 1/q = 1 + 1/r:

If f ∈ Lᵖ(μ) and g ∈ Lᵍ(μ), then:
  ‖f*g‖_{Lʳ(μ)} ≤ ‖f‖_{Lᵖ(μ)} * ‖g‖_{Lᵍ(μ)}

This is the finite measure version that serves as the foundation for the σ-finite case.
The proof strategy (from eLpNorm_convolution_le_mul.md):
1. Use duality: for φ ∈ Lʳ'(μ), estimate ∫(f*g)φ
2. Apply Fubini's theorem
3. Use Hölder's inequality twice (once for each variable)
4. The exponent arithmetic from young_exponent_p_le_r and young_exponent_q_le_r
   ensures the exponents match correctly
-/
lemma young_inequality_finite_measure
    [IsFiniteMeasure μ]
    (f g : G → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) r μ ≤
      eLpNorm f p μ * eLpNorm g q μ := by
  sorry

theorem eLpNorm_convolution_le_mul
    (f g : G → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) r μ ≤
      eLpNorm f p μ * eLpNorm g q μ := by
  -- 方針：
  -- 1. young_exponent_p_le_r と young_exponent_q_le_r から p ≤ r かつ q ≤ r を得る
  -- 2. MemLp.of_exponent_le を使って f ∈ Lʳ, g ∈ L¹ を導出
  -- 3. young_inequality_convolution_complex_sfiniteSeq で MemLp を得る
  -- 4. 有限測度での不等式を適用し、σ-有限測度へ拡張

  -- Step 1: 指数の関係を導出
  have h_p_le_r : p ≤ r := young_exponent_p_le_r hp hq hpqr
  have h_q_le_r : q ≤ r := young_exponent_q_le_r hp hq hpqr

  -- Step 2: 場合分け - q = 1 または q > 1
  by_cases hq_one : q = 1
  · -- Case q = 1: この場合 p⁻¹ + 1 = 1 + r⁻¹ より p = r
    -- 指数関係から p = r を導出
    -- q = 1 のとき 1/p + 1 = 1 + 1/r より p = r
    -- これは young_exponent_p_le_r と young_exponent_q_le_r から従うが、
    -- 直接証明するのは ENNReal の加法キャンセルが複雑なため、
    -- ここでは sorry とする
    have h_p_eq_r : p = r := by
      -- From q = 1, the exponent identity becomes 1/p + 1 = 1 + 1/r
      have h_sum : 1 / p + 1 = 1 + 1 / r := by
        simpa [hq_one, one_div, inv_one, add_comm, add_left_comm, add_assoc]
          using hpqr
      -- Cancel the common 1 on both sides to get 1/p = 1/r
      have h1_ne_top : (1 : ℝ≥0∞) ≠ ∞ := by simp
      have h_le_pr : 1 / p ≤ 1 / r := by
        have : 1 + 1 / p ≤ 1 + 1 / r := by
          simpa [add_comm] using (le_of_eq h_sum)
        exact ENNReal.le_of_add_le_add_left h1_ne_top this
      have h_le_rp : 1 / r ≤ 1 / p := by
        -- Prove the add-inequality in the form `r⁻¹ + 1 ≤ p⁻¹ + 1`
        have h_add_inv : r⁻¹ + 1 ≤ p⁻¹ + 1 := by
          -- From `h_sum.symm : 1 + 1 / r = 1 / p + 1`, derive equality on commuted sides
          have h_eq' : 1 / r + 1 = 1 / p + 1 := by
            have : 1 + 1 / r = 1 / p + 1 := by simpa [add_comm] using h_sum.symm
            simpa [add_comm] using this
          have : 1 / r + 1 ≤ 1 / p + 1 := by exact le_of_eq h_eq'
          simpa [one_div, add_comm] using this
        -- Cancel the finite `1` on the left using `le_of_add_le_add_left`
        exact ENNReal.le_of_add_le_add_left h1_ne_top (by simpa [one_div, add_comm] using h_add_inv)
      have h_inv_eq : 1 / p = 1 / r := le_antisymm h_le_pr h_le_rp
      -- Invert both sides to conclude p = r
      have := congrArg (fun x : ℝ≥0∞ => x⁻¹) h_inv_eq
      simpa [one_div, inv_inv] using this

    -- q = 1 のとき、畳み込みは ‖g‖_L¹ によるスケーリングになる
    -- p = r なので、eLpNorm f p μ = eLpNorm f r μ
    -- young_inequality_finite_measure をσ-有限測度に適用するのは困難
    -- （IsFiniteMeasure μ のインスタンスがない）
    -- したがって、σ-有限測度への拡張が必要だが、これは q > 1 の場合と同様
    sorry
  · -- Case q > 1
    push_neg at hq_one
    have hq_gt : 1 < q := by
      rcases hq.lt_or_eq with h | h
      · exact h
      · exact absurd h.symm hq_one

    -- 実装方針（eLpNorm_convolution_le_mul.md の §6「σ-有限測度への拡張」に対応）：
    --
    -- Step 1: σ-有限測度の分解を構成
    set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
    have hμn_fin : ∀ n, IsFiniteMeasure (μn n) := fun n => inferInstance
    have hμ_sum : Measure.sum μn = μ := MeasureTheory.sum_sfiniteSeq μ

    -- Step 2: 部分和測度を定義 μ_N = Σ_{k=0}^N μ_k
    let μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k
    have hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N) := by
      intro N
      classical
      infer_instance

    -- Step 3: 部分和測度での MemLp を準備
    have hμpartial_le_smul : ∀ N, μpartial N ≤ ((N + 1 : ℝ≥0∞) • μ) := by
      intro N
      sorry -- μpartial N ≤ (N + 1) • μ の証明

    have hf_partial : ∀ N, MemLp f p (μpartial N) := by
      intro N
      apply hf.of_measure_le_smul (c := (N + 1 : ℝ≥0∞))
      · simp
      · exact hμpartial_le_smul N

    have hg_partial : ∀ N, MemLp g q (μpartial N) := by
      intro N
      apply hg.of_measure_le_smul (c := (N + 1 : ℝ≥0∞))
      · simp
      · exact hμpartial_le_smul N

    -- Step 4: 各部分和測度で young_inequality_finite_measure を適用
    have h_partial_ineq : ∀ N,
      eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μpartial N) r (μpartial N) ≤
      eLpNorm f p (μpartial N) * eLpNorm g q (μpartial N) := by
      intro N
      -- young_inequality_finite_measure の呼び出しには以下が必要：
      -- 1. IsFiniteMeasure (μpartial N) ✓ (hμpartial_fin N で導出済み)
      -- 2. (μpartial N).IsAddRightInvariant ✗ (未導出)
      -- 3. (μpartial N).IsNegInvariant ✗ (未導出)
      --
      -- 問題：各 μn k が不変性を持っていても、それらの有限和 μpartial N が
      --       不変性を持つことを示すには追加の補題が必要
      --
      -- 必要な補題：
      -- - Measure.sum_isAddRightInvariant :
      --     (∀ k, (μn k).IsAddRightInvariant) → (∑ k, μn k).IsAddRightInvariant
      -- - Measure.sum_isNegInvariant :
      --     (∀ k, (μn k).IsNegInvariant) → (∑ k, μn k).IsNegInvariant
      sorry
      -- 本来の実装:
      -- haveI := hμpartial_fin N
      -- haveI : (μpartial N).IsAddRightInvariant := by
      --   -- μ の不変性から各 μn k の不変性を導出し、有限和に拡張
      --   sorry
      -- haveI : (μpartial N).IsNegInvariant := by
      --   sorry
      -- apply young_inequality_finite_measure hp hq hpqr hr_ne_top (hf_partial N) (hg_partial N)

    -- Step 5: 部分和測度での不等式を元の測度での不等式に拡張
    -- μpartial N ≤ μ より eLpNorm f p (μpartial N) ≤ eLpNorm f p μ
    have hμpartial_le : ∀ N, μpartial N ≤ μ := by
      intro N
      sorry -- μpartial N ≤ μ の証明 (μ = Σ μn からの導出)

    have hf_norm_mono : ∀ N, eLpNorm f p (μpartial N) ≤ eLpNorm f p μ := by
      intro N
      sorry -- eLpNorm の単調性

    have hg_norm_mono : ∀ N, eLpNorm g q (μpartial N) ≤ eLpNorm g q μ := by
      intro N
      sorry -- eLpNorm の単調性

    -- Step 6: N → ∞ の極限を取る
    -- eLpNorm (f*g) r (μpartial N) は N について単調増加
    -- lim_{N→∞} eLpNorm (f*g) r (μpartial N) = eLpNorm (f*g) r μ
    -- かつ各 N で不等式が成立するので、極限でも成立

    have h_final : eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) r μ ≤
        eLpNorm f p μ * eLpNorm g q μ := by
      -- 各 N での不等式と単調性から導出
      sorry -- 極限操作の詳細

    exact h_final

end ConvolutionAuxiliary
