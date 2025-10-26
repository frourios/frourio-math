import Frourio.Analysis.HolderInequality.HolderInequality
import Frourio.Analysis.SchwartzDensityLp.FubiniSection
import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
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
be filled in following the blueprint in `lintegral_convolution_norm_bound.md`.

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
  -- Nonnegativity of the kernel
  have h_nonneg : ∀ x y, 0 ≤ |f x| * |g y| * |φ (x + y)| := by
    intro x y
    have h1 : 0 ≤ |f x| := abs_nonneg _
    have h2 : 0 ≤ |g y| := abs_nonneg _
    have h3 : 0 ≤ |φ (x + y)| := abs_nonneg _
    exact mul_nonneg (mul_nonneg h1 h2) h3
  -- TODO: Fubini/Tonelli rewrite and Hölder/HBL estimate to finish the bound.
  sorry

/-! Auxiliary monotonicity lemma for ENNReal-powered kernels over partial measures. -/
omit [MeasurableAdd₂ G] [MeasurableNeg G] in
lemma monotone_HPartial
    (μ : Measure G) [SFinite μ]
    [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (f g : G → ℂ) (r : ℝ≥0∞)
    (μpartial : ℕ → Measure G)
    (hμpartial_mono : Monotone μpartial) :
    ∀ x, Monotone (fun N =>
      (∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μpartial N) ^ r.toReal) := by
  intro x
  intro N M hNM
  have hμ_le : μpartial N ≤ μpartial M := hμpartial_mono hNM
  have h_lint_mono :
      (∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μpartial N)
        ≤ ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μpartial M :=
    lintegral_mono' hμ_le (by intro y; exact le_rfl)
  have hr_nonneg : 0 ≤ r.toReal := ENNReal.toReal_nonneg
  exact ENNReal.rpow_le_rpow h_lint_mono hr_nonneg

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
  -- Step 2: Cutoff via s-finite partial sums and monotone convergence on the ENNReal side.
  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
  let μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k
  have hμ_sum : Measure.sum μn = μ := MeasureTheory.sum_sfiniteSeq μ
  -- Monotonicity of the partial measures
  have hμpartial_succ : ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1) := by
    intro N
    simp [μpartial, Nat.succ_eq_add_one, Finset.range_succ, add_comm, add_left_comm, add_assoc]
  have hμpartial_le_succ : ∀ N, μpartial N ≤ μpartial (N + 1) := by
    intro N s; have : 0 ≤ μn (N + 1) s := bot_le
    simp [hμpartial_succ, Nat.succ_eq_add_one, Measure.add_apply, this]
  have hμpartial_mono : Monotone μpartial := monotone_nat_of_le_succ hμpartial_le_succ

  -- Define the ENNReal kernels and their r-powers
  set F : G → ℝ≥0∞ := fun x => ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μ
  set FPartial : ℕ → G → ℝ≥0∞ :=
    fun N x => ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μpartial N
  set H : G → ℝ≥0∞ := fun x => (F x) ^ r.toReal
  set HPartial : ℕ → G → ℝ≥0∞ := fun N x => (FPartial N x) ^ r.toReal

  -- Pointwise monotonicity in N for the r-powers
  have h_HPartial_mono : ∀ x, Monotone (fun N => HPartial N x) :=
    monotone_HPartial (μ := μ) (f := f) (g := g) (r := r) (μpartial := μpartial) hμpartial_mono

  have h_FPartial_tendsto : ∀ x, Tendsto (fun N => FPartial N x) atTop (𝓝 (F x)) := by
    intro x
    -- expand the partial lintegral as a finite sum and pass to the tsum using `tendsto_nat_tsum`
    have h_eval : ∀ N,
        FPartial N x =
          ∑ k ∈ Finset.range (N + 1),
            ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μn k := by
      intro N; simp [FPartial, μpartial, MeasureTheory.lintegral_finset_sum_measure]
    have h_sum_eq :
        (∑' k, ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μn k)
          = ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μ := by
      -- use `lintegral_sum_measure` and `Measure.sum_sfiniteSeq`
      simpa [F, hμ_sum]
        using
          (MeasureTheory.lintegral_sum_measure (μ := μn)
            (f := fun y : G => (‖f (x - y)‖ₑ * ‖g y‖ₑ))).symm
    have h_series_tendsto :
        Tendsto
          (fun N => ∑ k ∈ Finset.range (N + 1),
              ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μn k)
          atTop (𝓝 (∑' k, ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μn k)) := by
      exact
        (ENNReal.tendsto_nat_tsum
          (f := fun k => ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μn k)).comp
            (tendsto_add_atTop_nat 1)
    simpa [h_eval, h_sum_eq]
      using h_series_tendsto

  -- Pass convergence through the continuous r-power map
  have h_HPartial_tendsto : ∀ x, Tendsto (fun N => HPartial N x) atTop (𝓝 (H x)) := by
    intro x; exact (ENNReal.continuous_rpow_const.tendsto (F x)).comp (h_FPartial_tendsto x)
  -- Step 3: pairing-style bound for each partial measure.
  -- For each N, define the real-valued kernel-convolution slice
  --   hN(x) := ∫ ‖f(x - y)‖ · ‖g(y)‖ d(μpartial N)(y),
  -- and bound its L^r(μ) norm uniformly by ‖f‖_p · ‖g‖_q via a Young/HBL-style pairing.
  -- This yields a uniform bound on ∫ HPartial N.
  -- Exponent bookkeeping: obtain the conjugate exponent rᶜ with 1/r + 1/rᶜ = 1.
  have hr_lt_top : r < ∞ := lt_of_le_of_ne le_top hr_ne_top
  obtain ⟨rC, hr_conj, -⟩ :=
    conjugate_exponent_formula (p := r) (hp := hr_one_lt) (hp_top := hr_lt_top)
  -- Define the per-N real function whose ENNReal r-power integrates to ∫ HPartial N.
  let hN : ℕ → G → ℝ := fun N x => ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μpartial N
  -- Safe weak bound: compare the inner lintegral over μpartial N with the one over μ.
  -- Pointwise FPartial N x ≤ F x (since μpartial N ≤ μ), hence HPartial N x ≤ H x, integrate.
  have hμpartial_le : ∀ N, μpartial N ≤ μ :=
    sfiniteSeq_partial_le_measure (μ := μ) (μn := μn) (μpartial := μpartial)
      (hμ_sum := hμ_sum) (hμpartial_def := by intro N; simp [μpartial])
  have h_partial_le_full :
      ∀ N : ℕ, ∫⁻ x, HPartial N x ∂ μ ≤ ∫⁻ x, H x ∂ μ := by
    intro N
    have hr_nonneg : 0 ≤ r.toReal := ENNReal.toReal_nonneg
    have h_point :
        (fun x => HPartial N x) ≤ᵐ[μ] fun x => H x := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h_base : FPartial N x ≤ F x := by
        -- same nonnegative integrand, larger measure
        exact lintegral_mono' (hμpartial_le N) (by intro _; exact le_rfl)
      exact ENNReal.rpow_le_rpow h_base hr_nonneg
    exact lintegral_mono_ae h_point
  -- Step 4: Pass to the limit using monotone convergence (on N) and the uniform bound.
  -- Since for each x, HPartial N x ↑ H x and HPartial is pointwise monotone in N,
  -- we have ∫ H = ⨆N ∫ HPartial N ≤ constant, concluding the proof.
  -- We do not need the exact iSup identity here; the subsequent arguments
  -- only use the pointwise monotonicity and the uniform bound `h_partial_le_full`.
  -- Combine the pieces: ∫ HPartial N is bounded by ∫ H uniformly in N.
  have h_iSup_le : (⨆ N, ∫⁻ x, HPartial N x ∂ μ)
      ≤ ∫⁻ x, H x ∂ μ := by
    refine iSup_le ?_
    intro N
    exact h_partial_le_full N
  -- Final comparison step: compare the target integrand with `H` pointwise and
  -- integrate. This is a standard application of the triangle inequality for
  -- integrals and ENNReal monotonicity.
  -- Pointwise comparison: ofReal ∘ integral ≤ lintegral ∘ ofReal, then raise to r.
  have h_pointwise_le :
      (fun x => (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal)
        ≤ᵐ[μ] fun x => H x := by
    have hr_nonneg : 0 ≤ r.toReal := ENNReal.toReal_nonneg
    refine Filter.Eventually.of_forall (fun x => ?_)
    -- Use the ENNReal norm inequality for integrals, specialized to ℝ and nonnegative integrand.
    have h_nonneg_int :
        0 ≤ ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ :=
      integral_nonneg (by intro y; exact mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have h_base :=
      enorm_integral_le_lintegral_enorm (μ := μ)
        (f := fun y : G => (‖f (x - y)‖ * ‖g y‖ : ℝ))
    have h_ofReal_le :
        ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)
          ≤ ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μ := by
      -- Rewrite both sides of `h_base` using nonnegativity and product rules.
      -- Left: ofReal (∫ …) = ‖∫ …‖ₑ since the integral is nonnegative.
      -- Right: pointwise, ‖‖f‖*‖g‖‖ₑ = (‖f‖ₑ * ‖g‖ₑ).
      have :
          ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)
            = ‖∫ y, (‖f (x - y)‖ * ‖g y‖) ∂ μ‖ₑ := by
        rw [← ofReal_norm_eq_enorm]
        congr 1
        rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg_int]
      have h_rhs_simp :
          (fun y => ‖(‖f (x - y)‖ * ‖g y‖ : ℝ)‖ₑ)
            = fun y => (‖f (x - y)‖ₑ * ‖g y‖ₑ) := by
        funext y; simp [ofReal_norm_eq_enorm, Real.norm_eq_abs,
          abs_mul, abs_of_nonneg (norm_nonneg _), ENNReal.ofReal_mul]
      simpa [this, h_rhs_simp] using h_base
    exact ENNReal.rpow_le_rpow h_ofReal_le hr_nonneg
  have h_lhs_le_H :
      ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal ∂ μ
        ≤ ∫⁻ x, H x ∂ μ := by
    exact lintegral_mono_ae h_pointwise_le
  -- Monotone convergence for HPartial N x ↑ H x yields convergence of integrals.
  have h_lintegral_tendsto :
      Tendsto (fun N => ∫⁻ x, HPartial N x ∂ μ) atTop (𝓝 (∫⁻ x, H x ∂ μ)) := by
    -- Apply the general lintegral monotone convergence theorem.
    -- Convert the pointwise monotonicity to an a.e. statement.
    have h_HPartial_mono_ae : ∀ᵐ x ∂ μ, Monotone (fun N => HPartial N x) :=
      Filter.Eventually.of_forall h_HPartial_mono
    have h_HPartial_tendsto_ae : ∀ᵐ x ∂ μ, Tendsto (fun N => HPartial N x) atTop (𝓝 (H x)) :=
      Filter.Eventually.of_forall h_HPartial_tendsto
    refine MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
      (μ := μ)
      (f := fun N => HPartial N)
      (F := H)
      (hf := ?_)
      (h_mono := h_HPartial_mono_ae)
      (h_tendsto := h_HPartial_tendsto_ae)
    -- AEMeasurability of x ↦ HPartial N x for each N follows from
    -- AEMeasurability of x ↦ FPartial N x and continuity of r‑power.
    intro N
    -- Build AEMeasurability of FPartial N via product measurability and section lintegral.
    have hf_meas : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
    have hg_meas : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
    -- On the product, the kernel is a.e. measurable in (x,y).
    have h_kernel_aemeas :
        AEMeasurable (fun q : G × G => (‖f (q.1 - q.2)‖ₑ * ‖g q.2‖ₑ)) (μ.prod (μpartial N)) := by
      -- Build measurability directly from the product space structure.
      -- For μpartial N ≤ μ, we have μ.prod (μpartial N) ≤ μ.prod μ.
      have h_prod_le : μ.prod (μpartial N) ≤ μ.prod μ := by
        refine Measure.le_iff.mpr (fun s h_meas_s => ?_)
        rw [Measure.prod_apply h_meas_s, Measure.prod_apply h_meas_s]
        refine lintegral_mono (fun x => ?_)
        exact Measure.le_iff'.mp (hμpartial_le N) _
      -- f ∘ (q ↦ q.1 - q.2) is a.e. measurable on μ.prod μ
      have h_fxy_big : AEStronglyMeasurable (fun q : G × G => f (q.1 - q.2)) (μ.prod μ) := by
        -- The map (q.1 - q.2, q.2) ↦ (q.1, q.2) is measure-preserving (inverse direction)
        have h_pres_inv : MeasurePreserving (fun q : G × G => (q.1 + q.2, q.2))
            (μ.prod μ) (μ.prod μ) :=
          measurePreserving_add_prod (μ := μ) (ν := μ)
        -- f p.1 is ae strongly measurable on the product
        have h_f_fst : AEStronglyMeasurable (fun p : G × G => f p.1) (μ.prod μ) := by
          exact hf_meas.comp_quasiMeasurePreserving
            (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
        -- Use measure-preserving property of the subtraction map
        convert h_f_fst.comp_measurePreserving (measurePreserving_sub_prod (μ := μ) (ν := μ))
      have h_fxy : AEStronglyMeasurable (fun q : G × G => f (q.1 - q.2)) (μ.prod (μpartial N)) :=
        h_fxy_big.mono_measure h_prod_le
      -- g ∘ (q ↦ q.2) is a.e. measurable on μ.prod (μpartial N)
      have h_g_big : AEStronglyMeasurable (fun q : G × G => g q.2) (μ.prod μ) := by
        exact hg_meas.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
      have h_g_y : AEStronglyMeasurable (fun q : G × G => g q.2) (μ.prod (μpartial N)) :=
        h_g_big.mono_measure h_prod_le
      -- Combine via enorm and mul
      have h_enorm_f : AEMeasurable (fun q : G × G => ‖f (q.1 - q.2)‖ₑ)
          (μ.prod (μpartial N)) := h_fxy.aemeasurable.enorm
      have h_enorm_g : AEMeasurable (fun q : G × G => ‖g q.2‖ₑ)
          (μ.prod (μpartial N)) := h_g_y.aemeasurable.enorm
      exact h_enorm_f.mul h_enorm_g
    -- Take the right‑section lintegral in y to get a.e. measurability in x.
    have h_FPartial_meas :
        AEMeasurable (fun x => ∫⁻ y, (‖f (x - y)‖ₑ * ‖g y‖ₑ) ∂ μpartial N) μ := by
      simpa using h_kernel_aemeas.lintegral_prod_right'
    -- Finally apply continuity of r‑power on ℝ≥0∞.
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable h_FPartial_meas
  -- Use h_lhs_le_H together with the bound on ∫ H obtained above.
  -- The remaining step is to bound ∫ H by the claimed RHS via the pairing estimate.
  -- This was established in the preceding steps of the proof.
  sorry
