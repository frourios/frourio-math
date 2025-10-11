import Frourio.Analysis.SchwartzDensityLp.SchwartzDensityLpCore
import Frourio.Analysis.SchwartzDensityLp.ConvolutionTheory
import Frourio.Analysis.SchwartzDensityLp.YoungInequality
import Frourio.Analysis.SchwartzDensityLp.ApproximateIdentity
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution

variable {n : ℕ}

/--
**平滑な切り詰め関数の存在 (Lemma 4.4 in the paper).**

任意の 0 < r < R に対して、χ ∈ C∞_c が存在して
- χ ≡ 1 on B_r
- 0 ≤ χ ≤ 1
- supp(χ) ⊆ B_R

これは論文のステップ4で使用される。
-/
lemma exists_smooth_cutoff
    (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    ∃ χ : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (∞ : WithTop ℕ∞) χ ∧
      (∀ x, ‖x‖ ≤ r → χ x = 1) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.closedBall (0 : Fin n → ℝ) R := by
  classical
  let χ_bump : ContDiffBump (0 : Fin n → ℝ) := ⟨r, R, hr, hR⟩
  let χ : (Fin n → ℝ) → ℝ := fun x => χ_bump x
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [χ] using χ_bump.contDiff
  · intro x hx
    have hx_mem : x ∈ Metric.closedBall (0 : Fin n → ℝ) χ_bump.rIn := by
      simpa [χ, Metric.mem_closedBall, dist_eq_norm] using hx
    simpa [χ] using χ_bump.one_of_mem_closedBall hx_mem
  · intro x
    have h_nonneg : 0 ≤ χ_bump x := by
      simpa [χ] using χ_bump.nonneg' x
    have h_le_one : χ_bump x ≤ 1 := by
      simpa [χ] using (χ_bump.le_one (x := x))
    exact ⟨h_nonneg, h_le_one⟩
  · simpa [χ] using χ_bump.hasCompactSupport
  · have h_tsupp_eq : tsupport χ =
        Metric.closedBall (0 : Fin n → ℝ) χ_bump.rOut := by
      simpa [χ] using χ_bump.tsupport_eq
    have h_rOut : χ_bump.rOut = R := rfl
    simp [χ, h_rOut, h_tsupp_eq]

/-- 補助: L¹ ノルムで 3 つの誤差をまとめて評価する。 -/
lemma triangle_inequality_aux
    (f g h : (Fin n → ℝ) → ℂ)
    (ε ε₁ ε₂ ε₃ : ℝ)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hh_meas : AEStronglyMeasurable h volume)
    (hf : eLpNorm f (1 : ℝ≥0∞) volume < ENNReal.ofReal ε₁)
    (hg : eLpNorm g 1 volume < ENNReal.ofReal ε₂)
    (hh : eLpNorm h 1 volume < ENNReal.ofReal ε₃)
    (h_sum : ε₁ + ε₂ + ε₃ ≤ ε) :
    eLpNorm (fun x => f x + g x + h x) 1 volume < ENNReal.ofReal ε := by
  classical
  -- First, apply the triangle inequality twice.
  have h_fg :
      eLpNorm (fun x => f x + g x) 1 volume
        ≤ eLpNorm f 1 volume + eLpNorm g 1 volume := by
    simpa using
      (eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞)) hf_meas hg_meas le_rfl)
  have h_gh :
      eLpNorm (fun x => g x + h x) 1 volume
        ≤ eLpNorm g 1 volume + eLpNorm h 1 volume := by
    simpa using
      (eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞)) hg_meas hh_meas le_rfl)
  have h_total_aux :
      eLpNorm (fun x => f x + (g x + h x)) 1 volume
        ≤ eLpNorm f 1 volume + eLpNorm (fun x => g x + h x) 1 volume := by
    have h_sum_meas : AEStronglyMeasurable (fun x => g x + h x) volume :=
      hg_meas.add hh_meas
    simpa using
      (eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞)) hf_meas h_sum_meas le_rfl)
  have h_total :
      eLpNorm (fun x => f x + g x + h x) 1 volume
        ≤ eLpNorm f 1 volume + eLpNorm (fun x => g x + h x) 1 volume := by
    have h_rewrite :
        (fun x => f x + g x + h x)
          = fun x => f x + (g x + h x) := by
      funext x; simp [add_comm, add_left_comm, add_assoc]
    simpa [h_rewrite] using h_total_aux
  have h_total_le :
      eLpNorm (fun x => f x + g x + h x) 1 volume
        ≤ eLpNorm f 1 volume + eLpNorm g 1 volume + eLpNorm h 1 volume := by
    have h_aux := add_le_add_left h_gh (eLpNorm f 1 volume)
    exact h_total.trans <| by
      simpa [add_comm, add_left_comm, add_assoc] using h_aux
  -- Each εᵢ must be positive, otherwise the inequalities `hf`, `hg`, `hh` are impossible.
  have hε₁_pos : 0 < ε₁ := by
    by_contra hle
    have h_zero : ENNReal.ofReal ε₁ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
    have : eLpNorm f 1 volume < 0 := by simp [h_zero] at hf
    exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ eLpNorm f 1 volume from bot_le)) this
  have hε₂_pos : 0 < ε₂ := by
    by_contra hle
    have h_zero : ENNReal.ofReal ε₂ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
    have : eLpNorm g 1 volume < 0 := by simp [h_zero] at hg
    exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ eLpNorm g 1 volume from bot_le)) this
  have hε₃_pos : 0 < ε₃ := by
    by_contra hle
    have h_zero : ENNReal.ofReal ε₃ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
    have : eLpNorm h 1 volume < 0 := by simp [h_zero] at hh
    exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ eLpNorm h 1 volume from bot_le)) this
  -- Combine the three individual bounds.
  have h_sum_fg :
      eLpNorm f 1 volume + eLpNorm g 1 volume
        < ENNReal.ofReal ε₁ + ENNReal.ofReal ε₂ :=
    ENNReal.add_lt_add hf hg
  have h_sum_total :
      eLpNorm f 1 volume + eLpNorm g 1 volume + eLpNorm h 1 volume
        < ENNReal.ofReal ε₁ + ENNReal.ofReal ε₂ + ENNReal.ofReal ε₃ := by
    -- Rearrange to use `ENnreal.add_lt_add` twice.
    have := ENNReal.add_lt_add h_sum_fg hh
    simpa [add_comm, add_left_comm, add_assoc]
      using this
  -- Rewrite the right-hand side using real addition.
  have h_ofReal_fg :
      ENNReal.ofReal ε₁ + ENNReal.ofReal ε₂
        = ENNReal.ofReal (ε₁ + ε₂) :=
    (ENNReal.ofReal_add (le_of_lt hε₁_pos) (le_of_lt hε₂_pos)).symm
  have h_ofReal_total :
      ENNReal.ofReal ε₁ + ENNReal.ofReal ε₂ + ENNReal.ofReal ε₃
        = ENNReal.ofReal (ε₁ + ε₂ + ε₃) := by
    have h_nonneg : 0 ≤ ε₁ + ε₂ := add_nonneg hε₁_pos.le hε₂_pos.le
    simpa [h_ofReal_fg, add_comm, add_left_comm, add_assoc]
      using (ENNReal.ofReal_add h_nonneg hε₃_pos.le).symm
  have h_target :
      eLpNorm (fun x => f x + g x + h x) 1 volume
        < ENNReal.ofReal (ε₁ + ε₂ + ε₃) := by
    refine lt_of_le_of_lt h_total_le ?_
    simpa [h_ofReal_total] using h_sum_total
  -- Use the assumption on ε₁ + ε₂ + ε₃ ≤ ε.
  have h_sum_nonneg : 0 ≤ ε₁ + ε₂ + ε₃ :=
    add_nonneg (add_nonneg hε₁_pos.le hε₂_pos.le) hε₃_pos.le
  have hε_nonneg : 0 ≤ ε := le_trans h_sum_nonneg h_sum
  have h_bound :
      ENNReal.ofReal (ε₁ + ε₂ + ε₃) ≤ ENNReal.ofReal ε :=
    (ENNReal.ofReal_le_ofReal_iff (q := ε) hε_nonneg).mpr h_sum
  exact lt_of_lt_of_le h_target h_bound

/--
**モリファイアスケールの選択 (Lemma 4.5 in the paper).**

f₀ ∈ L¹ ∩ L² で HasCompactSupport f₀ のとき、
任意の ε₁, ε₂ > 0 に対して η > 0 が存在して、
適切なモリファイア ψ_η との畳み込みが両方のノルムで ε-近似を与える。

これは論文のステップ6-7で使用される。
-/
lemma exists_mollifier_scale
    (f₀ : (Fin n → ℝ) → ℂ)
    (hf₀_compact : HasCompactSupport f₀)
    (hf₀_L1 : MemLp f₀ 1 volume)
    (hf₀_L2 : MemLp f₀ 2 volume)
    (ε₁ ε₂ : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    ∃ (η : ℝ) (hη : 0 < η) (hη_le : η ≤ 1) (ψ : (Fin n → ℝ) → ℝ),
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧
      HasCompactSupport ψ ∧
      (∫ x, ψ x = 1) ∧
      (∀ x, 0 ≤ ψ x) ∧
      tsupport ψ ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 ∧
      (let ψ_η := fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)
       let φ := fun x => ∫ y, f₀ (x - y) * ψ_η y
       eLpNorm (fun x => f₀ x - φ x) 1 volume < ENNReal.ofReal ε₁ ∧
       eLpNorm (fun x => f₀ x - φ x) 2 volume < ENNReal.ofReal ε₂) := by
  classical

  -- Step 1: Construct a basic mollifier using ContDiffBump
  -- We use a bump function supported in the unit ball
  let ψ_base : ContDiffBump (0 : Fin n → ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

  -- Step 2: The mollifier needs to be normalized so that ∫ ψ = 1
  -- For a ContDiffBump, the integral is positive and finite
  have h_integral_pos : 0 < ∫ x, ψ_base x := by
    -- Lean's bundled bump functions know their integral is positive on any
    -- open-positive measure (here, Lebesgue measure on ℝⁿ).
    simpa using
      (ContDiffBump.integral_pos (μ := (volume : Measure (Fin n → ℝ))) (f := ψ_base))

  have h_integral_finite : Integrable (fun x => ψ_base x) volume := by
    -- The bump function has compact support and is continuous, so it's integrable
    apply Continuous.integrable_of_hasCompactSupport
    · exact ψ_base.continuous
    · exact ψ_base.hasCompactSupport

  -- Define the normalization constant
  let C := ∫ x, ψ_base x
  have hC_pos : 0 < C := h_integral_pos
  have hC_ne_zero : C ≠ 0 := ne_of_gt hC_pos

  -- Normalized mollifier
  let ψ : (Fin n → ℝ) → ℝ := fun x => (1 / C) * ψ_base x

  -- Step 3: Verify properties of ψ
  have hψ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ := by
    apply ContDiff.mul
    · exact contDiff_const
    · exact ψ_base.contDiff

  have hψ_compact : HasCompactSupport ψ := by
    apply HasCompactSupport.mul_left
    exact ψ_base.hasCompactSupport

  have hψ_integral_one : ∫ x, ψ x = 1 := by
    simp only [ψ, C]
    have : ∫ x, (1 / ∫ x, ψ_base x) * ψ_base x = 1 := by
      rw [integral_const_mul]
      field_simp [ne_of_gt h_integral_pos]
    convert this using 1

  have hψ_nonneg : ∀ x, 0 ≤ ψ x := by
    intro x
    simp only [ψ]
    apply mul_nonneg
    · exact div_nonneg zero_le_one (le_of_lt hC_pos)
    · exact ψ_base.nonneg' x

  have hψ_support : tsupport ψ ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    -- The support of ψ is the same as the support of ψ_base
    -- since we're multiplying by a non-zero constant
    -- ψ_base has support in the ball of radius ψ_base.rOut = 1
    have h_subset_base :
        tsupport ψ ⊆ tsupport (fun x : Fin n → ℝ => ψ_base x) := by
      -- Scaling by a constant does not enlarge the (topological) support.
      simpa [ψ, C, Pi.mul_def] using
        (tsupport_mul_subset_right
          (f := fun _ : (Fin n → ℝ) => (1 / C))
          (g := fun x : (Fin n → ℝ) => ψ_base x))
    have h_tsupp_base :
        tsupport (fun x : Fin n → ℝ => ψ_base x) =
          Metric.closedBall (0 : Fin n → ℝ) 1 := by
      simpa using ψ_base.tsupport_eq
    exact h_subset_base.trans <| by simp [h_tsupp_base]

  -- Step 4: For f₀ with compact support in L¹ ∩ L², we can apply approximation identity
  -- The key is that for small η, the scaled mollifier ψ_η approximates the delta function
  -- and convolution with it approximates the identity operator

  -- We need to find η > 0 such that both L¹ and L² errors are small
  -- Strategy: Take ε := min(ε₁, ε₂) and find η for this ε

  set ε := min ε₁ ε₂
  have hε_pos : 0 < ε := lt_min hε₁ hε₂
  have hε_le₁ : ε ≤ ε₁ := min_le_left _ _
  have hε_le₂ : ε ≤ ε₂ := min_le_right _ _

  -- For f₀ ∈ Lp with compact support, convolution with mollifier converges in Lp
  -- This is the approximation identity property
  -- The convergence is: ‖f₀ - f₀ * ψ_η‖_p → 0 as η → 0

  -- We can use the existing mathlib4 lemma for smooth approximation
  -- Since f₀ has compact support and is in L¹ ∩ L², we can approximate it

  -- Choose η small enough (existence follows from approximation identity)
  -- For the detailed proof, we would use:
  -- 1. Continuity of translation in Lp: ‖τ_y f - f‖_p → 0 as y → 0
  -- 2. Dominated convergence for the convolution integral
  -- 3. The fact that ψ_η concentrates near 0 as η → 0

  -- The technical details require ~80 more lines using mathlib4's measure theory
  -- For now, we assert the existence of such η

  have h_exists_eta : ∃ η_min > 0, ∀ η, 0 < η → η < η_min →
      ∃ φ : (Fin n → ℝ) → ℂ,
        (let ψ_η := fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)
         φ = fun x => ∫ y, f₀ (x - y) * ψ_η y) ∧
        eLpNorm (fun x => f₀ x - φ x) 1 volume < ENNReal.ofReal ε ∧
        eLpNorm (fun x => f₀ x - φ x) 2 volume < ENNReal.ofReal ε := by
    -- This follows from the approximation identity theorem for Lp spaces
    --
    -- Strategy:
    -- 1. For f₀ ∈ L¹ with compact support, we can use mollifier_compactSupport_Lp_approx
    --    to get a smooth approximation in L¹ norm
    -- 2. Similarly for L² norm
    -- 3. We need to show that this approximation can be realized as a convolution
    --    with the scaled mollifier ψ_η for small enough η
    --
    -- Key facts:
    -- - f₀ has compact support ⇒ convolution is well-defined
    -- - ψ is normalized (∫ ψ = 1) ⇒ ψ_η is an approximation to identity
    -- - ψ is smooth with compact support ⇒ convolution preserves Lp
    -- - As η → 0, the convolution f₀ * ψ_η → f₀ in Lp norm (approximation identity)

    -- For f₀ ∈ L¹ ∩ L², both with compact support, we use the fact that
    -- convolution with mollifiers converges in both L¹ and L² norms

    -- Step 1: Show that f₀ is continuous (compact support + L² ⇒ bounded, but we need more)
    -- Actually, we don't need f₀ to be continuous. The approximation identity
    -- works for all Lp functions with 1 ≤ p < ∞

    -- Step 2: Apply approximation identity for L¹
    -- From measure theory: for f ∈ Lp with 1 ≤ p < ∞, and mollifier ψ_η,
    -- we have ‖f - f * ψ_η‖_p → 0 as η → 0

    -- Step 3: Since convergence → 0, there exists η small enough that the error is < ε

    -- The technical details involve:
    -- - Showing the convolution is well-defined (use compact support)
    -- - Showing the convolution converges (use approximation identity for Lp)
    -- - Finding a uniform η that works for both L¹ and L²

    -- We'll construct the proof in several steps:
    -- 1. Define the scaled mollifier ψ_η
    -- 2. Define the convolution φ_η = f₀ * ψ_η
    -- 3. Show convergence in L¹ and L² as η → 0
    -- 4. Extract an η that works for the given ε

    -- First, we need some auxiliary lemmas about convolution with mollifiers

    -- Lemma: For f ∈ Lp with compact support and normalized mollifier ψ,
    -- the convolution f * ψ_η converges to f in Lp norm as η → 0
    have h_conv_L1 : ∀ ε' > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
        eLpNorm (fun x => f₀ x -
          ∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) 1 volume
            < ENNReal.ofReal ε' := by
      intro ε' hε'
      -- Strategy: Approximate f₀ by a continuous function, then use smooth approximation
      --
      -- Step 1: Find a continuous function g that approximates f₀ in L¹
      -- Since f₀ ∈ L¹ with compact support, we can approximate it by continuous functions
      -- with compact support (this uses the density of C_c in L¹)

      -- For simplicity, we'll use the fact that we can make the convolution
      -- arbitrarily close in L¹ norm by choosing η small

      -- The key observation is:
      -- ‖f₀ - f₀ * ψ_η‖₁ ≤ ‖f₀ - g‖₁ + ‖g - g * ψ_η‖₁ + ‖g * ψ_η - f₀ * ψ_η‖₁
      -- where g is continuous with compact support

      -- Step 1a: Get a continuous approximation
      -- We use that continuous compactly supported functions are dense in L¹
      have h_exists_cont : ∃ g : (Fin n → ℝ) → ℂ,
          Continuous g ∧ HasCompactSupport g ∧
          eLpNorm (fun x => f₀ x - g x) 1 volume < ENNReal.ofReal (ε' / 4) := by
        -- Apply the density theorem for continuous compactly supported functions
        have hε'_fourth : 0 < ε' / 4 := by linarith
        obtain ⟨g, hg_cont, hg_compact, hg_memLp, hg_close⟩ :=
          continuous_compactSupport_dense_Lp 1 (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
            f₀ hf₀_L1 hε'_fourth
        use g
        exact ⟨hg_cont, hg_compact, hg_close⟩

      obtain ⟨g, hg_cont, hg_compact, hg_approx⟩ := h_exists_cont

      -- Step 1b: For the continuous function g, find a smooth approximation
      -- Apply mollifier_compactSupport_Lp_approx to g
      have h_smooth_exists := mollifier_compactSupport_Lp_approx 1 le_rfl g hg_cont hg_compact
        (by linarith : 0 < ε' / 4)
      obtain ⟨φ_g, hφ_g_smooth, hφ_g_close, _⟩ := h_smooth_exists

      -- Step 2: For the goal, we need to estimate the convolution
      -- The key insight is that for any fixed functions, we can choose δ small enough
      -- We appeal to the quantitative convergence result for mollifiers.

      have hψ_AI : IsApproximateIdentity ψ :=
        ⟨hψ_smooth, hψ_compact, by simpa using hψ_integral_one, hψ_nonneg, hψ_support⟩

      have hg_integrable : Integrable g volume :=
        hg_cont.integrable_of_hasCompactSupport hg_compact

      obtain ⟨δ₀, hδ₀_pos, hδ₀_bound⟩ :=
        (mollifier_converges_L1_compactSupport g ψ hg_integrable hg_compact hψ_AI)
          (ε' / 4) (by
            have : 0 < ε' / 4 := by linarith
            exact this)

      use min δ₀ 1
      constructor
      · exact lt_min hδ₀_pos (by norm_num)
      · intro η hη_pos hη_lt
        have hη_lt_δ₀ : η < δ₀ := lt_of_lt_of_le hη_lt (min_le_left _ _)
        have hη_lt_one : η < 1 := lt_of_lt_of_le hη_lt (min_le_right _ _)
        -- We need to show that the convolution is close to f₀
        -- Strategy: Use triangle inequality with intermediate g
        --
        -- ‖f₀ - f₀*ψ_η‖₁ ≤ ‖f₀ - g‖₁ + ‖g - g*ψ_η‖₁ + ‖g*ψ_η - f₀*ψ_η‖₁

        -- Step 1: We already have ‖f₀ - g‖₁ < ε'/4 from hg_approx

        -- Step 2: For continuous functions with compact support,
        -- convolution with a mollifier converges: ‖g - g*ψ_η‖₁ → 0 as η → 0.
        -- Since η < min δ₀ 1, in particular η < 1, so we obtain a quantitative bound.
        have h_g_conv_bound_integral :
            eLpNorm (fun x => g x - ∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ))
              1 volume < ENNReal.ofReal (ε' / 4) := by
          -- Apply the quantitative L¹ convergence of mollifiers for continuous data.
          have := hδ₀_bound η hη_pos hη_lt_δ₀
          simpa [scaledMollifier] using this

        -- Step 3: Convolution is linear, so
        -- ‖g*ψ_η - f₀*ψ_η‖₁ = ‖(g - f₀)*ψ_η‖₁ ≤ ‖g - f₀‖₁ · ‖ψ_η‖₁
        -- by Young's inequality
        have h_conv_diff_bound_integral :
            eLpNorm (fun x =>
              (∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) -
              (∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)))
              1 volume < ENNReal.ofReal (ε' / 4) := by
          classical
          have hg_minus_f0_lt :
              eLpNorm (fun x => g x - f₀ x) 1 volume < ENNReal.ofReal (ε' / 4) := by
            have h_symm :
                eLpNorm (fun x => g x - f₀ x) 1 volume =
                  eLpNorm (fun x => f₀ x - g x) 1 volume := by
              have hneg_pointwise :
                  (fun x => g x - f₀ x) = fun x => -(f₀ x - g x) := by
                funext x
                simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
              have hneg_ae :
                  (fun x => g x - f₀ x) =ᵐ[volume] fun x => -(f₀ x - g x) :=
                Filter.Eventually.of_forall <| by
                  intro x
                  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
              have hneg_eq :=
                eLpNorm_congr_ae (μ := volume) (p := (1 : ℝ≥0∞)) hneg_ae
              have hneg_symm :=
                eLpNorm_neg (f := fun x => f₀ x - g x) (p := (1 : ℝ≥0∞)) (μ := volume)
              exact hneg_eq.trans hneg_symm
            simpa [h_symm] using hg_approx
          have hf₀_integrable : Integrable f₀ volume := by
            simpa [memLp_one_iff_integrable] using hf₀_L1
          have h_bound :=
            mollifier_convolution_diff_L1
              (g := g) (f₀ := f₀) (ψ := ψ)
              hg_integrable hf₀_integrable hψ_compact hψ_nonneg hψ_integral_one
          have h_conv_diff_le := h_bound η hη_pos hη_lt_one
          exact lt_of_le_of_lt h_conv_diff_le hg_minus_f0_lt

        -- Step 4: Combine the three bounds using the auxiliary inequality.
        set ψη : (Fin n → ℝ) → ℝ := fun y => (η ^ n : ℝ)⁻¹ * ψ (fun i => y i / η)
        let ψηC : (Fin n → ℝ) → ℂ := fun y => (ψη y : ℝ)
        let conv_g : (Fin n → ℝ) → ℂ :=
          fun x => ∫ y, g (x - y) * ψηC y
        let conv_f₀ : (Fin n → ℝ) → ℂ :=
          fun x => ∫ y, f₀ (x - y) * ψηC y
        have hη_ne_zero : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
        have hψη_eq :
            ψη =
              (fun _ : Fin n → ℝ => (η ^ n : ℝ)⁻¹) * fun y : Fin n → ℝ => ψ (η⁻¹ • y) := by
          funext y
          have hfun :
              (fun i => y i / η) = fun i => (η⁻¹ : ℝ) * y i := by
            funext i
            simp [div_eq_mul_inv, mul_comm]
          have hsmul :
              (η⁻¹ • y) = fun i => (η⁻¹ : ℝ) * y i := by
            funext i
            simp [Pi.smul_apply]
          simp [ψη, hfun, hsmul, Pi.mul_apply]
        have hψη_compact : HasCompactSupport ψη := by
          have h_comp : HasCompactSupport (fun y : Fin n → ℝ => ψ ((1 / η) • y)) := by
            simpa [one_div] using
              (HasCompactSupport.comp_smul (α := Fin n → ℝ) (β := ℝ) (G₀ := ℝ)
                hψ_compact (inv_ne_zero hη_ne_zero))
          have h_mul :=
            HasCompactSupport.mul_left
              (f := fun _ : Fin n → ℝ => (η ^ n : ℝ)⁻¹)
              (f' := fun y : Fin n → ℝ => ψ ((1 / η) • y)) h_comp
          simpa [hψη_eq] using h_mul
        have hψη_cont : Continuous ψη := by
          have h_const : Continuous fun _ : Fin n → ℝ => (η ^ n : ℝ)⁻¹ :=
            continuous_const
          have h_scale : Continuous fun y : Fin n → ℝ => (1 / η : ℝ) • y :=
            continuous_const_smul (1 / η : ℝ)
          have h_comp : Continuous fun y : Fin n → ℝ => ψ ((1 / η) • y) :=
            hψ_smooth.continuous.comp h_scale
          simpa [hψη_eq] using h_const.mul h_comp
        have hψηC_compact : HasCompactSupport ψηC := by
          classical
          rw [hasCompactSupport_iff_eventuallyEq] at hψη_compact ⊢
          exact hψη_compact.mono (by intro x hx; simp [ψηC, hx])
        have hψηC_cont : Continuous ψηC := by
          simpa [ψηC] using (continuous_ofReal.comp hψη_cont)
        have hη_pow_ne_zero : (η ^ n : ℝ) ≠ 0 := by
          simpa using pow_ne_zero n hη_ne_zero
        have hψηC_rewrite :
            ψηC = fun y : Fin n → ℝ => ((↑η : ℂ) ^ n)⁻¹ * ↑(ψ fun i => y i / η) := by
          funext y
          simp [ψηC, ψη, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
            hη_pow_ne_zero, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        have hg_locInt : LocallyIntegrable g volume :=
          hg_integrable.locallyIntegrable
        have hf₀_integrable : Integrable f₀ volume := by
          simpa [memLp_one_iff_integrable] using hf₀_L1
        have hf₀_locInt : LocallyIntegrable f₀ volume :=
          hf₀_integrable.locallyIntegrable
        have h_conv_g_eq :
            conv_g =
              fun x => (g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψηC) x := by
          funext x
          have hconv :=
            convolution_mul_swap (μ := volume) (G := Fin n → ℝ)
              (f := g) (g := ψηC) (x := x)
          simpa [conv_g, ψηC, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using hconv.symm
        have h_conv_f₀_eq :
            conv_f₀ =
              fun x => (f₀ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψηC) x := by
          funext x
          have hconv :=
            convolution_mul_swap (μ := volume) (G := Fin n → ℝ)
              (f := f₀) (g := ψηC) (x := x)
          simpa [conv_f₀, ψηC, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using hconv.symm
        have h_conv_g_cont : Continuous conv_g := by
          have := hψηC_compact.continuous_convolution_right
            (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
            hg_locInt hψηC_cont
          simpa [conv_g, h_conv_g_eq] using this
        have h_conv_f₀_cont : Continuous conv_f₀ := by
          have := hψηC_compact.continuous_convolution_right
            (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
            hf₀_locInt hψηC_cont
          simpa [conv_f₀, h_conv_f₀_eq] using this
        have h_conv_f₀_integrand :
            conv_f₀ =
              fun x : Fin n → ℝ =>
                ∫ y, f₀ (x - y) * (((↑η : ℂ) ^ n)⁻¹ * ↑(ψ fun i => y i / η)) := by
          funext x
          simp [conv_f₀, hψηC_rewrite]
        have hf₀_aesm : AEStronglyMeasurable f₀ volume :=
          hf₀_L1.aestronglyMeasurable
        have hf_diff_meas :
            AEStronglyMeasurable (fun x => f₀ x - g x) volume :=
          aestronglyMeasurable_sub_of_aesm_continuous hf₀_aesm hg_cont
        have hg_diff_meas :
            AEStronglyMeasurable (fun x => g x - conv_g x) volume :=
          aestronglyMeasurable_sub_of_continuous hg_cont h_conv_g_cont.aestronglyMeasurable
        have hh_diff_meas :
            AEStronglyMeasurable (fun x => conv_g x - conv_f₀ x) volume :=
          h_conv_g_cont.aestronglyMeasurable.sub h_conv_f₀_cont.aestronglyMeasurable
        have h_g_conv_bound :
            eLpNorm (fun x => g x - conv_g x) 1 volume < ENNReal.ofReal (ε' / 4) := by
          simpa [conv_g, ψηC, ψη, Pi.mul_apply, Pi.smul_apply, one_div, div_eq_mul_inv,
            mul_comm, mul_left_comm, mul_assoc, integral_const_mul] using
            h_g_conv_bound_integral
        have h_conv_diff_bound :
            eLpNorm (fun x => conv_g x - conv_f₀ x) 1 volume < ENNReal.ofReal (ε' / 4) := by
          simpa [conv_g, conv_f₀, ψηC, ψη, sub_eq_add_neg, add_comm, add_left_comm,
            add_assoc, Pi.mul_apply, Pi.smul_apply, one_div, div_eq_mul_inv, mul_comm,
            mul_left_comm, mul_assoc]
            using h_conv_diff_bound_integral
        have h_triangle :=
          triangle_inequality_aux
            (f := fun x => f₀ x - g x)
            (g := fun x => g x - conv_g x)
            (h := fun x => conv_g x - conv_f₀ x)
            (hf_meas := hf_diff_meas)
            (hg_meas := hg_diff_meas)
            (hh_meas := hh_diff_meas)
            (ε := ε') (ε₁ := ε' / 4) (ε₂ := ε' / 4) (ε₃ := ε' / 4)
            hg_approx h_g_conv_bound h_conv_diff_bound (by nlinarith)
        have h_decomp :
            (fun x => f₀ x - conv_f₀ x)
              = fun x =>
                (f₀ x - g x)
                + (g x - conv_g x)
                + (conv_g x - conv_f₀ x) := by
          funext x
          simp [conv_g, conv_f₀, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        simpa [conv_g, h_conv_f₀_integrand, h_decomp]
          using h_triangle

    have h_conv_L2 : ∀ ε' > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
        eLpNorm (fun x => f₀ x -
          ∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) 2 volume
            < ENNReal.ofReal ε' := by
      intro ε' hε'
      -- Similar strategy to L¹ case, but for L²
      -- Step 1a: Get a continuous approximation in L²
      have h_exists_cont : ∃ g : (Fin n → ℝ) → ℂ,
          Continuous g ∧ HasCompactSupport g ∧
          eLpNorm (fun x => f₀ x - g x) 2 volume < ENNReal.ofReal (ε' / 4) := by
        -- Apply the density theorem for continuous compactly supported functions
        have hε'_fourth : 0 < ε' / 4 := by linarith
        obtain ⟨g, hg_cont, hg_compact, hg_memLp, hg_close⟩ :=
          continuous_compactSupport_dense_Lp (2 : ℝ≥0∞) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
            f₀ hf₀_L2 hε'_fourth
        use g
        exact ⟨hg_cont, hg_compact, hg_close⟩

      obtain ⟨g, hg_cont, hg_compact, hg_approx⟩ := h_exists_cont

      -- Step 1b: For the continuous function g, find a smooth approximation in L²
      have h_smooth_exists := mollifier_compactSupport_Lp_approx (2 : ℝ≥0∞)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) g hg_cont hg_compact (by linarith : 0 < ε' / 4)
      obtain ⟨φ_g, hφ_g_smooth, hφ_g_close, _⟩ := h_smooth_exists

      have hψ_AI : IsApproximateIdentity ψ :=
        ⟨hψ_smooth, hψ_compact, by simpa using hψ_integral_one, hψ_nonneg, hψ_support⟩

      -- Step 2: Obtain quantitative convergence from the L² mollifier theorem
      obtain ⟨δ₀, hδ₀_pos, hδ₀_bound⟩ :=
        (mollifier_converges_L2_compactSupport f₀ ψ hf₀_L2 hf₀_compact hψ_AI) ε' hε'

      use min δ₀ 1
      constructor
      · exact lt_min hδ₀_pos (by norm_num)
      · intro η hη_pos hη_lt
        have hη_lt_δ₀ : η < δ₀ := lt_of_lt_of_le hη_lt (min_le_left _ _)
        have h_bound := hδ₀_bound η hη_pos hη_lt_δ₀
        -- The integral appearing in `hδ₀_bound` matches the goal after unfolding
        -- the definition of `scaledMollifier`.
        simpa [scaledMollifier] using h_bound

    -- Now we can prove the main result
    -- Since both h_conv_L1 and h_conv_L2 give us convergence,
    -- we can find a common η that works for both

    -- Apply h_conv_L1 with ε
    obtain ⟨δ₁, hδ₁_pos, h₁⟩ := h_conv_L1 ε hε_pos

    -- Apply h_conv_L2 with ε
    obtain ⟨δ₂, hδ₂_pos, h₂⟩ := h_conv_L2 ε hε_pos

    -- Take η_min to be the minimum of δ₁ and δ₂
    use min δ₁ δ₂
    constructor
    · exact lt_min hδ₁_pos hδ₂_pos
    · intro η hη_pos hη_lt
      -- Define the convolution
      let ψ_η : (Fin n → ℝ) → ℝ := fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)
      let φ : (Fin n → ℝ) → ℂ := fun x => ∫ y, f₀ (x - y) * (↑(ψ_η y) : ℂ)
      use φ
      constructor
      · -- Show φ equals the convolution
        rfl
      constructor
      · -- L¹ bound
        have hη_lt₁ : η < δ₁ := lt_of_lt_of_le hη_lt (min_le_left _ _)
        have := h₁ η hη_pos hη_lt₁
        convert this using 2
      · -- L² bound
        have hη_lt₂ : η < δ₂ := lt_of_lt_of_le hη_lt (min_le_right _ _)
        have := h₂ η hη_pos hη_lt₂
        convert this using 2

  -- Extract a specific η from the existence result
  obtain ⟨η_min, hη_min_pos, h_forall_eta⟩ := h_exists_eta
  -- Choose η = min(η_min/2, 1/2) to ensure η ≤ 1
  set η := min (η_min / 2) (1 / 2) with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    apply lt_min
    · exact half_pos hη_min_pos
    · norm_num
  have hη_le_one : η ≤ 1 := by
    rw [hη_def]
    calc min (η_min / 2) (1 / 2)
        ≤ 1 / 2 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hη_lt : η < η_min := by
    rw [hη_def]
    calc min (η_min / 2) (1 / 2)
        ≤ η_min / 2 := min_le_left _ _
      _ < η_min := half_lt_self hη_min_pos

  obtain ⟨φ, hφ_def, hφ_L1, hφ_L2⟩ := h_forall_eta η hη_pos hη_lt

  -- Step 5: Package the result
  use η, hη_pos, hη_le_one, ψ

  constructor
  · exact hψ_smooth
  constructor
  · exact hψ_compact
  constructor
  · exact hψ_integral_one
  constructor
  · exact hψ_nonneg
  constructor
  · exact hψ_support
  · -- Show the approximation properties
    -- Since ε = min(ε₁, ε₂), we have ε ≤ ε₁ and ε ≤ ε₂
    -- Thus ENNReal.ofReal ε ≤ ENNReal.ofReal ε₁ and ENNReal.ofReal ε ≤ ENNReal.ofReal ε₂
    have hε₁_bound : ENNReal.ofReal ε ≤ ENNReal.ofReal ε₁ := by
      apply ENNReal.ofReal_le_ofReal
      exact hε_le₁
    have hε₂_bound : ENNReal.ofReal ε ≤ ENNReal.ofReal ε₂ := by
      apply ENNReal.ofReal_le_ofReal
      exact hε_le₂
    -- The goal has let-bound variables ψ_η and φ
    -- We need to show that our φ satisfies the bounds
    -- Since hφ_def states that φ equals the convolution,
    -- and hφ_L1, hφ_L2 give us the required bounds with ε < min(ε₁, ε₂),
    -- we can weaken these to ε₁ and ε₂
    -- Technical: This requires careful handling of let-bound variables
    -- and definitional equality, which can cause timeout issues
    have hφ_L1' :
        eLpNorm (fun x => f₀ x - φ x) 1 volume < ENNReal.ofReal ε₁ :=
      lt_of_lt_of_le hφ_L1 hε₁_bound
    have hφ_L2' :
        eLpNorm (fun x => f₀ x - φ x) 2 volume < ENNReal.ofReal ε₂ :=
      lt_of_lt_of_le hφ_L2 hε₂_bound
    have h_pair :
        eLpNorm (fun x => f₀ x - φ x) 1 volume < ENNReal.ofReal ε₁ ∧
        eLpNorm (fun x => f₀ x - φ x) 2 volume < ENNReal.ofReal ε₂ :=
      ⟨hφ_L1', hφ_L2'⟩
    simpa [hφ_def] using h_pair

/--
**切り詰め→畳み込みの統合補題.**

論文のステップ4-8を一つの補題にまとめたもの。
R を先に固定し、f を B_R で切り詰めてから畳み込むことで、
φ のサポートが B_{R+3} に収まることを保証する。

これにより、論文の正しい順序（R を先に決定→δ を選択）を実現できる。
-/
lemma cutoff_L1_bound
    (f : (Fin n → ℝ) → ℂ) (f_cut : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 volume)
    (χ : (Fin n → ℝ) → ℝ)
    (R ε_tail₁ : ℝ)
    (hχ_nonneg : ∀ x, 0 ≤ χ x)
    (hχ_le_one : ∀ x, χ x ≤ 1)
    (hf_cut_def : f_cut = fun x => (χ x : ℂ) * f x)
    (h_diff_zero_inside : ∀ {x : Fin n → ℝ}, ‖x‖ ≤ R → f x - f_cut x = 0)
    (hf_tail_L1 :
      ∫ x, ‖f x‖ ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ε_tail₁)
    (htail₁ : 0 < ε_tail₁) :
    eLpNorm (fun x => f x - f_cut x) 1 volume ≤ ENNReal.ofReal ε_tail₁ := by
  classical
  let tail : Set (Fin n → ℝ) := {x | R ≤ ‖x‖}
  have h_tail_meas : MeasurableSet tail :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have h_pointwise_le :
      ∀ x,
        ‖f x - f_cut x‖ₑ
          ≤ Set.indicator tail (fun x => ‖f x‖ₑ) x := by
    intro x
    by_cases hx : R ≤ ‖x‖
    · have h_abs_nonneg : 0 ≤ 1 - χ x := by
        have := hχ_le_one x
        have hχx_nonneg := hχ_nonneg x
        linarith
      have h_abs_le_one : 1 - χ x ≤ 1 := by
        have hχx_nonneg := hχ_nonneg x
        linarith
      have h_norm_eq : ‖f x - f_cut x‖ = (1 - χ x) * ‖f x‖ := by
        have hfactor : f x - f_cut x = f x * (1 - (χ x : ℂ)) := by
          have := (mul_sub (f x) (1 : ℂ) (χ x : ℂ))
          simpa [hf_cut_def, one_mul, mul_comm, mul_left_comm] using this.symm
        have hnormχ : ‖1 - (χ x : ℂ)‖ = |1 - χ x| := by
          simpa [Complex.ofReal_sub]
            using (RCLike.norm_ofReal (K := ℂ) (1 - χ x))
        have h_abs : |1 - χ x| = 1 - χ x := abs_of_nonneg h_abs_nonneg
        calc
          ‖f x - f_cut x‖
              = ‖f x * (1 - (χ x : ℂ))‖ := by simp [hfactor]
          _ = ‖f x‖ * ‖1 - (χ x : ℂ)‖ := norm_mul _ _
          _ = ‖f x‖ * |1 - χ x| := by simp [hnormχ]
          _ = (1 - χ x) * ‖f x‖ := by simp [h_abs, mul_comm]
      have h_mul_le : (1 - χ x) * ‖f x‖ ≤ ‖f x‖ := by
        have hnorm_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
        have := mul_le_mul_of_nonneg_right h_abs_le_one hnorm_nonneg
        simpa [one_mul] using this
      have h_indicator :
          Set.indicator tail (fun x => ‖f x‖ₑ) x = ‖f x‖ₑ := by
        simp [tail, hx, ofReal_norm_eq_enorm]
      have h_le :
          ENNReal.ofReal ((1 - χ x) * ‖f x‖)
            ≤ ENNReal.ofReal ‖f x‖ :=
        ENNReal.ofReal_le_ofReal h_mul_le
      have h_norm_eq_enorm :
          ‖f x - f_cut x‖ₑ = ENNReal.ofReal ((1 - χ x) * ‖f x‖) := by
        have := congrArg ENNReal.ofReal h_norm_eq
        simpa [ofReal_norm_eq_enorm] using this
      simpa [h_norm_eq_enorm, h_indicator, ofReal_norm_eq_enorm]
        using h_le
    · have hx_lt : ‖x‖ < R := lt_of_not_ge hx
      have hx_not_tail : x ∉ tail := by
        intro hx_mem
        exact hx ((hx_mem : R ≤ ‖x‖))
      have h_zero : f x - f_cut x = 0 := h_diff_zero_inside (le_of_lt hx_lt)
      simp [tail, hx_not_tail, h_zero, ofReal_norm_eq_enorm]
  have h_lintegral_le :
      ∫⁻ x, ‖f x - f_cut x‖ₑ ∂volume
        ≤ ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ) x ∂volume := by
    refine MeasureTheory.lintegral_mono_ae ?_
    exact Filter.Eventually.of_forall h_pointwise_le
  have h_indicator_eq :
      ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ) x ∂volume
        = ∫⁻ x in tail, ‖f x‖ₑ ∂volume := by
    classical
    simpa [tail]
      using
        (MeasureTheory.lintegral_indicator
          (μ := volume) (hs := h_tail_meas)
          (f := fun x => ‖f x‖ₑ))
  have hf_integrable : Integrable f volume :=
    (memLp_one_iff_integrable).1 hf_L1
  have hf_restrict_integrable : Integrable f (volume.restrict tail) :=
    hf_integrable.restrict (s := tail)
  have h_tail_lintegral_eq :
      ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict tail)
        = ENNReal.ofReal (∫ x, ‖f x‖ ∂(volume.restrict tail)) := by
    have h_int : Integrable (fun x => ‖f x‖) (volume.restrict tail) :=
      hf_restrict_integrable.norm
    have h_nonneg : 0 ≤ᵐ[volume.restrict tail] fun x => ‖f x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    simpa [ofReal_norm_eq_enorm]
      using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg).symm
  have h_tail_lt :
      ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict tail)
        < ENNReal.ofReal ε_tail₁ := by
    have hpos : 0 < ε_tail₁ := htail₁
    have h_ofReal_lt :
        ENNReal.ofReal (∫ x, ‖f x‖ ∂(volume.restrict tail))
          < ENNReal.ofReal ε_tail₁ :=
      (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by simpa [tail] using hf_tail_L1)
    simpa [h_tail_lintegral_eq] using h_ofReal_lt
  have h_tail_le :
      ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict tail)
        ≤ ENNReal.ofReal ε_tail₁ := le_of_lt h_tail_lt
  have h_le_indicator :
      eLpNorm (fun x => f x - f_cut x) 1 volume
        ≤ ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ) x ∂volume := by
    simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      using h_lintegral_le
  calc
    eLpNorm (fun x => f x - f_cut x) 1 volume
        ≤ ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ) x ∂volume :=
          h_le_indicator
    _ = ∫⁻ x in tail, ‖f x‖ₑ ∂volume := h_indicator_eq
    _ = ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict tail) := rfl
    _ ≤ ENNReal.ofReal ε_tail₁ := h_tail_le

lemma cutoff_L2_bound
    (f : (Fin n → ℝ) → ℂ) (f_cut : (Fin n → ℝ) → ℂ)
    (χ : (Fin n → ℝ) → ℝ)
    (R ε_tail₂ : ℝ)
    (hχ_nonneg : ∀ x, 0 ≤ χ x)
    (hχ_le_one : ∀ x, χ x ≤ 1)
    (hf_cut_def : f_cut = fun x => (χ x : ℂ) * f x)
    (h_diff_zero_inside : ∀ {x : Fin n → ℝ}, ‖x‖ ≤ R → f x - f_cut x = 0)
    (hf_tail_L2 :
      eLpNorm (fun x => f x) 2 (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖})
        < ENNReal.ofReal ε_tail₂) :
    eLpNorm (fun x => f x - f_cut x) 2 volume ≤ ENNReal.ofReal ε_tail₂ := by
  classical
  let tail : Set (Fin n → ℝ) := {x | R ≤ ‖x‖}
  have h_tail_meas : MeasurableSet tail :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have h_pointwise_le :
      ∀ x,
        ‖f x - f_cut x‖ₑ
          ≤ Set.indicator tail (fun x => ‖f x‖ₑ) x := by
    intro x
    by_cases hx : R ≤ ‖x‖
    · have h_abs_nonneg : 0 ≤ 1 - χ x := by
        have := hχ_le_one x
        have hχx_nonneg := hχ_nonneg x
        linarith
      have h_abs_le_one : 1 - χ x ≤ 1 := by
        have hχx_nonneg := hχ_nonneg x
        linarith
      have h_norm_eq : ‖f x - f_cut x‖ = (1 - χ x) * ‖f x‖ := by
        have hfactor : f x - f_cut x = f x * (1 - (χ x : ℂ)) := by
          have := (mul_sub (f x) (1 : ℂ) (χ x : ℂ))
          simpa [hf_cut_def, one_mul, mul_comm, mul_left_comm] using this.symm
        have hnormχ : ‖1 - (χ x : ℂ)‖ = |1 - χ x| := by
          simpa [Complex.ofReal_sub]
            using (RCLike.norm_ofReal (K := ℂ) (1 - χ x))
        have h_abs : |1 - χ x| = 1 - χ x := abs_of_nonneg h_abs_nonneg
        calc
          ‖f x - f_cut x‖
              = ‖f x * (1 - (χ x : ℂ))‖ := by simp [hfactor]
          _ = ‖f x‖ * ‖1 - (χ x : ℂ)‖ := norm_mul _ _
          _ = ‖f x‖ * |1 - χ x| := by simp [hnormχ]
          _ = (1 - χ x) * ‖f x‖ := by simp [h_abs, mul_comm]
      have h_mul_le : (1 - χ x) * ‖f x‖ ≤ ‖f x‖ := by
        have hnorm_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
        have := mul_le_mul_of_nonneg_right h_abs_le_one hnorm_nonneg
        simpa [one_mul] using this
      have h_indicator :
          Set.indicator tail (fun x => ‖f x‖ₑ) x = ‖f x‖ₑ := by
        simp [tail, hx, ofReal_norm_eq_enorm]
      have h_le :
          ENNReal.ofReal ((1 - χ x) * ‖f x‖)
            ≤ ENNReal.ofReal ‖f x‖ :=
        ENNReal.ofReal_le_ofReal h_mul_le
      have h_norm_eq_enorm :
          ‖f x - f_cut x‖ₑ = ENNReal.ofReal ((1 - χ x) * ‖f x‖) := by
        have := congrArg ENNReal.ofReal h_norm_eq
        simpa [ofReal_norm_eq_enorm] using this
      simpa [h_norm_eq_enorm, h_indicator, ofReal_norm_eq_enorm]
        using h_le
    · have hx_lt : ‖x‖ < R := lt_of_not_ge hx
      have hx_not_tail : x ∉ tail := by
        intro hx_mem
        exact hx ((hx_mem : R ≤ ‖x‖))
      have h_zero : f x - f_cut x = 0 := h_diff_zero_inside (le_of_lt hx_lt)
      simp [tail, hx_not_tail, h_zero, ofReal_norm_eq_enorm]
  have h_pointwise_sq :
      ∀ x,
        ‖f x - f_cut x‖ₑ ^ (2 : ℝ)
          ≤ Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x := by
    intro x
    have hpow := ENNReal.rpow_le_rpow (h_pointwise_le x) (by norm_num : 0 ≤ (2 : ℝ))
    have h_indicator_sq :
        Set.indicator tail (fun x => ‖f x‖ₑ) x ^ (2 : ℝ)
          = Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x := by
      by_cases hx : R ≤ ‖x‖
      · simp [tail, hx, ofReal_norm_eq_enorm]
      · simp [tail, hx, ofReal_norm_eq_enorm]
    simpa [h_indicator_sq]
      using hpow
  have h_lintegral_le :
      ∫⁻ x, ‖f x - f_cut x‖ₑ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume := by
    refine MeasureTheory.lintegral_mono_ae ?_
    exact Filter.Eventually.of_forall h_pointwise_sq
  have h_indicator_eq :
      ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume
        = ∫⁻ x in tail, ‖f x‖ₑ ^ (2 : ℝ) ∂volume := by
    classical
    simpa [tail]
      using
        (MeasureTheory.lintegral_indicator
          (μ := volume) (hs := h_tail_meas)
          (f := fun x => ‖f x‖ₑ ^ (2 : ℝ)))
  have h_le_indicator :
      (∫⁻ x, ‖f x - f_cut x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
        ≤ (∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume)
            ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow h_lintegral_le (by positivity : 0 ≤ 1 / (2 : ℝ))
  have h_eLp_diff :
      eLpNorm (fun x => f x - f_cut x) 2 volume
        = (∫⁻ x, ‖f x - f_cut x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa [ENNReal.toReal_ofNat, one_div]
      using
        (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (p := (2 : ℝ≥0∞))
            two_ne_zero ENNReal.ofNat_ne_top
            (f := fun x => f x - f_cut x) (μ := volume))
  have h_eLp_tail :
      eLpNorm (fun x => f x) 2 (volume.restrict tail)
        = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume.restrict tail)) ^ (1 / (2 : ℝ)) := by
    simpa [ENNReal.toReal_ofNat, one_div]
      using
        (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (p := (2 : ℝ≥0∞))
            two_ne_zero ENNReal.ofNat_ne_top
            (f := fun x => f x) (μ := volume.restrict tail))
  have h_le_indicator' :
      eLpNorm (fun x => f x - f_cut x) 2 volume
        ≤ (∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume)
            ^ (1 / (2 : ℝ)) := by
    simpa [h_eLp_diff] using h_le_indicator
  have h_indicator_eq_pow :
      (∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume)
            ^ (1 / (2 : ℝ))
        = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume.restrict tail)) ^ (1 / (2 : ℝ)) :=
    congrArg (fun t => t ^ (1 / (2 : ℝ))) h_indicator_eq
  have h_le_indicator'' :
      eLpNorm (fun x => f x - f_cut x) 2 volume
        ≤ eLpNorm (fun x => f x) 2 (volume.restrict tail) := by
    calc
      eLpNorm (fun x => f x - f_cut x) 2 volume
          ≤ (∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume)
              ^ (1 / (2 : ℝ)) := h_le_indicator'
      _ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume.restrict tail)) ^ (1 / (2 : ℝ)) := by
            simpa using h_indicator_eq_pow
      _ = eLpNorm (fun x => f x) 2 (volume.restrict tail) := by
            simp [h_eLp_tail, one_div]
  exact h_le_indicator''.trans (le_of_lt hf_tail_L2)

lemma cutoff_then_convolve_Lp
    (hn : 0 < n)
    (f : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 volume)
    (hf_L2 : MemLp f 2 volume)
    (R : ℝ) (hR : 0 < R)
    {ε ε_cut₁ ε_cut₂ ε_tail₁ ε_tail₂ : ℝ}
    (hε : 0 < ε)
    (hcut₁ : 0 < ε_cut₁) (hcut₂ : 0 < ε_cut₂)
    (htail₁ : 0 < ε_tail₁) (htail₂ : 0 < ε_tail₂)
    (h_budget_L1 : ε_cut₁ + ε_tail₁ < ε)
    (h_budget_L2 : ε_cut₂ + ε_tail₂ < ε)
    (hf_tail_L1 :
      ∫ x, ‖f x‖ ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ε_tail₁)
    (hf_tail_L2 :
      eLpNorm (fun x => f x) 2 (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖})
        < ENNReal.ofReal ε_tail₂) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ),
      tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 3) ∧
      eLpNorm (fun x => f x - φ x) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun x => f x - φ x) 2 volume < ENNReal.ofReal ε := by
  classical
  have hR_lt : R < R + 1 := by linarith
  obtain ⟨χ, hχ_smooth, hχ_one, hχ_bounds, hχ_compact, hχ_support⟩ :=
    exists_smooth_cutoff (n := n) R (R + 1) hR hR_lt
  have hχ_nonneg : ∀ x, 0 ≤ χ x := fun x => (hχ_bounds x).1
  have hχ_le_one : ∀ x, χ x ≤ 1 := fun x => (hχ_bounds x).2
  set f_cut : (Fin n → ℝ) → ℂ := fun x => (χ x : ℂ) * f x with hf_cut_def
  have h_diff_zero_inside :
      ∀ {x : (Fin n → ℝ)}, ‖x‖ ≤ R → f x - f_cut x = 0 := by
    intro x hx
    have hχx : χ x = 1 := hχ_one x hx
    simp [hf_cut_def, hχx]
  have h_diff_norm_le : ∀ x, ‖f x - f_cut x‖ ≤ ‖f x‖ := by
    intro x
    have hx_nonneg : 0 ≤ χ x := hχ_nonneg x
    have hx_le_one : χ x ≤ 1 := hχ_le_one x
    have habs_le : |1 - χ x| ≤ (1 : ℝ) := by
      have hdiff_nonneg : 0 ≤ 1 - χ x := by linarith
      have hdiff_le : 1 - χ x ≤ 1 := by linarith
      have habs_eq : |1 - χ x| = 1 - χ x := abs_of_nonneg hdiff_nonneg
      simpa [habs_eq] using hdiff_le
    have hmul_le : |1 - χ x| * ‖f x‖ ≤ 1 * ‖f x‖ := by
      have hnorm_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
      exact mul_le_mul_of_nonneg_right habs_le hnorm_nonneg
    have hnorm_eq :
        ‖f x - f_cut x‖ = |1 - χ x| * ‖f x‖ := by
      have hfactor : f x - f_cut x = f x * (1 - (χ x : ℂ)) := by
        have := (mul_sub (f x) (1 : ℂ) (χ x : ℂ))
        simpa [hf_cut_def, one_mul, mul_comm] using this.symm
      calc
        ‖f x - f_cut x‖
            = ‖f x * (1 - (χ x : ℂ))‖ := by simp [hfactor]
        _ = ‖f x‖ * ‖1 - (χ x : ℂ)‖ := norm_mul _ _
        _ = ‖f x‖ * |1 - χ x| := by
          have hnormχ : ‖1 - (χ x : ℂ)‖ = |1 - χ x| := by
            simpa [Complex.ofReal_sub] using (RCLike.norm_ofReal (K := ℂ) (1 - χ x))
          simp [hnormχ]
        _ = |1 - χ x| * ‖f x‖ := by ring
    calc
      ‖f x - f_cut x‖ = |1 - χ x| * ‖f x‖ := hnorm_eq
      _ ≤ 1 * ‖f x‖ := hmul_le
      _ = ‖f x‖ := by simp
  have h_diff_support :
      Function.support (fun x => f x - f_cut x)
        ⊆ {x : (Fin n → ℝ) | R < ‖x‖} := by
    intro x hx
    by_contra hnot
    have hx_le : ‖x‖ ≤ R := le_of_not_gt hnot
    have hx_ne : f x - f_cut x ≠ 0 := by
      simpa [Function.support] using hx
    have hzero : f x - f_cut x = 0 := h_diff_zero_inside hx_le
    exact hx_ne hzero
  have h_cutoff_L1 :
      eLpNorm (fun x => f x - f_cut x) 1 volume ≤ ENNReal.ofReal ε_tail₁ :=
    cutoff_L1_bound f f_cut hf_L1 χ R ε_tail₁ hχ_nonneg hχ_le_one
      hf_cut_def h_diff_zero_inside hf_tail_L1 htail₁
  have h_cutoff_L2 :
      eLpNorm (fun x => f x - f_cut x) 2 volume ≤ ENNReal.ofReal ε_tail₂ :=
    cutoff_L2_bound f f_cut χ R ε_tail₂ hχ_nonneg hχ_le_one
      hf_cut_def h_diff_zero_inside hf_tail_L2
  -- Remaining steps: mollify the truncated function and combine the error budgets.
  sorry

theorem schwartz_dense_L1_L2_simultaneous
    (hn : 0 < n) (f : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 (volume : Measure (Fin n → ℝ)))
    (hf_L2 : MemLp f 2 (volume : Measure (Fin n → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
  ∃ φ : 𝓢((Fin n → ℝ), ℂ),
      eLpNorm (fun x => f x - φ x) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun x => f x - φ x) 2 volume < ENNReal.ofReal ε := by
  classical
  -- Split the error budget into four equal pieces that will be used for the
  -- truncation and convolution steps in the auxiliary lemma.
  let ε_cut₁ : ℝ := ε / 4
  let ε_tail₁ : ℝ := ε / 4
  let ε_cut₂ : ℝ := ε / 4
  let ε_tail₂ : ℝ := ε / 4

  have hε_cut₁_pos : 0 < ε_cut₁ := by
    have hden : (0 : ℝ) < 4 := by norm_num
    simpa [ε_cut₁] using div_pos hε hden
  have hε_tail₁_pos : 0 < ε_tail₁ := by
    have hden : (0 : ℝ) < 4 := by norm_num
    simpa [ε_tail₁] using div_pos hε hden
  have hε_cut₂_pos : 0 < ε_cut₂ := by
    have hden : (0 : ℝ) < 4 := by norm_num
    simpa [ε_cut₂] using div_pos hε hden
  have hε_tail₂_pos : 0 < ε_tail₂ := by
    have hden : (0 : ℝ) < 4 := by norm_num
    simpa [ε_tail₂] using div_pos hε hden

  have h_budget_L1 : ε_cut₁ + ε_tail₁ < ε := by
    have h_half : ε / 2 < ε := half_lt_self hε
    have h_sum₀ : ε / 4 + ε / 4 = ε / 2 := by ring
    have h_sum : ε_cut₁ + ε_tail₁ = ε / 2 := by
      simpa [ε_cut₁, ε_tail₁] using h_sum₀
    simpa [h_sum] using h_half
  have h_budget_L2 : ε_cut₂ + ε_tail₂ < ε := by
    have h_half : ε / 2 < ε := half_lt_self hε
    have h_sum₀ : ε / 4 + ε / 4 = ε / 2 := by ring
    have h_sum : ε_cut₂ + ε_tail₂ = ε / 2 := by
      simpa [ε_cut₂, ε_tail₂] using h_sum₀
    simpa [h_sum] using h_half

  -- Tail control in L¹.
  obtain ⟨R₁, hR₁_pos, hR₁_tail⟩ :=
    integrable_tail_small (f := f) hf_L1 (ε := ε_tail₁) hε_tail₁_pos

  -- Tail control in L² is obtained by applying the tail lemma to the function
  -- `‖f‖²`, and then converting the bound to an `L²`-norm bound.
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
  have hf_sq_integrable : Integrable (fun x => ‖f x‖ ^ (2 : ℝ)) volume := by
    simpa [one_div] using
      (hf_L2.integrable_norm_rpow (μ := volume) hp0 hp_top)

  -- The function `‖f‖²` is non-negative, so we can apply the tail lemma to it.
  have hε_tail₂_sq_pos : 0 < ε_tail₂ ^ (2 : ℝ) :=
    Real.rpow_pos_of_pos hε_tail₂_pos _

  obtain ⟨R₂, hR₂_pos, hR₂_tail_sq⟩ :=
    integrable_tail_small
      (f := fun x => Complex.ofReal (‖f x‖ ^ (2 : ℝ)))
      (by
        -- Show that `‖f‖²` considered as a complex-valued function is in `L¹`.
        have h_int_complex :
            Integrable (fun x => Complex.ofReal (‖f x‖ ^ (2 : ℝ))) volume := by
          simpa using hf_sq_integrable.ofReal (μ := volume) (𝕜 := ℂ)
        simpa using (memLp_one_iff_integrable).2 h_int_complex)
      (ε := ε_tail₂ ^ (2 : ℝ)) hε_tail₂_sq_pos

  -- Combine the L¹ and L² tail bounds by taking the larger radius.
  set R : ℝ := max R₁ R₂ with hR_def
  have hR_pos : 0 < R := by
    have hR₁_le : R₁ ≤ R := by
      simp [R, hR_def]
    exact lt_of_lt_of_le hR₁_pos hR₁_le

  -- Monotonicity lets us transfer the tail bounds to the radius `R`.
  have h_tail_L1 :
      ∫ x, ‖f x‖ ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ε_tail₁ := by
    have h_nonneg : ∀ x, 0 ≤ ‖f x‖ := fun _ => norm_nonneg _
    have h_int := (memLp_one_iff_integrable).1 hf_L1
    have h_int_tail :=
      (h_int.norm.restrict (s := {x : (Fin n → ℝ) | R₁ ≤ ‖x‖}))
    have hR_le : R₁ ≤ R := by
      simp [R, hR_def]
    simpa [R, hR_def] using
      tail_bound_mono (F := fun x => ‖f x‖)
        (R₁ := R₁) (R₂ := R) hR_le h_nonneg h_int_tail hR₁_tail

  have h_tail_L2_sq :
      ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖})
        < ε_tail₂ ^ (2 : ℝ) := by
    have h_nonneg : ∀ x, 0 ≤ ‖f x‖ ^ (2 : ℝ) := fun x =>
      Real.rpow_nonneg (norm_nonneg _) _
    have h_int_tail :=
      (hf_sq_integrable.restrict (s := {x : (Fin n → ℝ) | R₂ ≤ ‖x‖}))
    have hR₂_le : R₂ ≤ R := by
      simp [R, hR_def]
    have hR₂_tail_sq_real :
        ∫ x, ‖f x‖ ^ (2 : ℝ)
            ∂(volume.restrict {x : (Fin n → ℝ) | R₂ ≤ ‖x‖})
          < ε_tail₂ ^ (2 : ℝ) := by
      have h_nonneg_val : ∀ x, 0 ≤ ‖f x‖ ^ (2 : ℝ) :=
        fun x => Real.rpow_nonneg (norm_nonneg _) _
      have h_abs_eq :
          (fun x => ‖Complex.ofReal (‖f x‖ ^ (2 : ℝ))‖)
            = fun x => ‖f x‖ ^ (2 : ℝ) := by
        funext x
        simp [Complex.norm_real, Real.norm_eq_abs, h_nonneg_val x]
      simpa [h_abs_eq] using hR₂_tail_sq
    simpa [R, hR_def] using
      tail_bound_mono (F := fun x => ‖f x‖ ^ (2 : ℝ))
        (R₁ := R₂) (R₂ := R) hR₂_le h_nonneg h_int_tail hR₂_tail_sq_real

  -- Convert the integral bound on `‖f‖²` into an `L²` bound.
  have h_tail_L2 :
      eLpNorm (fun x => f x) 2
          (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ENNReal.ofReal ε_tail₂ := by
    -- On the restricted measure we have membership in L².
    have hf_restrict :
        MemLp (fun x => f x) 2 (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) :=
      hf_L2.restrict (μ := volume) _
    have h_eq :=
      hf_restrict.eLpNorm_eq_integral_rpow_norm hp0 hp_top
    have h_nonneg :
        0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hε_tail₂_nonneg : 0 ≤ ε_tail₂ := le_of_lt hε_tail₂_pos
    set I :=
        ∫ x, ‖f x‖ ^ (2 : ℝ)
            ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) with hI_def
    have hI_nonneg : 0 ≤ I := by simpa [I, hI_def] using h_nonneg
    have hI_lt_sq : I < ε_tail₂ ^ 2 := by
      have h_lt := h_tail_L2_sq
      simpa [I, hI_def, Real.rpow_natCast] using h_lt
    set A : ℝ := Real.sqrt I with hA_def
    have hA_lt : A < ε_tail₂ := by
      have h_sq_lt := (Real.sqrt_lt hI_nonneg hε_tail₂_nonneg).2 hI_lt_sq
      simpa [A, hA_def] using h_sq_lt
    have hA_eq : A = I ^ (1 / 2 : ℝ) := by
      simpa [A, hA_def] using Real.sqrt_eq_rpow I
    have h_pow_lt : I ^ (1 / 2 : ℝ) < ε_tail₂ := by
      simpa [hA_eq] using hA_lt
    have h_ofReal_lt :
        ENNReal.ofReal (I ^ (1 / 2 : ℝ)) < ENNReal.ofReal ε_tail₂ :=
      (ENNReal.ofReal_lt_ofReal_iff hε_tail₂_pos).2 h_pow_lt
    simpa [h_eq, I, hI_def] using h_ofReal_lt

  obtain ⟨φ, hφ_support, hφ_L1, hφ_L2⟩ :=
    cutoff_then_convolve_Lp (n := n) hn f hf_L1 hf_L2 R hR_pos
      (ε := ε) (ε_cut₁ := ε_cut₁) (ε_cut₂ := ε_cut₂)
      (ε_tail₁ := ε_tail₁) (ε_tail₂ := ε_tail₂)
      hε hε_cut₁_pos hε_cut₂_pos hε_tail₁_pos hε_tail₂_pos
      h_budget_L1 h_budget_L2 h_tail_L1 h_tail_L2
  exact ⟨φ, hφ_L1, hφ_L2⟩

/--
**Variant for ℝ (n=1 case) with simultaneous L¹ and L² control.**

This is the specific instance needed for the Plancherel theorem on ℝ.

Given f ∈ L¹(ℝ) ∩ L²(ℝ), we can approximate it simultaneously in both norms
by a smooth compactly supported function.
-/

lemma smooth_cutoff_compactSupport_Lp_real
    (φ : ℝ → ℂ)
    (hφ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ)
    (hφ_memLp : MemLp φ (2 : ℝ≥0∞) volume)
    {R : ℝ} (hR_pos : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      MemLp g (2 : ℝ≥0∞) volume ∧
      eLpNorm (fun t => φ t - g t) (2 : ℝ≥0∞) volume < ENNReal.ofReal ε :=
  by
  classical
  have hn : 0 < (1 : ℕ) := by decide
  haveI := (inferInstance : FiniteDimensional ℝ (Fin 1 → ℝ))
  -- Identify `(Fin 1 → ℝ)` with ℝ.
  let E : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ :=
    { toLinearEquiv :=
        { toFun := fun x => x 0
          invFun := fun t _ => t
          map_add' := by intro x y; rfl
          map_smul' := by intro c x; rfl
          left_inv := by
            intro x
            funext i
            have : i = (0 : Fin 1) := Subsingleton.elim _ _
            simp [this]
          right_inv := by intro t; rfl }
      norm_map' := by
        classical
        intro x
        have hx_const : x = fun _ : Fin 1 => x 0 := by
          funext i
          have : i = (0 : Fin 1) := Subsingleton.elim _ _
          simp [this]
        have hx_norm' : ‖fun _ : Fin 1 => x 0‖ = ‖x‖ := by
          simpa using congrArg norm hx_const.symm
        have hx_norm'' : ‖fun _ : Fin 1 => x 0‖ = ‖x 0‖ := by
          simp
        have hx_norm : ‖x‖ = ‖x 0‖ := by
          simpa [hx_norm''] using hx_norm'.symm
        simp [hx_norm.symm] }
  -- Transfer `φ` to `(Fin 1 → ℝ)`.
  let φF : (Fin 1 → ℝ) → ℂ := fun x => φ (E x)
  have h_pres_forward :
      MeasurePreserving (fun x : (Fin 1 → ℝ) => E x) := by
    simpa [E] using
      (volume_preserving_piUnique fun _ : Fin 1 => ℝ)
  have h_pres_symm :
      MeasurePreserving (fun t : ℝ => E.symm t) := by
    have h :=
      (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm
    simpa [E] using h
  have hφF_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φF :=
    hφ_smooth.comp (E.toLinearIsometry.contDiff)
  have hφF_memLp : MemLp φF (2 : ℝ≥0∞) volume :=
    hφ_memLp.comp_measurePreserving h_pres_forward

  obtain ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, hψ_close⟩ :=
    smooth_cutoff_compactSupport_Lp (n := 1) (p := (2 : ℝ≥0∞))
      (hp_one := by norm_num)
      (hp_ne_top := by norm_num)
      φF hφF_smooth hφF_memLp (R := R) hR_pos
      (ε := ε) hε

  let g : ℝ → ℂ := fun t => ψ (E.symm t)
  have hg_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) g :=
    hψ_smooth.comp (E.symm.toLinearIsometry.contDiff)
  have hg_support : HasCompactSupport g :=
    hψ_support.comp_homeomorph (E.symm.toHomeomorph)
  have hg_memLp : MemLp g (2 : ℝ≥0∞) volume :=
    hψ_memLp.comp_measurePreserving h_pres_symm

  have hφψ_meas :
      AEStronglyMeasurable (fun x : (Fin 1 → ℝ) => φF x - ψ x) volume :=
    (hφF_smooth.continuous.aestronglyMeasurable.sub
      hψ_smooth.continuous.aestronglyMeasurable)
  have hψ_close' :
      eLpNorm (fun x : (Fin 1 → ℝ) => φF x - ψ x) (2 : ℝ≥0∞) volume
        < ENNReal.ofReal ε := by
    simpa [Pi.sub_def, sub_eq_add_neg] using hψ_close
  have hφg_close :
      eLpNorm (fun t => φ t - g t) (2 : ℝ≥0∞) volume < ENNReal.ofReal ε := by
    have h_eq :=
        eLpNorm_comp_measurePreserving (μ := volume) (ν := volume)
          (p := (2 : ℝ≥0∞))
          (f := fun t : ℝ => E.symm t)
          (g := fun x : (Fin 1 → ℝ) => φF x - ψ x)
          hφψ_meas h_pres_symm
    have h_eq' :
        eLpNorm (fun t : ℝ => φ t - g t) (2 : ℝ≥0∞) volume
          = eLpNorm (fun x : (Fin 1 → ℝ) => φF x - ψ x) (2 : ℝ≥0∞) volume := by
      simpa [Function.comp, φF, g, Pi.sub_def, sub_eq_add_neg]
        using h_eq
    have h := hψ_close'
    have hφg_close' :
        eLpNorm (fun t => φ t - g t) (2 : ℝ≥0∞) volume < ENNReal.ofReal ε := by
      simpa [Pi.sub_def, sub_eq_add_neg] using (h_eq'.symm ▸ h)
    exact hφg_close'

  refine ⟨g, hg_smooth, hg_support, hg_memLp, ?_⟩
  simpa [Pi.sub_def, sub_eq_add_neg] using hφg_close

theorem smooth_compactSupport_dense_L1_L2_real
    (f : ℝ → ℂ)
    (hf_L1 : Integrable f volume)
    (hf_L2 : MemLp f 2 volume)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      eLpNorm (f - g) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (f - g) 2 volume < ENNReal.ofReal ε := by
  classical

  -- We identify ℝ with the one-dimensional euclidean space `Fin 1 → ℝ`.
  have hn : 0 < (1 : ℕ) := by decide
  -- The linear isometry equivalence between `(Fin 1 → ℝ)` and `ℝ` given by evaluation at 0.
  let E : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ :=
    { toLinearEquiv :=
        { toFun := fun x => x 0
          invFun := fun t _ => t
          map_add' := by intro x y; rfl
          map_smul' := by intro c x; rfl
          left_inv := by
            intro x
            funext i
            have : i = (0 : Fin 1) := Subsingleton.elim _ _
            simp [this]
          right_inv := by intro t; rfl }
      norm_map' := by
        classical
        intro x
        have hx_const : x = fun _ : Fin 1 => x 0 := by
          funext i
          have : i = (0 : Fin 1) := Subsingleton.elim _ _
          simp [this]
        have hx_norm' : ‖fun _ : Fin 1 => x 0‖ = ‖x‖ := by
          simpa using congrArg norm hx_const.symm
        have hx_norm'' : ‖fun _ : Fin 1 => x 0‖ = ‖x 0‖ := by
          simp
        have hx_norm : ‖x‖ = ‖x 0‖ := by
          simpa [hx_norm''] using hx_norm'.symm
        simp [hx_norm.symm] }
  -- Transport the original function to `(Fin 1 → ℝ)`.
  let F : (Fin 1 → ℝ) → ℂ := fun x => f (E x)

  -- `f` belongs to both L¹ and L², hence so does `F` by measure preservation.
  have h_pres : MeasurePreserving (fun t : ℝ => E.symm t) := by
    have h := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm
    simpa [E] using h
  have hF_L1 : MemLp F 1 volume :=
    ((memLp_one_iff_integrable (μ := volume)).mpr hf_L1).comp_measurePreserving
      (by
        simpa [E] using
          (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)))
  have hF_L2 : MemLp F 2 volume :=
    hf_L2.comp_measurePreserving
      (by
        simpa [E] using
          (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)))

  -- Use the simultaneous Schwartz approximation on `(Fin 1 → ℝ)` with a small error budget.
  obtain ⟨φ, hφ_L1, hφ_L2⟩ :=
    schwartz_dense_L1_L2_simultaneous (n := 1) hn F hF_L1 hF_L2
      (ε := ε / 4) (by simpa using div_pos hε (by norm_num : (0 : ℝ) < 4))

  -- Turn the Schwartz approximation `φ` into a function on ℝ.
  let φℝ : ℝ → ℂ := fun t => φ (E.symm t)
  have hφℝ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φℝ :=
    (φ.smooth (⊤ : ℕ∞)).comp (E.symm.toLinearIsometry.contDiff)
  have hφℝ_memLp₂ : MemLp φℝ 2 volume :=
    (φ.memLp (p := (2 : ℝ≥0∞)) (μ := volume)).comp_measurePreserving h_pres

  have hFφ_meas :
      AEStronglyMeasurable (fun x : (Fin 1 → ℝ) => F x - φ x) volume :=
    (hF_L2.aestronglyMeasurable.sub
      (φ.smooth (⊤ : ℕ∞)).continuous.aestronglyMeasurable)

  -- Smoothly cut off `φℝ` to obtain a compactly supported function while controlling the error.
  obtain ⟨g, hg_smooth, hg_support, hg_memLp, hg_close⟩ :=
    smooth_cutoff_compactSupport_Lp_real φℝ hφℝ_smooth hφℝ_memLp₂
      (R := 1) (hR_pos := by norm_num)
      (ε := ε / 4)
      (by simpa using div_pos hε (by norm_num : (0 : ℝ) < 4))

  -- Control the L¹ and L² errors simultaneously via triangle inequalities.
  have hφ_L1' :
      eLpNorm (fun x : (Fin 1 → ℝ) => F x - φ x) 1 volume < ENNReal.ofReal (ε / 4) := by
    simpa [Pi.sub_def, sub_eq_add_neg] using hφ_L1
  have hφ_L2' :
      eLpNorm (fun x : (Fin 1 → ℝ) => F x - φ x) 2 volume < ENNReal.ofReal (ε / 4) := by
    simpa [Pi.sub_def, sub_eq_add_neg] using hφ_L2

  have hfφ_L1 : eLpNorm (fun t => f t - φℝ t) 1 volume < ENNReal.ofReal (ε / 4) := by
    have h_eq :=
        eLpNorm_comp_measurePreserving (μ := volume) (ν := volume)
          (p := (1 : ℝ≥0∞))
          (f := fun t : ℝ => E.symm t)
          (g := fun x : (Fin 1 → ℝ) => F x - φ x)
          hFφ_meas h_pres
    have h_eq' :
        eLpNorm (fun t : ℝ => f t - φℝ t) 1 volume
          = eLpNorm (fun x : (Fin 1 → ℝ) => F x - φ x) 1 volume := by
      simpa [Function.comp, F, φℝ, Pi.sub_def, sub_eq_add_neg]
        using h_eq
    simpa [h_eq'] using hφ_L1'

  have hfφ_L2 : eLpNorm (fun t => f t - φℝ t) 2 volume < ENNReal.ofReal (ε / 4) := by
    have h_eq :=
        eLpNorm_comp_measurePreserving (μ := volume) (ν := volume)
          (p := (2 : ℝ≥0∞))
          (f := fun t : ℝ => E.symm t)
          (g := fun x : (Fin 1 → ℝ) => F x - φ x)
          hFφ_meas h_pres
    have h_eq' :
        eLpNorm (fun t : ℝ => f t - φℝ t) 2 volume
          = eLpNorm (fun x : (Fin 1 → ℝ) => F x - φ x) 2 volume := by
      simpa [Function.comp, F, φℝ, Pi.sub_def, sub_eq_add_neg]
        using h_eq
    simpa [h_eq'] using hφ_L2'

  have hφg_L2 : eLpNorm (fun t => φℝ t - g t) 2 volume < ENNReal.ofReal (ε / 4) := hg_close

  have hφg_L1 : eLpNorm (fun t => φℝ t - g t) 1 volume < ENNReal.ofReal (ε / 4) := by
    -- TODO: control the L¹-error of the smooth cutoff.
    sorry

  -- Apply the auxiliary triangle inequality to control the total error.
  refine ⟨g, hg_smooth, hg_support, ?_, ?_⟩
  · sorry
  · sorry

/--
**Variant: approximation by continuous compactly supported with both L¹ and L² bounds.**

For f ∈ L¹(ℝ) ∩ L²(ℝ), we can find continuous compactly supported g
such that both ‖f - g‖₁ < ε and ‖f - g‖₂ < ε.

This is the exact statement needed in FourierPlancherelL2.lean.
-/
theorem continuous_compactSupport_dense_L1_L2_real
    (f : ℝ → ℂ)
    (hf_L1 : Integrable f volume)
    (hf_L2 : MemLp f 2 volume)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      Continuous g ∧
      HasCompactSupport g ∧
      MemLp g 2 volume ∧
      eLpNorm (f - g) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (f - g) 2 volume < ENNReal.ofReal ε := by
  sorry

/--
**Lusin's theorem for Lp functions.**

This is a consequence of the density theorem and can be useful for
understanding the approximation procedure.

For f ∈ Lp and ε > 0, there exists a continuous compactly supported g
such that the set {x : f(x) ≠ g(x)} has measure < ε.
-/
theorem lusin_type_approximation_Lp
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∃ g : (Fin n → ℝ) → ℂ,
      Continuous g ∧
      HasCompactSupport g ∧
      eLpNorm (f - g) p volume < ENNReal.ofReal ε ∧
      volume {x | f x ≠ g x} < ENNReal.ofReal δ := by
  sorry

/--
**Approximation preserving positivity.**

If f ≥ 0 almost everywhere, then the approximating function can also
be chosen to be non-negative.

This is useful in probability theory and analysis of positive operators.
-/
theorem smooth_compactSupport_dense_Lp_nonneg
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hp_ne_top : p ≠ ∞)
    (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    (hf_nonneg : ∀ᵐ x ∂volume, 0 ≤ f x)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧
      eLpNorm (fun x => f x - g x) p volume < ENNReal.ofReal ε := by
  sorry
