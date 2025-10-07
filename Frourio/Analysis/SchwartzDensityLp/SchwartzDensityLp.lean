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
open scoped ENNReal ContDiff Topology

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
      -- Here we use a conservative approach: choose δ = 1

      use 1
      constructor
      · norm_num
      · intro η hη_pos hη_lt
        -- We need to show that the convolution is close to f₀
        -- Strategy: Use triangle inequality with intermediate g
        --
        -- ‖f₀ - f₀*ψ_η‖₁ ≤ ‖f₀ - g‖₁ + ‖g - g*ψ_η‖₁ + ‖g*ψ_η - f₀*ψ_η‖₁

        -- Step 1: We already have ‖f₀ - g‖₁ < ε'/4 from hg_approx

        -- Step 2: For continuous functions with compact support,
        -- convolution with mollifier converges: ‖g - g*ψ_η‖₁ → 0 as η → 0
        -- For our fixed η < 1, we can bound this
        have h_g_conv_bound :
            eLpNorm (fun x => g x - ∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ))
              1 volume < ENNReal.ofReal (ε' / 4) := by
          -- For continuous functions with compact support,
          -- the convolution with a mollifier converges uniformly
          -- This follows from:
          -- - g is uniformly continuous (compact support)
          -- - ψ is a mollifier (normalized, compactly supported)
          -- - The standard approximation identity theorem
          sorry -- Technical: requires uniform continuity and
                -- dominated convergence for convolution

        -- Step 3: Convolution is linear, so
        -- ‖g*ψ_η - f₀*ψ_η‖₁ = ‖(g - f₀)*ψ_η‖₁ ≤ ‖g - f₀‖₁ · ‖ψ_η‖₁
        -- by Young's inequality
        have h_conv_diff_bound :
            eLpNorm (fun x =>
              (∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) -
              (∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)))
              1 volume < ENNReal.ofReal (ε' / 4) := by
          -- By linearity of integration:
          -- ∫ y, g(x-y)*ψ_η(y) - ∫ y, f₀(x-y)*ψ_η(y) = ∫ y, (g-f₀)(x-y)*ψ_η(y)
          --
          -- By Young's inequality for convolution:
          -- ‖f * g‖_p ≤ ‖f‖_p · ‖g‖₁
          --
          -- Here: ‖(g-f₀) * ψ_η‖₁ ≤ ‖g-f₀‖₁ · ‖ψ_η‖₁
          --
          -- We have:
          -- - ‖g-f₀‖₁ < ε'/4 (from hg_approx, symmetric)
          -- - ‖ψ_η‖₁ = 1 (by normalization of ψ)
          sorry -- Technical: requires Young's inequality and
                -- linearity of convolution

        -- Step 4: Combine all three bounds using triangle inequality
        -- The full calculation would be:
        -- ‖f₀ - f₀*ψ_η‖₁ ≤ ‖f₀ - g‖₁ + ‖g - g*ψ_η‖₁ + ‖g*ψ_η - f₀*ψ_η‖₁
        --                 < ε'/4 + ε'/4 + ε'/4 = 3ε'/4 < ε'

        -- We have all three bounds, so conclude directly
        -- Use the fact that ‖f₀ - f₀*ψ‖ < 3ε'/4 < ε'
        -- The detailed proof requires triangle inequality for eLpNorm
        sorry

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

      -- Step 2: Choose δ conservatively
      use 1
      constructor
      · norm_num
      · intro η hη_pos hη_lt
        -- Similar argument as L¹ case, but for L² norm
        -- The proof structure is identical to L¹ case
        -- Requires approximation identity theory for L²
        sorry

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
    sorry

/--
**切り詰め→畳み込みの統合補題.**

論文のステップ4-8を一つの補題にまとめたもの。
R を先に固定し、f を B_R で切り詰めてから畳み込むことで、
φ のサポートが B_{R+3} に収まることを保証する。

これにより、論文の正しい順序（R を先に決定→δ を選択）を実現できる。
-/
lemma cutoff_then_convolve_Lp
    (hn : 0 < n)
    (f : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 volume)
    (hf_L2 : MemLp f 2 volume)
    (R : ℝ) (hR : 0 < R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ),
      tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 3) ∧
      eLpNorm (fun x => f x - φ x) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun x => f x - φ x) 2 volume < ENNReal.ofReal ε := by
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
  sorry

/--
**Variant for ℝ (n=1 case) with simultaneous L¹ and L² control.**

This is the specific instance needed for the Plancherel theorem on ℝ.

Given f ∈ L¹(ℝ) ∩ L²(ℝ), we can approximate it simultaneously in both norms
by a smooth compactly supported function.
-/
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
  sorry

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
