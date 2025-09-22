import Frourio.Analysis.HilbertSpaceCore
import Frourio.Analysis.MellinBasic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Measure Real Complex SchwartzMap
open scoped ENNReal Topology ComplexConjugate

namespace Frourio

section DenseSubspaces


/-- Helper function: Create mollifier with support on [-δ, δ] -/
noncomputable def create_mollifier (δ : ℝ) (hδ_pos : 0 < δ) : ℝ → ℝ :=
  let Z := ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2))
  fun x => if |x| < δ then Real.exp (-1 / (δ^2 - x^2)) / Z else 0

/-- After Lp construction, the function is ae_eq to the original smooth function -/
lemma lp_construction_ae_eq {σ : ℝ}
    (smooth_func : ℝ → ℂ)
    (h_L2 : MemLp smooth_func 2 (weightedMeasure σ)) :
    (MemLp.toLp smooth_func h_L2 : ℝ → ℂ) =ᵐ[weightedMeasure σ] smooth_func := by
  -- This is the fundamental property of MemLp.toLp
  exact MemLp.coeFn_toLp h_L2

/-- For continuous functions, the Lp representative can be chosen to agree pointwise -/
lemma continuous_lp_pointwise {σ : ℝ}
    (smooth_func : ℝ → ℂ)
    (h_cont : Continuous smooth_func)
    (h_L2 : MemLp smooth_func 2 (weightedMeasure σ))
    (h_eq : weightedMeasure σ = mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))
    (x : ℝ) (hx : x > 0) :
    Hσ.toFun (cast (by rw [h_eq]) (MemLp.toLp smooth_func h_L2)) x = smooth_func x := by
  -- For continuous functions that are in L², the canonical representative
  -- agrees with the original function on the support of the measure
  sorry -- This requires showing that continuous L² functions have continuous representatives

/-- Distance estimate for mollified approximation in L²-norm -/
lemma mollified_approximation_distance {σ : ℝ} (ε : ℝ) (hε : 0 < ε)
    (f : Hσ σ)
    (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (f' : Lp ℂ 2 (weightedMeasure σ))
    (hs_close : dist (↑s : Lp ℂ 2 (weightedMeasure σ)) f' < ε / 3)
    (n : ℕ) (hn_pos : 0 < n) (hn_large : n > max 1 ‖f'‖)
    (h_eq : weightedMeasure σ = mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))
    (g : Hσ σ)
    (smooth_func : ℝ → ℂ)
    (h_L2 : MemLp smooth_func 2 (weightedMeasure σ))
    (h_g_def : g = cast (by rw [h_eq]) (MemLp.toLp smooth_func h_L2)) :
    dist f g < ε := by
  -- The proof relies on approximation theory:
  -- 1. f is close to f' in Hσ (same element up to cast)
  -- 2. f' is ε/3-close to the simple function s
  -- 3. The smooth function (from mollifier) approximates s within 2ε/3
  -- 4. g is the cast of the smooth function
  -- By triangle inequality, dist(f, g) < ε
  sorry  -- Requires detailed approximation estimates

lemma smooth_approximation_of_truncated_simple {σ : ℝ} (f : Hσ σ) (ε : ℝ) (hε : 0 < ε)
    (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (f' : Lp ℂ 2 (weightedMeasure σ))
    (hs_close : dist (↑s : Lp ℂ 2 (weightedMeasure σ)) f' < ε / 3)
    (n : ℕ) (hn_pos : 0 < n) (hn_large : n > max 1 ‖f'‖)
    (h_eq : weightedMeasure σ = mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) :
   ∃ (g : Hσ σ), g ∈ {h : Hσ σ | ∃ φ : ℝ → ℂ,
     (∀ x ≤ 0, φ x = 0) ∧
     (∃ R > 0, ∀ x ≥ R, φ x = 0) ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      ∀ x > 0, Hσ.toFun h x = φ x} ∧ dist f g < ε := by
  -- Construct a smooth approximation by convolving the truncated function with a mollifier
  -- Step 1: Define the truncated function
  let truncate := fun x : ℝ => if 1/n < x ∧ x < n then Lp.simpleFunc.toSimpleFunc s x else 0

  -- Step 2: Choose a mollifier (smooth bump function) with small support
  let δ : ℝ := min (1/(2*n : ℝ)) (ε/(6 * max 1 ‖f'‖))
  have hδ_pos : 0 < δ := by
    simp only [δ]
    apply lt_min
    · apply div_pos
      · norm_num
      · apply mul_pos (by norm_num : (0 : ℝ) < 2)
        simp only [Nat.cast_pos]
        exact hn_pos
    · apply div_pos hε
      apply mul_pos (by norm_num : (0 : ℝ) < 6)
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)

  -- Step 3: Convolution would create smooth function, but needs mollifier construction
  -- We need a mollifier φ_δ : ℝ → ℝ with:
  -- (1) φ_δ is smooth
  -- (2) φ_δ is supported on [-δ, δ]
  -- (3) ∫ φ_δ = 1
  -- (4) φ_δ ≥ 0

  -- First, we need the mollifier φ_δ : ℝ → ℝ
  -- This should be a smooth bump function with the properties listed above
  -- For now we assume its existence
  -- Standard mollifier construction: φ_δ(x) = (1/Z) * exp(-1/(δ²-x²)) for |x| < δ, 0 otherwise
  -- where Z is the normalization constant to make ∫ φ_δ = 1
  let φ_δ : ℝ → ℝ := fun x =>
    if h : |x| < δ then
      -- The unnormalized mollifier exp(-1/(δ²-x²))
      let unnormalized := Real.exp (-1 / (δ^2 - x^2))
      -- Normalization constant Z = ∫_{-δ}^{δ} exp(-1/(δ²-y²)) dy
      let Z : ℝ := ∫ y in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - y^2))
      unnormalized / Z
    else 0

  have hφ_supp : ∀ y, |y| > δ → φ_δ y = 0 := by
    intro y hy
    simp only [φ_δ]
    split_ifs with h
    · exfalso; linarith
    · rfl

  have hφ_nonneg : ∀ y, 0 ≤ φ_δ y := by
    intro y
    simp only [φ_δ]
    split_ifs with h
    · -- In support: exp(-1/(δ²-y²)) / Z ≥ 0 since exp > 0 and Z > 0
      apply div_nonneg
      · exact le_of_lt (Real.exp_pos _)
      · -- Z > 0 was proved earlier in mollifier_normalization_positive
        -- We need to extract the proof from within mollifier_smooth_at_boundary
        -- First, let's prove it directly here
        have hZ_pos : 0 < ∫ y in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - y^2)) := by
          -- Convert to interval integral
          have h_eq := integral_Ioo_eq_intervalIntegral δ hδ_pos
          rw [h_eq]
          apply intervalIntegral.intervalIntegral_pos_of_pos_on
          · -- The extended function is interval integrable
            let f_extended : ℝ → ℝ := fun t =>
              if |t| < δ then Real.exp (-1 / (δ^2 - t^2)) else 0
            have h_continuous : ContinuousOn f_extended (Set.uIcc (-δ) δ) :=
              mollifier_extended_continuous δ hδ_pos
            have h_integrable : IntervalIntegrable f_extended volume (-δ) δ :=
              ContinuousOn.intervalIntegrable h_continuous
            apply IntervalIntegrable.congr h_integrable
            apply ae_of_all
            intro x
            unfold f_extended
            have h_equiv : (x ∈ Set.Ioo (-δ) δ) ↔ (|x| < δ) := by
              simp [Set.mem_Ioo, abs_lt]
            by_cases hx : |x| < δ
            · simp only [if_pos hx]
              have hx_mem : x ∈ Set.Ioo (-δ) δ := h_equiv.mpr hx
              symm
              change (if x ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - x^2)) else 0) = _
              simp only [hx_mem, if_true]
            · simp only [if_neg hx]
              have hx_not_mem : x ∉ Set.Ioo (-δ) δ := by
                intro hmem
                exact hx (h_equiv.mp hmem)
              symm
              change (if x ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - x^2)) else 0) = _
              simp only [hx_not_mem, if_false]
          · -- The function is positive on the open interval
            intro x hx_in
            have hx_in_Ioo : x ∈ Set.Ioo (-δ) δ := by
              rw [Set.mem_Ioo]
              simp only [Set.mem_uIoc] at hx_in
              exact ⟨hx_in.1, hx_in.2⟩
            change (if x ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - x^2)) else 0) > 0
            simp only [hx_in_Ioo, if_true]
            exact Real.exp_pos _
          · linarith
        exact le_of_lt hZ_pos
    · exact le_refl 0

  -- Prove that φ_δ is smooth using the mollifier_smooth_at_boundary lemma
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ_δ := by
    -- φ_δ is the same as the mollifier function from mollifier_smooth_at_boundary
    -- We need to show it's smooth everywhere

    -- First, note that φ_δ equals the function from create_mollifier
    have h_eq : φ_δ = create_mollifier δ hδ_pos := by
      ext x
      simp only [φ_δ, create_mollifier]
      rfl

    -- The function is smooth on three regions:
    -- 1. |x| < δ: smooth as composition of smooth functions
    -- 2. |x| > δ: constantly 0, hence smooth
    -- 3. |x| = δ: smooth by mollifier_smooth_at_boundary

    -- Use that the function is piecewise smooth
    rw [h_eq]
    unfold create_mollifier

    -- The function is the same as the one analyzed in mollifier_smooth_at_boundary
    let Z := ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2))
    let φ := fun y => if |y| < δ then Real.exp (-1 / (δ^2 - y^2)) / Z else 0

    -- We already proved this is smooth at the boundaries
    have h_boundary := mollifier_smooth_at_boundary δ hδ_pos

    -- The function is smooth on the interior |y| < δ
    have h_interior : ∀ y, |y| < δ → ContDiffAt ℝ (⊤ : ℕ∞) φ y := by
      intro y hy
      -- On the interior, φ(y) = exp(-1/(δ²-y²))/Z which is smooth
      have h_pos : 0 < δ^2 - y^2 := by
        rw [sub_pos, ← sq_abs]
        have h_bound : -δ < |y| := by
          have : 0 ≤ |y| := abs_nonneg _
          linarith [hδ_pos]
        exact sq_lt_sq' h_bound hy

      -- The function is smooth as composition of smooth functions
      -- We need to show φ is smooth at y when |y| < δ
      -- φ(z) = exp(-1/(δ²-z²))/Z for |z| < δ
      have h_eq : ∀ᶠ z in 𝓝 y, φ z = Real.exp (-1 / (δ^2 - z^2)) / Z := by
        apply Metric.eventually_nhds_iff.mpr
        use (δ - |y|) / 2, by linarith
        intro z hz
        simp only [φ]
        split_ifs with h
        · rfl
        · exfalso
          rw [Real.dist_eq] at hz
          have : |z - y| < (δ - |y|) / 2 := hz
          -- Triangle inequality: |z| ≤ |z - y| + |y|
          have : |z| ≤ |z - y| + |y| := by
            calc |z| = |z - y + y| := by ring_nf
                 _ ≤ |z - y| + |y| := abs_add _ _
          linarith

      apply ContDiffAt.congr_of_eventuallyEq _ h_eq
      apply ContDiffAt.div_const
      apply Real.contDiff_exp.contDiffAt.comp
      -- The function is -1 / (δ² - y²)
      apply ContDiffAt.div
      · apply ContDiffAt.neg
        exact contDiffAt_const
      · apply ContDiffAt.sub
        · exact contDiffAt_const
        · exact ContDiffAt.pow contDiffAt_id 2
      · exact h_pos.ne'

    -- The function is smooth on the exterior |y| > δ
    have h_exterior : ∀ y, |y| > δ → ContDiffAt ℝ (⊤ : ℕ∞) φ y := by
      intro y hy
      -- On the exterior, φ is constantly 0
      have h_eq : ∀ᶠ z in 𝓝 y, φ z = 0 := by
        apply Metric.eventually_nhds_iff.mpr
        use (|y| - δ) / 2, by linarith
        intro z hz
        simp only [φ]
        split_ifs with h
        · exfalso
          rw [Real.dist_eq] at hz
          have : |z| < δ := h
          have : |z - y| < (|y| - δ) / 2 := hz
          -- Triangle inequality gives |z| ≥ |y| - |z - y|
          have hz_y : |z - y| < (|y| - δ) / 2 := hz
          -- From triangle inequality: |y| ≤ |y - z| + |z|
          have : |y| ≤ |y - z| + |z| := by
            calc |y| = |y - z + z| := by ring_nf
                 _ ≤ |y - z| + |z| := abs_add _ _
          have : |y| - |y - z| ≤ |z| := by linarith
          have : |y| - |z - y| ≤ |z| := by rw [abs_sub_comm]; exact this
          linarith
        · rfl
      exact contDiffAt_const.congr_of_eventuallyEq h_eq

    -- Combine all pieces to show global smoothness
    -- We need to show ContDiff, which follows from ContDiffAt everywhere
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases h1 : |y| < δ
    · exact h_interior y h1
    · by_cases h2 : |y| = δ
      · -- At the boundary, either y = δ or y = -δ
        have : y = δ ∨ y = -δ := by
          cases' le_or_gt 0 y with hy hy
          · -- y ≥ 0, so |y| = y
            left
            rw [abs_of_nonneg hy] at h2
            exact h2
          · -- y < 0, so |y| = -y
            right
            rw [abs_of_neg hy] at h2
            linarith
        cases' this with h h
        · -- y = δ
          rw [h]
          exact h_boundary.1
        · -- y = -δ
          rw [h]
          exact h_boundary.2
      · -- |y| > δ
        push_neg at h1 h2
        have : δ < |y| := by
          cases' lt_or_eq_of_le h1 with h h
          · exact h
          · exfalso; exact h2 h.symm
        exact h_exterior y this

  -- Step 4: Define the smooth approximation via convolution
  -- We need to prove that the mollifier has integral 1
  have hφ_integral : ∫ y, φ_δ y = 1 := by
    -- The mollifier is normalized so that its integral is 1
    -- By definition, φ_δ(y) = exp(-1/(δ²-y²))/Z for |y| < δ and 0 otherwise
    -- where Z = ∫_{-δ}^δ exp(-1/(δ²-t²)) dt

    -- The integral equals the integral over the support
    have : ∫ y, φ_δ y = ∫ y in Set.Ioo (-δ) δ, φ_δ y := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_Ioo] at hy
      simp only [φ_δ]
      split_ifs with h
      · exfalso
        have : -δ < y ∧ y < δ := abs_lt.mp h
        exact hy ⟨this.1, this.2⟩
      · rfl

    rw [this]
    -- On the interval (-δ, δ), φ_δ(y) = exp(-1/(δ²-y²))/Z
    -- First define Z explicitly
    let Z := ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2))

    have h_eq : ∀ y ∈ Set.Ioo (-δ) δ, φ_δ y = Real.exp (-1 / (δ^2 - y^2)) / Z := by
      intro y hy
      simp only [φ_δ]
      have : |y| < δ := by
        rw [abs_lt]
        exact ⟨hy.1, hy.2⟩
      rw [dif_pos this]
      -- The let-bound Z in φ_δ equals our Z

    -- Now the integral becomes (∫ exp(-1/(δ²-y²)) dy) / Z = Z / Z = 1
    have h_integral_eq : ∫ y in Set.Ioo (-δ) δ, φ_δ y = ∫ y in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - y^2)) / Z := by
      apply setIntegral_congr_fun
      · exact measurableSet_Ioo
      · intro y hy
        exact h_eq y hy
    rw [h_integral_eq]
    -- The integral ∫(f/Z) equals (∫f)/Z which equals Z/Z = 1
    simp only [Z]
    have hZ_pos : 0 < Z := mollifier_normalization_positive δ hδ_pos
    -- Since φ_δ y = exp(-1/(δ²-y²))/Z on Ioo(-δ,δ), we have ∫φ_δ = Z/Z = 1
    calc ∫ y in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - y^2)) / Z
        = (∫ y in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - y^2))) / Z := by
          -- ∫(f/c) = (∫f)/c for constant c
          -- We want to show ∫(f/Z) = (∫f)/Z
          have h_eq : ∀ y, Real.exp (-1 / (δ^2 - y^2)) / Z = (1/Z) * Real.exp (-1 / (δ^2 - y^2)) := by
            intro y; ring
          simp_rw [h_eq]
          rw [integral_const_mul]
          simp only [one_div]
          rw [div_eq_inv_mul]
        _ = Z / Z := rfl
        _ = 1 := div_self (ne_of_gt hZ_pos)

  -- Define the convolution of truncate with φ_δ
  let smooth_func : ℝ → ℂ := fun x => ∫ y, (φ_δ y : ℂ) * truncate (x - y)

  -- Step 5: Show that smooth_func has the required properties
  -- (a) It's smooth (from convolution with smooth mollifier)
  -- Need to provide the required properties of truncate
  have h_truncate_meas : Measurable truncate := by
    simp only [truncate]
    apply Measurable.ite
    · apply MeasurableSet.inter
      · exact measurableSet_Ioi
      · exact measurableSet_Iio
    · exact Lp.simpleFunc.measurable s
    · exact measurable_const

  have h_truncate_supp : ∀ x, x ∉ Set.Ioo (1/n : ℝ) n → truncate x = 0 := by
    intro x hx
    simp only [truncate]
    simp only [Set.mem_Ioo] at hx
    rw [if_neg]
    exact hx

  have h_smooth : ContDiff ℝ (⊤ : ℕ∞) smooth_func :=
    smooth_mollifier_convolution_truncated φ_δ s hφ_smooth hφ_supp hδ_pos hn_pos

  -- (b) It has compact support
  have h_support : ∃ R > 0, ∀ x ≥ R, smooth_func x = 0 :=
    convolution_mollifier_truncated_has_compact_support φ_δ truncate hφ_supp hδ_pos hn_pos
      h_truncate_supp

  have h_support_left_raw : ∀ x < (1/n : ℝ) - δ, smooth_func x = 0 :=
    convolution_mollifier_truncated_zero_outside_support φ_δ truncate hφ_supp hδ_pos hn_pos
      h_truncate_supp

  -- For the membership proof, we need ∀ x ≤ 0, smooth_func x = 0
  have hδ_bound : δ < 1 / n := by
    -- δ = min (1/(2*n)) (ε/(6 * max 1 ‖f'‖)) ≤ 1/(2*n) < 1/n
    simp only [δ]
    have h1 : 1 / (2 * n : ℝ) < 1 / n := by
      -- 1/(2n) < 1/n because 2n > n when n > 0
      have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      have h2n_pos : (0 : ℝ) < 2 * n := mul_pos (by norm_num : (0 : ℝ) < 2) hn_pos'
      -- Use div_lt_div_of_pos_left: a < b → 0 < c → c/b < c/a
      apply div_lt_div_of_pos_left
      · norm_num
      · exact hn_pos'
      · calc (n : ℝ)
          = 1 * n := by ring
          _ < 2 * n := by linarith
    calc min (1/(2*n : ℝ)) (ε/(6 * max 1 ‖f'‖))
      ≤ 1/(2*n : ℝ) := min_le_left _ _
      _ < 1/n := h1

  have h_support_left : ∀ x ≤ 0, smooth_func x = 0 :=
    convolution_vanishes_on_nonpositive φ_δ truncate hφ_supp hδ_pos hn_pos (le_of_lt hδ_bound) h_truncate_supp

  -- Step 6: Create the element of Hσ σ
  -- We need to show smooth_func is measurable and in L² with the weighted measure
  have h_measurable : AEStronglyMeasurable smooth_func (weightedMeasure σ) :=
    smooth_convolution_measurable smooth_func h_smooth

  have h_L2 : MemLp smooth_func 2 (weightedMeasure σ) := by
    -- Use the new lemma for smooth mollifier convolutions
    apply smooth_mollifier_convolution_memLp
    · exact hφ_smooth
    · exact hφ_supp
    · exact hδ_pos
    · exact hn_pos
    · exact hδ_bound

  -- Create the Lp function
  let g_lp : Lp ℂ 2 (weightedMeasure σ) := MemLp.toLp smooth_func h_L2
  -- Note: Hσ σ = Lp ℂ 2 (mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))
  -- while weightedMeasure σ = mulHaar.withDensity (weightFunction σ)
  -- where weightFunction σ x = if x > 0 then ENNReal.ofReal (x ^ (2 * σ - 1)) else 0
  -- These are equal on the support of mulHaar which is (0, ∞)
  let g : Hσ σ := cast (by rw [h_eq]) g_lp

  -- Step 7: Show g satisfies the requirements
  use g
  constructor
  · -- g is in the smooth compactly supported set
    simp only [Set.mem_setOf]
    -- The underlying function of g is smooth_func (up to a.e. equality)
    use smooth_func
    refine ⟨h_support_left, h_support, h_smooth, ?_⟩
    intro x hx
    -- Hσ.toFun g x should equal smooth_func x (at least a.e.)
    -- This follows from the construction of g_lp from smooth_func
    -- Note: We need pointwise equality here, which requires continuity
    -- Apply the lemma for continuous functions
    have h_cont : Continuous smooth_func := h_smooth.continuous
    exact continuous_lp_pointwise smooth_func h_cont h_L2 h_eq x hx
  · -- Distance estimate: dist f g < ε
    exact mollified_approximation_distance ε hε f s f' hs_close n hn_pos hn_large h_eq g smooth_func h_L2 rfl

/-- Smooth compactly supported functions are dense in Hσ -/
lemma smooth_compactly_supported_dense_in_Hσ (σ : ℝ) :
    Dense {f : Hσ σ | ∃ φ : ℝ → ℂ,
      (∀ x ≤ 0, φ x = 0) ∧
      (∃ R > 0, ∀ x ≥ R, φ x = 0) ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      ∀ x > 0, Hσ.toFun f x = φ x} := by
  -- The strategy is to use the density of simple functions and then smooth them
  rw [Metric.dense_iff]
  intro f ε hε

  -- Step 1: Use the fact that simple functions are dense in L²
  have hδ : 0 < ε / 3 := by linarith

  -- First approximate by a simple function using Lp.simpleFunc.isDenseEmbedding
  -- Note: Hσ σ = Lp ℂ 2 (weightedMeasure σ)
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have h_simple_dense := @Lp.simpleFunc.isDenseEmbedding ℝ ℂ _ _ 2 (weightedMeasure σ) _
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

  -- Get a simple function approximation using the density
  -- isDenseEmbedding means the embedding is dense, so we can approximate
  -- We use the fact that the image is dense
  -- First, we need to transport f from Hσ to Lp with weightedMeasure
  -- Note: weightedMeasure σ = mulHaar.withDensity (weightFunction σ) by definition
  -- and Hσ σ is defined with mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))
  -- Since mulHaar is supported on (0,∞), the weight functions agree on the support
  have heq : weightedMeasure σ =
      mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))) := by
    simp only [weightedMeasure]
    -- Use withDensity_congr_ae: if f =ᵐ[μ] g then μ.withDensity f = μ.withDensity g
    apply MeasureTheory.withDensity_congr_ae
    -- Show that weightFunction σ =ᵐ[mulHaar] fun x => ENNReal.ofReal (x ^ (2 * σ - 1))
    -- Since mulHaar is supported on (0,∞), we only need agreement there
    have : ∀ᵐ x ∂mulHaar, 0 < x := by
      -- mulHaar = (volume.withDensity fun x => ENNReal.ofReal (1/x)).restrict (Set.Ioi 0)
      simp only [mulHaar, ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (fun x hx => hx)
    filter_upwards [this] with x hx
    simp only [weightFunction, if_pos hx]
  let f' : Lp ℂ 2 (weightedMeasure σ) := by
    rw [heq]
    exact f
  -- Apply density directly to approximate f'
  obtain ⟨s, hs_close⟩ := exists_simple_func_approximation f' (ε / 3) hδ

  -- Step 2: Truncate the simple function to have compact support on (0,∞)
  -- Simple functions have finite range and are measurable, so we can truncate them
  -- to a bounded interval [1/n, n] for large enough n
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max 1 ‖f'‖)
  have hn_pos : 0 < n := by
    by_contra h
    push_neg at h
    have : n = 0 := Nat.eq_zero_of_le_zero h
    rw [this] at hn
    simp at hn
    have : max 1 ‖f'‖ ≥ 1 := le_max_left _ _
    linarith

  -- Create a truncated version that's zero outside [1/n, n]
  let truncate := fun x : ℝ => if 1/n < x ∧ x < n then Lp.simpleFunc.toSimpleFunc s x else 0

  -- The truncated function is still in L² and close to s for large n
  have h_truncate_mem : MemLp truncate 2 (weightedMeasure σ) := truncated_simple_func_mem_Lp s n

  -- Convert to Hσ using the measure equality
  have h_truncate_mem' : MemLp truncate 2
      (mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) := by
    rw [← heq]
    exact h_truncate_mem

  let g₁ : Hσ σ := MemLp.toLp truncate h_truncate_mem'

  -- Step 3: Use the lemma to get a smooth approximation
  obtain ⟨g, hg_mem, hg_close⟩ :=
    smooth_approximation_of_truncated_simple f ε hε s f' hs_close n hn_pos hn heq
  have hg_ball : g ∈ Metric.ball f ε := by
    simp only [Metric.ball, Set.mem_setOf]
    rw [dist_comm]
    exact hg_close
  exact ⟨g, hg_ball, hg_mem⟩

/-- Schwartz functions can approximate smooth compactly supported functions in Hσ norm -/
lemma schwartz_approximates_smooth_compactly_supported :
    ∀ φ : ℝ → ℂ,
    (∀ x ≤ 0, φ x = 0) →
    (∃ R > 0, ∀ x ≥ R, φ x = 0) →
    ContDiff ℝ (⊤ : ℕ∞) φ →
    ∀ ε > 0, ∃ g : SchwartzMap ℝ ℂ,
      ∀ x > 0, ‖φ x - g x‖ < ε := by
  intro φ h_left h_right h_smooth ε hε
  -- Since φ has compact support and is smooth, we can extend it to a Schwartz function
  -- The key is that φ is already 0 outside a compact set, so we just need to
  -- construct a Schwartz function that agrees with φ on its support

  -- Get the support bound
  obtain ⟨R, hR_pos, hR⟩ := h_right

  -- Construct a Schwartz function that equals φ on (0, R)
  -- We use a cutoff function to extend φ to a Schwartz function

  -- First, we need a smooth cutoff function that is 1 on [0, R] and decays rapidly
  -- Let χ be a smooth function that is 1 on [0, R+1] and 0 outside [0, R+2]
  -- with rapid decay outside the support

  -- Define the extended function
  let φ_extended : ℝ → ℂ := fun x =>
    if x ≤ 0 then 0
    else if x ≥ R then 0
    else φ x

  -- The extended function is smooth and compactly supported
  -- Now we need to mollify it to get a Schwartz function

  -- For the approximation, we can use the fact that smooth compactly supported
  -- functions can be approximated by Schwartz functions in the sup norm
  -- This is a standard result in distribution theory

  -- Use the existence of Schwartz approximations for smooth compactly supported functions
  -- This would typically use convolution with a mollifier and decay multiplication

  -- We claim there exists a Schwartz function g that approximates φ_extended
  -- For the proof, we need the following fact:
  -- Any smooth compactly supported function can be approximated uniformly
  -- by Schwartz functions

  -- Since φ is smooth with compact support in [0, R], and ε > 0,
  -- we can find a Schwartz function g such that |φ(x) - g(x)| < ε for all x

  -- The construction would involve:
  -- 1. Extending φ smoothly to all of ℝ (keeping it 0 outside [0, R])
  -- 2. Multiplying by a rapidly decreasing smooth function
  -- 3. Adjusting to ensure all derivatives decay rapidly

  -- For now, we postulate the existence of such a g
  classical

  -- Mathematical fact: smooth compactly supported functions are dense in Schwartz space
  -- and can be approximated in uniform norm

  -- Since φ has compact support in [0, R] and is smooth, it can be viewed as
  -- a Schwartz function (all derivatives vanish outside [0, R])

  -- We need to use the fact that C₀^∞(ℝ) ⊆ S(ℝ)
  -- where C₀^∞ is smooth compactly supported and S is Schwartz

  -- The key insight: φ already satisfies the Schwartz conditions
  -- because it's 0 outside a compact set

  -- For the construction, we would:
  -- 1. Use that φ extended by 0 is already rapidly decreasing
  -- 2. Apply a smoothing if needed at the boundary
  -- 3. Use the fact that SchwartzMap allows functions that are 0 outside compact sets

  -- This requires the API for constructing SchwartzMap from a function
  -- that we know satisfies the Schwartz conditions

  -- We need to construct a Schwartz function that approximates φ
  -- The key insight: φ with compact support [0, R] is already Schwartz-like

  -- Strategy: Use mollification to create a Schwartz function
  -- that equals φ on most of (0, R) and decays rapidly outside

  -- For the approximation, we use the fact that for any ε > 0,
  -- we can find a Schwartz function g such that:
  -- 1. g(x) = φ(x) for x ∈ [ε, R - ε]
  -- 2. |g(x) - φ(x)| < ε for x ∈ (0, R)
  -- 3. g has rapid decay outside [0, R + ε]

  -- Since we don't have the explicit constructor, we assert existence
  -- based on the mathematical fact that C₀^∞ ⊂ S (Schwartz space)

  -- Classical existence argument
  have h_exists : ∃ g : SchwartzMap ℝ ℂ, ∀ x > 0, ‖φ x - g x‖ < ε := by
    -- The existence follows from density of Schwartz functions
    -- in the space of continuous functions with compact support
    -- when equipped with the uniform norm

    -- Mathematical justification:
    -- 1. φ is smooth with compact support [0, R]
    -- 2. Extend φ by 0 outside [0, R]
    -- 3. Convolve with a mollifier to get smoothness at boundaries
    -- 4. Multiply by exp(-x²) for x > R + 1 to ensure rapid decay
    -- 5. The result is a Schwartz function approximating φ

    -- Detailed construction outline:
    -- Let η_δ be a mollifier with support in [-δ, δ] where δ = ε/2
    -- Define g₁(x) = ∫ φ(y) * η_δ(x - y) dy (convolution)
    -- Then g₁ is smooth and approximates φ within ε/2

    -- For rapid decay, define:
    -- g(x) = g₁(x) * χ(x) * exp(-α*x²)
    -- where χ is a smooth cutoff function that is 1 on [0, R+1]
    -- and α > 0 is chosen small enough that the approximation holds

    -- The resulting g is in SchwartzMap ℝ ℂ because:
    -- - It's smooth (product of smooth functions)
    -- - Has rapid decay (exponential factor dominates)
    -- - All derivatives decay rapidly

    sorry -- This requires the explicit SchwartzMap constructor

  obtain ⟨g, hg⟩ := h_exists
  exact ⟨g, hg⟩

/-- Schwartz functions restricted to (0,∞) -/
def SchwartzRestricted : Set (ℝ → ℂ) :=
  {f | ∃ g : SchwartzMap ℝ ℂ, ∀ x > 0, f x = g x}

/-- Schwartz functions are dense in Hσ for appropriate σ -/
theorem schwartz_dense_in_Hσ (σ : ℝ) (hσ : 1 / 2 < σ ∧ σ < 1) :
    Dense {f : Hσ σ | ∃ g : SchwartzMap ℝ ℂ, ∀ x > 0, Hσ.toFun f x = g x} := by
  -- Strategy: Show that for any f ∈ Hσ and ε > 0, there exists a Schwartz function g
  -- such that ‖f - g‖_{Hσ} < ε

  -- First show that smooth compactly supported functions are dense
  have h_smooth_dense := smooth_compactly_supported_dense_in_Hσ σ

  -- Combine the two results using density arguments
  apply dense_iff_inter_open.mpr
  intro U hU hne

  -- Step 1: Use h_smooth_dense to find a smooth compactly supported function in U
  have h_inter : (U ∩ {f : Hσ σ | ∃ φ : ℝ → ℂ,
      (∀ x ≤ 0, φ x = 0) ∧
      (∃ R > 0, ∀ x ≥ R, φ x = 0) ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      ∀ x > 0, Hσ.toFun f x = φ x}).Nonempty :=
    dense_iff_inter_open.mp h_smooth_dense U hU hne

  -- Step 2: Extract a witness from the nonempty intersection
  obtain ⟨f_smooth, hf_in_inter⟩ := h_inter
  obtain ⟨hf_in_U, hf_smooth⟩ := hf_in_inter

  -- Step 3: Extract the smooth function φ from f_smooth's property
  obtain ⟨φ, hφ_zero, ⟨R, hR, hφ_compact⟩, hφ_smooth, hφ_eq⟩ := hf_smooth

  -- Then show that Schwartz functions can approximate smooth compactly supported functions
  have h_schwartz_approx :=
    schwartz_approximates_smooth_compactly_supported φ hφ_zero ⟨R, hR, hφ_compact⟩ hφ_smooth

  -- Step 4: Use h_schwartz_approx to find a Schwartz approximation
  -- We need to choose ε small enough so that the Schwartz approximation stays in U
  -- This requires more work on the metric structure and continuity
  sorry

/-- Smooth compactly supported functions on (0,∞) are dense in Hσ -/
theorem smooth_compactly_supported_dense (σ : ℝ) :
    ∃ S : Set (Hσ σ), DenseRange (fun x : S => (x : Hσ σ)) := by
  -- Standard approximation argument
  sorry

end DenseSubspaces

section OperatorDomain

/-- Domain of unbounded operators on Hσ -/
structure UnboundedOperatorDomain (σ : ℝ) where
  carrier : Set (Hσ σ)
  dense : DenseRange (fun x : carrier => (x : Hσ σ))
  measurable : ∀ f ∈ carrier, Measurable ((f : ℝ → ℂ))

/-- The Frourio operator maps Hσ to Hσ₋₁ -/
def frourioOperatorDomain (σ : ℝ) : UnboundedOperatorDomain σ := {
  carrier := {f : Hσ σ | sorry} -- Domain conditions
  dense := sorry
  measurable := sorry
}

end OperatorDomain

end Frourio
