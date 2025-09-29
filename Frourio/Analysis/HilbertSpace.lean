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

/-- `weightedMeasure σ` assigns positive mass to any open interval contained in `(0, ∞)` -/
lemma weightedMeasure_pos_of_Ioo {σ a b : ℝ} (ha : 0 < a) (hb : a < b) :
    0 < weightedMeasure σ (Set.Ioo a b) := by
  classical
  have h_meas : MeasurableSet (Set.Ioo a b) := measurableSet_Ioo
  have h_inter : Set.Ioo a b ∩ Set.Ioi (0 : ℝ) = Set.Ioo a b := by
    ext x; constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, ha.trans hx.1⟩
  have h_apply := weightedMeasure_apply σ (Set.Ioo a b) h_meas
  simp [h_inter] at h_apply
  -- rewrite the integral in terms of a positive constant
  set p : ℝ := 2 * σ - 2
  set c : ℝ := if p ≤ 0 then b ^ p else a ^ p
  have ha_le_b : a ≤ b := le_of_lt hb
  have hb_pos : 0 < b := lt_trans ha hb
  have hc_pos : 0 < c := by
    by_cases hp : p ≤ 0
    · have hb' : 0 < b := hb_pos
      have := Real.rpow_pos_of_pos hb' p
      simpa [c, hp] using this
    · have hp_nonneg : 0 ≤ p := le_of_lt (lt_of_not_ge hp)
      have := Real.rpow_pos_of_pos ha p
      simpa [c, hp, not_le.mpr (lt_of_not_ge hp), hp_nonneg] using this
  have h_pointwise : ∀ x ∈ Set.Ioo a b,
      ENNReal.ofReal c ≤ ENNReal.ofReal (x ^ p) := by
    intro x hx
    have hx_pos : 0 < x := lt_trans ha hx.1
    have hx_le_b : x ≤ b := le_of_lt hx.2
    have ha_le_x : a ≤ x := le_of_lt hx.1
    by_cases hp : p ≤ 0
    · have hmono := Real.rpow_le_rpow_of_exponent_nonpos hx_pos hx_le_b hp
      have hb_pow_pos : 0 ≤ b ^ p := Real.rpow_nonneg (le_of_lt hb_pos) p
      have hx_pow_pos : 0 ≤ x ^ p := Real.rpow_nonneg (le_of_lt hx_pos) p
      have hcmp : b ^ p ≤ x ^ p := hmono
      have hc_def : c = b ^ p := by simp [c, hp]
      simpa [hc_def, ENNReal.ofReal_eq_ofReal_iff, hb_pow_pos, hx_pow_pos] using hcmp
    · have hp_nonneg : 0 ≤ p := le_of_lt (lt_of_not_ge hp)
      have hmono := Real.rpow_le_rpow (le_of_lt ha) ha_le_x hp_nonneg
      have ha_pow_pos : 0 ≤ a ^ p := Real.rpow_nonneg (le_of_lt ha) p
      have hx_pow_pos : 0 ≤ x ^ p := Real.rpow_nonneg (le_of_lt hx_pos) p
      have hcmp : a ^ p ≤ x ^ p := hmono
      have hc_def : c = a ^ p := by simp [c, hp]
      simpa [hc_def, ENNReal.ofReal_eq_ofReal_iff, ha_pow_pos, hx_pow_pos] using hcmp
  -- lower-bound the integral by the integral of the positive constant `c`
  have h_const_le : (∫⁻ x in Set.Ioo a b, ENNReal.ofReal c ∂volume)
      ≤ ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (x ^ p) ∂volume :=
    setLIntegral_mono' h_meas (fun x hx => h_pointwise x hx)
  have h_const_integral :
      ∫⁻ x in Set.Ioo a b, ENNReal.ofReal c ∂volume
        = ENNReal.ofReal c * volume (Set.Ioo a b) :=
    setLIntegral_const _ _
  have h_volume_pos : 0 < volume (Set.Ioo a b) := by
    simp [Real.volume_Ioo, sub_pos.mpr hb]
  have h_const_pos : 0 < ENNReal.ofReal c := by
    simpa using ENNReal.ofReal_pos.mpr hc_pos
  have h_integral_pos : 0 < ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (x ^ p) ∂volume := by
    refine lt_of_lt_of_le ?_ h_const_le
    have h_mul_pos : 0 < ENNReal.ofReal c * volume (Set.Ioo a b) :=
      ENNReal.mul_pos (ne_of_gt h_const_pos) (ne_of_gt h_volume_pos)
    simpa [h_const_integral] using h_mul_pos
  simpa [h_apply] using h_integral_pos

/-- If a continuous function agrees almost everywhere with a constant,
  it is constant on `(0, ∞)`. -/
lemma continuous_ae_eq_const_on_pos {σ : ℝ} {f : ℝ → ℂ} {c : ℂ}
    (hf : Continuous f)
    (h_ae : (fun x => f x) =ᵐ[weightedMeasure σ] fun _ => c) :
    ∀ x > 0, f x = c := by
  classical
  set μ := weightedMeasure σ
  intro x hx_pos
  set U := {y : ℝ | f y ≠ c}
  have hU_open : IsOpen U := by
    have h_pre : U = f ⁻¹' ({c}ᶜ) := by
      ext y; rfl
    have h_open : IsOpen ({c}ᶜ) := isClosed_singleton.isOpen_compl
    simpa [h_pre] using hf.isOpen_preimage (s := {c}ᶜ) h_open
  have hU_null : μ U = 0 := by
    have : μ ({y : ℝ | f y = c}ᶜ) = 0 := by
      simpa [ae_iff, Set.compl_setOf] using h_ae
    simpa [U, Set.compl_setOf] using this
  by_contra hx_ne
  have hx_mem : x ∈ U := by simpa [U] using hx_ne
  obtain ⟨δ, hδ_pos, hδ_subset⟩ := Metric.isOpen_iff.mp hU_open x hx_mem
  set ε₀ : ℝ := min δ (x / 2)
  have hε₀_le_δ : ε₀ ≤ δ := min_le_left _ _
  have hε₀_le_half : ε₀ ≤ x / 2 := min_le_right _ _
  have hε₀_pos : 0 < ε₀ := by
    by_cases hcase : δ ≤ x / 2
    · have h_eq : ε₀ = δ := by simp [ε₀, hcase]
      simpa [h_eq] using hδ_pos
    · have hx2_le : x / 2 ≤ δ := le_of_lt (lt_of_not_ge hcase)
      have h_eq : ε₀ = x / 2 := by simp [ε₀, hx2_le]
      simpa [h_eq] using half_pos hx_pos
  have h_ball_small : Metric.ball x ε₀ ⊆ U :=
    (Metric.ball_subset_ball hε₀_le_δ).trans hδ_subset
  have h_interval_subset : Set.Ioo (x - ε₀) (x + ε₀) ⊆ U := by
    intro y hy
    have hy_abs : |y - x| < ε₀ := by
      have hy_lt : y - x < ε₀ := by
        have := sub_lt_sub_right hy.2 x
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hy_gt : -ε₀ < y - x := by
        have := sub_lt_sub_right hy.1 x
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hy_range : -ε₀ < y - x ∧ y - x < ε₀ := ⟨hy_gt, hy_lt⟩
      simpa [sub_eq_add_neg] using abs_lt.mpr hy_range
    have hy_mem : y ∈ Metric.ball x ε₀ := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy_abs
    exact h_ball_small hy_mem
  have ha_pos : 0 < x - ε₀ := by
    have hx_lt : ε₀ < x := lt_of_le_of_lt hε₀_le_half (half_lt_self hx_pos)
    exact sub_pos.mpr hx_lt
  have hb_pos : x - ε₀ < x + ε₀ := by
    have hpos : 0 < 2 * ε₀ := by
      have : (0 : ℝ) < 2 := by norm_num
      exact mul_pos this hε₀_pos
    have := lt_add_of_pos_right (x - ε₀) hpos
    simpa [two_mul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  have h_measure_pos := weightedMeasure_pos_of_Ioo (σ := σ) ha_pos hb_pos
  have h_measure_zero : μ (Set.Ioo (x - ε₀) (x + ε₀)) = 0 := by
    have h_le_zero : μ (Set.Ioo (x - ε₀) (x + ε₀)) ≤ μ U := measure_mono h_interval_subset
    have : μ (Set.Ioo (x - ε₀) (x + ε₀)) ≤ 0 := by simpa [hU_null] using h_le_zero
    exact le_antisymm this bot_le
  simp [μ, h_measure_zero] at h_measure_pos

/-- If two continuous functions agree almost everywhere for the weighted measure,
they coincide on `(0, ∞)`. -/
lemma continuous_ae_eq_on_pos {σ : ℝ} {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (h_ae : f =ᵐ[weightedMeasure σ] g) :
    ∀ x > 0, f x = g x := by
  classical
  have h_diff : (fun x => f x - g x) =ᵐ[weightedMeasure σ] fun _ => (0 : ℂ) := by
    refine h_ae.mono ?_
    intro x hx
    simp [hx]
  have h_const :=
    continuous_ae_eq_const_on_pos (σ := σ) (f := fun x => f x - g x)
      (hf := hf.sub hg) (c := (0 : ℂ)) h_diff
  intro x hx
  have h_eval := h_const x hx
  exact sub_eq_zero.mp h_eval

/-- Coercion of cast between Lp spaces with equal measures -/
lemma coe_cast_eq {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞}
    [NormedAddCommGroup E] {μ ν : Measure α} (h : μ = ν) (f : Lp E p μ) :
    ((cast (by rw [h]) f : Lp E p ν) : α → E) =ᵐ[μ] (f : α → E) := by
  subst h
  rfl

lemma Hσ_cast_preserves_ae {σ : ℝ} (f : ℝ → ℂ)
    (h_L2 : MemLp f 2 (weightedMeasure σ))
    (h_eq : weightedMeasure σ = mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) :
    let g_lp := MemLp.toLp f h_L2
    let g := cast (by rw [h_eq]) g_lp
    (Hσ.toFun g : ℝ → ℂ) =ᵐ[weightedMeasure σ] (MemLp.toLp f h_L2 : ℝ → ℂ) := by
  set g_lp := MemLp.toLp f h_L2
  set g := cast (by rw [h_eq]) g_lp
  -- Hσ.toFun unfolds to the coercion
  change (g : ℝ → ℂ) =ᵐ[weightedMeasure σ] (g_lp : ℝ → ℂ)
  -- Apply the lemma about cast preserving coercions
  exact coe_cast_eq h_eq g_lp

/-- Cast preserves a.e. equality for Lp functions -/
lemma cast_preserves_ae_eq {σ : ℝ}
    (h_eq : weightedMeasure σ = mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))
    (f : ℝ → ℂ)
    (h_L2 : MemLp f 2 (weightedMeasure σ)) :
    let g_lp := MemLp.toLp f h_L2
    let g := cast (by rw [h_eq]) g_lp
    (Hσ.toFun g : ℝ → ℂ) =ᵐ[weightedMeasure σ] f := by
  classical
  set g_lp := MemLp.toLp f h_L2
  set g := cast (by rw [h_eq]) g_lp
  -- fundamental property of the canonical representative
  have h1 : (MemLp.toLp f h_L2 : ℝ → ℂ) =ᵐ[weightedMeasure σ] f :=
    MemLp.coeFn_toLp h_L2
  -- casting along a measure equality preserves the underlying function
  have h_pointwise := Hσ_cast_preserves_ae f h_L2 h_eq
  exact h_pointwise.trans h1

/-- Helper function: Create mollifier with support on [-δ, δ] -/
noncomputable def create_mollifier (δ : ℝ) : ℝ → ℝ :=
  let Z := ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2))
  fun x => if |x| < δ then Real.exp (-1 / (δ^2 - x^2)) / Z else 0

/-- Powers of 2 are at least 1 -/
lemma one_le_two_pow (k : ℕ) : (1 : ℝ) ≤ 2^k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    simp only [pow_succ]
    linarith [ih]

/-- The decay property required for SchwartzMap construction -/
lemma schwartz_map_decay_from_bounds (f : ℝ → ℂ)
    (hf_decay : ∀ (k n : ℕ), ∃ C > 0, ∀ x : ℝ, (1 + ‖x‖)^k * ‖iteratedDeriv n f x‖ ≤ C) :
    ∀ (p : ℕ × ℕ), ∃ C > 0, ∀ x : ℝ, (1 + ‖x‖)^p.1 * ‖iteratedDeriv p.2 f x‖ ≤ C := by
  -- This directly follows from hf_decay by taking p = (k, n)
  intro ⟨k, n⟩
  exact hf_decay k n

/-- Convolution with a smooth compactly supported mollifier preserves smoothness -/
lemma contDiff_convolution_mollifier {φ : ℝ → ℂ} {η : ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y, (η y : ℂ) * φ (x - y)) := by
  -- Convert η to a complex-valued function
  have hη_smooth' : ContDiff ℝ (⊤ : ℕ∞) (fun y => (η y : ℂ)) := by
    -- The coercion from ℝ to ℂ is smooth
    have : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) := by
      -- The coercion from ℝ to ℂ is a continuous linear isometry, hence smooth
      exact Complex.ofRealLI.contDiff
    exact ContDiff.comp this hη_smooth
  -- The convolution is defined as the integral we have
  -- We need to relate our integral to the standard convolution operation
  -- First, we need to show that η has compact support in complex form
  have hη_supp' : HasCompactSupport (fun y => (η y : ℂ)) := by
    -- The support doesn't change when we cast to complex
    rw [HasCompactSupport]
    -- We need to show: IsCompact (tsupport (fun y => (η y : ℂ)))
    -- This is the same as IsCompact (tsupport η) since casting to ℂ preserves zeros
    have h_eq : tsupport (fun y => (η y : ℂ)) = tsupport η := by
      -- tsupport f = closure (support f)
      simp only [tsupport]
      -- Now show support (fun y => (η y : ℂ)) = support η
      ext y
      -- y ∈ closure (support (fun y => (η y : ℂ))) ↔ y ∈ closure (support η)
      -- This follows because support (fun y => (η y : ℂ)) = support η
      have h_supp_eq : Function.support (fun y => (η y : ℂ)) = Function.support η := by
        ext z
        rw [Function.mem_support, Function.mem_support]
        rw [Complex.ofReal_ne_zero]
      rw [h_supp_eq]
    rw [h_eq]
    exact hη_supp
  -- Now we can apply the convolution smoothness theorem
  -- The integral ∫ y, (η y : ℂ) * φ (x - y) is a convolution
  -- We need to rewrite it in the standard convolution form
  -- Standard convolution is (f ⋆ g) x = ∫ y, f y * g (x - y)
  -- So we have (η' ⋆ φ) where η' y = (η y : ℂ)

  -- First establish that φ is locally integrable
  have hφ_loc : LocallyIntegrable φ volume := by
    -- A smooth function is continuous, hence locally integrable
    exact hφ.continuous.locallyIntegrable

  -- Now apply the convolution smoothness theorem
  -- The convolution of a compactly supported smooth function with
  -- a locally integrable smooth function is smooth

  -- We use the theorem that f ⋆[L, μ] g is smooth when:
  -- - f has compact support and is smooth
  -- - g is locally integrable
  -- - L is a continuous bilinear map (here multiplication)

  -- The integral ∫ y, (η y : ℂ) * φ (x - y) is exactly the convolution
  -- (fun y => (η y : ℂ)) ⋆[mul ℝ ℂ, volume] φ

  -- Apply the convolution smoothness theorem
  -- The integral ∫ y, (η y : ℂ) * φ (x - y) is the convolution
  -- We need to show this convolution is smooth

  -- Since (fun y => (η y : ℂ)) has compact support and is smooth,
  -- and φ is locally integrable, the convolution is smooth
  suffices h : ContDiff ℝ (⊤ : ℕ∞)
    (MeasureTheory.convolution (fun y => (η y : ℂ)) φ
      (ContinuousLinearMap.mul ℝ ℂ) volume) by
    -- The convolution equals our integral
    -- We need to show: fun x => ∫ y, (η y : ℂ) * φ (x - y)
    --               = MeasureTheory.convolution (fun y => (η y : ℂ)) φ (mul ℝ ℂ) volume

    -- The convolution is defined as:
    -- convolution f g L μ = fun x => ∫ y, L (f y) (g (x - y)) ∂μ
    -- With L = mul ℝ ℂ, this becomes: fun x => ∫ y, (f y) * (g (x - y))
    -- Which is exactly our integral with f = (fun y => (η y : ℂ)) and g = φ

    -- This follows from the definition of convolution with multiplication
    -- We need to show the functions are equal
    have eq : (fun x => ∫ y, (η y : ℂ) * φ (x - y)) =
              MeasureTheory.convolution (fun y => (η y : ℂ)) φ
                (ContinuousLinearMap.mul ℝ ℂ) volume := by
      funext x
      -- Unfold the definition of convolution
      simp only [MeasureTheory.convolution]
      -- ContinuousLinearMap.mul applies multiplication
      simp only [ContinuousLinearMap.mul_apply']
      -- The integrals are now identical
    rw [eq]
    exact h

  -- Apply the convolution smoothness theorem
  apply hη_supp'.contDiff_convolution_left
  · exact hη_smooth'
  · exact hφ_loc

/-- Schwartz functions restricted to (0,∞) -/
def SchwartzRestricted : Set (ℝ → ℂ) :=
  {f | ∃ g : SchwartzMap ℝ ℂ, ∀ x > 0, f x = g x}

end DenseSubspaces

section OperatorDomain

/-- Domain of unbounded operators on Hσ -/
structure UnboundedOperatorDomain (σ : ℝ) where
  carrier : Set (Hσ σ)
  dense : DenseRange (fun x : carrier => (x : Hσ σ))
  measurable : ∀ f ∈ carrier, Measurable ((f : ℝ → ℂ))

end OperatorDomain

end Frourio
