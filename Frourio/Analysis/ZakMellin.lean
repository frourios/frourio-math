import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Frourio.Analysis.QuadraticForm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Module.Basic

open MeasureTheory
open scoped ENNReal Topology BigOperators

namespace Frourio

/-!
Step 3: Discretization of the quadratic form via Zak coefficients (design-level).

We define a discrete quadratic form `Qdisc` indexed by the lattice steps and
provide a bounds predicate `Q_bounds` that will relate it to the continuous
quadratic form `Qℝ`. At this phase, `Qdisc` is a placeholder and the bounds are
recorded as a `Prop` to be supplied in later phases using frame inequalities
and boundedness assumptions on `K`.
-/

/-- Discrete quadratic form built from `K` and Zak coefficients (placeholder 0). -/
noncomputable def Qdisc (K : ℝ → ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ := 0

/-- Bounds predicate connecting the continuous and discrete quadratic forms. -/
def Q_bounds (K : ℝ → ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ) : Prop :=
  ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 ≤ c2 ∧
    ∀ g : Lp ℂ 2 (volume : Measure ℝ),
      c1 * Qℝ K g ≤ Qdisc K w Δτ Δξ g ∧ Qdisc K w Δτ Δξ g ≤ c2 * Qℝ K g

end Frourio

namespace Frourio

open MeasureTheory

/-!
Phase 1.1: Zak–Mellin frame building blocks (function-level forms + L² stubs).

We introduce the intended time-shift and modulation operators at the function
level and keep the `Lp`-level maps as identity placeholders to preserve the API
while avoiding heavy measure-theoretic proofs in this phase.
-/

/-- Function-level time shift: `(timeShiftFun τ g) t = g (t - τ)`. -/
noncomputable def timeShiftFun (τ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => g (t - τ)

/-- Function-level modulation: `(modFun ξ g) t = exp(i ξ t) · g t`. -/
noncomputable def modFun (ξ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * g t

/-!
Step 1: translation map and basic measurability/measure-preserving skeleton.
These will support the manual lifting to `Lp` in subsequent steps.
-/

-- Translation map on ℝ
def translationMap (τ : ℝ) : ℝ → ℝ := fun t => t - τ

-- Measurability of translation
lemma measurable_translation (τ : ℝ) : Measurable (translationMap τ) :=
  (continuous_id.sub continuous_const).measurable

-- Translation is a measurable embedding (being a homeomorphism)
lemma measurableEmbedding_translation (τ : ℝ) :
    MeasurableEmbedding (translationMap τ) := by
  classical
  -- Build the homeomorphism `x ↦ x - τ` with inverse `y ↦ y + τ`
  let e : Homeomorph ℝ ℝ :=
  { toFun := fun x => x - τ
    invFun := fun y => y + τ
    left_inv := by intro x; simp
    right_inv := by intro y; simp
    continuous_toFun := (continuous_id.sub continuous_const)
    continuous_invFun := (continuous_id.add continuous_const) }
  simpa [translationMap] using e.measurableEmbedding

-- Translation is measure-preserving for Lebesgue measure
lemma translation_measurePreserving (τ : ℝ) :
    MeasurePreserving (translationMap τ) (μa := volume) (μb := volume) := by
  -- Use Mathlib's standard theorem for translation invariance
  -- translationMap τ = fun t => t - τ, which matches measurePreserving_sub_right
  have : translationMap τ = fun x => x - τ := by
    ext x
    simp [translationMap]
  rw [this]
  exact measurePreserving_sub_right volume τ

-- Pullback a.e. predicates along translation (measurable set version)
lemma ae_comp_translation_iff {p : ℝ → Prop}
    (hp : MeasurableSet {y | p y}) (τ : ℝ) :
    (∀ᵐ y ∂ (volume : Measure ℝ), p y)
      ↔ (∀ᵐ x ∂ (volume : Measure ℝ), p ((translationMap τ) x)) := by
  have hiff := ae_map_iff (μ := (volume : Measure ℝ))
    ((measurable_translation τ).aemeasurable) hp
  have hmp := translation_measurePreserving τ
  simpa [hmp.map_eq] using hiff

/-! Helper lemmas for transporting a.e. equalities along translations -/

-- If two functions are a.e. equal, then their compositions with a translation are a.e. equal.
lemma ae_comp_translation_of_ae_eq
    {u v : ℝ → ℂ} (τ : ℝ)
    (hu : AEStronglyMeasurable u (volume : Measure ℝ))
    (hv : AEStronglyMeasurable v (volume : Measure ℝ))
    (h : u =ᵐ[volume] v) :
    (fun x => u (x - τ)) =ᵐ[volume] (fun x => v (x - τ)) := by
  classical
  -- Take measurable representatives of u and v
  let u' : ℝ → ℂ := (hu.aemeasurable.mk u)
  let v' : ℝ → ℂ := (hv.aemeasurable.mk v)
  have hu' : u =ᵐ[volume] u' := hu.aemeasurable.ae_eq_mk
  have hv' : v =ᵐ[volume] v' := hv.aemeasurable.ae_eq_mk
  -- The disagreement set between u' and v' is measurable and null
  let S : Set ℝ := {y | u' y ≠ v' y}
  have hS_meas : MeasurableSet S := by
    -- S = preimage of the complement of the diagonal under y ↦ (u' y, v' y)
    have hpair : Measurable (fun y => (u' y, v' y)) :=
      (hu.aemeasurable.measurable_mk.prodMk (hv.aemeasurable.measurable_mk))
    have hdiag : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
      isClosed_eq continuous_fst continuous_snd |>.measurableSet
    have : S = (fun y => (u' y, v' y)) ⁻¹' ({p : ℂ × ℂ | p.1 = p.2}ᶜ) := by
      ext y; simp [S]
    simpa [this] using (hdiag.compl.preimage hpair)
  have hS_null : volume S = 0 := by
    -- From u = v a.e., deduce u' = v' a.e., hence the equality set has full measure
    have hEq_ae : ∀ᵐ y ∂volume, u' y = v' y :=
      (hu'.symm.trans (h.trans hv'))
    -- The equality set is measurable: {u' = v'} = (u' - v')⁻¹' {0}
    have hEq_meas : MeasurableSet {y | u' y = v' y} := by
      have hsub : Measurable (fun y => u' y - v' y) :=
        (hu.aemeasurable.measurable_mk).sub (hv.aemeasurable.measurable_mk)
      have hzero : MeasurableSet ({0} : Set ℂ) :=
        (isClosed_singleton : IsClosed ({(0 : ℂ)} : Set ℂ)).measurableSet
      have hpre : MeasurableSet ((fun y => u' y - v' y) ⁻¹' ({0} : Set ℂ)) :=
        hzero.preimage hsub
      have : {y | u' y = v' y}
              = ((fun y => u' y - v' y) ⁻¹' ({0} : Set ℂ)) := by
        ext y; simp [Set.preimage, Set.mem_setOf_eq, sub_eq_zero]
      simpa [this]
    -- Convert a.e. equality to null complement via `ae_iff`
    have hEq_null : volume ({y | u' y = v' y}ᶜ) = 0 := by
      -- Use the predicate form of `ae_iff`: (∀ᵐ y, P y) ↔ μ {y | ¬ P y} = 0
      have hnull : volume {y | ¬ (u' y = v' y)} = 0 := by
        simpa using ((ae_iff (μ := (volume : Measure ℝ))).1 hEq_ae)
      simpa [Set.compl_setOf] using hnull
    -- Finally, {u' ≠ v'} ⊆ complement of equality set
    have hsubset : S ⊆ {y | u' y = v' y}ᶜ := by
      intro y hy; simpa [S] using hy
    exact measure_mono_null hsubset hEq_null
  -- Pull back the null set along translation using `ae_comp_translation_iff`
  have hpreim_null : volume ((translationMap τ) ⁻¹' S) = 0 := by
    -- From `volume S = 0`, get `∀ᵐ y, y ∈ Sᶜ` via predicate-form `ae_iff`
    have hS_ae_compl : (∀ᵐ y ∂(volume : Measure ℝ), y ∈ Sᶜ) := by
      -- Use predicate P y := y ∈ Sᶜ; then {y | ¬ P y} = S
      have hzero : (volume : Measure ℝ) {y | ¬ (y ∈ Sᶜ)} = 0 := by
        simpa [Set.compl_setOf] using hS_null
      exact ((ae_iff (μ := (volume : Measure ℝ)) (p := fun y : ℝ => y ∈ Sᶜ))).2 hzero
    -- Transport along the translation map
    have hpull : (∀ᵐ x ∂(volume : Measure ℝ), (translationMap τ x) ∈ Sᶜ) :=
      (ae_comp_translation_iff (hp := hS_meas.compl) τ).mp hS_ae_compl
    -- Convert back to measure-zero of the preimage S directly
    have : volume ((translationMap τ) ⁻¹' S) = 0 := by
      -- From ae[translationMap τ x ∈ Sᶜ], get μ {x | translationMap τ x ∈ S} = 0
      have := ((ae_iff (μ := (volume : Measure ℝ))).1 hpull)
      simpa [Set.preimage, Set.mem_setOf_eq] using this
    exact this
  -- Conclude the a.e. equality after composition: use `ae_iff` with predicate
  -- `p x := u (x - τ) = v (x - τ)` instead of rewriting.
  refine ((ae_iff (μ := (volume : Measure ℝ)) (p := fun x : ℝ => u (x - τ) = v (x - τ)))).2 ?_
  -- Reduce to showing the set of disagreement has measure zero
  -- Define auxiliary null sets coming from `u =ᵐ u'` and `v' =ᵐ v`.
  let Su : Set ℝ := {y | u y ≠ u' y}
  let Sv : Set ℝ := {y | v' y ≠ v y}
  have hSu_null : volume Su = 0 := by
    -- From `hu' : u =ᵐ[volume] u'`
    have : (∀ᵐ y ∂(volume : Measure ℝ), u y = u' y) := hu'
    have := ((ae_iff (μ := (volume : Measure ℝ)) (p := fun y : ℝ => u y = u' y))).1 this
    simpa [Su, Set.compl_setOf] using this
  have hSv_null : volume Sv = 0 := by
    -- From `hv' : v =ᵐ[volume] v'` rewritten
    have : (∀ᵐ y ∂(volume : Measure ℝ), v' y = v y) := hv'.symm
    have := ((ae_iff (μ := (volume : Measure ℝ)) (p := fun y : ℝ => v' y = v y))).1 this
    simpa [Sv, Set.compl_setOf] using this
  -- Pull back the null sets along translation
  have hpreim_Su : volume ((translationMap τ) ⁻¹' Su) = 0 := by
    -- Use measure preservation: preimage of a null set is null
    exact (translation_measurePreserving τ).preimage_null hSu_null
  have hpreim_Sv : volume ((translationMap τ) ⁻¹' Sv) = 0 := by
    exact (translation_measurePreserving τ).preimage_null hSv_null
  -- Show the disagreement set is contained in a finite union of null sets
  have hsubset_union :
      {x | u (x - τ) ≠ v (x - τ)} ⊆
        ((translationMap τ) ⁻¹' S) ∪ ((translationMap τ) ⁻¹' Su) ∪ ((translationMap τ) ⁻¹' Sv) := by
    intro x hx; classical
    by_cases h1 : u (x - τ) = u' (x - τ)
    · by_cases h3 : v' (x - τ) = v (x - τ)
      · -- then u' ≠ v' at x-τ, so x ∈ preimage S
        have : u' (x - τ) ≠ v' (x - τ) := by
          simpa [h1, h3] using hx
        have : (x - τ) ∈ S := by simpa [S] using this
        have hxS : x ∈ (translationMap τ) ⁻¹' S := by
          simpa [translationMap] using this
        exact Or.inl <| Or.inl hxS
      · -- x ∈ preimage Sv
        have : (x - τ) ∈ Sv := by simpa [Sv] using h3
        have hxSv : x ∈ (translationMap τ) ⁻¹' Sv := by
          simpa [translationMap] using this
        exact Or.inr hxSv
    · -- x ∈ preimage Su
      have : (x - τ) ∈ Su := by simpa [Su] using h1
      have hxSu : x ∈ (translationMap τ) ⁻¹' Su := by
        simpa [translationMap] using this
      exact Or.inl <| Or.inr hxSu
  -- Conclude measure-zero via subadditivity on finite unions
  have hUnion2 :
      volume (((translationMap τ) ⁻¹' S) ∪ ((translationMap τ) ⁻¹' Su)) = 0 := by
    have hle := measure_union_le (μ := (volume : Measure ℝ)) ((translationMap τ) ⁻¹' S) ((translationMap τ) ⁻¹' Su)
    have : volume ((translationMap τ) ⁻¹' S) + volume ((translationMap τ) ⁻¹' Su) = 0 := by
      simpa [hpreim_null, hpreim_Su]
    have hle0 : volume (((translationMap τ) ⁻¹' S) ∪ ((translationMap τ) ⁻¹' Su)) ≤ 0 := by
      simpa [this]
        using hle
    -- Measures take values in `ENNReal`, which are nonnegative by `bot_le`.
    exact le_antisymm hle0 (by simpa using bot_le)
  have hUnion3 :
      volume ((((translationMap τ) ⁻¹' S) ∪ ((translationMap τ) ⁻¹' Su)) ∪ ((translationMap τ) ⁻¹' Sv)) = 0 := by
    have hle := measure_union_le (μ := (volume : Measure ℝ)) (((translationMap τ) ⁻¹' S) ∪ ((translationMap τ) ⁻¹' Su)) ((translationMap τ) ⁻¹' Sv)
    have hle0 : volume ((((translationMap τ) ⁻¹' S) ∪ ((translationMap τ) ⁻¹' Su)) ∪ ((translationMap τ) ⁻¹' Sv)) ≤ 0 := by
      have : volume (((translationMap τ) ⁻¹' S) ∪ ((translationMap τ) ⁻¹' Su)) = 0 := hUnion2
      simpa [this, hpreim_Sv] using hle
    -- Measures take values in `ENNReal`, which are nonnegative by `bot_le`.
    exact le_antisymm hle0 (by simpa using bot_le)
  -- Final: the target set is a subset of a null set
  exact measure_mono_null hsubset_union hUnion3

/-!  L² time shift as a continuous linear map.
At the function level it acts by `(timeShift τ g) t = g (t - τ)`.
We use translation_measurePreserving to construct the L² isometry. -/

-- Helper: Show that composition with translation preserves L² membership
lemma comp_translation_memLp (τ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun t => (f : ℝ → ℂ) (t - τ)) 2 (volume : Measure ℝ) := by
  -- Measurability + measure-preserving composition preserves L²-membership
  -- `Lp.memLp f` gives that the (ae-strongly measurable) representative of `f` is in L².
  -- Precomposing with a measure-preserving map keeps membership in `MemLp`.
  classical
  have hf : MemLp (fun t => (f : ℝ → ℂ) t) 2 (volume : Measure ℝ) := Lp.memLp f
  -- Use the library lemma for precomposition with a measure-preserving map
  exact hf.comp_measurePreserving (translation_measurePreserving τ)

-- Linear map for time shift on L²
noncomputable def timeShift_linearMap (τ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := MemLp.toLp (fun t => (f : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ f)
  map_add' := by
    intro f g
    -- Prove equality in `Lp` via a.e. equality of representatives
    apply Lp.ext
    classical
    -- LHS representative: coeFn of toLp for (f+g)∘translation
    have hL :
        (((MemLp.toLp (fun t => ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (t - τ))
              (comp_translation_memLp τ (f + g))) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume]
        (fun x => ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (x - τ)) := by
      simpa using
        (MemLp.coeFn_toLp (comp_translation_memLp τ (f + g)))
    -- RHS representative: sum of toLp's
    have hR_add :
        (((MemLp.toLp (fun t => (f : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ f)
              + MemLp.toLp (fun t => (g : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ g)) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume]
        (fun x =>
          (((MemLp.toLp (fun t => (f : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ f)) :
                Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
          + (((MemLp.toLp (fun t => (g : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ g)) :
                Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) := by
      exact Lp.coeFn_add _ _
    have hf :
        (((MemLp.toLp (fun t => (f : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ f)) :
              Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume]
        (fun x => (f : ℝ → ℂ) (x - τ)) := by
      simpa using (MemLp.coeFn_toLp (comp_translation_memLp τ f))
    have hg :
        (((MemLp.toLp (fun t => (g : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ g)) :
              Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume]
        (fun x => (g : ℝ → ℂ) (x - τ)) := by
      simpa using (MemLp.coeFn_toLp (comp_translation_memLp τ g))
    -- Pull back the a.e. identity for `Lp.coeFn_add` along the translation
    have hsum :
        (fun x => ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (x - τ))
          =ᵐ[volume]
        (fun x => (f : ℝ → ℂ) (x - τ) + (g : ℝ → ℂ) (x - τ)) := by
      -- Directly transport `Lp.coeFn_add` along translation
      refine (ae_comp_translation_of_ae_eq τ
        (Lp.aestronglyMeasurable (f + g))
        (by
          have hf := (Lp.aestronglyMeasurable f)
          have hg := (Lp.aestronglyMeasurable g)
          simpa using hf.add hg)
        (by simpa using (Lp.coeFn_add f g)))
    -- Build RHS pointwise sum via coeFn_add and representatives
    have hR_sum :
        (((MemLp.toLp (fun t => (f : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ f)
              + MemLp.toLp (fun t => (g : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ g)) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume]
        (fun x => (f : ℝ → ℂ) (x - τ) + (g : ℝ → ℂ) (x - τ)) := by
      exact hR_add.trans (hf.add hg)
    -- Chain the equalities: LHS → pointwise sum → RHS
    exact hL.trans (hsum.trans hR_sum.symm)
  map_smul' := by
    intro c f
    apply Lp.ext
    classical
    -- Left side representative
    have hL :
        (((MemLp.toLp (fun t => ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (t - τ))
              (comp_translation_memLp τ (c • f))) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume]
        (fun x => ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (x - τ)) := by
      simpa using
        (MemLp.coeFn_toLp (comp_translation_memLp τ (c • f)))
    -- Right side representative
    have hR :
        ((c • (MemLp.toLp (fun t => (f : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ f)) :
              Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume]
        (fun x => c • (((MemLp.toLp (fun t => (f : ℝ → ℂ) (t - τ))
                  (comp_translation_memLp τ f)) :
                Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) := by
      exact Lp.coeFn_smul _ _
    have hf :
        (((MemLp.toLp (fun t => (f : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ f)) :
              Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume]
        (fun x => (f : ℝ → ℂ) (x - τ)) := by
      simpa using (MemLp.coeFn_toLp (comp_translation_memLp τ f))
    -- Transport a.e. identity for scalar multiplication along translation
    have hsmul :
        (fun x => ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (x - τ))
          =ᵐ[volume]
        (fun x => c • (f : ℝ → ℂ) (x - τ)) := by
      refine (ae_comp_translation_of_ae_eq τ
        (Lp.aestronglyMeasurable (c • f))
        (by
          have hf := (Lp.aestronglyMeasurable f)
          simpa using hf.const_smul c)
        (by simpa using (Lp.coeFn_smul c f)))
    -- Normalize both sides to the same pointwise expression
    have hR' :
        ((c • (MemLp.toLp (fun t => (f : ℝ → ℂ) (t - τ)) (comp_translation_memLp τ f)) :
              Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
          =ᵐ[volume]
        (fun x => c • (f : ℝ → ℂ) (x - τ)) := by
      exact hR.trans (hf.mono (fun _ hx => by simp [hx]))
    exact hL.trans (hsmul.trans hR'.symm)

-- Isometry property of time shift
lemma timeShift_norm_eq (τ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖timeShift_linearMap τ f‖ = ‖f‖ := by
  classical
  -- Express both norms via lintegrals of squared norms
  have hLrep :
      (((timeShift_linearMap τ f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      (fun x => (f : ℝ → ℂ) (x - τ)) := by
    simpa [timeShift_linearMap]
      using (MemLp.coeFn_toLp (comp_translation_memLp τ f))
  -- Step 1: equate the squared norms under lintegral by AE congruence
  -- Avoid complex coercions by naming the representative
  let Fτ : ℝ → ℂ := fun x => (((timeShift_linearMap τ f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
  have h_sq_ae :
      ((fun x : ℝ => ((↑‖Fτ x‖₊ : ENNReal) ^ (2 : ℕ))) : ℝ → ENNReal)
        =ᵐ[volume]
      (fun x : ℝ => (↑‖(f : ℝ → ℂ) (x - τ)‖₊ : ENNReal) ^ (2 : ℕ)) := by
    refine hLrep.mono ?_
    intro x hx; simp [Fτ, hx]
  -- Step 2: change variables using the pushforward identity for translations
  have h_map : Measure.map (translationMap τ) (volume : Measure ℝ) = (volume : Measure ℝ) :=
    (translation_measurePreserving τ).map_eq
  -- Change variables via translation invariance using `lintegral_map`.
  -- Define the integrand to avoid parser confusion with unicode tokens.
  -- Use the fact that translation preserves the measure
  have h_change :
      (∫⁻ x, ((↑‖(f : ℝ → ℂ) (x - τ)‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ))
        = ∫⁻ y, ((↑‖(f : ℝ → ℂ) y‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ) := by
    -- Use the fact that translation by τ is measure preserving
    -- The integral of f(x - τ) equals the integral of f(y) by change of variables
    -- This is a standard result for translation-invariant measures
    calc (∫⁻ x, ((↑‖(f : ℝ → ℂ) (x - τ)‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ))
        = ∫⁻ x, ((↑‖(f : ℝ → ℂ) (translationMap τ x)‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ) := by
          simp [translationMap]
      _ = ∫⁻ y, ((↑‖(f : ℝ → ℂ) y‖₊ : ENNReal) ^ (2 : ℕ)) ∂(Measure.map (translationMap τ) (volume : Measure ℝ)) := by
          -- This uses the standard change of variables formula for lintegral
          -- We use the symmetry of lintegral_map
          symm
          -- Show the integrand is AEMeasurable
          have hf_aemeas := (Lp.aestronglyMeasurable f).aemeasurable
          have h_integrand : AEMeasurable (fun y => ((↑‖(f : ℝ → ℂ) y‖₊ : ENNReal) ^ (2 : ℕ))) (Measure.map (translationMap τ) (volume : Measure ℝ)) := by
            rw [h_map]
            refine AEMeasurable.pow ?_ ?_
            · apply AEMeasurable.coe_nnreal_ennreal
              apply AEMeasurable.nnnorm
              exact hf_aemeas
            · exact aemeasurable_const
          -- Apply the change of variables formula
          exact lintegral_map' h_integrand (aemeasurable_id'.comp_measurable (measurable_translation τ))
      _ = ∫⁻ y, ((↑‖(f : ℝ → ℂ) y‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ) := by
          rw [h_map]
  -- Step 3: translate equality of lintegrals of squares into equality of norms
  have h1 : ‖timeShift_linearMap τ f‖ ^ 2
      = (∫⁻ x, ((↑‖Fτ x‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ)).toReal := by
    simpa using (Lp_norm_sq_as_lintegral (ν := (volume : Measure ℝ)) (timeShift_linearMap τ f))
  have h2 : ‖f‖ ^ 2
      = (∫⁻ x, ((↑‖(f : ℝ → ℂ) x‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ)).toReal := by
    simpa using (Lp_norm_sq_as_lintegral (ν := (volume : Measure ℝ)) f)
  -- Use AE congruence and change of variables to match the integrals
  have h_eq_int :
      (∫⁻ x, ((↑‖Fτ x‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ))
        = ∫⁻ x, ((↑‖(f : ℝ → ℂ) x‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ) := by
    have hleft := lintegral_congr_ae h_sq_ae
    -- Use the change-of-variables identity.
    calc (∫⁻ x, ((↑‖Fτ x‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ))
        = ∫⁻ x, ((↑‖(f : ℝ → ℂ) (x - τ)‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ) := hleft
      _ = ∫⁻ x, ((↑‖(f : ℝ → ℂ) x‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ) := h_change
  -- Conclude from equality of squares and nonnegativity of norms
  have hsq : ‖timeShift_linearMap τ f‖ ^ 2 = ‖f‖ ^ 2 := by
    simpa [h1, h2, h_eq_int]
  have hsqrt := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq, norm_nonneg] using hsqrt

-- Final continuous linear map for time shift
noncomputable def timeShift (τ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous (timeShift_linearMap τ) 1 fun f => by
    rw [timeShift_norm_eq]
    simp

section VariableChangeFormulas

/-- Change of variables formula for integration: ∫f(t-τ) = ∫f(t) -/
lemma integral_comp_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (τ : ℝ) (hf : Integrable f (volume : Measure ℝ)) :
    ∫ t, f (t - τ) ∂(volume : Measure ℝ) = ∫ t, f t ∂(volume : Measure ℝ) := by
  -- Change of variables via measure-preserving + measurable embedding
  have hMP : MeasurePreserving (translationMap τ) (μa := volume) (μb := volume) :=
    translation_measurePreserving τ
  have hME : MeasurableEmbedding (translationMap τ) :=
    measurableEmbedding_translation τ
  -- Use mathlib's `MeasurePreserving.integral_comp`
  simpa [translationMap] using hMP.integral_comp hME f

/-- L^p norm is preserved under translation -/
lemma eLpNorm_comp_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (p : ENNReal) (τ : ℝ)
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    eLpNorm (fun t => f (t - τ)) p (volume : Measure ℝ) =
    eLpNorm f p (volume : Measure ℝ) := by
  -- Use the measure-preserving property
  have h_meas := translation_measurePreserving τ
  -- Rewrite using composition
  have : (fun t => f (t - τ)) = f ∘ (translationMap τ) := by
    ext t; simp [translationMap]
  rw [this]
  -- Apply the general result for measure-preserving maps
  exact eLpNorm_comp_measurePreserving hf h_meas

/-- Special case for L² norm -/
lemma L2_norm_comp_sub (f : ℝ → ℂ) (τ : ℝ)
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    eLpNorm (fun t => f (t - τ)) 2 (volume : Measure ℝ) =
    eLpNorm f 2 (volume : Measure ℝ) :=
  eLpNorm_comp_sub f 2 τ hf

end VariableChangeFormulas

/-! Modulation on L²: multiplication by the unit-modulus phase `t ↦ exp(i ξ t)` -/

-- Helper: pointwise phase factor has unit modulus
lemma phase_abs_one (ξ t : ℝ) :
    ‖Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))‖ = 1 := by
  -- Reorder to `((t * ξ : ℝ) : ℂ) * I` so the library lemma applies
  have hmul : Complex.I * (ξ : ℂ) * (t : ℂ) = ((t * ξ : ℝ) : ℂ) * Complex.I := by
    -- Use commutativity/associativity and collapse real casts
    have := by
      -- move `I` to the right of the real product
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_comm (Complex.I) ((ξ : ℂ) * (t : ℂ)))
    -- Now rewrite `(ξ : ℂ) * (t : ℂ)` as `((ξ * t : ℝ) : ℂ)` and commute factors
    -- to get `((t * ξ : ℝ) : ℂ) * I`.
    -- Start from the left-hand side we want to transform
    -- `Complex.I * (ξ : ℂ) * (t : ℂ)` equals `((ξ : ℂ) * (t : ℂ)) * Complex.I` by the line above
    -- then fold the real multiplication and swap to `t * ξ`.
    -- Combine the two steps succinctly:
    -- first replace LHS by `((ξ : ℂ) * (t : ℂ)) * Complex.I`
    -- then perform the `ofReal` fold and swap reals.
    -- Implemented via `calc` for clarity.
    clear this
    calc
      Complex.I * (ξ : ℂ) * (t : ℂ)
          = ((ξ : ℂ) * (t : ℂ)) * Complex.I := by
            simpa [mul_comm, mul_left_comm, mul_assoc]
      _ = ((ξ * t : ℝ) : ℂ) * Complex.I := by
            simpa [← Complex.ofReal_mul]
      _ = ((t * ξ : ℝ) : ℂ) * Complex.I := by
            simpa [mul_comm]
  -- Apply the norm lemma after rewriting the exponent's argument
  simpa [hmul] using Complex.norm_exp_ofReal_mul_I (t * ξ)

-- AE pointwise algebra lemmas for modulation by the phase factor
lemma mod_add_ae (ξ : ℝ)
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun t : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))
        * ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
      =ᵐ[volume]
    (fun t : ℝ =>
        Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t
        + Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (g : ℝ → ℂ) t) := by
  -- First rewrite `↑↑(f+g)` a.e. as `(↑↑f + ↑↑g)`
  have h_add := (Lp.coeFn_add f g)
  refine h_add.mono ?_
  intro x hx
  -- Then distribute multiplication pointwise
  simp only [Pi.add_apply] at hx
  simp only [hx, mul_add]

lemma mod_smul_ae (ξ : ℝ) (c : ℂ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun t : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))
        * ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
      =ᵐ[volume]
    (fun t : ℝ =>
        c • (Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t)) := by
  -- Rewrite the representative of `(c • f)` a.e.
  have h_smul := (Lp.coeFn_smul c f)
  refine h_smul.mono ?_
  intro x hx
  -- Use the equality from h_smul and distribute scalar multiplication
  simp only [Pi.smul_apply] at hx
  simp only [hx, Pi.smul_apply, smul_eq_mul]
  ring

-- The L² class is preserved under modulation
lemma mod_memLp (ξ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun t : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t)
      2 (volume : Measure ℝ) := by
  -- Start from the L² membership of `f`
  have hf : MemLp (fun t => (f : ℝ → ℂ) t) 2 (volume : Measure ℝ) := Lp.memLp f
  -- Define the phase function
  let phase : ℝ → ℂ := fun t => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))
  -- a.e.-strong measurability for the product
  have h_ae : AEStronglyMeasurable (fun t : ℝ => phase t * (f : ℝ → ℂ) t)
      (volume : Measure ℝ) := by
    -- `phase` is continuous, hence (ae-)strongly measurable
    have hphase_cont : Continuous phase := by
      -- phase t = exp(I * ((ξ : ℂ) * (t : ℂ)))
      have h1 : Continuous fun t : ℝ => (t : ℂ) := Complex.continuous_ofReal
      have h2 : Continuous fun t : ℝ => (ξ : ℂ) * (t : ℂ) := continuous_const.mul h1
      have h3 : Continuous fun t : ℝ => Complex.I * ((ξ : ℂ) * (t : ℂ)) := continuous_const.mul h2
      simpa [phase, mul_assoc] using Complex.continuous_exp.comp h3
    have hphase : AEStronglyMeasurable phase (volume : Measure ℝ) :=
      hphase_cont.measurable.aestronglyMeasurable
    apply AEStronglyMeasurable.mul
    · exact hphase
    · exact hf.aestronglyMeasurable
  -- Apply MemLp.of_le_mul with c = 1
  refine MemLp.of_le_mul (c := 1) hf h_ae ?_
  -- Show that ‖phase t * f t‖ ≤ 1 * ‖f t‖
  filter_upwards with t
  simp only [one_mul, norm_mul, phase]
  rw [phase_abs_one ξ t, one_mul]

-- Linear map on L² induced by modulation
noncomputable def mod_linearMap (ξ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f :=
    MemLp.toLp (fun t => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t)
      (mod_memLp ξ f)
  map_add' f g := by
    -- Compare representatives a.e. and use `Lp.ext`
    apply Lp.ext (μ := (volume : Measure ℝ))
    have hfg := MemLp.coeFn_toLp (mod_memLp ξ f)
    have hgg := MemLp.coeFn_toLp (mod_memLp ξ g)
    have hsum := MemLp.coeFn_toLp (mod_memLp ξ (f + g))
    -- assemble AE equality of coeFns all the way to `coeFn (sum)`
    calc (MemLp.toLp _ (mod_memLp ξ (f + g)) : Lp ℂ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun t => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t := hsum
      _ =ᵐ[volume] (fun t : ℝ =>
        Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t
        + Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (g : ℝ → ℂ) t) := mod_add_ae ξ f g
      _ =ᵐ[volume] (MemLp.toLp _ (mod_memLp ξ f) : Lp ℂ 2 (volume : Measure ℝ)) + (MemLp.toLp _ (mod_memLp ξ g) : Lp ℂ 2 (volume : Measure ℝ)) := (hfg.add hgg).symm
      _ =ᵐ[volume] (MemLp.toLp _ (mod_memLp ξ f) + MemLp.toLp _ (mod_memLp ξ g) : Lp ℂ 2 (volume : Measure ℝ)) := (Lp.coeFn_add _ _).symm
  map_smul' c f := by
    -- Compare representatives a.e. and use `Lp.ext_ae`
    apply Lp.ext (μ := (volume : Measure ℝ))
    have hf := MemLp.coeFn_toLp (mod_memLp ξ f)
    have hcf := MemLp.coeFn_toLp (mod_memLp ξ (c • f))
    -- assemble AE equality of coeFns
    calc (MemLp.toLp _ (mod_memLp ξ (c • f)) : Lp ℂ 2 (volume : Measure ℝ))
      =ᵐ[volume] (fun t : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)) := hcf
      _ =ᵐ[volume] (fun t : ℝ => c • (Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t)) := mod_smul_ae ξ c f
      _ =ᵐ[volume] (fun t : ℝ => c • ((((MemLp.toLp _ (mod_memLp ξ f)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)) := by
        refine hf.symm.mono ?_
        intro x hx
        simpa using congrArg (fun z => c • z) hx
      _ =ᵐ[volume]
        (↑↑(((RingHom.id ℂ) c) • (MemLp.toLp _ (mod_memLp ξ f))) : ℝ → ℂ) := by
        simpa [Pi.smul_apply] using
          (Lp.coeFn_smul ((RingHom.id ℂ) c) (MemLp.toLp _ (mod_memLp ξ f))).symm

-- Isometry property of modulation
lemma mod_norm_eq (ξ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mod_linearMap ξ f‖ = ‖f‖ := by
  classical
  -- Coerce to functions and compare L² norms via lintegrals of squared norms
  let Fξ : ℝ → ℂ := fun t => (((mod_linearMap ξ f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t
  have hrep : Fξ =ᵐ[volume]
      (fun t => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t) := by
    simpa [mod_linearMap] using (MemLp.coeFn_toLp (mod_memLp ξ f))
  have h_sq_ae :
      (fun t : ℝ => ((↑‖Fξ t‖₊ : ENNReal) ^ (2 : ℕ)))
        =ᵐ[volume]
      (fun t : ℝ => ((↑‖(f : ℝ → ℂ) t‖₊ : ENNReal) ^ (2 : ℕ))) := by
    refine hrep.mono ?_
    intro t ht
    simp only [ht, pow_two, nnnorm_mul]
    have : ‖Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))‖₊ = 1 := by
      -- Prove in ℝ and lift via injectivity of the coercion
      apply Subtype.ext
      simpa [NNReal.coe_one, coe_nnnorm] using phase_abs_one ξ t
    simp [this, one_mul]
  have h1 : ‖mod_linearMap ξ f‖ ^ 2
      = (∫⁻ t, ((↑‖Fξ t‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ)).toReal := by
    simpa [mod_linearMap] using (Lp_norm_sq_as_lintegral (ν := (volume : Measure ℝ)) (mod_linearMap ξ f))
  have h2 : ‖f‖ ^ 2
      = (∫⁻ t, ((↑‖(f : ℝ → ℂ) t‖₊ : ENNReal) ^ (2 : ℕ)) ∂(volume : Measure ℝ)).toReal := by
    simpa using (Lp_norm_sq_as_lintegral (ν := (volume : Measure ℝ)) f)
  have h_eq := lintegral_congr_ae h_sq_ae
  have hsq : ‖mod_linearMap ξ f‖ ^ 2 = ‖f‖ ^ 2 := by simpa [h1, h2] using congrArg ENNReal.toReal h_eq
  have hsqrt := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq, norm_nonneg] using hsqrt

-- Final continuous linear map for modulation
noncomputable def mod (ξ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous (mod_linearMap ξ) 1 (by
    intro f; rw [mod_norm_eq]; simp)

/-- Zak coefficients: inner products against time–frequency shifts of `w`.
`ZakCoeff w Δτ Δξ g (n,k) = ⟪ g, mod (kΔξ) (timeShift (nΔτ) w) ⟫` -/
noncomputable def ZakCoeff (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) : ℤ × ℤ → ℂ :=
  fun nk =>
    let n : ℤ := nk.1
    let k : ℤ := nk.2
    inner (𝕜 := ℂ) g ((mod ((k : ℝ) * Δξ)) ((timeShift ((n : ℝ) * Δτ)) w))

/-- Placeholder frame energy built from `ZakCoeff` (currently 0). -/
noncomputable def FrameEnergy (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ :=
  ∑' nk : ℤ × ℤ, ‖ZakCoeff w Δτ Δξ g nk‖ ^ (2 : ℕ)

/-- Bessel 上界: Zak 係数の有限和が `B‖g‖²` 以下で抑えられる。 -/
def besselBound (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ g : Lp ℂ 2 (volume : Measure ℝ), ∀ s : Finset (ℤ × ℤ),
    s.sum (fun x => ‖ZakCoeff w Δτ Δξ g x‖ ^ (2 : ℕ)) ≤ B * ‖g‖^2

/-- 存在形式の Bessel 上界。 -/
def HasBesselBound (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ) : Prop :=
  ∃ B : ℝ, besselBound w Δτ Δξ B

/-- Bessel 上界のもとでフレームエネルギーは有限で、`B‖g‖²` に抑えられる。 -/
lemma frameEnergy_le_of_bessel
    {w : Lp ℂ 2 (volume : Measure ℝ)} {Δτ Δξ B : ℝ}
    (hb : besselBound w Δτ Δξ B)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    FrameEnergy w Δτ Δξ g ≤ B * ‖g‖^2 := by
  classical
  -- 非負列の `tsum` は有限部分和の上限に一致する。ここでは上から `B‖g‖²` に抑えられる。
  have hnonneg : ∀ nk : ℤ × ℤ, 0 ≤ ‖ZakCoeff w Δτ Δξ g nk‖ ^ (2 : ℕ) := by
    intro nk; have := sq_nonneg (‖ZakCoeff w Δτ Δξ g nk‖)
    simpa [pow_two] using this
  -- FrameEnergyの定義を展開
  rw [FrameEnergy]
  -- 収束性を示す：Besselの不等式から任意の有限和が有界
  have hsummable : Summable (fun nk : ℤ × ℤ => ‖ZakCoeff w Δτ Δξ g nk‖ ^ (2 : ℕ)) := by
    apply summable_of_sum_le
    · -- 非負性
      intro nk
      exact sq_nonneg _
    · -- 有限和の上界
      intro s
      exact hb.2 g s
  -- Summable.tsum_le_of_sum_le を使用して tsum の上界を得る
  apply hsummable.tsum_le_of_sum_le
  -- 有限部分和の上界は仮定から従う
  intro s
  exact hb.2 g s

end Frourio

namespace Frourio

open MeasureTheory

/-!
Phase 2.1: Frame inequality (statement-level API).

We introduce a minimal predicate `suitable_window` and a Prop capturing the
Zak–Mellin frame bounds. Proofs will be supplied in a later phase once the
time-shift/modulation operators are fully implemented on L² and the standard
Gabor-frame machinery is available.
-/

/-- Window suitability predicate: we require unit L²-norm. -/
def suitable_window (w : Lp ℂ 2 (volume : Measure ℝ)) : Prop := ‖w‖ = 1

/-- Zak–Mellin frame bounds predicate for steps `(Δτ, Δξ)`. -/
def ZakFrame_inequality
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧
    ∀ g : Lp ℂ 2 (volume : Measure ℝ),
      A * ‖g‖^2 ≤ FrameEnergy w Δτ Δξ g ∧ FrameEnergy w Δτ Δξ g ≤ B * ‖g‖^2

end Frourio
