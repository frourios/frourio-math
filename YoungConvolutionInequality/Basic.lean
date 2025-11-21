import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Topology.MetricSpace.Holder
import YoungConvolutionInequality.HolderInequality.HolderInequalityCore
import YoungConvolutionInequality.MinkowskiIntegral.MinkowskiIntegral
import YoungConvolutionInequality.TonelliTheorem.TonelliTheorem
import YoungConvolutionInequality.Core2

open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff ComplexConjugate

variable {n : ℕ}

/--
**ℝⁿ 上のルベーグ測度は負数変換に対して不変である**

ルベーグ測度 `volume : Measure (Fin n → ℝ)` は、反転 `-x` に対して不変である。
すなわち、`volume (-·)⁻¹' = volume` が成り立つ。

この性質は、畳み込みの対称性や、変数変換 `x - y = z` で利用される。
-/
lemma volume_isNegInvariant :
    (volume : Measure (Fin n → ℝ)).IsNegInvariant := by
  classical
  let μ : Measure (Fin n → ℝ) := volume
  refine ⟨?_⟩
  set T :=
    (-1 : ℝ) •
      (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  have h_det_eq :
      LinearMap.det T =
        (-1 : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
    simpa [T]
      using
        (LinearMap.det_smul (-1 : ℝ)
          (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
  have h_abs_det : abs (LinearMap.det T) = (1 : ℝ) := by
    simp [h_det_eq]
  have h_det_ne_zero : LinearMap.det T ≠ 0 := by
    have h_abs_ne : abs (LinearMap.det T) ≠ 0 := by
      simp [h_abs_det]
    exact abs_ne_zero.mp h_abs_ne
  have h_map_aux :=
    Real.map_linearMap_volume_pi_eq_smul_volume_pi
      (f := T) h_det_ne_zero
  have h_abs_inv : abs ((LinearMap.det T)⁻¹) = (1 : ℝ) := by
    have := abs_inv (LinearMap.det T)
    simpa [h_abs_det, h_det_ne_zero]
      using this
  have h_scalar :
      ENNReal.ofReal (abs ((LinearMap.det T)⁻¹)) = (1 : ℝ≥0∞) := by
    simp [h_abs_inv]
  have h_map_aux' :
      Measure.map (fun y : (Fin n → ℝ) => -y) μ
        = ENNReal.ofReal (abs ((LinearMap.det T)⁻¹)) • μ := by
    simpa [T, LinearMap.smul_apply, Pi.smul_apply]
      using h_map_aux
  have h_map :
      Measure.map (fun y : (Fin n → ℝ) => -y) μ = μ := by
    simpa [h_scalar] using h_map_aux'
  have h_map_neg :
      Measure.map (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) μ = μ := by
    simpa [Neg.neg] using h_map
  have h_neg_eq :
      Measure.neg (μ := μ) = μ := by
    simpa [Measure.neg] using h_map_neg
  simpa [μ] using h_neg_eq

/--
**畳み込みが強可測であることを示す**

関数 `f` と `g` がそれぞれ概強可測（almost everywhere strongly measurable）であるとき、
その畳み込み `(f ∗ g)(x) = ∫ y, f(x - y) * g(y)` も概強可測である。

この性質は、畳み込みが Lᵖ 空間に属することを示すための前提条件として必要となる。

**実装方針**:
- `Mathlib.Analysis.Convolution` の `aestronglyMeasurable_convolution` を利用
- 畳み込み核の可測性は `MeasurableAdd₂` と合成の可測性から従う
- ℝⁿ は可測な加法構造を持つため、条件を満たす
-/
lemma convolution_aestronglyMeasurable
    (f g : (Fin n → ℝ) → ℂ)
    (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun x => ∫ y, f (x - y) * g y) volume := by
  classical
  -- Work with the Lebesgue measure on `Fin n → ℝ` as `μ`.
  let μ : Measure (Fin n → ℝ) := volume
  -- The convolution kernel is a.e.-strongly measurable on the product space.
  have h_kernel_meas :
      AEStronglyMeasurable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f (p.1 - p.2) * g p.2) (μ.prod μ) :=
    convolution_kernel_aestronglyMeasurable
      (μ := μ) f g hf hg
  -- Fubini-type measurability for the integral over the second variable.
  have h_int_meas :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μ) (ν := μ) (E := ℂ) h_kernel_meas
  -- Rewriting `μ` as `volume` yields the desired statement.
  simpa [μ] using h_int_meas

/--
**Minkowski's integral inequality for convolution setting.**

This is a specialized version of the general Minkowski inequality from
MinkowskiIntegral.lean, adapted for the convolution context.

For integrable families of functions, the Lʳ norm of the integral is bounded by
the integral of the Lʳ norms.

This is the key tool for handling r ≠ ∞ cases in Young's inequality.

Note: The general version is already available in MinkowskiIntegral/MinkowskiIntegral.lean
-/
theorem minkowski_for_convolution
    {r : ℝ≥0∞}
    (hr : 1 ≤ r) (hr_ne_top : r ≠ ∞)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℂ)
    (hF_prod_meas :
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume))
    (hF_prod_int :
      Integrable (Function.uncurry F) (volume.prod volume))
    (hF_memLp :
      ∀ᵐ y ∂volume, MemLp (fun x => F x y) r volume)
    (hF_norm_integrable :
      Integrable
        (fun y : (Fin n → ℝ) =>
          (eLpNorm (fun x => F x y) r volume).toReal)
        volume) :
    eLpNorm (fun x => ∫ y, F x y ∂volume) r volume ≤
      ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) r volume).toReal ∂volume) := by
  classical
  -- Apply the general Minkowski inequality with μ = ν = volume on ℝⁿ.
  haveI : SFinite (volume : Measure (Fin n → ℝ)) := inferInstance
  simpa using
    (minkowski_integral_inequality_ennreal
      (μ := (volume : Measure (Fin n → ℝ)))
      (ν := (volume : Measure (Fin n → ℝ)))
      (E := ℂ) (p := r)
      hr hr_ne_top
      (F := F)
      (hF := hF_prod_meas)
      (hF_prod := hF_prod_int)
      (hF_memLp := hF_memLp)
      (hF_norm := hF_norm_integrable))

/--
**`p = 1` の場合の Young の畳み込み不等式**

最も基本的なケース `p = 1, q = r` において、Young の畳み込み不等式が成立する。
すなわち、`f ∈ L¹` かつ `g ∈ Lq` ならば、畳み込み `f ∗ g ∈ Lq` であり、
そのノルムは `‖f ∗ g‖_q ≤ ‖f‖₁ · ‖g‖_q` で抑えられる。

**証明の要点**:
```
‖∫ f(x-y) g(y) dy‖_q
  ≤ ∫ ‖f(x-y)‖ · ‖g(y)‖ dy      -- 積分の三角不等式

Lq ノルムを取ると:
‖∫ f(·-y) g(y) dy‖_Lq
  ≤ ∫ ‖g(y)‖ · ‖f(·-y)‖_Lq dy  -- Minkowski 積分不等式
  = ∫ ‖g(y)‖ · ‖f‖_Lq dy        -- 平行移動不変性
  = ‖f‖_Lq · ‖g‖_L1
```

**実装方針**:
1. Minkowski 積分不等式を適用（`minkowski_integral_inequality`）
2. ルベーグ測度の平行移動不変性を利用（`eLpNorm_sub_right` 系の補題）
3. 非負関数の積分を単純化
-/
lemma young_convolution_p_eq_one
    {q : ℝ≥0∞}
    (f g : (Fin n → ℝ) → ℂ)
    (hq : 1 ≤ q)
    (hf : MemLp f 1 volume)
    (hg : MemLp g q volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) q volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) q volume ≤
      eLpNorm f 1 volume * eLpNorm g q volume := by
  classical
  -- We work on the additive group `G = ℝⁿ` with Lebesgue measure.
  let G := (Fin n → ℝ)
  let μ : Measure G := volume

  -- We treat the cases `q = ∞` and `q ≠ ∞` separately.
  by_cases hq_top : q = ⊤
  · -- In the case `q = ∞`, the statement is an L^∞-bound for the convolution.
    -- One expects to argue via the essential supremum characterization of the
    -- `eLpNorm` at exponent ∞ and a pointwise bound on the convolution
    -- integrand using Fubini and the L¹–L^∞ duality.
    --
    -- This branch is kept as a placeholder; the detailed argument will be
    -- filled in later without invoking any a priori L¹-integrability of the
    -- kernel.
    have h_mem :
        MemLp (fun x => ∫ y, f (x - y) * g y ∂μ) q μ := by
      -- TODO: show essential boundedness of the convolution from
      -- `hf : MemLp f 1 μ` and `hg : MemLp g ∞ μ`.
      sorry
    have h_norm :
        eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) q μ ≤
          eLpNorm f 1 μ * eLpNorm g q μ := by
      -- TODO: identify the L^∞-norm of the convolution with an essential
      -- supremum and bound it by ‖f‖₁ · ‖g‖_∞ via a pointwise estimate.
      sorry
    simpa [G, μ, hq_top] using And.intro h_mem h_norm

  · -- From now on we assume `q ≠ ∞`.  We introduce the convolution
    --   h x = ∫ f (x - y) * g y dμ(y)
    -- and state the desired Lᵠ-membership and norm bound as separate
    -- placeholders, to be proved later using Minkowski's integral
    -- inequality and the translation invariance of μ.
    have hq_ne_top : q ≠ ∞ := hq_top

    let h : G → ℂ := fun x => ∫ y, f (x - y) * g y ∂μ

    -- Step 1: Lᵠ-メンバーシップ（Minkowski + 可測性・可積分性の解析で示す）
    have h_mem :
        MemLp h q μ := by
      /-
      Sketch:
      * Show that the map (x, y) ↦ f (x - y) * g y is
        AEStronglyMeasurable on μ × μ using the MemLp hypotheses.
      * Use the convolution-specific Minkowski inequality developed in
        `MinkowskiIntegral.lean` (specialised to exponent q) to obtain
        `eLpNorm h q μ < ∞`.
      * Package AEStronglyMeasurable of h together with finiteness of
        the eLpNorm into `MemLp h q μ`.
      -/
      sorry

    -- Step 2: Young の基本評価 ‖h‖_q ≤ ‖f‖₁ ‖g‖_q
    have h_norm :
        eLpNorm h q μ ≤ eLpNorm f 1 μ * eLpNorm g q μ := by
      /-
      Sketch:
      * For each fixed y, view x ↦ f (x - y) * g y as a scalar multiple
        of a translate of f, and use translation invariance of μ to
        express its Lᵠ-norm.
      * Apply Minkowski's integral inequality in the x-variable to get
          ‖h‖_q ≤ ∫ ‖f(· - y)‖_q ‖g y‖ dμ(y).
      * Simplify the translated norms and bound the remaining integral
        in y via Hölder with exponents (1, q).
      -/
      sorry

    -- 戻り値を元の記号に書き直す。
    refine And.intro ?_ ?_
    · simpa [G, μ, h] using h_mem
    · simpa [G, μ, h] using h_norm

section KeyTheorems

/-!
## Key theorems needed for Young's convolution inequality

This section contains the signatures of important theorems that are needed
to complete the proof of `young_convolution_inequality`.
-/

/--
**Hölder inequality for convolution integrands.**

For almost every x, the product of f(x-y) and g(y) satisfies Hölder's inequality
when integrated over y.
-/
theorem holder_inequality_convolution_general
    {p q : ℝ≥0∞}
    (f g : (Fin n → ℝ) → ℂ)
    (hpq : IsConjugateExponent p q)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume)
    (x : Fin n → ℝ) :
    Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) volume ∧
    ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂volume ≤
      (eLpNorm f p volume).toReal * (eLpNorm g q volume).toReal := by
  classical
  -- Work with real-valued norms of `f` and `g`.
  let fR : (Fin n → ℝ) → ℝ := fun y => ‖f y‖
  let gR : (Fin n → ℝ) → ℝ := fun y => ‖g y‖
  have hfR : MemLp fR p volume := hf.norm
  have hgR : MemLp gR q volume := hg.norm

  -- Lebesgue measure on ℝⁿ is negation invariant.
  haveI : (volume : Measure (Fin n → ℝ)).IsNegInvariant :=
    volume_isNegInvariant (n := n)

  -- Apply the general Hölder inequality for convolution to `fR` and `gR`.
  have h :=
    holder_inequality_convolution
      (μ := (volume : Measure (Fin n → ℝ)))
      (p := p) (q := q) hpq fR gR hfR hgR x
  rcases h with ⟨h_int, h_bound⟩

  -- Identify the Lᵖ norms of `fR`, `gR` with those of `f`, `g`.
  have hf_eLp :
      eLpNorm f p volume = eLpNorm fR p volume :=
    eLpNorm_congr_norm_ae (μ := volume) (p := p) <|
      Filter.Eventually.of_forall fun y => by
        simp [fR, Real.norm_eq_abs]
  have hg_eLp :
      eLpNorm g q volume = eLpNorm gR q volume :=
    eLpNorm_congr_norm_ae (μ := volume) (p := q) <|
      Filter.Eventually.of_forall fun y => by
        simp [gR, Real.norm_eq_abs]

  refine And.intro ?_ ?_
  · -- Integrability of the convolution integrand.
    simpa [fR, gR] using h_int
  · -- The Hölder bound with norms of `f` and `g`.
    have := h_bound
    simpa [fR, gR, hf_eLp.symm, hg_eLp.symm] using this

/-! ### Phase 2 core analytic lemmas

These lemmas package the dual pairing bounds and the passage from
pairing bounds to Lʳ-norm bounds, as outlined in `plan.md` (Phase 2).
They are stated here with `sorry` placeholders so that the main Young
inequality statement can be assembled before filling in the analytic
details.
-/

/-- Algebraic helper for Young exponents: starting from
`1 / p + 1 / q = 1 + 1 / r` with `1 < r < ∞`, extract the conjugate
exponent relation for `r` and a suitable `r'` (here `r.conjExponent`),
and rewrite the Young relation in a form adapted to Hölder in the
outer variable. -/
lemma conjugate_exponents_from_young
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 < r)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    IsConjugateExponent r r.conjExponent ∧
      1 / r.conjExponent = 2 - (1 / p + 1 / q) := by
  constructor
  · exact conjugateExponent_isConjugate r (le_of_lt hr)
  · -- Rewrite the Young exponent relation in a form adapted to Hölder
    -- on the outer x-variable, with exponents (r, r').
    -- Step 1: record the conjugate-exponent relation for r and r'.
    have h_conj :
        1 / r + 1 / r.conjExponent = (1 : ℝ≥0∞) := by
      -- Use the ENNReal-level Hölder conjugate structure: when `1 ≤ r`,
      -- the pair `(r, r.conjExponent)` is Hölder conjugate, hence their
      -- reciprocals sum to 1.
      have hHC : ENNReal.HolderConjugate r r.conjExponent :=
        ENNReal.HolderConjugate.conjExponent (p := r) (hp := (le_of_lt hr))
      have h_inv :
          r⁻¹ + r.conjExponent⁻¹ = (1 : ℝ≥0∞) := by
        haveI : ENNReal.HolderConjugate r r.conjExponent := hHC
        simpa using
          (ENNReal.HolderConjugate.inv_add_inv_eq_one
            (p := r) (q := r.conjExponent))
      simpa [one_div] using h_inv

    -- Step 2: eliminate `1 / r` between `hpqr` and `h_conj` to obtain the
    -- desired identity for `1 / r.conjExponent`.
    -- It suffices to check that adding `1 / p + 1 / q` to both sides gives
    -- the same result, and that the left summand is finite so that
    -- subtraction by `1 / p + 1 / q` is exact.
    have h_add :
        1 / p + 1 / q + 1 / r.conjExponent = (2 : ℝ≥0∞) := by
      calc
        1 / p + 1 / q + 1 / r.conjExponent
            = (1 + 1 / r) + 1 / r.conjExponent := by
              -- rewrite using the Young exponent relation `hpqr`
              -- on reciprocals
              rw [hpqr]
        _ = 1 + (1 / r + 1 / r.conjExponent) := by
              ac_rfl
        _ = 1 + 1 := by
              rw [h_conj]
        _ = 2 := by
              -- identify `1 + 1` with the natural number `2`
              norm_num

    -- Show that the summand `1 / p + 1 / q` is finite (≠ ∞).
    have h_fin : 1 / p + 1 / q ≠ (∞ : ℝ≥0∞) := by
      have hp_ne_zero : p ≠ 0 := by
        -- From `hp : 1 ≤ p` we get `p ≠ 0`.
        intro hp0
        have : (1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞) := by simp [hp0] at hp
        simp at this
      have hq_ne_zero : q ≠ 0 := by
        intro hq0
        have : (1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞) := by simp [hq0] at hq
        simp at this
      have h1 : (1 / p : ℝ≥0∞) ≠ ∞ := by
        simp [one_div, ENNReal.inv_ne_top, hp_ne_zero]
      have h2 : (1 / q : ℝ≥0∞) ≠ ∞ := by
        simp [one_div, ENNReal.inv_ne_top, hq_ne_zero]
      exact (ENNReal.add_ne_top).2 ⟨h1, h2⟩

    -- Now use `ENNReal.sub_eq_of_eq_add_rev` to isolate `1 / r.conjExponent`
    -- as the unique term satisfying the additive identity with the finite
    -- summand `1 / p + 1 / q`.
    refine
      (ENNReal.sub_eq_of_eq_add_rev (a := (2 : ℝ≥0∞))
          (b := 1 / p + 1 / q) (c := 1 / r.conjExponent) h_fin ?_) |>.symm
    -- The required equality is exactly `h_add`.
    show (2 : ℝ≥0∞) = (1 / p + 1 / q) + 1 / r.conjExponent
    exact h_add.symm

/-- From uniform control of all dual pairings against `L^{r'}` test
functions, deduce an `Lʳ`-norm bound. This is the abstract duality
step turning the pairing estimate into an inequality for the eLpNorm
of the convolution itself. -/
lemma eLpNorm_from_dual_bound
    {r : ℝ≥0∞} (hr : 1 < r) (hr_ne_top : r ≠ ∞)
    (F : (Fin n → ℝ) → ℂ) (C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (h_bound :
      ∀ φ : (Fin n → ℝ) → ℂ,
        MemLp φ r.conjExponent volume →
          ‖∫ x, F x * conj (φ x) ∂volume‖ ≤
            C * (eLpNorm φ r.conjExponent volume).toReal) :
    eLpNorm F r volume ≤ ENNReal.ofReal C := by
  classical
  -- Work with local notation for the underlying group and measure.
  let G := (Fin n → ℝ)
  let μ : Measure G := volume

  -- Replace the complex-valued function `F` by its real-valued norm,
  -- so that we can later appeal to real-valued `L^p` duality lemmas.
  set Fℝ : G → ℝ := fun x => ‖F x‖ with hFℝ_def

  have h_eLpNorm_F_eq_Fℝ :
      eLpNorm F r μ = eLpNorm Fℝ r μ :=
    eLpNorm_congr_norm_ae (μ := μ) (p := r) <|
      Filter.Eventually.of_forall fun x => by
        -- Pointwise identification of norms between `F` and its real lift.
        have : (‖F x‖ : ℝ) = Fℝ x := by
          simp [Fℝ, hFℝ_def]
        simpa [this, Fℝ, hFℝ_def, Real.norm_eq_abs]

  -- Reformulate the desired inequality in terms of the real-valued function `Fℝ`.
  have h_goal_real : eLpNorm Fℝ r μ ≤ ENNReal.ofReal C := by
    -- Step 1: introduce the conjugate exponent `q = r.conjExponent`
    -- and record the conjugate-exponent relation.
    set q : ℝ≥0∞ := r.conjExponent with hq_def
    have hr_le_one : (1 : ℝ≥0∞) ≤ r := le_of_lt hr
    have hrq_conj : IsConjugateExponent r q := by
      -- Use the canonical conjugate exponent for `r` and rewrite `q`.
      simpa [hq_def] using
        (conjugateExponent_isConjugate (r := r) hr_le_one)

    -- Step 2: record exponent bounds on the dual exponent `q`.
    have hr_lt_top : r < ⊤ := lt_of_le_of_ne le_top hr_ne_top
    obtain ⟨hq_gt_one, hq_lt_top⟩ :=
      conjugate_exponent_bounds (p := r) (q := q) hrq_conj hr hr_lt_top

    -- Step 3: recast the complex pairing bound `h_bound` as a
    -- real-valued pairing bound for the norm function `Fℝ`.
    have h_pairing_bound_real :
        ∀ g : G → ℝ,
          MemLp g q μ →
          (eLpNorm g q μ).toReal ≤ 1 →
          Integrable (fun x => Fℝ x * g x) μ →
          |∫ x, Fℝ x * g x ∂μ| ≤ C := by
      /-
      Starting from `h_bound`, which is formulated for complex-valued
      test functions `φ : G → ℂ`, one constructs for each real-valued
      `g : G → ℝ` a corresponding complex test function `φ` so that the
      complex pairing

        ∫ x, F x * conj (φ x) dμ(x)

      identifies with the real pairing

        ∫ x, Fℝ x * g x dμ(x).

      Using the equality ‖F x‖ = Fℝ x and standard properties of the
      Bochner integral and complex conjugation, the bound from `h_bound`
      transfers to the real pairing, yielding the desired inequality.

      The detailed construction of `φ` and the verification of the
      identification of pairings are deferred to later development.
      -/
      intro g hg_mem hg_norm hg_int
      sorry

    /-
    Main duality step (skeleton):

    View `F` (equivalently `Fℝ`) as an element of `L^r(μ)` and
    use the hypothesis `h_bound`, which bounds the pairings

      φ ↦ ∫ F x * conj (φ x) dμ(x)

    for all test functions `φ ∈ L^{r'}(μ)`, to control the
    `L^r` norm of `F` via the abstract `L^p`–`L^{p'}` duality.

    The detailed implementation will proceed as follows:

    * Rewrite the complex pairing against `φ` as a real pairing
      involving `Fℝ` and a suitable real-valued test function
      built from `φ`.
    * Restrict to test functions with unit `eLpNorm` and apply
      an abstract duality lemma (for example
      `SchwartzDensityLp.lp_duality_norm_le_of_pairing_bound`),
      after transporting between complex- and real-valued
      formulations.
    * Finally, upgrade the resulting bound on
      `(eLpNorm Fℝ r μ).toReal` to the desired inequality in
      `ℝ≥0∞`.

    All of these analytic details are deferred to future work.
    -/
    sorry

  -- Translate the real-valued statement back to the original `F`.
  simpa [G, μ, h_eLpNorm_F_eq_Fℝ] using h_goal_real

/--
**Real-valued Young/Hölder/Minkowski bound for the triple kernel.**

At the level of real-valued integrals, the kernel
  (x, y) ↦ ‖g y‖ · ‖φ x‖ · ‖f (x − y)‖
is bounded in L¹ by the product of the Lᵖ/Lᵠ/L^{r'} norms of f, g, and φ
under the Young exponent relation.
-/
lemma convolution_dual_kernel_real_bound
    (f g φ : (Fin n → ℝ) → ℂ)
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 < r) (hr_ne_top : r ≠ ∞)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume)
    (hφ : MemLp φ r.conjExponent volume) :
    (∫ x, ∫ y,
        ‖g y‖ * (‖φ x‖ * ‖f (x - y)‖) ∂volume ∂volume)
      ≤
      (eLpNorm f p volume).toReal *
      (eLpNorm g q volume).toReal *
      (eLpNorm φ r.conjExponent volume).toReal := by
  classical
  -- Work with local notation for the underlying group and measure.
  let G := (Fin n → ℝ)
  let μ : Measure G := volume
  haveI : SFinite μ := inferInstance

  -- Define the real-valued kernel built from the norms of f, g, and φ.
  set H : G → G → ℝ :=
    fun x y => ‖g y‖ * (‖φ x‖ * ‖f (x - y)‖) with hH_def

  -- Core analytic estimate (Young/Hölder/Minkowski) at the level of real
  -- integrals.  The detailed proof will use:
  --   • Hölder in the x-variable, with exponents (r, r'),
  --   • the Hölder-type convolution bound in the y-variable coming from
  --     `holder_inequality_convolution_general`,
  --   • Minkowski's integral inequality in the convolution setting, via
  --     `minkowski_for_convolution`,
  --   • the exponent relation `hpqr` to match up the norms.
  have h_core :
      (∫ x, ∫ y, H x y ∂μ ∂μ) ≤
        (eLpNorm f p μ).toReal *
        (eLpNorm g q μ).toReal *
        (eLpNorm φ r.conjExponent μ).toReal := by
    -- Step 1: for each fixed x, control the inner integral in y by Hölder.
    have h_step1
        (hpq : IsConjugateExponent p q) :
        ∀ x : G,
          Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ ∧
          ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ ≤
            (eLpNorm f p μ).toReal *
            (eLpNorm g q μ).toReal := by
      intro x
      -- Apply the convolution Hölder inequality to y ↦ f (x − y) and y ↦ g y.
      simpa [G, μ] using
        (holder_inequality_convolution_general
          (p := p) (q := q)
          (f := f) (g := g)
          (hpq := hpq)
          (hf := hf) (hg := hg)
          (x := x))
    -- Step 2: rewrite the Young exponent relation in a form adapted to
    -- Hölder on the outer x-variable, with exponents (r, r') and φ
    -- providing the L^{r'} weight.
    have h_step2 :
        1 / r.conjExponent = 2 - (1 / p + 1 / q) := by
      -- Step 2.1: record the conjugate-exponent relation for r and r'.
      have h_conj :
          1 / r + 1 / r.conjExponent = (1 : ℝ≥0∞) := by
        -- Use the ENNReal-level Hölder conjugate structure: when
        -- `1 ≤ r`, the pair `(r, r.conjExponent)` is Hölder
        -- conjugate, hence their reciprocals sum to 1.
        have hHC : ENNReal.HolderConjugate r r.conjExponent :=
          ENNReal.HolderConjugate.conjExponent (p := r) (hp := (le_of_lt hr))
        have h_inv :
            r⁻¹ + r.conjExponent⁻¹ = (1 : ℝ≥0∞) := by
          haveI : ENNReal.HolderConjugate r r.conjExponent := hHC
          simpa using
            (ENNReal.HolderConjugate.inv_add_inv_eq_one
              (p := r) (q := r.conjExponent))
        simpa [one_div] using h_inv
      -- Step 2.2: eliminate `1 / r` between `hpqr` and `h_conj` to
      -- obtain the desired identity for `1 / r.conjExponent`.
      -- It suffices to check that adding `1 / p + 1 / q` to both
      -- sides gives the same result, and that the left summand is
      -- finite so that subtraction by `1 / p + 1 / q` is exact.
      have h_add :
          1 / p + 1 / q + 1 / r.conjExponent = (2 : ℝ≥0∞) := by
        calc
          1 / p + 1 / q + 1 / r.conjExponent
              = (1 + 1 / r) + 1 / r.conjExponent := by
                -- rewrite using the Young exponent relation `hpqr`
                -- on reciprocals
                rw [hpqr]
          _ = 1 + (1 / r + 1 / r.conjExponent) := by
                ac_rfl
          _ = 1 + 1 := by
                rw [h_conj]
          _ = 2 := by
                -- identify `1 + 1` with the natural number `2`
                norm_num
      -- Show that the summand `1 / p + 1 / q` is finite (≠ ∞).
      have h_fin : 1 / p + 1 / q ≠ (∞ : ℝ≥0∞) := by
        have hp_ne_zero : p ≠ 0 := by
          -- From `hp : 1 ≤ p` we get `p ≠ 0`.
          intro hp0
          have : (1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞) := by simp [hp0] at hp
          simp at this
        have hq_ne_zero : q ≠ 0 := by
          intro hq0
          have : (1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞) := by simp [hq0] at hq
          simp at this
        have h1 : (1 / p : ℝ≥0∞) ≠ ∞ := by simp [one_div, ENNReal.inv_ne_top, hp_ne_zero]
        have h2 : (1 / q : ℝ≥0∞) ≠ ∞ := by simp [one_div, ENNReal.inv_ne_top, hq_ne_zero]
        exact (ENNReal.add_ne_top).2 ⟨h1, h2⟩
      -- Now use `ENNReal.sub_eq_of_eq_add_rev` to isolate
      -- `1 / r.conjExponent` as the unique term satisfying the
      -- additive identity with the finite summand `1 / p + 1 / q`.
      refine (ENNReal.sub_eq_of_eq_add_rev (a := (2 : ℝ≥0∞))
              (b := 1 / p + 1 / q) (c := 1 / r.conjExponent) h_fin ?_) |>.symm
      -- The required equality is exactly `h_add`.
      show (2 : ℝ≥0∞) = (1 / p + 1 / q) + 1 / r.conjExponent
      exact h_add.symm
    -- Step 3: package the inner y-integral as a function of x.
    set I : G → ℝ :=
      fun x => ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ with hI_def

    -- Pointwise, the kernel H is obtained by multiplying ‖φ x‖ with the
    -- inner convolution-type integral in y.
    have hH_as_I :
        ∀ x, (∫ y, H x y ∂μ) = ‖φ x‖ * I x := by
      intro x
      -- Factor the constant ‖φ x‖ out of the inner integral.
      have h_const_mul :
          ∫ y, ‖φ x‖ * (‖f (x - y)‖ * ‖g y‖) ∂μ =
            ‖φ x‖ * ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ := by
        simpa using
          (MeasureTheory.integral_const_mul
            (μ := μ) (r := ‖φ x‖)
            (f := fun y : G => ‖f (x - y)‖ * ‖g y‖))

      -- Rewrite the left-hand side using the definition of H and basic
      -- commutativity/associativity of multiplication.
      have h_left :
          ∫ y, H x y ∂μ =
            ∫ y, ‖φ x‖ * (‖f (x - y)‖ * ‖g y‖) ∂μ := by
        have h_point :
            (fun y => H x y) =
              fun y => ‖φ x‖ * (‖f (x - y)‖ * ‖g y‖) := by
          funext y
          simp [H, hH_def, mul_comm, mul_left_comm, mul_assoc]
        simp [h_point]

      -- Rewrite I x using its definition.
      have h_I :
          I x = ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ := by
        simp [I, hI_def]

      -- Combine the previous identities.
      calc
        ∫ y, H x y ∂μ
            = ∫ y, ‖φ x‖ * (‖f (x - y)‖ * ‖g y‖) ∂μ := h_left
        _ = ‖φ x‖ * ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂μ := h_const_mul
        _ = ‖φ x‖ * I x := by
              simp [h_I]

    -- Step 4: rewrite the iterated integral in the statement using I.
    have h_rewrite :
        (∫ x, ∫ y, H x y ∂μ ∂μ) =
          ∫ x, ‖φ x‖ * I x ∂μ := by
      -- First, identify the inner integral using hH_as_I.
      have h_inner :
          (fun x : G => ∫ y, H x y ∂μ) =
            fun x : G => ‖φ x‖ * I x := by
        funext x
        exact hH_as_I x
      -- Then rewrite the outer integral accordingly.
      calc
        (∫ x, ∫ y, H x y ∂μ ∂μ)
            = ∫ x, (∫ y, H x y ∂μ) ∂μ := rfl
        _ = ∫ x, ‖φ x‖ * I x ∂μ := by
              simp [h_inner]

    -- Step 5: apply Hölder in the x-variable with exponents (r, r') to
    -- control the integral of ‖φ x‖ · I x.
    have h_holder_x :
        (∫ x, ‖φ x‖ * I x ∂μ) ≤
          (eLpNorm φ r.conjExponent μ).toReal *
          (eLpNorm I r μ).toReal := by
      -- Hölder in the x-variable with exponents (r', r).

      -- First, record that (r, r') are conjugate exponents.
      have hr_conj' :
          IsConjugateExponent r r.conjExponent :=
        conjugateExponent_isConjugate r (le_of_lt hr)
      have hr_conj :
          IsConjugateExponent r.conjExponent r := by
        -- Symmetry of `IsConjugateExponent` by case analysis.
        rcases hr_conj' with h | h
        · rcases h with ⟨hr1, hrq⟩
          subst hr1
          rw [hrq]
          exact Or.inr <| Or.inl ⟨rfl, rfl⟩
        · rcases h with h | h
          · rcases h with ⟨hr_top, hrq⟩
            subst hr_top
            rw [hrq]
            exact Or.inl ⟨rfl, rfl⟩
          · rcases h with ⟨hr_gt_one, hr_lt_top, hq_gt_one, hq_lt_top, hsum⟩
            exact Or.inr <|
              Or.inr
                ⟨hq_gt_one, hq_lt_top, hr_gt_one, hr_lt_top,
                  by simpa [add_comm] using hsum⟩

      -- Next, record that I lies in Lʳ(μ).  This will be proved later
      -- using the convolution structure of I together with
      -- `minkowski_for_convolution` and the MemLp assumptions on f and g.
      -- We keep the detailed analytic argument as a placeholder here so that
      -- the Hölder step remains logically independent of Step 6.
      have hI_mem :
          MemLp I r μ := by
        /-
        Sketch of proof:

        1. Introduce the scalar kernel
             K : G × G → ℝ,
             K (x, y) = ‖f (x - y)‖ * ‖g y‖.
           Then I x = ∫ y, K (x, y) dμ(y).

        2. Use measurability of f and g (from hf, hg) together with the
           translation invariance of μ to show that
             (x, y) ↦ K (x, y)
           is AEStronglyMeasurable and integrable on μ × μ.  This follows
           from the corresponding convolution kernel lemmas in
           `MinkowskiIntegral.lean`.

        3. Apply `minkowski_for_convolution` with exponent r to the
           complexified kernel
             F (x) (y) = (‖f (x - y)‖ * ‖g y‖ : ℂ)
           to obtain an Lʳ bound on x ↦ ∫ y, F x y dμ(y), which coincides
           with I (up to the ℝ/ℂ identification).

        4. The bound expresses `eLpNorm I r μ` in terms of the norms of f
           and g.  Since these norms are finite by hf, hg and hr_ne_top,
           one concludes `eLpNorm I r μ < ∞`, hence `MemLp I r μ`.
        -/
        -- Step 1: package the integrand in terms of a kernel K.
        set K : G × G → ℝ :=
          fun p => ‖f (p.1 - p.2)‖ * ‖g p.2‖ with hK_def

        have hI_eq_K :
            ∀ x : G, I x = ∫ y, K (x, y) ∂μ := by
          intro x
          -- Unfold I and K and identify the integrands.
          have h_eq : (fun y => ‖f (x - y)‖ * ‖g y‖)
              = fun y => K (x, y) := by
            funext y
            simp [K, hK_def]
          simp [I, hI_def]
          rw [h_eq]

        -- Step 2: basic measurability of K on the product space μ × μ.
        have hf_ae : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
        have hg_ae : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
        have hf_norm_aemeas :
            AEMeasurable (fun x : G => ‖f x‖) μ :=
          hf_ae.norm.aemeasurable
        have hg_norm_aemeas :
            AEMeasurable (fun x : G => ‖g x‖) μ :=
          hg_ae.norm.aemeasurable

        -- Quasi-measure-preserving map (x, y) ↦ x − y with respect to μ × μ → μ.
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
            MeasureTheory.Measure.quasiMeasurePreserving_fst
              (μ := μ) (ν := μ)
          simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
            using h_fst_qmp.comp h_sub_prod.quasiMeasurePreserving

        have hf_comp_aemeas :
            AEMeasurable (fun p : G × G => ‖f (p.1 - p.2)‖) (μ.prod μ) :=
          hf_norm_aemeas.comp_quasiMeasurePreserving h_sub_qmp
        have hg_comp_aemeas :
            AEMeasurable (fun p : G × G => ‖g p.2‖) (μ.prod μ) :=
          hg_norm_aemeas.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_snd
              (μ := μ) (ν := μ))
        have hK_aemeas :
            AEMeasurable K (μ.prod μ) := by
          have h_mul :
              AEMeasurable
                (fun p : G × G =>
                  ‖f (p.1 - p.2)‖ * ‖g p.2‖) (μ.prod μ) :=
            hf_comp_aemeas.mul hg_comp_aemeas
          simpa [K, hK_def, mul_comm, mul_left_comm, mul_assoc] using h_mul

        -- Step 3: complexified kernel and Minkowski-type Lʳ bound for I.
        set F : G → G → ℂ :=
          fun x y => (K (x, y) : ℂ) with hF_def

        -- Measurability / integrability hypotheses for Minkowski will be
        -- established using the corresponding convolution-preparatory
        -- lemmas from `MinkowskiIntegral.lean`.  We record the required
        -- placeholders here.
        have hF_prod_meas :
            AEStronglyMeasurable (Function.uncurry F) (μ.prod μ) := by
          -- From `hK_aemeas` and the identification
          --   (Function.uncurry F) p = (K p : ℂ),
          -- together with continuity of the inclusion ℝ → ℂ, we obtain
          -- AEStronglyMeasurable for the complex-valued kernel on μ × μ.
          have hK_aesm : AEStronglyMeasurable K (μ.prod μ) :=
            hK_aemeas.aestronglyMeasurable
          have hF_eq :
              (Function.uncurry F) =
                fun p : G × G => (K p : ℂ) := by
            funext p
            -- Unfold F and K and simplify.
            simp only [Function.uncurry, F, hF_def, K, hK_def]
          have h_aux :
              AEStronglyMeasurable
                (fun p : G × G => (K p : ℂ)) (μ.prod μ) :=
            Complex.continuous_ofReal.comp_aestronglyMeasurable hK_aesm
          simpa [hF_eq] using h_aux

        have hF_prod_int :
            Integrable (Function.uncurry F) (μ.prod μ) := by
          /-
          TODO (Phase 2, plan.md):
          Prove integrability of the complex-valued kernel `Function.uncurry F`
          directly from the real triple-kernel estimates and Tonelli/Fubini,
          without relying on finite-measure-specific convolution lemmas.
          -/
          sorry

        have hF_memLp :
            ∀ᵐ y ∂μ, MemLp (fun x => F x y) r μ := by
          /-
          For almost every y, the function x ↦ F x y is a scalar multiple
          (by ‖g y‖) of a translate of ‖f‖.  The Lʳ membership thus follows
          from the corresponding convolution-kernel MemLp lemmas, applied
          to f and g with exponent r.
          -/
          sorry

        have hF_norm_integrable :
            Integrable
              (fun y : G =>
                (eLpNorm (fun x => F x y) r μ).toReal) μ := by
          /-
          The integrability of y ↦ ‖g y‖ · ‖f‖_r, and hence of the fibre
          Lʳ norms, is obtained from the MemLp assumptions on f and g and
          the preparatory estimates in `MinkowskiIntegral.lean`.
          -/
          sorry

        -- Minkowski's inequality for the complexified kernel F yields an
        -- Lʳ bound for the map x ↦ ∫ F x y dμ(y), which coincides with I.
        have h_minkowski :
            eLpNorm (fun x : G => ∫ y, F x y ∂μ) r μ ≤
              ENNReal.ofReal
                (∫ y, (eLpNorm (fun x => F x y) r μ).toReal ∂μ) :=
          minkowski_for_convolution
            (r := r) (hr := (le_of_lt hr)) (hr_ne_top := hr_ne_top)
            (F := F)
            (hF_prod_meas := hF_prod_meas)
            (hF_prod_int := hF_prod_int)
            (hF_memLp := hF_memLp)
            (hF_norm_integrable := hF_norm_integrable)

        -- Step 4: identify the Minkowski-bound function with I and conclude
        -- that I lies in Lʳ(μ).

        -- First, relate the complex-valued Bochner integral of F to the
        -- real-valued integral defining I.
        have hF_integral_eq_I :
            (fun x : G => ∫ y, F x y ∂μ) =
              fun x : G => (I x : ℂ) := by
          /-
          For each x, we have
            F x y = (K (x, y) : ℂ),
          so by linearity of the Bochner integral and the definition of
          I (via hI_eq_K), the integral ∫ F x y dμ coincides with the
          complexification of I x.
          The detailed justification uses the fact that the inclusion
          ℝ → ℂ is a bounded linear map commuting with integration.
          -/
          sorry

        -- Next, identify the eLpNorm of I with that of its ℂ-valued lift.
        have h_eLpNorm_eq :
            eLpNorm I r μ =
              eLpNorm (fun x : G => (I x : ℂ)) r μ := by
          /-
          This follows from the standard argument that the Lᵖ norm only
          depends on the pointwise real norm, together with the equality
          ‖(I x : ℂ)‖ = ‖I x‖.
          -/
          sorry

        -- From the Minkowski inequality and the exponent hypotheses, one
        -- obtains finiteness of `eLpNorm I r μ`.
        have h_eLp_I_lt_top : eLpNorm I r μ < ⊤ := by
          /-
          Combine `h_minkowski` with `hF_integral_eq_I` and `h_eLpNorm_eq`,
          together with the MemLp assumptions on f and g (hf, hg) and
          the exponent condition (hp, hq, hr_ne_top), to show that the
          right-hand side ENNReal bound is finite.  This yields
          `eLpNorm I r μ < ∞`.
          -/
          sorry

        -- Finally, package measurability and finiteness of the eLpNorm
        -- into a `MemLp` conclusion for I.
        have hI_aesm : AEStronglyMeasurable I μ := by
          /-
          Since K is a.e.-measurable on μ × μ, the map
            x ↦ ∫ y, K (x, y) dμ(y)
          is AEStronglyMeasurable on μ by a Fubini/Tonelli-type argument.
          Using `hI_eq_K`, this gives AEStronglyMeasurable I μ.
          -/
          sorry

        exact ⟨hI_aesm, h_eLp_I_lt_top⟩

      -- Apply Hölder's inequality with exponents (r', r) to φ and I.
      obtain ⟨h_int, h_le⟩ :=
        holder_inequality (μ := μ)
          (p := r.conjExponent) (q := r)
          hr_conj φ I hφ hI_mem

      -- The function I is an integral of a nonnegative kernel, hence
      -- is itself pointwise nonnegative.
      have hI_nonneg : ∀ x, 0 ≤ I x := by
        intro x
        have h_nonneg : ∀ y, 0 ≤ ‖f (x - y)‖ * ‖g y‖ := by
          intro y
          exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
        simpa [I, hI_def] using integral_nonneg h_nonneg

      -- Identify the Hölder integrand with the desired integrand
      -- ‖φ x‖ · I x using the nonnegativity of I.
      have h_integrand_eq :
          (fun x => ‖φ x‖ * ‖I x‖) =
            fun x => ‖φ x‖ * I x := by
        funext x
        have hI_norm : ‖I x‖ = I x := by
          have hx : 0 ≤ I x := hI_nonneg x
          simp [Real.norm_eq_abs, abs_of_nonneg hx]
        simp [hI_norm, mul_comm, mul_left_comm, mul_assoc]

      -- Rewrite the Hölder inequality in the desired form.
      have h_int_rewrite :
          ∫ x, ‖φ x‖ * I x ∂μ =
            ∫ x, ‖φ x‖ * ‖I x‖ ∂μ := by
        rw [← h_integrand_eq]

      -- Combine identifications with the Hölder bound.
      have :=
        calc
          ∫ x, ‖φ x‖ * I x ∂μ
              = ∫ x, ‖φ x‖ * ‖I x‖ ∂μ := h_int_rewrite
          _ ≤ (eLpNorm φ r.conjExponent μ).toReal *
              (eLpNorm I r μ).toReal := h_le
      exact this

    -- Step 6: bound the Lʳ-norm of I using the convolution structure in
    -- y together with Minkowski's integral inequality.
    have h_I_Lr :
        (eLpNorm I r μ).toReal ≤
          (eLpNorm f p μ).toReal *
          (eLpNorm g q μ).toReal := by
      -- One views I as coming from a convolution-type integral in y,
      -- uses the pointwise estimate h_step1 (Hölder in y) together with
      -- minkowski_for_convolution, and then rewrites the resulting bound
      -- in terms of the eLpNorms of f and g.
      sorry

    -- Step 7: combine the previous steps to obtain the desired bound for
    -- the original double integral of H.
    have h_final :
        (∫ x, ∫ y, H x y ∂μ ∂μ) ≤
          (eLpNorm f p μ).toReal *
          (eLpNorm g q μ).toReal *
          (eLpNorm φ r.conjExponent μ).toReal := by
      have :=
        calc
          (∫ x, ∫ y, H x y ∂μ ∂μ)
              = ∫ x, ‖φ x‖ * I x ∂μ := h_rewrite
          _ ≤ (eLpNorm φ r.conjExponent μ).toReal *
              (eLpNorm I r μ).toReal := h_holder_x
          _ ≤ (eLpNorm f p μ).toReal *
              (eLpNorm g q μ).toReal *
              (eLpNorm φ r.conjExponent μ).toReal := by
                -- Insert the estimate h_I_Lr and reorder the product;
                -- this uses only positivity of the norms and basic
                -- algebra in ℝ.
                sorry
      exact this

    exact h_final

  -- Rewrite back in terms of the original kernel on ℝⁿ with Lebesgue measure.
  simpa [G, μ, H, hH_def] using h_core

lemma convolution_dual_kernel_lintegral_lt_top
    (f g φ : (Fin n → ℝ) → ℂ)
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 < r) (hr_ne_top : r ≠ ∞)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume)
    (hφ : MemLp φ r.conjExponent volume) :
    (∫⁻ p : (Fin n → ℝ) × (Fin n → ℝ),
      ENNReal.ofReal
        (‖g p.2‖ * (‖φ p.1‖ * ‖f (p.1 - p.2)‖)) ∂(volume.prod volume)) < ⊤ := by
  classical
  -- Work with local notation for the underlying group and measure.
  let G := (Fin n → ℝ)
  let μ : Measure G := volume
  haveI : SFinite μ := inferInstance

  -- Define the scalar nonnegative kernel built from the norms of f, g, and φ.
  set H : G × G → ℝ :=
    fun p => ‖g p.2‖ * (‖φ p.1‖ * ‖f (p.1 - p.2)‖) with hH_def

  -- Analytic estimate (Young/Hölder/Minkowski) giving an L¹-bound.
  -- Using the exponent relation `hpqr` together with the MemLp assumptions
  -- on f, g, and φ, one obtains a uniform bound of the form
  --
  --   ∫∫ ‖g(y)‖ · ‖φ(x)‖ · ‖f(x − y)‖ dx dy
  --     ≤ C · ‖f‖_p · ‖g‖_q · ‖φ‖_{r'}
  --
  -- for some finite constant C depending only on the exponents.  In the
  -- present eLpNorm/lintegral formulation, this yields a bound by a finite
  -- ENNReal constant, which immediately implies finiteness of the lintegral.
  have h_bound :
      (∫⁻ p : G × G, ENNReal.ofReal (H p) ∂(μ.prod μ)) ≤
        ENNReal.ofReal
          ((eLpNorm f p μ).toReal *
           (eLpNorm g q μ).toReal *
           (eLpNorm φ r.conjExponent μ).toReal) := by
    -- Step 1: introduce a shorthand for the RHS constant.
    set C :
        ℝ :=
      (eLpNorm f p μ).toReal *
      (eLpNorm g q μ).toReal *
      (eLpNorm φ r.conjExponent μ).toReal
      with hC_def

    -- Step 2: observe that C is nonnegative, since it is a product of norms.
    have hC_nonneg : 0 ≤ C := by
      have h1 : 0 ≤ (eLpNorm f p μ).toReal :=
        ENNReal.toReal_nonneg
      have h2 : 0 ≤ (eLpNorm g q μ).toReal :=
        ENNReal.toReal_nonneg
      have h3 : 0 ≤ (eLpNorm φ r.conjExponent μ).toReal :=
        ENNReal.toReal_nonneg
      have h12 : 0 ≤
          (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal :=
        mul_nonneg h1 h2
      have h123 : 0 ≤
          (eLpNorm f p μ).toReal *
          (eLpNorm g q μ).toReal *
          (eLpNorm φ r.conjExponent μ).toReal :=
        mul_nonneg h12 h3
      simpa [C, hC_def] using h123

    -- Step 3: view the scalar kernel H as a nonnegative real-valued function
    -- on the product space and express its Bochner integral.  By Tonelli/Fubini
    -- this equals the iterated integral in x and y.
    have h_tonelli :
        (∫⁻ p : G × G, ENNReal.ofReal (H p) ∂(μ.prod μ)) =
          ENNReal.ofReal
            (∫ x, ∫ y, H (x, y) ∂μ ∂μ) := by
      -- Step 1: record nonnegativity of H on G × G.
      have hH_nonneg : ∀ p : G × G, 0 ≤ H p := by
        intro p
        dsimp [H]
        have h1 : 0 ≤ ‖g p.2‖ := norm_nonneg _
        have h2 : 0 ≤ ‖φ p.1‖ := norm_nonneg _
        have h3 : 0 ≤ ‖f (p.1 - p.2)‖ := norm_nonneg _
        exact mul_nonneg h1 (mul_nonneg h2 h3)
      -- Step 2: Tonelli on the ℝ≥0∞-valued kernel `ofReal ∘ H` to rewrite
      -- the product lintegral as an iterated lintegral in x and y.
      -- First, establish a.e.-measurability of H on μ × μ.
      have hf_ae : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
      have hg_ae : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
      have hφ_ae : AEStronglyMeasurable φ μ := hφ.aestronglyMeasurable
      have hf_norm_aemeas : AEMeasurable (fun x : G => ‖f x‖) μ :=
        hf_ae.norm.aemeasurable
      have hg_norm_aemeas : AEMeasurable (fun x : G => ‖g x‖) μ :=
        hg_ae.norm.aemeasurable
      have hφ_norm_aemeas : AEMeasurable (fun x : G => ‖φ x‖) μ :=
        hφ_ae.norm.aemeasurable
      -- Quasi-measure-preserving map (x, y) ↦ x − y with respect to μ × μ → μ.
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
      have hf_comp_aemeas :
          AEMeasurable (fun p : G × G => ‖f (p.1 - p.2)‖) (μ.prod μ) :=
        hf_norm_aemeas.comp_quasiMeasurePreserving h_sub_qmp
      have hg_comp_aemeas :
          AEMeasurable (fun p : G × G => ‖g p.2‖) (μ.prod μ) :=
        hg_norm_aemeas.comp_quasiMeasurePreserving
          (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
      have hφ_comp_aemeas :
          AEMeasurable (fun p : G × G => ‖φ p.1‖) (μ.prod μ) :=
        hφ_norm_aemeas.comp_quasiMeasurePreserving
          (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
      have hH_aemeas :
          AEMeasurable H (μ.prod μ) := by
        have hφf_aemeas :
            AEMeasurable (fun p : G × G => ‖φ p.1‖ * ‖f (p.1 - p.2)‖)
              (μ.prod μ) :=
          hφ_comp_aemeas.mul hf_comp_aemeas
        have hHgφf_aemeas :
            AEMeasurable
              (fun p : G × G => ‖g p.2‖ * (‖φ p.1‖ * ‖f (p.1 - p.2)‖))
              (μ.prod μ) :=
          hg_comp_aemeas.mul hφf_aemeas
        simpa [H, hH_def, mul_assoc] using hHgφf_aemeas
      have h_ofReal_aemeas :
          AEMeasurable (fun p : G × G => ENNReal.ofReal (H p)) (μ.prod μ) :=
        hH_aemeas.ennreal_ofReal
      have h_iter :
          (∫⁻ p : G × G, ENNReal.ofReal (H p) ∂(μ.prod μ)) =
            ∫⁻ x, ∫⁻ y, ENNReal.ofReal (H (x, y)) ∂μ ∂μ := by
        simpa using
          (MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
            (f := fun p : G × G => ENNReal.ofReal (H p)) h_ofReal_aemeas)
      -- Step 3: bridge each fibrewise lintegral in y to a real integral using
      -- `ofReal_integral_eq_lintegral_ofReal`, once sectionwise integrability
      -- is available via the Tonelli helper lemmas.
      have hH_int :
          (∫⁻ p : G × G, ENNReal.ofReal (H p) ∂(μ.prod μ)) < ⊤ := by
        /-
        At this stage, establishing finiteness of the product lintegral for H
        requires the full Young/Hölder/Minkowski analysis on μ × μ.
        This will be derived later from the real-valued core estimate
        `convolution_dual_kernel_real_bound` together with the Tonelli bridge
        encoded in `h_tonelli` itself.  We keep `hH_int` as a placeholder to
        record this analytic input without introducing a circular dependency.
        -/
        sorry
      have h_section_int :
          ∀ᵐ x ∂μ, Integrable (fun y => H (x, y)) μ :=
        MeasureTheory.ae_integrable_left_of_lintegral_ofReal_lt_top
          (μ := μ) (H := H) hH_nonneg hH_aemeas hH_int
      have h_inner_ae :
          (fun x => ∫⁻ y, ENNReal.ofReal (H (x, y)) ∂μ) =ᵐ[μ]
            fun x => ENNReal.ofReal (∫ y, H (x, y) ∂μ) := by
        refine h_section_int.mono ?_
        intro x hx
        -- From pointwise nonnegativity of H, deduce a.e. nonnegativity in y.
        have h_nonneg_y : 0 ≤ᵐ[μ] fun y => H (x, y) := by
          have h_pt : ∀ y, 0 ≤ H (x, y) := fun y => hH_nonneg (x, y)
          exact Filter.Eventually.of_forall h_pt
        -- Apply `ofReal_integral_eq_lintegral_ofReal` in the y-variable.
        have h_eq :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            (μ := μ) (f := fun y => H (x, y)) hx h_nonneg_y
        -- Rewrite to match the desired orientation.
        have h_eq' :
            ∫⁻ y, ENNReal.ofReal (H (x, y)) ∂μ =
              ENNReal.ofReal (∫ y, H (x, y) ∂μ) := by
          simpa using h_eq.symm
        exact h_eq'
      have h_iter_bridge :
          ∫⁻ x, ∫⁻ y, ENNReal.ofReal (H (x, y)) ∂μ ∂μ =
            ∫⁻ x, ENNReal.ofReal (∫ y, H (x, y) ∂μ) ∂μ := by
        refine lintegral_congr_ae h_inner_ae
      /-
      Skeleton for the Tonelli bridge:

      1. Use that `H ≥ 0` pointwise:

           (already recorded as `hH_nonneg` above)

      2. View `ofReal ∘ H` as an ℝ≥0∞-valued kernel on `μ.prod μ` and apply the
         product Tonelli theorem `MeasureTheory.lintegral_prod` to rewrite

           ∫⁻ p, ENNReal.ofReal (H p) d(μ.prod μ)

         as an iterated lintegral in `x` and `y`:

           ∫⁻ x, ∫⁻ y, ENNReal.ofReal (H (x, y)) dμ dμ.

         This is implemented above as `h_iter`, using a.e.-measurability of H
         on `μ.prod μ` derived from the MemLp assumptions on `f`, `g`, and `φ`
         together with the standard measurability of convolution kernels.

      3. For each fixed `x`, use nonnegativity of `H (x, ·)` together with the
         sectionwise Bochner integrability (eventually supplied by the Tonelli
         helper lemmas in `TonelliTheorem.lean`) to invoke

           MeasureTheory.ofReal_integral_eq_lintegral_ofReal

         in the `y`-variable, upgrading

           ∫⁻ y, ENNReal.ofReal (H (x, y)) dμ

         to `ENNReal.ofReal (∫ y, H (x, y) dμ)` for almost every `x`.

         Concretely, once we know that the product lintegral

           ∫⁻ p, ENNReal.ofReal (H p) d(μ.prod μ) < ∞,

         we can apply `ae_integrable_left_of_lintegral_ofReal_lt_top` with
         `H` and `hH_nonneg` to obtain a.e. integrability of the sections
         `y ↦ H (x, y)`.  For such x, the lemma
         `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` in the y-variable
         yields the pointwise identity

           ∫⁻ y, ENNReal.ofReal (H (x, y)) dμ =
             ENNReal.ofReal (∫ y, H (x, y) dμ),

         and hence an a.e.-equality of functions

           (fun x => ∫⁻ y, ENNReal.ofReal (H (x, y)) dμ)
             =ᵐ[μ]
           fun x => ENNReal.ofReal (∫ y, H (x, y) dμ).

         Lifting this a.e.-equality through the outer lintegral in x gives an
         equality between the iterated ENNReal integral and

           ∫⁻ x, ENNReal.ofReal (∫ y, H (x, y) dμ) dμ.

      4. Apply the same lemma once more in the outer `x`-variable, using

           x ↦ ∫ y, H (x, y) dμ,

         to identify the iterated lintegral in `x` and `y` with

           ENNReal.ofReal (∫ x, ∫ y, H (x, y) dμ dμ).

      5. Chaining these equalities yields the desired statement.  The detailed
         analytic proof is deferred to the Tonelli/Fubini infrastructure and
         will be filled in once the surrounding convolution kernel estimates
         are fully developed.
      -/
      sorry

    -- Step 4: apply Hölder/Young/Minkowski to the real-valued iterated
    -- integral to obtain the bound by C.
    have h_real_bound :
        (∫ x, ∫ y, H (x, y) ∂μ ∂μ) ≤ C := by
      -- This is where the core analytic estimate enters:
      --  • fix y and apply Hölder in x using the exponent relation derived
      --    from `hpqr` to control the inner integral in terms of ‖f‖_p
      --    and ‖φ‖_{r'},
      --  • then apply Minkowski (or Hölder again) in y to control the
      --    outer integral in terms of ‖g‖_q,
      --  • combine the pieces to obtain the inequality with constant C.
      -- Delegate the real-valued inequality to the global helper lemma
      -- `convolution_dual_kernel_real_bound` specialized to μ = volume.
      simpa [G, μ, H, hH_def, C, hC_def] using
        (convolution_dual_kernel_real_bound
          (f := f) (g := g) (φ := φ)
          (p := p) (q := q) (r := r)
          hp hq hr hr_ne_top hpqr hf hg hφ)

    -- Step 5: combine the Tonelli identification with the real bound and
    -- monotonicity of `ENNReal.ofReal` to obtain the desired ENNReal bound.
    have h_enreal :
        (∫⁻ p : G × G, ENNReal.ofReal (H p) ∂(μ.prod μ))
          ≤ ENNReal.ofReal C := by
      -- Starting from `h_tonelli`, rewrite the left-hand side in terms of
      -- the real iterated integral and then apply `ENNReal.ofReal_le_ofReal`
      -- using the inequality `h_real_bound` together with `hC_nonneg`.
      -- This translates the estimate on the real integral into an estimate
      -- on the corresponding lintegral.
      have h_eq :
          (∫⁻ p : G × G, ENNReal.ofReal (H p) ∂(μ.prod μ)) =
            ENNReal.ofReal (∫ x, ∫ y, H (x, y) ∂μ ∂μ) := h_tonelli
      have h_le :
          ENNReal.ofReal (∫ x, ∫ y, H (x, y) ∂μ ∂μ) ≤
            ENNReal.ofReal C :=
        ENNReal.ofReal_le_ofReal
          (by
            have := h_real_bound
            exact this)
      simpa [h_eq] using h_le

    -- Step 6: unfold the definition of C to match the required statement.
    simpa [C, hC_def] using h_enreal

  have h_lintegral_lt_top' :
      (∫⁻ p : G × G, ENNReal.ofReal (H p) ∂(μ.prod μ)) < ⊤ :=
    lt_of_le_of_lt h_bound ENNReal.ofReal_lt_top

  -- Step 3: rewrite the statement back in terms of the original kernel.
  simpa [G, μ, H, hH_def] using h_lintegral_lt_top'

theorem convolution_dual_kernel_integrable
    (f g φ : (Fin n → ℝ) → ℂ)
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 < r) (hr_ne_top : r ≠ ∞)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume)
    (hφ : MemLp φ r.conjExponent volume) :
    Integrable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        f (p.1 - p.2) * g p.2 * conj (φ p.1))
      (volume.prod volume) := by
  classical
  -- Work with a local notation for the underlying group and measure.
  let G := (Fin n → ℝ)
  let μ : Measure G := volume

  -- Define the triple kernel on G × G.
  set K : G × G → ℂ :=
    fun p => f (p.1 - p.2) * g p.2 * conj (φ p.1) with hK_def

  -- Step 1: basic measurability of the kernel.
  have hf_aesm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hg_aesm : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hφ_aesm : AEStronglyMeasurable φ μ := hφ.aestronglyMeasurable

  -- Measurability of the convolution kernel (x, y) ↦ f(x - y) * g(y).
  have h_fg_aesm :
      AEStronglyMeasurable
        (fun p : G × G => f (p.1 - p.2) * g p.2)
        (μ.prod μ) :=
    convolution_kernel_aestronglyMeasurable (μ := μ)
      f g hf_aesm hg_aesm

  -- Measurability of the factor (x, y) ↦ conj (φ x).
  have hφ_prod_aemeas :
      AEMeasurable (fun p : G × G => φ p.1) (μ.prod μ) :=
    hφ_aesm.aemeasurable.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
  have hφ_prod_aesm :
      AEStronglyMeasurable (fun p : G × G => φ p.1) (μ.prod μ) :=
    hφ_prod_aemeas.aestronglyMeasurable
  have hφ_prod_conj_aesm :
      AEStronglyMeasurable (fun p : G × G => conj (φ p.1)) (μ.prod μ) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hφ_prod_aesm

  -- Combine the pieces to obtain AEStronglyMeasurable for K.
  have hK_ae :
      ((fun p : G × G => f (p.1 - p.2) * g p.2) *
        fun p : G × G => conj (φ p.1)) =ᵐ[μ.prod μ] K := by
    refine Filter.Eventually.of_forall ?_
    intro p
    -- Pointwise, K p is exactly the product of the two factors.
    simp [K, hK_def, mul_assoc, mul_left_comm, mul_comm]

  have hK_aesm : AEStronglyMeasurable K (μ.prod μ) :=
    (h_fg_aesm.mul hφ_prod_conj_aesm).congr hK_ae

  -- Step 2: integrability of K from an L¹-bound.
  -- We rewrite the Bochner integrability condition in terms of the
  -- scalar nonnegative function ‖K‖, and bound it using Hölder-Young
  -- type estimates on the product space.  The detailed analytic
  -- argument is technical and will be supplied later.
  have hK_hasFinite :
      HasFiniteIntegral K (μ.prod μ) := by
    -- Work with the norm of K in scalar form.
    have h_norm_eq :
        (fun p : G × G => ‖K p‖) =
          fun p =>
            ‖f (p.1 - p.2)‖ * ‖g p.2‖ * ‖φ p.1‖ := by
      funext p
      simp [K, hK_def, norm_mul, mul_comm, mul_left_comm, mul_assoc,
        Real.norm_eq_abs, abs_mul]

    -- Rewrite the HasFiniteIntegral condition using h_norm_eq.
    -- By definition,
    --   HasFiniteIntegral K (μ.prod μ)
    -- means ∫⁻ p, ‖K p‖ₑ d(μ×μ)(p) < ∞.
    -- Using h_norm_eq, this becomes a finiteness statement for
    -- the lintegral of the nonnegative kernel built from the norms of
    -- f, g, and φ.
    have h_int_eq :
        (∫⁻ p, ‖K p‖ₑ ∂(μ.prod μ)) =
          ∫⁻ p : G × G,
            ENNReal.ofReal
              (‖g p.2‖ * (‖φ p.1‖ * ‖f (p.1 - p.2)‖)) ∂(μ.prod μ) := by
      refine lintegral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro p
      -- Pointwise identification of the ENNReal-valued kernels.
      have hnorm :
          ‖K p‖ =
            ‖f (p.1 - p.2)‖ * ‖g p.2‖ * ‖φ p.1‖ := by
        -- Specialize h_norm_eq at p.
        have := congrArg (fun (F : G × G → ℝ) => F p) h_norm_eq
        simpa using this
      -- Rearrange the scalar product to match the target expression.
      have h_prod :
          ‖g p.2‖ * (‖φ p.1‖ * ‖f (p.1 - p.2)‖) =
            ‖f (p.1 - p.2)‖ * ‖g p.2‖ * ‖φ p.1‖ := by
        ring_nf
      -- Now relate the ENNReal norms using `ofReal_norm_eq_enorm`.
      calc
        ‖K p‖ₑ
            = ENNReal.ofReal ‖K p‖ := (ofReal_norm_eq_enorm (K p)).symm
        _ = ENNReal.ofReal
              (‖f (p.1 - p.2)‖ * ‖g p.2‖ * ‖φ p.1‖) := by
              simp [hnorm]
        _ = ENNReal.ofReal
              (‖g p.2‖ * (‖φ p.1‖ * ‖f (p.1 - p.2)‖)) := by
              congr 1
              exact h_prod.symm

    -- Using the MemLp assumptions on f, g, and φ together with the
    -- Young exponent relation hpqr and Hölder-Minkowski tools from
    -- `HolderInequality` and `MinkowskiIntegral`, one shows that the
    -- right-hand side lintegral is finite.  This yields the desired
    -- HasFiniteIntegral statement via h_int_eq.
    --
    -- The detailed analytic proof is technical and is deferred to
    -- subsequent development; here we record the resulting fact as a
    -- placeholder.
    have h_lintegral_lt_top :
        (∫⁻ p : G × G,
          ENNReal.ofReal
            (‖g p.2‖ * (‖φ p.1‖ * ‖f (p.1 - p.2)‖)) ∂(μ.prod μ)) < ⊤ := by
      simpa [G, μ] using
        (convolution_dual_kernel_lintegral_lt_top
          (f := f) (g := g) (φ := φ)
          (p := p) (q := q) (r := r)
          hp hq hr hr_ne_top hpqr hf hg hφ)

    -- Translate finiteness of the rewritten lintegral back to
    -- HasFiniteIntegral K.
    have hK_lt_top :
        (∫⁻ p, ‖K p‖ₑ ∂(μ.prod μ)) < ⊤ := by
      simpa [h_int_eq] using h_lintegral_lt_top
    exact hK_lt_top

  exact ⟨hK_aesm, hK_hasFinite⟩

/--
**Fubini's theorem with variable change for convolution.**

For the product measure setting, we can exchange integration order and
apply variable substitution x - y = z.
-/
theorem fubini_convolution_product
    (f g φ : (Fin n → ℝ) → ℂ)
    (h_integrable :
      Integrable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f (p.1 - p.2) * g p.2 * φ p.1)
        (volume.prod volume)) :
    ∫ x, (∫ y, f (x - y) * g y) * φ x ∂volume =
      ∫ y, (∫ z, f z * φ (z + y)) * g y ∂volume := by
  classical
  -- Work with a local notation for the measure.
  let μ : Measure (Fin n → ℝ) := volume

  -- Step 1: rewrite the left-hand side as an iterated integral of the full kernel.
  have h_lhs_fun :
      (fun x : (Fin n → ℝ) =>
        (∫ y, f (x - y) * g y ∂μ) * φ x) =
        fun x => ∫ y, f (x - y) * g y * φ x ∂μ := by
    funext x
    -- Pull the scalar φ x inside the inner integral.
    have h_const_mul :
        ∫ y, φ x * (f (x - y) * g y) ∂μ =
          φ x * ∫ y, f (x - y) * g y ∂μ := by
      simpa using
        (MeasureTheory.integral_const_mul
          (μ := μ) (r := φ x)
          (f := fun y : (Fin n → ℝ) => f (x - y) * g y))
    have h_const_mul' :
        ∫ y, f (x - y) * g y * φ x ∂μ =
          φ x * ∫ y, f (x - y) * g y ∂μ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_const_mul
    calc
      (∫ y, f (x - y) * g y ∂μ) * φ x
          = φ x * ∫ y, f (x - y) * g y ∂μ := by
              simp [mul_comm]
      _ = ∫ y, f (x - y) * g y * φ x ∂μ := h_const_mul'.symm

  have h_lhs :
      ∫ x, (∫ y, f (x - y) * g y ∂μ) * φ x ∂μ =
        ∫ x, ∫ y, f (x - y) * g y * φ x ∂μ ∂μ := by
    simp [h_lhs_fun]

  -- Step 2: apply Fubini to swap the order of integration for the full kernel.
  have h_kernel_integrable :
      Integrable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f (p.1 - p.2) * g p.2 * φ p.1)
        (μ.prod μ) := by
    simpa [μ] using h_integrable

  have h_fubini :
      ∫ x, ∫ y, f (x - y) * g y * φ x ∂μ ∂μ =
        ∫ y, ∫ x, f (x - y) * g y * φ x ∂μ ∂μ := by
    simpa [Function.uncurry, μ] using
      (MeasureTheory.integral_integral_swap
        (μ := μ) (ν := μ)
        (f := fun x y => f (x - y) * g y * φ x)
        h_kernel_integrable)

  -- Step 3: rewrite the right-hand side in terms of the same kernel,
  -- using the change of variables (x, y) ↦ (x - y, y).
  have h_rhs :
      ∫ y, ∫ x, f (x - y) * g y * φ x ∂μ ∂μ =
        ∫ y, (∫ z, f z * φ (z + y) ∂μ) * g y ∂μ := by
    -- This is the variable change x = z + y, implemented via the
    -- measure-preserving map (x, y) ↦ (x - y, y) on the product space.
    -- The detailed proof will use `measurePreserving_sub_prod` together
    -- with the corresponding change-of-variables formula for integrals.
    -- Here we organize the calculation so that the remaining work is
    -- reduced to a one-dimensional change of variables inside the inner
    -- integral.

    -- Step 3a: factor out the constant g y from the inner integral.
    have h_inner :
        (fun y =>
          ∫ x, f (x - y) * g y * φ x ∂μ) =
        fun y => g y * ∫ x, f (x - y) * φ x ∂μ := by
      funext y
      have h_const_mul :
          ∫ x, g y * (f (x - y) * φ x) ∂μ =
            g y * ∫ x, f (x - y) * φ x ∂μ := by
        simpa using
          (MeasureTheory.integral_const_mul
            (μ := μ) (r := g y)
            (f := fun x : (Fin n → ℝ) => f (x - y) * φ x))
      have h_const_mul' :
          ∫ x, f (x - y) * g y * φ x ∂μ =
            g y * ∫ x, f (x - y) * φ x ∂μ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_const_mul
      simpa [mul_comm] using h_const_mul'

    have h_rhs1 :
        ∫ y, ∫ x, f (x - y) * g y * φ x ∂μ ∂μ =
          ∫ y, g y * ∫ x, f (x - y) * φ x ∂μ ∂μ := by
      simp [h_inner]

    -- Step 3b: change variables x = z + y inside the inner integral.
    have h_change :
        (fun y =>
          ∫ x, f (x - y) * φ x ∂μ) =
        fun y => ∫ z, f z * φ (z + y) ∂μ := by
      -- This is the change of variables x = z + y, implemented via the
      -- translation invariance of μ on ℝⁿ.
      funext y
      -- Define the translated integrand h_y(z) = f z * φ (z + y).
      have h_sub :
          ∫ x, (fun z : (Fin n → ℝ) => f z * φ (z + y)) (x - y) ∂μ =
            ∫ x, (fun z : (Fin n → ℝ) => f z * φ (z + y)) x ∂μ :=
        MeasureTheory.integral_sub_right_eq_self
          (μ := μ)
          (f := fun z : (Fin n → ℝ) => f z * φ (z + y))
          y
      -- Rewrite both sides in terms of the original integrands.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_sub

    have h_rhs2 :
        ∫ y, g y * ∫ x, f (x - y) * φ x ∂μ ∂μ =
          ∫ y, g y * ∫ z, f z * φ (z + y) ∂μ ∂μ := by
      -- Apply `h_change` inside the outer integral by functoriality.
      have h_change' :
          ∫ y, g y * (∫ x, f (x - y) * φ x ∂μ) ∂μ =
            ∫ y, g y * (∫ z, f z * φ (z + y) ∂μ) ∂μ :=
        congrArg
          (fun (F : (Fin n → ℝ) → ℂ) =>
            ∫ y, g y * F y ∂μ)
          h_change
      simpa using h_change'

    -- Step 3c: reorder the scalar multiplication to match the target.
    have h_rhs3 :
        ∫ y, g y * ∫ z, f z * φ (z + y) ∂μ ∂μ =
          ∫ y, (∫ z, f z * φ (z + y) ∂μ) * g y ∂μ := by
      have h_point :
          (fun y =>
            g y * ∫ z, f z * φ (z + y) ∂μ) =
          (fun y =>
            (∫ z, f z * φ (z + y) ∂μ) * g y) := by
        funext y
        simp [mul_comm]
      simp [h_point]

    exact h_rhs1.trans (h_rhs2.trans h_rhs3)

  -- Assemble the three steps.
  have h_lhs' :
      ∫ x, (∫ y, f (x - y) * g y) * φ x ∂volume =
        ∫ x, ∫ y, f (x - y) * g y * φ x ∂volume ∂volume := by
    simpa [μ] using h_lhs

  have h_fubini' :
      ∫ x, ∫ y, f (x - y) * g y * φ x ∂volume ∂volume =
        ∫ y, ∫ x, f (x - y) * g y * φ x ∂volume ∂volume := by
    simpa [μ] using h_fubini

  have h_rhs' :
      ∫ y, ∫ x, f (x - y) * g y * φ x ∂volume ∂volume =
        ∫ y, (∫ z, f z * φ (z + y)) * g y ∂volume := by
    simpa [μ] using h_rhs

  calc
    ∫ x, (∫ y, f (x - y) * g y) * φ x ∂volume
        = ∫ x, ∫ y, f (x - y) * g y * φ x ∂volume ∂volume := h_lhs'
    _ = ∫ y, ∫ x, f (x - y) * g y * φ x ∂volume ∂volume := h_fubini'
    _ = ∫ y, (∫ z, f z * φ (z + y)) * g y ∂volume := h_rhs'

/--
**Dual pairing bound for convolution (key for 1 < r < ∞).**

For any test function φ ∈ L^(r'), the pairing with the convolution is bounded.
This is the heart of the duality-based approach.
-/
theorem convolution_dual_pairing_bound
    (f g φ : (Fin n → ℝ) → ℂ)
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 < r) (hr_ne_top : r ≠ ∞)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume)
    (hφ : MemLp φ r.conjExponent volume) :
    ‖∫ x, (∫ y, f (x - y) * g y) * conj (φ x) ∂volume‖ ≤
      (eLpNorm f p volume).toReal *
      (eLpNorm g q volume).toReal *
      (eLpNorm φ r.conjExponent volume).toReal := by
  classical
  -- Local notation for the underlying measure.
  let μ : Measure (Fin n → ℝ) := volume

  -- Step 1: express the pairing as an integral over the product space
  -- using the Fubini/convolution change-of-variables lemma applied to
  -- the test function `x ↦ conj (φ x)`.
  have h_kernel_integrable :
      Integrable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f (p.1 - p.2) * g p.2 * conj (φ p.1))
        (μ.prod μ) := by
    -- Use the global kernel integrability statement specialized to `volume`.
    simpa [μ] using
      (convolution_dual_kernel_integrable
        (f := f) (g := g) (φ := φ)
        (p := p) (q := q) (r := r)
        hp hq hr hr_ne_top hpqr hf hg hφ)

  have h_fubini :
      ∫ x, (∫ y, f (x - y) * g y) * conj (φ x) ∂μ =
        ∫ y, (∫ z, f z * conj (φ (z + y)) ∂μ) * g y ∂μ := by
    -- Apply `fubini_convolution_product` with the modified test function.
    have h :=
      fubini_convolution_product
        (f := f) (g := g) (φ := fun x => conj (φ x))
        (h_integrable := h_kernel_integrable)
    simpa [μ] using h

  -- Step 2: for each fixed y, bound the inner integral in z by Hölder,
  -- using the exponent relation obtained from Young's condition.
  have h_exponents :
      ∃ p', IsConjugateExponent p p' ∧
        1 / p' + 1 / q = 1 / r.conjExponent := by
    -- This will be supplied by `young_exponent_relation` in the full proof,
    -- once the necessary endpoint/exponent assumptions are in place.
    -- (Skeleton placeholder.)
    sorry

  -- Using `h_exponents` and Hölder for convolution-type integrands,
  -- one can show that for almost every y,
  --   ‖∫ z, f z * conj (φ (z + y)) ∂μ‖
  --   ≤ (eLpNorm f p μ).toReal * (eLpNorm φ r.conjExponent μ).toReal.
  have h_inner_bound :
      ∀ᵐ y ∂μ,
        ‖∫ z, f z * conj (φ (z + y)) ∂μ‖ ≤
          (eLpNorm f p μ).toReal *
          (eLpNorm φ r.conjExponent μ).toReal := by
    -- This step will use `holder_inequality_convolution_general`
    -- together with the translation invariance of the Lᵖ norm.
    -- (Skeleton placeholder.)
    sorry

  -- Step 3: treat the outer integral in y as a pairing between
  --   y ↦ ∫ z, f z * conj (φ (z + y)) ∂μ
  -- and g(y), and apply Hölder/Minkowski to obtain the final bound
  --   ≤ ‖f‖_p · ‖g‖_q · ‖φ‖_{r'}.
  -- The detailed implementation will combine `h_inner_bound` with
  -- Minkowski's integral inequality in the y-variable.
  --
  -- Since these analytic estimates are nontrivial, we leave the
  -- remaining steps as a placeholder here.
  --
  -- (Skeleton placeholder for the concluding inequality.)
  sorry

/--
**Duality theorem for Lᵖ spaces (1 < p < ∞).**

The Lᵖ norm can be computed as the supremum over dual pairings with L^(p') functions.
-/
theorem eLpNorm_eq_dual_sup
    {p : ℝ≥0∞}
    (f : (Fin n → ℝ) → ℂ)
    (hp : 1 < p) (hp_ne_top : p ≠ ∞)
    (hf : MemLp f p volume) :
    eLpNorm f p volume =
      ⨆ (φ : (Fin n → ℝ) → ℂ) (hφ : MemLp φ p.conjExponent volume)
        (hφ_norm : eLpNorm φ p.conjExponent volume ≤ 1),
        ENNReal.ofReal (‖∫ x, f x * conj (φ x) ∂volume‖) := by
  sorry

/--
**Measure-preserving property of (x, y) ↦ (x - y, y).**

The transformation (x, y) ↦ (x - y, y) preserves the product measure on ℝⁿ × ℝⁿ.
This is used in variable substitutions during Fubini applications.
-/
theorem measurePreserving_sub_prod :
    MeasurePreserving
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 - p.2, p.2))
      (volume.prod volume) (volume.prod volume) := by
  sorry

/--
**Special case: Young's inequality when p = 1.**

When p = 1, the proof simplifies significantly and only requires Minkowski's
integral inequality without duality.
-/
theorem young_convolution_p_one
    {q : ℝ≥0∞}
    (f g : (Fin n → ℝ) → ℂ)
    (hq : 1 ≤ q)
    (hf : MemLp f 1 volume)
    (hg : MemLp g q volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) q volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) q volume ≤
      eLpNorm f 1 volume * eLpNorm g q volume := by
  sorry

/--
**Special case: Young's inequality when q = 1.**

When q = 1, we have r = p by the exponent condition.
-/
theorem young_convolution_q_one
    {p : ℝ≥0∞}
    (f g : (Fin n → ℝ) → ℂ)
    (hp : 1 ≤ p)
    (hf : MemLp f p volume)
    (hg : MemLp g 1 volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) p volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) p volume ≤
      eLpNorm f p volume * eLpNorm g 1 volume := by
  sorry

end KeyTheorems

/-!
# Young's Inequality for Convolution

This file provides Young's inequality for convolution in Lp spaces.

## Main results

- `young_convolution_inequality`: The main Young's inequality
- `young_L1_L1`: Special case: ‖f * g‖₁ ≤ ‖f‖₁ · ‖g‖₁
- `young_L1_L2`: Special case: ‖f * g‖₂ ≤ ‖f‖₂ · ‖g‖₁
- `convolution_diff_bound_L1`: Used in the paper's proof (Step 3)
- `convolution_diff_bound_L2`: L² version

## References

- Folland, Real Analysis, Theorem 8.8
- papers/schwartz_density_constructive_analysis.md, Section 3.2, Lemma 3.9
- papers/schwartz_density_constructive_analysis.md, Section 4.2, Step 3

## Technical notes

Young's inequality states that for 1 ≤ p, q, r ≤ ∞ with 1/p + 1/q = 1 + 1/r:
  ‖f * g‖_r ≤ ‖f‖_p · ‖g‖_q

For the Schwartz density theorem, we primarily need:
1. p = q = 1, r = 1: ‖f * g‖₁ ≤ ‖f‖₁ · ‖g‖₁
2. p = 2, q = 1, r = 2: ‖f * g‖₂ ≤ ‖f‖₂ · ‖g‖₁

-/

section YoungGeneral

/--
**Young's inequality for convolution (general form).**

For 1 ≤ p, q, r ≤ ∞ with 1/p + 1/q = 1 + 1/r:
  ‖f * g‖_r ≤ ‖f‖_p · ‖g‖_q
-/
theorem young_convolution_inequality
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) r volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
  classical

  -- Young's inequality proof strategy:
  --
  -- Key idea: Use Hölder's inequality and Minkowski's integral inequality
  --
  -- Step 1: For each x, estimate |∫ f(x-y) g(y) dy|
  -- Using Hölder: |∫ f(x-y) g(y) dy| ≤ (∫ |f(x-y)|^p' dy)^(1/p') · (∫ |g(y)|^q' dy)^(1/q')
  -- where 1/p' + 1/q' = 1
  --
  -- Step 2: Take L^r norm over x and apply Minkowski's integral inequality
  --
  -- The difficulty is that we need to relate the exponents p', q', r
  -- to the original p, q, r via the condition 1/p + 1/q = 1 + 1/r

  -- First, establish basic properties
  have hf_ae : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hg_ae : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  have hf_lt_top : eLpNorm f p volume < ⊤ := hf.eLpNorm_lt_top
  have hg_lt_top : eLpNorm g q volume < ⊤ := hg.eLpNorm_lt_top
  have hf_ne_top : eLpNorm f p volume ≠ ∞ := ne_of_lt hf_lt_top
  have hg_ne_top : eLpNorm g q volume ≠ ∞ := ne_of_lt hg_lt_top
  -- Basic positivity facts about the exponents.
  have hp_pos : (0 : ℝ≥0∞) < p := zero_lt_one.trans_le hp
  have hq_pos : (0 : ℝ≥0∞) < q := zero_lt_one.trans_le hq
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
  have hp_inv_ne_top : 1 / p ≠ ⊤ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hp_ne_zero)
  have hq_inv_ne_top : 1 / q ≠ ⊤ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hq_ne_zero)
  have hsum_ne_top : 1 / p + 1 / q ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hp_inv_ne_top, hq_inv_ne_top⟩
  have hr_ne_zero : r ≠ 0 := by
    intro hr_zero
    have h_rhs : 1 + 1 / r = ⊤ := by
      simp [hr_zero]
    have : 1 / p + 1 / q = ⊤ := by
      calc
        1 / p + 1 / q = 1 + 1 / r := hpqr
        _ = ⊤ := h_rhs
    exact hsum_ne_top this
  have hr_inv_ne_top : 1 / r ≠ ⊤ := by
    simpa [one_div] using (ENNReal.inv_ne_top.mpr hr_ne_zero)
  -- Package the convolution integrand and the convolution itself for reuse.
  set kernel := fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2) * g p.2 with hkernel_def
  set conv := fun x : (Fin n → ℝ) => ∫ y, f (x - y) * g y with hconv_def

  -- Re-express the goal in terms of the named convolution.
  suffices h_goal :
      MemLp conv r volume ∧
        eLpNorm conv r volume ≤
          eLpNorm f p volume * eLpNorm g q volume by
    simpa [conv, hconv_def] using h_goal

  have hf_aemeas : AEMeasurable f volume := hf_ae.aemeasurable
  have hg_aemeas : AEMeasurable g volume := hg_ae.aemeasurable
  have h_sub_qmp :
      Measure.QuasiMeasurePreserving
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2)
          (volume.prod volume) volume := by
    have h_measPres :
        MeasurePreserving
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 - p.2, p.2))
            (volume.prod volume) (volume.prod volume) :=
      measurePreserving_sub_prod (μ := volume) (ν := volume)
    have h_fst_qmp :
        Measure.QuasiMeasurePreserving
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1)
            (volume.prod volume) volume :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)
    have h_comp :=
      h_fst_qmp.comp h_measPres.quasiMeasurePreserving
    simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
      using h_comp
  have hf_prod_aemeas :
      AEMeasurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2))
        (volume.prod volume) :=
    hf_aemeas.comp_quasiMeasurePreserving h_sub_qmp
  have hg_prod_aemeas :
      AEMeasurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g p.2)
        (volume.prod volume) :=
    hg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hkernel_aemeas :
      AEMeasurable kernel (volume.prod volume) := by
    have := hf_prod_aemeas.mul hg_prod_aemeas
    simpa [kernel, hkernel_def, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hkernel_meas :
      AEStronglyMeasurable kernel (volume.prod volume) :=
    hkernel_aemeas.aestronglyMeasurable
  have hf_norm : MemLp (fun x => ‖f x‖) p volume := hf.norm
  have hg_norm : MemLp (fun x => ‖g x‖) q volume := hg.norm
  have h_conv_meas : AEStronglyMeasurable conv volume := by
    simpa [conv, hconv_def, kernel, hkernel_def] using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := volume) (ν := volume) (f := kernel) hkernel_meas)

  haveI : (volume : Measure (Fin n → ℝ)).IsNegInvariant :=
    volume_isNegInvariant (n := n)

  -- When `r = ⊤`, the exponent relation forces `p` and `q` to be conjugate.
  have h_conjugate_of_top : r = ⊤ → ENNReal.HolderConjugate p q := by
    intro hr_top
    have hpq_one : 1 / p + 1 / q = 1 := by simpa [hr_top] using hpqr
    exact young_exponent_inf_case hp hq hpq_one

  by_cases hr_top : r = ⊤
  · have h_conjugate : ENNReal.HolderConjugate p q := h_conjugate_of_top hr_top
    haveI : ENNReal.HolderConjugate p q := h_conjugate
    have hpq_one : 1 / p + 1 / q = 1 := by simpa [hr_top] using hpqr
    have hpq : IsConjugateExponent p q := by
      classical
      have h_inv_q : 1 / q = 1 - 1 / p :=
        ENNReal.eq_sub_of_add_eq' (by simp : (1 : ℝ≥0∞) ≠ ∞)
          (by simpa [add_comm] using hpq_one)
      have h_inv_p : 1 / p = 1 - 1 / q :=
        ENNReal.eq_sub_of_add_eq' (by simp : (1 : ℝ≥0∞) ≠ ∞) hpq_one
      by_cases hp_one : p = 1
      · subst hp_one
        have h_inv_zero : 1 / q = 0 := by
          simpa [one_div, inv_one, sub_self] using h_inv_q
        have hq_top : q = ⊤ :=
          ENNReal.inv_eq_zero.mp (by simpa [one_div] using h_inv_zero)
        exact Or.inl ⟨rfl, hq_top⟩
      · have hp_ne_one : p ≠ 1 := hp_one
        by_cases hp_top : p = ⊤
        · subst hp_top
          have h_inv : 1 / q = 1 := by
            simpa [one_div, ENNReal.inv_top, zero_add] using hpq_one
          have hq_one : q = 1 := by
            have h_inv' : q⁻¹ = 1 := by simpa [one_div] using h_inv
            exact ENNReal.inv_eq_one.mp h_inv'
          exact Or.inr <| Or.inl ⟨rfl, hq_one⟩
        · have hp_ne_top : p ≠ ∞ := hp_top
          have hq_ne_top : q ≠ ∞ := by
            intro hq_top
            have h_inv : 1 / p = 1 := by
              simpa [hq_top, one_div, ENNReal.inv_top, add_comm] using hpq_one
            have h_inv' : p⁻¹ = 1 := by simpa [one_div] using h_inv
            have hp_one : p = 1 := by
              exact ENNReal.inv_eq_one.mp h_inv'
            exact hp_ne_one hp_one
          have hq_ne_one : q ≠ 1 := by
            intro hq_one
            have h_inv_zero : 1 / p = 0 := by
              simpa [hq_one, one_div, inv_one, sub_self] using h_inv_p
            have h_inv_zero' : p⁻¹ = 0 := by simpa [one_div] using h_inv_zero
            have hp_top : p = ⊤ := ENNReal.inv_eq_zero.mp h_inv_zero'
            exact hp_ne_top hp_top
          have hp_lt_top : p < ⊤ := lt_of_le_of_ne le_top hp_ne_top
          have hq_lt_top : q < ⊤ := lt_of_le_of_ne le_top hq_ne_top
          have hp_gt_one : 1 < p := lt_of_le_of_ne hp (by simpa [eq_comm] using hp_ne_one)
          have hq_gt_one : 1 < q := lt_of_le_of_ne hq (by simpa [eq_comm] using hq_ne_one)
          exact Or.inr <| Or.inr ⟨hp_gt_one, hp_lt_top, hq_gt_one, hq_lt_top, hpq_one⟩
    have h_holder_convolution :
        ∀ x, Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) volume ∧
          ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂volume
              ≤ (eLpNorm f p volume).toReal * (eLpNorm g q volume).toReal := by
      intro x
      classical
      simpa using
        holder_inequality_convolution (μ := volume) (p := p) (q := q)
          (f := fun z => ‖f z‖) (g := fun z => ‖g z‖)
          hpq hf_norm hg_norm x
    set C :=
      (eLpNorm f p volume).toReal * (eLpNorm g q volume).toReal with hC_def
    have h_conv_pointwise : ∀ x, ‖conv x‖ ≤ C := by
      intro x
      have h_norm_le :
          ‖∫ y, f (x - y) * g y ∂volume‖
              ≤ ∫ y, ‖f (x - y) * g y‖ ∂volume :=
        norm_integral_le_integral_norm (μ := volume)
          (f := fun y => f (x - y) * g y)
      have h_bound :
          ∫ y, ‖f (x - y) * g y‖ ∂volume ≤ C := by
        simpa [C, norm_mul] using (h_holder_convolution x).2
      have h_le : ‖conv x‖ ≤ ∫ y, ‖f (x - y) * g y‖ ∂volume := by
        simpa [conv, hconv_def] using h_norm_le
      exact h_le.trans h_bound
    have h_conv_bound :
        ∀ᵐ x ∂volume, ‖conv x‖ ≤ C :=
      Filter.Eventually.of_forall h_conv_pointwise
    have h_memLp : MemLp conv ∞ volume :=
      memLp_top_of_bound h_conv_meas (C := C) h_conv_bound
    have h_bound_en :
        (fun x => (‖conv x‖ₑ : ℝ≥0∞)) ≤ᵐ[volume]
          fun _ => ENNReal.ofReal C := by
      refine h_conv_bound.mono ?_
      intro x hx
      have hx' : ENNReal.ofReal ‖conv x‖ ≤ ENNReal.ofReal C :=
        ENNReal.ofReal_le_ofReal hx
      simpa using hx'
    have h_essSup_le :
        essSup (fun x => (‖conv x‖ₑ : ℝ≥0∞)) volume ≤ ENNReal.ofReal C := by
      refine essSup_le_of_ae_le (μ := volume) (f := fun x => (‖conv x‖ₑ : ℝ≥0∞))
          (c := ENNReal.ofReal C) ?_
      simpa using h_bound_en
    have h_eLpNorm_le_top :
        eLpNorm conv ∞ volume ≤ ENNReal.ofReal C := by
      simpa [eLpNorm, eLpNorm_exponent_top, conv, hconv_def] using h_essSup_le
    have hf_ofReal :
        ENNReal.ofReal (eLpNorm f p volume).toReal = eLpNorm f p volume := by
      simpa using ENNReal.ofReal_toReal hf_ne_top
    have hg_ofReal :
        ENNReal.ofReal (eLpNorm g q volume).toReal = eLpNorm g q volume := by
      simpa using ENNReal.ofReal_toReal hg_ne_top
    have hf_toReal_nonneg :
        0 ≤ (eLpNorm f p volume).toReal := ENNReal.toReal_nonneg
    have hg_toReal_nonneg :
        0 ≤ (eLpNorm g q volume).toReal := ENNReal.toReal_nonneg
    have h_rhs_eq :
        ENNReal.ofReal C =
            eLpNorm f p volume * eLpNorm g q volume := by
      have h_mul :
          ENNReal.ofReal C =
              ENNReal.ofReal (eLpNorm f p volume).toReal *
                ENNReal.ofReal (eLpNorm g q volume).toReal := by
        simp [C, ENNReal.ofReal_mul, hf_toReal_nonneg, hg_toReal_nonneg]
      simpa [hf_ofReal, hg_ofReal, mul_comm, mul_left_comm, mul_assoc]
        using h_mul
    have h_memLp_r : MemLp conv r volume := by
      simpa [hr_top] using h_memLp
    have h_eLpNorm_le :
        eLpNorm conv r volume ≤ ENNReal.ofReal C := by
      simpa [hr_top] using h_eLpNorm_le_top
    refine ⟨h_memLp_r, ?_⟩
    calc
      eLpNorm conv r volume ≤ ENNReal.ofReal C := h_eLpNorm_le
      _ = eLpNorm f p volume * eLpNorm g q volume := h_rhs_eq
  · have hr_ne_top : r ≠ ⊤ := hr_top
    -- For r ≠ ⊤, we use Minkowski's integral inequality
    -- Strategy: Apply Minkowski to get
    --   ‖∫ f(·-y) g(y) dy‖_r ≤ ∫ ‖g(y)‖ · ‖f(·-y)‖_r dy
    -- Then use translation invariance: ‖f(·-y)‖_r = ‖f‖_r
    -- This gives ‖∫ f(·-y) g(y) dy‖_r ≤ ‖f‖_r · ‖g‖_1
    -- But we need ‖f‖_p · ‖g‖_q, so we need a more sophisticated approach

    -- First, derive that 1 ≤ r from the exponent relation
    have hr_ge_one : 1 ≤ r := by
      -- From 1/r = 1/p + 1/q - 1 with 1 ≤ p, q
      -- We have 1/p ≤ 1 and 1/q ≤ 1
      -- So 1/r ≤ 1, thus r ≥ 1
      have h_inv_p_le : p⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp
      have h_inv_q_le : q⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hq
      have h_inv_r_le : r⁻¹ ≤ 1 := by
        have h_eq : r⁻¹ + 1 = p⁻¹ + q⁻¹ := by
          simpa [one_div, add_comm] using hpqr.symm
        have h_sum_le : p⁻¹ + q⁻¹ ≤ 2 := by
          have : (1 : ℝ≥0∞) + 1 = 2 := by norm_num
          exact (add_le_add h_inv_p_le h_inv_q_le).trans_eq this
        have h_bound : r⁻¹ + 1 ≤ 2 := h_eq.le.trans h_sum_le
        have : r⁻¹ ≤ 1 := by
          have : (2 : ℝ≥0∞) = 1 + 1 := by norm_num
          have h_rearrange : r⁻¹ + 1 ≤ 1 + 1 := h_bound.trans_eq this
          exact ENNReal.le_of_add_le_add_right (by simp : (1 : ℝ≥0∞) ≠ ⊤) h_rearrange
        exact this
      -- r⁻¹ ≤ 1 implies 1 ≤ r (for r ≠ 0, r ≠ ⊤)
      have h_inv_r_le_real : (1 / r).toReal ≤ 1 := by
        have h := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) h_inv_r_le
        simpa [one_div] using h
      set rr := r.toReal with hrr
      have hr_pos : 0 < rr := ENNReal.toReal_pos hr_ne_zero hr_ne_top
      have h_inv_toReal : (1 / r).toReal = 1 / rr := by
        simp [hrr, one_div, ENNReal.toReal_inv, hr_ne_zero, hr_ne_top]
      have h_inv_real : 1 / rr ≤ 1 := by
        have := h_inv_r_le_real
        simpa [h_inv_toReal] using this
      have hr_ge_one_real : (1 : ℝ) ≤ rr := by
        have h' := (div_le_iff₀ hr_pos).mp h_inv_real
        have : 1 ≤ 1 * rr := h'
        simpa [one_div, one_mul] using this
      have hr_ofReal : ENNReal.ofReal rr = r := by
        simpa [hrr] using ENNReal.ofReal_toReal hr_ne_top
      have : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal rr :=
        ENNReal.ofReal_le_ofReal hr_ge_one_real
      simpa [hr_ofReal] using this

    -- Handle special cases: p = 1 or q = 1
    -- If p = 1, then 1 + 1/q = 1 + 1/r, so q = r
    -- If q = 1, then 1/p + 1 = 1 + 1/r, so p = r

    -- For now, we acknowledge that the r ≠ ⊤ case requires substantial infrastructure:
    -- - Either the pairing version of Young/HBL inequality (as outlined in lintegral_convolution_norm_bound.md)
    -- - Or the full Minkowski integral inequality with all required hypotheses
    -- - Or a duality-based approach
    --
    -- This is a significant gap that needs:
    -- 1. For p=1 or q=1 cases: direct application of Minkowski in simpler form
    -- 2. For general 1 < p, q, r < ∞: either duality or pairing Young/HBL
    --
    -- The mathematical content is well-understood but requires substantial
    -- technical infrastructure in Lean.
    sorry

end YoungGeneral
