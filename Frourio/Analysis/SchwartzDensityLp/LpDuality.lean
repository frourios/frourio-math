import Frourio.Analysis.HolderInequality.HolderInequality
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Duality arguments for `L^p` spaces

This auxiliary file collects statements describing how duality interacts
with `L^p` spaces.  The full proofs are deferred, but the theorem
signatures are provided so that other files (notably the Minkowski
integral inequality) can depend on them while development is in
progress.

The main declarations are:

* `lp_duality_pairing`: the classical Hölder-type inequality giving the
  dual pairing between `L^p` and `L^q`.
* `lp_duality_attains_sup`: existence of an almost-optimal dual element
  realising the operator norm of a non-zero `L^p` element.
All statements currently end with `sorry`, to be filled in by future
work.
-/

open scoped ENNReal
open MeasureTheory Real Topology

namespace SchwartzDensityLp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Hölder's inequality expressed as a dual pairing between `L^p` and `L^q`. -/
theorem lp_duality_pairing
    (p q : ℝ≥0∞) (_hp : 1 < p) (_hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f g : α → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  classical
  have h_holder :=
    holder_inequality (μ := μ) (p := p) (q := q) hpq (f := f) (g := g) hf hg
  have h_abs_bound : ∫ x, |f x * g x| ∂μ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
    simpa [Real.norm_eq_abs, abs_mul] using h_holder.2
  exact (abs_integral_le_integral_abs (μ := μ) (f := fun x => f x * g x)).trans h_abs_bound

/-- Scaling `f` by the reciprocal of its `L^p` norm yields a unit `eLpNorm`. -/
lemma normalized_eLpNorm_toReal_eq_one
    (p : ℝ≥0∞) {f : α → ℝ} (hf_ne_zero : (eLpNorm f p μ).toReal ≠ 0) :
    (eLpNorm (fun x => (1 / (eLpNorm f p μ).toReal) * f x) p μ).toReal = 1 := by
  classical
  set c : ℝ := (eLpNorm f p μ).toReal with hc
  have hc_ne_zero : c ≠ 0 := by simpa [hc] using hf_ne_zero
  have hc_nonneg : 0 ≤ c := ENNReal.toReal_nonneg
  have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (by simpa [hc, ne_comm] using hf_ne_zero)
  have h_scaling :
      eLpNorm (fun x => (1 / c) * f x) p μ =
        ‖(1 / c : ℝ)‖ₑ * eLpNorm f p μ := by
    simpa [hc, Pi.smul_apply, smul_eq_mul]
      using eLpNorm_const_smul (μ := μ) (p := p)
        (c := (1 / c : ℝ)) (f := f)
  have h_toReal :
      (eLpNorm (fun x => (1 / c) * f x) p μ).toReal = (1 / c) * c := by
    have h_nonneg : 0 ≤ (1 / c : ℝ) := one_div_nonneg.mpr hc_nonneg
    simpa [ENNReal.toReal_mul, hc, Real.norm_eq_abs, abs_of_nonneg h_nonneg]
      using congrArg ENNReal.toReal h_scaling
  have h_inv_mul : (1 / c : ℝ) * c = 1 := by
    simpa [one_div] using inv_mul_cancel₀ (a := c) hc_ne_zero
  exact h_toReal.trans h_inv_mul

/-- The standard Hölder extremiser associated to `f` lies in `L^q`. -/
lemma dual_candidate_memLp
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ) :
    MemLp (fun x => Real.sign (f x) * |f x| ^ (p.toReal - 1)) q μ := by
  classical
  set pr : ℝ := p.toReal with hpr
  have hp_ne_zero : p ≠ 0 := by
    have : (0 : ℝ≥0∞) < 1 := by simp
    exact ne_of_gt (lt_trans this hp)
  have hp_ne_top : p ≠ ∞ := by
    rcases hpq with h | h | h
    · rcases h with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases h with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq
      exact this.elim
    · rcases h with ⟨_, hp_lt_top, _, _, _⟩
      exact ne_of_lt hp_lt_top
  have hpr_pos : 0 < pr := by
    simpa [pr] using ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hpr_gt_one : 1 < pr := by
    have :=
      (ENNReal.toReal_lt_toReal (a := (1 : ℝ≥0∞)) (b := p) (by simp) hp_ne_top).2 hp
    simpa [pr, hpr] using this
  have hpr_ge_one : 1 ≤ pr := hpr_gt_one.le
  have hpr_ne_one : pr ≠ 1 := by
    intro h
    have hp_ofReal : ENNReal.ofReal pr = p := by
      simpa [pr] using ENNReal.ofReal_toReal hp_ne_top
    have hp_eq_one : p = 1 := by
      have : 1 = p := by simpa [h] using hp_ofReal
      exact this.symm
    have : (1 : ℝ≥0∞) < 1 := by simp [hp_eq_one] at hp
    exact lt_irrefl _ this
  -- Reduce the goal to the integrability of `|f|` raised to the conjugate exponent.
  -- Introduce the canonical dual candidate `g` and relate its norm to a simpler power.
  set g : α → ℝ := fun x => Real.sign (f x) * |f x| ^ (pr - 1)
  have hpr_sub_ne_zero : pr - 1 ≠ 0 := sub_ne_zero_of_ne hpr_ne_one
  have h_norm_abs : ∀ x, ‖g x‖ = |f x| ^ (pr - 1) := by
    intro x
    by_cases hfx : f x = 0
    · have hf_abs : |f x| = 0 := by simp [hfx]
      simp [g, hfx, hf_abs, Real.zero_rpow hpr_sub_ne_zero]
    · have hsign_abs : |Real.sign (f x)| = 1 := by
        rcases Real.sign_apply_eq_of_ne_zero (f x) hfx with hsign | hsign
        · simp [hsign]
        · simp [hsign]
      set t : ℝ := |f x| ^ (pr - 1) with ht
      have ht_nonneg : 0 ≤ t := by simpa [ht] using Real.rpow_nonneg (abs_nonneg _) _
      have ht_abs : |t| = t := abs_of_nonneg ht_nonneg
      have hcalc_abs : |g x| = |Real.sign (f x)| * |t| := by
        simp [g, ht, abs_mul]
      have hcalc_abs' : |g x| = |Real.sign (f x)| * t := by
        simpa [ht_abs]
          using hcalc_abs
      have hcalc : ‖g x‖ = |Real.sign (f x)| * t := by
        simpa [Real.norm_eq_abs] using hcalc_abs'
      simpa [hsign_abs, ht] using hcalc
  have h_norm_abs_ae : ∀ᵐ x ∂μ, ‖g x‖ = |f x| ^ (pr - 1) :=
    Filter.Eventually.of_forall h_norm_abs
  have h_abs_norm : ∀ x, ‖|f x| ^ (pr - 1)‖ = |f x| ^ (pr - 1) := by
    intro x
    have hpow_nonneg : 0 ≤ |f x| ^ (pr - 1) := Real.rpow_nonneg (abs_nonneg _) _
    simp [Real.norm_eq_abs, hpow_nonneg]
  have h_abs_norm_ae : ∀ᵐ x ∂μ, ‖|f x| ^ (pr - 1)‖ = |f x| ^ (pr - 1) :=
    Filter.Eventually.of_forall h_abs_norm
  -- The remaining work is to show membership in `MemLp` via these norm identities.
  -- Proof deferred for future development.
  classical
  -- basic properties of the conjugate exponent `q`
  have hq_ne_zero : q ≠ 0 := by
    have hlt : (0 : ℝ≥0∞) < q := lt_of_le_of_lt (by simp : (0 : ℝ≥0∞) ≤ 1) hq
    exact ne_of_gt hlt
  have hq_ne_top : q ≠ ∞ := by
    rcases hpq with hpq₁ | hpq₂ | hpq₃
    · rcases hpq₁ with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases hpq₂ with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq
      exact this.elim
    · rcases hpq₃ with ⟨_, _, _, hq_lt_top, _⟩
      exact ne_of_lt hq_lt_top
  -- collect the real exponents
  set qr : ℝ := q.toReal with hqr
  have hqr_pos : 0 < qr := by
    simpa [qr, hqr] using ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hqr_nonneg : 0 ≤ qr := hqr_pos.le
  -- obtain the real form of the conjugate relation
  have hpq_sum : 1 / p + 1 / q = 1 := by
    rcases hpq with hpq₁ | hpq₂ | hpq₃
    · rcases hpq₁ with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases hpq₂ with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq
      exact this.elim
    · rcases hpq₃ with ⟨_, _, _, _, hpq_sum⟩
      exact hpq_sum
  have hp_inv_ne_top : p⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hp_ne_zero
  have hq_inv_ne_top : q⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hq_ne_zero
  have h_inv_toReal : (1 / pr) + (1 / qr) = 1 := by
    have h_toReal := congrArg ENNReal.toReal hpq_sum
    have h_inv_pr : (p⁻¹).toReal = 1 / pr := by
      simp [pr, hpr, one_div]
    have h_inv_qr : (q⁻¹).toReal = 1 / qr := by
      simp [qr, hqr, one_div]
    have h_split := ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top
    simpa [one_div, h_split, h_inv_pr, h_inv_qr] using h_toReal
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hqr_ne_zero : qr ≠ 0 := ne_of_gt hqr_pos
  have h_pow_identity : (pr - 1) * qr = pr := by
    have h_mul_pr := congrArg (fun t : ℝ => pr * t) h_inv_toReal
    have h_simplify : (1 : ℝ) + pr / qr = pr := by
      simpa [mul_add, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hpr_ne_zero]
        using h_mul_pr
    have h_pr_div_qr : pr / qr = pr - 1 := (eq_sub_iff_add_eq').2 h_simplify
    have := congrArg (fun t : ℝ => t * qr) h_pr_div_qr
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hqr_ne_zero] using this.symm
  -- show the sign factor is measurable and hence AE strongly measurable
  have h_sign_measurable : Measurable fun x : ℝ => Real.sign x := by
    classical
    have h_neg : MeasurableSet {x : ℝ | x < 0} :=
      measurableSet_lt measurable_id measurable_const
    have h_pos : MeasurableSet {x : ℝ | 0 < x} :=
      measurableSet_lt measurable_const measurable_id
    have h_pos_fun : Measurable fun x : ℝ => if 0 < x then (1 : ℝ) else 0 :=
      (measurable_const : Measurable fun _ : ℝ => (1 : ℝ)).ite h_pos measurable_const
    have h_total : Measurable fun x : ℝ => if x < 0 then (-1 : ℝ) else if 0 < x then 1 else 0 :=
      (measurable_const : Measurable fun _ : ℝ => (-1 : ℝ)).ite h_neg h_pos_fun
    simpa [Real.sign] using h_total
  have hf_aestrong : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hf_aemeasurable : AEMeasurable f μ := hf_aestrong.aemeasurable
  have h_sign_aemeasurable : AEMeasurable (fun x => Real.sign (f x)) μ :=
    h_sign_measurable.comp_aemeasurable hf_aemeasurable
  have h_sign_aestrong : AEStronglyMeasurable (fun x => Real.sign (f x)) μ :=
    h_sign_aemeasurable.aestronglyMeasurable
  -- measurability of the power factor
  have h_abs_pow_cont : Continuous fun x : ℝ => |x| ^ (pr - 1) :=
    (continuous_abs).rpow_const (by intro _; exact Or.inr (sub_nonneg.mpr hpr_ge_one))
  have h_abs_pow_aestrong : AEStronglyMeasurable (fun x => |f x| ^ (pr - 1)) μ :=
    h_abs_pow_cont.comp_aestronglyMeasurable hf_aestrong
  have h_g_aestrong : AEStronglyMeasurable g μ := by
    have := h_sign_aestrong.mul h_abs_pow_aestrong
    simpa [g] using this
  -- identify the lintegral of `g`
  have hf_lintegral_fin : ∫⁻ x, ‖f x‖ₑ ^ pr ∂μ < ∞ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := μ) (p := p)
      (f := f) hp_ne_zero hp_ne_top hf.eLpNorm_lt_top
  have h_integrand_eq : ∀ᵐ x ∂μ, ‖g x‖ₑ ^ qr = ‖f x‖ₑ ^ pr := by
    refine h_norm_abs_ae.mono ?_
    intro x hx
    have hg_abs : |g x| = |f x| ^ (pr - 1) := by
      simpa [Real.norm_eq_abs] using hx
    have h_base_nonneg : 0 ≤ |f x| := abs_nonneg _
    have h_abs_eq : |g x| ^ qr = |f x| ^ ((pr - 1) * qr) := by
      have := Real.rpow_mul h_base_nonneg (pr - 1) qr
      simpa [hg_abs, mul_comm, mul_left_comm, mul_assoc] using this.symm
    have h_abs_pow : |g x| ^ qr = |f x| ^ pr := by
      simpa [h_pow_identity] using h_abs_eq
    have h_left : ‖g x‖ₑ ^ qr = ENNReal.ofReal (|g x| ^ qr) := by
      simpa [Real.enorm_eq_ofReal_abs] using
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hqr_nonneg
    have h_right : ‖f x‖ₑ ^ pr = ENNReal.ofReal (|f x| ^ pr) := by
      simpa [Real.enorm_eq_ofReal_abs] using
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpr_pos.le
    simpa [h_left, h_right] using congrArg ENNReal.ofReal h_abs_pow
  have hg_lintegral_fin : ∫⁻ x, ‖g x‖ₑ ^ qr ∂μ < ∞ := by
    have h_eq := lintegral_congr_ae h_integrand_eq
    simpa [h_eq] using hf_lintegral_fin
  have hg_eLpNorm_lt_top : eLpNorm g q μ < ∞ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := μ) (p := q)
        (f := g) hq_ne_zero hq_ne_top).2 hg_lintegral_fin
  exact ⟨h_g_aestrong, hg_eLpNorm_lt_top⟩

/-- The Hölder extremiser realises the dual pairing for a unit `L^p` function. -/
lemma dual_candidate_pairing_eq
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ)
    (hf_norm : (eLpNorm f p μ).toReal = 1) :
    (∫ x, f x *
        (Real.sign (f x) * |f x| ^ (p.toReal - 1)) ∂μ)
      =
        (eLpNorm f p μ).toReal *
          (eLpNorm (fun x => Real.sign (f x) * |f x| ^ (p.toReal - 1)) q μ).toReal ∧
      (eLpNorm (fun x => Real.sign (f x) * |f x| ^ (p.toReal - 1)) q μ).toReal = 1 := by
  classical
  set pr : ℝ := p.toReal with hpr
  set g : α → ℝ := fun x => Real.sign (f x) * |f x| ^ (pr - 1) with hg_def
  have hp_ne_zero : p ≠ 0 :=
    by
      have : (0 : ℝ≥0∞) < 1 := by simp
      exact ne_of_gt (lt_trans this hp)
  have hp_ne_top : p ≠ ∞ := by
    rcases hpq with h | h | h
    · rcases h with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases h with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq
      exact this.elim
    · rcases h with ⟨_, hp_lt_top, _, _, _⟩
      exact ne_of_lt hp_lt_top
  have hpq_sum : 1 / p + 1 / q = 1 := by
    obtain ⟨hp_eq, _⟩ | h := hpq
    · have : False := by simp [hp_eq] at hp
      exact (False.elim this : 1 / p + 1 / q = 1)
    · obtain ⟨hp_eq, hq_eq⟩ | h := h
      · have : False := by simp [hq_eq] at hq
        exact (False.elim this : 1 / p + 1 / q = 1)
      · rcases h with ⟨_, _, _, _, hpq_sum⟩
        exact hpq_sum
  have p_inv_add : p⁻¹ + q⁻¹ = 1 := by simpa [one_div] using hpq_sum
  haveI : ENNReal.HolderTriple p q 1 :=
    ⟨by simp [p_inv_add, inv_one]⟩
  have g_mem : MemLp g q μ := by
    simpa [g, hg_def, pr, hpr]
      using dual_candidate_memLp (μ := μ) (p := p) (q := q) hp hq hpq hf
  have h_integrable : Integrable (fun x => f x * g x) μ := by
    have :=
      MeasureTheory.MemLp.integrable_mul (p := p) (q := q) (μ := μ)
        (f := fun x => f x) (g := g) hf g_mem
    simpa [g]
      using this
  have h_holder :=
    lp_duality_pairing (μ := μ) (p := p) (q := q) hp hq hpq hf g_mem
  -- The equality statement should refine Hölder's inequality using the unit-norm hypothesis.
  -- Further analytic work is required to upgrade the inequality `h_holder` to an equality.
  -- The key ingredients prepared above: `g_mem`, `h_integrable`, and `hf_norm`.
  -- Proof deferred for future development.
  have hq_ne_zero : q ≠ 0 :=
    by
      have hq_pos : (0 : ℝ≥0∞) < q := lt_trans (by simp) hq
      exact ne_of_gt hq_pos
  have hq_ne_top : q ≠ ∞ := by
    rcases hpq with hpq₁ | hpq₂ | hpq₃
    · rcases hpq₁ with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases hpq₂ with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq
      exact this.elim
    · rcases hpq₃ with ⟨_, _, _, hq_lt_top, _⟩
      exact ne_of_lt hq_lt_top
  set qr : ℝ := q.toReal with hqr
  have hpr_pos : 0 < pr := by
    simpa [pr] using ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hpr_gt_one : 1 < pr :=
    by
      have :=
        (ENNReal.toReal_lt_toReal (a := (1 : ℝ≥0∞)) (b := p) (by simp) hp_ne_top).2 hp
      simpa [pr, hpr] using this
  have hpr_ge_one : 1 ≤ pr := hpr_gt_one.le
  have hpr_ne_one : pr ≠ 1 := by
    intro h_eq
    have : 1 < 1 := by simp [h_eq] at hpr_gt_one
    exact lt_irrefl _ this
  have hpr_sub_ne_zero : pr - 1 ≠ 0 := by
    have : pr ≠ 1 := hpr_ne_one
    simpa [sub_eq_zero] using this
  have hqr_pos : 0 < qr := by
    simpa [qr, hqr] using ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hqr_ne_zero : qr ≠ 0 := ne_of_gt hqr_pos
  have hqr_nonneg : 0 ≤ qr := hqr_pos.le
  have hpq_sum : 1 / p + 1 / q = 1 := by
    obtain ⟨hp_eq, _⟩ | h := hpq
    · have : False := by simp [hp_eq] at hp
      exact (False.elim this : 1 / p + 1 / q = 1)
    · obtain ⟨hp_eq, hq_eq⟩ | h := h
      · have : False := by simp [hq_eq] at hq
        exact (False.elim this : 1 / p + 1 / q = 1)
      · rcases h with ⟨_, _, _, _, hpq_sum⟩
        exact hpq_sum
  have hp_inv_ne_top : p⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hp_ne_zero
  have hq_inv_ne_top : q⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hq_ne_zero
  have h_inv_toReal : (1 / pr) + (1 / qr) = 1 := by
    have h_toReal := congrArg ENNReal.toReal hpq_sum
    have h_inv_pr : (p⁻¹).toReal = 1 / pr := by simp [pr, hpr, one_div]
    have h_inv_qr : (q⁻¹).toReal = 1 / qr := by simp [qr, hqr, one_div]
    have h_split := ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top
    simpa [one_div, h_split, h_inv_pr, h_inv_qr] using h_toReal
  have h_pow_identity : (pr - 1) * qr = pr := by
    have h_mul_pr := congrArg (fun t : ℝ => pr * t) h_inv_toReal
    have h_simplify : (1 : ℝ) + pr / qr = pr := by
      simpa [mul_add, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hpr_ne_zero]
        using h_mul_pr
    have h_pr_div_qr : pr / qr = pr - 1 := (eq_sub_iff_add_eq').2 h_simplify
    have := congrArg (fun t : ℝ => t * qr) h_pr_div_qr
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hqr_ne_zero] using this.symm
  -- pointwise description of the Hölder extremiser product
  have h_fg_pointwise : ∀ x, f x * g x = |f x| ^ pr := by
    intro x
    by_cases hfx : f x = 0
    · have hsign : Real.sign (f x) = 0 := by simp [hfx]
      simp [g, hg_def, hfx, hsign, Real.zero_rpow hpr_sub_ne_zero, Real.zero_rpow hpr_ne_zero]
    · have hsign_mul_self : Real.sign (f x) * f x = |f x| := by
        obtain hx | hx | hx := lt_trichotomy (f x) 0
        · simp [Real.sign_of_neg hx, hx, abs_of_neg hx, mul_comm, mul_left_comm, mul_assoc]
        · exact (hfx hx).elim
        · simp [Real.sign_of_pos hx, hx, abs_of_pos hx, mul_comm, mul_left_comm, mul_assoc]
      have h_abs_pos : 0 < |f x| := abs_pos.mpr hfx
      have hsum : 1 + (pr - 1) = pr := by ring
      calc
        f x * g x
            = f x * (Real.sign (f x) * |f x| ^ (pr - 1)) := by simp [g, hg_def]
        _ = (Real.sign (f x) * f x) * |f x| ^ (pr - 1) := by
              ring_nf
        _ = |f x| * |f x| ^ (pr - 1) := by simp [hsign_mul_self]
        _ = |f x| ^ (1 : ℝ) * |f x| ^ (pr - 1) := by simp [Real.rpow_one]
        _ = |f x| ^ pr := by
              have h_add := (Real.rpow_add h_abs_pos 1 (pr - 1)).symm
              simpa [hsum] using h_add
  have h_fg_eq :
      (fun x => f x * g x) =ᵐ[μ] fun x => |f x| ^ pr :=
    Filter.Eventually.of_forall h_fg_pointwise
  have h_abs_pow_integrable : Integrable (fun x => |f x| ^ pr) μ :=
    h_integrable.congr h_fg_eq
  have h_integral_eq :
      (∫ x, f x * g x ∂μ) = ∫ x, |f x| ^ pr ∂μ :=
    integral_congr_ae h_fg_eq
  set A : ℝ := ∫ x, |f x| ^ pr ∂μ with hA
  have hA_nonneg : 0 ≤ A :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  -- express the `L^p` norm in terms of `A`
  have h_eLpNorm_f :
      eLpNorm f p μ = ENNReal.ofReal (A ^ pr⁻¹) := by
    have :=
      MemLp.eLpNorm_eq_integral_rpow_norm (μ := μ) (f := f) hp_ne_zero hp_ne_top hf
    simpa [A, pr, hpr, Real.norm_eq_abs] using this
  have h_toReal_f : (eLpNorm f p μ).toReal = A ^ pr⁻¹ := by
    have h := congrArg ENNReal.toReal h_eLpNorm_f
    have hA_pow_nonneg : 0 ≤ A ^ pr⁻¹ := Real.rpow_nonneg hA_nonneg _
    simpa [hA_pow_nonneg] using h
  have hA_pow_eq_one : A ^ pr⁻¹ = 1 := by simpa [h_toReal_f] using hf_norm
  have hmul : pr⁻¹ * pr = 1 := by
    field_simp [hpr_ne_zero]
  have hA_eq_one : A = 1 := by
    have hpow := Real.rpow_mul hA_nonneg pr⁻¹ pr
    have hpow' : A = (A ^ pr⁻¹) ^ pr := by simpa [hmul, Real.rpow_one] using hpow
    calc
      A = (A ^ pr⁻¹) ^ pr := hpow'
      _ = 1 ^ pr := by simp [hA_pow_eq_one]
      _ = 1 := by simp
  -- describe the `L^q` norm of the dual candidate in terms of `A`
  have h_norm_abs : ∀ x, ‖g x‖ = |f x| ^ (pr - 1) := by
    intro x
    by_cases hfx : f x = 0
    · have hf_abs : |f x| = 0 := by simp [hfx]
      simp [g, hg_def, hfx, hf_abs, Real.zero_rpow hpr_sub_ne_zero]
    · have hsign_abs : |Real.sign (f x)| = 1 := by
        rcases Real.sign_apply_eq_of_ne_zero (f x) hfx with hsign | hsign
        · simp [hsign]
        · simp [hsign]
      set t : ℝ := |f x| ^ (pr - 1) with ht
      have ht_nonneg : 0 ≤ t := by simpa [ht] using Real.rpow_nonneg (abs_nonneg _) _
      have ht_abs : |t| = t := abs_of_nonneg ht_nonneg
      have hcalc_abs : |g x| = |Real.sign (f x)| * |t| := by
        simp [g, ht, abs_mul]
      have hcalc_abs' : |g x| = |Real.sign (f x)| * t := by
        simpa [ht_abs] using hcalc_abs
      have hcalc : ‖g x‖ = |Real.sign (f x)| * t := by
        simpa [Real.norm_eq_abs] using hcalc_abs'
      simpa [hsign_abs, ht] using hcalc
  have h_g_pow_eq : ∀ x, ‖g x‖ ^ qr = |f x| ^ pr := by
    intro x
    have hx_norm : ‖g x‖ = |f x| ^ (pr - 1) := h_norm_abs x
    have hpow := (Real.rpow_mul (abs_nonneg (f x)) (pr - 1) qr).symm
    simpa [hx_norm, h_pow_identity] using hpow
  have h_g_pow_fun :
      (fun x => ‖g x‖ ^ qr) = fun x => |f x| ^ pr := funext h_g_pow_eq
  have h_abs_ae : (fun x => |g x| ^ qr) =ᵐ[μ] fun x => |f x| ^ pr :=
    Filter.Eventually.of_forall fun x =>
      by simpa [Real.norm_eq_abs] using h_g_pow_eq x
  have h_abs_integral_eq : ∫ x, |g x| ^ qr ∂μ = ∫ x, |f x| ^ pr ∂μ :=
    integral_congr_ae h_abs_ae
  set B : ℝ := ∫ x, ‖g x‖ ^ qr ∂μ with hB
  have hB_eq_A : B = A := by
    calc
      B = ∫ x, |g x| ^ qr ∂μ := by simp [B, hB, Real.norm_eq_abs]
      _ = ∫ x, |f x| ^ pr ∂μ := h_abs_integral_eq
      _ = A := by simp [A, hA]
  have hB_nonneg : 0 ≤ B :=
    calc
      0 ≤ ∫ x, |g x| ^ qr ∂μ :=
        integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
      _ = B := by simp [B, hB, Real.norm_eq_abs]
  have h_eLpNorm_g :
      eLpNorm g q μ = ENNReal.ofReal (B ^ qr⁻¹) := by
    have :=
      MemLp.eLpNorm_eq_integral_rpow_norm (μ := μ) (f := g) hq_ne_zero hq_ne_top g_mem
    simpa [B, qr, hqr, Real.norm_eq_abs] using this
  have h_toReal_g : (eLpNorm g q μ).toReal = B ^ qr⁻¹ := by
    have h := congrArg ENNReal.toReal h_eLpNorm_g
    have hB_pow_nonneg : 0 ≤ B ^ qr⁻¹ := Real.rpow_nonneg hB_nonneg _
    simpa [hB_pow_nonneg] using h
  have h_integral_one : (∫ x, f x * g x ∂μ) = 1 := by
    simp [h_integral_eq, A, hA_eq_one]
  have h_norm_g_one : (eLpNorm g q μ).toReal = 1 := by
    simp [h_toReal_g, hB_eq_A, hA_eq_one]
  have h_norm_f_one : (eLpNorm f p μ).toReal = 1 := hf_norm
  refine ⟨?_, h_norm_g_one⟩
  simpa [h_integral_one, h_norm_f_one, h_norm_g_one]

/-- For a unit `L^p` element, produce a dual element saturating Hölder's inequality. -/
lemma exists_dual_pair_for_unit
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ) (hf_norm : (eLpNorm f p μ).toReal = 1) :
    ∃ g : α → ℝ,
      MemLp g q μ ∧
      (eLpNorm g q μ).toReal = 1 ∧
      Integrable (fun x => f x * g x) μ ∧
      (∫ x, f x * g x ∂μ) = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  classical
  -- Build the Hölder-dual candidate using the standard power/sign recipe.
  set pr : ℝ := p.toReal with hpr
  set qr : ℝ := q.toReal with hqr
  set g : α → ℝ :=
    fun x => Real.sign (f x) * |f x| ^ (pr - 1) with hg_def
  have hp_pos : 0 < p := lt_trans (by simp) hp
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have hp_ne_top : p ≠ ∞ := by
    cases hpq with
    | inl h =>
        rcases h with ⟨hp_eq, _⟩
        exact ((by simp [hp_eq] at hp) : False).elim
    | inr h =>
        cases h with
        | inl h' =>
            rcases h' with ⟨hp_eq, hq_eq⟩
            exact ((by simp [hq_eq] at hq) : False).elim
        | inr h' =>
            rcases h' with ⟨_, hp_top, _, _, _⟩
            exact ne_of_lt hp_top
  have h_pr_pos : 0 < pr := by
    simpa [pr] using ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have h_qr_pos : 0 < qr := by
    have hq_pos : 0 < q := lt_trans (by simp) hq
    have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
    have hq_ne_top : q ≠ ∞ := by
      cases hpq with
      | inl h =>
          rcases h with ⟨hp_eq, hq_eq⟩
          exact ((by simp [hp_eq] at hp) : False).elim
      | inr h =>
          cases h with
          | inl h' =>
              rcases h' with ⟨hp_eq, hq_eq⟩
              exact by simp [hq_eq]
          | inr h' =>
              rcases h' with ⟨_, _, _, hq_top, _⟩
              exact ne_of_lt hq_top
    simpa [qr] using ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hpq_sum : 1 / p + 1 / q = 1 := by
    obtain ⟨hp_eq, _⟩ | h := hpq
    · have : False := by simp [hp_eq] at hp
      exact (False.elim this : 1 / p + 1 / q = 1)
    · obtain ⟨hp_eq, hq_eq⟩ | h := h
      · have : False := by simp [hq_eq] at hq
        exact (False.elim this : 1 / p + 1 / q = 1)
      · rcases h with ⟨_, _, _, _, hpq_sum⟩
        exact hpq_sum
  have p_inv_add : p⁻¹ + q⁻¹ = 1 := by simpa [one_div] using hpq_sum
  haveI : ENNReal.HolderTriple p q 1 :=
    ⟨by simp [p_inv_add, inv_one]⟩
  have hg_mem : MemLp g q μ := by
    -- Show that the constructed `g` belongs to `L^q`.
    simpa [g, hg_def, pr, hpr]
      using dual_candidate_memLp (μ := μ) (p := p) (q := q) hp hq hpq hf
  have hg_integrable : Integrable (fun x => f x * g x) μ := by
    have h :=
      MeasureTheory.MemLp.integrable_mul (p := p) (q := q) (μ := μ)
        (f := fun x => f x) (g := fun x => g x) hf hg_mem
    simpa using h
  obtain ⟨hg_equality, hg_norm_one⟩ :=
    dual_candidate_pairing_eq (μ := μ) (p := p) (q := q) hp hq hpq hf hf_norm
  refine ⟨g, hg_mem, hg_norm_one, hg_integrable, ?_⟩
  exact hg_equality

/-- Pulling out a scalar when comparing `f` and its normalisation. -/
lemma integral_scaling_of_normalization
    {f g : α → ℝ} {c : ℝ} (hc_ne_zero : c ≠ 0)
    (h_int : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) =
      c * (∫ x, ((1 / c) * f x) * g x ∂μ) := by
  classical
  have h_integral_scaled :
      (∫ x, ((1 / c) * f x) * g x ∂μ) =
        (1 / c) * (∫ x, f x * g x ∂μ) := by
    have h := h_int.integral_smul (μ := μ) (c := (1 / c))
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using h
  set I : ℝ := ∫ x, f x * g x ∂μ with hI
  have h_cancel : c * c⁻¹ = 1 := by
    simpa [one_div] using mul_inv_cancel₀ hc_ne_zero
  have h_aux : ∫ x, ((1 / c) * f x) * g x ∂μ = c⁻¹ * I := by
    simpa [one_div] using h_integral_scaled
  have h_rhs : c * (∫ x, ((1 / c) * f x) * g x ∂μ) = I := by
    calc
      c * (∫ x, ((1 / c) * f x) * g x ∂μ)
          = c * (c⁻¹ * I) := by rw [h_aux]
      _ = (c * c⁻¹) * I := by
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ = I := by simp [h_cancel, I, hI, mul_comm, mul_left_comm, mul_assoc]
  have h_rhs' : I = c * (∫ x, ((1 / c) * f x) * g x ∂μ) := h_rhs.symm
  calc
    ∫ x, f x * g x ∂μ = I := by simp [I, hI]
    _ = c * (∫ x, ((1 / c) * f x) * g x ∂μ) := h_rhs'

/-- Existence of an almost-optimal element in the dual `L^q` achieving
the norm of a non-zero `L^p` element. -/
theorem lp_duality_attains_sup
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ) (hf_ne_zero : (eLpNorm f p μ).toReal ≠ 0) :
    ∃ g : α → ℝ, MemLp g q μ ∧
      (∫ x, f x * g x ∂μ) = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  classical
  -- We normalise `f` so that the rescaled function has unit `L^p` norm.
  set c : ℝ := (eLpNorm f p μ).toReal
  have hc_ne_zero : c ≠ 0 := hf_ne_zero
  set f₀ : α → ℝ := fun x => (1 / c) * f x with hf₀_def
  have hf₀_mem : MemLp f₀ p μ := by
    simpa [f₀, hf₀_def, c, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hf.const_mul (1 / c)
  -- Scaling should give a unit-norm function; this is the quantitative heart of the argument.
  have hf₀_norm_eq_one : (eLpNorm f₀ p μ).toReal = 1 := by
    have := normalized_eLpNorm_toReal_eq_one (μ := μ) (p := p) (f := f) hf_ne_zero
    simpa [f₀, hf₀_def, c]
  -- With the unit-norm representative in hand, construct a dual witness by Hölder.
  have h_exists_unit :
      ∃ g : α → ℝ,
        MemLp g q μ ∧
        (eLpNorm g q μ).toReal = 1 ∧
        Integrable (fun x => f₀ x * g x) μ ∧
        (∫ x, f₀ x * g x ∂μ) =
          (eLpNorm f₀ p μ).toReal * (eLpNorm g q μ).toReal := by
    have :=
      exists_dual_pair_for_unit (μ := μ) (p := p) (q := q) hp hq hpq
        (f := f₀) hf₀_mem hf₀_norm_eq_one
    simpa
  obtain ⟨g, hg_mem, hg_norm_one, hg_int, hg_eq⟩ := h_exists_unit
  refine ⟨g, hg_mem, ?_⟩
  have hf_int : Integrable (fun x => f x * g x) μ := by
    have hf_scaled : Integrable (fun x => c * (f₀ x * g x)) μ := hg_int.const_mul c
    have h_ae :
        (fun x => c * (f₀ x * g x)) =ᵐ[μ]
          fun x => f x * g x :=
      Filter.Eventually.of_forall (fun x => by
        simp [f₀, hf₀_def, c, hc_ne_zero, mul_comm, mul_left_comm, mul_assoc])
    exact Integrable.congr hf_scaled h_ae
  -- Convert the equality for the normalised function back to the original scaling.
  have h_integral_scaling :
      (∫ x, f x * g x ∂μ) =
        c * (∫ x, f₀ x * g x ∂μ) := by
    have := integral_scaling_of_normalization (μ := μ) (f := f) (g := g)
      (c := c) hc_ne_zero
      hf_int
    simpa [f₀, hf₀_def, c]
  -- Combine the pieces to recover the desired equality.
  have hc_toReal : (eLpNorm f p μ).toReal = c := rfl
  have h_integral_scaled :
      (∫ x, f x * g x ∂μ) =
        c * ((eLpNorm f₀ p μ).toReal * (eLpNorm g q μ).toReal) := by
    calc
      (∫ x, f x * g x ∂μ)
          = c * (∫ x, f₀ x * g x ∂μ) := h_integral_scaling
      _ = c * ((eLpNorm f₀ p μ).toReal * (eLpNorm g q μ).toReal) := by
            simp [hg_eq]
  have h_integral_final :
      (∫ x, f x * g x ∂μ) = c * (eLpNorm g q μ).toReal := by
    simpa [hf₀_norm_eq_one, mul_comm, mul_left_comm, mul_assoc] using h_integral_scaled
  simpa [hc_toReal, mul_comm, mul_left_comm, mul_assoc] using h_integral_final

/-- Produce a dual element with unit `L^q` norm attaining the `L^p` norm of `f`. -/
lemma lp_duality_exists_norm_one_attainer
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ) (hf_ne_zero : (eLpNorm f p μ).toReal ≠ 0) :
    ∃ g : α → ℝ,
      MemLp g q μ ∧
      (eLpNorm g q μ).toReal = 1 ∧
      Integrable (fun x => f x * g x) μ ∧
      (∫ x, f x * g x ∂μ) = (eLpNorm f p μ).toReal := by
  classical
  set c : ℝ := (eLpNorm f p μ).toReal
  have hc_ne_zero : c ≠ 0 := hf_ne_zero
  set f₀ : α → ℝ := fun x => (1 / c) * f x with hf₀_def
  have hf₀_mem : MemLp f₀ p μ := by
    simpa [f₀, hf₀_def, c, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hf.const_mul (1 / c)
  have hf₀_norm_eq_one : (eLpNorm f₀ p μ).toReal = 1 := by
    have := normalized_eLpNorm_toReal_eq_one (μ := μ) (p := p) (f := f) hf_ne_zero
    simpa [f₀, hf₀_def, c]
  obtain ⟨g, hg_mem, hg_norm_one, hg_int, hg_eq⟩ :=
    exists_dual_pair_for_unit (μ := μ) (p := p) (q := q) hp hq hpq
      (f := f₀) hf₀_mem hf₀_norm_eq_one
  have hf_int : Integrable (fun x => f x * g x) μ := by
    have hf_scaled : Integrable (fun x => c * (f₀ x * g x)) μ := hg_int.const_mul c
    have h_ae :
        (fun x => c * (f₀ x * g x)) =ᵐ[μ]
          fun x => f x * g x :=
      Filter.Eventually.of_forall fun x => by
        simp [f₀, hf₀_def, c, hc_ne_zero, mul_comm, mul_left_comm, mul_assoc]
    exact Integrable.congr hf_scaled h_ae
  have h_integral_scaling :
      (∫ x, f x * g x ∂μ) =
        c * (∫ x, f₀ x * g x ∂μ) := by
    have := integral_scaling_of_normalization (μ := μ) (f := f) (g := g)
      (c := c) hc_ne_zero hf_int
    simpa [f₀, hf₀_def, c]
  have h_integral_f₀ : (∫ x, f₀ x * g x ∂μ) = 1 := by
    simpa [hf₀_norm_eq_one, hg_norm_one] using hg_eq
  refine ⟨g, hg_mem, hg_norm_one, hf_int, ?_⟩
  have hc_toReal : (eLpNorm f p μ).toReal = c := rfl
  calc
    (∫ x, f x * g x ∂μ)
        = c * (∫ x, f₀ x * g x ∂μ) := h_integral_scaling
    _ = c := by simp [h_integral_f₀]
    _ = (eLpNorm f p μ).toReal := hc_toReal

/-- Control the `L^p` norm of `f` by bounding pairings against the unit ball of `L^q`. -/
theorem lp_duality_norm_le_of_pairing_bound
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ)
    {B : ℝ}
    (hB : ∀ g : α → ℝ,
      MemLp g q μ →
      (eLpNorm g q μ).toReal ≤ 1 →
      Integrable (fun x => f x * g x) μ →
      |∫ x, f x * g x ∂μ| ≤ B) :
    (eLpNorm f p μ).toReal ≤ B := by
  classical
  have h_nonneg : 0 ≤ (eLpNorm f p μ).toReal := ENNReal.toReal_nonneg
  by_cases hzero : (eLpNorm f p μ).toReal = 0
  · have hB_nonneg : 0 ≤ B := by
      have h_zero_mem : MemLp (fun _ : α => (0 : ℝ)) q μ := MemLp.zero
      have h_zero_norm : (eLpNorm (fun _ : α => (0 : ℝ)) q μ).toReal ≤ 1 := by
        simp
      have h_zero_int : Integrable (fun x => f x * (0 : ℝ)) μ := by
        simp
      have h_bound :=
        hB (fun _ : α => (0 : ℝ)) h_zero_mem h_zero_norm h_zero_int
      simpa using h_bound
    simpa [hzero] using hB_nonneg
  · have hf_ne_zero : (eLpNorm f p μ).toReal ≠ 0 := hzero
    obtain ⟨g, hg_mem, hg_norm_one, hg_int, hg_eq⟩ :=
      lp_duality_exists_norm_one_attainer (μ := μ)
        (p := p) (q := q) hp hq hpq hf hf_ne_zero
    have h_bound := hB g hg_mem (by simp [hg_norm_one]) hg_int
    have h_abs := h_bound
    have : (eLpNorm f p μ).toReal ≤ B := by
      simpa [hg_eq, abs_of_nonneg h_nonneg]
        using h_abs
    exact this

lemma eLpNorm_norm_integral_lt_top
    [SFinite μ] [SFinite ν]
    (p : ℝ≥0∞) (hp : 1 < p) (hp_ne_top : p ≠ ∞)
    {F : α → β → E}
    (hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    eLpNorm (fun x => ‖∫ y, F x y ∂ν‖) p μ < ∞ := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    have : (0 : ℝ≥0∞) < p := lt_trans (by simp) hp
    exact ne_of_gt this
  have hp_lt_top : p < ∞ := lt_of_le_of_ne le_top hp_ne_top
  have h_integral_meas :
      AEStronglyMeasurable (fun x => ∫ y, F x y ∂ν) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := ν) (f := Function.uncurry F) hF_meas)
  have h_norm_meas :
      AEStronglyMeasurable (fun x => ‖∫ y, F x y ∂ν‖) μ :=
    h_integral_meas.norm
  -- Extract the slice-wise information supplied by the product integrability assumption.
  have h_prod_info :=
    (integrable_prod_iff (μ := μ) (ν := ν)
      (f := Function.uncurry F) hF_meas).mp hF_prod
  have hF_int_left :
      ∀ᵐ x ∂μ, Integrable (fun y => F x y) ν := by
    simpa [Function.uncurry] using h_prod_info.1
  have h_majorant_int :
      Integrable (fun x => ∫ y, ‖F x y‖ ∂ν) μ := by
    simpa [Function.uncurry] using h_prod_info.2
  -- Pointwise domination by the integral of fibrewise norms.
  have h_pointwise :
      (fun x => ‖∫ y, F x y ∂ν‖)
        ≤ᵐ[μ]
          fun x => ∫ y, ‖F x y‖ ∂ν := by
    refine hF_int_left.mono ?_
    intro x hx
    have hx_bound :=
      norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    simpa using hx_bound
  -- Basic integrability of the norm of the fibrewise integral.
  have h_norm_integrable : Integrable (fun x => ‖∫ y, F x y ∂ν‖) μ := by
    refine Integrable.mono' h_majorant_int h_norm_meas ?_
    simpa using h_pointwise
  -- Introduce the auxiliary notation that will be used in the duality argument.
  set g : α → ℝ := fun x => ‖∫ y, F x y ∂ν‖
  have hg_meas : AEStronglyMeasurable g μ := h_norm_meas
  have hg_int : Integrable g μ := by simpa [g] using h_norm_integrable
  obtain ⟨q, hpq, -⟩ :=
    conjugate_exponent_formula (p := p) hp hp_lt_top
  have hq_gt_one : 1 < q := by
    rcases hpq with hpq | hpq
    · rcases hpq with ⟨hp_eq, _⟩
      simp [hp_eq] at hp
    · rcases hpq with hpq | hpq
      · rcases hpq with ⟨hp_eq, _⟩
        simpa [hp_eq] using hp_lt_top.ne
      · rcases hpq with ⟨_, _, hq, _, _⟩
        exact hq
  set B : ℝ := ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν
  have hB_nonneg : 0 ≤ B :=
    integral_nonneg fun _ => ENNReal.toReal_nonneg
  -- Pairing estimate coming from Hölder on each fibre.
  have h_pairing_bound :
      ∀ φ : α → ℝ,
        MemLp φ q μ →
        (eLpNorm φ q μ).toReal ≤ 1 →
        Integrable (fun x => g x * φ x) μ →
        |∫ x, g x * φ x ∂μ| ≤ B := by
    intro φ hφ_mem hφ_norm _hφ_int
    have h_est :=
      holder_kernel_pairing_bound (μ := μ) (ν := ν)
        (p := p) (q := q) hpq
        hF_meas hF_prod hF_memLp hF_norm hφ_mem
    have h_mul : (eLpNorm φ q μ).toReal * B ≤ B := by
      have := mul_le_mul_of_nonneg_right hφ_norm hB_nonneg
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    exact h_est.trans h_mul
  -- Final step: deduce the finiteness of the `L^p` norm from the pairing bounds.
  -- We adapt the classical duality argument based on truncations of `g`.
  set pr : ℝ := p.toReal with hpr
  have hp_ne_top : p ≠ ∞ := hp_ne_top
  have hp_toReal_pos : 0 < pr := by
    simpa [pr] using ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hp_toReal_gt_one : 1 < pr :=
    by
      have :=
        (ENNReal.toReal_lt_toReal (a := (1 : ℝ≥0∞)) (b := p) (by simp) hp_ne_top).2 hp
      simpa [pr, hpr] using this
  have hp_toReal_ge_one : 1 ≤ pr := hp_toReal_gt_one.le
  have hp_toReal_ne_one : pr ≠ 1 := ne_of_gt hp_toReal_gt_one
  have hp_toReal_sub_pos : 0 < pr - 1 := by
    have := sub_pos.mpr hp_toReal_gt_one
    simpa using this
  have hp_toReal_sub_ne_zero : pr - 1 ≠ 0 := by
    have := sub_ne_zero_of_ne hp_toReal_ne_one
    simpa using this
  set qr : ℝ := q.toReal with hqr
  have hq_ne_zero : q ≠ 0 := by
    have : (0 : ℝ≥0∞) < q := lt_of_lt_of_le
      (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) hq_gt_one.le
    exact ne_of_gt this
  have hq_ne_top : q ≠ ∞ := by
    rcases hpq with hpq₁ | hpq₂ | hpq₃
    · rcases hpq₁ with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases hpq₂ with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq_gt_one
      exact this.elim
    · rcases hpq₃ with ⟨_, _, _, hq_lt_top, _⟩
      exact ne_of_lt hq_lt_top
  have hq_toReal_pos : 0 < qr := by
    simpa [qr, hqr] using ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hq_toReal_ne_zero : qr ≠ 0 := ne_of_gt hq_toReal_pos
  have hq_toReal_nonneg : 0 ≤ qr := hq_toReal_pos.le
  have hp_inv_ne_top : p⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hp_ne_zero
  have hq_inv_ne_top : q⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hq_ne_zero
  have hpq_sum : 1 / p + 1 / q = 1 := by
    rcases hpq with hpq₁ | hpq₂ | hpq₃
    · rcases hpq₁ with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases hpq₂ with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq_gt_one
      exact this.elim
    · rcases hpq₃ with ⟨_, _, _, _, hpq_sum⟩
      exact hpq_sum
  have hpq_toReal : (1 / pr) + (1 / qr) = 1 := by
    have h_toReal := congrArg ENNReal.toReal hpq_sum
    have h_inv_pr : (p⁻¹).toReal = 1 / pr := by simp [pr, hpr, one_div]
    have h_inv_qr : (q⁻¹).toReal = 1 / qr := by simp [qr, hqr, one_div]
    have h_split := ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top
    simpa [one_div, h_split, h_inv_pr, h_inv_qr] using h_toReal
  have h_pow_identity : (pr - 1) * qr = pr := by
    have h_mul := congrArg (fun t : ℝ => t * (pr * qr)) hpq_toReal
    have h_pr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
    have h_qr_ne_zero : qr ≠ 0 := hq_toReal_ne_zero
    have h_left : (1 / pr + 1 / qr) * (pr * qr) = pr + qr := by
      have h₁ : pr⁻¹ * (pr * qr) = qr := by
        simp [one_div, h_pr_ne_zero, mul_comm, mul_left_comm, mul_assoc]
      have h₂ : qr⁻¹ * (pr * qr) = pr := by
        simp [one_div, h_qr_ne_zero, mul_comm, mul_left_comm, mul_assoc]
      calc
        (1 / pr + 1 / qr) * (pr * qr)
            = pr⁻¹ * (pr * qr) + qr⁻¹ * (pr * qr) := by
              simp [add_mul]
        _ = qr + pr := by simp [h₁, h₂]
        _ = pr + qr := by simp [add_comm]
    have h_mul' : pr + qr = pr * qr := by
      simpa [← h_left] using h_mul
    have h_diff := congrArg (fun t : ℝ => t - qr) h_mul'
    have h_fact : pr * qr - qr = (pr - 1) * qr := by ring
    simpa [h_fact, add_comm, add_left_comm, add_assoc] using h_diff.symm
  have h_qr_minus_one : qr - 1 = 1 / (pr - 1) := by
    have h_pr_sub_ne_zero : pr - 1 ≠ 0 := hp_toReal_sub_ne_zero
    have h_mul : (qr - 1) * (pr - 1) = 1 := by
      calc
        (qr - 1) * (pr - 1)
            = qr * (pr - 1) - 1 * (pr - 1) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (sub_mul qr (1 : ℝ) (pr - 1))
        _ = (pr - 1) * qr - (pr - 1) := by simp [mul_comm, mul_left_comm, mul_assoc]
        _ = pr - (pr - 1) := by simp [h_pow_identity]
        _ = 1 := by
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have h_one : (1 : ℝ) = (pr - 1) * (1 / (pr - 1)) := by
      simp [div_eq_mul_inv, h_pr_sub_ne_zero]
    have h_eq :
        (qr - 1) * (pr - 1) = (1 / (pr - 1)) * (pr - 1) := by
      simpa [mul_comm] using h_mul.trans h_one
    have h_cancel := mul_right_cancel₀ h_pr_sub_ne_zero h_eq
    simpa [div_eq_mul_inv] using h_cancel
  have h_qr_div_pr : qr / pr = 1 / (pr - 1) := by
    have h_pr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
    have h_pr_sub_ne_zero : pr - 1 ≠ 0 := hp_toReal_sub_ne_zero
    have h_div := congrArg (fun t : ℝ => t / pr) h_pow_identity
    have h_mul : (pr - 1) * (qr / pr) = 1 := by
      simpa [div_eq_mul_inv, h_pr_ne_zero, mul_comm, mul_left_comm, mul_assoc] using h_div
    have h_eq :
        (pr - 1) * (qr / pr) = (pr - 1) * (1 / (pr - 1)) := by
      have h_one : (1 : ℝ) = (pr - 1) * (1 / (pr - 1)) := by
        simp [div_eq_mul_inv, h_pr_sub_ne_zero]
      exact h_mul.trans h_one
    exact mul_left_cancel₀ h_pr_sub_ne_zero h_eq
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => norm_nonneg _
  have hg_abs : ∀ x, |g x| = g x := fun x => abs_of_nonneg (hg_nonneg x)
  have hg_norm : ∀ x, ‖g x‖ = g x := by intro x; simp [Real.norm_eq_abs, hg_abs x]
  -- Truncate the fibrewise norm in order to build admissible dual test functions
  -- whose `L^q` norms will be uniformly bounded.
  let trunc : ℕ → α → ℝ := fun N x => min (g x) (N : ℝ)
  have htrunc_le : ∀ N x, trunc N x ≤ g x := by
    intro N x; exact min_le_left _ _
  have htrunc_bdd : ∀ N x, trunc N x ≤ N := by
    intro N x
    have hle : trunc N x ≤ (N : ℝ) := min_le_right _ _
    simpa using hle
  have htrunc_nonneg : ∀ N x, 0 ≤ trunc N x := by
    intro N x
    have hgx_nonneg : 0 ≤ g x := hg_nonneg x
    have hN_nonneg : 0 ≤ (N : ℝ) := by
      exact (Nat.cast_nonneg N : 0 ≤ (N : ℝ))
    exact le_min hgx_nonneg hN_nonneg
  -- The precise control on the norm of `trunc N x` will be used when forming
  -- the candidate dual elements based on powers of the truncations.
  have htrunc_norm : ∀ N x, ‖trunc N x‖ = trunc N x := by
    intro N x
    have hnonneg : 0 ≤ trunc N x := htrunc_nonneg N x
    simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have htrunc_meas : ∀ N : ℕ, AEStronglyMeasurable (trunc N) μ := by
    intro N
    have hcont : Continuous fun t : ℝ => min t (N : ℝ) :=
      continuous_id.min continuous_const
    exact hcont.comp_aestronglyMeasurable hg_meas
  have htrunc_int : ∀ N : ℕ, Integrable (trunc N) μ := by
    intro N
    refine
      hg_int.mono' (htrunc_meas N) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have hx_le : trunc N x ≤ g x := htrunc_le N x
    have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
    have hg_nonneg' : 0 ≤ g x := hg_nonneg x
    have hle_norm : ‖trunc N x‖ ≤ g x := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hx_nonneg, abs_of_nonneg hg_nonneg'] using hx_le
    simpa using hle_norm
  have hpr_sub_nonneg : 0 ≤ pr - 1 := sub_nonneg.mpr hp_toReal_ge_one
  have htrunc_pow_bound :
      ∀ N x, (trunc N x) ^ pr ≤ (N : ℝ) ^ (pr - 1) * trunc N x := by
    intro N x
    have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
    have hx_le_N : trunc N x ≤ (N : ℝ) := htrunc_bdd N x
    by_cases hzero : trunc N x = 0
    · have hpow_zero : (trunc N x) ^ pr = 0 := by
        have hpr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
        simpa [hzero] using Real.zero_rpow hpr_ne_zero
      have hright_zero : (N : ℝ) ^ (pr - 1) * trunc N x = 0 := by
        simp [hzero]
      simp [hpow_zero, hright_zero]
    · have hx_pos : 0 < trunc N x :=
        lt_of_le_of_ne hx_nonneg (by simpa [eq_comm] using hzero)
      have hx_pow_le : (trunc N x) ^ (pr - 1) ≤ (N : ℝ) ^ (pr - 1) :=
        Real.rpow_le_rpow hx_nonneg hx_le_N hpr_sub_nonneg
      have hsum : (pr - 1) + 1 = pr := by ring
      have hpow_eq : (trunc N x) ^ pr = (trunc N x) ^ (pr - 1) * trunc N x := by
        have := Real.rpow_add hx_pos (pr - 1) 1
        simpa [hsum, Real.rpow_one, mul_comm, mul_left_comm, mul_assoc]
          using this
      have hx_nonneg' : 0 ≤ trunc N x := hx_nonneg
      have hmul_le := mul_le_mul_of_nonneg_right hx_pow_le hx_nonneg'
      simpa [hpow_eq]
        using hmul_le
  have htrunc_pow_integrable :
      ∀ N : ℕ, Integrable (fun x => (trunc N x) ^ pr) μ := by
    intro N
    set C : ℝ := (N : ℝ) ^ (pr - 1) with hC
    have hC_nonneg : 0 ≤ C := by
      simpa [hC] using Real.rpow_nonneg (show 0 ≤ (N : ℝ) from Nat.cast_nonneg _) (pr - 1)
    have h_major_int : Integrable (fun x => C * trunc N x) μ :=
      (htrunc_int N).const_mul C
    have h_pow_meas_norm :
        AEStronglyMeasurable (fun x => ‖trunc N x‖ ^ pr) μ := by
      have h_cont : Continuous fun t : ℝ => |t| ^ pr :=
        (continuous_abs).rpow_const
          (by intro _; exact Or.inr (le_of_lt hp_toReal_pos))
      have := h_cont.comp_aestronglyMeasurable ((htrunc_meas N).norm)
      simpa [Real.norm_eq_abs] using this
    have h_pow_meas :
        AEStronglyMeasurable (fun x => (trunc N x) ^ pr) μ := by
      refine h_pow_meas_norm.congr ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
      simp [Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
    have h_bound :
        ∀ᵐ x ∂μ, ‖(trunc N x) ^ pr‖ ≤ C * trunc N x := by
      refine Filter.Eventually.of_forall ?_
      intro x
      have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
      have hpow_le := htrunc_pow_bound N x
      have hnorm_pow : ‖(trunc N x) ^ pr‖ = (trunc N x) ^ pr := by
        have := Real.rpow_nonneg hx_nonneg pr
        simp [Real.norm_eq_abs, abs_of_nonneg this]
      simpa [hnorm_pow] using hpow_le
    have := Integrable.mono' h_major_int h_pow_meas h_bound
    simpa
  have htrunc_lintegral_lt_top :
      ∀ N : ℕ, (∫⁻ x, ‖trunc N x‖ₑ ^ pr ∂μ) < ∞ := by
    intro N
    have h_int := (htrunc_pow_integrable N).hasFiniteIntegral
    have h_abs_eq :
        ∀ x, ‖(trunc N x) ^ pr‖ₑ = ‖trunc N x‖ₑ ^ pr := by
      intro x
      have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
      have hpow_nonneg : 0 ≤ (trunc N x) ^ pr := Real.rpow_nonneg hx_nonneg _
      have hnorm : ‖trunc N x‖ = trunc N x := by
        simp [Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
      simp [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs, hnorm, abs_of_nonneg hx_nonneg,
        abs_of_nonneg hpow_nonneg, ENNReal.ofReal_rpow_of_nonneg hx_nonneg hp_toReal_pos.le]
    simpa [HasFiniteIntegral, h_abs_eq]
      using h_int
  have htrunc_mem : ∀ N : ℕ, MemLp (trunc N) p μ := by
    intro N
    refine ⟨htrunc_meas N, ?_⟩
    exact
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (μ := μ) (p := p) (f := trunc N) hp_ne_zero hp_ne_top).2
          (htrunc_lintegral_lt_top N)
  have hq_gt_one' : 1 ≤ q := hq_gt_one.le
  have h_trunc_pairing_bound :
      ∀ N φ,
        MemLp φ q μ →
        (eLpNorm φ q μ).toReal ≤ 1 →
        Integrable (fun x => trunc N x * φ x) μ →
        |∫ x, trunc N x * φ x ∂μ| ≤ B := by
    intro N φ hφ_mem hφ_norm hφ_int
    classical
    -- Rescale the test function so that the pairing against `g` coincides with the
    -- pairing against the truncated function.
    let coeff : α → ℝ := fun x => min (1 : ℝ) ((N : ℝ) / g x)
    let φ' : α → ℝ := fun x => coeff x * φ x
    have hcoeff_aemeas : AEMeasurable coeff μ := by
      have h_one : AEMeasurable (fun _ : α => (1 : ℝ)) μ := aemeasurable_const
      have h_div : AEMeasurable (fun x : α => (N : ℝ) / g x) μ :=
        (aemeasurable_const : AEMeasurable (fun _ : α => (N : ℝ)) μ).div
          (hg_meas.aemeasurable)
      simpa [coeff] using h_one.min h_div
    have hcoeff_meas : AEStronglyMeasurable coeff μ := hcoeff_aemeas.aestronglyMeasurable
    have hφ_meas : AEStronglyMeasurable φ μ := hφ_mem.aestronglyMeasurable
    have hφ'_meas : AEStronglyMeasurable φ' μ :=
      hcoeff_meas.mul hφ_meas
    have hcoeff_nonneg : ∀ x, 0 ≤ coeff x := by
      intro x
      by_cases hle : (N : ℝ) / g x ≤ 1
      · have hdiv_nonneg : 0 ≤ (N : ℝ) / g x :=
          div_nonneg (show 0 ≤ (N : ℝ) from by exact_mod_cast (Nat.zero_le N))
            (hg_nonneg x)
        simp [coeff, hle, hdiv_nonneg]
      · have hge : 1 ≤ (N : ℝ) / g x := le_of_not_ge hle
        simp [coeff, hge]
    have hcoeff_le_one : ∀ x, coeff x ≤ 1 := by
      intro x; exact min_le_left _ _
    have hcoeff_abs_le_one : ∀ x, |coeff x| ≤ 1 := by
      intro x
      have hnonneg := hcoeff_nonneg x
      have := hcoeff_le_one x
      simpa [abs_of_nonneg hnonneg]
    have hφ'_le : ∀ x, ‖φ' x‖ ≤ ‖φ x‖ := by
      intro x
      have hnonneg := hcoeff_nonneg x
      have hbound := hcoeff_abs_le_one x
      have hprod :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg (φ x))
      have : |coeff x| * |φ x| ≤ |φ x| := by
        simpa using hprod
      simpa [φ', Real.norm_eq_abs, abs_mul] using this
    have hφ'_mem : MemLp φ' q μ :=
      MemLp.mono hφ_mem hφ'_meas
        (Filter.Eventually.of_forall hφ'_le)
    have h_eLp_le : eLpNorm φ' q μ ≤ eLpNorm φ q μ :=
      eLpNorm_mono fun x => hφ'_le x
    have hφ'_norm : (eLpNorm φ' q μ).toReal ≤ 1 := by
      have h_lt_top : eLpNorm φ q μ < ∞ := hφ_mem.2
      have hφ'_lt_top : eLpNorm φ' q μ < ∞ := hφ'_mem.2
      have h_toReal_le :=
        (ENNReal.toReal_le_toReal hφ'_lt_top.ne h_lt_top.ne).mpr h_eLp_le
      exact h_toReal_le.trans hφ_norm
    have hcoeff_mul : ∀ x, g x * coeff x = trunc N x := by
      intro x
      dsimp [coeff, trunc]
      by_cases hg0 : g x = 0
      · simp [hg0]
      · have hg_pos : 0 < g x := lt_of_le_of_ne (hg_nonneg x)
          (by simpa [eq_comm] using hg0)
        by_cases hle : g x ≤ (N : ℝ)
        · have hmin : min (1 : ℝ) ((N : ℝ) / g x) = 1 := by
            have hge : 1 ≤ (N : ℝ) / g x := (one_le_div hg_pos).2 hle
            exact min_eq_left hge
          have htrunc : min (g x) (N : ℝ) = g x := min_eq_left hle
          simp [hg0, hmin, htrunc]
        · have hgt : (N : ℝ) < g x := lt_of_not_ge hle
          have hle' : (N : ℝ) / g x ≤ 1 := (div_le_one hg_pos).2 hgt.le
          have hmin : min (1 : ℝ) ((N : ℝ) / g x) = (N : ℝ) / g x :=
            min_eq_right hle'
          have htrunc : min (g x) (N : ℝ) = (N : ℝ) :=
            min_eq_right hgt.le
          have hg_ne : g x ≠ 0 := hg0
          have hcalc : g x * ((N : ℝ) / g x) = (N : ℝ) := by
            calc
              g x * ((N : ℝ) / g x)
                  = g x * ((N : ℝ) * (g x)⁻¹) := by simp [div_eq_mul_inv]
              _ = (g x * (g x)⁻¹) * (N : ℝ) := by ac_rfl
              _ = 1 * (N : ℝ) := by simp [hg_ne]
              _ = (N : ℝ) := by simp
          simpa [hmin, htrunc] using hcalc
    have hφ'_integrand_eq :
        (fun x => g x * φ' x) = fun x => trunc N x * φ x := by
      funext x
      simp [φ', mul_comm, mul_left_comm, mul_assoc, hcoeff_mul]
    have hφ'_integrable : Integrable (fun x => g x * φ' x) μ := by
      simpa [hφ'_integrand_eq] using hφ_int
    have h_integral_eq :
        ∫ x, g x * φ' x ∂μ = ∫ x, trunc N x * φ x ∂μ := by
      simp [hφ'_integrand_eq]
    have h_bound :=
      h_pairing_bound (φ := φ') hφ'_mem hφ'_norm hφ'_integrable
    have h_abs_eq : |∫ x, trunc N x * φ x ∂μ| = |∫ x, g x * φ' x ∂μ| := by
      simp [h_integral_eq]
    simpa [φ', h_abs_eq] using h_bound
  have h_trunc_norm_le : ∀ N : ℕ,
      (eLpNorm (trunc N) p μ).toReal ≤ B := by
    intro N
    refine
      lp_duality_norm_le_of_pairing_bound (μ := μ)
        (p := p) (q := q) hp hq_gt_one hpq (f := trunc N) (htrunc_mem N) ?_
    intro φ hφ_mem hφ_norm hφ_int
    simpa using h_trunc_pairing_bound N φ hφ_mem hφ_norm hφ_int
  -- Having obtained uniform bounds on the `L^p` norms of the truncations, it remains
  -- to pass to the limit and deduce the desired finiteness for `g`.
  have h_trunc_eLp_le :
      ∀ N : ℕ, eLpNorm (trunc N) p μ ≤ ENNReal.ofReal B := by
    intro N
    have h_fin : eLpNorm (trunc N) p μ ≠ ∞ := (htrunc_mem N).2.ne
    have hB_fin : ENNReal.ofReal B ≠ ∞ := by simp
    refine (ENNReal.toReal_le_toReal h_fin hB_fin).1 ?_
    simpa [ENNReal.toReal_ofReal hB_nonneg] using h_trunc_norm_le N
  have h_goal : eLpNorm g p μ ≤ ENNReal.ofReal B := by
    classical
    -- Choose a measurable non-negative representative of `g`.
    set gTilde := hg_meas.aemeasurable.mk g with hgTilde_def
    set g0 : α → ℝ := fun x => max (gTilde x) 0 with hg0_def
    have hg_ae' : g =ᵐ[μ] gTilde := hg_meas.aemeasurable.ae_eq_mk
    have hg0_ae : g =ᵐ[μ] g0 :=
      hg_ae'.mono fun x hx => by
        have hx_nonneg : 0 ≤ g x := hg_nonneg x
        have hx_nonneg' : 0 ≤ gTilde x := by simpa [hx] using hx_nonneg
        have hmax : max (g x) 0 = g x := by simpa [max_eq_left] using hx_nonneg
        simp [g0, hg0_def, hx, hmax, hx_nonneg']
    have h_eLp_congr : eLpNorm g p μ = eLpNorm g0 p μ :=
      eLpNorm_congr_ae hg0_ae
    have hgTilde_meas : Measurable gTilde := hg_meas.aemeasurable.measurable_mk
    have hg0_meas : Measurable g0 := hgTilde_meas.max measurable_const
    have hg0_nonneg : ∀ x, 0 ≤ g0 x := by
      intro x; exact le_max_right _ _
    -- Truncate the measurable representative and compare with the original truncations.
    let trunc0 : ℕ → α → ℝ := fun N x => min (g0 x) (N : ℝ)
    have h_trunc_ae : ∀ N, trunc N =ᵐ[μ] trunc0 N := by
      intro N
      exact hg0_ae.mono (by intro x hx; simp [trunc, trunc0, hx])
    have h_trunc0_meas : ∀ N, Measurable (trunc0 N) := by
      intro N; exact (hg0_meas.min measurable_const)
    have h_trunc0_nonneg : ∀ N x, 0 ≤ trunc0 N x := by
      intro N x; dsimp [trunc0]
      have hN_nonneg : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      exact le_min (hg0_nonneg x) hN_nonneg
    have h_trunc0_le : ∀ N x, trunc0 N x ≤ g0 x := by
      intro N x; dsimp [trunc0]; exact min_le_left _ _
    have h_trunc0_eLp_le : ∀ N : ℕ,
        eLpNorm (trunc0 N) p μ ≤ ENNReal.ofReal B := by
      intro N
      have h_bound := h_trunc_eLp_le N
      have h_eq :
          eLpNorm (trunc N) p μ = eLpNorm (trunc0 N) p μ :=
        eLpNorm_congr_ae (μ := μ) (p := p)
          (f := trunc N) (g := trunc0 N) (h_trunc_ae N)
      simpa [h_eq] using h_bound
    -- Work with the `L^p` densities of the truncations.
    set F0 : ℕ → α → ℝ≥0∞ := fun N x => ‖trunc0 N x‖ₑ ^ pr
      with hF0_def
    have hF0_meas : ∀ N, Measurable (F0 N) := by
      intro N
      have h_abs : Measurable fun x => |trunc0 N x| :=
        ((_root_.continuous_abs : Continuous fun t : ℝ => |t|).measurable.comp
          (h_trunc0_meas N))
      have h_enorm : Measurable fun x => ‖trunc0 N x‖ₑ := by
        simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using
          (ENNReal.measurable_ofReal.comp h_abs)
      have h_pow :
          Measurable fun x => ‖trunc0 N x‖ₑ ^ pr :=
        (ENNReal.continuous_rpow_const (y := pr)).measurable.comp h_enorm
      simpa [F0, hF0_def] using h_pow
    have hF0_mono : Monotone F0 := by
      intro m n hmn x
      have h_trunc_le : trunc0 m x ≤ trunc0 n x := by
        dsimp [trunc0]
        exact min_le_min le_rfl (by exact_mod_cast hmn)
      have h_nonneg_m : 0 ≤ trunc0 m x := h_trunc0_nonneg m x
      have h_nonneg_n : 0 ≤ trunc0 n x := h_trunc0_nonneg n x
      have : ENNReal.ofReal (trunc0 m x) ≤ ENNReal.ofReal (trunc0 n x) :=
        ENNReal.ofReal_le_ofReal h_trunc_le
      have h_le_enorm : ‖trunc0 m x‖ₑ ≤ ‖trunc0 n x‖ₑ := by
        simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs,
          abs_of_nonneg h_nonneg_m, abs_of_nonneg h_nonneg_n]
          using this
      exact ENNReal.rpow_le_rpow h_le_enorm hp_toReal_pos.le
    have hF0_iSup :
        (fun x => ‖g0 x‖ₑ ^ pr) = fun x => ⨆ N, F0 N x := by
      funext x
      have h_le : ∀ N, F0 N x ≤ ‖g0 x‖ₑ ^ pr := by
        intro N
        have h_trunc_le' : trunc0 N x ≤ g0 x := h_trunc0_le N x
        have h_nonneg_N : 0 ≤ trunc0 N x := h_trunc0_nonneg N x
        have h_nonneg_g0 : 0 ≤ g0 x := hg0_nonneg x
        have : ENNReal.ofReal (trunc0 N x) ≤ ENNReal.ofReal (g0 x) :=
          ENNReal.ofReal_le_ofReal h_trunc_le'
        have h_base : ‖trunc0 N x‖ₑ ≤ ‖g0 x‖ₑ := by
          simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs,
            abs_of_nonneg h_nonneg_N, abs_of_nonneg h_nonneg_g0]
            using this
        exact ENNReal.rpow_le_rpow h_base hp_toReal_pos.le
      apply le_antisymm
      · obtain ⟨N, hN⟩ := exists_nat_ge (g0 x)
        have h_min : min (g0 x) (N : ℝ) = g0 x := by
          exact min_eq_left (by exact_mod_cast hN)
        have h_trunc_eq : trunc0 N x = g0 x := by simp [trunc0, h_min]
        refine le_iSup_of_le N ?_
        have h_nonneg : 0 ≤ g0 x := hg0_nonneg x
        simp [F0, hF0_def, h_trunc_eq, Real.enorm_eq_ofReal_abs, Real.norm_eq_abs,
          abs_of_nonneg h_nonneg]
      · exact iSup_le h_le
    have h_lintegral_eq :
        ∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ = ⨆ N, ∫⁻ x, F0 N x ∂μ := by
      simpa [hF0_iSup] using
        MeasureTheory.lintegral_iSup (μ := μ) hF0_meas hF0_mono
    have h_int_eq :
        ∀ N : ℕ, ∫⁻ x, F0 N x ∂μ = (eLpNorm (trunc0 N) p μ) ^ pr := by
      intro N
      set A := ∫⁻ x, ‖trunc0 N x‖ₑ ^ pr ∂μ
      have h_eLp :=
        MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
          (μ := μ) (p := p) (f := trunc0 N)
          (hp_ne_zero := hp_ne_zero) (hp_ne_top := hp_ne_top)
      have h_pr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
      have h_mul : pr⁻¹ * pr = 1 := by
        simp [h_pr_ne_zero]
      have hA : eLpNorm (trunc0 N) p μ = A ^ (1 / pr) := by
        simpa [F0, hF0_def, A] using h_eLp
      have hA_inv : eLpNorm (trunc0 N) p μ = A ^ pr⁻¹ := by
        simpa [one_div] using hA
      have h_left : (A ^ pr⁻¹) ^ pr = A := by
        have h_rpow := (ENNReal.rpow_mul A pr⁻¹ pr).symm
        simpa [h_mul] using h_rpow
      have hA_pow : (eLpNorm (trunc0 N) p μ) ^ pr = A := by
        simpa [hA_inv] using h_left
      simpa [F0, hF0_def, A] using hA_pow.symm
    have h_int_le :
        ∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ ≤ (ENNReal.ofReal B) ^ pr := by
      calc
        ∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ
            = ⨆ N, ∫⁻ x, F0 N x ∂μ := h_lintegral_eq
        _ ≤ (ENNReal.ofReal B) ^ pr :=
          iSup_le fun N => by
            have h_le := ENNReal.rpow_le_rpow (h_trunc0_eLp_le N) hp_toReal_pos.le
            simpa [h_int_eq N] using h_le
    have h_bound_lt_top : (ENNReal.ofReal B) ^ pr < ∞ := by
      have : (ENNReal.ofReal B) < ∞ := by simp
      exact ENNReal.rpow_lt_top_of_nonneg hp_toReal_pos.le this.ne
    have h_int_lt_top :
        (∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ) < ∞ := lt_of_le_of_lt h_int_le h_bound_lt_top
    have h_eLp_repr :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        (μ := μ) (p := p) (f := g0)
        (hp_ne_zero := hp_ne_zero) (hp_ne_top := hp_ne_top)
    have h_eLp_value : eLpNorm g0 p μ =
        (∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ) ^ pr⁻¹ := by
      simpa [F0, hF0_def, one_div] using h_eLp_repr
    have h_inv_nonneg : 0 ≤ pr⁻¹ := by
      have h_pos : 0 < pr⁻¹ := by
        simpa [one_div] using inv_pos.mpr hp_toReal_pos
      exact h_pos.le
    have h_pow_le :=
      ENNReal.rpow_le_rpow h_int_le h_inv_nonneg
    have h_pow_eq :
        ((ENNReal.ofReal B) ^ pr) ^ pr⁻¹ = ENNReal.ofReal B := by
      have h_pr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
      have h_mul : pr * pr⁻¹ = 1 := by
        simp [h_pr_ne_zero]
      have h_rpow :=
        (ENNReal.rpow_mul (ENNReal.ofReal B) pr pr⁻¹).symm
      have h_rpow' :
          ((ENNReal.ofReal B) ^ pr) ^ pr⁻¹
            = (ENNReal.ofReal B) ^ 1 := by
        simpa [h_mul] using h_rpow
      simpa using h_rpow'
    have h_goal0 : eLpNorm g0 p μ ≤ ENNReal.ofReal B := by
      have h_base : (∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ) ^ pr⁻¹
          ≤ ((ENNReal.ofReal B) ^ pr) ^ pr⁻¹ := h_pow_le
      simpa [h_eLp_value, h_pow_eq] using h_base
    simpa [h_eLp_congr] using h_goal0
  have h_fin : eLpNorm g p μ < ∞ := lt_of_le_of_lt h_goal (by simp)
  simpa [g] using h_fin

/--
Auxiliary lemma preparing for Minkowski's integral inequality: under the standard measurability and
integrability assumptions on a kernel `F`, the function `x ↦ ‖∫ F x y ∂ν‖` belongs to `L^p(μ)`.
-/
lemma memLp_norm_integral
    {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    {F : α → β → E}
    (hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    MemLp (fun x => ‖∫ y, F x y ∂ν‖) p μ := by
  classical
  -- Basic measurability facts for the fibrewise integral and its norm.
  have h_integral_meas :
      AEStronglyMeasurable (fun x => ∫ y, F x y ∂ν) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := ν) (f := Function.uncurry F) hF_meas)
  have h_norm_meas :
      AEStronglyMeasurable (fun x => ‖∫ y, F x y ∂ν‖) μ :=
    h_integral_meas.norm
  -- Extract the information on fibrewise integrability provided by `hF_prod`.
  have h_prod_info :=
    (integrable_prod_iff (μ := μ) (ν := ν)
      (f := Function.uncurry F) hF_meas).mp hF_prod
  have hF_int_left :
      ∀ᵐ x ∂μ, Integrable (fun y => F x y) ν := by
    simpa [Function.uncurry] using h_prod_info.1
  have h_majorant_int :
      Integrable (fun x => ∫ y, ‖F x y‖ ∂ν) μ := by
    simpa [Function.uncurry] using h_prod_info.2
  -- Pointwise domination of the norm by the integral of fibrewise norms.
  have h_pointwise :
      (fun x => ‖∫ y, F x y ∂ν‖)
        ≤ᵐ[μ]
          fun x => ∫ y, ‖F x y‖ ∂ν := by
    refine hF_int_left.mono ?_
    intro x hx
    have hx_bound :=
      norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    simpa using hx_bound
  -- The pointwise domination yields integrability of the normed integral.
  have h_norm_integrable :
      Integrable (fun x => ‖∫ y, F x y ∂ν‖) μ := by
    refine Integrable.mono' h_majorant_int h_norm_meas ?_
    simpa using h_pointwise
  -- Work with the scalar helper `g`.
  set g : α → ℝ := fun x => ‖∫ y, F x y ∂ν‖
  have hg_meas : AEStronglyMeasurable g μ := h_norm_meas
  have hg_int : Integrable g μ := by
    simpa [g] using h_norm_integrable
  by_cases hp_eq_one : p = (1 : ℝ≥0∞)
  · subst hp_eq_one
    -- For `p = 1`, membership in `L¹` is equivalent to integrability.
    have hg_mem : MemLp g (1 : ℝ≥0∞) μ :=
      (memLp_one_iff_integrable : MemLp g (1 : ℝ≥0∞) μ ↔ Integrable g μ).2 hg_int
    simpa [g] using hg_mem
  -- For `p > 1`, the previous finiteness lemma applies directly.
  · have hp_ne_one : p ≠ (1 : ℝ≥0∞) := hp_eq_one
    have hp_one_lt : 1 < p :=
      lt_of_le_of_ne' hp (by simpa [eq_comm] using hp_ne_one)
    have hp_pos : (0 : ℝ≥0∞) < p :=
      lt_of_le_of_lt (by simp : (0 : ℝ≥0∞) ≤ 1) hp_one_lt
    have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
    have h_lt_top :=
      eLpNorm_norm_integral_lt_top (μ := μ) (ν := ν) (p := p)
        hp_one_lt hp_ne_top hF_meas hF_prod hF_memLp hF_norm
    have hg_mem : MemLp g p μ := ⟨hg_meas, by simpa [g] using h_lt_top⟩
    simpa [g] using hg_mem

end SchwartzDensityLp
