import Frourio.Analysis.HolderInequality.HolderInequality
import Frourio.Analysis.SchwartzDensityLp.MinkowskiIntegral
import Frourio.Analysis.SchwartzDensityLp.FubiniSection
import Frourio.Analysis.YoungInequality.YoungInequalityCore0
import Mathlib.Analysis.Convolution
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

section Auxiliary_Signatures

-- Pack three ENNReal r-powers of the same base (N+1) into a single exponent.
lemma ennreal_rpow_pack_three_eq (N : ℕ) (a b c t : ℝ) :
    (((N + 1 : ℝ≥0∞) ^ a) ^ t)
      * (((N + 1 : ℝ≥0∞) ^ b) ^ t)
      * (((N + 1 : ℝ≥0∞) ^ c) ^ t)
    = (N + 1 : ℝ≥0∞) ^ ((a + b + c) * t) := by
  classical
  set x : ℝ≥0∞ := (N + 1 : ℝ≥0∞)
  have hx0 : x ≠ 0 := by simp [x]
  have hxTop : x ≠ ∞ := by simp [x]
  calc
    ((x ^ a) ^ t) * ((x ^ b) ^ t) * ((x ^ c) ^ t)
        = (x ^ (a * t)) * (x ^ (b * t)) * (x ^ (c * t)) := by
              simp [ENNReal.rpow_mul]
    _ = ((x ^ (a * t)) * (x ^ (b * t))) * (x ^ (c * t)) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (x ^ ((a * t) + (b * t))) * (x ^ (c * t)) := by
              -- rewrite the first two factors using rpow_add, then reattach the third
              have h := (ENNReal.rpow_add (x := x) (y := a * t) (z := b * t) hx0 hxTop).symm
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                congrArg (fun z => z * (x ^ (c * t))) h
    _ = x ^ (((a * t) + (b * t)) + (c * t)) := by
              -- combine the remaining two factors via rpow_add
              have h :=
                (ENNReal.rpow_add (x := x)
                  (y := (a * t) + (b * t)) (z := (c * t)) hx0 hxTop).symm
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
    _ = x ^ (((a + b) * t) + (c * t)) := by
              ring_nf
    _ = x ^ (((a + b + c) * t)) := by
              ring_nf

-- Translate 1/p = 1/r + 1/s to toReal on the ENNReal side.
lemma ennreal_toReal_inv_add_of_split
    {p r s : ℝ≥0∞} (hr : r ≠ 0) (hs : s ≠ 0) (h_split : 1 / p = 1 / r + 1 / s) :
    (1 / p).toReal = (1 / r).toReal + (1 / s).toReal := by
  have hr_fin : (1 / r) ≠ ∞ := by simp [one_div, hr]
  have hs_fin : (1 / s) ≠ ∞ := by simp [one_div, hs]
  have h1 : (1 / p).toReal = (1 / r + 1 / s).toReal := by
    simpa using congrArg ENNReal.toReal h_split
  have h2 : (1 / r + 1 / s).toReal = (1 / r).toReal + (1 / s).toReal :=
    ENNReal.toReal_add hr_fin hs_fin
  exact h1.trans h2

-- Lower bound: 1 ≤ (N+1)^a for nonnegative exponents a.
lemma ennreal_one_le_rpow_nat_succ (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (1 : ℝ≥0∞) ≤ ((N + 1 : ℝ≥0∞) ^ a) := by
  have hbase : (1 : ℝ≥0∞) ≤ (N + 1 : ℝ≥0∞) := by
    have : (1 : ℕ) ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast this
  have h := ENNReal.rpow_le_rpow hbase ha
  simpa using h

-- Inflate by a ≥ 1 factor on the left.
lemma ennreal_le_mul_rpow_of_one_le (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (X : ℝ≥0∞) :
    X ≤ ((N + 1 : ℝ≥0∞) ^ a) * X := by
  have hbase : (1 : ℝ≥0∞) ≤ ((N + 1 : ℝ≥0∞) ^ a) :=
    ennreal_one_le_rpow_nat_succ N ha
  have h := mul_le_mul_left' hbase X
  simpa [one_mul, mul_comm] using h

-- Pointwise uniform bound implies limsup bound by the same constant.
lemma limsup_le_const_of_pointwise {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ N, u N ≤ c) :
    Filter.limsup u Filter.atTop ≤ c := by
  have hev : ∀ᶠ N in Filter.atTop, u N ≤ (fun _ : ℕ => c) N :=
    Filter.Eventually.of_forall h
  have h_le := Filter.limsup_le_limsup hev
  have h_const : Filter.limsup (fun _ : ℕ => c) Filter.atTop = c := by
    simp
  simpa [h_const] using h_le

end Auxiliary_Signatures

section ConvolutionAuxiliary

variable {G : Type*}
variable [MeasurableSpace G]
variable (μ : Measure G) [SFinite μ]

-- Pulling a finite ENNReal constant out of a limsup (left multiplication).
lemma limsup_const_mul_atTop
    (C : ℝ≥0∞) (u : ℕ → ℝ≥0∞) (hC_lt_top : C ≠ ∞) :
    Filter.limsup (fun n => C * u n) Filter.atTop
      = C * Filter.limsup u Filter.atTop := by
  classical
  -- Handle the degenerate constant case first.
  by_cases hC0 : C = 0
  · simp [hC0]
  -- From now on, 0 < C < ∞ in the ENNReal sense.
  have hC_ne_zero : C ≠ 0 := hC0
  -- Split on whether limsup u is infinite.
  by_cases hLtop : Filter.limsup u Filter.atTop = ∞
  · -- If limsup u = ∞ and C ≠ 0, then limsup (C*u) = ∞ as well.
    have h_inf_case :
        Filter.limsup (fun n => C * u n) Filter.atTop = ∞ := by
      -- Show that for any finite K, frequently K ≤ C * u n; hence limsup ≥ K; conclude = ∞.
      -- Fix an arbitrary finite K.
      have h_bdd :
          Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n => C * u n) := by
        -- Trivial boundedness by ⊤ for ENNReal-valued functions.
        refine Filter.isBoundedUnder_of ?_
        refine ⟨(∞ : ℝ≥0∞), ?_⟩
        intro n; simp
      -- For every finite K, we have K ≤ limsup(C*u).
      have h_all_finite :
          ∀ K : ℝ≥0∞, K ≠ ⊤ →
            K ≤ Filter.limsup (fun n => C * u n) Filter.atTop := by
        intro K hKfin
        -- Choose M with C * M = K. Take M = C⁻¹ * K (finite since K < ∞ and C ≠ 0).
        have hKM : C * (C⁻¹ * K) = K := by
          -- Rearrange using associativity; avoid 0·∞ issues thanks to hC_ne_zero and hC_lt_top, hK.
          have hK_ne_top : K ≠ ⊤ := hKfin
          have hC_inv_ne_top : C⁻¹ ≠ ∞ := by
            -- inv ≠ ∞ for nonzero finite ENNReal
            simp [ENNReal.inv_eq_top, hC_ne_zero]
          -- Use (C * C⁻¹) * K = 1 * K = K
          have hCCinv : C * C⁻¹ = 1 := by
            simpa [mul_comm] using ENNReal.mul_inv_cancel hC_ne_zero hC_lt_top
          calc
            C * (C⁻¹ * K) = (C * C⁻¹) * K := by
              simp [mul_comm, mul_left_comm, mul_assoc]
            _ = (1 : ℝ≥0∞) * K := by simp [hCCinv]
            _ = K := by simp
        -- From limsup u = ∞, for any finite M we have frequently M ≤ u n.
        have h_freq_M : ∀ {M : ℝ≥0∞}, M ≠ ∞ → (∃ᶠ n in Filter.atTop, M ≤ u n) := by
          intro M hMfin
          -- If not frequent, then eventually u n < M, hence eventually u n ≤ M, forcing limsup ≤ M.
          -- This contradicts limsup u = ∞.
          by_contra hnot
          -- `¬(∃ᶠ n, M ≤ u n)` ⇒ `∀ᶠ n, ¬ (M ≤ u n)` by definition of `Frequently`.
          have hev_not : ∀ᶠ n in Filter.atTop, ¬ (M ≤ u n) := by
            exact (Filter.not_frequently).1 hnot
          have hev_lt : ∀ᶠ n in Filter.atTop, u n < M := by
            exact hev_not.mono (fun _ h => by
              -- `¬ (M ≤ u n)` is equivalent to `u n < M` in a linear order like ENNReal.
              exact lt_of_not_ge h)
          have hev_le : ∀ᶠ n in Filter.atTop, u n ≤ M := hev_lt.mono (fun _ h => le_of_lt h)
          have hlim_le : Filter.limsup u Filter.atTop ≤ M :=
            Filter.limsup_le_of_le (h := hev_le)
          -- Contradict limsup u = ∞ and M < ∞.
          have : (∞ : ℝ≥0∞) ≤ M := by simpa [hLtop] using hlim_le
          have hM_lt_top : M < ⊤ := lt_of_le_of_ne le_top hMfin
          exact (not_le_of_gt hM_lt_top) this
        -- Apply `le_limsup_of_frequently_le` to `C*M = K`.
        have hfreq : ∃ᶠ n in Filter.atTop, K ≤ C * u n := by
          have hMfin : (C⁻¹ * K) ≠ ∞ := by
            -- product of finite terms is finite
            have h1 : C⁻¹ ≠ ∞ := by
              have hCfin : C < ∞ := lt_of_le_of_ne le_top hC_lt_top
              have : (0 : ℝ≥0∞) < C := by
                exact (bot_lt_iff_ne_bot).2 (by simpa [_root_.bot_eq_zero] using hC_ne_zero)
              -- From `C ≠ 0`, `inv` is finite; direct simp
              simp [ENNReal.inv_eq_top, hC_ne_zero]
            have h2 : K ≠ ⊤ := hKfin
            exact ENNReal.mul_ne_top h1 h2
          -- Get frequent inequality for M := C⁻¹ * K and multiply by C on the left.
          have hfreqM := h_freq_M (M := C⁻¹ * K) hMfin
          -- Turn `M ≤ u n` into `K ≤ C * u n` using monotonicity and `hKM`.
          exact hfreqM.mono (fun n hn => by
            -- K = C*M ≤ C*u n
            calc K = C * (C⁻¹ * K) := hKM.symm
                 _ ≤ C * u n := mul_le_mul_left' hn C)
        -- Now use the general lower bound lemma for limsup.
        exact Filter.le_limsup_of_frequently_le hfreq h_bdd
      -- Conclude `limsup (C*u) = ⊤` by contradiction: otherwise pick `K = s + 1`.
      -- Set `s := limsup (C*u)`.
      set s := Filter.limsup (fun n => C * u n) Filter.atTop with hs
      have hs_top : s = ⊤ := by
        by_contra hsfin
        have hs_ne_top : s ≠ ⊤ := hsfin
        -- `s + 1` is still finite, hence covered by `h_all_finite`.
        have hKfin : s + 1 ≠ ⊤ := by
          exact ENNReal.add_ne_top.mpr ⟨hs_ne_top, by simp⟩
        have hK_le_s : s + 1 ≤ s := by
          -- Use the finite-K bound with K := s + 1.
          simpa [hs] using h_all_finite (K := s + 1) hKfin
        -- But `s < s + 1`, contradiction with `s + 1 ≤ s`.
        have : s < s + 1 := by
          -- For ENNReal, s < s + 1 when s ≠ ⊤ and 1 > 0
          calc s = s + 0 := by simp
               _ < s + 1 := by
                 apply ENNReal.add_lt_add_left
                 · exact hs_ne_top
                 · simp
        exact (not_lt_of_ge hK_le_s) this
      -- Substitute back `s` to get the desired equality.
      simpa [hs] using hs_top
    -- With the infinite-value case handled, simplify the RHS.
    simp [hLtop, h_inf_case, hC_ne_zero, hC_lt_top]
  · -- Finite limsup case: set L := limsup u < ∞ and show equality by two inequalities.
    have hLfin : Filter.limsup u Filter.atTop ≠ ∞ := hLtop
    set L := Filter.limsup u Filter.atTop with hLdef
    have hL_lt_top : L < ∞ := lt_of_le_of_ne le_top hLfin
    -- Upper bound: limsup (C*u) ≤ C * L, via an order-density argument.
    have h_upper :
        Filter.limsup (fun n => C * u n) Filter.atTop ≤ C * L := by
      -- It suffices to prove: for all D > C*L, limsup(C*u) ≤ D.
      apply le_of_forall_gt_imp_ge_of_dense
      intro D hCL_D
      -- Trivial if D = ∞.
      by_cases hDtop : D = ∞
      · simp [hDtop]
      -- Use B = C⁻¹ * D, so that C*B = D and B > L by monotonicity.
      have hC_inv_ne_top : C⁻¹ ≠ ∞ := by
        simp [ENNReal.inv_eq_top, hC_ne_zero]
      have hCCinv : C * C⁻¹ = 1 := by
        simpa [mul_comm] using ENNReal.mul_inv_cancel hC_ne_zero hC_lt_top
      set B : ℝ≥0∞ := C⁻¹ * D with hBdef
      have hL_lt_B : L < B := by
        -- Multiply strict inequality on the left by C⁻¹ (strictly monotone since C ≠ 0, C < ∞).
        have hCinv_pos : 0 < C⁻¹ := by
          simp [ENNReal.inv_pos, hC_ne_zero, hC_lt_top]
        have hCinv_ne_top : C⁻¹ ≠ ⊤ := by
          simp [ENNReal.inv_eq_top, hC_ne_zero]
        -- First show C * L < D, then multiply both sides by C⁻¹
        have : C⁻¹ * (C * L) < C⁻¹ * D := by
          rw [ENNReal.mul_lt_mul_left hCinv_pos.ne' hCinv_ne_top]
          exact hCL_D
        -- Simplify C⁻¹*(C*L) to L using associativity and C*C⁻¹ = 1
        have hsimp : C⁻¹ * (C * L) = L := by
          calc C⁻¹ * (C * L) = (C⁻¹ * C) * L := by rw [mul_assoc]
               _ = (C * C⁻¹) * L := by rw [mul_comm C⁻¹ C]
               _ = 1 * L := by rw [hCCinv]
               _ = L := by simp
        -- Therefore L < C⁻¹ * D = B
        calc L = C⁻¹ * (C * L) := hsimp.symm
             _ < C⁻¹ * D := this
             _ = B := by simp [hBdef]
      -- Since limsup u = L < B, we have eventually u n < B, hence eventually C*u n ≤ C*B = D.
      have hlim_lt : Filter.limsup u Filter.atTop < B := by
        simpa [hLdef] using hL_lt_B
      have h_eventually_lt : ∀ᶠ n in Filter.atTop, u n < B :=
        Filter.eventually_lt_of_limsup_lt hlim_lt
      have h_eventually_le : ∀ᶠ n in Filter.atTop, u n ≤ B :=
        h_eventually_lt.mono (fun _ h => le_of_lt h)
      have hCB_eq : C * B = D := by
        calc C * B = C * (C⁻¹ * D) := by rw [hBdef]
             _ = (C * C⁻¹) * D := by rw [mul_assoc]
             _ = 1 * D := by rw [hCCinv]
             _ = D := by simp
      have h_eventually_leD : ∀ᶠ n in Filter.atTop, C * u n ≤ D := by
        have h_ev_le_CB : ∀ᶠ n in Filter.atTop, C * u n ≤ C * B :=
          h_eventually_le.mono (fun _ h => mul_le_mul_left' h C)
        exact h_ev_le_CB.mono (fun _ h => by simpa [hCB_eq] using h)
      exact Filter.limsup_le_of_le (h := h_eventually_leD)
    -- Lower bound: for any B < L, frequently B ≤ u n, then push through multiplication.
    have h_bdd :
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n => C * u n) := by
      refine Filter.isBoundedUnder_of ?_
      exact ⟨(∞ : ℝ≥0∞), by intro n; simp⟩
    have h_lower : C * L ≤ Filter.limsup (fun n => C * u n) Filter.atTop := by
      -- It suffices: for all B < L, we have C*B ≤ limsup(C*u). Then take `iSup` over B→L.
      -- We realize this via `le_limsup_of_frequently_le`.
      -- Fix ε-approximation B of L from below; use frequent events `B ≤ u n`.
      -- For any finite B with B < L
      have h_main :
          ∀ ⦃B : ℝ≥0∞⦄, B < L → C * B ≤ Filter.limsup (fun n => C * u n) Filter.atTop := by
        intro B hBlt
        -- As before, we get frequent `B ≤ u n` from `B < L = limsup u`.
        have hfreqB : ∃ᶠ n in Filter.atTop, B ≤ u n := by
          -- Otherwise, eventually `u n < B`, forcing limsup u ≤ B < L.
          by_contra hnot
          have hev_not : ∀ᶠ n in Filter.atTop, ¬ (B ≤ u n) := (Filter.not_frequently).1 hnot
          have hev_lt : ∀ᶠ n in Filter.atTop, u n < B := hev_not.mono (fun _ h => lt_of_not_ge h)
          have hev_le : ∀ᶠ n in Filter.atTop, u n ≤ B := hev_lt.mono (fun _ h => le_of_lt h)
          have : Filter.limsup u Filter.atTop ≤ B := Filter.limsup_le_of_le (h := hev_le)
          have : L ≤ B := by simpa [hLdef] using this
          exact (not_le_of_gt hBlt) this
        -- Multiply the frequent inequality by C on the left.
        have hfreqCB : ∃ᶠ n in Filter.atTop, C * B ≤ C * u n :=
          hfreqB.mono (fun n hn => by exact mul_le_mul_left' hn C)
        -- Lower-bound limsup via frequent ≤.
        exact Filter.le_limsup_of_frequently_le hfreqCB h_bdd
      apply le_of_forall_lt_imp_le_of_dense
      intro D hDlt_CL
      -- If D = ∞ this is trivial (but cannot happen since D < C*L < ∞).
      by_cases hDtop : D = ∞
      · -- D = ∞ but D < C*L, contradiction
        exfalso
        rw [hDtop] at hDlt_CL
        -- ∞ < C*L is impossible
        exact not_top_lt hDlt_CL
      -- Define B and show B < L by strict monotonicity of left-multiplication by C⁻¹.
      have hCCinv : C * C⁻¹ = 1 := by
        simpa [mul_comm] using ENNReal.mul_inv_cancel hC_ne_zero hC_lt_top
      -- Use the same approach as before for multiplication
      have hCinv_pos : 0 < C⁻¹ := by
        simp [ENNReal.inv_pos, hC_ne_zero, hC_lt_top]
      have hCinv_ne_top : C⁻¹ ≠ ⊤ := by
        simp [ENNReal.inv_eq_top, hC_ne_zero]
      have hB_lt_L : C⁻¹ * D < L := by
        -- From D < C*L, multiply both sides by C⁻¹
        have : C⁻¹ * D < C⁻¹ * (C * L) := by
          rw [ENNReal.mul_lt_mul_left hCinv_pos.ne' hCinv_ne_top]
          exact hDlt_CL
        -- Simplify C⁻¹*(C*L) to L
        have hsimp : C⁻¹ * (C * L) = L := by
          calc C⁻¹ * (C * L) = (C⁻¹ * C) * L := by rw [mul_assoc]
               _ = (C * C⁻¹) * L := by rw [mul_comm C⁻¹ C]
               _ = 1 * L := by rw [hCCinv]
               _ = L := by simp
        rw [hsimp] at this
        exact this
      -- Apply `h_main` with B := C⁻¹*D and compute C*B = D.
      have h_le : C * (C⁻¹ * D) ≤ Filter.limsup (fun n => C * u n) Filter.atTop :=
        h_main hB_lt_L
      -- Simplify C*(C⁻¹*D) = D
      have hsimp : C * (C⁻¹ * D) = D := by
        calc C * (C⁻¹ * D) = (C * C⁻¹) * D := by rw [mul_assoc]
             _ = 1 * D := by rw [hCCinv]
             _ = D := by simp
      rw [hsimp] at h_le
      exact h_le
    -- Combine the two inequalities.
    exact le_antisymm h_upper h_lower

-- Pulling a finite ENNReal constant out of a limsup (right multiplication).
lemma limsup_mul_const_atTop
    (u : ℕ → ℝ≥0∞) (C : ℝ≥0∞) (hC_lt_top : C ≠ ∞) :
    Filter.limsup (fun n => u n * C) Filter.atTop
      = Filter.limsup u Filter.atTop * C := by
  classical
  by_cases hC0 : C = 0
  · simp [hC0]
  -- Reduce to the left-multiplication lemma via commutativity of `*`.
  have h := limsup_const_mul_atTop C u hC_lt_top
  simpa [mul_comm] using h

-- Limsup of the power sequence (N+1)^a with positive real exponent is ∞.
lemma limsup_rpow_nat_atTop_eq_top
    {a : ℝ} (ha : 0 < a) :
    Filter.limsup (fun n : ℕ => ((n + 1 : ℝ≥0∞) ^ a)) Filter.atTop = ∞ := by
  classical
  -- Define the sequence f n := ((n+1) : ℝ≥0∞)^a.
  let f : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℝ≥0∞) ^ a)
  -- Basic boundedness is trivial in ENNReal (by ⊤), used for limsup lower bound lemma.
  have h_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop f := by
    refine Filter.isBoundedUnder_of ?_
    exact ⟨(∞ : ℝ≥0∞), by intro n; simp [f]⟩
  -- For any finite K, eventually K ≤ f n.
  have h_all_finite :
      ∀ K : ℝ≥0∞, K ≠ ∞ → ∀ᶠ n in Filter.atTop, K ≤ f n := by
    intro K hKfin
    -- Reduce to a real inequality via `ofReal`.
    -- Choose a positive threshold T := (K.toReal + 1)^(1/a)
    have ha_pos : 0 ≤ a := le_of_lt ha
    have hα_pos : 0 < 1 / a := by have : 0 < a := ha; simpa [one_div] using inv_pos.mpr this
    have hα_nonneg : 0 ≤ 1 / a := le_of_lt hα_pos
    let T : ℝ := (K.toReal + 1) ^ (1 / a)
    -- Pick N with T ≤ N (Archimedean property), so n ≥ N ⇒ (n : ℝ) ≥ T ⇒ (n+1 : ℝ) ≥ T.
    obtain ⟨N, hN⟩ := exists_nat_ge T
    have h_ev_ge : ∀ᶠ n : ℕ in Filter.atTop, ((n : ℝ) + 1 : ℝ) ≥ T := by
      apply Filter.eventually_of_mem (Filter.eventually_ge_atTop N)
      intro n hn
      have hn' : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
      have : ((n : ℝ) + 1 : ℝ) ≥ (N : ℝ) := by linarith
      have hNreal : (N : ℝ) ≥ T := hN
      exact le_trans hNreal this
    -- Monotonicity of rpow on ℝ for nonnegative base and nonnegative exponent yields
    -- (n+1)^a ≥ T^a = (K.toReal + 1).
    have h_ev_real : ∀ᶠ n : ℕ in Filter.atTop, ((n : ℝ) + 1 : ℝ) ^ a ≥ (K.toReal + 1) := by
      -- First, show 0 ≤ (n+1 : ℝ) and 0 ≤ T to apply `Real.rpow_le_rpow`.
      have hT_nonneg : 0 ≤ T := by
        -- K.toReal + 1 ≥ 0, so its rpow with nonnegative exponent is nonnegative.
        have hbase_pos : 0 ≤ K.toReal + 1 := by
          have : 0 ≤ K.toReal := ENNReal.toReal_nonneg
          linarith
        exact Real.rpow_nonneg hbase_pos _
      refine h_ev_ge.mono (fun n hn_ge => ?_)
      -- Apply rpow monotonicity and compute T^a.
      have hbase_nonneg : 0 ≤ ((n : ℝ) + 1 : ℝ) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hmono := Real.rpow_le_rpow hT_nonneg hn_ge ha_pos
      -- T^a = (K.toReal + 1)^( (1/a) * a ) = K.toReal + 1
      have hTpow : T ^ a = (K.toReal + 1) := by
        have hbase_nonneg' : 0 ≤ K.toReal + 1 := by
          have : 0 ≤ K.toReal := ENNReal.toReal_nonneg
          linarith
        simp only [T]
        rw [← Real.rpow_mul hbase_nonneg']
        have : (1 / a) * a = 1 := by field_simp
        rw [this, Real.rpow_one]
      -- Combine
      have : ((n : ℝ) + 1 : ℝ) ^ a ≥ T ^ a := hmono
      simpa [hTpow]
        using this
    -- Convert the real inequality to ENNReal with `ofReal`, and rewrite f n.
    have h_ev_ennreal : ∀ᶠ n in Filter.atTop, K ≤ f n := by
      -- `K = ofReal K.toReal` since K is finite.
      have hK_eq : ENNReal.ofReal K.toReal = K := ENNReal.ofReal_toReal hKfin
      refine h_ev_real.mono (fun n hn => ?_)
      -- Use monotonicity of `ofReal` and the identity `(n+1:ℝ≥0∞)^a = ofReal ((n+1:ℝ)^a)`.
      have : ENNReal.ofReal (K.toReal + 1) ≤ ENNReal.ofReal ((n + 1 : ℝ) ^ a) := by
        exact ENNReal.ofReal_le_ofReal hn
      have hK_le_ofReal : ENNReal.ofReal K.toReal ≤ ENNReal.ofReal (K.toReal + 1) := by
        exact ENNReal.ofReal_le_ofReal (by linarith)
      have hK_le : ENNReal.ofReal K.toReal ≤ ENNReal.ofReal ((n + 1 : ℝ) ^ a) :=
        le_trans hK_le_ofReal this
      -- Rewrite RHS into rpow form and LHS into K.
      have hpow_eq :
          ENNReal.ofReal ((n + 1 : ℝ) ^ a) = ((n + 1 : ℝ≥0∞) ^ a) := by
        have h_cast : (n + 1 : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1 : ℝ) := by
          norm_cast
        have hnneg : 0 ≤ ((n : ℝ) + 1 : ℝ) := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        simp only [h_cast, ENNReal.ofReal_rpow_of_nonneg hnneg ha_pos]
      simpa [hpow_eq, hK_eq, f]
        using hK_le
    exact h_ev_ennreal
  -- With the eventual lower bounds for all finite K, conclude limsup f = ⊤ by contradiction.
  -- Set s := limsup f and show it cannot be finite.
  set s := Filter.limsup f Filter.atTop with hs
  have hs_top : s = ⊤ := by
    by_contra hsfin
    have hs_ne_top : s ≠ ⊤ := hsfin
    -- Apply the finite-K bound with K := s + 1.
    have hKfin : s + 1 ≠ ⊤ := by exact ENNReal.add_ne_top.mpr ⟨hs_ne_top, by simp⟩
    have h_le : ∀ᶠ n in Filter.atTop, s + 1 ≤ f n := h_all_finite (K := s + 1) hKfin
    have h_bdd' : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop f := h_bdd
    have hfreq : ∃ᶠ n in Filter.atTop, s + 1 ≤ f n := h_le.frequently
    have h_le_limsup : s + 1 ≤ s := by
      -- Since s = limsup f, rewrite and apply the general lemma.
      have : s ≤ Filter.limsup f Filter.atTop := by simp [hs]
      -- Actually, use `le_limsup_of_frequently_le` directly.
      exact Filter.le_limsup_of_frequently_le hfreq h_bdd'
    -- But `s < s + 1` for ENNReal, contradiction.
    have : s < s + 1 := by
      have h_one_pos : (0 : ℝ≥0∞) < 1 := by norm_num
      calc s = s + 0 := by simp
           _ < s + 1 := ENNReal.add_lt_add_left (by simp [hs_ne_top]) h_one_pos
    exact (not_lt_of_ge h_le_limsup) this
  simpa [hs] using hs_top

lemma hpartial_tendsto_of_integrability_all
    {G : Type*} [MeasurableSpace G] [NormedAddCommGroup G]
    (μ : Measure G) [SFinite μ]
    (f g : G → ℂ)
    (x : G)
    (hx : Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ) :
    Tendsto (fun N => ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂
      (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k))
      atTop (𝓝 (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) := by
  classical
  set hxFun : G → ℝ := fun y => ‖f (x - y)‖ * ‖g y‖ with hxFun_def
  have hxμ_int : Integrable hxFun μ := hx
  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ with hμn_def
  have hμ_sum : Measure.sum μn = μ := MeasureTheory.sum_sfiniteSeq μ
  set μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k with hμpartial_def
  have hx_partial_int :
      ∀ N, Integrable hxFun (μpartial N) := by
    intro N
    refine hxμ_int.of_measure_le_smul (μ := μ) (μ' := μpartial N)
        (c := (N + 1 : ℝ≥0∞)) (by simp) ?_
    exact sfiniteSeq_partial_le_smul (μ := μ) N
  have hx_piece_int :
      ∀ n, Integrable hxFun (μn n) := by
    intro n
    have h_le : μn n ≤ μ := MeasureTheory.sfiniteSeq_le (μ := μ) n
    have h_le_smul : μn n ≤ (1 : ℝ≥0∞) • μ := by simp [h_le]
    refine hxμ_int.of_measure_le_smul (μ := μ) (μ' := μn n)
        (c := (1 : ℝ≥0∞)) (by simp) h_le_smul
  have hμpartial_succ :
      ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1) := by
    intro N
    classical
    simp [μpartial, Nat.succ_eq_add_one, Finset.range_succ, add_comm, add_left_comm, add_assoc]
  have hμpartial_zero : μpartial 0 = μn 0 := by
    classical
    simp [μpartial]
  have hx_Hpartial_succ :
      ∀ N,
        ∫ y, hxFun y ∂ μpartial (N + 1) =
          ∫ y, hxFun y ∂ μpartial N + ∫ y, hxFun y ∂ μn (N + 1) := by
    intro N
    have hx_add :=
      MeasureTheory.integral_add_measure
        (μ := μpartial N) (ν := μn (N + 1))
        (f := hxFun)
        (hx_partial_int N)
        (hx_piece_int (N + 1))
    simpa [hμpartial_succ, Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc]
      using hx_add
  have hx_Hpartial_sum :
      ∀ N,
        ∫ y, hxFun y ∂ μpartial N =
          ∑ k ∈ Finset.range (N + 1),
            ∫ y, hxFun y ∂ μn k := by
    intro N
    induction' N with N hN
    · simp [μpartial, hμpartial_zero, Finset.range_one]
    · have hx_step := hx_Hpartial_succ N
      calc
        ∫ y, hxFun y ∂ μpartial (N + 1)
            = ∫ y, hxFun y ∂ μpartial N + ∫ y, hxFun y ∂ μn (N + 1) := hx_step
        _ = (∑ k ∈ Finset.range (N + 1), ∫ y, hxFun y ∂ μn k)
              + ∫ y, hxFun y ∂ μn (N + 1) := by simp [hN]
        _ = ∑ k ∈ Finset.range (N + 1 + 1), ∫ y, hxFun y ∂ μn k := by
              simp [Finset.sum_range_succ, Nat.succ_eq_add_one, add_comm,
                add_left_comm, add_assoc]
  have hx_hasSum :
      HasSum (fun n => ∫ y, hxFun y ∂ μn n)
        (∫ y, hxFun y ∂ μ) := by
    have hx_int_sum : Integrable hxFun (Measure.sum μn) := by
      simpa [hμ_sum] using hxμ_int
    have hx_hasSum_aux :=
      MeasureTheory.hasSum_integral_measure
        (μ := μn) (f := hxFun) (hf := hx_int_sum)
    simpa [hμ_sum] using hx_hasSum_aux
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
          fun N => ∫ y, hxFun y ∂ μpartial N :=
    Filter.Eventually.of_forall fun N => (hx_Hpartial_sum N).symm
  exact hx_tendsto.congr' hx_eventually

lemma inv_p_eq_inv_r_add_inv_conj
    (p q r : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 < q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞) :
    1 / p = 1 / r + 1 / ENNReal.ofReal (q.toReal / (q.toReal - 1)) := by
  classical
  -- First, rule out the endpoint q = ∞ using the given Young relation and hr_ne_top.
  have hq_ne_top : q ≠ ∞ := by
    intro hq_top
    have h_eq : 1 / p = 1 + 1 / r := by simpa [hq_top, add_comm] using hpqr
    -- From 1 ≤ p we get 1/p ≤ 1, hence 1 + 1/r ≤ 1, forcing 1/r = 0 and r = ∞.
    have h_inv_p_le_one : 1 / p ≤ (1 : ℝ≥0∞) := by
      simpa [one_div] using (ENNReal.inv_le_inv).2 hp
    have h_le_one : (1 : ℝ≥0∞) + r⁻¹ ≤ 1 := by simpa [h_eq, one_div]
      using h_inv_p_le_one
    have h_le_one' : (1 : ℝ≥0∞) + r⁻¹ ≤ (1 : ℝ≥0∞) + 0 := by simpa using h_le_one
    have h_r_inv_le_zero : r⁻¹ ≤ (0 : ℝ≥0∞) :=
      (ENNReal.add_le_add_iff_left (by simp)).1 h_le_one'
    have h_zero_le : (0 : ℝ≥0∞) ≤ r⁻¹ := bot_le
    have h_r_inv_zero : r⁻¹ = 0 := le_antisymm h_r_inv_le_zero h_zero_le
    have hr_top : r = ∞ := ENNReal.inv_eq_zero.1 h_r_inv_zero
    exact hr_ne_top hr_top
  have hq_lt_top : q < ∞ := lt_of_le_of_ne le_top hq_ne_top
  -- Conjugate exponent for q in the finite case: s₀ = ofReal (q.toReal / (q.toReal - 1)).
  obtain ⟨s₀, h_conj, hs₀⟩ :=
    conjugate_exponent_formula (p := q) (by exact hq) (by exact hq_lt_top)
  -- From conjugacy: 1/q + 1/s₀ = 1.
  have h_sum : 1 / q + 1 / s₀ = 1 := by
    rcases h_conj with h | h | h
    · rcases h with ⟨hq_one, hs_top⟩; simp [hq_one, hs_top]
    · rcases h with ⟨hq_top, hs_one⟩; cases hq_ne_top hq_top
    · rcases h with ⟨_, _, _, _, hsum⟩; exact hsum
  -- Rearrange the Young relation using the conjugacy identity and cancel `1/q`.
  have h_left : 1 / q + 1 / p = 1 / q + (1 / s₀ + 1 / r) := by
    -- Start from `hpqr`, swap the LHS order, rewrite `1` using `h_sum`, then reassociate.
    have H0 : 1 / q + 1 / p = 1 + 1 / r := by
      simpa [add_comm] using hpqr
    have Hstep : 1 + 1 / r = (1 / q + 1 / s₀) + 1 / r := by
      have : (1 / q + 1 / s₀) + 1 / r = 1 + 1 / r := by
        simpa [one_div, add_comm, add_left_comm, add_assoc] using
          congrArg (fun t : ℝ≥0∞ => t + 1 / r) h_sum
      simpa using this.symm
    have H1 : 1 / q + 1 / p = (1 / q + 1 / s₀) + 1 / r := H0.trans Hstep
    simpa [add_comm, add_left_comm, add_assoc] using H1
  have hq_ne_zero : q ≠ 0 := by
    have hpos : (0 : ℝ≥0∞) < q := lt_trans (by simp) hq
    exact ne_of_gt hpos
  have h_inv_q_ne_top : 1 / q ≠ ∞ := by
    simpa [one_div] using (ENNReal.inv_ne_top).2 hq_ne_zero
  -- Cancel 1/q from both sides to isolate the desired identity.
  -- The previous lines give two expressions equal to `1 + 1/r`; cancel `1/q` to isolate `1/p`.
  -- Clean up the algebraic congruences and rewrite `s₀`.
  have h_eq : 1 / p = 1 / r + 1 / s₀ := by
    -- From `h_eq' : q⁻¹ + p⁻¹ = q⁻¹ + (s₀⁻¹ + r⁻¹)`, cancel `q⁻¹` on both sides.
    have h_cancel : p⁻¹ = s₀⁻¹ + r⁻¹ :=
      WithTop.add_left_cancel (α := ℝ≥0) h_inv_q_ne_top (by
        -- rewrite `h_left` in `⁻¹` notation
        simpa [one_div, add_comm, add_left_comm, add_assoc] using h_left)
    -- Translate back to `1 / _` notation and reorder.
    have : 1 / p = 1 / s₀ + 1 / r := by simpa [one_div] using h_cancel
    simpa [add_comm] using this
  simpa [hs₀] using h_eq

/-!
Mixed-norm helper (constant-translate bound).

For a finite, right-translation invariant measure, the inner `L^r`-norm of a translate
of `f` does not depend on the translate. Consequently, the outer `L^s`-norm in `y` is
just the `L^s`-norm of a constant function. This elementary bound is often a useful
step when estimating mixed norms of translates.
-/
lemma mixed_norm_translate_young
    [NormedAddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (f : G → ℂ) (r s : ℝ≥0∞)
    (hf_meas : AEStronglyMeasurable f μ) :
    eLpNorm (fun y => (eLpNorm (fun x => f (x - y)) r μ).toReal) s μ ≤
      (μ Set.univ) ^ (1 / s.toReal) * eLpNorm f r μ := by
  classical
  -- The inner L^r norm is invariant under translation of the argument.
  have h_translate : ∀ y, eLpNorm (fun x => f (x - y)) r μ = eLpNorm f r μ := by
    intro y
    simpa [sub_eq_add_neg] using
      (eLpNorm_comp_add_right (μ := μ) (f := f) (y := -y) (p := r) hf_meas)
  -- Therefore the outer function is constant with value `(eLpNorm f r μ).toReal`.
  have h_const :
      (fun y => (eLpNorm (fun x => f (x - y)) r μ).toReal)
        = fun _ : G => (eLpNorm f r μ).toReal := by
    funext y; simp [h_translate y]
  -- Compute/bound the `L^s` seminorm of this constant function.
  have h_le :
      eLpNorm (fun _ : G => (eLpNorm f r μ).toReal) s μ ≤
        (μ Set.univ) ^ (1 / s.toReal) * eLpNorm f r μ := by
    -- For a constant real function c := (eLpNorm f r μ).toReal ≥ 0:
    -- if s = 0, the eLpNorm is 0 and the bound is trivial;
    -- if s ≠ 0, use the library formula for constants and compare ofReal (toReal t) ≤ t.
    have h_nonneg : 0 ≤ (eLpNorm f r μ).toReal := ENNReal.toReal_nonneg
    by_cases hμ : μ = 0
    · -- Zero measure case: left side is zero, so the inequality is trivial.
      subst hμ
      have : eLpNorm (fun _ : G => (eLpNorm f r (0 : Measure G)).toReal) s (0 : Measure G) = 0 := by
        simp
      simp [this]
    · -- Nonzero measure: split on s = 0 or not.
      have hμ_ne : μ ≠ 0 := hμ
      by_cases hs : s = 0
      · -- If s = 0, the eLpNorm is zero; conclude by 0 ≤ RHS.
        have : eLpNorm (fun _ : G => (eLpNorm f r μ).toReal) s μ = 0 := by
          simp [hs]
        simp [this]
      · -- If s ≠ 0, use the constant eLpNorm formula and then compare factors.
        have h_const_eLp :
            eLpNorm (fun _ : G => (eLpNorm f r μ).toReal) s μ
              = ENNReal.ofReal ((eLpNorm f r μ).toReal) * (μ Set.univ) ^ (1 / s.toReal) := by
          -- `eLpNorm_const` uses the norm of the constant; simplify using nonnegativity.
          have h0 : s ≠ 0 := hs
          -- Rewrite ‖c‖ₑ = ENNReal.ofReal ‖c‖, and simplify using c ≥ 0.
          simpa [Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
                Real.norm_eq_abs, abs_of_nonneg h_nonneg] using
            (eLpNorm_const (μ := μ) (p := s) (c := (eLpNorm f r μ).toReal) h0 hμ_ne)
        have h_ofReal_le :
            ENNReal.ofReal ((eLpNorm f r μ).toReal) ≤ eLpNorm f r μ := by
          -- `ofReal (toReal t) ≤ t` for all `t : ℝ≥0∞`.
          simpa using (ENNReal.ofReal_toReal_le (a := eLpNorm f r μ))
        -- Multiply the factor-wise inequality on the right by (μ Set.univ)^(1 / s.toReal).
        have :
            ENNReal.ofReal ((eLpNorm f r μ).toReal) * (μ Set.univ) ^ (1 / s.toReal)
              ≤ eLpNorm f r μ * (μ Set.univ) ^ (1 / s.toReal) := by
          exact mul_le_mul_right' h_ofReal_le ((μ Set.univ) ^ (1 / s.toReal))
        simpa [h_const_eLp, mul_comm] using this
  simpa [h_const] using h_le

/-!
Auxiliary Hölder-style bound for multiplying by the constant 1.

For exponents p, r, s with 1/p = 1/r + 1/s, the L^p seminorm of f is bounded by the
product of its L^r seminorm and the L^s seminorm of the constant function 1. This is a
direct application of the general eLpNorm × eLpNorm inequality for pointwise products,
specialised to multiplication by (1 : ℂ).
-/
lemma eLpNorm_mul_one_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f : α → ℂ)
    {p r s : ℝ≥0∞}
    [ENNReal.HolderTriple r s p]
    (hf_meas : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ≤ eLpNorm f r μ * eLpNorm (fun _ : α => (1 : ℂ)) s μ := by
  classical
  -- Measurability of the constant-1 function (complex-valued)
  have h_one_meas : AEStronglyMeasurable (fun _ : α => (1 : ℂ)) μ := by
    simpa using (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : α => (1 : ℂ)) μ)
  -- Pointwise bound on the nnnorm of the product by the product of nnnorms (with c = 1)
  have h_bound :
      ∀ᵐ x ∂ μ, ‖f x * (1 : ℂ)‖₊ ≤ (1 : ℝ≥0) * ‖f x‖₊ * ‖(1 : ℂ)‖₊ :=
    Filter.Eventually.of_forall (fun x => by
      have : ‖f x * (1 : ℂ)‖₊ = ‖f x‖₊ * ‖(1 : ℂ)‖₊ := by
        simp [nnnorm_mul]
      simp [this, one_mul, mul_comm, mul_left_comm, mul_assoc])
  -- Apply the general inequality for eLpNorm of products, specialised to multiplication by 1
  have h :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (μ := μ)
      (p := r) (q := s) (r := p)
      hf_meas h_one_meas (fun x y : ℂ => x * y) (1 : ℝ≥0) h_bound
  -- Simplify with the identity f * 1 = f and c = 1
  simpa using
    (calc
      eLpNorm f p μ
          = eLpNorm (fun x => f x * (1 : ℂ)) p μ := by simp
      _ ≤ (1 : ℝ≥0∞) * eLpNorm f r μ * eLpNorm (fun _ : α => (1 : ℂ)) s μ := h
      _ = eLpNorm f r μ * eLpNorm (fun _ : α => (1 : ℂ)) s μ := by simp)

lemma limsup_control_aux
    (μ : Measure G) [SFinite μ] (g_pow : G → ℝ≥0∞) (Φ : ℕ → ℝ≥0∞)
    (f_seq : ℕ → G → ℝ≥0∞)
    (hΦ : ∀ N,
        Φ N =
          ∫⁻ x,
            f_seq N x ∂
              (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k))
    (hf_meas : ∀ N, AEMeasurable (f_seq N) μ)
    (hf_mono : ∀ᵐ x ∂ μ, Monotone fun N => f_seq N x)
    (hf_tendsto : ∀ᵐ x ∂ μ, Tendsto (fun N => f_seq N x) atTop (𝓝 (g_pow x))) :
    (∫⁻ x, g_pow x ∂ μ) ≤ Filter.limsup Φ Filter.atTop := by
  classical
  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
  set μpartial : ℕ → Measure G :=
    fun N => ∑ k ∈ Finset.range (N + 1), μn k
  have hμ_sum : Measure.sum μn = μ := MeasureTheory.sum_sfiniteSeq μ
  have hμn_le : ∀ k, μn k ≤ μ :=
    fun k => MeasureTheory.sfiniteSeq_le (μ := μ) k
  have hμn_ac : ∀ k, μn k ≪ μ :=
    fun k => Measure.absolutelyContinuous_of_le (hμn_le k)
  have hΦ_sum :
      ∀ N,
        Φ N =
          ∑ k ∈ Finset.range (N + 1),
            ∫⁻ x, f_seq N x ∂ μn k := by
    intro N
    classical
    simpa [μn, μpartial, MeasureTheory.lintegral_finset_sum_measure]
      using hΦ N
  let A : ℕ → ℕ → ℝ≥0∞ :=
    fun N k => ∫⁻ x, f_seq N x ∂ μn k
  let B : ℕ → ℝ≥0∞ := fun k => ∫⁻ x, g_pow x ∂ μn k
  have hf_meas' : ∀ k N, AEMeasurable (f_seq N) (μn k) := by
    intro k N
    exact (hf_meas N).mono_ac (hμn_ac k)
  have h_mono_zero :
      μ {x | ¬ Monotone fun N => f_seq N x} = 0 := by
    simpa [ae_iff] using hf_mono
  have h_tendsto_zero :
      μ {x |
          ¬ Tendsto (fun N => f_seq N x) atTop (𝓝 (g_pow x))} = 0 := by
    simpa [ae_iff] using hf_tendsto
  have hf_mono_k :
      ∀ k, ∀ᵐ x ∂ μn k, Monotone fun N => f_seq N x := by
    intro k
    have h_le := hμn_le k
    have h_zero' :
        μn k {x | ¬ Monotone fun N => f_seq N x} = 0 := by
      have hineq := h_le {x | ¬ Monotone fun N => f_seq N x}
      have hle_zero :
          μn k {x | ¬ Monotone fun N => f_seq N x} ≤ 0 := by
        simpa [h_mono_zero] using hineq
      exact le_antisymm hle_zero bot_le
    exact (ae_iff).2 h_zero'
  have hf_tendsto_k :
      ∀ k,
        ∀ᵐ x ∂ μn k, Tendsto (fun N => f_seq N x) atTop (𝓝 (g_pow x)) := by
    intro k
    have h_le := hμn_le k
    have h_zero' :
        μn k {x |
            ¬ Tendsto (fun N => f_seq N x) atTop (𝓝 (g_pow x))} = 0 := by
      have hineq := h_le
          {x | ¬ Tendsto (fun N => f_seq N x) atTop (𝓝 (g_pow x))}
      have hle_zero :
          μn k {x |
              ¬ Tendsto (fun N => f_seq N x) atTop (𝓝 (g_pow x))} ≤ 0 := by
        simpa [h_tendsto_zero] using hineq
      exact le_antisymm hle_zero bot_le
    exact (ae_iff).2 h_zero'
  have hA_tendsto :
      ∀ k, Tendsto (fun N => A N k) atTop (𝓝 (B k)) := by
    intro k
    have :=
      MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
        (μ := μn k)
        (f := fun N => f_seq N)
        (F := g_pow)
        (hf := hf_meas' k)
        (h_mono := hf_mono_k k)
        (h_tendsto := hf_tendsto_k k)
    simpa [A, B] using this
  have hA_mono :
      ∀ k, Monotone fun N => A N k := by
    intro k
    refine fun i j hij =>
      lintegral_mono_ae <|
        (hf_mono_k k).mono ?_
    intro x hx
    exact hx hij
  have hΦ_le_limsup_partial :
      ∀ J,
        (∑ k ∈ Finset.range (J + 1), B k) ≤
          Filter.limsup Φ Filter.atTop := by
    intro J
    classical
    let SJ : ℕ → ℝ≥0∞ :=
      fun N => ∑ k ∈ Finset.range (J + 1), A N k
    have h_eventually_le :
        ∀ᶠ N in Filter.atTop, SJ N ≤ Φ N := by
      refine (eventually_ge_atTop J).mono ?_
      intro N hNJ
      have h_subset :
          Finset.range (J + 1) ⊆ Finset.range (N + 1) := by
        intro k hk
        simp only [Finset.mem_range] at hk ⊢
        -- hk : k < J + 1 means k ≤ J
        -- hNJ : J ≤ N, so k ≤ J ≤ N, thus k < N + 1
        calc k < J + 1 := hk
          _ ≤ N + 1 := Nat.succ_le_succ hNJ
      have h_nonneg :
          ∀ i ∈ Finset.range (N + 1), i ∉ Finset.range (J + 1) →
            (0 : ℝ≥0∞) ≤ A N i :=
        fun _ _ _ => bot_le
      have :
          SJ N ≤ ∑ k ∈ Finset.range (N + 1), A N k :=
        Finset.sum_le_sum_of_subset_of_nonneg h_subset h_nonneg
      simpa [SJ, hΦ_sum N] using this
    have hSJ_limsup_le :
        Filter.limsup SJ Filter.atTop ≤ Filter.limsup Φ Filter.atTop :=
      Filter.limsup_le_limsup h_eventually_le
    have hSJ_tendsto :
        Tendsto SJ Filter.atTop (𝓝 (∑ k ∈ Finset.range (J + 1), B k)) := by
      classical
      have h_tendsto_finset :
        ∀ s : Finset ℕ,
          Tendsto (fun N => ∑ k ∈ s, A N k) Filter.atTop
              (𝓝 (∑ k ∈ s, B k)) := by
        intro s
        refine Finset.induction_on s ?base ?step
        · simp
        · intro a s ha h_ind
          have h_a := hA_tendsto a
          simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc]
            using (h_a.add h_ind)
      simpa [SJ] using h_tendsto_finset (Finset.range (J + 1))
    have hSJ_limsup_eq :
        Filter.limsup SJ Filter.atTop =
          (∑ k ∈ Finset.range (J + 1), B k) :=
      hSJ_tendsto.limsup_eq
    -- Since SJ tends to its limit and limsup SJ ≤ limsup Φ
    calc (∑ k ∈ Finset.range (J + 1), B k)
      = limsup SJ atTop := hSJ_limsup_eq.symm
      _ ≤ limsup Φ atTop := hSJ_limsup_le
  have h_tsum_eq :
      (∑' k, B k) = ∫⁻ x, g_pow x ∂ μ := by
    classical
    simpa [B, μn, hμ_sum] using
      (MeasureTheory.lintegral_sum_measure (μ := μn) (f := g_pow)).symm
  have h_partial_sup :
      (∑' k, B k) =
        iSup (fun n => ∑ k ∈ Finset.range n, B k) := by
    simpa using (ENNReal.tsum_eq_iSup_nat (f := fun k => B k))
  have h_partial_le :
      (∑' k, B k) ≤ Filter.limsup Φ Filter.atTop := by
    classical
    have h_sup_le :
        iSup (fun n => ∑ k ∈ Finset.range n, B k) ≤
          Filter.limsup Φ Filter.atTop := by
      refine iSup_le ?_
      intro n
      cases n with
      | zero => simp
      | succ J => simpa [Nat.succ_eq_add_one] using hΦ_le_limsup_partial J
    simpa [h_partial_sup] using h_sup_le
  calc
    ∫⁻ x, g_pow x ∂ μ = ∑' k, B k := h_tsum_eq.symm
    _ ≤ Filter.limsup Φ Filter.atTop := h_partial_le

variable {G : Type*}
variable [MeasurableSpace G]
variable (μ : Measure G)
variable [NormedAddCommGroup G]
variable [μ.IsAddRightInvariant]
variable [MeasurableAdd₂ G]

noncomputable def A_fun (μpartial : ℕ → Measure G) (f : G → ℂ)
    (r : ℝ≥0∞) (N : ℕ) (y : G) : ℝ :=
  (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal

-- Measurability of y ↦ (eLpNorm (x ↦ f(x−y)) r (μpartial N)).toReal on μpartial N.
lemma A_measurable_partial
    [SFinite μ] [MeasurableNeg G]
    (f : G → ℂ) (r : ℝ≥0∞) (μpartial : ℕ → Measure G)
    (hr_ne_zero : r ≠ 0) (hr_ne_top : r ≠ ∞)
    (hf_meas : AEStronglyMeasurable f μ)
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (hμpartial_prod_ac : ∀ N, (μpartial N).prod (μpartial N) ≪ μ.prod μ) :
    ∀ N, AEStronglyMeasurable (fun y => A_fun μpartial f r N y) (μpartial N) := by
  intro N
  classical
  -- Build the product-measurable kernel (without g) on μ.prod μ first,
  -- then transfer to (μpartial N).prod (μpartial N) via absolute continuity.
  let g1 : G → ℂ := fun _ => (1 : ℂ)
  have h_kernel_norm_meas_one :
      AEStronglyMeasurable
        (fun q : G × G => ‖f (q.1 - q.2) * g1 q.2‖) (μ.prod μ) :=
    (convolution_kernel_aestronglyMeasurable (μ := μ)
      (f := f) (g := g1) hf_meas
        (aestronglyMeasurable_const : AEStronglyMeasurable g1 μ)).norm
  have hF_meas_prod :
      AEStronglyMeasurable (fun q : G × G => ‖f (q.1 - q.2)‖) (μ.prod μ) := by
    -- From ‖f * g1‖ measurable, derive ‖f‖ measurable using g1 = 1
    have h1 : (fun q : G × G => ‖f (q.1 - q.2) * g1 q.2‖)
        = (fun q => ‖f (q.1 - q.2)‖) := by
      ext q
      simp [g1, mul_one]
    rw [← h1]
    exact h_kernel_norm_meas_one
  -- Transfer measurability to the partial product measure.
  have hF_meas_partial :
      AEStronglyMeasurable (fun q : G × G => ‖f (q.1 - q.2)‖)
        ((μpartial N).prod (μpartial N)) :=
    (hF_meas_prod.mono_ac (hμpartial_prod_ac N))
  -- Raise to r.toReal and integrate w.r.t. x to obtain the lintegral measurability in y.
  have h_integrand_aemeasurable :
      AEMeasurable
        (fun y => ∫⁻ x, (‖f (x - y)‖ₑ) ^ r.toReal ∂ μpartial N)
        (μpartial N) := by
    -- μpartial N is a finite measure, hence SFinite
    haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
    haveI : SFinite (μpartial N) := inferInstance
    have := hF_meas_partial.aemeasurable.enorm.pow_const r.toReal
    -- rearrange variables (x,y) ↔ (q.1,q.2)
    simpa [Function.uncurry]
      using this.lintegral_prod_left'
  -- Conclude measurability of eLpNorm_y via the r-power/ToReal representation.
  have hA_eLpMeas :
      AEMeasurable
        (fun y => eLpNorm (fun x => f (x - y)) r (μpartial N)) (μpartial N) := by
    -- Use the eLpNorm = lintegral^(1/r) representation.
    have :=
      (measurable_id.pow_const (1 / r.toReal)).comp_aemeasurable
        h_integrand_aemeasurable
    refine this.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    simp [eLpNorm_eq_lintegral_rpow_enorm (μ := μpartial N)
      (f := fun x => f (x - y)) hr_ne_zero hr_ne_top, one_div,
      ENNReal.rpow_mul, mul_comm, mul_left_comm, mul_assoc]
  -- Finally, take toReal and upgrade to AEStronglyMeasurable.
  exact (hA_eLpMeas.ennreal_toReal).aestronglyMeasurable

-- Finite‑measure exponent monotonicity in the r→p direction on a partial measure family.
-- Stub lemma placed here so it is available to subsequent proofs.
lemma exponent_mono_rp_on_partial_measure
    (f : G → ℂ) (p r : ℝ≥0∞) (μpartial : ℕ → Measure G)
    (hp_le_hr : p ≤ r)
    (hf : MemLp f p μ)
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (hμpartial_ac : ∀ N, μpartial N ≪ μ) :
    ∀ N y,
      ((μpartial N) Set.univ) ^ (1 / r.toReal - 1 / p.toReal)
        * eLpNorm (fun x => f (x - y)) p (μpartial N)
      ≤ eLpNorm (fun x => f (x - y)) r (μpartial N) := by
  intro N y
  classical
  haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
  have h_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using measurePreserving_add_right (μ := μ) (-y)
  have h_shift_mem : MemLp (fun x => f (x - y)) p μ :=
    hf.comp_measurePreserving h_pres
  have h_meas_μ : AEStronglyMeasurable (fun x => f (x - y)) μ :=
    h_shift_mem.aestronglyMeasurable
  have h_meas_partial :
      AEStronglyMeasurable (fun x => f (x - y)) (μpartial N) :=
    h_meas_μ.mono_ac (hμpartial_ac N)
  by_cases hμz : μpartial N = 0
  · -- Zero measure: both sides are zero.
    simp [hμz]
  · -- Apply the finite-measure p→r comparison and rearrange.
    have h_base :
        eLpNorm (fun x => f (x - y)) p (μpartial N)
          ≤ ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
              * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
      simpa [mul_comm]
        using
          (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
            (μ := μpartial N) (f := fun x => f (x - y))
            (p := p) (q := r) hp_le_hr h_meas_partial)
    -- Multiply both sides by μ(univ)^(1/r − 1/p) and cancel exponents.
    set α : ℝ≥0∞ := ((μpartial N) Set.univ) ^ (1 / r.toReal - 1 / p.toReal) with hα
    set β : ℝ≥0∞ := ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal) with hβ
    have hμU_ne_zero : (μpartial N) Set.univ ≠ 0 := by
      simpa [Measure.measure_univ_eq_zero] using hμz
    have hμU_ne_top : (μpartial N) Set.univ ≠ ∞ := by simp
    have h_prod_one : α * β = (1 : ℝ≥0∞) := by
      have h := ENNReal.rpow_add (x := (μpartial N) Set.univ)
                  (y := (1 / r.toReal - 1 / p.toReal))
                  (z := (1 / p.toReal - 1 / r.toReal))
                  hμU_ne_zero hμU_ne_top
      have : α * β
          = (μpartial N) Set.univ
              ^ ((1 / r.toReal - 1 / p.toReal) + (1 / p.toReal - 1 / r.toReal)) := by
        simpa [hα, hβ, mul_comm, mul_left_comm, mul_assoc] using h.symm
      simp [this]
    have h_mul := mul_le_mul_left' h_base α
    -- α * (β * ‖·‖_r) = (α * β) * ‖·‖_r = ‖·‖_r
    calc
      α * eLpNorm (fun x => f (x - y)) p (μpartial N)
          ≤ α * (β * eLpNorm (fun x => f (x - y)) r (μpartial N)) := h_mul
      _ = (α * β) * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ = eLpNorm (fun x => f (x - y)) r (μpartial N) := by
            simp [h_prod_one]

lemma A_uniform_bound_s0_of_split
    [SFinite μ] [MeasurableNeg G]
    (f : G → ℂ) (p r s₀ : ℝ≥0∞)
    (μpartial : ℕ → Measure G)
    (hf : MemLp f p μ) (hf_r : MemLp f r μ)
    (hs₀_ne_zero : s₀ ≠ 0) (hs₀_ne_top : s₀ ≠ ∞)
    (hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N))
    (hμpartial_le : ∀ N, μpartial N ≤ μ)
    :
    ∀ N,
      (eLpNorm (fun y => A_fun μpartial f r N y) s₀ (μpartial N)).toReal
        ≤ ((μpartial N) Set.univ ^ (1 / s₀.toReal) * eLpNorm f r μ).toReal := by
  -- See the proof sketch discussed in the main lemma: combine
  -- finite-measure exponent monotonicity p→r, measure monotonicity μpartial≤μ,
  -- translation invariance for L^p under μ, and exponent cancellation via h_split.
  intro N
  classical
  -- Notation
  set μN := μpartial N
  haveI : IsFiniteMeasure μN := hμpartial_fin N
  -- Basic properties for s₀
  have hs₀_pos : 0 < s₀.toReal := ENNReal.toReal_pos hs₀_ne_zero hs₀_ne_top
  have hs₀_nonneg : 0 ≤ s₀.toReal := le_of_lt hs₀_pos
  -- Rewrite the target as an inequality in ℝ≥0∞ and then use `toReal_mono`.
  have h_target :
      eLpNorm (fun y => A_fun μpartial f r N y) s₀ μN
        ≤ (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ := by
    -- Step 1: Reduce the left `eLpNorm` to the lintegral representation and bound the integrand.
    -- Define the auxiliary functions
    let A : G → ℝ := fun y => A_fun μpartial f r N y
    let B : G → ℝ≥0∞ := fun y => eLpNorm (fun x => f (x - y)) r μN
    -- Expand the eLpNorm on the left via the r-power representation and compare integrands.
    have h_eLp_A :=
      eLpNorm_eq_lintegral_rpow_enorm (μ := μN) (f := A) hs₀_ne_zero hs₀_ne_top
    -- Pointwise bound: ofReal (toReal (B y)) ≤ B y
    have h_pow_bound :
        ∀ᵐ y ∂ μN, (‖A y‖ₑ) ^ s₀.toReal ≤ (B y) ^ s₀.toReal := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      -- ‖A y‖ₑ = ofReal (A y) and A y = (B y).toReal
      have h_base : (‖A y‖ₑ) ≤ B y := by
        -- `A y = (B y).toReal` and `ofReal (toReal _) ≤ _`.
        simpa [A_fun, A, B,
          Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
          Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          using (ENNReal.ofReal_toReal_le (a := B y))
      exact ENNReal.rpow_le_rpow h_base hs₀_nonneg
    -- Therefore, (eLpNorm A s₀ μN) ^ s₀.toReal ≤ ∫ (B y)^s₀ dμN
    have h_step1 :
        (eLpNorm A s₀ μN) ^ s₀.toReal
          ≤ ∫⁻ y, (B y) ^ s₀.toReal ∂ μN := by
      -- h_eLp_A : eLpNorm A s₀ μN = (∫⁻ x, ‖A x‖ₑ ^ s₀.toReal ∂μN) ^ (1 / s₀.toReal)
      rw [h_eLp_A]
      have h_cancel : ((∫⁻ x, ‖A x‖ₑ ^ s₀.toReal ∂μN) ^ (1 / s₀.toReal)) ^ s₀.toReal
          = ∫⁻ x, ‖A x‖ₑ ^ s₀.toReal ∂μN := by
        have hs₀_toReal_ne_zero : s₀.toReal ≠ 0 := by
          have : 0 < s₀.toReal := hs₀_pos
          linarith
        rw [← ENNReal.rpow_mul, one_div]
        have : s₀.toReal⁻¹ * s₀.toReal = 1 := by
          rw [mul_comm]
          field_simp [hs₀_toReal_ne_zero]
        rw [this, ENNReal.rpow_one]
      rw [h_cancel]
      exact lintegral_mono_ae h_pow_bound
    -- Step 2: For each y, use finite-measure exponent monotonicity r→p on μN.
    have hf_meas : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
    have h_mono_r : ∀ y,
        eLpNorm (fun x => f (x - y)) r μN ≤ eLpNorm (fun x => f (x - y)) r μ := by
      intro y; exact eLpNorm_mono_measure (μ := μ) (ν := μN) (p := r)
        (f := fun x => f (x - y)) (hμpartial_le N)
    have h_translate_r : ∀ y,
        eLpNorm (fun x => f (x - y)) r μ = eLpNorm f r μ := by
      intro y
      have h :=
        eLpNorm_comp_add_right (μ := μ) (f := f) (y := -y) (p := r) hf_meas
      simpa [sub_eq_add_neg] using h
    have h_B_le_const : ∀ y, B y ≤ eLpNorm f r μ := by
      intro y; exact (h_mono_r y).trans (le_of_eq (h_translate_r y))
    -- Hence (B y)^s₀ ≤ (eLpNorm f r μ)^s₀ and integrate to bound the lintegral.
    have h_pow_mono : ∀ᵐ y ∂ μN, (B y) ^ s₀.toReal ≤ (eLpNorm f r μ) ^ s₀.toReal := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      exact ENNReal.rpow_le_rpow (h_B_le_const y) hs₀_nonneg
    have h_step2 :
        ∫⁻ y, (B y) ^ s₀.toReal ∂ μN ≤
          (μN Set.univ) * (eLpNorm f r μ) ^ s₀.toReal := by
      -- Integrate the pointwise bound; RHS is the integral of the constant.
      have h_const :
          (∫⁻ _ : G, (eLpNorm f r μ) ^ s₀.toReal ∂ μN)
            = (μN Set.univ) * (eLpNorm f r μ) ^ s₀.toReal := by
        rw [lintegral_const, mul_comm]
      exact (lintegral_mono_ae h_pow_mono).trans_eq h_const
    -- Combine step1 and step2, then extract (1/s₀) power.
    -- From h_step1: (‖A‖_{s₀,μN})^{s₀} ≤ ∫ (B^s₀).
    -- Thus (‖A‖_{s₀,μN})^{s₀} ≤ μN(univ) * (‖f‖_{r,μ})^{s₀}.
    have h_bound_rpow :
        (eLpNorm A s₀ μN) ^ s₀.toReal
          ≤ (μN Set.univ) * (eLpNorm f r μ) ^ s₀.toReal :=
      le_trans h_step1 h_step2
    -- Raise both sides to the power (1 / s₀) and simplify using rpow identities.
    have hs₀_toReal_ne_zero : s₀.toReal ≠ 0 := by
      have : 0 < s₀.toReal := hs₀_pos; linarith
    have h_nonneg : 0 ≤ 1 / s₀.toReal := by
      have : 0 < s₀.toReal := hs₀_pos
      exact div_nonneg (by norm_num) (le_of_lt this)
    -- Apply monotonicity of rpow with exponent 1/s₀.toReal > 0.
    have h_rpow_mono := ENNReal.rpow_le_rpow h_bound_rpow h_nonneg
    -- Rewrite LHS: ((‖A‖)^{s₀})^{1/s₀} = ‖A‖
    have hL :
        ((eLpNorm A s₀ μN) ^ s₀.toReal) ^ (1 / s₀.toReal)
          = eLpNorm A s₀ μN := by
      rw [one_div, ← ENNReal.rpow_mul]
      have : s₀.toReal * s₀.toReal⁻¹ = 1 := by
        field_simp [hs₀_toReal_ne_zero]
      rw [this, ENNReal.rpow_one]
    -- Rewrite RHS: (μN)^{1/s₀} * (‖f‖_r^{s₀})^{1/s₀} = (μN)^{1/s₀} * ‖f‖_r.
    have hR :
        ((μN Set.univ) * (eLpNorm f r μ) ^ s₀.toReal) ^ (1 / s₀.toReal)
          = (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ := by
      -- distribute rpow across the product and cancel s₀ on the second factor
      have h_distrib := ENNReal.mul_rpow_of_nonneg (μN Set.univ)
        ((eLpNorm f r μ) ^ s₀.toReal) h_nonneg
      have h_cancel :
          ((eLpNorm f r μ) ^ s₀.toReal) ^ (1 / s₀.toReal)
            = eLpNorm f r μ := by
        rw [one_div, ← ENNReal.rpow_mul]
        have : s₀.toReal * s₀.toReal⁻¹ = 1 := by
          field_simp [hs₀_toReal_ne_zero]
        rw [this, ENNReal.rpow_one]
      rw [h_cancel] at h_distrib
      exact h_distrib
    -- Conclude the desired bound in ℝ≥0∞.
    have : (eLpNorm A s₀ μN)
        ≤ (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ := by
      -- transform via the previous equalities
      rw [← hL, ← hR]
      exact h_rpow_mono
    exact this
  -- Finally, pass to `toReal` using finiteness of the right-hand side.
  -- The RHS is finite since μN is finite and ‖f‖_{r,μ} < ∞.
  have h_rhs_ne_top :
      (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f r μ ≠ ∞ := by
    have hμ_fin : (μN Set.univ) ≠ ∞ := by simp
    have hμ_rpow_fin : (μN Set.univ) ^ (1 / s₀.toReal) ≠ ∞ := by
      have : 0 ≤ (1 / s₀.toReal) := by
        rw [one_div]
        exact inv_nonneg.mpr (le_of_lt hs₀_pos)
      exact ENNReal.rpow_ne_top_of_nonneg this hμ_fin
    have hf_r_fin : eLpNorm f r μ ≠ ∞ := by simpa using hf_r.eLpNorm_ne_top
    exact ENNReal.mul_ne_top hμ_rpow_fin hf_r_fin
  exact ENNReal.toReal_mono h_rhs_ne_top h_target

-- Stronger uniform bound for A in L^{s₀} using the p-norm on μ.
-- This collapses the (μpartial N)-growth via the identity 1/p = 1/r + 1/s₀
-- and yields a bound independent of N on the right-hand side.
lemma hA_uniform_bound_s0_to_p
    (p r s₀ : ℝ≥0∞) [IsProbabilityMeasure μ] [ENNReal.HolderTriple p s₀ r] [MeasurableNeg G]
    (f : G → ℂ) (μpartial : ℕ → Measure G) (hf : MemLp f p μ)
    (hs₀_ne_zero : s₀ ≠ 0) (hs₀_ne_top : s₀ ≠ ∞) (hμpartial_le : ∀ N, μpartial N ≤ μ) :
    ∀ N,
      (eLpNorm (fun y => A_fun μpartial f r N y) s₀ (μpartial N)).toReal
        ≤ (eLpNorm f p μ).toReal := by
  -- We show a pointwise bound A_fun ≤ ‖f‖_p, then take the L^{s₀} norm in y.
  intro N
  classical
  set μN := μpartial N
  -- Basic properties for s₀
  have hs₀_pos : 0 < s₀.toReal := ENNReal.toReal_pos hs₀_ne_zero hs₀_ne_top
  have hs₀_nonneg : 0 ≤ s₀.toReal := le_of_lt hs₀_pos
  -- For each y, bound the inner r-norm on μN by the p-norm on μ.
  -- First push from μN to μ, then apply the product inequality with the constant 1
  -- using the split 1/r = 1/p + 1/s₀, and finally translate back to f.
  have hf_meas : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have h_one_meas : AEStronglyMeasurable (fun _ : G => (1 : ℂ)) μ := by
    simpa using (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : G => (1 : ℂ)) μ)
  have h_one_norm_prob : eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ = 1 := by
    -- Compute the L^{s₀} seminorm of the constant-1 function on a probability space.
    have hμ_ne : μ ≠ 0 := by
      -- Probability measure has μ(univ) = 1, hence μ ≠ 0.
      intro h0
      have h01 : (0 : ℝ≥0∞) ≠ 1 := by
        simp
      have : (0 : ℝ≥0∞) = 1 := by simpa [h0] using (IsProbabilityMeasure.measure_univ (μ := μ))
      exact h01 this
    have h_const :=
      eLpNorm_const (μ := μ) (p := s₀) (c := (1 : ℂ)) (by exact hs₀_ne_zero) hμ_ne
    -- ‖(1 : ℂ)‖ = 1, so the ENNReal constant factor is 1.
    have hnorm : ENNReal.ofReal ‖(1 : ℂ)‖ = 1 := by
      simp
    -- On a probability space, μ(univ) = 1
    have hμ : μ Set.univ = 1 := (IsProbabilityMeasure.measure_univ (μ := μ))
    simp [h_const, hnorm, hμ, one_div]
  have h_pointwise_B_le : ∀ y,
      eLpNorm (fun x => f (x - y)) r μN ≤ eLpNorm f p μ := by
    intro y
    -- Monotonicity in the measure: μN ≤ μ
    have h_mono :=
      eLpNorm_mono_measure (μ := μ) (ν := μN) (p := r)
        (f := fun x => f (x - y)) (hμpartial_le N)
    -- Hölder-style bound on μ for the translate using the constant function 1.
    -- 1/r = 1/p + 1/s₀ is encoded by the HolderTriple [r.HolderTriple s₀ p].
    have h_bound_prod :
        eLpNorm (fun x => f (x - y)) r μ
          ≤ eLpNorm (fun x => f (x - y)) p μ * eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ := by
      -- Measurability of the translate under μ
      have h_shift_meas : AEStronglyMeasurable (fun x => f (x - y)) μ := by
        -- Use measure-preserving translation to keep the same measure μ
        have h_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using measurePreserving_add_right (μ := μ) (-y)
        exact hf_meas.comp_measurePreserving h_pres
      -- Pointwise bound on nnnorm of the product by the product of nnnorms
      have h_bound :
          ∀ᵐ x ∂ μ,
            ‖((fun x => f (x - y)) x * (1 : ℂ))‖₊ ≤
              (1 : ℝ≥0) * ‖(fun x => f (x - y)) x‖₊ * ‖(1 : ℂ)‖₊ :=
        Filter.Eventually.of_forall (fun x => by
          have : ‖((fun x => f (x - y)) x * (1 : ℂ))‖₊
                = ‖(fun x => f (x - y)) x‖₊ * ‖(1 : ℂ)‖₊ := by
            simp [nnnorm_mul]
          simp [this, one_mul, mul_comm, mul_left_comm, mul_assoc])
      -- Apply the general eLpNorm (product) inequality
      have h :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
          (μ := μ)
          (p := p) (q := s₀) (r := r)
          h_shift_meas h_one_meas (fun x y : ℂ => x * y) (1 : ℝ≥0) h_bound
      simpa using h
    -- Translate invariance for the p-norm on μ
    have h_translate_p : eLpNorm (fun x => f (x - y)) p μ = eLpNorm f p μ := by
      simpa [sub_eq_add_neg] using
        eLpNorm_comp_add_right (μ := μ) (f := f) (y := -y) (p := p) hf_meas
    -- Combine and insert the probability-space simplification for ‖1‖_{s₀}.
    have : eLpNorm (fun x => f (x - y)) r μ ≤ eLpNorm f p μ := by
      simpa [h_translate_p, h_one_norm_prob, one_mul] using h_bound_prod
    exact (h_mono.trans this)
  -- Now replicate the A_uniform_bound_s0_of_split integration argument with the new constant.
  -- Define A(y) and B(y) and compare their r-powers as before.
  let A : G → ℝ := fun y => A_fun μpartial f r N y
  let B : G → ℝ≥0∞ := fun y => eLpNorm (fun x => f (x - y)) r μN
  have h_eLp_A :=
    eLpNorm_eq_lintegral_rpow_enorm (μ := μN) (f := A) hs₀_ne_zero hs₀_ne_top
  have h_pow_bound :
      ∀ᵐ y ∂ μN, (B y) ^ s₀.toReal ≤ (eLpNorm f p μ) ^ s₀.toReal := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    exact ENNReal.rpow_le_rpow (h_pointwise_B_le y) hs₀_nonneg
  have h_step1 :
      (eLpNorm A s₀ μN) ^ s₀.toReal
        ≤ ∫⁻ y, (B y) ^ s₀.toReal ∂ μN := by
    -- As in A_uniform_bound_s0_of_split: compare the integrands via toReal/ofReal
    -- using (‖A y‖ₑ) ≤ B y and rpow monotonicity.
    -- Pointwise, ‖A y‖ₑ = ofReal (A y) ≤ B y since A y = (B y).toReal.
    have h_pt : ∀ y, (‖A y‖ₑ) ≤ B y := by
      intro y
      -- A y = (B y).toReal and ofReal_toReal ≤ identity
      simpa [A_fun, A, B,
        Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
        Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        using (ENNReal.ofReal_toReal_le (a := B y))
    have h_pt_rpow : ∀ y, (‖A y‖ₑ) ^ s₀.toReal ≤ (B y) ^ s₀.toReal :=
      fun y => ENNReal.rpow_le_rpow (h_pt y) hs₀_nonneg
    -- Convert eLpNorm(A) into the rpow-lintegral and bound the integrand a.e.
    rw [h_eLp_A]
    have h_cancel : ((∫⁻ x, ‖A x‖ₑ ^ s₀.toReal ∂ μN) ^ (1 / s₀.toReal)) ^ s₀.toReal
        = ∫⁻ x, ‖A x‖ₑ ^ s₀.toReal ∂ μN := by
      have hs₀_toReal_ne_zero : s₀.toReal ≠ 0 := by linarith
      rw [← ENNReal.rpow_mul, one_div]
      have : s₀.toReal⁻¹ * s₀.toReal = 1 := by
        rw [mul_comm]; field_simp [hs₀_toReal_ne_zero]
      rw [this, ENNReal.rpow_one]
    rw [h_cancel]
    exact lintegral_mono (fun y => h_pt_rpow y)
  have h_step2 :
      ∫⁻ y, (B y) ^ s₀.toReal ∂ μN
        ≤ (μN Set.univ) * (eLpNorm f p μ) ^ s₀.toReal := by
    -- Integrate the constant bound on (B y)^s₀ over μN.
    have h_const :
        (∫⁻ _ : G, (eLpNorm f p μ) ^ s₀.toReal ∂ μN)
          = (μN Set.univ) * (eLpNorm f p μ) ^ s₀.toReal := by
      rw [lintegral_const, mul_comm]
    exact (lintegral_mono_ae h_pow_bound).trans_eq h_const
  -- Extract the (1/s₀)-power and simplify the product.
  have hs₀_toReal_ne_zero : s₀.toReal ≠ 0 := by linarith
  have h_nonneg : 0 ≤ 1 / s₀.toReal := by exact one_div_nonneg.mpr (le_of_lt hs₀_pos)
  have h_rpow_mono := ENNReal.rpow_le_rpow (le_trans h_step1 h_step2) h_nonneg
  have hL :
      ((eLpNorm A s₀ μN) ^ s₀.toReal) ^ (1 / s₀.toReal) = eLpNorm A s₀ μN := by
    rw [one_div, ← ENNReal.rpow_mul]
    have : s₀.toReal * s₀.toReal⁻¹ = 1 := by field_simp [hs₀_toReal_ne_zero]
    rw [this, ENNReal.rpow_one]
  have hR :
      ((μN Set.univ) * (eLpNorm f p μ) ^ s₀.toReal) ^ (1 / s₀.toReal)
        = (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f p μ := by
    have h_distrib :=
      ENNReal.mul_rpow_of_nonneg (μN Set.univ) ((eLpNorm f p μ) ^ s₀.toReal) h_nonneg
    have h_cancel :
        ((eLpNorm f p μ) ^ s₀.toReal) ^ (1 / s₀.toReal) = eLpNorm f p μ := by
      rw [one_div, ← ENNReal.rpow_mul]
      have : s₀.toReal * s₀.toReal⁻¹ = 1 := by field_simp [hs₀_toReal_ne_zero]
      rw [this, ENNReal.rpow_one]
    -- Rewrite the RHS using the cancellation on the second factor
    have := h_distrib
    rw [h_cancel] at this
    exact this
  have h_target :
      eLpNorm A s₀ μN ≤ (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f p μ := by
    -- Transform via the previous equalities
    rw [← hL, ← hR]
    exact h_rpow_mono
  -- Since μ is a probability measure and μN ≤ μ, we have μN(univ) ≤ 1; hence the factor ≤ 1.
  -- However, obtain it directly via the measure inequality.
  have hμN_le_μ : (μN Set.univ) ≤ μ Set.univ :=
    (hμpartial_le N) Set.univ
  have hμ_univ_one : μ Set.univ = 1 := IsProbabilityMeasure.measure_univ (μ := μ)
  have hμN_le_one' : (μN Set.univ) ≤ 1 := by simpa [hμ_univ_one] using hμN_le_μ
  have hμN_pow_le_one : (μN Set.univ) ^ (1 / s₀.toReal) ≤ 1 := by
    have hbase : (μN Set.univ) ≤ 1 := hμN_le_one'
    have : (1 : ℝ≥0∞) ≤ 1 := le_rfl
    -- Monotonicity of rpow in the base for nonnegative exponents
    have hx := ENNReal.rpow_le_rpow hbase (by exact one_div_nonneg.mpr (le_of_lt hs₀_pos))
    simpa using hx
  -- Conclude the desired ENNReal inequality and pass to toReal using finiteness of ‖f‖_p.
  have h_en : eLpNorm A s₀ μN ≤ eLpNorm f p μ := by
    calc eLpNorm A s₀ μN
        ≤ (μN Set.univ) ^ (1 / s₀.toReal) * eLpNorm f p μ := h_target
      _ ≤ 1 * eLpNorm f p μ := by
          exact mul_le_mul_of_nonneg_right hμN_pow_le_one (by simp)
      _ = eLpNorm f p μ := by simp
  -- Finally, convert to toReal.
  have h_rhs_fin : eLpNorm f p μ ≠ ∞ := by simpa using hf.eLpNorm_ne_top
  exact ENNReal.toReal_mono h_rhs_fin h_en

end ConvolutionAuxiliary
