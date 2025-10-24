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

/-!
Auxiliary lemmas potentially needed for the limsup step.

We add only the statements here; proofs will be supplied where needed during
the main argument to keep this file’s flow focused.
-/

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

/-!
Exponent monotonicity on finite measure spaces.

On a finite measure space, for exponents `0 < p ≤ r < ∞`, one has the Lyapunov-type
inequality

  ‖f‖_p ≤ μ(univ)^(1/p - 1/r) · ‖f‖_r.

We provide a version specialized to complex-valued functions, phrased with `eLpNorm`.
This form is the one used in the p-norm–based redesign of the Young inequality proof.
-/
section ExponentMonotonicity

variable {α : Type*} [MeasurableSpace α]

lemma eLpNorm_exponent_mono_of_finite_measure
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℂ)
    (p r : ℝ≥0∞)
    (hp_le_hr : p ≤ r)
    (hf_meas : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ≤ (μ Set.univ) ^ (1 / p.toReal - 1 / r.toReal) * eLpNorm f r μ := by
  classical
  by_cases hμz : μ = 0
  · -- Trivial in the zero-measure case
    simp [hμz]
  · -- Use the general comparison lemma and commute the factors.
    simpa [mul_comm]
      using
        (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (μ := μ) (f := f) (p := p) (q := r) hp_le_hr hf_meas)

-- Dual direction (upper bound) on a finite measure space: for r ≤ p,
-- ‖f‖_r ≤ μ(univ)^(1/r - 1/p) · ‖f‖_p.
lemma eLpNorm_exponent_mono_upper_of_finite_measure
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℂ)
    (r p : ℝ≥0∞)
    (hr_le_hp : r ≤ p)
    (hf_meas : AEStronglyMeasurable f μ) :
    eLpNorm f r μ ≤ (μ Set.univ) ^ (1 / r.toReal - 1 / p.toReal) * eLpNorm f p μ := by
  classical
  by_cases hμz : μ = 0
  · simp [hμz]
  · -- Apply the same library lemma with (p := r) and (q := p).
    simpa [mul_comm]
      using
        (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (μ := μ) (f := f) (p := r) (q := p) hr_le_hp hf_meas)

end ExponentMonotonicity

variable {G α : Type*}

section ConvolutionAuxiliary

variable {G : Type*}
variable [MeasurableSpace G]
variable (μ : Measure G) [SFinite μ]

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
    [r.HolderTriple s p]
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

set_option maxHeartbeats 1000000 in
lemma lintegral_convolution_norm_bound
    (μ : Measure G) [SFinite μ] [NormedAddCommGroup G] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (f g : G → ℂ) (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 < q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hr_ne_top : r ≠ ∞)
    (hf : MemLp f p μ) (hf_r : MemLp f r μ) (hg : MemLp g q μ)
    (h_kernel_int :
      Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ))
    (h_pointwise_piece :
      ∀ N,
        (fun y =>
            (eLpNorm (fun x => f (x - y) * g y) r
              (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k)).toReal)
          =ᵐ[∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k]
          fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r
                (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k)).toReal) :
    ∫⁻ x, (ENNReal.ofReal (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ)) ^ r.toReal ∂ μ ≤
      (eLpNorm f p μ * eLpNorm g q μ) ^ r.toReal := by
  -- Start by extracting the exponent inequalities implied by `hp`, `hq`, and `hpqr`.
  have h_inv_p_le_one : p⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa [one_div] using (ENNReal.inv_le_inv).2 hp
  have h_inv_q_le_one : q⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa [one_div] using (ENNReal.inv_le_inv).2 (le_of_lt hq)
  have hpqr_inv : p⁻¹ + q⁻¹ = (1 : ℝ≥0∞) + r⁻¹ := by
    simpa [one_div, add_comm, add_left_comm, add_assoc] using hpqr
  have h_sum_le_two : p⁻¹ + q⁻¹ ≤ (1 : ℝ≥0∞) + 1 :=
    add_le_add h_inv_p_le_one h_inv_q_le_one
  have h_aux : (1 : ℝ≥0∞) + r⁻¹ ≤ (1 : ℝ≥0∞) + 1 := by
    simpa [hpqr_inv] using h_sum_le_two
  have h_inv_r_le_one : r⁻¹ ≤ (1 : ℝ≥0∞) :=
    ENNReal.le_of_add_le_add_left (by simp) h_aux
  have hr : 1 ≤ r :=
    (ENNReal.inv_le_inv).1 <| by simpa [one_div] using h_inv_r_le_one
  have hr_pos : (0 : ℝ≥0∞) < r := lt_of_lt_of_le (by simp) hr
  have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
  have hr_toReal_pos : 0 < r.toReal := ENNReal.toReal_pos hr_ne_zero hr_ne_top
  have hp_ne_top : p ≠ ∞ := by
    intro hp_top
    have h_eq : q⁻¹ = (1 : ℝ≥0∞) + r⁻¹ := by
      simpa [hp_top, one_div, ENNReal.inv_top, zero_add, add_comm, add_left_comm, add_assoc]
        using hpqr
    have h_le_one : (1 : ℝ≥0∞) + r⁻¹ ≤ 1 := by
      simpa [h_eq] using h_inv_q_le_one
    have h_le_one' : (1 : ℝ≥0∞) + r⁻¹ ≤ (1 : ℝ≥0∞) + 0 := by
      simpa using h_le_one
    have h_r_inv_le_zero : r⁻¹ ≤ (0 : ℝ≥0∞) :=
      (ENNReal.add_le_add_iff_left (by simp)).1 h_le_one'
    have h_zero_le : (0 : ℝ≥0∞) ≤ r⁻¹ := bot_le
    have h_r_inv_zero : r⁻¹ = 0 := le_antisymm h_r_inv_le_zero h_zero_le
    have hr_top : r = ∞ := ENNReal.inv_eq_zero.1 h_r_inv_zero
    exact hr_ne_top hr_top
  have hq_ne_top : q ≠ ∞ := by
    intro hq_top
    have h_eq : p⁻¹ = (1 : ℝ≥0∞) + r⁻¹ := by
      simpa [hq_top, one_div, ENNReal.inv_top, add_comm, add_left_comm, add_assoc]
        using hpqr
    have h_le_one : (1 : ℝ≥0∞) + r⁻¹ ≤ 1 := by
      simpa [h_eq, add_comm] using h_inv_p_le_one
    have h_le_one' : (1 : ℝ≥0∞) + r⁻¹ ≤ (1 : ℝ≥0∞) + 0 := by
      simpa using h_le_one
    have h_r_inv_le_zero : r⁻¹ ≤ (0 : ℝ≥0∞) :=
      (ENNReal.add_le_add_iff_left (by simp)).1 h_le_one'
    have h_zero_le : (0 : ℝ≥0∞) ≤ r⁻¹ := bot_le
    have h_r_inv_zero : r⁻¹ = 0 := le_antisymm h_r_inv_le_zero h_zero_le
    have hr_top : r = ∞ := ENNReal.inv_eq_zero.1 h_r_inv_zero
    exact hr_ne_top hr_top
  set pr := ENNReal.toReal p with hpr
  set qr := ENNReal.toReal q with hqr
  set rr := ENNReal.toReal r with hrr
  have h_young_real :
      rr =
        (pr * qr) /
          (pr + qr - pr * qr) := by
    have :=
      young_exponent_relation
        (p := p) (q := q) (r := r)
        hp (le_of_lt hq) hr hpqr hp_ne_top hq_ne_top hr_ne_top
    simpa [hpr, hqr, hrr] using this
  have h_section_int :
      ∀ᵐ x ∂μ, Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ :=
    integrable_norm_convolution_kernel_section
      (μ := μ) (f := f) (g := g) h_kernel_int

  classical
  set H : G → ℝ := fun x => ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μ
  have h_H_nonneg :
      ∀ᵐ x ∂μ, 0 ≤ H x := by
    refine h_section_int.mono ?_
    intro x _
    have h_nonneg_fun :
        0 ≤ᵐ[μ] fun y => ‖f (x - y)‖ * ‖g y‖ :=
      Filter.Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa [H] using integral_nonneg_of_ae h_nonneg_fun

  set μn : ℕ → Measure G := MeasureTheory.sfiniteSeq μ
  have hμ_sum : Measure.sum μn = μ := MeasureTheory.sum_sfiniteSeq μ
  let μpartial : ℕ → Measure G := fun N => ∑ k ∈ Finset.range (N + 1), μn k
  have hμpartial_succ :
      ∀ N, μpartial (N + 1) = μpartial N + μn (N + 1) := by
    intro N
    classical
    simp [μpartial, Nat.succ_eq_add_one, Finset.range_succ, add_comm, add_left_comm, add_assoc]
  have hμpartial_zero : μpartial 0 = μn 0 := by
    classical
    simp [μpartial]
  have hμn_le : ∀ n, μn n ≤ μ := fun n =>
    by
      simpa [μn] using MeasureTheory.sfiniteSeq_le (μ := μ) n
  have hμpartial_fin : ∀ N, IsFiniteMeasure (μpartial N) := by
    intro N
    classical
    refine Nat.rec ?base ?step N
    · simpa [μpartial] using (inferInstance : IsFiniteMeasure (μn 0))
    · intro k hk
      have hk' : IsFiniteMeasure (μpartial k + μn (k + 1)) := by infer_instance
      simpa [hμpartial_succ, Nat.succ_eq_add_one] using hk'
  have hμpartial_le_succ : ∀ N, μpartial N ≤ μpartial (N + 1) := by
    intro N s
    classical
    have hnonneg : 0 ≤ μn (N + 1) s := bot_le
    simp [hμpartial_succ, Nat.succ_eq_add_one, Measure.add_apply, hnonneg]
  have hμpartial_mono : Monotone μpartial :=
    monotone_nat_of_le_succ hμpartial_le_succ
  have hμpartial_le_smul :
      ∀ N, μpartial N ≤ ((N + 1 : ℝ≥0∞) • μ) := by
    intro N
    simpa [μpartial] using (sfiniteSeq_partial_le_smul (μ := μ) N)
  have hμpartial_ac : ∀ N, μpartial N ≪ μ := by
    intro N
    exact Measure.absolutelyContinuous_of_le_smul (hμpartial_le_smul N)
  have hμpartial_tendsto :
      ∀ ⦃s : Set G⦄, MeasurableSet s →
        Tendsto (fun N => μpartial N s) atTop (𝓝 (μ s)) := by
    exact sfiniteSeq_partial_tendsto (μ := μ)
  have hμpartial_prod_le :
      ∀ N,
        (μpartial N).prod (μpartial N) ≤
          (((N + 1 : ℝ≥0∞) * (N + 1 : ℝ≥0∞)) • (μ.prod μ)) := by
    intro N
    simpa [μpartial, μn]
      using (sfiniteSeq_partial_prod_le_smul (μ := μ) N)
  have hμpartial_prod_ac :
      ∀ N, (μpartial N).prod (μpartial N) ≪ μ.prod μ := by
    intro N
    exact Measure.absolutelyContinuous_of_le_smul (hμpartial_prod_le N)
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
  have h_translate_norm_bound :
      ∀ N y,
        eLpNorm (fun x => f (x - y)) r (μpartial N) ≤
          ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ := by
    intro N y
    exact
      sfiniteSeq_partial_translate_norm_bound
        (μ := μ)
        (f := f)
        (μpartial := μpartial)
        (hf := hf_r)
        (h_le := hμpartial_le_smul)
        N y
  have h_translate_norm_bound_toReal :
      ∀ N y,
        (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ≤
          ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal := by
    intro N y
    have h_bound := h_translate_norm_bound N y
    have h_pow_ne_top :
        ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ := by
      have h_exp_nonneg : 0 ≤ (1 / r).toReal := by simp [one_div]
      exact ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
    have h_const_ne_top :
        ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ :=
      ENNReal.mul_ne_top h_pow_ne_top hf_r.eLpNorm_ne_top
    exact ENNReal.toReal_mono h_const_ne_top h_bound
  have hg_partial : ∀ N, MemLp g q (μpartial N) := by
    intro N
    refine hg.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
    · simp [Nat.succ_eq_add_one]
    · simpa using hμpartial_le_smul N
  have h_pointwise_piece_partial :
      ∀ N,
        (fun y =>
            (eLpNorm (fun x => f (x - y) * g y) r (μpartial N)).toReal)
          =ᵐ[μpartial N]
          fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
    intro N
    simpa [μpartial, μn] using h_pointwise_piece N
  have hg_partial_one : ∀ N, MemLp g 1 (μpartial N) := by
    intro N
    exact (hg_partial N).mono_exponent (p := (1 : ℝ≥0∞)) (q := q) (le_of_lt hq)
  have hg_partial_int : ∀ N, Integrable g (μpartial N) := by
    intro N
    exact (memLp_one_iff_integrable).1 (hg_partial_one N)

  -- Preparatory bounds for the finite-measure pieces
  have h_kernel_int_partial :
      ∀ N,
        Integrable (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)) := by
    intro N
    classical
    have h_const_ne_top :
        ((N + 1 : ℝ≥0∞) * (N + 1 : ℝ≥0∞)) ≠ ∞ := by
      simpa using
        ENNReal.mul_ne_top (by simp) (by simp)
    refine
      Integrable.of_measure_le_smul
        (μ := μ.prod μ)
        (μ' := (μpartial N).prod (μpartial N))
        (f := fun q : G × G => f (q.1 - q.2) * g q.2)
        h_const_ne_top (hμpartial_prod_le N) ?_
    simpa using h_kernel_int

  have h_kernel_meas_partial :
      ∀ N,
        AEStronglyMeasurable
          (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)) := by
    intro N
    exact
      (h_kernel_int.aestronglyMeasurable.mono_ac (hμpartial_prod_ac N))

  have h_kernel_fiber_int_partial :
      ∀ N, ∀ᵐ x ∂ μpartial N,
        Integrable (fun y => f (x - y) * g y) (μpartial N) := by
    intro N
    have h :=
      Integrable.prod_right_ae
        (μ := μpartial N) (ν := μpartial N)
        (h_kernel_int_partial N)
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx

  have hμpartial_def :
      ∀ N, μpartial N = ∑ k ∈ Finset.range (N + 1), μn k := fun _ => rfl

  have hμpartial_le :
      ∀ N, μpartial N ≤ μ :=
    sfiniteSeq_partial_le_measure
      (μ := μ)
      (μn := μn)
      (μpartial := μpartial)
      (hμ_sum := hμ_sum)
      (hμpartial_def := hμpartial_def)

  classical
  let Hpartial : ℕ → G → ℝ :=
    fun N x => ∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μpartial N

  have h_integrability_all :
      ∀ᵐ x ∂ μ,
        Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ ∧
          ∀ N,
            Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) (μpartial N) := by
    refine h_section_int.mono ?_
    intro x hx
    refine ⟨hx, ?_⟩
    intro N
    have h_const_ne_top :
        ((N + 1 : ℝ≥0∞)) ≠ ∞ := by simp
    exact
      Integrable.of_measure_le_smul
        (μ := μ) (μ' := μpartial N)
        (f := fun y => ‖f (x - y)‖ * ‖g y‖)
        h_const_ne_top
        (hμpartial_le_smul N)
        hx

  have h_Hpartial_mono :
      ∀ᵐ x ∂ μ, Monotone fun N => Hpartial N x := by
    refine h_integrability_all.mono ?_
    intro x hx
    rcases hx with ⟨hxμ, hx_partial⟩
    intro N M hNM
    have h_meas_le : μpartial N ≤ μpartial M := hμpartial_mono hNM
    haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
    haveI : IsFiniteMeasure (μpartial M) := hμpartial_fin M
    exact
      integral_norm_mul_mono
        (μ₁ := μpartial N) (μ₂ := μpartial M)
        f g x h_meas_le (hx_partial M)

  have h_Hpartial_le_H :
      ∀ᵐ x ∂ μ, ∀ N, Hpartial N x ≤ H x := by
    refine h_integrability_all.mono ?_
    intro x hx
    rcases hx with ⟨hxμ, hx_partial⟩
    intro N
    have h_meas_le : μpartial N ≤ μ := hμpartial_le N
    haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
    exact
      integral_norm_mul_mono
        (μ₁ := μpartial N) (μ₂ := μ)
        f g x h_meas_le hxμ

  have h_Hpartial_tendsto :
      ∀ᵐ x ∂ μ, Tendsto (fun N => Hpartial N x) atTop (𝓝 (H x)) := by
    refine h_integrability_all.mono ?_
    intro x hx
    rcases hx with ⟨hxμ, hx_partial⟩
    have h_tendsto := hpartial_tendsto_of_integrability_all
      (μ := μ) (f := f) (g := g) (x := x)
      (hx := hxμ)
    simp [Hpartial] at h_tendsto
    exact h_tendsto
  have h_H_pow_eq :
      ∀ᵐ x ∂ μ,
        ‖H x‖ₑ ^ r.toReal = (ENNReal.ofReal (H x)) ^ r.toReal := by
    refine h_H_nonneg.mono ?_
    intro x hx
    have hx_abs : ENNReal.ofReal ‖H x‖ = ENNReal.ofReal (H x) := by
      simp [Real.norm_eq_abs, abs_of_nonneg hx]
    have hx_pow := congrArg (fun t : ℝ≥0∞ => t ^ r.toReal) hx_abs
    have hx_coe : ‖H x‖ₑ = ENNReal.ofReal ‖H x‖ := by
      simpa using (ofReal_norm_eq_enorm (H x)).symm
    simp [hx_coe, Real.norm_eq_abs, abs_of_nonneg hx]
  have h_H_lintegral_eq :
      ∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ
        = ∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ := by
    refine lintegral_congr_ae h_H_pow_eq
  have h_eLpNorm_H :=
    eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := H) hr_ne_zero hr_ne_top
  have h_eLpNorm' :
      eLpNorm H r μ =
        (∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ) ^ r.toReal⁻¹ := by
    simpa [one_div] using h_eLpNorm_H
  have hr_toReal_pos' : 0 < r.toReal :=
    ENNReal.toReal_pos hr_ne_zero hr_ne_top
  have h_H_lintegral_repr :
      (eLpNorm H r μ) ^ r.toReal
        = ∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ := by
    have h_nonzero : r.toReal ≠ 0 := ne_of_gt hr_toReal_pos'
    have h_mul : r.toReal⁻¹ * r.toReal = 1 := by
      simp [one_div, h_nonzero]
    have h_pow :=
      congrArg (fun t : ℝ≥0∞ => t ^ r.toReal) h_eLpNorm'
    have h_rhs :
        ((∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ) ^ r.toReal⁻¹) ^ r.toReal
          = ∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ := by
      simpa [ENNReal.rpow_mul, h_mul]
        using
          (ENNReal.rpow_mul
            (∫⁻ x, ‖H x‖ₑ ^ r.toReal ∂ μ)
            r.toReal⁻¹
            r.toReal).symm
    have h_repr := h_pow.trans h_rhs
    simpa [h_H_lintegral_eq] using h_repr
  have h_kernel_norm_meas :
      AEStronglyMeasurable
        (fun q : G × G => ‖f (q.1 - q.2) * g q.2‖) (μ.prod μ) :=
    (convolution_kernel_aestronglyMeasurable (μ := μ)
      (f := f) (g := g) hf.aestronglyMeasurable hg.aestronglyMeasurable).norm
  have h_kernel_norm_meas_partial :
      ∀ N,
        AEStronglyMeasurable
          (fun q : G × G => ‖f (q.1 - q.2) * g q.2‖)
          (μ.prod (μpartial N)) := by
    intro N
    have h_ac : μ.prod (μpartial N) ≪ μ.prod μ :=
      Measure.AbsolutelyContinuous.rfl.prod (hμpartial_ac N)
    exact (h_kernel_norm_meas.mono_ac h_ac)
  have h_H_meas : AEStronglyMeasurable H μ := by
    simpa [H, norm_mul, mul_comm, mul_left_comm, mul_assoc]
      using h_kernel_norm_meas.integral_prod_right'
  have h_Hpartial_meas :
      ∀ N, AEStronglyMeasurable (fun x => Hpartial N x) μ := by
    intro N
    simpa [Hpartial, norm_mul, mul_comm, mul_left_comm, mul_assoc]
      using (h_kernel_norm_meas_partial N).integral_prod_right'
  have h_H_pow_meas :
      AEMeasurable (fun x => (ENNReal.ofReal (H x)) ^ r.toReal) μ := by
    have h_ofReal :
        AEMeasurable (fun x => ENNReal.ofReal (H x)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable h_H_meas.aemeasurable
    exact
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable h_ofReal)
  have h_Hpartial_pow_meas :
      ∀ N,
        AEMeasurable (fun x => (ENNReal.ofReal (Hpartial N x)) ^ r.toReal) μ := by
    intro N
    have h_ofReal :
        AEMeasurable (fun x => ENNReal.ofReal (Hpartial N x)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable (h_Hpartial_meas N).aemeasurable
    exact
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable h_ofReal)
  have h_Hpartial_nonneg :
      ∀ᵐ x ∂ μ, ∀ N, 0 ≤ Hpartial N x := by
    refine h_integrability_all.mono ?_
    intro x hx
    rcases hx with ⟨hxμ, hx_partial⟩
    intro N
    have h_nonneg_fun :
        0 ≤ᵐ[μpartial N] fun y => ‖f (x - y)‖ * ‖g y‖ :=
      Filter.Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h_nonneg :=
      integral_nonneg_of_ae (μ := μpartial N) (f := fun y => ‖f (x - y)‖ * ‖g y‖) h_nonneg_fun
    simpa [Hpartial] using h_nonneg
  have h_Hpartial_pow_mono :
      ∀ᵐ x ∂ μ,
        Monotone fun N =>
          (ENNReal.ofReal (Hpartial N x)) ^ r.toReal := by
    refine (h_Hpartial_mono.and h_Hpartial_nonneg).mono ?_
    intro x hx
    rcases hx with ⟨h_mono, -⟩
    intro N M hNM
    have h_le := ENNReal.ofReal_le_ofReal (h_mono hNM)
    exact ENNReal.rpow_le_rpow h_le (by have := ENNReal.toReal_nonneg (a := r); simp)
  have h_Hpartial_pow_tendsto :
      ∀ᵐ x ∂ μ,
        Tendsto (fun N => (ENNReal.ofReal (Hpartial N x)) ^ r.toReal) atTop
          (𝓝 ((ENNReal.ofReal (H x)) ^ r.toReal)) := by
    refine (h_Hpartial_tendsto.and h_H_nonneg).mono ?_
    intro x hx
    rcases hx with ⟨hx_tendsto, -⟩
    have h_ofReal_tendsto :
        Tendsto (fun N => ENNReal.ofReal (Hpartial N x)) atTop
          (𝓝 (ENNReal.ofReal (H x))) :=
      (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hx_tendsto
    have h_pow_tendsto :
        Tendsto (fun N => (ENNReal.ofReal (Hpartial N x)) ^ r.toReal) atTop
          (𝓝 ((ENNReal.ofReal (H x)) ^ r.toReal)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h_ofReal_tendsto
    simpa using h_pow_tendsto
  let g_pow : G → ℝ≥0∞ := fun x => (ENNReal.ofReal (H x)) ^ r.toReal
  have h_lintegral_Hpartial_partial :
      ∀ N,
        ∫⁻ x, g_pow x ∂ μpartial N =
          ∑ k ∈ Finset.range (N + 1),
            ∫⁻ x, g_pow x ∂ μn k := by
    intro N
    classical
    simp [g_pow, μpartial]
  have h_lintegral_Hpartial_sum :
      (∑' k, ∫⁻ x, g_pow x ∂ μn k) = ∫⁻ x, g_pow x ∂ μ := by
    classical
    simpa [g_pow, hμ_sum]
      using
        (MeasureTheory.lintegral_sum_measure
          (μ := μn)
          (f := fun x : G => g_pow x)).symm
  have h_lintegral_Hpartial_mono :
      Monotone (fun N => ∫⁻ x, g_pow x ∂ μpartial N) := by
    intro N M hNM
    exact lintegral_mono' (hμpartial_mono hNM) fun _ => le_rfl
  have h_lintegral_Hpartial_tendsto :
      Tendsto (fun N => ∫⁻ x, g_pow x ∂ μpartial N) atTop
        (𝓝 (∫⁻ x, g_pow x ∂ μ)) := by
    classical
    have h_series_tendsto :
        Tendsto
          (fun N =>
            ∑ k ∈ Finset.range (N + 1),
              ∫⁻ x, g_pow x ∂ μn k)
          atTop
          (𝓝 (∑' k, ∫⁻ x, g_pow x ∂ μn k)) := by
      exact
        (ENNReal.tendsto_nat_tsum
          (f := fun k => ∫⁻ x, g_pow x ∂ μn k)).comp
          (tendsto_add_atTop_nat 1)
    have h_eval :
        (fun N => ∫⁻ x, g_pow x ∂ μpartial N)
          = fun N =>
              ∑ k ∈ Finset.range (N + 1),
                ∫⁻ x, g_pow x ∂ μn k := by
      funext N
      exact h_lintegral_Hpartial_partial N
    have h_eval' :
        (∑' k, ∫⁻ x, g_pow x ∂ μn k)
          = ∫⁻ x, g_pow x ∂ μ :=
      h_lintegral_Hpartial_sum
    simpa [h_eval, h_eval'] using h_series_tendsto
  have h_kernel_int_piece :
      ∀ N,
        Integrable
          (fun q : G × G => f (q.1 - q.2) * g q.2) ((μpartial N).prod (μpartial N)) := by
    simpa using h_kernel_int_partial
  have h_kernel_meas_piece :
      ∀ N,
        AEStronglyMeasurable
          (fun q : G × G => f (q.1 - q.2) * g q.2)
          ((μpartial N).prod (μpartial N)) := by
    intro N
    exact h_kernel_meas_partial N
  have h_kernel_fiber_int_piece :
      ∀ N, ∀ᵐ y ∂ μpartial N,
        Integrable (fun x => f (x - y) * g y) (μpartial N) := by
    intro N
    have h :=
      Integrable.prod_left_ae (μ := μpartial N) (ν := μpartial N)
        (h_kernel_int_partial N)
    refine h.mono ?_
    intro y hy
    simpa [sub_eq_add_neg] using hy
  have h_kernel_fiber_mem_piece :
      ∀ N, ∀ᵐ y ∂ μpartial N,
        MemLp (fun x => f (x - y) * g y) r (μpartial N) := by
    intro N
    have h :=
      convolution_kernel_fiber_memLp_of_memLp (μ := μ)
        (p := r) (q := q) hf_r hg
    have h_dom :
        ∀ᵐ y ∂ μ,
          MemLp (fun x => f (x - y) * g y) r (μpartial N) := by
      refine h.mono ?_
      intro y hy
      refine hy.of_measure_le_smul (μ' := μpartial N) (c := (N + 1 : ℝ≥0∞)) ?_ ?_
      · simp [Nat.succ_eq_add_one]
      · simpa using hμpartial_le_smul N
    have h_zero :=
      (ae_iff).1 h_dom
    have h_zero' :=
      (hμpartial_ac N) h_zero
    exact (ae_iff).2 <| by
      simpa using h_zero'
  have h_norm_piece :
      ∀ N,
        Integrable
          (fun y =>
              ‖g y‖ *
                (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal)
          (μpartial N) := by
    intro N
    exact
      sfiniteSeq_partial_integrable_norm_mul
        (μ := μ)
        (hr := hr)
        (hr_ne_top := hr_ne_top)
        (f := f)
        (g := g)
        (μpartial := μpartial)
        (hf := hf_r)
        (hg_partial_int := hg_partial_int)
        (hμpartial_fin := hμpartial_fin)
        (hμpartial_prod_ac := hμpartial_prod_ac)
        (h_translate_norm_bound_toReal := h_translate_norm_bound_toReal)
        N
  have h_convPiece_def :
      ∀ N,
        (fun x => ∫ y, f (x - y) * g y ∂ μpartial N)
          = fun x => ∫ y, f (x - y) * g y ∂ μpartial N := by
    intro N; rfl
  have h_conv_piece_bound :
      ∀ N,
        eLpNorm
            (fun x => ∫ y, f (x - y) * g y ∂ μpartial N) r (μpartial N)
          ≤
        ENNReal.ofReal
          (∫ y, ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N) := by
    intro N
    have h_minkowski :=
      minkowski_inequality_convolution_complex
        (μ := μpartial N)
        (f := f) (g := g) (p := r)
        hr hr_ne_top
        (h_kernel_meas_piece N)
        (h_kernel_int_piece N)
        (h_kernel_fiber_int_piece N)
        (h_kernel_fiber_mem_piece N)
        (h_norm_piece N)
    simpa [h_convPiece_def N, sub_eq_add_neg,
      integral_congr_ae (h_pointwise_piece_partial N)]
      using h_minkowski
  -- Translate the previous `L^r` bound into a bound on the lintegral of the truncated
  -- Lemma: For complex-valued functions, eLpNorm of the norm equals eLpNorm of the function
  have eLpNorm_norm_eq_of_complex {μ' : Measure G} (h : G → ℂ) (p : ℝ≥0∞) :
      eLpNorm (fun x => ‖h x‖) p μ' = eLpNorm h p μ' := by
    simp

  -- Utility: expand `ENNReal.ofReal` over a triple product of nonnegative reals.
  -- This avoids fragile associativity/commutativity issues when rewriting large products.
  have ofReal_mul_three {a b c : ℝ}
      (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      ENNReal.ofReal (a * b * c)
        = ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c := by
    simp [ENNReal.ofReal_mul, ha, hb, hc, mul_comm, mul_left_comm, mul_assoc]

  -- convolution norms.
  have h_conv_lintegral_bound :
      ∀ N,
        ∫⁻ x,
            (ENNReal.ofReal
              (∫ y, ‖f (x - y)‖ * ‖g y‖ ∂ μpartial N)) ^ r.toReal ∂ μpartial N
          ≤
        (ENNReal.ofReal
            (∫ y, ‖g y‖ *
                (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N)) ^ r.toReal := by
    intro N
    haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
    let f_norm : G → ℝ := fun x => ‖f x‖
    let g_norm : G → ℝ := fun x => ‖g x‖
    have h_meas :
        AEStronglyMeasurable
          (fun q : G × G => f_norm (q.1 - q.2) * g_norm q.2)
          ((μpartial N).prod (μpartial N)) := by
      -- We need to show measurability of the product of norms
      simp only [f_norm, g_norm]
      -- Using the fact that norms preserve measurability and that the kernel is measurable
      have : AEStronglyMeasurable (fun q : G × G => ‖f (q.1 - q.2) * g q.2‖)
          ((μpartial N).prod (μpartial N)) := (h_kernel_meas_piece N).norm
      -- Now we need to show that ‖f(q.1 - q.2) * g(q.2)‖ = ‖f(q.1 - q.2)‖ * ‖g(q.2)‖ a.e.
      convert this using 1
      ext q
      simp only [norm_mul]
    have h_prod :
        Integrable
          (fun q : G × G => f_norm (q.1 - q.2) * g_norm q.2)
          ((μpartial N).prod (μpartial N)) := by
      have := (h_kernel_int_piece N).norm
      simpa [f_norm, g_norm, norm_mul, mul_comm, mul_left_comm, mul_assoc] using this
    have h_int :
        ∀ᵐ y ∂ μpartial N,
          Integrable (fun x => f_norm (x - y) * g_norm y) (μpartial N) := by
      refine (h_kernel_fiber_int_piece N).mono ?_
      intro y hy
      have hy_norm := hy.norm
      simpa [f_norm, g_norm, norm_mul, mul_comm, mul_left_comm, mul_assoc] using hy_norm
    have h_memLp :
        ∀ᵐ y ∂ μpartial N,
          MemLp (fun x => f_norm (x - y) * g_norm y) r (μpartial N) := by
      refine (h_kernel_fiber_mem_piece N).mono ?_
      intro y hy
      have hy_norm := hy.norm
      simpa [f_norm, g_norm, norm_mul, mul_comm, mul_left_comm, mul_assoc] using hy_norm
    have h_scaling :
        ∀ y : G,
          eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N) =
            ENNReal.ofReal (g_norm y) *
              eLpNorm (fun x => f_norm (x - y)) r (μpartial N) := by
      intro y
      simpa [f_norm, g_norm, smul_eq_mul, mul_comm]
        using
          (eLpNorm_const_smul (μ := μpartial N) (p := r)
            (c := g_norm y) (f := fun x => f_norm (x - y)))
    have h_norm :
        Integrable
          (fun y =>
            (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal)
          (μpartial N) := by
      have h_pointwise :
          (fun y =>
              (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal)
            =ᵐ[μpartial N]
          fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
        refine Filter.Eventually.of_forall ?_
        intro y
        have h_eq := h_scaling y
        have h_toReal := congrArg ENNReal.toReal h_eq
        have hg_nonneg : 0 ≤ g_norm y := by exact norm_nonneg _
        have hf_eq :
            eLpNorm (fun x => f_norm (x - y)) r (μpartial N) =
              eLpNorm (fun x => f (x - y)) r (μpartial N) := by
          simp only [f_norm]
          exact eLpNorm_norm_eq_of_complex (fun x => f (x - y)) r
        simpa [f_norm, g_norm, hf_eq, ENNReal.toReal_mul, hg_nonneg]
          using h_toReal
      have h_norm' := h_norm_piece N
      exact h_norm'.congr h_pointwise.symm
    -- Apply Minkowski inequality for convolutions
    -- Note: μpartial N may not have IsAddRightInvariant property
    -- FIXME: Need to either prove μpartial N has this property or use alternative approach
    have h_minkowski :
        eLpNorm (fun x => ∫ y, f_norm (x - y) * g_norm y ∂(μpartial N)) r (μpartial N) ≤
        ENNReal.ofReal (∫ y, |g_norm y| * (eLpNorm (fun x =>
        f_norm (x - y)) r (μpartial N)).toReal ∂(μpartial N)) := by
      haveI : SFinite (μpartial N) := inferInstance
      have h_raw :
          eLpNorm
              (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N) r (μpartial N) ≤
            ENNReal.ofReal
              (∫ y,
                  (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal
                ∂ μpartial N) := by
        refine
          minkowski_integral_inequality
            (μ := μpartial N) (ν := μpartial N) (p := r)
            hr hr_ne_top (fun x y => f_norm (x - y) * g_norm y)
            ?_ ?_ ?_ ?_ ?_
        · simpa using h_meas
        · simpa using h_prod
        · simpa using h_int
        · simpa using h_memLp
        · simpa using h_norm
      have h_integrand_eq :
          (fun y =>
              (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal)
            =ᵐ[μpartial N]
          fun y =>
            |g_norm y| *
              (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal := by
        refine Filter.Eventually.of_forall ?_
        intro y
        have hg_nonneg : 0 ≤ g_norm y := norm_nonneg _
        have hy_toReal :=
          congrArg ENNReal.toReal (h_scaling y)
        have hy_base :
            (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal =
              g_norm y *
                (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal := by
          simpa [ENNReal.toReal_mul, g_norm, hg_nonneg] using hy_toReal
        have hy_abs :
            (eLpNorm (fun x => f_norm (x - y) * g_norm y) r (μpartial N)).toReal =
              |g_norm y| *
                (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal := by
          simpa [abs_of_nonneg hg_nonneg] using hy_base
        simpa using hy_abs
      have h_integral_congr :=
        integral_congr_ae h_integrand_eq
      simpa [h_integral_congr] using h_raw
    have h_eLpNorm_bound :
        eLpNorm
            (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N) r (μpartial N)
          ≤
        ENNReal.ofReal
          (∫ y, ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N) := by
      have h_abs :
          (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N)
            = fun x => Hpartial N x := by
        funext x
        simp [Hpartial, f_norm, g_norm, mul_comm, mul_left_comm, mul_assoc]
      have h_rhs :
          (fun y => |g_norm y| * (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal)
            =ᵐ[μpartial N]
          fun y =>
            ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
        refine Filter.Eventually.of_forall ?_
        intro y
        have hg_nonneg : 0 ≤ g_norm y := by exact norm_nonneg _
        have hf_eq :
            eLpNorm (fun x => f_norm (x - y)) r (μpartial N) =
              eLpNorm (fun x => f (x - y)) r (μpartial N) := by
          simp only [f_norm]
          exact eLpNorm_norm_eq_of_complex (fun x => f (x - y)) r
        simp [f_norm, g_norm, hf_eq, abs_of_nonneg hg_nonneg]
      have h_eq1 : ENNReal.ofReal
                  (∫ y,
                      |g_norm y| *
                        (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal ∂ μpartial N)
                =
              ENNReal.ofReal
                  (∫ y,
                      ‖g y‖ *
                        (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N) := by
            exact congrArg ENNReal.ofReal
              (integral_congr_ae h_rhs)
      have h_eq2 : (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N)
                = fun x => Hpartial N x := h_abs
      -- Combine the inequalities and equalities
      calc eLpNorm (fun x => Hpartial N x) r (μpartial N)
        = eLpNorm (fun x => ∫ y, f_norm (x - y) * g_norm y ∂ μpartial N) r (μpartial N) :=
          by rw [← h_eq2]
        _ ≤ ENNReal.ofReal (∫ y, |g_norm y| *
          (eLpNorm (fun x => f_norm (x - y)) r (μpartial N)).toReal ∂(μpartial N)) := h_minkowski
        _ = ENNReal.ofReal (∫ y, ‖g y‖ * (eLpNorm (fun x =>
          f (x - y)) r (μpartial N)).toReal ∂(μpartial N)) := by rw [h_eq1]
    have h_nonneg :
        ∀ᵐ x ∂ μpartial N, 0 ≤ Hpartial N x := by
      apply (hμpartial_ac N).ae_le
      filter_upwards [h_integrability_all] with x hx
      -- Use that Hpartial N x is the integral of a non-negative function
      simp only [Hpartial]
      apply integral_nonneg
      intro y
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    -- Relate the eLpNorm to the lintegral of the r-th power
    have h_pow :
        (∫⁻ x, (ENNReal.ofReal (Hpartial N x)) ^ r.toReal ∂ μpartial N)
          =
        (eLpNorm (fun x => Hpartial N x) r (μpartial N)) ^ r.toReal := by
      -- Use the fact that for non-negative functions, eLpNorm^p = ∫⁻ |f|^p
      have h_eq := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
          (μ := μpartial N)
          (f := fun x => Hpartial N x)
          (p := r)
          hr_ne_zero
          hr_ne_top
      -- For non-negative real functions, ‖x‖ₑ = ENNReal.ofReal x when x ≥ 0
      have h_norm_eq : ∀ᵐ x ∂(μpartial N), ‖Hpartial N x‖ₑ = ENNReal.ofReal (Hpartial N x) := by
        filter_upwards [h_nonneg] with x hx
        simp [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs, abs_of_nonneg hx]
      -- Use the rpow property to relate the expressions
      have h_integral_eq :
          (∫⁻ x, ENNReal.ofReal (Hpartial N x) ^ r.toReal ∂ μpartial N) =
            ∫⁻ x, ‖Hpartial N x‖ₑ ^ r.toReal ∂ μpartial N := by
        refine lintegral_congr_ae ?_
        filter_upwards [h_norm_eq] with x hx
        simp [hx]
      have h_pow' :
          (eLpNorm (fun x => Hpartial N x) r (μpartial N)) ^ r.toReal =
            ∫⁻ x, ‖Hpartial N x‖ₑ ^ r.toReal ∂ μpartial N := by
        have hrtoReal_ne_zero : r.toReal ≠ 0 := ne_of_gt hr_toReal_pos'
        have := congrArg (fun t : ℝ≥0∞ => t ^ r.toReal) h_eq
        simpa [ENNReal.rpow_mul, one_div, hrtoReal_ne_zero, mul_comm, mul_left_comm, mul_assoc]
          using this
      exact h_integral_eq.trans h_pow'.symm
    -- We need to raise both sides to the r-th power
    have h_pow_bound : eLpNorm (fun x => Hpartial N x) r (μpartial N) ^ r.toReal ≤
        ENNReal.ofReal (∫ y, ‖g y‖ * (eLpNorm (fun x =>
        f (x - y)) r (μpartial N)).toReal ∂(μpartial N)) ^ r.toReal := by
      simp only [Hpartial, f_norm, g_norm] at h_eLpNorm_bound
      exact ENNReal.rpow_le_rpow h_eLpNorm_bound (ENNReal.toReal_nonneg)
    have h_final := (le_of_eq h_pow).trans h_pow_bound
    exact h_final
  -- Combine the lintegral bound with Step 4 convergence data to control
  -- the limit superior in Step 6.
  -- Notation for the key sequences appearing in Step 6.
  classical
  set Φ :
      ℕ → ℝ≥0∞ :=
    fun N =>
      ∫⁻ x, (ENNReal.ofReal (Hpartial N x)) ^ r.toReal ∂ μpartial N
    with hΦ_def
  set Ψ :
      ℕ → ℝ≥0∞ :=
    fun N =>
      (ENNReal.ofReal
          (∫ y, ‖g y‖ *
              (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ∂ μpartial N)) ^
        r.toReal
    with hΨ_def
  have h_limsup_control :
      (∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ)
        ≤ Filter.limsup Φ Filter.atTop := by
    classical
    let f_seq : ℕ → G → ℝ≥0∞ :=
      fun N x => (ENNReal.ofReal (Hpartial N x)) ^ r.toReal
    have hΦ_eq :
        ∀ N,
          Φ N =
            ∫⁻ x,
              f_seq N x ∂
                (∑ k ∈ Finset.range (N + 1), MeasureTheory.sfiniteSeq μ k) := by
      intro N
      simp [Φ, hΦ_def, f_seq, μpartial, μn]
    have hf_meas :
        ∀ N, AEMeasurable (f_seq N) μ := by
      intro N
      simpa [f_seq] using h_Hpartial_pow_meas N
    have hf_mono :
        ∀ᵐ x ∂ μ, Monotone fun N => f_seq N x := by
      simpa [f_seq] using h_Hpartial_pow_mono
    have hf_tendsto :
        ∀ᵐ x ∂ μ, Tendsto (fun N => f_seq N x) atTop (𝓝 (g_pow x)) := by
      simpa [f_seq, g_pow] using h_Hpartial_pow_tendsto
    simpa [g_pow, f_seq] using
      (limsup_control_aux
        (μ := μ)
        (g_pow := g_pow)
        (Φ := Φ)
        (f_seq := f_seq)
        (hΦ := hΦ_eq)
        (hf_meas := hf_meas)
        (hf_mono := hf_mono)
        (hf_tendsto := hf_tendsto))
  have h_limsup_compare :
      Filter.limsup Φ Filter.atTop ≤ Filter.limsup Ψ Filter.atTop := by
    refine Filter.limsup_le_limsup ?_
    exact
      Filter.Eventually.of_forall fun N =>
        by
          simpa [Φ, Ψ, hΦ_def, hΨ_def]
            using h_conv_lintegral_bound N
  have h_limsup_goal :
      (∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ)
        ≤ Filter.limsup Ψ Filter.atTop :=
    le_trans h_limsup_control h_limsup_compare
  -- Prepare the conjugate exponent s₀ of q and the Young split 1/p = 1/r + 1/s₀.
  have hq_lt_top : q < ∞ := lt_of_le_of_ne le_top hq_ne_top
  obtain ⟨s₀, hs₀_conj, hs₀_eq⟩ :=
    conjugate_exponent_formula (p := q) (by exact hq) (by exact hq_lt_top)
  have h_split : 1 / p = 1 / r + 1 / s₀ := by
    simpa [hs₀_eq] using
      inv_p_eq_inv_r_add_inv_conj p q r hp hq hpqr hr_ne_top
  -- Basic bounds for the conjugate exponent s₀.
  have hs₀_bounds :=
    conjugate_exponent_bounds (p := q) (q := s₀) hs₀_conj hq hq_lt_top
  have hs₀_one_lt : 1 < s₀ := hs₀_bounds.1
  have hs₀_lt_top : s₀ < ∞ := hs₀_bounds.2
  have hs₀_ne_top : s₀ ≠ ∞ := ne_of_lt hs₀_lt_top
  have hs₀_ne_zero : s₀ ≠ 0 := by
    have : (0 : ℝ≥0∞) < s₀ := lt_trans (by simp) hs₀_one_lt
    exact ne_of_gt this
  have hs₀_toReal_pos : 0 < s₀.toReal :=
    ENNReal.toReal_pos hs₀_ne_zero hs₀_ne_top
  -- Auxiliary: split exponents on the real side via `h_split`.
  have h_one_div_toReal_split :
      p.toReal⁻¹ = r.toReal⁻¹ + s₀.toReal⁻¹ := by
    have hr_fin : 1 / r ≠ ∞ := by simp [one_div, hr_ne_zero]
    have hs_fin : 1 / s₀ ≠ ∞ := by simp [one_div, hs₀_ne_zero]
    have h1 : (1 / p).toReal = (1 / r + 1 / s₀).toReal := by
      simpa using congrArg ENNReal.toReal h_split
    have h2 : (1 / r + 1 / s₀).toReal = (1 / r).toReal + (1 / s₀).toReal :=
      ENNReal.toReal_add hr_fin hs_fin
    have h3 : (1 / p).toReal = (1 / r).toReal + (1 / s₀).toReal := by
      simpa using (h1.trans h2)
    simpa [one_div, ENNReal.toReal_inv] using h3
  -- Base for combining powers of `(N+1 : ℝ≥0∞)` when needed later
  have h_Bpow_split :
      ∀ k : ℕ,
        ((k + 1 : ℝ≥0∞) ^ r.toReal⁻¹)
          * ((k + 1 : ℝ≥0∞) ^ s₀.toReal⁻¹)
          = ((k + 1 : ℝ≥0∞) ^ p.toReal⁻¹) := by
    intro k
    have hbase_ne_zero : (k + 1 : ℝ≥0∞) ≠ 0 := by simp
    have hbase_ne_top : (k + 1 : ℝ≥0∞) ≠ ∞ := by simp
    have h_add :
        r.toReal⁻¹ + s₀.toReal⁻¹ = p.toReal⁻¹ := by
      simpa using h_one_div_toReal_split.symm
    -- use `(x ^ (a + b)) = x ^ a * x ^ b`, rearranged
    have h_rw :=
      (ENNReal.rpow_add (x := (k + 1 : ℝ≥0∞)) (y := r.toReal⁻¹)
        (z := s₀.toReal⁻¹) hbase_ne_zero hbase_ne_top).symm
    simpa [h_add, add_comm, add_left_comm, add_assoc] using h_rw
  exact
    le_trans h_limsup_goal <| by
      -- Define A_N(y) and its uniform bound by a constant C_N.
      classical
      let A : ℕ → G → ℝ :=
        fun N y => (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal
      let C : ℕ → ℝ :=
        fun N => ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ).toReal
      have hA_leC : ∀ N y, A N y ≤ C N := by
        intro N y
        simpa [A, C] using h_translate_norm_bound_toReal N y
      -- Step B: Prepare a p-norm–based bound for A using exponent monotonicity on finite measures.
      -- We will use the generic translate bound at exponent p, and then convert p → r
      -- via the finite-measure exponent inequality.
      -- Translate bound at exponent p on the partial measures.
      have h_translate_norm_bound_toReal_p :
          ∀ N y,
            (eLpNorm (fun x => f (x - y)) p (μpartial N)).toReal
              ≤ ((N + 1 : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm f p μ).toReal := by
        intro N y
        -- This follows from the general partial-translate bound specialized to p.
        have :=
          sfiniteSeq_partial_translate_norm_bound
            (μ := μ) (r := p) (f := f) (μpartial := μpartial)
            (hf := hf) (h_le := hμpartial_le_smul) N y
        -- Convert both sides to `toReal` for convenience (both are finite under our hypotheses).
        have h_pow_ne_top : ((N + 1 : ℝ≥0∞) ^ (1 / p).toReal) ≠ ∞ := by
          have h_nonneg : 0 ≤ (1 / p).toReal := by simp [one_div]
          exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
        have h_rhs_ne_top :
            ((N + 1 : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm f p μ) ≠ ∞ :=
          ENNReal.mul_ne_top h_pow_ne_top (by simpa using hf.eLpNorm_ne_top)
        exact ENNReal.toReal_mono h_rhs_ne_top this
      -- Finite-measure exponent monotonicity (from p to r) on each μpartial N (correct direction).
      -- This is the key inequality enabling the p-based redesign of the constants.
      have h_exponent_mono_toReal :
          ∀ N y,
            (eLpNorm (fun x => f (x - y)) p (μpartial N)).toReal
              ≤ (((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)).toReal
                  * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
        intro N y
        -- Apply finite-measure exponent monotonicity to `h := fun x => f (x - y)`
        -- and then convert both sides with `toReal` (ensuring finiteness on the RHS).
        haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
        -- Measurability of the translate x ↦ f (x - y) w.r.t. μpartial N
        -- Use translation invariance to get measurability under μ, then restrict to μpartial N.
        have h_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using measurePreserving_add_right (μ := μ) (-y)
        have h_shift_mem : MemLp (fun x => f (x - y)) r μ :=
          hf_r.comp_measurePreserving h_pres
        have h_meas_μ : AEStronglyMeasurable (fun x => f (x - y)) μ :=
          h_shift_mem.aestronglyMeasurable
        have h_meas_partial : AEStronglyMeasurable (fun x => f (x - y)) (μpartial N) :=
          h_meas_μ.mono_ac (hμpartial_ac N)
        -- From 1/p = 1/r + 1/s₀ we deduce 1/r ≤ 1/p, hence p ≤ r by antitonicity of inv.
        have h_inv_r_le_inv_p : 1 / r ≤ 1 / p := by
          have : 1 / r ≤ 1 / r + 1 / s₀ := by simp
          simp [h_split, add_comm, add_left_comm, add_assoc]
        have hp_le_hr : p ≤ r := by
          have : r⁻¹ ≤ p⁻¹ := by simpa [one_div] using h_inv_r_le_inv_p
          exact (ENNReal.inv_le_inv).mp this
        -- Base inequality in ℝ≥0∞
        have h_base :
            eLpNorm (fun x => f (x - y)) p (μpartial N)
              ≤ ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
                  * eLpNorm (fun x => f (x - y)) r (μpartial N) :=
          eLpNorm_exponent_mono_of_finite_measure
            (μ := μpartial N)
            (f := fun x => f (x - y))
            (p := p) (r := r) hp_le_hr h_meas_partial
        -- The RHS is finite: both factors are finite.
        have h_exp_nonneg : 0 ≤ (1 / p.toReal - 1 / r.toReal) := by
          -- From 1/p = 1/r + 1/s₀ and 0 ≤ 1/s₀, deduce 1/r ≤ 1/p, hence the difference is ≥ 0.
          have h_sum : 1 / p.toReal = 1 / r.toReal + 1 / s₀.toReal := by
            simpa [one_div] using h_one_div_toReal_split
          have h_inv_s₀_nonneg : 0 ≤ 1 / s₀.toReal := by
            simp [one_div]
          have h_le : 1 / r.toReal ≤ 1 / p.toReal := by
            have : 1 / r.toReal ≤ 1 / r.toReal + 1 / s₀.toReal :=
              le_add_of_nonneg_right h_inv_s₀_nonneg
            simp [h_sum, add_comm, add_left_comm, add_assoc]
          exact sub_nonneg.mpr h_le
        have h_factor1_ne_top :
            ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal) ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
        have h_factor2_bound := h_translate_norm_bound N y
        have h_factor2_ne_top :
            eLpNorm (fun x => f (x - y)) r (μpartial N) ≠ ∞ := by
          -- Bounded by a finite constant ⇒ strictly below ⊤
          have h_pow_ne_top : ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / r).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have h_const_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ :=
            ENNReal.mul_ne_top h_pow_ne_top (by simpa using hf_r.eLpNorm_ne_top)
          have hc_lt_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) < ∞ := by
            simpa [lt_top_iff_ne_top] using h_const_ne_top
          have h_lt_top :
              eLpNorm (fun x => f (x - y)) r (μpartial N) < ∞ :=
            lt_of_le_of_lt h_factor2_bound hc_lt_top
          simpa [lt_top_iff_ne_top] using h_lt_top
        have h_rhs_ne_top :
            ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
                * eLpNorm (fun x => f (x - y)) r (μpartial N) ≠ ∞ :=
          ENNReal.mul_ne_top h_factor1_ne_top h_factor2_ne_top
        -- Convert the inequality with `toReal` and expand the RHS product.
        have h_base_toReal :
            (eLpNorm (fun x => f (x - y)) p (μpartial N)).toReal ≤
              ( ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
                  * eLpNorm (fun x => f (x - y)) r (μpartial N) ).toReal :=
          ENNReal.toReal_mono h_rhs_ne_top h_base
        have h_toReal_mul :
            ( ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)
                * eLpNorm (fun x => f (x - y)) r (μpartial N) ).toReal
              = (((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal)).toReal
                  * (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal := by
          simp
        simpa [h_toReal_mul] using h_base_toReal
      -- Combine the two bounds to produce a p-based uniform control for A.
      -- y-dependent lower-bound template coming from exponent monotonicity on finite measures
      let Cp : ℕ → G → ℝ :=
        fun N y =>
          (((μpartial N) Set.univ) ^ (1 / r.toReal - 1 / p.toReal)).toReal
            * ((eLpNorm (fun x => f (x - y)) p (μpartial N)).toReal)
      -- Placeholder: with the corrected exponent inequality direction, we will adjust the
      -- chaining to produce the desired bound on `A` in the next pass.
      -- We switch to a lower bound: A N y ≥ Cp N y.
      have hA_geCp : ∀ N y, A N y ≥ Cp N y := by
        intro N y
        -- Finite measure on μpartial N
        haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
        -- Trivial if the partial measure is zero.
        by_cases hμz : μpartial N = 0
        · simp [A, Cp, hμz]
        · -- Nonzero finite measure: prove the inequality in ℝ≥0∞, then pass to toReal.
          -- Notation: α = μ(univ)^(1/p - 1/r), β = μ(univ)^(1/r - 1/p)
          set α : ℝ≥0∞ := ((μpartial N) Set.univ) ^ (1 / p.toReal - 1 / r.toReal) with hα
          set β : ℝ≥0∞ := ((μpartial N) Set.univ) ^ (1 / r.toReal - 1 / p.toReal) with hβ
          -- Measurability of the translate under μpartial N
          have h_pres : MeasurePreserving (fun x : G => x - y) μ μ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
              using measurePreserving_add_right (μ := μ) (-y)
          have h_shift_mem : MemLp (fun x => f (x - y)) r μ :=
            hf_r.comp_measurePreserving h_pres
          have h_meas_partial :
              AEStronglyMeasurable (fun x => f (x - y)) (μpartial N) :=
            (h_shift_mem.aestronglyMeasurable).mono_ac (hμpartial_ac N)
          -- Base (Lyapunov) inequality in ℝ≥0∞ on μpartial N
          have h_baseENN :
              eLpNorm (fun x => f (x - y)) p (μpartial N)
                ≤ α * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
            have hp_le_hr : p ≤ r := by
              -- From 1/p = 1/r + 1/s₀ ⇒ 1/r ≤ 1/p in ℝ≥0∞
              have h_inv_r_le_inv_p : 1 / r ≤ 1 / p := by
                have : 1 / r ≤ 1 / r + 1 / s₀ := by simp
                simp [h_split, add_comm, add_left_comm, add_assoc]
              have : r⁻¹ ≤ p⁻¹ := by simpa [one_div] using h_inv_r_le_inv_p
              exact (ENNReal.inv_le_inv).1 this
            simpa [hα] using
              (eLpNorm_exponent_mono_of_finite_measure
                (μ := μpartial N) (f := fun x => f (x - y))
                (p := p) (r := r) hp_le_hr h_meas_partial)
          -- Multiply by β on both sides and simplify with β * α = 1 (in ℝ≥0∞).
          have h_mulENN :
              β * eLpNorm (fun x => f (x - y)) p (μpartial N)
                ≤ β * (α * eLpNorm (fun x => f (x - y)) r (μpartial N)) :=
            mul_le_mul_left' h_baseENN β
          have hμU_ne_zero : (μpartial N) Set.univ ≠ 0 := by
            simpa [Measure.measure_univ_eq_zero] using hμz
          have hμU_ne_top : (μpartial N) Set.univ ≠ ⊤ := by
            simp
          have h_prod_one : α * β = (1 : ℝ≥0∞) := by
            have h :=
              ENNReal.rpow_add (x := (μpartial N) Set.univ)
                (y := (1 / p.toReal - 1 / r.toReal))
                (z := (1 / r.toReal - 1 / p.toReal)) hμU_ne_zero hμU_ne_top
            -- x^(y+z) = x^y * x^z and (y+z) = 0
            have : α * β = ((μpartial N) Set.univ) ^ 0 := by
              simpa [hα, hβ, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
                using h.symm
            simpa using (this.trans (by simp))
          have h_leENN :
              β * eLpNorm (fun x => f (x - y)) p (μpartial N)
                ≤ eLpNorm (fun x => f (x - y)) r (μpartial N) := by
            simpa [mul_comm, mul_left_comm, mul_assoc, h_prod_one]
              using
                (le_trans h_mulENN (by
                  -- β * (α * E_r) = (β * α) * E_r = E_r
                  have : β * (α * eLpNorm (fun x => f (x - y)) r (μpartial N))
                      = (β * α) * eLpNorm (fun x => f (x - y)) r (μpartial N) := by
                    simp [mul_comm, mul_left_comm, mul_assoc]
                  simp [this, h_prod_one, mul_comm, mul_left_comm, mul_assoc]))
          -- RHS is finite by the uniform translate bound at r.
          have h_pow_ne_top : ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / r).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have h_const_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ :=
            ENNReal.mul_ne_top h_pow_ne_top (by simpa using hf_r.eLpNorm_ne_top)
          have h_factor2_ne_top :
              eLpNorm (fun x => f (x - y)) r (μpartial N) ≠ ⊤ := by
            have h_bound := h_translate_norm_bound N y
            exact ne_of_lt (lt_of_le_of_lt h_bound
              (by simpa [lt_top_iff_ne_top] using h_const_ne_top))
          -- Pass to toReal to conclude A N y ≥ Cp N y.
          have h_toReal := ENNReal.toReal_mono h_factor2_ne_top h_leENN
          simpa [A, Cp, hβ] using h_toReal
      -- Auxiliary facts: nonnegativity and L^q membership of ‖g‖ on μpartial N.
      have hA_nonneg : ∀ N y, 0 ≤ A N y := by
        intro N y; simp [A]
      have hg_norm_partial : ∀ N, MemLp (fun y => ‖g y‖) q (μpartial N) := by
        intro N; simpa using (hg_partial N).norm
      -- First, a crude bound using A ≤ C pointwise to control Ψ N.
      have hΨ_le_aux :
          ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                (C N * ∫ y, ‖g y‖ ∂ μpartial N)) ^ r.toReal := by
        intro N
        have h_pointwise :
            ∀ y, ‖g y‖ * A N y ≤ ‖g y‖ * C N := by
          intro y
          have := hA_leC N y
          exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
        have h_left_int :
            Integrable (fun y => ‖g y‖ * A N y) (μpartial N) := by
          -- Provided earlier as `h_norm_piece`.
          simpa [A] using h_norm_piece N
        have h_right_int :
            Integrable (fun y => ‖g y‖ * C N) (μpartial N) := by
          have := (hg_partial_int N).norm.mul_const (C N)
          simpa using this
        have h_int_le :
            ∫ y, ‖g y‖ * A N y ∂ μpartial N ≤
              ∫ y, ‖g y‖ * C N ∂ μpartial N := by
          refine integral_mono_ae h_left_int h_right_int ?_
          exact Filter.Eventually.of_forall h_pointwise
        have h_int_eval :
            ∫ y, ‖g y‖ * C N ∂ μpartial N = C N * ∫ y, ‖g y‖ ∂ μpartial N := by
          simpa [mul_comm, mul_left_comm, mul_assoc]
            using
              (integral_mul_const (μ := μpartial N) (r := C N)
                (f := fun y => ‖g y‖))
        have h_ofReal_le :
            ENNReal.ofReal (∫ y, ‖g y‖ * A N y ∂ μpartial N)
              ≤ ENNReal.ofReal (C N * ∫ y, ‖g y‖ ∂ μpartial N) := by
          have := le_trans h_int_le (le_of_eq h_int_eval)
          exact ENNReal.ofReal_le_ofReal this
        -- Raise both sides to r.toReal.
        have :
            (ENNReal.ofReal (∫ y, ‖g y‖ * A N y ∂ μpartial N)) ^ r.toReal
              ≤ (ENNReal.ofReal (C N * ∫ y, ‖g y‖ ∂ μpartial N)) ^ r.toReal := by
          exact ENNReal.rpow_le_rpow h_ofReal_le ENNReal.toReal_nonneg
        simpa [Ψ, hΨ_def, A] using this
      -- Hölder (q, s₀) with the constant 1 to control ∫ ‖g‖ on μpartial N.
      have h_one_memLp : ∀ N, MemLp (fun _ : G => (1 : ℝ)) s₀ (μpartial N) := by
        intro N
        have h_aesm : AEStronglyMeasurable (fun _ : G => (1 : ℝ)) (μpartial N) := by
          simpa using (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : G => (1 : ℝ)) (μpartial N))
        haveI : IsFiniteMeasure (μpartial N) := hμpartial_fin N
        by_cases hμz : μpartial N = 0
        · have : eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N) = 0 := by
            simp [hμz]
          exact ⟨h_aesm, by simp [this]⟩
        · have hs₀_ne_zero' : s₀ ≠ 0 := hs₀_ne_zero
          have h_const :
              eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)
                = ENNReal.ofReal (1 : ℝ) * (μpartial N Set.univ) ^ (1 / s₀.toReal) := by
            have h_nonneg : 0 ≤ (1 : ℝ) := by simp
            simpa [Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
              Real.norm_eq_abs, abs_of_nonneg h_nonneg]
              using (eLpNorm_const (μ := μpartial N) (p := s₀) (c := (1 : ℝ)) hs₀_ne_zero' hμz)
          have h_lt_top : eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N) < ∞ := by
            have : (μpartial N Set.univ) < ∞ := measure_lt_top _ _
            have hpow_lt : (μpartial N Set.univ) ^ (1 / s₀.toReal) < ∞ :=
              ENNReal.rpow_lt_top_of_nonneg (by simp) this.ne
            have h1 : ENNReal.ofReal (1 : ℝ) < ∞ := by simp
            have h_rhs_lt :
                ENNReal.ofReal (1 : ℝ) * (μpartial N Set.univ) ^ (1 / s₀.toReal) < ∞ :=
              ENNReal.mul_lt_top h1 hpow_lt
            simpa [h_const] using h_rhs_lt
          exact ⟨h_aesm, h_lt_top⟩
      have h_int_g_le :
          ∀ N,
            ∫ y, ‖g y‖ ∂ μpartial N
              ≤ (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal := by
        intro N
        have h_holder :=
          holder_inequality (μ := μpartial N) (p := q) (q := s₀) hs₀_conj
            (f := fun y => ‖g y‖) (g := fun _ : G => (1 : ℝ))
            (hg_norm_partial N) (h_one_memLp N)
        -- Simplify |‖g y‖ * 1| to ‖g y‖
        simpa using h_holder.2
      -- Refine hΨ_le_aux using the Hölder bound on ∫ ‖g‖.
      have h_C_nonneg : ∀ N, 0 ≤ C N := by
        intro N
        -- Show nonnegativity by factors: both toReal terms are nonnegative.
        have h1 : 0 ≤ (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal)).toReal := ENNReal.toReal_nonneg
        have h2 : 0 ≤ (eLpNorm f r μ).toReal := ENNReal.toReal_nonneg
        -- Depending on rewriting, `C N` may appear as product of toReals or toReal of product.
        -- Both yield a nonnegative real, so we solve both shapes.
        by_cases hshape :
          C N = (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal)).toReal * (eLpNorm f r μ).toReal
        · simpa [hshape]
          using mul_nonneg h1 h2
        · -- Fall back to the original definition `toReal` of an ENNReal product.
          -- In that shape, nonnegativity follows from `toReal_nonneg` directly.
          -- Rewrite back to the definition of `C`.
          have : 0 ≤ (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ).toReal :=
            ENNReal.toReal_nonneg
          simpa [C]
            using this
      -- Bound eLpNorm g on μpartial N by the smul-measure bound and convert to toReal.
      have h_g_partial_bound_toReal :
          ∀ N,
            (eLpNorm g q (μpartial N)).toReal ≤
              (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal := by
        intro N
        have h_le' :=
          eLpNorm_mono_measure
            (f := g) (μ := ((N + 1 : ℝ≥0∞) • μ)) (ν := μpartial N) (p := q)
            (hμpartial_le_smul N)
        have h_succ_pos : (0 : ℝ≥0∞) < (N + 1 : ℝ≥0∞) := by
          exact_mod_cast (Nat.succ_pos N)
        have h_c_ne_zero : (N + 1 : ℝ≥0∞) ≠ 0 := ne_of_gt h_succ_pos
        have h_smul :=
          eLpNorm_smul_measure_of_ne_zero
            (μ := μ) (p := q) (f := g) (c := (N + 1 : ℝ≥0∞)) h_c_ne_zero
        have h_step := h_le'.trans (le_of_eq h_smul)
        -- convert to toReal using that the RHS is finite
        have h_pow_ne_top :
            ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ≠ ∞ := by
          have h_exp_nonneg : 0 ≤ (1 / q).toReal := by simp [one_div]
          exact ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
        have h_const_ne_top :
            (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ) ≠ ∞ :=
          ENNReal.mul_ne_top h_pow_ne_top hg.eLpNorm_ne_top
        exact ENNReal.toReal_mono h_const_ne_top h_step
      -- ENNReal-level bound for the constant-1 eLpNorm on the partial measures.
      have h_one_partial_bound :
          ∀ N,
            eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)
              ≤ ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                  * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ := by
        intro N
        have h_le' :=
          eLpNorm_mono_measure
            (f := fun _ : G => (1 : ℝ))
            (μ := ((N + 1 : ℝ≥0∞) • μ)) (ν := μpartial N) (p := s₀)
            (hμpartial_le_smul N)
        have h_succ_pos : (0 : ℝ≥0∞) < (N + 1 : ℝ≥0∞) := by
          exact_mod_cast (Nat.succ_pos N)
        have h_c_ne_zero : (N + 1 : ℝ≥0∞) ≠ 0 := ne_of_gt h_succ_pos
        have h_smul :=
          eLpNorm_smul_measure_of_ne_zero
            (μ := μ) (p := s₀)
            (f := fun _ : G => (1 : ℝ)) (c := (N + 1 : ℝ≥0∞)) h_c_ne_zero
        simpa using h_le'.trans (le_of_eq h_smul)
      have h_mul_le :
          ∀ N,
            C N * ∫ y, ‖g y‖ ∂ μpartial N
              ≤ C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                    * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal := by
        intro N
        have h_int_le := h_int_g_le N
        calc C N * ∫ y, ‖g y‖ ∂ μpartial N
            ≤ C N * ((eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal) :=
          mul_le_mul_of_nonneg_left h_int_le (h_C_nonneg N)
          _ = C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal := by
            ring
      have h_ofReal_le :
          ∀ N,
            ENNReal.ofReal (C N * ∫ y, ‖g y‖ ∂ μpartial N)
              ≤ ENNReal.ofReal
                  (C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                    * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal) := by
        intro N
        refine ENNReal.ofReal_le_ofReal ?_
        exact h_mul_le N
      have hΨ_le_aux' :
          ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                (C N
                  * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal)) ^
              r.toReal := by
        intro N
        have h_int_le := h_int_g_le N
        have h_rpow_mono :
            (ENNReal.ofReal (C N * ∫ y, ‖g y‖ ∂ μpartial N)) ^ r.toReal
              ≤ (ENNReal.ofReal
                  (C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
                    * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal)) ^ r.toReal := by
          exact ENNReal.rpow_le_rpow (h_ofReal_le N) (by exact ENNReal.toReal_nonneg)
        have h_base := hΨ_le_aux N
        exact le_trans h_base h_rpow_mono
      -- Replace eLpNorm(‖g‖) by eLpNorm g and bound it by the smul-measure growth.
      have hΨ_le_aux'' :
          ∀ N,
            Ψ N ≤
              (ENNReal.ofReal
                (C N
                  * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm g q μ).toReal)
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal)) ^
              r.toReal := by
        intro N
        have h_base := hΨ_le_aux' N
        -- Convert the inner factor using h_g_partial_bound_toReal and monotonicity
        have h_eqNorm :
            eLpNorm (fun y => ‖g y‖) q (μpartial N) = eLpNorm g q (μpartial N) :=
          eLpNorm_norm_eq_of_complex g q
        have h_g_toReal :
            (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal ≤
              (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal := by
          rw [h_eqNorm]
          exact h_g_partial_bound_toReal N
        set D1 := (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal with hD1
        have hD1_nonneg : 0 ≤ D1 := ENNReal.toReal_nonneg
        have h_mul_left :
            C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal
              ≤ C N * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal := by
          exact mul_le_mul_of_nonneg_left h_g_toReal (h_C_nonneg N)
        have h_inner :
            C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal * D1
              ≤ C N * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal * D1 := by
          exact mul_le_mul_of_nonneg_right h_mul_left hD1_nonneg
        have h_ofReal_le :
            ENNReal.ofReal
                (C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal * D1)
              ≤ ENNReal.ofReal
                (C N * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal * D1) :=
          ENNReal.ofReal_le_ofReal h_inner
        have h_rpow_mono :
            (ENNReal.ofReal
              (C N * (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal * D1)) ^ r.toReal
              ≤ (ENNReal.ofReal
              (C N * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) *
              eLpNorm g q μ).toReal * D1)) ^ r.toReal := by
          exact ENNReal.rpow_le_rpow h_ofReal_le (by exact ENNReal.toReal_nonneg)
        -- Chain the two bounds
        refine (le_trans h_base ?_)
        simpa [D1, mul_comm, mul_left_comm, mul_assoc] using h_rpow_mono
      -- Further refine the D1 factor using the ENNReal-level bound h_one_partial_bound
      -- and convert it to a toReal inequality when the global constant is finite.
      have h_one_partial_bound_toReal :
          ∀ N,
            eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞ →
            (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal ≤
              (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal := by
        intro N h_ne_top
        have h_le := h_one_partial_bound N
        have h_pow_ne_top :
            ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ≠ ∞ := by
          have h_exp_nonneg : 0 ≤ (1 / s₀).toReal := by simp [one_div]
          exact ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg (by simp)
        have h_rhs_ne_top :
            (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ≠ ∞ :=
          ENNReal.mul_ne_top h_pow_ne_top h_ne_top
        exact ENNReal.toReal_mono h_rhs_ne_top h_le
      -- Apply the toReal bound to refine Ψ when eLpNorm(1) on μ is finite.
      have hΨ_le_aux''' :
          ∀ N,
            eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞ →
            Ψ N ≤
              (ENNReal.ofReal
                (C N
                  * ((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal)
                        * eLpNorm g q μ).toReal)
                  * ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal))) ^
              r.toReal := by
        intro N h_ne_top
        have h_base := hΨ_le_aux'' N
        -- Replace D1 by its toReal-bound derived above
        set Dq := (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal with hDq
        set D1 := (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal with hD1
        set D1' := ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal) with hD1'
        have hD1_le : D1 ≤ D1' := by
          simpa [D1, D1'] using h_one_partial_bound_toReal N h_ne_top
        have h_nonneg_c : 0 ≤ C N * Dq := by
          have h1 : 0 ≤ C N := h_C_nonneg N
          have h2 : 0 ≤ Dq := by exact ENNReal.toReal_nonneg
          exact mul_nonneg h1 h2
        have h_inner_le :
            C N * Dq * D1 ≤ C N * Dq * D1' := by
          exact mul_le_mul_of_nonneg_left hD1_le h_nonneg_c
        have h_ofReal_le :
            ENNReal.ofReal (C N * Dq * D1) ≤ ENNReal.ofReal (C N * Dq * D1') :=
          ENNReal.ofReal_le_ofReal h_inner_le
        have h_rpow_mono :
            (ENNReal.ofReal (C N * Dq * D1)) ^ r.toReal
              ≤ (ENNReal.ofReal (C N * Dq * D1')) ^ r.toReal := by
          exact ENNReal.rpow_le_rpow h_ofReal_le (by exact ENNReal.toReal_nonneg)
        -- Chain with the previous bound on Ψ N
        exact le_trans h_base h_rpow_mono
      -- TODO: Next, relate the remaining factors using h_split and bounds for eLpNorm(1) and C N.
      -- Step 1 (implemented here): extract a normalized bounding sequence Θ and compare limsups.
      classical
      let Θ : ℕ → ℝ≥0∞ :=
        fun N =>
          (ENNReal.ofReal
            (C N
              * ((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal)
              * ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                    * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal))) ^ r.toReal
      have h_limsup_compare_Theta :
          eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞ →
          Filter.limsup Ψ Filter.atTop ≤ Filter.limsup Θ Filter.atTop := by
        intro h_ne_top
        refine Filter.limsup_le_limsup ?_
        exact Filter.Eventually.of_forall (fun N => by
          -- Directly apply the pointwise bound hΨ_le_aux''' to obtain Ψ N ≤ Θ N.
          simpa [Θ]
            using (hΨ_le_aux''' N h_ne_top))
  -- The remaining steps will turn limsup Θ into the desired constant bound
  -- using exponent identities (h_split) and norm estimates.
  -- We postpone them to the next step.
  -- Small helper lemmas for reorganizing products inside ENNReal.ofReal
  -- can be added if needed; for now we rely on simp with ENNReal.ofReal_mul.
      -- Next step: split on finiteness of ‖1‖_{s₀,μ} and set the target constant.
      by_cases h_one_finite : eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ ≠ ∞
      · -- Under this finiteness, avoid N-growth and obtain a uniform bound on Ψ.
        have hcomp := h_limsup_compare_Theta h_one_finite
        -- First step of the Θ-rewrite: expand Θ N by pulling `toReal` outside `ofReal`
        -- and restoring the ENNReal factors. This normalizes Θ to a clean triple product
        -- of ENNReal factors raised to r.toReal, preparing exponent algebra.
        have hΘ_expand : ∀ N,
            Θ N =
              ( ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ)
                * ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm g q μ)
                * ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal
                    * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ) ^ r.toReal := by
          intro N
          -- Each inner real factor is nonnegative.
          have hC_nonneg : 0 ≤ C N := h_C_nonneg N
          have hDq_nonneg :
              0 ≤ ((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal) :=
            ENNReal.toReal_nonneg
          have hD1_nonneg :
              0 ≤ ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                      * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal) :=
            ENNReal.toReal_nonneg
          -- Finiteness of each ENNReal factor to use `ofReal_toReal`.
          have h_pow_r_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / r).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have hC_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) ≠ ∞ := by
            exact ENNReal.mul_ne_top h_pow_r_ne_top (by simpa using hf_r.eLpNorm_ne_top)
          have h_pow_q_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / q).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have hDq_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm g q μ) ≠ ∞ := by
            exact ENNReal.mul_ne_top h_pow_q_ne_top (by simpa using hg.eLpNorm_ne_top)
          have h_pow_s_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ≠ ∞ := by
            have h_nonneg : 0 ≤ (1 / s₀).toReal := by simp [one_div]
            exact ENNReal.rpow_ne_top_of_nonneg h_nonneg (by simp)
          have hD1_ne_top :
              ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal
                  * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ≠ ∞ := by
            exact ENNReal.mul_ne_top h_pow_s_ne_top h_one_finite
          -- Expand `ofReal` over the triple product and restore ENNReal factors.
          have h_expand_ofReal :
              ENNReal.ofReal
                  (C N
                    * ((((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ).toReal)
                    * ((((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
                          * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal))
                =
                  ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ)
                    * ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm g q μ)
                    * ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal
                        * eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) := by
            -- abbreviations for the ENNReal factors
            set DqE : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) * eLpNorm g q μ with hDqE
            set D1E : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) *
              eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ with hD1E
            -- split ofReal over the triple product
            have h_mul3 : ENNReal.ofReal (C N * DqE.toReal * D1E.toReal)
                = ENNReal.ofReal (C N) * ENNReal.ofReal (DqE.toReal) *
                  ENNReal.ofReal (D1E.toReal) := by
              simp [ENNReal.ofReal_mul, hC_nonneg, hDq_nonneg, hD1_nonneg,
                mul_comm, mul_left_comm, mul_assoc]
            -- convert ofReal (toReal _) back to the ENNReal factors
            have hC_back : ENNReal.ofReal (C N)
                = ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) := by
              have h := ENNReal.ofReal_toReal (a :=
                (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * eLpNorm f r μ)) hC_ne_top
              -- h : ENNReal.ofReal (((...) ).toReal) = ((...) )
              simpa [C] using h
            have hDq_back : ENNReal.ofReal (DqE.toReal) = DqE := by
              simpa [hDqE] using ENNReal.ofReal_toReal (a := DqE) hDq_ne_top
            have hD1_back : ENNReal.ofReal (D1E.toReal) = D1E := by
              simpa [hD1E] using ENNReal.ofReal_toReal (a := D1E) hD1_ne_top
            -- assemble explicitly in two steps to avoid fragile `simpa` obligations
            have h_prod :
                ENNReal.ofReal (C N * DqE.toReal * D1E.toReal)
                  = ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) * (DqE * D1E) := by
              -- first rewrite via h_mul3, then restore each factor
              have := h_mul3
              -- `this` has the form ofReal(C*...*...) = ofReal C * ofReal ... * ofReal ...
              -- now replace each `ofReal (toReal _)` back to the ENNReal factor
              simpa [hC_back, hDq_back, hD1_back,
                    mul_comm, mul_left_comm, mul_assoc]
                using this
            have h_reassoc :
                ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) * (DqE * D1E)
                  = eLpNorm f r μ * (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) * (DqE * D1E)) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
            -- rewrite (1/r).toReal as r.toReal⁻¹
            have h_exp_r : (1 / r).toReal = r.toReal⁻¹ := by
              have hr_ne_zero' : r ≠ 0 := hr_ne_zero
              simp [one_div, ENNReal.toReal_inv, hr_ne_zero', hr_ne_top]
            have h_prod_target :
                ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal * eLpNorm f r μ) * (DqE * D1E)
                  = eLpNorm f r μ * ((↑N + 1) ^ r.toReal⁻¹ * (DqE * D1E)) := by
              simp [h_exp_r, mul_comm, mul_left_comm, mul_assoc]
            -- combine with h_prod
            have := h_prod.trans h_prod_target
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
          -- Conclude the desired form of Θ N by rewriting with `h_expand_ofReal`.
          simpa [Θ] using congrArg (fun z => z ^ r.toReal) h_expand_ofReal
        -- Use μpartial N ≤ μ to get a uniform translate-norm bound.
        have hμpartial_le : ∀ N, μpartial N ≤ μ :=
          sfiniteSeq_partial_le_measure (μ := μ) (μn := μn) (μpartial := μpartial)
            (hμ_sum := hμ_sum) (hμpartial_def := fun _ => rfl)
        have h_translate_uniform : ∀ N y,
            (eLpNorm (fun x => f (x - y)) r (μpartial N)).toReal ≤
              (eLpNorm f r μ).toReal := by
          intro N y
          have h_le :=
            eLpNorm_mono_measure (f := fun x => f (x - y)) (μ := μ) (ν := μpartial N) (p := r)
              (hμpartial_le N)
          have h_translate :=
            eLpNorm_comp_add_right (μ := μ) (f := f) (p := r) (y := -y)
              hf_r.aestronglyMeasurable
          have h_eq : eLpNorm (fun x => f (x - y)) r μ = eLpNorm f r μ := by
            simpa [sub_eq_add_neg] using h_translate
          exact ENNReal.toReal_mono hf_r.eLpNorm_ne_top (h_le.trans (le_of_eq h_eq))
        -- Hölder on μpartial N, then monotonicity to μ (using h_one_finite for finiteness).
        have h_int_g_le' : ∀ N,
            ∫ y, ‖g y‖ ∂ μpartial N
              ≤ (eLpNorm (fun y => ‖g y‖) q μ).toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal := by
          intro N
          have h_holder := h_int_g_le N
          have h_mono_g :
              (eLpNorm (fun y => ‖g y‖) q (μpartial N)).toReal ≤
                (eLpNorm (fun y => ‖g y‖) q μ).toReal := by
            have h_le :=
              eLpNorm_mono_measure (f := fun y => ‖g y‖) (μ := μ) (ν := μpartial N) (p := q)
                (hμpartial_le N)
            exact ENNReal.toReal_mono (by simpa using hg.eLpNorm_ne_top) h_le
          have h_mono_one :
              (eLpNorm (fun _ : G => (1 : ℝ)) s₀ (μpartial N)).toReal ≤
                (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ).toReal := by
            have h_le :=
              eLpNorm_mono_measure (f := fun _ : G => (1 : ℝ)) (μ := μ) (ν := μpartial N)
                (p := s₀) (hμpartial_le N)
            exact ENNReal.toReal_mono (by simpa using h_one_finite) h_le
          exact le_trans h_holder (mul_le_mul h_mono_g h_mono_one (by simp) (by simp))
        -- Convert constants using the Hölder triple bound.
        have h_holder_one :
            eLpNorm f p μ ≤ eLpNorm f r μ * eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ := by
          -- Build the Hölder triple instance using the split 1/p = 1/r + 1/s₀.
          haveI : ENNReal.HolderTriple r s₀ p :=
            ⟨by simpa [one_div] using h_split.symm⟩
          simpa using
            eLpNorm_mul_one_le (μ := μ) (f := f) (p := p) (r := r) (s := s₀)
              (hf_meas := hf.aestronglyMeasurable)
        -- Replace ‖g‖ L^q by g L^q.
        have h_g_eq : eLpNorm (fun y => ‖g y‖) q μ = eLpNorm g q μ := by
          simp
        -- Identify the constant-1 norms over ℝ and ℂ to compare with Hölder.
        have h_one_real_eq_complex :
            eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ
              = eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ := by
          by_cases hμz : μ = 0
          · simp [hμz]
          · have h_nonnegR : 0 ≤ (1 : ℝ) := by simp
            have h_nonnegC : 0 ≤ (1 : ℝ) := by simp
            have hR :=
              (eLpNorm_const (μ := μ) (p := s₀) (c := (1 : ℝ)) hs₀_ne_zero hμz)
            have hC :=
              (eLpNorm_const (μ := μ) (p := s₀) (c := (1 : ℂ)) hs₀_ne_zero hμz)
            -- Rewrite both sides to the common closed form.
            -- For ℝ
            have hR' :
                eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ
                  = ENNReal.ofReal (1 : ℝ)
                      * (μ Set.univ) ^ (1 / s₀.toReal) := by
              simpa [Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
                Real.norm_eq_abs, abs_of_nonneg h_nonnegR] using hR
            -- For ℂ
            have hC' :
                eLpNorm (fun _ : G => (1 : ℂ)) s₀ μ
                  = ENNReal.ofReal (‖(1 : ℂ)‖)
                      * (μ Set.univ) ^ (1 / s₀.toReal) := by
              simpa [Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
                Real.norm_eq_abs, Complex.norm_real, abs_of_nonneg h_nonnegC]
                using hC
            simp [hR', hC']
        -- Step 1: Switch to the Θ-limsup route instead of the K-bound.
        -- We already have `hcomp : limsup Ψ ≤ limsup Θ` from `h_limsup_compare_Theta`.
        -- Compose with the earlier `h_limsup_goal : ∫⁻ ... ≤ limsup Ψ`.
        have h_limsup_le_Theta : Filter.limsup Ψ Filter.atTop ≤ Filter.limsup Θ Filter.atTop :=
          hcomp
        have h_goal_to_Theta :
            (∫⁻ x, (ENNReal.ofReal (H x)) ^ r.toReal ∂ μ)
              ≤ Filter.limsup Θ Filter.atTop :=
          le_trans h_limsup_goal h_limsup_le_Theta
        -- Step 2: Expand Θ N as a clean product, distributing r-powers across factors.
        have hr_nonneg : 0 ≤ r.toReal := le_of_lt hr_toReal_pos
        have hΘ_split : ∀ N,
            Θ N =
              (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                * (eLpNorm f r μ) ^ r.toReal
                * (eLpNorm g q μ) ^ r.toReal
                * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ^ r.toReal := by
          intro N
          -- Start from the triple-product expansion of Θ.
          have h := hΘ_expand N
          -- Abbreviations for readability
          set Ar : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / r).toReal)
          set Br : ℝ≥0∞ := eLpNorm f r μ
          set Aq : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / q).toReal)
          set Bq : ℝ≥0∞ := eLpNorm g q μ
          set As : ℝ≥0∞ := ((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal)
          set Bs : ℝ≥0∞ := eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ
          -- Θ N = (Ar*Br * (Aq*Bq) * (As*Bs)) ^ r
          have h' : Θ N = (((Ar * Br) * (Aq * Bq)) * (As * Bs)) ^ r.toReal := by
            simpa [Ar, Br, Aq, Bq, As, Bs, mul_comm, mul_left_comm, mul_assoc] using h
          -- Distribute the r-power across the product using `mul_rpow_of_nonneg`.
          have h1 : (((Ar * Br) * (Aq * Bq)) * (As * Bs)) ^ r.toReal
              = ((Ar * Br) * (Aq * Bq)) ^ r.toReal * (As * Bs) ^ r.toReal := by
            simpa [mul_comm, mul_left_comm, mul_assoc]
              using (ENNReal.mul_rpow_of_nonneg ((Ar * Br) * (Aq * Bq)) (As * Bs) hr_nonneg)
          have h2 : ((Ar * Br) * (Aq * Bq)) ^ r.toReal
              = (Ar * Br) ^ r.toReal * (Aq * Bq) ^ r.toReal := by
            simpa [mul_comm, mul_left_comm, mul_assoc]
              using (ENNReal.mul_rpow_of_nonneg (Ar * Br) (Aq * Bq) hr_nonneg)
          have h3 : (Ar * Br) ^ r.toReal = Ar ^ r.toReal * Br ^ r.toReal := by
            simpa using (ENNReal.mul_rpow_of_nonneg Ar Br hr_nonneg)
          have h4 : (Aq * Bq) ^ r.toReal = Aq ^ r.toReal * Bq ^ r.toReal := by
            simpa using (ENNReal.mul_rpow_of_nonneg Aq Bq hr_nonneg)
          -- Also record the commuted variant to avoid orientation mismatches during simp.
          have h4_comm : (Bq * Aq) ^ r.toReal = Bq ^ r.toReal * Aq ^ r.toReal := by
            simpa [mul_comm] using (ENNReal.mul_rpow_of_nonneg Bq Aq hr_nonneg)
          have h5 : (As * Bs) ^ r.toReal = As ^ r.toReal * Bs ^ r.toReal := by
            simpa using (ENNReal.mul_rpow_of_nonneg As Bs hr_nonneg)
          -- Assemble and clean up associations/commutations.
          calc
            Θ N = (((Ar * Br) * (Aq * Bq)) * (As * Bs)) ^ r.toReal := h'
            _ = ((Ar * Br) * (Aq * Bq)) ^ r.toReal * (As * Bs) ^ r.toReal := h1
            _ = (Ar * Br) ^ r.toReal * (Aq * Bq) ^ r.toReal * (As * Bs) ^ r.toReal := by
              rw [h2]
            _ = (Ar ^ r.toReal * Br ^ r.toReal) * (Aq * Bq) ^ r.toReal * (As * Bs) ^ r.toReal := by
              rw [h3]
            _ = (Ar ^ r.toReal * Br ^ r.toReal) * (Aq ^ r.toReal * Bq ^ r.toReal) *
              (As * Bs) ^ r.toReal := by rw [h4]
            _ = (Ar ^ r.toReal * Br ^ r.toReal) * (Aq ^ r.toReal * Bq ^ r.toReal) *
              (As ^ r.toReal * Bs ^ r.toReal) := by rw [h5]
            _ = (Ar ^ r.toReal) * (Aq ^ r.toReal) * (As ^ r.toReal)
                * (Br ^ r.toReal) * (Bq ^ r.toReal) * (Bs ^ r.toReal) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
            _ = (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                * (eLpNorm f r μ) ^ r.toReal
                * (eLpNorm g q μ) ^ r.toReal
                * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ^ r.toReal := by
              show Ar ^ r.toReal * Aq ^ r.toReal * As ^ r.toReal
                * Br ^ r.toReal * Bq ^ r.toReal * Bs ^ r.toReal
                = (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                  * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                  * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                  * (eLpNorm f r μ) ^ r.toReal
                  * (eLpNorm g q μ) ^ r.toReal
                  * (eLpNorm (fun _ : G => (1 : ℝ)) s₀ μ) ^ r.toReal
              rfl
        -- Step 3: Prepare exponent identities to collapse ((N+1))-powers later.
        have hq_ne_zero' : q ≠ 0 := by
          have : (0 : ℝ≥0∞) < q := lt_trans (by simp) hq
          exact ne_of_gt this
        have h_inv_r_toReal : (1 / r).toReal = r.toReal⁻¹ := by
          simp [one_div, ENNReal.toReal_inv, hr_ne_zero, hr_ne_top]
        have h_inv_q_toReal : (1 / q).toReal = q.toReal⁻¹ := by
          simp [one_div, ENNReal.toReal_inv, hq_ne_zero', hq_ne_top]
        have h_inv_s_toReal : (1 / s₀).toReal = s₀.toReal⁻¹ := by
          simp [one_div, ENNReal.toReal_inv, hs₀_ne_zero, hs₀_ne_top]
        -- Conjugacy of q and s₀ on the real side: q⁻¹ + s₀⁻¹ = 1 (in toReal exponents).
        have h_qs_sum_toReal : q.toReal⁻¹ + s₀.toReal⁻¹ = 1 := by
          have hq_ne_zero' : q ≠ 0 := by
            have : (0 : ℝ≥0∞) < q := lt_trans (by simp) hq
            exact ne_of_gt this
          exact
            (conjugate_exponent_toReal_sum
              (p := q) (q := s₀)
              (hp_ne_zero := hq_ne_zero') (hp_ne_top := hq_ne_top)
              (hq_ne_zero := hs₀_ne_zero) (hq_ne_top := hs₀_ne_top)
              (hpq_sum := by
                -- from conjugacy hs₀_conj : IsConjugateExponent q s₀ we extract 1/q + 1/s₀ = 1
                rcases hs₀_conj with h | h | h
                · rcases h with ⟨hq_one, hs_top⟩; simp [hq_one, hs_top]
                · rcases h with ⟨hq_top, hs_one⟩; cases hq_ne_top hq_top
                · rcases h with ⟨_, _, _, _, hsum⟩; simpa using hsum))
        -- Auxiliary packing of the ((N+1))-powers inside Θ.
        have h_base_ne_zero : ∀ N : ℕ, ((N + 1 : ℝ≥0∞)) ≠ 0 := by intro N; simp
        have h_base_ne_top : ∀ N : ℕ, ((N + 1 : ℝ≥0∞)) ≠ ∞ := by intro N; simp
        have h_pack_N : ∀ N : ℕ,
            (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
              * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
              * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
            = ((N + 1 : ℝ≥0∞)) ^
                (((1 / r).toReal * r.toReal)
                  + ((1 / q).toReal * r.toReal)
                  + ((1 / s₀).toReal * r.toReal)) := by
          intro N
          -- Convert ((X^a)^r) into X^(a*r) for each exponent a.
          have h1 :
              (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                = ((N + 1 : ℝ≥0∞)) ^ ((1 / r).toReal * r.toReal) := by
            simp [ENNReal.rpow_mul]
          have h2 :
              (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                = ((N + 1 : ℝ≥0∞)) ^ ((1 / q).toReal * r.toReal) := by
            simp [ENNReal.rpow_mul]
          have h3 :
              (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                = ((N + 1 : ℝ≥0∞)) ^ ((1 / s₀).toReal * r.toReal) := by
            simp [ENNReal.rpow_mul]
          -- Combine via rpow_add twice: X^(a*r)*X^(b*r)*X^(c*r) = X^((a+b+c)*r)
          have h12 :
              ((N + 1 : ℝ≥0∞) ^ ((1 / r).toReal * r.toReal))
                * ((N + 1 : ℝ≥0∞) ^ ((1 / q).toReal * r.toReal))
              = ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal))) := by
            simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
              using
                (ENNReal.rpow_add (x := (N + 1 : ℝ≥0∞))
                  (y := ((1 / r).toReal * r.toReal))
                  (z := ((1 / q).toReal * r.toReal))
                  (h_base_ne_zero N) (h_base_ne_top N)).symm
          have h123 :
              ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal)))
                * ((N + 1 : ℝ≥0∞) ^ ((1 / s₀).toReal * r.toReal))
              = ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal)
                    + ((1 / s₀).toReal * r.toReal))) := by
            simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
              using
                (ENNReal.rpow_add (x := (N + 1 : ℝ≥0∞))
                  (y := (((1 / r).toReal * r.toReal) + ((1 / q).toReal * r.toReal)))
                  (z := ((1 / s₀).toReal * r.toReal))
                  (h_base_ne_zero N) (h_base_ne_top N)).symm
          -- Assemble
          calc
            (((N + 1 : ℝ≥0∞) ^ (1 / r).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / q).toReal) ^ r.toReal)
                * (((N + 1 : ℝ≥0∞) ^ (1 / s₀).toReal) ^ r.toReal)
                = ((N + 1 : ℝ≥0∞) ^ ((1 / r).toReal * r.toReal))
                    * ((N + 1 : ℝ≥0∞) ^ ((1 / q).toReal * r.toReal))
                    * ((N + 1 : ℝ≥0∞) ^ ((1 / s₀).toReal * r.toReal)) := by
              rw [h1, h2, h3]
            _ = ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal)))
                * ((N + 1 : ℝ≥0∞) ^ ((1 / s₀).toReal * r.toReal)) := by
              rw [← h12]
            _ = ((N + 1 : ℝ≥0∞) ^ (((1 / r).toReal * r.toReal)
                    + ((1 / q).toReal * r.toReal)
                    + ((1 / s₀).toReal * r.toReal))) := by
              rw [← h123]
            -- We keep the exponent in the expanded additive form for later use.
        -- We will evaluate limsup Θ using these packed exponents in the next step.
        sorry
      · -- In the infinite case, we will avoid using hΨ_le_aux''' and instead
        -- proceed via the earlier bound hΨ_le_aux'' combined with finite-piece
        -- control. We postpone this technical branch to the next step.
        -- TODO: implement the alternative route without the finiteness assumption.
        sorry

end ConvolutionAuxiliary
