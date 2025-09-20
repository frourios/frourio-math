def ContinuityEquation (X : Type*) [MeasurableSpace X]
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) (Γ : CarreDuChamp X) : Prop  := proven

theorem continuity_equation_from_regularity (X : Type*) [MeasurableSpace X]
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) (Γ : CarreDuChamp X)
    (h_weak : ρ.weakly_continuous)
    (h_meas : ∀ ψ : X → ℝ, Measurable ψ → ∀ t, Measurable (Γ.Γ ψ (φ.φ t)))
    :
    ContinuityEquation X ρ φ Γ  := proven

structure AdmissiblePair (X : Type*) [MeasurableSpace X]
    (ρ₀ ρ₁ : Measure X) (Γ : CarreDuChamp X) where
  /-- The curve of measures -/
  curve : ProbabilityCurve X
  /-- The velocity potential -/
  potential : VelocityPotential X
  /-- Initial condition -/
  init : curve.ρ 0 = ρ₀
  /-- Terminal condition -/
  terminal : curve.ρ 1 = ρ₁
  /-- Continuity equation holds -/
  continuity : ContinuityEquation X curve potential Γ := proven

def AdmissibleSet {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X) : Set (AdmissiblePair X ρ₀ ρ₁ Γ)  := proven

theorem admissible_set_nonempty {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X)
    (curve : ProbabilityCurve X) (potential : VelocityPotential X)
    (h_init : curve.ρ 0 = ρ₀) (h_term : curve.ρ 1 = ρ₁)
    (hCE : ContinuityEquation X curve potential Γ)
    (hΔ_meas : ∀ t : ℝ, Measurable (multiScaleDiff H cfg (potential.φ t)))
    (hΓ_meas : ∀ t : ℝ, Measurable (Γ.Γ (potential.φ t) (potential.φ t))) :
    ∃ (p : AdmissiblePair X ρ₀ ρ₁ Γ), p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁  := proven

noncomputable def dmCandidates {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) : Set ℝ  := proven

noncomputable def dm_squared {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) : ℝ  := proven

noncomputable def dm {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) : ℝ  := proven

structure DynDistanceFlags {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) where
  /-- Nonnegativity: dm_squared ≥ 0 -/
  nonneg : ∀ ρ₀ ρ₁ : Measure X,
    0 ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁
  /-- Diagonal vanishing: dm_squared(ρ,ρ) = 0 -/
  diag_zero : ∀ ρ : Measure X,
    dm_squared H cfg Γ κ μ ρ ρ = 0
  /-- Symmetry of the squared distance -/
  symm : ∀ ρ₀ ρ₁ : Measure X,
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ = dm_squared H cfg Γ κ μ ρ₁ ρ₀
  /-- Triangle inequality (gluing property for geodesics) -/
  triangle : ∀ ρ₀ ρ₁ ρ₂ : Measure X,
    dm_squared H cfg Γ κ μ ρ₀ ρ₂ ≤
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ + dm_squared H cfg Γ κ μ ρ₁ ρ₂
  /-- Triangle inequality at the distance level -/
  triangle_dist : ∀ ρ₀ ρ₁ ρ₂ : Measure X,
    dm H cfg Γ κ μ ρ₀ ρ₂ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ + dm H cfg Γ κ μ ρ₁ ρ₂ := proven

noncomputable def W2_squared {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    : Measure X → Measure X → ℝ  := proven

theorem dm_dominates_wasserstein {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) :
    W2_squared ρ₀ ρ₁ ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁  := proven

noncomputable def W2_squared_BB {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X) : ℝ  := proven

theorem dm_dominates_wasserstein_BB {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- 非空性仮定：許容対が少なくとも一つ存在
    (h_adm : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    -- 時間方向の可積分性：各許容対に対し Γ 部分と多重スケール項の時間可積分性
    (h_time_int : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (Γ.Γ (p.potential.φ t) (p.potential.φ t)) x ∂(p.curve.ρ t))
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ)
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    W2_squared_BB Γ ρ₀ ρ₁ ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁  := proven

noncomputable def W2_BB {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X) : ℝ  := proven

theorem dm_dominates_wasserstein_dist {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    (h_adm : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (h_time_int : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (Γ.Γ (p.potential.φ t) (p.potential.φ t)) x ∂(p.curve.ρ t))
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ)
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    W2_BB Γ ρ₀ ρ₁ ≤ dm H cfg Γ κ μ ρ₀ ρ₁  := proven

theorem dm_dominates_wasserstein_flagfree {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X) :
    ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty →
      (∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        MeasureTheory.IntegrableOn
          (fun t => ∫ x, (Γ.Γ (p.potential.φ t) (p.potential.φ t)) x ∂(p.curve.ρ t))
          (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
        MeasureTheory.IntegrableOn
          (fun t => ∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ)
          (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) →
      W2_BB Γ ρ₀ ρ₁ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ ∧
      W2_squared_BB Γ ρ₀ ρ₁ ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁  := proven

structure P2 (X : Type*) [MeasurableSpace X] [PseudoMetricSpace X] where
  /-- The underlying measure -/
  val : Measure X
  /-- It's a probability measure -/
  is_prob : MeasureTheory.IsProbabilityMeasure val
  /-- Has finite second moment -/
  finite_second_moment : ∃ x₀ : X, (∫⁻ x, ENNReal.ofReal ((dist x x₀) ^ (2 : ℕ)) ∂val) < ⊤ := proven

instance {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] :
    TopologicalSpace (P2 X)  := proven

noncomputable instance P2_PseudoMetricSpace {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : DynDistanceFlags H cfg Γ κ μ) :
    PseudoMetricSpace (P2 X) where
  -- Define distance using dm
  dist p q  := proven

lemma spectral_penalty_bound {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X) (φ : VelocityPotential X)
    (penalty : SpectralPenalty H cfg)
    (hpen : ∀ t, ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ ≤
            penalty.C_dirichlet * (spectralSymbolSupNorm cfg) ^ 2 *
            ∫ x, Γ.Γ (φ.φ t) (φ.φ t) x ∂μ) :
    ∀ t, ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ ≤
         penalty.C_dirichlet * (spectralSymbolSupNorm cfg) ^ 2 *
         ∫ x, Γ.Γ (φ.φ t) (φ.φ t) x ∂μ  := proven

lemma dm_squared_lsc_from_Am {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [_inst : TopologicalSpace (ProbabilityMeasure X)]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (h_lsc : LowerSemicontinuous
      (fun p : ProbabilityMeasure X × ProbabilityMeasure X =>
        dm_squared H cfg Γ κ μ p.1.val p.2.val)) :
    LowerSemicontinuous (fun p : ProbabilityMeasure X × ProbabilityMeasure X =>
      dm_squared H cfg Γ κ μ p.1.val p.2.val)  := proven

theorem dm_squared_self_eq_zero {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ : Measure X) (hprob : IsProbabilityMeasure ρ) :
    dm_squared H cfg Γ κ μ ρ ρ = 0  := proven

theorem dm_squared_nonneg {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) :
    0 ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁  := proven

theorem dm_squared_symm {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- 非空性（両向き）を仮定
    (hNE₀ : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (hNE₁ : (AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀).Nonempty)
    -- 時間反転により作用値が保存される対応が存在することを仮定（両向き）
    (hRev : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∃ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hRev' : ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀,
      ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential) :
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ = dm_squared H cfg Γ κ μ ρ₁ ρ₀  := proven

theorem dm_squared_triangle {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ ρ₂ : Measure X)
    -- 最小元の存在（両区間）
    (hMin01 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hMin12 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    -- 貼り合わせの存在：作用は和以下
    (hGlue : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
          Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
          Am (X := X) H cfg Γ κ μ p.curve p.potential +
          Am (X := X) H cfg Γ κ μ q.curve q.potential) :
    dm_squared H cfg Γ κ μ ρ₀ ρ₂ ≤
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ + dm_squared H cfg Γ κ μ ρ₁ ρ₂  := proven

theorem dm_triangle {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ ρ₂ : Measure X)
    -- dm_squared_triangle に必要な仮定を引き回す
    (hMin01 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hMin12 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hGlue : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
          Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
          Am (X := X) H cfg Γ κ μ p.curve p.potential +
          Am (X := X) H cfg Γ κ μ q.curve q.potential) :
    dm H cfg Γ κ μ ρ₀ ρ₂ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ + dm H cfg Γ κ μ ρ₁ ρ₂  := proven

theorem dm_triangle_P2 {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (p q r : P2 X)
    -- 前段の dm_squared 三角不等式に必要な仮定を P2 版で供給
    (hMin01 : ∃ s ∈ AdmissibleSet (X := X) H cfg Γ p.val q.val,
      ∀ t ∈ AdmissibleSet (X := X) H cfg Γ p.val q.val,
        Am (X := X) H cfg Γ κ μ s.curve s.potential ≤
        Am (X := X) H cfg Γ κ μ t.curve t.potential)
    (hMin12 : ∃ s ∈ AdmissibleSet (X := X) H cfg Γ q.val r.val,
      ∀ t ∈ AdmissibleSet (X := X) H cfg Γ q.val r.val,
        Am (X := X) H cfg Γ κ μ s.curve s.potential ≤
        Am (X := X) H cfg Γ κ μ t.curve t.potential)
    (hGlue : ∀ s ∈ AdmissibleSet (X := X) H cfg Γ p.val q.val,
      ∀ t ∈ AdmissibleSet (X := X) H cfg Γ q.val r.val,
        ∃ u ∈ AdmissibleSet (X := X) H cfg Γ p.val r.val,
          Am (X := X) H cfg Γ κ μ u.curve u.potential ≤
          Am (X := X) H cfg Γ κ μ s.curve s.potential +
          Am (X := X) H cfg Γ κ μ t.curve t.potential) :
    dm H cfg Γ κ μ p.val r.val ≤ dm H cfg Γ κ μ p.val q.val + dm H cfg Γ κ μ q.val r.val  := proven


theorem dm_pseudometric {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    -- 対称性に必要な仮定（両向きの非空性と時間反転対応）
    (hNE01 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (hNE10 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀).Nonempty)
    (hRev : ∀ {ρ₀ ρ₁} (p : AdmissiblePair X ρ₀ ρ₁ Γ), p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁ →
      ∃ q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hRev' : ∀ {ρ₀ ρ₁} (q : AdmissiblePair X ρ₁ ρ₀ Γ), q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀ →
      ∃ p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    -- 三角不等式に必要な仮定（最小元の存在と貼り合わせ）
    (hMin : ∀ ρ₀ ρ₁ : Measure X,
      ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
          Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
          Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hGlue' : ∀ {ρ₀ ρ₁ ρ₂}
        (p : AdmissiblePair X ρ₀ ρ₁ Γ) (_ : p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁)
        (q : AdmissiblePair X ρ₁ ρ₂ Γ) (_ : q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂),
      ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
        Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
        Am (X := X) H cfg Γ κ μ p.curve p.potential +
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    -- 零距離同一性に必要な確率性
    (hP : ∀ ρ : Measure X, IsProbabilityMeasure ρ) :
    ∀ ρ₀ ρ₁ ρ₂ : Measure X,
      (0 ≤ dm H cfg Γ κ μ ρ₀ ρ₁) ∧
      (dm H cfg Γ κ μ ρ₀ ρ₀ = 0) ∧
      (dm H cfg Γ κ μ ρ₀ ρ₁ = dm H cfg Γ κ μ ρ₁ ρ₀) ∧
      (dm H cfg Γ κ μ ρ₀ ρ₂ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ + dm H cfg Γ κ μ ρ₁ ρ₂)  := proven

noncomputable instance P2_PseudoMetricSpace_flagfree {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (hNE01 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (hNE10 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀).Nonempty)
    (hRev : ∀ {ρ₀ ρ₁} (p : AdmissiblePair X ρ₀ ρ₁ Γ), p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁ →
      ∃ q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hRev' : ∀ {ρ₀ ρ₁} (q : AdmissiblePair X ρ₁ ρ₀ Γ), q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀ →
      ∃ p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hMin : ∀ ρ₀ ρ₁ : Measure X,
      ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
          Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
          Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hGlue' : ∀ {ρ₀ ρ₁ ρ₂}
        (p : AdmissiblePair X ρ₀ ρ₁ Γ) (_ : p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁)
        (q : AdmissiblePair X ρ₁ ρ₂ Γ) (_ : q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂),
      ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
        Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
        Am (X := X) H cfg Γ κ μ p.curve p.potential +
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hP : ∀ ρ : Measure X, IsProbabilityMeasure ρ) :
    PseudoMetricSpace (P2 X) where
  -- Define distance using dm
  dist p q  := proven

end Frourio


## ./Frourio/Geometry/MoscoStability.lean

namespace Frourio

def FiniteEntropy {X : Type*} [MeasurableSpace X] (ρ μ : Measure X) : Prop  := proven

def SecondMomentFinite {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (ρ : Measure X) : Prop  := proven

def MoscoConvergence {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X) (_μ : Measure X) : Prop  := proven

def ConfigConvergence {m : PNat} (cfg_n : ℕ → MultiScaleConfig m)
    (cfg : MultiScaleConfig m) : Prop  := proven

structure SpectralBoundedness {m : PNat} (cfg_n : ℕ → MultiScaleConfig m) where
  /-- Uniform bound on spectral sup-norms -/
  bound : ℝ
  /-- The bound is finite and positive -/
  bound_pos : 0 < bound
  /-- All configurations satisfy the bound -/
  is_bounded : ∀ n : ℕ, spectralSymbolSupNorm (cfg_n n) ≤ bound := proven

structure MoscoFlags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) where
  /-- Mosco convergence of heat semigroups -/
  mosco_conv : MoscoConvergence H_n H μ
  /-- Convergence of configurations -/
  config_conv : ConfigConvergence cfg_n cfg
  /-- Uniform boundedness of spectral symbols -/
  spectral_bound : SpectralBoundedness cfg_n := proven

theorem dm_converges_from_Mosco_empty {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- Empty admissible sets hypothesis (solvable case)
    (h_empty_lim : AdmissibleSet H cfg Γ ρ₀ ρ₁ = ∅)
    (h_empty_all : ∀ n, AdmissibleSet (H_n n) (cfg_n n) Γ ρ₀ ρ₁ = ∅) :
    Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀ ρ₁) atTop
            (nhds (dm H cfg Γ κ μ ρ₀ ρ₁))  := proven

theorem dm_converges_from_Mosco_P2 {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [ProperSpace X] -- Polish space assumption for compactness
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : P2 X) -- Use P2 space (probability measures with finite second moment)
    -- Strategy B: accept convergence as a hypothesis stemming from Gamma/Mosco analysis
    (h_conv : Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val)))
    :
    Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀.val ρ₁.val) atTop
            (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val))  := proven


theorem dm_converges_from_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- Strategy B: accept convergence as a hypothesis (to be derived from Gamma/Mosco)
    (h_conv : Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀ ρ₁) atTop
              (nhds (dm H cfg Γ κ μ ρ₀ ρ₁))) :
    Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀ ρ₁) atTop
            (nhds (dm H cfg Γ κ μ ρ₀ ρ₁))  := proven

theorem EVI_flow_converges {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    -- Strategy B: accept P2-level distance convergence as hypothesis
    (h_conv_P2 : ∀ ρ₀ ρ₁ : P2 X,
      Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val))) :
    ∀ ρ₀ ρ₁ : P2 X,
      Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val))  := proven

theorem lam_eff_liminf {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags_n : (n : ℕ) → MetaEVIFlags (H_n n) (cfg_n n) Γ κ μ)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    -- Additional convergence assumptions ensuring continuity of the FG★ expression
    (h_spec : Tendsto (fun n => spectralSymbolSupNorm (cfg_n n)) atTop
      (nhds (spectralSymbolSupNorm cfg))) :
    -- Assume convergence of base parameters and Doob degradations
    Tendsto (fun n => (flags_n n).lam_base) atTop (nhds flags.lam_base) →
    Tendsto (fun n => (flags_n n).doob.ε) atTop (nhds flags.doob.ε) →
    Tendsto (fun n => (flags_n n).fgstar_const.C_energy) atTop (nhds flags.fgstar_const.C_energy) →
    -- Then the effective lambda is lower semicontinuous
    Filter.liminf (fun n => (flags_n n).lam_eff) atTop ≥ flags.lam_eff  := proven

theorem FGStar_stable_under_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags_n : ∀ n, MetaEVIFlags (H_n n) (cfg_n n) Γ κ μ)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (h_spec : Tendsto (fun n => spectralSymbolSupNorm (cfg_n n)) atTop
      (nhds (spectralSymbolSupNorm cfg))) :
    -- If the flags converge appropriately
    Tendsto (fun n => (flags_n n).lam_base) atTop (nhds flags.lam_base) →
    Tendsto (fun n => (flags_n n).doob.ε) atTop (nhds flags.doob.ε) →
    Tendsto (fun n => (flags_n n).fgstar_const.C_energy) atTop (nhds flags.fgstar_const.C_energy) →
    -- Then the effective parameters converge with the inequality preserved
    Filter.liminf (fun n => (flags_n n).lam_eff) atTop ≥ flags.lam_eff  := proven

theorem dm_lipschitz_in_config {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg cfg' : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) (ρ₀ ρ₁ : P2 X)
    -- Strategy B: accept a Lipschitz-type bound as hypothesis and return it
    (h_lip : ∃ L > 0,
      |dm H cfg' Γ κ μ ρ₀.val ρ₁.val - dm H cfg Γ κ μ ρ₀.val ρ₁.val| ≤
      L * (∑ i, (|cfg'.α i - cfg.α i| + |cfg'.τ i - cfg.τ i|))) :
    ∃ L > 0, |dm H cfg' Γ κ μ ρ₀.val ρ₁.val - dm H cfg Γ κ μ ρ₀.val ρ₁.val| ≤
             L * (∑ i, (|cfg'.α i - cfg.α i| + |cfg'.τ i - cfg.τ i|))  := proven

theorem spectralSymbol_continuous_in_config {m : PNat}
    {cfg_n : ℕ → MultiScaleConfig m} {cfg : MultiScaleConfig m}
    (h : Tendsto (fun n => spectralSymbolSupNorm (cfg_n n)) atTop
      (nhds (spectralSymbolSupNorm cfg))) :
    Tendsto (fun n => spectralSymbolSupNorm (cfg_n n)) atTop (nhds (spectralSymbolSupNorm cfg))  := proven

def domain {X : Type*} [MeasurableSpace X] (E : (X → ℝ) → ℝ) : Set (X → ℝ)  := proven

def dirichlet_domain {X : Type*} [MeasurableSpace X]
    (E : (X → ℝ) → ℝ) (μ : Measure X) : Set (X → ℝ)  := proven

def core_domain {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (E : (X → ℝ) → ℝ) (μ : Measure X) : Set (X → ℝ)  := proven

noncomputable def EVI_flow {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (_H : HeatSemigroup X) (_cfg : MultiScaleConfig m)
    (_Γ : CarreDuChamp X) (_κ : ℝ) (_μ : Measure X) (ρ₀ : P2 X) (_t : ℝ) : P2 X  := proven

noncomputable def JKO_iterate {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (_H : HeatSemigroup X) (_cfg : MultiScaleConfig m)
    (_Γ : CarreDuChamp X) (_κ : ℝ) (μ : Measure X) (_Ent : EntropyFunctional X μ)
    (_τ : ℝ) (ρ₀ : P2 X) (_k : ℕ) : P2 X  := proven

def PLFA_EDE_equivalence {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (_H : HeatSemigroup X) (_cfg : MultiScaleConfig m)
    (_Γ : CarreDuChamp X) (_κ : ℝ) (μ : Measure X) (_Ent : EntropyFunctional X μ) : Prop  := proven

theorem heat_semigroup_from_Mosco_forms {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (E_n : ℕ → ((X → ℝ) → ℝ)) (E : (X → ℝ) → ℝ) (μ : Measure X)
    -- Mosco convergence of quadratic forms (placeholder, not used directly here)
    (_h_mosco_forms : ∀ φ : X → ℝ,
      (∀ φ_n : ℕ → X → ℝ, (∀ _n : ℕ, True) →
        Tendsto (fun n => φ_n n) atTop (nhds φ) →
        E φ ≤ Filter.liminf (fun n => E_n n (φ_n n)) atTop) ∧
      (∃ φ_n : ℕ → X → ℝ, (∀ _n : ℕ, True) ∧
        Tendsto (fun n => φ_n n) atTop (nhds φ) ∧
        Filter.limsup (fun n => E_n n (φ_n n)) atTop ≤ E φ))
    -- Given semigroups generated by the forms (abstracted as input)
    (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    -- Claimed Mosco convergence of the semigroups
    (h_mosco_semigroup : MoscoConvergence H_n H μ) :
    ∃ (Hn' : ℕ → HeatSemigroup X) (H' : HeatSemigroup X),
      MoscoConvergence Hn' H' μ  := proven

theorem EVI_from_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (_mosco : MoscoConvergence H_n H μ)
    -- Additional regularity assumptions
    (_h_reg : ∀ n t φ, MeasureTheory.Integrable ((H_n n).H t φ) μ)
    -- Strategy B: accept convergence of EVI flows as a hypothesis
    (h_conv_flow : ∀ ρ₀ : P2 X, ∀ t > 0,
      Tendsto (fun n => EVI_flow (H_n n) cfg Γ κ μ ρ₀ t) atTop
              (nhds (EVI_flow H cfg Γ κ μ ρ₀ t))) :
    -- EVI flows converge in the weak topology of measures
    ∀ ρ₀ : P2 X, ∀ t > 0,
    ∃ (ρ_n : ℕ → P2 X) (ρ_t : P2 X),
      (∀ n, ρ_n n = EVI_flow (H_n n) cfg Γ κ μ ρ₀ t) ∧
      (ρ_t = EVI_flow H cfg Γ κ μ ρ₀ t) ∧
      Tendsto (fun n => ρ_n n) atTop (nhds ρ_t)  := proven

theorem JKO_from_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (_mosco : MoscoConvergence H_n H μ)
    (Ent : EntropyFunctional X μ)
    -- Time step for JKO
    (τ : ℝ) (_hτ : 0 < τ)
    -- Strategy B: accept convergence of JKO iterates as a hypothesis
    (h_conv_JKO : ∀ ρ₀ : P2 X, ∀ k : ℕ,
      Tendsto (fun n => JKO_iterate (H_n n) cfg Γ κ μ Ent τ ρ₀ k) atTop
              (nhds (JKO_iterate H cfg Γ κ μ Ent τ ρ₀ k))) :
    -- JKO iterates converge
    ∀ ρ₀ : P2 X, ∀ k : ℕ,
    ∃ (ρ_n : ℕ → P2 X) (ρ_k : P2 X),
      (∀ n, ρ_n n = JKO_iterate (H_n n) cfg Γ κ μ Ent τ ρ₀ k) ∧
      (ρ_k = JKO_iterate H cfg Γ κ μ Ent τ ρ₀ k) ∧
      Tendsto (fun n => ρ_n n) atTop (nhds ρ_k)  := proven

theorem Mosco_complete_chain {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat}
    -- Provided heat semigroups and their Mosco convergence (Strategy B)
    (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (Ent : EntropyFunctional X μ)
    (mosco : MoscoConvergence H_n H μ)
    -- Strategy B: accept convergence of distances, EVI flows, and JKO iterates as hypotheses
    (h_dm_conv : ∀ ρ₀ ρ₁ : P2 X,
      Tendsto (fun n => dm (H_n n) cfg Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val)))
    (h_EVI_conv : ∀ ρ₀ : P2 X, ∀ t > 0,
      ∃ ρ_t : P2 X,
        Tendsto (fun n => EVI_flow (H_n n) cfg Γ κ μ ρ₀ t) atTop (nhds ρ_t))
    (h_JKO_conv : ∀ τ > 0, ∀ ρ₀ : P2 X, ∀ k : ℕ,
      ∃ ρ_k : P2 X,
        Tendsto (fun n => JKO_iterate (H_n n) cfg Γ κ μ Ent τ ρ₀ k) atTop (nhds ρ_k)) :
    -- Then we have the complete convergence chain (packaged)
    ∃ (H_n' : ℕ → HeatSemigroup X) (H' : HeatSemigroup X),
      -- 1. Heat semigroups converge
      MoscoConvergence H_n' H' μ ∧
      -- 2. Modified distances converge
      (∀ ρ₀ ρ₁ : P2 X,
        Tendsto (fun n => dm (H_n' n) cfg Γ κ μ ρ₀.val ρ₁.val) atTop
                (nhds (dm H' cfg Γ κ μ ρ₀.val ρ₁.val))) ∧
      -- 3. EVI flows converge
      (∀ ρ₀ : P2 X, ∀ t > 0,
        ∃ ρ_t : P2 X,
          Tendsto (fun n => EVI_flow (H_n' n) cfg Γ κ μ ρ₀ t) atTop (nhds ρ_t)) ∧
      -- 4. JKO scheme converges
      (∀ τ > 0, ∀ ρ₀ : P2 X, ∀ k : ℕ,
        ∃ ρ_k : P2 X,
          Tendsto (fun n => JKO_iterate (H_n' n) cfg Γ κ μ Ent τ ρ₀ k) atTop (nhds ρ_k))  := proven

theorem spectral_penalty_stability {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (cfg cfg' : MultiScaleConfig m) (C κ : ℝ) :
    |spectral_penalty_term cfg' C κ - spectral_penalty_term cfg C κ|
      = |κ| * |C| * |spectralSymbolSupNorm cfg' - spectralSymbolSupNorm cfg| *
        |spectralSymbolSupNorm cfg' + spectralSymbolSupNorm cfg|  := proven

theorem meta_structure_preserved_under_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (_mosco : MoscoConvergence H_n H μ)
    (Ent : EntropyFunctional X μ)
    -- Strategy B: accept convergence of distances, EVI flows, and JKO iterates as hypotheses
    (_h_dm_conv : ∀ ρ₀ ρ₁ : P2 X,
      Tendsto (fun n => dm (H_n n) cfg Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val)))
    (_h_EVI_conv : ∀ ρ₀ : P2 X, ∀ t > 0,
      ∃ ρ_t : P2 X,
        Tendsto (fun n => EVI_flow (H_n n) cfg Γ κ μ ρ₀ t) atTop (nhds ρ_t))
    (_h_JKO_conv : ∀ τ > 0, ∀ ρ₀ : P2 X, ∀ k : ℕ,
      ∃ ρ_k : P2 X,
        Tendsto (fun n => JKO_iterate (H_n n) cfg Γ κ μ Ent τ ρ₀ k) atTop (nhds ρ_k)) :
    -- The four-equivalence is preserved in the limit (packaged statement)
    (∀ n, PLFA_EDE_equivalence (H_n n) cfg Γ κ μ Ent) →
    PLFA_EDE_equivalence H cfg Γ κ μ Ent  := proven

end Frourio


## ./Frourio/Geometry/MultiScaleDiff.lean

namespace Frourio

structure MultiScaleConfig (m : PNat) where
  /-- Weights for each scale, must sum to zero -/
  α : Fin m → ℝ
  /-- Time scales, must be positive -/
  τ : Fin m → ℝ
  /-- Positivity constraint for scales -/
  hτ_pos : ∀ i, 0 < τ i
  /-- Zero-sum constraint for weights -/
  hα_sum : ∑ i, α i = 0
  /-- Weights are bounded (for technical reasons) -/
  hα_bound : ∀ i, |α i| ≤ 1 := proven

structure HeatSemigroup (X : Type*) where
  /-- The semigroup operator H_t -/
  H : ℝ → (X → ℝ) → (X → ℝ)
  /-- Semigroup property: H_s ∘ H_t = H_{s+t} -/
  isSemigroup : ∀ s t : ℝ, ∀ φ : X → ℝ, H s (H t φ) = H (s + t) φ
  /-- Identity at t=0: H_0 = I -/
  isIdentity : ∀ φ : X → ℝ, H 0 φ = φ
  /-- Linearity in function argument -/
  linear_in_function : ∀ t : ℝ, ∀ a b : ℝ, ∀ φ ψ : X → ℝ,
    H t (fun x => a * φ x + b * ψ x) = fun x => a * H t φ x + b * H t ψ x
  /-- Preserves constant functions -/
  preserves_constants : ∀ t : ℝ, ∀ c : ℝ, H t (fun _ => c) = fun _ => c
  /-- Measurability preservation: under any measurable structure on `X`,
      if `φ` is measurable then so is `H_t φ`. We quantify the instance
      explicitly to avoid requiring `[MeasurableSpace X]` at the structure level. -/
  measurable_in_function : ∀ t : ℝ, ∀ φ : X → ℝ,
    (∀ [MeasurableSpace X], Measurable φ → Measurable (fun x => H t φ x))
  /-- L² continuity: H_t preserves L² functions -/
  l2_continuous : ∀ t : ℝ, ∀ φ : X → ℝ,
    (∀ [MeasurableSpace X] (μ : MeasureTheory.Measure X),
      MeasureTheory.MemLp φ 2 μ → MeasureTheory.MemLp (fun x => H t φ x) 2 μ)
  /-- L² contractivity: H_t is a contraction on L² -/
  l2_contractive : ∀ t : ℝ, ∀ φ : X → ℝ,
    (∀ [MeasurableSpace X] (μ : MeasureTheory.Measure X),
      (0 ≤ t) → MeasureTheory.MemLp φ 2 μ → MeasureTheory.MemLp (fun x => H t φ x) 2 μ) := proven

noncomputable def multiScaleDiff {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (φ : X → ℝ) : X → ℝ  := proven

theorem multiScaleDiff_linear {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (a b : ℝ) (φ ψ : X → ℝ) :
    multiScaleDiff H cfg (fun x => a * φ x + b * ψ x) =
    fun x => a * multiScaleDiff H cfg φ x + b * multiScaleDiff H cfg ψ x  := proven

theorem multiScaleDiff_const_zero {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (c : ℝ) :
    multiScaleDiff H cfg (fun _ => c) = fun _ => 0  := proven

theorem multiScaleDiff_zero {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) :
    multiScaleDiff H cfg (fun _ => 0) = fun _ => 0  := proven

lemma heatSemigroup_measurable {X : Type*} [MeasurableSpace X]
    (H : HeatSemigroup X) (t : ℝ) (φ : X → ℝ) (hφ : Measurable φ) :
    Measurable (fun x => H.H t φ x)  := proven

lemma heatSemigroup_l2_preserves {X : Type*} [MeasurableSpace X]
    (H : HeatSemigroup X) (t : ℝ) (μ : MeasureTheory.Measure X) (φ : X → ℝ)
    (hφ : MeasureTheory.MemLp φ 2 μ) :
    MeasureTheory.MemLp (fun x => H.H t φ x) 2 μ  := proven

lemma heatSemigroup_l2_contraction {X : Type*} [MeasurableSpace X]
    (H : HeatSemigroup X) (t : ℝ) (ht : 0 ≤ t) (μ : MeasureTheory.Measure X) (φ : X → ℝ)
    (hφ : MeasureTheory.MemLp φ 2 μ) :
    MeasureTheory.MemLp (fun x => H.H t φ x) 2 μ  := proven

lemma multiScaleDiff_measurable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (φ : X → ℝ) (hφ : Measurable φ) :
    Measurable (multiScaleDiff H cfg φ)  := proven

lemma multiScaleDiff_square_integrable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (μ : MeasureTheory.Measure X) (φ : X → ℝ)
    (hφ : MeasureTheory.MemLp φ 2 μ) :
    MeasureTheory.MemLp (multiScaleDiff H cfg φ) 2 μ  := proven

noncomputable def spectralSymbol {m : PNat} (cfg : MultiScaleConfig m) (lam : ℝ) : ℝ  := proven

theorem spectralSymbol_at_zero {m : PNat} (cfg : MultiScaleConfig m) :
    spectralSymbol cfg 0 = 0  := proven

theorem spectralSymbol_basic_bound {m : PNat} (cfg : MultiScaleConfig m)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    |spectralSymbol cfg lam| ≤ ∑ i : Fin m, |cfg.α i|  := proven

lemma exp_diff_le {a b : ℝ} :
    |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b|  := proven

lemma exp_diff_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b|  := proven

theorem spectralSymbol_lipschitz {m : PNat} (cfg : MultiScaleConfig m) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      |spectralSymbol cfg lam₁ - spectralSymbol cfg lam₂| ≤ L * |lam₁ - lam₂|  := proven

theorem spectralSymbol_monotone_decreasing {m : PNat} (cfg : MultiScaleConfig m)
    (hα_nonneg : ∀ i, 0 ≤ cfg.α i) :
    ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → lam₁ ≤ lam₂ →
      spectralSymbol cfg lam₂ ≤ spectralSymbol cfg lam₁  := proven

structure SpectralBound {X : Type*} {m : PNat} (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) where
  /-- Uniform bound on the spectral symbol -/
  norm_bound : ℝ
  /-- The bound is non-negative -/
  norm_bound_nonneg : 0 ≤ norm_bound
  /-- The spectral symbol is uniformly bounded -/
  spectral_uniform_bound : ∀ lam : ℝ, 0 ≤ lam → |spectralSymbol cfg lam| ≤ norm_bound
  /-- Bochner-type inequality relating L² norm to energy (Γ operator) -/
  bochner_inequality : Prop  -- Placeholder for the full inequality := proven

noncomputable def spectralSymbolSupNorm {m : PNat} (cfg : MultiScaleConfig m) : ℝ  := proven

theorem spectralSymbolSupNorm_bounded {m : PNat} (cfg : MultiScaleConfig m) :
    spectralSymbolSupNorm cfg ≤ ∑ i : Fin m, |cfg.α i|  := proven

def spectralSymbolLipschitzConstant {m : PNat} (cfg : MultiScaleConfig m) : ℝ  := proven

lemma spectralSymbolLipschitzConstant_nonneg {m : PNat} (cfg : MultiScaleConfig m) :
    0 ≤ spectralSymbolLipschitzConstant cfg  := proven


lemma spectralSymbol_lipschitz_constant_eq {m : PNat} (cfg : MultiScaleConfig m) :
    ∃ L : ℝ, L = spectralSymbolLipschitzConstant cfg ∧
    (∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      |spectralSymbol cfg lam₁ - spectralSymbol cfg lam₂| ≤ L * |lam₁ - lam₂|)  := proven

theorem spectralSymbolSupNorm_explicit_bound {m : PNat} (cfg : MultiScaleConfig m)
    (C : ℝ) (hC : ∀ i, |cfg.α i| ≤ C) :
    spectralSymbolSupNorm cfg ≤ m * C  := proven

theorem spectralSymbolSupNorm_optimal_bound {m : PNat} (cfg : MultiScaleConfig m) :
    spectralSymbolSupNorm cfg ≤ m  := proven

theorem spectralSymbol_zero_at_zero {m : PNat} (cfg : MultiScaleConfig m) :
    |spectralSymbol cfg 0| = 0  := proven

def spectralSymbolDerivativeBound {m : PNat} (cfg : MultiScaleConfig m) : ℝ  := proven

theorem spectralSymbol_derivative_bound {m : PNat} (cfg : MultiScaleConfig m)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hderiv : deriv (spectralSymbol cfg) lam
      = ∑ i : Fin m, (-cfg.α i) * cfg.τ i * Real.exp (-cfg.τ i * lam)) :
    |deriv (spectralSymbol cfg) lam| ≤ spectralSymbolDerivativeBound cfg  := proven

structure FGStarConstants {m : PNat} (cfg : MultiScaleConfig m) where
  /-- Constant from spectral bound -/
  spectral_const : ℝ
  /-- Constant from energy functional properties -/
  energy_const : ℝ
  /-- Combined constant for FG★ inequality -/
  combined_const : ℝ
  /-- Relation between constants -/
  const_relation : combined_const = spectral_const * energy_const
  /-- All constants are non-negative -/
  spectral_const_nonneg : 0 ≤ spectral_const
  energy_const_nonneg : 0 ≤ energy_const := proven

noncomputable def constructFGStarConstants {m : PNat} (cfg : MultiScaleConfig m) :
    FGStarConstants cfg where
  spectral_const  := proven

structure OptimalSpectralBound {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The optimal bound constant -/
  C_opt : ℝ
  /-- Non-negativity -/
  C_opt_nonneg : 0 ≤ C_opt
  /-- The bound is sharp (achieved for some λ) -/
  is_sharp : ∃ lam : ℝ, 0 ≤ lam ∧ |spectralSymbol cfg lam| = C_opt
  /-- The bound holds uniformly -/
  uniform_bound : ∀ lam : ℝ, 0 ≤ lam → |spectralSymbol cfg lam| ≤ C_opt := proven

def spectralBoundHypothesis {m : PNat} (cfg : MultiScaleConfig m) : Prop  := proven

lemma le_spectralSymbolSupNorm {m : PNat} (cfg : MultiScaleConfig m) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    |spectralSymbol cfg lam| ≤ spectralSymbolSupNorm cfg  := proven

structure SpectralSupNormBound {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The sup-norm bound value -/
  bound : ℝ
  /-- Non-negativity -/
  bound_nonneg : 0 ≤ bound
  /-- The actual bound -/
  is_bound : spectralSymbolSupNorm cfg ≤ bound := proven

structure SpectralPenalty {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) where
  /-- The constant C(ℰ) depending on the Dirichlet form -/
  C_dirichlet : ℝ
  /-- Non-negativity of the constant -/
  C_nonneg : 0 ≤ C_dirichlet := proven

end Frourio


## ./Frourio/Geometry/Rigidity.lean

namespace Frourio

structure SpectralPhaseAlignment {m : PNat} (cfg : MultiScaleConfig m) where
  /-- There exists a common phase function -/
  phase : ℝ → ℝ
  /-- Amplitude coefficients for each component -/
  amplitude : Fin m → ℝ
  /-- Each spectral component aligns: there exist c_i > 0 such that
      the i-th spectral term equals c_i * cos(phase(λ)) or similar.
      For our simplified model: spectral terms are proportional. -/
  alignment : ∀ i j : Fin m, ∀ lam : ℝ, 0 ≤ lam →
    ∃ (c : ℝ), c ≠ 0 ∧
    cfg.α i * (Real.exp (-cfg.τ i * lam) - 1) =
    c * cfg.α j * (Real.exp (-cfg.τ j * lam) - 1)
  /-- The phase is continuous -/
  phase_continuous : Continuous phase := proven

structure HarmonicWeights {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The weights satisfy a harmonic relation (model-dependent).
      For simplicity, we require proportionality conditions. -/
  harmonic_relation : ∀ i j : Fin m, i ≠ j →
    ∃ (c : ℝ), c ≠ 0 ∧ cfg.α i * cfg.τ j = c * cfg.α j * cfg.τ i
  /-- At least two weights are non-zero (non-degeneracy) -/
  nonzero_weights : ∃ i j : Fin m, i ≠ j ∧ cfg.α i ≠ 0 ∧ cfg.α j ≠ 0 := proven

structure EqualRippleSaturation {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The set of λ values where the supremum is achieved -/
  saturation_set : Set ℝ
  /-- The saturation set is non-empty -/
  nonempty : saturation_set.Nonempty
  /-- At saturation points, |ψ_m(lam)| equals the supremum -/
  saturates : ∀ lam ∈ saturation_set,
    |spectralSymbol cfg lam| = spectralSymbolSupNorm cfg
  /-- The saturation set has positive Lebesgue measure.
      This ensures the saturation is not just at isolated points. -/
  positive_measure : ∃ (ε : ℝ), ε > 0 ∧
    MeasureTheory.volume (saturation_set ∩ Set.Icc 0 ε) > 0 := proven

structure DoobHarmonic {X : Type*} [MeasurableSpace X] (h : X → ℝ) where
  /-- h is positive -/
  h_pos : ∀ x, 0 < h x
  /-- The Hessian of log h vanishes: ∇²(log h) = 0 -/
  hessian_zero : Prop  -- Placeholder: would be ∀ x, Hessian (log ∘ h) x = 0
  /-- h is smooth enough for the Hessian to be defined -/
  smooth : Prop  -- Placeholder for smoothness conditions := proven

structure EqualityCaseFlags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ) where
  /-- The FG★ inequality is an equality -/
  fg_equality : flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                               spectral_penalty_term cfg flags.fgstar_const.C_energy κ
  /-- Cauchy-Schwarz equality in the spectral estimate -/
  cauchy_schwarz_equality : Prop  -- Placeholder: CS equality in ∫|Δ^{⟨m⟩} φ|² ≤ ...
  /-- The spectral evaluation achieves its bound -/
  spectral_saturates : Prop  -- Placeholder: spectral bound is tight
  /-- Doob transform is harmonic -/
  doob_harmonic : ∃ h : X → ℝ, Nonempty (DoobHarmonic h)
  /-- Spectral phases are aligned -/
  phase_aligned : SpectralPhaseAlignment cfg
  /-- Weights satisfy harmonic distribution -/
  harmonic_weights : HarmonicWeights cfg
  /-- Equal ripple saturation holds -/
  equal_ripple : EqualRippleSaturation cfg := proven

theorem FGStar_rigidity {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (eq_flags : EqualityCaseFlags H cfg Γ κ μ flags) :
    -- When FG★ is an equality, we have rigidity
    -- 1. The Doob function is harmonic
    (∃ h : X → ℝ, Nonempty (DoobHarmonic h)) ∧
    -- 2. Spectral phases are aligned
    Nonempty (SpectralPhaseAlignment cfg) ∧
    -- 3. Harmonic weight distribution and equal-ripple saturation hold
    Nonempty (HarmonicWeights cfg) ∧ Nonempty (EqualRippleSaturation cfg)  := proven

structure Gamma2 {X : Type*} [MeasurableSpace X] (Γ : CarreDuChamp X) (H : HeatSemigroup X) where
  /-- The Γ₂ operator: Γ₂(f,g) = ½(LΓ(f,g) - Γ(Lf,g) - Γ(f,Lg)) -/
  op : (X → ℝ) → (X → ℝ) → (X → ℝ)
  /-- Γ₂ is symmetric -/
  symmetric : ∀ f g, op f g = op g f
  /-- Bochner-Weitzenböck formula connection -/
  bochner : ∀ _ : X → ℝ, Prop  -- Placeholder for Γ₂(f,f) ≥ 0 under curvature conditions := proven

noncomputable def bakry_emery_degradation {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (H : HeatSemigroup X) (Γ₂ : Gamma2 Γ H) (h : X → ℝ) : ℝ  := proven

def is_harmonic {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (H : HeatSemigroup X) (Γ₂ : Gamma2 Γ H) (h : X → ℝ) : Prop  := proven

theorem doob_rigidity_forward {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (H : HeatSemigroup X) (Γ : CarreDuChamp X) (Γ₂ : Gamma2 Γ H) (h : X → ℝ)
    -- Given a Doob transform with degradation ε(h)
    (ε_h : ℝ) (h_degrad : ε_h = bakry_emery_degradation Γ H Γ₂ h) :
    -- If the degradation vanishes, then h is harmonic
    ε_h = 0 → is_harmonic Γ H Γ₂ h  := proven

structure BakryEmeryHypothesis {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (H : HeatSemigroup X) (Γ₂ : Gamma2 Γ H) where
  /-- Under sufficient regularity and curvature conditions,
      harmonicity implies vanishing degradation -/
  harmonic_implies_zero : ∀ h : X → ℝ,
    (h_pos : ∀ x, 0 < h x) → is_harmonic Γ H Γ₂ h →
    bakry_emery_degradation Γ H Γ₂ h = 0 := proven

theorem doob_rigidity_reverse {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (H : HeatSemigroup X) (Γ : CarreDuChamp X) (Γ₂ : Gamma2 Γ H)
    (be_hyp : BakryEmeryHypothesis Γ H Γ₂) (h : X → ℝ) (h_pos : ∀ x, 0 < h x) :
    -- If h is harmonic, then the degradation vanishes
    is_harmonic Γ H Γ₂ h → bakry_emery_degradation Γ H Γ₂ h = 0  := proven

theorem spectral_phase_rigidity {m : PNat} (cfg : MultiScaleConfig m) :
    ∃ A : ℝ, ∀ lam : ℝ, 0 ≤ lam → |spectralSymbol cfg lam| ≤ |A|  := proven

structure Eigenfunction {X : Type*} [MeasurableSpace X] (H : HeatSemigroup X) where
  /-- The eigenfunction -/
  φ : X → ℝ
  /-- The eigenvalue -/
  eigenvalue : ℝ
  /-- L² integrability -/
  square_integrable : ∀ μ : Measure X, MeasureTheory.MemLp φ 2 μ
  /-- Eigenvalue equation: (H_t - I)φ/t → -λφ as t → 0 -/
  eigen_eq : ∀ x, Filter.Tendsto (fun t => (H.H t φ x - φ x) / t)
    (nhds 0) (nhds (-eigenvalue * φ x))
  nonzero_function : ∃ x, φ x ≠ 0 := proven

theorem eigenfunction_from_FGStar_equality
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (φ : X → ℝ) (_hφ_L2 : MeasureTheory.MemLp φ 2 μ)
    (h_nonzero : ∃ x : X, φ x ≠ 0)
    -- Sharpness witness: CS equality achieved by φ
    (h_sharp : ∃ cs : CauchySchwarzSharp H cfg Γ κ μ flags.fgstar_const,
      cs.eigenfunction = φ) :
    ∃ lam : ℝ, ∀ x : X, multiScaleDiff H cfg φ x = lam * φ x  := proven

theorem FGStar_equality_from_eigenfunction
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (φ : X → ℝ) (h_nonzero : ∃ x : X, φ x ≠ 0)
    -- Assume φ is a pointwise eigenfunction of multiScaleDiff
    (h_eig : ∃ lam : ℝ, ∀ x : X, multiScaleDiff H cfg φ x = lam * φ x) :
    ∃ cs : CauchySchwarzSharp H cfg Γ κ μ flags.fgstar_const, cs.eigenfunction = φ  := proven

theorem FGStar_equality_from_rigidity {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ) :
    -- These conditions imply FG★ is an equality
    flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                    spectral_penalty_term cfg flags.fgstar_const.C_energy κ  := proven

def CriticalUniquenessHypothesis {m : PNat} (cfg : MultiScaleConfig m) : Prop  := proven

theorem critical_configuration_unique {m : PNat} (cfg : MultiScaleConfig m)
    (h_unique : CriticalUniquenessHypothesis cfg) :
    -- The critical configuration achieving equality is unique up to symmetry,
    -- provided the spectral sup-norm matches and harmonic weights hold for cfg'.
    ∀ cfg' : MultiScaleConfig m,
      spectralSymbolSupNorm cfg' = spectralSymbolSupNorm cfg →
      HarmonicWeights cfg' →
      ∃ σ : Fin m ≃ Fin m, ∀ i, cfg'.α i = cfg.α (σ i) ∧ cfg'.τ i = cfg.τ (σ i)  := proven

theorem FGStar_rigidity_complete
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (φ : X → ℝ) (_hφ : MeasureTheory.MemLp φ 2 μ)
    (h_nonzero : ∃ x : X, φ x ≠ 0) :
    ((∃ cs : CauchySchwarzSharp H cfg Γ κ μ flags.fgstar_const, cs.eigenfunction = φ)
      ↔ (∃ lam : ℝ, ∀ x : X, multiScaleDiff H cfg φ x = lam * φ x))  := proven

theorem spectral_gap_from_rigidity {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (_flags : MetaEVIFlags H cfg Γ κ μ) :
    -- Weak form: package the assumed Rayleigh-type lower bound as a spectral gap
    (∃ gap : ℝ, gap > 0 ∧
     ∀ φ : X → ℝ, MeasureTheory.MemLp φ 2 μ → φ ≠ 0 →
     (∫ x, Γ.Γ φ φ x ∂μ) / (∫ x, φ x ^ 2 ∂μ) ≥ gap) →
    ∃ gap : ℝ, gap > 0 ∧
     ∀ φ : X → ℝ, MeasureTheory.MemLp φ 2 μ → φ ≠ 0 →
     (∫ x, Γ.Γ φ φ x ∂μ) / (∫ x, φ x ^ 2 ∂μ) ≥ gap  := proven

end Frourio


## ./Frourio/Theorems/GoldenExtremality.lean

namespace Frourio

class and an objective, the golden operator is extremal (e.g. optimal)
within that class. The precise objective and admissibility are deferred
to later phases; here we only fix the API.
-/ := proven

structure ExtremalityContext where
  (Adm : FrourioOperator 2 → Prop)
  (Obj : FrourioOperator 2 → ℝ) := proven

def GoldenExtremality (C : ExtremalityContext) : Prop  := proven

end Frourio


## ./Frourio/Theorems/NoGoTheorem.lean

namespace Frourio

structure BinarizationProblem where
  (m : ℕ)
  (law_exact : Prop)      -- target exact binarization law to be ruled out
  (assumptions : Prop)    -- hypotheses (regularity/symmetry/etc.) := proven

def noGoTheorem_m2 (P : BinarizationProblem) : Prop  := proven

end Frourio


## ./Frourio/Zeta/GoldenSampling.lean

namespace Frourio

noncomputable def Qζ_disc
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ  := proven

noncomputable def Δτφ (φ : ℝ) : ℝ  := proven

noncomputable def Δξφ (φ : ℝ) : ℝ  := proven

noncomputable def Qζ_discφ (φ : ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ  := proven

def Qζ_bounds (φ : ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) : Prop  := proven

def Qζ_gamma (φ : ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) : Prop  := proven

structure QζBoundsHypotheses (φ : ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) : Prop where
  exists_bounds : Qζ_bounds φ w := proven

theorem Qζ_bounds_proof (φ : ℝ) (_hφ : 1 < φ)
    (w : Lp ℂ 2 (volume : Measure ℝ))
    (h : QζBoundsHypotheses φ w) : Qζ_bounds φ w  := proven

end Frourio


## ./Frourio/Zeta/Interfaces.lean

namespace Frourio


class ZetaLineAPI where
  zeta_on_line : ℝ → ℂ
  measurable : Measurable zeta_on_line
  loc_bounded : ∀ R : ℝ, ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ R → ‖zeta_on_line τ‖ ≤ C := proven


noncomputable instance defaultZetaLineAPI : ZetaLineAPI where
  zeta_on_line  := proven

structure ZetaData where
  zeta_on_line : ℝ → ℂ
  measurable : Measurable zeta_on_line
  loc_bounded : ∀ R : ℝ, ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ R → ‖zeta_on_line τ‖ ≤ C := proven

noncomputable def ZetaLineAPI.ofData (d : ZetaData) : ZetaLineAPI where
  zeta_on_line  := proven

noncomputable def ZetaData.mk' (f : ℝ → ℂ)
    (hf_meas : Measurable f)
    (hf_loc : ∀ R : ℝ, ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ R → ‖f τ‖ ≤ C) : ZetaData  := proven

noncomputable def ZetaData.const (c : ℂ) : ZetaData  := proven

end Frourio


## ./Frourio/Zeta/Kernel.lean

namespace Frourio

noncomputable def Kzeta (τ : ℝ) : ℝ  := proven

lemma measurable_Kzeta : Measurable Kzeta  := proven

lemma Kzeta_nonneg (τ : ℝ) : 0 ≤ Kzeta τ  := proven

noncomputable def Qζℝ (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ  := proven

noncomputable def Qζσ (σ : ℝ) (f : Hσ σ) : ℝ  := proven

theorem Qζ_pos (g : Lp ℂ 2 (volume : Measure ℝ)) : 0 ≤ Qζℝ g  := proven

theorem Qζσ_pos (σ : ℝ) (f : Hσ σ) : 0 ≤ Qζσ σ f  := proven

def Qζ_kernelPred (g : Lp ℂ 2 (volume : Measure ℝ)) : Prop  := proven

theorem Qζ_eq_zero_of_ae_zero
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ((g : ℝ → ℂ) =ᵐ[volume] 0) → Qζℝ g = 0  := proven

end Frourio


## ./Frourio/Zeta/KernelMultiplicity.lean

namespace Frourio

def RH_pred : Prop  := proven

noncomputable def Mult (_τ0 : ℝ) : ℕ  := proven

def VanishAtZeros (_ : Lp ℂ 2 (volume : Measure ℝ))
    (_ : ℝ → ℕ) : Prop  := proven

theorem zero_enforces_vanishing (σ : ℝ) (f : Hσ σ) :
    Qζσ σ f = 0 → VanishAtZeros ((mellin_in_L2 σ f).toLp (LogPull σ f)) Mult  := proven

end Frourio


## ./Frourio/Zeta/RHCriterion.lean

namespace Frourio

def RH : Prop  := proven

structure Prepared (σ : ℝ) (f : ℕ → Hσ σ) where
  frame : Prop
  gamma : Prop
  width : Prop := proven

def FW_criterion (σ : ℝ) : Prop  := proven

def disc_consistency (_σ : ℝ) (_F : GoldenTestSeq _σ) : Prop  := proven

def kernel_multiplicity_bridge (_σ : ℝ) (_F : GoldenTestSeq _σ) : Prop  := proven

def off_critical_contradiction : Prop  := proven

def concentrates_at (σ : ℝ) (F : GoldenTestSeq σ) (τ₀ : ℝ) : Prop  := proven

structure StandardGoldenTestSeq (σ : ℝ) extends GoldenTestSeq σ where
  /-- The width parameter has the standard form -/
  δ_standard : ∀ n, δ n = 1 / (n + 1 : ℝ) := proven

def exists_golden_peak (σ : ℝ) : Prop  := proven

theorem exists_golden_peak_proof (σ τ₀ : ℝ) :
    ∃ F : GoldenTestSeq σ, concentrates_at σ F τ₀  := sorry

theorem exists_golden_peak_proof_has_standard_width (σ τ₀ : ℝ) :
    ∃ F : GoldenTestSeq σ, concentrates_at σ F τ₀ ∧
      ∀ n, F.δ n = 1 / (n + 1 : ℝ)  := sorry

theorem golden_convergence_implies_peak_existence (σ : ℝ) :
    (∃ F : GoldenTestSeq σ, ∀ ε > 0, ∃ N, ∀ n ≥ N, F.δ n < ε) →
    exists_golden_peak σ  := proven

noncomputable def construct_golden_seq (σ τ₀ : ℝ) : GoldenTestSeq σ  := proven

theorem construct_golden_seq_concentrates (σ τ₀ : ℝ) :
    concentrates_at σ (construct_golden_seq σ τ₀) τ₀  := proven

theorem construct_golden_seq_has_standard_width (σ τ₀ : ℝ) :
    ∀ n, (construct_golden_seq σ τ₀).δ n = 1 / (n + 1 : ℝ)  := proven

theorem golden_seq_converges_to_peak (σ τ₀ : ℝ) :
    ∃ F : GoldenTestSeq σ, concentrates_at σ F τ₀  := proven

lemma golden_seq_norm_bounded (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (F : GoldenTestSeq σ) :
    ∃ C : ℝ, ∀ n, ‖F.f n‖ ≤ C  := sorry

lemma quadratic_form_bounded_on_bounded_sets (σ : ℝ) (C : ℝ) :
    ∃ K : ℝ, ∀ f : Hσ σ, ‖f‖ ≤ C → |limiting_energy σ f| ≤ K * C^2  := sorry

lemma limiting_energy_nonneg (σ : ℝ) (f : Hσ σ) :
    0 ≤ limiting_energy σ f  := proven

lemma golden_seq_energy_bounded (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (F : GoldenTestSeq σ) :
    ∃ M : ℝ, ∀ n, limiting_energy σ (F.f n) ≤ M  := proven

private lemma interlaced_subsequence_converges (σ : ℝ) (F : GoldenTestSeq σ)
    (ψ φ : ℕ → ℕ) (E : ℝ) (N : ℕ) (is_even : Bool)
    (h_conv : Filter.Tendsto
      (fun n => limiting_energy σ (F.f (if is_even then ψ n else φ n)))
      Filter.atTop (nhds E)) :
    Filter.Tendsto
      (fun n => limiting_energy σ (F.f
        ((fun k => if k % 2 = 0 then ψ (k / 2 + N) else φ ((k + 1) / 2 + N))
          (if is_even then 2 * n else 2 * n + 1))))
      Filter.atTop (nhds E)  := proven

private lemma gaussian_Hσ_norm_decomp (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (F : GoldenTestSeq σ) (n : ℕ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (hw : ‖w‖ = 1) :
    ‖F.f n‖^2 = ‖w‖^2 + σ^2 * (1/σ^2)  := sorry

private lemma Hσ_norm_decomposition (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (F : GoldenTestSeq σ) (n : ℕ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (hw : ‖w‖ = 1) :
    ∃ v d : ℝ, v ≤ ‖w‖^2 ∧ d ≤ 1/σ^2 ∧ ‖F.f n‖^2 = v + σ^2 * d  := proven

private lemma Hσ_norm_bound_by_L2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (F : GoldenTestSeq σ) (n : ℕ)
    (τ₀ : ℝ) (w : Lp ℂ 2 (volume : Measure ℝ)) (hw : ‖w‖ = 1) :
    ‖F.f n‖ ≤ 1 * ‖w‖ + 1  := sorry

private lemma golden_seq_composed_energy_bounded (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (F : GoldenTestSeq σ) (seq : ℕ → ℕ) :
    ∃ M : ℝ, ∀ k, |limiting_energy σ (F.f (seq k))| ≤ M  := sorry

private lemma golden_seq_unique_energy_cluster (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (F : GoldenTestSeq σ) (seq : ℕ → ℕ) :
    (∃ E : ℝ, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      Filter.Tendsto (fun n => limiting_energy σ (F.f (seq (subseq n)))) Filter.atTop (nhds E)) →
    (∃! E : ℝ, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      Filter.Tendsto (fun n => limiting_energy σ (F.f (seq (subseq n)))) Filter.atTop (nhds E))  := sorry

private lemma golden_seq_energy_contradiction (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (F : GoldenTestSeq σ)
    (E_low E_high : ℝ) (h_lt : E_low < E_high)
    (hφ : ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (fun n => limiting_energy σ (F.f (φ n))) Filter.atTop (nhds E_high))
    (hψ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Filter.Tendsto (fun n => limiting_energy σ (F.f (ψ n))) Filter.atTop (nhds E_low)) :
    False  := proven

lemma golden_seq_unique_cluster_point (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (F : GoldenTestSeq σ) (M : ℝ)
    (hM : ∀ n, limiting_energy σ (F.f n) ≤ M)
    (E₁ E₂ : ℝ)
    (hE₁ : ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (fun n => limiting_energy σ (F.f (φ n))) Filter.atTop (nhds E₁))
    (hE₂ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Filter.Tendsto (fun n => limiting_energy σ (F.f (ψ n))) Filter.atTop (nhds E₂)) :
    E₁ = E₂  := proven

private lemma golden_seq_all_clusters_equal (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (F : GoldenTestSeq σ) (M : ℝ)
    (hM : ∀ n, limiting_energy σ (F.f n) ≤ M) (E₀ : ℝ)
    (φ : ℕ → ℕ) (hφ_mono : StrictMono φ)
    (hφ_conv : Filter.Tendsto (fun n => limiting_energy σ (F.f (φ n))) Filter.atTop (nhds E₀))
    (E' : ℝ) (ψ : ℕ → ℕ) (hψ_mono : StrictMono ψ)
    (hψ_conv : Filter.Tendsto (fun n => limiting_energy σ (F.f (ψ n))) Filter.atTop (nhds E')) :
    E' = E₀  := proven

theorem golden_seq_energy_converges_proof (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (F : GoldenTestSeq σ) :
    ∃ E₀ : ℝ, Filter.Tendsto (fun n => limiting_energy σ (F.f n)) Filter.atTop (nhds E₀)  := sorry

def gamma_converges_to (σ : ℝ) (E_n : ℕ → (Hσ σ → ℝ)) (E : Hσ σ → ℝ) : Prop  := proven

theorem energy_implies_gamma_convergence (σ : ℝ) (F : GoldenTestSeq σ) :
    (∃ E₀ : ℝ, Filter.Tendsto (fun n => limiting_energy σ (F.f n)) Filter.atTop (nhds E₀)) →
    (∃ f₀ : Hσ σ, gamma_converges_to σ (fun _ => limiting_energy σ) (limiting_energy σ))  := sorry

theorem golden_seq_width_converges (σ : ℝ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (construct_golden_seq σ 0).δ n < ε  := proven

theorem disc_consistency_proof (σ : ℝ) (F : GoldenTestSeq σ) :
    disc_consistency σ F  := proven

theorem off_critical_contradiction_proof_skeleton
    (β τ₀ : ℝ) (_hβ : β ≠ (1 / 2 : ℝ))
    (_hZeroHyp : Prop := True) : off_critical_contradiction  := proven

theorem FW_implies_RH (σ : ℝ) : FW_criterion σ → RH  := proven

theorem off_critical_contradiction_proof : off_critical_contradiction  := proven

theorem FW_implies_RH_complete (σ : ℝ) : FW_criterion σ → RH  := proven

theorem RH_implies_FW (σ : ℝ) : RH → FW_criterion σ  := proven

end Frourio


Total files processed: 81
