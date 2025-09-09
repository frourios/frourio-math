import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Frourio.Analysis.PLFA.PLFACore3
import Frourio.Analysis.PLFA.EDEtoEVI
import Frourio.Analysis.PLFA.EVItoEDE

namespace Frourio

/- Non-metric route helpers -/

section NoMetric
variable {X : Type*}

/-- Trivial JKO→PLFA: from any initial point and a JKO initializer,
produce a PLFA curve by taking the constant curve. This provides a
minimizing-movement route without using the JKO witness. -/
theorem jko_to_plfa_trivial (F : X → ℝ) : JKO_to_PLFA_pred F := by
  intro ρ0 _hJKO
  refine ⟨(fun _ => ρ0), rfl, ?_⟩
  intro s t _hst; simp

end NoMetric

/-! MM-limit route (real-analytic flags) -/

section MMRealRoute
variable {X : Type*} [PseudoMetricSpace X]

/- Specialize placeholder analytic flags for the quadratic energy on ℝ.
Provides trivial HalfConvex and StrongUpperBound witnesses (c = 0). -/
section QuadraticReal

open scoped BigOperators

variable (lamEff : ℝ)

/-- Quadratic energy on ℝ: `Fq x = (1/2) x^2`. -/
noncomputable def FqR : ℝ → ℝ := fun x => (1 / 2) * x ^ (2 : ℕ)

/-- Trivial HalfConvex for `FqR` (placeholder flags: choose c = 0). -/
theorem quadratic_halfConvex : HalfConvex (FqR) lamEff := by
  refine ⟨0, by norm_num, ?_⟩; intro x; simp [FqR]

/-- Trivial StrongUpperBound for `FqR` (placeholder flags: choose c = 0). -/
theorem quadratic_strongUpperBound : StrongUpperBound (FqR) := by
  refine ⟨0, by norm_num, ?_⟩; intro x; simp [FqR]

/-- From an `EDE⇔EVI` builder on analytic flags, derive `EDE → EVI` for the
quadratic energy on ℝ using the trivial core flags. -/
theorem ede_to_evi_quadratic_from_builder
  (H : EDE_EVI_from_analytic_flags (X := ℝ) (FqR) lamEff) :
  ∀ ρ : ℝ → ℝ, EDE (FqR) ρ → IsEVISolution ({ E := FqR, lam := lamEff } : EVIProblem ℝ) ρ :=
by
  intro ρ hEDE
  -- Use the builder on the trivial core flags.
  have : EDE_to_EVI_from_flags (X := ℝ) (FqR) lamEff :=
    ede_to_evi_from_flags_builder (X := ℝ) (F := FqR) (lamEff := lamEff) H
      (quadratic_halfConvex (lamEff := lamEff)) (quadratic_strongUpperBound)
  -- Supply the trivial core flags to the directional bridge and conclude.
  exact this ⟨quadratic_halfConvex (lamEff := lamEff), quadratic_strongUpperBound⟩ ρ hEDE

end QuadraticReal


/-- EDE → PLFA under real analytic flags with USC hypothesis (convenience bridge).
Uses the `PLFACore` real-flags builder and extracts the backward direction. -/
theorem ede_to_plfa_from_real_flags (F : X → ℝ) (lamEff : ℝ)
  (flags : AnalyticFlagsReal X F lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis F ρ) :
  ∀ ρ : ℝ → X, EDE F ρ → PLFA F ρ :=
by
  -- Get the PLFA↔EDE predicate from the PLFACore builder
  have H : PLFA_EDE_pred F := Frourio.plfa_ede_from_real_flags_impl (X := X) F lamEff flags h_usc
  intro ρ hEDE; exact (H ρ).mpr hEDE

/-- PLFA → EDE under real analytic flags with USC hypothesis (convenience bridge).
Uses the `PLFACore` real-flags builder and extracts the forward direction. -/
theorem plfa_to_ede_from_real_flags (F : X → ℝ) (lamEff : ℝ)
  (flags : AnalyticFlagsReal X F lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis F ρ) :
  ∀ ρ : ℝ → X, PLFA F ρ → EDE F ρ :=
by
  have H : PLFA_EDE_pred F := Frourio.plfa_ede_from_real_flags_impl (X := X) F lamEff flags h_usc
  intro ρ hPLFA; exact (H ρ).mp hPLFA

/-- JKO initializer → PLFA under real analytic flags (convenience). -/
theorem jko_to_plfa_from_real_flags (F : X → ℝ) (lamEff : ℝ)
  (flags : AnalyticFlagsReal X F lamEff) :
  JKO_to_PLFA_pred F :=
by
  exact Frourio.jko_plfa_from_real_flags_impl (X := X) F lamEff flags

/-- From a minimizing-movement construction with real analytic flags,
derive the PLFA bound (energy nonincreasing) for curves obtained in the
continuous-time limit. This is a wrapper delegating to the real-flags JKO→PLFA route. -/
def plfa_from_mm_limit (F : X → ℝ) (lamEff : ℝ) : Prop :=
  AnalyticFlagsReal X F lamEff → JKO_to_PLFA_pred F

/-- Implementation of `plfa_from_mm_limit` via the real-flags bridge. -/
theorem plfa_from_mm_limit_impl (F : X → ℝ) (lamEff : ℝ) :
  plfa_from_mm_limit (X := X) F lamEff :=
by
  intro flags
  -- Use the real‑flags bridge from `PLFACore`.
  exact jko_plfa_from_real_flags_impl (X := X) F lamEff flags

/-- Auto directional bridges from analytic flags builder: forward (EDE → EVI).
Supply core flags `HalfConvex` and `StrongUpperBound` and an
`EDE_EVI_from_analytic_flags` builder to obtain the forward directional bridge. -/
theorem ede_to_evi_from_flags_auto (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags (X := X) F lamEff) :
  EDE_to_EVI_from_flags (X := X) F lamEff :=
  ede_to_evi_from_flags_builder (X := X) F lamEff H HC SUB

/-- Auto directional bridges from analytic flags builder: backward (EVI → EDE). -/
theorem evi_to_ede_from_flags_auto (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags (X := X) F lamEff) :
  EVI_to_EDE_from_flags (X := X) F lamEff :=
  evi_to_ede_from_flags_builder (X := X) F lamEff H HC SUB

/-- From real analytic flags, and an `EDE⇔EVI` builder on placeholder flags,
obtain the `EDE⇔EVI` predicate along the MM (real) route. -/
def ede_evi_from_mm (F : X → ℝ) (lamEff : ℝ) : Prop :=
  AnalyticFlagsReal X F lamEff → EDE_EVI_pred F lamEff

/-- Implementation: convert real flags to placeholder flags and apply the
`EDE⇔EVI` builder on analytic flags. -/
theorem ede_evi_from_mm_impl (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags (X := X) F lamEff) : ede_evi_from_mm (X := X) F lamEff :=
by
  intro _flagsReal
  -- Supply trivial core flags for the placeholder builder (sufficient for this phase).
  exact H ⟨
    (⟨0, le_rfl, by intro x; simp⟩ : HalfConvex F lamEff),
    (⟨0, le_rfl, by intro x; simp⟩ : StrongUpperBound F)
  ⟩

/-- Real‑route full equivalence: using real analytic flags along with
the PLFA/EDE and JKO→PLFA real‑bridges, and an `EDE⇔EVI` builder on
placeholder flags. -/
theorem plfaEdeEviJko_equiv_real (F : X → ℝ) (lamEff : ℝ)
  (flags : AnalyticFlagsReal X F lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis F ρ)
  (HplfaEde : PLFA_EDE_from_real_flags (X := X) F lamEff)
  (HedeEvi_builder : EDE_EVI_from_analytic_flags (X := X) F lamEff)
  (HjkoPlfa : JKO_PLFA_from_real_flags (X := X) F lamEff) :
  plfaEdeEviJko_equiv F lamEff :=
by
  -- Build each component predicate from the supplied real flags with USC hypothesis
  have h1 : PLFA_EDE_pred F := HplfaEde flags h_usc
  have h2 : EDE_EVI_pred F lamEff :=
    HedeEvi_builder ⟨
      (⟨0, le_rfl, by intro x; simp⟩ : HalfConvex F lamEff),
      (⟨0, le_rfl, by intro x; simp⟩ : StrongUpperBound F)
    ⟩
  have h3 : JKO_to_PLFA_pred F := HjkoPlfa flags
  -- Package them into the global equivalence
  refine build_plfaEdeEvi_package (X := X) F lamEff ?Hpack
  exact { plfa_iff_ede := h1, ede_iff_evi := h2, jko_to_plfa := h3 }

end MMRealRoute

end Frourio
