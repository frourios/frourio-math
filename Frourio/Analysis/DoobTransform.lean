import Mathlib.Data.Real.Basic

namespace Frourio

/-!
P5: Doob transform skeleton (API only)

We provide a lightweight `Diffusion` structure and a Doob transform shell.
Heavy analysis (Leibniz, Hessian calculus) is deferred. Key identities are
stated as `Prop` so CI remains light.
-/

/-- Doob transform effect on curvature-dimension parameter.
The BE degradation: λ ↦ λ - 2ε(h) where h > 0 is the Doob function.
In BE theory, ε(h) measures the curvature degradation:
- ε(h) = sup_φ {∫ Γ₂(log h, φ) dμ / ‖φ‖²}
- ε(h) = 0 iff h is log-harmonic (∇²(log h) = 0)
The transformed measure is dμ_h = h²dμ. -/
structure DoobDegradation where
  /-- The degradation amount ε(h) from the Doob function h -/
  ε : ℝ
  /-- Non-negativity (always true in BE theory) -/
  ε_nonneg : 0 ≤ ε
  /-- The degraded parameter after Doob transform -/
  degraded_lambda : ℝ → ℝ := fun lam => lam - 2 * ε

structure Diffusion (X : Type*) where
  (E : (X → ℝ) → ℝ)
  (L : (X → ℝ) → (X → ℝ))
  (Gamma : (X → ℝ) → (X → ℝ))
  (Gamma2 : (X → ℝ) → (X → ℝ))

/-- Curvature-dimension predicate (pointwise Γ₂ bound).
`HasCD D λ` encodes a Bakry–Émery type lower bound in the CD(λ, ∞)
form: for all test functions `f` and points `x`, one has
`Γ₂(f)(x) ≥ λ · Γ(f)(x)`. This concrete predicate keeps the API light
while allowing downstream theorems to reference an actual inequality. -/
def HasCD {X : Type*} (D : Diffusion X) (lam : ℝ) : Prop :=
  ∀ f : X → ℝ, ∀ x : X, D.Gamma2 f x ≥ lam * D.Gamma f x

/-- Symmetric bilinear form associated to `Gamma` by polarization.
This provides a concrete `Γ(f,g)` using the unary `Γ` available in `Diffusion`.
-/
noncomputable def gammaPair {X : Type*} (D : Diffusion X)
  (f g : X → ℝ) : X → ℝ :=
  fun x =>
    ((D.Gamma (fun y => f y + g y)) x - (D.Gamma f) x - (D.Gamma g) x) / 2

/-- Minimal Leibniz rule for the generator `L` using `gammaPair` for the
cross term. This is a concrete predicate, not a placeholder. -/
def HasLeibnizL {X : Type*} (D : Diffusion X) : Prop :=
  ∀ f g : X → ℝ,
    D.L (fun x => f x * g x) =
      (fun x => f x * (D.L g) x + g x * (D.L f) x - 2 * gammaPair D f g x)

/-- Product rule for `Γ` in a minimal concrete form via `gammaPair`. -/
def HasLeibnizGamma {X : Type*} (D : Diffusion X) : Prop :=
  ∀ f g : X → ℝ,
    D.Gamma (fun x => f x * g x) =
      (fun x => (f x) ^ (2 : ℕ) * (D.Gamma g) x
        + (g x) ^ (2 : ℕ) * (D.Gamma f) x
        + 2 * f x * g x * gammaPair D f g x)

/- Pointwise Doob-transformed generator.
   L^h f := h^{-1} · L (h · f) with a zero-guard for safety. -/
noncomputable def doobL {X : Type*} (D : Diffusion X)
  (h : X → ℝ) : (X → ℝ) → (X → ℝ) :=
  fun f x =>
    let g := D.L (fun y => h y * f y)
    if h x = 0 then 0 else (1 / h x) * g x

/- Doob transform: updates the generator to `doobL` and keeps other fields.
   More precise updates for `E`, `Gamma`, `Gamma2` can be introduced later. -/
noncomputable def Doob {X : Type*} (h : X → ℝ) (D : Diffusion X) : Diffusion X :=
  { E := D.E
  , L := doobL D h
  , Gamma := D.Gamma
  , Gamma2 := D.Gamma2 }

structure DoobAssumptions {X : Type*} (h : X → ℝ) (D : Diffusion X) where
  /-- Strict positivity of `h` ensuring the Doob transform is well-defined. -/
  (h_pos : ∀ x : X, 0 < h x)
  /-- Concrete Leibniz rule for the generator. -/
  (leibniz_L : HasLeibnizL D)
  /-- Concrete product rule for `Γ`. -/
  (leibniz_Gamma : HasLeibnizGamma D)
  (gamma_eq : (Doob h D).Gamma = D.Gamma)
  (gamma2_eq : ∀ f : X → ℝ, (Doob h D).Gamma2 f = D.Gamma2 f)
  /-- Curvature-dimension shift: for any CD parameter `lam` of `D`, there exists
  a possibly degraded parameter `lam'` for `Doob h D` with `lam' ≤ lam`.
  Later phases will refine this to an explicit formula using `∇² log h`. -/
  (cd_shift : ∀ lam : ℝ, HasCD D lam → ∃ lam' : ℝ, HasCD (Doob h D) lam' ∧ lam' ≤ lam)
  /-- BE degradation for meta-variational principle: λ_eff ≥ λ - 2ε(h).
  This field provides the degradation amount ε(h) ≥ 0 from the Hessian of log h. -/
  (BE_degradation : ℝ)
  /-- Non-negativity of degradation -/
  (BE_degradation_nonneg : 0 ≤ BE_degradation)
  /-- The cd_shift explicitly uses BE_degradation: Doob h D satisfies CD(λ - 2*BE_degradation) -/
  (cd_shift_explicit : ∀ lam : ℝ, HasCD D lam → HasCD (Doob h D) (lam - 2 * BE_degradation))

/-- Minimal Bochner-style correction statement needed to realize the explicit
CD parameter shift under a Doob transform. Parameterized by `eps` from the
Hessian bound on `log h`. -/
def BochnerMinimal {X : Type*} (h : X → ℝ) (D : Diffusion X) (eps : ℝ) : Prop :=
  ∀ lam : ℝ, HasCD D lam → HasCD (Doob h D) (lam - 2 * eps)

/-- Γ identity under Doob transform (theoremized via assumptions). -/
theorem doob_gamma_eq {X : Type*} (h : X → ℝ)
  (D : Diffusion X) (H : DoobAssumptions h D) : (Doob h D).Gamma = D.Gamma :=
  H.gamma_eq

/-- Γ₂ identity under Doob transform (theoremized via assumptions).
Later phases will relax the equality to the corrected identity under minimal
Bochner assumptions. -/
theorem doob_gamma2_eq {X : Type*} (h : X → ℝ)
  (D : Diffusion X) (f : X → ℝ) (H : DoobAssumptions h D) :
  (Doob h D).Gamma2 f = D.Gamma2 f :=
  H.gamma2_eq f

/-- Γ₂ identity for all test functions (quantified version). -/
theorem doob_gamma2_eq_all {X : Type*} (h : X → ℝ)
  (D : Diffusion X) (H : DoobAssumptions h D) :
  ∀ f : X → ℝ, (Doob h D).Gamma2 f = D.Gamma2 f :=
  H.gamma2_eq

/-- Under strict positivity of `h`, the Doob generator evaluates without
the `if` guard. This provides a convenient pointwise formula. -/
theorem doobL_pointwise {X : Type*} (D : Diffusion X)
  (h : X → ℝ) (H : DoobAssumptions h D) (f : X → ℝ) (x : X) :
  doobL D h f x = (1 / h x) * D.L (fun y => h y * f y) x := by
  have hx : h x ≠ 0 := ne_of_gt (H.h_pos x)
  simp [doobL, hx]

/-- Pairwise carré-du-champ agrees under the Doob transform when `Γ` agrees. -/
theorem gammaPair_doob_eq {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (f g : X → ℝ) :
  gammaPair (Doob h D) f g = gammaPair D f g := by
  -- Replace `(Doob h D).Gamma` by `D.Gamma` using the assumption.
  have hG : (Doob h D).Gamma = D.Gamma := doob_gamma_eq h D H
  ext x; simp [gammaPair, hG]

/-- If `Γ` satisfies the product rule for `D`, then it also does for `Doob h D`
when the `Γ` fields agree (operator-level compatibility). -/
theorem hasLeibnizGamma_doob_of_base {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (HG : HasLeibnizGamma D) :
  HasLeibnizGamma (Doob h D) := by
  intro f g
  -- Use equality of `Γ` and of `gammaPair` under Doob.
  have hG : (Doob h D).Gamma = D.Gamma := doob_gamma_eq h D H
  simpa [hG, gammaPair_doob_eq h D H] using (HG f g)

/- CD-parameter update (Ricci with potential) — theoremized placeholder. -/
theorem cd_parameter_shift {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) {lam : ℝ} (hCD : HasCD D lam) :
  ∃ lam' : ℝ, HasCD (Doob h D) lam' ∧ lam' ≤ lam :=
  H.cd_shift lam hCD

/- Auxiliary API: explicit Bakry–Émery parameter under Doob, λ_BE = λ − 2ε. -/
def lambdaBE (lam eps : ℝ) : ℝ := lam - 2 * eps

/- Monotonicity: for ε ≥ 0, λ_BE ≤ λ. -/
lemma lambdaBE_le_base {lam eps : ℝ} (hε : 0 ≤ eps) : lambdaBE lam eps ≤ lam := by
  unfold lambdaBE
  have hnonneg : 0 ≤ 2 * eps := mul_nonneg (by norm_num) hε
  -- a - b ≤ a for b ≥ 0
  exact sub_le_self _ hnonneg

/- If a minimal Bochner correction holds with parameter ε, then the Doob transform
   satisfies CD(lambdaBE lam eps) whenever the base diffusion satisfies CD(lam). -/
lemma hasCD_doob_of_bochnerMinimal {X : Type*}
  (h : X → ℝ) (D : Diffusion X) {eps lam : ℝ}
  (HB : BochnerMinimal h D eps) (hCD : HasCD D lam) :
  HasCD (Doob h D) (lambdaBE lam eps) := by
  unfold lambdaBE
  simpa [two_mul] using (HB lam hCD)

/-- API: Extract the effective curvature parameter λ_BE from DoobAssumptions
when we know the Hessian bound parameter ε. -/
theorem lambdaBE_from_doobAssumptions {X : Type*}
  (h : X → ℝ) (D : Diffusion X) (_H : DoobAssumptions h D)
  (lam eps : ℝ) (hCD : HasCD D lam) (hBochner : BochnerMinimal h D eps) :
  HasCD (Doob h D) (lambdaBE lam eps) :=
  hasCD_doob_of_bochnerMinimal h D hBochner hCD

/-- API: The Doob-shifted parameter λ_BE satisfies the expected inequality
λ_BE = λ - 2ε ≤ λ when ε ≥ 0. -/
theorem lambdaBE_bound_from_doobAssumptions {X : Type*}
  (h : X → ℝ) (D : Diffusion X) (_H : DoobAssumptions h D)
  (lam eps : ℝ) (heps : 0 ≤ eps) :
  lambdaBE lam eps ≤ lam :=
  lambdaBE_le_base heps

/-- Combined API: Given DoobAssumptions and BochnerMinimal, we get both
the CD property with λ_BE and the bound λ_BE ≤ λ. -/
theorem doob_cd_with_lambdaBE {X : Type*}
  (h : X → ℝ) (D : Diffusion X) (H : DoobAssumptions h D)
  (lam eps : ℝ) (heps : 0 ≤ eps)
  (hCD : HasCD D lam) (hBochner : BochnerMinimal h D eps) :
  HasCD (Doob h D) (lambdaBE lam eps) ∧ lambdaBE lam eps ≤ lam := by
  constructor
  · exact lambdaBE_from_doobAssumptions h D H lam eps hCD hBochner
  · exact lambdaBE_bound_from_doobAssumptions h D H lam eps heps

/-- Quantitative Doob transform pack: stores an `ε ≥ 0` for which the
minimal Bochner correction holds. This yields an explicit CD parameter
shift `λ' = λ − 2ε` together with `λ' ≤ λ`. -/
structure DoobQuantitative {X : Type*} (h : X → ℝ) (D : Diffusion X) where
  (eps : ℝ) (eps_nonneg : 0 ≤ eps) (bochner : BochnerMinimal h D eps)

/-- Explicit CD-parameter shift under the quantitative Doob pack. -/
theorem cd_parameter_shift_explicit {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (HQ : DoobQuantitative h D) {lam : ℝ} (hCD : HasCD D lam) :
  ∃ lam' : ℝ, lam' = lambdaBE lam HQ.eps ∧ HasCD (Doob h D) lam' ∧ lam' ≤ lam := by
  refine ⟨lambdaBE lam HQ.eps, rfl, ?_, ?_⟩
  · exact hasCD_doob_of_bochnerMinimal h D (eps := HQ.eps) HQ.bochner hCD
  · exact lambdaBE_le_base (lam := lam) (eps := HQ.eps) HQ.eps_nonneg

/-- Pointwise form: from `DoobQuantitative`, directly obtain the transformed CD
bound at the explicit value `λ_BE = λ − 2ε` along with the monotonicity `≤`. -/
theorem cd_parameter_shift_explicit_value {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (HQ : DoobQuantitative h D) {lam : ℝ} (hCD : HasCD D lam) :
  HasCD (Doob h D) (lambdaBE lam HQ.eps) ∧ lambdaBE lam HQ.eps ≤ lam := by
  refine And.intro ?h ?hle
  · exact hasCD_doob_of_bochnerMinimal h D (eps := HQ.eps) HQ.bochner hCD
  · exact lambdaBE_le_base (lam := lam) (eps := HQ.eps) HQ.eps_nonneg

/- Packaged lower‑bound interface for an effective λ under Doob. -/
structure DoobLamBound where
  (lamBase : ℝ) (eps : ℝ) (lamEff : ℝ) (h_lamEff : lamEff = lambdaBE lamBase eps)

/- Constructor with automatic computation of lamEff -/
def DoobLamBound.mk' (lamBase eps : ℝ) : DoobLamBound :=
  { lamBase := lamBase
    eps := eps
    lamEff := lambdaBE lamBase eps
    h_lamEff := rfl }

/- Helper: compare the effective parameter to the base given ε ≥ 0. -/
lemma DoobLamBound.le_base {B : DoobLamBound} (hε : 0 ≤ B.eps) :
  B.lamEff ≤ B.lamBase := by
  -- Use the constraint that lamEff = lambdaBE lamBase eps
  rw [B.h_lamEff]
  unfold lambdaBE
  have hnonneg : 0 ≤ 2 * B.eps := mul_nonneg (by norm_num) hε
  -- a - b ≤ a for b ≥ 0
  exact sub_le_self B.lamBase hnonneg

/-- Extended API for meta-variational principle:
Connect BE_degradation field to the explicit λ_eff formula. -/
theorem doob_lambda_eff_formula {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (lam : ℝ) (hCD : HasCD D lam) :
  ∃ lam_eff : ℝ, lam_eff = lam - 2 * H.BE_degradation ∧
    HasCD (Doob h D) lam_eff ∧ lam_eff ≤ lam := by
  -- Use the BE_degradation field directly
  use lam - 2 * H.BE_degradation
  refine ⟨rfl, ?_, ?_⟩
  · -- Need to show HasCD (Doob h D) (lam - 2 * H.BE_degradation)
    -- This follows directly from cd_shift_explicit
    exact H.cd_shift_explicit lam hCD
  · -- Show lam - 2 * H.BE_degradation ≤ lam
    have h_nonneg : 0 ≤ 2 * H.BE_degradation :=
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) H.BE_degradation_nonneg
    exact sub_le_self lam h_nonneg

/-- Convenience: extract effective λ for meta-variational principle -/
def doob_lambda_eff {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (lam : ℝ) : ℝ :=
  lam - 2 * H.BE_degradation

/-- The effective λ satisfies the expected bound -/
theorem doob_lambda_eff_le {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (lam : ℝ) :
  doob_lambda_eff h D H lam ≤ lam := by
  unfold doob_lambda_eff
  have h_nonneg : 0 ≤ 2 * H.BE_degradation :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) H.BE_degradation_nonneg
  exact sub_le_self lam h_nonneg

end Frourio
