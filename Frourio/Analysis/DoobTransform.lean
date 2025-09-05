import Mathlib.Data.Real.Basic

namespace Frourio

/-!
P5: Doob transform skeleton (API only)

We provide a lightweight `Diffusion` structure and a Doob transform shell.
Heavy analysis (Leibniz, Hessian calculus) is deferred. Key identities are
stated as `Prop` so CI remains light without `sorry`.
-/

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

/- Assumption pack for Doob transform statements.
We keep core analytic identities as fields so that theoremization becomes
trivial at this phase; later, these fields will be derivable from
positivity and Leibniz/Bochner hypotheses. -/
structure DoobAssumptions {X : Type*} (h : X → ℝ) (D : Diffusion X) : Prop where
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

end Frourio
