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

/-- Curvature-dimension parameter predicate (placeholder).
`HasCD D λ` is intended to encode that the diffusion `D` satisfies a
CD-type lower bound with parameter `λ`. This is kept abstract at this
phase and will be refined later. -/
def HasCD {X : Type*} (_D : Diffusion X) (_lam : ℝ) : Prop := True

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
  (h_pos : True)            -- later: ∀ x, 0 < h x
  (leibniz_L : True)        -- later: L(fg) = f L g + g L f - 2 Γ(f,g)
  (leibniz_Gamma : True)    -- later: Γ(fg) = f² Γ(g) + g² Γ(f) + 2 f g Γ(f,g)
  (gamma_eq : (Doob h D).Gamma = D.Gamma)
  (gamma2_eq : ∀ f : X → ℝ, (Doob h D).Gamma2 f = D.Gamma2 f)
  /-- Curvature-dimension shift: for any CD parameter `lam` of `D`, there exists
  a possibly degraded parameter `lam'` for `Doob h D` with `lam' ≤ lam`.
  Later phases will refine this to an explicit formula using `∇² log h`. -/
  (cd_shift : ∀ lam : ℝ, HasCD D lam → ∃ lam' : ℝ, HasCD (Doob h D) lam' ∧ lam' ≤ lam)

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

/- CD-parameter update (Ricci with potential) — theoremized placeholder. -/
theorem cd_parameter_shift {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) {lam : ℝ} (hCD : HasCD D lam) :
  ∃ lam' : ℝ, HasCD (Doob h D) lam' ∧ lam' ≤ lam :=
  H.cd_shift lam hCD

end Frourio
