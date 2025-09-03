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
Contains placeholders for positivity of `h` and Leibniz-type rules. -/
structure DoobAssumptions {X : Type*} (h : X → ℝ) (D : Diffusion X) : Prop where
  (h_pos : True)          -- later: ∀ x, 0 < h x
  (leibniz_L : True)      -- later: L(fg) = f L g + g L f - 2 Γ(f,g)
  (leibniz_Gamma : True)  -- later: Γ(fg) = f² Γ(g) + g² Γ(f) + 2 f g Γ(f,g)

/-- Γ identity under Doob transform (statement-only). -/
def doob_gamma_eq {X : Type*} (h : X → ℝ)
  (D : Diffusion X) : Prop :=
  DoobAssumptions h D → (Doob h D).Gamma = D.Gamma

/-- Γ₂ corrected identity under Doob transform (statement-only).
In later phases this will expand to the usual Bochner-type correction. -/
def doob_gamma2_eq {X : Type*} (h : X → ℝ)
  (D : Diffusion X) (f : X → ℝ) : Prop :=
  DoobAssumptions h D → (Doob h D).Gamma2 f = D.Gamma2 f

/-- Γ₂ identity for all test functions (quantified version). -/
def doob_gamma2_eq_all {X : Type*} (h : X → ℝ)
  (D : Diffusion X) : Prop :=
  DoobAssumptions h D → ∀ f : X → ℝ, (Doob h D).Gamma2 f = D.Gamma2 f

/- CD-parameter update (Ricci with potential) as a statement placeholder. -/
def cd_parameter_shift {X : Type*} (h : X → ℝ) (D : Diffusion X) : Prop :=
  DoobAssumptions h D → True

end Frourio
