import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace Frourio

/-!
P5: Dirac index (skeleton with light API)

We model a minimal Fredholm operator with an integer index, a Dirac
system carrying such an operator, and provide a zero-order invariance
lemma (by definition) together with a placeholder statement for the
torus index formula.
-/

/-- Minimal Fredholm operator model carrying only its index. -/
structure Fredholm where
  (index : ℤ)

/-- Zero-order bounded perturbations (placeholder over a bundle). -/
structure ZeroOrderBoundedOp (bundle : Type*) : Type where
  (dummy : Unit := ())

/-- Lightweight class tag for the 2-torus geometry on a space `M`.
This will replace the Prop field inside `DiracSystem` in later phases. -/
class IsTorus2 (M : Type*) : Prop where
  trivial_ok : True := True.intro

/-- Dirac system skeleton: base space, torus tag, bundle, connection,
and the principal Dirac operator as a Fredholm element. Also stores a
placeholder RHS value for the torus index formula (e.g. Chern number).

Note: `isTorus2 : Prop` is kept for backward compatibility, but we add
the `IsTorus2` class above and a class-based statement below
(`index_formula_T2_class`) as the forward-looking API.
-/
structure DiracSystem where
  (M : Type*)
  (isTorus2 : Prop)
  (bundle : Type*)
  (connection : Type*)
  (D_A : Fredholm)
  (indexRHS_T2 : ℤ)

/-- Extract the integer index. -/
@[simp] def index (T : Fredholm) : ℤ := T.index

/-- Add a zero-order bounded perturbation (skeleton keeps the same
Fredholm operator to model invariance at the API level). -/
noncomputable def addZeroOrder (S : DiracSystem)
    (_V : ZeroOrderBoundedOp S.bundle) : Fredholm :=
  S.D_A

/-- Index invariance under zero-order bounded perturbations (definitional). -/
@[simp] theorem index_invariance_zero_order (S : DiracSystem)
    (V : ZeroOrderBoundedOp S.bundle) :
    index (addZeroOrder S V) = index S.D_A := rfl

/-- Torus index formula placeholder: states equality of the analytical
index with a stored RHS (e.g. Chern number) under a torus hypothesis. -/
def index_formula_T2 (S : DiracSystem) (_hT2 : S.isTorus2) : Prop :=
  index S.D_A = S.indexRHS_T2

/-- Class-based variant of the torus index formula (forward-looking API). -/
def index_formula_T2_class (S : DiracSystem) [IsTorus2 S.M] : Prop :=
  index S.D_A = S.indexRHS_T2

/-- Prop-level witness that a type admits a `IsTorus2` instance. -/
def hasTorus2Class (S : DiracSystem) : Prop := Nonempty (IsTorus2 S.M)

/-- Tag-based index formula using either the legacy `Prop` tag or the
presence of a `IsTorus2` class instance (wrapped as a `Prop`). -/
def index_formula_T2_tag (S : DiracSystem) : Prop :=
  (S.isTorus2 ∨ hasTorus2Class S) → index S.D_A = S.indexRHS_T2

/-- Assumption pack for extensible hypotheses beyond `IsTorus2`.
All fields are placeholders for now to keep CI light. -/
structure DiracAssumptions (S : DiracSystem) : Prop where
  (torus2Tag : S.isTorus2 ∨ hasTorus2Class S)
  (bundleTop : True)         -- later: topological/metric assumptions on `S.bundle`
  (connSmooth : True)        -- later: smoothness/compatibility of `S.connection`
  (zeroOrderCompat : True)   -- later: admissibility of zero-order terms

/-- Index formula under an assumption pack (extensible tag-based form). -/
def index_formula (S : DiracSystem) (_H : DiracAssumptions S) : Prop :=
  index S.D_A = S.indexRHS_T2

/-- Class-based assumption pack (when `[IsTorus2 S.M]` is available). -/
structure DiracAssumptionsClass (S : DiracSystem) [IsTorus2 S.M] : Prop where
  (bundleTop : True)
  (connSmooth : True)
  (zeroOrderCompat : True)

/-- Index formula using the class-based assumption pack. -/
def index_formula_class (S : DiracSystem) [IsTorus2 S.M]
  (_H : DiracAssumptionsClass S) : Prop :=
  index S.D_A = S.indexRHS_T2

end Frourio
