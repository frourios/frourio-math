import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Data.Matrix.Basic
import Frourio.Analysis.QuadraticForm

namespace Frourio

open scoped BigOperators
open MeasureTheory

/-!
B-3: Finite trigonometric polynomials and positivity.

We model a finite trigonometric polynomial via complex exponentials with
integer frequencies k ∈ [-N, N], scaled by log a. The evaluation is
complex-valued; when used as a kernel for the quadratic form, we take
the real part.
-/

structure TrigPoly (a : ℝ) where
  N : ℕ
  c : ℤ → ℂ

namespace TrigPoly

variable {a : ℝ}

noncomputable def eval (F : TrigPoly a) (τ : ℝ) : ℂ :=
  Finset.sum (Finset.Icc (-(F.N : ℤ)) (F.N : ℤ))
    (fun k => F.c k * Complex.exp (Complex.I * ((k : ℂ) * (Real.log a : ℂ) * (τ : ℂ))))

/-- Real-valued kernel obtained as the real part of the complex trigonometric polynomial. -/
noncomputable def kernelR (F : TrigPoly a) : ℝ → ℝ := fun τ => (eval F τ).re

/-- Positivity wrapper: if the real part is a.e. nonnegative, then the quadratic
form built from it is nonnegative. -/
theorem Q_pos_of_ae_nonneg (F : TrigPoly a)
    (h : ∀ᵐ τ ∂MeasureTheory.volume, 0 ≤ kernelR F τ)
    (g : Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    0 ≤ Qℝ (kernelR F) g := by
  -- Directly apply the generic positivity theorem for Qℝ.
  simpa [kernelR] using Q_pos (K := kernelR F) h g

end TrigPoly

/-!
B-4: Finite lattice residue identity (design-level statement).

We introduce the exponential modes and state a finite-dimensional identity
as a `Prop` to be proven in later phases when we put the problem on an
appropriate compact domain or introduce weight/cutoffs that make the modes
belong to L².
-/

namespace LatticeResidue

open TrigPoly

variable {a : ℝ}

/-- Exponential mode `e_k(τ) = exp(i k (log a) τ)` as a design placeholder in L².
In later phases this will be replaced by a genuine `Lp` element on a periodic
domain or with suitable weights. -/
noncomputable def eK (_a : ℝ) (_k : ℤ) : Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  0

/-- Symmetric integer index set `{-N, …, N}`. -/
def symmIdx (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- Finite lattice residue identity (signature). For a trigonometric polynomial
`F` with coefficients `c_k` on the symmetric index set, the quadratic form with
kernel `Re (eval F)` equals a finite sum of modal energies weighted by `Re c_k`.
The right-hand side uses placeholder `eK a k` modes in `L²`.

This is a design-level `Prop` to be established in later phases. -/
def lattice_residue_finite (F : TrigPoly a) : Prop :=
  ∀ g : Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ),
    Qℝ (kernelR F) g
      = Finset.sum (symmIdx F.N)
          (fun k => (F.c k).re * ‖(@inner ℂ _ _ (eK a k) g)‖^2)

/-- Phase 4.2: hypotheses wrapper providing the finite lattice residue identity.
Concrete analytic proofs (orthogonality/Parseval on a periodic domain) will
populate this wrapper in a later phase. -/
structure LatticeResidueHypotheses (F : TrigPoly a) : Prop where
  holds : lattice_residue_finite F

/-- Phase 4.2: from the hypotheses wrapper, conclude the identity. -/
theorem lattice_residue_finite_proof (F : TrigPoly a)
    (h : LatticeResidueHypotheses (a := a) F) : lattice_residue_finite F :=
  h.holds

end LatticeResidue

/-!
Toeplitz form for finite trigonometric polynomials (finite-dimensional model).

We construct the Toeplitz matrix associated to coefficients `c_k` of a
trigonometric polynomial on the symmetric index set `{-N,…,N}`. The entry
at `(i,j)` is `c_{k_j - k_i}` where `k_t = t - N` encodes `Fin (2N+1)` into `ℤ`.
We also provide a positivity predicate stating the associated quadratic form
has nonnegative real part on all vectors.
-/

namespace Toeplitz

open TrigPoly

variable {a : ℝ}

/-- Encode `i : Fin (2N+1)` as an integer in `{-N,…,N}`. -/
def idxToZ (N : ℕ) (i : Fin (2 * N + 1)) : ℤ := (i.1 : ℤ) - N

/-- Toeplitz matrix from a trigonometric polynomial's coefficients on `{-N,…,N}`. -/
noncomputable def matrix (F : TrigPoly a) :
    Matrix (Fin (2 * F.N + 1)) (Fin (2 * F.N + 1)) ℂ :=
  fun i j => F.c (idxToZ F.N j - idxToZ F.N i)

/-- Quadratic form associated to the Toeplitz matrix (real part). -/
noncomputable def qform (F : TrigPoly a)
    (v : (Fin (2 * F.N + 1)) → ℂ) : ℝ :=
  let A := matrix (a := a) F
  (∑ i, ∑ j, v i * star (v j) * A i j).re

/-- Positivity predicate: the Toeplitz quadratic form has nonnegative real part. -/
def isPSD (F : TrigPoly a) : Prop :=
  ∀ v : (Fin (2 * F.N + 1)) → ℂ, 0 ≤ qform (a := a) F v

end Toeplitz

/-!
Finite model equivalence: nonnegativity ↔ Toeplitz PSD.

In this finite-dimensional scaffold, we take the definition of “F is
nonnegative” to be exactly the PSD property of its Toeplitz form. The
following theorem is therefore definitionally true and serves as the
bridge named in the plan; a stronger analytic statement relating the
pointwise kernel `kernelR F ≥ 0` to PSD will be introduced later.
-/

namespace TrigPoly

variable {a : ℝ}

/-- Finite-model nonnegativity predicate (alias to Toeplitz PSD). -/
def nonneg (F : TrigPoly a) : Prop := Toeplitz.isPSD (a := a) F

/-- In the finite model, “F is nonnegative” iff its Toeplitz form is PSD. -/
theorem F_nonneg_iff_toeplitz_psd (F : TrigPoly a) :
    nonneg (a := a) F ↔ Toeplitz.isPSD (a := a) F := Iff.rfl

end TrigPoly

end Frourio
