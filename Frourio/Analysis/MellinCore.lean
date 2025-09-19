import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

open MeasureTheory Measure
open scoped ENNReal

/-!
# Mellin Transform Core Definitions

This file contains the core definitions for the Mellin transform theory
that are needed by both MellinTransform and MellinBasic to avoid circular imports.

## Main Definitions

- `mulHaar`: Haar measure on ℝ
- `Hσ`: Hilbert-Sobolev space
- `zeroLatticeSpacing`: Zero lattice spacing function
-/

/-- Multiplicative Haar measure on (0,∞) -/
noncomputable def mulHaar : Measure ℝ :=
  (volume.withDensity (fun x => ENNReal.ofReal (1 / x))).restrict (Set.Ioi 0)

/-- Hilbert-Sobolev space Hσ -/
noncomputable abbrev Hσ (σ : ℝ) :=
  Lp ℂ 2 (mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))

/-- Coercion from Hσ to functions -/
noncomputable def Hσ.toFun {σ : ℝ} (f : Hσ σ) : ℝ → ℂ := ⇑(f : Lp ℂ 2 _)

/-- Zero lattice spacing -/
noncomputable def zeroLatticeSpacing (Λ : ℝ) : ℝ := Real.pi / Real.log Λ
