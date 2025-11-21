import Frourio.Analysis.MellinTransform
import Frourio.Analysis.HilbertSpaceCore
import Frourio.Analysis.MellinParseval.MellinParsevalCore2
import Frourio.Analysis.ZakMellin
import Frourio.Algebra.StructureSequence
import Frourio.Algebra.Operators
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Frourio Operator Mellin Symbol

This file implements the Mellin symbol analysis for the Frourio operator D_Φ.
The main result establishes the explicit form of the Mellin transform of the
Frourio operator action.

## Main Definitions
- `FrourioOperator`: The main Frourio differential operator D_Φ
- `ScaleOperator`: Scale transformation T_α
- `InverseMultOperator`: Inverse multiplication operator M_{1/x}

## Main Theorems
- `frourio_mellin_symbol`: Mellin transform of D_Φ f
- `scale_transform_mellin`: Mellin transform of scale transformation
- `inverse_mult_mellin`: Mellin transform of inverse multiplication

## Implementation Notes
The Frourio operator D_Φ is defined as the linear combination:
D_Φ f = T_φ f - T_{1/φ} f ∘ M_{1/x}

where:
- T_α f(x) = f(αx) (scale transformation)
- M_{1/x} f(x) = f(x)/x (inverse multiplication)
- φ is the golden ratio or a metallic ratio parameter
-/

noncomputable section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators Interval

namespace Frourio

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Scale operator with parameter α -/
noncomputable def mkScaleOperator (α : ℝ) (hα : 0 < α) : ScaleOperator :=
  { scale := α, scale_pos := hα }

/-- Standard inverse multiplication operator -/
def mkInverseMultOperator : InverseMultOperator := InverseMultOperator.standard

/-- The main Frourio operator D_Φ using structures -/
noncomputable def mkFrourioOperator (φ : ℝ) (hφ : 0 < φ) (f : ℝ → ℂ) : ℝ → ℂ :=
  let U_φ := mkScaleOperator φ hφ
  let U_inv := mkScaleOperator (1/φ) (by rw [one_div]; exact inv_pos.mpr hφ)
  let M := mkInverseMultOperator
  fun x => U_φ.act f x - U_inv.act (M.act f) x

-- Notation for operators
notation "D_Φ[" φ "]" => mkFrourioOperator φ
notation "T_[" α "]" => mkScaleOperator α
notation "M_{1/x}" => mkInverseMultOperator

/-- Mellin transform of scale transformation -/
theorem scale_transform_mellin
    (α : ℝ) (hα : 0 < α) (f : ℝ → ℂ) (s : ℂ)
    (hf : Integrable (fun t : ℝ => f t * t ^ (s - 1)) (volume.restrict (Ioi (0 : ℝ)))) :
    mellinTransform ((mkScaleOperator α hα).act f) s = α^(-s) * mellinTransform f s := by
  -- We keep the integrability hypothesis `hf` in the signature, even though
  -- the current proof works at the level of the defining integrals.
  have _ := hf
  -- Express both Mellin transforms via the logarithmic change of variables.
  have h_scaled :
      mellinTransform ((mkScaleOperator α hα).act f) s =
        ∫ t : ℝ, ((mkScaleOperator α hα).act f) (Real.exp t) *
          Complex.exp (s * t) := by
    simpa using mellin_to_fourier_change_of_variables
      ((mkScaleOperator α hα).act f) s
  have h_plain :
      mellinTransform f s =
        ∫ t : ℝ, f (Real.exp t) * Complex.exp (s * t) := by
    simpa using mellin_to_fourier_change_of_variables f s

  -- Identify the integrand of the scaled transform explicitly.
  have h_scaled_explicit :
      ∀ t : ℝ,
        ((mkScaleOperator α hα).act f) (Real.exp t) * Complex.exp (s * t)
          = f (α * Real.exp t) * Complex.exp (s * t) := by
    intro t
    simp [mkScaleOperator, ScaleOperator.act, mul_comm, mul_left_comm, mul_assoc]

  -- Define the Fourier-side integrand for the original Mellin transform.
  set h : ℝ → ℂ := fun u => f (Real.exp u) * Complex.exp (s * u) with h_def

  -- Relate the scaled integrand to a translated version of `h`, up to a constant.
  have h_scaled_as_shift :
      ∀ t : ℝ,
        f (α * Real.exp t) * Complex.exp (s * t) =
          Complex.exp (-s * (Real.log α)) *
            h (t + Real.log α) := by
    intro t
    -- First rewrite α · exp t as exp (t + log α).
    have hα_pos : 0 < α := hα
    have h_exp :
        α * Real.exp t = Real.exp (t + Real.log α) := by
      -- rewrite using `Real.exp_add`
      have h_add := Real.exp_add t (Real.log α)
      have h_aux : Real.exp (Real.log α) = α := Real.exp_log hα_pos
      -- `exp (t + log α) = exp t * exp (log α) = exp t * α`
      have h_add' :
          Real.exp (t + Real.log α) = Real.exp t * α := by
        simpa [h_aux] using h_add
      have h_add'' :
          Real.exp (t + Real.log α) = α * Real.exp t := by
        simpa [mul_comm] using h_add'
      simpa using h_add''.symm
    -- Rewrite the RHS using `h` and exponential identities.
    have h_rhs :
        Complex.exp (-s * (Real.log α)) *
          h (t + Real.log α)
          = f (Real.exp (t + Real.log α)) * Complex.exp (s * t) := by
      -- Unfold `h` and rearrange factors.
      have h1 :
          Complex.exp (-s * (Real.log α)) *
              h (t + Real.log α)
            =
          Complex.exp (-s * (Real.log α)) *
              (f (Real.exp (t + Real.log α)) *
                Complex.exp (s * (t + Real.log α))) := by
        simp [h_def]
      have h2 :
          Complex.exp (-s * (Real.log α)) *
              (f (Real.exp (t + Real.log α)) *
                Complex.exp (s * (t + Real.log α)))
            =
          f (Real.exp (t + Real.log α)) *
              (Complex.exp (-s * (Real.log α)) *
                Complex.exp (s * (t + Real.log α))) := by
        -- re-associate and commute the scalar factors
        ring_nf
      -- simplify the exponential product
      have h3 :
          Complex.exp (-s * (Real.log α)) *
              Complex.exp (s * (t + Real.log α))
            = Complex.exp (s * t) := by
        -- use `exp_add` and simplify the exponent
        have h_add_exp :=
          Complex.exp_add (-s * (Real.log α)) (s * (t + Real.log α))
        -- `h_add_exp` gives `exp (a + b) = exp a * exp b`
        have h_mul :
            Complex.exp (-s * (Real.log α)) *
                Complex.exp (s * (t + Real.log α))
              = Complex.exp
                  ((-s * (Real.log α : ℂ)) +
                    s * ((t : ℂ) + (Real.log α : ℂ))) := by
          -- rewrite to move to the sum in the exponent
          simpa using h_add_exp.symm
        -- simplify the exponent `-s log α + s (t + log α) = s t`
        have h_inner :
            (-s * (Real.log α : ℂ)) +
                s * ((t : ℂ) + (Real.log α : ℂ))
              = s * (t : ℂ) := by
          calc
            (-s * (Real.log α : ℂ)) +
                  s * ((t : ℂ) + (Real.log α : ℂ))
              = (-s * (Real.log α : ℂ)) +
                  (s * (t : ℂ) + s * (Real.log α : ℂ)) := by
                    simp [mul_add, add_comm, add_left_comm, add_assoc]
            _ = ((-s * (Real.log α : ℂ)) + s * (Real.log α : ℂ)) +
                    s * (t : ℂ) := by
                      ac_rfl
            _ = (0 : ℂ) + s * (t : ℂ) := by
                      simp [sub_eq_add_neg, add_comm, add_left_comm,
                        add_assoc, mul_comm, mul_left_comm, mul_assoc]
            _ = s * (t : ℂ) := by simp
        have h_exp_simpl :
            Complex.exp
                ((-s * (Real.log α : ℂ)) +
                  s * ((t : ℂ) + (Real.log α : ℂ)))
              = Complex.exp (s * (t : ℂ)) := by
          rw [h_inner]
        -- combine the two identities to obtain the desired product identity
        exact h_mul.trans h_exp_simpl
      -- put the pieces together
      calc
        Complex.exp (-s * (Real.log α)) *
              h (t + Real.log α)
            = Complex.exp (-s * (Real.log α)) *
                (f (Real.exp (t + Real.log α)) *
                  Complex.exp (s * (t + Real.log α))) := h1
        _ = f (Real.exp (t + Real.log α)) *
                (Complex.exp (-s * (Real.log α)) *
                  Complex.exp (s * (t + Real.log α))) := h2
        _ = f (Real.exp (t + Real.log α)) * Complex.exp (s * t) := by
          rw [h3]
    -- Combine the algebraic identities.
    simpa [h_exp] using h_rhs.symm

  -- Now compute the integral on the scaled side using the shift representation.
  have h_integral_scaled :
      ∫ t : ℝ, ((mkScaleOperator α hα).act f) (Real.exp t) *
          Complex.exp (s * t)
        = Complex.exp (-s * (Real.log α)) *
          ∫ t : ℝ, h t := by
    -- Replace the integrand with the explicit scaled form.
    have :
        ∫ t : ℝ, ((mkScaleOperator α hα).act f) (Real.exp t) *
            Complex.exp (s * t)
          = ∫ t : ℝ, f (α * Real.exp t) * Complex.exp (s * t) := by
      congr 1
    have h_point :
        (fun t : ℝ =>
          f (α * Real.exp t) * Complex.exp (s * t))
          =
        fun t : ℝ =>
          Complex.exp (-s * (Real.log α)) * h (t + Real.log α) := by
      funext t
      exact h_scaled_as_shift t
    -- Substitute and pull the constant factor out of the integral.
    calc
      ∫ t : ℝ, ((mkScaleOperator α hα).act f) (Real.exp t) *
            Complex.exp (s * t)
          = ∫ t : ℝ,
              Complex.exp (-s * (Real.log α)) * h (t + Real.log α) := by
                simpa [h_point] using this
      _ = Complex.exp (-s * (Real.log α)) *
            ∫ t : ℝ, h (t + Real.log α) := by
            -- treat the scalar factor via `integral_smul`
            simpa [smul_eq_mul] using
              (MeasureTheory.integral_smul (μ := volume)
                (c := Complex.exp (-s * (Real.log α)))
                (f := fun t : ℝ => h (t + Real.log α)))
      _ = Complex.exp (-s * (Real.log α)) *
            ∫ t : ℝ, h t := by
            -- translation invariance of the Lebesgue integral on ℝ
            have h_trans :=
              integral_comp_sub (f := h) (τ := -Real.log α)
            -- `t - (-log α) = t + log α`
            simpa [sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc] using h_trans

  -- Relate `Complex.exp (-s log α)` to `α ^ (-s)` using the Mellin kernel lemma.
  have h_cpow :
      (α : ℂ) ^ (-s) = Complex.exp (-s * (Real.log α)) := by
    have hα_pos : 0 < α := hα
    -- specialize `mellin_kernel_transform` with `s ↦ 1 - s`, `t ↦ log α`
    have h_mellin :=
      mellin_kernel_transform (s := 1 - s) (t := Real.log α)
    -- On the LHS we have `(exp (log α)) ^ ((1 - s) - 1) = α ^ (-s)`.
    have h_exp_log :
        (Real.exp (Real.log α) : ℂ) = (α : ℂ) := by
      have : Real.exp (Real.log α) = α := Real.exp_log hα_pos
      exact congrArg (fun x : ℝ => (x : ℂ)) this
    have h_exponent : (1 - s : ℂ) - 1 = -s := by
      ring
    -- Rewrite and simplify.
    simpa [h_exp_log, h_exponent] using h_mellin

  -- Put everything together.
  calc
    mellinTransform ((mkScaleOperator α hα).act f) s
        = Complex.exp (-s * (Real.log α)) *
            ∫ t : ℝ, h t := by
          simp [h_scaled, h_integral_scaled]
    _ = (α : ℂ) ^ (-s) * ∫ t : ℝ, h t := by
          simp [h_cpow]
    _ = α^(-s) * mellinTransform f s := by
          simp [h_plain, h_def]

/-- Helper lemma for Mellin inverse multiplication:
for `t > 0`, dividing `t^(s-1)` by `t` lowers the exponent by one. -/
lemma cpow_div (t : ℝ) (s : ℂ) (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) / (t : ℂ) = (t : ℂ) ^ (s - 2) := by
  have ht_ne : (t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht : t ≠ 0)
  simp only [Complex.cpow_sub _ _ ht_ne, Complex.cpow_one, div_eq_iff ht_ne]
  have h2_ne : (t : ℂ) ^ (2 : ℕ) ≠ 0 := by
    simp [pow_ne_zero, ht_ne]
  field_simp [h2_ne]
  ring

/-- Mellin transform of inverse multiplication:
`M[(f(x)/x)](s) = M[f](s-1)`. -/
theorem inverse_mult_mellin (f : ℝ → ℂ) (s : ℂ) :
    mellinTransform (M_{1/x}.act f) s = mellinTransform f (s - 1) := by
  -- M_{1/x} f(x) = f(x)/x, so Mellin transform becomes:
  -- ∫ (f(t)/t) t^(s-1) dt = ∫ f(t) t^(s-2) dt = ∫ f(t) t^((s+1)-1) dt
  unfold mellinTransform mkInverseMultOperator InverseMultOperator.act InverseMultOperator.standard
  -- We work directly with the definition of mellinTransform
  have h_shift :
      ∫ t in Ioi (0:ℝ), (if t ≠ 0 then f t / t else (0:ℂ)) * t ^ (s - 1) ∂volume =
        ∫ t in Ioi (0:ℝ), f t * t ^ (s - 1 - 1) ∂volume := by
    -- Since we're integrating over (0,∞), t ≠ 0, so the if-then-else simplifies
    have h_nonzero : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), t ≠ 0 := by
      -- On `Ioi 0`, all points are nonzero: t ∈ Ioi 0 → t ≠ 0.
      -- Use `ae_restrict_iff'` to transfer this to the restricted measure.
      refine (ae_restrict_iff' (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro t ht
      exact ne_of_gt ht
    have h_simplify : ∀ t ∈ Ioi (0:ℝ), (if t ≠ 0 then f t / t else (0:ℂ)) = f t / t := by
      intro t ht
      simp [if_pos (ne_of_gt (mem_Ioi.mp ht))]
    -- Combine the division and multiplication by t^(s-1)
    have h_combine :
        ∀ t ∈ Ioi (0:ℝ),
          (f t / t) * t ^ (s - 1) = f t * t ^ (s - 1) / t := by
      intro t ht
      calc
        (f t / t) * t ^ (s - 1)
            = (f t * (t : ℂ)⁻¹) * t ^ (s - 1) := by
                simp [div_eq_mul_inv]
        _ = f t * t ^ (s - 1) * (t : ℂ)⁻¹ := by
                ac_rfl
        _ = f t * t ^ (s - 1) / t := by
                simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    -- Show the two integrands coincide a.e. on (0,∞).
    have h_ae :
        (fun t : ℝ =>
          (if t ≠ 0 then f t / t else (0:ℂ)) * t ^ (s - 1))
          =ᵐ[volume.restrict (Ioi (0:ℝ))]
        fun t : ℝ => f t * t ^ (s - 2) := by
      -- Reduce to a pointwise statement on `Ioi 0`.
      refine (ae_restrict_iff' (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro t ht
      have ht_pos : 0 < t := ht
      have ht_ne : t ≠ 0 := ne_of_gt ht_pos
      -- Use the algebraic rewriting lemma `h_combine` and the cpow exponent rule.
      have h1 : (if t ≠ 0 then f t / t else (0:ℂ)) * t ^ (s - 1)
          = f t * t ^ (s - 1) / t := by
        have := h_combine t ht
        simp [ht_ne, this]
      have h2 : f t * t ^ (s - 1) / t = f t * t ^ (s - 2) := by
        -- Apply `cpow_div` and factor out `f t`.
        have h_div :=
          cpow_div t s ht_pos
        -- Rewrite the denominator and apply the exponent identity.
        calc
          f t * t ^ (s - 1) / t
              = f t * ((t : ℂ) ^ (s - 1) / (t : ℂ)) := by
                rw [mul_div_assoc]
          _ = f t * (t : ℂ) ^ (s - 2) := by
                -- multiply `cpow_div` by `f t` on the left
                have := congrArg (fun z : ℂ => f t * z) h_div
                exact this
          _ = f t * t ^ (s - 2) := rfl
      -- Combine the two local identities.
      simp only
      rw [h1, h2]
    -- Conclude equality of integrals over the restricted measure.
    have := integral_congr_ae h_ae
    -- Rewrite both sides back to integrals over `Ioi 0` with respect to `volume`.
    convert this using 2
    · ring_nf
  have h_exp_simp : s - 1 - 1 = s - 2 := by ring
  rw [h_shift]

/-- Main theorem: Mellin transform of the Frourio operator.

On its natural domain of integrability, we have
`M[D_Φ f](s) = φ^(-s) M[f](s) - (1/φ)^(-s) M[f](s-1)`. -/
theorem frourio_mellin_symbol
    (φ : ℝ) (hφ : 1 < φ) (f : ℝ → ℂ) (s : ℂ)
    (hf : Integrable (fun t : ℝ => f t * t ^ (s - 1)) (volume.restrict (Ioi (0 : ℝ))))
    (hf_inv : Integrable
      (fun t : ℝ => (M_{1/x}.act f) t * t ^ (s - 1))
      (volume.restrict (Ioi (0 : ℝ))))
    (hf_scale :
      IntegrableOn
        (fun t : ℝ =>
          (mkScaleOperator φ (by linarith : 0 < φ)).act f t * t ^ (s - 1))
        (Set.Ioi (0 : ℝ)) volume)
    (hf_scale_inv :
      IntegrableOn
        (fun t : ℝ =>
          (mkScaleOperator (1/φ)
            (by
              rw [one_div]
              exact inv_pos.mpr (by linarith : 0 < φ))).act (M_{1/x}.act f) t * t ^ (s - 1))
        (Set.Ioi (0 : ℝ)) volume) :
    mellinTransform (D_Φ[φ] (by linarith : 0 < φ) f) s =
    φ^(-s) * mellinTransform f s -
      (1/φ)^(-s) * mellinTransform f (s - 1) := by
  -- D_Φ f = T_φ f - T_{1/φ} (M_{1/x} f)
  -- Mellin transform of D_Φ f = Mellin[T_φ f] - Mellin[T_{1/φ} (M_{1/x} f)]
  unfold mkFrourioOperator
  have h_sub : mellinTransform (fun x => (mkScaleOperator φ (by linarith : 0 < φ)).act f x -
      (mkScaleOperator (1/φ)
        (by rw [one_div]; exact inv_pos.mpr (by linarith : 0 < φ))).act (M_{1/x}.act f) x) s =
      mellinTransform ((mkScaleOperator φ (by linarith : 0 < φ)).act f) s -
      mellinTransform ((mkScaleOperator (1/φ)
        (by rw [one_div]; exact inv_pos.mpr (by linarith : 0 < φ))).act (M_{1/x}.act f)) s := by
    -- Apply linearity of the Mellin transform (subtraction) with the two scaled pieces.
    -- Set up the two component functions.
    have := mellinTransform_sub
      (f := fun x : ℝ =>
        (mkScaleOperator φ (by linarith : 0 < φ)).act f x)
      (g := fun x : ℝ =>
        (mkScaleOperator (1/φ)
          (by
            rw [one_div]
            exact inv_pos.mpr (by linarith : 0 < φ))).act (M_{1/x}.act f) x)
      (s := s)
      (hf := hf_scale)
      (hg := hf_scale_inv)
    -- Rewrite `(f - g)` in the Mellin argument.
    simpa [Pi.sub_apply] using this
  rw [h_sub]
  -- Handle each term separately
  rw [scale_transform_mellin φ (by linarith : 0 < φ) f s hf]

  -- For the second term: T_{1/φ} (M_{1/x} f)
  have h_inv_phi_pos : 0 < 1/φ := by
    rw [one_div]
    exact inv_pos.mpr (by linarith : 0 < φ)
  rw [scale_transform_mellin (1/φ) h_inv_phi_pos (M_{1/x}.act f) s hf_inv]
  -- Apply the inverse multiplication Mellin identity to the remaining Mellin term.
  rw [inverse_mult_mellin f s]

  -- At this point we have
  -- `φ^(-s) * M[f](s) - (1/φ)^(-s) * M[f](s-1)`, as desired.
  -- Reassociate the last product to match the stated form.
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- The Frourio symbol function -/
def frourioSymbol (φ : ℝ) (s : ℂ) : ℂ := φ^(-s) - φ^(s-1)

/-- Alternative form of the Frourio symbol (for `φ ≠ 0`) -/
theorem frourio_symbol_alt (φ : ℝ) (hφ : 0 < φ) (s : ℂ) :
    frourioSymbol φ s = φ^(-s) - φ^s / φ := by
  unfold frourioSymbol
  congr 2
  -- We need to show φ^(s-1) = φ^s / φ
  -- Work in ℂ with base `z := (φ : ℂ)`.
  have hφ_ne : (φ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hφ : φ ≠ 0)
  -- Use the division rule for complex powers.
  -- We know φ^(s-1) / φ = φ^(s-2) from cpow_div, but we need φ^s / φ = φ^(s-1).
  -- Use the subtraction law: φ^(s-1) = φ^(s) * φ^(-1) = φ^s / φ.
  simp only [Complex.cpow_sub _ _ hφ_ne, Complex.cpow_one, div_eq_iff hφ_ne]

/-- The Frourio symbol has zeros on the shifted imaginary lattice
`s = 1/2 - (i π k) / log φ` for integers `k`, when `1 < φ`. -/
theorem frourio_symbol_zeros (φ : ℝ) (hφ : 1 < φ) (s : ℂ) :
    frourioSymbol φ s = 0 ↔
      ∃ k : ℤ,
        s = (1 / 2 : ℂ) -
          (Complex.I * (Real.pi : ℂ) * (k : ℂ)) / (Real.log φ : ℂ) := by
  classical
  -- Abbreviation for `log φ` in ℂ
  set a : ℂ := (Real.log φ : ℂ) with ha
  have ha0 : a ≠ 0 := by
    simpa [ha] using log_ne_zero_of_one_lt hφ
  constructor
  · -- Forward direction: from `frourioSymbol φ s = 0` to lattice representation.
    intro h0
    -- Rewrite the equality in terms of complex exponentials.
    -- `frourioSymbol φ s = 0` means `φ^(-s) = φ^(s-1)`.
    have h_eq_cpow : (φ : ℂ) ^ (-s) = (φ : ℂ) ^ (s - 1) := by
      have := sub_eq_zero.mp (by simpa [frourioSymbol] using h0)
      exact this
    -- Express both sides via `exp (⋅ * log φ)`.
    have h_exp :
        Complex.exp ((-s) * a) = Complex.exp ((s - 1) * a) := by
      -- By definition of cpow for nonzero real base.
      have hφ_pos : 0 < φ := lt_trans (by norm_num) hφ
      have hφ_ne : (φ : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hφ_pos : φ ≠ 0)
      -- `φ^z = exp (z * log φ)` for `φ > 0`.
      have h_log : Complex.log (φ : ℂ) = (Real.log φ : ℂ) := by
        rw [← Complex.ofReal_log hφ_pos.le]
      have hL :
          (φ : ℂ) ^ (-s)
            = Complex.exp ((-s) * a) := by
        rw [Complex.cpow_def, if_neg hφ_ne, h_log, ha]
        congr 1
        ring
      have hR :
          (φ : ℂ) ^ (s - 1)
            = Complex.exp ((s - 1) * a) := by
        rw [Complex.cpow_def, if_neg hφ_ne, h_log, ha]
        congr 1
        ring
      rw [hL, hR] at h_eq_cpow
      exact h_eq_cpow
    -- Shift the exponents by `a/2` to obtain an even/odd symmetry.
    have h_symm :
        Complex.exp (-((s - (1 / 2 : ℂ)) * a))
          = Complex.exp ((s - (1 / 2 : ℂ)) * a) := by
      -- Multiply both sides of `h_exp` by `exp (a/2)`.
      have hL :
          Complex.exp ((-s) * a) * Complex.exp (a / 2)
            = Complex.exp (-((s - (1 / 2 : ℂ)) * a)) := by
        -- `-s * a + a/2 = -(s - 1/2) * a`
        have : (-s : ℂ) * a + a / 2 = -((s - (1 / 2 : ℂ)) * a) := by
          ring
        rw [← Complex.exp_add, this]
      have hR :
          Complex.exp ((s - 1) * a) * Complex.exp (a / 2)
            = Complex.exp ((s - (1 / 2 : ℂ)) * a) := by
        -- `(s - 1) * a + a/2 = (s - 1/2) * a`
        have : (s - (1 : ℂ)) * a + a / 2 = (s - (1 / 2 : ℂ)) * a := by
          ring
        rw [← Complex.exp_add, this]
      have := congrArg (fun z : ℂ => z * Complex.exp (a / 2)) h_exp
      -- LHS and RHS after the shift
      calc
        Complex.exp (-((s - (1 / 2 : ℂ)) * a))
            = Complex.exp ((-s) * a) * Complex.exp (a / 2) := hL.symm
        _ = Complex.exp ((s - 1) * a) * Complex.exp (a / 2) := this
        _ = Complex.exp ((s - (1 / 2 : ℂ)) * a) := hR
    -- Apply the standard equivalence: `exp(-w) = exp w` ↔ `exp(2w) = 1`.
    have hexp_one :
        Complex.exp (2 * ((s - (1 / 2 : ℂ)) * a)) = 1 :=
      (exp_neg_eq_iff_exp_two_eq_one
        (w := (s - (1 / 2 : ℂ)) * a)).mp h_symm
    -- Characterize the solutions of `exp(2 w a) = 1` via the integer lattice.
    rcases Complex.exp_eq_one_iff.mp
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hexp_one)
      with ⟨k, hk⟩
    -- From `2 (s - 1/2) a = 2 π i k`, divide by `2` and then by `a`.
    have hs' :
        (s - (1 / 2 : ℂ))
          = (Complex.I * (Real.pi : ℂ) * (k : ℂ)) / a := by
      -- Start from the canonical form of the exponent.
      have h2 :
          2 * ((s - (1 / 2 : ℂ)) * a)
            = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        simpa [mul_comm, mul_left_comm, mul_assoc, two_mul] using hk
      -- Multiply both sides on the left by `(2)⁻¹` to cancel the factor 2.
      have h2' := congrArg (fun z : ℂ => ((2 : ℂ)⁻¹) * z) h2
      have hL :
          ((2 : ℂ)⁻¹) * (2 * ((s - (1 / 2 : ℂ)) * a))
            = (s - (1 / 2 : ℂ)) * a := by
        have : ((2 : ℂ)⁻¹) * (2 : ℂ) = (1 : ℂ) := by
          simp
        simp [mul_comm, mul_left_comm, mul_assoc, this]
      have hR :
          ((2 : ℂ)⁻¹) * ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
            = (k : ℂ) * (Real.pi : ℂ) * Complex.I := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      have hsa :
          (s - (1 / 2 : ℂ)) * a
            = (k : ℂ) * (Real.pi : ℂ) * Complex.I := by
        simpa [hL, hR, mul_comm, mul_left_comm, mul_assoc] using h2'
      -- Divide by `a` to solve for `s - 1/2`.
      exact (eq_div_iff_mul_eq_of_ne ha0).mpr
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hsa)
    -- Package as the desired lattice form for `s`.
    refine ⟨-k, ?_⟩
    -- Rewrite `a` back as `Real.log φ`.
    have hs_eq :
        s - (1 / 2 : ℂ)
          = (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
              (Real.log φ : ℂ) := by
      simpa [ha] using hs'
    -- Solve for `s` and flip the sign of the integer index.
    have :
        s = (1 / 2 : ℂ) +
          (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
            (Real.log φ : ℂ) := by
      have := congrArg (fun z : ℂ => z + (1 / 2 : ℂ)) hs_eq
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
    -- Replace `k` by `-k` to match the claimed sign convention.
    -- Note: 1/2 + (I * π * k) / log φ = 1/2 - (I * π * (-k)) / log φ
    rw [this]
    push_cast
    ring
  · -- Reverse direction: any point on the lattice is a zero of `frourioSymbol`.
    intro hs
    rcases hs with ⟨k, hk⟩
    -- Rewrite the lattice representation as an identity for `(s - 1/2) * log φ`.
    set a : ℂ := (Real.log φ : ℂ) with ha
    have ha0 : a ≠ 0 := by
      simpa [ha] using log_ne_zero_of_one_lt hφ
    have hsa :
        (s - (1 / 2 : ℂ)) * a
          = -(Complex.I * (Real.pi : ℂ) * (k : ℂ)) := by
      -- Starting from `s = 1/2 - i π k / log φ`, multiply both sides by `a`.
      have hk' :
          s - (1 / 2 : ℂ)
            = -(Complex.I * (Real.pi : ℂ) * (k : ℂ)) / a := by
        have : s = (1 / 2 : ℂ) - (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
            (Real.log φ : ℂ) := hk
        calc
          s - (1 / 2 : ℂ)
              = ((1 / 2 : ℂ) - (Complex.I * (Real.pi : ℂ) * (k : ℂ)) /
                  (Real.log φ : ℂ)) - (1 / 2 : ℂ) := by
                rw [this]
          _ = -(Complex.I * (Real.pi : ℂ) * (k : ℂ)) / (Real.log φ : ℂ) := by
                ring
          _ = -(Complex.I * (Real.pi : ℂ) * (k : ℂ)) / a := by
                rw [← ha]
      -- Convert to multiplication form: multiply by `a` and simplify.
      rw [hk', div_mul_cancel₀ _ ha0]
    -- From `exp(2 (s - 1/2) a) = 1`, get the symmetry `exp(-w) = exp w`
    -- and hence the numerator of `frourioSymbol` vanishes.
    have h2 :
        2 * ((s - (1 / 2 : ℂ)) * a)
          = (-k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      calc
        2 * ((s - 1 / 2) * a) = 2 * (-(Complex.I * (Real.pi : ℂ) * (k : ℂ))) := by
          congr 1
        _ = -(2 * (Complex.I * (Real.pi : ℂ) * (k : ℂ))) := by ring
        _ = -(Complex.I * (Real.pi : ℂ) * (k : ℂ) * 2) := by ring
        _ = (-k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
          simp
          ring
    have hexp :
        Complex.exp (2 * ((s - (1 / 2 : ℂ)) * a)) = 1 := by
      refine Complex.exp_eq_one_iff.mpr ⟨-k, ?_⟩
      push_cast at h2 ⊢
      convert h2 using 2
    have heq :
        Complex.exp (-(s - (1 / 2 : ℂ)) * a)
          = Complex.exp ((s - (1 / 2 : ℂ)) * a) := by
      have := (exp_neg_eq_iff_exp_two_eq_one
        (w := (s - (1 / 2 : ℂ)) * a)).mpr hexp
      convert this using 2; ring
    -- Translate back to the original exponents `-s a` and `(s - 1) a`.
    have hnum : (φ : ℂ) ^ (-s) = (φ : ℂ) ^ (s - 1) := by
      -- Convert the symmetric identity into one for the shifted exponents.
      have hL :
          Complex.exp (-(s - (1 / 2 : ℂ)) * a)
            = Complex.exp ((-s) * a + a / 2) := by
        -- `-(s - 1/2) a = -s a + a/2`
        have : (-(s - (1 / 2 : ℂ)) * a)
            = ((-s) * a + a / 2) := by
          ring
        rw [this]
      have hR :
          Complex.exp ((s - (1 / 2 : ℂ)) * a)
            = Complex.exp ((s - 1) * a + a / 2) := by
        -- `(s - 1/2) a = (s - 1) a + a/2`
        have : ((s - (1 / 2 : ℂ)) * a)
            = ((s - 1) * a + a / 2) := by
          ring
        rw [this]
      -- Using `heq`, we have equality of the shifted exponents as well.
      have h' :
          Complex.exp ((-s) * a + a / 2)
            = Complex.exp ((s - 1) * a + a / 2) := by
        rw [← hL, ← hR]
        exact heq
      -- Cancel the common factor `exp(a/2)` to get back to `exp(-s a) = exp((s-1) a)`.
      have h_exp :
          Complex.exp ((-s) * a) = Complex.exp ((s - 1) * a) := by
        -- Rewrite using exp_add
        have hL' : Complex.exp ((-s) * a + a / 2)
              = Complex.exp ((-s) * a) * Complex.exp (a / 2) := Complex.exp_add _ _
        have hR' : Complex.exp ((s - 1) * a + a / 2)
              = Complex.exp ((s - 1) * a) * Complex.exp (a / 2) := Complex.exp_add _ _
        -- From h', we get the factored equality
        have h'' : Complex.exp ((-s) * a) * Complex.exp (a / 2)
              = Complex.exp ((s - 1) * a) * Complex.exp (a / 2) := by
          rw [← hL', ← hR']
          exact h'
        -- Cancel exp(a/2) on both sides
        have h_exp_pos : Complex.exp (a / 2) ≠ 0 := Complex.exp_ne_zero _
        exact mul_right_cancel₀ h_exp_pos h''
      -- Now fold back to cpow form: `φ^(-s) = φ^(s-1)`.
      have hφ_pos : 0 < φ := lt_trans (by norm_num) hφ
      have hφ_ne : (φ : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hφ_pos : φ ≠ 0)
      -- Relate Complex.log to Real.log for positive reals
      have h_log : Complex.log (φ : ℂ) = (Real.log φ : ℂ) := by
        rw [← Complex.ofReal_log hφ_pos.le]
      -- Use the cpow definition again.
      have hL :
          (φ : ℂ) ^ (-s)
            = Complex.exp ((-s) * a) := by
        rw [Complex.cpow_def, if_neg hφ_ne, h_log, ha]
        ring_nf
      have hR :
          (φ : ℂ) ^ (s - 1)
            = Complex.exp ((s - 1) * a) := by
        rw [Complex.cpow_def, if_neg hφ_ne, h_log, ha]
        ring_nf
      -- Conclude equality of cpows.
      rw [hL, hR]
      exact h_exp
    -- Finally, express `frourioSymbol φ s` in terms of this equality.
    have : frourioSymbol φ s = 0 := by
      -- `frourioSymbol φ s = φ^(-s) - φ^(s-1)`.
      simp [frourioSymbol, hnum]
    exact this

end Frourio
