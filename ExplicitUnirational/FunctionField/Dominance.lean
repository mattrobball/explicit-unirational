/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.FunctionField.Unirationality
import all ExplicitUnirational.FunctionField.TangentResidual
import all ExplicitUnirational.FunctionField.PencilRationality
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Dominance of the unirational parametrization

Transcendence input for the injectivity of `surfaceCoordRingToPlane`.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace ExplicitUnirational

local notation "ι₂" => algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ)

instance : IsScalarTower ℚ (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) :=
  FunctionField.isScalarTower_planeField

/-! ## Step 1: the pencil parameter is transcendental over `ℚ` -/

public theorem planeZeta_mul_f₁aff : planeZeta * ι₂ f₁aff = ι₂ (-f₀aff) := by
  have h : ι₂ f₁aff ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact f₁aff_ne_zero
  show FunctionField.pencilParameter f₀aff f₁aff * _ = _
  unfold FunctionField.pencilParameter
  rw [div_mul_cancel₀ _ h, map_neg]

/-- The pencil parameter `ζ = −f₀/f₁` is transcendental over `ℚ`. -/
public theorem transcendental_planeZeta : Transcendental ℚ planeZeta := by
  intro halg
  -- `ζ` is integral over `ℚ`, hence over `ℚ[x, y]`
  have hintQ : IsIntegral ℚ planeZeta := halg.isIntegral
  have hint : IsIntegral (MvPolynomial (Fin 2) ℚ) planeZeta := hintQ.tower_top
  -- `ℚ[x, y]` is a UFD, hence integrally closed in its fraction field
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have h1 : ι₂ (a * f₁aff) = ι₂ (-f₀aff) := by
    rw [map_mul, ha]; exact planeZeta_mul_f₁aff
  have h2 : a * f₁aff = -f₀aff :=
    IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) h1
  -- evaluate at `(x, y) = (1, 0)`, where `f₁ = 0` but `-f₀ = 1`
  have h3 := congrArg (eval ![(1 : ℚ), 0]) h2
  simp [f₀aff, f₁aff] at h3

#print axioms transcendental_planeZeta

end ExplicitUnirational
