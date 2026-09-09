/-
Copyright (c) 2026 Matthew R. Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib
public import ExplicitUnirational.FunctionField.Dominance
import all ExplicitUnirational.FunctionField.Dominance

/-!
# Comparator solution: unirationality

Proves the statement of `comparator/Statement.lean`. The vocabulary below is duplicated from
that module and must stay structurally identical to it.

The witness is the map of `ExplicitUnirational.surfaceCoordRingToPlane`, sending
`ξ ↦ Θ/H²`, `η ↦ J/(2H³)`, `ζ ↦ −f₀/f₁` — the tangent-residual form of the relative
Abel–Jacobi map of [CLOP Lemma 3.4, Example 3.5] made explicit. Injectivity is `surfaceCoordRingToPlane_injective`.
-/

@[expose] public section

namespace ExplicitUnirationalChallenge

open MvPolynomial

abbrev PlaneField : Type := FractionRing (MvPolynomial (Fin 2) ℚ)

noncomputable def surfacePoly : MvPolynomial (Fin 3) ℚ :=
  4 * X 1 ^ 2 - 4 * X 0 ^ 3 - 4 * (X 2 ^ 2 * (3 - X 2)) * X 0
    - X 2 * (4 * X 2 ^ 4 - 23 * X 2 ^ 3 - 18 * X 2 ^ 2 + X 2 - 4)

abbrev surfaceCoordRing : Type := MvPolynomial (Fin 3) ℚ ⧸ Ideal.span {surfacePoly}

theorem unirationality :
    ∃ φ : surfaceCoordRing →ₐ[ℚ] PlaneField, Function.Injective φ :=
  ⟨ExplicitUnirational.surfaceCoordRingToPlane,
    ExplicitUnirational.surfaceCoordRingToPlane_injective⟩

end ExplicitUnirationalChallenge
#print axioms ExplicitUnirationalChallenge.unirationality
