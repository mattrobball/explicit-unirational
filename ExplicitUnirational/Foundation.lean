/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Project foundation

This module records the Mathlib interfaces on which the first formalization layers will build.
No project headline theorem is stated here.
-/

open CategoryTheory
open scoped AlgebraicGeometry

namespace ExplicitUnirational

/-- The weights of the ambient weighted projective space `ℙ(1,1,2,3)`. -/
def delPezzoWeights : Fin 4 → ℕ := ![1, 1, 2, 3]

@[simp] theorem delPezzoWeights_zero : delPezzoWeights 0 = 1 := rfl
@[simp] theorem delPezzoWeights_one : delPezzoWeights 1 = 1 := rfl
@[simp] theorem delPezzoWeights_two : delPezzoWeights 2 = 2 := rfl
@[simp] theorem delPezzoWeights_three : delPezzoWeights 3 = 3 := rfl

end ExplicitUnirational
