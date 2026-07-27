/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.FunctionField.GeometricIntegrality
public import ExplicitUnirational.FunctionField.TangentResidual
public import ExplicitUnirational.FunctionField.TorsorDescent
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Residual degree of the tangent-residual map (Route B, degree half of Lemma 2.1)

Note Lemma 2.1 / DESIGN Route B: the tangent-residual construction supplies Weierstrass
coordinates `(ξ, η)` on the Jacobian of the generic cubic `C : g = 0` over `K = ℚ(z)`, and
the degree of the induced function-field extension is

```
  [K(C) : K(ξ, η)] = 9.
```

A monolithic eliminant for this identity has total degree 18 with thousands of terms. This
module attacks the claim by a **field tower**, reusing the staged `Y`-reductions of
`TangentResidual` only as orientation (not as a single ring goal).

## Tower

```
  [K(C) : K(ξ)] = [K(C) : K(ξ, η)] · [K(ξ, η) : K(ξ)]
  [K(ξ, η) : K(ξ)] = 2     (η² = ξ³ + A ξ + B, η ∉ K(ξ))
  [K(C) : K(X)] = 3      (g monic of Y-degree 3 after clearing)
```

so the residual claim is equivalent to `[K(C) : K(ξ)] = 18`.

## Status (honest)

| Item | Statement | Status |
| --- | --- | --- |
| (1) | `[K(ξ, η) : K(ξ)] = 2` | **proved** abstractly for any short Weierstrass model |
| (2) | `[K(C) : K(X)] = 3` | **proved** for the monic model of the rational pencil |
| (3) | `[K(C) : K(ξ)] = 18` | **open** — offline sympy: resultant of `redTheta − ξ·redH2` vs `g` is degree 3 in `ξ` and 18 in `X`; square-free at specializations of `z`. Lean certificate not yet installed |
| (4) | `[K(C) : K(ξ, η)] = 9` | **conditional** on (3), via the tower identity below |

Coordinates of `ξ` on the affine chart: after `Y`-reduction one has
`ξ ≡ redTheta / redH2 (mod gAff)` (Fisher/Sage normal form of `Θ/H²`). The reduced forms live
in `TangentResidual`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

open Polynomial
open scoped RatFunc IntermediateField

namespace ExplicitUnirational

/-! ## Instances packaging the monic cubic coordinate ring over `KQ[X]` -/

public noncomputable instance instIsDomain_affineCoordRing_KQ :
    IsDomain (affineCoordRing KQ) :=
  isDomain_affineCoordRing_KQ

public noncomputable instance instFree_affineCoordRing_KQ :
    Module.Free (Polynomial KQ) (affineCoordRing KQ) :=
  (monicCubicY_monic KQ).free_adjoinRoot

public noncomputable instance instFinite_affineCoordRing_KQ :
    Module.Finite (Polynomial KQ) (affineCoordRing KQ) :=
  (AdjoinRoot.isAdjoinRootMonic (monicCubicY KQ) (monicCubicY_monic KQ)).finite

public noncomputable instance instIsAlgebraic_affineCoordRing_KQ :
    Algebra.IsAlgebraic (Polynomial KQ) (affineCoordRing KQ) :=
  Algebra.IsAlgebraic.of_finite (R := Polynomial KQ) (A := affineCoordRing KQ)

public noncomputable instance instFaithfulSMul_affineCoordRing_KQ :
    FaithfulSMul (Polynomial KQ) (affineCoordRing KQ) :=
  Module.IsTorsionFree.to_faithfulSMul

attribute [instance] FractionRing.liftAlgebra

/-! ## Item (2): `[K(C) : K(X)] = 3` -/

/-- Coordinate-ring form: `KQ[X][Y] / (monicCubicY)` is free of rank 3 over `KQ[X]`. -/
public theorem finrank_coordRing_over_KX :
    Module.finrank (Polynomial KQ) (affineCoordRing KQ) = 3 := by
  have h := (AdjoinRoot.isAdjoinRootMonic (monicCubicY KQ) (monicCubicY_monic KQ)).finrank
  rwa [monicCubicY_natDegree KQ] at h

/-- **Function-field form of `[K(C) : K(X)] = 3`.**

`Frac(KQ[X][Y]/(monicCubicY))` has degree 3 over `Frac(KQ[X])`, by freeness of the monic
adjoin-root and `Algebra.IsAlgebraic.finrank_of_isFractionRing`. -/
public theorem finrank_curveField_over_KX :
    Module.finrank (FractionRing (Polynomial KQ)) (FractionRing (affineCoordRing KQ)) = 3 := by
  have h := finrank_fractionRing_eq (Polynomial KQ) (affineCoordRing KQ)
  rwa [finrank_coordRing_over_KX] at h

/-- Same statement with the project's `curveFieldKQ` abbreviation. -/
public theorem finrank_curveFieldKQ_over_KX :
    Module.finrank (FractionRing (Polynomial KQ)) curveFieldKQ = 3 :=
  finrank_curveField_over_KX

/-! ## Item (1): `[K(ξ, η) : K(ξ)] = 2` for short Weierstrass models

Over any field `F`, the short Weierstrass cubic `x³ + A x + B` has odd degree 3, hence is not
a square in `F(x)`. Therefore `T² − (x³ + A x + B)` is irreducible over `F(x)` by the
prime-degree Kummer criterion, and adjoining a root yields a free extension of rank 2.
-/

variable {F : Type*} [Field F]

/-- A nonzero polynomial of odd degree is not a square in the rational function field. -/
public theorem not_isSquare_ratFunc_of_odd_natDegree {p : F[X]} (hp : p ≠ 0)
    (hodd : Odd p.natDegree) :
    ¬ IsSquare (algebraMap F[X] (RatFunc F) p) := by
  rintro ⟨r, hr⟩
  have hmap0 : algebraMap F[X] (RatFunc F) p ≠ 0 :=
    mt (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] (RatFunc F))).mp hp
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hmap0 (by simpa using hr)
  have hdeg : (p.natDegree : ℤ) = 2 * RatFunc.intDegree r := by
    calc
      (p.natDegree : ℤ) = RatFunc.intDegree (algebraMap F[X] (RatFunc F) p) :=
        (RatFunc.intDegree_polynomial (p := p)).symm
      _ = RatFunc.intDegree (r * r) := by rw [hr]
      _ = RatFunc.intDegree r + RatFunc.intDegree r := RatFunc.intDegree_mul hr0 hr0
      _ = 2 * RatFunc.intDegree r := by ring
  have heven : Even p.natDegree := by
    refine (even_iff_two_dvd (a := p.natDegree)).2 ?_
    exact (Int.natCast_dvd_natCast (m := 2) (n := p.natDegree)).1 (by
      rw [hdeg]
      exact dvd_mul_right _ _)
  exact Nat.not_even_iff_odd.mpr hodd heven

/-- The short Weierstrass cubic `X³ + A X + B` has degree 3. -/
public theorem natDegree_weierstrass_cubic (A B : F) :
    (X ^ 3 + C A * X + C B : F[X]).natDegree = 3 := by
  have htail : (C A * X + C B : F[X]).degree < 3 := by
    refine lt_of_le_of_lt (degree_add_le _ _) ?_
    refine max_lt_iff.mpr ⟨?_, ?_⟩
    · calc
        (C A * X : F[X]).degree ≤ (C A).degree + (X : F[X]).degree := degree_mul_le _ _
        _ ≤ 0 + 1 := add_le_add degree_C_le (by simp [degree_X])
        _ = 1 := by norm_num
        _ < 3 := by exact_mod_cast (by norm_num : (1 : ℕ) < 3)
    · calc
        (C B : F[X]).degree ≤ 0 := degree_C_le
        _ < 3 := by exact_mod_cast (by norm_num : (0 : ℕ) < 3)
  have hlt : (C A * X + C B : F[X]).degree < (X ^ 3 : F[X]).degree := by
    rwa [degree_X_pow]
  have hform : (X ^ 3 + C A * X + C B : F[X]) = X ^ 3 + (C A * X + C B) := by ring
  rw [hform]
  exact (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 3)).1
    (by rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow])

/-- The short Weierstrass cubic is not a square in `F(X)`. -/
public theorem not_isSquare_weierstrass_cubic (A B : F) :
    ¬ IsSquare (algebraMap F[X] (RatFunc F) (X ^ 3 + C A * X + C B)) := by
  refine not_isSquare_ratFunc_of_odd_natDegree ?_ ?_
  · intro h
    have := congrArg natDegree h
    rw [natDegree_zero, natDegree_weierstrass_cubic A B] at this
    exact absurd this (by norm_num)
  · rw [natDegree_weierstrass_cubic A B]
    decide

/-- `T² − (x³ + A x + B)` is irreducible over `F(x)`. -/
public theorem irreducible_weierstrassY (A B : F) :
    Irreducible
      (X ^ 2 - C (algebraMap F[X] (RatFunc F) (X ^ 3 + C A * X + C B)) : (RatFunc F)[X]) := by
  refine (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr ?_
  intro b hb
  exact not_isSquare_weierstrass_cubic A B ⟨b, by simpa [pow_two] using hb.symm⟩

/-- Affine coordinate ring of the short Weierstrass model over the `x`-line `F(x)`. -/
public noncomputable abbrev weierstrassCoordRing (A B : F) : Type _ :=
  AdjoinRoot (X ^ 2 - C (algebraMap F[X] (RatFunc F) (X ^ 3 + C A * X + C B)))

public theorem monic_weierstrassY (A B : F) :
    (X ^ 2 - C (algebraMap F[X] (RatFunc F) (X ^ 3 + C A * X + C B)) : (RatFunc F)[X]).Monic :=
  monic_X_pow_sub_C _ (by norm_num : (2 : ℕ) ≠ 0)

public theorem natDegree_weierstrassY (A B : F) :
    (X ^ 2 - C (algebraMap F[X] (RatFunc F) (X ^ 3 + C A * X + C B)) :
      (RatFunc F)[X]).natDegree = 2 :=
  natDegree_X_pow_sub_C

/-- **Item (1): `[K(ξ, η) : K(ξ)] = 2`.**

For any short Weierstrass coefficients `A, B` over a field `F`, the extension
`F(x)[y] / (y² − (x³ + A x + B))` has degree exactly 2 over `F(x)`. -/
public theorem finrank_weierstrassCoord_over_X (A B : F) :
    Module.finrank (RatFunc F) (weierstrassCoordRing A B) = 2 := by
  have h := (AdjoinRoot.isAdjoinRootMonic _ (monic_weierstrassY A B)).finrank
  rwa [natDegree_weierstrassY A B] at h

/-- Specialization to the note's model (3.7) over `KQ = ℚ(z)`. -/
public theorem finrank_weierstrassCoord_noteCurveQ :
    Module.finrank (RatFunc KQ)
      (weierstrassCoordRing (F := KQ) noteCurveQ.a₄ noteCurveQ.a₆) = 2 :=
  finrank_weierstrassCoord_over_X noteCurveQ.a₄ noteCurveQ.a₆

/-! ## Tower arithmetic toward degree 9

Once `[K(C) : K(ξ)] = 18` is available, the tower law with item (1) yields degree 9.
-/

/-- **Tower identity.** If `[L : M] = 2` and `[L' : M] = 18` with `M ≤ L ≤ L'`, then
`[L' : L] = 9`. Abstract packaging of the residual-degree conclusion. -/
public theorem finrank_eq_nine_of_tower
    {M L L' : Type*} [Field M] [Field L] [Field L']
    [Algebra M L] [Algebra M L'] [Algebra L L']
    [IsScalarTower M L L']
    [FiniteDimensional M L] [FiniteDimensional M L']
    (hML : Module.finrank M L = 2)
    (hML' : Module.finrank M L' = 18) :
    Module.finrank L L' = 9 := by
  -- Tower law: [L' : M] = [L : M] * [L' : L], so 18 = 2 * [L' : L]
  have hmul := Module.finrank_mul_finrank M L L'
  have h : (2 : ℕ) * Module.finrank L L' = 18 := by
    calc
      2 * Module.finrank L L' = Module.finrank M L * Module.finrank L L' := by rw [hML]
      _ = Module.finrank M L' := hmul
      _ = 18 := hML'
  -- 2 * n = 18 ⇒ n = 9  (and `18 / 2` reduces definitionally to `9`)
  exact (Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2) h.symm).symm

/-- Conditional residual-degree conclusion: items (1) and (3) imply degree 9. -/
public theorem finrank_residual_eq_nine_of_finrank_xi
    {M L L' : Type*} [Field M] [Field L] [Field L']
    [Algebra M L] [Algebra M L'] [Algebra L L']
    [IsScalarTower M L L']
    [FiniteDimensional M L] [FiniteDimensional M L']
    (h_eta : Module.finrank M L = 2)
    (h_xi : Module.finrank M L' = 18) :
    Module.finrank L L' = 9 :=
  finrank_eq_nine_of_tower h_eta h_xi

/-! ## Orientation for item (3): `ξ` relative to `K(X)`

After `Y`-reduction (`thetaAff_mod`, `hessAff_sq_mod` in `TangentResidual`), the Fisher
covariant ratio is represented by the reduced forms `redTheta` and `redH2`, both of
`Y`-degree ≤ 2. Offline sympy computation of

```
  Res_Y (gAff, redTheta − ξ · redH2) ∈ ℚ[X, z, ξ]
```

yields a primitive polynomial of degree **3** in `ξ` and degree **18** in `X`, square-free at
specializations `z ∈ {2,3,5}`. Combined with item (2) this suggests

* `[K(X, ξ) : K(X)] = 3` (so `K(C) = K(X, ξ)`),
* `[K(X, ξ) : K(ξ)] = 18` (so `[K(C) : K(ξ)] = 18`),

which is exactly the missing step. Installing the resultant as a Lean `ring` certificate
(chunked, as in `TangentResidual`) is the remaining Attack-2 work package; Attack 1 does not
collapse further because `ξ ∉ K(X)` (the cubic factor in `ξ` is nontrivial).
-/

/-! ## Axiom audit -/

#print axioms finrank_coordRing_over_KX
#print axioms finrank_curveField_over_KX
#print axioms finrank_curveFieldKQ_over_KX
#print axioms not_isSquare_ratFunc_of_odd_natDegree
#print axioms not_isSquare_weierstrass_cubic
#print axioms irreducible_weierstrassY
#print axioms finrank_weierstrassCoord_over_X
#print axioms finrank_weierstrassCoord_noteCurveQ
#print axioms finrank_eq_nine_of_tower
#print axioms finrank_residual_eq_nine_of_finrank_xi

end ExplicitUnirational
