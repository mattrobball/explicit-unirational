/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/

import ExplicitUnirational.FunctionField.TowerBProducts
import ExplicitUnirational.FunctionField.TangentResidual
import ExplicitUnirational.FunctionField.GeometricIntegrality
import ExplicitUnirational.FunctionField.MulThreeCert
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.RingTheory.AdjoinRoot

/-!
# The Weierstrass equation holds on the function field of the pencil cubic

The payoff of the Tower-B congruence programme.  Write `C` for the affine
cubic `gAff = 0` (the generic member of the rational pencil of [CLOP §4.1]), with
affine coordinate ring `affineCoordRing KQ = AdjoinRoot (monicCubicY KQ)`
(a domain, `GeometricIntegrality`) and function field
`curveFieldKQ = FractionRing (affineCoordRing KQ)`.

* `toCurve : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] affineCoordRing KQ` evaluates the
  ambient polynomial ring on the curve (`X 0 ↦ x`, `X 1 ↦ y`, `X 2 ↦ z`);
  `toCurve_gAff : toCurve gAff = 0`.
* `weierstrass_identity_on_curve`: pushing the congruence
  `weierstrass_congruence_mod_gAff` through `toCurve` gives, in the
  coordinate ring,
  `jAff² = 4·Θ³ + 4·A·Θ·H⁴ + Bnum·H⁶` (writing `Θ, H` for the covariant
  images).
* `hessAff` does not vanish on the curve (`toCurve_hessAff_ne_zero`), so in
  the function field the quantities `ξ = Θ/H²`, `η = J/(2H³)` make sense, and
* `noteCurveQ_equation_xi_eta`: `(ξ, η)` satisfies the Weierstrass equation
  of `noteCurveQ` base-changed to `curveFieldKQ`.

The last statement exhibits a `curveFieldKQ`-rational affine point of the
Jacobian model of [CLOP §4.1] (the equation for `J_η`); sending the Weierstrass
coordinate functions to `(ξ, η)` is the field embedding `K(W) ↪ K(C)` that underlies the dominant
rational map of the unirationality argument.  What is *not* formalized here
is the composition with the identification `K(C) ≅ ℚ(x, y)` of
`PencilRationality` ([CLOP §3, `Y = Bl_Σ ℙ²`], `adjoin_pencil_parameter_eq_top`) into a
single statement `P² ⤏ S`; that final glue is bookkeeping between the two
presentations of `K(C)` and is left for a follow-up.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MvPolynomial Polynomial

namespace ExplicitUnirational

/-! ## Coordinates on the affine curve -/

/-- The affine coordinate `x` in the coordinate ring of the pencil cubic. -/
noncomputable def curveX : affineCoordRing KQ :=
  AdjoinRoot.of (monicCubicY KQ) Polynomial.X

/-- The affine coordinate `y` (the adjoined root of the monic cubic). -/
noncomputable def curveY : affineCoordRing KQ :=
  AdjoinRoot.root (monicCubicY KQ)

/-- The pencil parameter `z` in the coordinate ring. -/
noncomputable def curveZ : affineCoordRing KQ :=
  AdjoinRoot.of (monicCubicY KQ) (Polynomial.C RatFunc.X)

/-- Evaluation of the ambient polynomial ring on the affine curve:
`X 0 ↦ x`, `X 1 ↦ y`, `X 2 ↦ z`. -/
noncomputable def toCurve : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] affineCoordRing KQ :=
  MvPolynomial.aeval ![curveX, curveY, curveZ]

theorem toCurve_X0 : toCurve (X 0) = curveX := by
  simp [toCurve]

theorem toCurve_X1 : toCurve (X 1) = curveY := by
  simp [toCurve]

theorem toCurve_X2 : toCurve (X 2) = curveZ := by
  simp [toCurve]

/-! ## The defining relation -/

private theorem z_inv_cancel :
    curveZ * AdjoinRoot.of (monicCubicY KQ) (Polynomial.C (RatFunc.X : KQ)⁻¹) = 1 := by
  rw [curveZ, ← map_mul, ← Polynomial.C_mul,
    mul_inv_cancel₀ (RatFunc.X_ne_zero (K := ℚ)), Polynomial.C_1, map_one]

/-- The image of the pencil cubic `gAff` vanishes on the curve. -/
theorem toCurve_gAff : toCurve gAff = 0 := by
  -- the monic relation satisfied by `curveY` (quotient index kept opaque;
  -- the explicit argument is definitionally `monicCubicY KQ`)
  have h : curveY ^ 3 + (curveY ^ 2
      + AdjoinRoot.of (monicCubicY KQ) (Polynomial.C (RatFunc.X : KQ)⁻¹) * curveY
      + AdjoinRoot.of (monicCubicY KQ) (Polynomial.C (RatFunc.X : KQ)⁻¹)
          * (-curveX ^ 3 + curveZ * curveX - curveZ)) = 0 := by
    have h0 : AdjoinRoot.mk (monicCubicY KQ)
        (Polynomial.X ^ 3 + (Polynomial.X ^ 2
          + Polynomial.C (Polynomial.C (RatFunc.X : KQ)⁻¹) * Polynomial.X
          + Polynomial.C (Polynomial.C (RatFunc.X : KQ)⁻¹
              * (-Polynomial.X ^ 3 + Polynomial.C (RatFunc.X : KQ) * Polynomial.X
                  - Polynomial.C (RatFunc.X : KQ))))) = 0 :=
      AdjoinRoot.mk_self
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, AdjoinRoot.mk_X,
      AdjoinRoot.mk_C] at h0
    unfold curveX curveY curveZ
    linear_combination h0
  have hzw : curveZ * AdjoinRoot.of (monicCubicY KQ) (Polynomial.C (RatFunc.X : KQ)⁻¹) = 1 :=
    z_inv_cancel
  unfold gAff
  simp only [map_add, map_sub, map_mul, map_pow, toCurve_X0, toCurve_X1, toCurve_X2]
  linear_combination curveZ * h
    - (curveY - curveX ^ 3 + curveZ * curveX - curveZ) * hzw


/-! ## `hessAff` does not vanish on the curve -/

/-- `y⁰`-coefficient of `hessAff` as a polynomial in `x` over `ℚ(z)`. -/
private noncomputable def hessQ0 : Polynomial KQ :=
  Polynomial.C (-(RatFunc.X : KQ) ^ 3)
    + Polynomial.C (3 + 9 * (RatFunc.X : KQ) ^ 2) * Polynomial.X
    + Polynomial.C (-3 * (RatFunc.X : KQ) ^ 2) * Polynomial.X ^ 2

/-- `y¹`-coefficient of `hessAff`. -/
private noncomputable def hessQ1 : Polynomial KQ :=
  Polynomial.C (-3 * (RatFunc.X : KQ) ^ 3)
    + Polynomial.C (3 * (RatFunc.X : KQ) + 27 * (RatFunc.X : KQ) ^ 2) * Polynomial.X
    + Polynomial.C (-9 * (RatFunc.X : KQ) ^ 2) * Polynomial.X ^ 2

/-- `y²`-coefficient of `hessAff`. -/
private noncomputable def hessQ2 : Polynomial KQ :=
  Polynomial.C (3 * (RatFunc.X : KQ) ^ 2 - 9 * (RatFunc.X : KQ)) * Polynomial.X

/-- The canonical degree-`≤ 2` representative of `hessAff` on the curve:
`hessAff` has `y`-degree two, so its image needs no reduction. -/
private noncomputable def hessP : Polynomial (Polynomial KQ) :=
  Polynomial.C hessQ0 + Polynomial.C hessQ1 * Polynomial.X
    + Polynomial.C hessQ2 * Polynomial.X ^ 2

private theorem toCurve_hessAff_eq :
    toCurve hessAff = AdjoinRoot.mk (monicCubicY KQ) hessP := by
  unfold hessAff hessP hessQ0 hessQ1 hessQ2
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    toCurve_X0, toCurve_X1, toCurve_X2, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  unfold curveX curveY curveZ
  ring

private theorem kq_lead_ne_zero : (3 * RatFunc.X ^ 2 - 9 * RatFunc.X : KQ) ≠ 0 := by
  have hrepr : (3 * RatFunc.X ^ 2 - 9 * RatFunc.X : KQ)
      = algebraMap (Polynomial ℚ) KQ (3 * Polynomial.X ^ 2 - 9 * Polynomial.X) := by
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_X, map_ofNat]
  rw [hrepr]
  apply RatFunc.algebraMap_ne_zero
  intro hcon
  have := congrArg (Polynomial.eval 1) hcon
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_zero, one_pow, mul_one] at this
  norm_num at this

private theorem hessP_coeff_two : hessP.coeff 2 = hessQ2 := by
  simp [hessP]

private theorem hessP_ne_zero : hessP ≠ 0 := by
  intro hcon
  have h2 := congrArg (fun q => Polynomial.coeff q 2) hcon
  simp only [hessP_coeff_two, Polynomial.coeff_zero] at h2
  rw [hessQ2] at h2
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr kq_lead_ne_zero) Polynomial.X_ne_zero h2

private theorem hessP_natDegree_le : hessP.natDegree ≤ 2 := by
  unfold hessP
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  refine max_le (le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)) ?_
  · simp [Polynomial.natDegree_C]
  · refine le_trans Polynomial.natDegree_mul_le ?_
    simp [Polynomial.natDegree_C, Polynomial.natDegree_X]
  · refine le_trans Polynomial.natDegree_mul_le ?_
    simp [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]

/-- The covariant `hessAff` does not vanish on the curve: its image in the
(integral) affine coordinate ring is nonzero. -/
theorem toCurve_hessAff_ne_zero : toCurve hessAff ≠ 0 := by
  rw [toCurve_hessAff_eq]
  intro hcon
  rw [AdjoinRoot.mk_eq_zero] at hcon
  have h1 : (monicCubicY KQ).natDegree ≤ hessP.natDegree :=
    Polynomial.natDegree_le_of_dvd hcon hessP_ne_zero
  rw [monicCubicY_natDegree] at h1
  have h2 := hessP_natDegree_le
  omega


/-! ## The Weierstrass identity in the coordinate ring -/

/-- Pushing the congruence `weierstrass_congruence_mod_gAff` onto the curve:
in the affine coordinate ring,
`J² = 4·Θ³ + 4·A·Θ·H⁴ + Bnum·H⁶`. -/
theorem weierstrass_identity_on_curve :
    toCurve jAff ^ 2 = 4 * toCurve thetaAff ^ 3
      + 4 * toCurve weierstrassA * toCurve thetaAff * toCurve hessAff ^ 4
      + toCurve weierstrassBnum * toCurve hessAff ^ 6 := by
  obtain ⟨c, hc⟩ := weierstrass_congruence_mod_gAff
  have h := congrArg toCurve hc
  simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, toCurve_gAff, zero_mul] at h
  linear_combination h

/-! ## The Weierstrass equation in the function field -/

/-- `ξ = Θ/H²` in the function field of the pencil cubic. -/
noncomputable def xiOnCurve : curveFieldKQ :=
  algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve thetaAff)
    / algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve hessAff) ^ 2

/-- `η = J/(2·H³)` in the function field of the pencil cubic. -/
noncomputable def etaOnCurve : curveFieldKQ :=
  algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve jAff)
    / (2 * algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve hessAff) ^ 3)

theorem hess_image_ne_zero :
    algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve hessAff) ≠ 0 := by
  rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  exact toCurve_hessAff_ne_zero

private theorem algebraMap_KQ_curveField_X :
    algebraMap KQ curveFieldKQ RatFunc.X
      = algebraMap (affineCoordRing KQ) curveFieldKQ curveZ := by
  rw [IsScalarTower.algebraMap_apply KQ (affineCoordRing KQ) curveFieldKQ]
  congr 1

private theorem a4_match :
    algebraMap KQ curveFieldKQ noteCurveQ.a₄
      = algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve weierstrassA) := by
  have hA : toCurve weierstrassA = curveZ ^ 2 * (3 - curveZ) := by
    unfold weierstrassA
    simp only [map_sub, map_mul, map_pow, map_ofNat, toCurve_X2]
  rw [hA]
  show algebraMap KQ curveFieldKQ (RatFunc.X ^ 2 * (3 - RatFunc.X)) = _
  simp only [map_mul, map_pow, map_sub, map_ofNat, algebraMap_KQ_curveField_X]

private theorem a6_match :
    4 * algebraMap KQ curveFieldKQ noteCurveQ.a₆
      = algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve weierstrassBnum) := by
  have hB : toCurve weierstrassBnum
      = curveZ * (4 * curveZ ^ 4 - 23 * curveZ ^ 3 - 18 * curveZ ^ 2 + curveZ - 4) := by
    unfold weierstrassBnum
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, toCurve_X2]
  rw [hB]
  have h4 : (4 : KQ) * noteCurveQ.a₆
      = RatFunc.X * (4 * RatFunc.X ^ 4 - 23 * RatFunc.X ^ 3
          - 18 * RatFunc.X ^ 2 + RatFunc.X - 4) := by
    show (4 : KQ) * (RatFunc.X / 4 * noteP) = _
    rw [noteP]
    ring
  calc 4 * algebraMap KQ curveFieldKQ noteCurveQ.a₆
      = algebraMap KQ curveFieldKQ ((4 : KQ) * noteCurveQ.a₆) := by
        rw [map_mul, map_ofNat]
    _ = _ := by
        rw [h4]
        simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, algebraMap_KQ_curveField_X]

/-- **The Weierstrass equation holds in the function field of the pencil
cubic** (the Weierstrass model of [CLOP §4.1], the equation for `J_η`): the
pair `ξ = Θ/H²`, `η = J/(2H³)` is an affine point of
`noteCurveQ` over `curveFieldKQ = Frac(ℚ(z)[x,y]/(g))`.  Together with
the rationality of the incidence surface ([CLOP §3, `Y = Bl_Σ ℙ²`],
`PencilRationality.adjoin_pencil_parameter_eq_top`, identifying
the function field of the pencil member with a rational function field in the
plane coordinates), this is the field-embedding form `K(W) ↪ K(C)` of the
dominant rational map underlying unirationality. -/
theorem noteCurveQ_equation_xi_eta :
    (noteCurveQ.baseChange curveFieldKQ).toAffine.Equation xiOnCurve etaOnCurve := by
  haveI : CharZero curveFieldKQ :=
    Algebra.charZero_of_charZero (R := KQ) (A := curveFieldKQ)
  rw [WeierstrassCurve.Affine.equation_iff]
  have hidK := congrArg (algebraMap (affineCoordRing KQ) curveFieldKQ)
    weierstrass_identity_on_curve
  simp only [map_add, map_mul, map_pow, map_ofNat] at hidK
  rw [← a4_match, ← a6_match] at hidK
  set H := algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve hessAff) with hH
  set J := algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve jAff) with hJ
  set Th := algebraMap (affineCoordRing KQ) curveFieldKQ (toCurve thetaAff) with hTh
  have hne : H ≠ 0 := hess_image_ne_zero
  have h2 : (2 : curveFieldKQ) ≠ 0 := two_ne_zero
  have h4H : (4 : curveFieldKQ) * H ^ 6 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ hne)
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆,
    show noteCurveQ.a₁ = 0 from rfl, show noteCurveQ.a₂ = 0 from rfl,
    show noteCurveQ.a₃ = 0 from rfl, map_zero, zero_mul, mul_zero, add_zero, zero_add]
  have heta : etaOnCurve ^ 2 = J ^ 2 / (4 * H ^ 6) := by
    unfold etaOnCurve
    rw [← hJ, ← hH, div_pow,
      show ((2 : curveFieldKQ) * H ^ 3) ^ 2 = 4 * H ^ 6 by ring]
  rw [heta, div_eq_iff h4H]
  unfold xiOnCurve
  rw [← hTh, ← hH]
  field_simp
  linear_combination hidK

#print axioms toCurve_gAff
#print axioms toCurve_hessAff_ne_zero
#print axioms weierstrass_identity_on_curve
#print axioms noteCurveQ_equation_xi_eta

end ExplicitUnirational
