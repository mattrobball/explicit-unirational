/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.Cert.Invariants
public import ExplicitUnirational.FunctionField.MulThreeCert
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Tangent residual and Weierstrass coordinates on the rational pencil (Route B)

Route B for Endpoint A0: an explicit, certificate-shaped treatment of the degree-9 map
from the generic plane cubic of the pencil of [CLOP §4.1] to its Jacobian (the Weierstrass
model of [CLOP §4.1], the equation for `J_η`), bypassing Picard schemes and torsor trivialization.

## Mathematics

Let `G_z = F₀ + z F₁` be the generic member of the pencil of [CLOP §4.1], and write
`g(X,Y) = G_z(X,Y,1)` for the affine chart `Z = 1`. For a point `P = (x,y)` on `g = 0`
with nonzero gradient, the tangent line at `P` meets the cubic again at a residual point
`Q(P)`. Classically `2P + Q(P) ∼ λ` (hyperplane class), so
`α_λ(P) = [3P − λ] ∼ [P − Q(P)]` ([CLOP Lemma 3.4] with [CLOP Example 3.5] / DESIGN §3
Route B).

This module supplies:

1. **Tangent residual.** Explicit polynomials giving `Q(P)` in affine coordinates, with the
   defining identities (on the curve, on the tangent line) checked by `ring`.

2. **Weierstrass coefficients.** Matching of the Jacobian model of [CLOP §4.1] (the equation
   for `J_η`) / `noteCurveQ` to the Aronhold invariants `S`, `T` of the ternary cubic
   (`27 S = A`, `−27 T = 4B`).

3. **Staged `Y`-reduction of Fisher/Sage covariants.** Integer forms of `Θ` and reduced normal
   forms of `H²`, `H³` modulo `gAff`, each as a separate `ring` certificate (no monolithic
   ~1900-term Weierstrass witness). Higher rungs measured offline.

4. **Degree 9.** Size report for a resultant certificate; full minimality left for a
   follow-up (no `sorry`).

Coordinates: `X 0 = X`, `X 1 = Y`, `X 2 = z` (parameter), matching `MulThreeCert`.
-/

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000

noncomputable section

open MvPolynomial

namespace ExplicitUnirational

/-! ## Affine cubic of the rational pencil -/

/-- Affine chart `Z = 1` of the generic member `G_z = F₀ + z F₁` of the pencil of [CLOP §4.1]:
`g = Y − X³ + z(X + Y³ + Y² − 1)`. Variables: `X 0 = X`, `X 1 = Y`, `X 2 = z`. -/
public noncomputable def gAff : MvPolynomial (Fin 3) ℚ :=
  (X 1) ^ 3 * (X 2)
    - (X 0) ^ 3
    + (X 1) ^ 2 * (X 2)
    + (X 0) * (X 2)
    + (X 1)
    - (X 2)

/-- Partial derivative `∂g/∂X`. -/
public noncomputable def gAff_pderivX : MvPolynomial (Fin 3) ℚ :=
  -3 * (X 0) ^ 2 + (X 2)

/-- Partial derivative `∂g/∂Y`. -/
public noncomputable def gAff_pderivY : MvPolynomial (Fin 3) ℚ :=
  3 * (X 1) ^ 2 * (X 2) + 2 * (X 1) * (X 2) + 1

/-! ## Tangent direction and residual binary coefficients -/

/-- Affine tangent direction `(-g_Y, g_X)` at the variable point `(X,Y)`. -/
public noncomputable def tangentDx : MvPolynomial (Fin 3) ℚ :=
  -(3 * (X 1) ^ 2 * (X 2) + 2 * (X 1) * (X 2) + 1)

public noncomputable def tangentDy : MvPolynomial (Fin 3) ℚ :=
  -3 * (X 0) ^ 2 + (X 2)

public theorem tangentDx_eq : tangentDx = -gAff_pderivY := by
  unfold tangentDx gAff_pderivY
  ring

public theorem tangentDy_eq : tangentDy = gAff_pderivX := by
  unfold tangentDy gAff_pderivX
  ring

/-- Leading coefficient `a₃` of the cubic restriction of `g` to the tangent line
parametrized as `(X,Y) + t · (-g_Y, g_X)`. CAS-generated; checked below. -/
public noncomputable def residualA3 : MvPolynomial (Fin 3) ℚ :=
  27 * (X 1) ^ 6 * (X 2) ^ 3
    + 54 * (X 1) ^ 5 * (X 2) ^ 3
    - 27 * (X 0) ^ 6 * (X 2)
    + 36 * (X 1) ^ 4 * (X 2) ^ 3
    + 27 * (X 0) ^ 4 * (X 2) ^ 2
    + 27 * (X 1) ^ 4 * (X 2) ^ 2
    + 8 * (X 1) ^ 3 * (X 2) ^ 3
    - 9 * (X 0) ^ 2 * (X 2) ^ 3
    + 36 * (X 1) ^ 3 * (X 2) ^ 2
    + 12 * (X 1) ^ 2 * (X 2) ^ 2
    + (X 2) ^ 4
    + 9 * (X 1) ^ 2 * (X 2)
    + 6 * (X 1) * (X 2)
    + 1

/-- Quadratic coefficient `a₂` of the same restriction (the linear coefficient vanishes
identically by tangency of the direction). -/
public noncomputable def residualA2 : MvPolynomial (Fin 3) ℚ :=
  -27 * (X 0) * (X 1) ^ 4 * (X 2) ^ 2
    + 27 * (X 0) ^ 4 * (X 1) * (X 2)
    - 36 * (X 0) * (X 1) ^ 3 * (X 2) ^ 2
    + 9 * (X 0) ^ 4 * (X 2)
    - 18 * (X 0) ^ 2 * (X 1) * (X 2) ^ 2
    - 12 * (X 0) * (X 1) ^ 2 * (X 2) ^ 2
    - 6 * (X 0) ^ 2 * (X 2) ^ 2
    - 18 * (X 0) * (X 1) ^ 2 * (X 2)
    + 3 * (X 1) * (X 2) ^ 3
    - 12 * (X 0) * (X 1) * (X 2)
    + (X 2) ^ 3
    - 3 * (X 0)

/-- Numerator of the residual `X`-coordinate: `Q_X = residualQx / residualA3`. -/
public noncomputable def residualQx : MvPolynomial (Fin 3) ℚ :=
  (X 0) * residualA3 - residualA2 * tangentDx

/-- Numerator of the residual `Y`-coordinate: `Q_Y = residualQy / residualA3`. -/
public noncomputable def residualQy : MvPolynomial (Fin 3) ℚ :=
  (X 1) * residualA3 - residualA2 * tangentDy

/-! ### Cleared evaluation of the affine cubic -/

/-- Homogenized (cleared-denominator) evaluation `D³ · g(N_X/D, N_Y/D)`. -/
public noncomputable def gAffCleared (nx ny d : MvPolynomial (Fin 3) ℚ) :
    MvPolynomial (Fin 3) ℚ :=
  ny * d ^ 2 - nx ^ 3
    + (X 2) * (nx * d ^ 2 + ny ^ 3 + ny ^ 2 * d - d ^ 3)

/-! ### Residual identities (polynomial, not merely on the curve) -/

/-- The residual direction is tangent: `∇g · (-g_Y, g_X) = 0`. -/
public theorem residual_direction_is_tangent :
    gAff_pderivX * tangentDx + gAff_pderivY * tangentDy = 0 := by
  unfold gAff_pderivX gAff_pderivY tangentDx tangentDy
  ring

/-- The residual point lies on the tangent line through `(X,Y)`.
Equivalent form: `∇g · (Q − A₃ · P) = 0`. -/
public theorem residual_on_tangent_line :
    gAff_pderivX * (residualQx - (X 0) * residualA3)
      + gAff_pderivY * (residualQy - (X 1) * residualA3) = 0 := by
  unfold residualQx residualQy residualA3 residualA2 tangentDx tangentDy
    gAff_pderivX gAff_pderivY
  ring

/-- **Residual lies on the cubic when the base point does.**

As rational functions, `g(Q) = g(P)` along the tangent parametrization (double contact
kills the linear term). Clearing denominators yields the polynomial identity
`gAffCleared residualQx residualQy residualA3 = g · residualA3³`. -/
public theorem residual_on_curve_identity :
    gAffCleared residualQx residualQy residualA3 = gAff * residualA3 ^ 3 := by
  unfold gAffCleared residualQx residualQy residualA3 residualA2
    tangentDx tangentDy gAff
  ring

/-- Corollary: `g` divides the cleared residual evaluation. -/
public theorem residual_on_curve_divisible :
    gAff ∣ gAffCleared residualQx residualQy residualA3 :=
  ⟨residualA3 ^ 3, residual_on_curve_identity⟩

/-! ## Weierstrass model coefficients (the Weierstrass model of [CLOP §4.1], the equation for
`J_η`, i.e. `noteCurveQ`) -/

/-- Coefficient `A = z²(3 − z)` of the Weierstrass model of [CLOP §4.1] (the equation for `J_η`),
i.e. `noteCurveQ.a₄`, as a polynomial in `z = X 2`. -/
public noncomputable def weierstrassA : MvPolynomial (Fin 3) ℚ :=
  (X 2) ^ 2 * (3 - X 2)

/-- Numerator of `B = (z/4) P(z)`: `Bnum = z · P(z)` so `B = Bnum/4`. -/
public noncomputable def weierstrassBnum : MvPolynomial (Fin 3) ℚ :=
  (X 2) * (4 * (X 2) ^ 4 - 23 * (X 2) ^ 3 - 18 * (X 2) ^ 2 + (X 2) - 4)

/-! ## Aronhold invariants vs. Weierstrass coefficients

For the ternary cubic `G_z`, the Aronhold invariants (Sage normalization) are
`S = z²(3−z)/27` and `T = −z P(z)/27`. The short Weierstrass model produced by
`WeierstrassForm` is `Y² = X³ + (27S) X + (−27/4 T)`, which is exactly the Weierstrass model
of [CLOP §4.1] (the equation for `J_η`):
`Y² = X³ + A X + B` with `A = z²(3−z)` and `B = (z/4) P(z)`. -/

/-- `27 S = A` as an identity of rational coefficients in `z`. -/
public theorem twentySeven_S_eq_A_coeff (z : ℚ) :
    (27 : ℚ) * (z ^ 2 / 9 - z ^ 3 / 27) = z ^ 2 * (3 - z) := by
  ring

/-- `−27 T = Bnum = 4 B` as an identity of rational coefficients in `z`. -/
public theorem neg_twentySeven_T_eq_Bnum_coeff (z : ℚ) :
    (-27 : ℚ) * (-(z * (4 * z ^ 4 - 23 * z ^ 3 - 18 * z ^ 2 + z - 4)) / 27) =
      z * (4 * z ^ 4 - 23 * z ^ 3 - 18 * z ^ 2 + z - 4) := by
  ring

/-- Polynomial form: `C 27 * aronholdS_poly = weierstrassA` with cleared `S`. -/
public noncomputable def aronholdS_poly : MvPolynomial (Fin 3) ℚ :=
  3 * (X 2) ^ 2 - (X 2) ^ 3

/-- `aronholdS_poly = 27 S` (so `S = aronholdS_poly / 27`). -/
public theorem aronholdS_poly_eq_weierstrassA :
    aronholdS_poly = weierstrassA := by
  unfold aronholdS_poly weierstrassA
  ring

/-- Polynomial form: `aronholdT_poly = −27 T = Bnum`. -/
public noncomputable def aronholdT_poly : MvPolynomial (Fin 3) ℚ :=
  (X 2) * (4 * (X 2) ^ 4 - 23 * (X 2) ^ 3 - 18 * (X 2) ^ 2 + (X 2) - 4)

public theorem aronholdT_poly_eq_weierstrassBnum :
    aronholdT_poly = weierstrassBnum := by
  unfold aronholdT_poly weierstrassBnum
  ring

/-! ## Affine Hessian (integer form of Sage `H_sage` at `Z = 1`)

`hessAff = 27 · H_sage|_{Z=1}` with `H_sage = det(∂²G)/216`. Related to
`Invariants.H_G_z` by a constant factor on the chart `Z = 1`. -/

public noncomputable def hessAff : MvPolynomial (Fin 3) ℚ :=
  -9 * (X 0) ^ 2 * (X 1) * (X 2) ^ 2
    + 3 * (X 0) * (X 1) ^ 2 * (X 2) ^ 2
    - 3 * (X 0) ^ 2 * (X 2) ^ 2
    - 9 * (X 0) * (X 1) ^ 2 * (X 2)
    + 27 * (X 0) * (X 1) * (X 2) ^ 2
    - 3 * (X 1) * (X 2) ^ 3
    + 3 * (X 0) * (X 1) * (X 2)
    + 9 * (X 0) * (X 2) ^ 2
    - (X 2) ^ 3
    + 3 * (X 0)

/-- Dehomogenization of `Invariants.H_G_z` at `Z = 1`, with parameter `z` as `X 2`.
Uses the closed form of the Hessian covariant `H` of [CLOP Example 2.1] on the pencil of
[CLOP §4.1], with `C z` replaced by `X 2`. -/
public noncomputable def H_G_z_aff : MvPolynomial (Fin 3) ℚ :=
  36 * (X 2) ^ 2 * ((X 0) ^ 2 * (X 1)) + 12 * (X 2) ^ 2 * ((X 0) ^ 2)
    - 12 * (X 2) ^ 2 * ((X 0) * (X 1) ^ 2) + 36 * (X 2) * ((X 0) * (X 1) ^ 2)
    - 108 * (X 2) ^ 2 * ((X 0) * (X 1)) - 12 * (X 2) * ((X 0) * (X 1))
    - 36 * (X 2) ^ 2 * (X 0) - 12 * (X 0)
    + 12 * (X 2) ^ 3 * (X 1) + 4 * (X 2) ^ 3

/-- Sage's affine Hessian is `-1/4` times the Hessian covariant `H` of [CLOP Example 2.1]
on `Z = 1`:
`hessAff = − H_G_z_aff / 4`. -/
public theorem hessAff_eq_neg_quarter_H :
    (4 : MvPolynomial (Fin 3) ℚ) * hessAff = -H_G_z_aff := by
  unfold hessAff H_G_z_aff
  ring

/-! ## Tangent residual package

The residual map on the affine chart is the rational map
`P ↦ (residualQx / residualA3, residualQy / residualA3)`.
The three identities say:

* the direction is the Euclidean dual of the gradient (hence tangent);
* `Q` lies on that tangent line;
* `g(Q) · residualA3³ = g(P) · residualA3³` as polynomials, so on `{g = 0}` one has
  `g(Q) = 0` wherever the residual is defined (`residualA3 ≠ 0`).

Together these are the defining properties of the tangent-residual map of Route B. -/

public theorem tangent_residual_package :
    (gAff_pderivX * tangentDx + gAff_pderivY * tangentDy = 0)
    ∧ (gAff_pderivX * (residualQx - (X 0) * residualA3)
        + gAff_pderivY * (residualQy - (X 1) * residualA3) = 0)
    ∧ (gAffCleared residualQx residualQy residualA3 = gAff * residualA3 ^ 3) :=
  ⟨residual_direction_is_tangent, residual_on_tangent_line, residual_on_curve_identity⟩

/-! ## Fisher–Sage covariants and staged `Y`-reduction

Integer scalings on the affine chart: `hessAff = 27 H_sage`, `thetaAff = 27² Θ`,
`jAff = 27³ J` (Sage/Fisher). The cleared Weierstrass identity is
`jAff² − 4 thetaAff³ − 4 A · thetaAff · hessAff⁴ − Bnum · hessAff⁶ ≡ 0 (mod gAff)`.

`gAff` has `Y`-degree 3 with leading coefficient `z`. Every class has a unique
representative of `Y`-degree ≤ 2. Each proved lemma is a separate measured-size
`ring` goal (term counts from sympy).
-/

public noncomputable def redH2 : MvPolynomial (Fin 3) ℚ :=
  81 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 54 * (X 0) ^ 6 * (X 2) ^ 3
    + 9 * (X 0) ^ 5 * (X 1) * (X 2) ^ 3
    + 54 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 450 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 54 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 162 * (X 0) ^ 6 * (X 2) ^ 2
    - 54 * (X 0) ^ 5 * (X 1) * (X 2) ^ 2
    + 153 * (X 0) ^ 5 * (X 2) ^ 3
    + 45 * (X 0) ^ 4 * (X 2) ^ 4
    - 162 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 333 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 630 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 4
    + 36 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 150 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + 9 * (X 1) ^ 2 * (X 2) ^ 6
    + 81 * (X 0) ^ 5 * (X 1) * (X 2)
    - 414 * (X 0) ^ 5 * (X 2) ^ 2
    - 108 * (X 0) ^ 4 * (X 2) ^ 3
    + 90 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 261 * (X 0) ^ 3 * (X 2) ^ 4
    + 405 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 3
    + 495 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 24 * (X 0) ^ 2 * (X 2) ^ 5
    - 54 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 108 * (X 0) * (X 1) * (X 2) ^ 5
    + 6 * (X 1) * (X 2) ^ 6
    - 135 * (X 0) ^ 5 * (X 2)
    - 297 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 576 * (X 0) ^ 3 * (X 2) ^ 3
    + 216 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 2
    - 153 * (X 0) ^ 2 * (X 1) * (X 2) ^ 3
    + 180 * (X 0) ^ 2 * (X 2) ^ 4
    + 12 * (X 0) * (X 1) * (X 2) ^ 4
    - 36 * (X 0) * (X 2) ^ 5
    + (X 2) ^ 6
    + 117 * (X 0) ^ 3 * (X 2) ^ 2
    - 135 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2)
    + 657 * (X 0) ^ 2 * (X 1) * (X 2) ^ 2
    - 414 * (X 0) ^ 2 * (X 2) ^ 3
    - 72 * (X 0) * (X 1) * (X 2) ^ 3
    + 54 * (X 0) * (X 2) ^ 4
    + 153 * (X 0) ^ 2 * (X 1) * (X 2)
    - 81 * (X 0) ^ 2 * (X 2) ^ 2
    - 6 * (X 0) * (X 2) ^ 3
    + 9 * (X 0) ^ 2

public noncomputable def quotH2 : MvPolynomial (Fin 3) ℚ :=
  -54 * (X 0) ^ 3 * (X 2) ^ 3
    + 9 * (X 0) ^ 2 * (X 1) * (X 2) ^ 3
    + 162 * (X 0) ^ 3 * (X 2) ^ 2
    - 54 * (X 0) ^ 2 * (X 1) * (X 2) ^ 2
    + 153 * (X 0) ^ 2 * (X 2) ^ 3
    - 18 * (X 0) * (X 2) ^ 4
    + 81 * (X 0) ^ 2 * (X 1) * (X 2)
    - 414 * (X 0) ^ 2 * (X 2) ^ 2
    + 54 * (X 0) * (X 2) ^ 3
    - 135 * (X 0) ^ 2 * (X 2)

public noncomputable def thetaAff : MvPolynomial (Fin 3) ℚ :=
  -108 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 6
    + 45 * (X 0) ^ 2 * (X 1) ^ 4 * (X 2) ^ 6
    - 6 * (X 0) * (X 1) ^ 5 * (X 2) ^ 6
    + (X 1) ^ 6 * (X 2) ^ 6
    + 27 * (X 0) ^ 6 * (X 2) ^ 5
    - 18 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 15 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    + 621 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 5
    - 108 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 135 * (X 0) ^ 2 * (X 1) ^ 4 * (X 2) ^ 5
    + 60 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 6
    + 36 * (X 0) * (X 1) ^ 5 * (X 2) ^ 5
    - 135 * (X 0) * (X 1) ^ 4 * (X 2) ^ 6
    + 108 * (X 0) * (X 1) ^ 3 * (X 2) ^ 7
    - 9 * (X 1) ^ 6 * (X 2) ^ 5
    + 27 * (X 1) ^ 5 * (X 2) ^ 6
    - 21 * (X 1) ^ 4 * (X 2) ^ 7
    + 54 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    - 231 * (X 0) ^ 5 * (X 2) ^ 5
    - 90 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 135 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 27 * (X 0) ^ 4 * (X 2) ^ 6
    + 486 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 4
    + 621 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 60 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 180 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 5
    + 30 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 54 * (X 0) * (X 1) ^ 5 * (X 2) ^ 4
    + 390 * (X 0) * (X 1) ^ 4 * (X 2) ^ 5
    - 801 * (X 0) * (X 1) ^ 3 * (X 2) ^ 6
    + 108 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 27 * (X 1) ^ 6 * (X 2) ^ 4
    - 159 * (X 1) ^ 5 * (X 2) ^ 5
    + 315 * (X 1) ^ 4 * (X 2) ^ 6
    - 128 * (X 1) ^ 3 * (X 2) ^ 7
    - 63 * (X 0) ^ 5 * (X 2) ^ 4
    + 135 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    - 390 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 666 * (X 0) ^ 4 * (X 2) ^ 5
    - 27 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 3
    + 486 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 72 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 162 * (X 0) ^ 3 * (X 2) ^ 6
    - 90 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 90 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    + 9 * (X 0) ^ 2 * (X 2) ^ 7
    + 45 * (X 0) * (X 1) ^ 4 * (X 2) ^ 4
    + 54 * (X 0) * (X 1) ^ 3 * (X 2) ^ 5
    - 741 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 30 * (X 0) * (X 1) * (X 2) ^ 7
    - 27 * (X 1) ^ 6 * (X 2) ^ 3
    + 225 * (X 1) ^ 5 * (X 2) ^ 4
    - 729 * (X 1) ^ 4 * (X 2) ^ 5
    + 939 * (X 1) ^ 3 * (X 2) ^ 6
    - 113 * (X 1) ^ 2 * (X 2) ^ 7
    - 45 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    + 351 * (X 0) ^ 4 * (X 2) ^ 4
    + 108 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 2
    - 27 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 621 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 651 * (X 0) ^ 3 * (X 2) ^ 5
    - 240 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 237 * (X 0) ^ 2 * (X 2) ^ 6
    - 33 * (X 0) * (X 1) ^ 3 * (X 2) ^ 4
    - 36 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 252 * (X 0) * (X 1) * (X 2) ^ 6
    - 23 * (X 0) * (X 2) ^ 7
    + 27 * (X 1) ^ 5 * (X 2) ^ 3
    - 75 * (X 1) ^ 4 * (X 2) ^ 4
    - 225 * (X 1) ^ 3 * (X 2) ^ 5
    + 756 * (X 1) ^ 2 * (X 2) ^ 6
    - 33 * (X 1) * (X 2) ^ 7
    + (X 2) ^ 8
    - 12 * (X 0) ^ 4 * (X 2) ^ 3
    + 108 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    + 486 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 486 * (X 0) ^ 3 * (X 2) ^ 4
    - 90 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 72 * (X 0) ^ 2 * (X 2) ^ 5
    + 72 * (X 0) * (X 1) ^ 3 * (X 2) ^ 3
    - 273 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 69 * (X 0) * (X 1) * (X 2) ^ 5
    - 39 * (X 0) * (X 2) ^ 6
    - 27 * (X 1) ^ 4 * (X 2) ^ 3
    + 27 * (X 1) ^ 3 * (X 2) ^ 4
    + 90 * (X 1) ^ 2 * (X 2) ^ 5
    + 229 * (X 1) * (X 2) ^ 6
    - 3 * (X 2) ^ 7
    + 63 * (X 0) ^ 4 * (X 2) ^ 2
    - 27 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 27 * (X 0) ^ 3 * (X 2) ^ 3
    + 6 * (X 0) ^ 2 * (X 2) ^ 4
    - 18 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    - 126 * (X 0) * (X 1) * (X 2) ^ 4
    + 27 * (X 0) * (X 2) ^ 5
    + 27 * (X 1) ^ 4 * (X 2) ^ 2
    - 155 * (X 1) ^ 3 * (X 2) ^ 3
    + 270 * (X 1) ^ 2 * (X 2) ^ 4
    + 30 * (X 1) * (X 2) ^ 5
    + 24 * (X 2) ^ 6
    + 108 * (X 0) ^ 3 * (X 1) * (X 2)
    - 108 * (X 0) ^ 3 * (X 2) ^ 2
    - 9 * (X 0) ^ 2 * (X 2) ^ 3
    - 3 * (X 0) * (X 1) * (X 2) ^ 3
    - 21 * (X 0) * (X 2) ^ 4
    - 18 * (X 1) ^ 3 * (X 2) ^ 2
    + 162 * (X 1) * (X 2) ^ 4
    - 2 * (X 2) ^ 5
    - 18 * (X 0) * (X 1) * (X 2) ^ 2
    + 9 * (X 0) * (X 2) ^ 3
    + 6 * (X 1) ^ 2 * (X 2) ^ 2
    + 18 * (X 1) * (X 2) ^ 3
    + 29 * (X 2) ^ 4
    - 3 * (X 0) * (X 2) ^ 2
    - 9 * (X 1) ^ 2 * (X 2)
    + 27 * (X 1) * (X 2) ^ 2
    + 3 * (X 1) * (X 2)
    + 9 * (X 2) ^ 2
    + 1

public noncomputable def quotTheta : MvPolynomial (Fin 3) ℚ :=
  -108 * (X 0) ^ 3 * (X 2) ^ 5
    + 45 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 6 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + (X 1) ^ 3 * (X 2) ^ 5
    + 622 * (X 0) ^ 3 * (X 2) ^ 4
    - 135 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 15 * (X 0) ^ 2 * (X 2) ^ 5
    + 36 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 129 * (X 0) * (X 1) * (X 2) ^ 5
    + 108 * (X 0) * (X 2) ^ 6
    - 9 * (X 1) ^ 3 * (X 2) ^ 4
    + 26 * (X 1) ^ 2 * (X 2) ^ 5
    - 21 * (X 1) * (X 2) ^ 6
    + 477 * (X 0) ^ 3 * (X 2) ^ 3
    - 45 * (X 0) ^ 2 * (X 2) ^ 4
    - 54 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 354 * (X 0) * (X 1) * (X 2) ^ 4
    - 673 * (X 0) * (X 2) ^ 5
    + 27 * (X 1) ^ 3 * (X 2) ^ 3
    - 150 * (X 1) ^ 2 * (X 2) ^ 4
    + 289 * (X 1) * (X 2) ^ 5
    - 107 * (X 2) ^ 6
    + 99 * (X 0) * (X 1) * (X 2) ^ 3
    - 285 * (X 0) * (X 2) ^ 4
    - 27 * (X 1) ^ 3 * (X 2) ^ 2
    + 198 * (X 1) ^ 2 * (X 2) ^ 3
    - 580 * (X 1) * (X 2) ^ 4
    + 651 * (X 2) ^ 5
    + 81 * (X 0) ^ 3 * (X 2)
    - 195 * (X 0) * (X 2) ^ 3
    + 54 * (X 1) ^ 2 * (X 2) ^ 2
    - 264 * (X 1) * (X 2) ^ 3
    + 320 * (X 2) ^ 4
    + 153 * (X 0) * (X 2) ^ 2
    - 108 * (X 1) * (X 2) ^ 2
    + 468 * (X 2) ^ 3
    + 54 * (X 1) * (X 2)
    - 272 * (X 2) ^ 2
    - 126 * (X 2)

public noncomputable def redTheta : MvPolynomial (Fin 3) ℚ :=
  -81 * (X 0) ^ 6 * (X 2) ^ 5
    + 27 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 9 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    + 622 * (X 0) ^ 6 * (X 2) ^ 4
    - 81 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    - 216 * (X 0) ^ 5 * (X 2) ^ 5
    - 54 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 6 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 243 * (X 0) ^ 4 * (X 2) ^ 6
    + 25 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 126 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 21 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 477 * (X 0) ^ 6 * (X 2) ^ 3
    - 108 * (X 0) ^ 5 * (X 2) ^ 4
    + 81 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    - 36 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 629 * (X 0) ^ 4 * (X 2) ^ 5
    - 141 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 604 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 392 * (X 0) ^ 3 * (X 2) ^ 6
    - 126 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 264 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 99 * (X 0) ^ 2 * (X 2) ^ 7
    - 100 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 51 * (X 0) * (X 1) * (X 2) ^ 7
    - 6 * (X 1) ^ 2 * (X 2) ^ 7
    + 54 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 411 * (X 0) ^ 4 * (X 2) ^ 4
    + 171 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 581 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 667 * (X 0) ^ 3 * (X 2) ^ 5
    + 189 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 4
    - 744 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 925 * (X 0) ^ 2 * (X 2) ^ 6
    + 564 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 778 * (X 0) * (X 1) * (X 2) ^ 6
    + 192 * (X 0) * (X 2) ^ 7
    + 152 * (X 1) ^ 2 * (X 2) ^ 6
    - 54 * (X 1) * (X 2) ^ 7
    + (X 2) ^ 8
    + 81 * (X 0) ^ 6 * (X 2)
    - 207 * (X 0) ^ 4 * (X 2) ^ 3
    + 81 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    - 255 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 311 * (X 0) ^ 3 * (X 2) ^ 4
    - 144 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 312 * (X 0) ^ 2 * (X 2) ^ 5
    - 684 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 1676 * (X 0) * (X 1) * (X 2) ^ 5
    - 1363 * (X 0) * (X 2) ^ 6
    - 669 * (X 1) ^ 2 * (X 2) ^ 5
    + 625 * (X 1) * (X 2) ^ 6
    - 110 * (X 2) ^ 7
    + 135 * (X 0) ^ 4 * (X 2) ^ 2
    - 135 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 495 * (X 0) ^ 3 * (X 2) ^ 3
    + 201 * (X 0) ^ 2 * (X 2) ^ 4
    - 324 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 522 * (X 0) * (X 1) * (X 2) ^ 4
    - 578 * (X 0) * (X 2) ^ 5
    + 580 * (X 1) ^ 2 * (X 2) ^ 4
    - 1201 * (X 1) * (X 2) ^ 5
    + 675 * (X 2) ^ 6
    + 81 * (X 0) ^ 3 * (X 1) * (X 2)
    - 299 * (X 0) ^ 3 * (X 2) ^ 2
    - 162 * (X 0) ^ 2 * (X 2) ^ 3
    + 300 * (X 0) * (X 1) * (X 2) ^ 3
    - 684 * (X 0) * (X 2) ^ 4
    + 590 * (X 1) ^ 2 * (X 2) ^ 3
    - 422 * (X 1) * (X 2) ^ 4
    + 318 * (X 2) ^ 5
    - 126 * (X 0) ^ 3 * (X 2)
    - 225 * (X 0) * (X 1) * (X 2) ^ 2
    + 434 * (X 0) * (X 2) ^ 3
    + 240 * (X 1) ^ 2 * (X 2) ^ 2
    - 558 * (X 1) * (X 2) ^ 3
    + 497 * (X 2) ^ 4
    + 123 * (X 0) * (X 2) ^ 2
    - 63 * (X 1) ^ 2 * (X 2)
    + 353 * (X 1) * (X 2) ^ 2
    - 272 * (X 2) ^ 3
    + 129 * (X 1) * (X 2)
    - 117 * (X 2) ^ 2
    + 1

public noncomputable def redH3 : MvPolynomial (Fin 3) ℚ :=
  -729 * (X 0) ^ 9 * (X 2) ^ 5
    + 729 * (X 0) ^ 8 * (X 1) * (X 2) ^ 5
    - 243 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 5
    + 27 * (X 0) ^ 9 * (X 2) ^ 4
    - 2187 * (X 0) ^ 8 * (X 1) * (X 2) ^ 4
    + 6318 * (X 0) ^ 8 * (X 2) ^ 5
    + 1458 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 4
    - 4212 * (X 0) ^ 7 * (X 1) * (X 2) ^ 5
    + 675 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 5
    - 486 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    + 486 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    - 243 * (X 0) ^ 9 * (X 2) ^ 3
    + 1458 * (X 0) ^ 8 * (X 2) ^ 4
    - 2187 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 3
    + 11664 * (X 0) ^ 7 * (X 1) * (X 2) ^ 4
    - 18441 * (X 0) ^ 7 * (X 2) ^ 5
    - 3807 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 4
    + 7560 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    - 2862 * (X 0) ^ 6 * (X 2) ^ 6
    - 2916 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 5
    + 5724 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    + 486 * (X 0) ^ 5 * (X 2) ^ 7
    - 2700 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 648 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 297 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 729 * (X 0) ^ 9 * (X 2) ^ 2
    + 2916 * (X 0) ^ 7 * (X 1) * (X 2) ^ 3
    - 6723 * (X 0) ^ 7 * (X 2) ^ 4
    + 4617 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 3
    - 15687 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    + 17523 * (X 0) ^ 6 * (X 2) ^ 5
    + 4374 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 4
    - 16200 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 18846 * (X 0) ^ 5 * (X 2) ^ 6
    + 15228 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 14931 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 4266 * (X 0) ^ 4 * (X 2) ^ 7
    + 1350 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 3348 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 216 * (X 0) ^ 3 * (X 2) ^ 8
    - 675 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    - 162 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 36 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 729 * (X 0) ^ 9 * (X 2)
    - 6075 * (X 0) ^ 7 * (X 2) ^ 3
    + 2187 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 2
    - 6885 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    + 8397 * (X 0) ^ 6 * (X 2) ^ 4
    - 2916 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    + 6021 * (X 0) ^ 5 * (X 2) ^ 5
    - 18468 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 45252 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 37935 * (X 0) ^ 4 * (X 2) ^ 6
    - 13932 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 3159 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 10503 * (X 0) ^ 3 * (X 2) ^ 7
    + 3807 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 3105 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 954 * (X 0) ^ 2 * (X 2) ^ 8
    - 216 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 324 * (X 0) * (X 1) * (X 2) ^ 8
    + 27 * (X 0) * (X 2) ^ 9
    - 9 * (X 1) * (X 2) ^ 9
    + 5103 * (X 0) ^ 7 * (X 2) ^ 2
    - 3645 * (X 0) ^ 6 * (X 1) * (X 2) ^ 2
    + 13365 * (X 0) ^ 6 * (X 2) ^ 3
    + 3888 * (X 0) ^ 5 * (X 2) ^ 4
    - 8748 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    + 14094 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 15606 * (X 0) ^ 4 * (X 2) ^ 5
    + 15660 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 34533 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 22086 * (X 0) ^ 3 * (X 2) ^ 6
    - 4617 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 9855 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 6534 * (X 0) ^ 2 * (X 2) ^ 7
    + 324 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 936 * (X 0) * (X 1) * (X 2) ^ 7
    + 729 * (X 0) * (X 2) ^ 8
    + 27 * (X 1) * (X 2) ^ 8
    - 28 * (X 2) ^ 9
    + 2187 * (X 0) ^ 6 * (X 1) * (X 2)
    - 8073 * (X 0) ^ 6 * (X 2) ^ 2
    - 3159 * (X 0) ^ 5 * (X 2) ^ 3
    + 8100 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 18468 * (X 0) ^ 4 * (X 2) ^ 4
    + 15930 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 11394 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 10233 * (X 0) ^ 3 * (X 2) ^ 5
    - 2187 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 4
    + 2403 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 2403 * (X 0) ^ 2 * (X 2) ^ 6
    - 108 * (X 0) * (X 1) * (X 2) ^ 6
    + 162 * (X 0) * (X 2) ^ 7
    - 3402 * (X 0) ^ 6 * (X 2)
    - 6075 * (X 0) ^ 4 * (X 1) * (X 2) ^ 2
    + 11718 * (X 0) ^ 4 * (X 2) ^ 3
    + 6480 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    - 15066 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 12150 * (X 0) ^ 3 * (X 2) ^ 4
    + 1485 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    - 1701 * (X 0) ^ 2 * (X 2) ^ 5
    + 9 * (X 0) * (X 2) ^ 6
    + 3321 * (X 0) ^ 4 * (X 2) ^ 2
    - 1701 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2)
    + 9531 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    - 7344 * (X 0) ^ 3 * (X 2) ^ 3
    - 1296 * (X 0) ^ 2 * (X 1) * (X 2) ^ 3
    + 1215 * (X 0) ^ 2 * (X 2) ^ 4
    + 3483 * (X 0) ^ 3 * (X 1) * (X 2)
    - 3159 * (X 0) ^ 3 * (X 2) ^ 2
    - 27 * (X 0) ^ 2 * (X 2) ^ 3
    + 27 * (X 0) ^ 3

public noncomputable def quotH3 : MvPolynomial (Fin 3) ℚ :=
  -729 * (X 0) ^ 6 * (X 2) ^ 5
    + 243 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 27 * (X 0) ^ 6 * (X 2) ^ 4
    - 729 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    + 6156 * (X 0) ^ 5 * (X 2) ^ 5
    - 1350 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 729 * (X 0) ^ 4 * (X 2) ^ 6
    + 162 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 243 * (X 0) ^ 6 * (X 2) ^ 3
    + 1944 * (X 0) ^ 5 * (X 2) ^ 4
    + 3564 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 17469 * (X 0) ^ 4 * (X 2) ^ 5
    + 1404 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 4104 * (X 0) ^ 3 * (X 2) ^ 6
    - 450 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 243 * (X 0) ^ 2 * (X 2) ^ 7
    + 27 * (X 0) * (X 1) * (X 2) ^ 7
    + 729 * (X 0) ^ 6 * (X 2) ^ 2
    + 1458 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 9666 * (X 0) ^ 4 * (X 2) ^ 4
    - 4455 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 17901 * (X 0) ^ 3 * (X 2) ^ 5
    + 1188 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 5814 * (X 0) ^ 2 * (X 2) ^ 6
    - 81 * (X 0) * (X 1) * (X 2) ^ 6
    + 684 * (X 0) * (X 2) ^ 7
    - 27 * (X 2) ^ 8
    - 729 * (X 0) ^ 6 * (X 2)
    - 5589 * (X 0) ^ 4 * (X 2) ^ 3
    - 2997 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 12366 * (X 0) ^ 3 * (X 2) ^ 4
    + 486 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    - 3303 * (X 0) ^ 2 * (X 2) ^ 5
    + 216 * (X 0) * (X 2) ^ 6
    + 3888 * (X 0) ^ 4 * (X 2) ^ 2
    - 2349 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 13392 * (X 0) ^ 3 * (X 2) ^ 3
    - 1620 * (X 0) ^ 2 * (X 2) ^ 4
    + 1215 * (X 0) ^ 3 * (X 1) * (X 2)
    - 6102 * (X 0) ^ 3 * (X 2) ^ 2
    + 1053 * (X 0) ^ 2 * (X 2) ^ 3
    - 2997 * (X 0) ^ 3 * (X 2)


/-- `hessAff² ≡ redH2 (mod gAff)`. Offline sizes: product≈41, quot=10, red=46. -/
public theorem hessAff_sq_mod :
    hessAff ^ 2 = quotH2 * gAff + redH2 := by
  unfold hessAff quotH2 gAff redH2
  ring

/-- `thetaAff ≡ redTheta (mod gAff)`. Offline sizes: θ=119, quot=39, red=84. -/
public theorem thetaAff_mod :
    thetaAff = quotTheta * gAff + redTheta := by
  unfold thetaAff quotTheta gAff redTheta
  ring

/-- `redH2 · hessAff ≡ redH3 (mod gAff)`. Offline sizes: product≈149, quot=42, red=113. -/
public theorem redH3_mod :
    redH2 * hessAff = quotH3 * gAff + redH3 := by
  unfold redH2 hessAff quotH3 gAff redH3
  ring

/-! ### `jAff` reduction (chunked monom batches)

Integer form `jAff = 19683 · J_sage|_{Z=1}` (368 terms). Offline: `jAff = gAff · quotJ + redJ`
with `|quotJ|=176`, `|redJ|=205`. A single `ring` on the full identity exceeds 30 min.

We partition the `Y`-degree ≥ 3 summands into monom-batches (size depends on degree:
deg 9–8 → 1 monom, deg 7–6 → 2, deg 5 → 3, deg 4 → 4, deg 3 → 5), each verified by
`ring` in seconds. Degrees ≤ 2 need no reduction. The global identity is the sum of the
chunk identities.
-/

public noncomputable def jAff_c0 : MvPolynomial (Fin 3) ℚ :=
  -25 * (X 1) ^ 9 * (X 2) ^ 9

public noncomputable def quotJ_c0 : MvPolynomial (Fin 3) ℚ :=
  -25 * (X 1) ^ 6 * (X 2) ^ 8
    - 25 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 7
    + 25 * (X 1) ^ 5 * (X 2) ^ 8
    - 25 * (X 0) ^ 6 * (X 2) ^ 6
    + 50 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 25 * (X 0) * (X 1) ^ 3 * (X 2) ^ 8
    - 25 * (X 1) ^ 4 * (X 2) ^ 8
    + 50 * (X 0) ^ 4 * (X 2) ^ 7
    - 75 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 50 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 25 * (X 1) ^ 4 * (X 2) ^ 7
    + 50 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 50 * (X 0) ^ 3 * (X 2) ^ 7
    - 25 * (X 0) ^ 2 * (X 2) ^ 8
    + 75 * (X 0) * (X 1) * (X 2) ^ 8
    - 50 * (X 1) ^ 3 * (X 2) ^ 7
    + 25 * (X 1) ^ 2 * (X 2) ^ 8
    - 150 * (X 0) ^ 3 * (X 2) ^ 6
    - 50 * (X 0) * (X 1) * (X 2) ^ 7
    - 50 * (X 0) * (X 2) ^ 8
    + 75 * (X 1) ^ 2 * (X 2) ^ 7
    - 50 * (X 1) * (X 2) ^ 8
    + 150 * (X 0) * (X 2) ^ 7
    - 25 * (X 1) ^ 2 * (X 2) ^ 6
    - 50 * (X 1) * (X 2) ^ 7
    + 50 * (X 2) ^ 8
    + 75 * (X 1) * (X 2) ^ 6
    - 25 * (X 2) ^ 7
    - 150 * (X 2) ^ 6
    + 25 * (X 2) ^ 5

public noncomputable def redJ_c0 : MvPolynomial (Fin 3) ℚ :=
  -25 * (X 0) ^ 9 * (X 2) ^ 6
    + 75 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 7
    + 75 * (X 0) ^ 7 * (X 2) ^ 7
    - 75 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    - 150 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    + 75 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    + 25 * (X 0) ^ 6 * (X 2) ^ 7
    - 75 * (X 0) ^ 5 * (X 2) ^ 8
    + 150 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 25 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 75 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    - 150 * (X 0) ^ 6 * (X 2) ^ 6
    - 150 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 50 * (X 0) ^ 4 * (X 2) ^ 8
    + 300 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 125 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 25 * (X 0) ^ 3 * (X 2) ^ 9
    - 75 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 25 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    + 300 * (X 0) ^ 4 * (X 2) ^ 7
    - 75 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 50 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 100 * (X 0) ^ 3 * (X 2) ^ 8
    + 75 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 25 * (X 0) ^ 2 * (X 2) ^ 9
    - 300 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 125 * (X 0) * (X 1) * (X 2) ^ 9
    - 25 * (X 1) ^ 2 * (X 2) ^ 9
    + 225 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 175 * (X 0) ^ 3 * (X 2) ^ 7
    - 150 * (X 0) ^ 2 * (X 2) ^ 8
    + 75 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 50 * (X 0) * (X 1) * (X 2) ^ 8
    - 100 * (X 0) * (X 2) ^ 9
    + 150 * (X 1) ^ 2 * (X 2) ^ 8
    - 50 * (X 1) * (X 2) ^ 9
    - 150 * (X 0) ^ 3 * (X 2) ^ 6
    - 225 * (X 0) * (X 1) * (X 2) ^ 7
    + 175 * (X 0) * (X 2) ^ 8
    + 175 * (X 1) ^ 2 * (X 2) ^ 7
    - 100 * (X 1) * (X 2) ^ 8
    + 50 * (X 2) ^ 9
    + 25 * (X 0) ^ 3 * (X 2) ^ 5
    + 150 * (X 0) * (X 2) ^ 7
    - 100 * (X 1) ^ 2 * (X 2) ^ 6
    + 100 * (X 1) * (X 2) ^ 7
    - 25 * (X 2) ^ 8
    - 25 * (X 0) * (X 2) ^ 6
    + 150 * (X 1) * (X 2) ^ 6
    - 150 * (X 2) ^ 7
    - 25 * (X 1) * (X 2) ^ 5
    + 25 * (X 2) ^ 6

public noncomputable def jAff_c1 : MvPolynomial (Fin 3) ℚ :=
  216 * (X 1) ^ 9 * (X 2) ^ 8

public noncomputable def quotJ_c1 : MvPolynomial (Fin 3) ℚ :=
  216 * (X 1) ^ 6 * (X 2) ^ 7
    + 216 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 6
    - 216 * (X 1) ^ 5 * (X 2) ^ 7
    + 216 * (X 0) ^ 6 * (X 2) ^ 5
    - 432 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 216 * (X 0) * (X 1) ^ 3 * (X 2) ^ 7
    + 216 * (X 1) ^ 4 * (X 2) ^ 7
    - 432 * (X 0) ^ 4 * (X 2) ^ 6
    + 648 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 432 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 216 * (X 1) ^ 4 * (X 2) ^ 6
    - 432 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 432 * (X 0) ^ 3 * (X 2) ^ 6
    + 216 * (X 0) ^ 2 * (X 2) ^ 7
    - 648 * (X 0) * (X 1) * (X 2) ^ 7
    + 432 * (X 1) ^ 3 * (X 2) ^ 6
    - 216 * (X 1) ^ 2 * (X 2) ^ 7
    + 1296 * (X 0) ^ 3 * (X 2) ^ 5
    + 432 * (X 0) * (X 1) * (X 2) ^ 6
    + 432 * (X 0) * (X 2) ^ 7
    - 648 * (X 1) ^ 2 * (X 2) ^ 6
    + 432 * (X 1) * (X 2) ^ 7
    - 1296 * (X 0) * (X 2) ^ 6
    + 216 * (X 1) ^ 2 * (X 2) ^ 5
    + 432 * (X 1) * (X 2) ^ 6
    - 432 * (X 2) ^ 7
    - 648 * (X 1) * (X 2) ^ 5
    + 216 * (X 2) ^ 6
    + 1296 * (X 2) ^ 5
    - 216 * (X 2) ^ 4

public noncomputable def redJ_c1 : MvPolynomial (Fin 3) ℚ :=
  216 * (X 0) ^ 9 * (X 2) ^ 5
    - 648 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 6
    - 648 * (X 0) ^ 7 * (X 2) ^ 6
    + 648 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    + 1296 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 648 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    - 216 * (X 0) ^ 6 * (X 2) ^ 6
    + 648 * (X 0) ^ 5 * (X 2) ^ 7
    - 1296 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 216 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 648 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    + 1296 * (X 0) ^ 6 * (X 2) ^ 5
    + 1296 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 432 * (X 0) ^ 4 * (X 2) ^ 7
    - 2592 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 1080 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 216 * (X 0) ^ 3 * (X 2) ^ 8
    + 648 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 216 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 2592 * (X 0) ^ 4 * (X 2) ^ 6
    + 648 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 432 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 864 * (X 0) ^ 3 * (X 2) ^ 7
    - 648 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 216 * (X 0) ^ 2 * (X 2) ^ 8
    + 2592 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 1080 * (X 0) * (X 1) * (X 2) ^ 8
    + 216 * (X 1) ^ 2 * (X 2) ^ 8
    - 1944 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 1512 * (X 0) ^ 3 * (X 2) ^ 6
    + 1296 * (X 0) ^ 2 * (X 2) ^ 7
    - 648 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 432 * (X 0) * (X 1) * (X 2) ^ 7
    + 864 * (X 0) * (X 2) ^ 8
    - 1296 * (X 1) ^ 2 * (X 2) ^ 7
    + 432 * (X 1) * (X 2) ^ 8
    + 1296 * (X 0) ^ 3 * (X 2) ^ 5
    + 1944 * (X 0) * (X 1) * (X 2) ^ 6
    - 1512 * (X 0) * (X 2) ^ 7
    - 1512 * (X 1) ^ 2 * (X 2) ^ 6
    + 864 * (X 1) * (X 2) ^ 7
    - 432 * (X 2) ^ 8
    - 216 * (X 0) ^ 3 * (X 2) ^ 4
    - 1296 * (X 0) * (X 2) ^ 6
    + 864 * (X 1) ^ 2 * (X 2) ^ 5
    - 864 * (X 1) * (X 2) ^ 6
    + 216 * (X 2) ^ 7
    + 216 * (X 0) * (X 2) ^ 5
    - 1296 * (X 1) * (X 2) ^ 5
    + 1296 * (X 2) ^ 6
    + 216 * (X 1) * (X 2) ^ 4
    - 216 * (X 2) ^ 5

public noncomputable def jAff_c2 : MvPolynomial (Fin 3) ℚ :=
  -594 * (X 1) ^ 9 * (X 2) ^ 7

public noncomputable def quotJ_c2 : MvPolynomial (Fin 3) ℚ :=
  -594 * (X 1) ^ 6 * (X 2) ^ 6
    - 594 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 5
    + 594 * (X 1) ^ 5 * (X 2) ^ 6
    - 594 * (X 0) ^ 6 * (X 2) ^ 4
    + 1188 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 594 * (X 0) * (X 1) ^ 3 * (X 2) ^ 6
    - 594 * (X 1) ^ 4 * (X 2) ^ 6
    + 1188 * (X 0) ^ 4 * (X 2) ^ 5
    - 1782 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 1188 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 594 * (X 1) ^ 4 * (X 2) ^ 5
    + 1188 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 1188 * (X 0) ^ 3 * (X 2) ^ 5
    - 594 * (X 0) ^ 2 * (X 2) ^ 6
    + 1782 * (X 0) * (X 1) * (X 2) ^ 6
    - 1188 * (X 1) ^ 3 * (X 2) ^ 5
    + 594 * (X 1) ^ 2 * (X 2) ^ 6
    - 3564 * (X 0) ^ 3 * (X 2) ^ 4
    - 1188 * (X 0) * (X 1) * (X 2) ^ 5
    - 1188 * (X 0) * (X 2) ^ 6
    + 1782 * (X 1) ^ 2 * (X 2) ^ 5
    - 1188 * (X 1) * (X 2) ^ 6
    + 3564 * (X 0) * (X 2) ^ 5
    - 594 * (X 1) ^ 2 * (X 2) ^ 4
    - 1188 * (X 1) * (X 2) ^ 5
    + 1188 * (X 2) ^ 6
    + 1782 * (X 1) * (X 2) ^ 4
    - 594 * (X 2) ^ 5
    - 3564 * (X 2) ^ 4
    + 594 * (X 2) ^ 3

public noncomputable def redJ_c2 : MvPolynomial (Fin 3) ℚ :=
  -594 * (X 0) ^ 9 * (X 2) ^ 4
    + 1782 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 5
    + 1782 * (X 0) ^ 7 * (X 2) ^ 5
    - 1782 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    - 3564 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    + 1782 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    + 594 * (X 0) ^ 6 * (X 2) ^ 5
    - 1782 * (X 0) ^ 5 * (X 2) ^ 6
    + 3564 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 594 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 1782 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    - 3564 * (X 0) ^ 6 * (X 2) ^ 4
    - 3564 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 1188 * (X 0) ^ 4 * (X 2) ^ 6
    + 7128 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 2970 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 594 * (X 0) ^ 3 * (X 2) ^ 7
    - 1782 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 594 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 7128 * (X 0) ^ 4 * (X 2) ^ 5
    - 1782 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 1188 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 2376 * (X 0) ^ 3 * (X 2) ^ 6
    + 1782 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    + 594 * (X 0) ^ 2 * (X 2) ^ 7
    - 7128 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 2970 * (X 0) * (X 1) * (X 2) ^ 7
    - 594 * (X 1) ^ 2 * (X 2) ^ 7
    + 5346 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 4158 * (X 0) ^ 3 * (X 2) ^ 5
    - 3564 * (X 0) ^ 2 * (X 2) ^ 6
    + 1782 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + 1188 * (X 0) * (X 1) * (X 2) ^ 6
    - 2376 * (X 0) * (X 2) ^ 7
    + 3564 * (X 1) ^ 2 * (X 2) ^ 6
    - 1188 * (X 1) * (X 2) ^ 7
    - 3564 * (X 0) ^ 3 * (X 2) ^ 4
    - 5346 * (X 0) * (X 1) * (X 2) ^ 5
    + 4158 * (X 0) * (X 2) ^ 6
    + 4158 * (X 1) ^ 2 * (X 2) ^ 5
    - 2376 * (X 1) * (X 2) ^ 6
    + 1188 * (X 2) ^ 7
    + 594 * (X 0) ^ 3 * (X 2) ^ 3
    + 3564 * (X 0) * (X 2) ^ 5
    - 2376 * (X 1) ^ 2 * (X 2) ^ 4
    + 2376 * (X 1) * (X 2) ^ 5
    - 594 * (X 2) ^ 6
    - 594 * (X 0) * (X 2) ^ 4
    + 3564 * (X 1) * (X 2) ^ 4
    - 3564 * (X 2) ^ 5
    - 594 * (X 1) * (X 2) ^ 3
    + 594 * (X 2) ^ 4

public noncomputable def jAff_c3 : MvPolynomial (Fin 3) ℚ :=
  432 * (X 1) ^ 9 * (X 2) ^ 6

public noncomputable def quotJ_c3 : MvPolynomial (Fin 3) ℚ :=
  432 * (X 1) ^ 6 * (X 2) ^ 5
    + 432 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 4
    - 432 * (X 1) ^ 5 * (X 2) ^ 5
    + 432 * (X 0) ^ 6 * (X 2) ^ 3
    - 864 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 432 * (X 0) * (X 1) ^ 3 * (X 2) ^ 5
    + 432 * (X 1) ^ 4 * (X 2) ^ 5
    - 864 * (X 0) ^ 4 * (X 2) ^ 4
    + 1296 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 864 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 432 * (X 1) ^ 4 * (X 2) ^ 4
    - 864 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 864 * (X 0) ^ 3 * (X 2) ^ 4
    + 432 * (X 0) ^ 2 * (X 2) ^ 5
    - 1296 * (X 0) * (X 1) * (X 2) ^ 5
    + 864 * (X 1) ^ 3 * (X 2) ^ 4
    - 432 * (X 1) ^ 2 * (X 2) ^ 5
    + 2592 * (X 0) ^ 3 * (X 2) ^ 3
    + 864 * (X 0) * (X 1) * (X 2) ^ 4
    + 864 * (X 0) * (X 2) ^ 5
    - 1296 * (X 1) ^ 2 * (X 2) ^ 4
    + 864 * (X 1) * (X 2) ^ 5
    - 2592 * (X 0) * (X 2) ^ 4
    + 432 * (X 1) ^ 2 * (X 2) ^ 3
    + 864 * (X 1) * (X 2) ^ 4
    - 864 * (X 2) ^ 5
    - 1296 * (X 1) * (X 2) ^ 3
    + 432 * (X 2) ^ 4
    + 2592 * (X 2) ^ 3
    - 432 * (X 2) ^ 2

public noncomputable def redJ_c3 : MvPolynomial (Fin 3) ℚ :=
  432 * (X 0) ^ 9 * (X 2) ^ 3
    - 1296 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 4
    - 1296 * (X 0) ^ 7 * (X 2) ^ 4
    + 1296 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    + 2592 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 1296 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    - 432 * (X 0) ^ 6 * (X 2) ^ 4
    + 1296 * (X 0) ^ 5 * (X 2) ^ 5
    - 2592 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 432 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 1296 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 2592 * (X 0) ^ 6 * (X 2) ^ 3
    + 2592 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 864 * (X 0) ^ 4 * (X 2) ^ 5
    - 5184 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 2160 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 432 * (X 0) ^ 3 * (X 2) ^ 6
    + 1296 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    + 432 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 5184 * (X 0) ^ 4 * (X 2) ^ 4
    + 1296 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 864 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 1728 * (X 0) ^ 3 * (X 2) ^ 5
    - 1296 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 432 * (X 0) ^ 2 * (X 2) ^ 6
    + 5184 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 2160 * (X 0) * (X 1) * (X 2) ^ 6
    + 432 * (X 1) ^ 2 * (X 2) ^ 6
    - 3888 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 3024 * (X 0) ^ 3 * (X 2) ^ 4
    + 2592 * (X 0) ^ 2 * (X 2) ^ 5
    - 1296 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 864 * (X 0) * (X 1) * (X 2) ^ 5
    + 1728 * (X 0) * (X 2) ^ 6
    - 2592 * (X 1) ^ 2 * (X 2) ^ 5
    + 864 * (X 1) * (X 2) ^ 6
    + 2592 * (X 0) ^ 3 * (X 2) ^ 3
    + 3888 * (X 0) * (X 1) * (X 2) ^ 4
    - 3024 * (X 0) * (X 2) ^ 5
    - 3024 * (X 1) ^ 2 * (X 2) ^ 4
    + 1728 * (X 1) * (X 2) ^ 5
    - 864 * (X 2) ^ 6
    - 432 * (X 0) ^ 3 * (X 2) ^ 2
    - 2592 * (X 0) * (X 2) ^ 4
    + 1728 * (X 1) ^ 2 * (X 2) ^ 3
    - 1728 * (X 1) * (X 2) ^ 4
    + 432 * (X 2) ^ 5
    + 432 * (X 0) * (X 2) ^ 3
    - 2592 * (X 1) * (X 2) ^ 3
    + 2592 * (X 2) ^ 4
    + 432 * (X 1) * (X 2) ^ 2
    - 432 * (X 2) ^ 3

public noncomputable def jAff_c4 : MvPolynomial (Fin 3) ℚ :=
  243 * (X 1) ^ 9 * (X 2) ^ 5

public noncomputable def quotJ_c4 : MvPolynomial (Fin 3) ℚ :=
  243 * (X 1) ^ 6 * (X 2) ^ 4
    + 243 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 3
    - 243 * (X 1) ^ 5 * (X 2) ^ 4
    + 243 * (X 0) ^ 6 * (X 2) ^ 2
    - 486 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 243 * (X 0) * (X 1) ^ 3 * (X 2) ^ 4
    + 243 * (X 1) ^ 4 * (X 2) ^ 4
    - 486 * (X 0) ^ 4 * (X 2) ^ 3
    + 729 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 486 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 243 * (X 1) ^ 4 * (X 2) ^ 3
    - 486 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    - 486 * (X 0) ^ 3 * (X 2) ^ 3
    + 243 * (X 0) ^ 2 * (X 2) ^ 4
    - 729 * (X 0) * (X 1) * (X 2) ^ 4
    + 486 * (X 1) ^ 3 * (X 2) ^ 3
    - 243 * (X 1) ^ 2 * (X 2) ^ 4
    + 1458 * (X 0) ^ 3 * (X 2) ^ 2
    + 486 * (X 0) * (X 1) * (X 2) ^ 3
    + 486 * (X 0) * (X 2) ^ 4
    - 729 * (X 1) ^ 2 * (X 2) ^ 3
    + 486 * (X 1) * (X 2) ^ 4
    - 1458 * (X 0) * (X 2) ^ 3
    + 243 * (X 1) ^ 2 * (X 2) ^ 2
    + 486 * (X 1) * (X 2) ^ 3
    - 486 * (X 2) ^ 4
    - 729 * (X 1) * (X 2) ^ 2
    + 243 * (X 2) ^ 3
    + 1458 * (X 2) ^ 2
    - 243 * (X 2)

public noncomputable def redJ_c4 : MvPolynomial (Fin 3) ℚ :=
  243 * (X 0) ^ 9 * (X 2) ^ 2
    - 729 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 3
    - 729 * (X 0) ^ 7 * (X 2) ^ 3
    + 729 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    + 1458 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 729 * (X 0) ^ 6 * (X 1) * (X 2) ^ 2
    - 243 * (X 0) ^ 6 * (X 2) ^ 3
    + 729 * (X 0) ^ 5 * (X 2) ^ 4
    - 1458 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 243 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 729 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 1458 * (X 0) ^ 6 * (X 2) ^ 2
    + 1458 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    + 486 * (X 0) ^ 4 * (X 2) ^ 4
    - 2916 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 1215 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 243 * (X 0) ^ 3 * (X 2) ^ 5
    + 729 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 243 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 2916 * (X 0) ^ 4 * (X 2) ^ 3
    + 729 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    + 486 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 972 * (X 0) ^ 3 * (X 2) ^ 4
    - 729 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    - 243 * (X 0) ^ 2 * (X 2) ^ 5
    + 2916 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 1215 * (X 0) * (X 1) * (X 2) ^ 5
    + 243 * (X 1) ^ 2 * (X 2) ^ 5
    - 2187 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 1701 * (X 0) ^ 3 * (X 2) ^ 3
    + 1458 * (X 0) ^ 2 * (X 2) ^ 4
    - 729 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    - 486 * (X 0) * (X 1) * (X 2) ^ 4
    + 972 * (X 0) * (X 2) ^ 5
    - 1458 * (X 1) ^ 2 * (X 2) ^ 4
    + 486 * (X 1) * (X 2) ^ 5
    + 1458 * (X 0) ^ 3 * (X 2) ^ 2
    + 2187 * (X 0) * (X 1) * (X 2) ^ 3
    - 1701 * (X 0) * (X 2) ^ 4
    - 1701 * (X 1) ^ 2 * (X 2) ^ 3
    + 972 * (X 1) * (X 2) ^ 4
    - 486 * (X 2) ^ 5
    - 243 * (X 0) ^ 3 * (X 2)
    - 1458 * (X 0) * (X 2) ^ 3
    + 972 * (X 1) ^ 2 * (X 2) ^ 2
    - 972 * (X 1) * (X 2) ^ 3
    + 243 * (X 2) ^ 4
    + 243 * (X 0) * (X 2) ^ 2
    - 1458 * (X 1) * (X 2) ^ 2
    + 1458 * (X 2) ^ 3
    + 243 * (X 1) * (X 2)
    - 243 * (X 2) ^ 2

public noncomputable def jAff_c5 : MvPolynomial (Fin 3) ℚ :=
  225 * (X 0) * (X 1) ^ 8 * (X 2) ^ 9

public noncomputable def quotJ_c5 : MvPolynomial (Fin 3) ℚ :=
  225 * (X 0) * (X 1) ^ 5 * (X 2) ^ 8
    + 225 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 225 * (X 0) * (X 1) ^ 4 * (X 2) ^ 8
    - 450 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 225 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    + 225 * (X 0) * (X 1) ^ 3 * (X 2) ^ 8
    + 675 * (X 0) ^ 4 * (X 2) ^ 7
    + 450 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 225 * (X 0) * (X 1) ^ 3 * (X 2) ^ 7
    - 450 * (X 0) ^ 4 * (X 2) ^ 6
    - 675 * (X 0) ^ 2 * (X 2) ^ 8
    + 450 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 225 * (X 0) * (X 1) * (X 2) ^ 8
    + 450 * (X 0) ^ 2 * (X 2) ^ 7
    - 675 * (X 0) * (X 1) * (X 2) ^ 7
    + 450 * (X 0) * (X 2) ^ 8
    + 225 * (X 0) * (X 1) * (X 2) ^ 6
    + 450 * (X 0) * (X 2) ^ 7
    - 675 * (X 0) * (X 2) ^ 6

public noncomputable def redJ_c5 : MvPolynomial (Fin 3) ℚ :=
  225 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 7
    - 450 * (X 0) ^ 7 * (X 1) * (X 2) ^ 7
    - 450 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 8
    + 675 * (X 0) ^ 7 * (X 2) ^ 7
    + 900 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    - 450 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    + 225 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    - 450 * (X 0) ^ 7 * (X 2) ^ 6
    - 1350 * (X 0) ^ 5 * (X 2) ^ 8
    + 1350 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 675 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 450 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    + 450 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 900 * (X 0) ^ 5 * (X 2) ^ 7
    - 1350 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 1125 * (X 0) ^ 4 * (X 2) ^ 8
    + 675 * (X 0) ^ 3 * (X 2) ^ 9
    - 1350 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    + 675 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 450 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    + 675 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 450 * (X 0) ^ 3 * (X 2) ^ 8
    + 1350 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 1125 * (X 0) ^ 2 * (X 2) ^ 9
    + 225 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 225 * (X 0) * (X 1) * (X 2) ^ 9
    - 675 * (X 0) ^ 4 * (X 2) ^ 6
    - 675 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 1350 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 1125 * (X 0) * (X 1) * (X 2) ^ 8
    + 450 * (X 0) * (X 2) ^ 9
    + 675 * (X 0) ^ 2 * (X 2) ^ 7
    - 225 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 225 * (X 0) * (X 1) * (X 2) ^ 7
    + 450 * (X 0) * (X 2) ^ 8
    + 675 * (X 0) * (X 1) * (X 2) ^ 6
    - 675 * (X 0) * (X 2) ^ 7

public noncomputable def jAff_c6 : MvPolynomial (Fin 3) ℚ :=
  54 * (X 1) ^ 8 * (X 2) ^ 10

public noncomputable def quotJ_c6 : MvPolynomial (Fin 3) ℚ :=
  54 * (X 1) ^ 5 * (X 2) ^ 9
    + 54 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    - 54 * (X 1) ^ 4 * (X 2) ^ 9
    - 108 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 54 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    + 54 * (X 1) ^ 3 * (X 2) ^ 9
    + 162 * (X 0) ^ 3 * (X 2) ^ 8
    + 108 * (X 0) * (X 1) * (X 2) ^ 9
    - 54 * (X 1) ^ 3 * (X 2) ^ 8
    - 108 * (X 0) ^ 3 * (X 2) ^ 7
    - 162 * (X 0) * (X 2) ^ 9
    + 108 * (X 1) ^ 2 * (X 2) ^ 8
    - 54 * (X 1) * (X 2) ^ 9
    + 108 * (X 0) * (X 2) ^ 8
    - 162 * (X 1) * (X 2) ^ 8
    + 108 * (X 2) ^ 9
    + 54 * (X 1) * (X 2) ^ 7
    + 108 * (X 2) ^ 8
    - 162 * (X 2) ^ 7

public noncomputable def redJ_c6 : MvPolynomial (Fin 3) ℚ :=
  54 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 8
    - 108 * (X 0) ^ 6 * (X 1) * (X 2) ^ 8
    - 108 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    + 162 * (X 0) ^ 6 * (X 2) ^ 8
    + 216 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    - 108 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    + 54 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 10
    - 108 * (X 0) ^ 6 * (X 2) ^ 7
    - 324 * (X 0) ^ 4 * (X 2) ^ 9
    + 324 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    - 162 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    - 108 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    + 108 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    + 216 * (X 0) ^ 4 * (X 2) ^ 8
    - 324 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 270 * (X 0) ^ 3 * (X 2) ^ 9
    + 162 * (X 0) ^ 2 * (X 2) ^ 10
    - 324 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    + 162 * (X 0) * (X 1) * (X 2) ^ 10
    - 108 * (X 1) ^ 2 * (X 2) ^ 10
    + 162 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 108 * (X 0) ^ 2 * (X 2) ^ 9
    + 324 * (X 0) * (X 1) * (X 2) ^ 9
    - 270 * (X 0) * (X 2) ^ 10
    + 54 * (X 1) ^ 2 * (X 2) ^ 9
    - 54 * (X 1) * (X 2) ^ 10
    - 162 * (X 0) ^ 3 * (X 2) ^ 7
    - 162 * (X 0) * (X 1) * (X 2) ^ 8
    + 324 * (X 1) ^ 2 * (X 2) ^ 8
    - 270 * (X 1) * (X 2) ^ 9
    + 108 * (X 2) ^ 10
    + 162 * (X 0) * (X 2) ^ 8
    - 54 * (X 1) ^ 2 * (X 2) ^ 7
    - 54 * (X 1) * (X 2) ^ 8
    + 108 * (X 2) ^ 9
    + 162 * (X 1) * (X 2) ^ 7
    - 162 * (X 2) ^ 8

public noncomputable def jAff_c7 : MvPolynomial (Fin 3) ℚ :=
  -1269 * (X 0) * (X 1) ^ 8 * (X 2) ^ 8

public noncomputable def quotJ_c7 : MvPolynomial (Fin 3) ℚ :=
  -1269 * (X 0) * (X 1) ^ 5 * (X 2) ^ 7
    - 1269 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    + 1269 * (X 0) * (X 1) ^ 4 * (X 2) ^ 7
    + 2538 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 1269 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    - 1269 * (X 0) * (X 1) ^ 3 * (X 2) ^ 7
    - 3807 * (X 0) ^ 4 * (X 2) ^ 6
    - 2538 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 1269 * (X 0) * (X 1) ^ 3 * (X 2) ^ 6
    + 2538 * (X 0) ^ 4 * (X 2) ^ 5
    + 3807 * (X 0) ^ 2 * (X 2) ^ 7
    - 2538 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 1269 * (X 0) * (X 1) * (X 2) ^ 7
    - 2538 * (X 0) ^ 2 * (X 2) ^ 6
    + 3807 * (X 0) * (X 1) * (X 2) ^ 6
    - 2538 * (X 0) * (X 2) ^ 7
    - 1269 * (X 0) * (X 1) * (X 2) ^ 5
    - 2538 * (X 0) * (X 2) ^ 6
    + 3807 * (X 0) * (X 2) ^ 5

public noncomputable def redJ_c7 : MvPolynomial (Fin 3) ℚ :=
  -1269 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 6
    + 2538 * (X 0) ^ 7 * (X 1) * (X 2) ^ 6
    + 2538 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 7
    - 3807 * (X 0) ^ 7 * (X 2) ^ 6
    - 5076 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    + 2538 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 1269 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 2538 * (X 0) ^ 7 * (X 2) ^ 5
    + 7614 * (X 0) ^ 5 * (X 2) ^ 7
    - 7614 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    + 3807 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 2538 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 2538 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 5076 * (X 0) ^ 5 * (X 2) ^ 6
    + 7614 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 6345 * (X 0) ^ 4 * (X 2) ^ 7
    - 3807 * (X 0) ^ 3 * (X 2) ^ 8
    + 7614 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    - 3807 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 2538 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 3807 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 2538 * (X 0) ^ 3 * (X 2) ^ 7
    - 7614 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 6345 * (X 0) ^ 2 * (X 2) ^ 8
    - 1269 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 1269 * (X 0) * (X 1) * (X 2) ^ 8
    + 3807 * (X 0) ^ 4 * (X 2) ^ 5
    + 3807 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 7614 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 6345 * (X 0) * (X 1) * (X 2) ^ 7
    - 2538 * (X 0) * (X 2) ^ 8
    - 3807 * (X 0) ^ 2 * (X 2) ^ 6
    + 1269 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + 1269 * (X 0) * (X 1) * (X 2) ^ 6
    - 2538 * (X 0) * (X 2) ^ 7
    - 3807 * (X 0) * (X 1) * (X 2) ^ 5
    + 3807 * (X 0) * (X 2) ^ 6

public noncomputable def jAff_c8 : MvPolynomial (Fin 3) ℚ :=
  -1026 * (X 1) ^ 8 * (X 2) ^ 9

public noncomputable def quotJ_c8 : MvPolynomial (Fin 3) ℚ :=
  -1026 * (X 1) ^ 5 * (X 2) ^ 8
    - 1026 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 1026 * (X 1) ^ 4 * (X 2) ^ 8
    + 2052 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 1026 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 1026 * (X 1) ^ 3 * (X 2) ^ 8
    - 3078 * (X 0) ^ 3 * (X 2) ^ 7
    - 2052 * (X 0) * (X 1) * (X 2) ^ 8
    + 1026 * (X 1) ^ 3 * (X 2) ^ 7
    + 2052 * (X 0) ^ 3 * (X 2) ^ 6
    + 3078 * (X 0) * (X 2) ^ 8
    - 2052 * (X 1) ^ 2 * (X 2) ^ 7
    + 1026 * (X 1) * (X 2) ^ 8
    - 2052 * (X 0) * (X 2) ^ 7
    + 3078 * (X 1) * (X 2) ^ 7
    - 2052 * (X 2) ^ 8
    - 1026 * (X 1) * (X 2) ^ 6
    - 2052 * (X 2) ^ 7
    + 3078 * (X 2) ^ 6

public noncomputable def redJ_c8 : MvPolynomial (Fin 3) ℚ :=
  -1026 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 7
    + 2052 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    + 2052 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    - 3078 * (X 0) ^ 6 * (X 2) ^ 7
    - 4104 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 2052 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    - 1026 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 2052 * (X 0) ^ 6 * (X 2) ^ 6
    + 6156 * (X 0) ^ 4 * (X 2) ^ 8
    - 6156 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 3078 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 2052 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 2052 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 4104 * (X 0) ^ 4 * (X 2) ^ 7
    + 6156 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 5130 * (X 0) ^ 3 * (X 2) ^ 8
    - 3078 * (X 0) ^ 2 * (X 2) ^ 9
    + 6156 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 3078 * (X 0) * (X 1) * (X 2) ^ 9
    + 2052 * (X 1) ^ 2 * (X 2) ^ 9
    - 3078 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 2052 * (X 0) ^ 2 * (X 2) ^ 8
    - 6156 * (X 0) * (X 1) * (X 2) ^ 8
    + 5130 * (X 0) * (X 2) ^ 9
    - 1026 * (X 1) ^ 2 * (X 2) ^ 8
    + 1026 * (X 1) * (X 2) ^ 9
    + 3078 * (X 0) ^ 3 * (X 2) ^ 6
    + 3078 * (X 0) * (X 1) * (X 2) ^ 7
    - 6156 * (X 1) ^ 2 * (X 2) ^ 7
    + 5130 * (X 1) * (X 2) ^ 8
    - 2052 * (X 2) ^ 9
    - 3078 * (X 0) * (X 2) ^ 7
    + 1026 * (X 1) ^ 2 * (X 2) ^ 6
    + 1026 * (X 1) * (X 2) ^ 7
    - 2052 * (X 2) ^ 8
    - 3078 * (X 1) * (X 2) ^ 6
    + 3078 * (X 2) ^ 7

public noncomputable def jAff_c9 : MvPolynomial (Fin 3) ℚ :=
  1539 * (X 0) * (X 1) ^ 8 * (X 2) ^ 7

public noncomputable def quotJ_c9 : MvPolynomial (Fin 3) ℚ :=
  1539 * (X 0) * (X 1) ^ 5 * (X 2) ^ 6
    + 1539 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 1539 * (X 0) * (X 1) ^ 4 * (X 2) ^ 6
    - 3078 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 1539 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 1539 * (X 0) * (X 1) ^ 3 * (X 2) ^ 6
    + 4617 * (X 0) ^ 4 * (X 2) ^ 5
    + 3078 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 1539 * (X 0) * (X 1) ^ 3 * (X 2) ^ 5
    - 3078 * (X 0) ^ 4 * (X 2) ^ 4
    - 4617 * (X 0) ^ 2 * (X 2) ^ 6
    + 3078 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 1539 * (X 0) * (X 1) * (X 2) ^ 6
    + 3078 * (X 0) ^ 2 * (X 2) ^ 5
    - 4617 * (X 0) * (X 1) * (X 2) ^ 5
    + 3078 * (X 0) * (X 2) ^ 6
    + 1539 * (X 0) * (X 1) * (X 2) ^ 4
    + 3078 * (X 0) * (X 2) ^ 5
    - 4617 * (X 0) * (X 2) ^ 4

public noncomputable def redJ_c9 : MvPolynomial (Fin 3) ℚ :=
  1539 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 5
    - 3078 * (X 0) ^ 7 * (X 1) * (X 2) ^ 5
    - 3078 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    + 4617 * (X 0) ^ 7 * (X 2) ^ 5
    + 6156 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    - 3078 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    + 1539 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 3078 * (X 0) ^ 7 * (X 2) ^ 4
    - 9234 * (X 0) ^ 5 * (X 2) ^ 6
    + 9234 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 4617 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 3078 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 3078 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 6156 * (X 0) ^ 5 * (X 2) ^ 5
    - 9234 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 7695 * (X 0) ^ 4 * (X 2) ^ 6
    + 4617 * (X 0) ^ 3 * (X 2) ^ 7
    - 9234 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 4617 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 3078 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 4617 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 3078 * (X 0) ^ 3 * (X 2) ^ 6
    + 9234 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 7695 * (X 0) ^ 2 * (X 2) ^ 7
    + 1539 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 1539 * (X 0) * (X 1) * (X 2) ^ 7
    - 4617 * (X 0) ^ 4 * (X 2) ^ 4
    - 4617 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 9234 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 7695 * (X 0) * (X 1) * (X 2) ^ 6
    + 3078 * (X 0) * (X 2) ^ 7
    + 4617 * (X 0) ^ 2 * (X 2) ^ 5
    - 1539 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 1539 * (X 0) * (X 1) * (X 2) ^ 5
    + 3078 * (X 0) * (X 2) ^ 6
    + 4617 * (X 0) * (X 1) * (X 2) ^ 4
    - 4617 * (X 0) * (X 2) ^ 5

public noncomputable def jAff_c10 : MvPolynomial (Fin 3) ℚ :=
  4464 * (X 1) ^ 8 * (X 2) ^ 8

public noncomputable def quotJ_c10 : MvPolynomial (Fin 3) ℚ :=
  4464 * (X 1) ^ 5 * (X 2) ^ 7
    + 4464 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 4464 * (X 1) ^ 4 * (X 2) ^ 7
    - 8928 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 4464 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 4464 * (X 1) ^ 3 * (X 2) ^ 7
    + 13392 * (X 0) ^ 3 * (X 2) ^ 6
    + 8928 * (X 0) * (X 1) * (X 2) ^ 7
    - 4464 * (X 1) ^ 3 * (X 2) ^ 6
    - 8928 * (X 0) ^ 3 * (X 2) ^ 5
    - 13392 * (X 0) * (X 2) ^ 7
    + 8928 * (X 1) ^ 2 * (X 2) ^ 6
    - 4464 * (X 1) * (X 2) ^ 7
    + 8928 * (X 0) * (X 2) ^ 6
    - 13392 * (X 1) * (X 2) ^ 6
    + 8928 * (X 2) ^ 7
    + 4464 * (X 1) * (X 2) ^ 5
    + 8928 * (X 2) ^ 6
    - 13392 * (X 2) ^ 5

public noncomputable def redJ_c10 : MvPolynomial (Fin 3) ℚ :=
  4464 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 6
    - 8928 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    - 8928 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    + 13392 * (X 0) ^ 6 * (X 2) ^ 6
    + 17856 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 8928 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 4464 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 8928 * (X 0) ^ 6 * (X 2) ^ 5
    - 26784 * (X 0) ^ 4 * (X 2) ^ 7
    + 26784 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 13392 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 8928 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 8928 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 17856 * (X 0) ^ 4 * (X 2) ^ 6
    - 26784 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 22320 * (X 0) ^ 3 * (X 2) ^ 7
    + 13392 * (X 0) ^ 2 * (X 2) ^ 8
    - 26784 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 13392 * (X 0) * (X 1) * (X 2) ^ 8
    - 8928 * (X 1) ^ 2 * (X 2) ^ 8
    + 13392 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 8928 * (X 0) ^ 2 * (X 2) ^ 7
    + 26784 * (X 0) * (X 1) * (X 2) ^ 7
    - 22320 * (X 0) * (X 2) ^ 8
    + 4464 * (X 1) ^ 2 * (X 2) ^ 7
    - 4464 * (X 1) * (X 2) ^ 8
    - 13392 * (X 0) ^ 3 * (X 2) ^ 5
    - 13392 * (X 0) * (X 1) * (X 2) ^ 6
    + 26784 * (X 1) ^ 2 * (X 2) ^ 6
    - 22320 * (X 1) * (X 2) ^ 7
    + 8928 * (X 2) ^ 8
    + 13392 * (X 0) * (X 2) ^ 6
    - 4464 * (X 1) ^ 2 * (X 2) ^ 5
    - 4464 * (X 1) * (X 2) ^ 6
    + 8928 * (X 2) ^ 7
    + 13392 * (X 1) * (X 2) ^ 5
    - 13392 * (X 2) ^ 6

public noncomputable def jAff_c11 : MvPolynomial (Fin 3) ℚ :=
  729 * (X 0) * (X 1) ^ 8 * (X 2) ^ 6

public noncomputable def quotJ_c11 : MvPolynomial (Fin 3) ℚ :=
  729 * (X 0) * (X 1) ^ 5 * (X 2) ^ 5
    + 729 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 729 * (X 0) * (X 1) ^ 4 * (X 2) ^ 5
    - 1458 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 729 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 729 * (X 0) * (X 1) ^ 3 * (X 2) ^ 5
    + 2187 * (X 0) ^ 4 * (X 2) ^ 4
    + 1458 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 729 * (X 0) * (X 1) ^ 3 * (X 2) ^ 4
    - 1458 * (X 0) ^ 4 * (X 2) ^ 3
    - 2187 * (X 0) ^ 2 * (X 2) ^ 5
    + 1458 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 729 * (X 0) * (X 1) * (X 2) ^ 5
    + 1458 * (X 0) ^ 2 * (X 2) ^ 4
    - 2187 * (X 0) * (X 1) * (X 2) ^ 4
    + 1458 * (X 0) * (X 2) ^ 5
    + 729 * (X 0) * (X 1) * (X 2) ^ 3
    + 1458 * (X 0) * (X 2) ^ 4
    - 2187 * (X 0) * (X 2) ^ 3

public noncomputable def redJ_c11 : MvPolynomial (Fin 3) ℚ :=
  729 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 4
    - 1458 * (X 0) ^ 7 * (X 1) * (X 2) ^ 4
    - 1458 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 5
    + 2187 * (X 0) ^ 7 * (X 2) ^ 4
    + 2916 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    - 1458 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    + 729 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 1458 * (X 0) ^ 7 * (X 2) ^ 3
    - 4374 * (X 0) ^ 5 * (X 2) ^ 5
    + 4374 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 2187 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 1458 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 1458 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 2916 * (X 0) ^ 5 * (X 2) ^ 4
    - 4374 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 3645 * (X 0) ^ 4 * (X 2) ^ 5
    + 2187 * (X 0) ^ 3 * (X 2) ^ 6
    - 4374 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 2187 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 1458 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 2187 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 1458 * (X 0) ^ 3 * (X 2) ^ 5
    + 4374 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 3645 * (X 0) ^ 2 * (X 2) ^ 6
    + 729 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 729 * (X 0) * (X 1) * (X 2) ^ 6
    - 2187 * (X 0) ^ 4 * (X 2) ^ 3
    - 2187 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 4374 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 3645 * (X 0) * (X 1) * (X 2) ^ 5
    + 1458 * (X 0) * (X 2) ^ 6
    + 2187 * (X 0) ^ 2 * (X 2) ^ 4
    - 729 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    - 729 * (X 0) * (X 1) * (X 2) ^ 4
    + 1458 * (X 0) * (X 2) ^ 5
    + 2187 * (X 0) * (X 1) * (X 2) ^ 3
    - 2187 * (X 0) * (X 2) ^ 4

public noncomputable def jAff_c12 : MvPolynomial (Fin 3) ℚ :=
  -4968 * (X 1) ^ 8 * (X 2) ^ 7

public noncomputable def quotJ_c12 : MvPolynomial (Fin 3) ℚ :=
  -4968 * (X 1) ^ 5 * (X 2) ^ 6
    - 4968 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 4968 * (X 1) ^ 4 * (X 2) ^ 6
    + 9936 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 4968 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 4968 * (X 1) ^ 3 * (X 2) ^ 6
    - 14904 * (X 0) ^ 3 * (X 2) ^ 5
    - 9936 * (X 0) * (X 1) * (X 2) ^ 6
    + 4968 * (X 1) ^ 3 * (X 2) ^ 5
    + 9936 * (X 0) ^ 3 * (X 2) ^ 4
    + 14904 * (X 0) * (X 2) ^ 6
    - 9936 * (X 1) ^ 2 * (X 2) ^ 5
    + 4968 * (X 1) * (X 2) ^ 6
    - 9936 * (X 0) * (X 2) ^ 5
    + 14904 * (X 1) * (X 2) ^ 5
    - 9936 * (X 2) ^ 6
    - 4968 * (X 1) * (X 2) ^ 4
    - 9936 * (X 2) ^ 5
    + 14904 * (X 2) ^ 4

public noncomputable def redJ_c12 : MvPolynomial (Fin 3) ℚ :=
  -4968 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 5
    + 9936 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    + 9936 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 14904 * (X 0) ^ 6 * (X 2) ^ 5
    - 19872 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 9936 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 4968 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 9936 * (X 0) ^ 6 * (X 2) ^ 4
    + 29808 * (X 0) ^ 4 * (X 2) ^ 6
    - 29808 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 14904 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 9936 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 9936 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 19872 * (X 0) ^ 4 * (X 2) ^ 5
    + 29808 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 24840 * (X 0) ^ 3 * (X 2) ^ 6
    - 14904 * (X 0) ^ 2 * (X 2) ^ 7
    + 29808 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 14904 * (X 0) * (X 1) * (X 2) ^ 7
    + 9936 * (X 1) ^ 2 * (X 2) ^ 7
    - 14904 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 9936 * (X 0) ^ 2 * (X 2) ^ 6
    - 29808 * (X 0) * (X 1) * (X 2) ^ 6
    + 24840 * (X 0) * (X 2) ^ 7
    - 4968 * (X 1) ^ 2 * (X 2) ^ 6
    + 4968 * (X 1) * (X 2) ^ 7
    + 14904 * (X 0) ^ 3 * (X 2) ^ 4
    + 14904 * (X 0) * (X 1) * (X 2) ^ 5
    - 29808 * (X 1) ^ 2 * (X 2) ^ 5
    + 24840 * (X 1) * (X 2) ^ 6
    - 9936 * (X 2) ^ 7
    - 14904 * (X 0) * (X 2) ^ 5
    + 4968 * (X 1) ^ 2 * (X 2) ^ 4
    + 4968 * (X 1) * (X 2) ^ 5
    - 9936 * (X 2) ^ 6
    - 14904 * (X 1) * (X 2) ^ 4
    + 14904 * (X 2) ^ 5

public noncomputable def jAff_c13 : MvPolynomial (Fin 3) ℚ :=
  -1728 * (X 1) ^ 8 * (X 2) ^ 6

public noncomputable def quotJ_c13 : MvPolynomial (Fin 3) ℚ :=
  -1728 * (X 1) ^ 5 * (X 2) ^ 5
    - 1728 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 1728 * (X 1) ^ 4 * (X 2) ^ 5
    + 3456 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 1728 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 1728 * (X 1) ^ 3 * (X 2) ^ 5
    - 5184 * (X 0) ^ 3 * (X 2) ^ 4
    - 3456 * (X 0) * (X 1) * (X 2) ^ 5
    + 1728 * (X 1) ^ 3 * (X 2) ^ 4
    + 3456 * (X 0) ^ 3 * (X 2) ^ 3
    + 5184 * (X 0) * (X 2) ^ 5
    - 3456 * (X 1) ^ 2 * (X 2) ^ 4
    + 1728 * (X 1) * (X 2) ^ 5
    - 3456 * (X 0) * (X 2) ^ 4
    + 5184 * (X 1) * (X 2) ^ 4
    - 3456 * (X 2) ^ 5
    - 1728 * (X 1) * (X 2) ^ 3
    - 3456 * (X 2) ^ 4
    + 5184 * (X 2) ^ 3

public noncomputable def redJ_c13 : MvPolynomial (Fin 3) ℚ :=
  -1728 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 4
    + 3456 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    + 3456 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 5184 * (X 0) ^ 6 * (X 2) ^ 4
    - 6912 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 3456 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 1728 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 3456 * (X 0) ^ 6 * (X 2) ^ 3
    + 10368 * (X 0) ^ 4 * (X 2) ^ 5
    - 10368 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 5184 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 3456 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 3456 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 6912 * (X 0) ^ 4 * (X 2) ^ 4
    + 10368 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 8640 * (X 0) ^ 3 * (X 2) ^ 5
    - 5184 * (X 0) ^ 2 * (X 2) ^ 6
    + 10368 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 5184 * (X 0) * (X 1) * (X 2) ^ 6
    + 3456 * (X 1) ^ 2 * (X 2) ^ 6
    - 5184 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 3456 * (X 0) ^ 2 * (X 2) ^ 5
    - 10368 * (X 0) * (X 1) * (X 2) ^ 5
    + 8640 * (X 0) * (X 2) ^ 6
    - 1728 * (X 1) ^ 2 * (X 2) ^ 5
    + 1728 * (X 1) * (X 2) ^ 6
    + 5184 * (X 0) ^ 3 * (X 2) ^ 3
    + 5184 * (X 0) * (X 1) * (X 2) ^ 4
    - 10368 * (X 1) ^ 2 * (X 2) ^ 4
    + 8640 * (X 1) * (X 2) ^ 5
    - 3456 * (X 2) ^ 6
    - 5184 * (X 0) * (X 2) ^ 4
    + 1728 * (X 1) ^ 2 * (X 2) ^ 3
    + 1728 * (X 1) * (X 2) ^ 4
    - 3456 * (X 2) ^ 5
    - 5184 * (X 1) * (X 2) ^ 3
    + 5184 * (X 2) ^ 4

public noncomputable def jAff_c14 : MvPolynomial (Fin 3) ℚ :=
  -810 * (X 1) ^ 8 * (X 2) ^ 5

public noncomputable def quotJ_c14 : MvPolynomial (Fin 3) ℚ :=
  -810 * (X 1) ^ 5 * (X 2) ^ 4
    - 810 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 810 * (X 1) ^ 4 * (X 2) ^ 4
    + 1620 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 810 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 810 * (X 1) ^ 3 * (X 2) ^ 4
    - 2430 * (X 0) ^ 3 * (X 2) ^ 3
    - 1620 * (X 0) * (X 1) * (X 2) ^ 4
    + 810 * (X 1) ^ 3 * (X 2) ^ 3
    + 1620 * (X 0) ^ 3 * (X 2) ^ 2
    + 2430 * (X 0) * (X 2) ^ 4
    - 1620 * (X 1) ^ 2 * (X 2) ^ 3
    + 810 * (X 1) * (X 2) ^ 4
    - 1620 * (X 0) * (X 2) ^ 3
    + 2430 * (X 1) * (X 2) ^ 3
    - 1620 * (X 2) ^ 4
    - 810 * (X 1) * (X 2) ^ 2
    - 1620 * (X 2) ^ 3
    + 2430 * (X 2) ^ 2

public noncomputable def redJ_c14 : MvPolynomial (Fin 3) ℚ :=
  -810 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 3
    + 1620 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    + 1620 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 2430 * (X 0) ^ 6 * (X 2) ^ 3
    - 3240 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 1620 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 810 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 1620 * (X 0) ^ 6 * (X 2) ^ 2
    + 4860 * (X 0) ^ 4 * (X 2) ^ 4
    - 4860 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 2430 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 1620 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 1620 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 3240 * (X 0) ^ 4 * (X 2) ^ 3
    + 4860 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 4050 * (X 0) ^ 3 * (X 2) ^ 4
    - 2430 * (X 0) ^ 2 * (X 2) ^ 5
    + 4860 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 2430 * (X 0) * (X 1) * (X 2) ^ 5
    + 1620 * (X 1) ^ 2 * (X 2) ^ 5
    - 2430 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 1620 * (X 0) ^ 2 * (X 2) ^ 4
    - 4860 * (X 0) * (X 1) * (X 2) ^ 4
    + 4050 * (X 0) * (X 2) ^ 5
    - 810 * (X 1) ^ 2 * (X 2) ^ 4
    + 810 * (X 1) * (X 2) ^ 5
    + 2430 * (X 0) ^ 3 * (X 2) ^ 2
    + 2430 * (X 0) * (X 1) * (X 2) ^ 3
    - 4860 * (X 1) ^ 2 * (X 2) ^ 3
    + 4050 * (X 1) * (X 2) ^ 4
    - 1620 * (X 2) ^ 5
    - 2430 * (X 0) * (X 2) ^ 3
    + 810 * (X 1) ^ 2 * (X 2) ^ 2
    + 810 * (X 1) * (X 2) ^ 3
    - 1620 * (X 2) ^ 4
    - 2430 * (X 1) * (X 2) ^ 2
    + 2430 * (X 2) ^ 3

public noncomputable def jAff_c15 : MvPolynomial (Fin 3) ℚ :=
  486 * (X 1) ^ 8 * (X 2) ^ 4

public noncomputable def quotJ_c15 : MvPolynomial (Fin 3) ℚ :=
  486 * (X 1) ^ 5 * (X 2) ^ 3
    + 486 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    - 486 * (X 1) ^ 4 * (X 2) ^ 3
    - 972 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    - 486 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 486 * (X 1) ^ 3 * (X 2) ^ 3
    + 1458 * (X 0) ^ 3 * (X 2) ^ 2
    + 972 * (X 0) * (X 1) * (X 2) ^ 3
    - 486 * (X 1) ^ 3 * (X 2) ^ 2
    - 972 * (X 0) ^ 3 * (X 2)
    - 1458 * (X 0) * (X 2) ^ 3
    + 972 * (X 1) ^ 2 * (X 2) ^ 2
    - 486 * (X 1) * (X 2) ^ 3
    + 972 * (X 0) * (X 2) ^ 2
    - 1458 * (X 1) * (X 2) ^ 2
    + 972 * (X 2) ^ 3
    + 486 * (X 1) * (X 2)
    + 972 * (X 2) ^ 2
    - 1458 * (X 2)

public noncomputable def redJ_c15 : MvPolynomial (Fin 3) ℚ :=
  486 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 2
    - 972 * (X 0) ^ 6 * (X 1) * (X 2) ^ 2
    - 972 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    + 1458 * (X 0) ^ 6 * (X 2) ^ 2
    + 1944 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 972 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 486 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 4
    - 972 * (X 0) ^ 6 * (X 2)
    - 2916 * (X 0) ^ 4 * (X 2) ^ 3
    + 2916 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    - 1458 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 972 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 972 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 1944 * (X 0) ^ 4 * (X 2) ^ 2
    - 2916 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 2430 * (X 0) ^ 3 * (X 2) ^ 3
    + 1458 * (X 0) ^ 2 * (X 2) ^ 4
    - 2916 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 1458 * (X 0) * (X 1) * (X 2) ^ 4
    - 972 * (X 1) ^ 2 * (X 2) ^ 4
    + 1458 * (X 0) ^ 3 * (X 1) * (X 2)
    - 972 * (X 0) ^ 2 * (X 2) ^ 3
    + 2916 * (X 0) * (X 1) * (X 2) ^ 3
    - 2430 * (X 0) * (X 2) ^ 4
    + 486 * (X 1) ^ 2 * (X 2) ^ 3
    - 486 * (X 1) * (X 2) ^ 4
    - 1458 * (X 0) ^ 3 * (X 2)
    - 1458 * (X 0) * (X 1) * (X 2) ^ 2
    + 2916 * (X 1) ^ 2 * (X 2) ^ 2
    - 2430 * (X 1) * (X 2) ^ 3
    + 972 * (X 2) ^ 4
    + 1458 * (X 0) * (X 2) ^ 2
    - 486 * (X 1) ^ 2 * (X 2)
    - 486 * (X 1) * (X 2) ^ 2
    + 972 * (X 2) ^ 3
    + 1458 * (X 1) * (X 2)
    - 1458 * (X 2) ^ 2

public noncomputable def jAff_c16 : MvPolynomial (Fin 3) ℚ :=
  -648 * (X 0) * (X 1) ^ 7 * (X 2) ^ 10
    + 6318 * (X 0) * (X 1) ^ 7 * (X 2) ^ 9

public noncomputable def quotJ_c16 : MvPolynomial (Fin 3) ℚ :=
  -648 * (X 0) * (X 1) ^ 4 * (X 2) ^ 9
    - 648 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 6318 * (X 0) * (X 1) ^ 4 * (X 2) ^ 8
    + 648 * (X 0) * (X 1) ^ 3 * (X 2) ^ 9
    + 6318 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 1296 * (X 0) ^ 4 * (X 2) ^ 8
    + 648 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 6318 * (X 0) * (X 1) ^ 3 * (X 2) ^ 8
    - 648 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 12636 * (X 0) ^ 4 * (X 2) ^ 7
    - 6318 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 1296 * (X 0) ^ 2 * (X 2) ^ 9
    + 6966 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 12636 * (X 0) ^ 2 * (X 2) ^ 8
    - 6318 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 1296 * (X 0) * (X 1) * (X 2) ^ 8
    + 648 * (X 0) * (X 2) ^ 9
    + 12636 * (X 0) * (X 1) * (X 2) ^ 7
    - 4374 * (X 0) * (X 2) ^ 8
    - 19602 * (X 0) * (X 2) ^ 7
    + 6318 * (X 0) * (X 2) ^ 6

public noncomputable def redJ_c16 : MvPolynomial (Fin 3) ℚ :=
  -648 * (X 0) ^ 7 * (X 1) * (X 2) ^ 8
    + 6318 * (X 0) ^ 7 * (X 1) * (X 2) ^ 7
    + 1296 * (X 0) ^ 7 * (X 2) ^ 8
    + 1296 * (X 0) ^ 5 * (X 1) * (X 2) ^ 9
    - 1944 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    - 12636 * (X 0) ^ 7 * (X 2) ^ 7
    - 12636 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    - 2592 * (X 0) ^ 5 * (X 2) ^ 9
    + 20250 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    - 648 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    - 648 * (X 0) ^ 3 * (X 1) * (X 2) ^ 10
    + 1944 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 10
    + 25272 * (X 0) ^ 5 * (X 2) ^ 8
    - 12636 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    + 3726 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 1944 * (X 0) ^ 4 * (X 2) ^ 9
    + 6318 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    + 1296 * (X 0) ^ 3 * (X 2) ^ 10
    - 20250 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 648 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    - 1296 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    + 25272 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 17010 * (X 0) ^ 4 * (X 2) ^ 8
    - 12636 * (X 0) ^ 3 * (X 2) ^ 9
    + 12636 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 3726 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 1944 * (X 0) ^ 2 * (X 2) ^ 10
    + 11340 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 19602 * (X 0) ^ 4 * (X 2) ^ 7
    - 25272 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 17010 * (X 0) ^ 2 * (X 2) ^ 9
    + 14580 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 1944 * (X 0) * (X 1) * (X 2) ^ 9
    + 648 * (X 0) * (X 2) ^ 10
    + 6318 * (X 0) ^ 4 * (X 2) ^ 6
    + 19602 * (X 0) ^ 2 * (X 2) ^ 8
    - 18954 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 17010 * (X 0) * (X 1) * (X 2) ^ 8
    - 4374 * (X 0) * (X 2) ^ 9
    - 6318 * (X 0) ^ 2 * (X 2) ^ 7
    + 19602 * (X 0) * (X 1) * (X 2) ^ 7
    - 19602 * (X 0) * (X 2) ^ 8
    - 6318 * (X 0) * (X 1) * (X 2) ^ 6
    + 6318 * (X 0) * (X 2) ^ 7

public noncomputable def jAff_c17 : MvPolynomial (Fin 3) ℚ :=
  1044 * (X 1) ^ 7 * (X 2) ^ 10
    - 12222 * (X 0) * (X 1) ^ 7 * (X 2) ^ 8

public noncomputable def quotJ_c17 : MvPolynomial (Fin 3) ℚ :=
  1044 * (X 1) ^ 4 * (X 2) ^ 9
    + 1044 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 12222 * (X 0) * (X 1) ^ 4 * (X 2) ^ 7
    - 1044 * (X 1) ^ 3 * (X 2) ^ 9
    - 12222 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 2088 * (X 0) ^ 3 * (X 2) ^ 8
    + 12222 * (X 0) * (X 1) ^ 3 * (X 2) ^ 7
    - 1044 * (X 0) * (X 1) * (X 2) ^ 9
    + 1044 * (X 1) ^ 2 * (X 2) ^ 9
    + 24444 * (X 0) ^ 4 * (X 2) ^ 6
    + 12222 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 12222 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 2088 * (X 0) * (X 2) ^ 9
    - 1044 * (X 1) ^ 2 * (X 2) ^ 8
    - 24444 * (X 0) ^ 2 * (X 2) ^ 7
    + 12222 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 2088 * (X 1) * (X 2) ^ 8
    - 1044 * (X 2) ^ 9
    - 24444 * (X 0) * (X 1) * (X 2) ^ 6
    + 12222 * (X 0) * (X 2) ^ 7
    - 3132 * (X 2) ^ 8
    + 36666 * (X 0) * (X 2) ^ 6
    + 1044 * (X 2) ^ 7
    - 12222 * (X 0) * (X 2) ^ 5

public noncomputable def redJ_c17 : MvPolynomial (Fin 3) ℚ :=
  1044 * (X 0) ^ 6 * (X 1) * (X 2) ^ 8
    - 12222 * (X 0) ^ 7 * (X 1) * (X 2) ^ 6
    - 2088 * (X 0) ^ 6 * (X 2) ^ 8
    - 2088 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    + 3132 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    + 24444 * (X 0) ^ 7 * (X 2) ^ 6
    + 24444 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    - 36666 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    + 4176 * (X 0) ^ 4 * (X 2) ^ 9
    - 2088 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 1044 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    + 1044 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    - 3132 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    - 48888 * (X 0) ^ 5 * (X 2) ^ 7
    + 24444 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 12222 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 8046 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 3132 * (X 0) ^ 3 * (X 2) ^ 9
    + 36666 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 2088 * (X 0) ^ 2 * (X 2) ^ 10
    + 2088 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 1044 * (X 0) * (X 1) * (X 2) ^ 10
    + 2088 * (X 1) ^ 2 * (X 2) ^ 10
    - 48888 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 36666 * (X 0) ^ 4 * (X 2) ^ 7
    + 21312 * (X 0) ^ 3 * (X 2) ^ 8
    - 24444 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 12222 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 24444 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 4176 * (X 0) * (X 1) * (X 2) ^ 9
    + 3132 * (X 0) * (X 2) ^ 10
    + 2088 * (X 1) ^ 2 * (X 2) ^ 9
    + 36666 * (X 0) ^ 4 * (X 2) ^ 6
    + 1044 * (X 0) ^ 3 * (X 2) ^ 7
    + 48888 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 36666 * (X 0) ^ 2 * (X 2) ^ 8
    - 24444 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 3132 * (X 0) * (X 2) ^ 9
    - 3132 * (X 1) ^ 2 * (X 2) ^ 8
    + 3132 * (X 1) * (X 2) ^ 9
    - 1044 * (X 2) ^ 10
    - 12222 * (X 0) ^ 4 * (X 2) ^ 5
    - 36666 * (X 0) ^ 2 * (X 2) ^ 7
    + 36666 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 36666 * (X 0) * (X 1) * (X 2) ^ 7
    + 11178 * (X 0) * (X 2) ^ 8
    + 3132 * (X 1) * (X 2) ^ 8
    - 3132 * (X 2) ^ 9
    + 12222 * (X 0) ^ 2 * (X 2) ^ 6
    - 36666 * (X 0) * (X 1) * (X 2) ^ 6
    + 36666 * (X 0) * (X 2) ^ 7
    - 1044 * (X 1) * (X 2) ^ 7
    + 1044 * (X 2) ^ 8
    + 12222 * (X 0) * (X 1) * (X 2) ^ 5
    - 12222 * (X 0) * (X 2) ^ 6

public noncomputable def jAff_c18 : MvPolynomial (Fin 3) ℚ :=
  -10287 * (X 1) ^ 7 * (X 2) ^ 9
    - 2214 * (X 0) * (X 1) ^ 7 * (X 2) ^ 7

public noncomputable def quotJ_c18 : MvPolynomial (Fin 3) ℚ :=
  -10287 * (X 1) ^ 4 * (X 2) ^ 8
    - 10287 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 2214 * (X 0) * (X 1) ^ 4 * (X 2) ^ 6
    + 10287 * (X 1) ^ 3 * (X 2) ^ 8
    - 2214 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 20574 * (X 0) ^ 3 * (X 2) ^ 7
    + 2214 * (X 0) * (X 1) ^ 3 * (X 2) ^ 6
    + 10287 * (X 0) * (X 1) * (X 2) ^ 8
    - 10287 * (X 1) ^ 2 * (X 2) ^ 8
    + 4428 * (X 0) ^ 4 * (X 2) ^ 5
    + 2214 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 2214 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 20574 * (X 0) * (X 2) ^ 8
    + 10287 * (X 1) ^ 2 * (X 2) ^ 7
    - 4428 * (X 0) ^ 2 * (X 2) ^ 6
    + 2214 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 20574 * (X 1) * (X 2) ^ 7
    + 10287 * (X 2) ^ 8
    - 4428 * (X 0) * (X 1) * (X 2) ^ 5
    + 2214 * (X 0) * (X 2) ^ 6
    + 30861 * (X 2) ^ 7
    + 6642 * (X 0) * (X 2) ^ 5
    - 10287 * (X 2) ^ 6
    - 2214 * (X 0) * (X 2) ^ 4

public noncomputable def redJ_c18 : MvPolynomial (Fin 3) ℚ :=
  -10287 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    - 2214 * (X 0) ^ 7 * (X 1) * (X 2) ^ 5
    + 20574 * (X 0) ^ 6 * (X 2) ^ 7
    + 20574 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 30861 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 4428 * (X 0) ^ 7 * (X 2) ^ 5
    + 4428 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    - 6642 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 41148 * (X 0) ^ 4 * (X 2) ^ 8
    + 20574 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 10287 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 10287 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 30861 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 8856 * (X 0) ^ 5 * (X 2) ^ 6
    + 4428 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 2214 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 43362 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 30861 * (X 0) ^ 3 * (X 2) ^ 8
    + 6642 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 20574 * (X 0) ^ 2 * (X 2) ^ 9
    - 20574 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 10287 * (X 0) * (X 1) * (X 2) ^ 9
    - 20574 * (X 1) ^ 2 * (X 2) ^ 9
    - 8856 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 6642 * (X 0) ^ 4 * (X 2) ^ 6
    + 35289 * (X 0) ^ 3 * (X 2) ^ 7
    - 4428 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 2214 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 4428 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 41148 * (X 0) * (X 1) * (X 2) ^ 8
    - 30861 * (X 0) * (X 2) ^ 9
    - 20574 * (X 1) ^ 2 * (X 2) ^ 8
    + 6642 * (X 0) ^ 4 * (X 2) ^ 5
    - 10287 * (X 0) ^ 3 * (X 2) ^ 6
    + 8856 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 6642 * (X 0) ^ 2 * (X 2) ^ 7
    - 4428 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 30861 * (X 0) * (X 2) ^ 8
    + 30861 * (X 1) ^ 2 * (X 2) ^ 7
    - 30861 * (X 1) * (X 2) ^ 8
    + 10287 * (X 2) ^ 9
    - 2214 * (X 0) ^ 4 * (X 2) ^ 4
    - 6642 * (X 0) ^ 2 * (X 2) ^ 6
    + 6642 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 6642 * (X 0) * (X 1) * (X 2) ^ 6
    + 12501 * (X 0) * (X 2) ^ 7
    - 30861 * (X 1) * (X 2) ^ 7
    + 30861 * (X 2) ^ 8
    + 2214 * (X 0) ^ 2 * (X 2) ^ 5
    - 6642 * (X 0) * (X 1) * (X 2) ^ 5
    + 6642 * (X 0) * (X 2) ^ 6
    + 10287 * (X 1) * (X 2) ^ 6
    - 10287 * (X 2) ^ 7
    + 2214 * (X 0) * (X 1) * (X 2) ^ 4
    - 2214 * (X 0) * (X 2) ^ 5

public noncomputable def jAff_c19 : MvPolynomial (Fin 3) ℚ :=
  20844 * (X 1) ^ 7 * (X 2) ^ 8
    - 2106 * (X 0) * (X 1) ^ 7 * (X 2) ^ 6

public noncomputable def quotJ_c19 : MvPolynomial (Fin 3) ℚ :=
  20844 * (X 1) ^ 4 * (X 2) ^ 7
    + 20844 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 2106 * (X 0) * (X 1) ^ 4 * (X 2) ^ 5
    - 20844 * (X 1) ^ 3 * (X 2) ^ 7
    - 2106 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 41688 * (X 0) ^ 3 * (X 2) ^ 6
    + 2106 * (X 0) * (X 1) ^ 3 * (X 2) ^ 5
    - 20844 * (X 0) * (X 1) * (X 2) ^ 7
    + 20844 * (X 1) ^ 2 * (X 2) ^ 7
    + 4212 * (X 0) ^ 4 * (X 2) ^ 4
    + 2106 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 2106 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + 41688 * (X 0) * (X 2) ^ 7
    - 20844 * (X 1) ^ 2 * (X 2) ^ 6
    - 4212 * (X 0) ^ 2 * (X 2) ^ 5
    + 2106 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 41688 * (X 1) * (X 2) ^ 6
    - 20844 * (X 2) ^ 7
    - 4212 * (X 0) * (X 1) * (X 2) ^ 4
    + 2106 * (X 0) * (X 2) ^ 5
    - 62532 * (X 2) ^ 6
    + 6318 * (X 0) * (X 2) ^ 4
    + 20844 * (X 2) ^ 5
    - 2106 * (X 0) * (X 2) ^ 3

public noncomputable def redJ_c19 : MvPolynomial (Fin 3) ℚ :=
  20844 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    - 2106 * (X 0) ^ 7 * (X 1) * (X 2) ^ 4
    - 41688 * (X 0) ^ 6 * (X 2) ^ 6
    - 41688 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 62532 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 4212 * (X 0) ^ 7 * (X 2) ^ 4
    + 4212 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    - 6318 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    + 83376 * (X 0) ^ 4 * (X 2) ^ 7
    - 41688 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 20844 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 20844 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 62532 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 8424 * (X 0) ^ 5 * (X 2) ^ 5
    + 4212 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 2106 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 81270 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 62532 * (X 0) ^ 3 * (X 2) ^ 7
    + 6318 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 41688 * (X 0) ^ 2 * (X 2) ^ 8
    + 41688 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 20844 * (X 0) * (X 1) * (X 2) ^ 8
    + 41688 * (X 1) ^ 2 * (X 2) ^ 8
    - 8424 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 6318 * (X 0) ^ 4 * (X 2) ^ 5
    - 58320 * (X 0) ^ 3 * (X 2) ^ 6
    - 4212 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 2106 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 4212 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 83376 * (X 0) * (X 1) * (X 2) ^ 7
    + 62532 * (X 0) * (X 2) ^ 8
    + 41688 * (X 1) ^ 2 * (X 2) ^ 7
    + 6318 * (X 0) ^ 4 * (X 2) ^ 4
    + 20844 * (X 0) ^ 3 * (X 2) ^ 5
    + 8424 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 6318 * (X 0) ^ 2 * (X 2) ^ 6
    - 4212 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + 62532 * (X 0) * (X 2) ^ 7
    - 62532 * (X 1) ^ 2 * (X 2) ^ 6
    + 62532 * (X 1) * (X 2) ^ 7
    - 20844 * (X 2) ^ 8
    - 2106 * (X 0) ^ 4 * (X 2) ^ 3
    - 6318 * (X 0) ^ 2 * (X 2) ^ 5
    + 6318 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 6318 * (X 0) * (X 1) * (X 2) ^ 5
    - 18738 * (X 0) * (X 2) ^ 6
    + 62532 * (X 1) * (X 2) ^ 6
    - 62532 * (X 2) ^ 7
    + 2106 * (X 0) ^ 2 * (X 2) ^ 4
    - 6318 * (X 0) * (X 1) * (X 2) ^ 4
    + 6318 * (X 0) * (X 2) ^ 5
    - 20844 * (X 1) * (X 2) ^ 5
    + 20844 * (X 2) ^ 6
    + 2106 * (X 0) * (X 1) * (X 2) ^ 3
    - 2106 * (X 0) * (X 2) ^ 4

public noncomputable def jAff_c20 : MvPolynomial (Fin 3) ℚ :=
  666 * (X 1) ^ 7 * (X 2) ^ 7
    + 1944 * (X 0) * (X 1) ^ 7 * (X 2) ^ 5

public noncomputable def quotJ_c20 : MvPolynomial (Fin 3) ℚ :=
  666 * (X 1) ^ 4 * (X 2) ^ 6
    + 666 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 1944 * (X 0) * (X 1) ^ 4 * (X 2) ^ 4
    - 666 * (X 1) ^ 3 * (X 2) ^ 6
    + 1944 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 1332 * (X 0) ^ 3 * (X 2) ^ 5
    - 1944 * (X 0) * (X 1) ^ 3 * (X 2) ^ 4
    - 666 * (X 0) * (X 1) * (X 2) ^ 6
    + 666 * (X 1) ^ 2 * (X 2) ^ 6
    - 3888 * (X 0) ^ 4 * (X 2) ^ 3
    - 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 1944 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 1332 * (X 0) * (X 2) ^ 6
    - 666 * (X 1) ^ 2 * (X 2) ^ 5
    + 3888 * (X 0) ^ 2 * (X 2) ^ 4
    - 1944 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 1332 * (X 1) * (X 2) ^ 5
    - 666 * (X 2) ^ 6
    + 3888 * (X 0) * (X 1) * (X 2) ^ 3
    - 1944 * (X 0) * (X 2) ^ 4
    - 1998 * (X 2) ^ 5
    - 5832 * (X 0) * (X 2) ^ 3
    + 666 * (X 2) ^ 4
    + 1944 * (X 0) * (X 2) ^ 2

public noncomputable def redJ_c20 : MvPolynomial (Fin 3) ℚ :=
  666 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    + 1944 * (X 0) ^ 7 * (X 1) * (X 2) ^ 3
    - 1332 * (X 0) ^ 6 * (X 2) ^ 5
    - 1332 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 1998 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 3888 * (X 0) ^ 7 * (X 2) ^ 3
    - 3888 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    + 5832 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 2664 * (X 0) ^ 4 * (X 2) ^ 6
    - 1332 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 666 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 666 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 1998 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 7776 * (X 0) ^ 5 * (X 2) ^ 4
    - 3888 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    + 1944 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 4608 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 1998 * (X 0) ^ 3 * (X 2) ^ 6
    - 5832 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    - 1332 * (X 0) ^ 2 * (X 2) ^ 7
    + 1332 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 666 * (X 0) * (X 1) * (X 2) ^ 7
    + 1332 * (X 1) ^ 2 * (X 2) ^ 7
    + 7776 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 5832 * (X 0) ^ 4 * (X 2) ^ 4
    - 5886 * (X 0) ^ 3 * (X 2) ^ 5
    + 3888 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 4
    - 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 3888 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 2664 * (X 0) * (X 1) * (X 2) ^ 6
    + 1998 * (X 0) * (X 2) ^ 7
    + 1332 * (X 1) ^ 2 * (X 2) ^ 6
    - 5832 * (X 0) ^ 4 * (X 2) ^ 3
    + 666 * (X 0) ^ 3 * (X 2) ^ 4
    - 7776 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 5832 * (X 0) ^ 2 * (X 2) ^ 5
    + 3888 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 1998 * (X 0) * (X 2) ^ 6
    - 1998 * (X 1) ^ 2 * (X 2) ^ 5
    + 1998 * (X 1) * (X 2) ^ 6
    - 666 * (X 2) ^ 7
    + 1944 * (X 0) ^ 4 * (X 2) ^ 2
    + 5832 * (X 0) ^ 2 * (X 2) ^ 4
    - 5832 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 5832 * (X 0) * (X 1) * (X 2) ^ 4
    - 2610 * (X 0) * (X 2) ^ 5
    + 1998 * (X 1) * (X 2) ^ 5
    - 1998 * (X 2) ^ 6
    - 1944 * (X 0) ^ 2 * (X 2) ^ 3
    + 5832 * (X 0) * (X 1) * (X 2) ^ 3
    - 5832 * (X 0) * (X 2) ^ 4
    - 666 * (X 1) * (X 2) ^ 4
    + 666 * (X 2) ^ 5
    - 1944 * (X 0) * (X 1) * (X 2) ^ 2
    + 1944 * (X 0) * (X 2) ^ 3

public noncomputable def jAff_c21 : MvPolynomial (Fin 3) ℚ :=
  5400 * (X 1) ^ 7 * (X 2) ^ 6
    - 5211 * (X 1) ^ 7 * (X 2) ^ 5

public noncomputable def quotJ_c21 : MvPolynomial (Fin 3) ℚ :=
  5400 * (X 1) ^ 4 * (X 2) ^ 5
    + 5400 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 5211 * (X 1) ^ 4 * (X 2) ^ 4
    - 5400 * (X 1) ^ 3 * (X 2) ^ 5
    - 5211 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 10800 * (X 0) ^ 3 * (X 2) ^ 4
    - 5400 * (X 0) * (X 1) * (X 2) ^ 5
    + 5211 * (X 1) ^ 3 * (X 2) ^ 4
    + 5400 * (X 1) ^ 2 * (X 2) ^ 5
    + 10422 * (X 0) ^ 3 * (X 2) ^ 3
    + 5211 * (X 0) * (X 1) * (X 2) ^ 4
    + 10800 * (X 0) * (X 2) ^ 5
    - 10611 * (X 1) ^ 2 * (X 2) ^ 4
    - 10422 * (X 0) * (X 2) ^ 4
    + 5211 * (X 1) ^ 2 * (X 2) ^ 3
    + 10800 * (X 1) * (X 2) ^ 4
    - 5400 * (X 2) ^ 5
    - 10422 * (X 1) * (X 2) ^ 3
    - 10989 * (X 2) ^ 4
    + 21033 * (X 2) ^ 3
    - 5211 * (X 2) ^ 2

public noncomputable def redJ_c21 : MvPolynomial (Fin 3) ℚ :=
  5400 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    - 5211 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    - 10800 * (X 0) ^ 6 * (X 2) ^ 4
    - 10800 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 16200 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 10422 * (X 0) ^ 6 * (X 2) ^ 3
    + 10422 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 21600 * (X 0) ^ 4 * (X 2) ^ 5
    - 26433 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 5400 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 5400 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 16200 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 20844 * (X 0) ^ 4 * (X 2) ^ 4
    + 10422 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 16389 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 16200 * (X 0) ^ 3 * (X 2) ^ 5
    - 5211 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 10800 * (X 0) ^ 2 * (X 2) ^ 6
    + 26433 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 5400 * (X 0) * (X 1) * (X 2) ^ 6
    + 10800 * (X 1) ^ 2 * (X 2) ^ 6
    - 20844 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 567 * (X 0) ^ 3 * (X 2) ^ 4
    + 10422 * (X 0) ^ 2 * (X 2) ^ 5
    - 10422 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 16389 * (X 0) * (X 1) * (X 2) ^ 5
    + 16200 * (X 0) * (X 2) ^ 6
    + 378 * (X 1) ^ 2 * (X 2) ^ 5
    + 21033 * (X 0) ^ 3 * (X 2) ^ 3
    + 20844 * (X 0) * (X 1) * (X 2) ^ 4
    + 567 * (X 0) * (X 2) ^ 5
    - 26622 * (X 1) ^ 2 * (X 2) ^ 4
    + 16200 * (X 1) * (X 2) ^ 5
    - 5400 * (X 2) ^ 6
    - 5211 * (X 0) ^ 3 * (X 2) ^ 2
    - 21033 * (X 0) * (X 2) ^ 4
    + 15633 * (X 1) ^ 2 * (X 2) ^ 3
    + 567 * (X 1) * (X 2) ^ 4
    - 10989 * (X 2) ^ 5
    + 5211 * (X 0) * (X 2) ^ 3
    - 21033 * (X 1) * (X 2) ^ 3
    + 21033 * (X 2) ^ 4
    + 5211 * (X 1) * (X 2) ^ 2
    - 5211 * (X 2) ^ 3

public noncomputable def jAff_c22 : MvPolynomial (Fin 3) ℚ :=
  -648 * (X 1) ^ 7 * (X 2) ^ 4

public noncomputable def quotJ_c22 : MvPolynomial (Fin 3) ℚ :=
  -648 * (X 1) ^ 4 * (X 2) ^ 3
    - 648 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 648 * (X 1) ^ 3 * (X 2) ^ 3
    + 1296 * (X 0) ^ 3 * (X 2) ^ 2
    + 648 * (X 0) * (X 1) * (X 2) ^ 3
    - 648 * (X 1) ^ 2 * (X 2) ^ 3
    - 1296 * (X 0) * (X 2) ^ 3
    + 648 * (X 1) ^ 2 * (X 2) ^ 2
    - 1296 * (X 1) * (X 2) ^ 2
    + 648 * (X 2) ^ 3
    + 1944 * (X 2) ^ 2
    - 648 * (X 2)

public noncomputable def redJ_c22 : MvPolynomial (Fin 3) ℚ :=
  -648 * (X 0) ^ 6 * (X 1) * (X 2) ^ 2
    + 1296 * (X 0) ^ 6 * (X 2) ^ 2
    + 1296 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 1944 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 2592 * (X 0) ^ 4 * (X 2) ^ 3
    + 1296 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    - 648 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 648 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 1944 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 2592 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 1944 * (X 0) ^ 3 * (X 2) ^ 3
    + 1296 * (X 0) ^ 2 * (X 2) ^ 4
    - 1296 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 648 * (X 0) * (X 1) * (X 2) ^ 4
    - 1296 * (X 1) ^ 2 * (X 2) ^ 4
    + 1944 * (X 0) ^ 3 * (X 2) ^ 2
    + 2592 * (X 0) * (X 1) * (X 2) ^ 3
    - 1944 * (X 0) * (X 2) ^ 4
    - 1296 * (X 1) ^ 2 * (X 2) ^ 3
    - 648 * (X 0) ^ 3 * (X 2)
    - 1944 * (X 0) * (X 2) ^ 3
    + 1944 * (X 1) ^ 2 * (X 2) ^ 2
    - 1944 * (X 1) * (X 2) ^ 3
    + 648 * (X 2) ^ 4
    + 648 * (X 0) * (X 2) ^ 2
    - 1944 * (X 1) * (X 2) ^ 2
    + 1944 * (X 2) ^ 3
    + 648 * (X 1) * (X 2)
    - 648 * (X 2) ^ 2

public noncomputable def jAff_c23 : MvPolynomial (Fin 3) ℚ :=
  -2700 * (X 0) ^ 3 * (X 1) ^ 6 * (X 2) ^ 9
    + 1944 * (X 0) ^ 2 * (X 1) ^ 6 * (X 2) ^ 10

public noncomputable def quotJ_c23 : MvPolynomial (Fin 3) ℚ :=
  -2700 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 8
    + 1944 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 9
    - 2700 * (X 0) ^ 6 * (X 2) ^ 7
    + 1944 * (X 0) ^ 5 * (X 2) ^ 8
    + 2700 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    - 1944 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 2700 * (X 0) ^ 4 * (X 2) ^ 8
    - 2700 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 1944 * (X 0) ^ 3 * (X 2) ^ 9
    + 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 2700 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 5400 * (X 0) ^ 3 * (X 2) ^ 7
    + 3888 * (X 0) ^ 2 * (X 2) ^ 8

public noncomputable def redJ_c23 : MvPolynomial (Fin 3) ℚ :=
  -2700 * (X 0) ^ 9 * (X 2) ^ 7
    + 1944 * (X 0) ^ 8 * (X 2) ^ 8
    + 5400 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 8
    - 3888 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 9
    + 5400 * (X 0) ^ 7 * (X 2) ^ 8
    - 2700 * (X 0) ^ 6 * (X 1) * (X 2) ^ 8
    - 3888 * (X 0) ^ 6 * (X 2) ^ 9
    + 1944 * (X 0) ^ 5 * (X 1) * (X 2) ^ 9
    - 5400 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    + 3888 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 10
    + 5400 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    - 2700 * (X 0) ^ 6 * (X 2) ^ 8
    - 3888 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    - 756 * (X 0) ^ 5 * (X 2) ^ 9
    + 2700 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    + 1944 * (X 0) ^ 4 * (X 2) ^ 10
    + 2700 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    - 1944 * (X 0) ^ 3 * (X 1) * (X 2) ^ 10
    - 1944 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 10
    - 5400 * (X 0) ^ 6 * (X 2) ^ 7
    + 3888 * (X 0) ^ 5 * (X 2) ^ 8
    - 5400 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 2700 * (X 0) ^ 4 * (X 2) ^ 9
    + 8100 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 1188 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    - 1944 * (X 0) ^ 3 * (X 2) ^ 10
    - 5832 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    + 5400 * (X 0) ^ 4 * (X 2) ^ 8
    - 2700 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 2700 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 3888 * (X 0) ^ 3 * (X 2) ^ 9
    + 1944 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 5400 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 5400 * (X 0) ^ 3 * (X 2) ^ 8
    - 3888 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 3888 * (X 0) ^ 2 * (X 2) ^ 9

public noncomputable def jAff_c24 : MvPolynomial (Fin 3) ℚ :=
  14553 * (X 0) ^ 3 * (X 1) ^ 6 * (X 2) ^ 8
    - 11322 * (X 0) ^ 2 * (X 1) ^ 6 * (X 2) ^ 9

public noncomputable def quotJ_c24 : MvPolynomial (Fin 3) ℚ :=
  14553 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 7
    - 11322 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 8
    + 14553 * (X 0) ^ 6 * (X 2) ^ 6
    - 11322 * (X 0) ^ 5 * (X 2) ^ 7
    - 14553 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 11322 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 14553 * (X 0) ^ 4 * (X 2) ^ 7
    + 14553 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 11322 * (X 0) ^ 3 * (X 2) ^ 8
    - 11322 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 14553 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 11322 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 29106 * (X 0) ^ 3 * (X 2) ^ 6
    - 22644 * (X 0) ^ 2 * (X 2) ^ 7

public noncomputable def redJ_c24 : MvPolynomial (Fin 3) ℚ :=
  14553 * (X 0) ^ 9 * (X 2) ^ 6
    - 11322 * (X 0) ^ 8 * (X 2) ^ 7
    - 29106 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 7
    + 22644 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 8
    - 29106 * (X 0) ^ 7 * (X 2) ^ 7
    + 14553 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    + 22644 * (X 0) ^ 6 * (X 2) ^ 8
    - 11322 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    + 29106 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    - 22644 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    - 29106 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    + 14553 * (X 0) ^ 6 * (X 2) ^ 7
    + 22644 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    + 3231 * (X 0) ^ 5 * (X 2) ^ 8
    - 14553 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 11322 * (X 0) ^ 4 * (X 2) ^ 9
    - 14553 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 11322 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    + 11322 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 29106 * (X 0) ^ 6 * (X 2) ^ 6
    - 22644 * (X 0) ^ 5 * (X 2) ^ 7
    + 29106 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 14553 * (X 0) ^ 4 * (X 2) ^ 8
    - 43659 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 8091 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 11322 * (X 0) ^ 3 * (X 2) ^ 9
    + 33966 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 11322 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 29106 * (X 0) ^ 4 * (X 2) ^ 7
    + 14553 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 14553 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 22644 * (X 0) ^ 3 * (X 2) ^ 8
    - 11322 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 11322 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 29106 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 29106 * (X 0) ^ 3 * (X 2) ^ 7
    + 22644 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 22644 * (X 0) ^ 2 * (X 2) ^ 8

public noncomputable def jAff_c25 : MvPolynomial (Fin 3) ℚ :=
  -4212 * (X 0) * (X 1) ^ 6 * (X 2) ^ 10
    - 216 * (X 1) ^ 6 * (X 2) ^ 11

public noncomputable def quotJ_c25 : MvPolynomial (Fin 3) ℚ :=
  -4212 * (X 0) * (X 1) ^ 3 * (X 2) ^ 9
    - 216 * (X 1) ^ 3 * (X 2) ^ 10
    - 4212 * (X 0) ^ 4 * (X 2) ^ 8
    - 216 * (X 0) ^ 3 * (X 2) ^ 9
    + 4212 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    + 216 * (X 1) ^ 2 * (X 2) ^ 10
    + 4212 * (X 0) ^ 2 * (X 2) ^ 9
    - 4212 * (X 0) * (X 1) * (X 2) ^ 9
    + 216 * (X 0) * (X 2) ^ 10
    - 216 * (X 1) * (X 2) ^ 10
    + 4212 * (X 0) * (X 1) * (X 2) ^ 8
    + 216 * (X 1) * (X 2) ^ 9
    - 8424 * (X 0) * (X 2) ^ 8
    - 432 * (X 2) ^ 9

public noncomputable def redJ_c25 : MvPolynomial (Fin 3) ℚ :=
  -4212 * (X 0) ^ 7 * (X 2) ^ 8
    - 216 * (X 0) ^ 6 * (X 2) ^ 9
    + 8424 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    + 432 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 10
    + 8424 * (X 0) ^ 5 * (X 2) ^ 9
    - 4212 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    + 432 * (X 0) ^ 4 * (X 2) ^ 10
    - 216 * (X 0) ^ 3 * (X 1) * (X 2) ^ 10
    - 8424 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 10
    - 432 * (X 0) * (X 1) ^ 2 * (X 2) ^ 11
    + 8424 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 4212 * (X 0) ^ 4 * (X 2) ^ 9
    + 432 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    - 4428 * (X 0) ^ 3 * (X 2) ^ 10
    + 4212 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    - 216 * (X 0) ^ 2 * (X 2) ^ 11
    + 4212 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    + 216 * (X 0) * (X 1) * (X 2) ^ 11
    + 216 * (X 1) ^ 2 * (X 2) ^ 11
    - 8424 * (X 0) ^ 4 * (X 2) ^ 8
    - 432 * (X 0) ^ 3 * (X 2) ^ 9
    - 8424 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 4212 * (X 0) ^ 2 * (X 2) ^ 10
    + 12636 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 4644 * (X 0) * (X 1) * (X 2) ^ 10
    + 216 * (X 0) * (X 2) ^ 11
    + 648 * (X 1) ^ 2 * (X 2) ^ 10
    - 216 * (X 1) * (X 2) ^ 11
    + 8424 * (X 0) ^ 2 * (X 2) ^ 9
    - 4212 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 4212 * (X 0) * (X 1) * (X 2) ^ 9
    + 432 * (X 0) * (X 2) ^ 10
    - 216 * (X 1) ^ 2 * (X 2) ^ 9
    + 216 * (X 1) * (X 2) ^ 10
    + 8424 * (X 0) * (X 1) * (X 2) ^ 8
    - 8424 * (X 0) * (X 2) ^ 9
    + 432 * (X 1) * (X 2) ^ 9
    - 432 * (X 2) ^ 10

public noncomputable def jAff_c26 : MvPolynomial (Fin 3) ℚ :=
  17739 * (X 0) ^ 3 * (X 1) ^ 6 * (X 2) ^ 7
    - 7452 * (X 0) ^ 2 * (X 1) ^ 6 * (X 2) ^ 8

public noncomputable def quotJ_c26 : MvPolynomial (Fin 3) ℚ :=
  17739 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 6
    - 7452 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 7
    + 17739 * (X 0) ^ 6 * (X 2) ^ 5
    - 7452 * (X 0) ^ 5 * (X 2) ^ 6
    - 17739 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 7452 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    - 17739 * (X 0) ^ 4 * (X 2) ^ 6
    + 17739 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 7452 * (X 0) ^ 3 * (X 2) ^ 7
    - 7452 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 17739 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 7452 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    + 35478 * (X 0) ^ 3 * (X 2) ^ 5
    - 14904 * (X 0) ^ 2 * (X 2) ^ 6

public noncomputable def redJ_c26 : MvPolynomial (Fin 3) ℚ :=
  17739 * (X 0) ^ 9 * (X 2) ^ 5
    - 7452 * (X 0) ^ 8 * (X 2) ^ 6
    - 35478 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 6
    + 14904 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 7
    - 35478 * (X 0) ^ 7 * (X 2) ^ 6
    + 17739 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    + 14904 * (X 0) ^ 6 * (X 2) ^ 7
    - 7452 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    + 35478 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 14904 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    - 35478 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    + 17739 * (X 0) ^ 6 * (X 2) ^ 6
    + 14904 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    + 10287 * (X 0) ^ 5 * (X 2) ^ 7
    - 17739 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 7452 * (X 0) ^ 4 * (X 2) ^ 8
    - 17739 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 7452 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 7452 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    + 35478 * (X 0) ^ 6 * (X 2) ^ 5
    - 14904 * (X 0) ^ 5 * (X 2) ^ 6
    + 35478 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 17739 * (X 0) ^ 4 * (X 2) ^ 7
    - 53217 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 2835 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 7452 * (X 0) ^ 3 * (X 2) ^ 8
    + 22356 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    - 7452 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 35478 * (X 0) ^ 4 * (X 2) ^ 6
    + 17739 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 17739 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 14904 * (X 0) ^ 3 * (X 2) ^ 7
    - 7452 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 7452 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 35478 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 35478 * (X 0) ^ 3 * (X 2) ^ 6
    + 14904 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 14904 * (X 0) ^ 2 * (X 2) ^ 7

public noncomputable def jAff_c27 : MvPolynomial (Fin 3) ℚ :=
  29295 * (X 0) * (X 1) ^ 6 * (X 2) ^ 9
    + 6042 * (X 1) ^ 6 * (X 2) ^ 10

public noncomputable def quotJ_c27 : MvPolynomial (Fin 3) ℚ :=
  29295 * (X 0) * (X 1) ^ 3 * (X 2) ^ 8
    + 6042 * (X 1) ^ 3 * (X 2) ^ 9
    + 29295 * (X 0) ^ 4 * (X 2) ^ 7
    + 6042 * (X 0) ^ 3 * (X 2) ^ 8
    - 29295 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 6042 * (X 1) ^ 2 * (X 2) ^ 9
    - 29295 * (X 0) ^ 2 * (X 2) ^ 8
    + 29295 * (X 0) * (X 1) * (X 2) ^ 8
    - 6042 * (X 0) * (X 2) ^ 9
    + 6042 * (X 1) * (X 2) ^ 9
    - 29295 * (X 0) * (X 1) * (X 2) ^ 7
    - 6042 * (X 1) * (X 2) ^ 8
    + 58590 * (X 0) * (X 2) ^ 7
    + 12084 * (X 2) ^ 8

public noncomputable def redJ_c27 : MvPolynomial (Fin 3) ℚ :=
  29295 * (X 0) ^ 7 * (X 2) ^ 7
    + 6042 * (X 0) ^ 6 * (X 2) ^ 8
    - 58590 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    - 12084 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    - 58590 * (X 0) ^ 5 * (X 2) ^ 8
    + 29295 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 12084 * (X 0) ^ 4 * (X 2) ^ 9
    + 6042 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    + 58590 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 12084 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    - 58590 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 29295 * (X 0) ^ 4 * (X 2) ^ 8
    - 12084 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 35337 * (X 0) ^ 3 * (X 2) ^ 9
    - 29295 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 6042 * (X 0) ^ 2 * (X 2) ^ 10
    - 29295 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 6042 * (X 0) * (X 1) * (X 2) ^ 10
    - 6042 * (X 1) ^ 2 * (X 2) ^ 10
    + 58590 * (X 0) ^ 4 * (X 2) ^ 7
    + 12084 * (X 0) ^ 3 * (X 2) ^ 8
    + 58590 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 29295 * (X 0) ^ 2 * (X 2) ^ 9
    - 87885 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 41379 * (X 0) * (X 1) * (X 2) ^ 9
    - 6042 * (X 0) * (X 2) ^ 10
    - 18126 * (X 1) ^ 2 * (X 2) ^ 9
    + 6042 * (X 1) * (X 2) ^ 10
    - 58590 * (X 0) ^ 2 * (X 2) ^ 8
    + 29295 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 29295 * (X 0) * (X 1) * (X 2) ^ 8
    - 12084 * (X 0) * (X 2) ^ 9
    + 6042 * (X 1) ^ 2 * (X 2) ^ 8
    - 6042 * (X 1) * (X 2) ^ 9
    - 58590 * (X 0) * (X 1) * (X 2) ^ 7
    + 58590 * (X 0) * (X 2) ^ 8
    - 12084 * (X 1) * (X 2) ^ 8
    + 12084 * (X 2) ^ 9

public noncomputable def jAff_c28 : MvPolynomial (Fin 3) ℚ :=
  3699 * (X 0) ^ 3 * (X 1) ^ 6 * (X 2) ^ 6
    - 3402 * (X 0) ^ 2 * (X 1) ^ 6 * (X 2) ^ 7

public noncomputable def quotJ_c28 : MvPolynomial (Fin 3) ℚ :=
  3699 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 5
    - 3402 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 6
    + 3699 * (X 0) ^ 6 * (X 2) ^ 4
    - 3402 * (X 0) ^ 5 * (X 2) ^ 5
    - 3699 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 3402 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 3699 * (X 0) ^ 4 * (X 2) ^ 5
    + 3699 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 3402 * (X 0) ^ 3 * (X 2) ^ 6
    - 3402 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 3699 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 3402 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 7398 * (X 0) ^ 3 * (X 2) ^ 4
    - 6804 * (X 0) ^ 2 * (X 2) ^ 5

public noncomputable def redJ_c28 : MvPolynomial (Fin 3) ℚ :=
  3699 * (X 0) ^ 9 * (X 2) ^ 4
    - 3402 * (X 0) ^ 8 * (X 2) ^ 5
    - 7398 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 5
    + 6804 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    - 7398 * (X 0) ^ 7 * (X 2) ^ 5
    + 3699 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    + 6804 * (X 0) ^ 6 * (X 2) ^ 6
    - 3402 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    + 7398 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 6804 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 7398 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    + 3699 * (X 0) ^ 6 * (X 2) ^ 5
    + 6804 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 297 * (X 0) ^ 5 * (X 2) ^ 6
    - 3699 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 3402 * (X 0) ^ 4 * (X 2) ^ 7
    - 3699 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 3402 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 3402 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 7398 * (X 0) ^ 6 * (X 2) ^ 4
    - 6804 * (X 0) ^ 5 * (X 2) ^ 5
    + 7398 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 3699 * (X 0) ^ 4 * (X 2) ^ 6
    - 11097 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 3105 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 3402 * (X 0) ^ 3 * (X 2) ^ 7
    + 10206 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 3402 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 7398 * (X 0) ^ 4 * (X 2) ^ 5
    + 3699 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 3699 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 6804 * (X 0) ^ 3 * (X 2) ^ 6
    - 3402 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 3402 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 7398 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 7398 * (X 0) ^ 3 * (X 2) ^ 5
    + 6804 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 6804 * (X 0) ^ 2 * (X 2) ^ 6

public noncomputable def jAff_c29 : MvPolynomial (Fin 3) ℚ :=
  -12879 * (X 0) * (X 1) ^ 6 * (X 2) ^ 8
    - 33660 * (X 1) ^ 6 * (X 2) ^ 9

public noncomputable def quotJ_c29 : MvPolynomial (Fin 3) ℚ :=
  -12879 * (X 0) * (X 1) ^ 3 * (X 2) ^ 7
    - 33660 * (X 1) ^ 3 * (X 2) ^ 8
    - 12879 * (X 0) ^ 4 * (X 2) ^ 6
    - 33660 * (X 0) ^ 3 * (X 2) ^ 7
    + 12879 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 33660 * (X 1) ^ 2 * (X 2) ^ 8
    + 12879 * (X 0) ^ 2 * (X 2) ^ 7
    - 12879 * (X 0) * (X 1) * (X 2) ^ 7
    + 33660 * (X 0) * (X 2) ^ 8
    - 33660 * (X 1) * (X 2) ^ 8
    + 12879 * (X 0) * (X 1) * (X 2) ^ 6
    + 33660 * (X 1) * (X 2) ^ 7
    - 25758 * (X 0) * (X 2) ^ 6
    - 67320 * (X 2) ^ 7

public noncomputable def redJ_c29 : MvPolynomial (Fin 3) ℚ :=
  -12879 * (X 0) ^ 7 * (X 2) ^ 6
    - 33660 * (X 0) ^ 6 * (X 2) ^ 7
    + 25758 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    + 67320 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 25758 * (X 0) ^ 5 * (X 2) ^ 7
    - 12879 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 67320 * (X 0) ^ 4 * (X 2) ^ 8
    - 33660 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 25758 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 67320 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    + 25758 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 12879 * (X 0) ^ 4 * (X 2) ^ 7
    + 67320 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 46539 * (X 0) ^ 3 * (X 2) ^ 8
    + 12879 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 33660 * (X 0) ^ 2 * (X 2) ^ 9
    + 12879 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 33660 * (X 0) * (X 1) * (X 2) ^ 9
    + 33660 * (X 1) ^ 2 * (X 2) ^ 9
    - 25758 * (X 0) ^ 4 * (X 2) ^ 6
    - 67320 * (X 0) ^ 3 * (X 2) ^ 7
    - 25758 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 12879 * (X 0) ^ 2 * (X 2) ^ 8
    + 38637 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 80199 * (X 0) * (X 1) * (X 2) ^ 8
    + 33660 * (X 0) * (X 2) ^ 9
    + 100980 * (X 1) ^ 2 * (X 2) ^ 8
    - 33660 * (X 1) * (X 2) ^ 9
    + 25758 * (X 0) ^ 2 * (X 2) ^ 7
    - 12879 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 12879 * (X 0) * (X 1) * (X 2) ^ 7
    + 67320 * (X 0) * (X 2) ^ 8
    - 33660 * (X 1) ^ 2 * (X 2) ^ 7
    + 33660 * (X 1) * (X 2) ^ 8
    + 25758 * (X 0) * (X 1) * (X 2) ^ 6
    - 25758 * (X 0) * (X 2) ^ 7
    + 67320 * (X 1) * (X 2) ^ 7
    - 67320 * (X 2) ^ 8

public noncomputable def jAff_c30 : MvPolynomial (Fin 3) ℚ :=
  2457 * (X 0) ^ 3 * (X 1) ^ 6 * (X 2) ^ 5
    + 1944 * (X 0) ^ 2 * (X 1) ^ 6 * (X 2) ^ 6

public noncomputable def quotJ_c30 : MvPolynomial (Fin 3) ℚ :=
  2457 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 4
    + 1944 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 5
    + 2457 * (X 0) ^ 6 * (X 2) ^ 3
    + 1944 * (X 0) ^ 5 * (X 2) ^ 4
    - 2457 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 1944 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    - 2457 * (X 0) ^ 4 * (X 2) ^ 4
    + 2457 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 1944 * (X 0) ^ 3 * (X 2) ^ 5
    + 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 2457 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 4914 * (X 0) ^ 3 * (X 2) ^ 3
    + 3888 * (X 0) ^ 2 * (X 2) ^ 4

public noncomputable def redJ_c30 : MvPolynomial (Fin 3) ℚ :=
  2457 * (X 0) ^ 9 * (X 2) ^ 3
    + 1944 * (X 0) ^ 8 * (X 2) ^ 4
    - 4914 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 4
    - 3888 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 5
    - 4914 * (X 0) ^ 7 * (X 2) ^ 4
    + 2457 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    - 3888 * (X 0) ^ 6 * (X 2) ^ 5
    + 1944 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 4914 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    + 3888 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 4914 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    + 2457 * (X 0) ^ 6 * (X 2) ^ 4
    - 3888 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    + 4401 * (X 0) ^ 5 * (X 2) ^ 5
    - 2457 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 1944 * (X 0) ^ 4 * (X 2) ^ 6
    - 2457 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 1944 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 1944 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 4914 * (X 0) ^ 6 * (X 2) ^ 3
    + 3888 * (X 0) ^ 5 * (X 2) ^ 4
    + 4914 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 2457 * (X 0) ^ 4 * (X 2) ^ 5
    - 7371 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 6345 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 1944 * (X 0) ^ 3 * (X 2) ^ 6
    - 5832 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 4914 * (X 0) ^ 4 * (X 2) ^ 4
    + 2457 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 2457 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 3888 * (X 0) ^ 3 * (X 2) ^ 5
    + 1944 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 4
    - 1944 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 4914 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 4914 * (X 0) ^ 3 * (X 2) ^ 4
    - 3888 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 3888 * (X 0) ^ 2 * (X 2) ^ 5

public noncomputable def jAff_c31 : MvPolynomial (Fin 3) ℚ :=
  10377 * (X 0) * (X 1) ^ 6 * (X 2) ^ 7
    + 22248 * (X 1) ^ 6 * (X 2) ^ 8

public noncomputable def quotJ_c31 : MvPolynomial (Fin 3) ℚ :=
  10377 * (X 0) * (X 1) ^ 3 * (X 2) ^ 6
    + 22248 * (X 1) ^ 3 * (X 2) ^ 7
    + 10377 * (X 0) ^ 4 * (X 2) ^ 5
    + 22248 * (X 0) ^ 3 * (X 2) ^ 6
    - 10377 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 22248 * (X 1) ^ 2 * (X 2) ^ 7
    - 10377 * (X 0) ^ 2 * (X 2) ^ 6
    + 10377 * (X 0) * (X 1) * (X 2) ^ 6
    - 22248 * (X 0) * (X 2) ^ 7
    + 22248 * (X 1) * (X 2) ^ 7
    - 10377 * (X 0) * (X 1) * (X 2) ^ 5
    - 22248 * (X 1) * (X 2) ^ 6
    + 20754 * (X 0) * (X 2) ^ 5
    + 44496 * (X 2) ^ 6

public noncomputable def redJ_c31 : MvPolynomial (Fin 3) ℚ :=
  10377 * (X 0) ^ 7 * (X 2) ^ 5
    + 22248 * (X 0) ^ 6 * (X 2) ^ 6
    - 20754 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 44496 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 20754 * (X 0) ^ 5 * (X 2) ^ 6
    + 10377 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 44496 * (X 0) ^ 4 * (X 2) ^ 7
    + 22248 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 20754 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 44496 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 20754 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 10377 * (X 0) ^ 4 * (X 2) ^ 6
    - 44496 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 32625 * (X 0) ^ 3 * (X 2) ^ 7
    - 10377 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 22248 * (X 0) ^ 2 * (X 2) ^ 8
    - 10377 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 22248 * (X 0) * (X 1) * (X 2) ^ 8
    - 22248 * (X 1) ^ 2 * (X 2) ^ 8
    + 20754 * (X 0) ^ 4 * (X 2) ^ 5
    + 44496 * (X 0) ^ 3 * (X 2) ^ 6
    + 20754 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 10377 * (X 0) ^ 2 * (X 2) ^ 7
    - 31131 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 54873 * (X 0) * (X 1) * (X 2) ^ 7
    - 22248 * (X 0) * (X 2) ^ 8
    - 66744 * (X 1) ^ 2 * (X 2) ^ 7
    + 22248 * (X 1) * (X 2) ^ 8
    - 20754 * (X 0) ^ 2 * (X 2) ^ 6
    + 10377 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 10377 * (X 0) * (X 1) * (X 2) ^ 6
    - 44496 * (X 0) * (X 2) ^ 7
    + 22248 * (X 1) ^ 2 * (X 2) ^ 6
    - 22248 * (X 1) * (X 2) ^ 7
    - 20754 * (X 0) * (X 1) * (X 2) ^ 5
    + 20754 * (X 0) * (X 2) ^ 6
    - 44496 * (X 1) * (X 2) ^ 6
    + 44496 * (X 2) ^ 7

public noncomputable def jAff_c32 : MvPolynomial (Fin 3) ℚ :=
  972 * (X 0) ^ 3 * (X 1) ^ 6 * (X 2) ^ 4
    - 16821 * (X 0) * (X 1) ^ 6 * (X 2) ^ 6

public noncomputable def quotJ_c32 : MvPolynomial (Fin 3) ℚ :=
  972 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 3
    - 16821 * (X 0) * (X 1) ^ 3 * (X 2) ^ 5
    + 972 * (X 0) ^ 6 * (X 2) ^ 2
    - 16821 * (X 0) ^ 4 * (X 2) ^ 4
    - 972 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 16821 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 972 * (X 0) ^ 4 * (X 2) ^ 3
    + 972 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 16821 * (X 0) ^ 2 * (X 2) ^ 5
    - 16821 * (X 0) * (X 1) * (X 2) ^ 5
    - 972 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 16821 * (X 0) * (X 1) * (X 2) ^ 4
    + 1944 * (X 0) ^ 3 * (X 2) ^ 2
    - 33642 * (X 0) * (X 2) ^ 4

public noncomputable def redJ_c32 : MvPolynomial (Fin 3) ℚ :=
  972 * (X 0) ^ 9 * (X 2) ^ 2
    - 16821 * (X 0) ^ 7 * (X 2) ^ 4
    - 1944 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 3
    + 33642 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 1944 * (X 0) ^ 7 * (X 2) ^ 3
    + 972 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    + 33642 * (X 0) ^ 5 * (X 2) ^ 5
    + 1944 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 16821 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 33642 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 1944 * (X 0) ^ 6 * (X 1) * (X 2) ^ 2
    + 972 * (X 0) ^ 6 * (X 2) ^ 3
    + 972 * (X 0) ^ 5 * (X 2) ^ 4
    + 32670 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 16821 * (X 0) ^ 4 * (X 2) ^ 5
    - 972 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 16821 * (X 0) ^ 3 * (X 2) ^ 6
    + 16821 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    + 16821 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 1944 * (X 0) ^ 6 * (X 2) ^ 2
    + 1944 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 34614 * (X 0) ^ 4 * (X 2) ^ 4
    - 2916 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 972 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 33642 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 16821 * (X 0) ^ 2 * (X 2) ^ 6
    + 50463 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 16821 * (X 0) * (X 1) * (X 2) ^ 6
    - 1944 * (X 0) ^ 4 * (X 2) ^ 3
    + 972 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    - 972 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 33642 * (X 0) ^ 2 * (X 2) ^ 5
    - 16821 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 16821 * (X 0) * (X 1) * (X 2) ^ 5
    - 1944 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 1944 * (X 0) ^ 3 * (X 2) ^ 3
    + 33642 * (X 0) * (X 1) * (X 2) ^ 4
    - 33642 * (X 0) * (X 2) ^ 5

public noncomputable def jAff_c33 : MvPolynomial (Fin 3) ℚ :=
  -13068 * (X 1) ^ 6 * (X 2) ^ 7
    - 1296 * (X 0) * (X 1) ^ 6 * (X 2) ^ 5

public noncomputable def quotJ_c33 : MvPolynomial (Fin 3) ℚ :=
  -13068 * (X 1) ^ 3 * (X 2) ^ 6
    - 13068 * (X 0) ^ 3 * (X 2) ^ 5
    - 1296 * (X 0) * (X 1) ^ 3 * (X 2) ^ 4
    + 13068 * (X 1) ^ 2 * (X 2) ^ 6
    - 1296 * (X 0) ^ 4 * (X 2) ^ 3
    + 1296 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 13068 * (X 0) * (X 2) ^ 6
    - 13068 * (X 1) * (X 2) ^ 6
    + 1296 * (X 0) ^ 2 * (X 2) ^ 4
    - 1296 * (X 0) * (X 1) * (X 2) ^ 4
    + 13068 * (X 1) * (X 2) ^ 5
    + 1296 * (X 0) * (X 1) * (X 2) ^ 3
    - 26136 * (X 2) ^ 5
    - 2592 * (X 0) * (X 2) ^ 3

public noncomputable def redJ_c33 : MvPolynomial (Fin 3) ℚ :=
  -13068 * (X 0) ^ 6 * (X 2) ^ 5
    + 26136 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 1296 * (X 0) ^ 7 * (X 2) ^ 3
    + 2592 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 26136 * (X 0) ^ 4 * (X 2) ^ 6
    - 13068 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 26136 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 2592 * (X 0) ^ 5 * (X 2) ^ 4
    - 1296 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 26136 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 13068 * (X 0) ^ 3 * (X 2) ^ 6
    - 2592 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    - 13068 * (X 0) ^ 2 * (X 2) ^ 7
    + 13068 * (X 0) * (X 1) * (X 2) ^ 7
    + 13068 * (X 1) ^ 2 * (X 2) ^ 7
    + 2592 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 1296 * (X 0) ^ 4 * (X 2) ^ 4
    - 27432 * (X 0) ^ 3 * (X 2) ^ 5
    + 1296 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 1296 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 26136 * (X 0) * (X 1) * (X 2) ^ 6
    + 13068 * (X 0) * (X 2) ^ 7
    + 39204 * (X 1) ^ 2 * (X 2) ^ 6
    - 13068 * (X 1) * (X 2) ^ 7
    - 2592 * (X 0) ^ 4 * (X 2) ^ 3
    - 2592 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 1296 * (X 0) ^ 2 * (X 2) ^ 5
    + 3888 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 1296 * (X 0) * (X 1) * (X 2) ^ 5
    + 26136 * (X 0) * (X 2) ^ 6
    - 13068 * (X 1) ^ 2 * (X 2) ^ 5
    + 13068 * (X 1) * (X 2) ^ 6
    + 2592 * (X 0) ^ 2 * (X 2) ^ 4
    - 1296 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 1296 * (X 0) * (X 1) * (X 2) ^ 4
    + 26136 * (X 1) * (X 2) ^ 5
    - 26136 * (X 2) ^ 6
    + 2592 * (X 0) * (X 1) * (X 2) ^ 3
    - 2592 * (X 0) * (X 2) ^ 4

public noncomputable def jAff_c34 : MvPolynomial (Fin 3) ℚ :=
  23808 * (X 1) ^ 6 * (X 2) ^ 6
    + 2700 * (X 1) ^ 6 * (X 2) ^ 5

public noncomputable def quotJ_c34 : MvPolynomial (Fin 3) ℚ :=
  23808 * (X 1) ^ 3 * (X 2) ^ 5
    + 23808 * (X 0) ^ 3 * (X 2) ^ 4
    + 2700 * (X 1) ^ 3 * (X 2) ^ 4
    - 23808 * (X 1) ^ 2 * (X 2) ^ 5
    + 2700 * (X 0) ^ 3 * (X 2) ^ 3
    - 23808 * (X 0) * (X 2) ^ 5
    - 2700 * (X 1) ^ 2 * (X 2) ^ 4
    + 23808 * (X 1) * (X 2) ^ 5
    - 2700 * (X 0) * (X 2) ^ 4
    - 21108 * (X 1) * (X 2) ^ 4
    - 2700 * (X 1) * (X 2) ^ 3
    + 47616 * (X 2) ^ 4
    + 5400 * (X 2) ^ 3

public noncomputable def redJ_c34 : MvPolynomial (Fin 3) ℚ :=
  23808 * (X 0) ^ 6 * (X 2) ^ 4
    - 47616 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 2700 * (X 0) ^ 6 * (X 2) ^ 3
    - 47616 * (X 0) ^ 4 * (X 2) ^ 5
    - 5400 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 23808 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 47616 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 5400 * (X 0) ^ 4 * (X 2) ^ 4
    - 44916 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 23808 * (X 0) ^ 3 * (X 2) ^ 5
    + 23808 * (X 0) ^ 2 * (X 2) ^ 6
    + 5400 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 23808 * (X 0) * (X 1) * (X 2) ^ 6
    - 23808 * (X 1) ^ 2 * (X 2) ^ 6
    - 5400 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 50316 * (X 0) ^ 3 * (X 2) ^ 4
    + 2700 * (X 0) ^ 2 * (X 2) ^ 5
    + 44916 * (X 0) * (X 1) * (X 2) ^ 5
    - 23808 * (X 0) * (X 2) ^ 6
    - 74124 * (X 1) ^ 2 * (X 2) ^ 5
    + 23808 * (X 1) * (X 2) ^ 6
    + 5400 * (X 0) ^ 3 * (X 2) ^ 3
    + 5400 * (X 0) * (X 1) * (X 2) ^ 4
    - 50316 * (X 0) * (X 2) ^ 5
    + 15708 * (X 1) ^ 2 * (X 2) ^ 4
    - 21108 * (X 1) * (X 2) ^ 5
    - 5400 * (X 0) * (X 2) ^ 4
    + 2700 * (X 1) ^ 2 * (X 2) ^ 3
    - 50316 * (X 1) * (X 2) ^ 4
    + 47616 * (X 2) ^ 5
    - 5400 * (X 1) * (X 2) ^ 3
    + 5400 * (X 2) ^ 4

public noncomputable def jAff_c35 : MvPolynomial (Fin 3) ℚ :=
  594 * (X 1) ^ 6 * (X 2) ^ 4
    - 432 * (X 1) ^ 6 * (X 2) ^ 3

public noncomputable def quotJ_c35 : MvPolynomial (Fin 3) ℚ :=
  594 * (X 1) ^ 3 * (X 2) ^ 3
    + 594 * (X 0) ^ 3 * (X 2) ^ 2
    - 432 * (X 1) ^ 3 * (X 2) ^ 2
    - 594 * (X 1) ^ 2 * (X 2) ^ 3
    - 432 * (X 0) ^ 3 * (X 2)
    - 594 * (X 0) * (X 2) ^ 3
    + 432 * (X 1) ^ 2 * (X 2) ^ 2
    + 594 * (X 1) * (X 2) ^ 3
    + 432 * (X 0) * (X 2) ^ 2
    - 1026 * (X 1) * (X 2) ^ 2
    + 432 * (X 1) * (X 2)
    + 1188 * (X 2) ^ 2
    - 864 * (X 2)

public noncomputable def redJ_c35 : MvPolynomial (Fin 3) ℚ :=
  594 * (X 0) ^ 6 * (X 2) ^ 2
    - 1188 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 432 * (X 0) ^ 6 * (X 2)
    - 1188 * (X 0) ^ 4 * (X 2) ^ 3
    + 864 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    + 594 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 1188 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 864 * (X 0) ^ 4 * (X 2) ^ 2
    - 1620 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 594 * (X 0) ^ 3 * (X 2) ^ 3
    + 594 * (X 0) ^ 2 * (X 2) ^ 4
    - 864 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    - 594 * (X 0) * (X 1) * (X 2) ^ 4
    - 594 * (X 1) ^ 2 * (X 2) ^ 4
    + 864 * (X 0) ^ 3 * (X 1) * (X 2)
    + 756 * (X 0) ^ 3 * (X 2) ^ 2
    - 432 * (X 0) ^ 2 * (X 2) ^ 3
    + 1620 * (X 0) * (X 1) * (X 2) ^ 3
    - 594 * (X 0) * (X 2) ^ 4
    - 1350 * (X 1) ^ 2 * (X 2) ^ 3
    + 594 * (X 1) * (X 2) ^ 4
    - 864 * (X 0) ^ 3 * (X 2)
    - 864 * (X 0) * (X 1) * (X 2) ^ 2
    - 756 * (X 0) * (X 2) ^ 3
    + 1890 * (X 1) ^ 2 * (X 2) ^ 2
    - 1026 * (X 1) * (X 2) ^ 3
    + 864 * (X 0) * (X 2) ^ 2
    - 432 * (X 1) ^ 2 * (X 2)
    - 756 * (X 1) * (X 2) ^ 2
    + 1188 * (X 2) ^ 3
    + 864 * (X 1) * (X 2)
    - 864 * (X 2) ^ 2

public noncomputable def jAff_c36 : MvPolynomial (Fin 3) ℚ :=
  450 * (X 0) ^ 4 * (X 1) ^ 5 * (X 2) ^ 8
    - 5184 * (X 0) ^ 3 * (X 1) ^ 5 * (X 2) ^ 9
    + 3888 * (X 0) ^ 2 * (X 1) ^ 5 * (X 2) ^ 10

public noncomputable def quotJ_c36 : MvPolynomial (Fin 3) ℚ :=
  450 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 5184 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 3888 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    - 450 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 5184 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 3888 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 450 * (X 0) ^ 4 * (X 2) ^ 7
    - 5184 * (X 0) ^ 3 * (X 2) ^ 8
    + 3888 * (X 0) ^ 2 * (X 2) ^ 9
    - 450 * (X 0) ^ 4 * (X 2) ^ 6
    + 5184 * (X 0) ^ 3 * (X 2) ^ 7
    - 3888 * (X 0) ^ 2 * (X 2) ^ 8

public noncomputable def redJ_c36 : MvPolynomial (Fin 3) ℚ :=
  450 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 7
    - 5184 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 8
    + 3888 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 9
    - 450 * (X 0) ^ 7 * (X 1) * (X 2) ^ 7
    + 5184 * (X 0) ^ 6 * (X 1) * (X 2) ^ 8
    - 450 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 8
    - 3888 * (X 0) ^ 5 * (X 1) * (X 2) ^ 9
    + 5184 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    - 3888 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 10
    + 450 * (X 0) ^ 7 * (X 2) ^ 7
    - 5184 * (X 0) ^ 6 * (X 2) ^ 8
    + 450 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    + 3888 * (X 0) ^ 5 * (X 2) ^ 9
    - 5184 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    + 3888 * (X 0) ^ 3 * (X 1) * (X 2) ^ 10
    - 450 * (X 0) ^ 7 * (X 2) ^ 6
    + 5184 * (X 0) ^ 6 * (X 2) ^ 7
    - 4338 * (X 0) ^ 5 * (X 2) ^ 8
    + 900 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 450 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 5184 * (X 0) ^ 4 * (X 2) ^ 9
    - 10368 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 5184 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    - 3888 * (X 0) ^ 3 * (X 2) ^ 10
    + 7776 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    - 3888 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    + 450 * (X 0) ^ 5 * (X 2) ^ 7
    - 450 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 4734 * (X 0) ^ 4 * (X 2) ^ 8
    + 5184 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 1296 * (X 0) ^ 3 * (X 2) ^ 9
    - 3888 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 3888 * (X 0) ^ 2 * (X 2) ^ 10
    + 450 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 450 * (X 0) ^ 4 * (X 2) ^ 7
    - 5184 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 5184 * (X 0) ^ 3 * (X 2) ^ 8
    + 3888 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 3888 * (X 0) ^ 2 * (X 2) ^ 9

public noncomputable def jAff_c37 : MvPolynomial (Fin 3) ℚ :=
  -2538 * (X 0) ^ 4 * (X 1) ^ 5 * (X 2) ^ 7
    + 29052 * (X 0) ^ 3 * (X 1) ^ 5 * (X 2) ^ 8
    - 25344 * (X 0) ^ 2 * (X 1) ^ 5 * (X 2) ^ 9

public noncomputable def quotJ_c37 : MvPolynomial (Fin 3) ℚ :=
  -2538 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    + 29052 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 25344 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    + 2538 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 29052 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 25344 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 2538 * (X 0) ^ 4 * (X 2) ^ 6
    + 29052 * (X 0) ^ 3 * (X 2) ^ 7
    - 25344 * (X 0) ^ 2 * (X 2) ^ 8
    + 2538 * (X 0) ^ 4 * (X 2) ^ 5
    - 29052 * (X 0) ^ 3 * (X 2) ^ 6
    + 25344 * (X 0) ^ 2 * (X 2) ^ 7

public noncomputable def redJ_c37 : MvPolynomial (Fin 3) ℚ :=
  -2538 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 6
    + 29052 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 7
    - 25344 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 8
    + 2538 * (X 0) ^ 7 * (X 1) * (X 2) ^ 6
    - 29052 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    + 2538 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 7
    + 25344 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    - 29052 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    + 25344 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    - 2538 * (X 0) ^ 7 * (X 2) ^ 6
    + 29052 * (X 0) ^ 6 * (X 2) ^ 7
    - 2538 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    - 25344 * (X 0) ^ 5 * (X 2) ^ 8
    + 29052 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 25344 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    + 2538 * (X 0) ^ 7 * (X 2) ^ 5
    - 29052 * (X 0) ^ 6 * (X 2) ^ 6
    + 27882 * (X 0) ^ 5 * (X 2) ^ 7
    - 5076 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    + 2538 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 29052 * (X 0) ^ 4 * (X 2) ^ 8
    + 58104 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 29052 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 25344 * (X 0) ^ 3 * (X 2) ^ 9
    - 50688 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    + 25344 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 2538 * (X 0) ^ 5 * (X 2) ^ 6
    + 2538 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 26514 * (X 0) ^ 4 * (X 2) ^ 7
    - 29052 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 3708 * (X 0) ^ 3 * (X 2) ^ 8
    + 25344 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 25344 * (X 0) ^ 2 * (X 2) ^ 9
    - 2538 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 2538 * (X 0) ^ 4 * (X 2) ^ 6
    + 29052 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 29052 * (X 0) ^ 3 * (X 2) ^ 7
    - 25344 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 25344 * (X 0) ^ 2 * (X 2) ^ 8

public noncomputable def jAff_c38 : MvPolynomial (Fin 3) ℚ :=
  -7056 * (X 0) * (X 1) ^ 5 * (X 2) ^ 10
    - 432 * (X 1) ^ 5 * (X 2) ^ 11
    + 3078 * (X 0) ^ 4 * (X 1) ^ 5 * (X 2) ^ 6

public noncomputable def quotJ_c38 : MvPolynomial (Fin 3) ℚ :=
  -7056 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 432 * (X 1) ^ 2 * (X 2) ^ 10
    + 3078 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    + 7056 * (X 0) * (X 1) * (X 2) ^ 9
    + 432 * (X 1) * (X 2) ^ 10
    - 3078 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 7056 * (X 0) * (X 2) ^ 9
    - 432 * (X 2) ^ 10
    + 3078 * (X 0) ^ 4 * (X 2) ^ 5
    + 7056 * (X 0) * (X 2) ^ 8
    + 432 * (X 2) ^ 9
    - 3078 * (X 0) ^ 4 * (X 2) ^ 4

public noncomputable def redJ_c38 : MvPolynomial (Fin 3) ℚ :=
  -7056 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    - 432 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 10
    + 3078 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 5
    + 7056 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    + 432 * (X 0) ^ 3 * (X 1) * (X 2) ^ 10
    + 7056 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 10
    + 432 * (X 0) * (X 1) ^ 2 * (X 2) ^ 11
    - 3078 * (X 0) ^ 7 * (X 1) * (X 2) ^ 5
    - 3078 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    - 7056 * (X 0) ^ 4 * (X 2) ^ 9
    - 432 * (X 0) ^ 3 * (X 2) ^ 10
    - 7056 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    - 432 * (X 0) * (X 1) * (X 2) ^ 11
    + 3078 * (X 0) ^ 7 * (X 2) ^ 5
    + 3078 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    + 7056 * (X 0) ^ 4 * (X 2) ^ 8
    + 432 * (X 0) ^ 3 * (X 2) ^ 9
    + 7056 * (X 0) ^ 2 * (X 2) ^ 10
    - 14112 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    + 7056 * (X 0) * (X 1) * (X 2) ^ 10
    + 432 * (X 0) * (X 2) ^ 11
    - 864 * (X 1) ^ 2 * (X 2) ^ 10
    + 432 * (X 1) * (X 2) ^ 11
    - 3078 * (X 0) ^ 7 * (X 2) ^ 4
    - 3078 * (X 0) ^ 5 * (X 2) ^ 6
    + 6156 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 3078 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 7056 * (X 0) ^ 2 * (X 2) ^ 9
    + 7056 * (X 0) * (X 1) * (X 2) ^ 9
    - 7488 * (X 0) * (X 2) ^ 10
    + 432 * (X 1) * (X 2) ^ 10
    - 432 * (X 2) ^ 11
    + 3078 * (X 0) ^ 5 * (X 2) ^ 5
    - 3078 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 3078 * (X 0) ^ 4 * (X 2) ^ 6
    - 7056 * (X 0) * (X 1) * (X 2) ^ 8
    + 7056 * (X 0) * (X 2) ^ 9
    - 432 * (X 1) * (X 2) ^ 9
    + 432 * (X 2) ^ 10
    + 3078 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 3078 * (X 0) ^ 4 * (X 2) ^ 5

public noncomputable def jAff_c39 : MvPolynomial (Fin 3) ℚ :=
  30942 * (X 0) ^ 3 * (X 1) ^ 5 * (X 2) ^ 7
    + 324 * (X 0) ^ 2 * (X 1) ^ 5 * (X 2) ^ 8
    + 50184 * (X 0) * (X 1) ^ 5 * (X 2) ^ 9

public noncomputable def quotJ_c39 : MvPolynomial (Fin 3) ℚ :=
  30942 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 324 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 50184 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 30942 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 324 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 50184 * (X 0) * (X 1) * (X 2) ^ 8
    + 30942 * (X 0) ^ 3 * (X 2) ^ 6
    + 324 * (X 0) ^ 2 * (X 2) ^ 7
    + 50184 * (X 0) * (X 2) ^ 8
    - 30942 * (X 0) ^ 3 * (X 2) ^ 5
    - 324 * (X 0) ^ 2 * (X 2) ^ 6
    - 50184 * (X 0) * (X 2) ^ 7

public noncomputable def redJ_c39 : MvPolynomial (Fin 3) ℚ :=
  30942 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 6
    + 324 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 7
    + 50184 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    - 30942 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    - 324 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    - 30942 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 50184 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 324 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    - 50184 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 30942 * (X 0) ^ 6 * (X 2) ^ 6
    + 324 * (X 0) ^ 5 * (X 2) ^ 7
    + 30942 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 50184 * (X 0) ^ 4 * (X 2) ^ 8
    + 324 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 50184 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 30942 * (X 0) ^ 6 * (X 2) ^ 5
    - 324 * (X 0) ^ 5 * (X 2) ^ 6
    - 81126 * (X 0) ^ 4 * (X 2) ^ 7
    + 61884 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 30942 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 324 * (X 0) ^ 3 * (X 2) ^ 8
    + 648 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    - 324 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 50184 * (X 0) ^ 2 * (X 2) ^ 9
    + 100368 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 50184 * (X 0) * (X 1) * (X 2) ^ 9
    + 30942 * (X 0) ^ 4 * (X 2) ^ 6
    - 30942 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 31266 * (X 0) ^ 3 * (X 2) ^ 7
    - 324 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 50508 * (X 0) ^ 2 * (X 2) ^ 8
    - 50184 * (X 0) * (X 1) * (X 2) ^ 8
    + 50184 * (X 0) * (X 2) ^ 9
    + 30942 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 30942 * (X 0) ^ 3 * (X 2) ^ 6
    + 324 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 324 * (X 0) ^ 2 * (X 2) ^ 7
    + 50184 * (X 0) * (X 1) * (X 2) ^ 7
    - 50184 * (X 0) * (X 2) ^ 8

public noncomputable def jAff_c40 : MvPolynomial (Fin 3) ℚ :=
  10110 * (X 1) ^ 5 * (X 2) ^ 10
    + 1458 * (X 0) ^ 4 * (X 1) ^ 5 * (X 2) ^ 5
    + 12690 * (X 0) ^ 3 * (X 1) ^ 5 * (X 2) ^ 6

public noncomputable def quotJ_c40 : MvPolynomial (Fin 3) ℚ :=
  10110 * (X 1) ^ 2 * (X 2) ^ 9
    + 1458 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 12690 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 10110 * (X 1) * (X 2) ^ 9
    - 1458 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 12690 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 10110 * (X 2) ^ 9
    + 1458 * (X 0) ^ 4 * (X 2) ^ 4
    + 12690 * (X 0) ^ 3 * (X 2) ^ 5
    - 10110 * (X 2) ^ 8
    - 1458 * (X 0) ^ 4 * (X 2) ^ 3
    - 12690 * (X 0) ^ 3 * (X 2) ^ 4

public noncomputable def redJ_c40 : MvPolynomial (Fin 3) ℚ :=
  10110 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    + 1458 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 4
    + 12690 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 5
    - 10110 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    - 10110 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    - 1458 * (X 0) ^ 7 * (X 1) * (X 2) ^ 4
    - 12690 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    - 1458 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 5
    - 12690 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    + 10110 * (X 0) ^ 3 * (X 2) ^ 9
    + 10110 * (X 0) * (X 1) * (X 2) ^ 10
    + 1458 * (X 0) ^ 7 * (X 2) ^ 4
    + 12690 * (X 0) ^ 6 * (X 2) ^ 5
    + 1458 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 12690 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 10110 * (X 0) ^ 3 * (X 2) ^ 8
    - 10110 * (X 0) * (X 2) ^ 10
    + 20220 * (X 1) ^ 2 * (X 2) ^ 9
    - 10110 * (X 1) * (X 2) ^ 10
    - 1458 * (X 0) ^ 7 * (X 2) ^ 3
    - 12690 * (X 0) ^ 6 * (X 2) ^ 4
    - 1458 * (X 0) ^ 5 * (X 2) ^ 5
    + 2916 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 1458 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 12690 * (X 0) ^ 4 * (X 2) ^ 6
    + 25380 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 12690 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 10110 * (X 0) * (X 2) ^ 9
    - 10110 * (X 1) * (X 2) ^ 9
    + 10110 * (X 2) ^ 10
    + 1458 * (X 0) ^ 5 * (X 2) ^ 4
    - 1458 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 14148 * (X 0) ^ 4 * (X 2) ^ 5
    - 12690 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 12690 * (X 0) ^ 3 * (X 2) ^ 6
    + 10110 * (X 1) * (X 2) ^ 8
    - 10110 * (X 2) ^ 9
    + 1458 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 1458 * (X 0) ^ 4 * (X 2) ^ 4
    + 12690 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 12690 * (X 0) ^ 3 * (X 2) ^ 5

public noncomputable def jAff_c41 : MvPolynomial (Fin 3) ℚ :=
  -25272 * (X 0) ^ 2 * (X 1) ^ 5 * (X 2) ^ 7
    - 27648 * (X 0) * (X 1) ^ 5 * (X 2) ^ 8
    - 51444 * (X 1) ^ 5 * (X 2) ^ 9

public noncomputable def quotJ_c41 : MvPolynomial (Fin 3) ℚ :=
  -25272 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 27648 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 51444 * (X 1) ^ 2 * (X 2) ^ 8
    + 25272 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    + 27648 * (X 0) * (X 1) * (X 2) ^ 7
    + 51444 * (X 1) * (X 2) ^ 8
    - 25272 * (X 0) ^ 2 * (X 2) ^ 6
    - 27648 * (X 0) * (X 2) ^ 7
    - 51444 * (X 2) ^ 8
    + 25272 * (X 0) ^ 2 * (X 2) ^ 5
    + 27648 * (X 0) * (X 2) ^ 6
    + 51444 * (X 2) ^ 7

public noncomputable def redJ_c41 : MvPolynomial (Fin 3) ℚ :=
  -25272 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    - 27648 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 51444 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 25272 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    + 27648 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 25272 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 51444 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 27648 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    + 51444 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 25272 * (X 0) ^ 5 * (X 2) ^ 6
    - 27648 * (X 0) ^ 4 * (X 2) ^ 7
    - 25272 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 51444 * (X 0) ^ 3 * (X 2) ^ 8
    - 27648 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 51444 * (X 0) * (X 1) * (X 2) ^ 9
    + 25272 * (X 0) ^ 5 * (X 2) ^ 5
    + 27648 * (X 0) ^ 4 * (X 2) ^ 6
    + 76716 * (X 0) ^ 3 * (X 2) ^ 7
    - 50544 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 25272 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 27648 * (X 0) ^ 2 * (X 2) ^ 8
    - 55296 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 27648 * (X 0) * (X 1) * (X 2) ^ 8
    + 51444 * (X 0) * (X 2) ^ 9
    - 102888 * (X 1) ^ 2 * (X 2) ^ 8
    + 51444 * (X 1) * (X 2) ^ 9
    - 25272 * (X 0) ^ 3 * (X 2) ^ 6
    + 25272 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 52920 * (X 0) ^ 2 * (X 2) ^ 7
    + 27648 * (X 0) * (X 1) * (X 2) ^ 7
    - 79092 * (X 0) * (X 2) ^ 8
    + 51444 * (X 1) * (X 2) ^ 8
    - 51444 * (X 2) ^ 9
    - 25272 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 25272 * (X 0) ^ 2 * (X 2) ^ 6
    - 27648 * (X 0) * (X 1) * (X 2) ^ 6
    + 27648 * (X 0) * (X 2) ^ 7
    - 51444 * (X 1) * (X 2) ^ 7
    + 51444 * (X 2) ^ 8

public noncomputable def jAff_c42 : MvPolynomial (Fin 3) ℚ :=
  14202 * (X 0) ^ 3 * (X 1) ^ 5 * (X 2) ^ 5
    - 4860 * (X 0) ^ 2 * (X 1) ^ 5 * (X 2) ^ 6
    + 53640 * (X 0) * (X 1) ^ 5 * (X 2) ^ 7

public noncomputable def quotJ_c42 : MvPolynomial (Fin 3) ℚ :=
  14202 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 4860 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 53640 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 14202 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 4860 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 53640 * (X 0) * (X 1) * (X 2) ^ 6
    + 14202 * (X 0) ^ 3 * (X 2) ^ 4
    - 4860 * (X 0) ^ 2 * (X 2) ^ 5
    + 53640 * (X 0) * (X 2) ^ 6
    - 14202 * (X 0) ^ 3 * (X 2) ^ 3
    + 4860 * (X 0) ^ 2 * (X 2) ^ 4
    - 53640 * (X 0) * (X 2) ^ 5

public noncomputable def redJ_c42 : MvPolynomial (Fin 3) ℚ :=
  14202 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 4
    - 4860 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 5
    + 53640 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 14202 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    + 4860 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    - 14202 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 53640 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 4860 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 53640 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 14202 * (X 0) ^ 6 * (X 2) ^ 4
    - 4860 * (X 0) ^ 5 * (X 2) ^ 5
    + 14202 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 53640 * (X 0) ^ 4 * (X 2) ^ 6
    - 4860 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 53640 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 14202 * (X 0) ^ 6 * (X 2) ^ 3
    + 4860 * (X 0) ^ 5 * (X 2) ^ 4
    - 67842 * (X 0) ^ 4 * (X 2) ^ 5
    + 28404 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 14202 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 4860 * (X 0) ^ 3 * (X 2) ^ 6
    - 9720 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 4860 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 53640 * (X 0) ^ 2 * (X 2) ^ 7
    + 107280 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 53640 * (X 0) * (X 1) * (X 2) ^ 7
    + 14202 * (X 0) ^ 4 * (X 2) ^ 4
    - 14202 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 9342 * (X 0) ^ 3 * (X 2) ^ 5
    + 4860 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 48780 * (X 0) ^ 2 * (X 2) ^ 6
    - 53640 * (X 0) * (X 1) * (X 2) ^ 6
    + 53640 * (X 0) * (X 2) ^ 7
    + 14202 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 14202 * (X 0) ^ 3 * (X 2) ^ 4
    - 4860 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 4860 * (X 0) ^ 2 * (X 2) ^ 5
    + 53640 * (X 0) * (X 1) * (X 2) ^ 5
    - 53640 * (X 0) * (X 2) ^ 6

public noncomputable def jAff_c43 : MvPolynomial (Fin 3) ℚ :=
  27297 * (X 1) ^ 5 * (X 2) ^ 8
    + 162 * (X 0) ^ 3 * (X 1) ^ 5 * (X 2) ^ 4
    - 144 * (X 0) * (X 1) ^ 5 * (X 2) ^ 6

public noncomputable def quotJ_c43 : MvPolynomial (Fin 3) ℚ :=
  27297 * (X 1) ^ 2 * (X 2) ^ 7
    + 162 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 144 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 27297 * (X 1) * (X 2) ^ 7
    - 162 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 144 * (X 0) * (X 1) * (X 2) ^ 5
    + 27297 * (X 2) ^ 7
    + 162 * (X 0) ^ 3 * (X 2) ^ 3
    - 144 * (X 0) * (X 2) ^ 5
    - 27297 * (X 2) ^ 6
    - 162 * (X 0) ^ 3 * (X 2) ^ 2
    + 144 * (X 0) * (X 2) ^ 4

public noncomputable def redJ_c43 : MvPolynomial (Fin 3) ℚ :=
  27297 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 162 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 3
    - 144 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 27297 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 27297 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    - 162 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    - 162 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 144 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 27297 * (X 0) ^ 3 * (X 2) ^ 7
    + 144 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 27297 * (X 0) * (X 1) * (X 2) ^ 8
    + 162 * (X 0) ^ 6 * (X 2) ^ 3
    + 162 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 144 * (X 0) ^ 4 * (X 2) ^ 5
    - 27297 * (X 0) ^ 3 * (X 2) ^ 6
    - 144 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 27297 * (X 0) * (X 2) ^ 8
    + 54594 * (X 1) ^ 2 * (X 2) ^ 7
    - 27297 * (X 1) * (X 2) ^ 8
    - 162 * (X 0) ^ 6 * (X 2) ^ 2
    - 18 * (X 0) ^ 4 * (X 2) ^ 4
    + 324 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 162 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 144 * (X 0) ^ 2 * (X 2) ^ 6
    - 288 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + 144 * (X 0) * (X 1) * (X 2) ^ 6
    + 27297 * (X 0) * (X 2) ^ 7
    - 27297 * (X 1) * (X 2) ^ 7
    + 27297 * (X 2) ^ 8
    + 162 * (X 0) ^ 4 * (X 2) ^ 3
    - 162 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 162 * (X 0) ^ 3 * (X 2) ^ 4
    - 144 * (X 0) ^ 2 * (X 2) ^ 5
    + 144 * (X 0) * (X 1) * (X 2) ^ 5
    - 144 * (X 0) * (X 2) ^ 6
    + 27297 * (X 1) * (X 2) ^ 6
    - 27297 * (X 2) ^ 7
    + 162 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    - 162 * (X 0) ^ 3 * (X 2) ^ 3
    - 144 * (X 0) * (X 1) * (X 2) ^ 4
    + 144 * (X 0) * (X 2) ^ 5

public noncomputable def jAff_c44 : MvPolynomial (Fin 3) ℚ :=
  -48816 * (X 1) ^ 5 * (X 2) ^ 7
    + 1944 * (X 0) ^ 3 * (X 1) ^ 5 * (X 2) ^ 3
    + 864 * (X 0) * (X 1) ^ 5 * (X 2) ^ 5

public noncomputable def quotJ_c44 : MvPolynomial (Fin 3) ℚ :=
  -48816 * (X 1) ^ 2 * (X 2) ^ 6
    + 1944 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    + 864 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 48816 * (X 1) * (X 2) ^ 6
    - 1944 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    - 864 * (X 0) * (X 1) * (X 2) ^ 4
    - 48816 * (X 2) ^ 6
    + 1944 * (X 0) ^ 3 * (X 2) ^ 2
    + 864 * (X 0) * (X 2) ^ 4
    + 48816 * (X 2) ^ 5
    - 1944 * (X 0) ^ 3 * (X 2)
    - 864 * (X 0) * (X 2) ^ 3

public noncomputable def redJ_c44 : MvPolynomial (Fin 3) ℚ :=
  -48816 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 1944 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 2
    + 864 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 48816 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 48816 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 1944 * (X 0) ^ 6 * (X 1) * (X 2) ^ 2
    - 1944 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    - 864 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 48816 * (X 0) ^ 3 * (X 2) ^ 6
    - 864 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    - 48816 * (X 0) * (X 1) * (X 2) ^ 7
    + 1944 * (X 0) ^ 6 * (X 2) ^ 2
    + 1944 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    + 864 * (X 0) ^ 4 * (X 2) ^ 4
    + 48816 * (X 0) ^ 3 * (X 2) ^ 5
    + 864 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 48816 * (X 0) * (X 2) ^ 7
    - 97632 * (X 1) ^ 2 * (X 2) ^ 6
    + 48816 * (X 1) * (X 2) ^ 7
    - 1944 * (X 0) ^ 6 * (X 2)
    - 2808 * (X 0) ^ 4 * (X 2) ^ 3
    + 3888 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    - 1944 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 864 * (X 0) ^ 2 * (X 2) ^ 5
    + 1728 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 864 * (X 0) * (X 1) * (X 2) ^ 5
    - 48816 * (X 0) * (X 2) ^ 6
    + 48816 * (X 1) * (X 2) ^ 6
    - 48816 * (X 2) ^ 7
    + 1944 * (X 0) ^ 4 * (X 2) ^ 2
    - 1944 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 1944 * (X 0) ^ 3 * (X 2) ^ 3
    + 864 * (X 0) ^ 2 * (X 2) ^ 4
    - 864 * (X 0) * (X 1) * (X 2) ^ 4
    + 864 * (X 0) * (X 2) ^ 5
    - 48816 * (X 1) * (X 2) ^ 5
    + 48816 * (X 2) ^ 6
    + 1944 * (X 0) ^ 3 * (X 1) * (X 2)
    - 1944 * (X 0) ^ 3 * (X 2) ^ 2
    + 864 * (X 0) * (X 1) * (X 2) ^ 3
    - 864 * (X 0) * (X 2) ^ 4

public noncomputable def jAff_c45 : MvPolynomial (Fin 3) ℚ :=
  3726 * (X 1) ^ 5 * (X 2) ^ 6
    - 1296 * (X 0) * (X 1) ^ 5 * (X 2) ^ 4
    - 1530 * (X 1) ^ 5 * (X 2) ^ 5

public noncomputable def quotJ_c45 : MvPolynomial (Fin 3) ℚ :=
  3726 * (X 1) ^ 2 * (X 2) ^ 5
    - 1296 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    - 1530 * (X 1) ^ 2 * (X 2) ^ 4
    - 3726 * (X 1) * (X 2) ^ 5
    + 1296 * (X 0) * (X 1) * (X 2) ^ 3
    + 1530 * (X 1) * (X 2) ^ 4
    + 3726 * (X 2) ^ 5
    - 1296 * (X 0) * (X 2) ^ 3
    - 5256 * (X 2) ^ 4
    + 1296 * (X 0) * (X 2) ^ 2
    + 1530 * (X 2) ^ 3

public noncomputable def redJ_c45 : MvPolynomial (Fin 3) ℚ :=
  3726 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 1296 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    - 1530 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 3726 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 3726 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 1296 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    + 1530 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 3726 * (X 0) ^ 3 * (X 2) ^ 5
    + 1296 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 4
    + 1530 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + 3726 * (X 0) * (X 1) * (X 2) ^ 6
    - 1296 * (X 0) ^ 4 * (X 2) ^ 3
    - 5256 * (X 0) ^ 3 * (X 2) ^ 4
    - 1296 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    - 1530 * (X 0) * (X 1) * (X 2) ^ 5
    - 3726 * (X 0) * (X 2) ^ 6
    + 7452 * (X 1) ^ 2 * (X 2) ^ 5
    - 3726 * (X 1) * (X 2) ^ 6
    + 1296 * (X 0) ^ 4 * (X 2) ^ 2
    + 1530 * (X 0) ^ 3 * (X 2) ^ 3
    + 1296 * (X 0) ^ 2 * (X 2) ^ 4
    - 2592 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 1296 * (X 0) * (X 1) * (X 2) ^ 4
    + 5256 * (X 0) * (X 2) ^ 5
    - 3060 * (X 1) ^ 2 * (X 2) ^ 4
    - 2196 * (X 1) * (X 2) ^ 5
    + 3726 * (X 2) ^ 6
    - 1296 * (X 0) ^ 2 * (X 2) ^ 3
    + 1296 * (X 0) * (X 1) * (X 2) ^ 3
    - 2826 * (X 0) * (X 2) ^ 4
    + 5256 * (X 1) * (X 2) ^ 4
    - 5256 * (X 2) ^ 5
    - 1296 * (X 0) * (X 1) * (X 2) ^ 2
    + 1296 * (X 0) * (X 2) ^ 3
    - 1530 * (X 1) * (X 2) ^ 3
    + 1530 * (X 2) ^ 4

public noncomputable def jAff_c46 : MvPolynomial (Fin 3) ℚ :=
  3267 * (X 1) ^ 5 * (X 2) ^ 4
    + 270 * (X 1) ^ 5 * (X 2) ^ 3

public noncomputable def quotJ_c46 : MvPolynomial (Fin 3) ℚ :=
  3267 * (X 1) ^ 2 * (X 2) ^ 3
    + 270 * (X 1) ^ 2 * (X 2) ^ 2
    - 3267 * (X 1) * (X 2) ^ 3
    - 270 * (X 1) * (X 2) ^ 2
    + 3267 * (X 2) ^ 3
    - 2997 * (X 2) ^ 2
    - 270 * (X 2)

public noncomputable def redJ_c46 : MvPolynomial (Fin 3) ℚ :=
  3267 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 270 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    - 3267 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 3267 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    - 270 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 3267 * (X 0) ^ 3 * (X 2) ^ 3
    - 270 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 3267 * (X 0) * (X 1) * (X 2) ^ 4
    - 2997 * (X 0) ^ 3 * (X 2) ^ 2
    + 270 * (X 0) * (X 1) * (X 2) ^ 3
    - 3267 * (X 0) * (X 2) ^ 4
    + 6534 * (X 1) ^ 2 * (X 2) ^ 3
    - 3267 * (X 1) * (X 2) ^ 4
    - 270 * (X 0) ^ 3 * (X 2)
    + 2997 * (X 0) * (X 2) ^ 3
    + 540 * (X 1) ^ 2 * (X 2) ^ 2
    - 3537 * (X 1) * (X 2) ^ 3
    + 3267 * (X 2) ^ 4
    + 270 * (X 0) * (X 2) ^ 2
    + 2997 * (X 1) * (X 2) ^ 2
    - 2997 * (X 2) ^ 3
    + 270 * (X 1) * (X 2)
    - 270 * (X 2) ^ 2

public noncomputable def jAff_c47 : MvPolynomial (Fin 3) ℚ :=
  1350 * (X 0) ^ 5 * (X 1) ^ 4 * (X 2) ^ 8
    - 1620 * (X 0) ^ 4 * (X 1) ^ 4 * (X 2) ^ 9
    - 3564 * (X 0) ^ 5 * (X 1) ^ 4 * (X 2) ^ 7
    + 5670 * (X 0) ^ 4 * (X 1) ^ 4 * (X 2) ^ 8

public noncomputable def quotJ_c47 : MvPolynomial (Fin 3) ℚ :=
  1350 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    - 1620 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 3564 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    - 1350 * (X 0) ^ 5 * (X 2) ^ 7
    + 5670 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 1620 * (X 0) ^ 4 * (X 2) ^ 8
    + 3564 * (X 0) ^ 5 * (X 2) ^ 6
    - 5670 * (X 0) ^ 4 * (X 2) ^ 7

public noncomputable def redJ_c47 : MvPolynomial (Fin 3) ℚ :=
  1350 * (X 0) ^ 8 * (X 1) * (X 2) ^ 7
    - 1620 * (X 0) ^ 7 * (X 1) * (X 2) ^ 8
    - 3564 * (X 0) ^ 8 * (X 1) * (X 2) ^ 6
    - 1350 * (X 0) ^ 8 * (X 2) ^ 7
    + 5670 * (X 0) ^ 7 * (X 1) * (X 2) ^ 7
    + 1620 * (X 0) ^ 7 * (X 2) ^ 8
    - 1350 * (X 0) ^ 6 * (X 1) * (X 2) ^ 8
    + 1350 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 8
    + 1620 * (X 0) ^ 5 * (X 1) * (X 2) ^ 9
    - 1620 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    + 3564 * (X 0) ^ 8 * (X 2) ^ 6
    - 5670 * (X 0) ^ 7 * (X 2) ^ 7
    + 3564 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    + 1350 * (X 0) ^ 6 * (X 2) ^ 8
    - 4914 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 7
    - 4320 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    - 1620 * (X 0) ^ 5 * (X 2) ^ 9
    + 7290 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    - 1620 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    - 3564 * (X 0) ^ 6 * (X 2) ^ 7
    + 3564 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    - 2214 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    + 4320 * (X 0) ^ 5 * (X 2) ^ 8
    - 5670 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    + 4050 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 1620 * (X 0) ^ 4 * (X 2) ^ 9
    - 3564 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    + 3564 * (X 0) ^ 5 * (X 2) ^ 7
    + 5670 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 5670 * (X 0) ^ 4 * (X 2) ^ 8

public noncomputable def jAff_c48 : MvPolynomial (Fin 3) ℚ :=
  360 * (X 0) ^ 3 * (X 1) ^ 4 * (X 2) ^ 9
    + 4320 * (X 0) ^ 2 * (X 1) ^ 4 * (X 2) ^ 10
    - 1458 * (X 0) ^ 5 * (X 1) ^ 4 * (X 2) ^ 6
    - 4950 * (X 0) ^ 4 * (X 1) ^ 4 * (X 2) ^ 7

public noncomputable def quotJ_c48 : MvPolynomial (Fin 3) ℚ :=
  360 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 4320 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 1458 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    - 4950 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 360 * (X 0) ^ 3 * (X 2) ^ 8
    - 4320 * (X 0) ^ 2 * (X 2) ^ 9
    + 1458 * (X 0) ^ 5 * (X 2) ^ 5
    + 4950 * (X 0) ^ 4 * (X 2) ^ 6

public noncomputable def redJ_c48 : MvPolynomial (Fin 3) ℚ :=
  360 * (X 0) ^ 6 * (X 1) * (X 2) ^ 8
    + 4320 * (X 0) ^ 5 * (X 1) * (X 2) ^ 9
    - 1458 * (X 0) ^ 8 * (X 1) * (X 2) ^ 5
    - 4950 * (X 0) ^ 7 * (X 1) * (X 2) ^ 6
    - 360 * (X 0) ^ 6 * (X 2) ^ 8
    - 4320 * (X 0) ^ 5 * (X 2) ^ 9
    - 360 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    + 360 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    - 4320 * (X 0) ^ 3 * (X 1) * (X 2) ^ 10
    + 4320 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 10
    + 1458 * (X 0) ^ 8 * (X 2) ^ 5
    + 4950 * (X 0) ^ 7 * (X 2) ^ 6
    + 1458 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    - 1458 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    + 4950 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    - 4950 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    + 360 * (X 0) ^ 4 * (X 2) ^ 9
    - 360 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 360 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    + 4320 * (X 0) ^ 3 * (X 2) ^ 10
    - 4320 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 4320 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    - 1458 * (X 0) ^ 6 * (X 2) ^ 6
    + 1458 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 5
    - 1458 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    - 4950 * (X 0) ^ 5 * (X 2) ^ 7
    + 4950 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 4950 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 360 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 360 * (X 0) ^ 3 * (X 2) ^ 9
    + 4320 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 4320 * (X 0) ^ 2 * (X 2) ^ 10
    - 1458 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 1458 * (X 0) ^ 5 * (X 2) ^ 6
    - 4950 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 4950 * (X 0) ^ 4 * (X 2) ^ 7

public noncomputable def jAff_c49 : MvPolynomial (Fin 3) ℚ :=
  12285 * (X 0) ^ 3 * (X 1) ^ 4 * (X 2) ^ 8
    - 39150 * (X 0) ^ 2 * (X 1) ^ 4 * (X 2) ^ 9
    - 7830 * (X 0) * (X 1) ^ 4 * (X 2) ^ 10
    - 396 * (X 1) ^ 4 * (X 2) ^ 11

public noncomputable def quotJ_c49 : MvPolynomial (Fin 3) ℚ :=
  12285 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 39150 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 7830 * (X 0) * (X 1) * (X 2) ^ 9
    - 396 * (X 1) * (X 2) ^ 10
    - 12285 * (X 0) ^ 3 * (X 2) ^ 7
    + 39150 * (X 0) ^ 2 * (X 2) ^ 8
    + 7830 * (X 0) * (X 2) ^ 9
    + 396 * (X 2) ^ 10

public noncomputable def redJ_c49 : MvPolynomial (Fin 3) ℚ :=
  12285 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    - 39150 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    - 7830 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    - 396 * (X 0) ^ 3 * (X 1) * (X 2) ^ 10
    - 12285 * (X 0) ^ 6 * (X 2) ^ 7
    + 39150 * (X 0) ^ 5 * (X 2) ^ 8
    - 12285 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 7830 * (X 0) ^ 4 * (X 2) ^ 9
    + 12285 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 39150 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    + 396 * (X 0) ^ 3 * (X 2) ^ 10
    - 39150 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 7830 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    - 7830 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    + 396 * (X 0) * (X 1) * (X 2) ^ 11
    - 396 * (X 1) ^ 2 * (X 2) ^ 11
    + 12285 * (X 0) ^ 4 * (X 2) ^ 8
    - 12285 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 12285 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 39150 * (X 0) ^ 3 * (X 2) ^ 9
    + 39150 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 39150 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    - 7830 * (X 0) ^ 2 * (X 2) ^ 10
    + 7830 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 7830 * (X 0) * (X 1) * (X 2) ^ 10
    - 396 * (X 0) * (X 2) ^ 11
    + 396 * (X 1) ^ 2 * (X 2) ^ 10
    - 396 * (X 1) * (X 2) ^ 11
    + 12285 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 12285 * (X 0) ^ 3 * (X 2) ^ 8
    - 39150 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 39150 * (X 0) ^ 2 * (X 2) ^ 9
    - 7830 * (X 0) * (X 1) * (X 2) ^ 9
    + 7830 * (X 0) * (X 2) ^ 10
    - 396 * (X 1) * (X 2) ^ 10
    + 396 * (X 2) ^ 11

public noncomputable def jAff_c50 : MvPolynomial (Fin 3) ℚ :=
  8370 * (X 0) ^ 4 * (X 1) ^ 4 * (X 2) ^ 6
    + 17145 * (X 0) ^ 3 * (X 1) ^ 4 * (X 2) ^ 7
    + 41940 * (X 0) ^ 2 * (X 1) ^ 4 * (X 2) ^ 8
    + 66195 * (X 0) * (X 1) ^ 4 * (X 2) ^ 9

public noncomputable def quotJ_c50 : MvPolynomial (Fin 3) ℚ :=
  8370 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 17145 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 41940 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 66195 * (X 0) * (X 1) * (X 2) ^ 8
    - 8370 * (X 0) ^ 4 * (X 2) ^ 5
    - 17145 * (X 0) ^ 3 * (X 2) ^ 6
    - 41940 * (X 0) ^ 2 * (X 2) ^ 7
    - 66195 * (X 0) * (X 2) ^ 8

public noncomputable def redJ_c50 : MvPolynomial (Fin 3) ℚ :=
  8370 * (X 0) ^ 7 * (X 1) * (X 2) ^ 5
    + 17145 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    + 41940 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    + 66195 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 8370 * (X 0) ^ 7 * (X 2) ^ 5
    - 17145 * (X 0) ^ 6 * (X 2) ^ 6
    - 8370 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    - 41940 * (X 0) ^ 5 * (X 2) ^ 7
    + 8370 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 17145 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 66195 * (X 0) ^ 4 * (X 2) ^ 8
    + 17145 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 41940 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 41940 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 66195 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 66195 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    + 8370 * (X 0) ^ 5 * (X 2) ^ 6
    - 8370 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    + 8370 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 17145 * (X 0) ^ 4 * (X 2) ^ 7
    - 17145 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 17145 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 41940 * (X 0) ^ 3 * (X 2) ^ 8
    - 41940 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 41940 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 66195 * (X 0) ^ 2 * (X 2) ^ 9
    - 66195 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 66195 * (X 0) * (X 1) * (X 2) ^ 9
    + 8370 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 8370 * (X 0) ^ 4 * (X 2) ^ 6
    + 17145 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 17145 * (X 0) ^ 3 * (X 2) ^ 7
    + 41940 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 41940 * (X 0) ^ 2 * (X 2) ^ 8
    + 66195 * (X 0) * (X 1) * (X 2) ^ 8
    - 66195 * (X 0) * (X 2) ^ 9

public noncomputable def jAff_c51 : MvPolynomial (Fin 3) ℚ :=
  9864 * (X 1) ^ 4 * (X 2) ^ 10
    - 4050 * (X 0) ^ 4 * (X 1) ^ 4 * (X 2) ^ 5
    + 14985 * (X 0) ^ 3 * (X 1) ^ 4 * (X 2) ^ 6
    - 13230 * (X 0) ^ 2 * (X 1) ^ 4 * (X 2) ^ 7

public noncomputable def quotJ_c51 : MvPolynomial (Fin 3) ℚ :=
  9864 * (X 1) * (X 2) ^ 9
    - 4050 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 14985 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 13230 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 9864 * (X 2) ^ 9
    + 4050 * (X 0) ^ 4 * (X 2) ^ 4
    - 14985 * (X 0) ^ 3 * (X 2) ^ 5
    + 13230 * (X 0) ^ 2 * (X 2) ^ 6

public noncomputable def redJ_c51 : MvPolynomial (Fin 3) ℚ :=
  9864 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    - 4050 * (X 0) ^ 7 * (X 1) * (X 2) ^ 4
    + 14985 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    - 13230 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    - 9864 * (X 0) ^ 3 * (X 2) ^ 9
    - 9864 * (X 0) * (X 1) * (X 2) ^ 10
    + 9864 * (X 1) ^ 2 * (X 2) ^ 10
    + 4050 * (X 0) ^ 7 * (X 2) ^ 4
    - 14985 * (X 0) ^ 6 * (X 2) ^ 5
    + 4050 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 13230 * (X 0) ^ 5 * (X 2) ^ 6
    - 4050 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 14985 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 14985 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 13230 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 13230 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 9864 * (X 0) * (X 2) ^ 10
    - 9864 * (X 1) ^ 2 * (X 2) ^ 9
    + 9864 * (X 1) * (X 2) ^ 10
    - 4050 * (X 0) ^ 5 * (X 2) ^ 5
    + 4050 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 4050 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 14985 * (X 0) ^ 4 * (X 2) ^ 6
    - 14985 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 14985 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 13230 * (X 0) ^ 3 * (X 2) ^ 7
    + 13230 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 13230 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 9864 * (X 1) * (X 2) ^ 9
    - 9864 * (X 2) ^ 10
    - 4050 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 4050 * (X 0) ^ 4 * (X 2) ^ 5
    + 14985 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 14985 * (X 0) ^ 3 * (X 2) ^ 6
    - 13230 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    + 13230 * (X 0) ^ 2 * (X 2) ^ 7

public noncomputable def jAff_c52 : MvPolynomial (Fin 3) ℚ :=
  -71235 * (X 0) * (X 1) ^ 4 * (X 2) ^ 8
    - 55671 * (X 1) ^ 4 * (X 2) ^ 9
    + 4860 * (X 0) ^ 4 * (X 1) ^ 4 * (X 2) ^ 4
    + 19575 * (X 0) ^ 3 * (X 1) ^ 4 * (X 2) ^ 5

public noncomputable def quotJ_c52 : MvPolynomial (Fin 3) ℚ :=
  -71235 * (X 0) * (X 1) * (X 2) ^ 7
    - 55671 * (X 1) * (X 2) ^ 8
    + 4860 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    + 19575 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 71235 * (X 0) * (X 2) ^ 7
    + 55671 * (X 2) ^ 8
    - 4860 * (X 0) ^ 4 * (X 2) ^ 3
    - 19575 * (X 0) ^ 3 * (X 2) ^ 4

public noncomputable def redJ_c52 : MvPolynomial (Fin 3) ℚ :=
  -71235 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    - 55671 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 4860 * (X 0) ^ 7 * (X 1) * (X 2) ^ 3
    + 19575 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    + 71235 * (X 0) ^ 4 * (X 2) ^ 7
    + 55671 * (X 0) ^ 3 * (X 2) ^ 8
    + 71235 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 71235 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 55671 * (X 0) * (X 1) * (X 2) ^ 9
    - 55671 * (X 1) ^ 2 * (X 2) ^ 9
    - 4860 * (X 0) ^ 7 * (X 2) ^ 3
    - 19575 * (X 0) ^ 6 * (X 2) ^ 4
    - 4860 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    + 4860 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 19575 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 19575 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 71235 * (X 0) ^ 2 * (X 2) ^ 8
    + 71235 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 71235 * (X 0) * (X 1) * (X 2) ^ 8
    - 55671 * (X 0) * (X 2) ^ 9
    + 55671 * (X 1) ^ 2 * (X 2) ^ 8
    - 55671 * (X 1) * (X 2) ^ 9
    + 4860 * (X 0) ^ 5 * (X 2) ^ 4
    - 4860 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    + 4860 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 19575 * (X 0) ^ 4 * (X 2) ^ 5
    - 19575 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 19575 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 71235 * (X 0) * (X 1) * (X 2) ^ 7
    + 71235 * (X 0) * (X 2) ^ 8
    - 55671 * (X 1) * (X 2) ^ 8
    + 55671 * (X 2) ^ 9
    + 4860 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 4860 * (X 0) ^ 4 * (X 2) ^ 4
    + 19575 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 19575 * (X 0) ^ 3 * (X 2) ^ 5

public noncomputable def jAff_c53 : MvPolynomial (Fin 3) ℚ :=
  -2160 * (X 0) ^ 2 * (X 1) ^ 4 * (X 2) ^ 6
    + 22545 * (X 0) * (X 1) ^ 4 * (X 2) ^ 7
    + 44541 * (X 1) ^ 4 * (X 2) ^ 8
    - 1350 * (X 0) ^ 3 * (X 1) ^ 4 * (X 2) ^ 4

public noncomputable def quotJ_c53 : MvPolynomial (Fin 3) ℚ :=
  -2160 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 22545 * (X 0) * (X 1) * (X 2) ^ 6
    + 44541 * (X 1) * (X 2) ^ 7
    - 1350 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 2160 * (X 0) ^ 2 * (X 2) ^ 5
    - 22545 * (X 0) * (X 2) ^ 6
    - 44541 * (X 2) ^ 7
    + 1350 * (X 0) ^ 3 * (X 2) ^ 3

public noncomputable def redJ_c53 : MvPolynomial (Fin 3) ℚ :=
  -2160 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 22545 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 44541 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 1350 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    + 2160 * (X 0) ^ 5 * (X 2) ^ 5
    - 22545 * (X 0) ^ 4 * (X 2) ^ 6
    + 2160 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 44541 * (X 0) ^ 3 * (X 2) ^ 7
    - 2160 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 22545 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 22545 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 44541 * (X 0) * (X 1) * (X 2) ^ 8
    + 44541 * (X 1) ^ 2 * (X 2) ^ 8
    + 1350 * (X 0) ^ 6 * (X 2) ^ 3
    + 1350 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 1350 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 2160 * (X 0) ^ 3 * (X 2) ^ 6
    + 2160 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    - 2160 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    + 22545 * (X 0) ^ 2 * (X 2) ^ 7
    - 22545 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 22545 * (X 0) * (X 1) * (X 2) ^ 7
    + 44541 * (X 0) * (X 2) ^ 8
    - 44541 * (X 1) ^ 2 * (X 2) ^ 7
    + 44541 * (X 1) * (X 2) ^ 8
    - 1350 * (X 0) ^ 4 * (X 2) ^ 4
    + 1350 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 1350 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 2160 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 2160 * (X 0) ^ 2 * (X 2) ^ 6
    + 22545 * (X 0) * (X 1) * (X 2) ^ 6
    - 22545 * (X 0) * (X 2) ^ 7
    + 44541 * (X 1) * (X 2) ^ 7
    - 44541 * (X 2) ^ 8
    - 1350 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 1350 * (X 0) ^ 3 * (X 2) ^ 4

public noncomputable def jAff_c54 : MvPolynomial (Fin 3) ℚ :=
  -3240 * (X 0) ^ 2 * (X 1) ^ 4 * (X 2) ^ 5
    - 2385 * (X 0) * (X 1) ^ 4 * (X 2) ^ 6
    - 25722 * (X 1) ^ 4 * (X 2) ^ 7
    + 3240 * (X 0) ^ 3 * (X 1) ^ 4 * (X 2) ^ 3

public noncomputable def quotJ_c54 : MvPolynomial (Fin 3) ℚ :=
  -3240 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    - 2385 * (X 0) * (X 1) * (X 2) ^ 5
    - 25722 * (X 1) * (X 2) ^ 6
    + 3240 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 3240 * (X 0) ^ 2 * (X 2) ^ 4
    + 2385 * (X 0) * (X 2) ^ 5
    + 25722 * (X 2) ^ 6
    - 3240 * (X 0) ^ 3 * (X 2) ^ 2

public noncomputable def redJ_c54 : MvPolynomial (Fin 3) ℚ :=
  -3240 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    - 2385 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 25722 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 3240 * (X 0) ^ 6 * (X 1) * (X 2) ^ 2
    + 3240 * (X 0) ^ 5 * (X 2) ^ 4
    + 2385 * (X 0) ^ 4 * (X 2) ^ 5
    + 3240 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 25722 * (X 0) ^ 3 * (X 2) ^ 6
    - 3240 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    + 2385 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 2385 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 25722 * (X 0) * (X 1) * (X 2) ^ 7
    - 25722 * (X 1) ^ 2 * (X 2) ^ 7
    - 3240 * (X 0) ^ 6 * (X 2) ^ 2
    - 3240 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    + 3240 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    - 3240 * (X 0) ^ 3 * (X 2) ^ 5
    + 3240 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 4
    - 3240 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    - 2385 * (X 0) ^ 2 * (X 2) ^ 6
    + 2385 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 2385 * (X 0) * (X 1) * (X 2) ^ 6
    - 25722 * (X 0) * (X 2) ^ 7
    + 25722 * (X 1) ^ 2 * (X 2) ^ 6
    - 25722 * (X 1) * (X 2) ^ 7
    + 3240 * (X 0) ^ 4 * (X 2) ^ 3
    - 3240 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    + 3240 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 3240 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 3240 * (X 0) ^ 2 * (X 2) ^ 5
    - 2385 * (X 0) * (X 1) * (X 2) ^ 5
    + 2385 * (X 0) * (X 2) ^ 6
    - 25722 * (X 1) * (X 2) ^ 6
    + 25722 * (X 2) ^ 7
    + 3240 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    - 3240 * (X 0) ^ 3 * (X 2) ^ 3

public noncomputable def jAff_c55 : MvPolynomial (Fin 3) ℚ :=
  7200 * (X 0) * (X 1) ^ 4 * (X 2) ^ 5
    + 2754 * (X 1) ^ 4 * (X 2) ^ 6
    + 270 * (X 0) * (X 1) ^ 4 * (X 2) ^ 4
    - 8829 * (X 1) ^ 4 * (X 2) ^ 5

public noncomputable def quotJ_c55 : MvPolynomial (Fin 3) ℚ :=
  7200 * (X 0) * (X 1) * (X 2) ^ 4
    + 2754 * (X 1) * (X 2) ^ 5
    + 270 * (X 0) * (X 1) * (X 2) ^ 3
    - 7200 * (X 0) * (X 2) ^ 4
    - 8829 * (X 1) * (X 2) ^ 4
    - 2754 * (X 2) ^ 5
    - 270 * (X 0) * (X 2) ^ 3
    + 8829 * (X 2) ^ 4

public noncomputable def redJ_c55 : MvPolynomial (Fin 3) ℚ :=
  7200 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 2754 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 270 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 7200 * (X 0) ^ 4 * (X 2) ^ 4
    - 8829 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 2754 * (X 0) ^ 3 * (X 2) ^ 5
    - 7200 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 7200 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    - 2754 * (X 0) * (X 1) * (X 2) ^ 6
    + 2754 * (X 1) ^ 2 * (X 2) ^ 6
    - 270 * (X 0) ^ 4 * (X 2) ^ 3
    + 8829 * (X 0) ^ 3 * (X 2) ^ 4
    - 270 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 7200 * (X 0) ^ 2 * (X 2) ^ 5
    - 6930 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 16029 * (X 0) * (X 1) * (X 2) ^ 5
    + 2754 * (X 0) * (X 2) ^ 6
    - 11583 * (X 1) ^ 2 * (X 2) ^ 5
    + 2754 * (X 1) * (X 2) ^ 6
    + 270 * (X 0) ^ 2 * (X 2) ^ 4
    - 270 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 7470 * (X 0) * (X 1) * (X 2) ^ 4
    - 16029 * (X 0) * (X 2) ^ 5
    + 8829 * (X 1) ^ 2 * (X 2) ^ 4
    - 6075 * (X 1) * (X 2) ^ 5
    - 2754 * (X 2) ^ 6
    + 270 * (X 0) * (X 1) * (X 2) ^ 3
    - 270 * (X 0) * (X 2) ^ 4
    - 8829 * (X 1) * (X 2) ^ 4
    + 8829 * (X 2) ^ 5

public noncomputable def jAff_c56 : MvPolynomial (Fin 3) ℚ :=
  -171 * (X 1) ^ 4 * (X 2) ^ 4
    - 54 * (X 1) ^ 4 * (X 2) ^ 3
    + 108 * (X 1) ^ 4 * (X 2) ^ 2

public noncomputable def quotJ_c56 : MvPolynomial (Fin 3) ℚ :=
  -171 * (X 1) * (X 2) ^ 3
    - 54 * (X 1) * (X 2) ^ 2
    + 171 * (X 2) ^ 3
    + 108 * (X 1) * (X 2)
    + 54 * (X 2) ^ 2
    - 108 * (X 2)

public noncomputable def redJ_c56 : MvPolynomial (Fin 3) ℚ :=
  -171 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 54 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 171 * (X 0) ^ 3 * (X 2) ^ 3
    + 171 * (X 0) * (X 1) * (X 2) ^ 4
    - 171 * (X 1) ^ 2 * (X 2) ^ 4
    + 108 * (X 0) ^ 3 * (X 1) * (X 2)
    + 54 * (X 0) ^ 3 * (X 2) ^ 2
    + 54 * (X 0) * (X 1) * (X 2) ^ 3
    - 171 * (X 0) * (X 2) ^ 4
    + 117 * (X 1) ^ 2 * (X 2) ^ 3
    - 171 * (X 1) * (X 2) ^ 4
    - 108 * (X 0) ^ 3 * (X 2)
    - 108 * (X 0) * (X 1) * (X 2) ^ 2
    - 54 * (X 0) * (X 2) ^ 3
    + 162 * (X 1) ^ 2 * (X 2) ^ 2
    - 225 * (X 1) * (X 2) ^ 3
    + 171 * (X 2) ^ 4
    + 108 * (X 0) * (X 2) ^ 2
    - 108 * (X 1) ^ 2 * (X 2)
    + 54 * (X 1) * (X 2) ^ 2
    + 54 * (X 2) ^ 3
    + 108 * (X 1) * (X 2)
    - 108 * (X 2) ^ 2

public noncomputable def jAff_c57 : MvPolynomial (Fin 3) ℚ :=
  -2700 * (X 0) ^ 6 * (X 1) ^ 3 * (X 2) ^ 8
    + 1944 * (X 0) ^ 5 * (X 1) ^ 3 * (X 2) ^ 9
    + 14553 * (X 0) ^ 6 * (X 1) ^ 3 * (X 2) ^ 7
    - 9522 * (X 0) ^ 5 * (X 1) ^ 3 * (X 2) ^ 8
    - 2160 * (X 0) ^ 4 * (X 1) ^ 3 * (X 2) ^ 9

public noncomputable def quotJ_c57 : MvPolynomial (Fin 3) ℚ :=
  -2700 * (X 0) ^ 6 * (X 2) ^ 7
    + 1944 * (X 0) ^ 5 * (X 2) ^ 8
    + 14553 * (X 0) ^ 6 * (X 2) ^ 6
    - 9522 * (X 0) ^ 5 * (X 2) ^ 7
    - 2160 * (X 0) ^ 4 * (X 2) ^ 8

public noncomputable def redJ_c57 : MvPolynomial (Fin 3) ℚ :=
  -2700 * (X 0) ^ 9 * (X 2) ^ 7
    + 1944 * (X 0) ^ 8 * (X 2) ^ 8
    + 2700 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 8
    - 1944 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 9
    + 14553 * (X 0) ^ 9 * (X 2) ^ 6
    - 9522 * (X 0) ^ 8 * (X 2) ^ 7
    + 540 * (X 0) ^ 7 * (X 2) ^ 8
    - 14553 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 7
    - 1944 * (X 0) ^ 6 * (X 2) ^ 9
    + 9522 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 8
    + 2160 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    - 14553 * (X 0) ^ 7 * (X 2) ^ 7
    + 2700 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    + 6822 * (X 0) ^ 6 * (X 2) ^ 8
    - 1944 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    + 4104 * (X 0) ^ 5 * (X 2) ^ 9
    - 14553 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    + 14553 * (X 0) ^ 6 * (X 2) ^ 7
    + 9522 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    - 9522 * (X 0) ^ 5 * (X 2) ^ 8
    + 2160 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    - 2160 * (X 0) ^ 4 * (X 2) ^ 9

public noncomputable def jAff_c58 : MvPolynomial (Fin 3) ℚ :=
  -2160 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 10
    + 17739 * (X 0) ^ 6 * (X 1) ^ 3 * (X 2) ^ 6
    - 12204 * (X 0) ^ 5 * (X 1) ^ 3 * (X 2) ^ 7
    + 7560 * (X 0) ^ 4 * (X 1) ^ 3 * (X 2) ^ 8
    + 16740 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 9

public noncomputable def quotJ_c58 : MvPolynomial (Fin 3) ℚ :=
  -2160 * (X 0) ^ 3 * (X 2) ^ 9
    + 17739 * (X 0) ^ 6 * (X 2) ^ 5
    - 12204 * (X 0) ^ 5 * (X 2) ^ 6
    + 7560 * (X 0) ^ 4 * (X 2) ^ 7
    + 16740 * (X 0) ^ 3 * (X 2) ^ 8

public noncomputable def redJ_c58 : MvPolynomial (Fin 3) ℚ :=
  -2160 * (X 0) ^ 6 * (X 2) ^ 9
    + 2160 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 10
    + 17739 * (X 0) ^ 9 * (X 2) ^ 5
    - 12204 * (X 0) ^ 8 * (X 2) ^ 6
    + 7560 * (X 0) ^ 7 * (X 2) ^ 7
    - 17739 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 6
    + 16740 * (X 0) ^ 6 * (X 2) ^ 8
    + 12204 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 7
    - 7560 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    + 2160 * (X 0) ^ 4 * (X 2) ^ 10
    - 16740 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    - 17739 * (X 0) ^ 7 * (X 2) ^ 6
    + 12204 * (X 0) ^ 6 * (X 2) ^ 7
    - 7560 * (X 0) ^ 5 * (X 2) ^ 8
    - 16740 * (X 0) ^ 4 * (X 2) ^ 9
    + 2160 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    - 2160 * (X 0) ^ 3 * (X 2) ^ 10
    - 17739 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    + 17739 * (X 0) ^ 6 * (X 2) ^ 6
    + 12204 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    - 12204 * (X 0) ^ 5 * (X 2) ^ 7
    - 7560 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 7560 * (X 0) ^ 4 * (X 2) ^ 8
    - 16740 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    + 16740 * (X 0) ^ 3 * (X 2) ^ 9

public noncomputable def jAff_c59 : MvPolynomial (Fin 3) ℚ :=
  7380 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 10
    + 216 * (X 0) * (X 1) ^ 3 * (X 2) ^ 11
    + 3699 * (X 0) ^ 6 * (X 1) ^ 3 * (X 2) ^ 5
    - 5346 * (X 0) ^ 5 * (X 1) ^ 3 * (X 2) ^ 6
    - 8100 * (X 0) ^ 4 * (X 1) ^ 3 * (X 2) ^ 7

public noncomputable def quotJ_c59 : MvPolynomial (Fin 3) ℚ :=
  7380 * (X 0) ^ 2 * (X 2) ^ 9
    + 216 * (X 0) * (X 2) ^ 10
    + 3699 * (X 0) ^ 6 * (X 2) ^ 4
    - 5346 * (X 0) ^ 5 * (X 2) ^ 5
    - 8100 * (X 0) ^ 4 * (X 2) ^ 6

public noncomputable def redJ_c59 : MvPolynomial (Fin 3) ℚ :=
  7380 * (X 0) ^ 5 * (X 2) ^ 9
    + 216 * (X 0) ^ 4 * (X 2) ^ 10
    - 7380 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 10
    - 216 * (X 0) * (X 1) ^ 2 * (X 2) ^ 11
    + 3699 * (X 0) ^ 9 * (X 2) ^ 4
    - 5346 * (X 0) ^ 8 * (X 2) ^ 5
    - 8100 * (X 0) ^ 7 * (X 2) ^ 6
    - 3699 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 5
    + 5346 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    + 8100 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 7380 * (X 0) ^ 3 * (X 2) ^ 10
    - 216 * (X 0) ^ 2 * (X 2) ^ 11
    - 3699 * (X 0) ^ 7 * (X 2) ^ 5
    + 5346 * (X 0) ^ 6 * (X 2) ^ 6
    + 8100 * (X 0) ^ 5 * (X 2) ^ 7
    - 7380 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 7380 * (X 0) ^ 2 * (X 2) ^ 10
    - 216 * (X 0) * (X 1) * (X 2) ^ 10
    + 216 * (X 0) * (X 2) ^ 11
    - 3699 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    + 3699 * (X 0) ^ 6 * (X 2) ^ 5
    + 5346 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    - 5346 * (X 0) ^ 5 * (X 2) ^ 6
    + 8100 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 8100 * (X 0) ^ 4 * (X 2) ^ 7

public noncomputable def jAff_c60 : MvPolynomial (Fin 3) ℚ :=
  3420 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 8
    - 57015 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 9
    - 11706 * (X 0) * (X 1) ^ 3 * (X 2) ^ 10
    - 408 * (X 1) ^ 3 * (X 2) ^ 11
    + 2457 * (X 0) ^ 6 * (X 1) ^ 3 * (X 2) ^ 4

public noncomputable def quotJ_c60 : MvPolynomial (Fin 3) ℚ :=
  3420 * (X 0) ^ 3 * (X 2) ^ 7
    - 57015 * (X 0) ^ 2 * (X 2) ^ 8
    - 11706 * (X 0) * (X 2) ^ 9
    - 408 * (X 2) ^ 10
    + 2457 * (X 0) ^ 6 * (X 2) ^ 3

public noncomputable def redJ_c60 : MvPolynomial (Fin 3) ℚ :=
  3420 * (X 0) ^ 6 * (X 2) ^ 7
    - 57015 * (X 0) ^ 5 * (X 2) ^ 8
    - 11706 * (X 0) ^ 4 * (X 2) ^ 9
    - 3420 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    - 408 * (X 0) ^ 3 * (X 2) ^ 10
    + 57015 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 11706 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    + 408 * (X 1) ^ 2 * (X 2) ^ 11
    + 2457 * (X 0) ^ 9 * (X 2) ^ 3
    - 2457 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 4
    - 3420 * (X 0) ^ 4 * (X 2) ^ 8
    + 57015 * (X 0) ^ 3 * (X 2) ^ 9
    + 11706 * (X 0) ^ 2 * (X 2) ^ 10
    + 408 * (X 0) * (X 2) ^ 11
    - 2457 * (X 0) ^ 7 * (X 2) ^ 4
    - 3420 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 3420 * (X 0) ^ 3 * (X 2) ^ 8
    + 57015 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 57015 * (X 0) ^ 2 * (X 2) ^ 9
    + 11706 * (X 0) * (X 1) * (X 2) ^ 9
    - 11706 * (X 0) * (X 2) ^ 10
    + 408 * (X 1) * (X 2) ^ 10
    - 408 * (X 2) ^ 11
    - 2457 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    + 2457 * (X 0) ^ 6 * (X 2) ^ 4

public noncomputable def jAff_c61 : MvPolynomial (Fin 3) ℚ :=
  1944 * (X 0) ^ 5 * (X 1) ^ 3 * (X 2) ^ 5
    + 19620 * (X 0) ^ 4 * (X 1) ^ 3 * (X 2) ^ 6
    + 7020 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 7
    + 23355 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 8
    + 76518 * (X 0) * (X 1) ^ 3 * (X 2) ^ 9

public noncomputable def quotJ_c61 : MvPolynomial (Fin 3) ℚ :=
  1944 * (X 0) ^ 5 * (X 2) ^ 4
    + 19620 * (X 0) ^ 4 * (X 2) ^ 5
    + 7020 * (X 0) ^ 3 * (X 2) ^ 6
    + 23355 * (X 0) ^ 2 * (X 2) ^ 7
    + 76518 * (X 0) * (X 2) ^ 8

public noncomputable def redJ_c61 : MvPolynomial (Fin 3) ℚ :=
  1944 * (X 0) ^ 8 * (X 2) ^ 4
    + 19620 * (X 0) ^ 7 * (X 2) ^ 5
    + 7020 * (X 0) ^ 6 * (X 2) ^ 6
    - 1944 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 5
    + 23355 * (X 0) ^ 5 * (X 2) ^ 7
    - 19620 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    + 76518 * (X 0) ^ 4 * (X 2) ^ 8
    - 7020 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    - 23355 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 76518 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 1944 * (X 0) ^ 6 * (X 2) ^ 5
    - 19620 * (X 0) ^ 5 * (X 2) ^ 6
    - 7020 * (X 0) ^ 4 * (X 2) ^ 7
    - 23355 * (X 0) ^ 3 * (X 2) ^ 8
    - 76518 * (X 0) ^ 2 * (X 2) ^ 9
    - 1944 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    + 1944 * (X 0) ^ 5 * (X 2) ^ 5
    - 19620 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 19620 * (X 0) ^ 4 * (X 2) ^ 6
    - 7020 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 7020 * (X 0) ^ 3 * (X 2) ^ 7
    - 23355 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 23355 * (X 0) ^ 2 * (X 2) ^ 8
    - 76518 * (X 0) * (X 1) * (X 2) ^ 8
    + 76518 * (X 0) * (X 2) ^ 9

public noncomputable def jAff_c62 : MvPolynomial (Fin 3) ℚ :=
  9378 * (X 1) ^ 3 * (X 2) ^ 10
    + 972 * (X 0) ^ 6 * (X 1) ^ 3 * (X 2) ^ 3
    - 15660 * (X 0) ^ 4 * (X 1) ^ 3 * (X 2) ^ 5
    - 540 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 6
    - 6165 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 7

public noncomputable def quotJ_c62 : MvPolynomial (Fin 3) ℚ :=
  9378 * (X 2) ^ 9
    + 972 * (X 0) ^ 6 * (X 2) ^ 2
    - 15660 * (X 0) ^ 4 * (X 2) ^ 4
    - 540 * (X 0) ^ 3 * (X 2) ^ 5
    - 6165 * (X 0) ^ 2 * (X 2) ^ 6

public noncomputable def redJ_c62 : MvPolynomial (Fin 3) ℚ :=
  9378 * (X 0) ^ 3 * (X 2) ^ 9
    - 9378 * (X 1) ^ 2 * (X 2) ^ 10
    + 972 * (X 0) ^ 9 * (X 2) ^ 2
    - 15660 * (X 0) ^ 7 * (X 2) ^ 4
    - 972 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 3
    - 540 * (X 0) ^ 6 * (X 2) ^ 5
    - 6165 * (X 0) ^ 5 * (X 2) ^ 6
    + 15660 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    + 540 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 6165 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    - 9378 * (X 0) * (X 2) ^ 10
    - 972 * (X 0) ^ 7 * (X 2) ^ 3
    + 15660 * (X 0) ^ 5 * (X 2) ^ 5
    + 540 * (X 0) ^ 4 * (X 2) ^ 6
    + 6165 * (X 0) ^ 3 * (X 2) ^ 7
    - 9378 * (X 1) * (X 2) ^ 9
    + 9378 * (X 2) ^ 10
    - 972 * (X 0) ^ 6 * (X 1) * (X 2) ^ 2
    + 972 * (X 0) ^ 6 * (X 2) ^ 3
    + 15660 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 15660 * (X 0) ^ 4 * (X 2) ^ 5
    + 540 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 540 * (X 0) ^ 3 * (X 2) ^ 6
    + 6165 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 6165 * (X 0) ^ 2 * (X 2) ^ 7

public noncomputable def jAff_c63 : MvPolynomial (Fin 3) ℚ :=
  -31842 * (X 0) * (X 1) ^ 3 * (X 2) ^ 8
    - 47907 * (X 1) ^ 3 * (X 2) ^ 9
    + 1620 * (X 0) ^ 4 * (X 1) ^ 3 * (X 2) ^ 4
    + 14580 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 5
    + 5625 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 6

public noncomputable def quotJ_c63 : MvPolynomial (Fin 3) ℚ :=
  -31842 * (X 0) * (X 2) ^ 7
    - 47907 * (X 2) ^ 8
    + 1620 * (X 0) ^ 4 * (X 2) ^ 3
    + 14580 * (X 0) ^ 3 * (X 2) ^ 4
    + 5625 * (X 0) ^ 2 * (X 2) ^ 5

public noncomputable def redJ_c63 : MvPolynomial (Fin 3) ℚ :=
  -31842 * (X 0) ^ 4 * (X 2) ^ 7
    - 47907 * (X 0) ^ 3 * (X 2) ^ 8
    + 31842 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 47907 * (X 1) ^ 2 * (X 2) ^ 9
    + 1620 * (X 0) ^ 7 * (X 2) ^ 3
    + 14580 * (X 0) ^ 6 * (X 2) ^ 4
    + 5625 * (X 0) ^ 5 * (X 2) ^ 5
    - 1620 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    - 14580 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 5625 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    + 31842 * (X 0) ^ 2 * (X 2) ^ 8
    + 47907 * (X 0) * (X 2) ^ 9
    - 1620 * (X 0) ^ 5 * (X 2) ^ 4
    - 14580 * (X 0) ^ 4 * (X 2) ^ 5
    - 5625 * (X 0) ^ 3 * (X 2) ^ 6
    + 31842 * (X 0) * (X 1) * (X 2) ^ 7
    - 31842 * (X 0) * (X 2) ^ 8
    + 47907 * (X 1) * (X 2) ^ 8
    - 47907 * (X 2) ^ 9
    - 1620 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    + 1620 * (X 0) ^ 4 * (X 2) ^ 4
    - 14580 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 14580 * (X 0) ^ 3 * (X 2) ^ 5
    - 5625 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 5625 * (X 0) ^ 2 * (X 2) ^ 6

public noncomputable def jAff_c64 : MvPolynomial (Fin 3) ℚ :=
  11034 * (X 0) * (X 1) ^ 3 * (X 2) ^ 7
    + 17517 * (X 1) ^ 3 * (X 2) ^ 8
    + 9720 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 4
    - 2700 * (X 0) ^ 2 * (X 1) ^ 3 * (X 2) ^ 5
    - 12798 * (X 0) * (X 1) ^ 3 * (X 2) ^ 6

public noncomputable def quotJ_c64 : MvPolynomial (Fin 3) ℚ :=
  11034 * (X 0) * (X 2) ^ 6
    + 17517 * (X 2) ^ 7
    + 9720 * (X 0) ^ 3 * (X 2) ^ 3
    - 2700 * (X 0) ^ 2 * (X 2) ^ 4
    - 12798 * (X 0) * (X 2) ^ 5

public noncomputable def redJ_c64 : MvPolynomial (Fin 3) ℚ :=
  11034 * (X 0) ^ 4 * (X 2) ^ 6
    + 17517 * (X 0) ^ 3 * (X 2) ^ 7
    - 11034 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    - 17517 * (X 1) ^ 2 * (X 2) ^ 8
    + 9720 * (X 0) ^ 6 * (X 2) ^ 3
    - 2700 * (X 0) ^ 5 * (X 2) ^ 4
    - 12798 * (X 0) ^ 4 * (X 2) ^ 5
    - 9720 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 2700 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    - 11034 * (X 0) ^ 2 * (X 2) ^ 7
    + 12798 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    - 17517 * (X 0) * (X 2) ^ 8
    - 9720 * (X 0) ^ 4 * (X 2) ^ 4
    + 2700 * (X 0) ^ 3 * (X 2) ^ 5
    + 12798 * (X 0) ^ 2 * (X 2) ^ 6
    - 11034 * (X 0) * (X 1) * (X 2) ^ 6
    + 11034 * (X 0) * (X 2) ^ 7
    - 17517 * (X 1) * (X 2) ^ 7
    + 17517 * (X 2) ^ 8
    - 9720 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 9720 * (X 0) ^ 3 * (X 2) ^ 4
    + 2700 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    - 2700 * (X 0) ^ 2 * (X 2) ^ 5
    + 12798 * (X 0) * (X 1) * (X 2) ^ 5
    - 12798 * (X 0) * (X 2) ^ 6

public noncomputable def jAff_c65 : MvPolynomial (Fin 3) ℚ :=
  -13677 * (X 1) ^ 3 * (X 2) ^ 7
    - 540 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 3
    + 1044 * (X 0) * (X 1) ^ 3 * (X 2) ^ 5
    + 8550 * (X 1) ^ 3 * (X 2) ^ 6
    + 2160 * (X 0) ^ 3 * (X 1) ^ 3 * (X 2) ^ 2

public noncomputable def quotJ_c65 : MvPolynomial (Fin 3) ℚ :=
  -13677 * (X 2) ^ 6
    - 540 * (X 0) ^ 3 * (X 2) ^ 2
    + 1044 * (X 0) * (X 2) ^ 4
    + 8550 * (X 2) ^ 5
    + 2160 * (X 0) ^ 3 * (X 2)

public noncomputable def redJ_c65 : MvPolynomial (Fin 3) ℚ :=
  -13677 * (X 0) ^ 3 * (X 2) ^ 6
    + 13677 * (X 1) ^ 2 * (X 2) ^ 7
    - 540 * (X 0) ^ 6 * (X 2) ^ 2
    + 1044 * (X 0) ^ 4 * (X 2) ^ 4
    + 540 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 8550 * (X 0) ^ 3 * (X 2) ^ 5
    - 1044 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + 13677 * (X 0) * (X 2) ^ 7
    - 8550 * (X 1) ^ 2 * (X 2) ^ 6
    + 2160 * (X 0) ^ 6 * (X 2)
    + 540 * (X 0) ^ 4 * (X 2) ^ 3
    - 2160 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    - 1044 * (X 0) ^ 2 * (X 2) ^ 5
    - 8550 * (X 0) * (X 2) ^ 6
    + 13677 * (X 1) * (X 2) ^ 6
    - 13677 * (X 2) ^ 7
    - 2160 * (X 0) ^ 4 * (X 2) ^ 2
    + 540 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    - 540 * (X 0) ^ 3 * (X 2) ^ 3
    - 1044 * (X 0) * (X 1) * (X 2) ^ 4
    + 1044 * (X 0) * (X 2) ^ 5
    - 8550 * (X 1) * (X 2) ^ 5
    + 8550 * (X 2) ^ 6
    - 2160 * (X 0) ^ 3 * (X 1) * (X 2)
    + 2160 * (X 0) ^ 3 * (X 2) ^ 2

public noncomputable def jAff_c66 : MvPolynomial (Fin 3) ℚ :=
  -90 * (X 0) * (X 1) ^ 3 * (X 2) ^ 4
    - 2403 * (X 1) ^ 3 * (X 2) ^ 5
    + 216 * (X 0) * (X 1) ^ 3 * (X 2) ^ 3
    + 27 * (X 1) ^ 3 * (X 2) ^ 4
    - 453 * (X 1) ^ 3 * (X 2) ^ 3

public noncomputable def quotJ_c66 : MvPolynomial (Fin 3) ℚ :=
  -90 * (X 0) * (X 2) ^ 3
    - 2403 * (X 2) ^ 4
    + 216 * (X 0) * (X 2) ^ 2
    + 27 * (X 2) ^ 3
    - 453 * (X 2) ^ 2

public noncomputable def redJ_c66 : MvPolynomial (Fin 3) ℚ :=
  -90 * (X 0) ^ 4 * (X 2) ^ 3
    - 2403 * (X 0) ^ 3 * (X 2) ^ 4
    + 90 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 2403 * (X 1) ^ 2 * (X 2) ^ 5
    + 216 * (X 0) ^ 4 * (X 2) ^ 2
    + 27 * (X 0) ^ 3 * (X 2) ^ 3
    + 90 * (X 0) ^ 2 * (X 2) ^ 4
    - 216 * (X 0) * (X 1) ^ 2 * (X 2) ^ 3
    + 2403 * (X 0) * (X 2) ^ 5
    - 27 * (X 1) ^ 2 * (X 2) ^ 4
    - 453 * (X 0) ^ 3 * (X 2) ^ 2
    - 216 * (X 0) ^ 2 * (X 2) ^ 3
    + 90 * (X 0) * (X 1) * (X 2) ^ 3
    - 117 * (X 0) * (X 2) ^ 4
    + 453 * (X 1) ^ 2 * (X 2) ^ 3
    + 2403 * (X 1) * (X 2) ^ 4
    - 2403 * (X 2) ^ 5
    - 216 * (X 0) * (X 1) * (X 2) ^ 2
    + 669 * (X 0) * (X 2) ^ 3
    - 27 * (X 1) * (X 2) ^ 3
    + 27 * (X 2) ^ 4
    + 453 * (X 1) * (X 2) ^ 2
    - 453 * (X 2) ^ 3

public noncomputable def jAff_low : MvPolynomial (Fin 3) ℚ :=
  -675 * (X 0) ^ 9 * (X 2) ^ 7
    + 675 * (X 0) ^ 8 * (X 1) * (X 2) ^ 7
    + 486 * (X 0) ^ 8 * (X 2) ^ 8
    - 648 * (X 0) ^ 7 * (X 1) * (X 2) ^ 8
    - 2484 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 8
    + 1944 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 9
    - 243 * (X 0) ^ 9 * (X 2) ^ 6
    - 1782 * (X 0) ^ 8 * (X 1) * (X 2) ^ 6
    + 5832 * (X 0) ^ 8 * (X 2) ^ 7
    - 1782 * (X 0) ^ 7 * (X 1) * (X 2) ^ 7
    - 5616 * (X 0) ^ 7 * (X 2) ^ 8
    + 14499 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 7
    + 4644 * (X 0) ^ 6 * (X 1) * (X 2) ^ 8
    + 432 * (X 0) ^ 6 * (X 2) ^ 9
    - 13122 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 8
    + 216 * (X 0) ^ 5 * (X 1) * (X 2) ^ 9
    - 720 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    - 2160 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 10
    - 729 * (X 0) ^ 8 * (X 1) * (X 2) ^ 5
    + 3618 * (X 0) ^ 8 * (X 2) ^ 6
    + 8262 * (X 0) ^ 7 * (X 1) * (X 2) ^ 6
    - 18063 * (X 0) ^ 7 * (X 2) ^ 7
    + 13203 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 6
    - 4266 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    + 22950 * (X 0) ^ 6 * (X 2) ^ 8
    + 5400 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 7
    - 19062 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    - 3222 * (X 0) ^ 5 * (X 2) ^ 9
    + 5940 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    + 2250 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    + 108 * (X 0) ^ 4 * (X 2) ^ 10
    + 14580 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    - 792 * (X 0) ^ 3 * (X 1) * (X 2) ^ 10
    + 5580 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 10
    + 216 * (X 0) * (X 1) ^ 2 * (X 2) ^ 11
    + 8910 * (X 0) ^ 7 * (X 1) * (X 2) ^ 5
    - 14985 * (X 0) ^ 7 * (X 2) ^ 6
    + 8991 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 5
    - 12555 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    + 27351 * (X 0) ^ 6 * (X 2) ^ 7
    - 22842 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    + 41148 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    - 42741 * (X 0) ^ 5 * (X 2) ^ 8
    - 24300 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    + 13590 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 8262 * (X 0) ^ 4 * (X 2) ^ 9
    + 3240 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 918 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    - 504 * (X 0) ^ 3 * (X 2) ^ 10
    - 38205 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    + 1908 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    - 8442 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    + 72 * (X 0) * (X 1) * (X 2) ^ 11
    - 264 * (X 1) ^ 2 * (X 2) ^ 11
    + 486 * (X 0) ^ 8 * (X 2) ^ 4
    - 1134 * (X 0) ^ 7 * (X 1) * (X 2) ^ 4
    - 729 * (X 0) ^ 7 * (X 2) ^ 5
    + 11745 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 4
    - 11745 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    + 19089 * (X 0) ^ 6 * (X 2) ^ 6
    - 6804 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 5
    + 17658 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    - 27675 * (X 0) ^ 5 * (X 2) ^ 7
    + 34020 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 48870 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 38304 * (X 0) ^ 4 * (X 2) ^ 8
    + 14310 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 324 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 8361 * (X 0) ^ 3 * (X 2) ^ 9
    - 3105 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 8622 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 666 * (X 0) ^ 2 * (X 2) ^ 10
    + 47430 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    - 2826 * (X 0) * (X 1) * (X 2) ^ 10
    + 33 * (X 0) * (X 2) ^ 11
    + 5562 * (X 1) ^ 2 * (X 2) ^ 10
    - 69 * (X 1) * (X 2) ^ 11
    - 2 * (X 2) ^ 12
    + 1944 * (X 0) ^ 7 * (X 1) * (X 2) ^ 3
    - 2835 * (X 0) ^ 7 * (X 2) ^ 4
    - 810 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 3
    + 4131 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    + 4293 * (X 0) ^ 6 * (X 2) ^ 5
    - 1080 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    - 3159 * (X 0) ^ 5 * (X 2) ^ 6
    + 14940 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 36450 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 30114 * (X 0) ^ 4 * (X 2) ^ 7
    - 14985 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    + 30348 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 21762 * (X 0) ^ 3 * (X 2) ^ 8
    - 6075 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    - 9531 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 4761 * (X 0) ^ 2 * (X 2) ^ 9
    + 1548 * (X 0) * (X 1) ^ 2 * (X 2) ^ 8
    + 14130 * (X 0) * (X 1) * (X 2) ^ 9
    - 936 * (X 0) * (X 2) ^ 10
    - 25245 * (X 1) ^ 2 * (X 2) ^ 9
    + 1536 * (X 1) * (X 2) ^ 10
    + 18 * (X 2) ^ 11
    - 324 * (X 0) ^ 7 * (X 2) ^ 3
    + 1944 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 2
    - 2997 * (X 0) ^ 6 * (X 1) * (X 2) ^ 3
    + 3915 * (X 0) ^ 6 * (X 2) ^ 4
    + 1296 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    - 3249 * (X 0) ^ 5 * (X 2) ^ 5
    - 2160 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 2430 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 3618 * (X 0) ^ 4 * (X 2) ^ 6
    - 19575 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    + 30258 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    - 18846 * (X 0) ^ 3 * (X 2) ^ 7
    + 4905 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 11097 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    + 4653 * (X 0) ^ 2 * (X 2) ^ 8
    + 16497 * (X 0) * (X 1) ^ 2 * (X 2) ^ 7
    + 3042 * (X 0) * (X 1) * (X 2) ^ 8
    + 1017 * (X 0) * (X 2) ^ 9
    - 1863 * (X 1) ^ 2 * (X 2) ^ 8
    - 6678 * (X 1) * (X 2) ^ 9
    + 168 * (X 2) ^ 10
    + 324 * (X 0) ^ 6 * (X 1) * (X 2) ^ 2
    + 1944 * (X 0) ^ 6 * (X 2) ^ 3
    - 702 * (X 0) ^ 5 * (X 2) ^ 4
    + 3240 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    - 7200 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    + 5562 * (X 0) ^ 4 * (X 2) ^ 5
    + 6885 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    - 54 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    - 4266 * (X 0) ^ 3 * (X 2) ^ 6
    - 540 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 5
    - 1161 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    + 243 * (X 0) ^ 2 * (X 2) ^ 7
    - 1773 * (X 0) * (X 1) ^ 2 * (X 2) ^ 6
    + 8208 * (X 0) * (X 1) * (X 2) ^ 7
    + 171 * (X 0) * (X 2) ^ 8
    - 12432 * (X 1) ^ 2 * (X 2) ^ 7
    - 1755 * (X 1) * (X 2) ^ 8
    - 669 * (X 2) ^ 9
    - 54 * (X 0) ^ 6 * (X 2) ^ 2
    - 270 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    + 1458 * (X 0) ^ 4 * (X 2) ^ 4
    - 4995 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 3
    + 6912 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 3987 * (X 0) ^ 3 * (X 2) ^ 5
    - 657 * (X 0) ^ 2 * (X 1) * (X 2) ^ 5
    + 315 * (X 0) ^ 2 * (X 2) ^ 6
    + 837 * (X 0) * (X 1) ^ 2 * (X 2) ^ 5
    + 1620 * (X 0) * (X 1) * (X 2) ^ 6
    + 1248 * (X 0) * (X 2) ^ 7
    + 90 * (X 1) ^ 2 * (X 2) ^ 6
    - 5112 * (X 1) * (X 2) ^ 7
    - 195 * (X 2) ^ 8
    + 216 * (X 0) ^ 6 * (X 2)
    - 18 * (X 0) ^ 4 * (X 2) ^ 3
    + 540 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 2
    + 1620 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    - 1944 * (X 0) ^ 3 * (X 2) ^ 4
    - 216 * (X 0) ^ 2 * (X 1) * (X 2) ^ 4
    + 108 * (X 0) ^ 2 * (X 2) ^ 5
    - 585 * (X 0) * (X 1) ^ 2 * (X 2) ^ 4
    + 1278 * (X 0) * (X 1) * (X 2) ^ 5
    + 315 * (X 0) * (X 2) ^ 6
    - 1539 * (X 1) ^ 2 * (X 2) ^ 5
    - 1731 * (X 1) * (X 2) ^ 6
    - 693 * (X 2) ^ 7
    + 108 * (X 0) ^ 4 * (X 2) ^ 2
    - 54 * (X 0) ^ 3 * (X 1) * (X 2) ^ 2
    + 54 * (X 0) ^ 3 * (X 2) ^ 3
    - 18 * (X 0) ^ 2 * (X 2) ^ 4
    + 216 * (X 0) * (X 1) * (X 2) ^ 4
    + 324 * (X 0) * (X 2) ^ 5
    + 297 * (X 1) ^ 2 * (X 2) ^ 4
    - 1206 * (X 1) * (X 2) ^ 5
    - 315 * (X 2) ^ 6
    + 216 * (X 0) ^ 3 * (X 1) * (X 2)
    - 216 * (X 0) ^ 3 * (X 2) ^ 2
    + 36 * (X 0) * (X 1) * (X 2) ^ 3
    + 90 * (X 0) * (X 2) ^ 4
    - 108 * (X 1) ^ 2 * (X 2) ^ 3
    - 405 * (X 1) * (X 2) ^ 4
    - 237 * (X 2) ^ 5
    + 27 * (X 0) * (X 2) ^ 3
    - 18 * (X 1) ^ 2 * (X 2) ^ 2
    - 108 * (X 1) * (X 2) ^ 3
    - 141 * (X 2) ^ 4
    + 9 * (X 0) * (X 2) ^ 2
    - 27 * (X 1) * (X 2) ^ 2
    - 27 * (X 2) ^ 3
    - 9 * (X 1) * (X 2)
    - 27 * (X 2) ^ 2
    - 2

/-- Full affine Jacobian covariant (integer form `27³ J`). -/
public noncomputable def jAff : MvPolynomial (Fin 3) ℚ :=
  jAff_c0 +
  jAff_c1 +
  jAff_c2 +
  jAff_c3 +
  jAff_c4 +
  jAff_c5 +
  jAff_c6 +
  jAff_c7 +
  jAff_c8 +
  jAff_c9 +
  jAff_c10 +
  jAff_c11 +
  jAff_c12 +
  jAff_c13 +
  jAff_c14 +
  jAff_c15 +
  jAff_c16 +
  jAff_c17 +
  jAff_c18 +
  jAff_c19 +
  jAff_c20 +
  jAff_c21 +
  jAff_c22 +
  jAff_c23 +
  jAff_c24 +
  jAff_c25 +
  jAff_c26 +
  jAff_c27 +
  jAff_c28 +
  jAff_c29 +
  jAff_c30 +
  jAff_c31 +
  jAff_c32 +
  jAff_c33 +
  jAff_c34 +
  jAff_c35 +
  jAff_c36 +
  jAff_c37 +
  jAff_c38 +
  jAff_c39 +
  jAff_c40 +
  jAff_c41 +
  jAff_c42 +
  jAff_c43 +
  jAff_c44 +
  jAff_c45 +
  jAff_c46 +
  jAff_c47 +
  jAff_c48 +
  jAff_c49 +
  jAff_c50 +
  jAff_c51 +
  jAff_c52 +
  jAff_c53 +
  jAff_c54 +
  jAff_c55 +
  jAff_c56 +
  jAff_c57 +
  jAff_c58 +
  jAff_c59 +
  jAff_c60 +
  jAff_c61 +
  jAff_c62 +
  jAff_c63 +
  jAff_c64 +
  jAff_c65 +
  jAff_c66 +
  jAff_low

public noncomputable def quotJ : MvPolynomial (Fin 3) ℚ :=
  quotJ_c0 +
  quotJ_c1 +
  quotJ_c2 +
  quotJ_c3 +
  quotJ_c4 +
  quotJ_c5 +
  quotJ_c6 +
  quotJ_c7 +
  quotJ_c8 +
  quotJ_c9 +
  quotJ_c10 +
  quotJ_c11 +
  quotJ_c12 +
  quotJ_c13 +
  quotJ_c14 +
  quotJ_c15 +
  quotJ_c16 +
  quotJ_c17 +
  quotJ_c18 +
  quotJ_c19 +
  quotJ_c20 +
  quotJ_c21 +
  quotJ_c22 +
  quotJ_c23 +
  quotJ_c24 +
  quotJ_c25 +
  quotJ_c26 +
  quotJ_c27 +
  quotJ_c28 +
  quotJ_c29 +
  quotJ_c30 +
  quotJ_c31 +
  quotJ_c32 +
  quotJ_c33 +
  quotJ_c34 +
  quotJ_c35 +
  quotJ_c36 +
  quotJ_c37 +
  quotJ_c38 +
  quotJ_c39 +
  quotJ_c40 +
  quotJ_c41 +
  quotJ_c42 +
  quotJ_c43 +
  quotJ_c44 +
  quotJ_c45 +
  quotJ_c46 +
  quotJ_c47 +
  quotJ_c48 +
  quotJ_c49 +
  quotJ_c50 +
  quotJ_c51 +
  quotJ_c52 +
  quotJ_c53 +
  quotJ_c54 +
  quotJ_c55 +
  quotJ_c56 +
  quotJ_c57 +
  quotJ_c58 +
  quotJ_c59 +
  quotJ_c60 +
  quotJ_c61 +
  quotJ_c62 +
  quotJ_c63 +
  quotJ_c64 +
  quotJ_c65 +
  quotJ_c66

public noncomputable def redJ : MvPolynomial (Fin 3) ℚ :=
  redJ_c0 +
  redJ_c1 +
  redJ_c2 +
  redJ_c3 +
  redJ_c4 +
  redJ_c5 +
  redJ_c6 +
  redJ_c7 +
  redJ_c8 +
  redJ_c9 +
  redJ_c10 +
  redJ_c11 +
  redJ_c12 +
  redJ_c13 +
  redJ_c14 +
  redJ_c15 +
  redJ_c16 +
  redJ_c17 +
  redJ_c18 +
  redJ_c19 +
  redJ_c20 +
  redJ_c21 +
  redJ_c22 +
  redJ_c23 +
  redJ_c24 +
  redJ_c25 +
  redJ_c26 +
  redJ_c27 +
  redJ_c28 +
  redJ_c29 +
  redJ_c30 +
  redJ_c31 +
  redJ_c32 +
  redJ_c33 +
  redJ_c34 +
  redJ_c35 +
  redJ_c36 +
  redJ_c37 +
  redJ_c38 +
  redJ_c39 +
  redJ_c40 +
  redJ_c41 +
  redJ_c42 +
  redJ_c43 +
  redJ_c44 +
  redJ_c45 +
  redJ_c46 +
  redJ_c47 +
  redJ_c48 +
  redJ_c49 +
  redJ_c50 +
  redJ_c51 +
  redJ_c52 +
  redJ_c53 +
  redJ_c54 +
  redJ_c55 +
  redJ_c56 +
  redJ_c57 +
  redJ_c58 +
  redJ_c59 +
  redJ_c60 +
  redJ_c61 +
  redJ_c62 +
  redJ_c63 +
  redJ_c64 +
  redJ_c65 +
  redJ_c66 +
  jAff_low

/-- Batch 0: `Y`-deg 9, input=1, quot=30, red=52. -/
public theorem jAff_c0_mod :
    jAff_c0 = quotJ_c0 * gAff + redJ_c0 := by
  unfold jAff_c0 quotJ_c0 gAff redJ_c0
  ring

/-- Batch 1: `Y`-deg 9, input=1, quot=30, red=52. -/
public theorem jAff_c1_mod :
    jAff_c1 = quotJ_c1 * gAff + redJ_c1 := by
  unfold jAff_c1 quotJ_c1 gAff redJ_c1
  ring

/-- Batch 2: `Y`-deg 9, input=1, quot=30, red=52. -/
public theorem jAff_c2_mod :
    jAff_c2 = quotJ_c2 * gAff + redJ_c2 := by
  unfold jAff_c2 quotJ_c2 gAff redJ_c2
  ring

/-- Batch 3: `Y`-deg 9, input=1, quot=30, red=52. -/
public theorem jAff_c3_mod :
    jAff_c3 = quotJ_c3 * gAff + redJ_c3 := by
  unfold jAff_c3 quotJ_c3 gAff redJ_c3
  ring

/-- Batch 4: `Y`-deg 9, input=1, quot=30, red=52. -/
public theorem jAff_c4_mod :
    jAff_c4 = quotJ_c4 * gAff + redJ_c4 := by
  unfold jAff_c4 quotJ_c4 gAff redJ_c4
  ring

/-- Batch 5: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c5_mod :
    jAff_c5 = quotJ_c5 * gAff + redJ_c5 := by
  unfold jAff_c5 quotJ_c5 gAff redJ_c5
  ring

/-- Batch 6: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c6_mod :
    jAff_c6 = quotJ_c6 * gAff + redJ_c6 := by
  unfold jAff_c6 quotJ_c6 gAff redJ_c6
  ring

/-- Batch 7: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c7_mod :
    jAff_c7 = quotJ_c7 * gAff + redJ_c7 := by
  unfold jAff_c7 quotJ_c7 gAff redJ_c7
  ring

/-- Batch 8: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c8_mod :
    jAff_c8 = quotJ_c8 * gAff + redJ_c8 := by
  unfold jAff_c8 quotJ_c8 gAff redJ_c8
  ring

/-- Batch 9: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c9_mod :
    jAff_c9 = quotJ_c9 * gAff + redJ_c9 := by
  unfold jAff_c9 quotJ_c9 gAff redJ_c9
  ring

/-- Batch 10: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c10_mod :
    jAff_c10 = quotJ_c10 * gAff + redJ_c10 := by
  unfold jAff_c10 quotJ_c10 gAff redJ_c10
  ring

/-- Batch 11: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c11_mod :
    jAff_c11 = quotJ_c11 * gAff + redJ_c11 := by
  unfold jAff_c11 quotJ_c11 gAff redJ_c11
  ring

/-- Batch 12: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c12_mod :
    jAff_c12 = quotJ_c12 * gAff + redJ_c12 := by
  unfold jAff_c12 quotJ_c12 gAff redJ_c12
  ring

/-- Batch 13: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c13_mod :
    jAff_c13 = quotJ_c13 * gAff + redJ_c13 := by
  unfold jAff_c13 quotJ_c13 gAff redJ_c13
  ring

/-- Batch 14: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c14_mod :
    jAff_c14 = quotJ_c14 * gAff + redJ_c14 := by
  unfold jAff_c14 quotJ_c14 gAff redJ_c14
  ring

/-- Batch 15: `Y`-deg 8, input=1, quot=19, red=37. -/
public theorem jAff_c15_mod :
    jAff_c15 = quotJ_c15 * gAff + redJ_c15 := by
  unfold jAff_c15 quotJ_c15 gAff redJ_c15
  ring

/-- Batch 16: `Y`-deg 7, input=2, quot=21, red=44. -/
public theorem jAff_c16_mod :
    jAff_c16 = quotJ_c16 * gAff + redJ_c16 := by
  unfold jAff_c16 quotJ_c16 gAff redJ_c16
  ring

/-- Batch 17: `Y`-deg 7, input=2, quot=24, red=55. -/
public theorem jAff_c17_mod :
    jAff_c17 = quotJ_c17 * gAff + redJ_c17 := by
  unfold jAff_c17 quotJ_c17 gAff redJ_c17
  ring

/-- Batch 18: `Y`-deg 7, input=2, quot=24, red=55. -/
public theorem jAff_c18_mod :
    jAff_c18 = quotJ_c18 * gAff + redJ_c18 := by
  unfold jAff_c18 quotJ_c18 gAff redJ_c18
  ring

/-- Batch 19: `Y`-deg 7, input=2, quot=24, red=55. -/
public theorem jAff_c19_mod :
    jAff_c19 = quotJ_c19 * gAff + redJ_c19 := by
  unfold jAff_c19 quotJ_c19 gAff redJ_c19
  ring

/-- Batch 20: `Y`-deg 7, input=2, quot=24, red=55. -/
public theorem jAff_c20_mod :
    jAff_c20 = quotJ_c20 * gAff + redJ_c20 := by
  unfold jAff_c20 quotJ_c20 gAff redJ_c20
  ring

/-- Batch 21: `Y`-deg 7, input=2, quot=21, red=44. -/
public theorem jAff_c21_mod :
    jAff_c21 = quotJ_c21 * gAff + redJ_c21 := by
  unfold jAff_c21 quotJ_c21 gAff redJ_c21
  ring

/-- Batch 22: `Y`-deg 7, input=1, quot=12, red=29. -/
public theorem jAff_c22_mod :
    jAff_c22 = quotJ_c22 * gAff + redJ_c22 := by
  unfold jAff_c22 quotJ_c22 gAff redJ_c22
  ring

/-- Batch 23: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c23_mod :
    jAff_c23 = quotJ_c23 * gAff + redJ_c23 := by
  unfold jAff_c23 quotJ_c23 gAff redJ_c23
  ring

/-- Batch 24: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c24_mod :
    jAff_c24 = quotJ_c24 * gAff + redJ_c24 := by
  unfold jAff_c24 quotJ_c24 gAff redJ_c24
  ring

/-- Batch 25: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c25_mod :
    jAff_c25 = quotJ_c25 * gAff + redJ_c25 := by
  unfold jAff_c25 quotJ_c25 gAff redJ_c25
  ring

/-- Batch 26: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c26_mod :
    jAff_c26 = quotJ_c26 * gAff + redJ_c26 := by
  unfold jAff_c26 quotJ_c26 gAff redJ_c26
  ring

/-- Batch 27: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c27_mod :
    jAff_c27 = quotJ_c27 * gAff + redJ_c27 := by
  unfold jAff_c27 quotJ_c27 gAff redJ_c27
  ring

/-- Batch 28: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c28_mod :
    jAff_c28 = quotJ_c28 * gAff + redJ_c28 := by
  unfold jAff_c28 quotJ_c28 gAff redJ_c28
  ring

/-- Batch 29: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c29_mod :
    jAff_c29 = quotJ_c29 * gAff + redJ_c29 := by
  unfold jAff_c29 quotJ_c29 gAff redJ_c29
  ring

/-- Batch 30: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c30_mod :
    jAff_c30 = quotJ_c30 * gAff + redJ_c30 := by
  unfold jAff_c30 quotJ_c30 gAff redJ_c30
  ring

/-- Batch 31: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c31_mod :
    jAff_c31 = quotJ_c31 * gAff + redJ_c31 := by
  unfold jAff_c31 quotJ_c31 gAff redJ_c31
  ring

/-- Batch 32: `Y`-deg 6, input=2, quot=14, red=38. -/
public theorem jAff_c32_mod :
    jAff_c32 = quotJ_c32 * gAff + redJ_c32 := by
  unfold jAff_c32 quotJ_c32 gAff redJ_c32
  ring

/-- Batch 33: `Y`-deg 6, input=2, quot=14, red=39. -/
public theorem jAff_c33_mod :
    jAff_c33 = quotJ_c33 * gAff + redJ_c33 := by
  unfold jAff_c33 quotJ_c33 gAff redJ_c33
  ring

/-- Batch 34: `Y`-deg 6, input=2, quot=13, red=32. -/
public theorem jAff_c34_mod :
    jAff_c34 = quotJ_c34 * gAff + redJ_c34 := by
  unfold jAff_c34 quotJ_c34 gAff redJ_c34
  ring

/-- Batch 35: `Y`-deg 6, input=2, quot=13, red=32. -/
public theorem jAff_c35_mod :
    jAff_c35 = quotJ_c35 * gAff + redJ_c35 := by
  unfold jAff_c35 quotJ_c35 gAff redJ_c35
  ring

/-- Batch 36: `Y`-deg 5, input=3, quot=12, red=39. -/
public theorem jAff_c36_mod :
    jAff_c36 = quotJ_c36 * gAff + redJ_c36 := by
  unfold jAff_c36 quotJ_c36 gAff redJ_c36
  ring

/-- Batch 37: `Y`-deg 5, input=3, quot=12, red=39. -/
public theorem jAff_c37_mod :
    jAff_c37 = quotJ_c37 * gAff + redJ_c37 := by
  unfold jAff_c37 quotJ_c37 gAff redJ_c37
  ring

/-- Batch 38: `Y`-deg 5, input=3, quot=12, red=41. -/
public theorem jAff_c38_mod :
    jAff_c38 = quotJ_c38 * gAff + redJ_c38 := by
  unfold jAff_c38 quotJ_c38 gAff redJ_c38
  ring

/-- Batch 39: `Y`-deg 5, input=3, quot=12, red=39. -/
public theorem jAff_c39_mod :
    jAff_c39 = quotJ_c39 * gAff + redJ_c39 := by
  unfold jAff_c39 quotJ_c39 gAff redJ_c39
  ring

/-- Batch 40: `Y`-deg 5, input=3, quot=12, red=41. -/
public theorem jAff_c40_mod :
    jAff_c40 = quotJ_c40 * gAff + redJ_c40 := by
  unfold jAff_c40 quotJ_c40 gAff redJ_c40
  ring

/-- Batch 41: `Y`-deg 5, input=3, quot=12, red=39. -/
public theorem jAff_c41_mod :
    jAff_c41 = quotJ_c41 * gAff + redJ_c41 := by
  unfold jAff_c41 quotJ_c41 gAff redJ_c41
  ring

/-- Batch 42: `Y`-deg 5, input=3, quot=12, red=39. -/
public theorem jAff_c42_mod :
    jAff_c42 = quotJ_c42 * gAff + redJ_c42 := by
  unfold jAff_c42 quotJ_c42 gAff redJ_c42
  ring

/-- Batch 43: `Y`-deg 5, input=3, quot=12, red=41. -/
public theorem jAff_c43_mod :
    jAff_c43 = quotJ_c43 * gAff + redJ_c43 := by
  unfold jAff_c43 quotJ_c43 gAff redJ_c43
  ring

/-- Batch 44: `Y`-deg 5, input=3, quot=12, red=41. -/
public theorem jAff_c44_mod :
    jAff_c44 = quotJ_c44 * gAff + redJ_c44 := by
  unfold jAff_c44 quotJ_c44 gAff redJ_c44
  ring

/-- Batch 45: `Y`-deg 5, input=3, quot=11, red=36. -/
public theorem jAff_c45_mod :
    jAff_c45 = quotJ_c45 * gAff + redJ_c45 := by
  unfold jAff_c45 quotJ_c45 gAff redJ_c45
  ring

/-- Batch 46: `Y`-deg 5, input=2, quot=7, red=23. -/
public theorem jAff_c46_mod :
    jAff_c46 = quotJ_c46 * gAff + redJ_c46 := by
  unfold jAff_c46 quotJ_c46 gAff redJ_c46
  ring

/-- Batch 47: `Y`-deg 4, input=4, quot=8, red=30. -/
public theorem jAff_c47_mod :
    jAff_c47 = quotJ_c47 * gAff + redJ_c47 := by
  unfold jAff_c47 quotJ_c47 gAff redJ_c47
  ring

/-- Batch 48: `Y`-deg 4, input=4, quot=8, red=36. -/
public theorem jAff_c48_mod :
    jAff_c48 = quotJ_c48 * gAff + redJ_c48 := by
  unfold jAff_c48 quotJ_c48 gAff redJ_c48
  ring

/-- Batch 49: `Y`-deg 4, input=4, quot=8, red=36. -/
public theorem jAff_c49_mod :
    jAff_c49 = quotJ_c49 * gAff + redJ_c49 := by
  unfold jAff_c49 quotJ_c49 gAff redJ_c49
  ring

/-- Batch 50: `Y`-deg 4, input=4, quot=8, red=36. -/
public theorem jAff_c50_mod :
    jAff_c50 = quotJ_c50 * gAff + redJ_c50 := by
  unfold jAff_c50 quotJ_c50 gAff redJ_c50
  ring

/-- Batch 51: `Y`-deg 4, input=4, quot=8, red=36. -/
public theorem jAff_c51_mod :
    jAff_c51 = quotJ_c51 * gAff + redJ_c51 := by
  unfold jAff_c51 quotJ_c51 gAff redJ_c51
  ring

/-- Batch 52: `Y`-deg 4, input=4, quot=8, red=36. -/
public theorem jAff_c52_mod :
    jAff_c52 = quotJ_c52 * gAff + redJ_c52 := by
  unfold jAff_c52 quotJ_c52 gAff redJ_c52
  ring

/-- Batch 53: `Y`-deg 4, input=4, quot=8, red=36. -/
public theorem jAff_c53_mod :
    jAff_c53 = quotJ_c53 * gAff + redJ_c53 := by
  unfold jAff_c53 quotJ_c53 gAff redJ_c53
  ring

/-- Batch 54: `Y`-deg 4, input=4, quot=8, red=36. -/
public theorem jAff_c54_mod :
    jAff_c54 = quotJ_c54 * gAff + redJ_c54 := by
  unfold jAff_c54 quotJ_c54 gAff redJ_c54
  ring

/-- Batch 55: `Y`-deg 4, input=4, quot=8, red=30. -/
public theorem jAff_c55_mod :
    jAff_c55 = quotJ_c55 * gAff + redJ_c55 := by
  unfold jAff_c55 quotJ_c55 gAff redJ_c55
  ring

/-- Batch 56: `Y`-deg 4, input=3, quot=6, red=23. -/
public theorem jAff_c56_mod :
    jAff_c56 = quotJ_c56 * gAff + redJ_c56 := by
  unfold jAff_c56 quotJ_c56 gAff redJ_c56
  ring

/-- Batch 57: `Y`-deg 3, input=5, quot=5, red=22. -/
public theorem jAff_c57_mod :
    jAff_c57 = quotJ_c57 * gAff + redJ_c57 := by
  unfold jAff_c57 quotJ_c57 gAff redJ_c57
  ring

/-- Batch 58: `Y`-deg 3, input=5, quot=5, red=25. -/
public theorem jAff_c58_mod :
    jAff_c58 = quotJ_c58 * gAff + redJ_c58 := by
  unfold jAff_c58 quotJ_c58 gAff redJ_c58
  ring

/-- Batch 59: `Y`-deg 3, input=5, quot=5, red=25. -/
public theorem jAff_c59_mod :
    jAff_c59 = quotJ_c59 * gAff + redJ_c59 := by
  unfold jAff_c59 quotJ_c59 gAff redJ_c59
  ring

/-- Batch 60: `Y`-deg 3, input=5, quot=5, red=25. -/
public theorem jAff_c60_mod :
    jAff_c60 = quotJ_c60 * gAff + redJ_c60 := by
  unfold jAff_c60 quotJ_c60 gAff redJ_c60
  ring

/-- Batch 61: `Y`-deg 3, input=5, quot=5, red=25. -/
public theorem jAff_c61_mod :
    jAff_c61 = quotJ_c61 * gAff + redJ_c61 := by
  unfold jAff_c61 quotJ_c61 gAff redJ_c61
  ring

/-- Batch 62: `Y`-deg 3, input=5, quot=5, red=25. -/
public theorem jAff_c62_mod :
    jAff_c62 = quotJ_c62 * gAff + redJ_c62 := by
  unfold jAff_c62 quotJ_c62 gAff redJ_c62
  ring

/-- Batch 63: `Y`-deg 3, input=5, quot=5, red=25. -/
public theorem jAff_c63_mod :
    jAff_c63 = quotJ_c63 * gAff + redJ_c63 := by
  unfold jAff_c63 quotJ_c63 gAff redJ_c63
  ring

/-- Batch 64: `Y`-deg 3, input=5, quot=5, red=25. -/
public theorem jAff_c64_mod :
    jAff_c64 = quotJ_c64 * gAff + redJ_c64 := by
  unfold jAff_c64 quotJ_c64 gAff redJ_c64
  ring

/-- Batch 65: `Y`-deg 3, input=5, quot=5, red=25. -/
public theorem jAff_c65_mod :
    jAff_c65 = quotJ_c65 * gAff + redJ_c65 := by
  unfold jAff_c65 quotJ_c65 gAff redJ_c65
  ring

/-- Batch 66: `Y`-deg 3, input=5, quot=5, red=23. -/
public theorem jAff_c66_mod :
    jAff_c66 = quotJ_c66 * gAff + redJ_c66 := by
  unfold jAff_c66 quotJ_c66 gAff redJ_c66
  ring

/-- `jAff ≡ redJ (mod gAff)`. Offline sizes: input=368, quot=176, red=205. -/
public theorem jAff_mod :
    jAff = quotJ * gAff + redJ := by
  unfold jAff quotJ redJ
  have h0 := jAff_c0_mod
  have h1 := jAff_c1_mod
  have h2 := jAff_c2_mod
  have h3 := jAff_c3_mod
  have h4 := jAff_c4_mod
  have h5 := jAff_c5_mod
  have h6 := jAff_c6_mod
  have h7 := jAff_c7_mod
  have h8 := jAff_c8_mod
  have h9 := jAff_c9_mod
  have h10 := jAff_c10_mod
  have h11 := jAff_c11_mod
  have h12 := jAff_c12_mod
  have h13 := jAff_c13_mod
  have h14 := jAff_c14_mod
  have h15 := jAff_c15_mod
  have h16 := jAff_c16_mod
  have h17 := jAff_c17_mod
  have h18 := jAff_c18_mod
  have h19 := jAff_c19_mod
  have h20 := jAff_c20_mod
  have h21 := jAff_c21_mod
  have h22 := jAff_c22_mod
  have h23 := jAff_c23_mod
  have h24 := jAff_c24_mod
  have h25 := jAff_c25_mod
  have h26 := jAff_c26_mod
  have h27 := jAff_c27_mod
  have h28 := jAff_c28_mod
  have h29 := jAff_c29_mod
  have h30 := jAff_c30_mod
  have h31 := jAff_c31_mod
  have h32 := jAff_c32_mod
  have h33 := jAff_c33_mod
  have h34 := jAff_c34_mod
  have h35 := jAff_c35_mod
  have h36 := jAff_c36_mod
  have h37 := jAff_c37_mod
  have h38 := jAff_c38_mod
  have h39 := jAff_c39_mod
  have h40 := jAff_c40_mod
  have h41 := jAff_c41_mod
  have h42 := jAff_c42_mod
  have h43 := jAff_c43_mod
  have h44 := jAff_c44_mod
  have h45 := jAff_c45_mod
  have h46 := jAff_c46_mod
  have h47 := jAff_c47_mod
  have h48 := jAff_c48_mod
  have h49 := jAff_c49_mod
  have h50 := jAff_c50_mod
  have h51 := jAff_c51_mod
  have h52 := jAff_c52_mod
  have h53 := jAff_c53_mod
  have h54 := jAff_c54_mod
  have h55 := jAff_c55_mod
  have h56 := jAff_c56_mod
  have h57 := jAff_c57_mod
  have h58 := jAff_c58_mod
  have h59 := jAff_c59_mod
  have h60 := jAff_c60_mod
  have h61 := jAff_c61_mod
  have h62 := jAff_c62_mod
  have h63 := jAff_c63_mod
  have h64 := jAff_c64_mod
  have h65 := jAff_c65_mod
  have h66 := jAff_c66_mod
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66]
  ring


/-! ## Composition of reduced forms (Tower-B)

From the staged reductions
`hessAff² ≡ redH2`, `thetaAff ≡ redTheta`, `hessAff³ ≡ redH3`, `jAff ≡ redJ`
(each right-hand side of `Y`-degree ≤ 2), multiplicativity of the congruence
modulo `gAff` reduces the cleared Weierstrass identity to a combination of
products of already-reduced forms. Offline sympy sizes:

* `redH2²`: raw 296, quot 89, red 223
* `redH3²`: raw 755, quot 233, red 524
* `redTheta²`: raw 546, quot 165, red 381
* `redTheta · redTheta2` (so `redTheta³`): raw 1350, quot 457, red 891
* `redJ²`: raw 1341, quot 454, red 889
* `A · redTheta · redH2sq`: raw 1123, quot 378, red 746

The four reduced remainders of `redJ²`, `redTheta³`, `A·redTheta·redH2²`, and
`redH3²` combine to the zero polynomial, so the Weierstrass form is 0 mod `gAff`.
-/

/-! ### Multiplicativity of congruence modulo a fixed element -/

/-- `a = q * g + b` implies `g ∣ a - b`. -/
public theorem dvd_sub_of_mod {R : Type*} [CommRing R] {g a b q : R}
    (h : a = q * g + b) : g ∣ a - b :=
  ⟨q, by linear_combination h⟩

/-- Congruence is multiplicative on the right. -/
public theorem mul_right_mod_eq {R : Type*} [CommRing R] {g a b c q : R}
    (h : a = q * g + b) : a * c = (q * c) * g + b * c := by
  rw [h]
  ring

/-- Congruence is multiplicative on the left. -/
public theorem mul_left_mod_eq {R : Type*} [CommRing R] {g a b c q : R}
    (h : a = q * g + b) : c * a = (c * q) * g + c * b := by
  rw [h]
  ring

/-- Powers preserve congruence: from `a = q * g + b` get `g ∣ a ^ n - b ^ n`. -/
public theorem dvd_pow_sub_of_mod {R : Type*} [CommRing R] {g a b q : R} {n : ℕ}
    (h : a = q * g + b) : g ∣ a ^ n - b ^ n := by
  have hab : a - b = q * g := by linear_combination h
  have hpow : a - b ∣ a ^ n - b ^ n := sub_dvd_pow_sub_pow a b n
  rw [hab, mul_comm q g] at hpow
  exact (dvd_mul_right g q).trans hpow

/-- `hessAff³ ≡ redH3 (mod gAff)`, assembled from `hessAff_sq_mod` and `redH3_mod`. -/
public theorem hessAff_cube_mod :
    hessAff ^ 3 = (quotH2 * hessAff + quotH3) * gAff + redH3 := by
  have h2 := hessAff_sq_mod
  have h3 := redH3_mod
  calc
    hessAff ^ 3 = hessAff ^ 2 * hessAff := by ring
    _ = (quotH2 * gAff + redH2) * hessAff := by rw [h2]
    _ = quotH2 * hessAff * gAff + redH2 * hessAff := by ring
    _ = quotH2 * hessAff * gAff + (quotH3 * gAff + redH3) := by rw [h3]
    _ = (quotH2 * hessAff + quotH3) * gAff + redH3 := by ring

/-- `gAff ∣ hessAff ^ 2 - redH2`. -/
public theorem gAff_dvd_hessAff_sq_sub : gAff ∣ hessAff ^ 2 - redH2 :=
  dvd_sub_of_mod hessAff_sq_mod

/-- `gAff ∣ thetaAff - redTheta`. -/
public theorem gAff_dvd_thetaAff_sub : gAff ∣ thetaAff - redTheta :=
  dvd_sub_of_mod thetaAff_mod

/-- `gAff ∣ hessAff ^ 3 - redH3`. -/
public theorem gAff_dvd_hessAff_cube_sub : gAff ∣ hessAff ^ 3 - redH3 :=
  dvd_sub_of_mod hessAff_cube_mod

/-- `gAff ∣ jAff - redJ`. -/
public theorem gAff_dvd_jAff_sub : gAff ∣ jAff - redJ :=
  dvd_sub_of_mod jAff_mod

/-- `gAff ∣ jAff ^ 2 - redJ ^ 2`. -/
public theorem gAff_dvd_jAff_sq_sub : gAff ∣ jAff ^ 2 - redJ ^ 2 :=
  dvd_pow_sub_of_mod (n := 2) jAff_mod

/-- `gAff ∣ thetaAff ^ 3 - redTheta ^ 3`. -/
public theorem gAff_dvd_thetaAff_cube_sub : gAff ∣ thetaAff ^ 3 - redTheta ^ 3 :=
  dvd_pow_sub_of_mod (n := 3) thetaAff_mod

/-- `gAff ∣ hessAff ^ 4 - redH2 ^ 2`. -/
public theorem gAff_dvd_hessAff_pow4_sub : gAff ∣ hessAff ^ 4 - redH2 ^ 2 := by
  have h : hessAff ^ 4 - redH2 ^ 2 = (hessAff ^ 2) ^ 2 - redH2 ^ 2 := by ring
  rw [h]
  exact dvd_pow_sub_of_mod (n := 2) hessAff_sq_mod

/-- `gAff ∣ hessAff ^ 6 - redH3 ^ 2`. -/
public theorem gAff_dvd_hessAff_pow6_sub : gAff ∣ hessAff ^ 6 - redH3 ^ 2 := by
  have h : hessAff ^ 6 - redH3 ^ 2 = (hessAff ^ 3) ^ 2 - redH3 ^ 2 := by ring
  rw [h]
  exact dvd_pow_sub_of_mod (n := 2) hessAff_cube_mod

/-! ### Product reductions of already-reduced forms

Offline sympy sizes for the composition products (certificates for the larger
products live in the generation scripts under `/tmp/towerB_certs/`; only the
`redH2²` certificate is discharged in Lean so far):

* `redH2²`: raw 296, quot 89, red 223 — **proved**
* `redH3²`: raw 755, quot 233, red 524
* `redTheta²`: raw 546, quot 165, red 381
* `redTheta · redTheta2`: raw 1350, quot 457, red 891
* `redJ²`: raw 1341, quot 454, red 889
* `A · redTheta · redH2sq`: raw 1123, quot 378, red 746

-/

public noncomputable def quotH2sq : MvPolynomial (Fin 3) ℚ :=
  6561 * (X 0) ^ 8 * (X 1) * (X 2) ^ 7
    - 72900 * (X 0) ^ 7 * (X 1) * (X 2) ^ 7
    - 26244 * (X 0) ^ 7 * (X 1) * (X 2) ^ 6
    + 8748 * (X 0) ^ 6 * (X 1) * (X 2) ^ 8
    + 304560 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    + 211410 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    + 61236 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    - 21870 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    - 72900 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    - 593244 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    - 568620 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    - 325620 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 51516 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    + 43740 * (X 0) ^ 5 * (X 1) * (X 2) ^ 3
    + 4374 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    + 203040 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 537840 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 551124 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    + 421605 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    + 4860 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 62694 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    - 58320 * (X 0) ^ 4 * (X 1) * (X 2) ^ 2
    + 18225 * (X 0) ^ 4 * (X 1) * (X 2)
    - 24300 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    - 197748 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 189540 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    - 108540 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 17172 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 14580 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    + 972 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    + 33840 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 23490 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    + 6804 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 2430 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 2700 * (X 0) * (X 1) * (X 2) ^ 10
    - 972 * (X 0) * (X 1) * (X 2) ^ 9
    + 81 * (X 1) * (X 2) ^ 11
    + 1458 * (X 0) ^ 9 * (X 2) ^ 6
    - 8748 * (X 0) ^ 9 * (X 2) ^ 5
    + 13122 * (X 0) ^ 9 * (X 2) ^ 4
    + 2187 * (X 0) ^ 8 * (X 2) ^ 7
    - 8100 * (X 0) ^ 8 * (X 2) ^ 6
    + 45684 * (X 0) ^ 8 * (X 2) ^ 5
    - 55404 * (X 0) ^ 8 * (X 2) ^ 4
    - 26244 * (X 0) ^ 8 * (X 2) ^ 3
    - 28674 * (X 0) ^ 7 * (X 2) ^ 7
    + 28836 * (X 0) ^ 7 * (X 2) ^ 6
    - 100116 * (X 0) ^ 7 * (X 2) ^ 5
    + 62208 * (X 0) ^ 7 * (X 2) ^ 4
    + 39852 * (X 0) ^ 7 * (X 2) ^ 3
    + 49572 * (X 0) ^ 7 * (X 2) ^ 2
    - 21870 * (X 0) ^ 7 * (X 2)
    + 2916 * (X 0) ^ 6 * (X 2) ^ 8
    + 140670 * (X 0) ^ 6 * (X 2) ^ 7
    - 150336 * (X 0) ^ 6 * (X 2) ^ 6
    + 288198 * (X 0) ^ 6 * (X 2) ^ 5
    + 119556 * (X 0) ^ 6 * (X 2) ^ 4
    - 28998 * (X 0) ^ 5 * (X 2) ^ 8
    - 278640 * (X 0) ^ 5 * (X 2) ^ 7
    + 347328 * (X 0) ^ 5 * (X 2) ^ 6
    - 661284 * (X 0) ^ 5 * (X 2) ^ 5
    - 513864 * (X 0) ^ 5 * (X 2) ^ 4
    - 245916 * (X 0) ^ 5 * (X 2) ^ 3
    + 80190 * (X 0) ^ 5 * (X 2) ^ 2
    + 1458 * (X 0) ^ 4 * (X 2) ^ 9
    + 92880 * (X 0) ^ 4 * (X 2) ^ 8
    + 131652 * (X 0) ^ 4 * (X 2) ^ 7
    - 116154 * (X 0) ^ 4 * (X 2) ^ 6
    + 558333 * (X 0) ^ 4 * (X 2) ^ 5
    + 520344 * (X 0) ^ 4 * (X 2) ^ 4
    + 511758 * (X 0) ^ 4 * (X 2) ^ 3
    - 52974 * (X 0) ^ 4 * (X 2) ^ 2
    - 59535 * (X 0) ^ 4 * (X 2)
    - 9558 * (X 0) ^ 3 * (X 2) ^ 9
    - 89748 * (X 0) ^ 3 * (X 2) ^ 8
    + 96498 * (X 0) ^ 3 * (X 2) ^ 7
    - 199692 * (X 0) ^ 3 * (X 2) ^ 6
    - 158004 * (X 0) ^ 3 * (X 2) ^ 5
    - 65448 * (X 0) ^ 3 * (X 2) ^ 4
    + 19440 * (X 0) ^ 3 * (X 2) ^ 3
    + 324 * (X 0) ^ 2 * (X 2) ^ 10
    + 15030 * (X 0) ^ 2 * (X 2) ^ 9
    - 13320 * (X 0) ^ 2 * (X 2) ^ 8
    + 27918 * (X 0) ^ 2 * (X 2) ^ 7
    + 11340 * (X 0) ^ 2 * (X 2) ^ 6
    - 1044 * (X 0) * (X 2) ^ 10
    + 540 * (X 0) * (X 2) ^ 9
    - 1296 * (X 0) * (X 2) ^ 8
    + 27 * (X 2) ^ 11

public noncomputable def redH2sq : MvPolynomial (Fin 3) ℚ :=
  -8748 * (X 0) ^ 10 * (X 1) ^ 2 * (X 2) ^ 7
    + 26325 * (X 0) ^ 10 * (X 1) ^ 2 * (X 2) ^ 6
    - 972 * (X 0) ^ 10 * (X 1) ^ 2 * (X 2) ^ 5
    + 4374 * (X 0) ^ 10 * (X 1) ^ 2 * (X 2) ^ 4
    - 8748 * (X 0) ^ 10 * (X 1) ^ 2 * (X 2) ^ 3
    + 6561 * (X 0) ^ 10 * (X 1) ^ 2 * (X 2) ^ 2
    + 72900 * (X 0) ^ 9 * (X 1) ^ 2 * (X 2) ^ 7
    - 192456 * (X 0) ^ 9 * (X 1) ^ 2 * (X 2) ^ 6
    - 78732 * (X 0) ^ 9 * (X 1) ^ 2 * (X 2) ^ 5
    + 2187 * (X 0) ^ 8 * (X 1) ^ 2 * (X 2) ^ 8
    - 210195 * (X 0) ^ 8 * (X 1) ^ 2 * (X 2) ^ 7
    + 475308 * (X 0) ^ 8 * (X 1) ^ 2 * (X 2) ^ 6
    + 349920 * (X 0) ^ 8 * (X 1) ^ 2 * (X 2) ^ 5
    + 201204 * (X 0) ^ 8 * (X 1) ^ 2 * (X 2) ^ 4
    - 91854 * (X 0) ^ 8 * (X 1) ^ 2 * (X 2) ^ 3
    - 56700 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 8
    + 340038 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 7
    - 331938 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 6
    - 393012 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 5
    - 462348 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 4
    + 93798 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 3
    + 83106 * (X 0) ^ 7 * (X 1) ^ 2 * (X 2) ^ 2
    + 8748 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 9
    + 279099 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 8
    - 711666 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 7
    - 530712 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 6
    - 290142 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 5
    + 129033 * (X 0) ^ 6 * (X 1) ^ 2 * (X 2) ^ 4
    - 72900 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 9
    - 378594 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 8
    + 1258254 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 7
    + 1179036 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 6
    + 1387044 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 5
    - 281394 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 4
    - 249318 * (X 0) ^ 5 * (X 1) ^ 2 * (X 2) ^ 3
    + 4050 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 10
    + 168750 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 9
    - 108135 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 8
    - 895212 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 7
    - 821502 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 6
    - 1240839 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 5
    - 43659 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 4
    + 345870 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 3
    + 145152 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2) ^ 2
    - 20655 * (X 0) ^ 4 * (X 1) ^ 2 * (X 2)
    - 18900 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 10
    - 77004 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 9
    + 282528 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 8
    + 262008 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 7
    + 308232 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 6
    - 62532 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 5
    - 55404 * (X 0) ^ 3 * (X 1) ^ 2 * (X 2) ^ 4
    + 648 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 11
    + 16902 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 10
    - 43902 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 9
    - 32886 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 8
    - 17658 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 7
    + 7776 * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 6
    - 1200 * (X 0) * (X 1) ^ 2 * (X 2) ^ 11
    + 3168 * (X 0) * (X 1) ^ 2 * (X 2) ^ 10
    + 1296 * (X 0) * (X 1) ^ 2 * (X 2) ^ 9
    + 27 * (X 1) ^ 2 * (X 2) ^ 12
    - 81 * (X 1) ^ 2 * (X 2) ^ 11
    + 6561 * (X 0) ^ 11 * (X 1) * (X 2) ^ 7
    - 972 * (X 0) ^ 11 * (X 1) * (X 2) ^ 6
    + 8748 * (X 0) ^ 11 * (X 1) * (X 2) ^ 5
    - 26244 * (X 0) ^ 11 * (X 1) * (X 2) ^ 4
    + 26244 * (X 0) ^ 11 * (X 1) * (X 2) ^ 3
    - 78732 * (X 0) ^ 10 * (X 1) * (X 2) ^ 7
    - 5994 * (X 0) ^ 10 * (X 1) * (X 2) ^ 6
    - 23976 * (X 0) ^ 10 * (X 1) * (X 2) ^ 5
    + 67068 * (X 0) ^ 10 * (X 1) * (X 2) ^ 4
    - 52488 * (X 0) ^ 10 * (X 1) * (X 2) ^ 3
    - 21870 * (X 0) ^ 10 * (X 1) * (X 2) ^ 2
    + 2187 * (X 0) ^ 9 * (X 1) * (X 2) ^ 8
    + 357858 * (X 0) ^ 9 * (X 1) * (X 2) ^ 7
    + 40824 * (X 0) ^ 9 * (X 1) * (X 2) ^ 6
    + 135594 * (X 0) ^ 9 * (X 1) * (X 2) ^ 5
    - 148716 * (X 0) ^ 9 * (X 1) * (X 2) ^ 4
    + 7533 * (X 0) ^ 8 * (X 1) * (X 2) ^ 8
    - 729243 * (X 0) ^ 8 * (X 1) * (X 2) ^ 7
    - 41796 * (X 0) ^ 8 * (X 1) * (X 2) ^ 6
    - 669708 * (X 0) ^ 8 * (X 1) * (X 2) ^ 5
    + 605556 * (X 0) ^ 8 * (X 1) * (X 2) ^ 4
    + 218700 * (X 0) ^ 8 * (X 1) * (X 2) ^ 3
    - 4374 * (X 0) ^ 7 * (X 1) * (X 2) ^ 9
    - 209466 * (X 0) ^ 7 * (X 1) * (X 2) ^ 8
    + 557118 * (X 0) ^ 7 * (X 1) * (X 2) ^ 7
    - 50220 * (X 0) ^ 7 * (X 1) * (X 2) ^ 6
    + 850905 * (X 0) ^ 7 * (X 1) * (X 2) ^ 5
    - 571536 * (X 0) ^ 7 * (X 1) * (X 2) ^ 4
    - 419580 * (X 0) ^ 7 * (X 1) * (X 2) ^ 3
    - 150174 * (X 0) ^ 7 * (X 1) * (X 2) ^ 2
    + 41553 * (X 0) ^ 7 * (X 1) * (X 2)
    + 62532 * (X 0) ^ 6 * (X 1) * (X 2) ^ 9
    + 895428 * (X 0) ^ 6 * (X 1) * (X 2) ^ 8
    - 48222 * (X 0) ^ 6 * (X 1) * (X 2) ^ 7
    + 678294 * (X 0) ^ 6 * (X 1) * (X 2) ^ 6
    - 727866 * (X 0) ^ 6 * (X 1) * (X 2) ^ 5
    - 231822 * (X 0) ^ 6 * (X 1) * (X 2) ^ 4
    - 3402 * (X 0) ^ 5 * (X 1) * (X 2) ^ 10
    - 288630 * (X 0) ^ 5 * (X 1) * (X 2) ^ 9
    - 1385910 * (X 0) ^ 5 * (X 1) * (X 2) ^ 8
    + 106920 * (X 0) ^ 5 * (X 1) * (X 2) ^ 7
    - 1612305 * (X 0) ^ 5 * (X 1) * (X 2) ^ 6
    + 1580472 * (X 0) ^ 5 * (X 1) * (X 2) ^ 5
    + 992412 * (X 0) ^ 5 * (X 1) * (X 2) ^ 4
    + 341658 * (X 0) ^ 5 * (X 1) * (X 2) ^ 3
    - 103761 * (X 0) ^ 5 * (X 1) * (X 2) ^ 2
    + 28350 * (X 0) ^ 4 * (X 1) * (X 2) ^ 10
    + 514134 * (X 0) ^ 4 * (X 1) * (X 2) ^ 9
    + 602424 * (X 0) ^ 4 * (X 1) * (X 2) ^ 8
    + 150012 * (X 0) ^ 4 * (X 1) * (X 2) ^ 7
    + 697653 * (X 0) ^ 4 * (X 1) * (X 2) ^ 6
    - 1044819 * (X 0) ^ 4 * (X 1) * (X 2) ^ 5
    - 807246 * (X 0) ^ 4 * (X 1) * (X 2) ^ 4
    - 597618 * (X 0) ^ 4 * (X 1) * (X 2) ^ 3
    + 83025 * (X 0) ^ 4 * (X 1) * (X 2) ^ 2
    + 62289 * (X 0) ^ 4 * (X 1) * (X 2)
    - 891 * (X 0) ^ 3 * (X 1) * (X 2) ^ 11
    - 69714 * (X 0) ^ 3 * (X 1) * (X 2) ^ 10
    - 274644 * (X 0) ^ 3 * (X 1) * (X 2) ^ 9
    + 48546 * (X 0) ^ 3 * (X 1) * (X 2) ^ 8
    - 290736 * (X 0) ^ 3 * (X 1) * (X 2) ^ 7
    + 336312 * (X 0) ^ 3 * (X 1) * (X 2) ^ 6
    + 190944 * (X 0) ^ 3 * (X 1) * (X 2) ^ 5
    + 63828 * (X 0) ^ 3 * (X 1) * (X 2) ^ 4
    - 20736 * (X 0) ^ 3 * (X 1) * (X 2) ^ 3
    + 4032 * (X 0) ^ 2 * (X 1) * (X 2) ^ 11
    + 45414 * (X 0) ^ 2 * (X 1) * (X 2) ^ 10
    - 9342 * (X 0) ^ 2 * (X 1) * (X 2) ^ 9
    + 28242 * (X 0) ^ 2 * (X 1) * (X 2) ^ 8
    - 37962 * (X 0) ^ 2 * (X 1) * (X 2) ^ 7
    - 10368 * (X 0) ^ 2 * (X 1) * (X 2) ^ 6
    - 81 * (X 0) * (X 1) * (X 2) ^ 12
    - 3348 * (X 0) * (X 1) * (X 2) ^ 11
    + 744 * (X 0) * (X 1) * (X 2) ^ 10
    - 756 * (X 0) * (X 1) * (X 2) ^ 9
    + 1296 * (X 0) * (X 1) * (X 2) ^ 8
    + 93 * (X 1) * (X 2) ^ 12
    - 27 * (X 1) * (X 2) ^ 11
    + 4374 * (X 0) ^ 12 * (X 2) ^ 6
    - 26244 * (X 0) ^ 12 * (X 2) ^ 5
    + 39366 * (X 0) ^ 12 * (X 2) ^ 4
    + 2187 * (X 0) ^ 11 * (X 2) ^ 7
    - 24624 * (X 0) ^ 11 * (X 2) ^ 6
    + 139968 * (X 0) ^ 11 * (X 2) ^ 5
    - 174960 * (X 0) ^ 11 * (X 2) ^ 4
    - 69984 * (X 0) ^ 11 * (X 2) ^ 3
    - 34992 * (X 0) ^ 10 * (X 2) ^ 7
    + 87237 * (X 0) ^ 10 * (X 2) ^ 6
    - 274914 * (X 0) ^ 10 * (X 2) ^ 5
    + 192294 * (X 0) ^ 10 * (X 2) ^ 4
    + 151632 * (X 0) ^ 10 * (X 2) ^ 3
    + 67797 * (X 0) ^ 10 * (X 2) ^ 2
    - 21870 * (X 0) ^ 10 * (X 2)
    + 729 * (X 0) ^ 9 * (X 2) ^ 8
    + 192186 * (X 0) ^ 9 * (X 2) ^ 7
    - 421848 * (X 0) ^ 9 * (X 2) ^ 6
    + 607986 * (X 0) ^ 9 * (X 2) ^ 5
    + 212868 * (X 0) ^ 9 * (X 2) ^ 4
    + 1296 * (X 0) ^ 8 * (X 2) ^ 8
    - 416826 * (X 0) ^ 8 * (X 2) ^ 7
    + 1000188 * (X 0) ^ 8 * (X 2) ^ 6
    - 1274940 * (X 0) ^ 8 * (X 2) ^ 5
    - 858600 * (X 0) ^ 8 * (X 2) ^ 4
    - 328050 * (X 0) ^ 8 * (X 2) ^ 3
    + 104976 * (X 0) ^ 8 * (X 2) ^ 2
    - 1458 * (X 0) ^ 7 * (X 2) ^ 9
    - 88722 * (X 0) ^ 7 * (X 2) ^ 8
    + 436752 * (X 0) ^ 7 * (X 2) ^ 7
    - 882414 * (X 0) ^ 7 * (X 2) ^ 6
    + 743175 * (X 0) ^ 7 * (X 2) ^ 5
    + 739044 * (X 0) ^ 7 * (X 2) ^ 4
    + 585954 * (X 0) ^ 7 * (X 2) ^ 3
    - 82296 * (X 0) ^ 7 * (X 2) ^ 2
    - 61965 * (X 0) ^ 7 * (X 2)
    + 24408 * (X 0) ^ 6 * (X 2) ^ 9
    + 398007 * (X 0) ^ 6 * (X 2) ^ 8
    - 731646 * (X 0) ^ 6 * (X 2) ^ 7
    + 1065798 * (X 0) ^ 6 * (X 2) ^ 6
    + 618084 * (X 0) ^ 6 * (X 2) ^ 5
    + 196587 * (X 0) ^ 6 * (X 2) ^ 4
    - 62694 * (X 0) ^ 6 * (X 2) ^ 3
    - 1134 * (X 0) ^ 5 * (X 2) ^ 10
    - 122310 * (X 0) ^ 5 * (X 2) ^ 9
    - 478116 * (X 0) ^ 5 * (X 2) ^ 8
    + 908010 * (X 0) ^ 5 * (X 2) ^ 7
    - 1599507 * (X 0) ^ 5 * (X 2) ^ 6
    - 1224396 * (X 0) ^ 5 * (X 2) ^ 5
    - 781326 * (X 0) ^ 5 * (X 2) ^ 4
    + 143532 * (X 0) ^ 5 * (X 2) ^ 3
    + 61641 * (X 0) ^ 5 * (X 2) ^ 2
    + 10638 * (X 0) ^ 4 * (X 2) ^ 10
    + 210384 * (X 0) ^ 4 * (X 2) ^ 9
    - 23274 * (X 0) ^ 4 * (X 2) ^ 8
    - 12474 * (X 0) ^ 4 * (X 2) ^ 7
    + 864297 * (X 0) ^ 4 * (X 2) ^ 6
    + 651888 * (X 0) ^ 4 * (X 2) ^ 5
    + 502119 * (X 0) ^ 4 * (X 2) ^ 4
    - 60426 * (X 0) ^ 4 * (X 2) ^ 3
    - 60993 * (X 0) ^ 4 * (X 2) ^ 2
    + 81 * (X 0) ^ 4
    - 297 * (X 0) ^ 3 * (X 2) ^ 11
    - 26838 * (X 0) ^ 3 * (X 2) ^ 10
    - 85644 * (X 0) ^ 3 * (X 2) ^ 9
    + 117774 * (X 0) ^ 3 * (X 2) ^ 8
    - 252072 * (X 0) ^ 3 * (X 2) ^ 7
    - 161784 * (X 0) ^ 3 * (X 2) ^ 6
    - 65124 * (X 0) ^ 3 * (X 2) ^ 5
    + 20412 * (X 0) ^ 3 * (X 2) ^ 4
    - 108 * (X 0) ^ 3 * (X 2) ^ 3
    + 1416 * (X 0) ^ 2 * (X 2) ^ 11
    + 16146 * (X 0) ^ 2 * (X 2) ^ 10
    - 16740 * (X 0) ^ 2 * (X 2) ^ 9
    + 31104 * (X 0) ^ 2 * (X 2) ^ 8
    + 10692 * (X 0) ^ 2 * (X 2) ^ 7
    + 54 * (X 0) ^ 2 * (X 2) ^ 6
    - 27 * (X 0) * (X 2) ^ 12
    - 1116 * (X 0) * (X 2) ^ 11
    + 648 * (X 0) * (X 2) ^ 10
    - 1308 * (X 0) * (X 2) ^ 9
    + 28 * (X 2) ^ 12

/-- `redH2² ≡ redH2sq (mod gAff)`. Offline: raw=296, quot=89, red=223. -/
public theorem redH2_sq_mod :
    redH2 ^ 2 = quotH2sq * gAff + redH2sq := by
  unfold redH2 quotH2sq gAff redH2sq
  ring


/-! ### Remaining product reductions

Certificates `quotH3sq`, `redH3sq`, `quotTheta2`, `redTheta2`, `quotTheta3step`,
`redTheta3`, `quotJ2`, `redJ2`, `quotATHH2`, `redATHH2` are generated offline
(sympy Y-reduction). Their `ring` proofs and the final remainder cancellation are
large; `redH2_sq_mod` is the composition-style template (raw 296, ~8 min).

The multiplicative lemmas above already give
`gAff ∣ jAff² - redJ²`, `gAff ∣ thetaAff³ - redTheta³`,
`gAff ∣ hessAff⁴ - redH2²`, `gAff ∣ hessAff⁶ - redH3²`.
Closing the Weierstrass identity then reduces to product reductions of the
`red*` forms and the identically-zero remainder combination.
-/

/-- `gAff ∣ redH2 ^ 2 - redH2sq` from the product reduction. -/
public theorem gAff_dvd_redH2_sq_sub : gAff ∣ redH2 ^ 2 - redH2sq :=
  dvd_sub_of_mod redH2_sq_mod

/-! ## Congruence tower status

### Offline (sympy) and Lean

| Stage | input | quot | red | Lean |
|---|---:|---:|---:|---|
| `hessAff²` | 41 | 10 | 46 | **proved** |
| `thetaAff` | 119 | 39 | 84 | **proved** |
| `H³` | 149 | 42 | 113 | **proved** |
| `jAff` | 368 | 176 | 205 | **proved** (67 monom-batches) |
| multiplicativity + `hessAff³` | — | — | — | **proved** |
| `redH2²` | 296 | 89 | 223 | **proved** (composition template) |
| `redH3²` | 755 | 233 | 524 | certificate generated; ring pending |
| `redTheta²` / `³` | 546 / 1350 | 165 / 457 | 381 / 891 | certificate generated; ring pending |
| `redJ²` | 1341 | 454 | 889 | certificate generated; ring pending |
| `A·Θ·redH2sq` | 1123 | 378 | 746 | certificate generated; ring pending |
| final red remainders | — | — | **0** | offline (sympy); Lean ring pending |
| original Weierstrass mod `gAff` | — | — | — | structure ready; needs product rings |

Composition route (Tower-B): multiplicative congruence from the four staged
reductions, then Y-reduce products of already-reduced forms. The product-reduction
certificates are in this file; full `ring` discharge of the larger products
(raw ≥ 500 monoms) is left for follow-up (single-`ring` on `redH2²` is ~8 min;
`redH3²` exceeds 30 min). Offline sympy confirms the reduced remainders cancel
identically and the original Weierstrass form is 0 mod `gAff`.
-/

#print axioms residual_on_curve_identity
#print axioms residual_on_tangent_line
#print axioms residual_direction_is_tangent
#print axioms residual_on_curve_divisible
#print axioms tangent_residual_package
#print axioms aronholdS_poly_eq_weierstrassA
#print axioms aronholdT_poly_eq_weierstrassBnum
#print axioms twentySeven_S_eq_A_coeff
#print axioms neg_twentySeven_T_eq_Bnum_coeff
#print axioms hessAff_eq_neg_quarter_H
#print axioms hessAff_sq_mod
#print axioms thetaAff_mod
#print axioms redH3_mod
#print axioms jAff_mod
#print axioms hessAff_cube_mod
#print axioms redH2_sq_mod
#print axioms gAff_dvd_jAff_sq_sub
#print axioms gAff_dvd_thetaAff_cube_sub
#print axioms gAff_dvd_hessAff_pow4_sub
#print axioms gAff_dvd_hessAff_pow6_sub
#print axioms gAff_dvd_redH2_sq_sub
