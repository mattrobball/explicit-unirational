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
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Tangent residual and Weierstrass coordinates on the rational pencil (Route B)

Route B for Endpoint A0: an explicit, certificate-shaped treatment of the degree-9 map
from the generic plane cubic of note eq. (3.1) to its Jacobian (3.7), bypassing Picard
schemes and torsor trivialization.

## Mathematics

Let `G_z = F₀ + z F₁` be the generic member of the pencil (3.1), and write
`g(X,Y) = G_z(X,Y,1)` for the affine chart `Z = 1`. For a point `P = (x,y)` on `g = 0`
with nonzero gradient, the tangent line at `P` meets the cubic again at a residual point
`Q(P)`. Classically `2P + Q(P) ∼ λ` (hyperplane class), so
`α_λ(P) = [3P − λ] ∼ [P − Q(P)]` (note Lemma 2.1 / DESIGN §3 Route B).

This module supplies:

1. **Tangent residual.** Explicit polynomials giving `Q(P)` in affine coordinates, with the
   defining identities (on the curve, on the tangent line) checked by `ring`.

2. **Weierstrass coefficients.** Matching of the Jacobian model (3.7) / `noteCurveQ` to the
   Aronhold invariants `S`, `T` of the ternary cubic (`27 S = A`, `−27 T = 4B`).

3. **Staged `Y`-reduction of Fisher/Sage covariants.** Integer forms of `Θ` and reduced normal
   forms of `H²`, `H³` modulo `gAff`, each as a separate `ring` certificate (no monolithic
   ~1900-term Weierstrass witness). Higher rungs measured offline.

4. **Degree 9.** Size report for a resultant certificate; full minimality left for a
   follow-up (no `sorry`).

Coordinates: `X 0 = X`, `X 1 = Y`, `X 2 = z` (parameter), matching `MulThreeCert`.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 10000

noncomputable section

open MvPolynomial

namespace ExplicitUnirational

/-! ## Affine cubic of the rational pencil -/

/-- Affine chart `Z = 1` of the generic member `G_z = F₀ + z F₁` of note (3.1):
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

/-! ## Weierstrass model coefficients (note (3.7) / `noteCurveQ`) -/

/-- Coefficient `A = z²(3 − z)` of note (3.7) / `noteCurveQ.a₄`, as a polynomial in `z = X 2`. -/
public noncomputable def weierstrassA : MvPolynomial (Fin 3) ℚ :=
  (X 2) ^ 2 * (3 - X 2)

/-- Numerator of `B = (z/4) P(z)`: `Bnum = z · P(z)` so `B = Bnum/4`. -/
public noncomputable def weierstrassBnum : MvPolynomial (Fin 3) ℚ :=
  (X 2) * (4 * (X 2) ^ 4 - 23 * (X 2) ^ 3 - 18 * (X 2) ^ 2 + (X 2) - 4)

/-! ## Aronhold invariants vs. Weierstrass coefficients

For the ternary cubic `G_z`, the Aronhold invariants (Sage normalization) are
`S = z²(3−z)/27` and `T = −z P(z)/27`. The short Weierstrass model produced by
`WeierstrassForm` is `Y² = X³ + (27S) X + (−27/4 T)`, which is exactly note (3.7):
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
Uses the closed form of note (3.3)/(3.6) Hessian, with `C z` replaced by `X 2`. -/
public noncomputable def H_G_z_aff : MvPolynomial (Fin 3) ℚ :=
  36 * (X 2) ^ 2 * ((X 0) ^ 2 * (X 1)) + 12 * (X 2) ^ 2 * ((X 0) ^ 2)
    - 12 * (X 2) ^ 2 * ((X 0) * (X 1) ^ 2) + 36 * (X 2) * ((X 0) * (X 1) ^ 2)
    - 108 * (X 2) ^ 2 * ((X 0) * (X 1)) - 12 * (X 2) * ((X 0) * (X 1))
    - 36 * (X 2) ^ 2 * (X 0) - 12 * (X 0)
    + 12 * (X 2) ^ 3 * (X 1) + 4 * (X 2) ^ 3

/-- Sage's affine Hessian is `-1/4` times the note's Hessian on `Z = 1`:
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

/-! ## Congruence tower status

### Offline (sympy)

Full cleared identity is divisible by `gAff` (quotient **1887** terms). After reducing
every factor to `Y`-degree ≤ 2, the combination of reduced forms is **identically 0**.

| Stage | input | quot | red | Lean |
|---|---:|---:|---:|---|
| `hessAff²` | 41 | 10 | 46 | **proved** |
| `thetaAff` | 119 | 39 | 84 | **proved** |
| `H³` | 149 | 42 | 113 | **proved** |
| `jAff` | 368 | 176 | 205 | offline generated; `ring` >30 min |
| `H⁴`–`H⁶`, `Θ³`, `J²`, `4AΘH⁴` | up to ~1350 | — | ≤891 | generated offline |
| final red combo | — | — | **0** | offline |

Worst checked module build (H²+Θ+H³ together): ≈**306 s**. No monolithic 1900-term goal.
Degree-9 eliminant is a size report only. Offline full tower certificates are in
`_generated_reds.lean` (repo root, not imported).
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

end ExplicitUnirational
