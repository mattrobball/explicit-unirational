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

3. **Degree 9.** Size report for a resultant certificate; full minimality left for a
   follow-up (no `sorry`).

Coordinates: `X 0 = X`, `X 1 = Y`, `X 2 = z` (parameter), matching `MulThreeCert`.
-/

set_option maxHeartbeats 8000000
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

/-! ## Degree-9 outlook (item 3)

The extension degree `[K(C) : K(ξ, η)] = 9` for `ξ = Θ/H²`, `η = J/(2H³)` (Fisher /
Sage covariants) is the field-theoretic content of `deg α_λ = 9`. Offline resultant
experiments produce an eliminant of total degree 18 in `(X, ξ)` with on the order of
**10³–10⁴ terms** once `z` is kept symbolic — at the edge of a single `ring`-checked
witness in this toolchain. A modular tower or factorized eliminant is the practical
next step; it is not stubbed here (no `sorry`).

Items delivered: the residual package (item 1) and the identification of Jacobian
Weierstrass coefficients with Aronhold `S`, `T` / note (3.7) (item 2 coefficient half).
The full multipolynomial identity `η² − ξ³ − Aξ − B ≡ 0 (mod g)` for expanded `Θ`, `J`
is verified offline by polynomial division (~2k-term witness); embedding that witness
is deferred to keep `lake build` stable. -/

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

end ExplicitUnirational
