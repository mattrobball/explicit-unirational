/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.FunctionField.TowerBProducts
import all ExplicitUnirational.FunctionField.TangentResidual
public import ExplicitUnirational.FunctionField.PencilRationality
import all ExplicitUnirational.FunctionField.PencilRationality
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Unirationality: the Weierstrass surface acquires a point over `ℚ(x, y)`

Composition of the two halves of the unirationality argument:

* Lemma 3.1 (`PencilRationality.adjoin_pencil_parameter_eq_top`): on the chart
  `Z = 1` the pencil parameter is the *rational plane function*
  `ζ = −f₀/f₁ ∈ ℚ(x, y)`, where `f₀ = y − x³`, `f₁ = x + y³ + y² − 1` are the
  dehomogenizations of `F₀_rat`, `F₁_rat` (note (3.1)).
* The Tower-B congruence (`weierstrass_congruence_mod_gAff`), which holds in
  `ℚ[x, y, z]` and therefore evaluates along *any* assignment killing `gAff`.

Rather than bridging the two presentations of the curve's function field
(the `AdjoinRoot` one of `WeierstrassOnCurve` and the `MvPolynomial` quotient
implicit in `PencilRationality`) we evaluate the ambient polynomial ring
directly into the plane function field `planeField ℚ = Frac(ℚ[x, y])` by
`x ↦ x`, `y ↦ y`, `z ↦ ζ`; `gAff` dies by Lemma 3.1, so the congruence lands
on the Weierstrass equation.  The result (`noteCurvePlane_equation`,
`surfaceToPlane_vanishes`): the plane rational functions

    ζ = −f₀/f₁,  ξ = Θ/H²,  η = J/(2H³)

satisfy the affine equation of the note's Weierstrass model (3.7) with
parameter `ζ` — equivalently, there is a ℚ-algebra homomorphism
`surfaceCoordRingToPlane` from the affine coordinate ring
`ℚ[ξ, η, z]/(4η² − 4ξ³ − 4z²(3−z)ξ − z·P(z))` of the note's elliptic surface
into the rational function field `ℚ(x, y)` in two variables, sending the fibre
parameter `z` to the pencil parameter.  This homomorphism is the algebraic
form of the rational map `𝔸² ⤏ S` of the unirationality argument.

## What is *not* proved here

The upgrade from homomorphism to *field embedding* `K(S) ↪ ℚ(x, y)`
(equivalently: dominance of the rational map) is the injectivity of
`surfaceCoordRingToPlane`, which amounts to the transcendence facts that
`ζ` is transcendental over `ℚ` and `ξ` is transcendental over `ℚ(ζ)` — i.e.
that `(ξ, η)` is a *generic* point of the surface, the classical
"the multiplication-by-`α_λ` map is nonconstant" step (the note's degree-9
computation).  That is genuine mathematical content, not bookkeeping, and is
left for a follow-up (`ResidualDegree` contains the relevant resultant
certificate infrastructure).  Similarly, identifying `K(S)` with the function
field of the weighted del Pezzo hypersurface `S_Q` of `DelPezzo/Surface.lean`
is a birationality statement about the two models that is not formalized
here; the present theorem is about the Weierstrass model (3.7) itself.
-/

@[expose] public section

set_option maxHeartbeats 1600000

noncomputable section

open MvPolynomial

namespace ExplicitUnirational

/-! ## The affine pencil cubics and the plane function field -/

/-- Dehomogenization of `F₀_rat = YZ² − X³` at `Z = 1`: `f₀ = y − x³`. -/
public noncomputable def f₀aff : MvPolynomial (Fin 2) ℚ :=
  X 1 - X 0 ^ 3

/-- Dehomogenization of `F₁_rat = XZ² + Y³ + Y²Z − Z³` at `Z = 1`:
`f₁ = x + y³ + y² − 1`. -/
public noncomputable def f₁aff : MvPolynomial (Fin 2) ℚ :=
  X 0 + X 1 ^ 3 + X 1 ^ 2 - 1

/-- `gAff` is the pencil relation of the affine cubics (note (3.1) at `Z = 1`). -/
public theorem pencilRelation_eq_gAff :
    FunctionField.pencilRelation f₀aff f₁aff = gAff := by
  unfold FunctionField.pencilRelation f₀aff f₁aff gAff
  simp only [map_sub, map_add, map_pow, map_one, rename_X, Fin.castSucc_zero,
    Fin.castSucc_one]
  ring

public theorem f₁aff_ne_zero : f₁aff ≠ 0 := by
  intro h
  have h1 := congrArg (eval fun _ => (1 : ℚ)) h
  simp [f₁aff] at h1

/-- The plane coordinates and the pencil parameter inside `ℚ(x, y)`. -/
public noncomputable def planeX : FunctionField.planeField ℚ :=
  algebraMap (MvPolynomial (Fin 2) ℚ) _ (X 0)

public noncomputable def planeY : FunctionField.planeField ℚ :=
  algebraMap (MvPolynomial (Fin 2) ℚ) _ (X 1)

/-- The pencil parameter `ζ = −f₀/f₁` (Lemma 3.1) as a plane rational function. -/
public noncomputable def planeZeta : FunctionField.planeField ℚ :=
  FunctionField.pencilParameter f₀aff f₁aff

/-- Evaluation of the ambient ring `ℚ[x, y, z]` into the plane function field:
`x ↦ x`, `y ↦ y`, `z ↦ ζ`. -/
public noncomputable def toPlane :
    MvPolynomial (Fin 3) ℚ →ₐ[ℚ] FunctionField.planeField ℚ :=
  aeval ![planeX, planeY, planeZeta]

public theorem toPlane_X0 : toPlane (X 0) = planeX := by simp [toPlane]
public theorem toPlane_X1 : toPlane (X 1) = planeY := by simp [toPlane]
public theorem toPlane_X2 : toPlane (X 2) = planeZeta := by simp [toPlane]

/-- On bivariate polynomials (composed with the inclusion of the first two
variables), `toPlane` is the canonical map to the fraction field. -/
private theorem toPlane_rename (f : MvPolynomial (Fin 2) ℚ) :
    toPlane (rename Fin.castSucc f)
      = algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) f := by
  rw [show toPlane (rename Fin.castSucc f)
      = aeval (![planeX, planeY, planeZeta] ∘ Fin.castSucc) f from aeval_rename _ _ _]
  have hfun : (![planeX, planeY, planeZeta] ∘ Fin.castSucc) = ![planeX, planeY] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun]
  have h := MvPolynomial.algHom_ext
    (f := aeval (R := ℚ) ![planeX, planeY])
    (g := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ))
    (fun i => by fin_cases i <;> simp [planeX, planeY])
  exact DFunLike.congr_fun h f

/-- The pencil cubic dies under `toPlane` — Lemma 3.1 in evaluation form. -/
public theorem toPlane_gAff : toPlane gAff = 0 := by
  have h31 := (FunctionField.adjoin_pencil_parameter_eq_top f₀aff f₁aff f₁aff_ne_zero).1
  rw [← pencilRelation_eq_gAff]
  unfold FunctionField.pencilRelation
  rw [map_add, map_mul, toPlane_rename, toPlane_rename, toPlane_X2]
  exact h31

/-! ## The Weierstrass identity over `ℚ(x, y)` -/

/-- The cleared Weierstrass identity of note (3.7), evaluated in the plane
function field along `z ↦ ζ`. -/
public theorem weierstrass_identity_plane :
    toPlane jAff ^ 2 = 4 * toPlane thetaAff ^ 3
      + 4 * toPlane weierstrassA * toPlane thetaAff * toPlane hessAff ^ 4
      + toPlane weierstrassBnum * toPlane hessAff ^ 6 := by
  obtain ⟨c, hc⟩ := weierstrass_congruence_mod_gAff
  have h := congrArg toPlane hc
  simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, toPlane_gAff, zero_mul] at h
  linear_combination h

/-! ## Nonvanishing of the Hessian covariant in `ℚ(x, y)` -/

private noncomputable def hz0 : MvPolynomial (Fin 2) ℚ := 3 * X 0
private noncomputable def hz1 : MvPolynomial (Fin 2) ℚ :=
  3 * X 0 * X 1 - 9 * X 0 * X 1 ^ 2
private noncomputable def hz2 : MvPolynomial (Fin 2) ℚ :=
  9 * X 0 + 27 * X 0 * X 1 + 3 * X 0 * X 1 ^ 2 - 3 * X 0 ^ 2 - 9 * X 0 ^ 2 * X 1
private noncomputable def hz3 : MvPolynomial (Fin 2) ℚ := -1 - 3 * X 1

private theorem A_hz0 :
    algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) hz0 = 3 * planeX := by
  unfold hz0 planeX
  rw [map_mul, map_ofNat]

private theorem A_hz1 :
    algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) hz1
      = 3 * planeX * planeY - 9 * planeX * planeY ^ 2 := by
  unfold hz1 planeX planeY
  simp only [map_sub, map_mul, map_pow, map_ofNat]

private theorem A_hz2 :
    algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) hz2
      = 9 * planeX + 27 * planeX * planeY + 3 * planeX * planeY ^ 2
        - 3 * planeX ^ 2 - 9 * planeX ^ 2 * planeY := by
  unfold hz2 planeX planeY
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]

private theorem A_hz3 :
    algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) hz3
      = -1 - 3 * planeY := by
  unfold hz3 planeY
  simp only [map_sub, map_mul, map_neg, map_one, map_ofNat]

private theorem toPlane_hessAff_decomp :
    toPlane hessAff
      = algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) hz0
        + algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) hz1 * planeZeta
        + algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) hz2 * planeZeta ^ 2
        + algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) hz3 * planeZeta ^ 3 := by
  rw [A_hz0, A_hz1, A_hz2, A_hz3]
  unfold hessAff
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, map_neg,
    toPlane_X0, toPlane_X1, toPlane_X2]
  ring

/-- `hessAff(x, y, −f₀/f₁)` with denominators cleared by `f₁³`. -/
private noncomputable def hessClear : MvPolynomial (Fin 2) ℚ :=
  hz0 * f₁aff ^ 3 - hz1 * f₀aff * f₁aff ^ 2 + hz2 * f₀aff ^ 2 * f₁aff - hz3 * f₀aff ^ 3

private theorem hessClear_ne_zero : hessClear ≠ 0 := by
  intro h
  have h1 := congrArg (eval ![(2 : ℚ), 0]) h
  simp [hessClear, hz0, hz1, hz2, hz3, f₀aff, f₁aff] at h1
  norm_num at h1

/-- The Hessian covariant does not vanish as a plane rational function. -/
public theorem toPlane_hessAff_ne_zero : toPlane hessAff ≠ 0 := by
  intro hcon
  have hF₁ : algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) f₁aff ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact f₁aff_ne_zero
  set A := algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) with hA
  -- expand `toPlane hessAff` along the z-decomposition
  have hdec := toPlane_hessAff_decomp
  rw [hcon] at hdec
  replace hdec := hdec.symm
  -- the parameter is `−F₀/F₁`
  have hzeta : planeZeta = -(A f₀aff) / A f₁aff := rfl
  rw [hzeta] at hdec
  -- clear denominators
  have hcleared : A hessClear = 0 := by
    have hMap : A hessClear
        = A hz0 * A f₁aff ^ 3 - A hz1 * A f₀aff * A f₁aff ^ 2
          + A hz2 * (A f₀aff) ^ 2 * A f₁aff - A hz3 * (A f₀aff) ^ 3 := by
      unfold hessClear
      simp only [map_sub, map_add, map_mul, map_pow]
    rw [hMap]
    have hd := congrArg (fun t => t * A f₁aff ^ 3) hdec
    simp only [zero_mul] at hd
    field_simp at hd
    linear_combination hd
  rw [hA, IsFractionRing.to_map_eq_zero_iff] at hcleared
  exact hessClear_ne_zero hcleared

/-! ## The point of the Weierstrass surface over `ℚ(x, y)` -/

/-- `ξ = Θ/H²` as a plane rational function. -/
public noncomputable def xiPlane : FunctionField.planeField ℚ :=
  toPlane thetaAff / toPlane hessAff ^ 2

/-- `η = J/(2H³)` as a plane rational function. -/
public noncomputable def etaPlane : FunctionField.planeField ℚ :=
  toPlane jAff / (2 * toPlane hessAff ^ 3)

/-- The Weierstrass model of note (3.7) over the plane function field, with the
fibre parameter specialized to the pencil parameter `ζ = −f₀/f₁`.  Its
coefficients are the defining polynomials of `noteCurveQ` (`a₄ = z²(3 − z)`,
`a₆ = (z/4)·P(z)`) evaluated at `z = ζ`. -/
public noncomputable def noteCurvePlane : WeierstrassCurve (FunctionField.planeField ℚ) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := planeZeta ^ 2 * (3 - planeZeta)
  a₆ := planeZeta / 4 * (4 * planeZeta ^ 4 - 23 * planeZeta ^ 3
    - 18 * planeZeta ^ 2 + planeZeta - 4)

private theorem a4_plane : noteCurvePlane.a₄ = toPlane weierstrassA := by
  show planeZeta ^ 2 * (3 - planeZeta) = _
  unfold weierstrassA
  simp only [map_sub, map_mul, map_pow, map_ofNat, toPlane_X2]

private theorem a6_plane : 4 * noteCurvePlane.a₆ = toPlane weierstrassBnum := by
  show (4 : FunctionField.planeField ℚ) * (planeZeta / 4 * _) = _
  unfold weierstrassBnum
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one, toPlane_X2]
  ring

/-- **Unirationality, field-theoretic form**: the plane rational functions
`ξ = Θ/H²`, `η = J/(2H³)` satisfy the Weierstrass equation of the note's
model (3.7) with parameter `ζ = −f₀/f₁`, inside the rational function field
`ℚ(x, y)`.  (This is the *point* of the surface over `ℚ(x, y)`; the induced
coordinate-ring homomorphism is `surfaceCoordRingToPlane` below.  Upgrading
it to a field embedding `K(S) ↪ ℚ(x, y)` — dominance — additionally requires
the transcendence facts discussed in the module docstring.) -/
public theorem noteCurvePlane_equation :
    noteCurvePlane.toAffine.Equation xiPlane etaPlane := by
  haveI : CharZero (FunctionField.planeField ℚ) :=
    Algebra.charZero_of_charZero (R := ℚ) (A := FunctionField.planeField ℚ)
  rw [WeierstrassCurve.Affine.equation_iff]
  have hidP := weierstrass_identity_plane
  rw [← a4_plane, ← a6_plane] at hidP
  set H := toPlane hessAff with hH
  set J := toPlane jAff with hJ
  set Th := toPlane thetaAff with hTh
  have hne : H ≠ 0 := toPlane_hessAff_ne_zero
  have h4H : (4 : FunctionField.planeField ℚ) * H ^ 6 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ hne)
  show etaPlane ^ 2 + noteCurvePlane.a₁ * xiPlane * etaPlane + noteCurvePlane.a₃ * etaPlane
      = xiPlane ^ 3 + noteCurvePlane.a₂ * xiPlane ^ 2 + noteCurvePlane.a₄ * xiPlane
        + noteCurvePlane.a₆
  rw [show noteCurvePlane.a₁ = 0 from rfl, show noteCurvePlane.a₂ = 0 from rfl,
    show noteCurvePlane.a₃ = 0 from rfl]
  have heta : etaPlane ^ 2 = J ^ 2 / (4 * H ^ 6) := by
    unfold etaPlane
    rw [← hJ, ← hH, div_pow,
      show ((2 : FunctionField.planeField ℚ) * H ^ 3) ^ 2 = 4 * H ^ 6 by ring]
  rw [heta]
  simp only [zero_mul, mul_zero, add_zero, zero_add]
  rw [div_eq_iff h4H]
  unfold xiPlane
  rw [← hTh, ← hH]
  field_simp
  linear_combination hidP

/-! ## The coordinate-ring homomorphism -/

/-- Affine equation of the note-(3.7) elliptic surface with denominators
cleared: `4η² − 4ξ³ − 4z²(3−z)·ξ − z·P(z)`, coordinates `0 ↦ ξ`, `1 ↦ η`,
`2 ↦ z`. -/
public noncomputable def weierstrassSurfaceAff : MvPolynomial (Fin 3) ℚ :=
  4 * X 1 ^ 2 - 4 * X 0 ^ 3 - 4 * (X 2 ^ 2 * (3 - X 2)) * X 0
    - X 2 * (4 * X 2 ^ 4 - 23 * X 2 ^ 3 - 18 * X 2 ^ 2 + X 2 - 4)

/-- Evaluation of the surface coordinates at the plane point
`(ξ, η, ζ) ∈ ℚ(x, y)³`. -/
public noncomputable def surfaceToPlane :
    MvPolynomial (Fin 3) ℚ →ₐ[ℚ] FunctionField.planeField ℚ :=
  aeval ![xiPlane, etaPlane, planeZeta]

/-- The surface equation vanishes at the plane point. -/
public theorem surfaceToPlane_vanishes : surfaceToPlane weierstrassSurfaceAff = 0 := by
  haveI : CharZero (FunctionField.planeField ℚ) :=
    Algebra.charZero_of_charZero (R := ℚ) (A := FunctionField.planeField ℚ)
  have heq := noteCurvePlane_equation
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  rw [show noteCurvePlane.a₁ = 0 from rfl, show noteCurvePlane.a₂ = 0 from rfl,
    show noteCurvePlane.a₃ = 0 from rfl] at heq
  have ha₄ : noteCurvePlane.a₄ = planeZeta ^ 2 * (3 - planeZeta) := rfl
  have ha₆ : noteCurvePlane.a₆ = planeZeta / 4 * (4 * planeZeta ^ 4
    - 23 * planeZeta ^ 3 - 18 * planeZeta ^ 2 + planeZeta - 4) := rfl
  rw [ha₄, ha₆] at heq
  unfold weierstrassSurfaceAff surfaceToPlane
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination 4 * heq

/-- **The unirationality homomorphism**: the ℚ-algebra homomorphism from the
affine coordinate ring of the note's Weierstrass surface (3.7) to the rational
function field `ℚ(x, y)`, sending `ξ ↦ Θ/H²`, `η ↦ J/(2H³)` and the fibre
parameter `z` to the pencil parameter `−f₀/f₁` of Lemma 3.1.  Injectivity of
this map (= dominance of the underlying rational map `𝔸² ⤏ S`, = the field
embedding `K(S) ↪ ℚ(x, y)`) is *not* proved here; see the module docstring. -/
public noncomputable def surfaceCoordRingToPlane :
    (MvPolynomial (Fin 3) ℚ ⧸ Ideal.span {weierstrassSurfaceAff})
      →ₐ[ℚ] FunctionField.planeField ℚ :=
  Ideal.Quotient.liftₐ (Ideal.span {weierstrassSurfaceAff}) surfaceToPlane
    (fun a ha => by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
      · rintro x rfl
        exact surfaceToPlane_vanishes
      · exact map_zero _
      · intro x y _ _ hx hy
        rw [map_add, hx, hy, add_zero]
      · intro r x _ hx
        rw [smul_eq_mul, map_mul, hx, mul_zero])

@[simp]
public theorem surfaceCoordRingToPlane_mk (p : MvPolynomial (Fin 3) ℚ) :
    surfaceCoordRingToPlane (Ideal.Quotient.mk _ p) = surfaceToPlane p := by
  simp [surfaceCoordRingToPlane]

#print axioms toPlane_gAff
#print axioms weierstrass_identity_plane
#print axioms toPlane_hessAff_ne_zero
#print axioms noteCurvePlane_equation
#print axioms surfaceToPlane_vanishes

end ExplicitUnirational
