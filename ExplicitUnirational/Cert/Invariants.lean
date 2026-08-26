/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Hessian normalization and Fisher invariants of the cubic pencils

Formalization of the Hessian normalization `[CLOP Example 2.1]`, the invariants
`[CLOP §4.1]` / `[CLOP §4.2]`, the expanded Hessian `[CLOP §4.2]`, and the covariant
identity `[CLOP (2.2)]` for the rational pencil.

Numeric coefficients are plain numerals (so bare `simp` closes partials). The
coefficient map `C` is reserved for genuine parameters (`z`, `μ`, `t`, `λ`, …).

Coordinates: `X = X 0`, `Y = X 1`, `Z = X 2`.
-/

noncomputable section

open MvPolynomial Matrix

namespace ExplicitUnirational.Invariants

/-! ## Hessian normalization `[CLOP Example 2.1]` -/

/-- The matrix of second partial derivatives of a ternary polynomial. -/
public noncomputable def hessianMatrix {R : Type*} [CommRing R]
    (G : MvPolynomial (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) R) :=
  fun i j => pderiv i (pderiv j G)

/-- The Hessian normalization `H(G) = -(1/2) det (d^2 G / dX_i dX_j)` of `[CLOP Example 2.1]`.

The factor `1/2` is realized by `Ring.inverse` so the definition typechecks for every
`CommRing`. Whenever `2` is a unit (in particular over `ℚ`) this is the classical
normalization. -/
public noncomputable def hessian {R : Type*} [CommRing R] (G : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 3) R :=
  -C (Ring.inverse (2 : R)) * (hessianMatrix G).det

private theorem hessian_eq_neg_half_det (G : MvPolynomial (Fin 3) ℚ) :
    hessian G = -C (1 / 2 : ℚ) * (hessianMatrix G).det := by
  unfold hessian
  have h2 : Ring.inverse (2 : ℚ) = (1 / 2 : ℚ) := by
    rw [Ring.inverse_eq_inv, inv_eq_one_div]
  rw [h2]

/-- `pderiv` kills a bare numeral. Mathlib has `pderiv_C`, but a numeric literal is not
syntactically `C n`. The generic form with `[n.AtLeastTwo]` is not applied by `simp`
(the instance blocks unification); concrete `@[simp]` instances below do fire. -/
private lemma pderiv_ofNat (i : Fin 3) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (OfNat.ofNat n : MvPolynomial (Fin 3) ℚ) = 0 := by
  rw [← map_ofNat (C : ℚ →+* MvPolynomial (Fin 3) ℚ) n, pderiv_C]

@[simp] private lemma pderiv_two (i : Fin 3) :
    pderiv i (2 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_ofNat i 2

@[simp] private lemma pderiv_three (i : Fin 3) :
    pderiv i (3 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_ofNat i 3

@[simp] private lemma pderiv_four (i : Fin 3) :
    pderiv i (4 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_ofNat i 4

@[simp] private lemma pderiv_six (i : Fin 3) :
    pderiv i (6 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_ofNat i 6

@[simp] private lemma pderiv_twelve (i : Fin 3) :
    pderiv i (12 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_ofNat i 12

@[simp] private lemma pderiv_twentyFour (i : Fin 3) :
    pderiv i (24 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_ofNat i 24

@[simp] private lemma pderiv_thirtySix (i : Fin 3) :
    pderiv i (36 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_ofNat i 36

@[simp] private lemma pderiv_seventyTwo (i : Fin 3) :
    pderiv i (72 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_ofNat i 72

@[simp] private lemma pderiv_oneOhEight (i : Fin 3) :
    pderiv i (108 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_ofNat i 108

/-- `C n` for a bare numeral does not reduce to the polynomial numeral without a concrete
instance (same instance-blocking issue as `pderiv_ofNat`). -/
private lemma C_ofNat (n : ℕ) [n.AtLeastTwo] :
    C (OfNat.ofNat n : ℚ) = (OfNat.ofNat n : MvPolynomial (Fin 3) ℚ) :=
  map_ofNat (C : ℚ →+* MvPolynomial (Fin 3) ℚ) n

@[simp] private lemma C_two : C (2 : ℚ) = (2 : MvPolynomial (Fin 3) ℚ) := C_ofNat 2
@[simp] private lemma C_three : C (3 : ℚ) = (3 : MvPolynomial (Fin 3) ℚ) := C_ofNat 3
@[simp] private lemma C_four : C (4 : ℚ) = (4 : MvPolynomial (Fin 3) ℚ) := C_ofNat 4
@[simp] private lemma C_six : C (6 : ℚ) = (6 : MvPolynomial (Fin 3) ℚ) := C_ofNat 6
@[simp] private lemma C_twelve : C (12 : ℚ) = (12 : MvPolynomial (Fin 3) ℚ) := C_ofNat 12
@[simp] private lemma C_eighteen : C (18 : ℚ) = (18 : MvPolynomial (Fin 3) ℚ) := C_ofNat 18
@[simp] private lemma C_twentyThree : C (23 : ℚ) = (23 : MvPolynomial (Fin 3) ℚ) := C_ofNat 23
@[simp] private lemma C_twentyFour : C (24 : ℚ) = (24 : MvPolynomial (Fin 3) ℚ) := C_ofNat 24
@[simp] private lemma C_thirtySix : C (36 : ℚ) = (36 : MvPolynomial (Fin 3) ℚ) := C_ofNat 36
@[simp] private lemma C_fortyEight : C (48 : ℚ) = (48 : MvPolynomial (Fin 3) ℚ) := C_ofNat 48
@[simp] private lemma C_seventyTwo : C (72 : ℚ) = (72 : MvPolynomial (Fin 3) ℚ) := C_ofNat 72
@[simp] private lemma C_oneOhEight : C (108 : ℚ) = (108 : MvPolynomial (Fin 3) ℚ) := C_ofNat 108
@[simp] private lemma C_twoSixteen : C (216 : ℚ) = (216 : MvPolynomial (Fin 3) ℚ) := C_ofNat 216

private theorem two_eq_C_two :
    (2 : MvPolynomial (Fin 3) ℚ) = C (2 : ℚ) :=
  C_two.symm

private theorem hessian_eq_of_det_eq (G H : MvPolynomial (Fin 3) ℚ)
    (h : (hessianMatrix G).det = -(2 : MvPolynomial (Fin 3) ℚ) * H) :
    hessian G = H := by
  have hC : C ((2 : ℚ)⁻¹) * (2 : MvPolynomial (Fin 3) ℚ) = 1 := by
    rw [two_eq_C_two, ← map_mul]
    norm_num
  -- `-C (1/2) * (-2 * H) = (C (1/2) * 2) * H = H`
  rw [hessian_eq_neg_half_det, h, one_div, ← mul_assoc, neg_mul_neg, hC, one_mul]

private theorem hessianMatrix_add_C_mul (i j : Fin 3) (a : ℚ)
    (f g : MvPolynomial (Fin 3) ℚ) :
    hessianMatrix (f + C a * g) i j =
      hessianMatrix f i j + C a * hessianMatrix g i j := by
  simp only [hessianMatrix, map_add, pderiv_C_mul]

/-! ## Rational pencil and invariants `[CLOP §4.1]` -/

/-- `F₀ = Y Z² - X³` of `[CLOP §4.1]` (there written `f₀ = yz² - x³`). -/
public noncomputable def F0_rat : MvPolynomial (Fin 3) ℚ :=
  X 1 * X 2 ^ 2 - X 0 ^ 3

/-- `F₁ = X Z² + Y³ + Y² Z - Z³` of `[CLOP §4.1]` (there written
`f₁ = xz² + y³ + y²z - z³`). -/
public noncomputable def F1_rat : MvPolynomial (Fin 3) ℚ :=
  X 0 * X 2 ^ 2 + X 1 ^ 3 + X 1 ^ 2 * X 2 - X 2 ^ 3

/-- Generic member `G_z = F₀ + z F₁` of the rational pencil. -/
public noncomputable def G_z (z : ℚ) : MvPolynomial (Fin 3) ℚ :=
  F0_rat + C z * F1_rat

/-- `P(z) = 4z⁴ - 23z³ - 18z² + z - 4`, the quartic factor of `c₆` in `[CLOP §4.1]`. -/
public def P_rat (z : ℚ) : ℚ :=
  4 * z ^ 4 - 23 * z ^ 3 - 18 * z ^ 2 + z - 4

/-- `c₄(z) = 48 z² (z - 3)` of `[CLOP §4.1]`. -/
public def c4_rat (z : ℚ) : ℚ :=
  48 * z ^ 2 * (z - 3)

/-- `c₆(z) = -216 z P(z)` of `[CLOP §4.1]`. -/
public def c6_rat (z : ℚ) : ℚ :=
  -216 * z * P_rat z

/-- Expanded Hessian of `G_z`. Numeric literals are plain; `C` carries the parameter `z`. -/
public noncomputable def H_G_z (z : ℚ) : MvPolynomial (Fin 3) ℚ :=
  36 * C z ^ 2 * (X 0 ^ 2 * X 1) + 12 * C z ^ 2 * (X 0 ^ 2 * X 2)
    - 12 * C z ^ 2 * (X 0 * X 1 ^ 2) + 36 * C z * (X 0 * X 1 ^ 2)
    - 108 * C z ^ 2 * (X 0 * X 1 * X 2) - 12 * C z * (X 0 * X 1 * X 2)
    - 36 * C z ^ 2 * (X 0 * X 2 ^ 2) - 12 * (X 0 * X 2 ^ 2)
    + 12 * C z ^ 3 * (X 1 * X 2 ^ 2) + 4 * C z ^ 3 * (X 2 ^ 3)

/-! ### Hessian matrix of `G_z` (plain numerals; bare `simp`) -/

private theorem hess00_G_z (z : ℚ) : hessianMatrix (G_z z) 0 0 = -6 * X 0 := by
  unfold hessianMatrix G_z F0_rat F1_rat
  simp; ring

private theorem hess01_G_z (z : ℚ) : hessianMatrix (G_z z) 0 1 = 0 := by
  unfold hessianMatrix G_z F0_rat F1_rat
  simp

private theorem hess02_G_z (z : ℚ) : hessianMatrix (G_z z) 0 2 = 2 * C z * X 2 := by
  unfold hessianMatrix G_z F0_rat F1_rat
  simp; ring

private theorem hess10_G_z (z : ℚ) : hessianMatrix (G_z z) 1 0 = 0 := by
  unfold hessianMatrix G_z F0_rat F1_rat
  simp

private theorem hess11_G_z (z : ℚ) :
    hessianMatrix (G_z z) 1 1 = 6 * C z * X 1 + 2 * C z * X 2 := by
  unfold hessianMatrix G_z F0_rat F1_rat
  simp; ring

private theorem hess12_G_z (z : ℚ) :
    hessianMatrix (G_z z) 1 2 = 2 * C z * X 1 + 2 * X 2 := by
  unfold hessianMatrix G_z F0_rat F1_rat
  simp; ring

private theorem hess20_G_z (z : ℚ) : hessianMatrix (G_z z) 2 0 = 2 * C z * X 2 := by
  unfold hessianMatrix G_z F0_rat F1_rat
  simp; ring

private theorem hess21_G_z (z : ℚ) :
    hessianMatrix (G_z z) 2 1 = 2 * C z * X 1 + 2 * X 2 := by
  unfold hessianMatrix G_z F0_rat F1_rat
  simp; ring

private theorem hess22_G_z (z : ℚ) :
    hessianMatrix (G_z z) 2 2 = 2 * C z * X 0 + 2 * X 1 - 6 * C z * X 2 := by
  unfold hessianMatrix G_z F0_rat F1_rat
  simp; ring

private theorem det_hess_G_z (z : ℚ) :
    (hessianMatrix (G_z z)).det = -(2 : MvPolynomial (Fin 3) ℚ) * H_G_z z := by
  rw [det_fin_three]
  simp only [hess00_G_z, hess01_G_z, hess02_G_z, hess10_G_z, hess11_G_z, hess12_G_z,
    hess20_G_z, hess21_G_z, hess22_G_z, H_G_z]
  ring

/-- Closed form of the Hessian of the rational pencil member `G_z`. -/
public theorem hessian_G_z_eq (z : ℚ) : hessian (G_z z) = H_G_z z :=
  hessian_eq_of_det_eq _ _ (det_hess_G_z z)

/-! ### Hessian matrix of the closed form `H_G_z` -/

private theorem hess00_H_G_z (z : ℚ) :
    hessianMatrix (H_G_z z) 0 0 = 72 * C z ^ 2 * X 1 + 24 * C z ^ 2 * X 2 := by
  unfold hessianMatrix H_G_z
  simp; ring

private theorem hess01_H_G_z (z : ℚ) :
    hessianMatrix (H_G_z z) 0 1 =
      72 * C z ^ 2 * X 0 + (-24 * C z ^ 2 + 72 * C z) * X 1
        + (-108 * C z ^ 2 - 12 * C z) * X 2 := by
  unfold hessianMatrix H_G_z
  simp; ring

private theorem hess02_H_G_z (z : ℚ) :
    hessianMatrix (H_G_z z) 0 2 =
      24 * C z ^ 2 * X 0 + (-108 * C z ^ 2 - 12 * C z) * X 1
        + (-72 * C z ^ 2 - 24) * X 2 := by
  unfold hessianMatrix H_G_z
  simp; ring

private theorem hess10_H_G_z (z : ℚ) :
    hessianMatrix (H_G_z z) 1 0 =
      72 * C z ^ 2 * X 0 + (-24 * C z ^ 2 + 72 * C z) * X 1
        + (-108 * C z ^ 2 - 12 * C z) * X 2 := by
  unfold hessianMatrix H_G_z
  simp; ring

private theorem hess11_H_G_z (z : ℚ) :
    hessianMatrix (H_G_z z) 1 1 = (-24 * C z ^ 2 + 72 * C z) * X 0 := by
  unfold hessianMatrix H_G_z
  simp; ring

private theorem hess12_H_G_z (z : ℚ) :
    hessianMatrix (H_G_z z) 1 2 =
      (-108 * C z ^ 2 - 12 * C z) * X 0 + 24 * C z ^ 3 * X 2 := by
  unfold hessianMatrix H_G_z
  simp; ring

private theorem hess20_H_G_z (z : ℚ) :
    hessianMatrix (H_G_z z) 2 0 =
      24 * C z ^ 2 * X 0 + (-108 * C z ^ 2 - 12 * C z) * X 1
        + (-72 * C z ^ 2 - 24) * X 2 := by
  unfold hessianMatrix H_G_z
  simp; ring

private theorem hess21_H_G_z (z : ℚ) :
    hessianMatrix (H_G_z z) 2 1 =
      (-108 * C z ^ 2 - 12 * C z) * X 0 + 24 * C z ^ 3 * X 2 := by
  unfold hessianMatrix H_G_z
  simp; ring

private theorem hess22_H_G_z (z : ℚ) :
    hessianMatrix (H_G_z z) 2 2 =
      (-72 * C z ^ 2 - 24) * X 0 + 24 * C z ^ 3 * X 1 + 24 * C z ^ 3 * X 2 := by
  unfold hessianMatrix H_G_z
  simp; ring

/-! ### The invariants `c₄`, `c₆` of `[CLOP §4.1]` -/

/-- `[CLOP §4.1]`: the Fisher invariants of the generic member of the pencil over `ℚ`. -/
public theorem c4_c6_rat (z : ℚ) :
    c4_rat z = 48 * z ^ 2 * (z - 3) ∧ c6_rat z = -216 * z * P_rat z := by
  constructor <;> rfl

/-! ### Identity `[CLOP (2.2)]` -/

private noncomputable def Gmu (z mu : ℚ) : MvPolynomial (Fin 3) ℚ :=
  G_z z + C mu * H_G_z z

private theorem hess_Gmu (z mu : ℚ) (i j : Fin 3) :
    hessianMatrix (Gmu z mu) i j =
      hessianMatrix (G_z z) i j + C mu * hessianMatrix (H_G_z z) i j :=
  hessianMatrix_add_C_mul i j mu (G_z z) (H_G_z z)

private noncomputable def rhs_identity (z mu : ℚ) : MvPolynomial (Fin 3) ℚ :=
  C (3 * (c4_rat z * mu + 2 * c6_rat z * mu ^ 2 + c4_rat z ^ 2 * mu ^ 3)) * G_z z
    + C (1 - 3 * c4_rat z * mu ^ 2 - 2 * c6_rat z * mu ^ 3) * H_G_z z

private theorem det_hess_Gmu (z mu : ℚ) :
    (hessianMatrix (Gmu z mu)).det = -(2 : MvPolynomial (Fin 3) ℚ) * rhs_identity z mu := by
  rw [det_fin_three]
  -- Apply closed-form Hessian entries first (before unfolding G_z / H_G_z).
  simp only [hess_Gmu, hess00_G_z, hess01_G_z, hess02_G_z, hess10_G_z, hess11_G_z, hess12_G_z,
    hess20_G_z, hess21_G_z, hess22_G_z, hess00_H_G_z, hess01_H_G_z, hess02_H_G_z, hess10_H_G_z,
    hess11_H_G_z, hess12_H_G_z, hess20_H_G_z, hess21_H_G_z, hess22_H_G_z]
  -- Unfold the RHS, push `C` through coefficient arithmetic, and reduce `C n` numerals.
  simp only [rhs_identity, G_z, H_G_z, F0_rat, F1_rat, c4_rat, c6_rat, P_rat]
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_neg, C_two, C_three, C_four,
    C_eighteen, C_twentyThree, C_fortyEight, C_twoSixteen]
  ring

/-- `[CLOP (2.2)]` holds for the pencil over `ℚ` with the invariants of `[CLOP §4.1]`. -/
public theorem hessian_identity_rat (z mu : ℚ) :
    hessian (G_z z + C mu * hessian (G_z z)) =
      C (3 * (c4_rat z * mu + 2 * c6_rat z * mu ^ 2 + c4_rat z ^ 2 * mu ^ 3)) * G_z z
        + C (1 - 3 * c4_rat z * mu ^ 2 - 2 * c6_rat z * mu ^ 3) * hessian (G_z z) := by
  rw [hessian_G_z_eq]
  change hessian (Gmu z mu) = rhs_identity z mu
  exact hessian_eq_of_det_eq _ _ (det_hess_Gmu z mu)

/-! ## Pencil over `C(t)`: `[CLOP §4.2]` -/

/-- `F₀ = Y Z² - X³` of `[CLOP §4.2]`. -/
public noncomputable def F0_Ct : MvPolynomial (Fin 3) ℚ :=
  F0_rat

/-- `F₁ = Y³ - X Z² - 2 t Z³` of `[CLOP §4.2]`. -/
public noncomputable def F1_Ct (t : ℚ) : MvPolynomial (Fin 3) ℚ :=
  X 1 ^ 3 - X 0 * X 2 ^ 2 - 2 * C t * X 2 ^ 3

/-- Generic member `G_λ = F₀ + λ F₁` of the pencil of `[CLOP §4.2]`. -/
public noncomputable def G_lambda (t lam : ℚ) : MvPolynomial (Fin 3) ℚ :=
  F0_Ct + C lam * F1_Ct t

/-- `c₄(λ) = 144 λ²` of `[CLOP §4.2]`. -/
public def c4_lambda (lam : ℚ) : ℚ :=
  144 * lam ^ 2

/-- `c₆(λ) = 864 λ (λ⁴ + 27 t² λ³ + 1)` of `[CLOP §4.2]`. -/
public def c6_lambda (t lam : ℚ) : ℚ :=
  864 * lam * (lam ^ 4 + 27 * t ^ 2 * lam ^ 3 + 1)

/-- `[CLOP §4.2]`: the Fisher invariants of the generic member of the pencil over `C(t)`. -/
public theorem c4_c6_lambda (t lam : ℚ) :
    c4_lambda lam = 144 * lam ^ 2 ∧
    c6_lambda t lam = 864 * lam * (lam ^ 4 + 27 * t ^ 2 * lam ^ 3 + 1) := by
  constructor <;> rfl

/-- Right-hand side of the displayed Hessian `H(g)` of `[CLOP §4.2]`. -/
public noncomputable def H_G_lambda (t lam : ℚ) : MvPolynomial (Fin 3) ℚ :=
  -36 * C lam ^ 2 * (X 0 ^ 2 * X 1) + 36 * C lam * (X 0 * X 1 ^ 2)
    - 216 * C t * C lam ^ 2 * (X 0 * X 1 * X 2) - 12 * (X 0 * X 2 ^ 2)
    + 12 * C lam ^ 3 * (X 1 * X 2 ^ 2)

private theorem hess00_G_lambda (t lam : ℚ) :
    hessianMatrix (G_lambda t lam) 0 0 = -6 * X 0 := by
  unfold hessianMatrix G_lambda F0_Ct F0_rat F1_Ct
  simp; ring

private theorem hess01_G_lambda (t lam : ℚ) : hessianMatrix (G_lambda t lam) 0 1 = 0 := by
  unfold hessianMatrix G_lambda F0_Ct F0_rat F1_Ct
  simp

private theorem hess02_G_lambda (t lam : ℚ) :
    hessianMatrix (G_lambda t lam) 0 2 = -2 * C lam * X 2 := by
  unfold hessianMatrix G_lambda F0_Ct F0_rat F1_Ct
  simp; ring

private theorem hess10_G_lambda (t lam : ℚ) : hessianMatrix (G_lambda t lam) 1 0 = 0 := by
  unfold hessianMatrix G_lambda F0_Ct F0_rat F1_Ct
  simp

private theorem hess11_G_lambda (t lam : ℚ) :
    hessianMatrix (G_lambda t lam) 1 1 = 6 * C lam * X 1 := by
  unfold hessianMatrix G_lambda F0_Ct F0_rat F1_Ct
  simp; ring

private theorem hess12_G_lambda (t lam : ℚ) :
    hessianMatrix (G_lambda t lam) 1 2 = 2 * X 2 := by
  unfold hessianMatrix G_lambda F0_Ct F0_rat F1_Ct
  simp

private theorem hess20_G_lambda (t lam : ℚ) :
    hessianMatrix (G_lambda t lam) 2 0 = -2 * C lam * X 2 := by
  unfold hessianMatrix G_lambda F0_Ct F0_rat F1_Ct
  simp; ring

private theorem hess21_G_lambda (t lam : ℚ) :
    hessianMatrix (G_lambda t lam) 2 1 = 2 * X 2 := by
  unfold hessianMatrix G_lambda F0_Ct F0_rat F1_Ct
  simp

private theorem hess22_G_lambda (t lam : ℚ) :
    hessianMatrix (G_lambda t lam) 2 2 =
      -2 * C lam * X 0 + 2 * X 1 - 12 * C t * C lam * X 2 := by
  unfold hessianMatrix G_lambda F0_Ct F0_rat F1_Ct
  simp; ring

private theorem det_hess_G_lambda (t lam : ℚ) :
    (hessianMatrix (G_lambda t lam)).det =
      -(2 : MvPolynomial (Fin 3) ℚ) * H_G_lambda t lam := by
  rw [det_fin_three]
  simp only [hess00_G_lambda, hess01_G_lambda, hess02_G_lambda, hess10_G_lambda, hess11_G_lambda,
    hess12_G_lambda, hess20_G_lambda, hess21_G_lambda, hess22_G_lambda, H_G_lambda]
  ring

/-- `[CLOP §4.2]`: the Hessian of the generic member of the pencil over `C(t)`. -/
public theorem hessian_lambda (t lam : ℚ) :
    hessian (G_lambda t lam) = H_G_lambda t lam :=
  hessian_eq_of_det_eq _ _ (det_hess_G_lambda t lam)

end ExplicitUnirational.Invariants
