/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.Cert.Discriminant
public import ExplicitUnirational.FunctionField.MulThreeCert
public import ExplicitUnirational.FunctionField.TorsorDescent
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Geometric integrality of the generic plane cubic (Torsor gap 1)

[CLOP §4.1]: the generic member of the rational pencil, dehomogenized at `Z = 1`, is the
affine plane cubic

```
  G = (y − x³) + z · (x + y³ + y² − 1) ∈ ℚ(z)[x, y].
```

## Status

1. **Definitions** of the pencil parameter, monic cubic in `y` over `R[x]`, and non-monic form.
2. **Monicity and degree** of `monicCubicY` (monic of degree 3).
3. **Integral root form**: a monic-cubic root `r ∈ R[X]` yields
   `z r³ + z r² + r + z X − z = X³`.
4. **No roots** of that integral equation in `R[X]` (degrees ≥ 2, = 1, = 0).
5. **Irreducibility** of `monicCubicY R` over `R[X]` for any char-0 `KQ`-field `R` with
   `param R ≠ 0`, in particular over `KQ` and over `AlgebraicClosure KQ`.
6. **Affine coordinate ring** `AdjoinRoot (monicCubicY R)` is a domain; its fraction field is the
   function field of the affine model.
7. **Tensor-is-a-field packaging**: `Algebra.TensorProduct.isField_of_isAlgebraic` specialized so
   that for `Kp = AlgebraicClosure KQ` the algebraic side is `Or.inr` (no need for algebraic
   `L/KQ`). The domain hypothesis is discharged unconditionally for the affine coordinate ring
   after base change (`isDomain_geometric_affineCoordRing`). For the function-field tensor
   `curveFieldKQ ⊗[KQ] AlgebraicClosure KQ`, the same packaging is available under an `IsDomain`
   hypothesis (`isField_curveField_tensor_algClosure`) — lifting affine geometric integrality to
   the fraction-field tensor is the residual non-mechanical step.
-/

noncomputable section

open Polynomial
open scoped TensorProduct

namespace ExplicitUnirational

/-! ## Parameter and monic cubic -/

/-- Pencil parameter in a `KQ`-algebra. -/
public noncomputable def param (R : Type*) [CommRing R] [Algebra KQ R] : R :=
  algebraMap KQ R RatFunc.X

public theorem param_KQ_ne_zero : param KQ ≠ 0 := by
  change RatFunc.X ≠ 0
  exact RatFunc.X_ne_zero

public theorem param_algClosure_ne_zero : param (AlgebraicClosure KQ) ≠ 0 := by
  change algebraMap KQ (AlgebraicClosure KQ) RatFunc.X ≠ 0
  rw [← map_zero (algebraMap KQ (AlgebraicClosure KQ))]
  exact (FaithfulSMul.algebraMap_injective KQ (AlgebraicClosure KQ)).ne RatFunc.X_ne_zero

/-- Lower-degree summand of the monic cubic in `y`. -/
public noncomputable def monicCubicY_tail (R : Type*) [Field R] [Algebra KQ R] :
    Polynomial (Polynomial R) :=
  let z : R := param R
  X ^ 2 + C (C z⁻¹) * X + C (C z⁻¹ * (-X ^ 3 + C z * X - C z))

/-- Monic cubic in `y` over `R[x]`:
`Y³ + Y² + z⁻¹ Y + z⁻¹ (−x³ + z x − z)`. -/
public noncomputable def monicCubicY (R : Type*) [Field R] [Algebra KQ R] :
    Polynomial (Polynomial R) :=
  X ^ 3 + monicCubicY_tail R

/-- Non-monic form `z Y³ + z Y² + Y − x³ + z x − z`. -/
public noncomputable def affineG_polyY (R : Type*) [CommRing R] [Algebra KQ R] :
    Polynomial (Polynomial R) :=
  let z : R := param R
  C (C z) * X ^ 3 + C (C z) * X ^ 2 + X + C (-X ^ 3 + C z * X - C z)

private theorem tail_natDegree_le (R : Type*) [Field R] [Algebra KQ R] :
    (monicCubicY_tail R).natDegree ≤ 2 := by
  unfold monicCubicY_tail
  have hX2 : ((X : Polynomial (Polynomial R)) ^ 2).natDegree ≤ 2 := by rw [natDegree_X_pow]
  have hCX : (C (C (param R)⁻¹) * X : Polynomial (Polynomial R)).natDegree ≤ 2 := by
    refine le_trans natDegree_mul_le ?_
    simp only [natDegree_C, natDegree_X]; norm_num
  have hC : (C (C (param R)⁻¹ * (-X ^ 3 + C (param R) * X - C (param R))) :
      Polynomial (Polynomial R)).natDegree ≤ 2 := by
    refine le_trans (natDegree_C _).le ?_; norm_num
  refine le_trans (natDegree_add_le _ _) ?_
  exact max_le (le_trans (natDegree_add_le _ _) (max_le hX2 hCX)) hC

private theorem tail_degree_lt (R : Type*) [Field R] [Algebra KQ R] :
    (monicCubicY_tail R).degree < 3 := by
  cases eq_or_ne (monicCubicY_tail R) 0 with
  | inl h0 => rw [h0, degree_zero]; exact WithBot.bot_lt_coe 3
  | inr hne =>
    rw [degree_eq_natDegree hne]
    exact_mod_cast lt_of_le_of_lt (tail_natDegree_le R) (by norm_num : (2 : ℕ) < 3)

public theorem monicCubicY_monic (R : Type*) [Field R] [Algebra KQ R] :
    (monicCubicY R).Monic :=
  monic_X_pow_add (tail_degree_lt R)

public theorem monicCubicY_natDegree (R : Type*) [Field R] [Algebra KQ R] :
    (monicCubicY R).natDegree = 3 := by
  have hlt : (monicCubicY_tail R).degree < (X ^ 3 : Polynomial (Polynomial R)).degree := by
    rw [degree_X_pow (R := Polynomial R)]; exact tail_degree_lt R
  refine (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 3)).1 ?_
  unfold monicCubicY
  rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]

/-! ## Integral root form -/

/-- A monic-cubic root yields the integral polynomial identity
`param · r³ + param · r² + r + param · X − param = X³`. -/
public theorem monicCubicY_root_integral {R : Type*} [Field R] [Algebra KQ R]
    {r : Polynomial R} (hz : param R ≠ 0) (hr : (monicCubicY R).IsRoot r) :
    C (param R) * r ^ 3 + C (param R) * r ^ 2 + r + C (param R) * X - C (param R) =
      X ^ 3 := by
  set z : R := param R
  have hinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  have heval :
      r ^ 3 + (r ^ 2 + C z⁻¹ * r + C z⁻¹ * (-X ^ 3 + C z * X - C z)) = 0 := by
    simpa [IsRoot.def, monicCubicY, monicCubicY_tail, eval_add, eval_pow, eval_mul, eval_C,
      eval_X] using hr
  have hmul := congrArg (fun p : Polynomial R => C z * p) heval
  simp only [mul_zero] at hmul
  have hexpand :
      C z * (r ^ 3 + (r ^ 2 + C z⁻¹ * r + C z⁻¹ * (-X ^ 3 + C z * X - C z))) =
        C z * r ^ 3 + C z * r ^ 2 + r - X ^ 3 + C z * X - C z := by
    have hzC : C z * C z⁻¹ = (1 : Polynomial R) := by rw [← map_mul, hinv, map_one]
    simp only [mul_add, ← mul_assoc, hzC, one_mul]; ring
  rw [hexpand] at hmul
  linear_combination hmul

/-! ## No degree-≥2 roots -/

/-- The integral cubic relation admits no solution of degree ≥ 2. -/
public theorem monicCubicY_no_root_natDegree_ge_two {R : Type*} [Field R]
    {r : Polynomial R} {z : R} (hz : z ≠ 0)
    (hrel : C z * r ^ 3 + C z * r ^ 2 + r + C z * X - C z = X ^ 3)
    (hd : 2 ≤ r.natDegree) : False := by
  have hrz : r ≠ 0 := fun h => by simp [h, natDegree_zero] at hd
  set N := 3 * r.natDegree
  have hcoeff_r3 : (C z * r ^ 3).coeff N = z * r.leadingCoeff ^ 3 := by
    have hdeg : (r ^ 3).natDegree = N := by simp [N, natDegree_pow r 3]
    rw [coeff_C_mul, ← hdeg, coeff_natDegree, leadingCoeff_pow]
  have hcoeff_r2 : (C z * r ^ 2).coeff N = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    by_cases h : r ^ 2 = 0
    · simp [h, natDegree_zero]; omega
    · rw [natDegree_C_mul hz, natDegree_pow r 2]; omega
  have hcoeff_r : r.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeff_lin : (C z * X).coeff N = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C_mul hz, natDegree_X]; omega
  have hcoeff_c : (C z : Polynomial R).coeff N = 0 := by simp [coeff_C]; omega
  have hL : (C z * r ^ 3 + C z * r ^ 2 + r + C z * X - C z).coeff N =
      z * r.leadingCoeff ^ 3 := by
    simp [coeff_add, coeff_sub, hcoeff_r3, hcoeff_r2, hcoeff_r, hcoeff_lin, hcoeff_c]
  have hR : (X ^ 3 : Polynomial R).coeff N = 0 := by
    apply coeff_eq_zero_of_natDegree_lt; rw [natDegree_X_pow]; omega
  have hcongr := congrArg (coeff · N) hrel
  rw [hL, hR] at hcongr
  exact (mul_ne_zero hz (pow_ne_zero 3 (leadingCoeff_ne_zero.mpr hrz))) hcongr

/-! ## Binomial coefficient calculus for linear candidates -/

public theorem factor_lin {R : Type*} [Field R] (a b : R) (ha : a ≠ 0) :
    C a * X + C b = C a * (X + C (a⁻¹ * b)) := by
  calc
    C a * X + C b = C a * X + C a * C (a⁻¹ * b) := by
      congr 1; rw [← map_mul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    _ = C a * (X + C (a⁻¹ * b)) := by rw [mul_add]

public theorem cube_coeff_3 {R : Type*} [Field R] (a b : R) (ha : a ≠ 0) :
    ((C a * X + C b : Polynomial R) ^ 3).coeff 3 = a ^ 3 := by
  rw [factor_lin a b ha, mul_pow, ← map_pow, coeff_C_mul, coeff_X_add_C_pow]
  simp [Nat.choose_self]

public theorem cube_coeff_2 {R : Type*} [Field R] (a b : R) (ha : a ≠ 0) :
    ((C a * X + C b : Polynomial R) ^ 3).coeff 2 = 3 * a ^ 2 * b := by
  rw [factor_lin a b ha, mul_pow, ← map_pow, coeff_C_mul, coeff_X_add_C_pow]
  have hc : (3 : ℕ).choose 2 = 3 := by decide
  rw [hc, Nat.cast_ofNat, show (3 - 2 = 1) from rfl, pow_one]
  field_simp [mul_assoc, mul_comm, mul_left_comm]

public theorem cube_coeff_1 {R : Type*} [Field R] (a b : R) (ha : a ≠ 0) :
    ((C a * X + C b : Polynomial R) ^ 3).coeff 1 = 3 * a * b ^ 2 := by
  rw [factor_lin a b ha, mul_pow, ← map_pow, coeff_C_mul, coeff_X_add_C_pow]
  have hc : (3 : ℕ).choose 1 = 3 := by decide
  rw [hc, Nat.cast_ofNat, show (3 - 1 = 2) from rfl]
  field_simp [mul_assoc, mul_comm, mul_left_comm]

public theorem cube_coeff_0 {R : Type*} [Field R] (a b : R) (ha : a ≠ 0) :
    ((C a * X + C b : Polynomial R) ^ 3).coeff 0 = b ^ 3 := by
  rw [factor_lin a b ha, mul_pow, ← map_pow, coeff_C_mul, coeff_X_add_C_pow]
  have hc : (3 : ℕ).choose 0 = 1 := by decide
  rw [hc, Nat.cast_one, mul_one, show (3 - 0 = 3) from rfl]
  field_simp [mul_assoc, mul_comm, mul_left_comm]

public theorem sq_coeff_2 {R : Type*} [Field R] (a b : R) (ha : a ≠ 0) :
    ((C a * X + C b : Polynomial R) ^ 2).coeff 2 = a ^ 2 := by
  rw [factor_lin a b ha, mul_pow, ← map_pow, coeff_C_mul, coeff_X_add_C_pow]
  simp [Nat.choose_self]

public theorem sq_coeff_1 {R : Type*} [Field R] (a b : R) (ha : a ≠ 0) :
    ((C a * X + C b : Polynomial R) ^ 2).coeff 1 = 2 * a * b := by
  rw [factor_lin a b ha, mul_pow, ← map_pow, coeff_C_mul, coeff_X_add_C_pow]
  have hc : (2 : ℕ).choose 1 = 2 := by decide
  rw [hc, Nat.cast_ofNat, show (2 - 1 = 1) from rfl, pow_one]
  field_simp [mul_assoc, mul_comm, mul_left_comm]

public theorem sq_coeff_0 {R : Type*} [Field R] (a b : R) (ha : a ≠ 0) :
    ((C a * X + C b : Polynomial R) ^ 2).coeff 0 = b ^ 2 := by
  rw [factor_lin a b ha, mul_pow, ← map_pow, coeff_C_mul, coeff_X_add_C_pow]
  have hc : (2 : ℕ).choose 0 = 1 := by decide
  rw [hc, Nat.cast_one, mul_one, show (2 - 0 = 2) from rfl]
  field_simp [mul_assoc, mul_comm, mul_left_comm]

public theorem sq_coeff_3 {R : Type*} [Field R] (a b : R) :
    ((C a * X + C b : Polynomial R) ^ 2).coeff 3 = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hle : (C a * X + C b : Polynomial R).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans ?_
    simp only [natDegree_C]
    exact max_le ((natDegree_C_mul_le _ _).trans (by simp [natDegree_X])) (by norm_num)
  exact lt_of_le_of_lt natDegree_pow_le (by omega)

/-! ## Numerical identities for the degree-1 case -/

public theorem rat_id_neg {R : Type*} [Field R] [CharZero R] :
    ((1 : R) / 3) * (-((27 : R) / 25)) = -((9 : R) / 25) := by
  have h : ((1 : R) / 3) * ((27 : R) / 25) = (9 : R) / 25 := by
    field_simp
    norm_cast
  linear_combination -h

/-- From the linear-term equation with `b = -1/3` and `z = -9/25`, one has `a = 9/28`. -/
public theorem a_eq_nine_over_twenty_eight {R : Type*} [Field R] [CharZero R] (a : R)
    (hX1 : (-((9 : R) / 25)) * (3 * a * (-((1 : R) / 3)) ^ 2) +
        (-((9 : R) / 25)) * (2 * a * (-((1 : R) / 3))) + a + (-((9 : R) / 25)) = 0) :
    a = (9 : R) / 28 := by
  ring_nf at hX1
  field_simp at hX1
  have := congrArg (fun t : R => (25 : R) * t) hX1
  ring_nf at this
  have h700 : a * 700 = 225 := by linear_combination this
  have ha' : a = (225 : R) / 700 := by
    have : (700 : R) ≠ 0 := by exact_mod_cast (by norm_num : (700 : ℚ) ≠ 0)
    field_simp
    exact h700
  rw [ha']
  have h700ne : (700 : R) ≠ 0 := by exact_mod_cast (by norm_num : (700 : ℚ) ≠ 0)
  have h28ne : (28 : R) ≠ 0 := by exact_mod_cast (by norm_num : (28 : ℚ) ≠ 0)
  refine (div_eq_div_iff h700ne h28ne).2 ?_
  exact_mod_cast (by decide : (225 : ℕ) * 28 = 700 * 9)

/-! ## No constant roots -/

/-- Helper: coefficient of `C z * X`. -/
private theorem coeff_C_mul_X {R : Type*} [Semiring R] (z : R) (n : ℕ) :
    (C z * X : Polynomial R).coeff n = if n = 1 then z else 0 := by
  rw [coeff_C_mul, coeff_X, mul_ite, mul_one, mul_zero]
  split_ifs with h h' h' <;> first | rfl | omega

/-- Helper: coefficient of `C z`. -/
private theorem coeff_C_const {R : Type*} [Semiring R] (z : R) (n : ℕ) :
    (C z : Polynomial R).coeff n = if n = 0 then z else 0 := by
  simp [coeff_C]

/-- The integral cubic relation admits no constant (degree-0) solution. -/
public theorem monicCubicY_no_root_natDegree_eq_zero {R : Type*} [Field R]
    {r : Polynomial R} {z : R} (_hz : z ≠ 0)
    (hrel : C z * r ^ 3 + C z * r ^ 2 + r + C z * X - C z = X ^ 3)
    (hd : r.natDegree = 0) : False := by
  -- With `r` constant, the degree-3 coefficient of the LHS is 0, while RHS is 1.
  have hX3 : (X ^ 3 : Polynomial R).coeff 3 = (1 : R) := coeff_X_pow_self 3
  have hlt (p : Polynomial R) (hp : p.natDegree = 0) : p.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hr3le : (r ^ 3).natDegree = 0 := by
    rw [natDegree_pow, hd, mul_zero]
  have hr2le : (r ^ 2).natDegree = 0 := by
    rw [natDegree_pow, hd, mul_zero]
  have hCX3 : (C z * X : Polynomial R).coeff 3 = 0 := by
    rw [coeff_C_mul_X]; simp
  have hCz3 : (C z : Polynomial R).coeff 3 = 0 := by
    rw [coeff_C_const]; simp
  have hL3 : (C z * r ^ 3 + C z * r ^ 2 + r + C z * X - C z).coeff 3 = 0 := by
    simp only [coeff_add, coeff_sub, coeff_C_mul, hlt (r ^ 3) hr3le, hlt (r ^ 2) hr2le,
      hlt r hd, hCX3, hCz3, mul_zero, add_zero, sub_zero]
  have hcongr := congrArg (coeff · 3) hrel
  rw [hL3, hX3] at hcongr
  exact one_ne_zero hcongr.symm

/-! ## No linear roots (degree-1 contradiction) -/

/-- Degree-1 linear candidate forces specific coefficients, which are inconsistent. -/
private theorem monicCubicY_no_root_lin {R : Type*} [Field R] [CharZero R]
    (a b z : R) (ha : a ≠ 0) (hz : z ≠ 0)
    (hrel : C z * (C a * X + C b) ^ 3 + C z * (C a * X + C b) ^ 2 + (C a * X + C b) +
      C z * X - C z = X ^ 3) : False := by
  set lin : Polynomial R := C a * X + C b
  have hnd : lin.natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans ?_
    simp only [natDegree_C]
    exact max_le ((natDegree_C_mul_le _ _).trans (by simp [natDegree_X])) (by norm_num)
  have hlin_coeff_ge_two (n : ℕ) (hn : 2 ≤ n) : lin.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hnd hn)
  have hLHS (n : ℕ) :
      (C z * lin ^ 3 + C z * lin ^ 2 + lin + C z * X - C z).coeff n =
        z * (lin ^ 3).coeff n + z * (lin ^ 2).coeff n + lin.coeff n +
          (C z * X).coeff n - (C z).coeff n := by
    simp [coeff_add, coeff_sub, coeff_C_mul]
  -- === coeff 3: z a³ = 1 ===
  have h3 : z * a ^ 3 = 1 := by
    have h := congrArg (coeff · 3) hrel
    have hCX : (C z * X : Polynomial R).coeff 3 = 0 := by rw [coeff_C_mul_X]; simp
    have hCz : (C z : Polynomial R).coeff 3 = 0 := by rw [coeff_C_const]; simp
    have hR : (X ^ 3 : Polynomial R).coeff 3 = 1 := coeff_X_pow_self 3
    rw [hLHS 3, cube_coeff_3 a b ha, sq_coeff_3 a b, hlin_coeff_ge_two 3 (by norm_num),
      hCX, hCz, hR] at h
    -- z * a³ + z * 0 + 0 + 0 - 0 = 1
    linear_combination h
  -- === coeff 2: 3b + 1 = 0 ===
  have hb : b = -((1 : R) / 3) := by
    have h := congrArg (coeff · 2) hrel
    have hCX : (C z * X : Polynomial R).coeff 2 = 0 := by rw [coeff_C_mul_X]; simp
    have hCz : (C z : Polynomial R).coeff 2 = 0 := by rw [coeff_C_const]; simp
    have hR : (X ^ 3 : Polynomial R).coeff 2 = 0 := by
      rw [coeff_X_pow]; simp
    rw [hLHS 2, cube_coeff_2 a b ha, sq_coeff_2 a b ha, hlin_coeff_ge_two 2 (by norm_num),
      hCX, hCz, hR] at h
    -- z*(3 a² b) + z*a² = 0
    have h' : z * a ^ 2 * ((3 : R) * b + 1) = 0 := by convert h using 1; ring
    have h3b : (3 : R) * b + 1 = 0 :=
      (mul_eq_zero.mp h').resolve_left (mul_ne_zero hz (pow_ne_zero 2 ha))
    have h3ne : (3 : R) ≠ 0 := by exact_mod_cast (by norm_num : (3 : ℚ) ≠ 0)
    have : (3 : R) * b = -1 := by linear_combination h3b
    calc
      b = ((3 : R) * b) / 3 := by field_simp [h3ne]
      _ = (-1 : R) / 3 := by rw [this]
      _ = -((1 : R) / 3) := by ring
  -- === coeff 0: z = -9/25 ===
  have hz_val : z = -((9 : R) / 25) := by
    have h := congrArg (coeff · 0) hrel
    have hCX : (C z * X : Polynomial R).coeff 0 = 0 := by rw [coeff_C_mul_X]; simp
    have hCz : (C z : Polynomial R).coeff 0 = z := by rw [coeff_C_const]; simp
    have hR : (X ^ 3 : Polynomial R).coeff 0 = 0 := by rw [coeff_X_pow]; simp
    have hlin0 : lin.coeff 0 = b := by
      simp [lin, coeff_add, coeff_X, coeff_C]
    rw [hLHS 0, cube_coeff_0 a b ha, sq_coeff_0 a b ha, hlin0, hCX, hCz, hR] at h
    -- z*b³ + z*b² + b - z = 0
    rw [hb] at h
    have h' : z * (-((25 : R) / 27)) = (1 : R) / 3 := by
      -- h : z*(-1/3)³ + z*(-1/3)² + (-1/3) - z = 0
      have : z * (-((1 : R) / 27) + (1 : R) / 9 - 1) = (1 : R) / 3 := by
        linear_combination h
      convert this using 2
      field_simp; ring
    have h25ne : (25 : R) ≠ 0 := by exact_mod_cast (by norm_num : (25 : ℚ) ≠ 0)
    have h27ne : (27 : R) ≠ 0 := by exact_mod_cast (by norm_num : (27 : ℚ) ≠ 0)
    have : z = ((1 : R) / 3) * (-((27 : R) / 25)) := by
      have hmul := congrArg (fun t : R => t * (-((27 : R) / 25))) h'
      field_simp [h25ne, h27ne] at hmul ⊢
      linear_combination hmul
    rw [this, rat_id_neg]
  -- === coeff 1: a = 9/28 ===
  have ha_val : a = (9 : R) / 28 := by
    have h := congrArg (coeff · 1) hrel
    have hCX : (C z * X : Polynomial R).coeff 1 = z := by rw [coeff_C_mul_X]; simp
    have hCz : (C z : Polynomial R).coeff 1 = 0 := by rw [coeff_C_const]; simp
    have hR : (X ^ 3 : Polynomial R).coeff 1 = 0 := by rw [coeff_X_pow]; simp
    have hlin1 : lin.coeff 1 = a := by
      simp [lin, coeff_add, coeff_C]
    rw [hLHS 1, cube_coeff_1 a b ha, sq_coeff_1 a b ha, hlin1, hCX, hCz, hR] at h
    -- z*(3 a b²) + z*(2 a b) + a + z - 0 = 0
    rw [hb, hz_val] at h
    have h' : (-((9 : R) / 25)) * (3 * a * (-((1 : R) / 3)) ^ 2) +
        (-((9 : R) / 25)) * (2 * a * (-((1 : R) / 3))) + a + (-((9 : R) / 25)) = 0 := by
      convert h using 1; ring
    exact a_eq_nine_over_twenty_eight a h'
  -- Contradiction with h3
  rw [hz_val, ha_val] at h3
  have hne : (-((9 : R) / 25)) * ((9 : R) / 28) ^ 3 ≠ (1 : R) := by
    intro heq
    have h25ne : (25 : R) ≠ 0 := by exact_mod_cast (by norm_num : (25 : ℚ) ≠ 0)
    have h28ne : (28 : R) ≠ 0 := by exact_mod_cast (by norm_num : (28 : ℚ) ≠ 0)
    -- Multiply heq by 25 * 28³ and simplify both sides by field_simp.
    have hmul :=
      congrArg (fun t : R => t * ((25 : R) * (28 : R) ^ 3)) heq
    -- LHS becomes -9 * 9³, RHS becomes 25 * 28³
    have hL : (-((9 : R) / 25)) * ((9 : R) / 28) ^ 3 * ((25 : R) * (28 : R) ^ 3) =
        -((9 : R) ^ 4) := by
      field_simp [h25ne, h28ne]
      try ring
    -- After clearing denominators: -9^4 = 25 * 28^3
    have hcleared : -((9 : R) ^ 4) = (25 : R) * (28 : R) ^ 3 := by
      calc
        -((9 : R) ^ 4)
            = (-((9 : R) / 25)) * ((9 : R) / 28) ^ 3 * ((25 : R) * (28 : R) ^ 3) := hL.symm
        _ = (1 : R) * ((25 : R) * (28 : R) ^ 3) := by rw [heq]
        _ = (25 : R) * (28 : R) ^ 3 := by ring
    have hnum : (9 : R) ^ 4 = (6561 : R) := by norm_num
    have hden : (25 : R) * (28 : R) ^ 3 = (548800 : R) := by norm_num
    rw [hnum, hden] at hcleared
    exact absurd hcleared
      (by exact_mod_cast (by norm_num : (-(6561 : ℚ) ≠ (548800 : ℚ))))
  exact hne h3

/-- The integral cubic relation admits no degree-1 solution over a characteristic-zero field. -/
public theorem monicCubicY_no_root_natDegree_eq_one {R : Type*} [Field R] [CharZero R]
    {r : Polynomial R} {z : R} (hz : z ≠ 0)
    (hrel : C z * r ^ 3 + C z * r ^ 2 + r + C z * X - C z = X ^ 3)
    (hd : r.natDegree = 1) : False := by
  obtain ⟨a, ha, b, rfl⟩ := natDegree_eq_one.mp hd
  exact monicCubicY_no_root_lin a b z ha hz hrel

/-! ## No polynomial roots; irreducibility -/

/-- The monic cubic has no roots in `R[X]`. -/
public theorem monicCubicY_no_root {R : Type*} [Field R] [Algebra KQ R] [CharZero R]
    (hz : param R ≠ 0) (r : Polynomial R) : ¬ (monicCubicY R).IsRoot r := by
  intro hr
  have hrel := monicCubicY_root_integral hz hr
  match hdeg : r.natDegree with
  | 0 => exact monicCubicY_no_root_natDegree_eq_zero hz hrel hdeg
  | 1 => exact monicCubicY_no_root_natDegree_eq_one hz hrel hdeg
  | n + 2 =>
    exact monicCubicY_no_root_natDegree_ge_two hz hrel (by omega : 2 ≤ r.natDegree)

/-- The monic cubic is irreducible over `R[X]`. -/
public theorem monicCubicY_irreducible {R : Type*} [Field R] [Algebra KQ R] [CharZero R]
    (hz : param R ≠ 0) : Irreducible (monicCubicY R) := by
  have hmon := monicCubicY_monic R
  have hdeg : (monicCubicY R).natDegree = 3 := monicCubicY_natDegree R
  rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by omega : 2 ≤ (monicCubicY R).natDegree)
    (by omega : (monicCubicY R).natDegree ≤ 3)]
  refine Multiset.eq_zero_of_forall_notMem ?_
  intro r hr
  have hne : monicCubicY R ≠ 0 := hmon.ne_zero
  have : (monicCubicY R).IsRoot r := (mem_roots hne).mp hr
  exact monicCubicY_no_root hz r this

public theorem monicCubicY_irreducible_KQ : Irreducible (monicCubicY KQ) :=
  monicCubicY_irreducible param_KQ_ne_zero

public theorem monicCubicY_irreducible_algClosure :
    Irreducible (monicCubicY (AlgebraicClosure KQ)) := by
  haveI : CharZero (AlgebraicClosure KQ) :=
    Algebra.charZero_of_charZero (R := KQ) (A := AlgebraicClosure KQ)
  exact monicCubicY_irreducible param_algClosure_ne_zero

/-! ## Discriminant nonvanishing (the discriminant octic `q₈`) -/

public theorem q8_ne_zero : Cert.q8 ≠ 0 := by
  intro h
  have := congrArg leadingCoeff h
  rw [Cert.q8_values.2.1, leadingCoeff_zero] at this
  exact absurd this (by norm_num)

/-! ## Affine coordinate ring and function field -/

/-- Affine coordinate ring of the monic model over `R`: `R[x][y] / (monicCubicY R)`. -/
public noncomputable abbrev affineCoordRing (R : Type*) [Field R] [Algebra KQ R] : Type _ :=
  AdjoinRoot (monicCubicY R)

public theorem monicCubicY_prime {R : Type*} [Field R] [Algebra KQ R] [CharZero R]
    (hz : param R ≠ 0) : Prime (monicCubicY R) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (monicCubicY_irreducible hz)

public theorem isDomain_affineCoordRing {R : Type*} [Field R] [Algebra KQ R] [CharZero R]
    (hz : param R ≠ 0) : IsDomain (affineCoordRing R) :=
  AdjoinRoot.isDomain_of_prime (monicCubicY_prime hz)

public theorem isDomain_affineCoordRing_KQ : IsDomain (affineCoordRing KQ) :=
  isDomain_affineCoordRing param_KQ_ne_zero

public theorem isDomain_affineCoordRing_algClosure :
    IsDomain (affineCoordRing (AlgebraicClosure KQ)) := by
  haveI : CharZero (AlgebraicClosure KQ) :=
    Algebra.charZero_of_charZero (R := KQ) (A := AlgebraicClosure KQ)
  exact isDomain_affineCoordRing param_algClosure_ne_zero

/-- Unconditional domain structure on the geometric affine coordinate ring
`AdjoinRoot (monicCubicY (AlgebraicClosure KQ))`. This is geometric integrality of the affine
model. -/
public theorem isDomain_geometric_affineCoordRing :
    IsDomain (affineCoordRing (AlgebraicClosure KQ)) :=
  isDomain_affineCoordRing_algClosure

/-- Function field of the affine model over `KQ`: fraction field of the coordinate ring. -/
public noncomputable abbrev curveFieldKQ : Type _ :=
  FractionRing (affineCoordRing KQ)

/-- Function field of the geometric affine model. -/
public noncomputable abbrev curveFieldAlgClosure : Type _ :=
  FractionRing (affineCoordRing (AlgebraicClosure KQ))

noncomputable instance : IsDomain (affineCoordRing KQ) := isDomain_affineCoordRing_KQ

noncomputable instance : IsDomain (affineCoordRing (AlgebraicClosure KQ)) :=
  isDomain_affineCoordRing_algClosure

noncomputable instance : Field curveFieldKQ :=
  FractionRing.field (A := affineCoordRing KQ)

noncomputable instance : Field curveFieldAlgClosure :=
  FractionRing.field (A := affineCoordRing (AlgebraicClosure KQ))

/-! ## Route A interface (tensor product is a field) -/

/-- Packaging of `TorsorDescent.isField_tensorProduct_of_isDomain_of_isAlgebraic` when the
algebraic side is the left factor (finite/algebraic extension of `KQ`). -/
public theorem isField_of_isDomain_of_isAlgebraic_base
    (L Kp : Type*) [Field L] [Field Kp]
    [Algebra KQ L] [Algebra KQ Kp] [Algebra.IsAlgebraic KQ L]
    [IsDomain (L ⊗[KQ] Kp)] :
    IsField (L ⊗[KQ] Kp) :=
  isField_tensorProduct_of_isDomain_of_isAlgebraic KQ L Kp

/-- Same packaging with the algebraic side on the right: for geometric base change along
`KQ → AlgebraicClosure KQ`. -/
public theorem isField_tensorProduct_of_isDomain_of_isAlgebraic_right
    (L Kp : Type*) [Field L] [Field Kp]
    [Algebra KQ L] [Algebra KQ Kp] [Algebra.IsAlgebraic KQ Kp]
    [IsDomain (L ⊗[KQ] Kp)] :
    IsField (L ⊗[KQ] Kp) :=
  Algebra.TensorProduct.isField_of_isAlgebraic KQ L Kp (Or.inr ‹_›)

/-- Geometric base change of the function field is a field once the tensor is known to be a
domain. Geometric irreducibility of the monic model (`monicCubicY_irreducible_algClosure`) is the
source of that domain property for the affine coordinate ring; lifting it to fraction fields is
the residual packaging step recorded by the `IsDomain` hypothesis here. -/
public theorem isField_curveField_tensor_algClosure
    [IsDomain (curveFieldKQ ⊗[KQ] AlgebraicClosure KQ)] :
    IsField (curveFieldKQ ⊗[KQ] AlgebraicClosure KQ) :=
  isField_tensorProduct_of_isDomain_of_isAlgebraic_right
    curveFieldKQ (AlgebraicClosure KQ)

/-! ## Axiom audit -/

#print axioms monicCubicY_monic
#print axioms monicCubicY_natDegree
#print axioms monicCubicY_root_integral
#print axioms monicCubicY_no_root_natDegree_ge_two
#print axioms monicCubicY_no_root_natDegree_eq_zero
#print axioms monicCubicY_no_root_natDegree_eq_one
#print axioms monicCubicY_no_root
#print axioms monicCubicY_irreducible
#print axioms monicCubicY_irreducible_KQ
#print axioms monicCubicY_irreducible_algClosure
#print axioms a_eq_nine_over_twenty_eight
#print axioms q8_ne_zero
#print axioms isDomain_affineCoordRing_KQ
#print axioms isDomain_geometric_affineCoordRing
#print axioms isField_of_isDomain_of_isAlgebraic_base
#print axioms isField_curveField_tensor_algClosure

end ExplicitUnirational
