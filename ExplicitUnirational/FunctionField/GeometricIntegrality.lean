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
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Geometric integrality of the generic plane cubic (Torsor gap 1)

Note §3.1–3.2: the generic member of the rational pencil, dehomogenized at `Z = 1`, is the
affine plane cubic

```
  G = (y − x³) + z · (x + y³ + y² − 1) ∈ ℚ(z)[x, y].
```

## Status (honest)

**Delivered and compiling:**

1. **Definitions** of the pencil parameter, monic cubic in `y` over `R[x]`, and non-monic form.
2. **Monicity and degree** of `monicCubicY` (monic of degree 3).
3. **Integral root form**: a monic-cubic root `r ∈ R[X]` yields
   `z r³ + z r² + r + z X − z = X³`.
4. **No degree-≥2 roots** of that integral equation (leading-coefficient comparison).
5. **Binomial coefficient calculus** for linear candidates `(aX+b)ⁿ` via `coeff_X_add_C_pow`.
6. **Numerical identities** for the degree-1 case (`rat_id_neg`, `a_from`).
7. **Discriminant certificate**: `q₈ ≠ 0` as a polynomial (note (3.14)).
8. **Route A interface packaging**: re-export of
   `isField_tensorProduct_of_isDomain_of_isAlgebraic` specialized to a placeholder function-field
   type class shape (see `isField_of_isDomain_of_isAlgebraic_base`).

**Not yet closed in this module (no `sorry` — omitted rather than stubbed):**

* Full monic-cubic irreducibility (needs the degree-1 root contradiction assembled end-to-end
  without residual `field_simp`/`ring` goal-management failures under the module build).
* `IsDomain` on `AdjoinRoot affineG_polyY` and the function-field tensor
  `curveField ⊗[KQ] AlgebraicClosure KQ` (blocked on irreducibility).
* Relative algebraic closure `algebraicClosure KQ curveField = ⊥`.

The coefficient calculus and monicity infrastructure below is the computational heart of the
irreducibility argument; closing the last assembly step is mechanical follow-up.
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

/-! ## Discriminant nonvanishing (note (3.14)) -/

public theorem q8_ne_zero : Cert.q8 ≠ 0 := by
  intro h
  have := congrArg leadingCoeff h
  rw [Cert.q8_values.2.1, leadingCoeff_zero] at this
  exact absurd this (by norm_num)

/-! ## Route A interface (shape only; domain hypothesis retained) -/

/-- Packaging of `TorsorDescent.isField_tensorProduct_of_isDomain_of_isAlgebraic` for a
function field of the generic cubic. The domain hypothesis is the remaining packaging obligation
once monic-cubic irreducibility is fully assembled. -/
public theorem isField_of_isDomain_of_isAlgebraic_base
    (L Kp : Type*) [Field L] [Field Kp]
    [Algebra KQ L] [Algebra KQ Kp] [Algebra.IsAlgebraic KQ L]
    [IsDomain (L ⊗[KQ] Kp)] :
    IsField (L ⊗[KQ] Kp) :=
  isField_tensorProduct_of_isDomain_of_isAlgebraic KQ L Kp

/-! ## Axiom audit -/

#print axioms monicCubicY_monic
#print axioms monicCubicY_natDegree
#print axioms monicCubicY_root_integral
#print axioms monicCubicY_no_root_natDegree_ge_two
#print axioms cube_coeff_3
#print axioms a_eq_nine_over_twenty_eight
#print axioms q8_ne_zero
#print axioms isField_of_isDomain_of_isAlgebraic_base

end ExplicitUnirational
