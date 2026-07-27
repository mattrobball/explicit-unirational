/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Discriminant factorizations (note §3.2 and §5.3)

Pure polynomial identities over `ℚ`:

* `(3.10)`–`(3.15)`: the quartic `P4`, octic `Q8`, Weierstrass discriminant factorization
  `Δ = -u² v² Q8`, and the dehomogenized octic `q8` with the three numeric values used to
  place its roots;
* `(5.7)`–`(5.8)`: the analogous factorization `4A³ + 27B² = 27 u² v² Q₊ Q₋` over `ℚ(t)`,
  encoded in `MvPolynomial (Fin 3) ℚ` with variables `(u,v,t) = (X 0, X 1, X 2)`.

All identities are characteristic-free and close by `ring` (after clearing the rational
scalar in `B` for (3.13)).

**Notation caveat.** With `open MvPolynomial`, the bare token `X` is the multivariate
indeterminate, so the univariate type must be written `Polynomial ℚ` rather than `ℚ[X]`
(the latter is misread as GetElem).
-/

noncomputable section

open MvPolynomial

namespace ExplicitUnirational.Cert

/-! ## Arithmetic surface: `P4`, `Q8`, and the discriminant (3.10)–(3.13) -/

/-- The bihomogeneous quartic `P₄(u,v)` of note eq. (3.10).
Variables: `u = X 0`, `v = X 1`. -/
public noncomputable def P4 : MvPolynomial (Fin 2) ℚ :=
  4 * (X 1) ^ 4 - 23 * X 0 * (X 1) ^ 3 - 18 * (X 0) ^ 2 * (X 1) ^ 2
    + (X 0) ^ 3 * X 1 - 4 * (X 0) ^ 4

/-- The bihomogeneous octic `Q₈(u,v)` of note eq. (3.11).
Variables: `u = X 0`, `v = X 1`. -/
public noncomputable def Q8 : MvPolynomial (Fin 2) ℚ :=
  64 * X 0 * (X 1) ^ 4 * (3 * X 0 - X 1) ^ 3 + 27 * P4 ^ 2

/-- Eq. (3.13): the discriminant of the Weierstrass model over `ℚ` factors as `-u² v² Q₈`.

With `A = u v² (3u - v)` and `W = u v P₄` as in (3.12) (so `B = W / 4`), one has
`-16 (4 A³ + 27 B²) = -64 A³ - 27 W²`. We state the integral form so every coefficient is
an integer and the identity is plain `ring` over `ℚ` (no scalar `•` or division). -/
public theorem discriminant_factorization :
    -64 * (X 0 * (X 1) ^ 2 * (3 * X 0 - X 1)) ^ 3
      - 27 * (X 0 * X 1 * P4) ^ 2
      = -(X 0) ^ 2 * (X 1) ^ 2 * Q8 := by
  unfold Q8 P4
  ring

/-! ## Dehomogenized octic `q₈` (3.14)–(3.15) -/

/-- The dehomogenized octic `q₈(z)` of note eq. (3.14), given by its expanded form.
See `q8_dehomogenize` for the identification `q₈(z) = Q₈(1, z)`. -/
public noncomputable def q8 : Polynomial ℚ :=
  432 * Polynomial.X ^ 8 - 5032 * Polynomial.X ^ 7 + 10971 * Polynomial.X ^ 6
    + 20844 * Polynomial.X ^ 5 + 8370 * Polynomial.X ^ 4 + 3996 * Polynomial.X ^ 3
    + 3915 * Polynomial.X ^ 2 - 216 * Polynomial.X + 432

/-- Eq. (3.14): the expanded form of the dehomogenization of `Q8` at `u = 1`. -/
public theorem q8_eq :
    q8 = 432 * Polynomial.X ^ 8 - 5032 * Polynomial.X ^ 7 + 10971 * Polynomial.X ^ 6
      + 20844 * Polynomial.X ^ 5 + 8370 * Polynomial.X ^ 4 + 3996 * Polynomial.X ^ 3
      + 3915 * Polynomial.X ^ 2 - 216 * Polynomial.X + 432 := by
  rfl

/-- `q₈(z) = Q₈(1, z)`: dehomogenization of `Q8` at `u = 1`. -/
public theorem q8_dehomogenize :
    eval₂Hom (R := ℚ) (σ := Fin 2) (S₁ := Polynomial ℚ) Polynomial.C
      ![(1 : Polynomial ℚ), Polynomial.X] Q8 = q8 := by
  unfold q8 Q8 P4
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Eq. (3.15): the three numeric values used to place the roots of `Q8`. -/
public theorem q8_values :
    q8.eval 0 = 432 ∧ q8.leadingCoeff = 432 ∧ q8.eval 3 = 5713200 := by
  rw [q8_eq]
  refine ⟨?eval0, ?lc, ?eval3⟩
  case eval0 =>
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    norm_num
  case lc =>
    have hdeg :
        Polynomial.natDegree
          (432 * Polynomial.X ^ 8 - 5032 * Polynomial.X ^ 7 + 10971 * Polynomial.X ^ 6
            + 20844 * Polynomial.X ^ 5 + 8370 * Polynomial.X ^ 4 + 3996 * Polynomial.X ^ 3
            + 3915 * Polynomial.X ^ 2 - 216 * Polynomial.X + 432 : Polynomial ℚ) = 8 := by
      compute_degree!
    rw [Polynomial.leadingCoeff, hdeg]
    compute_degree!
  case eval3 =>
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    norm_num

/-! ## Geometric surface over `ℂ(t)`: `Q±` and the factorization (5.7)–(5.8)

Variables are `(u, v, t) = (X 0, X 1, X 2)` in `MvPolynomial (Fin 3) ℚ`.
-/

/-- `Q₊(u,v)` of note eq. (5.8), in variables `(u,v,t) = (X 0, X 1, X 2)`. -/
public noncomputable def Qplus : MvPolynomial (Fin 3) ℚ :=
  (X 0) ^ 4 + (X 1) ^ 4 + 27 * (X 2) ^ 2 * X 0 * (X 1) ^ 3 + 2 * (X 0) ^ 2 * (X 1) ^ 2

/-- `Q₋(u,v)` of note eq. (5.8), in variables `(u,v,t) = (X 0, X 1, X 2)`. -/
public noncomputable def Qminus : MvPolynomial (Fin 3) ℚ :=
  (X 0) ^ 4 + (X 1) ^ 4 + 27 * (X 2) ^ 2 * X 0 * (X 1) ^ 3 - 2 * (X 0) ^ 2 * (X 1) ^ 2

/-- Eq. (5.7): with `A = -3 u² v²` and `B = -u⁵ v - u v⁵ - 27 t² u² v⁴`,
`4A³ + 27B² = 27 u² v² Q₊ Q₋`. -/
public theorem discriminant_factorization_t :
    4 * (-3 * (X 0) ^ 2 * (X 1) ^ 2) ^ 3
      + 27
        * (-(X 0) ^ 5 * X 1 - X 0 * (X 1) ^ 5
            - 27 * (X 2) ^ 2 * (X 0) ^ 2 * (X 1) ^ 4) ^ 2
      = 27 * (X 0) ^ 2 * (X 1) ^ 2 * Qplus * Qminus := by
  unfold Qplus Qminus
  ring

end ExplicitUnirational.Cert
