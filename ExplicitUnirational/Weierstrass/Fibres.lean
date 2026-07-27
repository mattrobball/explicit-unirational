/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Irreducible singular fibres (note Prop. 3.3, §4.1, Prop. 5.3)

## Scope — deliberate replacement of Tate / Kodaira

The note classifies singular fibres of the three elliptic surfaces by Tate's algorithm:
two of type II and eight of type I₁ over `ℚ` (Prop. 3.3); three of type II and six of
type I₁ after reduction mod 5 (§4.1); two of type II and eight of type I₁ for the
`C(t)` family (Prop. 5.3). **This module does not formalize Tate's algorithm**, nor the
Kodaira symbols themselves.

What the downstream argument actually consumes — and the only consequence of the fibre
classification used anywhere in the paper — is the Shioda–Tate hypothesis (note §4.2,
§5.4):

> every geometric singular fibre is irreducible.

Kodaira types II (cuspidal cubic) and I₁ (nodal cubic) each have a single irreducible
component. That is exactly the content needed for
`rk MW = rk NS − 2 − ∑ (m_v − 1)` to collapse to `rk NS − 2` when every `m_v = 1`.

We prove the needed fact directly: a short Weierstrass cubic
`y² = x³ + A x + B` over an integral domain is cut out by an **irreducible** bivariate
polynomial, whether or not `Δ = 0`. Mathlib already records this as
`WeierstrassCurve.Affine.irreducible_polynomial`; we re-export it for the short form,
emphasize the singular case, and apply it to the three families of the note.

The discriminant factorizations of note (3.13) and (5.7) are re-proved here as ring
identities on the specialized coefficients (matching `Cert/Discriminant`), so that the
singular locus of each family is explicit.

## Deliverables

1. **Criterion.** Short Weierstrass polynomials are irreducible over any integral domain
   (including when `Δ = 0`: nodal or cuspidal). After base change to any field extension
   the same holds, so geometric fibres are irreducible.
2. **Arithmetic family over `ℚ`.** The model (3.12) at every base point — in particular
   at every singular fibre — is geometrically irreducible.
3. **Reduction mod 5 and the `C(t)` family.** The same statement for the specialized
   coefficients of §4.1 and for (5.6)–(5.8).
-/

noncomputable section

open Polynomial WeierstrassCurve
open scoped Polynomial.Bivariate

namespace ExplicitUnirational.Weierstrass

/-! ## Short Weierstrass models -/

/-- The short Weierstrass curve `y² = x³ + A x + B`. -/
public def shortWeierstrass {R : Type*} [CommRing R] (A B : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, A, B⟩

public instance shortWeierstrass_isShortNF {R : Type*} [CommRing R] (A B : R) :
    (shortWeierstrass A B).IsShortNF where
  a₁ := by unfold shortWeierstrass; rfl
  a₂ := by unfold shortWeierstrass; rfl
  a₃ := by unfold shortWeierstrass; rfl

/-- Note's short-form `c₄ = −48 A`. -/
public theorem shortWeierstrass_c₄ {R : Type*} [CommRing R] (A B : R) :
    (shortWeierstrass A B).c₄ = -48 * A := by
  rw [(shortWeierstrass A B).c₄_of_isShortNF]
  unfold shortWeierstrass
  rfl

/-- Note's short-form `c₆ = −864 B`. -/
public theorem shortWeierstrass_c₆ {R : Type*} [CommRing R] (A B : R) :
    (shortWeierstrass A B).c₆ = -864 * B := by
  rw [(shortWeierstrass A B).c₆_of_isShortNF]
  unfold shortWeierstrass
  rfl

/-- Note's short-form discriminant `Δ = −16 (4 A³ + 27 B²)`. -/
public theorem shortWeierstrass_Δ {R : Type*} [CommRing R] (A B : R) :
    (shortWeierstrass A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  rw [(shortWeierstrass A B).Δ_of_isShortNF]
  unfold shortWeierstrass
  rfl

/-! ## Criterion: singular Weierstrass cubics remain irreducible -/

/-- **Core criterion.** The short Weierstrass polynomial
`Y² − (X³ + A X + B)` is irreducible in `R[X][Y]` over any integral domain `R`.

This holds with no hypothesis on `Δ`: in particular it covers the singular cases
`Δ = 0` (nodal cubic when `c₄ ≠ 0`, cuspidal when `c₄ = 0`), which is what
"Kodaira type II or I₁ ⇒ irreducible fibre" amounts to for the Shioda–Tate step. -/
public theorem irreducible_shortWeierstrass {R : Type*} [CommRing R] [IsDomain R] (A B : R) :
    Irreducible (shortWeierstrass A B).toAffine.polynomial :=
  Affine.irreducible_polynomial

/-- The same criterion stated under the singularity hypothesis `Δ = 0`, matching the
wording "singular fibre is irreducible". -/
public theorem irreducible_shortWeierstrass_of_Δ_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    (A B : R) (_hΔ : (shortWeierstrass A B).Δ = 0) :
    Irreducible (shortWeierstrass A B).toAffine.polynomial :=
  irreducible_shortWeierstrass A B

/-- Geometric fibres: after base change to any field extension (in particular an
algebraic closure) the specialized polynomial remains irreducible. -/
public theorem geometrically_irreducible_shortWeierstrass {K : Type*} [Field K] (A B : K)
    (L : Type*) [Field L] [Algebra K L] :
    Irreducible ((shortWeierstrass A B).baseChange L).toAffine.polynomial :=
  Affine.irreducible_polynomial

/-- Under `Δ = 0`, the geometric fibre is still irreducible. -/
public theorem geometrically_irreducible_shortWeierstrass_of_Δ_eq_zero {K : Type*} [Field K]
    (A B : K) (_hΔ : (shortWeierstrass A B).Δ = 0) (L : Type*) [Field L] [Algebra K L] :
    Irreducible ((shortWeierstrass A B).baseChange L).toAffine.polynomial :=
  geometrically_irreducible_shortWeierstrass A B L

/-! ## Cuspidal character at vanishing `A`, `B`

At `u = 0` or `v = 0` the note finds type II: the fibre is the cuspidal cubic `y² = x³`.
We record the algebraic content: `A = B = 0` forces `c₄ = 0` and `Δ = 0`, and the
equation is still irreducible. -/

public theorem shortWeierstrass_cusp_Δ {R : Type*} [CommRing R] :
    (shortWeierstrass (0 : R) 0).Δ = 0 := by
  rw [shortWeierstrass_Δ]
  ring

public theorem shortWeierstrass_cusp_c₄ {R : Type*} [CommRing R] :
    (shortWeierstrass (0 : R) 0).c₄ = 0 := by
  rw [shortWeierstrass_c₄]
  ring

/-- The cuspidal cubic is irreducible (type II ⇒ irreducible component). -/
public theorem irreducible_cuspidal {R : Type*} [CommRing R] [IsDomain R] :
    Irreducible (shortWeierstrass (0 : R) 0).toAffine.polynomial :=
  irreducible_shortWeierstrass 0 0

/-! ## Arithmetic family (note (3.12)–(3.13))

`A = u v² (3u − v)`, `B = (1/4) u v P₄(u,v)`. -/

/-- The bihomogeneous quartic `P₄(u,v)` of note (3.10), evaluated at ring elements. -/
public def P4_eval {R : Type*} [CommRing R] (u v : R) : R :=
  4 * v ^ 4 - 23 * u * v ^ 3 - 18 * u ^ 2 * v ^ 2 + u ^ 3 * v - 4 * u ^ 4

/-- The bihomogeneous octic `Q₈(u,v)` of note (3.11), evaluated at ring elements. -/
public def Q8_eval {R : Type*} [CommRing R] (u v : R) : R :=
  64 * u * v ^ 4 * (3 * u - v) ^ 3 + 27 * (P4_eval u v) ^ 2

/-- Coefficient `A` of the arithmetic Weierstrass family (3.12). -/
public def A_arith {R : Type*} [CommRing R] (u v : R) : R :=
  u * v ^ 2 * (3 * u - v)

/-- Coefficient `B` of the arithmetic Weierstrass family (3.12). -/
public def B_arith {R : Type*} [Field R] (u v : R) : R :=
  (u * v * P4_eval u v) / 4

/-- Integral form of note (3.13): `-64 A³ − 27 W² = −u² v² Q₈` with `W = u v P₄`. -/
public theorem discriminant_factorization_integral {R : Type*} [CommRing R] (u v : R) :
    -64 * (A_arith u v) ^ 3 - 27 * (u * v * P4_eval u v) ^ 2
      = -u ^ 2 * v ^ 2 * Q8_eval u v := by
  unfold A_arith Q8_eval P4_eval
  ring

/-- Clearing the `/4` in `B`: short-form `Δ` matches the integral expression of (3.13). -/
public theorem shortWeierstrass_Δ_arith_integral {K : Type*} [Field K] (u v : K)
    (h2 : (2 : K) ≠ 0) :
    (shortWeierstrass (A_arith u v) (B_arith u v)).Δ
      = -64 * (A_arith u v) ^ 3 - 27 * (u * v * P4_eval u v) ^ 2 := by
  have h4 : (4 : K) ≠ 0 := by
    intro h
    have e : (4 : K) = 2 * 2 := by norm_num
    rw [e] at h
    exact h2 ((mul_eq_zero.mp h).elim id id)
  rw [shortWeierstrass_Δ, B_arith]
  field_simp [h4]
  ring

/-- Over any field of characteristic not 2, the short-form discriminant of the arithmetic
family is `-u² v² Q₈(u,v)`. -/
public theorem Δ_arith_eq_factor {K : Type*} [Field K] (u v : K) (h2 : (2 : K) ≠ 0) :
    (shortWeierstrass (A_arith u v) (B_arith u v)).Δ
      = -u ^ 2 * v ^ 2 * Q8_eval u v := by
  rw [shortWeierstrass_Δ_arith_integral u v h2, discriminant_factorization_integral]

/-- At `u = 0` the arithmetic fibre is the cuspidal cubic (type II). -/
public theorem A_arith_u_zero {R : Type*} [CommRing R] (v : R) : A_arith (0 : R) v = 0 := by
  simp [A_arith]

public theorem B_arith_u_zero {K : Type*} [Field K] (v : K) : B_arith (0 : K) v = 0 := by
  simp [B_arith, P4_eval]

/-- At `v = 0` the arithmetic fibre is the cuspidal cubic (type II). -/
public theorem A_arith_v_zero {R : Type*} [CommRing R] (u : R) : A_arith u (0 : R) = 0 := by
  simp [A_arith]

public theorem B_arith_v_zero {K : Type*} [Field K] (u : K) : B_arith u (0 : K) = 0 := by
  simp [B_arith, P4_eval]

/-- **Arithmetic family, every fibre.** For any field `K` and any base point `(u,v)`, the
Weierstrass polynomial of the fibre is irreducible. In particular every singular fibre
(those with `Δ = 0`) is irreducible as a plane cubic. -/
public theorem irreducible_arith_fibre {K : Type*} [Field K] (u v : K) :
    Irreducible (shortWeierstrass (A_arith u v) (B_arith u v)).toAffine.polynomial :=
  irreducible_shortWeierstrass _ _

/-- Geometric fibres of the arithmetic family (base change to any extension). -/
public theorem geometrically_irreducible_arith_fibre {K : Type*} [Field K] (u v : K)
    (L : Type*) [Field L] [Algebra K L] :
    Irreducible
      ((shortWeierstrass (A_arith u v) (B_arith u v)).baseChange L).toAffine.polynomial :=
  geometrically_irreducible_shortWeierstrass _ _ L

/-- Singular geometric fibres of the arithmetic family over `ℚ` are irreducible.
This is the Shioda–Tate input of note Prop. 3.3 / §4.2. -/
public theorem singular_arith_fibre_geometrically_irreducible (u v : ℚ)
    (hΔ : (shortWeierstrass (A_arith u v) (B_arith u v)).Δ = 0)
    (L : Type*) [Field L] [Algebra ℚ L] :
    Irreducible
      ((shortWeierstrass (A_arith u v) (B_arith u v)).baseChange L).toAffine.polynomial :=
  geometrically_irreducible_shortWeierstrass_of_Δ_eq_zero _ _ hΔ L

/-! ## Reduction modulo 5 (note §4.1)

All coefficients of the arithmetic family are integral, so the same `A`, `B` formulas
specialize to `F₅`. The six simple roots of `d₆` and the three type-II places
`[0:1]`, `[1:0]`, `[1:3]` yield singular fibres; each remains irreducible as a plane cubic. -/

/-- Primality of `5`, so `ZMod 5` is a field. -/
public instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Arithmetic coefficients reduced to `F₅`. -/
public def A_F5 (u v : ZMod 5) : ZMod 5 := A_arith u v

public def B_F5 (u v : ZMod 5) : ZMod 5 := B_arith u v

/-- Every fibre of the mod-5 Weierstrass family is irreducible (including the three type-II
and six type-I₁ fibres of note §4.1). -/
public theorem irreducible_F5_fibre (u v : ZMod 5) :
    Irreducible (shortWeierstrass (A_F5 u v) (B_F5 u v)).toAffine.polynomial :=
  irreducible_shortWeierstrass _ _

/-- Geometric singular fibres after reduction mod 5 are irreducible. -/
public theorem singular_F5_fibre_geometrically_irreducible (u v : ZMod 5)
    (hΔ : (shortWeierstrass (A_F5 u v) (B_F5 u v)).Δ = 0)
    (L : Type*) [Field L] [Algebra (ZMod 5) L] :
    Irreducible
      ((shortWeierstrass (A_F5 u v) (B_F5 u v)).baseChange L).toAffine.polynomial :=
  geometrically_irreducible_shortWeierstrass_of_Δ_eq_zero _ _ hΔ L

/-- Type-II places of note §4.1: `[0:1]` and `[1:0]` give the cuspidal cubic. -/
public theorem F5_fibre_u_zero_cuspidal (v : ZMod 5) :
    A_F5 0 v = 0 ∧ B_F5 0 v = 0 := by
  constructor
  · simp [A_F5, A_arith]
  · simp [B_F5, B_arith, P4_eval]

public theorem F5_fibre_v_zero_cuspidal (u : ZMod 5) :
    A_F5 u 0 = 0 ∧ B_F5 u 0 = 0 := by
  constructor
  · simp [A_F5, A_arith]
  · simp [B_F5, B_arith, P4_eval]

/-! ## Geometric family over `ℚ(t)` (note (5.6)–(5.8))

`A = −3 u² v²`, `B = −u⁵ v − u v⁵ − 27 t² u² v⁴`. The discriminant factors as
`27 u² v² Q₊ Q₋` (5.7). Every specialized fibre is an irreducible Weierstrass cubic. -/

/-- Coefficient `A` of the `C(t)` Weierstrass family (5.6)/(5.7). -/
public def A_t {R : Type*} [CommRing R] (u v : R) : R :=
  -3 * u ^ 2 * v ^ 2

/-- Coefficient `B` of the `C(t)` Weierstrass family, with parameter `t`. -/
public def B_t {R : Type*} [CommRing R] (u v t : R) : R :=
  -u ^ 5 * v - u * v ^ 5 - 27 * t ^ 2 * u ^ 2 * v ^ 4

/-- `Q₊(u,v)` of note (5.8), evaluated. -/
public def Qplus_eval {R : Type*} [CommRing R] (u v t : R) : R :=
  u ^ 4 + v ^ 4 + 27 * t ^ 2 * u * v ^ 3 + 2 * u ^ 2 * v ^ 2

/-- `Q₋(u,v)` of note (5.8), evaluated. -/
public def Qminus_eval {R : Type*} [CommRing R] (u v t : R) : R :=
  u ^ 4 + v ^ 4 + 27 * t ^ 2 * u * v ^ 3 - 2 * u ^ 2 * v ^ 2

/-- Eq. (5.7) specialized: `4 A³ + 27 B² = 27 u² v² Q₊ Q₋`. -/
public theorem discriminant_factorization_t_eval {R : Type*} [CommRing R] (u v t : R) :
    4 * (A_t u v) ^ 3 + 27 * (B_t u v t) ^ 2
      = 27 * u ^ 2 * v ^ 2 * Qplus_eval u v t * Qminus_eval u v t := by
  unfold A_t B_t Qplus_eval Qminus_eval
  ring

/-- Over any commutative ring, `Δ = -432 u² v² Q₊ Q₋` for the `C(t)` family. -/
public theorem Δ_t_eq_factor {R : Type*} [CommRing R] (u v t : R) :
    (shortWeierstrass (A_t u v) (B_t u v t)).Δ
      = -432 * u ^ 2 * v ^ 2 * Qplus_eval u v t * Qminus_eval u v t := by
  rw [shortWeierstrass_Δ, discriminant_factorization_t_eval]
  ring

/-- At `u = 0` the `C(t)` fibre is cuspidal. -/
public theorem A_t_u_zero {R : Type*} [CommRing R] (v : R) : A_t (0 : R) v = 0 := by
  simp [A_t]

public theorem B_t_u_zero {R : Type*} [CommRing R] (v t : R) : B_t (0 : R) v t = 0 := by
  simp [B_t]

/-- At `v = 0` the `C(t)` fibre is cuspidal. -/
public theorem A_t_v_zero {R : Type*} [CommRing R] (u : R) : A_t u (0 : R) = 0 := by
  simp [A_t]

public theorem B_t_v_zero {R : Type*} [CommRing R] (u t : R) : B_t u (0 : R) t = 0 := by
  simp [B_t]

/-- **`C(t)` family, every fibre.** Irreducible over any field of definition. -/
public theorem irreducible_t_fibre {K : Type*} [Field K] (u v t : K) :
    Irreducible (shortWeierstrass (A_t u v) (B_t u v t)).toAffine.polynomial :=
  irreducible_shortWeierstrass _ _

/-- Geometric fibres of the `C(t)` family. -/
public theorem geometrically_irreducible_t_fibre {K : Type*} [Field K] (u v t : K)
    (L : Type*) [Field L] [Algebra K L] :
    Irreducible
      ((shortWeierstrass (A_t u v) (B_t u v t)).baseChange L).toAffine.polynomial :=
  geometrically_irreducible_shortWeierstrass _ _ L

/-- Singular geometric fibres of the `C(t)` family are irreducible
(note Prop. 5.3 / §5.4). Working over `ℚ(t)` via `RatFunc ℚ`. -/
public theorem singular_t_fibre_geometrically_irreducible
    (u v t : RatFunc ℚ)
    (hΔ : (shortWeierstrass (A_t u v) (B_t u v t)).Δ = 0)
    (L : Type*) [Field L] [Algebra (RatFunc ℚ) L] :
    Irreducible
      ((shortWeierstrass (A_t u v) (B_t u v t)).baseChange L).toAffine.polynomial :=
  geometrically_irreducible_shortWeierstrass_of_Δ_eq_zero _ _ hΔ L

/-- Convenience form over `ℚ` with a fixed rational parameter `t₀`. -/
public theorem singular_t_fibre_geometrically_irreducible_rat
    (u v t₀ : ℚ)
    (hΔ : (shortWeierstrass (A_t u v) (B_t u v t₀)).Δ = 0)
    (L : Type*) [Field L] [Algebra ℚ L] :
    Irreducible
      ((shortWeierstrass (A_t u v) (B_t u v t₀)).baseChange L).toAffine.polynomial :=
  geometrically_irreducible_shortWeierstrass_of_Δ_eq_zero _ _ hΔ L

/-! ## Headline summaries

The three statements consumed by Shioda–Tate in the note. -/

/-- Note Prop. 3.3 (fibre half): every geometric singular fibre of the arithmetic surface
is irreducible. -/
public theorem every_singular_fibre_irreducible_arith :
    ∀ (u v : ℚ), (shortWeierstrass (A_arith u v) (B_arith u v)).Δ = 0 →
      Irreducible (shortWeierstrass (A_arith u v) (B_arith u v)).toAffine.polynomial := by
  intro _ _ h
  exact irreducible_shortWeierstrass_of_Δ_eq_zero _ _ h

/-- Note §4.1 (fibre half): every geometric singular fibre of the mod-5 surface is
irreducible. -/
public theorem every_singular_fibre_irreducible_F5 :
    ∀ (u v : ZMod 5), (shortWeierstrass (A_F5 u v) (B_F5 u v)).Δ = 0 →
      Irreducible (shortWeierstrass (A_F5 u v) (B_F5 u v)).toAffine.polynomial := by
  intro _ _ h
  exact irreducible_shortWeierstrass_of_Δ_eq_zero _ _ h

/-- Note Prop. 5.3 (fibre half): every geometric singular fibre of the `C(t)` surface is
irreducible. -/
public theorem every_singular_fibre_irreducible_t :
    ∀ (u v t : RatFunc ℚ), (shortWeierstrass (A_t u v) (B_t u v t)).Δ = 0 →
      Irreducible (shortWeierstrass (A_t u v) (B_t u v t)).toAffine.polynomial := by
  intro _ _ _ h
  exact irreducible_shortWeierstrass_of_Δ_eq_zero _ _ h

end ExplicitUnirational.Weierstrass

/-! ## Axiom audit for headline theorems -/

#print axioms ExplicitUnirational.Weierstrass.irreducible_shortWeierstrass
#print axioms ExplicitUnirational.Weierstrass.geometrically_irreducible_shortWeierstrass
#print axioms ExplicitUnirational.Weierstrass.every_singular_fibre_irreducible_arith
#print axioms ExplicitUnirational.Weierstrass.every_singular_fibre_irreducible_F5
#print axioms ExplicitUnirational.Weierstrass.every_singular_fibre_irreducible_t
#print axioms ExplicitUnirational.Weierstrass.Δ_arith_eq_factor
#print axioms ExplicitUnirational.Weierstrass.Δ_t_eq_factor
