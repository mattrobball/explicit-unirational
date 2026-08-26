/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Rabin's irreducibility criterion

Formalization of Rabin's criterion for irreducibility of monic polynomials over finite fields
([LN97, §3.4]; used here for the explicit irreducibility certificates, which are
computer-algebra generated and not in [CLOP]), together with a Frobenius ladder for reducing the congruence
`X ^ (q ^ n) ≡ X [MOD f]` to a chain of ordinary polynomial identities of manageable degree.

The four public theorems are the API consumed by the certificate modules
(`Cert/OcticF7`, `Cert/NonicF5`, `Cert/SexticF5`).

## Certificate idiom (ladder steps over `ZMod q`)

Bare `ring` does not reduce integer numerals modulo the characteristic. Polynomial-level
`decide` is unusable (`DecidableEq` on `Polynomial` is classical). The working pattern is:

1. unfold definitions with `simp only`;
2. expand with `ring` to a common form that still contains characteristic numerals
   (a formal identity in any `CommRing`);
3. rewrite residual numerals via `CharP.cast_eq_mod` / `(n : (ZMod q)[X]) = (n % q : ℕ)`,
   with `n % q = 0` or `n % q = r` discharged by `decide` on `ℕ`;
4. finish with `ring`.
-/

noncomputable section

open Polynomial

namespace ExplicitUnirational.Rabin

/-! ## Frobenius ladder (no finiteness required) -/

section Ladder

variable {F : Type*} [Field F]

/-- One step of the Frobenius ladder: if `a` is the reduction of `X ^ (q ^ m)` modulo `f`,
and `a ^ q = f * s + b`, then `b` is the reduction of `X ^ (q ^ (m + 1))`. -/
public theorem dvd_sub_step {f a b s : F[X]} {m : ℕ}
    (hprev : f ∣ X ^ (Nat.card F ^ m) - a)
    (hstep : a ^ (Nat.card F) = f * s + b) :
    f ∣ X ^ (Nat.card F ^ (m + 1)) - b := by
  set q := Nat.card F
  have hpow : (X : F[X]) ^ (q ^ (m + 1)) = (X ^ (q ^ m)) ^ q := by
    rw [pow_succ, pow_mul]
  have hchain : f ∣ (X ^ (q ^ m)) ^ q - a ^ q :=
    hprev.trans (sub_dvd_pow_sub_pow (X ^ (q ^ m)) a q)
  have hchain' : f ∣ X ^ (q ^ (m + 1)) - a ^ q := by
    rwa [← hpow] at hchain
  have hrewrite : X ^ (q ^ (m + 1)) - b = (X ^ (q ^ (m + 1)) - a ^ q) + f * s := by
    rw [hstep]
    ring
  rw [hrewrite]
  exact dvd_add hchain' (dvd_mul_right _ _)

/-- Coprimality may be checked against a reduced representative. -/
public theorem isCoprime_of_reduction {f r : F[X]} {m : ℕ}
    (hr : f ∣ (X ^ (Nat.card F ^ m) - X) - r) (h : IsCoprime f r) :
    IsCoprime f (X ^ (Nat.card F ^ m) - X) := by
  obtain ⟨t, ht⟩ := hr
  have htarget : X ^ (Nat.card F ^ m) - X = f * t + r := by
    linear_combination ht
  rw [htarget]
  exact h.mul_add_left_right t

end Ladder

/-! ## Rabin criterion (finite base field) -/

section Rabin

variable {F : Type*} [Field F] [Finite F]

/-- If `d ∣ n` and `d < n` with `0 < d`, some prime `ℓ ∣ n` satisfies `d ∣ n / ℓ`. -/
private theorem exists_prime_dvd_of_natDegree_dvd_lt {d n : ℕ} (hdpos : 0 < d) (hdvd : d ∣ n)
    (hlt : d < n) : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ n ∧ d ∣ n / ℓ := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 1 < k := (Nat.lt_mul_iff_one_lt_right hdpos).1 hlt
  obtain ⟨ℓ, hℓ_prime, hℓ_dvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hk)
  refine ⟨ℓ, hℓ_prime, dvd_mul_of_dvd_right hℓ_dvd d, ?_⟩
  rw [Nat.mul_div_assoc _ hℓ_dvd]
  exact dvd_mul_right _ _

/-- A monic irreducible `g` of degree dividing `m` divides `X ^ (q ^ m) - X`. -/
public theorem dvd_X_pow_card_pow_sub_X_of_natDegree_dvd
    {g : F[X]} (hg : Irreducible g) (hgm : g.Monic) {m : ℕ} (h : g.natDegree ∣ m) :
    g ∣ X ^ (Nat.card F ^ m) - X := by
  classical
  haveI : Fact (Irreducible g) := ⟨hg⟩
  haveI := hgm.finite_adjoinRoot
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite F
  haveI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  obtain ⟨j, rfl⟩ := h
  have hcard : Fintype.card (AdjoinRoot g) = Nat.card F ^ g.natDegree := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := F),
      PowerBasis.finrank (AdjoinRoot.powerBasis hg.ne_zero),
      AdjoinRoot.powerBasis_dim hg.ne_zero]
  have hroot :
      (AdjoinRoot.root g) ^ (Nat.card F ^ (g.natDegree * j)) = AdjoinRoot.root g := by
    have hexp : Nat.card F ^ (g.natDegree * j) = Fintype.card (AdjoinRoot g) ^ j := by
      rw [hcard, pow_mul]
    rw [hexp]
    exact FiniteField.pow_card_pow j _
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, hroot, sub_self]

/-- Rabin's irreducibility criterion. -/
public theorem irreducible_of_rabin {f : F[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (h1 : f ∣ X ^ (Nat.card F ^ f.natDegree) - X)
    (h2 : ∀ l : ℕ, l.Prime → l ∣ f.natDegree →
      IsCoprime f (X ^ (Nat.card F ^ (f.natDegree / l)) - X)) :
    Irreducible f := by
  obtain ⟨g, hg_monic, hg_irr, hg_dvd⟩ :=
    exists_monic_irreducible_factor f (not_isUnit_of_natDegree_pos f hdeg)
  set n := f.natDegree
  set d := g.natDegree
  have hg_dvd_pow : g ∣ X ^ (Nat.card F ^ n) - X := hg_dvd.trans h1
  have hd_dvd_n : d ∣ n := hg_irr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hg_dvd_pow
  have hd_pos : 0 < d := hg_irr.natDegree_pos
  have hd_le : d ≤ n := Nat.le_of_dvd hdeg hd_dvd_n
  have hd_eq : d = n := by
    by_contra hne
    have hlt : d < n := lt_of_le_of_ne hd_le hne
    obtain ⟨ℓ, hℓ_prime, hℓ_dvd_n, hd_dvd_div⟩ :=
      exists_prime_dvd_of_natDegree_dvd_lt hd_pos hd_dvd_n hlt
    have hg_dvd_poly : g ∣ X ^ (Nat.card F ^ (n / ℓ)) - X :=
      dvd_X_pow_card_pow_sub_X_of_natDegree_dvd hg_irr hg_monic hd_dvd_div
    exact hg_irr.not_isUnit <| (h2 ℓ hℓ_prime hℓ_dvd_n).isUnit_of_dvd' hg_dvd hg_dvd_poly
  rwa [eq_of_monic_of_dvd_of_natDegree_le hg_monic hf hg_dvd (le_of_eq hd_eq.symm)]

end Rabin

/-! ## Freshman's dream: the `q`-th power map on `(ZMod p)[X]` -/

/-- Over `ZMod p`, raising a polynomial to the `p`-th power is substitution `X ↦ X ^ p`.

This is what makes the ladder of §Ladder computationally feasible. A ladder step
`r_k ^ p = f * s_k + r_(k+1)` expanded naively produces a dense polynomial of degree
`p * deg r_k` with coefficients as large as `(p-1)^p`; via `expand` the left side stays as
sparse as `r_k` itself, and the residual certificate has small coefficients. -/
public theorem pow_card_eq_expand (p : ℕ) [Fact p.Prime] (r : (ZMod p)[X]) :
    r ^ p = expand (ZMod p) p r := by
  have h := map_frobenius_expand (R := ZMod p) (p := p) r
  rw [ZMod.frobenius_zmod, map_id] at h
  exact h.symm

/-! ## Smoke test: `X² + 2` over `F₅`

A faithful miniature of C2/C3/C4: modulus odd, ladder uses real mod-5 numeral reduction.
Witnesses are precomputed; each identity is closed by expand-then-clear-characteristic.
-/

section SmokeTest

/-! End-to-end exercise of the API on `X² + 2` over `F₅`, irreducible because `-2 = 3` is not
a square mod `5`. This deliberately uses `q = 5`, not `q = 2`: characteristic two is degenerate
(`-1 = 1`), so an idiom validated there would not transfer to the irreducibility certificates. -/

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def f₅ : (ZMod 5)[X] := X ^ 2 + 2
private def s₀ : (ZMod 5)[X] := X ^ 3 + 3 * X
private def s₁ : (ZMod 5)[X] := 4 * X ^ 3 + 2 * X

/-- The characteristic numeral, cleared once. Every ladder identity below is discharged by
`linear_combination c * h5`, where `c = (LHS - RHS) / 5` is computed over `ℤ`. -/
private lemma h5 : (5 : (ZMod 5)[X]) = 0 := by
  simpa using CharP.cast_eq_zero ((ZMod 5)[X]) 5

private lemma f₅_eq : f₅ = X ^ 2 + C 2 := by
  rw [f₅]; norm_cast

private lemma f₅_monic : f₅.Monic := by
  rw [f₅_eq]; exact monic_X_pow_add_C 2 (by norm_num)

private lemma f₅_natDegree : f₅.natDegree = 2 := by
  rw [f₅_eq, natDegree_X_pow_add_C]

private lemma card_zmod_five : Nat.card (ZMod 5) = 5 := Nat.card_zmod 5

/-- Ladder step 0: `X ^ 5 = f * s₀ + 4 * X`. -/
private lemma ladder_step0 : (X : (ZMod 5)[X]) ^ 5 = f₅ * s₀ + 4 * X := by
  simp only [f₅, s₀]
  linear_combination (-(X ^ 3) - 2 * X) * h5

/-- Ladder step 1: `(4 * X) ^ 5 = f * s₁ + X`. -/
private lemma ladder_step1 : (4 * X : (ZMod 5)[X]) ^ 5 = f₅ * s₁ + X := by
  simp only [f₅, s₁]
  linear_combination (204 * X ^ 5 - 2 * X ^ 3 - X) * h5

/-- Reduction witness: `(X ^ 5 - X) - 3 * X = f * s₀`. -/
private lemma reduction_eq : (X ^ 5 - X : (ZMod 5)[X]) - 3 * X = f₅ * s₀ := by
  simp only [f₅, s₀]
  linear_combination (-(X ^ 3) - 2 * X) * h5

/-- Bézout witness: `3 * f + (4 * X) * (3 * X) = 1`. -/
private lemma bezout_eq : (3 : (ZMod 5)[X]) * f₅ + (4 * X) * (3 * X) = 1 := by
  simp only [f₅]
  linear_combination (3 * X ^ 2 + 1) * h5

/-- End-to-end smoke test of the Rabin API on `X² + 2` over `F₅`. -/
public theorem irreducible_X_pow_two_add_two_zmod_five :
    Irreducible (X ^ 2 + 2 : (ZMod 5)[X]) := by
  change Irreducible f₅
  refine irreducible_of_rabin f₅_monic (by rw [f₅_natDegree]; norm_num) ?h1 ?h2
  · -- Ladder: X ↦ 4X ↦ X over two Frobenius steps, so f₅ ∣ X ^ (5 ^ 2) - X.
    have hbase : f₅ ∣ X ^ (Nat.card (ZMod 5) ^ 0) - X := by simp
    have hstep0 : (X : (ZMod 5)[X]) ^ Nat.card (ZMod 5) = f₅ * s₀ + 4 * X := by
      rw [card_zmod_five, ladder_step0]
    have hstep1 : (4 * X : (ZMod 5)[X]) ^ Nat.card (ZMod 5) = f₅ * s₁ + X := by
      rw [card_zmod_five, ladder_step1]
    have hmid : f₅ ∣ X ^ (Nat.card (ZMod 5) ^ 1) - 4 * X := dvd_sub_step hbase hstep0
    have htop : f₅ ∣ X ^ (Nat.card (ZMod 5) ^ 2) - X := dvd_sub_step hmid hstep1
    rw [f₅_natDegree]
    exact htop
  · intro l hl_prime hl_dvd
    have hl_eq : l = 2 :=
      (Nat.prime_dvd_prime_iff_eq hl_prime Nat.prime_two).1 (by rwa [f₅_natDegree] at hl_dvd)
    subst hl_eq
    have hred : f₅ ∣ (X ^ (Nat.card (ZMod 5) ^ 1) - X) - 3 * X := by
      refine ⟨s₀, ?_⟩
      rw [card_zmod_five, pow_one]
      exact reduction_eq
    have hcop_r : IsCoprime f₅ (3 * X : (ZMod 5)[X]) := ⟨3, 4 * X, bezout_eq⟩
    have hcop : IsCoprime f₅ (X ^ (Nat.card (ZMod 5) ^ 1) - X) :=
      isCoprime_of_reduction hred hcop_r
    rw [f₅_natDegree, Nat.div_self (by norm_num : 0 < 2)]
    exact hcop

end SmokeTest

#print axioms ExplicitUnirational.Rabin.irreducible_of_rabin

end ExplicitUnirational.Rabin
