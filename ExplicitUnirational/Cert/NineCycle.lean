/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Nine-cycle Frobenius and arithmetic Picard ranks (`[CLOP Lemma 3.9]`, `[CLOP Cor 3.8]`)

Pure representation-theoretic content of `[CLOP Cor 3.8]` and of the base-change rank
formula `ρ = 1, 3, 9` according to `gcd(9,n)` (not in [CLOP]), independent of geometry:

* the geometric sum `∑_{i=0}^{8} X^i` — the polynomial `Φ(t) = (t⁹ - 1)/(t - 1)` displayed
  in `[CLOP Example 3.10]` — factors as `Φ₃ Φ₉` over `ℚ` (the factorization itself is not
  displayed in [CLOP]);
* `Nat.gcd 9 n` realises the three cases of the base-change rank formula;
* geometric Frobenius acts as the 9-cycle `finRotate 9` on the nine base points.

The characteristic polynomial claim behind `[CLOP Cor 3.8]` is the identity
`(T^9 - 1)/(T - 1) = Φ₃(T) Φ₉(T)`, formalised as `cyclotomic_three_mul_nine`.
The base-change rank formula reduces to the value of `gcd 9 n`, formalised as
`picardRank_formula`.
-/

noncomputable section

open Polynomial
open Equiv Equiv.Perm

namespace ExplicitUnirational.NineCycle

/-! ## Cyclotomic factorization of `Φ(t) = (t⁹ - 1)/(t - 1)` (`[CLOP Example 3.10]`) -/

/-- The non-trivial divisors of `9` are `{3, 9}`. -/
private theorem erase_one_divisors_nine :
    ((9 : ℕ).divisors.erase 1) = ({3, 9} : Finset ℕ) := by
  ext d
  simp only [Finset.mem_erase, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hdvd : d ∣ (3 ^ 2) := by
      change d ∣ 9
      exact h.2.1
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl
    · exact absurd rfl h.1
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl) <;> decide

/-- `Φ₃(T) Φ₉(T) = ∑_{i=0}^{8} T^i` over `ℚ`, i.e. the factorization of the polynomial
`Φ(t) = (t⁹ - 1)/(t - 1)` of `[CLOP Example 3.10]`. -/
public theorem cyclotomic_three_mul_nine :
    Polynomial.cyclotomic 3 ℚ * Polynomial.cyclotomic 9 ℚ =
      ∑ i ∈ Finset.range 9, Polynomial.X ^ i := by
  rw [← prod_cyclotomic_eq_geom_sum (by decide : 0 < 9) ℚ, erase_one_divisors_nine,
    Finset.prod_pair (by decide : (3 : ℕ) ≠ 9)]

/-! ## Arithmetic Picard rank cases (the `gcd(9,n)` base-change formula; not in [CLOP]) -/

/-- The `n`-th power of a nine-cycle has `gcd 9 n` orbits, so its fixed subspace on the
zero-sum representation has dimension `gcd 9 n - 1`; adding the anticanonical class gives
the arithmetic Picard rank `ρ = 1, 3, 9` according to `gcd(9,n)`. -/
public theorem picardRank_formula (n : ℕ) (_hn : 0 < n) :
    Nat.gcd 9 n = if 9 ∣ n then 9 else if 3 ∣ n then 3 else 1 := by
  have hform : ∃ k ≤ 2, Nat.gcd 9 n = 3 ^ k :=
    (Nat.dvd_prime_pow Nat.prime_three).1 <| by
      exact Nat.gcd_dvd_left 9 n
  obtain ⟨k, hk_le, hk⟩ := hform
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl | rfl
  · -- `gcd = 3^0 = 1`
    have hnot3 : ¬ 3 ∣ n := by
      intro h3
      have : 3 ∣ Nat.gcd 9 n := Nat.dvd_gcd (by decide) h3
      rw [hk] at this
      exact (by decide : ¬ 3 ∣ 1) this
    have hnot9 : ¬ 9 ∣ n := fun h9 => hnot3 ((by decide : 3 ∣ 9).trans h9)
    rw [if_neg hnot9, if_neg hnot3, hk, pow_zero]
  · -- `gcd = 3^1 = 3`
    have h3 : 3 ∣ n := by
      simpa [hk] using Nat.gcd_dvd_right 9 n
    have hnot9 : ¬ 9 ∣ n := by
      intro h9
      have : Nat.gcd 9 n = 9 := Nat.gcd_eq_left h9
      rw [hk] at this
      exact (by decide : ¬ 3 ^ 1 = 9) this
    rw [if_neg hnot9, if_pos h3, hk, pow_one]
  · -- `gcd = 3^2 = 9`
    have h9 : 9 ∣ n := by
      simpa [hk] using Nat.gcd_dvd_right 9 n
    rw [if_pos h9, hk]
    norm_num

/-! ## Nine-cycle on the base points (the setup of `[CLOP Cor 3.8]`) -/

/-- Geometric Frobenius acts as a 9-cycle on the nine base points. -/
public theorem isCycle_finRotate_nine : IsCycle (finRotate 9) :=
  isCycle_finRotate_of_le (by decide)

/-- Cycle type of the geometric Frobenius 9-cycle. -/
public theorem cycleType_finRotate_nine : cycleType (finRotate 9) = {9} :=
  cycleType_finRotate_of_le (by decide)

/-- The 9-cycle has order 9. -/
public theorem orderOf_finRotate_nine : orderOf (finRotate 9) = 9 := by
  rw [IsCycle.orderOf isCycle_finRotate_nine, support_finRotate_of_le (by decide),
    Finset.card_univ, Fintype.card_fin]

end ExplicitUnirational.NineCycle
