/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.Cert.Discriminant
public import ExplicitUnirational.Cert.OcticF7
import all ExplicitUnirational.Cert.Discriminant
import all ExplicitUnirational.Cert.OcticF7
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination

/-!
# Irreducibility of the octic `q₈` over `ℚ`

The reduction of `q₈` mod 7 is irreducible in `𝔽₇[z]` (the explicit Rabin certificate
`irreducible_f8`, computer-algebra generated and not in [CLOP], up to the unit scaling by 3
that makes the reduction monic). Since the leading coefficient `432` is nonzero mod 7, the
reduction has the same degree 8, so Gauss's lemma yields irreducibility of `q₈` over `ℚ`,
and in particular square-freeness. Geometrically this says that the eight nodal members of
the pencil of `[CLOP §4.1]` form a single closed point, as in `[CLOP Lemma 4.1]`.
-/

noncomputable section

open Polynomial

namespace ExplicitUnirational.Cert

section OcticQ

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private lemma seven_eq_zero : (7 : (ZMod 7)[X]) = 0 := by
  simpa using CharP.cast_eq_zero ((ZMod 7)[X]) 7

/-- Integer-coefficient lift of the discriminant octic `q₈`.

Coefficients are `C`-wrapped so that `Polynomial.map_C` applies cleanly under reduction. -/
public def q8Z : ℤ[X] :=
  C (432 : ℤ) * X ^ 8 + C (-5032) * X ^ 7 + C 10971 * X ^ 6 + C 20844 * X ^ 5
    + C 8370 * X ^ 4 + C 3996 * X ^ 3 + C 3915 * X ^ 2 + C (-216) * X + C 432

public lemma q8Z_map_rat : q8Z.map (Int.castRingHom ℚ) = q8 := by
  rw [q8_eq]
  unfold q8Z
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    eq_intCast]
  norm_num
  ring

public lemma q8Z_natDegree : q8Z.natDegree = 8 := by
  unfold q8Z
  compute_degree!

public lemma q8Z_leadingCoeff : q8Z.leadingCoeff = 432 := by
  rw [leadingCoeff, q8Z_natDegree]
  unfold q8Z
  simp [coeff_X_pow, coeff_X, coeff_add]

private lemma q8Z_coeff_0 : q8Z.coeff 0 = 432 := by
  unfold q8Z
  simp [coeff_X_pow, coeff_X, coeff_add]

private lemma q8Z_coeff_7 : q8Z.coeff 7 = -5032 := by
  unfold q8Z
  simp [coeff_X_pow, coeff_X, coeff_add]

private lemma q8Z_coeff_6 : q8Z.coeff 6 = 10971 := by
  unfold q8Z
  simp [coeff_X_pow, coeff_X, coeff_add]

public lemma q8Z_isPrimitive : IsPrimitive q8Z := by
  intro r hr
  have hr0 : r ∣ (432 : ℤ) := by
    have := (C_dvd_iff_dvd_coeff r q8Z).mp hr 0
    rwa [q8Z_coeff_0] at this
  have hr7 : r ∣ (-5032 : ℤ) := by
    have := (C_dvd_iff_dvd_coeff r q8Z).mp hr 7
    rwa [q8Z_coeff_7] at this
  have hr6 : r ∣ (10971 : ℤ) := by
    have := (C_dvd_iff_dvd_coeff r q8Z).mp hr 6
    rwa [q8Z_coeff_6] at this
  have hgcd : r ∣ Int.gcd 432 (Int.gcd (-5032) 10971) :=
    dvd_gcd hr0 (dvd_gcd hr7 hr6)
  have h1 : Int.gcd 432 (Int.gcd (-5032) 10971) = 1 := by norm_num
  rw [h1] at hgcd
  exact isUnit_of_dvd_one hgcd

/-- The reduction of `q₈` mod 7. -/
public def r7 : (ZMod 7)[X] :=
  5 * X ^ 8 + X ^ 7 + 2 * X ^ 6 + 5 * X ^ 5 + 5 * X ^ 4 + 6 * X ^ 3 + 2 * X ^ 2 + X + 5

/-- Multiplying the reduction by 3 makes it monic, so `r7 = C 5 * f8`
(since `3 * 5 = 1` in `𝔽₇`). -/
public lemma r7_eq_C5_mul_f8 : r7 = C (5 : ZMod 7) * f8 := by
  unfold r7 f8
  rw [C_ofNat (R := ZMod 7) 5]
  -- Residual multiples of the characteristic after expanding `5 * f8`.
  linear_combination (-(2 * X + 4 * X ^ 2 + 2 * X ^ 3 + 4 * X ^ 6 + 2 * X ^ 7)) * seven_eq_zero

public lemma map_q8Z_eq_r7 : q8Z.map (Int.castRingHom (ZMod 7)) = r7 := by
  unfold q8Z r7
  simp only [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X]
  have h432 : C ((432 : ℤ) : ZMod 7) = C 5 := congr_arg C (by decide)
  have h5032 : C ((-5032 : ℤ) : ZMod 7) = C 1 := congr_arg C (by decide)
  have h10971 : C ((10971 : ℤ) : ZMod 7) = C 2 := congr_arg C (by decide)
  have h20844 : C ((20844 : ℤ) : ZMod 7) = C 5 := congr_arg C (by decide)
  have h8370 : C ((8370 : ℤ) : ZMod 7) = C 5 := congr_arg C (by decide)
  have h3996 : C ((3996 : ℤ) : ZMod 7) = C 6 := congr_arg C (by decide)
  have h3915 : C ((3915 : ℤ) : ZMod 7) = C 2 := congr_arg C (by decide)
  have h216 : C ((-216 : ℤ) : ZMod 7) = C 1 := congr_arg C (by decide)
  simp only [eq_intCast, h432, h5032, h10971, h20844, h8370, h3996, h3915, h216]
  simp only [C_ofNat, C_1, one_mul]

public lemma map_q8Z_eq_C_mul_f8 :
    q8Z.map (Int.castRingHom (ZMod 7)) = C (5 : ZMod 7) * f8 := by
  rw [map_q8Z_eq_r7, r7_eq_C5_mul_f8]

public lemma irreducible_map_q8Z :
    Irreducible (q8Z.map (Int.castRingHom (ZMod 7))) := by
  rw [map_q8Z_eq_C_mul_f8]
  refine (irreducible_isUnit_mul ?_).mpr irreducible_f8
  exact isUnit_C.mpr (Ne.isUnit (by decide : (5 : ZMod 7) ≠ 0))

public lemma q8Z_map_natDegree :
    (q8Z.map (Int.castRingHom (ZMod 7))).natDegree = q8Z.natDegree := by
  rw [q8Z_natDegree, map_q8Z_eq_C_mul_f8, natDegree_C_mul, f8_natDegree]
  exact Ne.isUnit (by decide : (5 : ZMod 7) ≠ 0) |>.ne_zero

/-- Reduction mod `p` with preserved degree ⇒ irreducibility over `ℤ` for a primitive polynomial.

Mathlib's `Monic.irreducible_of_irreducible_map` needs monicity, which `q8Z` lacks (`lc = 432`).
The primitive / same-degree argument is the standard Gauss reduction criterion. -/
private lemma irreducible_of_irreducible_map_zmod
    {p : ℕ} [Fact p.Prime] {f : ℤ[X]}
    (hprim : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom (ZMod p))))
    (hdeg : (f.map (Int.castRingHom (ZMod p))).natDegree = f.natDegree) :
    Irreducible f := by
  refine ⟨fun hu => hirr.not_isUnit (IsUnit.map (mapRingHom (Int.castRingHom (ZMod p))) hu),
    fun a b hab => ?_⟩
  have hab_map :
      f.map (Int.castRingHom (ZMod p)) =
        a.map (Int.castRingHom (ZMod p)) * b.map (Int.castRingHom (ZMod p)) := by
    rw [hab, Polynomial.map_mul]
  have hf0 : f ≠ 0 := hprim.ne_zero
  have ha0 : a ≠ 0 := fun h => by simp [h, hab] at hf0
  have hb0 : b ≠ 0 := fun h => by simp [h, hab] at hf0
  have hdeg_add : f.natDegree = a.natDegree + b.natDegree := by
    rw [hab, natDegree_mul ha0 hb0]
  rcases hirr.isUnit_or_isUnit hab_map with hau | hbu
  · have hda_map : (a.map (Int.castRingHom (ZMod p))).natDegree = 0 :=
      natDegree_eq_zero_of_isUnit hau
    have hbmap_ne : b.map (Int.castRingHom (ZMod p)) ≠ 0 := fun hbmap0 =>
      hirr.ne_zero (by rw [hab_map, hbmap0, mul_zero])
    have hsum := natDegree_mul hau.ne_zero hbmap_ne
    rw [← hab_map, hda_map, zero_add] at hsum
    have hdb_le : (b.map (Int.castRingHom (ZMod p))).natDegree ≤ b.natDegree :=
      natDegree_map_le
    have ha_deg : a.natDegree = 0 := by
      have hle : f.natDegree ≤ b.natDegree := by
        calc
          f.natDegree = (f.map (Int.castRingHom (ZMod p))).natDegree := hdeg.symm
          _ = (b.map (Int.castRingHom (ZMod p))).natDegree := hsum
          _ ≤ b.natDegree := hdb_le
      omega
    have haC : a = C (a.coeff 0) := eq_C_of_natDegree_eq_zero ha_deg
    have hCdvd : C (a.coeff 0) ∣ f := by
      rw [← haC, hab]
      exact dvd_mul_right _ _
    exact Or.inl (haC ▸ isUnit_C.mpr (hprim _ hCdvd))
  · have hdb_map : (b.map (Int.castRingHom (ZMod p))).natDegree = 0 :=
      natDegree_eq_zero_of_isUnit hbu
    have hamap_ne : a.map (Int.castRingHom (ZMod p)) ≠ 0 := fun hamap0 =>
      hirr.ne_zero (by rw [hab_map, hamap0, zero_mul])
    have hsum := natDegree_mul hamap_ne hbu.ne_zero
    rw [← hab_map, hdb_map, add_zero] at hsum
    have hda_le : (a.map (Int.castRingHom (ZMod p))).natDegree ≤ a.natDegree :=
      natDegree_map_le
    have hb_deg : b.natDegree = 0 := by
      have hle : f.natDegree ≤ a.natDegree := by
        calc
          f.natDegree = (f.map (Int.castRingHom (ZMod p))).natDegree := hdeg.symm
          _ = (a.map (Int.castRingHom (ZMod p))).natDegree := hsum
          _ ≤ a.natDegree := hda_le
      omega
    have hbC : b = C (b.coeff 0) := eq_C_of_natDegree_eq_zero hb_deg
    have hCdvd : C (b.coeff 0) ∣ f := by
      rw [← hbC, hab]
      exact dvd_mul_left _ _
    exact Or.inr (hbC ▸ isUnit_C.mpr (hprim _ hCdvd))

public theorem irreducible_q8Z : Irreducible q8Z :=
  irreducible_of_irreducible_map_zmod q8Z_isPrimitive irreducible_map_q8Z q8Z_map_natDegree

/-- `q₈` is irreducible over `ℚ`. -/
public theorem irreducible_q8 : Irreducible (q8 : Polynomial ℚ) := by
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast q8Z_isPrimitive).mp
    irreducible_q8Z
  rwa [q8Z_map_rat] at h

/-- `q₈` is square-free over `ℚ` (corollary of irreducibility). -/
public theorem squarefree_q8 : Squarefree (q8 : Polynomial ℚ) :=
  irreducible_q8.squarefree

end OcticQ

end ExplicitUnirational.Cert

#print axioms ExplicitUnirational.Cert.irreducible_q8
#print axioms ExplicitUnirational.Cert.squarefree_q8
