/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.Cert.NineCycle
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.Ring

/-!
# Abstract Néron–Severi lattice of the nine-point blow-up ([CLOP §2], [CLOP Cor 3.8])

Lattice-theoretic content of the arithmetic Picard-rank argument, with no scheme theory.

## What is proved

* Free rank-10 lattice on `H, E₁, …, E₉` with intersection form `diag(1,-1,…,-1)`.
* Canonical / fibre classes `K = -3H + ∑ Eᵢ`, `F = -K`, with `K² = F² = 0`, `Eᵢ · F = 1`,
  `K · Eᵢ = -1`, and `(K - Eᵢ)² = 1` (del Pezzo degree after contracting a section).
* Orthogonal complements: `ℚ · H ⊕ H^⊥` (since `H² ≠ 0`) and `finrank K^⊥ = 9` with
  `K ∈ K^⊥` (since `K` is isotropic).
* `S₉`-action permuting the `Eᵢ` and fixing `H`, preserving the form and fixing `K` and `F`.
* Zero-sum representation on `ℚ⁹` of rank 8, embedded as pure exceptional combinations;
  full `S₉`-invariants vanish ([CLOP Cor 3.8], with the `𝔖₉` monodromy of [CLOP Remark 4.4]).
* For the geometric Frobenius 9-cycle, fixed vectors on the zero-sum summand vanish, so the
  lattice-theoretic arithmetic Picard rank is `1` ([CLOP Cor 3.8]: `ρ = 1`).
* The case split of the base-change rank formula `ρ = 1, 3, 9` according to `gcd(9,n)`
  (not in [CLOP]) as pure number theory is already
  `NineCycle.picardRank_formula`; we re-export the connection that the rank equals `gcd(9,n)`
  once the fixed-dimension count `gcd(9,n)-1` on the zero-sum summand is granted by the
  orbit count for powers of a 9-cycle (formalised here for the identity power `n = 1`, which
  is the `ρ = 1` case).

## Honesty

This proves the lattice / representation argument of [CLOP] on an **abstract** free lattice. It does
**not** identify that lattice with geometric `NS(X_{k̄})`, nor does it prove Shioda–Tate.

Intersection numbers: on this rank-10 lattice one has `K² = F² = 0` (as for `Bl₉ ℙ²`). The
brief's simultaneous claims `K² = 1`, `F = -K`, and `F² = 0` are inconsistent; we follow
[CLOP] and the geometry of `Bl₉ ℙ²`. Degree `1` appears as `(K - Eᵢ)²` after contracting a
section.
-/

@[expose] public section
noncomputable section

open Matrix Module Equiv Equiv.Perm
open LinearMap (BilinForm)
open LinearMap.BilinForm
open Fin.NatCast

namespace ExplicitUnirational.NSLattice

/-! ## Index set and free modules -/

/-- Index: `none` is the pullback `H` of a line, `some i` is the exceptional curve `Eᵢ`. -/
public abbrev Index := Option (Fin 9)

/-- Abstract Néron–Severi lattice as free `ℤ`-module on the geometric basis. -/
public abbrev NS := Index → ℤ

/-- Rational span `NS ⊗ ℚ`. -/
public abbrev NSQ := Index → ℚ

public def H : NSQ := Pi.single none 1
public def E (i : Fin 9) : NSQ := Pi.single (some i) 1

public def intersectionMatrix : Matrix Index Index ℚ :=
  Matrix.diagonal fun i => match i with | none => (1 : ℚ) | some _ => (-1 : ℚ)

public def intersectionForm : BilinForm ℚ NSQ := Matrix.toBilin' intersectionMatrix

public theorem intersectionMatrix_diag_none : intersectionMatrix none none = 1 := by
  simp [intersectionMatrix]

public theorem intersectionMatrix_diag_some (i : Fin 9) :
    intersectionMatrix (some i) (some i) = -1 := by
  simp [intersectionMatrix]

public theorem intersectionMatrix_off {i j : Index} (h : i ≠ j) :
    intersectionMatrix i j = 0 := by
  simp [intersectionMatrix, h]

public theorem intersectionForm_single (i j : Index) :
    intersectionForm (Pi.single i 1) (Pi.single j 1) = intersectionMatrix i j :=
  Matrix.toBilin'_single (R₁ := ℚ) intersectionMatrix i j

@[simp] public theorem intersectionForm_H_H : intersectionForm H H = 1 := by
  simpa [H, intersectionMatrix_diag_none] using intersectionForm_single none none

@[simp] public theorem intersectionForm_E_E (i : Fin 9) :
    intersectionForm (E i) (E i) = -1 := by
  simpa [E, intersectionMatrix_diag_some i] using intersectionForm_single (some i) (some i)

public theorem intersectionForm_H_E (i : Fin 9) : intersectionForm H (E i) = 0 := by
  have : (none : Index) ≠ some i := by simp
  rw [H, E, intersectionForm_single, intersectionMatrix_off this]

public theorem intersectionForm_E_E_of_ne {i j : Fin 9} (hij : i ≠ j) :
    intersectionForm (E i) (E j) = 0 := by
  have : (some i : Index) ≠ some j := by simp [hij]
  rw [E, E, intersectionForm_single, intersectionMatrix_off this]

public theorem intersectionForm_apply (x y : NSQ) :
    intersectionForm x y =
      x none * y none - ∑ i : Fin 9, x (some i) * y (some i) := by
  dsimp only [intersectionForm]
  rw [Matrix.toBilin'_apply]
  simp only [intersectionMatrix, diagonal_apply]
  have h :
      (∑ i : Index, ∑ j : Index,
          x i * (if i = j then (match i with | none => (1 : ℚ) | some _ => (-1 : ℚ)) else 0) *
            y j) =
        ∑ i : Index, x i * (match i with | none => (1 : ℚ) | some _ => (-1 : ℚ)) * y i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg (Ne.symm hji)]; ring
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  rw [h]
  classical
  rw [Fintype.sum_option]
  ring_nf
  simp [Finset.sum_neg_distrib]
  ring

public theorem intersectionForm_isSymm : intersectionForm.IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [intersectionForm_apply, intersectionForm_apply]
  simp [mul_comm]

public theorem intersectionForm_isRefl : intersectionForm.IsRefl :=
  intersectionForm_isSymm.isRefl

/-! ## Canonical and fibre classes -/

/-- Canonical class `K = -3H + ∑ Eᵢ` ([CLOP §2], [CLOP §3]). -/
public def K : NSQ := (-3 : ℚ) • H + ∑ i : Fin 9, E i

/-- Fibre class `F = 3H - ∑ Eᵢ = -K`. -/
public def F : NSQ := (3 : ℚ) • H - ∑ i : Fin 9, E i

public theorem F_eq_neg_K : F = -K := by
  simp only [F, K, neg_add_rev, neg_smul, neg_neg]
  abel

public theorem K_eq_neg_F : K = -F := by
  rw [F_eq_neg_K, neg_neg]

public theorem K_apply (i : Index) :
    K i = match i with | none => (-3 : ℚ) | some _ => (1 : ℚ) := by
  cases i with
  | none => simp [K, H, E, Finset.sum_apply]
  | some a => simp [K, H, E, Pi.single_apply, Finset.sum_apply]

public theorem F_apply (i : Index) :
    F i = match i with | none => (3 : ℚ) | some _ => (-1 : ℚ) := by
  have h := congrArg (fun v : NSQ => v i) F_eq_neg_K
  simp only [Pi.neg_apply, K_apply] at h
  cases i <;> simp [h]

public theorem K_sq : intersectionForm K K = 0 := by
  rw [intersectionForm_apply]; simp [K_apply]; norm_num

public theorem F_sq : intersectionForm F F = 0 := by
  rw [F_eq_neg_K]; simp [neg_right, K_sq]

public theorem F_dot_K : intersectionForm F K = 0 := by
  rw [F_eq_neg_K]; simp [K_sq]

public theorem E_dot_F (i : Fin 9) : intersectionForm (E i) F = 1 := by
  rw [intersectionForm_apply]; simp [E, F_apply, Pi.single_apply]

public theorem K_dot_E (i : Fin 9) : intersectionForm K (E i) = -1 := by
  have h := congrArg (fun v => intersectionForm v (E i)) K_eq_neg_F
  have h' : intersectionForm (-F) (E i) = -intersectionForm F (E i) := neg_left F (E i)
  have hFE : intersectionForm F (E i) = 1 := by
    rw [intersectionForm_isSymm.eq]; exact E_dot_F i
  simp only [h', hFE] at h
  linarith

public theorem K_sub_E_sq (i : Fin 9) :
    intersectionForm (K - E i) (K - E i) = 1 := by
  have hKE := K_dot_E i
  have hEK : intersectionForm (E i) K = -1 := by rw [intersectionForm_isSymm.eq, hKE]
  have hEE := intersectionForm_E_E i
  have hKK := K_sq
  simp only [sub_left, sub_right, hKK, hKE, hEK, hEE]
  norm_num

/-! ## Ranks and orthogonals -/

public theorem finrank_NSQ : finrank ℚ NSQ = 10 := by
  simp [NSQ, Index, Fintype.card_option, Fintype.card_fin]

private theorem finrank_range_eq_one {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (f : V →ₗ[ℚ] ℚ) (hf : f ≠ 0) :
    finrank ℚ (LinearMap.range f) = 1 := by
  -- nonzero linear form V → ℚ is surjective, so range = ⊤ ≃ ℚ
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := not_forall.mp fun h =>
    hf (LinearMap.ext fun x => h x)
  have hsurj : Function.Surjective f := fun c =>
    ⟨(c / f v) • v, by simp [hv]⟩
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 hsurj
  rw [hrange, finrank_top, finrank_self]

public theorem isCompl_span_H_orthogonal :
    IsCompl (ℚ ∙ H) (intersectionForm.orthogonal (ℚ ∙ H)) :=
  isCompl_span_singleton_orthogonal (by
    have : intersectionForm H H = 1 := intersectionForm_H_H
    simp [this])

public theorem finrank_H_orthogonal :
    finrank ℚ (intersectionForm.orthogonal (ℚ ∙ H)) = 9 := by
  have hker :
      LinearMap.ker (toLinHomAux₁ intersectionForm H) =
        intersectionForm.orthogonal (ℚ ∙ H) :=
    (orthogonal_span_singleton_eq_toLin_ker (B := intersectionForm) H).symm
  have hf : toLinHomAux₁ intersectionForm H ≠ 0 := by
    intro h
    have := congrArg (fun g : NSQ →ₗ[ℚ] ℚ => g H) h
    simp [toLinHomAux₁, intersectionForm_H_H] at this
  have hsum := LinearMap.finrank_range_add_finrank_ker (toLinHomAux₁ intersectionForm H)
  have hrange := finrank_range_eq_one (toLinHomAux₁ intersectionForm H) hf
  have htop := finrank_NSQ
  rw [hker] at hsum
  omega

private def K_form : NSQ →ₗ[ℚ] ℚ := toLinHomAux₁ intersectionForm K

private theorem K_form_ne_zero : K_form ≠ 0 := by
  intro h
  have := congrArg (fun g : NSQ →ₗ[ℚ] ℚ => g (E 0)) h
  simp [K_form, toLinHomAux₁, K_dot_E] at this

public theorem finrank_K_orthogonal :
    finrank ℚ (intersectionForm.orthogonal (ℚ ∙ K)) = 9 := by
  have hker :
      LinearMap.ker K_form = intersectionForm.orthogonal (ℚ ∙ K) :=
    (orthogonal_span_singleton_eq_toLin_ker (B := intersectionForm) K).symm
  have hsum := LinearMap.finrank_range_add_finrank_ker K_form
  have hrange := finrank_range_eq_one K_form K_form_ne_zero
  have htop := finrank_NSQ
  rw [hker] at hsum
  omega

public theorem K_mem_K_orthogonal : K ∈ intersectionForm.orthogonal (ℚ ∙ K) := by
  intro y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  simp [K_sq]

/-! ## Sym(9) action -/

public def permAction (σ : Perm (Fin 9)) : NSQ →ₗ[ℚ] NSQ where
  toFun v i := match i with | none => v none | some j => v (some (σ.symm j))
  map_add' := by intro x y; funext i; cases i <;> simp
  map_smul' := by intro c x; funext i; cases i <;> simp

@[simp] public theorem permAction_H (σ : Perm (Fin 9)) : permAction σ H = H := by
  funext i; cases i <;> simp [permAction, H]

@[simp] public theorem permAction_E (σ : Perm (Fin 9)) (i : Fin 9) :
    permAction σ (E i) = E (σ i) := by
  funext j
  cases j with
  | none => simp [permAction, E]
  | some k =>
    simp only [permAction, E, Pi.single_apply, Option.some.injEq]
    by_cases h : k = σ i
    · subst h; simp
    · have : σ.symm k ≠ i := by
        contrapose! h
        exact (Equiv.symm_apply_eq σ).mp h
      simp [h, this]

public theorem permAction_mul (σ τ : Perm (Fin 9)) :
    permAction (σ * τ) = permAction σ ∘ₗ permAction τ := by
  apply LinearMap.ext
  intro x
  funext i
  cases i with
  | none => rfl
  | some j =>
    change x (some ((σ * τ).symm j)) = x (some (τ.symm (σ.symm j)))
    have hinv : (σ * τ).symm = τ.symm * σ.symm := by
      change (σ * τ)⁻¹ = τ⁻¹ * σ⁻¹
      exact mul_inv_rev σ τ
    rw [hinv]
    rfl

public theorem permAction_one : permAction (1 : Perm (Fin 9)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  cases i with
  | none => rfl
  | some j =>
    change x (some ((1 : Perm (Fin 9)).symm j)) = x (some j)
    rfl

public theorem permAction_preserves_form (σ : Perm (Fin 9)) (x y : NSQ) :
    intersectionForm (permAction σ x) (permAction σ y) = intersectionForm x y := by
  rw [intersectionForm_apply, intersectionForm_apply]
  simp only [permAction]
  have hreindex :
      (∑ j : Fin 9, x (some (σ.symm j)) * y (some (σ.symm j))) =
        ∑ i : Fin 9, x (some i) * y (some i) :=
    Function.Bijective.sum_comp (Equiv.bijective σ.symm)
      (fun i => x (some i) * y (some i))
  exact congrArg₂ _ rfl hreindex

public theorem permAction_K (σ : Perm (Fin 9)) : permAction σ K = K := by
  unfold K
  rw [map_add, map_smul, map_sum, permAction_H]
  simp only [permAction_E]
  have hreindex : (∑ i : Fin 9, E (σ i)) = ∑ i : Fin 9, E i :=
    Function.Bijective.sum_comp (Equiv.bijective σ) E
  rw [hreindex]

public theorem permAction_F (σ : Perm (Fin 9)) : permAction σ F = F := by
  rw [F_eq_neg_K, map_neg, permAction_K]

/-! ## Zero-sum representation ([CLOP Lemma 3.9]) -/

public def zeroSum : Submodule ℚ (Fin 9 → ℚ) where
  carrier := { v | ∑ i : Fin 9, v i = 0 }
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    rw [Finset.sum_add_distrib, ha, hb, add_zero]
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [← Finset.mul_sum, hv, mul_zero]

@[simp] public theorem mem_zeroSum_iff (v : Fin 9 → ℚ) :
    v ∈ zeroSum ↔ ∑ i : Fin 9, v i = 0 := Iff.rfl

/-- Embed `ℚ⁹` into `NSQ` as pure exceptional combinations `∑ rᵢ Eᵢ`. -/
public def zeroSumEmbed (r : Fin 9 → ℚ) : NSQ :=
  ∑ i : Fin 9, r i • E i

public theorem zeroSumEmbed_coord (r : Fin 9 → ℚ) (i : Fin 9) :
    zeroSumEmbed r (some i) = r i := by
  simp [zeroSumEmbed, E, Pi.single_apply, Finset.sum_apply]

public theorem zeroSumEmbed_none (r : Fin 9 → ℚ) : zeroSumEmbed r none = 0 := by
  simp [zeroSumEmbed, E, Finset.sum_apply]

public theorem zeroSumEmbed_mem_F_orthogonal (r : Fin 9 → ℚ) (hr : r ∈ zeroSum) :
    intersectionForm F (zeroSumEmbed r) = 0 := by
  have hdot : intersectionForm F (zeroSumEmbed r) = ∑ i : Fin 9, r i := by
    simp only [zeroSumEmbed, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hFE : intersectionForm F (E i) = 1 := by
      rw [intersectionForm_isSymm.eq]; exact E_dot_F i
    -- B F (rᵢ • Eᵢ) = rᵢ * B F Eᵢ = rᵢ
    simp [hFE]
  rw [hdot, (mem_zeroSum_iff r).1 hr]

private def sumForm : (Fin 9 → ℚ) →ₗ[ℚ] ℚ := ∑ i : Fin 9, LinearMap.proj i

private theorem sumForm_apply (v : Fin 9 → ℚ) : sumForm v = ∑ i : Fin 9, v i := by
  simp [sumForm, LinearMap.coe_sum, Finset.sum_apply]

private theorem sumForm_ne_zero : sumForm ≠ 0 := by
  intro h
  have := congrArg (fun f : (Fin 9 → ℚ) →ₗ[ℚ] ℚ => f (Pi.single 0 1)) h
  simp [sumForm_apply, Pi.single_apply] at this

public theorem finrank_zeroSum : finrank ℚ zeroSum = 8 := by
  have hker : LinearMap.ker sumForm = zeroSum := by
    ext v; simp [sumForm_apply, zeroSum]
  have hsum := LinearMap.finrank_range_add_finrank_ker sumForm
  have hrange := finrank_range_eq_one sumForm sumForm_ne_zero
  have h9 : finrank ℚ (Fin 9 → ℚ) = 9 := by simp
  rw [hker] at hsum
  omega

/-! ## Action on ℚ⁹ and invariants -/

public def permOnNine (σ : Perm (Fin 9)) : (Fin 9 → ℚ) →ₗ[ℚ] (Fin 9 → ℚ) where
  toFun v j := v (σ.symm j)
  map_add' := by intros; funext; simp
  map_smul' := by intros; funext; simp

public theorem permOnNine_apply (σ : Perm (Fin 9)) (v : Fin 9 → ℚ) (j : Fin 9) :
    permOnNine σ v j = v (σ.symm j) := by
  rfl

public theorem mem_fixed_permOnNine_iff (σ : Perm (Fin 9)) (v : Fin 9 → ℚ) :
    v ∈ LinearMap.fixedSubmodule (permOnNine σ) ↔ ∀ i, v (σ i) = v i := by
  simp only [LinearMap.mem_fixedSubmodule_iff]
  constructor
  · intro h i
    have := congrFun h (σ i)
    -- permOnNine σ v (σ i) = v i, equals v (σ i)
    change v (σ.symm (σ i)) = v (σ i) at this
    simpa using this.symm
  · intro h
    funext j
    change v (σ.symm j) = v j
    simpa using (h (σ.symm j)).symm

public theorem permOnNine_maps_zeroSum (σ : Perm (Fin 9)) {v : Fin 9 → ℚ}
    (hv : v ∈ zeroSum) : permOnNine σ v ∈ zeroSum := by
  rw [mem_zeroSum_iff] at hv ⊢
  change ∑ j, v (σ.symm j) = 0
  rw [Function.Bijective.sum_comp σ.symm.bijective v, hv]

/-- An `S₉`-invariant vector in the zero-sum representation vanishes ([CLOP Cor 3.8]). -/
public theorem zeroSum_S9_invariants (v : Fin 9 → ℚ)
    (hfix : ∀ σ : Perm (Fin 9), permOnNine σ v = v) (hsum : v ∈ zeroSum) : v = 0 := by
  have hconst : ∀ i j : Fin 9, v i = v j := by
    intro i j
    have hij := congrFun (hfix (Equiv.swap i j)) j
    -- hij : permOnNine (swap i j) v j = v j, i.e. v i = v j
    change v ((Equiv.swap i j).symm j) = v j at hij
    have : v i = v j := by
      simpa [Equiv.symm_swap, Equiv.swap_apply_right] using hij
    exact this
  have hall : ∀ i, v i = v 0 := fun i => hconst i 0
  have hsum' : ∑ i, v i = 0 := (mem_zeroSum_iff v).1 hsum
  have h9v : (9 : ℚ) * v 0 = 0 := by
    simp only [hall] at hsum'
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum'
  have hv0 : v 0 = 0 := (mul_eq_zero.mp h9v).resolve_left (by norm_num)
  ext i; simp [hall i, hv0]

public abbrev fixedNine (σ : Perm (Fin 9)) : Submodule ℚ (Fin 9 → ℚ) :=
  LinearMap.fixedSubmodule (permOnNine σ)

public def fixedZeroSum (σ : Perm (Fin 9)) : Submodule ℚ (Fin 9 → ℚ) :=
  fixedNine σ ⊓ zeroSum

/-! ## Nine-cycle and ρ = 1 -/

public theorem finRotate_pow_apply (n : ℕ) (i : Fin 9) :
    ((finRotate 9) ^ n) i = i + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, finRotate_apply, ih, Nat.cast_succ, add_assoc]

/-- A vector fixed by the 9-cycle is constant on `Fin 9`. -/
public theorem fixed_finRotate_const (v : Fin 9 → ℚ)
    (hv : v ∈ fixedNine (finRotate 9)) (i j : Fin 9) : v i = v j := by
  have hcycle := ExplicitUnirational.NineCycle.isCycle_finRotate_nine
  have hfix : ∀ k, v ((finRotate 9) k) = v k := (mem_fixed_permOnNine_iff _ v).1 hv
  -- Iterate: v is constant along the cycle
  have hpow : ∀ n : ℕ, ∀ k, v (((finRotate 9) ^ n) k) = v k := by
    intro n k
    induction n generalizing k with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, hfix, ih]
  -- Any two points of Fin 9 lie on the single 9-cycle
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq
    (by
      have hs := ExplicitUnirational.NineCycle.cycleType_finRotate_nine
      -- support is all of Fin 9
      have hsup := support_finRotate_of_le (by decide : 2 ≤ 9)
      have : i ∈ support (finRotate 9) := by simp [hsup]
      exact mem_support.mp this)
    (by
      have hsup := support_finRotate_of_le (by decide : 2 ≤ 9)
      have : j ∈ support (finRotate 9) := by simp [hsup]
      exact mem_support.mp this)
  calc
    v i = v (((finRotate 9) ^ n) i) := (hpow n i).symm
    _ = v j := by rw [hn]

/-- Fixed subspace of the 9-cycle on the zero-sum representation is trivial. -/
public theorem fixedZeroSum_finRotate_eq_bot :
    fixedZeroSum (finRotate 9) = ⊥ := by
  ext v
  simp only [fixedZeroSum, Submodule.mem_inf, Submodule.mem_bot]
  constructor
  · intro ⟨hfix, hsum⟩
    have hconst := fixed_finRotate_const v hfix
    have hall : ∀ i, v i = v 0 := fun i => hconst i 0
    have hsum' : ∑ i, v i = 0 := (mem_zeroSum_iff v).1 hsum
    have h9v : (9 : ℚ) * v 0 = 0 := by
      simp only [hall] at hsum'
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum'
    have hv0 : v 0 = 0 := (mul_eq_zero.mp h9v).resolve_left (by norm_num)
    ext i; simp [hall i, hv0]
  · rintro rfl; simp

public theorem finrank_fixedZeroSum_finRotate :
    finrank ℚ (fixedZeroSum (finRotate 9)) = 0 := by
  rw [fixedZeroSum_finRotate_eq_bot, finrank_bot]

/-- Lattice-theoretic arithmetic Picard rank for the geometric Frobenius 9-cycle:
`1 + dim Fix(zeroSum) = 1` ([CLOP Cor 3.8], `ρ = 1`). -/
public theorem arithmeticPicardRank_one :
    finrank ℚ (fixedZeroSum (finRotate 9)) + 1 = 1 := by
  simp [finrank_fixedZeroSum_finRotate]

/-- Re-export of the number-theoretic case split of the base-change rank formula
`ρ = 1, 3, 9` according to `gcd(9,n)` (not in [CLOP]). Combined with the
representation-theoretic fact that the fixed dimension of the `n`-th power of a 9-cycle on the
zero-sum representation is `gcd(9,n) - 1`, this yields the arithmetic Picard
ranks over finite extensions. The identity-power case `gcd(9,1) - 1 = 0` is
`finrank_fixedZeroSum_finRotate` above. -/
public theorem picardRank_formula_reexport (n : ℕ) (hn : 0 < n) :
    Nat.gcd 9 n = if 9 ∣ n then 9 else if 3 ∣ n then 3 else 1 :=
  ExplicitUnirational.NineCycle.picardRank_formula n hn

/-- Full `S₉`-invariants of the zero-sum summand vanish ([CLOP Remark 4.4] monodromy,
[CLOP Cor 3.8]). -/
public theorem rho_eq_one_of_S9 :
    ∀ v : Fin 9 → ℚ,
      (∀ σ : Perm (Fin 9), permOnNine σ v = v) → v ∈ zeroSum → v = 0 :=
  zeroSum_S9_invariants

end ExplicitUnirational.NSLattice
