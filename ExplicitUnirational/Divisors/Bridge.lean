/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.Divisors.ClassGroup
public import ExplicitUnirational.Divisors.NSLattice
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Bridge: Weil class group ↔ combinatorial NS lattice (note §4.2, §5.4)

Two objects already live in this repository and are not yet connected:

* `ClassGroup X` (`Divisors/ClassGroup.lean`) — the **real** Weil divisor class group of an
  integral locally Noetherian scheme.
* `NSLattice` (`Divisors/NSLattice.lean`) — the **combinatorial** rank-10 lattice on
  `H, E₁, …, E₉` with form `diag(1,-1,…,-1)`, the `S₉` action, the zero-sum representation, and
  the lattice-theoretic `ρ = 1` for the geometric Frobenius 9-cycle.

The note's Picard-rank argument (docs/note.txt §4.2, §5.4, Prop. 4.2, (5.18)) is stated about
geometry but is proved combinatorially on the second object. This module turns that combinatorial
fact into a **conditional theorem about schemes**: *if* the rational class group of `X` is
identified with the lattice model as a module with form and with Galois/Frobenius action, *then*
the note's `ρ = 1` conclusion holds for `X`.

## What is proved unconditionally

* `ClassGroupQ X := ClassGroup X ⊗[ℤ] ℚ` — rationalized Weil class group.
* Transfer of fixed-subspace dimension along linear equivalences that intertwine endomorphisms.
* The abstract rank count for the model 9-cycle action on the full lattice (`finrank = 2`) and
  on the zero-sum summand (`finrank = 0`, already in `NSLattice`).
* Conditional interface theorems: under an identification hypothesis
  (`IsNineCycleNSModel`, `IsS9NSModel`, `IsDelPezzoNineCycleModel`), the arithmetic Picard rank
  of `X` equals the lattice-theoretic value (`2` for the elliptic-surface packaging of `NSQ`,
  `1` for the del Pezzo packaging used by the note).

## What is an explicit hypothesis (not a construction)

* **Intersection pairing.** Mathlib has no intersection theory of divisors on surfaces. The
  structure `HasIntersectionForm X` packages a symmetric bilinear form on `ClassGroupQ X` as a
  **hypothesis** a surface may carry. No form is constructed from scheme data.
* **Galois / Frobenius action on `ClassGroupQ`.** Functoriality of `ClassGroup` under base
  change and the identification of geometric Frobenius with a permutation of exceptional curves
  are not formalized. Linear actions appear as data of the identification structures.
* **The identification itself.** Structures such as `IsNineCycleNSModel X` assert the existence
  of a form-preserving linear equivalence intertwining actions. Proving any concrete `X` (e.g.
  `S₅`, `S_ℚ`, `S_t`) satisfies them is out of scope.

## What is not proved at all

* Blow-ups of schemes (absent from Mathlib).
* `Cl(Bl₉ ℙ²) ≅ NS` as lattices with form, or the Shioda–Tate decomposition.
* Specialization injectivity on Néron–Severi (note (4.6)).
* That `ClassGroupQ X` equals `NS(X_{k̄}) ⊗ ℚ` (on a rational surface one has
  `Pic⁰ = 0` so `NS = Pic = Cl`, but that comparison is not formalized).

See `BlowUpIdentificationObligations` for a precise checklist of missing inputs for a
blow-up of `ℙ²`.

## Relation to the note's two packagings of `ρ = 1`

* **Elliptic surface `E`** (rank-10 lattice `NSQ`, Shioda–Tate): Gal-invariants are
  `ℚ[O] ⊕ ℚ[F]` after the MW summand contributes none, so `ρ(E) = 2`. Transferred by
  `rho_eq_two_of_nineCycleNSModel` when the full lattice is identified with the 9-cycle action.
* **Del Pezzo `S`** (contract the zero section): the note packages
  `ρ(S) = 1 + dim Fix(zeroSum)`. Transferred by `rho_eq_one_of_delPezzoNineCycleModel` and the
  monodromy variant `rho_eq_one_of_S9NSModel`.
-/

@[expose] public section
noncomputable section

open AlgebraicGeometry Scheme
open LinearMap (BilinForm)
open LinearMap.BilinForm
open ExplicitUnirational.NSLattice
open Equiv Equiv.Perm
open TensorProduct

universe u

namespace ExplicitUnirational.Divisors

/-! ## Rationalized class group -/

/-- Rationalized Weil class group: `ℚ ⊗[ℤ] Cl(X)`.

Ordered as `ℚ ⊗[ℤ] _` so the left `Module ℚ` instance fires (Mathlib's
`TensorProduct.leftModule`). On a smooth rational surface one expects
`NS(X) = Pic(X) = Cl(X)`, so this type stands in for the rational Néron–Severi space of the
note. That comparison is **not** proved here; it is part of the identification hypothesis when
the note's statements are read geometrically. -/
public abbrev ClassGroupQ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] : Type u :=
  ℚ ⊗[ℤ] ClassGroup X

/-! ## Axiomatic intersection form (hypothesis, not a construction) -/

/-- A scheme carries an **intersection form** on its rational class group.

This is a **hypothesis**, not a construction: Mathlib has no intersection theory of divisors.
Downstream results that need a pairing take `[HasIntersectionForm X]` (or an explicit field of
an identification structure) rather than synthesizing a form from scheme data.

For a smooth projective surface the intended interpretation is the intersection pairing on
`NS(X) ⊗ ℚ ≅ ClassGroupQ X` (under the rational-surface comparison above). -/
public class HasIntersectionForm (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] where
  /-- Symmetric bilinear intersection form on `ClassGroupQ X`. -/
  form : BilinForm ℚ (ClassGroupQ X)
  /-- Symmetry of the intersection form. -/
  isSymm : form.IsSymm

/-- The intersection form attached to a `HasIntersectionForm` instance. -/
public abbrev intersectionFormQ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [HasIntersectionForm X] : BilinForm ℚ (ClassGroupQ X) :=
  HasIntersectionForm.form

public theorem intersectionFormQ_isSymm (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [HasIntersectionForm X] : (intersectionFormQ X).IsSymm :=
  HasIntersectionForm.isSymm

/-! ## Arithmetic Picard rank relative to a linear action -/

/-- Arithmetic Picard rank relative to a single linear endomorphism: dimension of the fixed
subspace.

Matches definition (1.2) of the note when `V` is `NS(X_{k̄}) ⊗ ℚ` and `σ` is geometric Frobenius
(or a topological generator of the image of `Gal(k̄/k)`). For a full Galois group one uses the
common fixed space under the whole image; see `arithmeticPicardRank_of_action`. -/
public noncomputable def arithmeticPicardRank {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (σ : V →ₗ[ℚ] V) : ℕ :=
  Module.finrank ℚ (LinearMap.fixedSubmodule σ)

/-- Fixed subspace under a family of linear endomorphisms (e.g. the image of a Galois
representation). -/
public def fixedBy {V : Type*} [AddCommGroup V] [Module ℚ V] {ι : Type*}
    (σ : ι → (V →ₗ[ℚ] V)) : Submodule ℚ V :=
  ⨅ i : ι, LinearMap.fixedSubmodule (σ i)

/-- Arithmetic Picard rank relative to a family of endomorphisms: dimension of the common fixed
space. -/
public noncomputable def arithmeticPicardRank_of_action {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {ι : Type*} (σ : ι → (V →ₗ[ℚ] V)) : ℕ :=
  Module.finrank ℚ (fixedBy σ)

/-! ## Transfer of fixed subspaces along intertwining equivalences -/

/-- An intertwining linear equivalence maps fixed points of `f` onto fixed points of `g`. -/
public theorem map_mem_fixedSubmodule_of_comp_eq {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : V ≃ₗ[ℚ] W) (f : V →ₗ[ℚ] V) (g : W →ₗ[ℚ] W)
    (hconj : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap)
    {v : V} (hv : v ∈ LinearMap.fixedSubmodule f) :
    e v ∈ LinearMap.fixedSubmodule g := by
  rw [LinearMap.mem_fixedSubmodule_iff] at hv ⊢
  have h := congrArg (fun φ : V →ₗ[ℚ] W => φ v) hconj
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [hv] at h
  exact h.symm

/-- Symmetrically, fixed points pull back along an intertwining equivalence. -/
public theorem mem_fixedSubmodule_of_map_mem {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : V ≃ₗ[ℚ] W) (f : V →ₗ[ℚ] V) (g : W →ₗ[ℚ] W)
    (hconj : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap)
    {v : V} (hv : e v ∈ LinearMap.fixedSubmodule g) :
    v ∈ LinearMap.fixedSubmodule f := by
  rw [LinearMap.mem_fixedSubmodule_iff] at hv ⊢
  have h := congrArg (fun φ : V →ₗ[ℚ] W => φ v) hconj
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  have : e (f v) = e v := by rw [h, hv]
  exact e.injective this

/-- The image of `fixedSubmodule f` under an intertwining equivalence is `fixedSubmodule g`. -/
public theorem map_fixedSubmodule_eq {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : V ≃ₗ[ℚ] W) (f : V →ₗ[ℚ] V) (g : W →ₗ[ℚ] W)
    (hconj : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) :
    (LinearMap.fixedSubmodule f).map (e : V →ₗ[ℚ] W) = LinearMap.fixedSubmodule g := by
  ext w
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact map_mem_fixedSubmodule_of_comp_eq e f g hconj hv
  · intro hw
    refine ⟨e.symm w, ?_, by simp⟩
    exact mem_fixedSubmodule_of_map_mem e f g hconj (by simpa using hw)

/-- Linear equivalence of fixed submodules induced by an intertwining equivalence. -/
public def fixedSubmoduleCongr {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : V ≃ₗ[ℚ] W) (f : V →ₗ[ℚ] V) (g : W →ₗ[ℚ] W)
    (hconj : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) :
    LinearMap.fixedSubmodule f ≃ₗ[ℚ] LinearMap.fixedSubmodule g :=
  (e.submoduleMap (LinearMap.fixedSubmodule f)).trans
    (LinearEquiv.ofEq _ _ (map_fixedSubmodule_eq e f g hconj))

/-- Fixed-subspace dimensions agree under intertwining linear equivalences. -/
public theorem finrank_fixedSubmodule_eq_of_comp_eq {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]
    (e : V ≃ₗ[ℚ] W) (f : V →ₗ[ℚ] V) (g : W →ₗ[ℚ] W)
    (hconj : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) :
    Module.finrank ℚ (LinearMap.fixedSubmodule f) =
      Module.finrank ℚ (LinearMap.fixedSubmodule g) :=
  LinearEquiv.finrank_eq (fixedSubmoduleCongr e f g hconj)

/-- Arithmetic Picard ranks agree under intertwining linear equivalences. -/
public theorem arithmeticPicardRank_eq_of_comp_eq {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]
    (e : V ≃ₗ[ℚ] W) (f : V →ₗ[ℚ] V) (g : W →ₗ[ℚ] W)
    (hconj : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) :
    arithmeticPicardRank f = arithmeticPicardRank g :=
  finrank_fixedSubmodule_eq_of_comp_eq e f g hconj

/-! ## Model fixed ranks on the combinatorial lattice -/

/-- Sum of the nine exceptional classes. -/
public def sumE : NSQ := ∑ i : Fin 9, E i

@[simp] public theorem sumE_none : sumE none = 0 := by
  simp [sumE, E, Finset.sum_apply]

@[simp] public theorem sumE_some (i : Fin 9) : sumE (some i) = 1 := by
  simp [sumE, E, Finset.sum_apply, Pi.single_apply]

/-- The 9-cycle fixes `H`. -/
public theorem H_mem_fixed_finRotate :
    H ∈ LinearMap.fixedSubmodule (permAction (finRotate 9)) := by
  rw [LinearMap.mem_fixedSubmodule_iff, permAction_H]

/-- The 9-cycle fixes `∑ Eᵢ` (it permutes the summands). -/
public theorem sumE_mem_fixed_finRotate :
    sumE ∈ LinearMap.fixedSubmodule (permAction (finRotate 9)) := by
  rw [LinearMap.mem_fixedSubmodule_iff]
  funext idx
  cases idx with
  | none => simp [permAction, sumE, E, Finset.sum_apply]
  | some k =>
    -- permAction σ sumE (some k) = sumE (some (σ.symm k)) = 1 = sumE (some k)
    simp [permAction, sumE_some]

/-- Coordinate projection from the fixed subspace of the 9-cycle to `ℚ × ℚ`:
`(H-coefficient, common exceptional coefficient)`. -/
public def fixedFinRotateToCoord :
    LinearMap.fixedSubmodule (permAction (finRotate 9)) →ₗ[ℚ] ℚ × ℚ where
  toFun v := (v.val none, v.val (some 0))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Membership: linear combinations of the two fixed vectors remain fixed. -/
public theorem smul_H_add_smul_sumE_mem_fixed (a b : ℚ) :
    a • H + b • sumE ∈ LinearMap.fixedSubmodule (permAction (finRotate 9)) := by
  have hH := H_mem_fixed_finRotate
  have hs := sumE_mem_fixed_finRotate
  rw [LinearMap.mem_fixedSubmodule_iff] at hH hs ⊢
  rw [map_add, map_smul, map_smul, hH, hs]

/-- Reconstruct a fixed vector from its two coordinates. -/
public def coordToFixedFinRotate :
    ℚ × ℚ →ₗ[ℚ] LinearMap.fixedSubmodule (permAction (finRotate 9)) where
  toFun ab := ⟨ab.1 • H + ab.2 • sumE, smul_H_add_smul_sumE_mem_fixed ab.1 ab.2⟩
  map_add' x y := Subtype.ext <| by
    change (x.1 + y.1) • H + (x.2 + y.2) • sumE =
      (x.1 • H + x.2 • sumE) + (y.1 • H + y.2 • sumE)
    module
  map_smul' c x := Subtype.ext <| by
    change (c • x.1) • H + (c • x.2) • sumE = c • (x.1 • H + x.2 • sumE)
    module

/-- On the fixed subspace of the 9-cycle, all exceptional coordinates are equal. -/
public theorem fixed_finRotate_exceptional_const
    (v : LinearMap.fixedSubmodule (permAction (finRotate 9))) (i : Fin 9) :
    v.val (some i) = v.val (some 0) := by
  have hv : permAction (finRotate 9) v.val = v.val :=
    (LinearMap.mem_fixedSubmodule_iff).1 v.property
  have hstep : ∀ k : Fin 9, v.val (some ((finRotate 9) k)) = v.val (some k) := by
    intro k
    have := congrFun hv (some ((finRotate 9) k))
    change v.val (some ((finRotate 9).symm ((finRotate 9) k))) =
      v.val (some ((finRotate 9) k)) at this
    simpa using this.symm
  have hpow : ∀ n : ℕ, v.val (some (((finRotate 9) ^ n) 0)) = v.val (some 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, hstep, ih]
  obtain ⟨n, hn⟩ := ExplicitUnirational.NineCycle.isCycle_finRotate_nine.exists_pow_eq
    (by
      have hsup := support_finRotate_of_le (by decide : 2 ≤ 9)
      exact mem_support.mp (by simp [hsup] : (0 : Fin 9) ∈ support (finRotate 9)))
    (by
      have hsup := support_finRotate_of_le (by decide : 2 ≤ 9)
      exact mem_support.mp (by simp [hsup] : i ∈ support (finRotate 9)))
  calc
    v.val (some i) = v.val (some (((finRotate 9) ^ n) 0)) := by rw [hn]
    _ = v.val (some 0) := hpow n

public theorem fixedFinRotateToCoord_leftInverse
    (v : LinearMap.fixedSubmodule (permAction (finRotate 9))) :
    coordToFixedFinRotate (fixedFinRotateToCoord v) = v := by
  apply Subtype.ext
  funext idx
  cases idx with
  | none =>
    simp only [coordToFixedFinRotate, fixedFinRotateToCoord, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, H, sumE_none, mul_zero, add_zero]
    simp
  | some i =>
    have hi := fixed_finRotate_exceptional_const v i
    simp only [coordToFixedFinRotate, fixedFinRotateToCoord, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, H, sumE_some, Pi.single_apply]
    simp [hi]

public theorem fixedFinRotateToCoord_rightInverse (ab : ℚ × ℚ) :
    fixedFinRotateToCoord (coordToFixedFinRotate ab) = ab := by
  ext
  · simp [fixedFinRotateToCoord, coordToFixedFinRotate, H, sumE_none]
  · simp [fixedFinRotateToCoord, coordToFixedFinRotate, H, sumE_some]

/-- The fixed subspace of the 9-cycle on the full rank-10 lattice is linearly equivalent to
`ℚ × ℚ` (coordinates: coefficient of `H`, common coefficient of the `Eᵢ`). -/
public def fixedFinRotateEquivCoord :
    LinearMap.fixedSubmodule (permAction (finRotate 9)) ≃ₗ[ℚ] ℚ × ℚ where
  toLinearMap := fixedFinRotateToCoord
  invFun := coordToFixedFinRotate
  left_inv := fixedFinRotateToCoord_leftInverse
  right_inv := fixedFinRotateToCoord_rightInverse

/-- Fixed subspace of the 9-cycle on the full rank-10 lattice is 2-dimensional
(`span{H, ∑ Eᵢ}`). This is the lattice model for `ρ(E) = 2` on the elliptic surface
(note Prop. 4.2: `ρ_{𝔽₅}(E₅) = 2`). -/
public theorem finrank_fixed_permAction_finRotate :
    Module.finrank ℚ (LinearMap.fixedSubmodule (permAction (finRotate 9))) = 2 := by
  rw [LinearEquiv.finrank_eq fixedFinRotateEquivCoord, Module.finrank_prod]
  have h1 : Module.finrank ℚ ℚ = 1 := Module.finrank_self (R := ℚ)
  omega

/-- Lattice model for `ρ(E) = 2`: arithmetic Picard rank of the 9-cycle on full `NSQ`. -/
public theorem arithmeticPicardRank_NSQ_finRotate :
    arithmeticPicardRank (permAction (finRotate 9)) = 2 :=
  finrank_fixed_permAction_finRotate

/-! ## Identification structures (hypotheses) -/

/-- **Hypothesis**: the rational class group of `X` is identified with the combinatorial NS
lattice as a module with form, and a designated endomorphism (geometric Frobenius) is
intertwined with the model 9-cycle action on the full rank-10 lattice.

This is the packaging for the **elliptic surface** `E` of the note (`ρ(E) = 2`). It does **not**
by itself give `ρ = 1` for the del Pezzo obtained by contracting the zero section; see
`IsDelPezzoNineCycleModel`. -/
public structure IsNineCycleNSModel (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] where
  /-- Intersection form on `ClassGroupQ X` (axiomatic). -/
  form : BilinForm ℚ (ClassGroupQ X)
  /-- Symmetry of the form. -/
  isSymm : form.IsSymm
  /-- Linear identification with the combinatorial lattice. -/
  equiv : ClassGroupQ X ≃ₗ[ℚ] NSQ
  /-- The identification is an isometry for the intersection forms. -/
  form_compat : ∀ x y : ClassGroupQ X,
    intersectionForm (equiv x) (equiv y) = form x y
  /-- Endomorphism modelling geometric Frobenius on `ClassGroupQ X`. -/
  frobenius : ClassGroupQ X →ₗ[ℚ] ClassGroupQ X
  /-- Frobenius is intertwined with the model 9-cycle action. -/
  frobenius_compat :
    equiv.toLinearMap ∘ₗ frobenius = permAction (finRotate 9) ∘ₗ equiv.toLinearMap

/-- Under a nine-cycle NS model identification, `ClassGroupQ X` is finite-dimensional of rank
10. -/
public theorem IsNineCycleNSModel.finrank_eq_ten {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (M : IsNineCycleNSModel X) :
    Module.finrank ℚ (ClassGroupQ X) = 10 := by
  haveI : FiniteDimensional ℚ (ClassGroupQ X) :=
    FiniteDimensional.of_injective M.equiv.toLinearMap M.equiv.injective
  rw [LinearEquiv.finrank_eq M.equiv, finrank_NSQ]

/-- Finite-dimensionality of `ClassGroupQ X` under a nine-cycle model. -/
public theorem IsNineCycleNSModel.finiteDimensional {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (M : IsNineCycleNSModel X) :
    FiniteDimensional ℚ (ClassGroupQ X) :=
  FiniteDimensional.of_injective M.equiv.toLinearMap M.equiv.injective

/-- **Conditional theorem (elliptic-surface packaging).** If `ClassGroupQ X` is identified with
`NSQ` as a formed module with 9-cycle action, then the arithmetic Picard rank relative to that
action is `2` (note Prop. 4.2: `ρ(E) = 2`).

Stated in terms of `finrank` of the fixed submodule so the finite-dimensionality instance
(from the identification) need not appear in the theorem binder list. -/
public theorem rho_eq_two_of_nineCycleNSModel {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (M : IsNineCycleNSModel X) :
    Module.finrank ℚ (LinearMap.fixedSubmodule M.frobenius) = 2 := by
  haveI : FiniteDimensional ℚ (ClassGroupQ X) := M.finiteDimensional
  have h := arithmeticPicardRank_eq_of_comp_eq M.equiv M.frobenius (permAction (finRotate 9))
    M.frobenius_compat
  -- h : arithmeticPicardRank M.frobenius = arithmeticPicardRank (permAction ...)
  change arithmeticPicardRank M.frobenius = 2
  rw [h]
  exact arithmeticPicardRank_NSQ_finRotate

/-- **Hypothesis for the del Pezzo `ρ = 1` packaging of the note.**

The note computes `ρ(S) = 1 + dim Fix(zeroSum)` after contracting a rational zero section
(Prop. 4.2, (5.18)). This structure packages exactly that bookkeeping as hypotheses on
`ClassGroupQ X`:

* a Frobenius-fixed line (the anticanonical / residual class after contraction);
* a complementary summand identified with the zero-sum representation, on which Frobenius acts
  as the 9-cycle;
* the claim that Gal-invariants are exactly the span of that line
  (equivalently: the zero-sum summand contributes no fixed vectors, which follows from the
  lattice computation once the action is identified).

None of these is constructed from geometry here. The last field `invariants_eq` is the
geometric input that Shioda–Tate + fibre-irreducibility + contraction of `O` supply in the note.
-/
public structure IsDelPezzoNineCycleModel (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] where
  /-- Anticanonical (or residual) class, expected to span the unique invariant line. -/
  kappa : ClassGroupQ X
  /-- Endomorphism modelling geometric Frobenius. -/
  frobenius : ClassGroupQ X →ₗ[ℚ] ClassGroupQ X
  /-- `kappa` is Frobenius-fixed. -/
  frobenius_kappa : frobenius kappa = kappa
  /-- Embedding of the combinatorial zero-sum summand into `ClassGroupQ X`. -/
  zeroSumIncl : zeroSum →ₗ[ℚ] ClassGroupQ X
  /-- The embedding is injective (linear independence of the MW / E₈ part). -/
  zeroSumIncl_injective : Function.Injective zeroSumIncl
  /-- Frobenius preserves the summand and acts as the model 9-cycle. -/
  frobenius_zeroSum :
    ∀ v : zeroSum,
      frobenius (zeroSumIncl v) =
        zeroSumIncl
          ⟨permOnNine (finRotate 9) (v : Fin 9 → ℚ),
            permOnNine_maps_zeroSum (finRotate 9) v.property⟩
  /-- **Key geometric hypothesis**: Frobenius-fixed classes are exactly the line `ℚ · kappa`.
      In the note this follows from Shioda–Tate (no reducible fibres) plus the vanishing of
      fixed vectors on the zero-sum MW summand (lattice computation) after contracting `O`. -/
  invariants_eq : LinearMap.fixedSubmodule frobenius = ℚ ∙ kappa
  /-- `kappa` is nonzero (so the invariant line is genuinely 1-dimensional). -/
  kappa_ne_zero : kappa ≠ 0

/-- **Primary conditional theorem.** Under the del Pezzo nine-cycle identification hypothesis,
the arithmetic Picard rank relative to Frobenius is `1` (note Prop. 4.2 / (5.18): `ρ = 1`).

This is the interface that turns `NSLattice.arithmeticPicardRank_one` into a statement about
schemes. The geometric content is entirely in the fields of `IsDelPezzoNineCycleModel`; the
proof here is linear algebra. -/
public theorem rho_eq_one_of_delPezzoNineCycleModel {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (M : IsDelPezzoNineCycleModel X)
    [FiniteDimensional ℚ (ClassGroupQ X)] :
    arithmeticPicardRank M.frobenius = 1 := by
  have hfixed := M.invariants_eq
  have hne := M.kappa_ne_zero
  have hrank : Module.finrank ℚ (ℚ ∙ M.kappa) = 1 := finrank_span_singleton hne
  rw [arithmeticPicardRank, hfixed, hrank]

/-- Under the del Pezzo model, the lattice computation implies that no nonzero zero-sum vector
is Frobenius-fixed (transport of `fixedZeroSum_finRotate_eq_bot`). -/
public theorem IsDelPezzoNineCycleModel.zeroSum_fixed_trivial {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (M : IsDelPezzoNineCycleModel X)
    (v : zeroSum)
    (hv : M.frobenius (M.zeroSumIncl v) = M.zeroSumIncl v) : v = 0 := by
  have h' := M.frobenius_zeroSum v
  rw [h'] at hv
  have hinj := M.zeroSumIncl_injective hv
  -- hinj : ⟨permOnNine …, _⟩ = v, so permOnNine v = v as functions
  have hperm : permOnNine (finRotate 9) (v : Fin 9 → ℚ) = (v : Fin 9 → ℚ) :=
    congrArg Subtype.val hinj
  have hfix : (v : Fin 9 → ℚ) ∈ fixedZeroSum (finRotate 9) :=
    ⟨(LinearMap.mem_fixedSubmodule_iff).2 hperm, v.property⟩
  have hbot := fixedZeroSum_finRotate_eq_bot
  have : (v : Fin 9 → ℚ) = 0 := by
    have hvbot : (v : Fin 9 → ℚ) ∈ (⊥ : Submodule ℚ (Fin 9 → ℚ)) := by
      rw [← hbot]; exact hfix
    simpa using hvbot
  exact Subtype.ext this

/-- **Hypothesis**: monodromy / Galois acts through the full `S₉` on a zero-sum summand of
`ClassGroupQ X`, as in note §5.4 over `ℂ(t)`. -/
public structure IsS9NSModel (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] where
  /-- Anticanonical (or residual) class. -/
  kappa : ClassGroupQ X
  /-- Linear action of `S₉` on `ClassGroupQ X`. -/
  action : Perm (Fin 9) → (ClassGroupQ X →ₗ[ℚ] ClassGroupQ X)
  /-- Multiplicativity of the action (representation). -/
  action_mul : ∀ σ τ : Perm (Fin 9), action (σ * τ) = action σ ∘ₗ action τ
  /-- Unitality. -/
  action_one : action 1 = LinearMap.id
  /-- `kappa` is `S₉`-invariant. -/
  action_kappa : ∀ σ : Perm (Fin 9), action σ kappa = kappa
  /-- Embedding of the combinatorial zero-sum summand. -/
  zeroSumIncl : zeroSum →ₗ[ℚ] ClassGroupQ X
  zeroSumIncl_injective : Function.Injective zeroSumIncl
  /-- Action on the summand matches `permOnNine`. -/
  action_zeroSum :
    ∀ (σ : Perm (Fin 9)) (v : zeroSum),
      action σ (zeroSumIncl v) =
        zeroSumIncl ⟨permOnNine σ (v : Fin 9 → ℚ), permOnNine_maps_zeroSum σ v.property⟩
  /-- Invariants under the full `S₉` equal `ℚ · kappa`
      (i.e. the zero-sum summand contributes no invariants — note §5.4). -/
  invariants_eq : fixedBy action = ℚ ∙ kappa
  kappa_ne_zero : kappa ≠ 0

/-- **Conditional theorem (monodromy packaging).** Under the full `S₉` identification
hypothesis of note §5.4, the arithmetic Picard rank is `1`. -/
public theorem rho_eq_one_of_S9NSModel {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (M : IsS9NSModel X)
    [FiniteDimensional ℚ (ClassGroupQ X)] :
    arithmeticPicardRank_of_action M.action = 1 := by
  have hfixed := M.invariants_eq
  have hne := M.kappa_ne_zero
  have hrank : Module.finrank ℚ (ℚ ∙ M.kappa) = 1 := finrank_span_singleton hne
  rw [arithmeticPicardRank_of_action, hfixed, hrank]

/-- Re-export: the lattice computation that powers the del Pezzo interface
(`1 + dim Fix(zeroSum on 9-cycle) = 1`). -/
public theorem lattice_rho_eq_one :
    Module.finrank ℚ (fixedZeroSum (finRotate 9)) + 1 = 1 :=
  arithmeticPicardRank_one

/-! ## Blow-up of `ℙ²`: precise obligations (not formalized) -/

/-- Checklist of ingredients that would be required to **construct** (rather than assume) an
identification of `ClassGroupQ X` with `NSLattice` for `X = Bl_{p₁,…,p₉} ℙ²_L`.

None of these is available in Mathlib v4.32.1 or in this repository. The structure is a
documentation device: its fields name missing theorems. The trivial inhabitant below does
**not** mean any geometric identification has been proved — every field is the unit type. -/
public structure BlowUpIdentificationObligations where
  /-- Blow-up of a scheme along a closed subscheme (or along a finite set of closed points). -/
  hasBlowUp : True := trivial
  /-- The blow-up of `ℙ²` at nine distinct points is an integral locally Noetherian scheme. -/
  blowUp_integral : True := trivial
  /-- Exceptional divisors `Eᵢ` are prime Weil divisors (codimension-one points). -/
  exceptional_codim_one : True := trivial
  /-- Pullback of a line `H` is a Weil divisor class. -/
  pullback_line : True := trivial
  /-- The classes `H, E₁, …, E₉` freely generate `ClassGroup` (or `Pic`) of the blow-up. -/
  free_basis : True := trivial
  /-- Intersection numbers: `H² = 1`, `Eᵢ² = -1`, cross terms zero. -/
  intersection_numbers : True := trivial
  /-- Canonical class formula `K = -3H + ∑ Eᵢ`. -/
  canonical_class : True := trivial
  /-- Permutation of base points induces the `S₉` action on `ClassGroupQ` matching
      `NSLattice.permAction`. -/
  gal_action : True := trivial
  /-- Geometric Frobenius (when the base points form a single Galois orbit of size 9) acts as
      `finRotate 9`. -/
  frobenius_is_nine_cycle : True := trivial
  /-- After choosing a zero section and applying Shioda–Tate with irreducible fibres, the MW
      summand is the zero-sum representation (note (4.4), (5.16)). -/
  shioda_tate_zero_sum : True := trivial
  /-- Contracting a rational (−1)-section yields the del Pezzo and drops one invariant class
      (note Prop. 4.2, (5.18)). -/
  contract_section : True := trivial

/-- Documentation-only inhabitant of the blow-up checklist. Every field is `True`; this does
**not** construct a geometric identification. -/
public theorem BlowUpIdentificationObligations.docs : BlowUpIdentificationObligations := {}

/-! ## Form-isometry packaging -/

/-- Convert an `IsNineCycleNSModel` into a Mathlib `IsometryEquiv` between the axiomatic form
and the combinatorial intersection form. -/
public def IsNineCycleNSModel.toIsometryEquiv {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (M : IsNineCycleNSModel X) :
    M.form.IsometryEquiv intersectionForm :=
  { toLinearEquiv := M.equiv
    map_app' := fun x y => M.form_compat x y }

/-! ## Axiom audit -/

#print axioms arithmeticPicardRank_eq_of_comp_eq
#print axioms finrank_fixed_permAction_finRotate
#print axioms rho_eq_two_of_nineCycleNSModel
#print axioms rho_eq_one_of_delPezzoNineCycleModel
#print axioms rho_eq_one_of_S9NSModel
#print axioms lattice_rho_eq_one
#print axioms fixedSubmoduleCongr
#print axioms IsDelPezzoNineCycleModel.zeroSum_fixed_trivial

end ExplicitUnirational.Divisors
