/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Weil divisors and the divisor class group

This module constructs the **Weil divisor class group** of an integral locally Noetherian scheme,
following the classical free-abelian-group route rather than invertible sheaves.

## Why Weil divisors (and not Picard-as-invertible-sheaves)

Mathlib has `SheafOfModules` and `IsLocallyFree`, but **no monoidal/tensor structure** on sheaves
of modules and **no rank predicate**. The group law on `Pic` as invertible sheaves modulo
isomorphism is therefore unavailable. By contrast:

* `AlgebraicGeometry.Scheme.ord` / `ordHom` (in `OrderOfVanishing.lean`) give the order of
  vanishing of a rational function at a codimension-one point, as a monoid-with-zero homomorphism;
* `AlgebraicCycle` (locally finite support functions `X → R`) is the ambient cycle type, of which
  Weil divisors are the codimension-one case.

For the surfaces in the note (`docs/note.txt` §4.2, §5.4) the surface is rational, so
`Pic⁰ = 0` and `NS(X) = Pic(X) = Cl(X)`. The note needs only the divisor class group.

## Main definitions

* `CodimOne X` — points of codimension one (`Order.coheight z = 1`).
* `Div X` — Weil divisors: free abelian group `CodimOne X →₀ ℤ` on those points.
* `HasFinitePrincipalSupport f` — the set of codim-1 points where `ord f ≠ 0` is finite.
* `finitePrincipalUnits X` — the subgroup of `X.functionFieldˣ` consisting of units with finite
  principal support (a subgroup by multiplicativity of `ord`).
* `principalDivisorOf f hf` — `Σ_z ord_z(f) · [z]`, for a unit with finite support.
* `principalDivisor` — the monoid homomorphism
  `finitePrincipalUnits X →* Multiplicative (Div X)`.
* `PrincipalDivisors X` — the image of `principalDivisor` as an `AddSubgroup` of `Div X`.
* `ClassGroup X` — `Div X ⧸ PrincipalDivisors X`.
* `LinearEquiv` — linear equivalence of divisors (`D₁ - D₂` principal).

## The finiteness hypothesis (the crux)

A nonzero rational function on an integral locally Noetherian scheme has **locally finite** zeros
and poles among codimension-one points; on a **quasi-compact** (e.g. Noetherian) scheme the support
is therefore finite, so every unit lies in `finitePrincipalUnits` and `principalDivisor` extends
to a map out of all of `X.functionFieldˣ`.

Mathlib currently provides:

* `Scheme.ord` / `ordHom` and `ord_mul` (multiplicative);
* `Ideal.finite_minimalPrimes_of_isNoetherianRing` and Krull's height theorem
  (`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`);
* the identification `idealHeight_eq_coheight` on `Spec R`.

What is **not** yet available is the glue: that for `f ∈ X.functionFieldˣ`, the set
`{z | coheight z = 1 ∧ ord f z ≠ 0}` is (locally) finite. The missing steps, under the
hypotheses `[IsIntegral X] [IsLocallyNoetherian X]` (and quasi-compactness for *global*
finiteness), are:

1. On an affine open `U ≅ Spec A` with `A` a Noetherian domain, write `f` as a ratio `a/b` in
   `Frac(A)` and identify `ord` at height-one primes of `A` with the order coming from
   `Ring.ordFrac` on the stalk (or DVR localization).
2. Show that primes of height one at which the order is nonzero are among the minimal primes over
   `(a)` or `(b)`, hence form a finite set by Krull + finite minimal primes.
3. Gluing: local finiteness on an affine open cover, plus quasi-compactness of `X`, yields global
   finiteness.

Until that glue is formalized, every construction that produces an element of `Div X` from a
rational function carries `HasFinitePrincipalSupport` (or membership in `finitePrincipalUnits`)
explicitly. The class group is still well-defined: it quotients by exactly those principal
divisors that exist as finitely supported cycles.

Do **not** confuse this with quietly assuming finiteness inside a proof: the hypothesis is in the
type of `principalDivisorOf` / the domain of `principalDivisor`.

## Out of scope

Intersection pairing, blow-ups, and the computation of `Cl` for the specific surface of the note
are separate work packages.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry Scheme

universe u

namespace ExplicitUnirational.Divisors

variable {X : Scheme.{u}}

/-! ## Codimension-one points and Weil divisors -/

/-- Codimension-one points of a scheme: points of specialization-coheight one. -/
public abbrev CodimOne (X : Scheme.{u}) : Type u :=
  {z : X // Order.coheight z = 1}

/-- The group of Weil divisors on `X`: the free abelian group on codimension-one points.

This is the classical definition (Stacks 0AYR restricted to finite support). On a quasi-compact
locally Noetherian scheme, local finiteness of supports is equivalent to finiteness, so this
agrees with the `AlgebraicCycle` formulation restricted to codimension one. -/
public abbrev Div (X : Scheme.{u}) : Type u :=
  CodimOne X →₀ ℤ

namespace Div

/-- The prime (irreducible) Weil divisor associated with a codimension-one point. -/
public def prime (z : X) (hz : Order.coheight z = 1) : Div X :=
  Finsupp.single ⟨z, hz⟩ (1 : ℤ)

/-- Coefficient of a Weil divisor at a codimension-one point. -/
public def coeff (D : Div X) (z : X) (hz : Order.coheight z = 1) : ℤ :=
  D ⟨z, hz⟩

@[simp] public theorem coeff_prime_self (z : X) (hz : Order.coheight z = 1) :
    coeff (prime z hz) z hz = 1 := by
  simp [coeff, prime]

@[simp] public theorem coeff_zero (z : X) (hz : Order.coheight z = 1) :
    coeff (0 : Div X) z hz = 0 := by
  simp [coeff]

@[simp] public theorem coeff_add (D₁ D₂ : Div X) (z : X) (hz : Order.coheight z = 1) :
    coeff (D₁ + D₂) z hz = coeff D₁ z hz + coeff D₂ z hz := by
  simp [coeff]

@[simp] public theorem coeff_neg (D : Div X) (z : X) (hz : Order.coheight z = 1) :
    coeff (-D) z hz = -coeff D z hz := by
  simp [coeff]

@[simp] public theorem coeff_sub (D₁ D₂ : Div X) (z : X) (hz : Order.coheight z = 1) :
    coeff (D₁ - D₂) z hz = coeff D₁ z hz - coeff D₂ z hz := by
  simp [coeff]

public theorem ext_coeff {D₁ D₂ : Div X}
    (h : ∀ z hz, coeff D₁ z hz = coeff D₂ z hz) : D₁ = D₂ := by
  ext ⟨z, hz⟩
  exact h z hz

end Div

/-! ## Multiplicativity of `ord` on units -/

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- Order of vanishing of `1` is zero at every point. -/
public theorem ord_one (z : X) : ord (1 : X.functionField) z = 0 := by
  by_cases hz : Order.coheight z = 1
  · rw [ord_eq_iff hz (one_ne_zero (α := X.functionField))]
    exact map_one (ordHom z hz)
  · exact ord_eq_zero_of_coheight_neq_one hz _

/-- Order of vanishing of an inverse: `ord(f⁻¹) = -ord(f)` for `f ≠ 0`. -/
public theorem ord_inv {f : X.functionField} (hf : f ≠ 0) (z : X) :
    ord (f⁻¹) z = -ord f z := by
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hsum : ord (f * f⁻¹) z = ord f z + ord f⁻¹ z := ord_mul hf hfi
  have h1 : ord (f * f⁻¹) z = 0 := by
    rw [mul_inv_cancel₀ hf, ord_one]
  omega

/-- Multiplicativity of `ord` on units of the function field. -/
public theorem ord_units_mul (f g : X.functionFieldˣ) (z : X) :
    ord ((f * g : X.functionFieldˣ) : X.functionField) z =
      ord (f : X.functionField) z + ord (g : X.functionField) z :=
  ord_mul (Units.ne_zero f) (Units.ne_zero g)

/-- `ord` of the inverse of a unit. -/
public theorem ord_units_inv (f : X.functionFieldˣ) (z : X) :
    ord ((f⁻¹ : X.functionFieldˣ) : X.functionField) z = -ord (f : X.functionField) z := by
  rw [Units.val_inv_eq_inv_val]
  exact ord_inv (Units.ne_zero f) z

/-- Order of a unit of the function field, as a group homomorphism into `Multiplicative ℤ`. -/
public def ordUnitsHom (z : X) (_hz : Order.coheight z = 1) :
    X.functionFieldˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (ord (f : X.functionField) z)
  map_one' := by simp [ord_one]
  map_mul' f g := by
    simp only [Units.val_mul]
    rw [ord_mul (Units.ne_zero f) (Units.ne_zero g), ofAdd_add]

@[simp] public theorem ordUnitsHom_apply (z : X) (hz : Order.coheight z = 1)
    (f : X.functionFieldˣ) :
    ordUnitsHom z hz f = Multiplicative.ofAdd (ord (f : X.functionField) z) :=
  rfl

/-! ## Finite principal support -/

/-- The set of codimension-one points at which `f` has nonzero order of vanishing. -/
public def principalSupport (f : X.functionField) : Set (CodimOne X) :=
  Function.support fun z : CodimOne X => ord f z.1

/-- A rational function has **finite principal support** if only finitely many codimension-one
points are zeros or poles.

This is the content of the classical finiteness of zeros and poles of a nonzero rational function
on an integral Noetherian scheme. It is carried as an explicit hypothesis until the affine glue
described in the module docstring is available in Mathlib / this project. -/
public def HasFinitePrincipalSupport (f : X.functionField) : Prop :=
  (principalSupport (X := X) f).Finite

public theorem hasFinitePrincipalSupport_iff (f : X.functionField) :
    HasFinitePrincipalSupport (X := X) f ↔
      (Function.support fun z : CodimOne X => ord f z.1).Finite :=
  Iff.rfl

public theorem hasFinitePrincipalSupport_one :
    HasFinitePrincipalSupport (X := X) (1 : X.functionField) := by
  unfold HasFinitePrincipalSupport principalSupport
  simp [ord_one]

public theorem hasFinitePrincipalSupport_zero :
    HasFinitePrincipalSupport (X := X) (0 : X.functionField) := by
  unfold HasFinitePrincipalSupport principalSupport
  simp [ord_zero]

public theorem hasFinitePrincipalSupport_mul {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hff : HasFinitePrincipalSupport (X := X) f)
    (hgg : HasFinitePrincipalSupport (X := X) g) :
    HasFinitePrincipalSupport (X := X) (f * g) := by
  unfold HasFinitePrincipalSupport principalSupport at *
  refine (hff.union hgg).subset ?_
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz ⊢
  rw [ord_mul hf hg] at hz
  simp only [Set.mem_union, Function.mem_support, ne_eq]
  by_contra h
  obtain ⟨hf0, hg0⟩ : ord f z.1 = 0 ∧ ord g z.1 = 0 := by
    simpa [not_or] using h
  exact hz (by simp [hf0, hg0])

public theorem hasFinitePrincipalSupport_inv {f : X.functionField} (hf : f ≠ 0)
    (hff : HasFinitePrincipalSupport (X := X) f) :
    HasFinitePrincipalSupport (X := X) f⁻¹ := by
  unfold HasFinitePrincipalSupport principalSupport at *
  have heq :
      (Function.support fun z : CodimOne X => ord f⁻¹ z.1) =
        (Function.support fun z : CodimOne X => ord f z.1) := by
    ext z
    simp [ord_inv hf]
  rwa [heq]

public theorem hasFinitePrincipalSupport_units_mul (f g : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField))
    (hg : HasFinitePrincipalSupport (X := X) (g : X.functionField)) :
    HasFinitePrincipalSupport (X := X) ((f * g : X.functionFieldˣ) : X.functionField) :=
  hasFinitePrincipalSupport_mul (Units.ne_zero f) (Units.ne_zero g) hf hg

public theorem hasFinitePrincipalSupport_units_inv (f : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField)) :
    HasFinitePrincipalSupport (X := X) ((f⁻¹ : X.functionFieldˣ) : X.functionField) := by
  rw [Units.val_inv_eq_inv_val]
  exact hasFinitePrincipalSupport_inv (Units.ne_zero f) hf

/-- Units of the function field whose principal divisors have finite support.

This is a subgroup of `X.functionFieldˣ` by multiplicativity of `ord`. Under the missing
finiteness theorem it equals the full unit group. -/
public def finitePrincipalUnits (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    Subgroup X.functionFieldˣ where
  carrier := {f | HasFinitePrincipalSupport (X := X) (f : X.functionField)}
  one_mem' := hasFinitePrincipalSupport_one
  mul_mem' {f g} hf hg := hasFinitePrincipalSupport_units_mul f g hf hg
  inv_mem' {f} hf := hasFinitePrincipalSupport_units_inv f hf

public theorem mem_finitePrincipalUnits_iff {f : X.functionFieldˣ} :
    f ∈ finitePrincipalUnits X ↔ HasFinitePrincipalSupport (X := X) (f : X.functionField) :=
  Iff.rfl

/-! ## Principal divisors -/

/-- The principal Weil divisor of a unit with finite principal support:
`div(f) = Σ_z ord_z(f) · [z]`. -/
public def principalDivisorOf (f : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField)) : Div X :=
  Finsupp.ofSupportFinite (fun z : CodimOne X => ord (f : X.functionField) z.1) hf

@[simp] public theorem coeff_principalDivisorOf (f : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField))
    (z : X) (hz : Order.coheight z = 1) :
    Div.coeff (principalDivisorOf f hf) z hz = ord (f : X.functionField) z := by
  simp [Div.coeff, principalDivisorOf, Finsupp.ofSupportFinite_coe]

public theorem principalDivisorOf_one :
    principalDivisorOf (X := X) (1 : X.functionFieldˣ) hasFinitePrincipalSupport_one = 0 := by
  apply Div.ext_coeff
  intro z hz
  simp [ord_one]

public theorem principalDivisorOf_mul (f g : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField))
    (hg : HasFinitePrincipalSupport (X := X) (g : X.functionField)) :
    principalDivisorOf (f * g) (hasFinitePrincipalSupport_units_mul f g hf hg) =
      principalDivisorOf f hf + principalDivisorOf g hg := by
  apply Div.ext_coeff
  intro z hz
  simp only [coeff_principalDivisorOf, Div.coeff_add]
  exact ord_units_mul f g z

public theorem principalDivisorOf_inv (f : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField)) :
    principalDivisorOf f⁻¹ (hasFinitePrincipalSupport_units_inv f hf) =
      -principalDivisorOf f hf := by
  apply Div.ext_coeff
  intro z hz
  simp only [coeff_principalDivisorOf, Div.coeff_neg]
  exact ord_units_inv f z

/-- Extract the finiteness hypothesis from membership in `finitePrincipalUnits`. -/
public theorem HasFinitePrincipalSupport.of_mem_finitePrincipalUnits
    {f : X.functionFieldˣ} (hf : f ∈ finitePrincipalUnits X) :
    HasFinitePrincipalSupport (X := X) (f : X.functionField) :=
  hf

/-- The principal-divisor monoid homomorphism on units with finite support.

Codomain is written multiplicatively so the domain keeps its natural multiplicative structure:
`Multiplicative.toAdd (principalDivisor f) = principalDivisorOf ↑f …`. -/
public def principalDivisor :
    finitePrincipalUnits X →* Multiplicative (Div X) where
  toFun f := Multiplicative.ofAdd
    (principalDivisorOf (f : X.functionFieldˣ)
      (HasFinitePrincipalSupport.of_mem_finitePrincipalUnits f.property))
  map_one' := by
    change Multiplicative.ofAdd (principalDivisorOf (1 : X.functionFieldˣ) _) = 1
    rw [ofAdd_eq_one]
    exact principalDivisorOf_one
  map_mul' f g := by
    change Multiplicative.ofAdd (principalDivisorOf (↑f * ↑g : X.functionFieldˣ) _) =
      Multiplicative.ofAdd (principalDivisorOf ↑f _) *
        Multiplicative.ofAdd (principalDivisorOf ↑g _)
    rw [← ofAdd_add]
    congr 1
    exact principalDivisorOf_mul (f : X.functionFieldˣ) (g : X.functionFieldˣ)
      (HasFinitePrincipalSupport.of_mem_finitePrincipalUnits f.property)
      (HasFinitePrincipalSupport.of_mem_finitePrincipalUnits g.property)

@[simp] public theorem principalDivisor_apply (f : finitePrincipalUnits X) :
    Multiplicative.toAdd (principalDivisor f) =
      principalDivisorOf (f : X.functionFieldˣ)
        (HasFinitePrincipalSupport.of_mem_finitePrincipalUnits f.property) :=
  rfl

/-- The subgroup of principal Weil divisors (those in the image of `principalDivisor`). -/
public def PrincipalDivisors (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    AddSubgroup (Div X) where
  carrier := Set.range fun f : finitePrincipalUnits X =>
    Multiplicative.toAdd (principalDivisor f)
  zero_mem' := ⟨1, by
    change Multiplicative.toAdd (principalDivisor (1 : finitePrincipalUnits X)) = 0
    simp [map_one]⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    refine ⟨f * g, ?_⟩
    change Multiplicative.toAdd (principalDivisor (f * g)) =
      Multiplicative.toAdd (principalDivisor f) + Multiplicative.toAdd (principalDivisor g)
    rw [map_mul, toAdd_mul]
  neg_mem' := by
    rintro _ ⟨f, rfl⟩
    refine ⟨f⁻¹, ?_⟩
    change Multiplicative.toAdd (principalDivisor f⁻¹) =
      -Multiplicative.toAdd (principalDivisor f)
    rw [map_inv, toAdd_inv]

public theorem mem_PrincipalDivisors {D : Div X} :
    D ∈ PrincipalDivisors X ↔
      ∃ f : finitePrincipalUnits X, Multiplicative.toAdd (principalDivisor f) = D :=
  Iff.rfl

public theorem principalDivisorOf_mem_PrincipalDivisors (f : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField)) :
    principalDivisorOf f hf ∈ PrincipalDivisors X := by
  refine ⟨⟨f, hf⟩, ?_⟩
  simp [principalDivisor_apply]

/-! ## The divisor class group -/

/-- The **Weil divisor class group** of an integral locally Noetherian scheme:
Weil divisors modulo principal divisors (of finite support). -/
public abbrev ClassGroup (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] : Type u :=
  Div X ⧸ PrincipalDivisors X

/-- Class of a Weil divisor in the class group. -/
public def classOf (D : Div X) : ClassGroup X :=
  QuotientAddGroup.mk D

@[simp] public theorem classOf_add (D₁ D₂ : Div X) :
    classOf (D₁ + D₂) = classOf D₁ + classOf D₂ :=
  rfl

@[simp] public theorem classOf_zero : classOf (0 : Div X) = (0 : ClassGroup X) :=
  rfl

@[simp] public theorem classOf_neg (D : Div X) : classOf (-D) = -classOf D :=
  rfl

@[simp] public theorem classOf_sub (D₁ D₂ : Div X) :
    classOf (D₁ - D₂) = classOf D₁ - classOf D₂ :=
  rfl

public theorem classOf_eq_iff {D₁ D₂ : Div X} :
    classOf D₁ = classOf D₂ ↔ D₁ - D₂ ∈ PrincipalDivisors X :=
  QuotientAddGroup.eq_iff_sub_mem

public theorem classOf_eq_zero_iff {D : Div X} :
    classOf D = (0 : ClassGroup X) ↔ D ∈ PrincipalDivisors X := by
  rw [← sub_zero D, ← classOf_eq_iff, classOf_zero, sub_zero]

/-- The class of a principal divisor is zero. -/
public theorem classOf_principalDivisorOf (f : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField)) :
    classOf (principalDivisorOf f hf) = (0 : ClassGroup X) :=
  (classOf_eq_zero_iff).2 (principalDivisorOf_mem_PrincipalDivisors f hf)

/-- The quotient map `Div X → ClassGroup X` as an additive group homomorphism. -/
public def classHom : Div X →+ ClassGroup X :=
  QuotientAddGroup.mk' (PrincipalDivisors X)

@[simp] public theorem classHom_apply (D : Div X) : classHom D = classOf D :=
  rfl

/-! ## Linear equivalence -/

/-- Two Weil divisors are **linearly equivalent** if their difference is principal. -/
public def LinearEquiv (D₁ D₂ : Div X) : Prop :=
  D₁ - D₂ ∈ PrincipalDivisors X

public theorem linearEquiv_iff_classOf_eq {D₁ D₂ : Div X} :
    LinearEquiv D₁ D₂ ↔ classOf D₁ = classOf D₂ :=
  classOf_eq_iff.symm

public theorem LinearEquiv.refl (D : Div X) : LinearEquiv D D := by
  change D - D ∈ PrincipalDivisors X
  rw [sub_self]
  exact (PrincipalDivisors X).zero_mem

public theorem LinearEquiv.symm {D₁ D₂ : Div X} (h : LinearEquiv D₁ D₂) :
    LinearEquiv D₂ D₁ := by
  change D₂ - D₁ ∈ PrincipalDivisors X
  have h' : D₁ - D₂ ∈ PrincipalDivisors X := h
  have : D₂ - D₁ = -(D₁ - D₂) := by abel
  rw [this]
  exact (PrincipalDivisors X).neg_mem h'

public theorem LinearEquiv.trans {D₁ D₂ D₃ : Div X}
    (h₁₂ : LinearEquiv D₁ D₂) (h₂₃ : LinearEquiv D₂ D₃) :
    LinearEquiv D₁ D₃ := by
  change D₁ - D₃ ∈ PrincipalDivisors X
  have : D₁ - D₃ = (D₁ - D₂) + (D₂ - D₃) := by abel
  rw [this]
  exact add_mem h₁₂ h₂₃

public theorem linearEquiv_principalDivisorOf (f : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField)) :
    LinearEquiv (principalDivisorOf f hf) 0 := by
  change principalDivisorOf f hf - 0 ∈ PrincipalDivisors X
  rw [sub_zero]
  exact principalDivisorOf_mem_PrincipalDivisors f hf

/-- Adding a principal divisor does not change the linear-equivalence class. -/
public theorem linearEquiv_add_principal (D : Div X) (f : X.functionFieldˣ)
    (hf : HasFinitePrincipalSupport (X := X) (f : X.functionField)) :
    LinearEquiv (D + principalDivisorOf f hf) D := by
  change D + principalDivisorOf f hf - D ∈ PrincipalDivisors X
  have h : D + principalDivisorOf f hf - D = principalDivisorOf f hf := by abel
  rw [h]
  exact principalDivisorOf_mem_PrincipalDivisors f hf

/-! ## Optional: global finiteness as a typeclass -/

/-- Predicate: every unit of the function field has only finitely many zeros and poles among
codimension-one points.

This holds for integral locally Noetherian quasi-compact schemes (in particular, integral
Noetherian schemes), but the proof is not yet in Mathlib; see the module docstring. -/
public class HasFinitePrincipalDivisors (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    Prop where
  finite_support : ∀ f : X.functionFieldˣ, HasFinitePrincipalSupport (X := X) (f : X.functionField)

public theorem HasFinitePrincipalDivisors.mem_finitePrincipalUnits
    [HasFinitePrincipalDivisors X] (f : X.functionFieldˣ) :
    f ∈ finitePrincipalUnits X :=
  HasFinitePrincipalDivisors.finite_support f

/-- Under global finiteness, every unit determines a principal Weil divisor. -/
public def principalDivisorUnits [HasFinitePrincipalDivisors X] :
    X.functionFieldˣ →* Multiplicative (Div X) where
  toFun f := Multiplicative.ofAdd
    (principalDivisorOf f (HasFinitePrincipalDivisors.finite_support f))
  map_one' := by
    change Multiplicative.ofAdd (principalDivisorOf (1 : X.functionFieldˣ) _) = 1
    rw [ofAdd_eq_one]
    exact principalDivisorOf_one
  map_mul' f g := by
    change Multiplicative.ofAdd (principalDivisorOf (f * g) _) =
      Multiplicative.ofAdd (principalDivisorOf f _) *
        Multiplicative.ofAdd (principalDivisorOf g _)
    rw [← ofAdd_add]
    congr 1
    exact principalDivisorOf_mul f g
      (HasFinitePrincipalDivisors.finite_support f)
      (HasFinitePrincipalDivisors.finite_support g)

@[simp] public theorem principalDivisorUnits_apply [HasFinitePrincipalDivisors X]
    (f : X.functionFieldˣ) :
    Multiplicative.toAdd (principalDivisorUnits f) =
      principalDivisorOf f (HasFinitePrincipalDivisors.finite_support f) :=
  rfl

public theorem principalDivisorUnits_mem_PrincipalDivisors [HasFinitePrincipalDivisors X]
    (f : X.functionFieldˣ) :
    Multiplicative.toAdd (principalDivisorUnits f) ∈ PrincipalDivisors X :=
  principalDivisorOf_mem_PrincipalDivisors _ _

public theorem classOf_principalDivisorUnits [HasFinitePrincipalDivisors X]
    (f : X.functionFieldˣ) :
    classOf (Multiplicative.toAdd (principalDivisorUnits f)) = (0 : ClassGroup X) :=
  classOf_principalDivisorOf _ _

/-! ## Cheap functoriality -/

/-- Transport of class groups along an additive isomorphism of divisor groups that identifies
principal subgroups. -/
public def classGroupCongr {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (e : Div X ≃+ Div Y)
    (hP : AddSubgroup.map (e : Div X →+ Div Y) (PrincipalDivisors X) = PrincipalDivisors Y) :
    ClassGroup X ≃+ ClassGroup Y :=
  QuotientAddGroup.congr (PrincipalDivisors X) (PrincipalDivisors Y) e hP

/-! ## Axiom audit (headline theorems) -/

#print axioms ord_one
#print axioms ord_inv
#print axioms ord_units_mul
#print axioms ordUnitsHom
#print axioms principalDivisorOf_mul
#print axioms principalDivisor
#print axioms PrincipalDivisors
#print axioms classOf_eq_iff
#print axioms classOf_principalDivisorOf
#print axioms LinearEquiv.trans
#print axioms principalDivisorUnits

end ExplicitUnirational.Divisors
