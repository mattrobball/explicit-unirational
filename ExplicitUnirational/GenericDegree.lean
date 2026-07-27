/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Generic degree of dominant rational maps

For a dominant rational map `f : X ⤏ Y` of integral schemes, Mathlib's
`RationalMap.fromFunctionField` supplies a morphism `Spec K(X) ⟶ Y` which, by dominance,
lands at the generic point of `Y`. The induced stalk map is a field homomorphism
`K(Y) →+* K(X)`.

This module packages that construction and the numerical invariants of the resulting
extension:

* `RationalMap.functionFieldHom` — the induced map of function fields
* `RationalMap.genericDegree` — `Module.finrank` of `K(X)` over `K(Y)` (or `0` if infinite)
* `RationalMap.IsGenericallySeparable` — separability of the same extension

The definition is taken on the rational-map quotient (via `fromFunctionField`), so it is
automatically invariant under `PartialMap.equiv` and under restriction of a representative to a
dense open of its domain.

## Hypotheses

Integral schemes are required so that function fields are fields. Dominance is required so that
the image of the generic point of the source is the generic point of the target. No separatedness
hypothesis beyond integrality is used for the core definitions; the well-definedness of
`functionFieldHom` on the rational-map quotient holds with exactly these hypotheses.

## Multiplicativity and birational transport

Multiplicativity of `genericDegree` under composition, and transport of the degree along a
birational equivalence of either side, are left for a follow-up: both need a careful comparison
of `fromFunctionField` along `PartialMap.comp` / `PartialIso`, which is not yet packaged in
Mathlib. The core API (items 1–2 of WP2) and the free invariances (equiv of representatives,
domain restriction) are complete here.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ## Dominant morphisms send generic points to generic points -/

/-- A dominant morphism of irreducible schemes sends the generic point to the generic point. -/
public theorem map_genericPoint_of_isDominant {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  rw [isGenericPoint_def]
  have hsub : Set.range (f : X → Y) ⊆ closure {(f (genericPoint X) : Y)} := by
    rintro _ ⟨x, rfl⟩
    exact (specializes_iff_mem_closure).1 ((genericPoint_specializes x).map f.continuous)
  have hdense : DenseRange (f : X → Y) := IsDominant.denseRange (f := f)
  rw [denseRange_iff_closure_range] at hdense
  apply Set.eq_univ_of_univ_subset
  calc
    Set.univ = closure (Set.range (f : X → Y)) := hdense.symm
    _ ⊆ closure (closure {(f (genericPoint X) : Y)}) := closure_mono hsub
    _ = closure {(f (genericPoint X) : Y)} := closure_closure

namespace Scheme

variable {X Y : Scheme.{u}}

/-! ## The function-field point of a dominant partial / rational map -/

/-- For a dominant partial map of integral schemes, `fromFunctionField` sends the closed point of
`Spec K(X)` to the generic point of `Y`. -/
public theorem PartialMap.fromFunctionField_apply_closedPoint [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) [IsDominant f.hom] :
    f.fromFunctionField (IsLocalRing.closedPoint X.functionField) = genericPoint Y := by
  have hmem : genericPoint X ∈ f.domain :=
    (genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec
  haveI : Nonempty f.domain := ⟨⟨genericPoint X, hmem⟩⟩
  change (f.domain.fromSpecStalkOfMem (genericPoint X) hmem ≫ f.hom)
    (IsLocalRing.closedPoint X.functionField) = genericPoint Y
  rw [Hom.comp_apply]
  have hpt : f.domain.fromSpecStalkOfMem (genericPoint X) hmem
      (IsLocalRing.closedPoint X.functionField) = ⟨genericPoint X, hmem⟩ := by
    apply f.domain.ι.isOpenEmbedding.injective
    have hcomp := Opens.fromSpecStalkOfMem_ι f.domain (genericPoint X) hmem
    have : (f.domain.fromSpecStalkOfMem (genericPoint X) hmem ≫ f.domain.ι)
        (IsLocalRing.closedPoint _) =
        X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint _) := by
      simp only [hcomp]
    rwa [Hom.comp_apply, fromSpecStalk_closedPoint] at this
  rw [hpt]
  haveI : IsIntegral f.domain.toScheme := isIntegral_of_isOpenImmersion f.domain.ι
  have hgp_dom : genericPoint f.domain.toScheme = ⟨genericPoint X, hmem⟩ :=
    Subtype.ext (genericPoint_eq_of_isOpenImmersion f.domain.ι)
  have : f.hom (genericPoint f.domain.toScheme) = genericPoint Y :=
    map_genericPoint_of_isDominant f.hom
  rwa [← hgp_dom]

/-- For a dominant rational map of integral schemes, `fromFunctionField` sends the closed point of
`Spec K(X)` to the generic point of `Y`. -/
public theorem RationalMap.fromFunctionField_apply_closedPoint [IsIntegral X] [IsIntegral Y]
    (f : X ⤏ Y) [f.IsDominant] :
    f.fromFunctionField (IsLocalRing.closedPoint X.functionField) = genericPoint Y := by
  obtain ⟨g, rfl⟩ := f.exists_rep
  haveI : IsDominant g.hom := by
    rwa [← g.isDominant_toRationalMap_iff]
  simpa using PartialMap.fromFunctionField_apply_closedPoint g

namespace RationalMap

variable [IsIntegral X] [IsIntegral Y]

/-! ## Induced function-field homomorphism -/

/-- The field homomorphism `K(Y) →+* K(X)` induced by a dominant rational map `f : X ⤏ Y` of
integral schemes.

Defined via `fromFunctionField` (which is constant on `PartialMap.equiv`-classes), so the
construction is independent of the choice of representative partial map. -/
public noncomputable def functionFieldHom (f : X ⤏ Y) [f.IsDominant] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr
    (Inseparable.of_eq (fromFunctionField_apply_closedPoint f).symm)).hom ≫
    stalkClosedPointTo f.fromFunctionField

/-- The underlying unbundled ring homomorphism. -/
public noncomputable def functionFieldRingHom (f : X ⤏ Y) [f.IsDominant] :
    Y.functionField →+* X.functionField :=
  (functionFieldHom f).hom

/-- The induced map of function fields is injective (as a map of fields). -/
public theorem functionFieldRingHom_injective (f : X ⤏ Y) [f.IsDominant] :
    Function.Injective (functionFieldRingHom f) :=
  RingHom.injective _

/-- Algebra structure making `K(X)` a `K(Y)`-algebra via `functionFieldHom`.

Not registered as a global instance (the `IsDominant` argument is not a synthesizable
out-parameter). The definitions `genericDegree` and `IsGenericallySeparable` introduce it
locally via `letI`. -/
public noncomputable abbrev algebra (f : X ⤏ Y) [f.IsDominant] :
    Algebra Y.functionField X.functionField :=
  (functionFieldRingHom f).toAlgebra

/-! ## Generic degree and separability -/

/-- The **generic degree** of a dominant rational map `f : X ⤏ Y` of integral schemes: the
`Module.finrank` of `K(X)` as a vector space over `K(Y)`. Returns `0` when the extension is
infinite. -/
public noncomputable def genericDegree (f : X ⤏ Y) [f.IsDominant] : ℕ :=
  letI : Algebra Y.functionField X.functionField := algebra f
  Module.finrank Y.functionField X.functionField

/-- A dominant rational map is **generically separable** if the induced extension of function
fields is separable. -/
public def IsGenericallySeparable (f : X ⤏ Y) [f.IsDominant] : Prop :=
  letI : Algebra Y.functionField X.functionField := algebra f
  Algebra.IsSeparable Y.functionField X.functionField

/-! ## Invariance under equivalence of representatives

Because `functionFieldHom` is defined on the rational-map quotient (via the well-defined
`fromFunctionField`), any two equivalent partial maps give identical homomorphisms, degrees, and
separability predicates. -/

/-- Helper: rewrite a dependent application after equality of rational maps. -/
theorem functionFieldHom_congr {f g : X ⤏ Y} [f.IsDominant] [g.IsDominant]
    (h : f = g) :
    functionFieldHom f = functionFieldHom g := by
  cases h
  rfl

theorem genericDegree_congr {f g : X ⤏ Y} [f.IsDominant] [g.IsDominant]
    (h : f = g) :
    genericDegree f = genericDegree g := by
  cases h
  rfl

theorem isGenericallySeparable_congr {f g : X ⤏ Y} [f.IsDominant] [g.IsDominant]
    (h : f = g) :
    IsGenericallySeparable f ↔ IsGenericallySeparable g := by
  cases h
  rfl

/-- Equivalent partial maps induce the same function-field homomorphism. -/
public theorem functionFieldHom_eq_of_equiv (f g : X.PartialMap Y)
    [IsDominant f.hom] [IsDominant g.hom] (h : f.equiv g) :
    functionFieldHom f.toRationalMap = functionFieldHom g.toRationalMap :=
  functionFieldHom_congr (PartialMap.toRationalMap_eq_iff.mpr h)

/-- Equivalent partial maps have the same generic degree. -/
public theorem genericDegree_eq_of_equiv (f g : X.PartialMap Y)
    [IsDominant f.hom] [IsDominant g.hom] (h : f.equiv g) :
    genericDegree f.toRationalMap = genericDegree g.toRationalMap :=
  genericDegree_congr (PartialMap.toRationalMap_eq_iff.mpr h)

/-- Equivalent partial maps are generically separable under the same conditions. -/
public theorem isGenericallySeparable_iff_of_equiv (f g : X.PartialMap Y)
    [IsDominant f.hom] [IsDominant g.hom] (h : f.equiv g) :
    IsGenericallySeparable f.toRationalMap ↔ IsGenericallySeparable g.toRationalMap :=
  isGenericallySeparable_congr (PartialMap.toRationalMap_eq_iff.mpr h)

/-! ## Invariance under restriction of the domain

Restricting a representative to a dense open of its domain does not change the rational map, hence
does not change any of the associated function-field invariants. -/

/-- Restricting a dominant partial map to a dense open of its domain does not change the
generic degree. -/
public theorem genericDegree_restrict (f : X.PartialMap Y) [IsDominant f.hom]
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    genericDegree (f.restrict U hU hU').toRationalMap = genericDegree f.toRationalMap :=
  genericDegree_congr (PartialMap.restrict_toRationalMap f U hU hU')

/-- Restricting a dominant partial map to a dense open of its domain does not change the
induced function-field homomorphism. -/
public theorem functionFieldHom_restrict (f : X.PartialMap Y) [IsDominant f.hom]
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    functionFieldHom (f.restrict U hU hU').toRationalMap =
      functionFieldHom f.toRationalMap :=
  functionFieldHom_congr (PartialMap.restrict_toRationalMap f U hU hU')

/-- Restricting a dominant partial map preserves generic separability. -/
public theorem isGenericallySeparable_restrict (f : X.PartialMap Y) [IsDominant f.hom]
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    IsGenericallySeparable (f.restrict U hU hU').toRationalMap ↔
      IsGenericallySeparable f.toRationalMap :=
  isGenericallySeparable_congr (PartialMap.restrict_toRationalMap f U hU hU')

end RationalMap

/-! ## Partial-map convenience wrappers -/

namespace PartialMap

variable [IsIntegral X] [IsIntegral Y]

/-- Function-field map of a dominant partial map (via its rational map). -/
public noncomputable def functionFieldHom (f : X.PartialMap Y) [IsDominant f.hom] :
    Y.functionField ⟶ X.functionField :=
  RationalMap.functionFieldHom f.toRationalMap

/-- Unbundled ring homomorphism. -/
public noncomputable def functionFieldRingHom (f : X.PartialMap Y) [IsDominant f.hom] :
    Y.functionField →+* X.functionField :=
  RationalMap.functionFieldRingHom f.toRationalMap

/-- Generic degree of a dominant partial map. -/
public noncomputable def genericDegree (f : X.PartialMap Y) [IsDominant f.hom] : ℕ :=
  RationalMap.genericDegree f.toRationalMap

/-- Generic separability of a dominant partial map. -/
public def IsGenericallySeparable (f : X.PartialMap Y) [IsDominant f.hom] : Prop :=
  RationalMap.IsGenericallySeparable f.toRationalMap

@[simp] public theorem functionFieldHom_toRationalMap (f : X.PartialMap Y) [IsDominant f.hom] :
    RationalMap.functionFieldHom f.toRationalMap = functionFieldHom f :=
  rfl

@[simp] public theorem genericDegree_toRationalMap (f : X.PartialMap Y) [IsDominant f.hom] :
    RationalMap.genericDegree f.toRationalMap = genericDegree f :=
  rfl

/-- Equivalent partial maps have equal `functionFieldHom` (partial-map form). -/
public theorem functionFieldHom_eq_of_equiv (f g : X.PartialMap Y)
    [IsDominant f.hom] [IsDominant g.hom] (h : f.equiv g) :
    functionFieldHom f = functionFieldHom g :=
  RationalMap.functionFieldHom_eq_of_equiv f g h

/-- Equivalent partial maps have equal generic degree (partial-map form). -/
public theorem genericDegree_eq_of_equiv (f g : X.PartialMap Y)
    [IsDominant f.hom] [IsDominant g.hom] (h : f.equiv g) :
    genericDegree f = genericDegree g :=
  RationalMap.genericDegree_eq_of_equiv f g h

end PartialMap

/-! ## Morphisms -/

/-- For a morphism of irreducible schemes, `fromFunctionField` of the associated partial map is
`fromSpecStalk η ≫ f`. -/
public theorem Hom.toPartialMap_fromFunctionField [IrreducibleSpace X] (f : X ⟶ Y) :
    f.toPartialMap.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ f :=
  PartialMap.fromSpecStalkOfMem_toPartialMap f (genericPoint X)

namespace Hom

variable [IsIntegral X] [IsIntegral Y]

/-- Function-field map of a dominant morphism of integral schemes. -/
public noncomputable def functionFieldHom (f : X ⟶ Y) [IsDominant f] :
    Y.functionField ⟶ X.functionField :=
  RationalMap.functionFieldHom f.toRationalMap

/-- Unbundled ring homomorphism for a dominant morphism. -/
public noncomputable def functionFieldRingHom (f : X ⟶ Y) [IsDominant f] :
    Y.functionField →+* X.functionField :=
  RationalMap.functionFieldRingHom f.toRationalMap

/-- Generic degree of a dominant morphism of integral schemes. -/
public noncomputable def genericDegree (f : X ⟶ Y) [IsDominant f] : ℕ :=
  RationalMap.genericDegree f.toRationalMap

/-- Generic separability of a dominant morphism of integral schemes. -/
public def IsGenericallySeparable (f : X ⟶ Y) [IsDominant f] : Prop :=
  RationalMap.IsGenericallySeparable f.toRationalMap

/-- The function-field homomorphism of a dominant morphism is injective. -/
public theorem functionFieldRingHom_injective (f : X ⟶ Y) [IsDominant f] :
    Function.Injective (functionFieldRingHom f) :=
  RationalMap.functionFieldRingHom_injective f.toRationalMap

end Hom

end Scheme

end AlgebraicGeometry
