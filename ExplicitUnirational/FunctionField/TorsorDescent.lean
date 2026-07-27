/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.FunctionField.MulThree
public import ExplicitUnirational.FunctionField.MulThreeCert
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Torsor descent of the degree-nine map (Route A)

Note Proposition 2.2 produces a degree-9 extension of function fields `k(E) ↪ k(Γ)`. Restricted
to the pencil base this is an extension of function fields of curves over `K = k(z)`:

```
  K(C) / K(W)    of degree 9
```

where `C` is the generic plane cubic and `W` is its Jacobian (note eq. (3.7)). The obstruction is
that `C` is a **torsor**: the generic cubic has no `K`-point, so `C ≇ W` over `K` — only over an
algebraic closure. The note bridges this by quoting Fisher [Fis08, Prop. 2.3], which is not in
Mathlib.

## Route A (this module)

Degree of a finite extension of fields is invariant under base change of the ground field.
Over an algebraic closure the torsor trivializes, `C ≅ W`, and the map becomes `[3]` followed by
a translation, so the degree is 9 by `finrank_mulThreeX` / `finrank_mulThreeX_noteCurveQ`.

What this module supplies (ordinary commutative algebra — no Picard schemes):

1. **Absolute base-change invariance of `finrank`.** For a finite field extension `L/K` and any
   field extension `Kp/K`,
   `Module.finrank Kp (Kp ⊗[K] L) = Module.finrank K L`.

2. **Relative base-change invariance.** For a tower `K → M → L` of fields with `L/M` finite and
   any domain `K`-algebra `Kp` into which `K` injects,
   `Module.finrank (M ⊗[K] Kp) ((M ⊗[K] Kp) ⊗[M] L) = Module.finrank M L`.
   This is the form needed for function fields of curves: base-change the finite extension
   `K(C)/K(W)` along `K → K̄`.

3. **Tensor of a finite extension with a field is a field when it is a domain.** Uses
   `Algebra.TensorProduct.isField_of_isAlgebraic`.

4. **Descent corollary.** If the base-changed extension has rank 9, then the original extension
   has degree 9.

5. **Fraction-field comparison.** Degree of a finite algebraic extension of domains is preserved
   on fraction fields (`Algebra.IsAlgebraic.finrank_of_isFractionRing`).

## Remaining gap (honest status)

The missing geometric steps, not attempted here:

* **Geometric integrality of the generic cubic** `C/K`: that `K` is algebraically closed in
  `K(C)`, equivalently that `K(C) ⊗[K] K̄` is a field (domain). This is a statement about the
  plane cubic `G_z = 0` remaining geometrically integral — true by the note's smoothness
  hypothesis on the generic member, but not yet connected to a Mathlib `IsIntegral` /
  `GeometricallyIntegral` instance for this explicit pencil.
* **Torsor trivialization over `K̄`:** an identification `K̄(C) ≃ K̄(W)` under which the map
  becomes `[3]` composed with a translation. That is Fisher [Fis08, Prop. 2.3] / note Lemma 2.1's
  Picard-scheme argument; Mathlib has neither `Pic` of a genus-one curve nor Fisher's Jacobian
  formula as a scheme morphism.
* **Translation-invariance of degree** for the composite `τ ∘ [3]` as a map of curves (as
  function-field extensions this is automatic once the map is identified with an automorphism
  of the target composed with `[3]`).

With (1)–(5) in hand, the only remaining work for Endpoint A0 along Route A is to supply those
three geometric identifications; the degree arithmetic then closes by
`finrank_mulThreeX_noteCurveQ`.
-/

noncomputable section

open scoped TensorProduct IntermediateField
open Module

namespace ExplicitUnirational

/-! ## Absolute base-change invariance of `finrank` -/

/-- **Degree of a finite field extension is invariant under base change of the ground field.**

For `L/K` finite and any field extension `Kp/K`, the free `Kp`-module `Kp ⊗[K] L` has the same
rank as `L` over `K`. When `Kp ⊗[K] L` is itself a field (e.g. after geometric integrality), this
is the degree of the base-changed extension. -/
public theorem finrank_tensorProduct_baseChange
    (K L Kp : Type*) [Field K] [Field L] [Field Kp]
    [Algebra K L] [Algebra K Kp] [FiniteDimensional K L] :
    Module.finrank Kp (Kp ⊗[K] L) = Module.finrank K L :=
  Module.finrank_baseChange

/-! ## Relative base-change invariance (tower form) -/

/-- **Relative base-change invariance of `finrank`.**

For a tower of fields `K → M → L` with `L/M` finite and any domain `K`-algebra `Kp` with
`K → Kp` injective, the base-changed module `(M ⊗[K] Kp) ⊗[M] L` is free of rank
`Module.finrank M L` over `M ⊗[K] Kp`.

This is the commutative-algebra engine of Route A: the finite extension of function fields
`K(C)/K(W)` has the same degree after base change along `K → K̄`. -/
public theorem finrank_tensorProduct_baseChange_relative
    (K M L : Type*) (Kp : Type*) [Field K] [Field M] [Field L]
    [CommRing Kp] [IsDomain Kp] [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [Algebra K Kp] [FaithfulSMul K Kp] [FiniteDimensional M L] :
    Module.finrank (M ⊗[K] Kp) ((M ⊗[K] Kp) ⊗[M] L) = Module.finrank M L := by
  letI : Module.Free M L := Module.Free.of_divisionRing M L
  haveI : Nontrivial (M ⊗[K] Kp) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K M Kp
      (FaithfulSMul.algebraMap_injective K M)
      (FaithfulSMul.algebraMap_injective K Kp)
  exact Module.finrank_baseChange (R := M ⊗[K] Kp) (S := M) (M' := L)

/-- Field-valued special case: any field extension `Kp/K` is a faithful domain algebra. -/
public theorem finrank_tensorProduct_baseChange_relative_field
    (K M L Kp : Type*) [Field K] [Field M] [Field L] [Field Kp]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [Algebra K Kp] [FiniteDimensional M L] :
    Module.finrank (M ⊗[K] Kp) ((M ⊗[K] Kp) ⊗[M] L) = Module.finrank M L :=
  finrank_tensorProduct_baseChange_relative K M L Kp

/-! ## Tensor products of fields that remain domains are fields -/

/-- If `L/K` is algebraic (in particular, finite) and `L ⊗[K] Kp` is a domain, then it is a field.

Geometric integrality of a curve over `K` supplies the domain hypothesis after base change to an
algebraic extension of `K`. -/
public theorem isField_tensorProduct_of_isDomain_of_isAlgebraic
    (K L Kp : Type*) [Field K] [Field L] [Field Kp]
    [Algebra K L] [Algebra K Kp] [Algebra.IsAlgebraic K L]
    [IsDomain (L ⊗[K] Kp)] :
    IsField (L ⊗[K] Kp) :=
  Algebra.TensorProduct.isField_of_isAlgebraic K L Kp (Or.inl ‹_›)

/-- Finite-dimensional special case of `isField_tensorProduct_of_isDomain_of_isAlgebraic`. -/
public theorem isField_tensorProduct_of_isDomain_of_finiteDimensional
    (K L Kp : Type*) [Field K] [Field L] [Field Kp]
    [Algebra K L] [Algebra K Kp] [FiniteDimensional K L]
    [IsDomain (L ⊗[K] Kp)] :
    IsField (L ⊗[K] Kp) :=
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  isField_tensorProduct_of_isDomain_of_isAlgebraic K L Kp

/-! ## Descent of a numerical degree -/

/-- **Degree descent along base change.**

If the free base change of `L/M` along `K → Kp` has `finrank = n`, then `L/M` has degree `n`. -/
public theorem finrank_eq_of_baseChange_finrank
    (K M L : Type*) (Kp : Type*) [Field K] [Field M] [Field L]
    [CommRing Kp] [IsDomain Kp] [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [Algebra K Kp] [FaithfulSMul K Kp] [FiniteDimensional M L]
    {n : ℕ}
    (h : Module.finrank (M ⊗[K] Kp) ((M ⊗[K] Kp) ⊗[M] L) = n) :
    Module.finrank M L = n := by
  rwa [finrank_tensorProduct_baseChange_relative K M L Kp] at h

/-- Absolute form: if `Kp ⊗[K] L` has degree `n` over `Kp`, then `L/K` has degree `n`. -/
public theorem finrank_eq_of_tensorProduct_finrank
    (K L Kp : Type*) [Field K] [Field L] [Field Kp]
    [Algebra K L] [Algebra K Kp] [FiniteDimensional K L]
    {n : ℕ}
    (h : Module.finrank Kp (Kp ⊗[K] L) = n) :
    Module.finrank K L = n := by
  rwa [finrank_tensorProduct_baseChange K L Kp] at h

/-! ## Application shape for the degree-nine map

The full A0 statement needs a `K`-algebra map `K(W) →ₐ[K] K(C)` whose base change to `K̄`
is identified with the function-field map of `τ ∘ [3]`. Under that identification the degree is
9 by `finrank_mulThreeX`. The pure degree-arithmetic half is recorded below. -/

/-- **Arithmetic half of torsor descent.**

Suppose `L/M` is a finite extension of fields over `K` (think `L = K(C)`, `M = K(W)`), and
after base change to some `Kp/K` the free module `(M ⊗[K] Kp) ⊗[M] L` has rank 9. Then
`Module.finrank M L = 9`.

The geometric content that upgrades this to Proposition 2.2 is: choose `Kp = AlgebraicClosure K`,
verify the tensor is a field (geometric integrality), and identify the extension with the degree-9
extension coming from `mulThreeX` on the Weierstrass model (torsor trivialization + translation). -/
public theorem finrank_eq_nine_of_baseChange_finrank_nine
    (K M L : Type*) (Kp : Type*) [Field K] [Field M] [Field L]
    [CommRing Kp] [IsDomain Kp] [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [Algebra K Kp] [FaithfulSMul K Kp] [FiniteDimensional M L]
    (h : Module.finrank (M ⊗[K] Kp) ((M ⊗[K] Kp) ⊗[M] L) = 9) :
    Module.finrank M L = 9 :=
  finrank_eq_of_baseChange_finrank K M L Kp h

/-- Field-valued special case of `finrank_eq_nine_of_baseChange_finrank_nine`. -/
public theorem finrank_eq_nine_of_baseChange_finrank_nine_field
    (K M L Kp : Type*) [Field K] [Field M] [Field L] [Field Kp]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [Algebra K Kp] [FiniteDimensional M L]
    (h : Module.finrank (M ⊗[K] Kp) ((M ⊗[K] Kp) ⊗[M] L) = 9) :
    Module.finrank M L = 9 :=
  finrank_eq_nine_of_baseChange_finrank_nine K M L Kp h

/-- Specialization of the arithmetic half to the note's Weierstrass `x`-line over `ℚ(z)`.

If a finite extension `L` of `KQ⟮mulThreeX noteCurveQ⟯` base-changes to rank 9 along any
faithful domain `KQ`-algebra (in particular along an algebraic closure), then `L` itself has
degree 9 over that subfield. Combined with `finrank_mulThreeX_noteCurveQ` this is the
degree-arithmetic needed once the torsor is trivialized. -/
public theorem finrank_eq_nine_of_baseChange_over_mulThreeX
    (L : Type*) [Field L] [Algebra KQ L]
    [Algebra KQ⟮mulThreeX noteCurveQ⟯ L]
    [IsScalarTower KQ KQ⟮mulThreeX noteCurveQ⟯ L]
    [FiniteDimensional KQ⟮mulThreeX noteCurveQ⟯ L]
    (Kp : Type*) [CommRing Kp] [IsDomain Kp] [Algebra KQ Kp] [FaithfulSMul KQ Kp]
    (h : Module.finrank (KQ⟮mulThreeX noteCurveQ⟯ ⊗[KQ] Kp)
        ((KQ⟮mulThreeX noteCurveQ⟯ ⊗[KQ] Kp) ⊗[KQ⟮mulThreeX noteCurveQ⟯] L) = 9) :
    Module.finrank KQ⟮mulThreeX noteCurveQ⟯ L = 9 :=
  finrank_eq_nine_of_baseChange_finrank_nine KQ KQ⟮mulThreeX noteCurveQ⟯ L Kp h

/-- Unconditional degree 9 for the `x`-line of the note's model (3.7), restated as the target of
descent. The base-change lemmas above reduce the torsor problem to matching this number after
trivialization. -/
public theorem finrank_mulThreeX_noteCurveQ_eq_nine :
    Module.finrank KQ⟮mulThreeX noteCurveQ⟯ (RatFunc KQ) = 9 :=
  finrank_mulThreeX_noteCurveQ

/-! ## Fraction-field form (coordinate rings of curves)

For affine models, the degree of a finite extension of coordinate rings equals the degree of the
extension of function fields, by `Algebra.IsAlgebraic.finrank_of_isFractionRing`. Packaged for
downstream use when explicit affine charts are available. -/

attribute [local instance] FractionRing.liftAlgebra

/-- Degree of a finite algebraic extension of domains is preserved on fraction fields. -/
public theorem finrank_fractionRing_eq
    (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S] :
    Module.finrank (FractionRing R) (FractionRing S) = Module.finrank R S :=
  Algebra.IsAlgebraic.finrank_of_isFractionRing R (FractionRing R) S (FractionRing S)

/-! ## Axiom audit -/

#print axioms finrank_tensorProduct_baseChange
#print axioms finrank_tensorProduct_baseChange_relative
#print axioms finrank_tensorProduct_baseChange_relative_field
#print axioms isField_tensorProduct_of_isDomain_of_isAlgebraic
#print axioms finrank_eq_nine_of_baseChange_finrank_nine
#print axioms finrank_eq_nine_of_baseChange_over_mulThreeX
#print axioms finrank_mulThreeX_noteCurveQ_eq_nine
#print axioms finrank_fractionRing_eq

end ExplicitUnirational
