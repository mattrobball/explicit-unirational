/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.FunctionField.MulThree
public import ExplicitUnirational.FunctionField.MulThreeCert
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Torsor trivialization and translation-invariance (gaps 2–3 of Route A)

[CLOP Lemma 3.4], in the case of [CLOP Example 3.5], identifies the degree-9 map
`α_λ : C → Jac(C)`, after base change to an algebraic closure and choice of an origin, with
multiplication-by-3 followed by a translation on the Jacobian. Combined with the base-change
arithmetic of `ExplicitUnirational.FunctionField.TorsorDescent`, this would close Endpoint A0
along Route A.

This module supplies the **field-theoretic** half of that identification:

* **Gap 3 (complete).** A translation is a field automorphism of the function field. Pre- or
  post-composing a finite extension with an automorphism does not change `Module.finrank`. Pure
  field theory; no geometry.

* **Gap 2 (partial).** Full torsor trivialization `K̄(C) ≃ K̄(W)` needs either:
  1. a rational point on the plane cubic over `K̄` plus the classical "genus-one curve with a
     point is its Jacobian", or
  2. an explicit plane-cubic → Weierstrass normalization (as in the sibling repo's
     `exists_shortWeierstrass_coordinates` / `exists_hesseWeierstrassModel`).

  Mathlib has neither the Picard/Jacobian scheme of a genus-one curve nor plane-cubic normal
  forms. What *is* available, and what this file proves, is the **transfer of degree along a
  hypothetical identification**: once an `AlgEquiv` identifies the ambient function field of `C`
  with that of a Weierstrass model (or with `RatFunc`), degrees of intermediate extensions and
  of AlgHom images transport without change. The geometric construction of that `AlgEquiv` is
  the remaining obstruction (documented at the end of the module docstring).

## Sibling-repo status (Route 2, not imported)

Checked against
`/Users/worker/unirational/problems/B-conic-bundle-multisections/` on this toolchain:

* `HesseNormalFormWeierstrass.lean` (`exists_hesseWeierstrassModel`) — **sorry-free**.
* `ShortWeierstrassNormalForm.lean` (`exists_shortWeierstrass_coordinates`) — **sorry-free**.
* `HesseNormalFormFlex.lean` (`exists_weierstrassSupport_coordinates`) — **sorry-free**.
* `HesseNormalFormBridge.lean` (`exists_hesseNormalForm_coordinates`) — **sorry-free** per
  `certificates/HesseNormalFormStatus.md`.

These rest on ~1.6k lines of plane-cubic infrastructure local to that repo and must not be
imported here. Vendoring them would be a multi-module Mathlib-scale contribution, not a local
lemma.

## What Mathlib would need for a complete gap 2

Either of:

1. **Scheme-theoretic:** for a smooth geometrically integral genus-one curve `C` over an
   algebraically closed field, `C(k) ≠ ∅`, and choice of a point gives `C ≅ Jac(C)` as
   principal homogeneous spaces (equivalently as elliptic curves). Needs: genus, Picard scheme
   or at least `Pic⁰`, and the classical torsor-trivialization.
2. **Explicit:** plane cubic → short Weierstrass via linear substitution over alg. closed
   fields of char `≠ 2, 3` (the sibling stack above), plus transport of function fields along
   the induced coordinate change.

Until one of those lands, Route A for A0 stops at: base-change arithmetic (TorsorDescent) +
translation-invariance (this file) + `finrank_mulThreeX` (MulThree), with the single missing
geometric identification `K̄(C) ≃ K̄(W)`.
-/

noncomputable section

open Module IntermediateField

namespace ExplicitUnirational

/-! ## Gap 3 — translation-invariance of degree

A translation of the curve induces a `K`-algebra automorphism of its function field. The
lemmas below record that automorphisms preserve `finrank` of intermediate extensions and of
images of algebra homs — the function-field content of "composing with a translation does not
change the degree". -/

/-- Finite free rank is invariant under a `K`-algebra isomorphism of the ambient fields. -/
public theorem finrank_eq_of_algEquiv
    {K L L' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') :
    Module.finrank K L = Module.finrank K L' :=
  e.toLinearEquiv.finrank_eq

/-- **Translation-invariance for intermediate fields.**

If `σ` is a `K`-automorphism of `L` (e.g. the function-field automorphism induced by a
translation of the curve) and `M ⊆ L` is intermediate, then
`[L : σ(M)] = [L : M]`. -/
public theorem finrank_map_algEquiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (M : IntermediateField K L) :
    Module.finrank (M.map σ.toAlgHom) L = Module.finrank M L := by
  refine (Algebra.finrank_eq_of_equiv_equiv
      (IntermediateField.equivMap M σ.toAlgHom).toRingEquiv
      σ.toRingEquiv ?_).symm
  ext x
  -- algebraMap (M.map σ) L ∘ equivMap = σ ∘ algebraMap M L
  -- Both sides reduce to `σ ↑x` via the inclusion algebra maps and `coe_equivMap_apply`.
  simp [IntermediateField.algebraMap_apply, IntermediateField.coe_equivMap_apply]

/-- Same statement with the numerical degree packaged as a hypothesis-rewrite form. -/
public theorem finrank_eq_of_map_algEquiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (M : IntermediateField K L) {n : ℕ}
    (h : Module.finrank M L = n) :
    Module.finrank (M.map σ.toAlgHom) L = n := by
  rwa [finrank_map_algEquiv]

/-- Converse direction: if the translated intermediate field has degree `n`, so does the original. -/
public theorem finrank_eq_of_map_algEquiv'
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (M : IntermediateField K L) {n : ℕ}
    (h : Module.finrank (M.map σ.toAlgHom) L = n) :
    Module.finrank M L = n := by
  rwa [finrank_map_algEquiv] at h

/-- **Postcomposition with an automorphism preserves the degree of an algebra hom.**

If `f : M →ₐ[K] L` realizes a finite extension of degree `n` (as `finrank` of its field range)
and `τ` is a `K`-automorphism of `L`, then `τ ∘ f` has the same degree. This is the pure
field-theory form of "composing the degree-9 map with a translation does not change the
degree". -/
public theorem finrank_fieldRange_comp_algEquiv_right
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L]
    (f : M →ₐ[K] L) (τ : L ≃ₐ[K] L) :
    Module.finrank (AlgHom.fieldRange (τ.toAlgHom.comp f)) L =
      Module.finrank (AlgHom.fieldRange f) L := by
  -- fieldRange (τ ∘ f) = (fieldRange f).map τ
  have hrange :
      AlgHom.fieldRange (τ.toAlgHom.comp f) =
        (AlgHom.fieldRange f).map τ.toAlgHom := by
    apply IntermediateField.toSubalgebra_injective
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨f y, ⟨y, rfl⟩, ?_⟩
      simp
    · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, by simp⟩
  rw [hrange, finrank_map_algEquiv]

/-- **Precomposition with an automorphism of the domain preserves degree.**

If `σ : M ≃ₐ[K] M` and `f : M →ₐ[K] L`, then `f ∘ σ` and `f` have the same field-range
degree over `L`. -/
public theorem finrank_fieldRange_comp_algEquiv_left
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L]
    (σ : M ≃ₐ[K] M) (f : M →ₐ[K] L) :
    Module.finrank (AlgHom.fieldRange (f.comp σ.toAlgHom)) L =
      Module.finrank (AlgHom.fieldRange f) L := by
  -- Surjectivity of σ gives equal field ranges as sets.
  have hrange :
      AlgHom.fieldRange (f.comp σ.toAlgHom) = AlgHom.fieldRange f := by
    apply IntermediateField.toSubalgebra_injective
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨σ y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨σ.symm y, ?_⟩
      simp
  rw [hrange]

/-- Combined left-and-right: automorphisms on either side of a field embedding do not change
the degree of the induced extension. -/
public theorem finrank_fieldRange_comp_algEquiv_both
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L]
    (σ : M ≃ₐ[K] M) (f : M →ₐ[K] L) (τ : L ≃ₐ[K] L) :
    Module.finrank (AlgHom.fieldRange (τ.toAlgHom.comp (f.comp σ.toAlgHom))) L =
      Module.finrank (AlgHom.fieldRange f) L := by
  rw [finrank_fieldRange_comp_algEquiv_right, finrank_fieldRange_comp_algEquiv_left]

/-- Tower form without intermediate-field packaging: if `L/M` is finite and `τ` is a
`K`-automorphism of `L` that stabilizes `M` setwise (i.e. restricts to an automorphism of
`M`), the degree is unchanged — recovered as the special case of `finrank_eq_of_algEquiv`
after restriction of scalars along the identity on the base. Packaged for the case where the
automorphism of `L` is over `M` itself (translation fixing the base field of the Jacobian). -/
public theorem finrank_eq_of_algEquiv_over_base
    {M L L' : Type*} [Field M] [Field L] [Field L']
    [Algebra M L] [Algebra M L'] (e : L ≃ₐ[M] L') :
    Module.finrank M L = Module.finrank M L' :=
  finrank_eq_of_algEquiv e

/-- **Headline gap-3 statement for the composite `τ ∘ [3]`.**

If a finite extension of function fields has degree `n` and `τ` is any automorphism of the
big field over the base, the image of the small field under `τ` still has degree `n`. In the
geometry of [CLOP Lemma 3.4], the small field is the pullback of the function field of the
Jacobian along `[3]`, and `τ` is translation by a fixed point of the Jacobian. -/
public theorem finrank_eq_of_translation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (τ : L ≃ₐ[K] L) (M : IntermediateField K L) {n : ℕ}
    (h : Module.finrank M L = n) :
    Module.finrank (M.map τ.toAlgHom) L = n :=
  finrank_eq_of_map_algEquiv τ M h

/-- Specialization: degree 9 is preserved under translation. -/
public theorem finrank_eq_nine_of_translation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (τ : L ≃ₐ[K] L) (M : IntermediateField K L)
    (h : Module.finrank M L = 9) :
    Module.finrank (M.map τ.toAlgHom) L = 9 :=
  finrank_eq_of_translation τ M h

/-! ## Gap 2 (partial) — transfer of degree along a trivialization

The geometric identification `K̄(C) ≃ₐ[K̄] K̄(W)` is not formalized. What *is* formalized is
that any such identification, once supplied, transports the degree-9 computation on the
Weierstrass `x`-line to the plane-cubic side, including after an arbitrary translation. -/

/-- **Degree transport along an ambient field isomorphism.**

If `e : L ≃ₐ[K] L'` identifies two ambient function fields and carries the intermediate field
`M ⊆ L` onto `N ⊆ L'`, then `[L : M] = [L' : N]`. This is the algebraic skeleton of "once
`C ≅ W` over `K̄`, degrees of maps of curves agree on function fields". -/
public theorem finrank_eq_of_algEquiv_map
    {K L L' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') (M : IntermediateField K L) (N : IntermediateField K L')
    (hmap : M.map e.toAlgHom = N) :
    Module.finrank M L = Module.finrank N L' := by
  have h1 : Module.finrank M L = Module.finrank (M.map e.toAlgHom) L' := by
    refine Algebra.finrank_eq_of_equiv_equiv
      (IntermediateField.equivMap M e.toAlgHom).toRingEquiv e.toRingEquiv ?_
    ext x
    simp [IntermediateField.algebraMap_apply, IntermediateField.coe_equivMap_apply]
  rw [← hmap]
  exact h1

/-- Numerical form of `finrank_eq_of_algEquiv_map`. -/
public theorem finrank_eq_of_algEquiv_map_eq
    {K L L' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') (M : IntermediateField K L) (N : IntermediateField K L')
    (hmap : M.map e.toAlgHom = N) {n : ℕ}
    (hn : Module.finrank N L' = n) :
    Module.finrank M L = n := by
  rwa [finrank_eq_of_algEquiv_map e M N hmap]

/-- **Trivialization + translation + `mulThreeX`.**

Suppose an identification `e : L ≃ₐ[F] RatFunc F` carries an intermediate field `M` of the
(function field of the) plane cubic onto the translate of the `mulThreeX` subfield of the
Weierstrass `x`-line. Then `[L : M] = 9`, using `finrank_mulThreeX` and gap 3.

This is the precise field-theoretic residual of [CLOP Lemma 3.4] once the geometric
trivialization `e` is supplied. -/
public theorem finrank_eq_nine_of_trivialization_translation
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (W : WeierstrassCurve F) (h3 : (3 : F) ≠ 0)
    (hcop : IsCoprime (W.Φ 3) (W.ΨSq 3))
    (e : L ≃ₐ[F] RatFunc F) (τ : RatFunc F ≃ₐ[F] RatFunc F)
    (M : IntermediateField F L)
    (hmap : M.map e.toAlgHom = (F⟮mulThreeX W⟯).map τ.toAlgHom) :
    Module.finrank M L = 9 := by
  have h9 : Module.finrank F⟮mulThreeX W⟯ (RatFunc F) = 9 :=
    finrank_mulThreeX W h3 hcop
  have h9' : Module.finrank ((F⟮mulThreeX W⟯).map τ.toAlgHom) (RatFunc F) = 9 :=
    finrank_eq_nine_of_translation τ F⟮mulThreeX W⟯ h9
  exact finrank_eq_of_algEquiv_map_eq e M _ hmap h9'

/-- Specialization to the Weierstrass model of [CLOP §4.1] (the equation for `J_η`) over `ℚ(z)`,
where coprimality of
`Φ₃` and `ΨSq₃` is already certified. -/
public theorem finrank_eq_nine_of_trivialization_translation_noteCurveQ
    {L : Type*} [Field L] [Algebra KQ L]
    (e : L ≃ₐ[KQ] RatFunc KQ) (τ : RatFunc KQ ≃ₐ[KQ] RatFunc KQ)
    (M : IntermediateField KQ L)
    (hmap : M.map e.toAlgHom = (KQ⟮mulThreeX noteCurveQ⟯).map τ.toAlgHom) :
    Module.finrank M L = 9 :=
  finrank_eq_nine_of_trivialization_translation noteCurveQ
    (by simp [KQ]) isCoprime_Φ_ΨSq_noteCurveQ e τ M hmap

/-- Without translation: if `e` carries `M` exactly onto the `mulThreeX` subfield, degree is 9. -/
public theorem finrank_eq_nine_of_trivialization
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (W : WeierstrassCurve F) (h3 : (3 : F) ≠ 0)
    (hcop : IsCoprime (W.Φ 3) (W.ΨSq 3))
    (e : L ≃ₐ[F] RatFunc F) (M : IntermediateField F L)
    (hmap : M.map e.toAlgHom = F⟮mulThreeX W⟯) :
    Module.finrank M L = 9 := by
  have h9 : Module.finrank F⟮mulThreeX W⟯ (RatFunc F) = 9 :=
    finrank_mulThreeX W h3 hcop
  exact finrank_eq_of_algEquiv_map_eq e M _ hmap h9

/-- Specialization of `finrank_eq_nine_of_trivialization` to `noteCurveQ`, the Weierstrass
model of [CLOP §4.1] (the equation for `J_η`). -/
public theorem finrank_eq_nine_of_trivialization_noteCurveQ
    {L : Type*} [Field L] [Algebra KQ L]
    (e : L ≃ₐ[KQ] RatFunc KQ) (M : IntermediateField KQ L)
    (hmap : M.map e.toAlgHom = KQ⟮mulThreeX noteCurveQ⟯) :
    Module.finrank M L = 9 :=
  finrank_eq_nine_of_trivialization noteCurveQ (by simp [KQ]) isCoprime_Φ_ΨSq_noteCurveQ e M hmap

/-! ## Axiom audit -/

#print axioms finrank_eq_of_algEquiv
#print axioms finrank_map_algEquiv
#print axioms finrank_fieldRange_comp_algEquiv_right
#print axioms finrank_fieldRange_comp_algEquiv_left
#print axioms finrank_fieldRange_comp_algEquiv_both
#print axioms finrank_eq_of_translation
#print axioms finrank_eq_nine_of_translation
#print axioms finrank_eq_of_algEquiv_map
#print axioms finrank_eq_nine_of_trivialization_translation
#print axioms finrank_eq_nine_of_trivialization_translation_noteCurveQ
#print axioms finrank_eq_nine_of_trivialization
#print axioms finrank_eq_nine_of_trivialization_noteCurveQ

end ExplicitUnirational
