/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.FunctionField.PencilRationality
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Topology.Irreducible

/-!
# Incidence surface of a cubic pencil (WP3; note (3.2), Lemma 3.1)

For ternary forms `F₀, F₁` over a field `k`, the incidence surface of the pencil is
```
  Γ = { u · F₀ + v · F₁ = 0 } ⊆ ℙ² × ℙ¹
```
(note (3.2)). Lemma 3.1 asserts that projection `Γ → ℙ²` is birational, with rational inverse
```
  [X : Y : Z]  ↦  ([X : Y : Z], [F₁(X,Y,Z) : -F₀(X,Y,Z)])
```
away from the base scheme `{F₀ = F₁ = 0}`.

## Contents

1. Ambient `ℙⁿ` and `ℙᵐ × ℙⁿ` (sibling shape).
2. Incidence Cox equation `u F₀ + v F₁` and the polynomial form of the rational inverse.
3. Affine chart model `Γ_aff = Spec(AdjoinRoot(C f₁ · X + C f₀))` over `R = k[x,y]`.
4. Integrality under `PencilGeneric` (`f₁ ≠ 0` and `IsRelPrime f₁ f₀`).
5. Dominance of the affine projection `Γ_aff → 𝔸²`.
6. Localization isomorphism `R[1/f₁] ≃ A[1/φ(f₁)]` realizing `z = -f₀/f₁`
   (`planeAwayMap` / `planeAwayEquiv`).
7. Affine `PartialIso` / birationality of `Γ_aff ∼ 𝔸²` on `D(f₁)`, with explicit rational inverse
   (`affineInversePartialMap` / `affineInverseRationalMap`).
8. Algebraic witness that the projection has generic degree 1: the localization of the structure
   map is an isomorphism (`planeAwayEquiv_bijective`).

**Strategy.** Scheme-level birationality is proved directly on the affine chart by constructing
inverse localization maps and packaging them as a `PartialIso` of basic opens — not by routing
through `FunctionField.PencilRationality` (which records the same algebra in fraction-field
language). Global projective zero locus / `PartialIso` for `Γ ⊂ ℙ² × ℙ¹`, equality of the
partial-iso projection with `affineIncidenceProj` as rational maps, and the full
`Hom.genericDegree = 1` identification via `GenericDegree.lean` are left for a follow-up.
-/

noncomputable section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace ExplicitUnirational.CubicPencil

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Ambient projective and biprojective spaces -/

/-- Scheme-level projective `n`-space over a commutative ring `R`. -/
public abbrev ProjectiveSpace (n : ℕ) (R : Type u) [CommRing R] : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

namespace ProjectiveSpace

/-- Structure morphism `ℙⁿ_R → Spec R`. -/
public def toSpec (n : ℕ) (R : Type u) [CommRing R] : ProjectiveSpace n R ⟶ Spec (.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)))

instance (n : ℕ) (R : Type u) [CommRing R] :
    (ProjectiveSpace n R).CanonicallyOver (Spec (.of R)) where
  hom := toSpec n R

/-- Degree-zero homogeneous localization at `Xᵢ`. -/
public abbrev StandardChartRing (n : ℕ) (R : Type u) [CommRing R] (i : Fin (n + 1)) : Type u :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X i)

/-- Standard open immersion from the `i`-th chart. -/
public def standardChartι (n : ℕ) (R : Type u) [CommRing R] (i : Fin (n + 1)) :
    Spec (.of (StandardChartRing n R i)) ⟶ ProjectiveSpace n R :=
  Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) zero_lt_one

instance (n : ℕ) (R : Type u) [CommRing R] (i : Fin (n + 1)) :
    IsOpenImmersion (standardChartι n R i) :=
  inferInstanceAs (IsOpenImmersion
    (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) zero_lt_one))

theorem irrelevant_le_span_X (n : ℕ) (R : Type u) [CommRing R] :
    (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toIdeal ≤
      Ideal.span (Set.range
        (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd p hp
  change p ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R
  rw [← pow_one (MvPolynomial.idealOfVars (Fin (n + 1)) R),
    MvPolynomial.mem_pow_idealOfVars_iff]
  intro monomial hmonomial
  rw [Finsupp.degree_apply, ← hp.degree_eq_sum_deg_support hmonomial]
  exact Nat.succ_le_iff.mpr hd

/-- Affine open cover of projective space by standard charts. -/
public def standardAffineOpenCover (n : ℕ) (R : Type u) [CommRing R] :
    (ProjectiveSpace n R).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (fun i ↦ MvPolynomial.isHomogeneous_X R i) (fun _ ↦ zero_lt_one)
    (irrelevant_le_span_X n R)

/-- Projective space is proper over its affine base. -/
instance (n : ℕ) (R : Type u) [CommRing R] : IsProper (toSpec n R) := by
  unfold toSpec
  letI : IsScalarTower R
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)
      (MvPolynomial (Fin (n + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun r : R ↦
      show algebraMap R (MvPolynomial (Fin (n + 1)) R) r =
        algebraMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)
          (MvPolynomial (Fin (n + 1)) R)
          (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) r) from rfl
  haveI : Algebra.FiniteType
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)
      (MvPolynomial (Fin (n + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)
      (MvPolynomial (Fin (n + 1)) R)
  let f : R →+* MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0 := algebraMap R _
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply MvPolynomial.C_injective (Fin (n + 1)) R
      exact congrArg Subtype.val hxy
    · intro x
      have hx : x.1 ∈ (1 : Submodule R (MvPolynomial (Fin (n + 1)) R)) := by
        rw [← MvPolynomial.homogeneousSubmodule_zero]
        exact x.2
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx
      refine ⟨r, Subtype.ext ?_⟩
      exact hr
  letI : IsIso (CommRingCat.ofHom f) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hf
  infer_instance

end ProjectiveSpace

/-- The scheme `ℙᵐ_R ×_{Spec R} ℙⁿ_R`. -/
public abbrev BiprojectiveSpace (m n : ℕ) (R : Type u) [CommRing R] : Scheme.{u} :=
  pullback (ProjectiveSpace.toSpec m R) (ProjectiveSpace.toSpec n R)

namespace BiprojectiveSpace

/-- First projection. -/
public abbrev fst (m n : ℕ) (R : Type u) [CommRing R] :
    BiprojectiveSpace m n R ⟶ ProjectiveSpace m R :=
  pullback.fst (ProjectiveSpace.toSpec m R) (ProjectiveSpace.toSpec n R)

/-- Second projection. -/
public abbrev snd (m n : ℕ) (R : Type u) [CommRing R] :
    BiprojectiveSpace m n R ⟶ ProjectiveSpace n R :=
  pullback.snd (ProjectiveSpace.toSpec m R) (ProjectiveSpace.toSpec n R)

/-- Structure morphism to the base. -/
public def toSpec (m n : ℕ) (R : Type u) [CommRing R] :
    BiprojectiveSpace m n R ⟶ Spec (.of R) :=
  fst m n R ≫ ProjectiveSpace.toSpec m R

instance (m n : ℕ) (R : Type u) [CommRing R] :
    (BiprojectiveSpace m n R).CanonicallyOver (Spec (.of R)) where
  hom := toSpec m n R

instance (m n : ℕ) (R : Type u) [CommRing R] : IsProper (fst m n R) := inferInstance
instance (m n : ℕ) (R : Type u) [CommRing R] : IsProper (snd m n R) := inferInstance
instance (m n : ℕ) (R : Type u) [CommRing R] : IsProper (toSpec m n R) := by
  unfold toSpec
  infer_instance

end BiprojectiveSpace

/-! ## Cox coordinates and the incidence equation -/

/-- The two blocks of Cox coordinates for `ℙᵐ × ℙⁿ`. -/
public abbrev BiprojectiveCoordinate (m n : ℕ) := Sum (Fin (m + 1)) (Fin (n + 1))

/-- Standard `ℕ × ℕ` weight on Cox coordinates. -/
public def bidegreeWeight {m n : ℕ} : BiprojectiveCoordinate m n → ℕ × ℕ
  | .inl _ => (1, 0)
  | .inr _ => (0, 1)

/-- Bihomogeneous of bidegree `(a, b)`. -/
public def IsBihomogeneousOfBidegree {m n : ℕ} {R : Type*} [CommSemiring R]
    (a b : ℕ) (F : MvPolynomial (BiprojectiveCoordinate m n) R) : Prop :=
  F.IsWeightedHomogeneous bidegreeWeight (a, b)

/-- The incidence equation `u · F₀ + v · F₁` on Cox coordinates of `ℙ² × ℙ¹`.

Indices: `inl 0,1,2` are plane coordinates `X,Y,Z`; `inr 0,1` are pencil coordinates `u,v`.
For homogeneous cubics this is bihomogeneous of bidegree `(3, 1)` (note (3.2)). -/
public noncomputable def incidenceEquation {R : Type*} [CommSemiring R]
    (F₀ F₁ : MvPolynomial (Fin 3) R) :
    MvPolynomial (BiprojectiveCoordinate 2 1) R :=
  MvPolynomial.X (.inr 0) * MvPolynomial.rename Sum.inl F₀ +
    MvPolynomial.X (.inr 1) * MvPolynomial.rename Sum.inl F₁

/-- Evaluation of the incidence equation on a biprojective point `(x, y)`. -/
public theorem eval_incidenceEquation {R : Type*} [CommSemiring R]
    (F₀ F₁ : MvPolynomial (Fin 3) R) (x : Fin 3 → R) (y : Fin 2 → R) :
    MvPolynomial.eval (Sum.elim x y) (incidenceEquation F₀ F₁) =
      y 0 * MvPolynomial.eval x F₀ + y 1 * MvPolynomial.eval x F₁ := by
  simp [incidenceEquation, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr]

/-- Polynomial form of the rational inverse of Lemma 3.1: the section
`[F₁(x) : -F₀(x)]` lands on the incidence locus. -/
public theorem eval_incidenceEquation_inverseSection {R : Type*} [CommRing R]
    (F₀ F₁ : MvPolynomial (Fin 3) R) (x : Fin 3 → R) :
    MvPolynomial.eval (Sum.elim x ![MvPolynomial.eval x F₁, -MvPolynomial.eval x F₀])
      (incidenceEquation F₀ F₁) = 0 := by
  simp [eval_incidenceEquation]
  ring

/-! ## Affine incidence ring (chart `Z = 1`, `u = 1`) -/

variable {k : Type u} [Field k]

/-- Affine coordinate ring of the plane: `k[x, y]`. -/
public abbrev PlaneRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k

/-- The linear pencil polynomial `C f₁ · X + C f₀ ∈ (k[x,y])[X]`. -/
public noncomputable def pencilPoly (f₀ f₁ : PlaneRing k) : Polynomial (PlaneRing k) :=
  Polynomial.C f₁ * Polynomial.X + Polynomial.C f₀

/-- Affine incidence ring: `k[x,y,z] / (f₀ + z f₁)`. -/
public abbrev AffineIncidenceRing (f₀ f₁ : PlaneRing k) : Type u :=
  AdjoinRoot (pencilPoly f₀ f₁)

/-- Affine incidence scheme. -/
public noncomputable abbrev affineIncidence (f₀ f₁ : PlaneRing k) : Scheme.{u} :=
  Spec (.of (AffineIncidenceRing f₀ f₁))

/-- The affine plane `𝔸²_k = Spec k[x,y]`. -/
public noncomputable abbrev affinePlane (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (PlaneRing k))

/-- Structure map `k[x,y] → AdjoinRoot(f₀ + z f₁)`. -/
public noncomputable def planeToIncidence (f₀ f₁ : PlaneRing k) :
    PlaneRing k →+* AffineIncidenceRing f₀ f₁ :=
  AdjoinRoot.of (pencilPoly f₀ f₁)

/-- Projection morphism of affine schemes `Γ_aff → 𝔸²`. -/
public noncomputable def affineIncidenceProj (f₀ f₁ : PlaneRing k) :
    affineIncidence f₀ f₁ ⟶ affinePlane k :=
  Spec.map (CommRingCat.ofHom (planeToIncidence f₀ f₁))

/-- The pencil parameter `z` in the affine incidence ring. -/
public noncomputable def incidenceParameter (f₀ f₁ : PlaneRing k) :
    AffineIncidenceRing f₀ f₁ :=
  AdjoinRoot.root (pencilPoly f₀ f₁)

/-- The defining relation `f₁ · z + f₀ = 0`. -/
public theorem incidence_relation (f₀ f₁ : PlaneRing k) :
    planeToIncidence f₀ f₁ f₁ * incidenceParameter f₀ f₁ +
      planeToIncidence f₀ f₁ f₀ = 0 := by
  dsimp only [planeToIncidence, incidenceParameter, pencilPoly]
  have h := AdjoinRoot.eval₂_root (Polynomial.C f₁ * Polynomial.X + Polynomial.C f₀)
  -- expand fully
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  exact h

/-! ## Integrality under genericity

**Genericity hypothesis** (`PencilGeneric f₀ f₁`): `f₁ ≠ 0` and every common divisor of
`f₀` and `f₁` in `k[x,y]` is a unit.  Then `C f₁ · X + C f₀` is irreducible of degree 1, hence
prime in the UFD `(k[x,y])[X]`, so `AdjoinRoot` is a domain.
-/

/-- Genericity for the affine pencil. -/
public structure PencilGeneric (f₀ f₁ : PlaneRing k) : Prop where
  f₁_ne_zero : f₁ ≠ 0
  isRelPrime : IsRelPrime f₁ f₀

/-- Under genericity, the linear pencil polynomial is irreducible. -/
public theorem irreducible_pencilPoly {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    Irreducible (pencilPoly f₀ f₁) :=
  Polynomial.irreducible_C_mul_X_add_C h.f₁_ne_zero h.isRelPrime

/-- Under genericity, the linear pencil polynomial is prime. -/
public theorem prime_pencilPoly {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    Prime (pencilPoly f₀ f₁) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_pencilPoly h)

/-- Under genericity, the affine incidence ring is a domain. -/
public theorem isDomain_affineIncidenceRing {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    IsDomain (AffineIncidenceRing f₀ f₁) :=
  AdjoinRoot.isDomain_of_prime (prime_pencilPoly h)

/-- Under genericity, the affine incidence scheme is integral. -/
public theorem isIntegral_affineIncidence {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    AlgebraicGeometry.IsIntegral (affineIncidence f₀ f₁) := by
  letI : IsDomain (AffineIncidenceRing f₀ f₁) := isDomain_affineIncidenceRing h
  dsimp [affineIncidence]
  exact inferInstance

/-! ## Explicit inverse on `D(f₁)` (algebraic form of Lemma 3.1)

The ring map `AdjoinRoot → Localization.Away f₁` sending the adjoined root to
`-f₀ / f₁` realises the rational inverse of the projection on the open where `f₁` is
inverted.  Combined with injectivity of `planeToIncidence` under genericity, this yields
dominance of the affine projection.
-/

/-- Witness that `f₁` lies in the submonoid of powers of itself. -/
theorem f₁_mem_powers (f₁ : PlaneRing k) : f₁ ∈ Submonoid.powers f₁ :=
  Submonoid.mem_powers f₁

/-- The rational value `-f₀ / f₁` as a localisation element `mk' (-f₀) ⟨f₁⟩`. -/
public noncomputable def inverseParameter (f₀ f₁ : PlaneRing k) : Localization.Away f₁ :=
  IsLocalization.mk' (Localization.Away f₁) (-f₀) ⟨f₁, f₁_mem_powers f₁⟩

/-- The evaluation identity used to build `incidenceToPlaneAway`. -/
theorem eval₂_inverseParameter (f₀ f₁ : PlaneRing k) :
    (pencilPoly f₀ f₁).eval₂ (algebraMap (PlaneRing k) (Localization.Away f₁))
      (inverseParameter f₀ f₁) = 0 := by
  simp only [pencilPoly, inverseParameter, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  have hmul :
      algebraMap (PlaneRing k) (Localization.Away f₁) f₁ *
        IsLocalization.mk' (Localization.Away f₁) (-f₀) ⟨f₁, f₁_mem_powers f₁⟩ =
        algebraMap (PlaneRing k) (Localization.Away f₁) (-f₀) :=
    IsLocalization.mk'_spec' (Localization.Away f₁) (-f₀) ⟨f₁, f₁_mem_powers f₁⟩
  rw [hmul, map_neg]
  ring

/-- Evaluation at `z = -f₀ / f₁` in the localisation of the plane at `f₁`. -/
public noncomputable def incidenceToPlaneAway (f₀ f₁ : PlaneRing k) :
    AffineIncidenceRing f₀ f₁ →+* Localization.Away f₁ :=
  AdjoinRoot.lift (algebraMap (PlaneRing k) (Localization.Away f₁))
    (inverseParameter f₀ f₁) (eval₂_inverseParameter f₀ f₁)

theorem incidenceToPlaneAway_comp_of (f₀ f₁ : PlaneRing k) :
    (incidenceToPlaneAway f₀ f₁).comp (planeToIncidence f₀ f₁) =
      algebraMap (PlaneRing k) (Localization.Away f₁) :=
  AdjoinRoot.lift_comp_of (h := eval₂_inverseParameter f₀ f₁)

theorem incidenceToPlaneAway_root (f₀ f₁ : PlaneRing k) :
    incidenceToPlaneAway f₀ f₁ (incidenceParameter f₀ f₁) = inverseParameter f₀ f₁ :=
  AdjoinRoot.lift_root (h := eval₂_inverseParameter f₀ f₁)

/-- The inverse map sends `of f₁` to a unit (namely `f₁` itself in the localisation). -/
theorem isUnit_incidenceToPlaneAway_f₁ (f₀ f₁ : PlaneRing k) :
    IsUnit (incidenceToPlaneAway f₀ f₁ (planeToIncidence f₀ f₁ f₁)) := by
  have h : incidenceToPlaneAway f₀ f₁ (planeToIncidence f₀ f₁ f₁) =
      algebraMap (PlaneRing k) (Localization.Away f₁) f₁ :=
    congrArg (fun g : PlaneRing k →+* Localization.Away f₁ => g f₁)
      (incidenceToPlaneAway_comp_of f₀ f₁)
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit f₁

/-! ## Injectivity of the structure map and dominance -/

/-- Under genericity, `planeToIncidence` is injective. -/
public theorem planeToIncidence_injective {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    Function.Injective (planeToIncidence f₀ f₁) := by
  intro a b hab
  have hsub : planeToIncidence f₀ f₁ (a - b) = 0 := by
    simp [map_sub, hab]
  have hker : pencilPoly f₀ f₁ ∣ Polynomial.C (a - b) := by
    rw [← AdjoinRoot.mk_eq_zero]
    simpa [planeToIncidence, AdjoinRoot.algebraMap_eq] using hsub
  obtain ⟨q, hq⟩ := hker
  by_cases hab0 : a - b = 0
  · exact sub_eq_zero.mp hab0
  · have hCne : Polynomial.C (a - b) ≠ 0 := by
      rw [Ne, Polynomial.C_eq_zero]
      exact hab0
    have hpne : pencilPoly f₀ f₁ ≠ 0 := (irreducible_pencilPoly h).ne_zero
    have hqne : q ≠ 0 := fun hq0 => by
      rw [hq0, mul_zero] at hq
      exact hCne hq
    haveI : IsDomain (PlaneRing k) := inferInstance
    have hdeg_p : (pencilPoly f₀ f₁).natDegree = 1 := by
      simp only [pencilPoly]
      compute_degree!
      exact h.f₁_ne_zero
    have hsum : (pencilPoly f₀ f₁).natDegree + q.natDegree =
        (Polynomial.C (a - b)).natDegree := by
      rw [← Polynomial.natDegree_mul hpne hqne, hq]
    simp only [hdeg_p, Polynomial.natDegree_C] at hsum
    exact absurd hsum (by lia)

/-- Under genericity, the affine projection is dominant. -/
public theorem isDominant_affineIncidenceProj {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    AlgebraicGeometry.IsDominant (affineIncidenceProj f₀ f₁) := by
  letI : IsDomain (AffineIncidenceRing f₀ f₁) := isDomain_affineIncidenceRing h
  constructor
  -- The underlying point-map of `Spec.map` is definitionally `PrimeSpectrum.comap`.
  change DenseRange (PrimeSpectrum.comap (planeToIncidence f₀ f₁))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro x hx
  have hx0 : planeToIncidence f₀ f₁ x = 0 := by
    simpa [RingHom.mem_ker] using hx
  have : x = 0 := (planeToIncidence_injective h) (by simpa using hx0)
  simp [this]

/-- **Ring-level content of Lemma 3.1.**  The map `incidenceToPlaneAway` realises the rational
inverse `z ↦ -f₀/f₁` of the affine projection on the open where `f₁` is inverted: it is a
ring homomorphism sending the adjoined pencil parameter to that rational function and
restricting to the canonical localisation map on the plane coordinates. -/
public theorem lemma_3_1_affine_inverse (f₀ f₁ : PlaneRing k) :
    (incidenceToPlaneAway f₀ f₁).comp (planeToIncidence f₀ f₁) =
        algebraMap (PlaneRing k) (Localization.Away f₁) ∧
      incidenceToPlaneAway f₀ f₁ (incidenceParameter f₀ f₁) = inverseParameter f₀ f₁ ∧
      IsUnit (incidenceToPlaneAway f₀ f₁ (planeToIncidence f₀ f₁ f₁)) :=
  ⟨incidenceToPlaneAway_comp_of f₀ f₁, incidenceToPlaneAway_root f₀ f₁,
    isUnit_incidenceToPlaneAway_f₁ f₀ f₁⟩

/-! ## Localization isomorphism `R[1/f₁] ≃ A[1/φ(f₁)]`

The relation `f₁ · z + f₀ = 0` becomes `z = -f₀/f₁` after inverting `f₁`.  The localization of
`planeToIncidence` at `f₁` is therefore a ring isomorphism, giving the affine form of Lemma 3.1.
-/

/-- From the incidence relation: `φ(f₁) · z = -φ(f₀)`. -/
theorem planeToIncidence_mul_root (f₀ f₁ : PlaneRing k) :
    planeToIncidence f₀ f₁ f₁ * incidenceParameter f₀ f₁ =
      -planeToIncidence f₀ f₁ f₀ := by
  have h := incidence_relation f₀ f₁
  linear_combination h

/-- Powers of the relation: `φ(f₁)^n · z^n = φ((-f₀)^n)`. -/
theorem planeToIncidence_pow_mul_root_pow (f₀ f₁ : PlaneRing k) (n : ℕ) :
    planeToIncidence f₀ f₁ (f₁ ^ n) * incidenceParameter f₀ f₁ ^ n =
      planeToIncidence f₀ f₁ ((-f₀) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- φ(f₁)^{n+1} z^{n+1} = (φ(f₁)^n z^n) · (φ(f₁) z) = φ((-f₀)^n) · (-φ(f₀))
    have h1 :
        planeToIncidence f₀ f₁ (f₁ ^ n.succ) * incidenceParameter f₀ f₁ ^ n.succ =
          (planeToIncidence f₀ f₁ (f₁ ^ n) * incidenceParameter f₀ f₁ ^ n) *
            (planeToIncidence f₀ f₁ f₁ * incidenceParameter f₀ f₁) := by
      simp only [pow_succ, map_mul]
      ring
    rw [h1, ih, planeToIncidence_mul_root]
    simp [map_neg, map_mul, pow_succ]
/-- `mk (C c * X ^ n) = φ(c) · z^n`. -/
theorem adjoinRoot_mk_C_mul_X_pow (f₀ f₁ : PlaneRing k) (c : PlaneRing k) (n : ℕ) :
    AdjoinRoot.mk (pencilPoly f₀ f₁) (Polynomial.C c * Polynomial.X ^ n) =
      planeToIncidence f₀ f₁ c * incidenceParameter f₀ f₁ ^ n := by
  simp [planeToIncidence, incidenceParameter, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_pow,
    map_mul]

/-- Clearing denominators in the incidence ring. -/
theorem exists_plane_mul_of_adjoin (f₀ f₁ : PlaneRing k) (a : AffineIncidenceRing f₀ f₁) :
    ∃ (b : PlaneRing k) (m : ℕ),
      planeToIncidence f₀ f₁ b =
        planeToIncidence f₀ f₁ f₁ ^ m * a := by
  refine AdjoinRoot.induction_on (f := pencilPoly f₀ f₁) a fun p => ?_
  let m : ℕ := p.natDegree
  let b : PlaneRing k := ∑ n ∈ p.support, p.coeff n * f₁ ^ (m - n) * (-f₀) ^ n
  refine ⟨b, m, ?_⟩
  have hrepr :
      AdjoinRoot.mk (pencilPoly f₀ f₁) p =
        ∑ n ∈ p.support,
          planeToIncidence f₀ f₁ (p.coeff n) * incidenceParameter f₀ f₁ ^ n := by
    conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
    simp only [map_sum, adjoinRoot_mk_C_mul_X_pow]
  have hφb :
      planeToIncidence f₀ f₁ b =
        ∑ n ∈ p.support,
          planeToIncidence f₀ f₁ (p.coeff n) *
            planeToIncidence f₀ f₁ (f₁ ^ (m - n)) *
            planeToIncidence f₀ f₁ ((-f₀) ^ n) := by
    dsimp [b]
    simp only [map_sum, map_mul]
  rw [hφb, hrepr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnle : n ≤ m := Polynomial.le_natDegree_of_mem_supp n hn
  have hsplit : (f₁ : PlaneRing k) ^ m = f₁ ^ (m - n) * f₁ ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hnle]
  have hpow :
      planeToIncidence f₀ f₁ f₁ ^ m * incidenceParameter f₀ f₁ ^ n =
        planeToIncidence f₀ f₁ (f₁ ^ (m - n)) *
          planeToIncidence f₀ f₁ ((-f₀) ^ n) := by
    have : planeToIncidence f₀ f₁ f₁ ^ m =
        planeToIncidence f₀ f₁ (f₁ ^ (m - n)) * planeToIncidence f₀ f₁ (f₁ ^ n) := by
      rw [← map_mul, ← hsplit, map_pow]
    rw [this, mul_assoc, planeToIncidence_pow_mul_root_pow]
  calc
    planeToIncidence f₀ f₁ (p.coeff n) * planeToIncidence f₀ f₁ (f₁ ^ (m - n)) *
        planeToIncidence f₀ f₁ ((-f₀) ^ n) =
      planeToIncidence f₀ f₁ (p.coeff n) *
        (planeToIncidence f₀ f₁ (f₁ ^ (m - n)) * planeToIncidence f₀ f₁ ((-f₀) ^ n)) := by
      ring
    _ = planeToIncidence f₀ f₁ (p.coeff n) *
        (planeToIncidence f₀ f₁ f₁ ^ m * incidenceParameter f₀ f₁ ^ n) := by
      rw [← hpow]
    _ = planeToIncidence f₀ f₁ f₁ ^ m *
        (planeToIncidence f₀ f₁ (p.coeff n) * incidenceParameter f₀ f₁ ^ n) := by
      ring

/-- Localization of the structure map at `f₁`. -/
public noncomputable def planeAwayMap (f₀ f₁ : PlaneRing k) :
    Localization.Away f₁ →+* Localization.Away (planeToIncidence f₀ f₁ f₁) :=
  IsLocalization.Away.map (Localization.Away f₁)
    (Localization.Away (planeToIncidence f₀ f₁ f₁)) (planeToIncidence f₀ f₁) f₁

/-- Under genericity, `planeAwayMap` is bijective. -/
public theorem planeAwayMap_bijective {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    Function.Bijective (planeAwayMap f₀ f₁) := by
  constructor
  · dsimp [planeAwayMap]
    rw [IsLocalization.Away.map_injective_iff]
    intro a ha
    have ha0 : a = 0 := (planeToIncidence_injective h) (by simpa using ha)
    exact ⟨0, by simp [ha0]⟩
  · dsimp [planeAwayMap]
    rw [IsLocalization.Away.map_surjective_iff]
    intro a
    obtain ⟨b, m, hb⟩ := exists_plane_mul_of_adjoin f₀ f₁ a
    exact ⟨b, m, hb⟩

/-- Ring equivalence `R[1/f₁] ≃+* A[1/φ(f₁)]`. -/
public noncomputable def planeAwayEquiv {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    Localization.Away f₁ ≃+* Localization.Away (planeToIncidence f₀ f₁ f₁) :=
  RingEquiv.ofBijective (planeAwayMap f₀ f₁) (planeAwayMap_bijective h)

/-- Inverse localization map, lifting `incidenceToPlaneAway`. -/
public noncomputable def incidenceAwayLift (f₀ f₁ : PlaneRing k) :
    Localization.Away (planeToIncidence f₀ f₁ f₁) →+* Localization.Away f₁ :=
  IsLocalization.Away.lift (planeToIncidence f₀ f₁ f₁) (isUnit_incidenceToPlaneAway_f₁ f₀ f₁)

theorem incidenceAwayLift_comp_planeAwayMap (f₀ f₁ : PlaneRing k) :
    (incidenceAwayLift f₀ f₁).comp (planeAwayMap f₀ f₁) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f₁)
  apply RingHom.ext
  intro x
  dsimp [planeAwayMap, incidenceAwayLift]
  have hle :
      Submonoid.powers f₁ ≤
        (Submonoid.powers (planeToIncidence f₀ f₁ f₁)).comap (planeToIncidence f₀ f₁) := by
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    exact ⟨n, by simp⟩
  rw [IsLocalization.Away.map, IsLocalization.map_eq (hy := hle),
    IsLocalization.Away.lift_eq]
  have hcomp := incidenceToPlaneAway_comp_of f₀ f₁
  simpa [RingHom.comp_apply] using congrArg (fun g : PlaneRing k →+* Localization.Away f₁ => g x) hcomp

theorem planeAwayMap_comp_incidenceAwayLift {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    (planeAwayMap f₀ f₁).comp (incidenceAwayLift f₀ f₁) = RingHom.id _ := by
  have hlm : ∀ x, incidenceAwayLift f₀ f₁ (planeAwayMap f₀ f₁ x) = x := fun x => by
    simpa [RingHom.comp_apply] using
      congrArg (fun g : _ →+* _ => g x) (incidenceAwayLift_comp_planeAwayMap f₀ f₁)
  refine RingHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (planeAwayMap_bijective h).2 y
  show planeAwayMap f₀ f₁ (incidenceAwayLift f₀ f₁ (planeAwayMap f₀ f₁ x)) = planeAwayMap f₀ f₁ x
  rw [hlm x]

theorem incidenceAwayLift_eq_planeAwayEquiv_symm {f₀ f₁ : PlaneRing k}
    (h : PencilGeneric f₀ f₁) :
    incidenceAwayLift f₀ f₁ = (planeAwayEquiv h).symm.toRingHom := by
  have hml : ∀ y, planeAwayMap f₀ f₁ (incidenceAwayLift f₀ f₁ y) = y := fun y => by
    simpa [RingHom.comp_apply] using
      congrArg (fun g : _ →+* _ => g y) (planeAwayMap_comp_incidenceAwayLift h)
  ext x
  apply (planeAwayMap_bijective h).1
  rw [hml x]
  exact ((planeAwayEquiv h).apply_symm_apply x).symm

theorem planeToIncidence_f₁_ne_zero {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    planeToIncidence f₀ f₁ f₁ ≠ 0 := by
  intro hf
  exact h.f₁_ne_zero ((planeToIncidence_injective h) (by simpa using hf))

/-- Under genericity, `incidenceToPlaneAway` is injective. -/
public theorem incidenceToPlaneAway_injective {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    Function.Injective (incidenceToPlaneAway f₀ f₁) := by
  letI : IsDomain (AffineIncidenceRing f₀ f₁) := isDomain_affineIncidenceRing h
  intro a b hab
  have hlift_inj : Function.Injective (incidenceAwayLift f₀ f₁) := by
    rw [incidenceAwayLift_eq_planeAwayEquiv_symm h]
    exact (planeAwayEquiv h).symm.injective
  have hM :
      Submonoid.powers (planeToIncidence f₀ f₁ f₁) ≤
        nonZeroDivisors (AffineIncidenceRing f₀ f₁) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (planeToIncidence_f₁_ne_zero h)
  have halg_inj :
      Function.Injective
        (algebraMap (AffineIncidenceRing f₀ f₁)
          (Localization.Away (planeToIncidence f₀ f₁ f₁))) :=
    IsLocalization.injective _ hM
  have hfactor (x : AffineIncidenceRing f₀ f₁) :
      incidenceToPlaneAway f₀ f₁ x =
        incidenceAwayLift f₀ f₁
          (algebraMap (AffineIncidenceRing f₀ f₁)
            (Localization.Away (planeToIncidence f₀ f₁ f₁)) x) :=
    (IsLocalization.Away.lift_eq (planeToIncidence f₀ f₁ f₁)
      (isUnit_incidenceToPlaneAway_f₁ f₀ f₁) x).symm
  rw [hfactor a, hfactor b] at hab
  exact halg_inj (hlift_inj hab)


/-! ## Affine `PartialIso` (Lemma 3.1 on the chart)

The localization isomorphism yields an isomorphism of basic opens
`D(φ f₁) ≅ Spec A_φ ≅ Spec R_f ≅ D(f₁)`, packaged as a `PartialIso`.
-/

theorem basicOpen_nonempty_of_ne_zero {R : Type u} [CommRing R] [IsDomain R] {f : R}
    (hf : f ≠ 0) : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)).Nonempty := by
  refine ⟨⊥, ?_⟩
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
  exact hf

theorem dense_basicOpen_of_ne_zero {R : Type u} [CommRing R] [IsDomain R] {f : R}
    (hf : f ≠ 0) : Dense (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  refine PrimeSpectrum.isOpen_basicOpen.dense ?_
  exact basicOpen_nonempty_of_ne_zero hf

/-- Source open: `D(φ(f₁)) ⊆ Γ_aff`. -/
public noncomputable def affineIncidenceAwayOpen (f₀ f₁ : PlaneRing k) :
    (affineIncidence f₀ f₁).Opens :=
  PrimeSpectrum.basicOpen (planeToIncidence f₀ f₁ f₁)

/-- Target open: `D(f₁) ⊆ 𝔸²`. -/
public noncomputable def affinePlaneAwayOpen (f₁ : PlaneRing k) : (affinePlane k).Opens :=
  PrimeSpectrum.basicOpen f₁

/-- `CommRingCat` isomorphism underlying `planeAwayEquiv`. -/
public noncomputable def planeAwayCommRingIso {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    CommRingCat.of (Localization.Away f₁) ≅
      CommRingCat.of (Localization.Away (planeToIncidence f₀ f₁ f₁)) :=
  (planeAwayEquiv h).toCommRingCatIso

/-- Basic-open isomorphism `D(φ f₁) ≅ D(f₁)`. -/
public noncomputable def affineIncidenceAwayIso {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    Scheme.Opens.toScheme (X := affineIncidence f₀ f₁) (affineIncidenceAwayOpen f₀ f₁) ≅
      Scheme.Opens.toScheme (X := affinePlane k) (affinePlaneAwayOpen f₁) :=
  basicOpenIsoSpecAway (R := .of (AffineIncidenceRing f₀ f₁))
      (planeToIncidence f₀ f₁ f₁) ≪≫
    asIso (Spec.map (planeAwayCommRingIso h).hom) ≪≫
      (basicOpenIsoSpecAway (R := .of (PlaneRing k)) f₁).symm

/-- **Affine form of Lemma 3.1 as a `PartialIso`.** -/
public noncomputable def affineIncidencePartialIso {f₀ f₁ : PlaneRing k}
    (h : PencilGeneric f₀ f₁) :
    Scheme.PartialIso (affineIncidence f₀ f₁) (affinePlane k) where
  source := affineIncidenceAwayOpen f₀ f₁
  dense_source := by
    letI : IsDomain (AffineIncidenceRing f₀ f₁) := isDomain_affineIncidenceRing h
    exact dense_basicOpen_of_ne_zero (planeToIncidence_f₁_ne_zero h)
  target := affinePlaneAwayOpen f₁
  dense_target := dense_basicOpen_of_ne_zero h.f₁_ne_zero
  iso := affineIncidenceAwayIso h

/-- Under genericity, `Γ_aff` is birational to `𝔸²`. -/
public theorem birational_affineIncidence {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    Scheme.Birational (affineIncidence f₀ f₁) (affinePlane k) :=
  ⟨affineIncidencePartialIso h⟩

/-- Explicit rational inverse of Lemma 3.1 as a partial map on `D(f₁)`. -/
public noncomputable def affineInversePartialMap {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    (affinePlane k).PartialMap (affineIncidence f₀ f₁) :=
  (affineIncidencePartialIso h).symm.toPartialMap

/-- Explicit rational inverse as a rational map. -/
public noncomputable def affineInverseRationalMap {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    affinePlane k ⤏ affineIncidence f₀ f₁ :=
  (affineIncidencePartialIso h).symm.toRationalMap

/-- Projection as a rational map. -/
public noncomputable def affineIncidenceProjRationalMap (f₀ f₁ : PlaneRing k) :
    affineIncidence f₀ f₁ ⤏ affinePlane k :=
  (affineIncidenceProj f₀ f₁).toRationalMap

/-- Partial-iso projection as a rational map. -/
public noncomputable def affineIncidencePartialIsoRationalMap {f₀ f₁ : PlaneRing k}
    (h : PencilGeneric f₀ f₁) :
    affineIncidence f₀ f₁ ⤏ affinePlane k :=
  (affineIncidencePartialIso h).toRationalMap

/-- The inverse partial map is defined on the dense open `D(f₁)`. -/
public theorem affineInversePartialMap_domain {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    (affineInversePartialMap h).domain = affinePlaneAwayOpen f₁ := by
  dsimp [affineInversePartialMap, Scheme.PartialIso.toPartialMap, Scheme.PartialIso.symm]
  rfl

/-- Package: dominance, birationality, inverse domain, localization iso.
Affine content of note Lemma 3.1 / (3.2). -/
public theorem lemma_3_1_affine {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    AlgebraicGeometry.IsDominant (affineIncidenceProj f₀ f₁) ∧
      Scheme.Birational (affineIncidence f₀ f₁) (affinePlane k) ∧
      (affineInversePartialMap h).domain = affinePlaneAwayOpen f₁ ∧
      Function.Bijective (planeAwayMap f₀ f₁) :=
  ⟨isDominant_affineIncidenceProj h, birational_affineIncidence h,
    affineInversePartialMap_domain h, planeAwayMap_bijective h⟩

/-- Algebraic form of generic degree 1: localization of the structure map is an isomorphism. -/
public theorem planeAwayEquiv_bijective {f₀ f₁ : PlaneRing k} (h : PencilGeneric f₀ f₁) :
    Function.Bijective (planeAwayEquiv h).toRingHom :=
  (planeAwayEquiv h).bijective

/-! ## Projective packaging -/

/-- Ambient product `ℙ²_k × ℙ¹_k` of note (3.2). -/
public abbrev ambient (k : Type u) [Field k] : Scheme.{u} :=
  BiprojectiveSpace 2 1 k

/-- Projection of the ambient product onto the plane factor. -/
public abbrev ambientFst (k : Type u) [Field k] : ambient k ⟶ ProjectiveSpace 2 k :=
  BiprojectiveSpace.fst 2 1 k

/-- Incidence equation for a general pair of ternary forms. -/
public noncomputable abbrev incidencePoly (F₀ F₁ : MvPolynomial (Fin 3) k) :
    MvPolynomial (BiprojectiveCoordinate 2 1) k :=
  incidenceEquation F₀ F₁

/-- Concrete forms of note (3.1). -/
public noncomputable abbrev F₀_rat : MvPolynomial (Fin 3) ℚ :=
  ExplicitUnirational.FunctionField.F₀_rat

public noncomputable abbrev F₁_rat : MvPolynomial (Fin 3) ℚ :=
  ExplicitUnirational.FunctionField.F₁_rat

/-- Incidence equation of the rational pencil (3.1)–(3.2). -/
public noncomputable def incidenceEquation_rat : MvPolynomial (BiprojectiveCoordinate 2 1) ℚ :=
  incidenceEquation F₀_rat F₁_rat

/-- Polynomial-level rational inverse for the rational pencil. -/
public theorem inverseSection_rat (x : Fin 3 → ℚ) :
    MvPolynomial.eval (Sum.elim x ![MvPolynomial.eval x F₁_rat, -MvPolynomial.eval x F₀_rat])
      incidenceEquation_rat = 0 :=
  eval_incidenceEquation_inverseSection F₀_rat F₁_rat x

end ExplicitUnirational.CubicPencil
