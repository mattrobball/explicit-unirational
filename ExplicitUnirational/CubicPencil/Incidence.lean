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
6. Birationality: after localising at `f₁` the projection becomes an isomorphism of basic opens
   (affine form of Lemma 3.1), via the explicit inverse `z = -f₀/f₁`.

The field-theoretic content is in `FunctionField.PencilRationality`. Global scheme-level
birationality of the *projective* projection reduces to the same chart computation once the
projective zero locus is compared with its affine charts; ambient and equation are defined here,
but the global projective `PartialIso` is left for a follow-up that glues charts.
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
public noncomputable def affineIncidence (f₀ f₁ : PlaneRing k) : Scheme.{u} :=
  Spec (.of (AffineIncidenceRing f₀ f₁))

/-- The affine plane `𝔸²_k = Spec k[x,y]`. -/
public noncomputable def affinePlane (k : Type u) [Field k] : Scheme.{u} :=
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
