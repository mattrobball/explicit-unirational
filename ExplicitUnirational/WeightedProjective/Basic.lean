/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.Foundation
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted projective space `ℙ(1,1,2,3)` (WP4)

Constructs the ambient weighted projective space of the del Pezzo surface of degree one as a
scheme, via Mathlib's `Proj` of a weighted graded multivariate polynomial ring.

## Construction

Let `R` be a commutative ring. Write `A = R[u,v,x,y]` with the weighted grading
```
  deg u = deg v = 1,  deg x = 2,  deg y = 3
```
Mathlib supplies `MvPolynomial.weightedHomogeneousSubmodule` and
`MvPolynomial.weightedGradedAlgebra`, so
```
  ℙ(1,1,2,3)_R  :=  Proj (weightedHomogeneousSubmodule R weights)
```
is immediately a scheme. The structure morphism to `Spec R` factors through
`Proj.toSpecZero` and the identification of degree-zero forms with constants.

## Contents (priority order of WP4)

1. The weighted `GradedAlgebra` instance (via Mathlib's `weightedGradedAlgebra`).
2. The scheme `WeightedProjectiveSpace R` and its structure morphism to `Spec R`.
3. The four standard charts `D₊(u)`, `D₊(v)`, `D₊(x)`, `D₊(y)` and their affine coordinate rings.
4. That the four standard charts cover the total space.
5. Weighted hypersurfaces: the homogeneous ideal and the closed zero locus of a
   weighted-homogeneous form (as the complement of `D₊(f)`).

Integrality of the total space, properness, the chartwise Jacobian criterion, weighted
adjunction, and the scheme structure of a hypersurface as `Proj(A/⟨f⟩)` are deferred (scope
discipline of WP4; the last needs a graded-quotient instance that Mathlib does not yet supply).

## Design choice

We specialise to the fixed weights `(1,1,2,3)` rather than a general `P(w₀,…,wₙ)`. The specific
case is what the paper needs; positivity of all four weights is used for the chart degrees and the
irrelevant-ideal comparison. (Foundation records the same weight vector, but it is not yet a
public export, so the weights are restated here.)
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace ExplicitUnirational

open AlgebraicGeometry MvPolynomial
open Finsupp (weight)

/-! ## Weights and graded algebra -/

/-- The weights of the ambient weighted projective space `ℙ(1,1,2,3)`.
Restated from `Foundation` (which is not yet a public export under the module system). -/
def weights : Fin 4 → ℕ := ![1, 1, 2, 3]

@[simp] theorem weights_zero : weights 0 = 1 := rfl
@[simp] theorem weights_one : weights 1 = 1 := rfl
@[simp] theorem weights_two : weights 2 = 2 := rfl
@[simp] theorem weights_three : weights 3 = 3 := rfl

/-- Positive degree of each standard generator (used for chart open immersions). -/
theorem weights_pos (i : Fin 4) : 0 < weights i := by
  fin_cases i <;> decide

/-- The graded pieces of `R[u,v,x,y]` under the weights `(1,1,2,3)`. -/
abbrev delPezzoGraded (R : Type u) [CommRing R] : ℕ → Submodule R (MvPolynomial (Fin 4) R) :=
  weightedHomogeneousSubmodule R weights

/-- `R[u,v,x,y]` with weights `(1,1,2,3)` is a graded algebra. -/
instance delPezzoGradedAlgebra (R : Type u) [CommRing R] :
    GradedAlgebra (delPezzoGraded R) :=
  weightedGradedAlgebra R weights

/-- Each coordinate is weighted-homogeneous of the expected degree. -/
theorem isWeightedHomogeneous_X_weights (R : Type u) [CommRing R] (i : Fin 4) :
    IsWeightedHomogeneous weights (X i : MvPolynomial (Fin 4) R) (weights i) :=
  isWeightedHomogeneous_X (R := R) weights i

/-- Membership form of the previous lemma (what `Proj.awayι` consumes). -/
theorem mem_delPezzoGraded_X (R : Type u) [CommRing R] (i : Fin 4) :
    (X i : MvPolynomial (Fin 4) R) ∈ delPezzoGraded R (weights i) :=
  isWeightedHomogeneous_X_weights R i

/-! ## The scheme `ℙ(1,1,2,3)` -/

/-- Scheme-level weighted projective space `ℙ(1,1,2,3)_R`. -/
abbrev WeightedProjectiveSpace (R : Type u) [CommRing R] : Scheme.{u} :=
  Proj (delPezzoGraded R)

namespace WeightedProjectiveSpace

variable (R : Type u) [CommRing R]

/-- Structure morphism `ℙ(1,1,2,3)_R → Spec R`. -/
def toSpec : WeightedProjectiveSpace R ⟶ Spec (.of R) :=
  Proj.toSpecZero (delPezzoGraded R) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap R (delPezzoGraded R 0)))

instance : (WeightedProjectiveSpace R).CanonicallyOver (Spec (.of R)) where
  hom := toSpec R

/-! ## Standard charts `D₊(Xᵢ)` -/

/-- Degree-zero homogeneous localization at the coordinate `Xᵢ`
(the affine coordinate ring of the `i`-th standard chart). -/
abbrev StandardChartRing (i : Fin 4) : Type u :=
  HomogeneousLocalization.Away (delPezzoGraded R) (X i)

/-- Standard open immersion `Spec (A_(Xᵢ))₀ → ℙ(1,1,2,3)_R`. -/
def standardChartι (i : Fin 4) :
    Spec (.of (StandardChartRing R i)) ⟶ WeightedProjectiveSpace R :=
  Proj.awayι (delPezzoGraded R) (X i)
    (mem_delPezzoGraded_X R i) (weights_pos i)

instance (i : Fin 4) : IsOpenImmersion (standardChartι R i) :=
  inferInstanceAs (IsOpenImmersion
    (Proj.awayι (delPezzoGraded R) (X i)
      (mem_delPezzoGraded_X R i) (weights_pos i)))

/-- The basic open `D₊(Xᵢ)` as an open of the scheme. -/
abbrev standardBasicOpen (i : Fin 4) : (WeightedProjectiveSpace R).Opens :=
  Proj.basicOpen (delPezzoGraded R) (X i)

@[simp]
theorem opensRange_standardChartι (i : Fin 4) :
    (standardChartι R i).opensRange = standardBasicOpen R i :=
  Proj.opensRange_awayι (delPezzoGraded R) (X i)
    (mem_delPezzoGraded_X R i) (weights_pos i)

/-! ## The charts cover -/

/-- Every positive-degree weighted-homogeneous polynomial lies in the ideal generated by the
variables. (All weights are positive, so a multiindex of positive weighted degree is non-zero and
hence has ordinary degree at least one.) -/
theorem irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant (delPezzoGraded R)).toIdeal ≤
      Ideal.span (Set.range (X : Fin 4 → MvPolynomial (Fin 4) R)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd p hp
  change p ∈ idealOfVars (Fin 4) R
  rw [← pow_one (idealOfVars (Fin 4) R), mem_pow_idealOfVars_iff]
  intro m hm
  have hp' : IsWeightedHomogeneous weights p d := hp
  have hwt : weight weights m = d :=
    hp' (by simpa [mem_support_iff] using hm)
  have hm_ne : m ≠ 0 := by
    intro hm0
    subst hm0
    have : (0 : ℕ) = d := by
      simpa [map_zero] using hwt
    exact (Nat.pos_iff_ne_zero.mp hd) this.symm
  have hdeg_pos : 0 < m.degree := by
    rw [pos_iff_ne_zero, ne_eq, Finsupp.degree_eq_zero_iff]
    exact hm_ne
  exact Nat.succ_le_iff.mpr hdeg_pos

/-- Affine open cover of `ℙ(1,1,2,3)_R` by the four standard charts. -/
def standardAffineOpenCover : (WeightedProjectiveSpace R).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan
    (delPezzoGraded R)
    (X : Fin 4 → MvPolynomial (Fin 4) R)
    (fun i ↦ mem_delPezzoGraded_X R i)
    (fun i ↦ weights_pos i)
    (irrelevant_le_span_X R)

/-- The four basic opens `D₊(Xᵢ)` cover the total space. -/
theorem iSup_standardBasicOpen_eq_top :
    ⨆ i : Fin 4, standardBasicOpen R i = ⊤ :=
  Proj.iSup_basicOpen_eq_top (delPezzoGraded R) (X : Fin 4 → MvPolynomial (Fin 4) R)
    (irrelevant_le_span_X R)

/-! ## Weighted hypersurfaces -/

/-- The homogeneous ideal generated by a single weighted-homogeneous polynomial. -/
def hypersurfaceIdeal {d : ℕ} (f : MvPolynomial (Fin 4) R)
    (hf : IsWeightedHomogeneous weights f d) :
    HomogeneousIdeal (delPezzoGraded R) where
  toSubmodule := Ideal.span {f}
  is_homogeneous' := by
    refine Ideal.homogeneous_span (delPezzoGraded R) {f} ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨d, ?_⟩
    simpa [delPezzoGraded, mem_weightedHomogeneousSubmodule] using hf

/-- The closed zero locus `V₊(f) ⊆ ℙ(1,1,2,3)_R`, realised as the complement of `D₊(f)`. -/
def hypersurfaceZeroLocus (f : MvPolynomial (Fin 4) R) :
    Set (WeightedProjectiveSpace R) :=
  (Proj.basicOpen (delPezzoGraded R) f : Set (WeightedProjectiveSpace R))ᶜ

theorem isClosed_hypersurfaceZeroLocus (f : MvPolynomial (Fin 4) R) :
    IsClosed (hypersurfaceZeroLocus (R := R) f) := by
  unfold hypersurfaceZeroLocus
  exact isClosed_compl_iff.mpr (Proj.basicOpen (delPezzoGraded R) f).2

/-- Membership in the hypersurface zero locus: `x ∈ V₊(f)` iff `f` vanishes at `x`. -/
theorem mem_hypersurfaceZeroLocus (f : MvPolynomial (Fin 4) R)
    (x : WeightedProjectiveSpace R) :
    x ∈ hypersurfaceZeroLocus (R := R) f ↔ f ∈ x.asHomogeneousIdeal := by
  simp [hypersurfaceZeroLocus, Proj.mem_basicOpen]

end WeightedProjectiveSpace

/-- The concrete ambient space over `ℚ` used by the del Pezzo construction. -/
abbrev DelPezzoAmbient : Scheme :=
  WeightedProjectiveSpace ℚ

/-- Structure morphism of the rational ambient space. -/
def delPezzoAmbient_toSpec : DelPezzoAmbient ⟶ Spec (.of ℚ) :=
  WeightedProjectiveSpace.toSpec ℚ

end ExplicitUnirational

/-! ## Axiom audit (headline theorems) -/

#print axioms ExplicitUnirational.weights_pos
#print axioms ExplicitUnirational.mem_delPezzoGraded_X
#print axioms ExplicitUnirational.WeightedProjectiveSpace.irrelevant_le_span_X
#print axioms ExplicitUnirational.WeightedProjectiveSpace.iSup_standardBasicOpen_eq_top
#print axioms ExplicitUnirational.WeightedProjectiveSpace.isClosed_hypersurfaceZeroLocus
#print axioms ExplicitUnirational.WeightedProjectiveSpace.mem_hypersurfaceZeroLocus
