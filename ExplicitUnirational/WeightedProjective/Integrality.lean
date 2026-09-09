/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.WeightedProjective.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Sober

/-!
# Integrality of weighted projective space and the hypersurface zero locus

Mathlib (v4.32.1) has neither
- `IsDomain (HomogeneousLocalization.Away 𝒜 f)`, nor
- `IsIntegral (Proj 𝒜)`,
so WP4 stopped short of integrality of `ℙ(1,1,2,3)`. This module closes that gap for our
weighted projective space and packages the hypersurface zero locus as a reduced closed subscheme.

## Main results

1. **Homogeneous localization of a domain is a domain.** The degree-zero part of `A[S⁻¹]` injects
   into the ordinary localization, which is a domain when `S ≤ nonZeroDivisors A`. Specialised to
   `Away f` with `f ≠ 0`, and then to the four standard chart rings of `ℙ(1,1,2,3)`.

2. **`IsIntegral (WeightedProjectiveSpace R)`** when `R` is an integral domain
   (with `IsCancelAdd`, so that `MvPolynomial` is a domain). Route:
   - *reduced*: open cover by the four integral affine charts (`IsReduced.of_openCover`);
   - *irreducible*: the zero ideal is a relevant homogeneous prime (generic point) whose closure
     is the whole space (`IsGenericPoint` of `univ`).

3. **Weighted hypersurface as reduced closed subscheme.** Mathlib still has no `GradedRing`
   instance on a quotient by a homogeneous ideal, so `Proj(A/⟨f⟩)` is unavailable. We instead take
   the reduced induced structure on the closed zero locus `V₊(f)` via
   `IdealSheafData.vanishingIdeal`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped AlgebraicGeometry
open TopologicalSpace

universe u

namespace ExplicitUnirational

open AlgebraicGeometry MvPolynomial HomogeneousLocalization
open Finsupp (weight)

/-! ## Homogeneous localization of a domain is a domain -/

namespace HomogeneousLocalizationDomain

variable {ι A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι → σ) [GradedRing 𝒜]

/-- Degree-zero homogeneous localization injects into ordinary localization, so it is a domain
whenever the ambient ring is a domain and the localizing monoid consists of non-zero-divisors. -/
public theorem isDomain_of_le_nonZeroDivisors [IsDomain A] (S : Submonoid A)
    (hS : S ≤ nonZeroDivisors A) :
    IsDomain (HomogeneousLocalization 𝒜 S) := by
  have : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  exact (val_injective (𝒜 := 𝒜) (x := S)).isDomain
    (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))

/-- Homogeneous localization away from a non-zero element of a domain is a domain. -/
public theorem Away.isDomain [IsDomain A] {f : A} (hf : f ≠ 0) :
    IsDomain (Away 𝒜 f) :=
  isDomain_of_le_nonZeroDivisors 𝒜 (Submonoid.powers f)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

end HomogeneousLocalizationDomain

namespace WeightedProjectiveSpace

variable (R : Type u) [CommRing R]

/-! ## Chart rings are domains -/

section Domain

variable [IsDomain R] [IsCancelAdd R]

/-- Each standard chart ring `A_(Xᵢ)₀` is an integral domain. -/
public instance standardChartRing_isDomain (i : Fin 4) :
    IsDomain (StandardChartRing R i) :=
  HomogeneousLocalizationDomain.Away.isDomain (delPezzoGraded R)
    (MvPolynomial.X_ne_zero i)

/-- Each standard chart is an integral scheme. -/
public instance standardChart_isIntegral (i : Fin 4) :
    IsIntegral (Spec (.of (StandardChartRing R i))) :=
  inferInstance

end Domain

/-! ## The generic point of `ℙ(1,1,2,3)` -/

section GenericPoint

variable [IsDomain R]

/-- The irrelevant ideal is not contained in `(0)`, since each coordinate has positive weight and
is non-zero. -/
public theorem not_irrelevant_le_bot :
    ¬ HomogeneousIdeal.irrelevant (delPezzoGraded R) ≤ (⊥ : HomogeneousIdeal (delPezzoGraded R)) := by
  intro h
  have hx : (X (0 : Fin 4) : MvPolynomial (Fin 4) R) ∈
      HomogeneousIdeal.irrelevant (delPezzoGraded R) :=
    HomogeneousIdeal.mem_irrelevant_of_mem (delPezzoGraded R) (weights_pos 0)
      (mem_delPezzoGraded_X R 0)
  have : (X (0 : Fin 4) : MvPolynomial (Fin 4) R) ∈
      (⊥ : HomogeneousIdeal (delPezzoGraded R)).toIdeal := h hx
  simp only [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at this
  exact MvPolynomial.X_ne_zero (0 : Fin 4) this

/-- The zero ideal as a relevant homogeneous prime (generic point of the projective spectrum).
`IsCancelAdd` is not required for this construction; it is only needed later so that
`MvPolynomial` is a domain when building chart-domain instances. -/
public def genericPointPS : ProjectiveSpectrum (delPezzoGraded R) where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le := not_irrelevant_le_bot R

/-- The zero ideal is the generic point of the whole projective spectrum. -/
public theorem isGenericPoint_genericPointPS :
    IsGenericPoint (genericPointPS R)
      (Set.univ : Set (ProjectiveSpectrum (delPezzoGraded R))) := by
  rw [isGenericPoint_def]
  have hclosure :=
    ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure (delPezzoGraded R)
      ({genericPointPS R} : Set (ProjectiveSpectrum (delPezzoGraded R)))
  rw [← hclosure, ProjectiveSpectrum.vanishingIdeal_singleton]
  change ProjectiveSpectrum.zeroLocus (delPezzoGraded R)
      ((genericPointPS R).asHomogeneousIdeal : Set _) = Set.univ
  simp only [genericPointPS, HomogeneousIdeal.coe_bot]
  exact ProjectiveSpectrum.zeroLocus_singleton_zero (delPezzoGraded R)

/-- The generic point of the scheme `ℙ(1,1,2,3)_R` (carrier = projective spectrum). -/
public def genericPoint : WeightedProjectiveSpace R :=
  genericPointPS R

/-- The zero ideal is the generic point of the scheme `ℙ(1,1,2,3)_R`. -/
public theorem isGenericPoint_genericPoint :
    IsGenericPoint (genericPoint R) (Set.univ : Set (WeightedProjectiveSpace R)) := by
  -- Carrier of `Proj` is definitionally `ProjectiveSpectrum`.
  change IsGenericPoint (genericPointPS R)
    (Set.univ : Set (ProjectiveSpectrum (delPezzoGraded R)))
  exact isGenericPoint_genericPointPS R

end GenericPoint

/-! ## Integrality of the total space -/

section Integrality

variable [IsDomain R] [IsCancelAdd R]

/-- `ℙ(1,1,2,3)_R` is reduced: covered by four integral (hence reduced) affine charts. -/
public instance instIsReduced : IsReduced (WeightedProjectiveSpace R) := by
  -- The index type of the cover is `Fin 4`, but only up to unfolding `standardAffineOpenCover`,
  -- so the chart instances are supplied explicitly rather than by synthesis.
  have hchart : ∀ i : Fin 4, IsReduced ((standardAffineOpenCover R).openCover.X i) := by
    intro i
    -- openCover.X i = Spec (A_(Xᵢ))₀, and the chart ring is a domain.
    dsimp [Scheme.AffineOpenCover.openCover, Scheme.AffineCover.cover,
      standardAffineOpenCover, Proj.affineOpenCoverOfIrrelevantLESpan]
    haveI : IsDomain (HomogeneousLocalization.Away (delPezzoGraded R) (X i)) :=
      standardChartRing_isDomain R i
    infer_instance
  exact @IsReduced.of_openCover (WeightedProjectiveSpace R)
    (standardAffineOpenCover R).openCover hchart

/-- `ℙ(1,1,2,3)_R` is irreducible: it has a generic point (the zero ideal). -/
public instance instIrreducibleSpace : IrreducibleSpace (WeightedProjectiveSpace R) := by
  change IrreducibleSpace (ProjectiveSpectrum (delPezzoGraded R))
  exact (irreducibleSpace_def _).mpr (isGenericPoint_genericPointPS R).isIrreducible

/-- **Headline.** Weighted projective space `ℙ(1,1,2,3)_R` is an integral scheme whenever `R` is
an integral domain. -/
public instance instIsIntegral : IsIntegral (WeightedProjectiveSpace R) :=
  isIntegral_of_irreducibleSpace_of_isReduced (WeightedProjectiveSpace R)

end Integrality

/-! ## Weighted hypersurface as reduced closed subscheme

Mathlib has no `GradedRing` / `GradedAlgebra` instance on a quotient by a homogeneous ideal
(searched under `RingTheory/GradedAlgebra/` and neighbours). Consequently `Proj (A / ⟨f⟩)` is
not available. We deliver the reduced induced closed subscheme on the set-theoretic zero locus
`V₊(f)` instead.
-/

section Hypersurface

/-- The closed set `V₊(f) ⊆ ℙ(1,1,2,3)_R`. -/
public def hypersurfaceCloseds (f : MvPolynomial (Fin 4) R) :
    Closeds (WeightedProjectiveSpace R) :=
  ⟨hypersurfaceZeroLocus (R := R) f, isClosed_hypersurfaceZeroLocus (R := R) f⟩

/-- Ideal sheaf of the reduced induced structure on `V₊(f)`. -/
public def hypersurfaceIdealSheaf (f : MvPolynomial (Fin 4) R) :
    (WeightedProjectiveSpace R).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (hypersurfaceCloseds (R := R) f)

/-- The weighted hypersurface `V₊(f)` as a scheme (reduced induced structure on the zero locus).
Not `Proj (A/⟨f⟩)`, which needs a graded-quotient instance Mathlib does not supply. -/
public abbrev weightedHypersurface (f : MvPolynomial (Fin 4) R) : Scheme :=
  (hypersurfaceIdealSheaf (R := R) f).subscheme

/-- Closed immersion of the weighted hypersurface into ambient weighted projective space. -/
public def weightedHypersurfaceι (f : MvPolynomial (Fin 4) R) :
    weightedHypersurface (R := R) f ⟶ WeightedProjectiveSpace R :=
  (hypersurfaceIdealSheaf (R := R) f).subschemeι

public instance (f : MvPolynomial (Fin 4) R) :
    IsClosedImmersion (weightedHypersurfaceι (R := R) f) :=
  inferInstanceAs (IsClosedImmersion (hypersurfaceIdealSheaf (R := R) f).subschemeι)

/-- The underlying point set of the hypersurface scheme is exactly `V₊(f)`. -/
public theorem range_weightedHypersurfaceι (f : MvPolynomial (Fin 4) R) :
    Set.range (weightedHypersurfaceι (R := R) f) =
      hypersurfaceZeroLocus (R := R) f := by
  change Set.range (hypersurfaceIdealSheaf (R := R) f).subschemeι =
    (hypersurfaceCloseds (R := R) f : Set _)
  exact Scheme.IdealSheafData.range_subschemeι _

end Hypersurface

end WeightedProjectiveSpace

/-! ## Specialisation to the rational ambient space -/

/-- The del Pezzo ambient space `ℙ_ℚ(1,1,2,3)` is an integral scheme. -/
public instance delPezzoAmbient_isIntegral : IsIntegral DelPezzoAmbient :=
  WeightedProjectiveSpace.instIsIntegral ℚ

end ExplicitUnirational

/-! ## Axiom audit (headline theorems) -/

#print axioms ExplicitUnirational.HomogeneousLocalizationDomain.Away.isDomain
#print axioms ExplicitUnirational.WeightedProjectiveSpace.standardChartRing_isDomain
#print axioms ExplicitUnirational.WeightedProjectiveSpace.not_irrelevant_le_bot
#print axioms ExplicitUnirational.WeightedProjectiveSpace.isGenericPoint_genericPoint
#print axioms ExplicitUnirational.WeightedProjectiveSpace.instIsIntegral
#print axioms ExplicitUnirational.delPezzoAmbient_isIntegral
#print axioms ExplicitUnirational.WeightedProjectiveSpace.range_weightedHypersurfaceι
