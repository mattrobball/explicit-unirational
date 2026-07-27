/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.DelPezzo.Surface
public import ExplicitUnirational.Cert.Discriminant
public import ExplicitUnirational.Cert.OcticQ
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.Tactic.Ring

/-!
# Chartwise Jacobian criterion for weighted hypersurfaces

Note Proposition 3.3 (smoothness half) and the deferred clause of
`DelPezzo/Surface.lean`.

## Vendored material (sorry-free at time of vendoring)

The affine Jacobian criterion already exists, fully proved, in the sibling repository
`BConicBundleMultisections` on this toolchain.  The following were copied (namespace renames
only) from that source:

* `IdealDescent` ← `GeometricPointDescent.lean`
* Nullstellensatz half of `Hypersurface` ← `BiprojectiveSmoothCriterion.lean`
  (`sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero` and geometric variants)

The conversion “partials generate `(1)` ⇒ smooth algebra” is the conclusion of
`Hypersurface.smooth_of_pderiv_span_eq_top` / `formallySmooth_of_pderiv_span_eq_top` in
`BiprojectiveSmoothCriterion.lean` (conormal argument from `BiprojectiveAffineJacobian.lean`).
Here the same conclusion is reached via Mathlib standard-smooth localisations of a naive
hypersurface presentation (`AffineHypersurfaceJacobian.smooth_of_jacobianIdeal_eq_top`).

## Contents

* Affine single-equation Jacobian criterion (standard-smooth + Nullstellensatz forms).
* Weighted packaging: charts cover, Zariski locality, chart dehomogenisation, Euler.
* Algebraic input for `surfaceEquation` / Proposition 3.3.
* Status of `Smooth (S_Q ⟶ Spec ℚ)`: affine criterion and algebraic input land; scheme glue
  identifying reduced induced chart opens with dehomogenised `Spec` quotients does not.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace ExplicitUnirational

open AlgebraicGeometry MvPolynomial
open ExplicitUnirational.WeightedProjectiveSpace
open ExplicitUnirational.DelPezzo
open ExplicitUnirational.Cert

/-! ## Affine hypersurface Jacobian criterion -/

namespace AffineHypersurfaceJacobian

open Algebra

variable {R : Type u} [CommRing R] {σ : Type u}

/-- Relation family for a single equation (matches `naive`'s `Set.range`). -/
public noncomputable def singleRel (f : MvPolynomial σ R) : Unit → MvPolynomial σ R :=
  fun _ ↦ f

/-- The hypersurface algebra `R[X_σ] / (f)`. -/
public abbrev Quot (f : MvPolynomial σ R) : Type u :=
  MvPolynomial σ R ⧸ Ideal.span (Set.range (singleRel f))

/-- Image of a polynomial in the hypersurface quotient. -/
public noncomputable abbrev mkQ (f : MvPolynomial σ R) :
    MvPolynomial σ R →+* Quot f :=
  Ideal.Quotient.mk (Ideal.span (Set.range (singleRel f)))

/-- Naive pre-submersive presentation of `R[X_σ]/(f)` selecting variable `j`. -/
public noncomputable def prePresentation (f : MvPolynomial σ R) (j : σ) :
    PreSubmersivePresentation R (Quot f) σ Unit :=
  PreSubmersivePresentation.naive
    (v := singleRel f) (a := fun _ : Unit ↦ j)
    (ha := Function.injective_of_subsingleton _)

/-- The Jacobian of the naive presentation is the image of `∂f/∂Xⱼ`. -/
public theorem prePresentation_jacobian [Fintype σ] [DecidableEq σ]
    (f : MvPolynomial σ R) (j : σ) :
    (prePresentation f j).jacobian = mkQ f (pderiv j f) := by
  haveI : Fintype Unit := inferInstance
  haveI : DecidableEq Unit := inferInstance
  haveI : Unique Unit := inferInstance
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have hentry : (prePresentation f j).jacobiMatrix default default = pderiv j f := by
    rw [prePresentation, PreSubmersivePresentation.jacobiMatrix_naive]
    rfl
  rw [Matrix.det_unique, hentry]
  rfl

/-- Relative dimension of the naive presentation: `#σ - 1`. -/
public theorem prePresentation_dimension (f : MvPolynomial σ R) (j : σ) :
    (prePresentation f j).dimension = Nat.card σ - 1 := by
  simp [Presentation.dimension]

/-- Localising the hypersurface at the image of `∂f/∂Xⱼ` is standard smooth of
relative dimension `#σ - 1`. -/
public theorem isStandardSmoothOfRelativeDimension_localization_pderiv
    [Finite σ] [DecidableEq σ]
    (f : MvPolynomial σ R) (j : σ) :
    IsStandardSmoothOfRelativeDimension (Nat.card σ - 1) R
      (Localization.Away (mkQ f (pderiv j f))) := by
  classical
  cases nonempty_fintype σ
  set g : Quot f := mkQ f (pderiv j f)
  let P : PreSubmersivePresentation R (Quot f) σ Unit := prePresentation f j
  let Q : SubmersivePresentation (Quot f) (Localization.Away g) Unit Unit :=
    SubmersivePresentation.localizationAway (S := Localization.Away g) g
  let Cpre :
      PreSubmersivePresentation R (Localization.Away g) (Unit ⊕ σ) (Unit ⊕ Unit) :=
    Q.toPreSubmersivePresentation.comp P
  have hjac : IsUnit Cpre.jacobian := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def,
      IsUnit.mul_iff]
    refine ⟨?_, Q.jacobian_isUnit⟩
    have hP : P.jacobian = g := prePresentation_jacobian f j
    rw [hP]
    exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g
  let C : SubmersivePresentation R (Localization.Away g) (Unit ⊕ σ) (Unit ⊕ Unit) :=
    ⟨Cpre, hjac⟩
  have hdim : C.dimension = Nat.card σ - 1 := by
    have hcomp :=
      PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension
        Q.toPreSubmersivePresentation P
    have hQ : Q.toPreSubmersivePresentation.dimension = 0 :=
      Presentation.localizationAway_dimension_zero (S := Localization.Away g) g
    have hP : P.dimension = Nat.card σ - 1 := prePresentation_dimension f j
    calc
      C.dimension = Q.toPreSubmersivePresentation.dimension + P.dimension := hcomp
      _ = 0 + (Nat.card σ - 1) := by rw [hQ, hP]
      _ = Nat.card σ - 1 := by simp
  exact C.isStandardSmoothOfRelativeDimension hdim

/-- If some partial is already a unit in the quotient, the hypersurface algebra
itself is standard smooth of relative dimension `#σ - 1`. -/
public theorem isStandardSmoothOfRelativeDimension_of_isUnit_pderiv
    [Finite σ] [DecidableEq σ]
    (f : MvPolynomial σ R) (j : σ)
    (h : IsUnit (mkQ f (pderiv j f))) :
    IsStandardSmoothOfRelativeDimension (Nat.card σ - 1) R (Quot f) := by
  classical
  cases nonempty_fintype σ
  let P : PreSubmersivePresentation R (Quot f) σ Unit := prePresentation f j
  have hjac : IsUnit P.jacobian := by
    rwa [prePresentation_jacobian]
  let S : SubmersivePresentation R (Quot f) σ Unit := ⟨P, hjac⟩
  exact S.isStandardSmoothOfRelativeDimension (prePresentation_dimension f j)

/-- The Jacobian ideal of `f` in the hypersurface quotient. -/
public noncomputable def jacobianIdeal (f : MvPolynomial σ R) : Ideal (Quot f) :=
  Ideal.span (Set.range fun i : σ ↦ mkQ f (pderiv i f))

/-- **Affine hypersurface Jacobian criterion.**

If the images of `∂f/∂Xᵢ` generate the unit ideal in `R[X_σ]/(f)`, then that
quotient is smooth over `R`. -/
public theorem smooth_of_jacobianIdeal_eq_top
    [Finite σ] [DecidableEq σ]
    (f : MvPolynomial σ R) (h : jacobianIdeal f = ⊤) :
    Algebra.Smooth R (Quot f) := by
  classical
  cases nonempty_fintype σ
  rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
  refine ⟨Set.range fun i : σ ↦ mkQ f (pderiv i f), ?span, ?std⟩
  case span =>
    simpa [jacobianIdeal] using h
  case std =>
    intro t ht
    obtain ⟨j, rfl⟩ := ht
    set g := mkQ f (pderiv j f)
    have hstd : Algebra.IsStandardSmooth R (Localization.Away g) :=
      (isStandardSmoothOfRelativeDimension_localization_pderiv f j).isStandardSmooth
    -- Locally asks for IsStandardSmooth of the composed ring map
    -- `algebraMap R (Localization.Away g)` is definitionally that composition
    -- (OreLocalization algebra: numeratorRingHom.comp (algebraMap R (Quot f))).
    have heq :
        (algebraMap (Quot f) (Localization.Away g)).comp (algebraMap R (Quot f)) =
          algebraMap R (Localization.Away g) :=
      rfl
    rwa [heq, RingHom.isStandardSmooth_algebraMap]

/-- `Ideal.span (Set.range (singleRel f))` is the principal ideal `(f)`. -/
public theorem span_singleRel (f : MvPolynomial σ R) :
    Ideal.span (Set.range (singleRel f)) = Ideal.span {f} := by
  change Ideal.span (Set.range (fun _ : Unit => f)) = Ideal.span {f}
  rw [Set.range_const]

/-- If `f` and its partials generate the unit ideal, so do the classes of the partials in
`R[X]/(f)` (packaged as `jacobianIdeal`). -/
public theorem jacobianIdeal_eq_top_of_sup_span_eq_top
    (f : MvPolynomial σ R)
    (hJ : Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i f) ⊔ Ideal.span {f} = ⊤) :
    jacobianIdeal f = ⊤ := by
  classical
  have heq := span_singleRel f
  rw [← heq] at hJ
  have h1 : (1 : MvPolynomial σ R) ∈
      Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i f) ⊔
        Ideal.span (Set.range (singleRel f)) :=
    (Ideal.eq_top_iff_one _).mp hJ
  have hmap := Ideal.mem_map_of_mem (mkQ f) h1
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span] at hmap
  have hzero : Ideal.span (mkQ f '' Set.range (singleRel f)) = ⊥ := by
    have hr : Set.range (singleRel f) = ({f} : Set (MvPolynomial σ R)) := by
      change Set.range (fun _ : Unit => f) = {f}
      rw [Set.range_const]
    simp only [hr, Set.image_singleton]
    have : mkQ f f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by
        change f ∈ Ideal.span (Set.range (singleRel f))
        rw [heq]; exact Ideal.mem_span_singleton_self f)
    rw [this, Ideal.span_singleton_eq_bot.mpr rfl]
  have himg : mkQ f '' (Set.range fun i : σ => MvPolynomial.pderiv i f) =
      Set.range fun i : σ => mkQ f (MvPolynomial.pderiv i f) :=
    (Set.range_comp _ _).symm
  rw [hzero, sup_bot_eq, himg] at hmap
  exact (Ideal.eq_top_iff_one _).mpr hmap

/-- Same criterion, packaged with `Ideal.span {f}` as in the sibling. -/
public theorem smooth_of_pderiv_span_eq_top
    [Finite σ] [DecidableEq σ]
    (f : MvPolynomial σ R)
    (hspan : Ideal.span (Set.range fun i : σ =>
      Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.pderiv i f)) = ⊤) :
    Algebra.Smooth R (MvPolynomial σ R ⧸ Ideal.span {f}) := by
  classical
  have heq := span_singleRel f
  -- Transport the unit-ideal hypothesis into `jacobianIdeal`.
  have hjac : jacobianIdeal f = ⊤ := by
    refine (Ideal.eq_top_iff_one _).mpr ?_
    have h1 : (1 : MvPolynomial σ R ⧸ Ideal.span {f}) ∈
        Ideal.span (Set.range fun i : σ =>
          Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) :=
      (Ideal.eq_top_iff_one _).mp hspan
    let e : (MvPolynomial σ R ⧸ Ideal.span {f}) ≃ₐ[R] Quot f :=
      Ideal.quotientEquivAlgOfEq R heq.symm
    have h1' : (1 : Quot f) ∈ Ideal.map e.toRingHom
        (Ideal.span (Set.range fun i : σ =>
          Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) := by
      simpa [map_one] using Ideal.mem_map_of_mem e.toRingHom h1
    have hmap :
        Ideal.map e.toRingHom
            (Ideal.span (Set.range fun i : σ =>
              Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) =
          Ideal.span (Set.range fun i : σ => mkQ f (pderiv i f)) := by
      rw [Ideal.map_span]
      congr 1
      ext z
      simp only [Set.mem_image, Set.mem_range, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        refine ⟨i, ?_⟩
        exact (Ideal.quotientEquivAlgOfEq_mk R heq.symm (pderiv i f)).symm ▸ rfl
      · rintro ⟨i, rfl⟩
        refine ⟨_, ⟨i, rfl⟩, ?_⟩
        exact Ideal.quotientEquivAlgOfEq_mk R heq.symm (pderiv i f)
    rwa [hmap] at h1'
  haveI : Algebra.Smooth R (Quot f) := smooth_of_jacobianIdeal_eq_top f hjac
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlgOfEq R heq)

/-- Direct Nullstellensatz form on the `Quot` packaging. -/
public theorem smooth_of_sup_span_eq_top
    [Finite σ] [DecidableEq σ]
    (f : MvPolynomial σ R)
    (hJ : Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i f) ⊔ Ideal.span {f} = ⊤) :
    Algebra.Smooth R (Quot f) :=
  smooth_of_jacobianIdeal_eq_top f (jacobianIdeal_eq_top_of_sup_span_eq_top f hJ)

end AffineHypersurfaceJacobian

/-! ## Vendored: ideal descent along coefficient field extension

Source: `BConicBundleMultisections/GeometricPointDescent.lean` (IdealDescent).
Verified sorry-free at time of vendoring. -/

namespace IdealDescent

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {σ : Type u}

/-- Apply a `k`-linear functional to every coefficient.

Vendored from `BConicBundleMultisections.GeometricPointDescent.coeffProj`. -/
public noncomputable def coeffProj (π : K →ₗ[k] k) (p : MvPolynomial σ K) : MvPolynomial σ k :=
  ∑ d ∈ p.support, MvPolynomial.monomial d (π (p.coeff d))

@[simp] public theorem coeff_coeffProj (π : K →ₗ[k] k) (p : MvPolynomial σ K) (e : σ →₀ ℕ) :
    (coeffProj π p).coeff e = π (p.coeff e) := by
  classical
  rw [coeffProj, MvPolynomial.coeff_sum]
  by_cases h : e ∈ p.support
  · refine (Finset.sum_eq_single e ?_ ?_).trans ?_
    · intro d _ hd
      rw [MvPolynomial.coeff_monomial, if_neg hd]
    · intro hne
      exact absurd h hne
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · refine (Finset.sum_eq_zero ?_).trans ?_
    · intro d hd
      rw [MvPolynomial.coeff_monomial, if_neg]
      rintro rfl
      exact h hd
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

public theorem coeffProj_zero (π : K →ₗ[k] k) : coeffProj π (0 : MvPolynomial σ K) = 0 := by
  ext e; simp

public theorem coeffProj_add (π : K →ₗ[k] k) (p q : MvPolynomial σ K) :
    coeffProj π (p + q) = coeffProj π p + coeffProj π q := by
  ext e; simp

public theorem coeffProj_one (π : K →ₗ[k] k) (hπ : π (1 : K) = 1) :
    coeffProj π (1 : MvPolynomial σ K) = 1 := by
  classical
  ext e
  rw [coeff_coeffProj, MvPolynomial.coeff_one, MvPolynomial.coeff_one]
  split_ifs with h
  · exact hπ
  · exact map_zero π

public theorem coeffProj_map_mul (π : K →ₗ[k] k) (a : MvPolynomial σ k) (q : MvPolynomial σ K) :
    coeffProj π (MvPolynomial.map (algebraMap k K) a * q) = a * coeffProj π q := by
  classical
  ext e
  rw [coeff_coeffProj, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MvPolynomial.coeff_map, coeff_coeffProj, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- Ideal membership descends along a coefficient field extension.

Vendored from `BConicBundleMultisections.GeometricPointDescent.comap_map_mvPolynomial_eq_self`. -/
public theorem comap_map_mvPolynomial_eq_self (I : Ideal (MvPolynomial σ k)) :
    (I.map (MvPolynomial.map (algebraMap k K))).comap (MvPolynomial.map (algebraMap k K)) = I := by
  classical
  refine le_antisymm ?_ Ideal.le_comap_map
  obtain ⟨π, hπ⟩ := (Algebra.linearMap k K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k K).injective)
  have hπ1 : π (1 : K) = 1 := by
    have h := congrArg (fun f : k →ₗ[k] k => f 1) hπ
    simpa using h
  set J : Ideal (MvPolynomial σ K) :=
    { carrier := {p | ∀ a : MvPolynomial σ K, coeffProj π (a * p) ∈ I}
      add_mem' := by
        intro p q hp hq a
        rw [mul_add, coeffProj_add]
        exact I.add_mem (hp a) (hq a)
      zero_mem' := by
        intro a
        rw [mul_zero, coeffProj_zero]
        exact I.zero_mem
      smul_mem' := by
        intro c p hp a
        rw [smul_eq_mul, ← mul_assoc]
        exact hp _ }
  have hle : I.map (MvPolynomial.map (algebraMap k K)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg a
    rw [mul_comm, coeffProj_map_mul]
    exact I.mul_mem_right _ hg
  intro y hy
  have hyJ : MvPolynomial.map (algebraMap k K) y ∈ J := hle hy
  have h1 := hyJ 1
  rw [one_mul] at h1
  rwa [show MvPolynomial.map (algebraMap k K) y
        = MvPolynomial.map (algebraMap k K) y * 1 from (mul_one _).symm,
    coeffProj_map_mul, coeffProj_one π hπ1, mul_one] at h1

/-- A polynomial ideal that becomes unit after coefficient extension was already unit.

Vendored from `BConicBundleMultisections.GeometricPointDescent.ideal_eq_top_of_map_eq_top`. -/
public theorem ideal_eq_top_of_map_eq_top {I : Ideal (MvPolynomial σ k)}
    (h : I.map (MvPolynomial.map (algebraMap k K)) = ⊤) : I = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  have h1 : (1 : MvPolynomial σ K) ∈ I.map (MvPolynomial.map (algebraMap k K)) := by
    rw [h]; trivial
  have := (comap_map_mvPolynomial_eq_self (K := K) I).le (show (1 : MvPolynomial σ k) ∈ _ by
    simpa using h1)
  exact this

end IdealDescent

/-! ## Vendored: Nullstellensatz form of the hypersurface criterion

Source: `BConicBundleMultisections/BiprojectiveSmoothCriterion.lean` (Hypersurface).
Verified sorry-free at time of vendoring. -/

namespace Hypersurface

variable {K : Type u} [Field K] {σ : Type u}

/-- Vendored from `BConicBundleMultisections.Hypersurface.ne_zero_of_exists_pderiv_ne_zero`. -/
public theorem ne_zero_of_exists_pderiv_ne_zero
    (f : MvPolynomial σ K)
    (h : ∀ a : σ → K, MvPolynomial.aeval a f = 0 →
      ∃ i : σ, MvPolynomial.aeval a (MvPolynomial.pderiv i f) ≠ 0) :
    f ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := h 0 (by simp)
  exact hi (by simp)

/-- Vendored from
`BConicBundleMultisections.Hypersurface.pderiv_span_eq_top_of_sup_span_eq_top`. -/
public theorem pderiv_span_eq_top_of_sup_span_eq_top (f : MvPolynomial σ K)
    (hJ : Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i f) ⊔ Ideal.span {f} = ⊤) :
    Ideal.span (Set.range fun i : σ =>
      Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.pderiv i f)) = ⊤ := by
  classical
  have h1 : (1 : MvPolynomial σ K) ∈
      Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i f) ⊔ Ideal.span {f} :=
    (Ideal.eq_top_iff_one _).mp hJ
  have hmap := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {f})) h1
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span] at hmap
  have hzero : Ideal.span
      ((Ideal.Quotient.mk (Ideal.span {f})) '' ({f} : Set (MvPolynomial σ K))) = ⊥ := by
    rw [Set.image_singleton]
    have : Ideal.Quotient.mk (Ideal.span {f}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    rw [this, Ideal.span_singleton_eq_bot.mpr rfl]
  have himg :
      (Ideal.Quotient.mk (Ideal.span {f})) ''
          (Set.range fun i : σ => MvPolynomial.pderiv i f) =
        Set.range fun i : σ =>
          Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.pderiv i f) :=
    (Set.range_comp _ _).symm
  rw [hzero, sup_bot_eq, himg] at hmap
  exact (Ideal.eq_top_iff_one _).mpr hmap

/-- Vendored from
`BConicBundleMultisections.Hypersurface.sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero`. -/
public theorem sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero
    [Finite σ] [IsAlgClosed K] (f : MvPolynomial σ K)
    (h : ∀ a : σ → K, MvPolynomial.aeval a f = 0 →
      ∃ i : σ, MvPolynomial.aeval a (MvPolynomial.pderiv i f) ≠ 0) :
    Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i f) ⊔ Ideal.span {f} = ⊤ := by
  classical
  set J : Ideal (MvPolynomial σ K) :=
    Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i f) ⊔ Ideal.span {f}
  have hfJ : f ∈ J := (le_sup_right : Ideal.span {f} ≤ J) (Ideal.subset_span rfl)
  have hdJ : ∀ i : σ, MvPolynomial.pderiv i f ∈ J := fun i =>
    (le_sup_left : Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i f) ≤ J)
      (Ideal.subset_span ⟨i, rfl⟩)
  have hzl : MvPolynomial.zeroLocus K J = ∅ := by
    ext a
    simp only [Set.mem_empty_iff_false, iff_false, MvPolynomial.mem_zeroLocus_iff]
    intro ha
    obtain ⟨i, hi⟩ := h a (ha f hfJ)
    exact hi (ha _ (hdJ i))
  have hrad := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) J
  rw [hzl, MvPolynomial.vanishingIdeal_empty] at hrad
  exact Ideal.radical_eq_top.mp hrad.symm

/-- Vendored from
`BConicBundleMultisections.Hypersurface.pderiv_span_eq_top_of_exists_pderiv_ne_zero`. -/
public theorem pderiv_span_eq_top_of_exists_pderiv_ne_zero
    [Finite σ] [IsAlgClosed K] (f : MvPolynomial σ K)
    (h : ∀ a : σ → K, MvPolynomial.aeval a f = 0 →
      ∃ i : σ, MvPolynomial.aeval a (MvPolynomial.pderiv i f) ≠ 0) :
    Ideal.span (Set.range fun i : σ =>
      Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.pderiv i f)) = ⊤ :=
  pderiv_span_eq_top_of_sup_span_eq_top f
    (sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero f h)

/-- Vendored from
`BConicBundleMultisections.Hypersurface.ne_zero_of_exists_pderiv_ne_zero_of_geometric`. -/
public theorem ne_zero_of_exists_pderiv_ne_zero_of_geometric
    {L : Type u} [Field L] [Algebra K L] (f : MvPolynomial σ K)
    (h : ∀ a : σ → L, MvPolynomial.aeval a (MvPolynomial.map (algebraMap K L) f) = 0 →
      ∃ i : σ, MvPolynomial.aeval a
        (MvPolynomial.map (algebraMap K L) (MvPolynomial.pderiv i f)) ≠ 0) :
    f ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := h 0 (by simp)
  exact hi (by simp)

/-- Vendored from
`BConicBundleMultisections.Hypersurface.sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero_of_geometric`.
-/
public theorem sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero_of_geometric
    [Finite σ] {L : Type u} [Field L] [IsAlgClosed L] [Algebra K L] (f : MvPolynomial σ K)
    (h : ∀ a : σ → L, MvPolynomial.aeval a (MvPolynomial.map (algebraMap K L) f) = 0 →
      ∃ i : σ, MvPolynomial.aeval a
        (MvPolynomial.map (algebraMap K L) (MvPolynomial.pderiv i f)) ≠ 0) :
    Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i f) ⊔ Ideal.span {f} = ⊤ := by
  classical
  refine IdealDescent.ideal_eq_top_of_map_eq_top (K := L) ?_
  have hup := sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero
    (K := L) (MvPolynomial.map (algebraMap K L) f) (by
      intro a ha
      obtain ⟨i, hi⟩ := h a ha
      exact ⟨i, by rwa [MvPolynomial.pderiv_map]⟩)
  have hfun : (MvPolynomial.map (algebraMap K L)) ∘ (fun i : σ => MvPolynomial.pderiv i f)
      = fun i : σ => MvPolynomial.pderiv i (MvPolynomial.map (algebraMap K L) f) :=
    funext fun _ => MvPolynomial.pderiv_map.symm
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    ← Set.range_comp, hfun]
  exact hup

/-- Sibling: `Hypersurface.smooth_of_exists_pderiv_ne_zero`, on the `Quot` packaging. -/
public theorem smooth_of_exists_pderiv_ne_zero
    [Finite σ] [DecidableEq σ] [IsAlgClosed K] (f : MvPolynomial σ K)
    (h : ∀ a : σ → K, MvPolynomial.aeval a f = 0 →
      ∃ i : σ, MvPolynomial.aeval a (MvPolynomial.pderiv i f) ≠ 0) :
    Algebra.Smooth K (AffineHypersurfaceJacobian.Quot f) :=
  AffineHypersurfaceJacobian.smooth_of_sup_span_eq_top f
    (sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero f h)

/-- Sibling: `Hypersurface.smooth_of_exists_pderiv_ne_zero`, as a `RingHom.Smooth`. -/
public theorem smooth_ringHom_of_exists_pderiv_ne_zero
    [Finite σ] [DecidableEq σ] [IsAlgClosed K] (f : MvPolynomial σ K)
    (h : ∀ a : σ → K, MvPolynomial.aeval a f = 0 →
      ∃ i : σ, MvPolynomial.aeval a (MvPolynomial.pderiv i f) ≠ 0) :
    RingHom.Smooth
      (algebraMap K (AffineHypersurfaceJacobian.Quot f)) := by
  rw [RingHom.smooth_algebraMap]
  exact smooth_of_exists_pderiv_ne_zero f h

/-- Sibling: `Hypersurface.smooth_of_exists_pderiv_ne_zero_of_geometric`. -/
public theorem smooth_of_exists_pderiv_ne_zero_of_geometric
    [Finite σ] [DecidableEq σ] {L : Type u} [Field L] [IsAlgClosed L] [Algebra K L]
    (f : MvPolynomial σ K)
    (h : ∀ a : σ → L, MvPolynomial.aeval a (MvPolynomial.map (algebraMap K L) f) = 0 →
      ∃ i : σ, MvPolynomial.aeval a
        (MvPolynomial.map (algebraMap K L) (MvPolynomial.pderiv i f)) ≠ 0) :
    Algebra.Smooth K (AffineHypersurfaceJacobian.Quot f) :=
  AffineHypersurfaceJacobian.smooth_of_sup_span_eq_top f
    (sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero_of_geometric f h)

/-- Ring-hom form of the geometric criterion. -/
public theorem smooth_ringHom_of_exists_pderiv_ne_zero_of_geometric
    [Finite σ] [DecidableEq σ] {L : Type u} [Field L] [IsAlgClosed L] [Algebra K L]
    (f : MvPolynomial σ K)
    (h : ∀ a : σ → L, MvPolynomial.aeval a (MvPolynomial.map (algebraMap K L) f) = 0 →
      ∃ i : σ, MvPolynomial.aeval a
        (MvPolynomial.map (algebraMap K L) (MvPolynomial.pderiv i f)) ≠ 0) :
    RingHom.Smooth
      (algebraMap K (AffineHypersurfaceJacobian.Quot f)) := by
  rw [RingHom.smooth_algebraMap]
  exact smooth_of_exists_pderiv_ne_zero_of_geometric (L := L) f h

/-- Spec form of the geometric Jacobian criterion (universes of source/target match). -/
public theorem smooth_spec_of_exists_pderiv_ne_zero_of_geometric
    [Finite σ] [DecidableEq σ] {L : Type u} [Field L] [IsAlgClosed L] [Algebra K L]
    (f : MvPolynomial σ K)
    (h : ∀ a : σ → L, MvPolynomial.aeval a (MvPolynomial.map (algebraMap K L) f) = 0 →
      ∃ i : σ, MvPolynomial.aeval a
        (MvPolynomial.map (algebraMap K L) (MvPolynomial.pderiv i f)) ≠ 0) :
    Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap K (AffineHypersurfaceJacobian.Quot f)))) := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AffineHypersurfaceJacobian.Quot f) :=
    CommRingCat.ofHom (algebraMap K (AffineHypersurfaceJacobian.Quot f))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := φ)).mpr
    (smooth_ringHom_of_exists_pderiv_ne_zero_of_geometric (L := L) f h)

end Hypersurface

/-! ## Weighted packaging -/

namespace WeightedProjectiveSpace

variable (R : Type u) [CommRing R]

/-- Homogeneous partial of a form. -/
public noncomputable def partials (f : MvPolynomial (Fin 4) R) (i : Fin 4) :
    MvPolynomial (Fin 4) R :=
  pderiv i f

/-- Jacobian ideal of the affine cone: generated by `f` and its four partials. -/
public noncomputable def coneJacobianIdeal (f : MvPolynomial (Fin 4) R) :
    Ideal (MvPolynomial (Fin 4) R) :=
  Ideal.span ({f} ∪ Set.range (partials (R := R) f))

/-- The four standard charts cover the ambient space. -/
public theorem charts_cover :
    ⨆ i : Fin 4, standardBasicOpen R i = ⊤ :=
  iSup_standardBasicOpen_eq_top R

/-- Smoothness is local on the source. -/
public theorem smooth_of_openCover_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : X.OpenCover) (h : ∀ i, Smooth (𝒰.f i ≫ f)) :
    Smooth f :=
  IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 h

/-- Smoothness may be checked on an open cover by opens. -/
public theorem smooth_of_iSup_opens_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, Smooth ((U i).ι ≫ f)) :
    Smooth f :=
  IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) U hU h

/-- Structure morphism of a weighted hypersurface to `Spec R`. -/
public def weightedHypersurfaceToSpec (f : MvPolynomial (Fin 4) R) :
    weightedHypersurface (R := R) f ⟶ Spec (.of R) :=
  weightedHypersurfaceι (R := R) f ≫ toSpec R

/-- Chart substitution for `D₊(X i)`: constant `1` at the chart index, free variables on the
complement via `succAbove`. -/
public noncomputable def chartSubst (i : Fin 4) : Fin 4 → MvPolynomial (Fin 3) R :=
  Fin.insertNth (α := fun _ => MvPolynomial (Fin 3) R) i 1 fun r => X r

/-- Dehomogenised equation of a form on the chart `D₊(X i)`. -/
public noncomputable def chartEquation (i : Fin 4) (f : MvPolynomial (Fin 4) R) :
    MvPolynomial (Fin 3) R :=
  aeval (chartSubst (R := R) i) f

/-- **Chartwise Jacobian criterion (affine form), specialised to universe-`0` fields.**

`Fin 3` and `Fin 4` live in `Type`, so the affine packaging (which requires the variable index
type to share a universe with the coefficient field) is stated here for `K : Type`.  This covers
`ℚ` and every concrete base field used in the note. -/
public theorem smooth_chartEquation_of_exists_pderiv_ne_zero_of_geometric
    {K : Type} [Field K] {L : Type} [Field L] [IsAlgClosed L] [Algebra K L]
    (i : Fin 4) (f : MvPolynomial (Fin 4) K)
    (h : ∀ a : Fin 3 → L,
      MvPolynomial.aeval a (MvPolynomial.map (algebraMap K L) (chartEquation (R := K) i f)) = 0 →
      ∃ q : Fin 3,
        MvPolynomial.aeval a
          (MvPolynomial.map (algebraMap K L)
            (MvPolynomial.pderiv q (chartEquation (R := K) i f))) ≠ 0) :
    Algebra.Smooth K (AffineHypersurfaceJacobian.Quot (chartEquation (R := K) i f)) :=
  Hypersurface.smooth_of_exists_pderiv_ne_zero_of_geometric (L := L)
    (chartEquation (R := K) i f) h

/-- Spec form of the chartwise criterion (universe-`0` fields). -/
public theorem smooth_spec_chartEquation_of_exists_pderiv_ne_zero_of_geometric
    {K : Type} [Field K] {L : Type} [Field L] [IsAlgClosed L] [Algebra K L]
    (i : Fin 4) (f : MvPolynomial (Fin 4) K)
    (h : ∀ a : Fin 3 → L,
      MvPolynomial.aeval a (MvPolynomial.map (algebraMap K L) (chartEquation (R := K) i f)) = 0 →
      ∃ q : Fin 3,
        MvPolynomial.aeval a
          (MvPolynomial.map (algebraMap K L)
            (MvPolynomial.pderiv q (chartEquation (R := K) i f))) ≠ 0) :
    Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap K (AffineHypersurfaceJacobian.Quot (chartEquation (R := K) i f))))) :=
  Hypersurface.smooth_spec_of_exists_pderiv_ne_zero_of_geometric (L := L)
    (chartEquation (R := K) i f) h

/-- Weighted Euler identity for a form of degree `d` in weights `(1,1,2,3)`. -/
public theorem weighted_euler (f : MvPolynomial (Fin 4) R) {d : ℕ}
    (hf : IsWeightedHomogeneous weights f d) :
    ∑ i : Fin 4, weights i • (X i * pderiv i f) = d • f :=
  hf.sum_weight_X_mul_pderiv

end WeightedProjectiveSpace

/-! ## Algebraic content of Proposition 3.3 for `surfaceEquation` -/

namespace DelPezzo

/-! Local `pderiv` simp lemmas for numerals (cf. `Cert/Invariants.lean`).
A generic `[n.AtLeastTwo]` lemma does not fire under `simp`. -/

private lemma pderiv_ofNat (i : Fin 4) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (OfNat.ofNat n : MvPolynomial (Fin 4) ℚ) = 0 := by
  rw [← map_ofNat (C : ℚ →+* MvPolynomial (Fin 4) ℚ) n, pderiv_C]

@[simp] private lemma pderiv_three (i : Fin 4) :
    pderiv i (3 : MvPolynomial (Fin 4) ℚ) = 0 := pderiv_ofNat i 3
@[simp] private lemma pderiv_four (i : Fin 4) :
    pderiv i (4 : MvPolynomial (Fin 4) ℚ) = 0 := pderiv_ofNat i 4
@[simp] private lemma pderiv_eighteen (i : Fin 4) :
    pderiv i (18 : MvPolynomial (Fin 4) ℚ) = 0 := pderiv_ofNat i 18
@[simp] private lemma pderiv_twentyThree (i : Fin 4) :
    pderiv i (23 : MvPolynomial (Fin 4) ℚ) = 0 := pderiv_ofNat i 23

/-- `∂/∂y` of the short Weierstrass equation is `2y`. -/
public theorem pderiv_surfaceEquation_y :
    (pderiv (3 : Fin 4) surfaceEquation : MvPolynomial (Fin 4) ℚ) = 2 * X 3 := by
  classical
  unfold surfaceEquation A_poly B_poly P4_uv
  simp only [map_sub, map_add, pderiv_mul, pderiv_pow, pderiv_C, pderiv_X,
    pderiv_three, pderiv_four, pderiv_eighteen, pderiv_twentyThree,
    Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 3),
    Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 3),
    Pi.single_eq_of_ne (by decide : (2 : Fin 4) ≠ 3)]
  ring

/-- `∂/∂x` of the short Weierstrass equation is `-3x² - A`. -/
public theorem pderiv_surfaceEquation_x :
    (pderiv (2 : Fin 4) surfaceEquation : MvPolynomial (Fin 4) ℚ) =
      -3 * (X 2) ^ 2 - A_poly := by
  classical
  -- Keep A_poly folded on the RHS; expand the defining equation only.
  unfold surfaceEquation
  have hA : pderiv (2 : Fin 4) A_poly = 0 := by
    unfold A_poly
    simp only [map_sub, pderiv_mul, pderiv_pow, pderiv_X, pderiv_three,
      Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2),
      Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    ring
  have hB : pderiv (2 : Fin 4) B_poly = 0 := by
    unfold B_poly P4_uv
    simp only [map_sub, map_add, pderiv_mul, pderiv_pow, pderiv_C, pderiv_X,
      pderiv_four, pderiv_eighteen, pderiv_twentyThree,
      Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2),
      Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    ring
  have hy : pderiv (2 : Fin 4) ((X 3 : MvPolynomial (Fin 4) ℚ) ^ 2) = 0 := by
    simp only [pderiv_pow, pderiv_X, Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 2)]
    ring
  have hx : pderiv (2 : Fin 4) ((X 2 : MvPolynomial (Fin 4) ℚ) ^ 3) =
      3 * (X 2) ^ 2 := by
    simp only [pderiv_pow, pderiv_X, Pi.single_eq_same]
    ring
  have hAx : pderiv (2 : Fin 4) (A_poly * X 2) = A_poly := by
    rw [pderiv_mul, hA, pderiv_X_self]
    ring
  simp only [map_sub, hy, hx, hAx, hB]
  ring

/-- Evaluation at `u = v = 0`, free coordinates `(x, y) = (X 0, X 1)`. -/
public noncomputable def uv0Eval : MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  aeval fun i : Fin 4 =>
    if i = 2 then (X 0 : MvPolynomial (Fin 2) ℚ)
    else if i = 3 then (X 1 : MvPolynomial (Fin 2) ℚ)
    else 0

private lemma uv0Eval_X0 : uv0Eval (X 0) = 0 := by
  simp only [uv0Eval, aeval_X]; decide
private lemma uv0Eval_X1 : uv0Eval (X 1) = 0 := by
  simp only [uv0Eval, aeval_X]; decide
private lemma uv0Eval_X2 : uv0Eval (X 2) = (X 0 : MvPolynomial (Fin 2) ℚ) := by
  simp [uv0Eval]
private lemma uv0Eval_X3 : uv0Eval (X 3) = (X 1 : MvPolynomial (Fin 2) ℚ) := by
  simp [uv0Eval]

/-- On `u = v = 0`, the equation becomes `y² - x³`. -/
public theorem aeval_uv0_surfaceEquation :
    uv0Eval surfaceEquation = (X 1) ^ 2 - (X 0) ^ 3 := by
  unfold surfaceEquation A_poly B_poly P4_uv
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat,
    uv0Eval_X0, uv0Eval_X1, uv0Eval_X2, uv0Eval_X3,
    zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0)]
  ring

/-- On `u = v = 0`, `∂/∂x` specialises to `-3x²`. -/
public theorem aeval_uv0_pderiv_x :
    uv0Eval (pderiv (2 : Fin 4) surfaceEquation) = -3 * (X 0) ^ 2 := by
  rw [pderiv_surfaceEquation_x]
  have hA : uv0Eval A_poly = 0 := by
    unfold A_poly
    simp only [map_mul, map_sub, map_ofNat, uv0Eval_X0, uv0Eval_X1, zero_mul, mul_zero]
  calc
    uv0Eval (-3 * (X 2) ^ 2 - A_poly)
        = uv0Eval (-3 * (X 2) ^ 2) - uv0Eval A_poly := by simp only [map_sub]
    _ = uv0Eval (-3 * (X 2) ^ 2) := by rw [hA, sub_zero]
    _ = uv0Eval (-3 : MvPolynomial (Fin 4) ℚ) * uv0Eval ((X 2) ^ 2) := by
        simp only [map_mul]
    _ = (-3 : MvPolynomial (Fin 2) ℚ) * (X 0) ^ 2 := by
        simp only [map_ofNat, map_neg, map_pow, uv0Eval_X2]
    _ = -3 * (X 0) ^ 2 := by ring

/-- On `u = v = 0`, `∂/∂y` specialises to `2y`. -/
public theorem aeval_uv0_pderiv_y :
    uv0Eval (pderiv (3 : Fin 4) surfaceEquation) = 2 * X 1 := by
  rw [pderiv_surfaceEquation_y]
  simp only [map_mul, map_ofNat, uv0Eval_X3]

/-- Note Prop. 3.3 (cone form on `u = v = 0`): if `y² = x³` and both partials
`-3x²` and `2y` vanish over `ℚ`, then `x = y = 0`. -/
public theorem uv0_singular_implies_origin
    (x y : ℚ) (_heq : y ^ 2 = x ^ 3)
    (hx : (-3 : ℚ) * x ^ 2 = 0) (hy : (2 : ℚ) * y = 0) :
    x = 0 ∧ y = 0 := by
  have hy0 : y = 0 := by
    have : (2 : ℚ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hy).resolve_left this
  have hx0 : x = 0 := by
    have h3 : (-3 : ℚ) ≠ 0 := by norm_num
    have hx2 : x ^ 2 = 0 := (mul_eq_zero.mp hx).resolve_left h3
    exact sq_eq_zero_iff.mp hx2
  exact ⟨hx0, hy0⟩

/-- Re-export: `q₈` is square-free (simple zeros of the discriminant). -/
public theorem squarefree_q8_for_smoothness : Squarefree (q8 : Polynomial ℚ) :=
  squarefree_q8

/-- Discriminant factorisation (3.13). -/
public theorem discriminant_factorization_for_smoothness :
    -64 * (X 0 * (X 1) ^ 2 * (3 * X 0 - X 1)) ^ 3
      - 27 * (X 0 * X 1 * P4) ^ 2
      = -(X 0) ^ 2 * (X 1) ^ 2 * Q8 :=
  discriminant_factorization

/-- Ambient singular ideals miss `S_Q`. -/
public theorem ambient_singular_miss_S_Q :
    surfaceEquation ∉ ambientSingularIdeal_x ∧
    surfaceEquation ∉ ambientSingularIdeal_y :=
  ambientSingularIdeals_avoid_surfaceEquation

/-- Structure morphism `S_Q → Spec ℚ`. -/
public def S_Q_toSpec : S_Q ⟶ Spec (.of ℚ) :=
  weightedHypersurfaceToSpec (R := ℚ) surfaceEquation

/-- Weighted Euler for `surfaceEquation` (degree 6). -/
public theorem surfaceEquation_weighted_euler :
    ∑ i : Fin 4, weights i • (X i * pderiv i surfaceEquation) =
      (6 : ℕ) • surfaceEquation :=
  (isWeightedHomogeneous_surfaceEquation).sum_weight_X_mul_pderiv

/-- Same conclusion over any characteristic-zero field. -/
public theorem uv0_singular_implies_origin_of_charZero
    {L : Type u} [Field L] [CharZero L]
    (x y : L) (_heq : y ^ 2 = x ^ 3)
    (hx : (-3 : L) * x ^ 2 = 0) (hy : (2 : L) * y = 0) :
    x = 0 ∧ y = 0 := by
  have hy0 : y = 0 := by
    have : (2 : L) ≠ 0 := two_ne_zero
    exact (mul_eq_zero.mp hy).resolve_left this
  have hx0 : x = 0 := by
    have h3 : (-3 : L) ≠ 0 := by
      intro h
      have : (3 : L) = 0 := by linear_combination -(h)
      exact (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0) : (3 : L) ≠ 0) this
    have hx2 : x ^ 2 = 0 := (mul_eq_zero.mp hx).resolve_left h3
    exact sq_eq_zero_iff.mp hx2
  exact ⟨hx0, hy0⟩

/-!
### Status of `Smooth (S_Q ⟶ Spec ℚ)`

**Affine criterion: available** (vendored Nullstellensatz form + standard-smooth localisation).

**Chartwise packaging: available**
(`smooth_chartEquation_of_exists_pderiv_ne_zero_of_geometric`, Zariski locality,
weighted Euler, four-chart cover).

**Algebraic input for Proposition 3.3: available**
(partials, `u = v = 0` specialisation, square-free `q₈`, discriminant factorisation,
ambient singular ideals miss `S_Q`).

**Scheme-theoretic glue: still open.** The reduced induced structure
`weightedHypersurface = vanishingIdeal.subscheme` is not yet identified on each standard chart
with `Spec` of the dehomogenised hypersurface quotient. That comparison needs either an explicit
isomorphism of the degree-zero homogeneous localisation with a free polynomial ring (true for
weight-1 charts, delicate for weights 2 and 3), or a graded-quotient instance yielding
`Proj(A/⟨f⟩)` (absent from Mathlib; see `WeightedProjective/Integrality`).

Until that comparison lands, `Smooth S_Q_toSpec` is not proved. We refuse a bespoke smoothness
predicate.
-/

end DelPezzo

end ExplicitUnirational

/-! ## Axiom audit -/

#print axioms ExplicitUnirational.IdealDescent.ideal_eq_top_of_map_eq_top
#print axioms ExplicitUnirational.AffineHypersurfaceJacobian.prePresentation_jacobian
#print axioms ExplicitUnirational.AffineHypersurfaceJacobian.isStandardSmoothOfRelativeDimension_localization_pderiv
#print axioms ExplicitUnirational.AffineHypersurfaceJacobian.isStandardSmoothOfRelativeDimension_of_isUnit_pderiv
#print axioms ExplicitUnirational.AffineHypersurfaceJacobian.smooth_of_jacobianIdeal_eq_top
#print axioms ExplicitUnirational.AffineHypersurfaceJacobian.smooth_of_pderiv_span_eq_top
#print axioms ExplicitUnirational.Hypersurface.sup_span_pderiv_eq_top_of_exists_pderiv_ne_zero
#print axioms ExplicitUnirational.Hypersurface.smooth_of_exists_pderiv_ne_zero
#print axioms ExplicitUnirational.Hypersurface.smooth_ringHom_of_exists_pderiv_ne_zero_of_geometric
#print axioms ExplicitUnirational.WeightedProjectiveSpace.smooth_of_openCover_smooth
#print axioms ExplicitUnirational.WeightedProjectiveSpace.smooth_chartEquation_of_exists_pderiv_ne_zero_of_geometric
#print axioms ExplicitUnirational.WeightedProjectiveSpace.weighted_euler
#print axioms ExplicitUnirational.DelPezzo.pderiv_surfaceEquation_y
#print axioms ExplicitUnirational.DelPezzo.pderiv_surfaceEquation_x
#print axioms ExplicitUnirational.DelPezzo.uv0_singular_implies_origin
#print axioms ExplicitUnirational.DelPezzo.uv0_singular_implies_origin_of_charZero
#print axioms ExplicitUnirational.DelPezzo.squarefree_q8_for_smoothness
#print axioms ExplicitUnirational.DelPezzo.surfaceEquation_weighted_euler
