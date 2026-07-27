/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.WeightedProjective.Integrality
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.Ring

/-!
# The arithmetic surface `S_ℚ` as a closed subscheme of `ℙ(1,1,2,3)`

Note Theorem 1.1 (first clause) / equations (1.1) and (3.9).

## Deliverables

1. `surfaceEquation` — LHS of (1.1), weighted-homogeneous of degree 6.
2. `S_Q` — closed subscheme via `weightedHypersurface`.
3. The coordinate ideals of the ambient singular points `[0:0:1:0]` and `[0:0:0:1]` do
   not contain `surfaceEquation` (so those points cannot lie on `S_Q`).
4. Completing the square in cleared-denominator form (note (3.12)): integer identity relating
   the short and long Weierstrass models.

## Smoothness (deferred)

Mathlib has `AlgebraicGeometry.Smooth` but **no chartwise Jacobian criterion for weighted
hypersurfaces in weighted `Proj`**, and no `Proj(A/⟨f⟩)` (missing graded-quotient instance;
see `WeightedProjective/Integrality`). Full `Smooth (S_Q ⟶ Spec ℚ)` is deferred. Packaging the
two ambient singular points as `ProjectiveSpectrum` elements (which needs a primeness proof for
the coordinate spans equal to kernels of evaluations) is also deferred; the ideal-level
non-membership below is exactly the vanishing check the note uses.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped AlgebraicGeometry

namespace ExplicitUnirational

open AlgebraicGeometry MvPolynomial
open ExplicitUnirational.WeightedProjectiveSpace

namespace DelPezzo

/-! ## Polynomials: `(u,v,x,y) = (X 0, X 1, X 2, X 3)` -/

/-- The bihomogeneous quartic `P₄(u,v)` of note (3.10), in four variables. -/
public def P4_uv : MvPolynomial (Fin 4) ℚ :=
  4 * (X 1) ^ 4 - 23 * X 0 * (X 1) ^ 3 - 18 * (X 0) ^ 2 * (X 1) ^ 2
    + (X 0) ^ 3 * X 1 - 4 * (X 0) ^ 4

/-- Weierstrass coefficient `A = u v² (3u − v)` of note (3.12). -/
public def A_poly : MvPolynomial (Fin 4) ℚ :=
  X 0 * (X 1) ^ 2 * (3 * X 0 - X 1)

/-- Weierstrass coefficient `B = (1/4) u v P₄` of note (3.12). -/
public def B_poly : MvPolynomial (Fin 4) ℚ :=
  C (1 / 4 : ℚ) * X 0 * X 1 * P4_uv

/-- Defining equation of `S_ℚ` (note (1.1)): `y² − x³ − A x − B`. -/
public def surfaceEquation : MvPolynomial (Fin 4) ℚ :=
  (X 3) ^ 2 - (X 2) ^ 3 - A_poly * X 2 - B_poly

/-- Integral long Weierstrass equation of note (3.9). -/
public def surfaceEquationLong : MvPolynomial (Fin 4) ℚ :=
  (X 3) ^ 2 + X 0 * X 1 * (X 1 - X 0) * X 3 - (X 2) ^ 3 - A_poly * X 2
    - X 0 * X 1 * ((X 1) ^ 4 - 6 * X 0 * (X 1) ^ 3 - 4 * (X 0) ^ 2 * (X 1) ^ 2 - (X 0) ^ 4)

/-! ## Weighted homogeneity of degree 6 -/

section WeightedHomogeneous

private lemma whX0 : IsWeightedHomogeneous weights (X 0 : MvPolynomial (Fin 4) ℚ) 1 := by
  have h := isWeightedHomogeneous_X_weights ℚ 0
  rwa [weights_zero] at h
private lemma whX1 : IsWeightedHomogeneous weights (X 1 : MvPolynomial (Fin 4) ℚ) 1 := by
  have h := isWeightedHomogeneous_X_weights ℚ 1
  rwa [weights_one] at h
private lemma whX2 : IsWeightedHomogeneous weights (X 2 : MvPolynomial (Fin 4) ℚ) 2 := by
  have h := isWeightedHomogeneous_X_weights ℚ 2
  rwa [weights_two] at h
private lemma whX3 : IsWeightedHomogeneous weights (X 3 : MvPolynomial (Fin 4) ℚ) 3 := by
  have h := isWeightedHomogeneous_X_weights ℚ 3
  rwa [weights_three] at h

private lemma whC {n : ℕ} {p : MvPolynomial (Fin 4) ℚ}
    (hp : IsWeightedHomogeneous weights p n) (r : ℚ) :
    IsWeightedHomogeneous weights (C r * p) n :=
  hp.C_mul r

private lemma whNat {n : ℕ} {p : MvPolynomial (Fin 4) ℚ}
    (hp : IsWeightedHomogeneous weights p n) (k : ℕ) :
    IsWeightedHomogeneous weights ((k : MvPolynomial (Fin 4) ℚ) * p) n := by
  have h : (k : MvPolynomial (Fin 4) ℚ) * p = C (k : ℚ) * p := by
    rw [← C_eq_coe_nat k]
  rw [h]
  exact whC hp (k : ℚ)

private lemma whNeg {n : ℕ} {p : MvPolynomial (Fin 4) ℚ}
    (hp : IsWeightedHomogeneous weights p n) :
    IsWeightedHomogeneous weights (-p) n := by
  have h : (-p : MvPolynomial (Fin 4) ℚ) = C (-1 : ℚ) * p := by
    rw [C_mul', neg_smul, one_smul]
  rw [h]
  exact whC hp (-1)

private lemma whSub {n : ℕ} {p q : MvPolynomial (Fin 4) ℚ}
    (hp : IsWeightedHomogeneous weights p n) (hq : IsWeightedHomogeneous weights q n) :
    IsWeightedHomogeneous weights (p - q) n := by
  rw [sub_eq_add_neg]; exact hp.add (whNeg hq)

/-- `P₄` is weighted-homogeneous of degree 4. -/
public theorem isWeightedHomogeneous_P4_uv :
    IsWeightedHomogeneous weights P4_uv 4 := by
  unfold P4_uv
  have h_v4 : IsWeightedHomogeneous weights ((X 1 : MvPolynomial (Fin 4) ℚ) ^ 4) 4 := by
    simpa using whX1.pow 4
  have h_u4 : IsWeightedHomogeneous weights ((X 0 : MvPolynomial (Fin 4) ℚ) ^ 4) 4 := by
    simpa using whX0.pow 4
  have h_u3v : IsWeightedHomogeneous weights ((X 0 : MvPolynomial (Fin 4) ℚ) ^ 3 * X 1) 4 := by
    have h := (by simpa using whX0.pow 3 : IsWeightedHomogeneous weights ((X 0)^3) 3).mul whX1
    simpa using h
  have h_uv3 : IsWeightedHomogeneous weights (X 0 * (X 1 : MvPolynomial (Fin 4) ℚ) ^ 3) 4 := by
    have h := whX0.mul (by simpa using whX1.pow 3 : IsWeightedHomogeneous weights ((X 1)^3) 3)
    simpa using h
  have h_u2v2 : IsWeightedHomogeneous weights
      ((X 0 : MvPolynomial (Fin 4) ℚ) ^ 2 * (X 1) ^ 2) 4 := by
    have h := (by simpa using whX0.pow 2 : IsWeightedHomogeneous weights ((X 0)^2) 2).mul
      (by simpa using whX1.pow 2 : IsWeightedHomogeneous weights ((X 1)^2) 2)
    simpa using h
  have t1 := whNat h_v4 4
  have t2 : IsWeightedHomogeneous weights (23 * X 0 * (X 1 : MvPolynomial (Fin 4) ℚ) ^ 3) 4 := by
    convert whNat h_uv3 23 using 1; ring
  have t3 : IsWeightedHomogeneous weights
      (18 * (X 0 : MvPolynomial (Fin 4) ℚ) ^ 2 * (X 1) ^ 2) 4 := by
    convert whNat h_u2v2 18 using 1; ring
  have t5 := whNat h_u4 4
  exact whSub ((whSub (whSub t1 t2) t3).add h_u3v) t5

/-- `A` is weighted-homogeneous of degree 4. -/
public theorem isWeightedHomogeneous_A_poly :
    IsWeightedHomogeneous weights A_poly 4 := by
  unfold A_poly
  have h3u := whNat whX0 3
  have hdiff := whSub h3u whX1
  have hv2 : IsWeightedHomogeneous weights ((X 1 : MvPolynomial (Fin 4) ℚ) ^ 2) 2 := by
    simpa using whX1.pow 2
  -- degrees: 1 + 2 + 1 = 4, and the product matches `A_poly` definitionally after unfold
  simpa using (whX0.mul hv2).mul hdiff

/-- `B` is weighted-homogeneous of degree 6. -/
public theorem isWeightedHomogeneous_B_poly :
    IsWeightedHomogeneous weights B_poly 6 := by
  have h : B_poly = C (1 / 4 : ℚ) * (X 0 * X 1 * P4_uv) := by
    unfold B_poly; ring
  rw [h]
  have hmul := (whX0.mul whX1).mul isWeightedHomogeneous_P4_uv
  -- degrees 1+1+4 = 6
  simpa using whC hmul (1 / 4 : ℚ)

/-- **Headline.** `surfaceEquation` is weighted-homogeneous of degree 6. -/
public theorem isWeightedHomogeneous_surfaceEquation :
    IsWeightedHomogeneous weights surfaceEquation 6 := by
  unfold surfaceEquation
  have hy2 : IsWeightedHomogeneous weights ((X 3 : MvPolynomial (Fin 4) ℚ) ^ 2) 6 := by
    simpa using whX3.pow 2
  have hx3 : IsWeightedHomogeneous weights ((X 2 : MvPolynomial (Fin 4) ℚ) ^ 3) 6 := by
    simpa using whX2.pow 3
  have hAx : IsWeightedHomogeneous weights (A_poly * X 2) 6 := by
    simpa using isWeightedHomogeneous_A_poly.mul whX2
  exact whSub (whSub (whSub hy2 hx3) hAx) isWeightedHomogeneous_B_poly

/-- Long form (3.9) is weighted-homogeneous of degree 6.

Proved by transporting the short-form result along the cleared completing-the-square identity
is not available without inverting 4 in the graded sense; we instead assemble termwise. -/
public theorem isWeightedHomogeneous_surfaceEquationLong :
    IsWeightedHomogeneous weights surfaceEquationLong 6 := by
  -- Rewrite long form as an explicit sum of known weighted-homogeneous pieces.
  have hy2 : IsWeightedHomogeneous weights ((X 3 : MvPolynomial (Fin 4) ℚ) ^ 2) 6 := by
    simpa using whX3.pow 2
  have hx3 : IsWeightedHomogeneous weights ((X 2 : MvPolynomial (Fin 4) ℚ) ^ 3) 6 := by
    simpa using whX2.pow 3
  have hAx : IsWeightedHomogeneous weights (A_poly * (X 2 : MvPolynomial (Fin 4) ℚ)) 6 := by
    simpa using isWeightedHomogeneous_A_poly.mul whX2
  have hd : IsWeightedHomogeneous weights
      ((X 1 : MvPolynomial (Fin 4) ℚ) - X 0) 1 := whSub whX1 whX0
  have hlin' : IsWeightedHomogeneous weights
      ((X 0 : MvPolynomial (Fin 4) ℚ) * X 1 * ((X 1) - X 0) * X 3) (1 + 1 + 1 + 3) :=
    ((whX0.mul whX1).mul hd).mul whX3
  have hlin : IsWeightedHomogeneous weights
      ((X 0 : MvPolynomial (Fin 4) ℚ) * X 1 * ((X 1) - X 0) * X 3) 6 :=
    by convert hlin'
  have s1 : IsWeightedHomogeneous weights ((X 1 : MvPolynomial (Fin 4) ℚ) ^ 4) 4 := by
    simpa using whX1.pow 4
  have s2 : IsWeightedHomogeneous weights
      ((6 : MvPolynomial (Fin 4) ℚ) * X 0 * (X 1) ^ 3) 4 := by
    have h0 : IsWeightedHomogeneous weights ((X 1 : MvPolynomial (Fin 4) ℚ) ^ 3) 3 := by
      simpa using whX1.pow 3
    have h := whNat (whX0.mul h0) 6
    convert h using 1; ring
  have s3 : IsWeightedHomogeneous weights
      ((4 : MvPolynomial (Fin 4) ℚ) * (X 0) ^ 2 * (X 1) ^ 2) 4 := by
    have hu2 : IsWeightedHomogeneous weights ((X 0 : MvPolynomial (Fin 4) ℚ) ^ 2) 2 := by
      simpa using whX0.pow 2
    have hv2 : IsWeightedHomogeneous weights ((X 1 : MvPolynomial (Fin 4) ℚ) ^ 2) 2 := by
      simpa using whX1.pow 2
    have h := whNat (hu2.mul hv2) 4
    convert h using 1; ring
  have s4 : IsWeightedHomogeneous weights ((X 0 : MvPolynomial (Fin 4) ℚ) ^ 4) 4 := by
    simpa using whX0.pow 4
  have hpoly4 : IsWeightedHomogeneous weights
      ((X 1 : MvPolynomial (Fin 4) ℚ) ^ 4 - 6 * X 0 * (X 1) ^ 3
        - 4 * (X 0) ^ 2 * (X 1) ^ 2 - (X 0) ^ 4) 4 :=
    whSub (whSub (whSub s1 s2) s3) s4
  have hB : IsWeightedHomogeneous weights
      ((X 0 : MvPolynomial (Fin 4) ℚ) * X 1 *
        ((X 1) ^ 4 - 6 * X 0 * (X 1) ^ 3 - 4 * (X 0) ^ 2 * (X 1) ^ 2 - (X 0) ^ 4)) 6 := by
    convert (whX0.mul whX1).mul hpoly4
  -- Assemble: y² + linear − x³ − Ax − B_long, matching `surfaceEquationLong`.
  have hpos : IsWeightedHomogeneous weights
      ((X 3 : MvPolynomial (Fin 4) ℚ) ^ 2 +
        X 0 * X 1 * (X 1 - X 0) * X 3) 6 := hy2.add hlin
  have hfinal := whSub (whSub (whSub hpos hx3) hAx) hB
  simpa [surfaceEquationLong] using hfinal

end WeightedHomogeneous

/-! ## Completing the square (note (3.12))

The short form involves the rational scalar `1/4`. Clearing denominators yields an
equivalent integer-coefficient identity, which closes by `ring`.
-/

/-- Cleared-denominator form of note (3.12): with `s = u v (v − u)`,
`(2y + s)² − 4 x³ − 4 A x − u v P₄ = 4 · (long form)`. -/
public theorem completing_the_square_cleared :
    let s : MvPolynomial (Fin 4) ℚ := X 0 * X 1 * (X 1 - X 0)
    (2 * X 3 + s) ^ 2 - 4 * (X 2) ^ 3 - 4 * A_poly * X 2 - X 0 * X 1 * P4_uv
      = 4 * surfaceEquationLong := by
  unfold surfaceEquationLong A_poly P4_uv
  ring


/-! ## The scheme `S_ℚ` -/

/-- The arithmetic surface `S_ℚ` of note (1.1). -/
public abbrev S_Q : Scheme :=
  weightedHypersurface (R := ℚ) surfaceEquation

/-- Closed immersion `S_ℚ ↪ ℙ_ℚ(1,1,2,3)`. -/
public def S_Q_ι : S_Q ⟶ WeightedProjectiveSpace ℚ :=
  weightedHypersurfaceι (R := ℚ) surfaceEquation

public instance S_Q_ι_isClosedImmersion : IsClosedImmersion S_Q_ι :=
  inferInstanceAs (IsClosedImmersion (weightedHypersurfaceι (R := ℚ) surfaceEquation))

/-- Underlying points of `S_ℚ` are `V₊(surfaceEquation)`. -/
public theorem range_S_Q_ι :
    Set.range S_Q_ι = hypersurfaceZeroLocus (R := ℚ) surfaceEquation :=
  range_weightedHypersurfaceι (R := ℚ) surfaceEquation

/-- `surfaceEquation` lies in the degree-6 graded piece. -/
public theorem mem_delPezzoGraded_surfaceEquation :
    surfaceEquation ∈ delPezzoGraded ℚ 6 :=
  (mem_weightedHomogeneousSubmodule ℚ weights 6 surfaceEquation).mpr
    isWeightedHomogeneous_surfaceEquation

/-! ## Ambient singular points: defining equation does not vanish

The singular locus of `ℙ(1,1,2,3)` is the pair of coordinate points `[0:0:1:0]` and
`[0:0:0:1]` (note Prop. 3.3). Their homogeneous ideals are `(u,v,y)` and `(u,v,x)`.
Evaluating the defining equation along the complementary free coordinate shows it does not
lie in either ideal, so neither point lies on the hypersurface zero locus.
-/

section AmbientSingularPoints

/-- Homogeneous ideal of `[0:0:1:0]`: `(u,v,y)`. -/
public def ambientSingularIdeal_x : HomogeneousIdeal (delPezzoGraded ℚ) where
  toSubmodule := Ideal.span (X '' ({0, 1, 3} : Set (Fin 4)))
  is_homogeneous' := by
    refine Ideal.homogeneous_span (delPezzoGraded ℚ) _ ?_
    intro p hp
    obtain ⟨i, _, rfl⟩ := (Set.mem_image X _ _).mp hp
    exact ⟨weights i, mem_delPezzoGraded_X ℚ i⟩

/-- Homogeneous ideal of `[0:0:0:1]`: `(u,v,x)`. -/
public def ambientSingularIdeal_y : HomogeneousIdeal (delPezzoGraded ℚ) where
  toSubmodule := Ideal.span (X '' ({0, 1, 2} : Set (Fin 4)))
  is_homogeneous' := by
    refine Ideal.homogeneous_span (delPezzoGraded ℚ) _ ?_
    intro p hp
    obtain ⟨i, _, rfl⟩ := (Set.mem_image X _ _).mp hp
    exact ⟨weights i, mem_delPezzoGraded_X ℚ i⟩

private noncomputable def aeval_keep (keep : Fin 4) :
    MvPolynomial (Fin 4) ℚ →ₐ[ℚ] Polynomial ℚ :=
  aeval fun i => if i = keep then (Polynomial.X : Polynomial ℚ) else 0

private lemma span_le_ker (keep : Fin 4) (s : Set (Fin 4)) (hs : keep ∉ s) :
    Ideal.span (X '' s) ≤ RingHom.ker (aeval_keep keep).toRingHom := by
  rw [Ideal.span_le]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := (Set.mem_image X _ _).mp hp
  change aeval_keep keep (X i) = 0
  simp only [aeval_keep, aeval_X]
  have : i ≠ keep := fun h => hs (h ▸ hi)
  simp [this]

private lemma aeval_keep_X (keep i : Fin 4) :
    aeval_keep keep (X i) = if i = keep then (Polynomial.X : Polynomial ℚ) else 0 := by
  simp [aeval_keep, aeval_X]

/-- Restricting to `u = v = y = 0` (free `x`) yields `-x³ ≠ 0`. -/
private lemma aeval_keep_2_surfaceEquation :
    aeval_keep 2 surfaceEquation = -((Polynomial.X : Polynomial ℚ) ^ 3) := by
  have hx0 : aeval_keep 2 (X 0) = 0 := by simp [aeval_keep_X]
  have hx1 : aeval_keep 2 (X 1) = 0 := by simp [aeval_keep_X]
  have hx2 : aeval_keep 2 (X 2) = Polynomial.X := by simp [aeval_keep_X]
  have hx3 : aeval_keep 2 (X 3) = 0 := by simp [aeval_keep_X]
  simp only [surfaceEquation, A_poly, B_poly, P4_uv, map_sub, map_add, map_mul, map_pow,
    map_ofNat, hx0, hx1, hx2, hx3, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 4 ≠ 0)]
  ring

/-- Restricting to `u = v = x = 0` (free `y`) yields `y² ≠ 0`. -/
private lemma aeval_keep_3_surfaceEquation :
    aeval_keep 3 surfaceEquation = (Polynomial.X : Polynomial ℚ) ^ 2 := by
  have hx0 : aeval_keep 3 (X 0) = 0 := by simp [aeval_keep_X]
  have hx1 : aeval_keep 3 (X 1) = 0 := by simp [aeval_keep_X]
  have hx2 : aeval_keep 3 (X 2) = 0 := by simp [aeval_keep_X]
  have hx3 : aeval_keep 3 (X 3) = Polynomial.X := by simp [aeval_keep_X]
  simp only [surfaceEquation, A_poly, B_poly, P4_uv, map_sub, map_add, map_mul, map_pow,
    map_ofNat, hx0, hx1, hx2, hx3, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 4 ≠ 0)]
  ring

/-- The defining equation is not in the ideal of `[0:0:1:0]`. -/
public theorem surfaceEquation_not_mem_ambientSingularIdeal_x :
    surfaceEquation ∉ ambientSingularIdeal_x := by
  intro h
  have hker := span_le_ker 2 ({0, 1, 3} : Set (Fin 4)) (by decide) h
  have heval : aeval_keep 2 surfaceEquation = 0 := hker
  rw [aeval_keep_2_surfaceEquation] at heval
  exact neg_ne_zero.mpr (pow_ne_zero 3 Polynomial.X_ne_zero) heval

/-- The defining equation is not in the ideal of `[0:0:0:1]`. -/
public theorem surfaceEquation_not_mem_ambientSingularIdeal_y :
    surfaceEquation ∉ ambientSingularIdeal_y := by
  intro h
  have hker := span_le_ker 3 ({0, 1, 2} : Set (Fin 4)) (by decide) h
  have heval : aeval_keep 3 surfaceEquation = 0 := hker
  rw [aeval_keep_3_surfaceEquation] at heval
  exact pow_ne_zero 2 Polynomial.X_ne_zero heval

/-- Note Prop. 3.3 (ideal form): the equation does not vanish at the ambient singular ideals,
so those points cannot lie on the hypersurface zero locus. -/
public theorem ambientSingularIdeals_avoid_surfaceEquation :
    surfaceEquation ∉ ambientSingularIdeal_x ∧
    surfaceEquation ∉ ambientSingularIdeal_y :=
  ⟨surfaceEquation_not_mem_ambientSingularIdeal_x,
    surfaceEquation_not_mem_ambientSingularIdeal_y⟩

end AmbientSingularPoints

/-! ## Axiom audit -/

#print axioms isWeightedHomogeneous_surfaceEquation
#print axioms isWeightedHomogeneous_surfaceEquationLong
#print axioms completing_the_square_cleared
#print axioms range_S_Q_ι
#print axioms surfaceEquation_not_mem_ambientSingularIdeal_x
#print axioms surfaceEquation_not_mem_ambientSingularIdeal_y

end DelPezzo

end ExplicitUnirational
