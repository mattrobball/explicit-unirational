/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.FunctionField.Unirationality
import all ExplicitUnirational.FunctionField.TangentResidual
import all ExplicitUnirational.FunctionField.PencilRationality
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Dominance of the unirational parametrization

Transcendence input for the injectivity of `surfaceCoordRingToPlane`.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace ExplicitUnirational

local notation "ι₂" => algebraMap (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ)

instance : IsScalarTower ℚ (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) :=
  FunctionField.isScalarTower_planeField

/-! ## Step 1: the pencil parameter is transcendental over `ℚ` -/

public theorem planeZeta_mul_f₁aff : planeZeta * ι₂ f₁aff = ι₂ (-f₀aff) := by
  have h : ι₂ f₁aff ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact f₁aff_ne_zero
  show FunctionField.pencilParameter f₀aff f₁aff * _ = _
  unfold FunctionField.pencilParameter
  rw [div_mul_cancel₀ _ h, map_neg]

/-- The pencil parameter `ζ = −f₀/f₁` is transcendental over `ℚ`. -/
public theorem transcendental_planeZeta : Transcendental ℚ planeZeta := by
  intro halg
  -- `ζ` is integral over `ℚ`, hence over `ℚ[x, y]`
  have hintQ : IsIntegral ℚ planeZeta := halg.isIntegral
  have hint : IsIntegral (MvPolynomial (Fin 2) ℚ) planeZeta := hintQ.tower_top
  -- `ℚ[x, y]` is a UFD, hence integrally closed in its fraction field
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have h1 : ι₂ (a * f₁aff) = ι₂ (-f₀aff) := by
    rw [map_mul, ha]; exact planeZeta_mul_f₁aff
  have h2 : a * f₁aff = -f₀aff :=
    IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) (FunctionField.planeField ℚ) h1
  -- evaluate at `(x, y) = (1, 0)`, where `f₁ = 0` but `-f₀ = 1`
  have h3 := congrArg (eval ![(1 : ℚ), 0]) h2
  simp [f₀aff, f₁aff] at h3

public theorem planeZeta_ne_zero : planeZeta ≠ 0 := by
  intro h
  have h1 : ι₂ (-f₀aff) = 0 := by rw [← planeZeta_mul_f₁aff, h, zero_mul]
  rw [IsFractionRing.to_map_eq_zero_iff] at h1
  have h2 := congrArg (eval ![(0 : ℚ), 1]) h1
  simp [f₀aff] at h2

/-! ## Step 2: the residue along the cuspidal fibre `ζ = 0`

The fibre `ζ = 0` of the pencil is the cuspidal cubic `y = x³`, which is rational:
it is parametrized by `t ↦ (t, t³)`.  Restricting a plane rational function to that
fibre is the "residue" used below; on the generic point of the fibre one has
`ζ ↦ 0` and `ξ = Θ/H² ↦ 1/(9t²)`, and the latter is transcendental over `ℚ`. -/

/-- Restriction of plane polynomials to the cuspidal fibre: `x ↦ t`, `y ↦ t³`. -/
public def rhoCurve : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] Polynomial ℚ :=
  aeval ![Polynomial.X, Polynomial.X ^ 3]

/-- Evaluation of ambient polynomials at the generic point of the fibre `ζ = 0`:
`(x, y, z) ↦ (t, t³, 0)`. -/
public def curveEval : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] Polynomial ℚ :=
  aeval ![Polynomial.X, Polynomial.X ^ 3, 0]

@[simp] public theorem rhoCurve_X0 : rhoCurve (X 0) = Polynomial.X := by simp [rhoCurve]
@[simp] public theorem rhoCurve_X1 : rhoCurve (X 1) = Polynomial.X ^ 3 := by simp [rhoCurve]
@[simp] public theorem curveEval_X0 : curveEval (X 0) = Polynomial.X := by simp [curveEval]
@[simp] public theorem curveEval_X1 : curveEval (X 1) = Polynomial.X ^ 3 := by simp [curveEval]
@[simp] public theorem curveEval_X2 : curveEval (X 2) = 0 := by simp [curveEval]

public theorem rhoCurve_f₀aff : rhoCurve f₀aff = 0 := by
  simp [f₀aff]

public theorem rhoCurve_f₁aff :
    rhoCurve f₁aff = Polynomial.X ^ 9 + Polynomial.X ^ 6 + Polynomial.X - 1 := by
  simp [f₁aff]; ring

public theorem rhoCurve_f₁aff_ne_zero : rhoCurve f₁aff ≠ 0 := by
  intro h
  have h0 : Polynomial.eval 0 (rhoCurve f₁aff) = 0 := by rw [h]; simp
  rw [rhoCurve_f₁aff] at h0
  simp at h0

/-- The Hessian covariant restricted to the fibre `ζ = 0`: `H(t, t³, 0) = 3t`. -/
public theorem curveEval_hessAff : curveEval hessAff = 3 * Polynomial.X := by
  simp [hessAff, map_ofNat]

/-- The covariant `Θ` restricted to the fibre `ζ = 0`: `Θ(t, t³, 0) = 1`. -/
public theorem curveEval_thetaAff : curveEval thetaAff = 1 := by
  simp [thetaAff, map_ofNat]

/-! ### Clearing denominators along `z ↦ ζ`

Every value `toPlane p` of the substitution `z ↦ ζ = −f₀/f₁` becomes a *polynomial*
after multiplying by a power of `f₁`, and the same power of `rhoCurve f₁aff` relates
the residue of `toPlane p` to `curveEval p`.  This is proved by induction on `p`, so no
explicit `z`-expansion of the covariants is needed. -/

public theorem exists_clear (p : MvPolynomial (Fin 3) ℚ) :
    ∃ (n : ℕ) (r : MvPolynomial (Fin 2) ℚ),
      toPlane p * ι₂ f₁aff ^ n = ι₂ r ∧
      curveEval p * rhoCurve f₁aff ^ n = rhoCurve r := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, MvPolynomial.C a, ?_, ?_⟩
      · rw [pow_zero, mul_one, ← MvPolynomial.algebraMap_eq, ← MvPolynomial.algebraMap_eq,
          AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
      · rw [pow_zero, mul_one, ← MvPolynomial.algebraMap_eq, ← MvPolynomial.algebraMap_eq,
          AlgHom.commutes, AlgHom.commutes]
  | add p q hp hq =>
      obtain ⟨n, r, h1, h2⟩ := hp
      obtain ⟨m, s, k1, k2⟩ := hq
      refine ⟨n + m, r * f₁aff ^ m + s * f₁aff ^ n, ?_, ?_⟩
      · rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← h1, ← k1]; ring
      · rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← h2, ← k2]; ring
  | mul_X p i hp =>
      obtain ⟨n, r, h1, h2⟩ := hp
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
      rcases hi with rfl | rfl | rfl
      · refine ⟨n, r * X 0, ?_, ?_⟩
        · rw [map_mul, map_mul, toPlane_X0, ← h1, planeX]; ring
        · rw [map_mul, map_mul, curveEval_X0, rhoCurve_X0, ← h2]; ring
      · refine ⟨n, r * X 1, ?_, ?_⟩
        · rw [map_mul, map_mul, toPlane_X1, ← h1, planeY]; ring
        · rw [map_mul, map_mul, curveEval_X1, rhoCurve_X1, ← h2]; ring
      · refine ⟨n + 1, r * -f₀aff, ?_, ?_⟩
        · rw [map_mul, map_mul, toPlane_X2, ← h1, ← planeZeta_mul_f₁aff]; ring
        · rw [map_mul, map_mul, curveEval_X2, map_neg, rhoCurve_f₀aff, ← h2]; ring

/-- If a plane rational function built from `x`, `y`, `ζ` vanishes, so does its
restriction to the fibre `ζ = 0`. -/
public theorem curveEval_eq_zero_of_toPlane_eq_zero {p : MvPolynomial (Fin 3) ℚ}
    (h : toPlane p = 0) : curveEval p = 0 := by
  obtain ⟨n, r, h1, h2⟩ := exists_clear p
  rw [h, zero_mul] at h1
  have hr : r = 0 := by
    have h1' := h1.symm
    rwa [IsFractionRing.to_map_eq_zero_iff] at h1'
  rw [hr, map_zero] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd h3 (pow_ne_zero _ rhoCurve_f₁aff_ne_zero)

/-! ### The residue of `ξ` on the fibre

`ξ = Θ/H²` restricts to `1/(9t²)` on the cuspidal fibre, which is transcendental
over `ℚ`. -/

local notation "rc" => algebraMap (Polynomial ℚ) (RatFunc ℚ)

/-- The value of `ξ` at the generic point of the fibre `ζ = 0`, namely `1/(9t²)`. -/
public def residueXi : RatFunc ℚ := (rc ((9 : Polynomial ℚ) * Polynomial.X ^ 2))⁻¹

public theorem nine_X_sq_ne_zero : ((9 : Polynomial ℚ) * Polynomial.X ^ 2) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.coeff · 2) h
  simp at this

public theorem transcendental_residueXi : Transcendental ℚ residueXi := by
  have hinj : Function.Injective (algebraMap (Polynomial ℚ) (RatFunc ℚ)) :=
    IsFractionRing.injective _ _
  have h9 : (9 : ℚ) ≠ 0 := by norm_num
  have h9C : ((9 : Polynomial ℚ) * Polynomial.X ^ 2)
      = Polynomial.C (9 : ℚ) * Polynomial.X ^ 2 := by
    rw [map_ofNat]
  have hpoly : Transcendental ℚ ((9 : Polynomial ℚ) * Polynomial.X ^ 2) := by
    rw [h9C]
    refine Polynomial.transcendental _ ?_ ?_
    · rw [Polynomial.natDegree_C_mul_X_pow 2 (9 : ℚ) h9]; norm_num
    · rw [Polynomial.leadingCoeff_C_mul_X_pow]
      exact mem_nonZeroDivisors_of_ne_zero h9
  have halg : Transcendental ℚ (rc ((9 : Polynomial ℚ) * Polynomial.X ^ 2)) :=
    (transcendental_algebraMap_iff (A := RatFunc ℚ) hinj).mpr hpoly
  intro hcon
  unfold residueXi at hcon
  rw [IsAlgebraic.inv_iff] at hcon
  exact halg hcon

/-- `ξ` is the quotient of two plane polynomials whose residues on the cuspidal fibre
are nonzero, with quotient `1/(9t²)`. -/
public theorem exists_xi_rep :
    ∃ a b : MvPolynomial (Fin 2) ℚ,
      xiPlane * ι₂ b = ι₂ a ∧ rhoCurve a ≠ 0 ∧
        rhoCurve b = (9 : Polynomial ℚ) * Polynomial.X ^ 2 * rhoCurve a := by
  obtain ⟨nT, rT, hT1, hT2⟩ := exists_clear thetaAff
  obtain ⟨nH, rH, hH1, hH2⟩ := exists_clear hessAff
  rw [curveEval_thetaAff, one_mul] at hT2
  rw [curveEval_hessAff] at hH2
  have hHne : toPlane hessAff ≠ 0 := toPlane_hessAff_ne_zero
  refine ⟨rT * f₁aff ^ (nH * 2), f₁aff ^ nT * rH ^ 2, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, map_pow, map_pow, map_pow, ← hH1, ← hT1]
    unfold xiPlane
    field_simp
    ring
  · rw [map_mul, map_pow, ← hT2]
    exact mul_ne_zero (pow_ne_zero _ rhoCurve_f₁aff_ne_zero)
      (pow_ne_zero _ rhoCurve_f₁aff_ne_zero)
  · rw [map_mul, map_mul, map_pow, map_pow, map_pow, ← hT2, ← hH2]
    ring

/-! ### Clearing denominators for a two-variable relation -/

public theorem exists_clear_pair (a b : MvPolynomial (Fin 2) ℚ)
    (hab : xiPlane * ι₂ b = ι₂ a)
    (hres : residueXi * rc (rhoCurve b) = rc (rhoCurve a))
    (P : MvPolynomial (Fin 2) ℚ) :
    ∃ (n m : ℕ) (r : MvPolynomial (Fin 2) ℚ),
      aeval ![planeZeta, xiPlane] P * ι₂ f₁aff ^ n * ι₂ b ^ m = ι₂ r ∧
      aeval ![(0 : RatFunc ℚ), residueXi] P * rc (rhoCurve f₁aff) ^ n * rc (rhoCurve b) ^ m
        = rc (rhoCurve r) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      refine ⟨0, 0, MvPolynomial.C c, ?_, ?_⟩
      · rw [pow_zero, pow_zero, mul_one, mul_one, ← MvPolynomial.algebraMap_eq,
          AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
      · rw [pow_zero, pow_zero, mul_one, mul_one, ← MvPolynomial.algebraMap_eq,
          AlgHom.commutes, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | add p q hp hq =>
      obtain ⟨n, m, r, h1, h2⟩ := hp
      obtain ⟨n', m', r', k1, k2⟩ := hq
      refine ⟨n + n', m + m', r * f₁aff ^ n' * b ^ m' + r' * f₁aff ^ n * b ^ m, ?_, ?_⟩
      · simp only [map_add, map_mul, map_pow]
        linear_combination (ι₂ f₁aff ^ n' * ι₂ b ^ m') * h1 + (ι₂ f₁aff ^ n * ι₂ b ^ m) * k1
      · simp only [map_add, map_mul, map_pow]
        linear_combination (rc (rhoCurve f₁aff) ^ n' * rc (rhoCurve b) ^ m') * h2
          + (rc (rhoCurve f₁aff) ^ n * rc (rhoCurve b) ^ m) * k2
  | mul_X p i hp =>
      obtain ⟨n, m, r, h1, h2⟩ := hp
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
      rcases hi with rfl | rfl
      · refine ⟨n + 1, m, r * -f₀aff, ?_, ?_⟩
        · simp only [map_mul, aeval_X, Matrix.cons_val_zero]
          rw [← h1, ← planeZeta_mul_f₁aff]; ring
        · simp only [map_mul, aeval_X, Matrix.cons_val_zero, map_neg, rhoCurve_f₀aff]
          simp
      · refine ⟨n, m + 1, r * a, ?_, ?_⟩
        · simp only [map_mul, aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [← h1, ← hab]; ring
        · simp only [map_mul, aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [← h2, ← hres]; ring

public theorem residue_eq_zero {a b : MvPolynomial (Fin 2) ℚ}
    (hab : xiPlane * ι₂ b = ι₂ a)
    (hres : residueXi * rc (rhoCurve b) = rc (rhoCurve a))
    (hb : rhoCurve b ≠ 0)
    {P : MvPolynomial (Fin 2) ℚ} (h : aeval ![planeZeta, xiPlane] P = 0) :
    aeval ![(0 : RatFunc ℚ), residueXi] P = 0 := by
  have hinj : Function.Injective (algebraMap (Polynomial ℚ) (RatFunc ℚ)) :=
    IsFractionRing.injective _ _
  obtain ⟨n, m, r, h1, h2⟩ := exists_clear_pair a b hab hres P
  rw [h, zero_mul, zero_mul] at h1
  have hr : r = 0 := by
    have h1' := h1.symm
    rwa [IsFractionRing.to_map_eq_zero_iff] at h1'
  rw [hr, map_zero, map_zero] at h2
  have hF : rc (rhoCurve f₁aff) ≠ 0 := fun hc => rhoCurve_f₁aff_ne_zero (hinj (by simpa using hc))
  have hB : rc (rhoCurve b) ≠ 0 := fun hc => hb (hinj (by simpa using hc))
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exact absurd h4 (pow_ne_zero _ hF)
  · exact absurd h3 (pow_ne_zero _ hB)

/-! ### From the residue relation to divisibility by `X 0` -/

/-- Setting the first variable to zero. -/
public def projX0 : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] Polynomial ℚ :=
  aeval ![0, Polynomial.X]

public theorem aeval_residue_eq (P : MvPolynomial (Fin 2) ℚ) :
    aeval ![(0 : RatFunc ℚ), residueXi] P = Polynomial.aeval residueXi (projX0 P) := by
  have hcomp : (Polynomial.aeval (R := ℚ) residueXi).comp projX0
      = aeval ![(0 : RatFunc ℚ), residueXi] := by
    apply MvPolynomial.algHom_ext
    intro i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
    rcases hi with rfl | rfl <;> simp [projX0]
  rw [← hcomp]; rfl

public theorem X0_dvd_sub_emb (P : MvPolynomial (Fin 2) ℚ) :
    (X 0 : MvPolynomial (Fin 2) ℚ) ∣
      P - Polynomial.aeval (X 1 : MvPolynomial (Fin 2) ℚ) (projX0 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [projX0]
  | add p q hp hq =>
      obtain ⟨c, hc⟩ := hp
      obtain ⟨d, hd⟩ := hq
      refine ⟨c + d, ?_⟩
      rw [map_add, map_add]
      linear_combination hc + hd
  | mul_X p i hp =>
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
      rcases hi with rfl | rfl
      · refine ⟨p, ?_⟩
        have hz : projX0 (p * X 0) = 0 := by simp [projX0]
        rw [hz, map_zero, sub_zero]; ring
      · obtain ⟨c, hc⟩ := hp
        refine ⟨c * X 1, ?_⟩
        have hz : projX0 (p * X 1) = projX0 p * Polynomial.X := by simp [projX0]
        rw [hz, map_mul, Polynomial.aeval_X, ← sub_mul, hc]; ring

public theorem X0_dvd_of_residue {P : MvPolynomial (Fin 2) ℚ}
    (h : aeval ![(0 : RatFunc ℚ), residueXi] P = 0) : (X 0 : MvPolynomial (Fin 2) ℚ) ∣ P := by
  rw [aeval_residue_eq] at h
  have hp0 : projX0 P = 0 := by
    by_contra hc
    exact transcendental_residueXi ⟨projX0 P, hc, h⟩
  have hd := X0_dvd_sub_emb P
  rw [hp0, map_zero, sub_zero] at hd
  exact hd

/-! ## Step 3: algebraic independence of the pencil parameter and `ξ` -/

/-- **The two coordinates `ζ` and `ξ` are algebraically independent over `ℚ`.**
Equivalently, the rational map `𝔸² ⤏ 𝔸²`, `(x, y) ↦ (ζ, ξ)`, is dominant. -/
public theorem algebraicIndependent_planeZeta_xiPlane :
    AlgebraicIndependent ℚ ![planeZeta, xiPlane] := by
  obtain ⟨a, b, hab, hane, hres0⟩ := exists_xi_rep
  have hb : rhoCurve b ≠ 0 := by
    rw [hres0]; exact mul_ne_zero nine_X_sq_ne_zero hane
  have h9 : rc ((9 : Polynomial ℚ) * Polynomial.X ^ 2) ≠ 0 := fun hc =>
    nine_X_sq_ne_zero
      (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) (by simpa using hc))
  have hres : residueXi * rc (rhoCurve b) = rc (rhoCurve a) := by
    rw [hres0, map_mul]
    unfold residueXi
    exact inv_mul_cancel_left₀ h9 _
  rw [algebraicIndependent_iff]
  have key : ∀ (n : ℕ) (P : MvPolynomial (Fin 2) ℚ), P.degreeOf 0 ≤ n →
      aeval ![planeZeta, xiPlane] P = 0 → P = 0 := by
    intro n
    induction n with
    | zero =>
        intro P hdeg h
        obtain ⟨Q, hQ⟩ := X0_dvd_of_residue (residue_eq_zero hab hres hb h)
        by_cases hQ0 : Q = 0
        · rw [hQ, hQ0, mul_zero]
        · exfalso
          have hd : P.degreeOf 0 = Q.degreeOf 0 + 1 := by
            rw [hQ, mul_comm]
            exact (degreeOf_mul_X_eq_degreeOf_add_one_iff 0 Q).mpr hQ0
          omega
    | succ n ih =>
        intro P hdeg h
        obtain ⟨Q, hQ⟩ := X0_dvd_of_residue (residue_eq_zero hab hres hb h)
        by_cases hQ0 : Q = 0
        · rw [hQ, hQ0, mul_zero]
        · exfalso
          have hQz : aeval ![planeZeta, xiPlane] Q = 0 := by
            rw [hQ, map_mul] at h
            simp only [aeval_X, Matrix.cons_val_zero] at h
            rcases mul_eq_zero.mp h with h' | h'
            · exact absurd h' planeZeta_ne_zero
            · exact h'
          have hd : P.degreeOf 0 = Q.degreeOf 0 + 1 := by
            rw [hQ, mul_comm]
            exact (degreeOf_mul_X_eq_degreeOf_add_one_iff 0 Q).mpr hQ0
          exact hQ0 (ih Q (by omega) hQz)
  intro P hP
  exact key (P.degreeOf 0) P le_rfl hP

#print axioms transcendental_planeZeta
#print axioms algebraicIndependent_planeZeta_xiPlane

end ExplicitUnirational
