/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rationality of the incidence surface of a cubic pencil (Lemma 3.1)

Field-theoretic form of note Lemma 3.1 / §5.1: on the chart `Z = 1`, the pencil relation
`f₀ + z · f₁ = 0` is solved by the rational function `z = -f₀ / f₁` in the fraction field of
the affine plane. Consequently adjoining that parameter does not enlarge the function field.

No scheme theory: everything is stated in `MvPolynomial` and `FractionRing`.
-/

noncomputable section

open MvPolynomial IntermediateField

namespace ExplicitUnirational.FunctionField

variable {k : Type*} [Field k]

/-! ## Pencil relation in three affine variables `x, y, z` -/

/-- Dehomogenization of the pencil on the chart `Z = 1`: `g = f₀ + z * f₁` where `f₀, f₁`
are the affine cubics in `x = X/Z`, `y = Y/Z`, and the third variable is the pencil parameter
`z`. Variables of the result are indexed `0 ↦ x`, `1 ↦ y`, `2 ↦ z`. -/
public noncomputable def pencilRelation (f₀ f₁ : MvPolynomial (Fin 2) k) :
    MvPolynomial (Fin 3) k :=
  rename Fin.castSucc f₀ + (X (2 : Fin 3) : MvPolynomial (Fin 3) k) * rename Fin.castSucc f₁

/-- The rational function field of the affine plane: `Frac(k[x, y])`. -/
public abbrev planeField (k : Type*) [Field k] : Type _ :=
  FractionRing (MvPolynomial (Fin 2) k)

/-- The pencil parameter `z = -f₀ / f₁` as an element of the plane function field. -/
public noncomputable def pencilParameter (f₀ f₁ : MvPolynomial (Fin 2) k) :
    planeField k :=
  -(algebraMap (MvPolynomial (Fin 2) k) (planeField k) f₀) /
    algebraMap (MvPolynomial (Fin 2) k) (planeField k) f₁

/-! ## Helpers: coordinates generate the polynomial image inside the intermediate field -/

private theorem isScalarTower_planeField :
    IsScalarTower k (MvPolynomial (Fin 2) k) (planeField k) :=
  IsScalarTower.of_algebraMap_eq' rfl

private theorem algebraMap_eq_aeval_coords (f : MvPolynomial (Fin 2) k) :
    algebraMap (MvPolynomial (Fin 2) k) (planeField k) f =
      aeval (fun i : Fin 2 =>
        algebraMap (MvPolynomial (Fin 2) k) (planeField k)
          (X i : MvPolynomial (Fin 2) k)) f := by
  letI := isScalarTower_planeField (k := k)
  let φ : MvPolynomial (Fin 2) k →ₐ[k] planeField k :=
    IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (planeField k)
  have hφ : φ =
      aeval (fun i : Fin 2 =>
        algebraMap (MvPolynomial (Fin 2) k) (planeField k)
          (X i : MvPolynomial (Fin 2) k)) :=
    aeval_unique φ
  simpa [φ, IsScalarTower.toAlgHom_apply] using
    congrArg (fun g : MvPolynomial (Fin 2) k →ₐ[k] planeField k => g f) hφ

private theorem range_coords_eq (k : Type*) [Field k] :
    Set.range (fun i : Fin 2 =>
        algebraMap (MvPolynomial (Fin 2) k) (planeField k)
          (X i : MvPolynomial (Fin 2) k)) =
      ({algebraMap (MvPolynomial (Fin 2) k) (planeField k)
            (X (0 : Fin 2) : MvPolynomial (Fin 2) k),
          algebraMap (MvPolynomial (Fin 2) k) (planeField k)
            (X (1 : Fin 2) : MvPolynomial (Fin 2) k)} : Set (planeField k)) := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]

private theorem algebraMap_mem_adjoin_coords (f : MvPolynomial (Fin 2) k) :
    algebraMap (MvPolynomial (Fin 2) k) (planeField k) f ∈
      IntermediateField.adjoin k
        ({algebraMap (MvPolynomial (Fin 2) k) (planeField k)
              (X (0 : Fin 2) : MvPolynomial (Fin 2) k),
            algebraMap (MvPolynomial (Fin 2) k) (planeField k)
              (X (1 : Fin 2) : MvPolynomial (Fin 2) k)} : Set (planeField k)) := by
  let K := planeField k
  let x : K :=
    algebraMap (MvPolynomial (Fin 2) k) K (X (0 : Fin 2) : MvPolynomial (Fin 2) k)
  let y : K :=
    algebraMap (MvPolynomial (Fin 2) k) K (X (1 : Fin 2) : MvPolynomial (Fin 2) k)
  have h_aeval :
      algebraMap (MvPolynomial (Fin 2) k) K f =
        aeval (fun i : Fin 2 =>
          algebraMap (MvPolynomial (Fin 2) k) K (X i : MvPolynomial (Fin 2) k)) f :=
    algebraMap_eq_aeval_coords f
  have h_mem :
      algebraMap (MvPolynomial (Fin 2) k) K f ∈
        Algebra.adjoin k
          (Set.range fun i : Fin 2 =>
            algebraMap (MvPolynomial (Fin 2) k) K (X i : MvPolynomial (Fin 2) k)) := by
    rw [h_aeval, ← aeval_range]
    exact ⟨f, rfl⟩
  have h_le :
      Algebra.adjoin k ({x, y} : Set K) ≤
        (IntermediateField.adjoin k ({x, y} : Set K)).toSubalgebra :=
    Algebra.adjoin_le fun _ hz => IntermediateField.subset_adjoin k _ hz
  rw [range_coords_eq k] at h_mem
  exact h_le h_mem

private theorem algebraMap_ne_zero_of_ne_zero {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) :
    algebraMap (MvPolynomial (Fin 2) k) (planeField k) f ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf)

/-! ## Lemma 3.1 (field-theoretic form) -/

/-- Lemma 3.1: the incidence relation is solved by `z = -f₀ / f₁` in the rational function
field of the affine plane, and adjoining that parameter does not enlarge the field generated
by the two plane coordinates.

Concretely, if `K = Frac(k[x,y])`, `z = -f₀/f₁ ∈ K`, then `f₀ + z·f₁ = 0` in `K` and
`k(x,y,z) = k(x,y)` as intermediate fields of `K/k`. -/
public theorem adjoin_pencil_parameter_eq_top
    (f₀ f₁ : MvPolynomial (Fin 2) k) (hf₁ : f₁ ≠ 0) :
    (algebraMap (MvPolynomial (Fin 2) k) (planeField k) f₀ +
        pencilParameter f₀ f₁ *
          algebraMap (MvPolynomial (Fin 2) k) (planeField k) f₁ =
        (0 : planeField k)) ∧
      IntermediateField.adjoin k
          ({algebraMap (MvPolynomial (Fin 2) k) (planeField k)
                (X (0 : Fin 2) : MvPolynomial (Fin 2) k),
              algebraMap (MvPolynomial (Fin 2) k) (planeField k)
                (X (1 : Fin 2) : MvPolynomial (Fin 2) k),
              pencilParameter f₀ f₁} : Set (planeField k)) =
        IntermediateField.adjoin k
          ({algebraMap (MvPolynomial (Fin 2) k) (planeField k)
                (X (0 : Fin 2) : MvPolynomial (Fin 2) k),
              algebraMap (MvPolynomial (Fin 2) k) (planeField k)
                (X (1 : Fin 2) : MvPolynomial (Fin 2) k)} : Set (planeField k)) := by
  let K := planeField k
  let x : K :=
    algebraMap (MvPolynomial (Fin 2) k) K (X (0 : Fin 2) : MvPolynomial (Fin 2) k)
  let y : K :=
    algebraMap (MvPolynomial (Fin 2) k) K (X (1 : Fin 2) : MvPolynomial (Fin 2) k)
  let z : K := pencilParameter f₀ f₁
  let f₀K : K := algebraMap (MvPolynomial (Fin 2) k) K f₀
  let f₁K : K := algebraMap (MvPolynomial (Fin 2) k) K f₁
  have hf₁K : f₁K ≠ 0 := algebraMap_ne_zero_of_ne_zero hf₁
  refine ⟨?_root, ?_adjoin⟩
  · -- `f₀ + z * f₁ = 0`
    change f₀K + z * f₁K = 0
    dsimp only [z, pencilParameter, f₀K, f₁K]
    have hcancel :
        (-(algebraMap (MvPolynomial (Fin 2) k) K f₀) /
            algebraMap (MvPolynomial (Fin 2) k) K f₁) *
            algebraMap (MvPolynomial (Fin 2) k) K f₁ =
          -(algebraMap (MvPolynomial (Fin 2) k) K f₀) :=
      div_mul_cancel₀ _ hf₁K
    linear_combination hcancel
  · -- `k(x,y,z) = k(x,y)`
    have hz : z ∈ IntermediateField.adjoin k ({x, y} : Set K) := by
      have hf₀_mem := algebraMap_mem_adjoin_coords f₀
      have hf₁_mem := algebraMap_mem_adjoin_coords f₁
      dsimp only [z, pencilParameter, x, y] at hf₀_mem hf₁_mem ⊢
      exact IntermediateField.div_mem (IntermediateField.neg_mem _ hf₀_mem) hf₁_mem
    have hset : ({x, y, z} : Set K) = insert z {x, y} := by
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    change IntermediateField.adjoin k ({x, y, z} : Set K) =
      IntermediateField.adjoin k ({x, y} : Set K)
    rw [hset]
    refine le_antisymm ?_ (IntermediateField.adjoin.mono k _ (Set.subset_insert z {x, y}))
    rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff]
    exact ⟨hz, IntermediateField.subset_adjoin k {x, y}⟩

/-! ## Concrete pencils from the note -/

/-- Homogeneous forms of the rational pencil (3.1). Indices `0,1,2` correspond to `X,Y,Z`:
`F₀ = Y Z² - X³`. -/
public noncomputable def F₀_rat : MvPolynomial (Fin 3) ℚ :=
  (X 1 : MvPolynomial (Fin 3) ℚ) * (X 2 : MvPolynomial (Fin 3) ℚ) ^ 2 -
    (X 0 : MvPolynomial (Fin 3) ℚ) ^ 3

/-- Homogeneous forms of the rational pencil (3.1):
`F₁ = X Z² + Y³ + Y² Z - Z³`. -/
public noncomputable def F₁_rat : MvPolynomial (Fin 3) ℚ :=
  (X 0 : MvPolynomial (Fin 3) ℚ) * (X 2 : MvPolynomial (Fin 3) ℚ) ^ 2 +
    (X 1 : MvPolynomial (Fin 3) ℚ) ^ 3 +
    (X 1 : MvPolynomial (Fin 3) ℚ) ^ 2 * (X 2 : MvPolynomial (Fin 3) ℚ) -
    (X 2 : MvPolynomial (Fin 3) ℚ) ^ 3

/-- Homogeneous forms of the `C(t)` pencil (5.1). Indices `0,1,2` correspond to `X,Y,Z`:
`F₀ = Y Z² - X³` (independent of the base parameter `t`). -/
public noncomputable def F₀_t {R : Type*} [CommRing R] : MvPolynomial (Fin 3) R :=
  (X 1 : MvPolynomial (Fin 3) R) * (X 2 : MvPolynomial (Fin 3) R) ^ 2 -
    (X 0 : MvPolynomial (Fin 3) R) ^ 3

/-- Homogeneous forms of the `C(t)` pencil (5.1):
`F₁ = Y³ - X Z² - 2 t Z³`, with base parameter `t : R`. -/
public noncomputable def F₁_t {R : Type*} [CommRing R] (t : R) : MvPolynomial (Fin 3) R :=
  (X 1 : MvPolynomial (Fin 3) R) ^ 3 -
    (X 0 : MvPolynomial (Fin 3) R) * (X 2 : MvPolynomial (Fin 3) R) ^ 2 -
    (C (2 * t) : MvPolynomial (Fin 3) R) * (X 2 : MvPolynomial (Fin 3) R) ^ 3

end ExplicitUnirational.FunctionField
