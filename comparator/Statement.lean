/-
Copyright (c) 2026 Matthew R. Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
import Mathlib

/-!
# Trusted comparator statement: unirationality of the note's Weierstrass model

This is the trusted statement interface. It intentionally imports only `Mathlib`, so the
claim cannot lean on any project definition that was shaped to make a proof go through.
The vocabulary is duplicated in `Solution.lean`; keeping the declarations structurally
identical lets the comparator check the theorem without unchecked definition holes.

The claim formalized is unirationality of the affine Weierstrass model of note eq. (3.7)
over `ℚ`: there is a dominant rational map from the affine plane to the surface.

Statement design note. The conclusion is an `↔` identifying the kernel of the evaluation
with the surface ideal, NOT a bare existence of a point on the surface. That matters: a
bare existence claim would be witnessed by degenerate points such as `ξ = η = ζ = 0`, and
would assert nothing. Requiring the kernel to be exactly the ideal forces the evaluation
to be injective on the coordinate ring, which is precisely dominance.

What this does NOT claim: nothing about the degree of the map (the note's value `9`), and
nothing about the weighted hypersurface `S_Q ⊂ ℙ(1,1,2,3)` — identifying the function
field of this affine model with that of `S_Q` is a separate birationality statement.
-/

@[expose] public section

namespace ExplicitUnirationalChallenge

open MvPolynomial

/-- The rational function field `ℚ(x, y)` in two variables. -/
abbrev PlaneField : Type := FractionRing (MvPolynomial (Fin 2) ℚ)

/-- The affine Weierstrass surface of note eq. (3.7), cleared of denominators:
`4η² − 4ξ³ − 4ζ²(3 − ζ)ξ − ζ·P(ζ)` with `P(z) = 4z⁴ − 23z³ − 18z² + z − 4`.
Variables: `X 0 = ξ`, `X 1 = η`, `X 2 = ζ`. -/
noncomputable def surfacePoly : MvPolynomial (Fin 3) ℚ :=
  4 * X 1 ^ 2 - 4 * X 0 ^ 3 - 4 * (X 2 ^ 2 * (3 - X 2)) * X 0
    - X 2 * (4 * X 2 ^ 4 - 23 * X 2 ^ 3 - 18 * X 2 ^ 2 + X 2 - 4)

/-- The coordinate ring of the affine Weierstrass model: `ℚ[ξ, η, ζ]` modulo the surface. -/
abbrev surfaceCoordRing : Type := MvPolynomial (Fin 3) ℚ ⧸ Ideal.span {surfacePoly}

/-- **Unirationality of the note's affine Weierstrass model (3.7).**

The coordinate ring of the surface admits an injective `ℚ`-algebra homomorphism into the
rational function field `ℚ(x, y)` in two variables. Equivalently: the function field of the
surface embeds into a purely transcendental extension of `ℚ` of transcendence degree two,
i.e. there is a dominant rational map `𝔸² ⤏ S` defined over `ℚ`. That is unirationality of
`S` over `ℚ` in its standard field-theoretic form.

Non-vacuity. The existential is over the MAP, and the content is carried by `Injective`:
the zero map and any map killing a non-ideal polynomial are excluded, so no degenerate
witness satisfies this. (An existential over a mere *point* of the surface would be
witnessed by `ξ = η = ζ = 0` and would assert nothing.) -/
theorem unirationality :
    ∃ φ : surfaceCoordRing →ₐ[ℚ] PlaneField, Function.Injective φ := by
  sorry

end ExplicitUnirationalChallenge
