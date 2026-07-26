# Formalization roadmap

## Public theorem sequence

The project should expose increasingly faithful endpoints rather than hiding missing geometry inside definitions.

### Endpoint A: explicit unirational surface

Construct the explicit weighted sextic surface `S` and prove:

- `S → Spec k` is integral, smooth, and proper;
- there is a dominant rational map `𝔸²_k ⤏ S`;
- the induced function-field extension is finite separable of degree `9`.

### Endpoint B: degree-one del Pezzo recognition

Develop enough weighted adjunction, invertible-sheaf, ampleness, and intersection theory to prove that `-K_S` is ample and `K_S² = 1`.

### Endpoint C: arithmetic Picard rank one

Develop the specialized blow-up and Néron–Severi theory needed to identify the geometric Picard representation with the augmentation representation of the nine base points. Transitivity then gives arithmetic Picard rank one.

## Work packages

### WP0 — project foundation

- Pin Lean and Mathlib.
- Extract or reproduce the small unirationality API from `mattrobball/unirational`.
- Establish exact theorem guards, `#guard_no_sorry`, and axiom-audit conventions.

### WP1 — arithmetic certificates

Formalize the exact polynomial identities, discriminant factorizations, Rabin tests, and Bézout certificates used by the three examples.

### WP2 — generic-degree API

For dominant rational maps of integral schemes:

- construct the pullback embedding of function fields;
- define generic finiteness, generic degree, and generic separability;
- prove invariance under restriction and birational replacement;
- prove multiplicativity under composition.

### WP3 — cubic-pencil incidence surface

Construct

`Γ = {u F₀ + v F₁ = 0} ⊂ ℙ² × ℙ¹`

using the existing projective/biprojective style from the unirational repository. Prove that projection to `ℙ²` is birational.

### WP4 — weighted projective geometry

Construct `ℙ(1,1,2,3)` from Mathlib's general `Proj` and weighted grading. Develop:

- the structure morphism;
- standard charts and overlap maps;
- weighted hypersurface ideal sheaves;
- properness and integrality;
- a weighted chartwise Jacobian criterion.

### WP5 — explicit degree-nine map

Obtain explicit rational functions for the ternary-cubic-to-Jacobian map and prove:

- the coordinate identities;
- compatibility with the pencil parameter;
- dominance;
- generic degree `9`;
- generic separability.

This work package should avoid developing the Picard functor or a general Jacobian construction.

### WP6 — Weierstrass models and fibres

Instantiate Mathlib's Weierstrass infrastructure and prove all displayed invariant and discriminant identities. Prove only the fibre facts required downstream: the relevant singular cubic fibres are geometrically irreducible.

### WP7 — first guarded main theorem

Assemble WP2–WP6 into a no-`sorryAx` theorem giving a smooth proper explicit surface with a generically separable degree-nine unirational parametrization.

### WP8 — divisor and blow-up foundations

Develop a focused theory for smooth projective rational surfaces:

- invertible sheaves or Cartier divisor classes;
- Picard and rational Néron–Severi groups;
- blow-up of a smooth point and a reduced finite scheme;
- exceptional divisor classes;
- intersection pairing and canonical-class formulas.

### WP9 — degree-one del Pezzo theorem

Prove weighted adjunction, ampleness of the anticanonical class, and `K² = 1` for the explicit surface.

### WP10 — augmentation representation theorem

For a cubic pencil with nine reduced base points and geometrically irreducible fibres, prove that the relevant rational Néron–Severi quotient is the augmentation representation

`{r : Fin 9 → ℚ | ∑ i, r i = 0}`.

Prove that transitivity of the Galois action implies no nonzero invariants.

### WP11 — arithmetic examples

- Over `ℚ`, use irreducibility of the degree-nine base polynomial directly; avoid Néron–Severi specialization.
- Over `𝔽₅`, compute the Frobenius action and extension-field Picard ranks.
- Over `ℂ(t)`, use irreducibility/transitivity; full `S₉` monodromy is optional.

## Deliberately deferred infrastructure

The headline theorem should not depend on general implementations of:

- Picard schemes;
- elliptic surfaces;
- Kodaira fibre classification;
- Tate's algorithm;
- Shioda–Tate;
- Mordell–Weil height pairings;
- the full Weyl group of `E₈`;
- topological monodromy giving the full `S₉` group.

These may be added later as independent generalizations.
