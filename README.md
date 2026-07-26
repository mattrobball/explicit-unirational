# Explicit unirational degree-one del Pezzo surfaces

Lean 4 formalization of explicit degree-one del Pezzo surfaces over `ℚ`, `𝔽₅`, and `ℂ(t)` with arithmetic Picard rank one and a generically separable unirational parametrization of degree nine.

The mathematical source is the research note **Explicit Unirational Degree-One Del Pezzo Surfaces of Arithmetic Picard Rank One over Q, F5, and C(t)**.

## Target results

The project is organized around three guarded endpoints.

1. Construct the explicit weighted sextic surface and prove that it is smooth and proper.
2. Construct a dominant rational map from affine two-space, prove generic separability, and compute generic degree `9`.
3. Identify the geometric Néron–Severi representation with the augmentation representation of the nine base points and deduce arithmetic Picard rank `1`.

The first major milestone deliberately avoids general Picard-scheme and elliptic-surface theory: the degree-nine map should be verified through explicit rational functions and function-field calculations.

## Dependency strategy

- Lean `4.32.1`
- Mathlib `v4.32.1`
- Reuse or extract the unirationality and birational-transfer API from [`mattrobball/unirational`](https://github.com/mattrobball/unirational)
- Use external computer algebra only to generate certificates; Lean checks every polynomial identity and finite-field certificate

## Planned layers

- `Unirational`: dominant rational maps, generic degree, and separability
- `WeightedProjective`: `ℙ(1,1,2,3)`, weighted hypersurfaces, charts, and smoothness
- `CubicPencil`: the incidence surface, nine-point base scheme, and the explicit degree-nine covering
- `Weierstrass`: explicit models, invariants, discriminants, and irreducible singular fibres
- `Picard`: blow-ups, divisor classes, Néron–Severi groups, and the augmentation representation
- `Arithmetic`: exact certificates over `ℚ` and `𝔽₅`
- `FunctionFieldFamily`: the `ℂ(t)` example

See [`ROADMAP.md`](ROADMAP.md) for the work-package decomposition and dependency boundary.

## Build

```bash
lake update
lake build
```

No theorem advertised as a project endpoint should depend on `sorryAx`. Endpoint modules will have neighboring axiom audits and exact statement guards.
