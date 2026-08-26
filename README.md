# Explicit unirational degree-one del Pezzo surfaces

Lean 4 formalization, in progress, of explicit degree-one del Pezzo surfaces over `ℚ`, `𝔽₅`, and `ℂ(t)` with arithmetic Picard rank one and a generically separable unirational parametrization of degree nine. See [What is proved so far](#what-is-proved-so-far) for the current checked endpoint and how it falls short of the full theorem.

## Natural-language source

This repository is a formal (Lean) counterpart to a research paper. Every definition and theorem here is a formalization of the natural-language mathematics in

> Ivan Cheltsov, Konstantin Loginov, Dmitri Orlov, and Yuri Prokhorov,
> **Unirational del Pezzo surfaces of degree one**,
> arXiv:2608.15435 [math.AG], 15 August 2026.
> <https://arxiv.org/abs/2608.15435> · <https://doi.org/10.48550/arXiv.2608.15435>

The surfaces, the degree-nine parametrization, and the Picard-rank argument are theirs. This repository contributes no new mathematics; it only re-states their constructions and proofs in a form Lean can check. The three base fields below correspond to the paper's Theorems 1.4 (`ℚ`), 1.5 (`𝔽₅`), and 1.6 (`ℂ(t)`).

The formalization was written against an earlier draft of the paper, kept as plain text at [`docs/note.txt`](docs/note.txt) under the working title *Explicit Unirational Degree-One Del Pezzo Surfaces of Arithmetic Picard Rank One over Q, F5, and C(t)*. Section, theorem, and equation numbers cited in [`DESIGN.md`](DESIGN.md) and in Lean docstrings refer to that draft; they do not match the arXiv numbering.

```bibtex
@misc{cheltsov2026unirationaldelpezzosurfaces,
  title         = {Unirational del Pezzo surfaces of degree one},
  author        = {Ivan Cheltsov and Konstantin Loginov and Dmitri Orlov and Yuri Prokhorov},
  year          = {2026},
  eprint        = {2608.15435},
  archivePrefix = {arXiv},
  primaryClass  = {math.AG},
  url           = {https://arxiv.org/abs/2608.15435},
}
```

## What is proved so far

The one independently checked endpoint is [`comparator/Statement.lean`](comparator/Statement.lean):

> **`unirationality`.** The coordinate ring of the affine Weierstrass model
> `4η² = 4ξ³ + 4ζ²(3 − ζ)ξ + ζ(4ζ⁴ − 23ζ³ − 18ζ² + ζ − 4)`
> (the chart `u = 1` of `S_ℚ`; draft eq. (3.7)) admits an injective `ℚ`-algebra map into `ℚ(x, y)`.
> Equivalently, there is a dominant rational map `𝔸²_ℚ ⤏ S_ℚ`, so `S_ℚ` is unirational over `ℚ`.

`Statement.lean` imports only Mathlib, so the claim cannot depend on any project definition. The proof in [`comparator/Solution.lean`](comparator/Solution.lean) uses only the axioms `propext`, `Quot.sound`, `Classical.choice` (`#print axioms`, Lean 4.32.1).

Verification status, honestly: an independent kernel replay with Lean Comparator accepted an earlier version of this proof on 2026-07-28 (see [`comparator/README.md`](comparator/README.md)). On 2026-08-26 the certificate checking was moved to Macaulean's GMP-free path (below), which changes the proof term; that version has been kernel-checked by Lean 4.32.1 locally but not yet replayed through Comparator. Both dates predate Lean v4.33.1, the release that stopped shipping the GMP 6.1.2 build implicated in the July 2026 kernel-soundness incident; the next replay should use ≥ 4.33.1 and the second kernel (`enable_nanoda` is now on in [`comparator/unirationality.json`](comparator/unirationality.json)).

### How the proof relates to the paper's

- **The map is the paper's map.** `ζ = −f₀/f₁` is the pencil parameter (the incidence surface is rational; draft Lemma 3.1), and `ξ = Θ/H²`, `η = J/(2H³)` are the classical covariant formulas for the map from a plane cubic to its Jacobian, which is Lemma 2.1's `P ↦ 3P − λ` with `λ = 𝒪_C(1)`. Definitions: [`ExplicitUnirational/FunctionField/Unirationality.lean`](ExplicitUnirational/FunctionField/Unirationality.lean).
- **The verification is by explicit computation, not by the paper's argument.** That the map lands on the surface is the covariant syzygy `J² ≡ 4Θ³ + …` modulo the cubic, checked as a polynomial identity: computer-algebra-generated quotient/remainder certificates (defined with Macaulean's [`poly_def`](https://github.com/Macaulean/Macaulean/blob/gmp-free-certificates/Macaulean/PolyDef.lean) command) are verified by [Macaulean](https://github.com/Macaulean/Macaulean)'s `algebra_norm_reflect`, a reflection tactic checked by one kernel evaluation — no `native_decide`, and on its default path no GMP: coefficients are carried as residues modulo ~31-bit moduli with a proved bound lifting the result back to `ℤ`, so every natural number the kernel computes with stays below 2^63 (see the audit in Macaulean's `KroneckerMod.lean`). Dominance, which the paper gets from "a finite map of degree 9 induces an inclusion of function fields", is proved directly: `ζ` is transcendental, `ξ` is independent of `ζ` by specialising to the cuspidal fibre `ζ = 0`, and `η` follows from the quadratic relation ([`FunctionField/Dominance.lean`](ExplicitUnirational/FunctionField/Dominance.lean)). This elementary route was the intended design; see the note under *Target results*.

### Not yet part of the checked statement

- **Degree 9.** Proved separately (`finrank_mulThreeX_noteCurveQ` in [`FunctionField/MulThreeCert.lean`](ExplicitUnirational/FunctionField/MulThreeCert.lean): the function-field extension has degree 9), but not connected to the comparator theorem.
- **Separability**, the weighted model `S_ℚ ⊂ ℙ(1,1,2,3)` and its smoothness, the del Pezzo property, and Picard rank one. Modules for these exist (`CubicPencil`, `WeightedProjective`, `DelPezzo`, `Divisors`, `Weierstrass`) but are not on the import path of the checked theorem.
- The surfaces over `𝔽₅` and `ℂ(t)`.

## Target results

The project is organized around three guarded endpoints.

1. Construct the explicit weighted sextic surface and prove that it is smooth and proper.
2. Construct a dominant rational map from affine two-space, prove generic separability, and compute generic degree `9`.
3. Identify the geometric Néron–Severi representation with the augmentation representation of the nine base points and deduce arithmetic Picard rank `1`.

The first major milestone deliberately avoids general Picard-scheme and elliptic-surface theory: the degree-nine map should be verified through explicit rational functions and function-field calculations.

## Dependency strategy

- Lean `4.32.1`
- Mathlib `v4.32.1`
- [Macaulean](https://github.com/Macaulean/Macaulean), branch `gmp-free-certificates`, pinned by commit in `lakefile.toml`: verified reflective polynomial-identity checking (`algebra_norm_reflect`). Mathlib-free; builds on this project's toolchain.
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

## License

Apache 2.0; see [`LICENSE`](LICENSE).
