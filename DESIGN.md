# Formalization design

Source of truth for the mathematics: Cheltsov–Loginov–Orlov–Prokhorov,
*Unirational del Pezzo surfaces of degree one*, arXiv:2608.15435v1. Citations of
the form `[CLOP §n.m]`, `[CLOP (n.m)]`, `[CLOP Lemma n.m]` below and in the Lean
docstrings refer to that paper.

This document supersedes the sequencing in `ROADMAP.md`. The work-package
content there is largely right; the *ordering* is not, for the reason given in
§2.

---

## 1. Dependency reality check

Verified against the local Mathlib checkout (`v4.32.0-rc1` tree, matching our
pinned `v4.32.1`).

### Present and directly usable

| Need | Mathlib |
| --- | --- |
| rational maps, dominance | `AlgebraicGeometry.Birational.{RationalMap,Dominant}` — `Scheme.PartialMap`, `X ⤏ Y`, `IsDominant`, `PartialMap.fromFunctionField` |
| function field of an integral scheme | `AlgebraicGeometry.FunctionField` — `Scheme.functionField`, `functionField_isFractionRing_of_isAffineOpen` |
| Weierstrass curves | `EllipticCurve.Weierstrass` — `c₄`, `c₆`, `Δ`, `j`; plus `VariableChange`, `NormalForms`, `Reduction` |
| **division polynomials with exact degrees** | `EllipticCurve.DivisionPolynomial.{Basic,Degree}` — `W.Φ n`, `W.ΨSq n`, `natDegree_Φ` (`= n.natAbs ^ 2`), `natDegree_ΨSq` (`= n.natAbs ^ 2 - 1`), `Ψ₃`, `natDegree_Ψ₃ = 4` |
| **degree of a rational function as a field extension** | `FieldTheory.RatFunc.IntermediateField` — `RatFunc.finrank_eq_max_natDegree : Module.finrank K⟮f⟯ K⟮X⟯ = max f.num.natDegree f.denom.natDegree` |
| weighted gradings | `RingTheory.MvPolynomial.WeightedHomogeneous`, `AlgebraicGeometry.ProjectiveSpectrum` |

### Absent — must be built here

Weighted projective space **as a scheme**; blow-ups of schemes; Picard /
Néron–Severi group of a scheme; intersection pairing; ampleness and del Pezzo
recognition; Kodaira fibre types; Tate's algorithm; Shioda–Tate; Mordell–Weil;
**generic degree of a dominant rational map**.

### Sibling asset — reuse, do not rebuild

`../unirational/problems/B-conic-bundle-multisections/` is 279 modules / ~83k
lines on the *same toolchain*. Directly relevant:

- `Unirationality.lean`, `UnirationalTower.lean`, `BirationalUnirationality.lean`
  — `UnirationalParametrization`, `HasUnirationalParametrization`,
  `IsUnirationalOver`, transport along birational maps and partial isos.
  Note: this API has **no degree**; adding it is WP2.
- `HesseNormalForm*.lean`, `ShortWeierstrassNormalForm.lean` — plane-cubic
  normal forms, `hesseWeierstrass`, discriminant/`c₄`/`j` lemmas,
  `exists_shortWeierstrass_coordinates`.
- `Standard/ShortWeierstrassTangentResidual.lean`,
  `ResidualLineMap*.lean`, `TangentPointResidualInfinitesimalCertificate.lean`
  — the tangent-residual construction (see §3, route B).
- `Biprojective*.lean` — charts, overlaps, Jacobian smoothness criterion,
  projection dominance for `P² × P¹`. This is exactly the ambient of the
  incidence surface `Γ` — the blow-up `Y = Bl_Σ ℙ²` of [CLOP §3], realized as
  `{u f₀ + v f₁ = 0} ⊂ ℙ² × ℙ¹` for the pencils of [CLOP §4.1] and [CLOP §4.2] —
  so WP3 is mostly instantiation.

That repo has ~57 `sorry`s; anything imported must be checked with
`#print axioms` before it enters a guarded endpoint.

---

## 2. The ordering problem, and the fix

`ROADMAP.md` puts WP4 (weighted projective schemes) upstream of every headline
theorem. That inverts the risk: constructing `P(1,1,2,3)` as a scheme with
charts, properness, and a weighted Jacobian criterion is a Mathlib-scale
project, and until it lands **nothing** in the paper is formalized.

The paper's actual content — the degree-9 map, the invariant computations, the
irreducibility certificates, the Frobenius representation — needs none of it.

**Fix: insert Endpoint A0, a purely field-theoretic statement, upstream of all
scheme theory.** The ambient weighted projective space is then an
*upgrade in faithfulness*, not a prerequisite.

### The ladder

| Rung | Statement | New scheme theory needed | Risk |
| --- | --- | --- | --- |
| **L0** | Certificate tier: every polynomial identity, discriminant factorization, and irreducibility certificate behind the smoothness and fibre analysis of [CLOP Lemma 2.2], [CLOP Lemma 4.1] and [CLOP Lemma 4.2] (most of these computations are not displayed in [CLOP]) | none | low |
| **L0′** | The `gcd(9,n)` base-change rank formula (`ρ = 1, 3, 9`; not in [CLOP]) as a standalone representation-theoretic theorem | none | low |
| **A0** | For `k ∈ {ℚ, F₅, ℂ(t)}`: an explicit finite separable field extension of degree exactly 9 realizing the parametrization | none | medium |
| **A1** | A0 + `S` as a smooth proper scheme in `P(1,1,2,3)` | WP4 | high |
| **A2** | A1 packaged as `UnirationalParametrization` carrying degree 9 | WP2 | medium |
| **B** | `−K_S` ample, `K_S² = 1` (del Pezzo of degree 1) | invertible sheaves, ampleness, weighted adjunction | high |
| **C** | `ρ_k(S) = 1` | blow-up, NS, Shioda–Tate, Mordell–Weil | very high |

L0, L0′ and A0 together are the majority of the paper's verifiable content and
carry no research risk in the formalization. They ship first.

---

## 3. Endpoint A0 — the field-theoretic heart

### Statement shape

For a base field `k` with `char k ≠ 3`, put `K = k(z)`. Let `W : K` be the
Weierstrass curve of [CLOP §4.1] (resp. [CLOP §4.2]) — the equation for `J_η` —
and let `C/K` be the generic
member of the cubic pencil. The target is

```lean
theorem degree_nine (hk : (3 : k) ≠ 0) :
    ∃ (φ : FunctionField_of_W →ₐ[K] FunctionField_of_C),
      Module.finrank (φ.range) (FunctionField_of_C) = 9 ∧
      Algebra.IsSeparable (φ.range) (FunctionField_of_C)
```

with `FunctionField_of_C ≃ₐ[k] RatFunc₂ k` (two variables) supplied separately
by the rationality of the incidence surface ([CLOP §3], `Y = Bl_Σ ℙ²`). Exact
signatures are fixed in WP-A0 below before dispatch.

### Why this is now tractable

[CLOP Lemma 3.4] proves `deg μ_A = n²` abstractly via the relative Abel–Jacobi
map, specialized in [CLOP Example 3.5] to `Z = ℙ²`, `A = 𝒪(1)`, `n = 3`, so
`deg = 9`; the argument runs through `Pic` and the multiplication-by-3 isogeny. Formalizing `Pic` of a
genus-one curve and the degree of an isogeny is out of reach at this stage.

**Replace it with the explicit computation on the `x`-line.** Over any field,
`x ∘ [3] = Φ₃ / ΨSq₃` as a rational function, and Mathlib already gives

- `natDegree_Φ (n := 3) : (W.Φ 3).natDegree = 9`
- `natDegree_ΨSq (n := 3) : (W.ΨSq 3).natDegree = 8`

so `RatFunc.finrank_eq_max_natDegree` yields `max 9 8 = 9` for the extension
`K(x) / K(x ∘ [3])` directly. Combined with `[K(W) : K(x)] = 2` on both sides,
`deg[3] = 9`. Separability is `char ≠ 3` via `Ψ₃ ≠ 0`
(`natDegree_Ψ₃` needs `(3 : R) ≠ 0`, which is exactly the paper's standing
assumption `char 𝕜 ≠ 2, 3`).

This is the same theorem by a strictly more elementary route, and it lands
almost entirely inside existing Mathlib.

### The one genuinely hard node

`C` is a torsor: the generic plane cubic `G_z = 0` has no `K`-rational point, so
`C ≇ W` over `K`, and [CLOP Lemma 3.4] is applied to a curve that is only
geometrically an elliptic curve. Bridging `K(C)` to `K(W)` is
Fisher [Fis08, Prop. 2.3] — [CLOP Example 2.1] cites it, and it is **not** in
Mathlib.

Two routes; build **A** first, keep **B** as fallback and as an independent
cross-check.

**Route A — descend the degree from `k̄`.** Degree of a finite extension of
function fields of geometrically integral curves is invariant under base change
to `k̄`. Over `k̄` the torsor trivializes, `C_k̄ ≅ W_k̄`, and the map is `[3]`
followed by a translation, so the degree is 9 by the paragraph above. Needs: `k`
algebraically closed in `K(C)` (geometric integrality of the generic cubic), and
`finrank` invariance under base change. Both are ordinary commutative algebra.

**Route B — explicit covariants.** `α(P) = [3P − λ]` and, since the tangent line
at `P` meets `C` at `P, P, Q`, one has `3P − λ ∼ P − Q(P)` where `Q(P)` is the
**tangent residual** of `P`. That construction is already formalized in the
sibling repo (`ShortWeierstrassTangentResidual`, `ResidualLineMapInjective`,
`TangentPointResidualInfinitesimalCertificate`). Route B then reduces to a
CAS-generated explicit pair of rational functions plus two Lean-checked facts:
the Weierstrass identity holds modulo `G_z`, and a degree-9 minimal polynomial
certificate. Mechanical, certificate-shaped, ideal for a subagent.

Route A is cheaper and more robust; Route B produces the explicit formulas the
README promises ("verified through explicit rational functions"). Doing both
gives an independent check on the paper's degree claim.

---

## 4. Work packages

Ordered by dispatch readiness. `⊥` = no upstream dependency.

### Tier L0 — certificates (fully parallel, no scheme theory)

Every one of these is a self-contained module over `Polynomial`/`MvPolynomial`.
The algebra is internally consistent — the discriminant factorizations
`Δ = −u²v²Q₈` and `4A³ + 27B² = 27u²v²Q₊Q₋`, and the `ξ = 36x, η = 216y`
normalizations turning [CLOP (2.1)] into the `J_η` equations of [CLOP §4.1]
and [CLOP §4.2], all check by hand — so these should close by `ring`/`decide`
plus the supplied witnesses.

- **C1 `Cert/Rabin.lean`** `⊥` — Rabin's irreducibility criterion over `ZMod q`
  ([LN97 §3.4]). *The only L0 item with real mathematical
  content*; everything below consumes it. Statement: for monic `f` of degree
  `n`, if `X^(q^n) ≡ X [MOD f]` and `IsCoprime f (X^(q^(n/ℓ)) - X)` for every
  prime `ℓ ∣ n`, then `Irreducible f`. Dispatch this one alone and first.
- **C2 `Cert/OcticF7.lean`** ← C1 — `f₈` irreducible over `F₇`, using an
  explicit Bézout pair `A₈, B₈` (computer-algebra generated; not in [CLOP]).
- **C3 `Cert/NonicF5.lean`** ← C1 — `R = X⁹ + X⁶ + X − 1` irreducible over `F₅`
  (witnesses `A_R, B_R`, likewise computer-algebra generated). This is the core
  of [CLOP Lemma 4.1].
- **C4 `Cert/SexticF5.lean`** ← C1 — `d₆ = X⁶ − X⁴ + X³ − X − 1` irreducible
  over `F₅` (witnesses `A₂,B₂,A₃,B₃`).
- **C5 `Cert/OcticQ.lean`** ← C2 — the discriminant octic `q₈` of the model
  [CLOP §1, `S_ℚ`] is irreducible over `ℚ` by Gauss + degree-preserving
  reduction mod 7.
- **C6 `Cert/Invariants.lean`** `⊥` — the Fisher invariants `c₄`, `c₆` of the
  two pencils, displayed in [CLOP §4.1] and [CLOP §4.2]: the Hessian
  normalization `H(g) = −½ det Hess(g)` of [CLOP Example 2.1] and the identity
  [CLOP (2.2)]. Pure `MvPolynomial (Fin 3)` expansion.
- **C7 `Cert/Discriminant.lean`** `⊥` — the discriminant factorizations
  `Δ = −u²v²Q₈` and `4A³ + 27B² = 27u²v²Q₊Q₋` for the models of [CLOP §1], plus
  the numeric values placing the roots of `Q₈`. None of this is displayed in
  [CLOP].
- **C8 `Cert/QuarticDiscriminants.lean`** `⊥` — `disc(q₊)`, `disc(q₋)`,
  `Res(q₊,q₋) = 256` in `ℚ[t]`, and their nonvanishing in `ℂ(t)` (not in
  [CLOP]).
- **C9 `Cert/BaseScheme.lean`** ← C3 — [CLOP Lemma 4.1] and [CLOP Lemma 4.3]:
  `f₀ = f₁ = 0` forces `z ≠ 0`, `y = x³`, and `x⁹ + x⁶ + x − 1 = 0` (resp.
  `x⁹ − x − 2t`); hence the base scheme is `Spec` of a degree-9 field.
- **C10 `Cert/NineCycle.lean`** `⊥` — [CLOP Cor 3.8] and the base-change rank
  formula as pure representation theory: the characteristic polynomial of a
  9-cycle on the zero-sum subrepresentation of `ℚ⁹` is `(T⁹−1)/(T−1)` (the
  polynomial displayed in [CLOP Example 3.10]), which factors as `Φ₃Φ₉`, and the
  fixed space of its `n`-th power has dimension `gcd(9,n) − 1`. **This proves the
  `ρ = 1, 3, 9` case split outright** (not stated in [CLOP]), independently of
  all geometry.

### Tier A0

- **WP-A0a `FunctionField/PencilRationality.lean`** `⊥` — rationality of the
  incidence surface ([CLOP §3], `Y = Bl_Σ ℙ²`) for the pencils of [CLOP §4.1]
  and [CLOP §4.2]:
  `k(Γ) ≅ k(s₁,s₂)` via `z = −F₀/F₁`, as an explicit `k`-algebra isomorphism of
  fraction fields. No schemes.
- **WP-A0b `FunctionField/MulThree.lean`** `⊥` — `deg[3] = 9` via `Φ₃`/`ΨSq₃` and
  `RatFunc.finrank_eq_max_natDegree`. Self-contained; **highest value per unit of effort in
  the whole project**. Statement shape: for `m₃ := (W.Φ 3 : RatFunc F) / (W.ΨSq 3)`,
  `Module.finrank F⟮m₃⟯ (RatFunc F) = 9`.

  **Gap found (verified 2026-07-27): `IsCoprime (W.Φ 3) (W.ΨSq 3)` is not in Mathlib** — there
  is no `IsCoprime` anywhere under `Mathlib/AlgebraicGeometry/EllipticCurve/`. It is required,
  not incidental: `finrank_eq_max_natDegree` is stated about `num`/`denom`, so a common factor
  `d` would give `9 - d.natDegree` rather than `9`. Two tracks, lower-load first:

  - **A0b-cert** (do first) — for the two *explicit* `J_η` curves of [CLOP §4.1]
    and [CLOP §4.2], certify
    coprimality by an explicit Bézout identity, CAS-generated and `ring`-checked. Over `ℚ` and
    `F₅` this is ordinary tier-L0 work; over `ℂ(t)` the witnesses carry `t` and live in
    `ℚ(t)[x]`.
  - **A0b-gen** (later) — the general theorem `IsCoprime (Φ n) (ΨSq n)` for an elliptic curve
    (`Δ ≠ 0`). Genuinely Mathlib-worthy, and the right generalization once the certificate
    route has pinned the statement down.
- **WP-A0c `FunctionField/TorsorDescent.lean`** ← A0b — Route A of §3.
- **WP-A0d `FunctionField/JacobianExplicit.lean`** ← C6 — Route B of §3;
  CAS-generated covariants, Lean-checked.
- **WP-A0e `Endpoint/A0.lean`** ← A0a–A0c — assembly + `#print axioms` guard.

### Tier A2 and above

- **WP2 `GenericDegree.lean`** — for dominant `f : X ⤏ Y` of integral schemes,
  the induced `Y.functionField →+* X.functionField` (Mathlib's
  `PartialMap.fromFunctionField` gives the map), `genericDegree` as `finrank`,
  generic separability; invariance under `PartialMap.equiv`, restriction and
  birational replacement; multiplicativity under composition. This is the piece
  the sibling repo's `UnirationalParametrization` is missing.
- **WP3 `CubicPencil/Incidence.lean`** ← Biprojective* from the sibling repo —
  `Γ ⊂ P² × P¹` and birationality of the projection.
- **WP4 `WeightedProjective/`** — `P(1,1,2,3)` from `Proj` of the weighted
  graded ring; structure morphism, four standard charts, overlaps, weighted
  hypersurfaces, properness, integrality, chartwise Jacobian criterion. The
  single largest package. Gate A1/B/C behind it; gate nothing else.
- **WP6 `Weierstrass/Fibres.lean`** — the invariant and discriminant identities
  (mostly done in C6/C7), plus *only* the fibre facts used downstream: the
  relevant singular fibres are geometrically irreducible. Do **not** formalize
  Tate's algorithm; state the type-II / type-I₁ conclusions as the specific
  irreducibility facts they are used for.
- **WP8–WP11** — as in `ROADMAP.md`. Re-scope only after WP4 lands.

---

## 5. Conventions

1. **No `sorry`, no `native_decide`** in anything reachable from an endpoint.
   Certificates are explicit witnesses (computer-algebra generated Bézout
   pairs), checked by `decide`/`ring`/`norm_num`.
2. Every module that an endpoint depends on gets a neighbouring
   `*AxiomAudit.lean` with `#print axioms`, matching the sibling repo's
   convention.
3. Endpoint statements are frozen in `Endpoint/*.lean` and are never edited to
   fit a proof. If a proof will not close against the frozen statement, that is
   escalated, not worked around.
4. Imports from `../unirational` are vendored explicitly with provenance and an
   axiom audit; nothing is imported transitively without a check.
5. CAS (Sage / Macaulay2 / sympy) generates certificates only. Lean checks
   every one. No CAS output is trusted.

---

## 6. Build protocol for subagents

Grok subagents execute well and plan poorly, so every dispatched task is
fully specified before it starts and carries no design latitude.

### Dispatch mode: sealed typed artifact

Following the house pattern in the blueprint generator
(`~/lean/blueprint_harness_restart/src/bphr/dispatch.py`, `GrokCliBackend`):

```
grok -p "<brief>" -m grok-4.5 --reasoning-effort high --cwd <repo> \
     --output-format plain --sandbox read-only --session-id <UUID> < /dev/null
```

**grok never writes the repo.** It reads for grounding and returns the complete module as
one fenced `lean` block; the orchestrator writes it, runs `lake build`, and feeds compiler
errors back on the same `--session-id`. Ground truth on the build therefore stays with the
orchestrator rather than a subagent self-report, and every dispatch is a clean revertible
diff authored in one place.

Two consequences for brief-writing, both load-bearing:

- Because the subagent cannot iterate against the compiler, **grounding beats recall**. Every
  brief must name the specific dependency source files to read, and must ask the subagent to
  flag explicitly any lemma name or signature it could not verify.
- The older sealed harness disqualified grok at probe tier for exactly this failure mode
  (9/20 dispatches emitted no Lean; 8/20 narrated first —
  `blueprint_harness_implementation/config.live.yaml` §5.9). So the output contract is stated
  as a hard constraint: commentary before the block, exactly one block, nothing after it.

### Brief contents

A task brief must contain:

1. Exact file path and module name.
2. **The exact `theorem`/`def` signatures to be proved, written out in full.**
   The subagent may add private lemmas; it may not alter a given signature.
3. The permitted import list.
4. The [CLOP] section / equation numbers being formalized, with the relevant
   text quoted inline.
5. Any witnesses (Bézout pairs, coefficient lists), transcribed or
   computer-algebra generated.
6. Definition of done, checked by the orchestrator not the subagent:
   `lake build` clean, plus `#print axioms` showing only `propext`,
   `Classical.choice`, `Quot.sound`.
7. Explicit prohibitions: no `sorry`, no `native_decide`, no signature edits, no
   new dependencies, no attempt to write files or run `lake`.

Dispatch order: C1 alone → then C2–C10 and WP-A0a/A0b fully in parallel →
then A0c/A0d → then A0e. Only after A0 is guarded do WP2/WP3, and only after
those is WP4 worth starting.

C1 goes alone because it is the only tier-L0 item with real mathematical content and
because its answer to one question — which tactic actually discharges the ladder step
identities over `ZMod 5` / `ZMod 7` at degree 8–9 — parameterizes the C2/C3/C4 briefs.

---

## 7. Open questions for the author

1. **Faithfulness of A0.** A0 states the degree-9 result about function fields
   rather than about a surface in `P(1,1,2,3)`. Is that an acceptable
   *published* intermediate endpoint, or strictly an internal milestone?
2. **Route A vs. Route B** for the torsor node (§3) — or both, for the
   cross-check.
3. **WP4 scope.** A general `P(w₀,…,w_n)` is reusable and Mathlib-worthy; a
   bespoke `P(1,1,2,3)` glued from four explicit charts is perhaps a third of
   the work and sufficient here.
4. **Tate's algorithm.** Classifying the singular fibres as type II / type I₁
   needs it, but only geometric irreducibility of the singular fibres is used
   downstream — which is exactly what [CLOP Lemma 2.2] and the proof of
   [CLOP Lemma 4.1] turn on. Confirm we may state the weaker fact directly.
