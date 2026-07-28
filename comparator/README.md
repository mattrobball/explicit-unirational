# Comparator package: unirationality

Verified 2026-07-28. Comparator accepted this solution:

    Exporting #[ExplicitUnirationalChallenge.unirationality, propext, Quot.sound,
                Classical.choice, ...] from Solution
    Running Lean default kernel on solution.
    Lean default kernel accepts the solution
    Your solution is okay!

## What is checked

`Statement.lean` imports **only Mathlib** and rebuilds every definition it needs, so the
claim cannot lean on a project definition shaped to fit a proof. `Solution.lean` discharges
it with the development's `surfaceCoordRingToPlane` and `surfaceCoordRingToPlane_injective`.
Comparator exports the theorem, runs the Lean kernel independently on the exported term, and
verifies the axiom set is within `propext`, `Quot.sound`, `Classical.choice`.

## Running it

Comparator's sandbox (`landrun`) is Linux-only, so on macOS this needs a Linux container.

    container run -d --name eu-comparator --cpus 12 --memory 49152m \
      -v <workdir>:/work docker.io/library/ubuntu:24.04 sleep infinity

Inside, install Go + elan, then build the three pinned tools (see
`~/lean_eval/README.md` section 5 for the authoritative pins):

  * landrun      go install github.com/zouuup/landrun/cmd/landrun@5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
  * lean4export  github.com/leanprover/lean4export   @ 3de59f10bc4b4a0f2de698597aeb1246caa0df0a
  * comparator   github.com/leanprover/comparator    @ 71b52ec29e06d4b7d882726553b1ceb99a2499e0

IMPORTANT: build `lean4export` and `comparator` with the toolchain THIS PROJECT uses
(v4.32.1), not the v4.32.0-rc1 in their own `lean-toolchain`. `lean4export` reads oleans
produced by the workspace toolchain; a mismatch gives `incompatible header`, which is a
version-skew error and never a problem with the proof.

Then, from the project root:

    lake build Statement Solution
    lake env comparator config.json
