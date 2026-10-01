# Lean formalization of the Toeplitz SOS results

The formalization uses Lean `v4.34.0-rc2` and Mathlib commit
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, pinned in
[lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json).
For the original real Toeplitz quartic, Lean proves SOS representability
for **2 ≤ N ≤ 20** and non-SOS for **every N ≥ 2^9961475**.
The negative theorem allows arbitrary real coefficients and any finite
number of homogeneous quadratic squares. It does not assert that the
quartic takes negative values or identify the first non-SOS order.

## Read this first

1. [Defs](ToeplitzSOS/Defs.lean): `V`, `toeplitzBW`, `IsSumSqHomQuad`, and
   `MI15` define the original variables, matrix polynomial, SOS predicate,
   and universal conjecture. `MI15` is a proposition definition;
   `Negative.not_MI15` is the proof of its negation.
2. [SharpStatement](ToeplitzSOS/Negative/SharpStatement.lean):
   `SharpNegativeResolution` states the sufficient bound;
   `sharpNegativeResolution_iff_explicit` exposes the finite square count,
   real coefficients, homogeneity, and polynomial equality.
3. [Resolution](ToeplitzSOS/Negative/Resolution.lean):
   `sharpNegativeResolution`, `sharp_negative_explicit`, and
   `not_isSumSqHomQuad_of_large_order` prove that statement.
   The proof combines `cornerGram_of_sos` in `CornerExtraction` with `no_cornerGram` and
   the proved `Analytic.analyticInputs`.
4. [Certificates/Range](ToeplitzSOS/Certificates/Range.lean):
   `toeplitzBW_isSumSq_of_le_20` collects the positive certificates;
   order 2 is in `Defs`, orders 3–20 are in `Certificates/Generated`.

The `2^33554433` statement in `Statement` and `ExplicitStatement` stays
as a **weaker corollary** of the `2^9961475` theorem. The word `sharp` in
registered names distinguishes these two sufficient bounds; it does not
claim an optimal order.

## Release modules

[ToeplitzSOSRelease](ToeplitzSOSRelease.lean) imports exactly `Defs`,
`Certificates.Range`, and `Negative.Resolution`.
[release-modules.json](release-modules.json) lists their complete local
import closure: **88 modules**, including the release root, in dependency
order. Mathlib and its dependencies are pinned separately by Lake.

| Modules | Count | Purpose |
|---|---:|---|
| `ToeplitzSOSRelease`, `ToeplitzSOS.Defs` | 2 | Entry point and original statement |
| `Certificates/{Basic, Range}`, `Certificates/Generated/N3`–`N20` | 20 | Positive certificates and their range theorem |
| `SOS/LinearSubstitution` | 1 | Homogeneous linear substitutions preserve SOS |
| `Negative/*.lean`, `Negative/Analytic/*.lean`, as listed in the manifest | 54 | Corner extraction, exact witness, analytic estimates, negative theorem |
| `ThmA/{Defs, Reindex, Commutator, Mixed, SameSide, Poly, Main}` | 7 | Residual-form decomposition used by the generated certificates; signed-index identities |
| `Kernel/Basic` | 1 | Wedge indices and Gram identities |
| `Uniform/{Corner, Bridge}` | 2 | Finite corner formula and its canonical Gram embedding |
| `General/Moment` | 1 | Quadratic polarization used to extract the full alternating frame |

The support modules in the last four rows are actual proof dependencies.
The manifest is the complete source inventory; the scope is the paper's
finite positive range and negative theorem.

## Build and cost

Run from this directory after installing the pinned Lean toolchain:

```sh
lake exe cache get             # fetch the pinned Mathlib build cache on a fresh clone
lake build                    # supporting modules and the negative theorem
./verify                      # build and audit the default library
./verify --certificates       # additionally build and audit N3–N20 and the release root
```

Do not run `lake update`: the dependency pins are part of the release.
`./verify --certificates` and `bash build-release.sh` compile generated
certificates one at a time. The latter performs the builds alone; the verifier
also audits every imported project declaration, including private and generated
ones. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
The verifier checks the exact module inventory and runs source-token and
untrusted-axiom rejection controls on every invocation, including with
`python3 -O verify`.

The last lines of the two verification commands are, respectively:

```text
PASS: Lean verification (default library)
PASS: Lean verification including certificates through N=20
```

With Mathlib already cached, representative clean-build costs are:

| Command | Wall time | Peak resident memory |
|---|---:|---:|
| `lake exe cache get` | depends on network and package cache | varies with dependency setup |
| `lake build` | about 14 minutes | about 9–10 GiB |
| `./verify` | about 14 minutes from clean sources; seconds with compiled files | about 9–10 GiB for a fresh build |
| `bash build-release.sh` | about 2–3 hours from clean sources | up to about 70 GiB |
| `./verify --certificates` | about 2–3 hours from clean sources; seconds with compiled files | up to about 70 GiB for a fresh build |

The default build is dominated by the 1024-point integer witness in
`Negative/WitnessCertificate`. The full build adds the certificates at orders
3–20 and the range theorem; allow at least 80 GiB of memory headroom and keep
certificate builds sequential. Times depend on the environment. Fetching or
building the pinned Mathlib dependencies is a separate initial cost.

The complete release build checks both headline results together. The default
library checks the negative theorem and the common certificate definitions.
The paper's displayed uniform statement ranges over every integer k ≥ 16;
Lean proves the ingredients and the required fixed-scale application at
k = 4980737, using the sharper coefficient-mass bound. The result map records
this scope for each numbered statement.
