# Verification record

Verification completed at **2026-10-02T20:22:10Z** (UTC), with the checks below
starting at 2026-10-02T16:47:44Z.

Verified source commit:
[`8e1d71634efa68b03b68b3963e419fcb98416d0d`](https://github.com/erenup/toeplitz-bw-not-sos/tree/8e1d71634efa68b03b68b3963e419fcb98416d0d).
The exact Git tree of `lean/` is **`69d02281c91fea6ff54fe3556aaddc43eae66e65`**.
The checks below verified this exact `lean/` tree.
The [v1.0 tag](https://github.com/erenup/toeplitz-bw-not-sos/tree/v1.0/lean)
contains exactly the same tree, frozen except for errata.

## Statement and scope

[`ToeplitzSOS.toeplitzBW`](https://github.com/erenup/toeplitz-bw-not-sos/blob/8e1d71634efa68b03b68b3963e419fcb98416d0d/lean/ToeplitzSOS/Defs.lean)
is defined directly as
`2 * frob X * frob Y - 2 * inner X Y ^ 2 - frob (X * Y - Y * X)`,
where `X` and `Y` are generic real Toeplitz matrices and `frob` is the
squared Frobenius norm. The variables are two independent real coordinate
families indexed by `Fin (2 * n - 1)`, hence `4n - 2` variables for `n ≥ 1`.
`IsSumSqHomQuad` quantifies over an arbitrary finite number of squares of
homogeneous quadratic polynomials with arbitrary real coefficients.
`MI15` is the assertion that this predicate holds for every `n ≥ 2`.

The verified declarations are:

- `ToeplitzSOS.Negative.not_MI15`: the negation of the original universal
  Toeplitz SOS conjecture, using exactly those definitions.
- `ToeplitzSOS.Negative.sharpNegativeResolution`: every order
  `N ≥ 2^9961475` is non-SOS for the original polynomial.
- `ToeplitzSOS.Negative.sharp_negative_explicit`: the same conclusion with
  the finite square count, real coefficient field, degree-two homogeneity
  and polynomial equality written explicitly.
- `ToeplitzSOS.toeplitzBW_isSumSq_of_le_20`: SOS at every integer order
  `2 ≤ N ≤ 20`.

The negative declarations are in
[`Negative/Resolution.lean`](https://github.com/erenup/toeplitz-bw-not-sos/blob/8e1d71634efa68b03b68b3963e419fcb98416d0d/lean/ToeplitzSOS/Negative/Resolution.lean);
the positive theorem is in
[`Certificates/Range.lean`](https://github.com/erenup/toeplitz-bw-not-sos/blob/8e1d71634efa68b03b68b3963e419fcb98416d0d/lean/ToeplitzSOS/Certificates/Range.lean).
All algebraic, analytic and arithmetic premises needed by the negative
theorems are proved in their dependencies. There are no unproved analytic
assumptions or restrictions on the SOS representation.
The bound is sufficient and does not identify the first non-SOS order.
The exact Python certificates through order 50 and the paper's broader
uniform finite-scale statement have the separate scopes recorded in
[`paper-lean-mapping/`](paper-lean-mapping/README.md).

## Toolchain and dependencies

Lean: `leanprover/lean4:v4.34.0-rc2`.
The actual dependency revisions were checked against
[`lean/lake-manifest.json`](lean/lake-manifest.json):

| Dependency | Git revision |
|---|---|
| mathlib | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |
| plausible | `d9598f07b1bc701f1e3aae163d2681c1fd978793` |
| LeanSearchClient | `ba67e212be1197b84c1f1f6299488a10a3002713` |
| importGraph | `d8823026ac7ef130c253089d95685f9877b95323` |
| proofwidgets | `a8acbfd87375ff4abe14ce09db5b7664d383bc7f` |
| aesop | `18889deb9e83ea7420ef51c160d6f88552e744e3` |
| Qq | `507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3` |
| batteries | `d54dddc581e08be364c278052863524bff7a99a9` |
| Cli | `ab3a82db9fea14cf0fd7f5a2de650f4b534640af` |

Do not run `lake update`.

## Reproduction

Install the pinned Lean toolchain with elan and Python 3.10 or later.
From a clone of this repository, reproduce the exact source revision:

```sh
git checkout 8e1d71634efa68b03b68b3963e419fcb98416d0d
test "$(git rev-parse HEAD:lean)" = "69d02281c91fea6ff54fe3556aaddc43eae66e65"
cd lean
lake exe cache get
export LEAN_NUM_THREADS=6
./verify
./verify --certificates
python3 -O verify
python3 -O verify --certificates
```

To check another revision, including v1.0, use the same tree comparison
before the remaining commands. The full certificate command builds
orders 3–20 one at a time; its prerequisites are documented in
[`lean/README.md`](lean/README.md).

The default audits covered **68 modules and 1,842 declarations** each;
the complete audits covered **88 modules and 8,465 declarations** each.
They include private and generated declarations. Both Python modes ran
the forbidden-source and untrusted-axiom rejection controls successfully.

| Check | Completion (UTC) | Exit status |
|---|---|---:|
| `./verify` | 2026-10-02T17:04:37Z | 0 |
| `./verify --certificates` | 2026-10-02T19:18:50Z | 0 |
| `python3 -O verify` | 2026-10-02T19:19:05Z | 0 |
| `python3 -O verify --certificates` | 2026-10-02T19:20:33Z | 0 |
| `lake env lean TargetAxioms.lean` | 2026-10-02T19:20:42Z | 0 |

Closing output of `./verify` (also obtained with `python3 -O verify`):

```text
PASS: axiom audit
PASS: source policy, complete module coverage, and negative controls
PASS: Lean verification (default library)
```

Closing output of `./verify --certificates` (also obtained with
`python3 -O verify --certificates`):

```text
PASS: axiom audit
PASS: source policy, complete module coverage, and negative controls
PASS: Lean verification including certificates through N=20
```

## Runtime and disk space

All recorded builds and audits used `LEAN_NUM_THREADS=6`. The default build
started with the pinned Mathlib cache available and no compiled project
modules. The certificate build followed it and built all 18 generated
certificates afresh. The optimized runs reused the completed builds.

| Command | Build state | Recorded wall time |
|---|---|---:|
| `./verify` | Fresh default project | 1,013.88 s (about 17 min) |
| `./verify --certificates` | Fresh certificates after default build | 8,052.40 s (about 2 h 14 min) |
| `python3 -O verify` | Compiled default project | 15.03 s |
| `python3 -O verify --certificates` | Compiled complete project | 88.17 s |
| Per-module `lake env leanchecker` loop below | Compiled complete project; sequential | 3,688.56 s (about 61 min) |

Reserve about **20 GiB of disk** for the pinned Lean toolchain, dependencies,
downloaded cache and project build files. This is a planning allowance,
not a measured peak; it excludes a TeX installation and Python environment.
The default build, certificate build and optional per-module replay share
these files, so the allowance is not additive. Replay reads the existing
compiled modules and does not require another copy of the build.
Cache download and toolchain installation time are excluded from the table;
wall times depend on the environment. The representative memory requirements
in the [Lean inventory](lean/README.md) are about 9–10 GiB for a fresh
default build and up to about 70 GiB for the full certificate build.

## Target-theorem axioms

After the full build, run this from `lean/`:

```sh
cat > TargetAxioms.lean <<'LEAN'
import ToeplitzSOSRelease
#print axioms ToeplitzSOS.Negative.not_MI15
#print axioms ToeplitzSOS.Negative.sharpNegativeResolution
#print axioms ToeplitzSOS.Negative.sharp_negative_explicit
#print axioms ToeplitzSOS.toeplitzBW_isSumSq_of_le_20
LEAN
lake env lean TargetAxioms.lean
rm TargetAxioms.lean
```

The output was:

```text
'ToeplitzSOS.Negative.not_MI15' depends on axioms: [propext, Classical.choice, Quot.sound]
'ToeplitzSOS.Negative.sharpNegativeResolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'ToeplitzSOS.Negative.sharp_negative_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ToeplitzSOS.toeplitzBW_isSumSq_of_le_20' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The accepted axioms are only Lean's standard foundational axioms
`propext`, `Classical.choice` and `Quot.sound`, or a subset.
No `sorryAx`, custom axiom or additional trust in native execution
supports these theorems.

## Per-module kernel replay

Every one of the 88 project modules was also checked in a separate
`leanchecker` invocation, replaying its declarations in the kernel with
its imported environment. This supplements the builds and transitive
axiom audit; it is not an external proof kernel.
This optional check took 3,688.56 seconds in total (about 61 minutes),
with `LEAN_NUM_THREADS=6` and one module per invocation. It reuses the
compiled files within the 20 GiB disk allowance above.
From `lean/`, after removing the temporary axiom file above:

```sh
export LEAN_NUM_THREADS=6
python3 - <<'PY'
import json
import subprocess
from pathlib import Path
for module in json.loads(Path('release-modules.json').read_text())['modules']:
    subprocess.run(['lake', 'env', 'leanchecker', module], check=True)
    print('PASS:', module, flush=True)
PY
```

The recorded invocations all exited successfully:

| Module | Completion (UTC) | Exit status |
|---|---|---:|
| `ToeplitzSOS.Defs` | 2026-10-02T19:20:49Z | 0 |
| `ToeplitzSOS.ThmA.Defs` | 2026-10-02T19:20:58Z | 0 |
| `ToeplitzSOS.Certificates.Basic` | 2026-10-02T19:21:07Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N3` | 2026-10-02T19:21:16Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N4` | 2026-10-02T19:21:25Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N5` | 2026-10-02T19:21:35Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N6` | 2026-10-02T19:21:46Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N7` | 2026-10-02T19:21:58Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N8` | 2026-10-02T19:22:27Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N9` | 2026-10-02T19:23:25Z | 0 |
| `ToeplitzSOS.ThmA.Reindex` | 2026-10-02T19:23:34Z | 0 |
| `ToeplitzSOS.ThmA.Commutator` | 2026-10-02T19:23:43Z | 0 |
| `ToeplitzSOS.ThmA.Mixed` | 2026-10-02T19:23:54Z | 0 |
| `ToeplitzSOS.ThmA.SameSide` | 2026-10-02T19:24:04Z | 0 |
| `ToeplitzSOS.ThmA.Poly` | 2026-10-02T19:24:14Z | 0 |
| `ToeplitzSOS.ThmA.Main` | 2026-10-02T19:24:23Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N10` | 2026-10-02T19:24:36Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N11` | 2026-10-02T19:24:53Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N12` | 2026-10-02T19:25:18Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N13` | 2026-10-02T19:25:54Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N14` | 2026-10-02T19:26:48Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N15` | 2026-10-02T19:28:10Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N16` | 2026-10-02T19:30:29Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N17` | 2026-10-02T19:33:51Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N18` | 2026-10-02T19:39:05Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N19` | 2026-10-02T19:46:37Z | 0 |
| `ToeplitzSOS.Certificates.Generated.N20` | 2026-10-02T19:57:36Z | 0 |
| `ToeplitzSOS.Certificates.Range` | 2026-10-02T19:57:49Z | 0 |
| `ToeplitzSOS.Negative.Analytic.Tails` | 2026-10-02T19:57:56Z | 0 |
| `ToeplitzSOS.Negative.Analytic.Nodes` | 2026-10-02T19:58:04Z | 0 |
| `ToeplitzSOS.Negative.TangentScalar` | 2026-10-02T19:58:11Z | 0 |
| `ToeplitzSOS.Negative.WitnessArithmetic` | 2026-10-02T19:58:20Z | 0 |
| `ToeplitzSOS.Negative.WitnessCertificate` | 2026-10-02T20:14:10Z | 0 |
| `ToeplitzSOS.Negative.Pairing` | 2026-10-02T20:14:19Z | 0 |
| `ToeplitzSOS.Negative.Kernels` | 2026-10-02T20:14:28Z | 0 |
| `ToeplitzSOS.Negative.Baseline` | 2026-10-02T20:14:37Z | 0 |
| `ToeplitzSOS.Negative.AnalyticInputs` | 2026-10-02T20:14:46Z | 0 |
| `ToeplitzSOS.Negative.Nodes` | 2026-10-02T20:14:55Z | 0 |
| `ToeplitzSOS.Negative.Witness` | 2026-10-02T20:15:04Z | 0 |
| `ToeplitzSOS.Negative.TangentReference` | 2026-10-02T20:15:13Z | 0 |
| `ToeplitzSOS.Negative.CornerGram` | 2026-10-02T20:15:22Z | 0 |
| `ToeplitzSOS.Negative.ExplicitStatement` | 2026-10-02T20:15:29Z | 0 |
| `ToeplitzSOS.Negative.Statement` | 2026-10-02T20:15:37Z | 0 |
| `ToeplitzSOS.Negative.SharpStatement` | 2026-10-02T20:15:44Z | 0 |
| `ToeplitzSOS.Negative.Constants` | 2026-10-02T20:15:52Z | 0 |
| `ToeplitzSOS.Negative.ContinuationApplication` | 2026-10-02T20:16:00Z | 0 |
| `ToeplitzSOS.Negative.FiniteObstruction` | 2026-10-02T20:16:09Z | 0 |
| `ToeplitzSOS.Negative.GramEvaluation` | 2026-10-02T20:16:18Z | 0 |
| `ToeplitzSOS.Negative.InitialBounds` | 2026-10-02T20:16:27Z | 0 |
| `ToeplitzSOS.Negative.Analytic.TailBudget` | 2026-10-02T20:16:35Z | 0 |
| `ToeplitzSOS.Negative.GlobalBound` | 2026-10-02T20:16:44Z | 0 |
| `ToeplitzSOS.Negative.SliceBound` | 2026-10-02T20:16:53Z | 0 |
| `ToeplitzSOS.Negative.TangentApplication` | 2026-10-02T20:17:02Z | 0 |
| `ToeplitzSOS.Negative.Analytic.Series` | 2026-10-02T20:17:11Z | 0 |
| `ToeplitzSOS.Negative.Analytic.Truncation` | 2026-10-02T20:17:20Z | 0 |
| `ToeplitzSOS.Negative.Analytic.BaselineBounds` | 2026-10-02T20:17:29Z | 0 |
| `ToeplitzSOS.Negative.Analytic.Comparison` | 2026-10-02T20:17:36Z | 0 |
| `ToeplitzSOS.Negative.Analytic.Barriers` | 2026-10-02T20:17:44Z | 0 |
| `ToeplitzSOS.Negative.Analytic.Continuation` | 2026-10-02T20:17:51Z | 0 |
| `ToeplitzSOS.Negative.Analytic.Means` | 2026-10-02T20:17:59Z | 0 |
| `ToeplitzSOS.Negative.Analytic.MixedTail` | 2026-10-02T20:18:06Z | 0 |
| `ToeplitzSOS.Negative.Analytic.Interface` | 2026-10-02T20:18:15Z | 0 |
| `ToeplitzSOS.Negative.CornerObstruction` | 2026-10-02T20:18:24Z | 0 |
| `ToeplitzSOS.SOS.LinearSubstitution` | 2026-10-02T20:18:31Z | 0 |
| `ToeplitzSOS.Negative.Restriction` | 2026-10-02T20:18:39Z | 0 |
| `ToeplitzSOS.Uniform.Corner` | 2026-10-02T20:18:48Z | 0 |
| `ToeplitzSOS.Kernel.Basic` | 2026-10-02T20:18:55Z | 0 |
| `ToeplitzSOS.Uniform.Bridge` | 2026-10-02T20:19:06Z | 0 |
| `ToeplitzSOS.Negative.CornerRestriction` | 2026-10-02T20:19:15Z | 0 |
| `ToeplitzSOS.Negative.CornerCoordinates` | 2026-10-02T20:19:24Z | 0 |
| `ToeplitzSOS.Negative.CornerExchange` | 2026-10-02T20:19:33Z | 0 |
| `ToeplitzSOS.General.Moment` | 2026-10-02T20:19:42Z | 0 |
| `ToeplitzSOS.Negative.Frame` | 2026-10-02T20:19:51Z | 0 |
| `ToeplitzSOS.Negative.CornerFrame` | 2026-10-02T20:20:00Z | 0 |
| `ToeplitzSOS.Negative.CornerForms` | 2026-10-02T20:20:09Z | 0 |
| `ToeplitzSOS.Negative.CornerBaselineForms` | 2026-10-02T20:20:18Z | 0 |
| `ToeplitzSOS.Negative.CornerEvaluation` | 2026-10-02T20:20:27Z | 0 |
| `ToeplitzSOS.Negative.CornerAveraging` | 2026-10-02T20:20:36Z | 0 |
| `ToeplitzSOS.Negative.CornerRepairs` | 2026-10-02T20:20:45Z | 0 |
| `ToeplitzSOS.Negative.CornerFactors` | 2026-10-02T20:20:54Z | 0 |
| `ToeplitzSOS.Negative.CornerLaplacian` | 2026-10-02T20:21:03Z | 0 |
| `ToeplitzSOS.Negative.LowMeans` | 2026-10-02T20:21:12Z | 0 |
| `ToeplitzSOS.Negative.CornerForcedMeans` | 2026-10-02T20:21:22Z | 0 |
| `ToeplitzSOS.Negative.CornerCorrection` | 2026-10-02T20:21:31Z | 0 |
| `ToeplitzSOS.Negative.CornerCoefficientBound` | 2026-10-02T20:21:40Z | 0 |
| `ToeplitzSOS.Negative.CornerExtraction` | 2026-10-02T20:21:49Z | 0 |
| `ToeplitzSOS.Negative.Resolution` | 2026-10-02T20:21:57Z | 0 |
| `ToeplitzSOSRelease` | 2026-10-02T20:22:10Z | 0 |

All checked Lean source hashes were unchanged at completion.
