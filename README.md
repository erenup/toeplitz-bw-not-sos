# Sum-of-Squares and Non-Sum-of-Squares Regimes for the Toeplitz Böttcher–Wenzel Form

Authors: Wenqi Zhu; Ping Nie.

Wenqi Zhu — Mathematical Institute, Woodstock Road, University of Oxford,
Oxford, UK, OX2 6GG — wenqi.zhu@maths.ox.ac.uk

Ping Nie — David R. Cheriton School of Computer Science, University of Waterloo
— ping.nie@uwaterloo.ca

The paper is a **working version dated 2 October 2026** and is being finalized
by the authors. The final version will be posted on arXiv and will replace
`paper/`. The theorem and equation numbers in `paper-lean-mapping/` refer
to this working version.

For real Toeplitz matrices of order N ≥ 2^9961475, the quartic F_N = 2‖X‖_F²‖Y‖_F² − 2⟨X,Y⟩_F² − ‖XY−YX‖_F² is not a finite sum of squares of real homogeneous quadratic forms, allowing arbitrary real coefficients. It is SOS for 2 ≤ N ≤ 50 (and identically zero at N = 1); the gap 51 ≤ N < 2^9961475 remains open.

Here X_ij = x_(i−j) and Y_ij = y_(i−j); F_N has 4N−2 real variables.
The strengthened Böttcher–Wenzel inequality gives F_N ≥ 0 for every input
at every order. The negative result concerns SOS representation.

## Evidence status

- **Formally proved in Lean 4 with Mathlib:** F_N is not SOS for every
  N ≥ 2^9961475, for the original matrix polynomial and arbitrary finite
  sums of real homogeneous quadratic squares. The formal proof contains the
  corner extraction, all analytic estimates, and the exact 1024-point
  witness; it uses only the axioms `propext`, `Classical.choice`, and
  `Quot.sound`. Lean also proves that F_N is SOS for 2 ≤ N ≤ 20.
- **Exact computation:** F_N is SOS for 2 ≤ N ≤ 50, by a chain of 48
  exact rational Gram identities checked in Python with integer and
  rational arithmetic. The negative tangent witness and the paper's
  constants are also rechecked exactly in Python.
- **Proved in the paper only:** the uniform finite-scale estimate for every
  scale k ≥ 16 (Lean proves its ingredients and the one scale,
  k = 4980737, that the negative theorem needs), the full written forms of
  several structural lemmas, the exchange criterion and criticality bound,
  the boundary-layer corollary, and the classical nonnegativity F_N ≥ 0.
  The [result map](paper-lean-mapping/by-section.md) states the exact
  formal scope of each numbered result.
- **Open:** every order 51 ≤ N < 2^9961475, and the location of the first
  non-SOS order. The manuscript's expectation for this range is an
  unproved remark.

## Where to read

Start with the [guide linking the paper, Lean, and exact checks](paper-lean-mapping/README.md),
then the [manuscript's introduction](paper/main.pdf). To read the formal proof,
follow [Defs](lean/ToeplitzSOS/Defs.lean) →
[SharpStatement](lean/ToeplitzSOS/Negative/SharpStatement.lean) →
[Resolution](lean/ToeplitzSOS/Negative/Resolution.lean).

Lean proves the negative theorem at the displayed threshold for the original
polynomial and arbitrary finite sums of real homogeneous quadratic squares.
Its proof includes the literal corner extraction, analytic estimates, and the
exact 1024-point witness. Lean also checks SOS certificates for 2 ≤ N ≤ 20.
Python checks the complete positive certificate chain through N = 50. See
the detailed [Lean inventory](lean/README.md) and
[verification description](verification/README.md).

The negative theorem also has a finite analytic proof, written out in the
[manuscript](paper/main.pdf). The Python programs recheck its exact
tangent-kernel witness and arithmetic constants; these computations check
inputs to the analytic argument. They do not check the analytic proof
itself, which is the part that Lean verifies, or construct an ambient
separating matrix at the displayed order.

## Reproduce the checks

The dated [verification record](VERIFICATION.md) lists the verified commit,
the exact `lean/` tree, the reproduction commands and the target-theorem
axiom reports.

Install [elan](https://github.com/leanprover/elan), Python 3.10 or later,
Graphviz (`dot`), and the TeX dependencies listed in [paper/](paper/README.md).

**Formal proof (recommended first check).** From this directory:

```sh
cd lean
lake exe cache get   # fetch the pinned Mathlib build cache
./verify             # build and audit the default library
```

`./verify` runs `lake build` itself, then checks every imported project
declaration's transitive axioms; only `propext`, `Classical.choice`, and
`Quot.sound` are accepted. The default library contains the negative theorem
and the common certificate definitions. With the Mathlib cache in place, a
fresh build takes about 14 minutes and about 9–10 GiB of peak resident
memory; with compiled files it takes seconds. Expected last line:

```text
PASS: Lean verification (default library)
```

**Optional: the positive certificates in Lean.** `./verify --certificates`
additionally builds the order-3–20 certificates one at a time and audits the
complete release. A fresh build takes about 2–3 hours and up to about
70 GiB of peak resident memory; allow at least 80 GiB of memory headroom.
Expected last line:

```text
PASS: Lean verification including certificates through N=20
```

`./verify` runs Lean with `LEAN_NUM_THREADS=2` unless that variable is
already set; `lean/build-release.sh` defaults to 6. The memory and time
figures are those of the [Lean inventory](lean/README.md); times depend on
the environment.

**Exact computations, manuscript, and result map.** From this directory:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r verification/requirements.txt
.venv/bin/python verification/positive.py
.venv/bin/python -O verification/positive.py
python3 verification/negative.py
python3 -O verification/negative.py
python3 verification/witness.py
python3 -O verification/witness.py
bash paper/build.sh
python3 paper-lean-mapping/build_and_check.py
python3 -O paper-lean-mapping/build_and_check.py
```

The Python checks use explicit rejection gates and include corrupted-input
controls, including under `python -O`. Expected last line of each command
(normal and optimized Python report the same result):

```text
PASS: F_N is SOS for 2 <= N <= 50; 48 exact steps; negative controls rejected
PASS: exact tangent witness and constants
PASS: manuscript witness, convolution, threshold, and five rejection controls
PASS: paper built (.build/main.pdf)
PASS: mapping, DAG, declarations, scripts, and rejection controls (paper labels covered)
```

The toolchain and all Lean dependencies are pinned; do not run `lake update`.
The manuscript build writes the ignored `paper/.build/main.pdf`. Use
`bash paper/build.sh --update-pdf` to replace the tracked `paper/main.pdf`.
Per-command runtime and memory costs are listed in the directory READMEs.

## Layout

- `paper-lean-mapping/`: beginner guide, result map, and generated dependency diagrams.
- `lean/`: pinned Lean project, proofs, generated certificates, and `verify`.
- `verification/`: exact Python checkers and compressed positive certificates.
- `paper/`: manuscript sources, PDF, and portable build script.

## License

Everything outside `paper/` is available under the [MIT license](LICENSE).
The paper sources and PDF in `paper/` are not licensed; all rights reserved.
