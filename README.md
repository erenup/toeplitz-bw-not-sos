# The Toeplitz Böttcher–Wenzel form is not always a sum of squares

Authors: Wenqi Zhu; Ping Nie.

For real Toeplitz matrices of order N ≥ 2^9961475, the quartic F_N = 2‖X‖_F²‖Y‖_F² − 2⟨X,Y⟩_F² − ‖XY−YX‖_F² is not a finite sum of squares of real homogeneous quadratic forms, allowing arbitrary real coefficients. It is SOS for 2 ≤ N ≤ 50 (and identically zero at N = 1); the gap 51 ≤ N < 2^9961475 remains open.

Here X_ij = x_(i−j) and Y_ij = y_(i−j); F_N has 4N−2 real variables.
The strengthened Böttcher–Wenzel inequality gives F_N ≥ 0 for every input
at every order. The negative result concerns SOS representation.

Read this first: the [guide linking the paper, Lean, and exact checks](paper-lean-mapping/README.md),
then the [manuscript's introduction](paper/main.pdf). To read the formal proof,
follow [Defs](lean/ToeplitzSOS/Defs.lean) →
[SharpStatement](lean/ToeplitzSOS/Negative/SharpStatement.lean) →
[Resolution](lean/ToeplitzSOS/Negative/Resolution.lean).

The negative theorem has a finite analytic proof. This distribution includes
its exact tangent-kernel witness and arithmetic constants; these computations
check inputs to the analytic argument. They do not check the analytic proof
or construct an ambient separating matrix at the displayed order.
Read the [manuscript](paper/main.pdf) for the complete analytic argument.

Lean proves the negative theorem at the displayed threshold for the original
polynomial and arbitrary finite sums of real homogeneous quadratic squares.
Its proof includes the literal corner extraction, analytic estimates, and the
exact 1024-point witness. Lean also checks SOS certificates for 2 ≤ N ≤ 20. Python checks the
complete positive certificate chain through N = 50. See the detailed
[Lean inventory](lean/README.md) and [verification description](verification/README.md).

To run every supplied check, install Python 3.10 or later and
[elan](https://github.com/leanprover/elan), Graphviz (`dot`), and the TeX dependencies listed in [paper/](paper/README.md), then run from this directory:

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
cd lean
lake exe cache get
lake build
./verify --certificates
```

`./verify --certificates` builds the order-3–20 certificates and needs about
70 GB of memory. `./verify` checks the default library (the negative theorem and
common certificate definitions) and needs about 10 GB.

The toolchain and all Lean dependencies are pinned. `lake exe cache get`
fetches the dependencies and their normal compiled cache. The default
`lake build` builds the mathematical library; `./verify --certificates`
also builds the large fixed-order certificates in sequence and checks every
project declaration's transitive axioms. Only `propext`, `Classical.choice`,
and `Quot.sound` are accepted. The Python checks use explicit rejection gates
and include corrupted-input controls, including under `python -O`.

Expected last line of each verification/build command (normal and optimized
Python report the same result):

```text
PASS: F_N is SOS for 2 <= N <= 50; 48 exact steps; negative controls rejected
PASS: exact tangent witness and constants
PASS: manuscript witness, convolution, threshold, and five rejection controls
PASS: paper built (.build/main.pdf)
PASS: mapping, DAG, declarations, scripts, and rejection controls (paper labels covered)
PASS: Lean verification including certificates through N=20
```

The manuscript build writes the ignored `paper/.build/main.pdf`. Use
`bash paper/build.sh --update-pdf` to replace the tracked `paper/main.pdf`.
Per-command runtime and memory costs are listed in the directory READMEs.

Layout:

- `paper-lean-mapping/`: beginner guide, result map, and generated dependency diagrams.
- `lean/`: pinned Lean project, proofs, generated certificates, and `verify`.
- `verification/`: exact Python checkers and compressed positive certificates.
- `paper/`: manuscript sources, PDF, and portable build script.

The license is to be decided by the owner; no license is granted by this repository.
