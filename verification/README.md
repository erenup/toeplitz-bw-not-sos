# Exact computations

From the repository root, create an environment and install the two dependencies:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r verification/requirements.txt
```
NumPy stores bounded integer arrays and proposes floating Cholesky factors;
python-flint performs arbitrary-precision integer matrix operations. Floating
point never decides acceptance. The negative checker uses only the Python
standard library. Each checker runs its rejection controls on every invocation.

## Positive orders

Run from the repository root:

```sh
.venv/bin/python verification/positive.py
```

Expected last line:
`PASS: F_N is SOS for 2 <= N <= 50; 48 exact steps; negative controls rejected`.
The same command with `.venv/bin/python -O` must produce the same output.

Every step also prints an exact lower bound, for example:

```text
LOWER_BOUND: step 49, retained Gram >= 0.015624875921 I (exact decimal)
```

The noncentral wedges `(a,b)` are ordered lexicographically. For each mixed
gap `g = n+1,...,2n`, the checker deletes the first coordinate with `b-a=g`.
The printed bound applies to the retained principal matrix, before any
orthonormal change of coordinates, and is the minimum over all its connected
components. The central squares are checked separately. For steps 2–16 this
matrix represents `R_n`; for steps 17–49 it represents `I_n` as defined below.
It is not a strictly positive bound on the full Gram, which has forced zero
directions, or a bound on the optimal SOS margin. Twelve decimal places are
obtained by rounding an exact rational lower bound **down**; every printed
decimal is itself an exact rational certificate. The last few digits may
vary with the floating proposal, while acceptance always uses exact integers.

Put z_ab = x_a y_b − x_b y_a. Direct polynomial expansion first checks
F_2 = 4 z_(-1,0)^2 + 4 z_(0,1)^2. The remaining steps are:

| Steps n | Polynomial certified as SOS | Consequence |
|---|---|---|
| 2–16 | R_n = (n−1) F_(n+1) − (n+1) F_n | F_(n+1) = (R_n + (n+1) F_n)/(n−1). |
| 17–49 | I_n = F_(n+1) − F_n composed with L_q, where L_q scales x_a,y_a by q^abs(a) | F_(n+1) = I_n + F_n composed with L_q. |

The rational q is `1 - theta/n`, with `theta` supplied by each step.
At the last step q = 97/98. Positive scaling and linear substitution
preserve a finite SOS of homogeneous quadratic forms.

For each step the checker independently expands the literal matrix expression
for both adjacent orders. It builds a Gram in the noncentral wedges, adds
the central wedge squares, and compares all monomial coefficients. Every
Plücker correction is checked to give the zero polynomial; an additional
exact evaluation checks the assembled matrix against the literal expression.

The stored corrections encode sums of
2(z_ab z_cd − z_ac z_bd + z_ad z_bc) = 0 for a < b < c < d.
A `pure` tag adds the corresponding matrix and its distinct reflection.
A `storage` tag expands into the three reflection orbits specified explicitly
in `storage_plucker`; no external formula or precomputed acceptance flag is used.

Positivity is exact. The checker verifies the disjoint forced gap-kernel
vectors and deletes one coordinate from each. This gives a congruence to
zero plus the retained principal matrix. Its connected components are
positive definite either by exact fraction-free elimination with positive
leading minors and no pivoting, or by the following enclosure:

```text
2^(2s) A = D L L^T + E,
min_i (E_ii - sum_(j != i) abs(E_ij)) > 0,   D > 0.
```

Here A/D is a rational Gram component and L is an integer matrix proposed
by floating point. The displayed identity and strict diagonal dominance
are evaluated with arbitrary-precision integers, proving A/D positive definite.
Integer array computations have explicit bounds before accumulation.
Malformed input, a failed identity, or failed positivity causes a nonzero exit.

`data/manifest.json` lists exactly steps 2–49 and SHA-256 digests for both
the gzip payloads and their uncompressed JSON. The compressed data contain
only rational correction coefficients and their mathematical indices.
There are no stored floating proposals or precomputed success results.

Each default run also sends two altered copies of step 17 through the full
checker. Adding 1 to a Gram diagonal must fail coefficient equality. Adding
`10^9` to one pure Plücker numerator leaves the polynomial unchanged but must
fail positivity. The latter magnitude deliberately overwhelms the positive
block; it is a test input, not a mathematical bound. Small indefinite and
singular matrices, a changed `F_2` coefficient, and a corrupted payload hash
exercise the other rejection gates. `--self-test` runs these controls alone.

The implementation uses `2^40` bounds on small stored integers and a `2^60`
bound before signed-64-bit accumulation; these are overflow guards, not
positivity assumptions. The factor proposal tries 36, 44, and 52 binary
fractional bits and dyadic diagonal shifts down to exponent −79, rejecting
proposals too large for signed integers (`2^62`). These search parameters
only affect whether a certificate is found. A fixed random seed and integer
samples in `[-5,5]` or `[-4,4]` make an additional evaluation reproducible;
the full monomial identity, rather than that sample, proves equality.

## Negative tangent witness and constants

Run from the repository root:

```sh
python3 verification/negative.py
```

Expected last line: `PASS: exact tangent witness and constants`.
The same command with `python3 -O` must produce the same output.

For r,t in {1,2}, j,k in {1,...,256}, and signs sigma,tau in {−1,1}, set

```text
A = (r+t)^2 + (sigma*j - tau*k)^2,    C = 4*r*t,
S_F = 2 (2/A^2 + 1/C^2 - 1/(A*C)),
z_j = floor(2^43*j / (128^2 + j^2)^2),    c_(r,j,sigma) = sigma*z_j.
```

The checker regenerates every coefficient and encloses the sum of all
1024² rational Hermitian-pairing terms by integer division at denominator
2^64. Each rounding interval has width 1/2^64, including for negative
terms. The resulting upper endpoint is strictly below −2^42, and the
coefficient l1 norm is exactly 859652168 < 2^30. A separately grouped
sine pairing provides a normalization check. Removing the negative kernel
term produces a strictly positive lower bound and is rejected as a witness.

The arithmetic checks specialize the analytic estimates at
K = 38·2^17 + 1 = 4980737, epsilon = 2^(-K), m = epsilon^(-2).
They give m = 2^9961474 and ambient threshold 2m = 2^9961475.
The integer comparison

```text
262143^131072 > 2^(18·131072 − 1)
```

certifies 2^(-1/131072) < 262143/262144. Thus the budget
−2^42 + 2^(90−K) + 2^(42−1/131072) is below −2^24 + 1 < 0.
A corrupted root bound is rejected. The code checks arithmetic implications
of the analytic estimates; the estimates themselves are part of the paper.

Here 128 is the width of the chosen rational frequency profile, 256 is its
frequency cutoff, and `2^43` converts that profile to integer coefficients.
The two radial values and two signs give `2·256·2 = 1024` points. `2^64` is
the denominator for directed entrywise rounding. The computed mass
859652168 gives the convenient coarse square bound `2^60` and the sharper
bound `3·2^58` used by Lean. The witness threshold is `−2^42`.

The rectangle allowances are `eta1 = 2^-13`, `eta2 = 2^-5`, whose product
`2 eta1 eta2 = 2^-17` is the interpolation exponent. The paper's global
entrywise constant `2^20` and mass square `2^60` give the slow pairing
constant `2^80`; the baseline constant `2^30` gives `2^90`. Solving
`80 − k/2^17 < 42` gives `k = (80−42)·2^17+1`. The integer root enclosure
uses `2·2^17 = 2^18`, hence its deficit is `2^42/2^18 = 2^24`.
The tail base case is `2^(16−2) >= 8·16+40`; the induction step is the
algebraic inequality `2(8k+40) − (8(k+1)+40) = 8k+32 > 0` for `k >= 16`.
These arithmetic checks accompany the estimates proved in the paper.

Lean uses the sharper mass bound: the pure error is at most
`3·2^58·2^-18 = 3·2^40`, strictly below `2^42`. The script checks that this
leaves room for a baseline error below 1. Thus the formal application at the
selected scale does not need the root-enclosure/convexity step.

## Manuscript witness cross-check

```sh
python3 verification/witness.py
python3 -O verification/witness.py
```

Expected last line:
`PASS: manuscript witness, convolution, threshold, and five rejection controls`.
This standard-library program reads the threshold macro in `paper/main.tex`.
It independently compares all 1024² rational entries with a 513-term exact
convolution, checks the coefficient and normalized-defect budgets, and rejects
five altered inputs on every run. This also checks that the paper and the
standalone negative checker use the same threshold.

The two programs intentionally use separate implementations. `negative.py`
checks the analytic constants and compares the full pairing with a grouped
sine pairing. `witness.py` checks the manuscript's published integers and
threshold macro against an independently assembled exact convolution. The
convolution has 513 slots because frequency sums run from 0 through 512.
Its normalized defect interval `(2^-18, 2^-16)` is a coarse enclosure of
`−pairing/||c||_1^2`, not an asserted optimum. Running both checks arithmetic
consistency across the paper and witness representations; neither replaces
the analytic proof.

## Runtime and memory

Representative measurements for these sources, with one numeric-library
thread and warm filesystem cache; the environment and floating proposals affect
the times. Normal and optimized Python have comparable costs.

| Command (from the repository root) | Wall time | Peak resident memory |
|---|---:|---:|
| `.venv/bin/python verification/positive.py` | about 95 s | about 1.8 GiB |
| `.venv/bin/python -O verification/positive.py` | about 95 s | about 1.8 GiB |
| `.venv/bin/python verification/positive.py --self-test` | under 1 s | under 0.1 GiB |
| `python3 verification/negative.py` (also `-O`) | about 1 s | under 25 MiB |
| `python3 verification/witness.py` (also `-O`) | about 1 s | under 25 MiB |

Environment creation and dependency installation depend on network and
package-cache availability. For the paper, mapping and Lean commands, see
their directory READMEs; the large Lean certificates require substantially
more memory than any Python command here.
