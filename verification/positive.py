"""Exact finite SOS certificate chain. See README.md for the proof of the checks."""

import argparse
import gzip
import os
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import sys
from time import perf_counter

for _name in (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
):
    os.environ.setdefault(_name, "2")
import numpy as np
from flint import fmpz_mat


class Mono:
    def __init__(self, M):
        self.M = M
        self.K = 2 * M + 1

    def idx(self, p1, p2, r1, r2):
        p1 = np.asarray(p1, dtype=np.int64)
        p2 = np.asarray(p2, dtype=np.int64)
        r1 = np.asarray(r1, dtype=np.int64)
        r2 = np.asarray(r2, dtype=np.int64)
        K, M = (self.K, self.M)
        a = np.minimum(p1, p2) + M
        b = np.maximum(p1, p2) + M
        c = np.minimum(r1, r2) + M
        d = np.maximum(r1, r2) + M
        require(a.min(initial=0) >= 0 and d.max(initial=0) < K, "certificate condition")
        return ((a * K + b) * K + c) * K + d


def literal_F(N, mono, scale=1):
    """Expand the literal matrix quartic as integer monomial contributions."""
    idx, w = ([], [])
    count = defaultdict(int)
    for i in range(N):
        for j in range(N):
            count[i - j] += 1
    labs = np.array(sorted(count), dtype=np.int64)
    wt = np.array([count[a] for a in labs], dtype=np.int64)
    P, R = np.meshgrid(labs, labs, indexing="ij")
    WW = np.outer(wt, wt)
    idx.append(mono.idx(P, P, R, R).ravel())
    w.append((2 * scale * WW).ravel())
    idx.append(mono.idx(P, R, P, R).ravel())
    w.append((-2 * scale * WW).ravel())
    for i in range(N):
        for j in range(N):
            form = defaultdict(int)
            for k in range(N):
                form[i - k, k - j] += 1
                form[k - j, i - k] -= 1
            items = [(p, r, c) for (p, r), c in form.items() if c]
            if not items:
                continue
            p = np.array([t[0] for t in items], dtype=np.int64)
            r = np.array([t[1] for t in items], dtype=np.int64)
            c = np.array([t[2] for t in items], dtype=np.int64)
            idx.append(mono.idx(p[:, None], p[None, :], r[:, None], r[None, :]).ravel())
            w.append((-scale * np.outer(c, c)).ravel())
    return (idx, w)


def gram_poly(rows, cols, vals, WA, WB, mono):
    a, b, c, d = (WA[rows], WB[rows], WA[cols], WB[cols])
    vals = np.asarray(vals, dtype=np.int64)
    return (
        [
            mono.idx(a, c, b, d),
            mono.idx(a, d, b, c),
            mono.idx(b, c, a, d),
            mono.idx(b, d, a, c),
        ],
        [vals, -vals, -vals, vals],
    )


def dense_poly(M, WA, WB, mono, scale=1):
    r, c = np.nonzero(M)
    return gram_poly(r, c, scale * M[r, c], WA, WB, mono)


def central_poly(N, labels_all, mono, scale=1):
    WA, WB, vals = ([], [], [])
    for a in labels_all:
        if a == 0 or abs(a) >= N:
            continue
        lo, hi = (min(a, 0), max(a, 0))
        WA.append(lo)
        WB.append(hi)
        vals.append(scale * 2 * N * (N - abs(a)))
    WA = np.array(WA, dtype=np.int64)
    WB = np.array(WB, dtype=np.int64)
    ids = np.arange(len(WA))
    return gram_poly(ids, ids, np.array(vals, dtype=np.int64), WA, WB, mono)


def is_zero(parts):
    idx = np.concatenate([i for p in parts for i in p[0]])
    w = np.concatenate([x for p in parts for x in p[1]]).astype(np.int64)
    total = len(w) * max(abs(int(w.min(initial=0))), abs(int(w.max(initial=0))))
    # Four guard bits below the signed 64-bit range bound every partial sum.
    require(total < 2**60, "int64 accumulation guard")
    order = np.argsort(idx, kind="stable")
    idx = idx[order]
    w = w[order]
    starts = np.flatnonzero(np.r_[True, idx[1:] != idx[:-1]])
    sums = np.add.reduceat(w, starts)
    bad = int(np.count_nonzero(sums))
    return (bad == 0, bad, len(starts))


def setup(n):
    labels = [a for a in range(-n, n + 1) if a]
    wedges = [
        (labels[i], labels[j])
        for i in range(len(labels))
        for j in range(i + 1, len(labels))
    ]
    loc = {w: k for k, w in enumerate(wedges)}
    WA = np.array([w[0] for w in wedges], dtype=np.int64)
    WB = np.array([w[1] for w in wedges], dtype=np.int64)
    return (labels, wedges, loc, WA, WB)


def classical_gram(N, wedges, loc):
    """Lagrange diagonal minus the commutator Gram on noncentral wedges."""
    m = len(wedges)
    G = np.zeros((m, m), dtype=np.int64)
    for k, (a, b) in enumerate(wedges):
        G[k, k] = 2 * max(0, N - abs(a)) * max(0, N - abs(b))
    for i in range(N):
        for j in range(N):
            vec = defaultdict(int)
            for k in range(N):
                a, b = (i - k, k - j)
                if a == 0 or b == 0 or a == b:
                    continue
                if a < b:
                    vec[loc[a, b]] += 1
                else:
                    vec[loc[b, a]] -= 1
            ids = [key for key, value in vec.items() if value]
            values = np.array([vec[key] for key in ids], dtype=np.int64)
            G[np.ix_(ids, ids)] -= np.outer(values, values)
    return G


def plucker_add(M, quad, value, loc):
    """Add the zero polynomial 2 value (z_ab z_cd - z_ac z_bd + z_ad z_bc)."""
    a, b, c, d = quad
    require(a < b < c < d, "certificate condition")
    for p, r, s in (((a, b), (c, d), 1), ((a, c), (b, d), -1), ((a, d), (b, c), 1)):
        i, j = (loc[p], loc[r])
        M[i, j] += s * value
        M[j, i] += s * value


def reflect(quad):
    return tuple((-v for v in quad[::-1]))


def orbit_add(M, key, value, loc):
    key = tuple(key)
    for quad in sorted({key, reflect(key)}):
        plucker_add(M, quad, value, loc)


def exchange(G, wedges, loc):
    """Exchange nested mixed pairs using exact Pluecker relations."""
    H = G.copy()
    r, c = np.nonzero(np.triu(G, 1))
    for i, j in zip(r.tolist(), c.tolist()):
        (a1, b1), (a2, b2) = (wedges[i], wedges[j])
        if a1 < a2 < b2 < b1:
            quad = (a1, a2, b2, b1)
        elif a2 < a1 < b1 < b2:
            quad = (a2, a1, b1, b2)
        else:
            continue
        plucker_add(H, quad, -int(G[i, j]), loc)
    return H


def storage_plucker(n, tags, nums, loc, m):
    """Construct the integer Pluecker correction encoded by storage and pure tags."""
    P = np.zeros((m, m), dtype=np.int64)

    def key(a, b, delta, other=None):
        other = delta if other is None else other
        q = (-a - delta, -a, b, b + other)
        return min(q, reflect(q))

    for tag, num in zip(tags, nums):
        require(abs(num) < 2**40, "numerator bound")
        if not num:
            continue
        if tag[0] == "storage":
            _, delta, p, r = tag
            require(
                1 <= delta and 1 <= p <= r <= n - delta - 2, "certificate condition"
            )
            terms = defaultdict(int)
            for a, b in [(p + 1, r)] if p == r else [(p + 1, r), (r + 1, p)]:
                terms[key(a, b, delta, delta + 2)] += 1
                terms[key(a, b, delta + 1)] += -2 if a == b else -1
                terms[key(a + delta, b, 1)] += 2 if a + delta == b else 1
            for k, v in terms.items():
                if v:
                    orbit_add(P, k, v * num, loc)
        elif tag[0] == "pure":
            q = tuple(tag[1:])
            require(
                all((v < 0 for v in q)) and sum(q) % 2 == 0, "certificate condition"
            )
            orbit_add(P, q, num, loc)
        else:
            raise AssertionError(("unknown tag", tag))
    return P


def sylvester_pd(block):
    """Positive leading minors via exact fraction-free elimination, without pivoting."""
    require(all((len(row) == len(block) for row in block)), "square matrix")
    require(
        all((block[i][j] == block[j][i] for i in range(len(block)) for j in range(i))),
        "symmetric matrix",
    )
    if len(block) == 0:
        return True
    P, L, D, U = fmpz_mat(block).fflu()
    size = len(block)
    ident = all(
        (int(P[i, j]) == (1 if i == j else 0) for i in range(size) for j in range(size))
    )
    if not ident:
        return False
    return all((int(U[i, i]) > 0 for i in range(size)))


def residual_pd(block, D):
    """A float factor only proposes L. Exact integer residual dominance proves A/D > 0."""
    size = len(block)
    require(D > 0, "positive denominator")
    require(all((len(row) == size for row in block)), "square matrix")
    require(
        all((block[i][j] == block[j][i] for i in range(size) for j in range(i))),
        "symmetric matrix",
    )
    if size == 0:
        return Fraction(1)
    Af = np.array([[int(v) / D for v in row] for row in block], dtype=float)
    ev = np.linalg.eigvalsh(Af)[0]
    Afm = fmpz_mat(block)
    # These are proposal parameters, never tolerances for acceptance:
    # try a dyadic shift below the floating eigenvalue, decreasing by 4,
    # down to exponent -79. The tiny floor only makes log2 defined.
    for sig_exp in range(int(np.floor(np.log2(max(ev, 1e-300)))) - 1, -80, -2):
        sigma = 2.0**sig_exp
        try:
            Lf = np.linalg.cholesky(Af - sigma * np.eye(size))
        except np.linalg.LinAlgError:
            continue
        # Increasing binary factor precision; the 2^62 guard leaves room
        # when converting the rounded proposal to signed 64-bit integers.
        for s in (36, 44, 52):
            Li = np.rint(Lf * 2.0**s)
            if not np.all(np.isfinite(Li)) or np.max(np.abs(Li)) >= 2.0**62:
                continue
            Lm = fmpz_mat(Li.astype(np.int64).tolist())
            M = Afm * (1 << 2 * s) - Lm * Lm.transpose() * D
            ent = [int(v) for v in M.entries()]
            g = None
            for i in range(size):
                rowv = ent[i * size : (i + 1) * size]
                slack = rowv[i] - (sum((abs(v) for v in rowv)) - abs(rowv[i]))
                g = slack if g is None else min(g, slack)
            if g > 0:
                return Fraction(g, D << 2 * s)
    return None


def prove_psd(get_block, comps, kernel_ok, method, D):
    out = []
    for comp in comps:
        block = get_block(comp)
        if method == "sylvester":
            ok = sylvester_pd(block)
            out.append((len(comp), "sylvester", bool(ok)))
            if not ok:
                return (out, False)
        else:
            lb = residual_pd(block, D)
            out.append((len(comp), "residual", None if lb is None else lb))
            if lb is None:
                return (out, False)
    return (out, kernel_ok)


def components(pattern, keep):
    """Connected components of the exact nonzero pattern restricted to retained coordinates."""
    unseen = set(keep)
    result = []
    while unseen:
        start = min(unseen)
        unseen.remove(start)
        component = [start]
        todo = [start]
        while todo:
            i = todo.pop()
            for j in np.flatnonzero(pattern[i]):
                j = int(j)
                if j in unseen:
                    unseen.remove(j)
                    component.append(j)
                    todo.append(j)
        result.append(sorted(component))
    return result


def forced_kernel(n, wedges):
    """Disjoint mixed gap indicators; deleting one coordinate per indicator gives a congruence."""
    vecs, piv = ([], [])
    for g in range(n + 1, 2 * n + 1):
        ids = [k for k, (a, b) in enumerate(wedges) if a < 0 < b and b - a == g]
        vecs.append(ids)
        piv.append(ids[0])
    return (vecs, piv)


def literal_value(N, x, y):
    X = [[x.get(i - j, 0) for j in range(N)] for i in range(N)]
    Y = [[y.get(i - j, 0) for j in range(N)] for i in range(N)]
    nx = sum((v * v for r in X for v in r))
    ny = sum((v * v for r in Y for v in r))
    ip = sum((X[i][j] * Y[i][j] for i in range(N) for j in range(N)))
    C = 0
    for i in range(N):
        for j in range(N):
            c = sum((X[i][k] * Y[k][j] - Y[i][k] * X[k][j] for k in range(N)))
            C += c * c
    return 2 * nx * ny - 2 * ip * ip - C


def check_normalized(path, method="residual", rng=None):
    """Certify (n-1) F_(n+1) - (n+1) F_n as a positive rational wedge Gram."""
    tic = perf_counter()
    data = load_certificate(path)
    n = data["n"]
    require(
        type(n) is int and data["kind"] == "normalized" and (2 <= n <= 16),
        "certificate condition",
    )
    den = int(data["denominator"])
    require(0 < den < 2**40, "certificate condition")
    require(len(data["keys"]) == len(data["numerators"]), "certificate condition")
    labels, wedges, loc, WA, WB = setup(n)
    m = len(wedges)
    mono = Mono(n)
    Gn1 = classical_gram(n + 1, wedges, loc)
    Gn = classical_gram(n, wedges, loc)
    P = np.zeros((m, m), dtype=np.int64)
    for key, num in zip(data["keys"], data["numerators"]):
        num = int(num)
        require(abs(num) < 2**40, "numerator bound")
        if num:
            key = tuple(key)
            require(
                sum(key) % 2 == 0 and key == min(key, reflect(key)),
                "certificate condition",
            )
            orbit_add(P, key, num, loc)
    all_labels = list(range(-n, n + 1))
    id1 = is_zero(
        [
            dense_poly(Gn1, WA, WB, mono),
            central_poly(n + 1, all_labels, mono),
            literal_F(n + 1, mono, -1),
        ]
    )
    id2 = is_zero(
        [
            dense_poly(Gn, WA, WB, mono),
            central_poly(n, all_labels, mono),
            literal_F(n, mono, -1),
        ]
    )
    id3 = is_zero([dense_poly(P, WA, WB, mono)])
    identity = id1[0] and id2[0] and id3[0]
    require(
        den * 4 * (n + 1) ** 4 + int(np.abs(P).max()) < 2**60, "integer matrix bound"
    )
    Q = den * ((n - 1) * Gn1 - (n + 1) * Gn) + P
    require(np.array_equal(Q, Q.T), "certificate condition")
    central = [
        (n - 1) * 2 * (n + 1) * (n + 1 - a) - (n + 1) * 2 * n * (n - a)
        for a in range(1, n + 1)
    ]
    central_ok = all((c >= 0 for c in central))
    kv, piv = forced_kernel(n, wedges)
    kernel_ok = all((not np.any(Q[:, ids].sum(axis=1)) for ids in kv))
    keep = [k for k in range(m) if k not in set(piv)]
    comps = components(Q != 0, keep)
    blocks, psd_ok = prove_psd(
        lambda comp: Q[np.ix_(comp, comp)].tolist(), comps, kernel_ok, method, den
    )
    # Fixed seed and small integer samples make this extra evaluation
    # reproducible; full coefficient equality is checked independently above.
    rng = rng or random.Random(53)
    x = {a: rng.randint(-5, 5) for a in range(-n, n + 1)}
    y = {a: rng.randint(-5, 5) for a in range(-n, n + 1)}
    z = np.array([x[a] * y[b] - x[b] * y[a] for a, b in wedges], dtype=object)
    lhs = Fraction(int(z @ (Q.astype(object) @ z)), den) + sum(
        (
            c * (x[0] * y[a] - x[a] * y[0]) ** 2
            + c * (x[-a] * y[0] - x[0] * y[-a]) ** 2
            for a, c in zip(range(1, n + 1), central)
        )
    )
    rhs = (n - 1) * literal_value(n + 1, x, y) - (n + 1) * literal_value(n, x, y)
    spot = lhs == rhs
    ok = identity and central_ok and kernel_ok and psd_ok and spot
    lbs = [v for _, meth, v in blocks if meth == "residual" and v is not None]
    return {
        "file": Path(path).name,
        "sha256": hashlib.sha256(Path(path).read_bytes()).hexdigest(),
        "increment": f"R_{n}=(n-1)F_{n + 1}-(n+1)F_{n}",
        "n": n,
        "denominator": den,
        "identity_F_new": id1[:2],
        "identity_F_old": id2[:2],
        "plucker_zero": id3[:2],
        "kernel_annihilated": kernel_ok,
        "central_nonnegative": central_ok,
        "components": [(s, meth, str(v)) for s, meth, v in blocks],
        "min_certified_lower_bound": str(min(lbs)) if lbs else None,
        "psd": psd_ok,
        "spot_check": spot,
        "accepted": ok,
        "seconds": round(perf_counter() - tic, 2),
    }


def geometric_q(data):
    n = data["n"]
    theta = Fraction(data["theta"])
    return 1 - theta / n


def check_geometric(path, rng=None, tamper=None, spot=True):
    """Certify F_(n+1) - F_n composed with x_a,y_a -> q^|a| x_a,q^|a| y_a."""
    tic = perf_counter()
    data = load_certificate(path)
    n = data["n"]
    require(type(n) is int and 17 <= n <= 49, "certificate condition")
    q = geometric_q(data)
    require(0 < q <= 1, "certificate condition")
    den = int(data["storage_denominator"])
    require(den > 0, "certificate condition")
    tags = [tuple(t) for t in data["tags"]]
    nums = [int(v) for v in data["storage_numerators"]]
    require(len(tags) == len(nums), "certificate condition")
    if tamper == "pure_huge":
        j = next((i for i, t in enumerate(tags) if t[0] == "pure"))
        nums[j] += 10**9
    labels, wedges, loc, WA, WB = setup(n)
    m = len(wedges)
    mono = Mono(n)
    all_labels = list(range(-n, n + 1))
    Hn = exchange(classical_gram(n + 1, wedges, loc), wedges, loc)
    Ho = exchange(classical_gram(n, wedges, loc), wedges, loc)
    if tamper == "diag":
        Hn[0, 0] += 1
    P = storage_plucker(n, tags, nums, loc, m)
    t1 = perf_counter()
    id1 = is_zero(
        [
            dense_poly(Hn, WA, WB, mono),
            central_poly(n + 1, all_labels, mono),
            literal_F(n + 1, mono, -1),
        ]
    )
    id2 = is_zero(
        [
            dense_poly(Ho, WA, WB, mono),
            central_poly(n, all_labels, mono),
            literal_F(n, mono, -1),
        ]
    )
    id3 = is_zero([dense_poly(P, WA, WB, mono)])
    identity = id1[0] and id2[0] and id3[0]
    t_id = perf_counter() - t1
    qn, qd = (q.numerator, q.denominator)
    E = 4 * n
    pw = [qn**e * qd ** (E - e) for e in range(E + 1)]
    D = den * qd**E
    wt = np.abs(WA) + np.abs(WB)
    require(
        np.array_equal(Hn, Hn.T)
        and np.array_equal(Ho, Ho.T)
        and np.array_equal(P, P.T),
        "certificate condition",
    )

    def qblock(rows, cols):
        rows = np.asarray(rows)
        cols = np.asarray(cols)
        hn = Hn[np.ix_(rows, cols)].astype(object)
        ho = Ho[np.ix_(rows, cols)].astype(object)
        pp = P[np.ix_(rows, cols)].astype(object)
        e = wt[rows][:, None] + wt[cols][None, :]
        powers = np.array(pw, dtype=object)[e]
        return den * qd**E * hn - den * powers * ho + qd**E * pp

    pattern = (Hn != 0) | (Ho != 0) | (P != 0)
    central = [
        2 * ((n + 1) * (n + 1 - a) - q ** (2 * a) * n * (n - a))
        for a in range(1, n + 1)
    ]
    central_ok = all((c > 0 for c in central))
    kv, piv = forced_kernel(n, wedges)
    kernel_ok = True
    for ids in kv:
        rows = np.flatnonzero(pattern[:, ids].any(axis=1))
        if len(rows) and np.any(qblock(rows, ids).sum(axis=1)):
            kernel_ok = False
    keep = [k for k in range(m) if k not in set(piv)]
    comps = components(pattern, keep)
    t2 = perf_counter()
    blocks, psd_ok = prove_psd(
        lambda comp: qblock(comp, comp).tolist(), comps, kernel_ok, "residual", D
    )
    t_psd = perf_counter() - t2
    spot_ok = None
    if spot:
        rng = rng or random.Random(53 + n)
        x = {a: rng.randint(-4, 4) for a in all_labels}
        y = {a: rng.randint(-4, 4) for a in all_labels}
        z = np.array([x[a] * y[b] - x[b] * y[a] for a, b in wedges], dtype=object)
        quad = 0
        for comp in components(pattern, list(range(m))):
            zc = z[comp]
            quad += int(zc @ (qblock(comp, comp) @ zc))
        lhs = Fraction(quad, D) + sum(
            (
                c
                * (
                    (x[0] * y[a] - x[a] * y[0]) ** 2
                    + (x[-a] * y[0] - x[0] * y[-a]) ** 2
                )
                for a, c in zip(range(1, n + 1), central)
            )
        )
        xq = {a: q ** abs(a) * v for a, v in x.items()}
        yq = {a: q ** abs(a) * v for a, v in y.items()}
        rhs = literal_value(n + 1, x, y) - literal_value(n, xq, yq)
        spot_ok = lhs == rhs
    ok = identity and central_ok and kernel_ok and psd_ok and (spot_ok is not False)
    lbs = [v for _, _, v in blocks if v is not None]
    return {
        "file": Path(path).name,
        "sha256": hashlib.sha256(Path(path).read_bytes()).hexdigest(),
        "increment": f"I_{n}=F_{n + 1}-F_{n} o L_q",
        "n": n,
        "q": str(q),
        "tamper": tamper,
        "storage_denominator": den,
        "tags": dict(
            storage=sum((t[0] == "storage" for t in tags)),
            pure=sum((t[0] == "pure" for t in tags)),
        ),
        "identity_F_new": id1[:2],
        "identity_F_old": id2[:2],
        "plucker_zero": id3[:2],
        "kernel_annihilated": kernel_ok,
        "central_positive": central_ok,
        "component_sizes": [s for s, _, _ in blocks],
        "psd": psd_ok,
        "min_certified_lower_bound": str(min(lbs)) if lbs else None,
        "min_certified_lower_bound_float": float(min(lbs)) if lbs else None,
        "spot_check": spot_ok,
        "accepted": ok,
        "seconds_identity": round(t_id, 2),
        "seconds_psd": round(t_psd, 2),
        "seconds": round(perf_counter() - tic, 2),
    }


def check_F2():
    mono = Mono(1)
    WA = np.array([-1, 0])
    WB = np.array([0, 1])
    ids = np.arange(2)
    return is_zero(
        [gram_poly(ids, ids, np.array([4, 4]), WA, WB, mono), literal_F(2, mono, -1)]
    )[0]


def require(condition, message):
    if not condition:
        raise ValueError("FAIL: " + str(message))


def load_certificate(path):
    raw = gzip.decompress(Path(path).read_bytes())
    return json.loads(raw)


def checked_hash(raw, expected):
    require(hashlib.sha256(raw).hexdigest() == expected, "SHA-256 mismatch")


def controls():
    require(sylvester_pd([[2, 1], [1, 2]]), "positive matrix control")
    require(not sylvester_pd([[1, 2], [2, 1]]), "indefinite matrix rejected")
    require(not sylvester_pd([[1, 1], [1, 1]]), "singular matrix rejected")
    require(residual_pd([[1, 2], [2, 1]], 1) is None, "indefinite residual rejected")
    require(residual_pd([[2, 1], [1, 2]], 1) > 0, "positive residual control")
    mono = Mono(1)
    a, b, ids = np.array([-1, 0]), np.array([0, 1]), np.arange(2)
    require(
        not is_zero(
            [gram_poly(ids, ids, np.array([3, 4]), a, b, mono), literal_F(2, mono, -1)]
        )[0],
        "corrupted identity rejected",
    )
    raw = b"certificate"
    try:
        checked_hash(raw + b"!", hashlib.sha256(raw).hexdigest())
    except ValueError:
        pass
    else:
        raise ValueError("FAIL: corrupted data accepted")
    # Exercise the complete geometric-certificate path, beyond small matrices.
    path = Path(__file__).resolve().parent / "data/step_17.json.gz"
    altered_diagonal = check_geometric(path, tamper="diag", spot=False)
    require(not altered_diagonal["accepted"] and not altered_diagonal["identity_F_new"][0],
            "altered certificate diagonal must fail the polynomial identity")
    altered_correction = check_geometric(path, tamper="pure_huge", spot=False)
    require(not altered_correction["accepted"] and not altered_correction["psd"]
            and altered_correction["identity_F_new"][0]
            and altered_correction["plucker_zero"][0],
            "altered Pluecker correction must fail positivity despite preserving the polynomial")


def lower_bound_line(result):
    """Round an exact retained-principal-matrix bound down to 12 decimal places."""
    bound = Fraction(result["min_certified_lower_bound"])
    # Decimal display precision only; rounding down preserves the inequality.
    display_denominator = 10**12
    units = bound.numerator * display_denominator // bound.denominator
    require(units > 0, "displayed exact lower bound must be positive")
    integer, fractional = divmod(units, display_denominator)
    return (f"LOWER_BOUND: step {result['n']:02d}, retained Gram >= "
            f"{integer}.{fractional:012d} I (exact decimal)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--self-test", action="store_true", help="only run rejection controls"
    )
    args = parser.parse_args()
    controls()
    if args.self_test:
        print("PASS: positive checker negative controls")
        return
    directory = Path(__file__).resolve().parent / "data"
    manifest = json.loads((directory / "manifest.json").read_text())
    require(
        [entry["n"] for entry in manifest] == list(range(2, 50)), "complete chain 2..49"
    )
    for entry in manifest:
        n = entry["n"]
        require(entry["file"] == f"step_{n:02d}.json.gz", "certificate filename")
        require(
            entry["kind"] == ("normalized" if n <= 16 else "geometric"), "step kind"
        )
        path = directory / entry["file"]
        raw = path.read_bytes()
        checked_hash(raw, entry["sha256"])
        payload = gzip.decompress(raw)
        checked_hash(payload, entry["json_sha256"])
        require(json.loads(payload)["n"] == n, "certificate order")
    require(check_F2(), "F2 literal identity")
    print("PASS: F_2 = 4 z_(-1,0)^2 + 4 z_(0,1)^2", flush=True)
    for entry in manifest:
        path = directory / entry["file"]
        result = (
            check_normalized(path)
            if entry["kind"] == "normalized"
            else check_geometric(path)
        )
        require(result["accepted"], f"step {entry['n']}")
        print(
            f"PASS: step {entry['n']:02d} ({entry['kind']}), literal identity, kernel, exact PSD",
            flush=True,
        )
        print(lower_bound_line(result), flush=True)
    print(
        "PASS: F_N is SOS for 2 <= N <= 50; 48 exact steps; negative controls rejected"
    )


if __name__ == "__main__":
    main()
