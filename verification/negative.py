"""Exact integer enclosures for the tangent witness and extraction constants.

The analytic implications connecting these quantities to non-SOS are in the
paper. This program checks their arithmetic, not the analytic proof.
"""

from fractions import Fraction


def require(condition, message):
    if not condition:
        raise ValueError("FAIL: " + message)


def enclose(terms, scale=2**64):
    """Each rational term lies between floor(scale*t)/scale and that plus 1/scale."""
    lower = 0
    count = 0
    for numerator, denominator in terms:
        require(denominator > 0, "positive denominator")
        lower += scale * numerator // denominator
        count += 1
    return lower, lower + count


def full_terms(values, omit_negative=False):
    points = [
        (r, sign * j, sign * values[j - 1])
        for r in (1, 2)
        for j in range(1, 257)
        for sign in (-1, 1)
    ]
    for r, j, c in points:
        for t, k, d in points:
            A = (r + t) ** 2 + (j - k) ** 2
            C = 4 * r * t
            # S_F = 2 (2/A^2 + 1/C^2 - 1/(AC)).
            numerator = 4 * C * C + 2 * A * A
            if not omit_negative:
                numerator -= 2 * A * C
            yield c * d * numerator, A * A * C * C


def sine_terms(values):
    # Sum over positive frequencies after canceling the constant radial term.
    for r in (1, 2):
        for t in (1, 2):
            C = 4 * r * t
            for j, c in enumerate(values, 1):
                for k, d in enumerate(values, 1):
                    A = (r + t) ** 2 + (j - k) ** 2
                    B = (r + t) ** 2 + (j + k) ** 2
                    yield (
                        c * d * (2 * C * (B * B - A * A) - A * B * (B - A)),
                        C * A * A * B * B,
                    )


def root_upper_bound(numerator):
    """Certify an upper bound on 2^(-1/131072) by an integer power comparison."""
    q = 2**17
    require(pow(numerator, q) > 1 << (18 * q - 1), "rational root enclosure")
    return Fraction(numerator, 2 * q)


def constants(K):
    # q is the reciprocal of the two-rectangle interpolation exponent.
    q = 2**17
    require(K == 38 * q + 1, "specified K")
    eta1, eta2 = Fraction(1, 2**13), Fraction(1, 2**5)
    require(2 * eta1 * eta2 == Fraction(1, 2**17), "interpolation exponent")
    # The paper's sine and hyperbolic-sine barrier factors give respectively
    # (1/1024)(1/4) and (1/2)(1/4); the chosen allowances are smaller.
    require(Fraction(1, 1024 * 4) > eta1, "first barrier allowance")
    require(Fraction(1, 2 * 4) > eta2, "second barrier allowance")
    require(2 ** (16 - 2) >= 8 * 16 + 40, "tail inequality base")
    # For k >= 16, 2(8k+40) - (8(k+1)+40) = 8k+32 > 0.
    # This symbolic observation propagates the preceding base case; evaluating
    # that fixed positive expression would add no independent check.
    require(K >= 16, "tail inequality range")
    exponent = 20 - K * 2 * eta1 * eta2
    require(exponent == -18 - Fraction(1, q), "scaled pure entry exponent")
    require(60 + exponent == 42 - Fraction(1, q), "pure pairing error exponent")
    upper = root_upper_bound(2 * q - 1)
    deficit = 2**42 * (1 - upper)
    require(deficit == 2**24, "strict pure pairing deficit")
    require(90 - K < 0, "baseline pairing error < 1")
    require(1 < deficit, "strict final contradiction")
    require(2 * K == 9961474 and 2 * K + 1 == 9961475, "depth and ambient threshold")


def main():
    values = [(2**43 * j) // (128**2 + j * j) ** 2 for j in range(1, 257)]
    require(4 * sum(values) == 859652168 < 2**30, "coefficient l1 norm")
    # Lean uses the sharper squared coefficient mass, so the pure error
    # <= 2^-18 already leaves a full 2^40 gap below the negative 2^42 witness.
    mass_squared = (4 * sum(values))**2
    require(mass_squared <= 3 * 2**58, "sharp squared coefficient mass")
    require(Fraction(mass_squared, 2**18) + 1 < 2**42,
            "sharp mass budget closes without the root estimate")
    scale = 2**64
    lo, hi = enclose(full_terms(values))
    require(hi < -(2**42) * scale, "negative full Hermitian pairing")
    slo, shi = enclose(sine_terms(values))
    require(shi < -(2**40) * scale, "negative sine pairing")
    # Symbolic sign summation: K(A)+K(A)-K(B)-K(B) = 4 G(A,B).
    # Three rational regression inputs exercise small, unequal-radial, and
    # widely separated frequency denominators; they are not analytic bounds.
    for A, B, C in [(4, 8, 4), (9, 34, 8), (16, 65552, 16)]:
        kernel = lambda T: (
            2 * (Fraction(2, T * T) + Fraction(1, C * C) - Fraction(1, T * C))
        )
        G = (
            Fraction(2, A * A)
            - Fraction(2, B * B)
            - Fraction(1, C) * (Fraction(1, A) - Fraction(1, B))
        )
        require(2 * (kernel(A) - kernel(B)) == 4 * G, "sign-sum normalization control")
    require(max(lo, 4 * slo) <= min(hi, 4 * shi), "independent enclosure agreement")
    constants(4980737)
    # Removing the negative kernel term must destroy the negative certificate.
    control_lo, _ = enclose(full_terms(values, omit_negative=True))
    require(control_lo > 0, "corrupted kernel rejected")
    try:
        constants(4980736)
    except ValueError:
        pass
    else:
        raise ValueError("FAIL: altered constant was accepted")
    try:
        root_upper_bound(262142)
    except ValueError:
        pass
    else:
        raise ValueError("FAIL: altered root enclosure was accepted")
    print(f"full pairing in [{lo}, {hi}] / {scale}")
    print("coefficient l1 = 859652168; pairing < -2^42")
    print("K = 4980737; depth = 2^9961474; threshold = 2^9961475")
    print("root bound: (262143/262144)^131072 > 1/2; total budget < -2^24 + 1 < 0; negative controls rejected")
    print("PASS: exact tangent witness and constants")


if __name__ == "__main__":
    main()
