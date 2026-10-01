#!/usr/bin/env python3
"""Reproduce the exact integer witness appendix using integers and Fraction only; no external packages.

This checks the rational witness and exponent budget, not the analytic lemmas.
All acceptance checks are explicit and remain active under python -O.
"""
from fractions import Fraction
from pathlib import Path
import argparse
import json
import re
import time

DEN = 1 << 64
# Published directed-rounding endpoints and coefficient mass, regenerated below.
LOW = -111807741093765987869670624504700
HIGH = -111807741093765987869670623456124
L1 = 859652168


def require(condition, message):
    if not condition:
        raise ValueError(message)


def weights():
    return [(1 << 43) * j // (128**2 + j*j)**2 for j in range(1, 257)]


def enclosure(z, hardy=True):
    points = [(r, j, sig, sig*z[j-1])
              for r in (1, 2) for j in range(1, 257) for sig in (-1, 1)]
    low = 0
    for r, j, sig, c in points:
        for t, k, tau, d in points:
            a = (r+t)**2 + (sig*j-tau*k)**2
            b = 4*r*t
            numerator = 4*b*b + 2*a*a - (2*a*b if hardy else 0)
            low += (DEN*c*d*numerator) // (a*a*b*b)
    return low, low + len(points)**2


def convolution_pairing(z):
    ds = [0] * 513
    for j, zj in enumerate(z, 1):
        for k, zk in enumerate(z, 1):
            ds[abs(j-k)] += zj*zk
            ds[j+k] -= zj*zk
    total = Fraction(0)
    for ell, value in enumerate(ds):
        if not value:
            continue
        for r in (1, 2):
            for t in (1, 2):
                a = (r+t)**2 + ell*ell
                total += 4*value*(Fraction(2, a*a) - Fraction(1, 4*r*t*a))
    return total


def validate(low, high, l1, rational):
    require((low, high, l1) == (LOW, HIGH, L1), 'Published integers differ')
    require(high - low == 1024**2, 'Wrong interval width')
    require(high < -(1 << 42)*DEN, 'Negative bound fails')
    require(l1 < 1 << 30, 'Coefficient budget fails')
    require(Fraction(low, DEN) <= rational <= Fraction(high, DEN),
            'Full-entry and convolution calculations disagree')
    nu = -rational/(l1*l1)
    require(Fraction(1, 1 << 18) < nu < Fraction(1, 1 << 16),
            'Normalized defect interval fails')


def threshold_budget(exponent):
    # 1/q is the interpolation exponent; 80 = 20 (entrywise majorant)
    # + 60 (squared coefficient-mass bound); 42 is the negative-pairing exponent.
    q = 1 << 17
    witness_power, slow_power, fast_power = 42, 80, 90
    predecessor = (slow_power-witness_power)*q
    require(exponent == predecessor+1, 'Threshold is not the least negative budget')
    # The integer root enclosure implies 2^(-1/q) < 1 - 1/(2q).
    require(pow(2*q-1, q) > 1 << (18*q-1), 'Integer root enclosure fails')
    deficit = Fraction(1 << witness_power, 2*q)
    require(fast_power-exponent < 0 and deficit > 1,
            'Final scalar sign bound fails')
    require(slow_power*q-(exponent-1) == witness_power*q,
            'Predecessor budget is not positive')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    started = time.monotonic()
    z = weights()
    low, high = enclosure(z)
    l1 = 4*sum(z)
    rational = convolution_pairing(z)
    validate(low, high, l1, rational)
    # The negative channel is essential; removing it gives a positive pairing.
    positive_low, _ = enclosure(z, hardy=False)
    require(positive_low > 0, 'Positive control fails')
    # Base case for 2^(k-2) >= 8k+40. For k >= 16 the induction
    # step follows algebraically from 2(8k+40) - (8(k+1)+40) = 8k+32 > 0.
    k = 16
    require(1 << (k-2) >= 8*k+40, 'Tail budget base case fails')
    source = (Path(__file__).resolve().parents[1] / 'paper/main.tex').read_text()
    match = re.search(r'\\newcommand\{\\ThresholdExponent\}\{(\d+)\}', source)
    require(match is not None, 'Threshold macro is missing')
    ambient = int(match.group(1))
    exponent, remainder = divmod(ambient-1, 2)
    require(remainder == 0, 'Ambient exponent does not encode a dyadic depth')
    threshold_budget(exponent)
    controls = 0
    for candidate in [(low+1, high, l1, rational),
                      (low, high+1, l1, rational),
                      (low, high, l1+1, rational),
                      (low, high, l1, -rational)]:
        rejected = False
        try:
            validate(*candidate)
        except ValueError:
            rejected = True
        require(rejected, 'Corrupted certificate was accepted')
        controls += 1
    rejected = False
    try:
        threshold_budget(exponent-1)
    except ValueError:
        rejected = True
    require(rejected, 'Predecessor threshold was accepted')
    controls += 1
    print(json.dumps({'status': 'PASS', 'entries': 1024**2,
        'l1': l1, 'lower_numerator': str(low), 'upper_numerator': str(high),
        'denominator': str(DEN), 'convolution_agrees': True,
        'dyadic_exponent': exponent, 'ambient_exponent': ambient,
        'least_negative_budget': True, 'integer_root_enclosure': True,
        'positive_control': True, 'corruptions_rejected': controls,
        'seconds': round(time.monotonic()-started, 3)}, indent=2))
    print('PASS: manuscript witness, convolution, threshold, and five rejection controls')


if __name__ == '__main__':
    main()
