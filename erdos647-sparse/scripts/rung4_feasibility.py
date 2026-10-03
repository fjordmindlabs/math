#!/usr/bin/env python3
"""Erdős #647 rung 4 feasibility: does a mod 23 / mod 29 sieve re-sparsify the grid?

Method = rung 2's divisor-budget engine, one prime deeper. For a candidate n
(360360 | n, (n%17, n%19) in the 41 survivors) and a residue class c_p = n % p
(p = 23, 29), a shift k >= 1 kills the whole class if the *forced* divisor
stack of m = n - k,

    d = gcd(360360, k)
        * 17 if k % 17 == c17  * 19 if k % 19 == c19
        * 23 if k % 23 == c23 [* 29 if k % 29 == c29]

satisfies the budget 2*tau(d) >= k + 3 (pairing divisors e <-> m/e, valid
whenever d*d < m).  The class survives if no k <= K_MAX works.

Outputs survivor counts for: (a) mod 23 joint with the 41 classes,
(b) mod 29 joint, (c) mod 23*29 joint — plus the implied n-threshold
(max d^2 over used shifts) and projected witness counts for (1e11, 1e12].
"""

from math import gcd
import json, os

SURVIVORS_1719 = [
    (0, 0), (0, 7), (0, 11), (0, 13), (0, 14), (0, 15),
    (0, 16), (0, 17), (11, 0), (11, 13), (11, 14), (11, 15),
    (11, 16), (11, 17), (13, 0), (13, 7), (13, 14), (13, 15),
    (13, 16), (13, 17), (14, 0), (14, 7), (14, 11), (14, 13),
    (14, 15), (14, 16), (14, 17), (15, 0), (15, 7), (15, 11),
    (15, 13), (15, 14), (15, 16), (15, 17), (16, 0), (16, 7),
    (16, 11), (16, 13), (16, 14), (16, 15), (16, 17),
]

K_MAX = 20000
D_MAX = 316227  # d^2 < 1e11 so the rung applies to all n > 1e11


def tau(n):
    t, d = 1, 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            t *= e + 1
        d += 1
    if n > 1:
        t *= 2
    return t


TAU_GCD = {}  # gcd(360360,k) -> tau, memo


def stack_tau(k, c17, c19, extra):  # extra: list of (p, c_p)
    g = gcd(360360, k)
    d = g
    for p, c in (((17, c17), (19, c19)) + tuple(extra)):
        if k % p == c:
            d *= p
    if d not in TAU_GCD:
        TAU_GCD[d] = tau(d)
    return d, TAU_GCD[d]


def kill_shift(c17, c19, extra):
    """Smallest k killing the class, or None. Returns (k, d)."""
    for k in range(1, K_MAX + 1):
        d, t = stack_tau(k, c17, c19, extra)
        if d <= D_MAX and 2 * t >= k + 3:
            return k, d
    return None


def sweep(primes):
    """primes: list of extra primes, e.g. [23] or [23, 29]."""
    from itertools import product
    survivors, kills = [], []
    max_d = 0
    for c17, c19 in SURVIVORS_1719:
        for cs in product(*(range(p) for p in primes)):
            extra = list(zip(primes, cs))
            r = kill_shift(c17, c19, extra)
            if r is None:
                survivors.append((c17, c19) + cs)
            else:
                kills.append(((c17, c19) + cs, r))
                max_d = max(max_d, r[1])
    return survivors, kills, max_d


def report(primes):
    total = 41
    for p in primes:
        total *= p
    surv, kills, max_d = sweep(primes)
    frac = len(surv) / total
    # points in (1e11, 1e12]
    span = 10**12 - 10**11
    cur_pts = span / 360360 * (41 / 323)
    new_pts = span / 360360 * (len(surv) / (323 * __import__("math").prod(primes)))
    print(f"--- extra primes {primes} ---")
    print(f"classes: {len(surv)}/{total} survive  ({frac:.4f})")
    print(f"max stacked d used: {max_d}  -> rung valid for n > {max_d*max_d:,}")
    print(f"grid points (1e11,1e12]: {cur_pts:,.0f} now -> {new_pts:,.0f} with rung "
          f"({cur_pts/new_pts if new_pts else float('inf'):.2f}x sparser)")
    ks = [r[1][0] for r in kills]
    if ks:
        print(f"kill shifts: max k = {max(ks)}, mean = {sum(ks)/len(ks):.1f}")
    return surv


if __name__ == "__main__":
    import math
    s23 = report([23])
    s29 = report([29])
    s2329 = report([23, 29])
    out = {"mod23": s23, "mod29": s29, "mod23_29": [list(x) for x in s2329]}
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "rung4_survivors.json"), "w") as f:
        json.dump({k: [list(x) for x in v] for k, v in out.items()}, f)
    print("survivor lists written to rung4_survivors.json")
