#!/usr/bin/env python3
"""Erdős #647 — rung-scaling extrapolation toward the 10^22 unverified frontier.

Appendix engine for the consolidated methods writeup (Fjordmind Labs,
2026-10-03; CEO-directed 2026-10-02).

Generalizes rung4_feasibility.py's divisor-budget sieve to sieve primes
17..97 and validity thresholds 10^11..10^21, and projects the kernel cost of
a kernel-checked "no solution in (24, T]" certificate for T up to 10^22.

Sieve rule (sound for every candidate n with 360360 | n, n > dmax^2):
  for shift k >= 1 the forced divisor stack of m = n - k is
      d = gcd(360360, k) * prod{ p in S : k ≡ c_p (mod p) }
  for any subset S of the sieve primes (taking a subset is sound: every
  listed prime divides m).  m = d*t with t > d (needs d*d < m, i.e. d <= dmax)
  gives tau(m) >= 2*tau(d); the candidate property forces tau(m) <= k + 2;
  so 2*tau(d) >= k + 3 is a contradiction and the whole residue class dies.
  'min' stacking takes the s smallest matching primes with s minimal
  (superset of rung4_feasibility.py's 'all' stacking, which multiplies every
  matching prime and so can overshoot dmax).

Outputs rung_scaling_extrapolation.json + a markdown table on stdout.
"""

import json
import math
import os
import sys
import time
from math import gcd

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = 360360
PRIMES = [17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
K_MAX = int(os.environ.get("K_MAX", "600"))
EXACT_LIMIT = int(os.environ.get("EXACT_LIMIT", "3000000"))   # classes
SAMPLE_N = int(os.environ.get("SAMPLE_N", "300000"))
RNG = np.random.default_rng(647)

# 41 rung-2b survivors of (n%17, n%19), as proved by mod_17_19_of_cand.
SURVIVORS_1719 = [
    (0, 0), (0, 7), (0, 11), (0, 13), (0, 14), (0, 15),
    (0, 16), (0, 17), (11, 0), (11, 13), (11, 14), (11, 15),
    (11, 16), (11, 17), (13, 0), (13, 7), (13, 14), (13, 15),
    (13, 16), (13, 17), (14, 0), (14, 7), (14, 11), (14, 13),
    (14, 15), (14, 16), (14, 17), (15, 0), (15, 7), (15, 11),
    (15, 13), (15, 14), (15, 16), (15, 17), (16, 0), (16, 7),
    (16, 11), (16, 13), (16, 14), (16, 15), (16, 17),
]


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


G = [gcd(BASE, k) for k in range(K_MAX + 1)]
TG = [tau(g) for g in G]
S_MIN = []  # minimal number of extra matching primes needed at shift k
for k in range(K_MAX + 1):
    s = 0
    while k >= 1 and 2 * TG[k] * (1 << s) < k + 3:
        s += 1
    S_MIN.append(s)


def kill(C, primes, dmax, stack="min", kmax=K_MAX):
    """C: (N, m) residues mod primes (ascending). Returns (killed bool (N,), kill_k int (N,))."""
    N, m = C.shape
    P = np.array(primes, dtype=np.int64)
    Pf = P.astype(np.float64)
    killed = np.zeros(N, dtype=bool)
    killk = np.zeros(N, dtype=np.int32)
    alive_idx = np.arange(N)
    for k in range(1, kmax + 1):
        g, tg, s = G[k], TG[k], S_MIN[k]
        if g > dmax or s > m or len(alive_idx) == 0:
            continue
        Ca = C[alive_idx]
        M = Ca == (k % P)  # (Na, m) which sieve primes divide n - k in this class
        if stack == "min":
            cnt = M.sum(axis=1)
            cc = np.cumsum(M, axis=1)
            PP = np.cumprod(np.where(M, Pf, 1.0), axis=1)
            prod_s = np.max(np.where(cc <= s, PP, 0.0), axis=1)  # product of the s smallest matches
            dead = (cnt >= s) & (g * prod_s <= dmax)
        else:  # 'all': stack every matching prime (rung4_feasibility.py semantics)
            d = g * np.prod(np.where(M, Pf, 1.0), axis=1)
            t = tg * (1 << M.sum(axis=1))
            dead = (d <= dmax) & (2 * t >= k + 3)
        if dead.any():
            di = alive_idx[dead]
            killed[di] = True
            killk[di] = k
            alive_idx = alive_idx[~dead]
    return killed, killk


def extend(C, p):
    """Append residue 0..p-1 to every row: (N, m) -> (N*p, m+1)."""
    N = C.shape[0]
    R = np.repeat(C, p, axis=0)
    r = np.tile(np.arange(p, dtype=C.dtype), N)[:, None]
    return np.concatenate([R, r], axis=1)


def sample_extend(C, p, n):
    rows = RNG.integers(0, C.shape[0], size=n)
    r = RNG.integers(0, p, size=n, dtype=C.dtype)[:, None]
    return np.concatenate([C[rows], r], axis=1)


def chain(dmax, primes_extra, stack="min", log=print):
    """Run the rung chain 17,19 -> +23 -> +29 -> ... for a given dmax.
    Returns list of per-rung dicts."""
    primes = [17, 19]
    C = np.array(SURVIVORS_1719, dtype=np.int16)
    S = float(len(C))          # survivor-class count (exact or estimated)
    M = 17 * 19                # modulus
    exact = True
    out = [dict(primes=list(primes), modulus=M, survivors=S, exact=True,
                frac=S / M, certs=0, kill_frac_prime=None, max_k=0, kill_k_hist={})]
    for p in primes_extra:
        t0 = time.time()
        primes = primes + [p]
        M *= p
        if exact and C.shape[0] * p <= EXACT_LIMIT:
            Cn = extend(C, p)
            killed, kk = kill(Cn, primes, dmax, stack)
            surv_frac = 1.0 - killed.mean()
            S_new = float((~killed).sum())
            C = Cn[~killed]
            certs = float(killed.sum())
        else:
            exact = False
            Cn = sample_extend(C, p, SAMPLE_N)
            killed, kk = kill(Cn, primes, dmax, stack)
            surv_frac = 1.0 - killed.mean()
            S_new = S * p * surv_frac
            certs = S * p - S_new
            C = Cn[~killed]        # keep a sample of survivors for the next rung
        ks = kk[killed]
        hist = {}
        if ks.size:
            for lo, hi in ((1, 10), (11, 50), (51, 100), (101, 300), (301, K_MAX)):
                hist[f"{lo}-{hi}"] = int(((ks >= lo) & (ks <= hi)).sum())
        rec = dict(primes=list(primes), modulus=M, survivors=S_new, exact=exact,
                   frac=S_new / M, certs=certs, kill_frac_prime=1.0 - surv_frac,
                   max_k=int(ks.max()) if ks.size else 0, kill_k_hist=hist,
                   sample=None if exact else int(Cn.shape[0]))
        out.append(rec)
        S = S_new
        log(f"  dmax={dmax:.3g} +{p:2d}: survivors {S_new:12.4g} / {M:.3g} "
            f"(frac {S_new / M:.3e}, prime-kill {1 - surv_frac:.3f}, "
            f"{'exact' if exact else 'MC'}, max k {rec['max_k']}, {time.time() - t0:.1f}s)")
    return out


def hardest_class_check(primes, dmax):
    """The class c_17 = 16, every other residue 0: show it is never killed."""
    C = np.array([[16] + [0] * (len(primes) - 1)], dtype=np.int16)
    killed, _ = kill(C, primes, dmax, "min", kmax=K_MAX)
    return not bool(killed[0])


def main():
    thresholds = [10 ** e for e in (11, 13, 15, 17, 19, 21)]
    results = {"k_max": K_MAX, "exact_limit": EXACT_LIMIT, "sample_n": SAMPLE_N,
               "primes": PRIMES, "chains": {}}

    # Regression: reproduce rung4_feasibility.py at dmax = 316227 with 'all' stacking.
    print("== regression vs rung4_feasibility.py ('all' stacking, dmax 316227) ==")
    reg = chain(316227, [23, 29], stack="all")
    print(f"  mod23·29 survivors: {reg[-1]['survivors']:.0f} (expected 4431)")
    results["regression_all_stack_4431"] = reg[-1]["survivors"]
    regm = chain(316227, [23, 29], stack="min")
    print(f"  'min' stacking at same dmax: {regm[-1]['survivors']:.0f} (<= 4431 expected)")
    results["regression_min_stack"] = regm[-1]["survivors"]

    for T in thresholds:
        dmax = math.isqrt(T) - 1
        print(f"== validity threshold n > {T:.0e}  (dmax {dmax}) ==")
        results["chains"][f"{T:.0e}"] = chain(dmax, PRIMES[2:])

    # structural obstruction to full divisibility
    print("== hardest class (c17=16, all other residues 0) survives? ==")
    hc = {}
    for T in (10 ** 11, 10 ** 21):
        ok = hardest_class_check(PRIMES, math.isqrt(T) - 1)
        hc[f"{T:.0e}"] = ok
        print(f"  dmax^2={T:.0e}: survives = {ok}")
    results["hardest_class_survives"] = hc

    with open(os.path.join(HERE, "rung_scaling_extrapolation.json"), "w") as f:
        json.dump(results, f, indent=1)
    print("written rung_scaling_extrapolation.json")


if __name__ == "__main__":
    main()
