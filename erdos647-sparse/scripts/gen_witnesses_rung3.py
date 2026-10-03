#!/usr/bin/env python3
"""Erdős #647 rung 3: witness generation for the sparse candidate grid (1e9, 1e11].

By Erdos647Mod (kernel-clean, rungs 1+2), every candidate n > 2.5e8 has
360360 | n and (n%17, n%19) in the 41-class survivor list. decanus certifies
no candidate <= 1e9. This script finds, for every surviving grid point
n = 360360*j in (1e9, 1e11], a kill witness m = n - k with
certTau(m, pairs) >= k + 3, in exactly the decanus witness format
(Erdos647/Defs.lean): pairs = maximal prime-power divisors p^e of m with
p < 1024 (strictly decreasing p), certTau = prod(e+1), doubled when the
cofactor m / smooth > 1.

Output: witnesses_rung3.jsonl, one line per grid point
    {"n": int, "k": int, "pairs": [[p, e], ...]}   (pairs desc by p)
Failures (no witness within K_MAX): failures_rung3.jsonl.
Checkpoint: progress_rung3.json {"next_j": int} — safe to re-run, resumes.
"""

import json
import os
import sys

import numpy as np

M = 360360  # 2^3 * 3^2 * 5 * 7 * 11 * 13
A = 10**9
X = 10**11
K_MAX = 131072  # staged windows double up to this scan depth

# 41 survivor classes of (n % 17, n % 19) — must match Erdos647Mod.survivors.
SURVIVORS = {
    (0, 0), (0, 7), (0, 11), (0, 13), (0, 14), (0, 15),
    (0, 16), (0, 17), (11, 0), (11, 13), (11, 14), (11, 15),
    (11, 16), (11, 17), (13, 0), (13, 7), (13, 14), (13, 15),
    (13, 16), (13, 17), (14, 0), (14, 7), (14, 11), (14, 13),
    (14, 15), (14, 16), (14, 17), (15, 0), (15, 7), (15, 11),
    (15, 13), (15, 14), (15, 16), (15, 17), (16, 0), (16, 7),
    (16, 11), (16, 13), (16, 14), (16, 15), (16, 17),
}

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "witnesses_rung3.jsonl")
FAIL = os.path.join(HERE, "failures_rung3.jsonl")
PROG = os.path.join(HERE, "progress_rung3.json")
CHECKPOINT_EVERY = 200  # grid points between progress flushes


def primes_below(n):
    sieve = np.ones(n, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    return np.nonzero(sieve)[0].astype(np.int64)


PRIMES = primes_below(1024)  # 172 primes


def cert_tau_window(ms):
    """Vectorized certTau for an int64 array of m values (decanus semantics)."""
    tau = np.ones_like(ms)
    smooth = np.ones_like(ms)
    for p in PRIMES:
        mask = ms % p == 0
        if not mask.any():
            continue
        e = np.zeros_like(ms)
        pe = np.ones_like(ms)
        while mask.any():
            e[mask] += 1
            pe[mask] *= p
            mask = mask & (ms % (pe * p) == 0)
        tau *= e + 1
        smooth *= pe
    return np.where(smooth < ms, 2 * tau, tau)


def factor_pairs(m):
    """Maximal prime-power pairs of m over primes < 1024, descending by p."""
    pairs = []
    for p in PRIMES:
        p = int(p)
        if m % p == 0:
            e = 0
            mm = m
            while mm % p == 0:
                mm //= p
                e += 1
            pairs.append([p, e])
    pairs.sort(reverse=True)
    return pairs


def check_witness(n, k, pairs):
    """Mirror Erdos647.witnessOk + kill condition exactly, in pure Python."""
    m = n - k
    assert 0 < m < n
    smooth = 1
    tau = 1
    prev = 1024
    for p, e in pairs:
        assert p < prev, "pairs not strictly decreasing"
        prev = p
        assert m % p**e == 0 and m % p ** (e + 1) != 0, "not maximal"
        smooth *= p**e
        tau *= e + 1
    assert m % smooth == 0
    cert = 2 * tau if smooth < m else tau
    assert m + cert >= n + 3, "does not kill n"


def find_witness(n):
    """Return (k, pairs) with certTau(n-k) >= k+3, or None."""
    lo = 1
    width = 512
    while lo <= K_MAX:
        hi = min(lo + width - 1, K_MAX)
        ks = np.arange(lo, hi + 1, dtype=np.int64)
        certs = cert_tau_window(n - ks)
        ok = np.nonzero(certs >= ks + 3)[0]
        if ok.size:
            k = int(ks[ok[0]])
            pairs = factor_pairs(n - k)
            check_witness(n, k, pairs)
            return k, pairs
        lo = hi + 1
        width *= 2
    return None


def main():
    j0 = A // M + 1
    j1 = X // M
    next_j = j0
    if os.path.exists(PROG):
        with open(PROG) as f:
            next_j = json.load(f)["next_j"]
    print(f"grid j in [{next_j}, {j1}], module {M}, {len(SURVIVORS)} classes", flush=True)

    out = open(OUT, "a")
    fail = open(FAIL, "a")
    done_since = 0
    n_pts = 0
    for j in range(next_j, j1 + 1):
        n = M * j
        if (n % 17, n % 19) not in SURVIVORS:
            continue
        n_pts += 1
        w = find_witness(n)
        if w is None:
            fail.write(json.dumps({"n": n}) + "\n")
            fail.flush()
            print(f"FAIL n={n} (no witness within {K_MAX})", flush=True)
        else:
            k, pairs = w
            out.write(json.dumps({"n": n, "k": k, "pairs": pairs}) + "\n")
        done_since += 1
        if done_since >= CHECKPOINT_EVERY:
            out.flush()
            os.fsync(out.fileno())
            with open(PROG, "w") as f:
                json.dump({"next_j": j + 1}, f)
            done_since = 0
            print(f"checkpoint j={j} n={n} points so far this run: {n_pts}", flush=True)
    out.flush()
    fail.close()
    out.close()
    with open(PROG, "w") as f:
        json.dump({"next_j": j1 + 1}, f)
    print(f"done: processed through j={j1}", flush=True)


if __name__ == "__main__":
    sys.exit(main())
