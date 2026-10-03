#!/usr/bin/env python3
"""Erdős #647 rung 4: generate class-kill certificates for the mod 23·29 sieve.

Grid: flat index i over (pairIdx, c23, c29), i = (pairIdx*23 + c23)*29 + c29,
pairIdx in [0,41) indexing SURVIVORS_1719 in list order. 27,347 classes.

For each killed class, cert = (k, ps): shift k and the full factorization ps
(decanus Pairs format: (p, e) strictly decreasing in p) of the forced stack

    d = gcd(360360, k) * 17^[k%17=c17] * 19^[k%19=c19]
                       * 23^[k%23=c23] * 29^[k%29=c29]

subject to: d*d + k <= 10^11  (rung valid for all n > 10^11)
            2*smoothTau(ps) >= k + 3  (budget)

Outputs rung4_certs.json: {"survivors": [flat indices], "kills": [[i, k,
[[p,e],...]], ...]} both sorted by flat index. Verifies the exact Lean
walker semantics (rung4Walk / classKillOk mirror) before writing.
"""

from math import gcd
import json, os

HERE = os.path.dirname(os.path.abspath(__file__))

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
N_THRESH = 10**11  # rung applies to all n > N_THRESH; need d*d + k <= N_THRESH
TOTAL = 41 * 23 * 29  # 27347


def factor(n):
    """Full factorization as decanus Pairs: (p, e) strictly decreasing in p."""
    ps = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            ps.append((d, e))
        d += 1
    if n > 1:
        ps.append((n, 1))
    return ps[::-1]  # most-significant first, strictly decreasing


def smooth_val(ps):
    v = 1
    for p, e in ps:
        v *= p ** e
    return v


def smooth_tau(ps):
    t = 1
    for _, e in ps:
        t *= e + 1
    return t


def stack_d(c17, c19, c23, c29, k):
    d = gcd(360360, k)
    for p, c in ((17, c17), (19, c19), (23, c23), (29, c29)):
        if k % p == c:
            d *= p
    return d


def kill_shift(c17, c19, c23, c29):
    for k in range(1, K_MAX + 1):
        d = stack_d(c17, c19, c23, c29, k)
        if d * d + k <= N_THRESH and 2 * smooth_tau(factor(d)) >= k + 3:
            return k, d
    return None


def class_at(i):
    pair_idx, rem = divmod(i, 23 * 29)
    c23, c29 = divmod(rem, 29)
    c17, c19 = SURVIVORS_1719[pair_idx]
    return c17, c19, c23, c29


# ---- exact mirrors of the Lean checker (for pre-build verification) ----

def pairs_ok(bound, ps):
    for p, e in ps:
        if not (p < bound):
            return False
        if not is_prime_small(p):
            return False
        bound = p
    return True


SMALL_SIEVE = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


def is_prime_small(p):
    if p in SMALL_SIEVE:
        return True
    return 31 < p < 1024 and all(p % q != 0 for q in SMALL_SIEVE)


def maximal_in(m, ps):
    return all(m % p ** (e + 1) != 0 for p, e in ps)


def witness_ok(C, d, ps):
    # decanus witnessOk: d < C, pairsOk, (C-d) % smoothVal = 0, maximalIn
    return (d < C and pairs_ok(1024, ps) and (C - d) % smooth_val(ps) == 0
            and maximal_in(C - d, ps))


def cert_tau(m, ps):
    return 2 * smooth_tau(ps) if smooth_val(ps) < m else smooth_tau(ps)


def class_kill_ok(i, k, ps):
    """Mirror of Lean classKillOk (flat index form)."""
    c17, c19, c23, c29 = class_at(i)
    d = stack_d(c17, c19, c23, c29, k)
    return (0 < k and witness_ok(d, 0, ps)
            and smooth_val(ps) == d           # exact factorization: certTau = smoothTau
            and d * d + k <= N_THRESH
            and k + 2 < 2 * smooth_tau(ps))


def rung4_walk(fuel, i, ss, ks):
    """Mirror of Lean rung4Walk."""
    ss = list(ss); ks = list(ks)
    while fuel > 0:
        if ss and ss[0] == i:
            ss.pop(0)
        else:
            if not ks:
                return False
            j, k, ps = ks.pop(0)
            if j != i:  # certs carry their index for sanity; Lean walker is positional
                return False
            if not class_kill_ok(i, k, ps):
                return False
        fuel -= 1
        i += 1
    return not ss and not ks


def main():
    survivors, kills = [], []
    max_d = 0
    for i in range(TOTAL):
        c17, c19, c23, c29 = class_at(i)
        r = kill_shift(c17, c19, c23, c29)
        if r is None:
            survivors.append(i)
        else:
            k, d = r
            kills.append([i, k, factor(d)])
            max_d = max(max_d, d)
    print(f"classes: {len(survivors)} survive, {len(kills)} killed "
          f"(total {TOTAL}); max d = {max_d}")

    # verify every cert against the exact Lean-checker mirror
    for i, k, ps in kills:
        assert class_kill_ok(i, k, [tuple(p) for p in ps]), f"cert fails at i={i}"
    # verify the full walk
    ks = [(i, k, [tuple(p) for p in ps]) for i, k, ps in kills]
    assert rung4_walk(TOTAL, 0, survivors, ks), "full walk fails"
    print("all certs verified against Lean-checker mirror; full walk OK")

    with open(os.path.join(HERE, "rung4_certs.json"), "w") as f:
        json.dump({"survivors": survivors, "kills": kills,
                   "max_d": max_d, "n_thresh": N_THRESH}, f)
    print("written rung4_certs.json")

    # cross-check survivor count against rung4_feasibility.py result
    with open(os.path.join(HERE, "rung4_survivors.json")) as f:
        old = json.load(f)
    old_set = {tuple(x) for x in old["mod23_29"]}
    new_set = {class_at(i) for i in survivors}
    assert old_set == new_set, (
        f"survivor mismatch vs rung4_feasibility: {len(old_set)} vs {len(new_set)}")
    print(f"survivor set matches rung4_feasibility.py ({len(new_set)} classes)")


if __name__ == "__main__":
    main()
