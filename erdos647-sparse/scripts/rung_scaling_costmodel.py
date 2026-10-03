#!/usr/bin/env python3
"""Erdős #647 — kernel-cost projection from rung_scaling_extrapolation.json.

Cost model (CPU-seconds), all constants measured on the 10^12 / 10^13 builds
(8-core desktop, Lean v4.30.0, decanus witness format):

  walk_cost   = 2.5e-3  s per GRID POINT  (fast testBit filter + fuel-recursion
                overhead, measured 2026-10-02 on probe chunks; this is what the
                current design pays for every multiple of 360360 whether or not
                it survives the sieve)
  wit_cost    = [0.5e-3, 2.5e-3] s per SURVIVING point (period-walk design that
                visits survivors only; low end = bare witness check, high end =
                today's per-point walk cost)
  cert_cost   = 5e-3   s per killed class (rung theorem: 1000 classes / ~5 s)
  S_MAX       = 1e8    survivor classes — practical ceiling for an enumerable
                survivor list (Lean literal size; decanus' 10^9 asset is 260 MB)

For each target T and each rung r we report witnesses W = (T/360360) * frac_r
and three CPU-time curves:
  A. current design (per-grid-point walk): walk_cost * T/360360   [rung-independent]
  B. period walk, cheapest enumerable rung: cert_cost * certs_r + wit_cost * W
  C. period walk, best rung ignoring enumerability (lower bound on the method)
"""

import json
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = 360360
WALK = 2.5e-3
WIT_LO, WIT_HI = 0.5e-3, 2.5e-3
CERT = 5e-3
S_MAX = 1e8
YEAR = 365.25 * 86400

with open(os.path.join(HERE, "rung_scaling_extrapolation.json")) as f:
    R = json.load(f)


def fmt_t(s):
    if s < 3600:
        return f"{s / 60:.1f} min"
    if s < 86400 * 3:
        return f"{s / 3600:.1f} h"
    if s < YEAR / 2:
        return f"{s / 86400:.0f} d"
    return f"{s / YEAR:.3g} y"


def pick_chain(T):
    """Use the chain whose validity threshold is the largest ≤ T/100
    (the rung must hold for all n in the extended range; keep 2 decades
    of slack so the previous certificate covers the small n)."""
    keys = sorted(R["chains"], key=lambda k: float(k))
    best = keys[0]
    for k in keys:
        if float(k) <= T / 100:
            best = k
    return best, R["chains"][best]


print("## Table A — sieve strength per rung (validity threshold n > 10^11 vs 10^21)\n")
print("| rung | primes up to | modulus | survivors (classes) | density f | prime kill-frac | certs for this rung |")
print("|---|---|---|---|---|---|---|")
for key in ("1e+11", "1e+21"):
    ch = R["chains"][key]
    print(f"| **n > {key}** | | | | | | |")
    for i, rec in enumerate(ch):
        p = rec["primes"][-1]
        ex = "" if rec["exact"] else " (MC)"
        kf = "–" if rec["kill_frac_prime"] is None else f"{rec['kill_frac_prime']:.3f}"
        print(f"| {i + 2} | {p} | {rec['modulus']:.3g} | {rec['survivors']:.4g}{ex} | "
              f"{rec['frac']:.3e} | {kf} | {rec['certs']:.3g} |")
print()

print("## Table B — projected kernel cost of a kernel-checked bound to T\n")
print("| T | grid pts | chain used | best enumerable rung (prime) | survivors | witnesses W | "
      "A: current walk | B: period walk (lo–hi) | C: no-enumerability floor (rung, W) |")
print("|---|---|---|---|---|---|---|---|---|")
rows = []
for e in range(13, 23):
    T = 10 ** e
    key, ch = pick_chain(T)
    G = T / BASE
    costA = WALK * G
    # B: cheapest enumerable rung
    bestB = None
    for rec in ch:
        if rec["survivors"] > S_MAX:
            continue
        W = G * rec["frac"]
        lo = CERT * rec["certs"] + WIT_LO * W
        hi = CERT * rec["certs"] + WIT_HI * W
        if bestB is None or hi < bestB[2]:
            bestB = (rec, lo, hi, W)
    # C: best rung regardless of enumerability (witness cost only, low constant)
    bestC = None
    for rec in ch:
        W = G * rec["frac"]
        c = WIT_LO * W
        if bestC is None or c < bestC[1]:
            bestC = (rec, c, W)
    rec, lo, hi, W = bestB
    print(f"| 10^{e} | {G:.2e} | n>{key} | rung {len(rec['primes'])} ({rec['primes'][-1]}) | "
          f"{rec['survivors']:.3g} | {W:.3g} | {fmt_t(costA)} | {fmt_t(lo)} – {fmt_t(hi)} | "
          f"{fmt_t(bestC[1])} (p≤{bestC[0]['primes'][-1]}, W={bestC[2]:.2g}) |")
    rows.append(dict(T=T, grid=G, chain=key, rung=len(rec["primes"]), prime=rec["primes"][-1],
                     survivors=rec["survivors"], W=W, costA=costA, costB_lo=lo, costB_hi=hi,
                     costC=bestC[1], C_prime=bestC[0]["primes"][-1], C_W=bestC[2]))
with open(os.path.join(HERE, "rung_scaling_costmodel.json"), "w") as f:
    json.dump(dict(WALK=WALK, WIT_LO=WIT_LO, WIT_HI=WIT_HI, CERT=CERT, S_MAX=S_MAX, rows=rows), f, indent=1)
print("\nhardest-class survives:", R["hardest_class_survives"])
