#!/usr/bin/env python3
"""Erdős #647 rung 3 (low range): witnesses for the grid in (1e7, 1e9].

Filter matches the Lean gridFilter: a grid point n = 360360*j needs a witness
iff n <= 250000000 (below the rung-2b threshold: every 360360-multiple
survives) or (n%17, n%19) is in the 41-class survivor list.

Output: witnesses_low.jsonl, same schema as witnesses_rung3.jsonl.
Range: j in [28, 2775]  (360360*28 = 10090080 > 1e7; 360360*2775 = 999999000 <= 1e9;
j = 2776 onward is covered by witnesses_rung3.jsonl).
"""

import json
import os

from gen_witnesses_rung3 import M, SURVIVORS, find_witness

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "witnesses_low.jsonl")

J0, J1 = 28, 2775
THRESH = 250000000


def grid_filter(n):
    return n <= THRESH or (n % 17, n % 19) in SURVIVORS


def main():
    n_pts = 0
    fails = 0
    with open(OUT, "w") as out:
        for j in range(J0, J1 + 1):
            n = M * j
            if not grid_filter(n):
                continue
            n_pts += 1
            w = find_witness(n)
            if w is None:
                fails += 1
                print(f"FAIL n={n}", flush=True)
                continue
            k, pairs = w
            out.write(json.dumps({"n": n, "k": k, "pairs": pairs}) + "\n")
    print(f"done: {n_pts} grid points, {fails} failures")
    return 1 if fails else 0


if __name__ == "__main__":
    raise SystemExit(main())
