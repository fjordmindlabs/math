#!/usr/bin/env python3
"""Erdős #647: witness generation for the rung-4 sparse grid in (1e12, 1e13].

Same witness engine as gen_witnesses_rung3 (certTau search, decanus
semantics), but the grid filter is the rung-4 fast filter mirrored in
filter13.py: only grid points n = 360360*j whose (n%17,n%19) pair AND flat
(17,19,23,29)-class survive are scanned (~514k of 25M). Resumable via
progress_1e13.json.
"""

import json
import os
import sys

import gen_witnesses_rung3 as g
from filter13 import grid_filter13

A = 10**12
X = 10**13
M = g.M
OUT = os.path.join(g.HERE, "witnesses_1e13.jsonl")
FAIL = os.path.join(g.HERE, "failures_1e13.jsonl")
PROG = os.path.join(g.HERE, "progress_1e13.json")
CHECKPOINT_EVERY = 500


def main():
    j0 = A // M + 1
    j1 = X // M
    next_j = j0
    if os.path.exists(PROG):
        with open(PROG) as f:
            next_j = json.load(f)["next_j"]
    print(f"grid j in [{next_j}, {j1}], module {M}, rung-4 fast filter", flush=True)

    out = open(OUT, "a")
    fail = open(FAIL, "a")
    done_since = 0
    n_pts = 0
    for j in range(next_j, j1 + 1):
        n = M * j
        if not grid_filter13(n):
            continue
        n_pts += 1
        w = g.find_witness(n)
        if w is None:
            fail.write(json.dumps({"n": n}) + "\n")
            fail.flush()
            print(f"FAIL n={n} (no witness within {g.K_MAX})", flush=True)
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
