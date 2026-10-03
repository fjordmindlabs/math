#!/usr/bin/env python3
"""Full coverage verification for the (1e7, 1e11] sparse certificate.

Invariant mirrored from the Lean side (Erdos647Sparse):
  walking j = 28 .. 277500, the concatenation of witnesses_low.jsonl and
  witnesses_rung3.jsonl provides exactly one witness, in order, for every j
  with gridFilter(360360*j) = true, and each witness satisfies
  witnessOk n k pairs && n + 3 <= (n - k) + certTau(n - k, pairs).
"""

import json
import os

from gen_witnesses_rung3 import M, SURVIVORS, check_witness

HERE = os.path.dirname(os.path.abspath(__file__))
J0, J1 = 28, 277500
THRESH = 250000000


def grid_filter(n):
    return n <= THRESH or (n % 17, n % 19) in SURVIVORS


def load(fn):
    with open(os.path.join(HERE, fn)) as f:
        return [json.loads(line) for line in f]


def main():
    ws = load("witnesses_low.jsonl") + load("witnesses_rung3.jsonl")
    i = 0
    for j in range(J0, J1 + 1):
        n = M * j
        if not grid_filter(n):
            continue
        assert i < len(ws), f"ran out of witnesses at j={j}"
        rec = ws[i]
        assert rec["n"] == n, f"misalignment at j={j}: witness n={rec['n']} expected {n}"
        check_witness(rec["n"], rec["k"], rec["pairs"])
        i += 1
    assert i == len(ws), f"{len(ws) - i} unconsumed witnesses"
    print(f"OK: {i} witnesses cover every surviving grid point, j in [{J0}, {J1}]")
    print(f"boundary: first n = {M*J0}, last n = {M*J1}")


if __name__ == "__main__":
    main()
