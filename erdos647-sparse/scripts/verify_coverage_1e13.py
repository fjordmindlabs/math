#!/usr/bin/env python3
"""Full coverage verification for the (1e12, 1e13] rung-4 sparse certificate.

Invariant mirrored from the Lean side (Erdos647Sparse.Grid13):
  walking j = 2775003 .. 27750027, witnesses_1e13.jsonl provides exactly one
  witness, in order, for every j with gridFilter13(360360*j) = true, and each
  witness satisfies witnessOk n k pairs && n + 3 <= (n - k) + certTau(n - k).

gridFilter13 is mirrored by filter13.grid_filter13, itself doubly verified
against the built Lean survivor lists.
"""

import json
import os

from gen_witnesses_rung3 import M, check_witness
from filter13 import grid_filter13

HERE = os.path.dirname(os.path.abspath(__file__))
J0, J1 = 2775003, 27750027


def main():
    with open(os.path.join(HERE, "witnesses_1e13.jsonl")) as f:
        ws = [json.loads(line) for line in f]
    i = 0
    for j in range(J0, J1 + 1):
        n = M * j
        if not grid_filter13(n):
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
