#!/usr/bin/env python3
"""Erdős #647 10^13 extension: the rung-2b + rung-4 fast grid filter.

Exact Python mirror of the Lean-side gridFilter13 (Erdos647Sparse/Checker13.lean):

    gridFilter13 n = (n <= 10^11) || (mask323.testBit (n % 323)
                                      && mask27k.testBit (flatIdx n))
    flatIdx n = (pairIdxOf (n % 17) (n % 19) * 23 + n % 23) * 29 + n % 29

Masks are built here from two INDEPENDENT sources and cross-checked:
  1. the rung4SsNN survivor lists extracted from the built Lean files
     Erdos647Sparse/Rung4Chunks/Chunk00-27.lean (the exact artifact
     classOk4 is proved against), and
  2. rung4_survivors.json "mod23_29" tuples from the feasibility analysis,
     flat-encoded with the mirrored pairIdxOf table.

Importers get: PAIR_IDX, MASK323, MASK27K, FLAT_SURVIVORS, grid_filter13(n),
and mask hex strings for the Lean emitter.
"""

import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
DEC = os.environ.get("ERDOS647_SPARSE_ROOT", os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))  # package root (holds Erdos647Sparse/)

from gen_witnesses_rung3 import SURVIVORS  # 41 rung-2b pairs (c17, c19)

# pairIdxOf mirror: lexicographically sorted survivor pairs -> 0..40.
# Must match Erdos647Sparse/Rung4.lean pairIdxOf (verified below against
# pairAt order used by the flat encoding).
PAIR_IDX = {p: i for i, p in enumerate(sorted(SURVIVORS))}


def _extract_lean_survivors():
    """Pull the 4431 flat survivor indices out of the built Lean chunks."""
    flat = []
    for c in range(28):
        path = os.path.join(DEC, "Erdos647Sparse", "Rung4Chunks", f"Chunk{c:02d}.lean")
        with open(path) as f:
            src = f.read()
        m = re.search(r"def rung4Ss%02d : List ℕ :=\s*\[(.*?)\]" % c, src, re.S)
        assert m, f"rung4Ss{c:02d} not found in {path}"
        body = m.group(1).strip()
        if body:
            flat.extend(int(x) for x in body.replace("\n", " ").split(","))
    return flat


def _json_survivors_flat():
    with open(os.path.join(HERE, "rung4_survivors.json")) as f:
        tup = json.load(f)["mod23_29"]
    out = []
    for c17, c19, c23, c29 in tup:
        out.append((PAIR_IDX[(c17, c19)] * 23 + c23) * 29 + c29)
    return out


_lean = _extract_lean_survivors()
_json = _json_survivors_flat()
assert len(_lean) == 4431, f"Lean survivor count {len(_lean)} != 4431"
assert sorted(_lean) == sorted(_json), "Lean vs JSON survivor mismatch"
assert _lean == sorted(_lean), "Lean survivor list not sorted"
FLAT_SURVIVORS = _lean

MASK27K = 0
for i in FLAT_SURVIVORS:
    MASK27K |= 1 << i

# mask323: bit r set iff (r % 17, r % 19) is a rung-2b survivor pair.
MASK323 = 0
for r in range(323):
    if (r % 17, r % 19) in SURVIVORS:
        MASK323 |= 1 << r
assert bin(MASK323).count("1") == 41

_FLAT_SET = set(FLAT_SURVIVORS)


def flat_idx(n):
    pi = PAIR_IDX.get((n % 17, n % 19), 41)
    return (pi * 23 + n % 23) * 29 + n % 29


def grid_filter13(n):
    """Exact mirror of Lean gridFilter13."""
    if n <= 10**11:
        return True
    return bool((MASK323 >> (n % 323)) & 1) and bool((MASK27K >> flat_idx(n)) & 1)


# Consistency: mask-based filter == set-based reference on a full period.
def _selfcheck():
    M = 360360
    base = 10**12 // M + 1
    for j in range(base, base + 215441):
        n = M * j
        ref = (n % 17, n % 19) in SURVIVORS and flat_idx(n) in _FLAT_SET
        assert grid_filter13(n) == ref, f"filter mismatch at n={n}"
    cnt = sum(grid_filter13(M * j) for j in range(base, base + 215441))
    assert cnt == 4431, f"period survivor count {cnt} != 4431"


if __name__ == "__main__":
    _selfcheck()
    print(f"OK: 4431 flat survivors, masks consistent over a full 215441-period")
    print(f"MASK323  hex digits: {len(f'{MASK323:x}')}")
    print(f"MASK27K  hex digits: {len(f'{MASK27K:x}')}")
