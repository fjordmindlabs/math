#!/usr/bin/env python3
"""Erdős #647: witness generation for the sparse grid in (1e11, 1e12].

Same engine as gen_witnesses_rung3 (which covered (1e9, 1e11]); only the
range and output files change. Resumable via progress_1e12.json.
"""

import os
import sys

import gen_witnesses_rung3 as g

g.A = 10**11
g.X = 10**12
g.OUT = os.path.join(g.HERE, "witnesses_1e12.jsonl")
g.FAIL = os.path.join(g.HERE, "failures_1e12.jsonl")
g.PROG = os.path.join(g.HERE, "progress_1e12.json")

if __name__ == "__main__":
    sys.exit(g.main())
