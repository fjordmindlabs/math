#!/bin/bash
# Erdős #647 — 10^13 extension, RESUME of stage 4 only (build) after queue runner vanished 2026-10-03 ~02:21.
# Stages 0-3 verified complete in run_1e13.log (513661 witnesses, coverage OK, 1525 chunks emitted).
set -euo pipefail
export PATH=$HOME/.elan/bin:$PATH
cd "$ROOT"
echo "=== stage 4 (resume): lake build Erdos647Sparse ==="
lake build Erdos647Sparse 2>&1 | grep -v "^trace"
echo BUILD_OK_1E13
