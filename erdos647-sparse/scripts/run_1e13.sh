#!/bin/bash
# Erdős #647 — 10^13 extension, chained pipeline (Fjordmind Labs 2026-10-02).
# Stages: filter self-check -> witness gen (1e12,1e13] -> coverage verify -> Lean emit -> lake build.
set -euo pipefail
export PATH=$HOME/.elan/bin:$PATH
ROOT="${ERDOS647_SPARSE_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
cd "$ROOT/scripts"

echo "=== stage 0: filter self-check (masks vs survivor lists) ==="
python3 -u filter13.py

echo "=== stage 1: witness generation (1e12, 1e13] ==="
python3 -u gen_witnesses_1e13.py
if [ -s failures_1e13.jsonl ]; then
  echo "ABORT: witness generation recorded failures"; exit 1
fi

echo "=== stage 2: coverage verification (1e12, 1e13] ==="
python3 -u verify_coverage_1e13.py

echo "=== stage 3: emit Lean chunks + driver + root module ==="
python3 -u emit_sparse_lean13.py

echo "=== stage 4: lake build Erdos647Sparse ==="
cd "$ROOT"
lake build Erdos647Sparse 2>&1 | grep -v "^trace"
echo BUILD_OK_1E13
