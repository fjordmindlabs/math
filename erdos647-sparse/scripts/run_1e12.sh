#!/bin/bash
# Erdős #647 — 10^12 extension, chained pipeline (Fjordmind Labs 2026-10-02).
# Stages: witness gen (1e11,1e12] -> coverage verify (1e7,1e12] -> Lean emit -> lake build.
set -euo pipefail
export PATH=$HOME/.elan/bin:$PATH
ROOT="${ERDOS647_SPARSE_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
cd "$ROOT/scripts"

echo "=== stage 1: witness generation (1e11, 1e12] ==="
python3 -u gen_witnesses_1e12.py
if [ -s failures_1e12.jsonl ]; then
  echo "ABORT: witness generation recorded failures"; exit 1
fi

echo "=== stage 2: coverage verification (1e7, 1e12] ==="
python3 -u verify_coverage_1e12.py

echo "=== stage 3: emit Lean chunks + driver + headline ==="
python3 -u emit_sparse_lean.py
# Headline.lean is hand-written and already lives in Erdos647Sparse/

echo "=== stage 4: lake build Erdos647Sparse ==="
cd "$ROOT"
lake build Erdos647Sparse 2>&1 | grep -v "^trace"
echo BUILD_OK_1E12
