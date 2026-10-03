# Provenance and trust status of the 10¹³ certificate

Companion to `../README.md` §6. States exactly what was run, where, and what
has and has not been independently re-checked. Format follows decanus's
`docs/RUNG_1E9.md`.

## Headline

`Erdos647Sparse.erdos647_no_solution_upto_1e13` (`Erdos647Sparse/Headline13.lean`),
Lean `leanprover/lean4:v4.30.0`, Mathlib `v4.30.0`
(`c5ea00351c28e24afc9f0f84379aa41082b1188f`), decanus `91d178dc36640fd1dec135ae6efa8fcefb0e0a21`.
`#print axioms` → `[propext, Classical.choice, Quot.sound]`.

## Machine

One desktop: Intel Core i7-7700K (4 cores / 8 threads, 4.2 GHz), 31 GB RAM,
Ubuntu Linux, 8-way `lake build`. No cloud, no GPU.

## Runs (all 2026-10-02 / 2026-10-03, UTC+2)

| Stage | What | Result |
|---|---|---|
| Rungs 1–2 (`Mod.lean`) | tactic proofs, ported from Lean 4.26 to 4.30 | builds in minutes; `mod2520_of_cand`, `mod360360_of_cand`, `mod_17_19_of_cand`, `sup_iff_cand` kernel-clean |
| 10¹¹ slice | 35,803 witnesses, 68 chunks | Python coverage verifier: 0 failures; `lake build` exit 0 (~25 min wall) |
| 10¹² extension | +316,000 witnesses (352,823 total over (10⁷, 10¹²]), 678 chunks of 4,096 grid indices, 8.3 MB | coverage verifier: "352823 witnesses cover every surviving grid point, j in [28, 2775002]"; `Build completed successfully (9194 jobs)`; ~3.5 CPU-h kernel time |
| Rung 4 (`Rung4*.lean`) | 22,916 class-kill certificates, 4,431 survivors, 28 chunks | builds in ~5 min; `classOk4_of_cand` kernel-clean |
| 10¹³ extension | 513,661 witnesses, 1,525 chunks of 16,384 grid indices, 12.3 MB | filter self-check: "4431 flat survivors, masks consistent over a full 215441-period"; coverage verifier OK over j ∈ [2775003, 27750027]; `Build completed successfully (10753 jobs)`; 48.8 CPU-h for the chunks |
| Axiom gate | `AxiomCheck.lean` (19 manifest theorems) + `AxiomAudit.lean` | PASS: 8,090 theorems across 2,242 `Erdos647Sparse` modules, all within the three allowed axioms (2026-10-03) |

## Incidents, stated plainly

- **Power-off mid-build.** The 10¹³ pipeline (stages 0–3 complete, stage 4
  running) lost its runner at ~02:21 on 2026-10-03. Lake's per-module caching
  meant only the unbuilt modules were rebuilt on resume; no chunk result was
  reused without its `.olean` being rebuilt from source by Lake's own
  dependency tracking.
- **Driver replaced.** The first 10¹³ driver (`Grid13.lean`) was a linear
  1,525-branch `by_cases` ladder; it reached 23 GB RSS after 21 minutes and was
  killed. It was replaced by a balanced binary-split tree driver
  (`scripts/emit_grid13_tree.py`), which elaborates in 56 s. The chunk
  certificates were not touched by this change.
- **Soundness fix during development.** decanus's `witnessOk` alone admits
  shift 0; `killOk` adds `0 < k` explicitly. Caught by an `omega`
  countermodel while proving `sparseOk_sound`, before any certificate was
  emitted.

## What has NOT been done

- No `lean4checker` replay of the `Erdos647Sparse` modules yet (decanus
  replays all of its modules; this is the next hardening step).
- No second from-source build on independent hardware.
- The full 10¹³ build does not run in CI (≈ 50 CPU-h). A 10¹¹-only CI target
  is planned.

Until those are done the trust status is the one decanus assigns its own 10⁹
rung: kernel-checked once, on one machine, with the axiom closure recorded.

## Data integrity

`../data/SHA256SUMS` lists the gzipped witness and certificate files. The
Lean chunk files in `Erdos647Sparse/Chunks*/` and `Rung4Chunks/` are
deterministic functions of those inputs via the scripts in `../scripts/`.
