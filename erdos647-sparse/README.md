# Erdős Problem 647: no solution in (24, 10¹³], kernel-checked

### Sieve-then-sparse-walk — modular rungs proved inside the kernel, one witness per surviving grid point

**Eero Tölö, Fjordmind Labs** — October 2026 — [github.com/fjordmindlabs/math](https://github.com/fjordmindlabs/math) · Apache-2.0

```lean
theorem Erdos647Sparse.erdos647_no_solution_upto_1e13 :
    ∀ n : ℕ, 24 < n → n ≤ 10000000000000 →
      ¬ (⨆ m : Fin n, ↑m + σ 0 m ≤ n + 2)
-- #print axioms: [propext, Classical.choice, Quot.sound]
```

Lean 4.30.0 / Mathlib v4.30.0, on top of [decanus](https://github.com/ibrahimmian36/decanus) (Mian–Siddique) at commit `91d178dc`. The problem itself remains open; this repository does not solve it. The Lean proofs and the Python pipeline here were produced by an AI agent under human direction (see §9).

**Contents:** `Erdos647Sparse/` (the library: ~1,900 lines hand-written Lean + ~21 MB generated certificates), `scripts/` (generators, verifiers, Lean emitters, run pipelines), `data/` (witness lists and rung-4 certificates, gzipped, with `SHA256SUMS`), `docs/` (scaling appendix, provenance), `arxiv/` (the note). Build and reproduction: §8.

## Abstract

Erdős Problem 647 asks whether any n > 24 satisfies max_{m<n}(m + τ(m)) ≤ n + 2, τ the divisor-count function. The strongest exclusion checked end to end by a proof kernel was (24, 10⁹] (Mian–Siddique, *decanus*, arXiv:2608.17880), obtained by a contiguous chain of 6.7 million factorization witnesses; the authors note the representation is at its ceiling (10¹⁰ would need ~45M witnesses and ~2 GB of source). We extend the kernel-checked exclusion to (24, 10¹³] — a 10,000× larger range — with a *smaller* certificate: 866,484 witnesses in about 21 MB of Lean source, less than decanus's in-repo 10⁸ certificate. The gain comes from doing the structural mathematics inside the kernel first: four modular "rungs", proved in Lean without `native_decide`, force 360360 ∣ n for every candidate n > 10⁵ and confine (n mod 17, 19, 23, 29) to 4,431 of 215,441 residue classes for n > 10¹¹. Only the surviving grid points then need a witness, and each needs just one. The composed theorem `Erdos647Sparse.erdos647_no_solution_upto_1e13` is stated in the formal-conjectures vocabulary and has axiom closure exactly {propext, Classical.choice, Quot.sound}: no `sorry`, no `native_decide`, no problem-specific axiom. The mathematics of the rungs is not new (it re-derives, kernel-clean, the residue reduction Hughes verified with `native_decide`); the contribution is the certificate architecture — modular rungs as certificate lists, a sparse grid walk with bitmask filters, and a balanced-tree driver — and an honest account of where it stops: a cost model (Appendix) puts the kernel-checked horizon of this family of methods at 10¹⁷–10¹⁸, not at the 10²² unverified GPU frontier.

## 1. Introduction

Let τ(m) be the number of divisors of m. Problem 647 (Erdős–Selfridge; Bloom's database) asks whether some n > 24 has max_{m<n}(m + τ(m)) ≤ n + 2. The condition holds at n = 24 and the problem is open. Computational exclusions reach 10¹² by direct sieve (Idén), ~6.2×10¹⁷ via Hughes's modular reduction (Lean + `native_decide`, residue classes searched on GPU), ~9.2×10¹⁸ (bentrd, C), and 10²² (GPU + CRT lifting, forum, Sep 2026). None of these is checked by a proof kernel. decanus [MS26] gave the first kernel-checked exclusion, at 10⁹, and framed the natural next step as "structure rather than length": certify the modular reduction inside the kernel so that only surviving classes need witnesses. This note does that.

**Result.** `theorem Erdos647Sparse.erdos647_no_solution_upto_1e13 : ∀ n : ℕ, 24 < n → n ≤ 10000000000000 → ¬ (⨆ m : Fin n, ↑m + σ 0 m ≤ n + 2)`, Lean 4.30.0 / Mathlib v4.30.0, `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The inner predicate is the one pinned by decanus from google-deepmind/formal-conjectures (`ErdosProblems/647.lean`, commit c252a41), so the theorem speaks the public formal statement's vocabulary and composes with the decanus rung theorems.

**Trust tier, stated plainly.** As in decanus, this is a certification result, not a computational record. Our range is nine orders of magnitude below the largest unverified computation. The claim is that every step from 24 to 10¹³ — the divisibility forced by each rung, the residue sieve, the divisor bound of every witness, the primality of every listed factor, and the gapless coverage of the surviving grid — is checked by the Lean kernel.

**Contributions.**
1. *Kernel-clean modular rungs* (§3): 2520 ∣ n (n > 1800), 360360 ∣ n (n > 10⁵), a 41-class survivor list for (n mod 17, n mod 19) (n > 2.5×10⁸), and a 4,431-class survivor list for (n mod 17, 19, 23, 29) (n > 10¹¹). The 41-class list is an independent re-derivation of Hughes's reduction mod 46189, with the `native_decide` trust removed.
2. *Rungs as certificate lists, not tactic proofs* (§3.3): the 22,916 class kills of rung 4 are data checked by chunked `decide`, with one generic soundness lemma — the same shape as the witness certificate.
3. *A sparse-walk certificate* (§4): one witness per surviving grid point; 866,484 witnesses over (10⁷, 10¹³] versus 6,685,922 for decanus's contiguous (24, 10⁹].
4. *Engineering for kernel scale* (§5): bitmask residue filters (`Nat.testBit`), chunk sizing from measured superlinear fuel cost, and a balanced binary-split driver after a linear `by_cases` ladder went quadratic at 1,525 chunks.
5. *A scaling analysis* (§7 and Appendix): what deeper rungs buy, a structural proof that no prime ≥ 17 can ever be fully forced by this method, and a cost curve to 10²².

## 2. Setting and the divisor-budget engine

Write `Cand n` for ∀ m < n, m + τ(m) ≤ n + 2. We proved `sup_iff_cand`: `Cand n ↔ (⨆ m : Fin n, ↑m + σ 0 m ≤ n + 2)` (forward via `le_ciSup` over the finite range; backward via `ciSup_le`, with the n = 0 case by `ciSup_of_empty`), so all internal work is on `Cand`.

The single engine behind every rung is the **divisor budget**: `Cand n` gives, for every shift k with 1 ≤ k ≤ n, τ(n − k) ≤ k + 2 (`cand_budget`). The lemma `two_mul_tau_le`: if m = d·t with d < t then τ(m) ≥ 2τ(d) (the divisors of d and their t-multiples are disjoint by size). Hence (`rung`): if `Cand n`, k ≥ 1, d ∣ n − k, and d² < n − k, then 2τ(d) ≤ k + 2. Contrapositive: a shift k whose forced divisor d of n − k has 2τ(d) ≥ k + 3 kills n. All rungs are tables of (residue class, shift k, forced divisor d) with 2τ(d) ≥ k + 3; all were enumerated and verified in Python first and then generated as Lean.

## 3. The modular rungs

(Numbering note: the internal development and file names count the bridge/port/sparse-walk step as "rung 3" and call the mod 23·29 sieve "rung 4" (`Rung4Checker.lean`, `classOk4`); the Appendix numbers rungs by sieve prime instead. This section uses the internal names so that identifiers match the code.)

### 3.1 Rung 1 — 2520 ∣ n for n > 1800 (`mod2520_of_cand`)
For each nonzero residue of n mod 8, 3, 9, 5, 7 there is a shift k ≤ 6 at which already-established divisibilities stack into d ∈ {4, 8, 6, 12, 9, 18, 5, 10, 15, 20, 7, 14, 21, 28, 35, 42} with 2τ(d) > k + 2. One uniform case per residue, closed by `omega`; the largest `decide` is τ(42) = 8.

### 3.2 Rung 2 — 360360 ∣ n (n > 10⁵) and 41 survivor classes mod 17·19 (n > 2.5×10⁸)
`mod360360_of_cand`: with 2520 ∣ n, every nonzero residue mod 11 and mod 13 dies at some shift k ≤ 24 where gcd(2520, k) stacks with 11 or 13 (tight cases: r = 7 mod 11 at k = 18, d = 198; r = 7 mod 13 at k = 20, d = 260; r = 11 mod 13 at k = 24, d = 312). `mod_17_19_of_cand`: mod 17 and mod 19 do not fully eliminate — per-prime survivors {0, 11, 13, 14, 15, 16} mod 17 and {0, 7, 11, 13, 14, 15, 16, 17} mod 19 (48 pairs), of which 7 die only to joint shifts where 17·19 = 323 enters one divisor (largest d = 14535 at k = 45). The 41 survivors equal, under the unit map 2520 ≡ 4 (mod 17), ≡ 12 (mod 19), the 41 classes of N = n/2520 mod 46189 in Hughes's reduction — derived independently, kernel-clean. The n > 2.5×10⁸ threshold is 14535² rounded; it is irrelevant in practice because the low range is covered by decanus's chain and by extra witnesses (§4).

### 3.3 Rung 4 — 4,431 survivor classes mod 17·19·23·29 (n > 10¹¹) (`classOk4_of_cand`)
Adding primes 23 and 29 jointly thins the 41 × 23 × 29 = 27,347 classes to 4,431 (6.17× sparsification; shifts k ≤ 90; largest forced stack d = 17·19·23·29 = 215,441, whence the 10¹¹ validity threshold via d² < n). The decisive design change from rung 2: **the kills are certificates, not tactic cases.** `classKillOk i k ps` stores, for flat class index i, a shift k and the full factorization ps of the forced stack `stackD i k` (reusing decanus's `witnessOk d 0 ps` and `witness_tau` for the τ(d) lower bound). `classKillOk_sound` discharges the CRT divisibility (`Nat.modEq_iff_dvd'` per prime + coprime stacking). A positional walker `rung4Walk` consumes the 27,347-class flat grid: each class is either the next kill certificate or the next listed survivor; `rung4Walk_sound` yields "every class is killed or in `rung4Survivors`". 28 chunks of 1,000 classes, one `decide` each (~5 s). A single rung-2-style tactic ladder over 27k cases would have been infeasible; the certificate form built in ~5 minutes.

Mod 23 alone and mod 29 alone give only 2.67× and 2.16×; the joint rung is worth building, and per the Appendix it is the last one that clearly is (rung 5 with 31 would add ~2.2× for 60k survivors).

## 4. The sparse-walk certificate

After the rungs, a candidate n in (10⁷, 10¹³] is a multiple of 360360 — write n = 360360·j, j ∈ [28, 27,750,027] — and, above the respective thresholds, lies in a surviving residue class. The **grid filter** encodes exactly which j still need killing:

- (10⁷, 10¹²]: `gridFilter n = (n ≤ 2.5×10⁸) || classOk n` — below the rung-2b threshold every multiple of 360360 needs a witness (932 extra points), above it only the 41 classes.
- (10¹², 10¹³]: `gridFilter13 n = (n ≤ 10¹¹) || (mask323.testBit (n % 323) && mask27k.testBit (flatIdx n))` — the 41-pair and 4,431-index survivor lists become two `Nat` bitmask literals, tested by `Nat.testBit` (GMP-accelerated shifts) instead of list scans. Bridge lemmas `mask323_complete`, `mask27k_covers`, and `gridFilter13_of_cand` tie the masks to the proved rung theorems, so the headline derives `gridFilter13 n = true` for any candidate.

**Kill witnesses.** A surviving grid point n is killed by one m = n − k with certified τ(m) ≥ k + 3, in decanus's witness format (maximal prime powers p < 1024, so primality of listed factors is eleven trial divisions). Because n is a multiple of 360360 its neighbourhood is divisor-rich, and kills are cheap: over (10⁹, 10¹¹] mean k = 1.9, median 1 (52.8 % of points die at k = 1, i.e. τ(n − 1) ≥ 4), max k = 16; over (10¹², 10¹³] mean k ≈ 1.75, max k = 8 on a sample. `killOk n k ps` adds the explicit conjunct 0 < k (decanus's `witnessOk` alone admits offset 0, which an omega countermodel caught during the soundness proof).

**The walker.** `sparseOk fuel j ws : Bool` steps j through a chunk's grid range; at each j it evaluates the filter and, if the point survives, requires the next witness in `ws` to kill exactly 360360·j, consuming it; non-surviving points consume nothing; leftovers are rejected. `sparseOk_sound`: a passing chunk kills every surviving grid point of its range. `sparseOk13` is the twin with the fast filter. Each chunk is a single `by decide`.

**Counts.** (10⁷, 10¹²]: 352,823 witnesses (including the 932 low-range points below 2.5×10⁸) in 678 chunks of 4,096 grid indices (8.3 MB). (10¹², 10¹³]: 513,661 witnesses in 1,525 chunks of 16,384 indices (12.3 MB). Rung-4 kill certificates: 22,916 (0.76 MB). Total ≈ 21 MB of generated Lean source for the whole 10¹³ result, against 38.5 MB for decanus's in-repo 10⁸ chain and ~260 MB for its 10⁹ release asset.

**Composition** (`Headline13.lean`): n ≤ 10⁷ by decanus `killed_upto` (the in-repo 31-chunk chain, imported from `Erdos647.Cert` — not `Erdos647.Headline`, which would drag in the 223-chunk 10⁸ certificate); 10⁷ < n ≤ 10¹² by `killed_of_cand_mid`; 10¹² < n ≤ 10¹³ by `killed_of_cand_high` (`gridFilter13_of_cand` + `mod360360_of_cand` + `grid13_killed`); each case closed through decanus's `not_sup_le_of_killed`.

## 5. Engineering at kernel scale

- **Chunk size from measured fuel cost.** Walk cost per grid point under the fast filter is ~2.5 ms isolated, ~7 ms under 8-way load (memory-bandwidth contention); fuel-recursion cost is superlinear in chunk length (~fuel^1.7: 16,384 → 43 s net, 32,768 → 139 s). CHUNK = 16,384 keeps chunks ~90 s median and totals 48.8 CPU-h for the 10¹³ walk.
- **Drivers must be trees.** The 678-branch linear `by_cases` ladder for 10¹² elaborated in 286 s. The 1,525-branch ladder for 10¹³ reached 23 GB RSS at 21 min and was killed: each negated branch hypothesis stays in the `omega` context, so the ladder is quadratic. The replacement driver emits one `span` lemma per chunk (direct `sparseOk13_sound` application, no omega) and an 11-level balanced binary merge tree whose nodes each do one `by_cases` with an O(1) context — 3,050 tiny theorems, 56 s. Rule of thumb: tree drivers from ~500 chunks upward.
- **Survivor membership in O(1).** Deciding membership of a flat index in a 4,431-element list inside the kernel (`inSub` Bool-subset decides) is quadratic and blew a 10-minute budget; `List.mem_append` embedding terms, generated per survivor, are O(1).
- **omega modulus blow-up.** omega's cost grows with the LCM of *all* mod facts in context; `(n − 45) = 14535·((n − 45)/14535)` proves in ~10 s from exactly {n%45 = 0, n%17 = 11, n%19 = 7} and times out at 8M heartbeats if `n % 2520 = 0` is also present. Pattern: derive per-case minimal facts, `clear` the rest.
- **Per-declaration heartbeats.** Hoist repeated `decide` facts (τ values) into top-level lemmas; `set_option maxRecDepth 40000` for `decide` on σ₀ d up to 14535. Both elaborator-side; `#print axioms` confirms kernel-cleanliness unaffected.
- **Generate, do not hand-write.** Every table (rung shifts/divisors, rung-4 kills, witnesses) is enumerated and verified in Python, then emitted as Lean; the Python verifier mirrors decanus `witnessOk` semantics line for line and the coverage verifier checks exact one-witness-per-surviving-point alignment over the whole grid before any Lean is emitted.
- **Resumability.** Generators checkpoint every 200 points; Lake caches chunk `.olean`s, so a power-off mid-build (which happened) cost only the unbuilt driver.

## 6. Verification record

| Check | 10¹¹ | 10¹² | 10¹³ |
|---|---|---|---|
| Python coverage verifier (exact alignment, every witness replayed) | 35,803 OK, 0 failures | 352,823 OK | 513,661 OK |
| Lean build (Lean 4.30.0, Mathlib v4.30.0) | exit 0, ~25 min wall | exit 0, 9,194 Lake jobs | exit 0, 10,753 Lake jobs |
| `#print axioms` on headline | {propext, Classical.choice, Quot.sound} | same | same |
| `sorry` / `native_decide` tokens in Erdos647Sparse sources | none (doc-comments only) | none | none |
| Kernel time | 68 chunks ≈ 35 s each | 678 chunks, median ~80 s, max 656 s | 1,525 chunks, median 92 s, 48.8 CPU-h |

**Axiom gate.** decanus's two-layer gate is mirrored for this library: `Erdos647Sparse/AxiomCheck.lean` is the curated manifest (19 `#print axioms` lines: rungs, bridge, checker soundness, rung-4 and grid theorems, both headlines), and `Erdos647Sparse/AxiomAudit.lean` walks every theorem in every `Erdos647Sparse.*` module from the compiled environment and refuses to compile if any depends on an axiom outside the allowed three. Run 2026-10-03: **AXIOM AUDIT: PASS: 8,090 theorems across 2,242 Erdos647Sparse modules**; all 19 manifest lines report exactly `[propext, Classical.choice, Quot.sound]`. `scripts/axiom_gate.sh` runs both layers.

**Not yet done:** (i) a `lean4checker` replay of the `Erdos647Sparse` modules (decanus replays all of its modules; expected ~2 h for the 2,200 chunk modules here); (ii) a second from-source build on different hardware. Every build so far ran once, on one 8-core desktop — the same trust status decanus assigns to its own 10⁹ rung. The full 10¹³ build is ~50 CPU-hours and is therefore not run in CI; the 10¹¹ slice (rungs 1–2 plus 68 chunks, ~40 CPU-minutes) is the natural CI target and is a planned addition.

## 7. Discussion: what this does and does not show

**Mathematical novelty: none claimed.** The modular ladder (Dutta–Alexeev), the shift condition (Kitamura), and the residue reduction (Hughes) are prior work; our rung 2 is Hughes's reduction with the `native_decide` trust removed, and rung 4 is its predictable extension. The problem is open; nothing here bears on whether a solution exists.

**Methodological point.** Certificate architecture, not compute, is what moved the kernel-checked frontier four orders of magnitude at *lower* artifact size. The two levers were (a) proving the structure inside the kernel so that the certificate only covers the sparse survivor grid, and (b) representing the structure itself (the rung kills) as data checked by `decide` with one generic soundness lemma, so a rung costs minutes rather than a week of tactic engineering.

**Limits, quantified (Appendix: `docs/scaling_appendix.md`).** (i) Each added sieve prime kills a shrinking share of remaining classes (63 % at 23 → 45 % at 41 → 22 % at 97), because a prime p helps only at shifts k ≡ c_p (mod p) with useful k ≲ 170. (ii) Full divisibility by any prime ≥ 17 is never forced: the class c₁₇ = 16, all other residues 0, survives at every threshold, since any matched stack divides k and the budget would need τ(d) > d/2, possible only for d ∈ {1, 2, 3, 4, 6}. So 360360 is the final forced modulus. (iii) Survivor counts grow 20–50× per rung; rung 7 (primes ≤ 41, ~2.5×10⁷ survivors) is the practical ceiling of an enumerable Lean sieve. (iv) The present walk visits every multiple of 360360 and so costs ∝ T regardless of sieve depth: it walls at 10¹⁴–10¹⁵. A *period walk* that steps only through surviving residues per period is the one structural lever left and buys about two decades: 10¹⁷–10¹⁸ at ~1 CPU-year. (v) With any certifiable sieve, 10²² needs ~7×10¹³ witnesses ≈ 10³–10⁴ CPU-years; even an uncertifiable 19-prime sieve leaves ≥ 4×10¹¹ witnesses. A kernel-checked 10²² therefore needs a different proof object — kills for whole arithmetic progressions at once, so that witness count stops being ∝ T — which is a research question, not an engineering one.

## 8. Reproduction

**Layout.** `Erdos647Sparse/Mod.lean` (rungs 1–2, bridge), `Rung4Checker.lean` + `Rung4Chunks/` (28 files) + `Rung4.lean` (rung 4), `Checker.lean` + `Chunks/` (678 files) + `Grid.lean` + `Headline.lean` (10¹²), `Masks13.lean` + `Checker13.lean` + `Chunks13/` (1,525 files) + `Grid13.lean` + `Headline13.lean` (10¹³), `AxiomCheck.lean` + `AxiomAudit.lean` (gate). Hand-written files carry a header saying so; generated files say which script emitted them.

**Build the Lean certificate** (Lean 4.30.0 via `elan`; decanus and Mathlib are fetched by Lake from the pinned revisions in `lakefile.toml` / `lake-manifest.json`):

```sh
cd erdos647-sparse
lake exe cache get          # Mathlib oleans (via the decanus dependency)
lake build Erdos647Sparse   # ≈ 50 CPU-hours for the 10^13 chunks; ~1 GB RAM per parallel job
bash scripts/axiom_gate.sh  # manifest + whole-library audit
```

`lake build Erdos647Sparse.Headline` builds the 10¹² result only (678 chunks, ~3.5 CPU-h); `lake build Erdos647Sparse.Mod` builds just the rungs (minutes).

**Regenerate the certificates** (Python 3 + numpy; the Lean emitters write into `Erdos647Sparse/`):

```sh
cd erdos647-sparse
for f in data/*.gz; do gunzip -c "$f" > "scripts/$(basename "${f%.gz}")"; done   # inputs next to the scripts
cd scripts
python3 gen_rung4_certs.py && python3 emit_rung4_lean.py     # rung 4: kills + survivors → Rung4Chunks/, Rung4.lean
python3 gen_witnesses_rung3.py && python3 gen_witnesses_low.py && python3 gen_witnesses_1e12.py
python3 verify_coverage_1e12.py && python3 emit_sparse_lean.py                    # 10^12: Chunks/, Grid.lean
python3 filter13.py && python3 gen_witnesses_1e13.py && python3 verify_coverage_1e13.py
python3 emit_sparse_lean13.py && python3 emit_grid13_tree.py                      # 10^13: Chunks13/, Grid13.lean
```

The generators are resumable (progress files every 200 points) and their outputs are byte-identical to `data/` (compare against `data/SHA256SUMS` after decompression). `run_1e12.sh` / `run_1e13.sh` chain the stages. The scaling appendix (`docs/scaling_appendix.md`) is reproduced by `rung_scaling_extrapolation.py` then `rung_scaling_costmodel.py`.

## 9. Credit and provenance

Built on decanus (Ibrahim Mian & Shayaan Siddique, Apache-2.0, [arXiv:2608.17880](https://arxiv.org/abs/2608.17880)): witness format, `TauLower`/`Chain`/`Bridge` soundness, the 10⁷ chain, and the pinned formal-conjectures statement. Structural mathematics: Dutta–Alexeev, Kitamura, Hughes (erdosproblems.com forum thread 647). Reference computations: Idén (10¹²), Hughes (6.2×10¹⁷), bentrd (9.2×10¹⁸), veljjanoski (10²²).

**AI authorship.** The Lean proofs, the Python generators and verifiers, and the first draft of this writeup were produced by an AI agent operated by Fjordmind Labs, working with compiler feedback under human direction; the human author set the goals, reviewed the results, and is responsible for the claims. Nothing in the trust argument depends on how the proofs were written: the Lean kernel checks them the same way.

Build and verification log: `docs/PROVENANCE.md`.
