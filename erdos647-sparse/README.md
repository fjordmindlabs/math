# A kernel-checked exclusion for Erdős Problem 647 to 10¹³

### via a modular sieve proved inside the kernel and a sparse witness walk

**Eero Tölö, Fjordmind Labs, Oslo, Norway** — eero@fjordmind.no — October 2026 — [github.com/fjordmindlabs/math](https://github.com/fjordmindlabs/math) · Apache-2.0

```lean
theorem Erdos647Sparse.erdos647_no_solution_upto_1e13 :
    ∀ n : ℕ, 24 < n → n ≤ 10000000000000 →
      ¬ (⨆ m : Fin n, ↑m + σ 0 m ≤ n + 2)
-- #print axioms: [propext, Classical.choice, Quot.sound]
```

Lean 4.30.0 / Mathlib v4.30.0, on top of [decanus](https://github.com/ibrahimmian36/decanus) (Mian–Siddique) at commit `91d178dc`. The problem itself remains open; this repository does not solve it. The Lean proofs and the Python pipeline here were written by an AI coding agent under human direction (§10).

**Contents:** `Erdos647Sparse/` (the library: ~1,900 lines hand-written Lean + ~21 MB generated certificates), `scripts/` (generators, verifiers, Lean emitters, run pipelines), `data/` (witness lists and stage-4 certificates, gzipped, with `SHA256SUMS`), `docs/` (scaling appendix, provenance), `draft_note/` (the writeup, [PDF](draft_note/erdos647_sparse.pdf) and LaTeX source; this README follows it). Build and reproduction: §9.

## Abstract

Erdős Problem 647 asks whether any n > 24 satisfies max_{m<n}(m + τ(m)) ≤ n + 2, where τ is the divisor-count function. The largest range excluded end to end by a proof kernel was (24, 10⁹] (Mian–Siddique, *decanus*, arXiv:2608.17880), via a contiguous chain of 6.7 million factorization witnesses that the authors describe as at the ceiling of the representation. We extend the kernel-checked exclusion to (24, 10¹³], a 10,000× larger range, with a *smaller* certificate: 866,484 witnesses in about 21 MB of Lean source. The gain comes from proving the structural reduction inside the kernel first: four modular sieve stages, proved in Lean 4 and checked by its kernel with no appeal to compiled-code evaluation, force 360360 ∣ n for every candidate n > 10⁵ and confine (n mod 17, 19, 23, 29) to 4,431 of 215,441 residue classes for n > 10¹¹. Only the surviving grid points then need a witness, and each needs one. The resulting theorem is stated in the vocabulary of the public formal statement and depends on nothing beyond the three standard axioms of Lean's mathematical library. No new mathematics is claimed: the sieve stages re-derive, fully kernel-checked, a residue reduction that had previously been verified only by trusting compiled code. The contribution is the certificate architecture, together with a cost model showing where this family of methods stops: a kernel-checked horizon of 10¹⁷–10¹⁸, not the 10²² unverified GPU frontier.

## 1. Introduction

Let τ(m) denote the number of divisors of m. Problem 647 in Bloom's database of Erdős problems (Erdős–Selfridge) asks whether some n > 24 satisfies max_{m<n}(m + τ(m)) ≤ n + 2. The condition holds at n = 24 and the problem is open. Computational exclusions reach 10¹² by direct sieve (Idén), about 6.2×10¹⁷ via Hughes's modular reduction (Lean with compiled-code evaluation, residue classes searched on a GPU), about 9.2×10¹⁸ (bentrd), and 10²² (GPU with CRT lifting, 2026). None of these is checked by a proof kernel. Mian and Siddique gave the first kernel-checked exclusion, at 10⁹, and framed the natural next step as "structure rather than length": certify the modular reduction inside the kernel so that only surviving classes need witnesses. This work aims to do that.

**Reading the Lean vocabulary.** The proofs are written in the Lean 4 proof assistant on top of its mathematical library Mathlib. A few conventions recur below.

- *Kernel.* Lean separates proof *search* (tactics, automation, user code) from proof *checking*. Every proof, however it was found, is re-checked by a small trusted core, the kernel. "Kernel-checked" means exactly this: the only thing one has to trust is the kernel.
- *Typewriter names.* A name in code font, such as `sup_iff_cand` or `killOk`, is the identifier of a definition or theorem in the Lean source. Each is given in words at first use; the name is there so that a reader can locate the exact statement in the repository.
- *Axioms.* Lean can print the complete list of axioms a theorem depends on (`#print axioms`). Ordinary classical mathematics in Mathlib rests on three: propositional extensionality (`propext`), the axiom of choice (`Classical.choice`) and quotient soundness (`Quot.sound`). "Three standard axioms" and "kernel-clean" both mean that a theorem's list is exactly these three and nothing else.
- *`native_decide`.* Lean offers a shortcut that evaluates a decidable statement by compiling it to native machine code and trusting the result. It adds an extra axiom ("trust the compiler") to the theorem's list, so the kernel is no longer the only trusted component. It is never used here; "compiled-code trust" below means a proof that does use it. The alternative, `decide`, has the kernel itself carry out the computation, which is slower but fully checked.
- *Tactics.* `omega` is Lean's decision procedure for linear integer arithmetic; `by_cases` is a case split on a proposition. Both produce ordinary kernel-checked proofs. `sorry` is a placeholder for a missing proof; a development with none is complete.
- *Certificates.* A *witness* or *certificate* is data (here: a number, a shift, and a factorization) together with a once-proved *soundness lemma* saying "if this data passes a Boolean check, the mathematical statement holds". The kernel then verifies each item by running the check with `decide`. "Witness" is used in its usual logical sense: an explicit object that establishes an existential statement, here the m < n that shows n is not a solution.
- *Source vocabulary.* The Lean source, following decanus, calls an excluded number "killed" and calls each modular stage a "rung". In prose this document says *excluded* and *stage*; decanus itself uses "rung" for its range tiers (10⁷, 10⁸, 10⁹), so the word would otherwise carry two meanings. Identifiers such as `killOk` and `Rung4` are quoted as they are in the repository.

**Result.** `erdos647_no_solution_upto_1e13 : ∀ n : ℕ, 24 < n → n ≤ 10¹³ → ¬ (⨆ m : Fin n, m + σ₀(m) ≤ n + 2)`. Here ⨆ is Lean's notation for a supremum over an index type, `Fin n` is the type {0, …, n−1} and σ₀ is Mathlib's name for the divisor-count function τ (Lean writes function application without parentheses, `σ 0 m`; the prose writes σ₀(m) and τ(m) throughout). The inner proposition is therefore the literal max_{m<n}(m + τ(m)) ≤ n + 2, and the theorem says that no n in (24, 10¹³] satisfies it. The Lean source states the bound as the literal `10000000000000`; `Erdos647Sparse/Headline13.lean` has the exact text. Lean 4.30.0 / Mathlib v4.30.0; the axiom report lists exactly the three standard axioms. The inner predicate is the one pinned by decanus from google-deepmind/formal-conjectures (`ErdosProblems/647.lean`, commit `c252a41`), so the theorem speaks the public formal statement's vocabulary and composes with the decanus range theorems.

**Trust tier.** As in decanus, this is a certification result, not a computational record; the range is nine orders of magnitude below the largest unverified computation. The claim is that every step from 24 to 10¹³ — the divisibility forced by each sieve stage, the residue classes removed, the divisor bound of every witness, the primality of every listed factor, and the gapless coverage of the surviving grid — is checked by the Lean kernel.

**Contributions.**
1. *A kernel-clean modular sieve* (§3): 2520 ∣ n (n > 1800), 360360 ∣ n (n > 10⁵), a 41-class survivor list for (n mod 17, n mod 19) (n > 2.5×10⁸), and a 4,431-class survivor list for (n mod 17, 19, 23, 29) (n > 10¹¹). The 41-class list is an independent re-derivation of Hughes's reduction mod 46189 with the compiled-code trust removed.
2. *Sieve stages as certificate lists, not tactic proofs* (§3.3): the 22,916 class exclusions of the fourth stage are data checked by chunked kernel computation under one generic soundness lemma, the same shape as the witness certificate.
3. *A sparse-walk certificate* (§4): one witness per surviving grid point; 866,484 witnesses over (10⁷, 10¹³] versus 6,685,922 for decanus's contiguous (24, 10⁹].
4. *Engineering for kernel scale* (§5): bitmask residue filters, chunk sizing from measured superlinear fuel cost, and a balanced binary-split driver after a linear case-split ladder went quadratic at 1,525 chunks.
5. *A scaling analysis* (§7 and `docs/scaling_appendix.md`): what deeper sieve stages buy, a structural argument that no prime ≥ 17 is ever fully forced by this method, and a cost curve to 10²²; and an outline, not a result, of how the same method would reach about 10¹⁸ (§8).

## 2. The divisor-budget engine

For n ∈ ℕ write Cand(n), "n is a candidate", for the proposition ∀ m < n, m + τ(m) ≤ n + 2: n satisfies the condition of Problem 647. The problem asks whether Cand(n) holds for some n > 24, and excluding a range means proving ¬Cand(n) on it. A bridge lemma (`sup_iff_cand`) shows that Cand(n) is equivalent to the supremum form used in the public statement, ⨆_{m : Fin n} (m + σ₀(m)) ≤ n + 2; both directions are routine facts about the supremum of a finite range (forward via `le_ciSup`, backward via `ciSup_le`), with n = 0 handled separately because the range is then empty (`ciSup_of_empty`). All internal work is on Cand.

The single engine behind every stage is the **divisor budget**: Cand(n) gives, for every shift 1 ≤ k ≤ n, τ(n − k) ≤ k + 2 (`cand_budget`). If m = d·t with d < t then τ(m) ≥ 2τ(d), since the divisors of d and their t-multiples are disjoint by size (`two_mul_tau_le`). Hence (lemma `rung`): if Cand(n), k ≥ 1, d ∣ n − k and d² < n − k, then 2τ(d) ≤ k + 2. Contrapositively, a shift k whose forced divisor d of n − k satisfies 2τ(d) ≥ k + 3 excludes n. Every stage is a table of (residue class, shift k, forced divisor d) with 2τ(d) ≥ k + 3; all tables were enumerated and verified in Python first and then generated as Lean.

## 3. The modular sieve

(Numbering note: the source counts the bridge/port/sparse-walk step as "rung 3" and calls the mod 23·29 sieve "rung 4" (`Rung4Checker.lean`, `classOk4`); `docs/scaling_appendix.md` numbers stages by sieve prime instead. This section keeps the source numbering so that identifiers match the code.)

### 3.1 Stage 1 — 2520 ∣ n for n > 1800 (`mod2520_of_cand`)
For each nonzero residue of n modulo 8, 3, 9, 5, 7 there is a shift k ≤ 6 at which already-established divisibilities stack into some d ∈ {4, 8, 6, 12, 9, 18, 5, 10, 15, 20, 7, 14, 21, 28, 35, 42} with 2τ(d) > k + 2. One uniform case per residue, closed by `omega`; the largest value the kernel has to compute is τ(42) = 8.

### 3.2 Stage 2 — 360360 ∣ n (n > 10⁵) and 41 survivor classes mod 17·19 (n > 2.5×10⁸)
`mod360360_of_cand`: with 2520 ∣ n, every nonzero residue mod 11 and mod 13 is excluded at some shift k ≤ 24 where gcd(2520, k) stacks with 11 or 13 (tight cases: r ≡ 7 mod 11 at k = 18, d = 198; r ≡ 7 mod 13 at k = 20, d = 260; r ≡ 11 mod 13 at k = 24, d = 312). `mod_17_19_of_cand`: mod 17 and mod 19 do not fully eliminate; per-prime survivors are {0, 11, 13, 14, 15, 16} mod 17 and {0, 7, 11, 13, 14, 15, 16, 17} mod 19 (48 pairs), of which 7 are excluded only by joint shifts where 17·19 = 323 enters one divisor (largest d = 14535 at k = 45). The 41 survivors equal, under 2520 ≡ 4 (mod 17), ≡ 12 (mod 19), the 41 classes of N = n/2520 mod 46189 in Hughes's reduction, derived independently and kernel-clean. The threshold 2.5×10⁸ is 14535² rounded; it is irrelevant in practice because the low range is covered by decanus's chain and by extra witnesses (§4).

### 3.3 Stage 4 — 4,431 survivor classes mod 17·19·23·29 (n > 10¹¹) (`classOk4_of_cand`)
Adding 23 and 29 jointly thins the 41 × 23 × 29 = 27,347 classes to 4,431 (a 6.17× sparsification; shifts k ≤ 90; the largest forced stack is 17·19·23·29 = 215,441, whence the 10¹¹ validity threshold via d² < n). The decisive design change from stage 2: **the exclusions are certificates, not tactic cases.** `classKillOk i k ps` stores, for flat class index i, a shift k and the full factorization ps of the forced stack `stackD i k`; the lower bound on τ(d) is read off the factorization by decanus's witness checker (`witnessOk d 0 ps`, `witness_tau`). `classKillOk_sound` discharges the divisibility by the Chinese remainder theorem (`Nat.modEq_iff_dvd'` per prime, combined over coprime moduli). A positional walker `rung4Walk` consumes the 27,347-class flat grid: each class is either the next exclusion certificate or the next listed survivor; `rung4Walk_sound` yields "every class is excluded or in `rung4Survivors`". Twenty-eight chunks of 1,000 classes, one `decide` each (≈ 5 s). A stage-2-style tactic ladder over 27k cases would have been infeasible; the certificate form built in about five minutes.

Mod 23 alone and mod 29 alone give only 2.67× and 2.16×; the joint stage is worth building and, per §7, is the last one that clearly is (stage 5 with 31 would add ~2.2× for 60k survivors).

## 4. The sparse-walk certificate

After the sieve, a candidate n ∈ (10⁷, 10¹³] is a multiple of 360360, say n = 360360·j with j ∈ [28, 27,750,027], and above the respective thresholds lies in a surviving residue class. A Boolean **grid filter** encodes which j still need a witness:

- (10⁷, 10¹²]: `gridFilter n = (n ≤ 2.5×10⁸) || classOk n` — below the stage-2 threshold every multiple of 360360 needs a witness (932 extra points), above it only the 41 classes.
- (10¹², 10¹³]: `gridFilter13 n = (n ≤ 10¹¹) || (mask323.testBit (n % 323) && mask27k.testBit (flatIdx n))` — the 41-pair and 4,431-index survivor lists are stored as two natural-number bitmask literals and membership is a single `Nat.testBit` (GMP-accelerated) instead of a list scan. Bridge lemmas `mask323_complete`, `mask27k_covers` and `gridFilter13_of_cand` tie the masks to the proved stage theorems, so the headline derives `gridFilter13 n = true` for any candidate.

**Witnesses.** A surviving grid point n is excluded by one m = n − k with certified τ(m) ≥ k + 3, in decanus's witness format (maximal prime powers p < 1024, so primality of listed factors is eleven trial divisions). Because n is a multiple of 360360 its neighbourhood is divisor-rich and witnesses are cheap to find: over (10⁹, 10¹¹] the mean shift is k = 1.9, the median 1 (52.8 % of points are excluded at k = 1, i.e. τ(n − 1) ≥ 4), the maximum 16; over (10¹², 10¹³] the mean is ≈ 1.75 and the maximum 8 on a sample. The exclusion check `killOk n k ps` adds to decanus's witness check the explicit conjunct 0 < k: `witnessOk` alone admits shift 0, which an `omega` countermodel caught during the soundness proof.

**The walker.** `sparseOk fuel j ws : Bool` steps j through a chunk's grid range; at each j it evaluates the filter and, if the point survives, requires the next witness in `ws` to exclude exactly 360360·j, consuming it; non-surviving points consume nothing; leftovers are rejected. `sparseOk_sound`: a passing chunk excludes every surviving grid point of its range. `sparseOk13` is the twin with the fast filter. Each chunk is a single `by decide`.

**Counts.** (10⁷, 10¹²]: 352,823 witnesses (including the 932 low-range points below 2.5×10⁸) in 678 chunks of 4,096 grid indices (8.3 MB). (10¹², 10¹³]: 513,661 witnesses in 1,525 chunks of 16,384 indices (12.3 MB). Stage-4 exclusion certificates: 22,916 (0.76 MB). Total ≈ 21 MB of generated Lean source for the whole 10¹³ result, against 38.5 MB for decanus's in-repository 10⁸ chain and ≈ 260 MB for its 10⁹ release asset.

**Composition** (`Headline13.lean`): n ≤ 10⁷ by decanus's contiguous chain theorem `killed_upto` (the in-repository 31-chunk chain, imported from `Erdos647.Cert`, not `Erdos647.Headline`, which would drag in the 223-chunk 10⁸ certificate); 10⁷ < n ≤ 10¹² by `killed_of_cand_mid`; 10¹² < n ≤ 10¹³ by `killed_of_cand_high` (`gridFilter13_of_cand` + `mod360360_of_cand` + `grid13_killed`); each case is then carried back to the supremum form of the public statement by decanus's bridge lemma `not_sup_le_of_killed`.

## 5. Engineering at kernel scale

- **Chunk size from measured fuel cost.** Walk cost per grid point under the fast filter is ≈ 2.5 ms isolated and ≈ 7 ms under 8-way load (memory-bandwidth contention); the cost of the fuel-bounded recursion is superlinear in chunk length (~fuel^1.7: 16,384 → 43 s net, 32,768 → 139 s). Chunks of 16,384 keep the median at ≈ 90 s and the 10¹³ walk at 48.8 CPU-hours.
- **Drivers must be trees.** The theorem that glues the chunks together must split the range into cases. The 678-branch linear `by_cases` ladder for 10¹² elaborated in 286 s. The 1,525-branch ladder for 10¹³ reached 23 GB RSS at 21 minutes and was stopped: each negated branch hypothesis stays in the `omega` context, so the ladder is quadratic. The replacement driver (`scripts/emit_grid13_tree.py`) emits one `span` lemma per chunk (direct `sparseOk13_sound` application, no omega) and an 11-level balanced binary merge tree whose nodes each do one `by_cases` with O(1) context: 3,050 small theorems, 56 s. Rule of thumb: tree drivers from ~500 chunks upward.
- **Survivor membership in O(1).** Deciding membership of a flat index in a 4,431-element list inside the kernel via Boolean sublist checks (`inSub`) is quadratic and exceeded a ten-minute budget; a per-survivor `List.mem_append` proof term that points directly at the element's position is O(1).
- **Modulus blow-up in linear arithmetic.** The cost of `omega` grows with the lcm of all modular facts in context; (n − 45) = 14535·((n − 45)/14535) proves in ≈ 10 s from exactly {n % 45 = 0, n % 17 = 11, n % 19 = 7} and times out at 8M heartbeats if n % 2520 = 0 is also present. Derive per-case minimal facts and `clear` the rest.
- **Per-declaration heartbeats.** Hoist repeated `decide` facts (τ values) into top-level lemmas; `set_option maxRecDepth 40000` for `decide` on σ₀(d) up to 14535. Both are elaborator-side; `#print axioms` confirms kernel-cleanliness is unaffected.
- **Generate, do not hand-write.** Every table (stage shifts/divisors, stage-4 exclusions, witnesses) is enumerated and verified in Python, then emitted as Lean; the Python verifier mirrors decanus's `witnessOk` semantics line for line, and the coverage verifier checks exact one-witness-per-surviving-point alignment over the whole grid before any Lean is emitted.
- **Resumability.** Generators checkpoint every 200 points; Lake caches chunk `.olean`s, so a power-off mid-build (which happened) cost only the unbuilt driver.

## 6. Verification record

| Check | 10¹¹ | 10¹² | 10¹³ |
|---|---|---|---|
| Python coverage verifier (exact alignment, every witness replayed) | 35,803 OK, 0 failures | 352,823 OK | 513,661 OK |
| Lean build (Lean 4.30.0, Mathlib v4.30.0) | exit 0, ~25 min wall | exit 0, 9,194 Lake jobs | exit 0, 10,753 Lake jobs |
| `#print axioms` on headline | {propext, Classical.choice, Quot.sound} | same | same |
| `sorry` / `native_decide` tokens in Erdos647Sparse sources | none (doc-comments only) | none | none |
| Kernel time | 68 chunks ≈ 35 s each | 678 chunks, median ~80 s, max 656 s | 1,525 chunks, median 92 s, 48.8 CPU-h |

**Axiom gate.** decanus's two-layer gate is mirrored for this library: `Erdos647Sparse/AxiomCheck.lean` is the curated manifest (19 `#print axioms` lines: stages, bridge, checker soundness, stage-4 and grid theorems, both headlines), and `Erdos647Sparse/AxiomAudit.lean` walks every theorem in every `Erdos647Sparse.*` module from the compiled environment and refuses to compile if any depends on an axiom outside the allowed three. Run 2026-10-03: **AXIOM AUDIT: PASS: 8,090 theorems across 2,242 Erdos647Sparse modules**; all 19 manifest lines report exactly `[propext, Classical.choice, Quot.sound]`. `scripts/axiom_gate.sh` runs both layers.

**Not yet done:** (i) a `lean4checker` replay of the `Erdos647Sparse` modules (decanus replays all of its modules; expected ~2 h for the 2,200 chunk modules here); (ii) an independent external implementation of the kernel check; (iii) a second from-source build on different hardware. Every build so far ran once, on one 8-core desktop, the trust status decanus assigns its own 10⁹ range tier. The full 10¹³ build is ~50 CPU-hours and is therefore not run in CI; the 10¹¹ slice (stages 1–2 plus 68 chunks, ~40 CPU-minutes) is the natural CI target and is a planned addition.

## 7. What this does and does not show

**Mathematical novelty: none claimed.** The modular ladder (Dutta–Alexeev), the shift condition (Kitamura) and the residue reduction (Hughes) are prior work; stage 2 is Hughes's reduction with the compiled-code trust removed, and stage 4 is its predictable extension. The problem is open and nothing here bears on whether a solution exists.

**Why the small solutions are small.** The complete solution set below 10¹³ is {2, 3, 4, 5, 6, 8, 10, 12, 24}. Two observations explain it and locate the difficulty. First, for a divisor k of n we have n − k = k·(n/k − 1), so τ(n−k) = 2τ(k) exactly when n/k − 1 is prime, and 2τ(k) ≤ k + 2 for every k ≥ 1. The numbers 2, 4, 6, 8, 12, 24 are precisely the n for which n/d − 1 is prime or 1 for every proper divisor d (for 24: 23, 11, 7, 5, 3, 2, 1); we checked to 10⁵ and 24 is the last such n. These are the pure form of the one residue class the budget engine can never kill (item 2 below): n divisible by every small k, with the first cofactors prime. By the Hardy–Littlewood prime-tuples heuristic that head pattern recurs infinitely often, so the first few shifts can never supply a proof. Second, a violation at shift k needs an m = n − k with τ(m) ≥ k + 3; below 24 no integer has τ ≥ 7, so only shifts k ≤ 3 can ever bite, and the small solutions are simply the n that dodge those three. From 24 onward the divisor-rich integers cover one another in a chain (24 reaches 30, 28 reaches 32, 30 reaches 36, 36 reaches 43, …), and the witness walk of §4 is that chain verified to 10¹³. A solution is a break in the chain; the small ones lie before it starts. The cousin problem "every totative of n is prime" has the almost identical solution set {2, 3, 4, 6, 8, 12, 18, 24, 30} and is provably finite by Bonse's inequality, because the primorial outgrows n by a power. Here the analogous margin is only logarithmic (about 3 log n expected violating shifts per surviving n), which is why no elementary growth argument is in sight.

**Methodological point.** Certificate architecture, not compute, moved the kernel-checked frontier four orders of magnitude at lower artifact size. The two levers were (a) proving the structure inside the kernel so that the certificate covers only the sparse survivor grid, and (b) representing the structure itself (the stage exclusions) as data checked by kernel computation under one generic soundness lemma, so that a stage costs minutes rather than a week of tactic engineering.

**Limits, quantified** (`docs/scaling_appendix.md`: a sweep of the divisor-budget engine over sieve primes 17 to 97 and validity thresholds 10¹¹ to 10²¹, exact enumeration to 3×10⁶ classes, Monte Carlo beyond).
1. Each added sieve prime removes a shrinking share of the remaining classes: 63 % at 23, 56 % at 31, 48 % at 37, 44 % at 41, 35 % at 61, 22 % at 97. A prime p helps only at shifts k ≡ c_p (mod p), and useful k stay below about 170.
2. *Full divisibility by any prime p ≥ 17 is never forced.* The class c₁₇ = 16, all other residues 0, survives at every threshold: in it a sieve prime q ≠ 17 matches shift k only if q ∣ k, so the matched stack divides k, d ≤ k, and the budget 2τ(d) ≥ k + 3 would need τ(d) > d/2, possible only for d ∈ {1, 2, 3, 4, 6}, none reachable with k ≡ 16 (mod 17). Hence 360360 is the final forced modulus; all further sieving is residue thinning, never grid coarsening.
3. Survivor-class counts grow 20–50× per stage (4.4×10³ at stage 4, 2.6×10⁷ at stage 7 with primes ≤ 41); a kernel-checked literal above ~10⁸ entries is outside anything built so far, so stage 7 is the practical ceiling of an enumerable sieve, with density floor f ≈ 2.5×10⁻³.
4. The present walk visits every multiple of 360360 and costs ∝ T regardless of sieve depth; it walls at 10¹⁴–10¹⁵. A *period walk* that steps only through surviving residues per period is the one structural lever left and buys about two decades: 10¹⁷–10¹⁸ at roughly one CPU-year (§8).
5. With any certifiable sieve, 10²² needs ≈ 7×10¹³ witnesses, i.e. 10³–10⁴ CPU-years; even an uncertifiable 19-prime sieve leaves ≥ 4×10¹¹ witnesses. A kernel-checked 10²² therefore needs a different proof object — exclusions of whole arithmetic progressions at once, so that the witness count stops being ∝ T — which is a research question, not an engineering one.

## 8. Outline: a kernel-checked 10¹⁸

Nothing beyond 10¹³ has been built or verified. This section records how the method would be taken to about 10¹⁸, so that item 4 of §7 is concrete. The figures are cost-model estimates using the constants measured in §5; none of them is a result.

**Period walk.** Fix a sieve stage with prime set P and let M = 360360·∏_{p∈P} p. The stage theorem, in the certificate form of §3.3, lists the S surviving residues r₁ < … < r_S of n/360360 modulo ∏ p above its validity threshold. A walker then visits, in each period q, only the S points n = Mq + 360360·r_i, and the stage theorem supplies the exclusion of every skipped point. Kernel cost becomes proportional to the number of survivors instead of to the range T. Stage 6 (primes ≤ 37) has M ≈ 8.9×10¹³ and S ≈ 1.15×10⁶, with 1.1×10⁶ exclusion certificates (about 1.5 CPU-hours at the stage-4 rate) and a survivor literal 260× the size of stage 4's; it is the realistic target. Stage 7 (primes ≤ 41, M ≈ 3.7×10¹⁵, S ≈ 2.6×10⁷) is the ceiling of §7 item 3, and its survivor literal would be larger than anything kernel-checked so far.

**Witnesses without witness data.** At 10¹⁸ the certificate covers 7×10⁹ to 1.3×10¹⁰ surviving points. Stored in the present format (about 24 bytes per witness) that is of the order of 10² GB of Lean source, which no toolchain will load; the witness data, not kernel time, is the first wall. The remedy is to move the search into the checker: for each surviving point the kernel itself trial-divides n − k for k = 1, 2, … by the primes below 1024 and stops as soon as the prime powers found certify τ(n − k) ≥ k + 3. This is the check `killOk` already performs, with the factorization found rather than supplied, so the soundness lemma is unchanged and the per-chunk certificate shrinks to a range of period indices. Since shifts average 1.75, the search costs a few hundred big-number divisions per point, expected to be of the order of the present per-point walk cost; this has not been measured.

**Estimates** (at 0.5–2.5 ms of kernel time per surviving point):

| T | stage | surviving points | kernel CPU time | chunks of 16,384 |
|---|---|---|---|---|
| 10¹⁷ | 6 | 1.3×10⁹ | 7–38 CPU-days | 8×10⁴ |
| 10¹⁷ | 7 | 6.9×10⁸ | 4–20 CPU-days | 4×10⁴ |
| 10¹⁸ | 6 | 1.3×10¹⁰ | 0.2–1.0 CPU-years | 8×10⁵ |
| 10¹⁸ | 7 | 6.9×10⁹ | 41 CPU-days–0.55 CPU-years | 4×10⁵ |

Parallel hardware divides wall time, not CPU time. The chunk counts are 40–500× the 1,525 modules of the 10¹³ build and are themselves an untested build-system scale; a 20-level binary merge tree replaces the 11-level one of §5.

**Where it stops.** No table of residue-class exclusions, however deep, bears on the conjecture itself. For every modulus L the class n ≡ 0 (mod L) survives: at shift k the forced divisor is gcd(L, k), which divides k, so 2τ(gcd(L, k)) ≤ 2τ(k) ≤ k + 2 < k + 3 for every k ≥ 1 (every divisor of k other than k is at most k/2, so τ(k) ≤ k/2 + 1). The method therefore excludes finite ranges only. Beyond about 10¹⁸ the witness count outgrows kernel budgets (§7 item 5), and a proof for all n would need analytic input of a kind not currently available.

## 9. Reproduction

**Layout.** `Erdos647Sparse/Mod.lean` (stages 1–2, bridge), `Rung4Checker.lean` + `Rung4Chunks/` (28 files) + `Rung4.lean` (stage 4), `Checker.lean` + `Chunks/` (678 files) + `Grid.lean` + `Headline.lean` (10¹²), `Masks13.lean` + `Checker13.lean` + `Chunks13/` (1,525 files) + `Grid13.lean` + `Headline13.lean` (10¹³), `AxiomCheck.lean` + `AxiomAudit.lean` (gate). Hand-written files carry a header saying so; generated files say which script emitted them.

**Build the Lean certificate** (Lean 4.30.0 via `elan`; decanus and Mathlib are fetched by Lake from the pinned revisions in `lakefile.toml` / `lake-manifest.json`):

```sh
cd erdos647-sparse
lake exe cache get          # Mathlib oleans (via the decanus dependency)
lake build Erdos647Sparse   # ≈ 50 CPU-hours for the 10^13 chunks; ~1 GB RAM per parallel job
bash scripts/axiom_gate.sh  # manifest + whole-library audit
```

`lake build Erdos647Sparse.Headline` builds the 10¹² result only (678 chunks, ~3.5 CPU-h); `lake build Erdos647Sparse.Mod` builds just the sieve stages (minutes).

**Regenerate the certificates** (Python 3 + numpy; the Lean emitters write into `Erdos647Sparse/`):

```sh
cd erdos647-sparse
for f in data/*.gz; do gunzip -c "$f" > "scripts/$(basename "${f%.gz}")"; done   # inputs next to the scripts
cd scripts
python3 gen_rung4_certs.py && python3 emit_rung4_lean.py     # stage 4: exclusions + survivors → Rung4Chunks/, Rung4.lean
python3 gen_witnesses_rung3.py && python3 gen_witnesses_low.py && python3 gen_witnesses_1e12.py
python3 verify_coverage_1e12.py && python3 emit_sparse_lean.py                    # 10^12: Chunks/, Grid.lean
python3 filter13.py && python3 gen_witnesses_1e13.py && python3 verify_coverage_1e13.py
python3 emit_sparse_lean13.py && python3 emit_grid13_tree.py                      # 10^13: Chunks13/, Grid13.lean
```

The generators are resumable (progress files every 200 points) and their outputs are byte-identical to `data/` (compare against `data/SHA256SUMS` after decompression). `run_1e12.sh` / `run_1e13.sh` chain the stages. The scaling appendix (`docs/scaling_appendix.md`) is reproduced by `rung_scaling_extrapolation.py` then `rung_scaling_costmodel.py`.

**The writeup.** `draft_note/erdos647_sparse.tex` builds with `pdflatex`; the PDF is committed alongside. It is a draft, not a published or submitted paper; this README carries the same content in repository form.

## 10. How this was produced

The Lean proofs, the Python generators and verifiers, the scaling analysis and the first draft of the writeup were written by an AI coding agent operated by Fjordmind Labs, working with compiler feedback, under the direction of the author, who set the goals, approved each extension of scope, reviewed the drafts and is responsible for the claims. The process is recorded because the result is small and the process is the part a reader may find informative.

**Timeline.** Day 1 (2026-10-01): survey of AI for research-level mathematics; selection of problem classes where a search-and-verify loop exists today (constructions, combinatorial bounds, formalization); a shortlist of Erdős problems ranked by explicit criteria. Problem 647 was chosen because its kernel-checked frontier (10⁹) lagged its unverified computational frontier (10²²) by thirteen orders of magnitude and the decanus authors had named the next step. Day 2: stages 1–2 proved kernel-clean, the bridge to the public statement, the sparse checker and its soundness lemmas, the 10¹¹ and 10¹² walks, stage 4. Day 3: the 10¹³ walk, the scaling analysis of §7, the axiom gate, the repository and the writeup. Every design decision and every verification step is logged in `docs/PROVENANCE.md`.

**Cost.** One 8-core desktop. 48.8 CPU-hours of kernel time for the 10¹³ walk, about 6 hours wall-clock; the smaller walks and the stage proofs are a fraction of that. No separate API spend: the agent ran inside the operator's existing coding-assistant subscription. No GPU.

**What went wrong and how it was caught.** Three failure modes are worth recording. (i) The witness soundness lemma was first stated over a check that admitted the shift k = 0, under which "m < n" is false; `omega` produced the countermodel while the soundness proof was being attempted, and 0 < k became an explicit conjunct of `killOk`. (ii) The 1,525-branch linear case split for 10¹³ reached 23 GB of memory and was replaced by the balanced binary merge tree of §5; the 678-branch ladder for 10¹² had worked and gave no warning that the next step would not. (iii) In a parallel formalization task the same week, the agent found that a failed typeclass synthesis inside a rewrite can be recovered by Lean with a synthetic `sorryAx` at exit code 0 and no `sorry` token anywhere in the source. This is why acceptance here is defined by the axiom report of every theorem, never by a clean build, and why the whole-library audit of §6 exists. None of the three would have been visible from a successful build alone.

**What the agent did not do.** It did not find new mathematics, and its own analysis (§7 item 2, §8) shows the method cannot settle the conjecture: for every modulus L the divisor budget leaves the class n ≡ 0 (mod L) untouched (since 2τ(k) < k + 3 for every shift k ≥ 1), so no finite table of sieve stages proves the statement. We think this is representative of what AI contributions to open problems look like at present: certified, incremental, cheap, and most useful when they say exactly where they stop.

## Credit and provenance

Built on decanus (Ibrahim Mian & Shayaan Siddique, Apache-2.0, [arXiv:2608.17880](https://arxiv.org/abs/2608.17880)): witness format, the soundness lemmas for witnesses, chains and the bridge to the public statement (`TauLower`/`Chain`/`Bridge`), the 10⁷ chain, and the pinned formal-conjectures statement. Structural mathematics: Dutta–Alexeev, Kitamura, Hughes (erdosproblems.com forum, problem 647). Reference computations: Idén (10¹²), Hughes (6.2×10¹⁷), bentrd (9.2×10¹⁸), veljjanoski (10²²).

The proofs, code and first draft were produced by an AI agent under the author's direction, as described in §10. Nothing in the trust argument depends on how the proofs were written: the Lean kernel checks them the same way.

Build and verification log: `docs/PROVENANCE.md`. Cite via `CITATION.cff`.
