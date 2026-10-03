# Erdős #647 — Appendix: how far can kernel-checked bounds go? (rung-scaling extrapolation toward 10²²)

Appendix to [`../README.md`](../README.md) (Eero Tölö, Fjordmind Labs, October 2026). Engine: `../scripts/rung_scaling_extrapolation.py` and `../scripts/rung_scaling_costmodel.py`; raw results: `../data/rung_scaling_*.json.gz`.

## Question

Our certificate architecture (modular rungs that force `360360 | n` and restrict
`(n mod 17, 19, 23, 29)` to 4,431 classes, then a sparse witness walk over the
surviving grid points, all kernel-checked with axioms `{propext, Classical.choice,
Quot.sound}`) has reached 10¹³. The unverified GPU+CRT frontier is 10²². Three
questions: (a) how much more sieving the method can buy, (b) whether
deeper rungs ever force full divisibility by the next prime (which would coarsen
the grid), and (c) where the kernel-time curve puts 10¹⁵…10²².

## Method

`rung_scaling_extrapolation.py` generalises the rung-4 divisor-budget engine
(`rung4_feasibility.py`) to sieve primes 17…97 and validity thresholds
n > 10¹¹ … 10²¹ (cap d ≤ √T on the forced divisor stack). The rule is the one
every Lean rung already certifies: for a residue class and a shift k ≥ 1, the
forced divisor stack `d = gcd(360360, k) · ∏{p : k ≡ c_p (mod p)}` of `m = n − k`
kills the whole class when `2·τ(d) ≥ k + 3` and `d² < m`. Two refinements over the
rung-4 engine: subset stacking (take the s smallest matching primes with s
minimal — sound, and strictly stronger when the full stack overshoots the cap),
and a shift bound K = 600 (every kill found lies at k ≤ 168; the rung-4 run saw
max k = 90).

Chains are enumerated exactly while the joint class count stays ≤ 3·10⁶
(through rung 6, prime 37) and by Monte Carlo (3·10⁵ sampled classes per rung,
seed 647) beyond — the CRT makes a uniform sample of the next rung's classes
exact in expectation. Regression: at the rung-4 setting the engine returns
4,412 survivors vs the 4,431 the Lean rung proves (the 19 extra "survivors" in
the old engine are classes killable by a sub-stack; the Lean list is a
superset, so nothing is unsound — just 0.4% less sharp than it could be).

`rung_scaling_costmodel.py` turns survivor densities into kernel CPU time with
constants measured on the 10¹²/10¹³ builds (below).

## Results

### (a) Sieve strength per rung — diminishing returns, independent of threshold

| rung | +prime | modulus | surviving classes | density f | kill-fraction of this prime | kill certificates |
|---|---|---|---|---|---|---|
| 2 | 19 | 323 | 41 | 1.27e-1 | – | (tactic proof) |
| 3 | 23 | 7.4e3 | 353 | 4.75e-2 | 0.626 | 590 |
| 4 | 29 | 2.2e5 | 4,412 (Lean: 4,431) | 2.05e-2 | 0.569 | 5.8e3 |
| 5 | 31 | 6.7e6 | 60,086 | 9.00e-3 | 0.561 | 7.7e4 |
| 6 | 37 | 2.5e8 | 1.15e6 | 4.67e-3 | 0.481 | 1.1e6 |
| 7 | 41 | 1.0e10 | 2.6e7 (MC) | 2.59e-3 | 0.445 | 2.1e7 |
| 8 | 43 | 4.4e11 | 6.3e8 (MC) | 1.45e-3 | 0.439 | 5.0e8 |
| 9 | 47 | 2.0e13 | 1.7e10 (MC) | 8.4e-4 | 0.421 | 1.3e10 |
| 12 | 61 | 3.9e18 | 8.6e14 (MC) | 2.2e-4 | 0.347 | 4.6e14 |
| 15 | 73 | 1.4e24 | 1.0e20 (MC) | 7.5e-5 | 0.295 | 4.2e19 |
| 19 | 97 | 7.7e31 | 1.8e27 (MC) | 2.4e-5 | 0.223 | 5.3e26 |

(validity threshold n > 10¹¹; full table for n > 10²¹ in the archived log)

- **Each added prime kills a shrinking share of what is left**: 63% (23) →
  56% (31) → 48% (37) → 44% (41–43) → 35% (59–61) → 30% (73) → 22% (97). The
  mechanism is simple: prime p only helps at shifts k ≡ c_p (mod p), and with
  useful k ≤ ~170 a large p contributes at most a handful of shifts.
- **The d² < n relaxation is worth almost nothing.** Moving the validity
  threshold from 10¹¹ to 10²¹ (cap 3·10⁵ → 3·10¹⁰) lowers rung-4 survivors
  4,412 → 4,374 (−0.9%), rung-7 density 2.59e-3 → 2.50e-3 (−3.5%), rung-19
  density 2.4e-5 → 1.4e-5 (−40%, but see (c): that rung is unusable). Do rungs
  strengthen with n? Yes, measurably but marginally;
  the kills that matter use d ≪ 10⁵ anyway because k must stay small.
- **Survivor-class counts grow ~20–50× per rung** (p · survivor-fraction),
  from 4.4·10³ (rung 4) to 2.6·10⁷ (rung 7) to 6·10⁸ (rung 8). The Lean rung
  theorem must list the survivors (or the kills) explicitly, and a kernel-checked
  literal above ~10⁸ entries is outside anything built so far (decanus's 10⁹
  witness asset is 260 MB, CI-unverifiable). **Rung 7 (primes ≤ 41, ~2.5·10⁷
  survivors, ~2·10⁷ kill certificates ≈ 30 CPU-h at today's 5 ms/cert) is the
  practical ceiling of the enumerable sieve; its density floor is f ≈ 2.5·10⁻³.**

### (b) Full divisibility by the next prime is never provable by this method

The grid would coarsen by p if every class with c_p ≠ 0 died. It cannot: the
class `c₁₇ = 16, every other residue 0` survives at every threshold (checked
numerically up to validity 10²¹; `hardest_class_survives` in the JSON), and
the reason is structural. In that class a sieve prime q ≠ 17 matches shift k
only if q | k, so the whole matched stack divides k and `d ≤ k`; the budget
`2·τ(d) ≥ k + 3` then needs `τ(d) > d/2`, which holds only for d ∈ {1, 2, 3, 4, 6}
— none reachable with k ≡ 16 (mod 17). The same argument applies to every
p ≥ 17 (what made 11 and 13 fully forced at rung 2 is that `k = c_p` itself is a
small shift with a divisor-rich `gcd(360360, k)`; for p ≥ 17 the needed τ grows
linearly in k while τ(gcd) does not). Hence 360360 is the final forced modulus;
all further sieving is residue-class thinning, never grid coarsening.

### (c) Kernel-time curve to 10²²

Cost constants (CPU-seconds), from the 10¹²/10¹³ builds on the 8-core desktop:

| constant | value | source |
|---|---|---|
| walk (current design: every multiple of 360360 is visited) | 2.5 ms/pt isolated probe; **~7 ms/pt under 8-way load** (48.8 CPU-h / 2.5·10⁷ pts in the 10¹³ run, median chunk 92 s) | 2026-10-02/03 |
| per-survivor cost in a *period walk* (visits only surviving classes) | 0.5–2.5 ms | witness check is near-free; the fuel-recursion overhead is the upper end |
| rung kill certificate | 5 ms | rung-4 chunks: 1,000 classes / ~5 s |
| enumerable-survivor ceiling | 10⁸ classes | literal-size argument above |

| T | grid pts | best enumerable rung | witnesses W | A. current walk (×2.3 under load) | B. period walk, lo–hi | C. floor if a p ≤ 97 sieve were certifiable (W) |
|---|---|---|---|---|---|---|
| 10¹³ | 2.8e7 | 5 (31) | 2.5e5 | 19 h (measured ~49 CPU-h) | 9–17 min | – |
| 10¹⁴ | 2.8e8 | 5 (31) | 2.5e6 | 8 d | 0.5–1.8 h | – |
| 10¹⁵ | 2.8e9 | 6 (37) | 1.3e7 | 80 d | 3–10 h | 0.4 min (5e4) |
| 10¹⁶ | 2.8e10 | 7 (41) | 7.0e7 | 2.2 y | 1.6–3 d | 4 min (5e5) |
| 10¹⁷ | 2.8e11 | 7 (41) | 6.9e8 | 22 y | 5–21 d | 35 min (4e6) |
| 10¹⁸ | 2.8e12 | 7 (41) | 6.9e9 | 220 y | 41 d – 0.55 y | 6 h (4e7) |
| 10¹⁹ | 2.8e13 | 7 (41) | 6.9e10 | 2,200 y | 1.1–5.5 y | 2.4 d (4e8) |
| 10²⁰ | 2.8e14 | 7 (41) | 6.9e11 | 22,000 y | 11–55 y | 24 d (4e9) |
| 10²¹ | 2.8e15 | 7 (41) | 6.9e12 | 2.2e5 y | 110–550 y | 0.6 y (4e10) |
| 10²² | 2.8e16 | 7 (41) | 6.9e13 | 2.2e6 y | **1,100–5,500 y** | **6–30 y (4e11)** |

Reading the table:

1. **The current design walls at ~10¹⁴–10¹⁵.** Visiting every multiple of
   360360 costs ∝ T regardless of the sieve; 10¹⁵ is ~80 CPU-days (×2.3 under
   load ≈ 6 months). The sieve only reduces witness checks, which are already
   the cheap part.
2. **A period walk (iterate the 4,431 — later 2.5·10⁷ — surviving residues per
   period instead of testing every grid point) is the one structural lever left,
   and it buys ~2 decades**: 10¹⁶ in days, 10¹⁷ in weeks, 10¹⁸ in months.
   Implementation: the walker steps `j ← j + Δ` through the survivor list of
   the period M = 360360·∏p, and the rung theorem supplies "non-survivors are
   killed" for the skipped points. Kernel cost per survivor is then the witness
   check (0.5 ms) plus walk overhead.
3. **10²² is out of reach for kernel checking by 3–4 orders of magnitude.**
   With the deepest enumerable sieve (rung 7, f ≈ 2.5·10⁻³) the witness count at
   10²² is 7·10¹³ → 10³–10⁴ CPU-years. Even an ideal sieve with all primes ≤ 97
   (f ≈ 2.4·10⁻⁵, which has no certifiable representation: 10²⁷ survivor
   classes per period) still leaves 4·10¹¹ witnesses → 6–30 CPU-years, and that
   number is a *floor* for any certificate that checks one witness per surviving
   grid point. The GPU result reaches 10²² precisely by not paying per-point
   verification; a kernel-checked 10²² would need a different proof object
   (e.g. a certified sieve that proves kills for whole arithmetic progressions
   at once, so that W stops being ∝ T). That is a research question, not an
   engineering one.
4. **A naive estimate corrected.** One might guess "10²² ≈ 3–30 CPU-years if
   deep-sieve survivors stay ~10⁹–10¹⁰". The sweep shows that
   survivors at 10²² are ≥ 4·10¹¹ even for an uncertifiable 19-prime sieve, and
   ~7·10¹³ for any certifiable one; the 3–30-year figure survives only as the
   floor of column C. The honest headline is: **kernel-checked ≈ 10¹⁷–10¹⁸ at
   ~1 CPU-year with a period walk; 10²² ≈ 10³ CPU-years.**

## Assumptions and caveats

- Cost constants are single-machine (8-core desktop, Lean v4.30.0, decanus
  witness format). Cloud parallelism divides wall time, not CPU-years.
- Monte Carlo rungs (≥ 7) carry ~0.2% relative error on the survivor fraction
  (3·10⁵ samples); the compounding over rungs is what drives the 10²⁷ at rung
  19, not sampling noise.
- "Enumerable ≤ 10⁸" is a judgement about Lean literal sizes and CI
  verifiability, not a hard limit; relaxing it to 10⁹ (rung 8, f ≈ 1.4·10⁻³)
  changes column B by < 2×.
- The witness-count floor assumes one kernel-visible check per surviving grid
  point. Compressed certificates (one proof per *family* of witnesses — e.g.
  all points with the same `(k, d)` in a progression) are the only way around
  it and are not covered by this appendix.
