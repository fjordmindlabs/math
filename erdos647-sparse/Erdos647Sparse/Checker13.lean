/-
Erdős #647 fast sparse-grid checker for the 10^13 extension.
Fjordmind Labs (Eero Tölö), 2026-10. Builds on decanus (Mian–Siddique, Apache-2.0).

The 10^13 walk spans ~25M grid indices — 10× the 10^12 walk — so the
per-point filter must be cheap in the kernel. Instead of scanning the
41-pair (`classOk`) and 4431-element (`classOk4`) survivor lists at every
grid point, `gridFilter13` tests single bits of two Nat bitmask literals
(`Masks13.lean`); `Nat.testBit` reduces via GMP-accelerated shifts. The
bridge lemmas below tie the masks to the proved sieve facts, so the
headline side can discharge `gridFilter13 n = true` for any candidate from
`mod_17_19_of_cand` + `classOk4_of_cand`. `sparseOk13` is the walker twin
of `sparseOk` with the fast filter; chunked certificates live in
`Erdos647Sparse/Chunks13/`, the driver in `Erdos647Sparse/Grid13.lean`.
-/
import Erdos647Sparse.Checker
import Erdos647Sparse.Rung4
import Erdos647Sparse.Masks13

namespace Erdos647Sparse

open Erdos647 (Pairs Killed)

/-- Converse of `inPairs_of_mem`. -/
theorem mem_of_inPairs {a b : ℕ} : ∀ {l : List (ℕ × ℕ)},
    inPairs a b l = true → (a, b) ∈ l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons hd t ih =>
    intro h
    obtain ⟨x, y⟩ := hd
    rw [inPairs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- Converse of `inIdx_of_mem`. -/
theorem mem_of_inIdx {a : ℕ} : ∀ {l : List ℕ}, inIdx a l = true → a ∈ l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x t ih =>
    intro h
    rw [inIdx, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- The flat residue-class index of `n`, exactly as in `classOk4`. -/
def flatIdx (n : ℕ) : ℕ :=
  (pairIdxOf (n % 17) (n % 19) * 23 + n % 23) * 29 + n % 29

/-- The fast grid filter for the `(10^12, 10^13]` walk: candidates below the
rung-4 threshold pass outright; above it the rung-2b and rung-4 residue
masks must both accept. -/
def gridFilter13 (n : ℕ) : Bool :=
  decide (n ≤ 100000000000)
    || (mask323.testBit (n % 323) && mask27k.testBit (flatIdx n))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- `mask323` accepts every residue whose pair survives rung 2b. -/
theorem mask323_complete : ∀ r, r < 323 →
    inPairs (r % 17) (r % 19) Erdos647Mod.survivors = true →
    mask323.testBit r = true := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- `mask27k` accepts every rung-4 survivor class. -/
theorem mask27k_covers : rung4Survivors.all (fun i => mask27k.testBit i) = true := by
  decide

/-- Bridge, rung 2b: survivor-pair membership forces the mask bit. -/
theorem mask323_of_mem {n : ℕ}
    (h : (n % 17, n % 19) ∈ Erdos647Mod.survivors) :
    mask323.testBit (n % 323) = true := by
  have h17 : n % 323 % 17 = n % 17 := Nat.mod_mod_of_dvd n (by norm_num)
  have h19 : n % 323 % 19 = n % 19 := Nat.mod_mod_of_dvd n (by norm_num)
  refine mask323_complete (n % 323) (Nat.mod_lt _ (by norm_num)) ?_
  rw [h17, h19]
  exact inPairs_of_mem h

/-- Bridge, rung 4: `classOk4` forces the mask bit. -/
theorem mask27k_of_classOk4 {n : ℕ} (h : classOk4 n = true) :
    mask27k.testBit (flatIdx n) = true := by
  rw [classOk4] at h
  exact List.all_eq_true.mp mask27k_covers _ (mem_of_inIdx h)

/-- **Headline-side coverage**: every candidate `n > 10^12` passes the fast
filter. -/
theorem gridFilter13_of_cand {n : ℕ} (hn : 1000000000000 < n)
    (H : Erdos647Mod.Cand n) : gridFilter13 n = true := by
  have hp := Erdos647Mod.mod_17_19_of_cand (by omega) H
  have h4 := classOk4_of_cand (by omega) H
  rw [gridFilter13, Bool.or_eq_true, Bool.and_eq_true]
  exact Or.inr ⟨mask323_of_mem hp, mask27k_of_classOk4 h4⟩

/-- The fast sparse walk: twin of `sparseOk` with `gridFilter13`. -/
def sparseOk13 : ℕ → ℕ → List (ℕ × Pairs) → Bool
  | 0, _, ws => ws.isEmpty
  | fuel + 1, j, [] =>
      !gridFilter13 (360360 * j) && sparseOk13 fuel (j + 1) []
  | fuel + 1, j, (k, ps) :: t =>
      if gridFilter13 (360360 * j) then
        killOk (360360 * j) k ps && sparseOk13 fuel (j + 1) t
      else
        sparseOk13 fuel (j + 1) ((k, ps) :: t)

/-- Soundness of the fast walk: every filter-passing grid point in the
walked span is killed. -/
theorem sparseOk13_sound : ∀ {fuel j : ℕ} {ws : List (ℕ × Pairs)},
    sparseOk13 fuel j ws = true →
    ∀ i : ℕ, j ≤ i → i < j + fuel → gridFilter13 (360360 * i) = true →
    Killed (360360 * i) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j ws _ i h1 h2 _
    omega
  | succ fuel ih =>
    intro j ws h i h1 h2 hf
    rcases ws with _ | ⟨⟨k, ps⟩, t⟩
    · rw [sparseOk13, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hg, hrest⟩ := h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hij
      · rw [hf] at hg; cases hg
      · exact ih hrest i hij (by omega) hf
    · rw [sparseOk13] at h
      by_cases hg : gridFilter13 (360360 * j) = true
      · rw [if_pos hg, Bool.and_eq_true] at h
        obtain ⟨hk, hrest⟩ := h
        rcases Nat.eq_or_lt_of_le h1 with rfl | hij
        · exact killOk_sound hk
        · exact ih hrest i hij (by omega) hf
      · rw [if_neg hg] at h
        rcases Nat.eq_or_lt_of_le h1 with rfl | hij
        · exact absurd hf hg
        · exact ih h i hij (by omega) hf

end Erdos647Sparse
