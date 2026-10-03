/-
Erdős #647 sparse-grid checker and soundness (rung 3).
Fjordmind Labs (Eero Tölö), 2026-10. Builds on decanus (Mian–Siddique, Apache-2.0).

After the kernel-clean sieve (Erdos647Sparse.Mod), any candidate n in
(10^7, 10^11] lies on the grid n = 360360*j, and for n > 2.5*10^8 its
residue pair (n % 17, n % 19) is one of 41 survivor classes. The surviving
grid is sparse: 35,803 points over the whole range. `sparseOk` walks the
grid and checks one decanus-format kill witness per surviving point; its
soundness lemma turns each passing walk into `Killed n` for every surviving
grid point in the walked span. Chunked `decide` certificates live in
`Erdos647Sparse/Chunks/`, the composed driver in `Erdos647Sparse/Grid.lean`,
and the 10^11 headline in `Erdos647Sparse/Headline.lean`.
-/
import Erdos647.Chain
import Erdos647Sparse.Mod

namespace Erdos647Sparse

open Erdos647 (Pairs witnessOk certTau Killed witness_tau)

/-- Membership of the pair `(a, b)` in a pair list, as a kernel-friendly
Bool recursion. -/
def inPairs (a b : ℕ) : List (ℕ × ℕ) → Bool
  | [] => false
  | (x, y) :: t => (a == x && b == y) || inPairs a b t

theorem inPairs_of_mem {a b : ℕ} : ∀ {l : List (ℕ × ℕ)},
    (a, b) ∈ l → inPairs a b l = true := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons hd t ih =>
    intro h
    obtain ⟨x, y⟩ := hd
    rw [inPairs, Bool.or_eq_true]
    rcases List.mem_cons.mp h with h | h
    · left
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · right
      exact ih h

/-- The residue-class filter of rung 2b: `(n % 17, n % 19)` is one of the
41 survivor classes. -/
def classOk (n : ℕ) : Bool := inPairs (n % 17) (n % 19) Erdos647Mod.survivors

/-- The grid filter. A grid point `n = 360360 * j` can carry a candidate
only if it passes: below the rung-2b threshold every grid point survives,
above it only the 41 residue classes. -/
def gridFilter (n : ℕ) : Bool := decide (n ≤ 250000000) || classOk n

/-- One sparse kill: witness `m = n - k` is wellformed (decanus
`witnessOk`) and its certified divisor-count bound kills `n` outright. -/
def killOk (n k : ℕ) (ps : Pairs) : Bool :=
  decide (0 < k) && witnessOk n k ps
    && decide (n + 3 ≤ (n - k) + certTau (n - k) ps)

/-- The sparse walk: `fuel` grid indices starting at `j`, consuming one
witness per surviving point. Points failing `gridFilter` are skipped; the
witness list must be exactly consumed (no leftovers, no misalignment). -/
def sparseOk : ℕ → ℕ → List (ℕ × Pairs) → Bool
  | 0, _, ws => ws.isEmpty
  | fuel + 1, j, [] =>
      !gridFilter (360360 * j) && sparseOk fuel (j + 1) []
  | fuel + 1, j, (k, ps) :: t =>
      if gridFilter (360360 * j) then
        killOk (360360 * j) k ps && sparseOk fuel (j + 1) t
      else
        sparseOk fuel (j + 1) ((k, ps) :: t)

theorem killOk_sound {n k : ℕ} {ps : Pairs} (h : killOk n k ps = true) :
    Killed n := by
  rw [killOk, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hk0, hw⟩, hkill⟩ := h
  have hkn : k < n := by
    have hw' := hw
    rw [witnessOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hw'
    exact hw'.1.1.1
  have htau : certTau (n - k) ps ≤ (n - k).divisors.card := witness_tau hw
  exact ⟨n - k, by omega, by omega, by omega⟩

/-- Soundness of the sparse walk: every surviving grid point in the walked
span is killed. -/
theorem sparseOk_sound : ∀ {fuel j : ℕ} {ws : List (ℕ × Pairs)},
    sparseOk fuel j ws = true →
    ∀ i : ℕ, j ≤ i → i < j + fuel → gridFilter (360360 * i) = true →
    Killed (360360 * i) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j ws _ i h1 h2 _
    omega
  | succ fuel ih =>
    intro j ws h i h1 h2 hf
    rcases ws with _ | ⟨⟨k, ps⟩, t⟩
    · rw [sparseOk, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hg, hrest⟩ := h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hij
      · rw [hf] at hg; cases hg
      · exact ih hrest i hij (by omega) hf
    · rw [sparseOk] at h
      by_cases hg : gridFilter (360360 * j) = true
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
