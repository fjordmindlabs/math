/-
Erdős #647: the 10^12 headline.
Fjordmind Labs (Eero Tölö), 2026-10. Builds on decanus (Mian–Siddique, Apache-2.0).

Composition: decanus's kernel-checked contiguous chain covers (24, 10^7].
Above 10^7, the kernel-clean modular sieve (Erdos647Sparse.Mod) confines any
candidate to the sparse grid n = 360360 * j (41 residue classes mod 17*19
once n > 2.5*10^8), and the chunked sparse certificates (Erdos647Sparse.Grid)
kill every surviving grid point up to 10^12.
-/
import Erdos647.Cert
import Erdos647.Bridge
import Erdos647Sparse.Grid

set_option maxRecDepth 100000

namespace Erdos647Sparse

open ArithmeticFunction ArithmeticFunction.sigma
open Erdos647 (Killed killed_upto not_sup_le_of_killed)

/-- Every `n` with `10^7 < n ≤ 10^12` satisfying the Erdős 647 inner
predicate would be a killed grid point — contradiction fuel. -/
theorem killed_of_cand_mid {n : ℕ} (h7 : 10000000 < n) (hX : n ≤ 1000000000000)
    (H : Erdos647Mod.Cand n) : Killed n := by
  have h360 : 360360 ∣ n := Erdos647Mod.mod360360_of_cand (by omega) H
  obtain ⟨j, rfl⟩ := h360
  have hf : gridFilter (360360 * j) = true := by
    by_cases hsm : 360360 * j ≤ 250000000
    · rw [gridFilter, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl hsm
    · have hmem := Erdos647Mod.mod_17_19_of_cand (by omega) H
      rw [gridFilter, Bool.or_eq_true]
      exact Or.inr (inPairs_of_mem hmem)
  exact grid_killed j (by omega) (by omega) hf

/-- **No solution to Erdős #647 exists in `(24, 10^12]`**: every such `n`
fails `max_{m<n}(m + τ(m)) ≤ n + 2`. Kernel-clean: the sieve, the sparse
certificates, and decanus's contiguous chain are all checked by `decide`,
no `native_decide`. -/
theorem erdos647_no_solution_upto_1e12 :
    ∀ n : ℕ, 24 < n → n ≤ 1000000000000 →
      ¬ (⨆ m : Fin n, ↑m + σ 0 m ≤ n + 2) := by
  intro n h24 hX hsup
  by_cases hlow : n ≤ 10000000
  · exact not_sup_le_of_killed (killed_upto n h24 hlow) hsup
  · have H : Erdos647Mod.Cand n := Erdos647Mod.cand_of_sup hsup
    exact not_sup_le_of_killed (killed_of_cand_mid (by omega) hX H) hsup

end Erdos647Sparse

#print axioms Erdos647Sparse.erdos647_no_solution_upto_1e12
