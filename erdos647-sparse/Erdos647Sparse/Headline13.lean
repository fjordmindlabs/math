/-
Erdős #647: the 10^13 headline.
Fjordmind Labs (Eero Tölö), 2026-10. Builds on decanus (Mian–Siddique, Apache-2.0).

Composition: decanus's kernel-checked contiguous chain covers (24, 10^7];
the 10^12 sparse certificate (Erdos647Sparse.Headline machinery) covers
(10^7, 10^12]; above 10^12 the rung-4 sieve (Erdos647Sparse.Rung4) confines
any candidate to the 4431-class sparse grid, whose fast-filter certificates
(Erdos647Sparse.Grid13) kill every surviving point up to 10^13.
-/
import Erdos647.Cert
import Erdos647.Bridge
import Erdos647Sparse.Headline
import Erdos647Sparse.Grid13

set_option maxRecDepth 100000

namespace Erdos647Sparse

open ArithmeticFunction ArithmeticFunction.sigma
open Erdos647 (Killed killed_upto not_sup_le_of_killed)

/-- Every `n` with `10^12 < n ≤ 10^13` satisfying the Erdős 647 inner
predicate would be a killed rung-4 grid point — contradiction fuel. -/
theorem killed_of_cand_high {n : ℕ} (h12 : 1000000000000 < n)
    (hX : n ≤ 10000000000000) (H : Erdos647Mod.Cand n) : Killed n := by
  have hf : gridFilter13 n = true := gridFilter13_of_cand h12 H
  have h360 : 360360 ∣ n := Erdos647Mod.mod360360_of_cand (by omega) H
  obtain ⟨j, rfl⟩ := h360
  exact grid13_killed j (by omega) (by omega) hf

/-- **No solution to Erdős #647 exists in `(24, 10^13]`**: every such `n`
fails `max_{m<n}(m + τ(m)) ≤ n + 2`. Kernel-clean: the sieves, the sparse
certificates, and decanus's contiguous chain are all checked by `decide`,
no `native_decide`. -/
theorem erdos647_no_solution_upto_1e13 :
    ∀ n : ℕ, 24 < n → n ≤ 10000000000000 →
      ¬ (⨆ m : Fin n, ↑m + σ 0 m ≤ n + 2) := by
  intro n h24 hX hsup
  by_cases hlow : n ≤ 10000000
  · exact not_sup_le_of_killed (killed_upto n h24 hlow) hsup
  have H : Erdos647Mod.Cand n := Erdos647Mod.cand_of_sup hsup
  by_cases hmid : n ≤ 1000000000000
  · exact not_sup_le_of_killed (killed_of_cand_mid (by omega) hmid H) hsup
  · exact not_sup_le_of_killed (killed_of_cand_high (by omega) hX H) hsup

end Erdos647Sparse

#print axioms Erdos647Sparse.erdos647_no_solution_upto_1e13
