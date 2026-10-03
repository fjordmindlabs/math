/-
Erdős #647 sparse rungs (10^7, 10^13]: curated axiom manifest.
Fjordmind Labs (Eero Tölö), 2026-10. Builds on decanus (Mian–Siddique, Apache-2.0).
-/
import Erdos647Sparse.Mod
import Erdos647Sparse.Checker
import Erdos647Sparse.Rung4
import Erdos647Sparse.Checker13
import Erdos647Sparse.Grid
import Erdos647Sparse.Headline
import Erdos647Sparse.Grid13
import Erdos647Sparse.Headline13

/-! Publication gate for the sparse library, mirroring `Erdos647/AxiomCheck.lean`:
every theorem below must depend on at most `[propext, Classical.choice, Quot.sound]`
— no `sorryAx`, no `Lean.ofReduceBool` (`native_decide`).
`Erdos647Sparse/AxiomAudit.lean` re-checks every theorem in every
`Erdos647Sparse` module mechanically; `scripts/axiom_gate.sh` requires both. -/

-- Rungs 1–2 and the bridge (Erdos647Sparse.Mod)
#print axioms Erdos647Mod.mod2520_of_cand
#print axioms Erdos647Mod.mod360360_of_cand
#print axioms Erdos647Mod.mod_17_19_of_cand
#print axioms Erdos647Mod.sup_iff_cand
#print axioms Erdos647Mod.sieve_of_sup

-- Sparse checker soundness (Erdos647Sparse.Checker, Erdos647Sparse.Checker13)
#print axioms Erdos647Sparse.killOk_sound
#print axioms Erdos647Sparse.sparseOk_sound
#print axioms Erdos647Sparse.sparseOk13_sound
#print axioms Erdos647Sparse.gridFilter13_of_cand

-- Rung 4: the mod 23·29 class sieve (Erdos647Sparse.Rung4, generated)
#print axioms Erdos647Sparse.rung4_killed_or_surv
#print axioms Erdos647Sparse.classOk4_of_cand

-- The certified sparse grids (Erdos647Sparse.Grid, Erdos647Sparse.Grid13, generated)
#print axioms Erdos647Sparse.grid_killed
#print axioms Erdos647Sparse.grid13_killed

-- The headlines (Erdos647Sparse.Headline, Erdos647Sparse.Headline13)
#print axioms Erdos647Sparse.killed_of_cand_mid
#print axioms Erdos647Sparse.erdos647_no_solution_upto_1e12
#print axioms Erdos647Sparse.killed_of_cand_high
#print axioms Erdos647Sparse.erdos647_no_solution_upto_1e13
