/-
Erdős #647 sparse rungs (10^7, 10^13]: automated whole-library axiom audit.
Fjordmind Labs (Eero Tölö), 2026-10. Builds on decanus (Mian–Siddique, Apache-2.0).
-/
import Erdos647Sparse

/-! Sibling of `Erdos647/AxiomAudit.lean` for the sparse library. At elaboration
time it walks every module under `Erdos647Sparse.*` (hand-written files, the
Rung4 class-sieve chunks, and the 2,203 sparse-grid chunk modules), finds every
theorem and any `axiom` declaration, recomputes each axiom closure from the
compiled environment, and refuses to compile unless everything depends on at
most `propext`, `Classical.choice`, and `Quot.sound`. `sorryAx` and the
`native_decide` axioms lie outside that set and fail this file by construction.

The upstream audit filters modules by the name prefix `Erdos647`, which as a
`Name` prefix does NOT match `Erdos647Sparse` (different first component), so
the sparse library needs its own audit. `scripts/axiom_gate.sh` runs both. -/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut modules : Nat := 0
  let mut offenders : Array (Name × Array Name) := #[]
  let mut axiomDecls : Array Name := #[]
  for (modName, modData) in env.header.moduleNames.zip env.header.moduleData do
    unless Name.isPrefixOf `Erdos647Sparse modName do continue
    modules := modules + 1
    for declName in modData.constNames do
      match env.find? declName with
      | some (.thmInfo _) =>
        let axs ← collectAxioms declName
        let bad := axs.filter (fun ax => !allowed.contains ax)
        checked := checked + 1
        unless bad.isEmpty do offenders := offenders.push (declName, bad)
      | some (.axiomInfo _) =>
        unless allowed.contains declName do axiomDecls := axiomDecls.push declName
      | _ => pure ()
  unless axiomDecls.isEmpty do
    throwError "AXIOM AUDIT: FAIL: axiom declarations in Erdos647Sparse modules: {axiomDecls}"
  unless offenders.isEmpty do
    throwError
      "AXIOM AUDIT: FAIL: {offenders.size} theorem(s) beyond the allowed axioms: {offenders}"
  if checked == 0 then
    throwError "AXIOM AUDIT: FAIL: scanned zero theorems, the module filter is broken"
  logInfo
    m!"AXIOM AUDIT: PASS: {checked} theorems across {modules} Erdos647Sparse modules, axioms within {allowed}"
