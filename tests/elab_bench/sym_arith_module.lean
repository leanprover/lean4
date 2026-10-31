import Lean

/-!
Benchmark additive equality and term normalization over natural and integer modules, including
kernel checking of the resulting certificates. `TEST_BENCH` increases the number of distinct atoms.
-/

open Lean Meta Elab Tactic Sym

set_option maxRecDepth 10000

elab "module_bench_eq" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some h ← SymM.run (Arith.proveAddEq? target) | throwError "normal forms differ"
    g.assign h
    replaceMainGoal []

elab "module_bench_nf" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let r ← SymM.run do
      Simp.SimpM.run' (Simp.simp (← shareCommon target)) { post := fun e => Arith.normalizeAdd? e }
    let .step target h .. := r | throwError "normalization made no progress"
    replaceMainGoal [← g.replaceTargetEq target h]

run_cmd do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let n := if bench then 128 else 32
  let xs := (Array.range n).map fun i => mkIdent (Name.mkSimple s!"x{i}")
  let terms ← xs.mapIdxM fun i x => `(term| ($(quote (i + 1)) : Nat) • $x)
  let sum (ts : Array (TSyntax `term)) := ts[1:].toArray.foldlM (init := ts[0]!) fun a b =>
    `(term| $a + $b)
  let lhs ← sum terms
  let rhs ← sum terms.reverse
  for cls in [mkIdent ``Grind.NatModule, mkIdent ``Grind.IntModule] do
    Elab.Command.elabCommand (← `(command|
      example {M : Type} [$cls M] ($[$xs:ident]* : M) : $lhs = $rhs := by
        module_bench_eq))
    Elab.Command.elabCommand (← `(command|
      example {M : Type} [$cls M] (f : M → M) ($[$xs:ident]* : M) : f $lhs = f $rhs := by
        module_bench_nf
        rfl))
