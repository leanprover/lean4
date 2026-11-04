import Lean

/-!
Benchmark normalization of powers with symbolic `Nat` exponents (`symbolicPow := true`): a sum of
many exponents, a tower of nested powers, and a power of a long product, including kernel checking
of the certificates. `TEST_BENCH` increases the sizes.
-/

open Lean Meta Elab Tactic Sym

set_option maxRecDepth 10000
set_option sym.arith.maxDegree 1024
set_option sym.arith.maxTerms 1024

elab "power_nf" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let r ← SymM.run do
      Simp.SimpM.run' (Simp.simp (← shareCommon target))
        { pre := Simp.simpArith (symbolicPow := true), post := Simp.evalGround }
    let .step t h .. := r | throwError "no progress"
    unless t.isTrue do throwError "unequal normal forms:{indentExpr t}"
    g.assign (← mkOfEqTrue h)
    replaceMainGoal []

run_cmd do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let n := if bench then 192 else 32
  let ns := (Array.range n).map fun i => mkIdent (Name.mkSimple s!"n{i}")
  let ys := (Array.range n).map fun i => mkIdent (Name.mkSimple s!"y{i}")
  let fold (op : TSyntax `term → TSyntax `term → Elab.Command.CommandElabM (TSyntax `term))
      (ts : Array (TSyntax `term)) := ts[1:].toArray.foldlM (init := ts[0]!) op
  let x := mkIdent `x
  let m := mkIdent `m
  let sum ← fold (fun a b => `(term| $a + $b)) ns
  let pows ← fold (fun a b => `(term| $a * $b)) (← ns.reverse.mapM fun k => `(term| $x ^ $k))
  Elab.Command.elabCommand (← `(command|
    example ($x : Int) ($[$ns:ident]* : Nat) : $x ^ ($sum) = $pows := by power_nf))
  let tower ← ns.foldlM (init := x) fun a k => `(term| ($a) ^ $k)
  let prod ← fold (fun a b => `(term| $a * $b)) ns
  Elab.Command.elabCommand (← `(command|
    example ($x : Int) ($[$ns:ident]* : Nat) : $tower = $x ^ ($prod) := by power_nf))
  let base ← fold (fun a b => `(term| $a * $b)) ys
  let dist ← fold (fun a b => `(term| $a * $b)) (← ys.reverse.mapM fun y => `(term| $y ^ ($m + 1)))
  Elab.Command.elabCommand (← `(command|
    example ($[$ys:ident]* : Int) ($m : Nat) : ($base) ^ ($m + 1) = $dist := by power_nf))
