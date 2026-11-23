import Lean

/-!
Generates the equation lemmas of a definition by `match` on many `String` literals with a
catch-all case (#16313).
-/

set_option Elab.async false

open Lean Elab Command

elab "#test_gen " f:ident n:num : command => do
  let n := n.getNat
  let cases ← (Array.range n).mapM fun i =>
    `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit s!"registered_name_{i}") => $(Syntax.mkNatLit i))
  let cases := cases.push (← `(Lean.Parser.Term.matchAltExpr| | _ => $(Syntax.mkNatLit n)))
  elabCommand (← `(def $f:ident : String → Nat $cases:matchAlt*))
  let some eqns ← liftTermElabM <| Meta.getEqnsFor? f.getId
    | throwError "no equation lemmas for `{f}`"
  unless eqns.size == n + 1 do
    throwError "expected {n + 1} equation lemmas, got {eqns.size}"

#eval show CommandElabM Unit from do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let n := if bench then 128 else 64
  elabCommand (← `(#test_gen f $(Syntax.mkNatLit n)))
