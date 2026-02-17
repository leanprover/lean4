import Lean

open Lean
open Lean.Meta
open Lean.Meta.Sym
open Lean.Meta.Sym.Simp

/--
trace: [Meta.Tactic] Adding: Nat.succ ?m.1 to the discrimination tree
[Meta.Tactic] Generated keys: [Nat.succ, *]
[Meta.Tactic] We will try to retrieve: Nat.succ 42
[Meta.Tactic] Normal match result: [true]
[Meta.Tactic] overapplied match result: [(true, 0)]
-/
#guard_msgs in
set_option trace.Meta.Tactic true in
#eval show MetaM Unit from do
  let natMVar ← mkFreshExprMVar (mkConst ``Nat)
  let exprToAdd := mkApp (mkConst ``Nat.succ) natMVar
  trace[Meta.Tactic] "Adding: {exprToAdd} to the discrimination tree"
  let pattern ← mkSimprocPatternFromExpr exprToAdd
  let keys := pattern.mkDiscrTreeKeys
  trace[Meta.Tactic] "Generated keys: {keys}"
  let d : DiscrTree Bool := {}
  let d := d.insertKeyValue keys true
  let exprToAdd := mkApp (mkConst ``Nat.succ) (mkNatLit 42)
  trace[Meta.Tactic] "We will try to retrieve: {exprToAdd}"
  let normalMatch ← d.getMatch exprToAdd
  trace[Meta.Tactic] "Normal match result: {normalMatch}"
  let matchWithExtra ← d.getMatchWithExtra exprToAdd
  trace[Meta.Tactic] "overapplied match result: {matchWithExtra}"
