import Lean

open Lean
open Lean.Meta
open Lean.Meta.Sym.Simp


def test : MetaM Unit := do
  let natMVar ← mkFreshExprMVar (mkConst ``Nat)
  let exprToAdd := mkApp (mkConst ``Nat.succ) natMVar
  trace[Meta.Tactic] "Adding: {exprToAdd} to the discrimination tree"
  let pattern ← mkSimprocPatternFromExpr exprToAdd
  let keys := pattern.mkDiscrTreeKeys
  -- The generated keys are `[Nat.succ]`, but I would like to have a wildcard pattern for the argument here
  trace[Meta.Tactic] "Generated keys: {keys}"
  let d : DiscrTree Bool := {}
  let d := d.insertKeyValue keys true
  let exprToAdd := mkApp (mkConst ``Nat.succ) (mkNatLit 42)
  trace[Meta.Tactic] "We will try to retrieve: {exprToAdd}"
  -- The normal match will fail
  let normalMatch ← d.getMatch exprToAdd
  trace[Meta.Tactic] "Normal match result: {normalMatch}"
  -- The overapplied one works
  let matchWithExtra ← d.getMatchWithExtra exprToAdd
  trace[Meta.Tactic] "overapplied match result: {matchWithExtra}"


set_option trace.Meta.Tactic true
#eval test
