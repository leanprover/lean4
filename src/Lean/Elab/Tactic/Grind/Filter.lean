/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Init.Grind.Interactive
namespace Lean.Elab.Tactic.Grind
open Meta

public inductive Filter where
  | true
  | const (declName : Name)
  | fvar (fvarId : FVarId)
  | gen (pred : Nat → Bool)
  | or (a b : Filter)
  | and (a b : Filter)
  | not (a : Filter)

public partial def elabFilter (filter? : Option (TSyntax `grind_filter)) : GrindTacticM Filter := do
  let some filter := filter? | return .true
  go filter
where
  go (filter : TSyntax `grind_filter) : GrindTacticM Filter := do
    match filter with
    | `(grind_filter| $id:ident) =>
      match (← Term.resolveId? id) with
      | some (.const declName _) => return .const declName
      | some (.fvar fvarId) => return .fvar fvarId
      | _ => throwErrorAt id "invalid identifier"
    | `(grind_filter| $a:grind_filter && $b:grind_filter) => return .and (← go a) (← go b)
    | `(grind_filter| $a:grind_filter || $b:grind_filter) => return .or (← go a) (← go b)
    | `(grind_filter| ! $a:grind_filter) => return .not (← go a)
    | `(grind_filter| ($a:grind_filter)) => go a
    | `(grind_filter| gen = $n:num)  => let n := n.getNat; return .gen fun x => x == n
    | `(grind_filter| gen > $n:num)  => let n := n.getNat; return .gen fun x => x > n
    | `(grind_filter| gen ≥ $n:num)  => let n := n.getNat; return .gen fun x => x ≥ n
    | `(grind_filter| gen >= $n:num) => let n := n.getNat; return .gen fun x => x ≥ n
    | `(grind_filter| gen ≤ $n:num)  => let n := n.getNat; return .gen fun x => x ≤ n
    | `(grind_filter| gen <= $n:num) => let n := n.getNat; return .gen fun x => x ≤ n
    | `(grind_filter| gen < $n:num)  => let n := n.getNat; return .gen fun x => x < n
    | `(grind_filter| gen != $n:num) => let n := n.getNat; return .gen fun x => x != n
    | _ => throwUnsupportedSyntax

open Meta.Grind

-- **Note**: facts may not have been internalized if they are equalities.
def getGen (e : Expr) : GoalM Nat := do
  if (← alreadyInternalized e) then
    getGeneration e
  else match_expr e with
   | Eq _ lhs rhs => return max (← getGeneration lhs) (← getGeneration rhs)
   | _ => return 0

public def Filter.eval (filter : Filter) (e : Expr) : GoalM Bool := do
  go filter
where
  go (filter : Filter) : GoalM Bool := do
  match filter with
  | .true => return .true
  | .and a b => go a <&&> go b
  | .or a b => go a <||> go b
  | .not a => return !(← go a)
  | .const declName => return Option.isSome <| e.find? fun e => e.isConstOf declName
  | .fvar fvarId => return Option.isSome <| e.find? fun e => e.isFVar && e.fvarId! == fvarId
  | .gen pred => let gen ← getGen e; return pred gen

end Lean.Elab.Tactic.Grind
