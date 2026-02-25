/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
public import Lean.Meta.Tactic.Grind.Filter
namespace Lean.Elab.Tactic.Grind
open Meta Grind

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

end Lean.Elab.Tactic.Grind
