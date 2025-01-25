/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Util

namespace Lean.Meta.Grind.Arith.Offset
/-- Construct a model that statisfies all offset constraints -/
def mkModel (goal : Goal) : MetaM (Array (Expr × Nat)) := do
  let s := goal.arith.offset
  let nodes := s.nodes
  let mut pre : Array (Option Int) := mkArray nodes.size none
  for u in [:nodes.size] do
    let val? := s.sources[u]!.foldl (init := @none Int) fun val? v k => Id.run do
      let some va := pre[v]! | return val?
      let val' := va - k
      let some val := val? | return val'
      if val' > val then return val' else val?
    let val? := s.targets[u]!.foldl (init := val?) fun val? v k => Id.run do
      let some va := pre[v]! | return val?
      let val' := va + k
      let some val := val? | return val'
      if val' < val then return val' else val?
    let val := val?.getD 0
    pre := pre.set! u (some val)
  let min := pre.foldl (init := 0) fun min val? => Id.run do
    let some val := val? | return min
    if val < min then val else min
  let mut r := {}
  for u in [:nodes.size] do
    let some val := pre[u]! | unreachable!
    let val := (val - min).toNat
    let e := nodes[u]!
    /-
    We should not include the assignment for auxiliary offset terms since
    they do not provide any additional information.
    That said, the information is relevant for debugging `grind`.
    -/
    if (!(← isLitValue e) && (isNatOffset? e).isNone && isNatNum? e != some 0) || grind.debug.get (← getOptions) then
      r := r.push (e, val)
  return r

end Lean.Meta.Grind.Arith.Offset
