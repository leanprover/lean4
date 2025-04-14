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

/-- Construct a model that satisfies all offset constraints -/
def mkModel (goal : Goal) : MetaM (Array (Expr × Nat)) := do
  let s := goal.arith.offset
  let dbg := grind.debug.get (← getOptions)
  let nodes := s.nodes
  let isInterpreted (u : Nat) : Bool := isNatNum s.nodes[u]!
  let mut pre : Array (Option Int) := .replicate nodes.size none
  /-
  `needAdjust[u]` is true if `u` assignment is not connected to an interpreted value in the graph.
  That is, its assignment may be negative.
  -/
  let mut needAdjust : Array Bool := .replicate nodes.size true
  -- Initialize `needAdjust`
  for u in [: nodes.size] do
    if isInterpreted u then
      -- Interpreted values have a fixed value.
      needAdjust := needAdjust.set! u false
    else if s.sources[u]!.any fun v _ => isInterpreted v then
      needAdjust := needAdjust.set! u false
    else if s.targets[u]!.any fun v _ => isInterpreted v then
      needAdjust := needAdjust.set! u false
  -- Set interpreted values
  for h : u in [:nodes.size] do
    let e := nodes[u]
    if let some v ← getNatValue? e then
      pre := pre.set! u (Int.ofNat v)
  -- Set remaining values
  for u in [:nodes.size] do
    let lower? := s.sources[u]!.foldl (init := none) fun val? v k => Id.run do
      let some va := pre[v]! | return val?
      let val' := va - k
      let some val := val? | return val'
      if val' > val then return val' else val?
    let upper? := s.targets[u]!.foldl (init := none) fun val? v k => Id.run do
      let some va := pre[v]! | return val?
      let val' := va + k
      let some val := val? | return val'
      if val' < val then return val' else val?
    if dbg then
      let some upper := upper? | pure ()
      let some lower := lower? | pure ()
      assert! lower ≤ upper
      let some val := pre[u]! | pure ()
      assert! lower ≤ val
      assert! val ≤ upper
    unless pre[u]!.isSome do
      let val := lower?.getD (upper?.getD 0)
      pre := pre.set! u (some val)
  let min := pre.foldl (init := 0) fun min val? => Id.run do
    let some val := val? | return min
    if val < min then val else min
  let mut r := {}
  for u in [:nodes.size] do
    let some val := pre[u]! | unreachable!
    let val := if needAdjust[u]! then (val - min).toNat else val.toNat
    let e := nodes[u]!
    /-
    We should not include the assignment for auxiliary offset terms since
    they do not provide any additional information.
    That said, the information is relevant for debugging `grind`.
    -/
    if (!(← isLitValue e) && (isNatOffset? e).isNone && isNatNum? e != some 0) || grind.debug.get (← getOptions) then
      r := r.push (e, val)
  r := r.qsort fun (e₁, _) (e₂, _) => e₁.lt e₂
  if (← isTracingEnabledFor `grind.offset.model) then
    for (x, v) in r do
      trace[grind.offset.model] "{quoteIfArithTerm x} := {v}"
  return r

end Lean.Meta.Grind.Arith.Offset
