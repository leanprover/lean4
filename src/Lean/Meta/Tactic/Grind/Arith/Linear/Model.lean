/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.Types
import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
import Lean.Meta.Tactic.Grind.Arith.ModelUtil
import Init.Grind.Module.Envelope
public section
namespace Lean.Meta.Grind.Arith.Linear

def getAssignment? (s : Struct) (e : Expr) : Option Rat := Id.run do
  let some x := s.varMap.find? { expr := e } | return none
  if h : x < s.assignment.size then
    return some s.assignment[x]
  else
    return none

private def hasType (type : Expr) (n : ENode): MetaM Bool :=
  withDefault do
    let type' ← inferType n.self
    isDefEq type' type

private def toQ? (e : Expr) : Option Expr :=
  match_expr e with
  | Grind.IntModule.OfNatModule.toQ _ _ a => some a
  | _ => none

/--
Helper function for evaluating terms that have been processed by `internalize`, but
we did not added them to constraints. See comment at `assignTerms`.
-/
private partial def evalTermAt? (e : Expr) (s : Struct) (model : Std.HashMap Expr Rat) : MetaM (Option Rat) := do
  go e
where
  go (e : Expr) : OptionT MetaM Rat := do
    if let some val := model.get? e then
      return val
    match_expr e with
    | Neg.neg _ i a => if isNegInst s i then return - (← go a) else failure
    | HAdd.hAdd _ _ _ i a b => if isAddInst s i then return (← go a) + (← go b) else failure
    | HSub.hSub _ _ _ i a b => if isSubInst s i then return (← go a) - (← go b) else failure
    | HMul.hMul _ _ _ i a b => if isHomoMulInst s i then return (← go a) * (← go b) else failure
    | HSMul.hSMul _ _ _ i a b =>
      if isSMulIntInst s i then
        let k ← getIntValue? a
        return k * (← go b)
      else if isSMulNatInst s i then
        let k ← getNatValue? a
        return k * (← go b)
      else
        failure
    | Zero.zero _ i => if isZeroInst s i then return 0 else failure
    | OfNat.ofNat _ n _ => let k ← getNatValue? n; return k
    | _ => failure

/--
Assigns terms that do not have an assignment associated with them because they were used only as markers
for communicating with the `grind` core.
For example, suppose we have `a + b = c`. The `internalize` function marks `a + b`, `a`, and `b`
with theory variables. Let's assume we also have `c = 2*b`. In this case, `internalize` marks `2*b`
with a theory variable, and `b` is already marked. Then, when both equalities are asserted
in the `grind` core, the `linarith` module is notified that `a + b = 2*b` is true, and it is then
normalized as `a + -1*b = 0`. The terms `a` and `b` are assigned rational values by the search
procedure, but `a + b` and `2*b` are not. This procedure assigns them using the model computed by the
search procedure.

**Note**: We should reconsider whether to add the equalities `「a+b」 = a + b` and `「2*b」 = 2*b`
to force the search procedure to assign interpretations to these terms.
-/
private def assignTerms (goal : Goal) (structId : Nat) (model : Std.HashMap Expr Rat) : MetaM (Std.HashMap Expr Rat) := do
  let mut model := model
  let s ← linearExt.getStateCore goal
  let struct := s.structs[structId]!
  for (e, structId') in s.exprToStructIdEntries do
    if structId == structId' && !model.contains e then
      if let some v ← evalTermAt? e struct model then
        model := assignEqc goal e v model
  return model

/--
Construct a model that satisfies all constraints in the linarith model for the structure with id `structId`.
It also assigns values to (integer) terms that have not been internalized by the linarith model.
-/
def mkModel (goal : Goal) (structId : Nat) : MetaM (Array (Expr × Rat)) := do
  let mut model := {}
  let s := (← linearExt.getStateCore goal).structs[structId]!
  -- Assign on expressions associated with cutsat terms or interpreted terms
  for e in goal.exprs do
    let node ← goal.getENode e
    if node.isRoot then
    if (← hasType s.type node) then
      if let some v := getAssignment? s node.self then
        model := assignEqc goal node.self v model
  model ← assignTerms goal structId model
  -- Assign `toQ a` terms
  for e in goal.exprs do
    let node ← goal.getENode e
    let i := node.self
    let some n := toQ? i | pure ()
    if model[n]?.isNone then
      let some v := model[i]? | pure ()
      model := assignEqc goal n v model
  let r ← finalizeModel goal (hasType s.type) model
  traceModel `grind.linarith.model r
  return r

end Lean.Meta.Grind.Arith.Linear
