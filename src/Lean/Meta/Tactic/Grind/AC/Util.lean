/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.ProveEq
public import Lean.Meta.Tactic.Grind.SynthInstance
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
public section

namespace Lean.Meta.Grind.AC

def get' : GoalM State := do
  return (← get).ac

@[inline] def modify' (f : State → State) : GoalM Unit := do
  modify fun s => { s with ac := f s.ac }

structure ACM.Context where
  opId : Nat

class MonadGetStruct (m : Type → Type) where
  getStruct : m Struct

export MonadGetStruct (getStruct)

@[always_inline]
instance (m n) [MonadLift m n] [MonadGetStruct m] : MonadGetStruct n where
  getStruct    := liftM (getStruct : m Struct)

abbrev ACM := ReaderT ACM.Context GoalM

abbrev ACM.run (opId : Nat) (x : ACM α) : GoalM α :=
  x { opId }

abbrev getOpId : ACM Nat :=
  return (← read).opId

protected def ACM.getStruct : ACM Struct := do
  let s ← get'
  let opId ← getOpId
  if h : opId < s.structs.size then
    return s.structs[opId]
  else
    throwError "`grind` internal error, invalid structure id"

instance : MonadGetStruct ACM where
  getStruct := ACM.getStruct

def getOp : ACM Expr :=
  return (← getStruct).op

private def notAssoc : Std.HashSet Name :=
  Std.HashSet.ofList [``Eq, ``And, ``Or, ``Iff, ``getElem, ``OfNat.ofNat, ``ite, ``dite, ``cond, ``LT.lt, ``LE.le]

/--
Returns `true` if `op` is an arithmetic operator supported in other modules.
Remark: `f == op.getAppFn!`
-/
private def isArithOpInOtherModules (op : Expr) (f : Expr) : GoalM Bool := do
  unless (← getConfig).ring do return false
  -- Remark: if `ring` is disabled we could check whether `cutsat` is enabled and discard `+` and `-`, but this is just a filter.
  let .const declName _ := f | return false
  if declName == ``HAdd.hAdd || declName == ``HMul.hMul || declName == ``HSub.hSub || declName == ``HDiv.hDiv || declName == ``HPow.hPow then
    if op.getAppNumArgs == 4 then
      let α := op.appFn!.appFn!.appArg!
      if (← Arith.CommRing.getRingId? α).isSome then return true
      if (← Arith.CommRing.getSemiringId? α).isSome then return true
  return false

def getOpId? (op : Expr) : GoalM (Option Nat) := do
  if let some id? := (← get').opIdOf.find? { expr := op } then
    return id?
  let id? ← go
  modify' fun s => { s with opIdOf := s.opIdOf.insert { expr := op } id? }
  return id?
where
  go : GoalM (Option Nat) := do
    let f := op.getAppFn
    if let .const declName _ := f then
      if notAssoc.contains declName then return none
    let .forallE _ α b _ ← whnf (← inferType op) | return none
    if b.hasLooseBVars then return none
    let .forallE _ α₂ α₃ _ ← whnf b | return none
    if α₃.hasLooseBVars then return none
    unless (← isDefEq α α₂) do return none
    unless (← isDefEq α α₃) do return none
    if (← isArithOpInOtherModules op f) then return none
    let u ← getLevel α
    let assocType := mkApp2 (mkConst ``Std.Associative [u]) α op
    let some assocInst ← synthInstance? assocType | return none
    let commType := mkApp2 (mkConst ``Std.Commutative [u]) α op
    let commInst? ← synthInstance? commType
    let idempotentType := mkApp2 (mkConst ``Std.IdempotentOp [u]) α op
    let idempotentInst? ← synthInstance? idempotentType
    let (neutralInst?, neutral?) ← do
      let neutral ← mkFreshExprMVar α
      let identityType := mkApp3 (mkConst ``Std.Identity [u]) α op neutral
      if let some identityInst ← synthInstance? identityType then
        let neutral ← instantiateExprMVars neutral
        let neutral ← preprocessLight neutral
        internalize neutral (← getGeneration op)
        pure (some identityInst, some neutral)
      else
        pure (none, none)
    let id := (← get').structs.size
    modify' fun s => { s with
      structs := s.structs.push {
        id, type := α, u, op, neutral?, assocInst, commInst?,
        idempotentInst?, neutralInst?
    }}
    -- TODO: neutral element must be variable 0
    trace[grind.debug.ac.op] "{op}, comm: {commInst?.isSome}, idempotent: {idempotentInst?.isSome}, neutral?: {neutral?}"
    return some id

end Lean.Meta.Grind.AC
