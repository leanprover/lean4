/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PhaseExt

/-!
This module contains a pass for propagating user provided borrows as far forward in the function as
possible. This analysis is used to inform the reset-reuse insertion as to avoid inserting
reset-reuse on values that the user explicitly requested to be borrowed.
-/

namespace Lean.Compiler.LCNF

public inductive Ownedness where
  | bot
  | borrow
  | own
  | top
  deriving Inhabited, BEq

def Ownedness.join : Ownedness → Ownedness → Ownedness
  | .bot, v => v
  | .borrow, .borrow =>  .borrow
  | .own, .own =>  .own
  | _, _ => .top

structure State where
  values : Std.HashMap FVarId Ownedness
  modified : Bool
  deriving Inhabited

abbrev InferM := StateRefT State CompilerM

public partial def Decl.analyzePropagatedBorrows (decl : Decl .impure) :
    CompilerM (Std.HashMap FVarId Ownedness) := do
  let (_, { values, .. }) ← go |>.run { values := {}, modified := false }
  return values
where
  @[inline]
  getOwnedness (fvarId : FVarId) : InferM Ownedness := do
    return (← get).values.getD fvarId .bot

  @[inline]
  join (fvarId : FVarId) (v : Ownedness) : InferM Unit := do
    modify fun s =>
      let old := s.values.getD fvarId .bot
      let new := old.join v
      if old == new then
        s
      else
        { s with values := s.values.insert fvarId new, modified := true }

  getParams (f : Name) : InferM (Array (Param .impure)) := do
    let some sig ← getImpureSignature? f | unreachable!
    return sig.params

  go : InferM Unit := do
    initializeDecl
    loop

  initializeDecl : InferM Unit := do
    match decl.value with
    | .code .. =>
      for p in decl.params do
        let init := if p.borrow then .borrow else .top
        modify fun s => { s with values := s.values.insert p.fvarId init }
    | _ => return ()

  loop : InferM Unit := do
    modify fun s => { s with modified := false }
    match decl.value with
    | .code code => collectCode code
    | _ => pure ()
    if (← get).modified then loop

  collectCode (code : Code .impure) : InferM Unit := do
    match code with
    | .jp decl k =>
      for p in decl.params do
        unless (← get).values.contains p.fvarId do
          let init := if p.borrow then .borrow else .bot
          modify fun s => { s with values := s.values.insert p.fvarId init }
      collectCode k
      collectCode decl.value
    | .let decl k =>
      collectLetValue decl.fvarId decl.value
      collectCode k
    | .jmp jpId args =>
      let some decl ← findFunDecl? (pu := .impure) jpId | unreachable!
      for arg in args, p in decl.params do
        if let .fvar arg := arg then
          let argValue ← getOwnedness arg
          join p.fvarId argValue
    | .cases cs => cs.alts.forM (·.forCodeM collectCode)
    | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => collectCode k
    | .return .. | .unreach .. => return ()
    | .inc .. | .dec .. | .setTag .. | .oset .. | .del .. => unreachable!

  collectLetValue (z : FVarId) (v : LetValue .impure) : InferM Unit := do
    match v with
    | .oproj _ parent _ =>
      let parentVal ← getOwnedness parent
      join z parentVal
    -- Keep in sync with ExplicitRC, InferBorrow
    | .fap ``Array.getInternal args =>
      if let .fvar parent := args[1]! then
        let parentVal ← getOwnedness parent
        join z parentVal
    | .fap ``Array.get!Internal args =>
      if let .fvar parent := args[1]! then
        let parentVal ← getOwnedness parent
        join z parentVal
      if let .fvar parent := args[2]! then
        let parentVal ← getOwnedness parent
        join z parentVal
    | .fap ``Array.uget args =>
      if let .fvar parent := args[1]! then
        let parentVal ← getOwnedness parent
        join z parentVal
    | .fap _ args =>
      let value := if args.isEmpty then .borrow else .own
      join z value
    | .ctor .. | .fvar .. | .pap .. | .sproj .. | .uproj .. | .erased .. | .lit .. =>
      join z .own
    | _ => unreachable!


def Ownedness.toBorrow : Ownedness → Option Bool
  | .bot => none
  | .borrow => some true
  | .own | .top => some false

public partial def Decl.applyOwnedness (decl : Decl .impure) (values : Std.HashMap FVarId Ownedness) :
    CompilerM (Decl .impure) := do
  match decl.value with
  | .code code =>
    let params ← updateParams decl.params
    let code ← goCode code
    return { decl with params, value := .code code }
  | _ => return decl
where
  updateParams (ps : Array (Param .impure)) : CompilerM (Array (Param .impure)) :=
    ps.mapM fun p => do
      match values[p.fvarId]!.toBorrow with
      | none => return p
      | some borrow => p.updateBorrow borrow

  goCode (code : Code .impure) : CompilerM (Code .impure) := do
    match code with
    | .jp decl k =>
      let ps ← updateParams decl.params
      let decl ← decl.update decl.type ps (← goCode decl.value)
      return code.updateFun! decl (← goCode k)
    | .cases cs => return code.updateAlts! <| ← cs.alts.mapMonoM (·.mapCodeM goCode)
    | .let _ k | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => return code.updateCont! (← goCode k)
    | .return .. | .jmp .. | .unreach .. => return code
    | .inc .. | .dec .. | .setTag .. | .oset .. | .del .. => unreachable!

end Lean.Compiler.LCNF
