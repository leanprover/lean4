/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Tactic
open Meta

private def equivMVarDecl (d₁ d₂ : MetavarDecl) : Bool :=
  d₁.type == d₂.type
  -- The following additional check does not seem to be necessary
/-
  &&
  d₁.lctx.decls.size == d₂.lctx.decls.size &&
  Id.run do
     for i in [:d₁.lctx.decls.size] do
       match d₁.lctx.decls[i], d₂.lctx.decls[i] with
       | some localDecl₁, some localDecl₂ => if localDecl₁.type != localDecl₂.type then return false
       | none, none => pure ()
       | _, _ => return false
     return true
-/

register_builtin_option tactic.dbg_cache : Bool := {
  defValue := false
  group    := "tactic"
  descr    := "enable tactic cache debug messages (remark: they are sent to the standard error)"
}

private def dbg_cache (msg : String) : TacticM Unit := do
  if tactic.dbg_cache.get (← getOptions) then
    dbg_trace msg

private def dbg_cache' (cacheRef : IO.Ref Cache) (pos : String.Pos) (mvarId : MVarId) (msg : String) : TacticM Unit := do
  if tactic.dbg_cache.get (← getOptions) then
    let {line, column} := (← getFileMap).toPosition pos
    dbg_trace "{msg}, cache size: {(← cacheRef.get).pre.size}, line: {line}, column: {column}, contains entry: {(← cacheRef.get).pre.find? { mvarId, pos } |>.isSome}"

private def findCache? (cacheRef : IO.Ref Cache) (mvarId : MVarId) (stx : Syntax) (pos : String.Pos) : TacticM (Option Snapshot) := do
  let some s := (← cacheRef.get).pre.find? { mvarId, pos } | do dbg_cache "cache key not found"; return none
  let mvarDecl ← mvarId.getDecl
  let some mvarDeclOld := s.meta.mctx.findDecl? mvarId | return none
  if equivMVarDecl mvarDecl mvarDeclOld then
    if stx == s.stx then
      return some s
    else
      dbg_cache "syntax is different"
      return none
  else
    dbg_cache "cached state is not compatible"
    return none

@[builtin_tactic checkpoint] def evalCheckpoint : Tactic := fun stx =>
  focus do
    let mvarId ← getMainGoal
    let some cacheRef := (← readThe Term.Context).tacticCache? | evalTactic stx[1]
    let some pos := stx.getPos? | evalTactic stx[1]
    match (← findCache? cacheRef mvarId stx[1] pos) with
    | some s =>
      cacheRef.modify fun { pre, post } => { pre, post := post.insert { mvarId, pos } s }
      set s.core
      set s.meta
      set s.term
      set s.tactic
      dbg_cache' cacheRef pos mvarId "cache hit"
    | none =>
      evalTactic stx[1]
      let s := {
        stx    := stx[1]
        core   := (← getThe Core.State)
        meta   := (← getThe Meta.State)
        term   := (← getThe Term.State)
        tactic := (← get)
      }
      dbg_cache' cacheRef pos mvarId "cache miss"
      cacheRef.modify fun { pre, post } => { pre, post := post.insert { mvarId, pos } s }

end Lean.Elab.Tactic
