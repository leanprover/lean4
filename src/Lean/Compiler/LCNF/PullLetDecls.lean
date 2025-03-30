/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.DependsOn
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF
namespace PullLetDecls

structure Context where
  isCandidateFn : LetDecl → FVarIdSet → CompilerM Bool
  included : FVarIdSet := {}

structure State where
  toPull : Array LetDecl := #[]

abbrev PullM := ReaderT Context $ StateRefT State CompilerM

@[inline] def withFVar (fvarId : FVarId) (x : PullM α) : PullM α :=
  withReader (fun ctx => { ctx with included := ctx.included.insert fvarId }) x

@[inline] def withParams (ps : Array Param) (x : PullM α) : PullM α :=
  withReader (fun ctx => { ctx with included := ps.foldl (init := ctx.included) fun s p => s.insert p.fvarId }) x

@[inline] def withNewScope (x : PullM α) : PullM α :=
  withReader (fun ctx => { ctx with included := {} }) x

partial def withCheckpoint (x : PullM Code) : PullM Code := do
  let toPullSizeSaved := (← get).toPull.size
  let c ← withNewScope x
  let toPull := (← get).toPull
  let rec go (i : Nat) (included : FVarIdSet) : StateM (Array LetDecl) Code := do
    if h : i < toPull.size then
      let letDecl := toPull[i]
      if letDecl.dependsOn included then
        let c ← go (i+1) (included.insert letDecl.fvarId)
        return .let letDecl c
      else
        modify (·.push letDecl)
        go (i+1) included
    else
      return c
  let (c, keep) := go toPullSizeSaved (← read).included |>.run #[]
  modify fun s => { s with toPull := s.toPull.shrink toPullSizeSaved ++ keep }
  return c

def attachToPull (c : Code) : PullM Code := do
  let toPull := (← get).toPull
  return toPull.foldr (init := c) fun decl c => .let decl c

def shouldPull (decl : LetDecl) : PullM Bool := do
  unless decl.dependsOn (← read).included do
    if (← (← read).isCandidateFn decl (← read).included) then
      modify fun s => { s with toPull := s.toPull.push decl }
      return true
  return false

mutual
  partial def pullAlt (alt : Alt) : PullM Alt :=
    match alt with
    | .default k => return alt.updateCode (← withNewScope <| pullDecls k)
    | .alt _ params k => return alt.updateCode (← withNewScope <| withParams params <| pullDecls k)

  partial def pullDecls (code : Code) : PullM Code := do
    match code with
    | .cases c =>
      withCheckpoint do
        let alts ← c.alts.mapMonoM pullAlt
        return code.updateAlts! alts
    | .let decl k =>
      if (← shouldPull decl) then
        pullDecls k
      else
        withFVar decl.fvarId do return code.updateCont! (← pullDecls k)
    | .fun decl k | .jp decl k =>
      withCheckpoint do
        let value ← withParams decl.params <| pullDecls decl.value
        let decl ← decl.updateValue value
        withFVar decl.fvarId do return code.updateFun! decl (← pullDecls k)
    | _ => return code

end

def PullM.run (x : PullM α) (isCandidateFn : LetDecl → FVarIdSet → CompilerM Bool) : CompilerM α :=
  x { isCandidateFn } |>.run' {}

end PullLetDecls

open PullLetDecls

def Decl.pullLetDecls (decl : Decl) (isCandidateFn : LetDecl → FVarIdSet → CompilerM Bool) : CompilerM Decl := do
  PullM.run (isCandidateFn := isCandidateFn) do
    withParams decl.params do
      let value ← decl.value.mapCodeM pullDecls
      let value ← value.mapCodeM attachToPull
      return { decl with value }

def Decl.pullInstances (decl : Decl) : CompilerM Decl :=
  decl.pullLetDecls fun letDecl candidates => do
    if (← isClass? letDecl.type).isSome then
      return true
    else if let .proj _ _ fvarId := letDecl.value then
      return candidates.contains fvarId
    else
      return false

def pullInstances : Pass :=
  .mkPerDeclaration `pullInstances Decl.pullInstances .base

builtin_initialize
  registerTraceClass `Compiler.pullInstances (inherited := true)

end Lean.Compiler.LCNF
