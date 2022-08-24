/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
#exit -- TODO: port to new LCNF
import Lean.Compiler.CompilerM
import Lean.Compiler.Decl

namespace Lean.Compiler
namespace PullLocalDecls

structure Context where
  isCandidateFn : LocalDecl → FVarIdSet → CompilerM Bool

structure State where
  toPull : FVarIdSet := {}

abbrev PullM := ReaderT Context $ StateRefT State CompilerM

def dependsOn (e : Expr) (fvarIdSet : FVarIdSet) : Bool :=
  e.hasAnyFVar fun fvarId => fvarIdSet.contains fvarId

def mkLambda (xs : Array Expr) (letFVarsSavedSize : Nat) (e : Expr) : PullM Expr := do
  let letFVars := (← getThe CompilerM.State).letFVars
  let toPull := (← get).toPull
  let mut xs := xs
  let mut included : FVarIdSet := xs.foldl (init := {}) fun s x => s.insert x.fvarId!
  let mut keep := #[] -- Variables to keep pulling
  for i in [letFVarsSavedSize : letFVars.size] do
    let y := letFVars[i]!
    let some (.ldecl _ fvarId _ type value _) ← findDecl? y.fvarId! | unreachable!
    if toPull.contains fvarId then
      if !dependsOn value included && !dependsOn type included then
        keep := keep.push y
        continue
    xs := xs.push y
    included := included.insert fvarId
  modifyThe CompilerM.State fun s => { s with letFVars := s.letFVars.shrink letFVarsSavedSize ++ keep }
  -- Remark: we could remove all variables in `xs` from the local context
  Compiler.mkLambda xs e

mutual

partial def visitLambda (e : Expr) (topLevel := false) : PullM Expr := do
  let (as, e) ← Compiler.visitLambdaCore e
  let letFVarsSavedSize := (← getThe CompilerM.State).letFVars.size
  let e ← visitLet e as
  if topLevel then
    Compiler.mkLambda as (← mkLetUsingScope e)
  else
    mkLambda as letFVarsSavedSize e

partial def visitCases (casesInfo : CasesInfo) (cases : Expr) : PullM Expr := do
  let mut args := cases.getAppArgs
  for i in casesInfo.altsRange do
    args ← args.modifyM i visitLambda
  return mkAppN cases.getAppFn args

partial def visitLet (e : Expr) (xs : Array Expr := #[]) : PullM Expr := do
  match e with
  | .letE binderName type value body nonDep =>
    let type := type.instantiateRev xs
    let mut value := value.instantiateRev xs
    if value.isLambda then
      value ← visitLambda value
    let x ← mkLetDecl binderName type value nonDep
    let some localDecl ← findDecl? x.fvarId! | unreachable!
    if (← (← read).isCandidateFn localDecl (← get).toPull) then
      trace[Compiler.pullLocalDecls.candidate] "{x}"
      modify fun s => { s with toPull := s.toPull.insert localDecl.fvarId }
    visitLet body (xs.push x)
  | e =>
    let e := e.instantiateRev xs
    if let some casesInfo ← isCasesApp? e then
      visitCases casesInfo e
    else
      return e

end

end PullLocalDecls

def Decl.pullLocalDecls (decl : Decl) (isCandidateFn : LocalDecl → FVarIdSet → CompilerM Bool) : CoreM Decl :=
  decl.mapValue fun value => PullLocalDecls.visitLambda value (topLevel := true) |>.run { isCandidateFn } |>.run' {}

def Decl.pullInstances (decl : Decl) : CoreM Decl :=
  decl.pullLocalDecls fun localDecl candidates => do
    if (← isClass? localDecl.type).isSome then
      return true
    else if let .proj _ _ (.fvar fvarId) := localDecl.value then
      return candidates.contains fvarId
    else
      return false

builtin_initialize
  registerTraceClass `Compiler.pullLocalDecls.candidate

end Lean.Compiler
