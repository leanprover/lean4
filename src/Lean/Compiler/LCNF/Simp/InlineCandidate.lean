/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Simp.SimpM

namespace Lean.Compiler.LCNF
namespace Simp

/--
Result of `inlineCandidate?`.
It contains information for inlining local and global functions.
-/
structure InlineCandidateInfo where
  isLocal  : Bool
  params   : Array Param
  /-- Value (lambda expression) of the function to be inlined. -/
  value    : Code
  f        : Expr
  args     : Array Expr
  /-- `ifReduce = true` if the declaration being inlined was tagged with `inlineIfReduce`. -/
  ifReduce : Bool
  /-- `recursive = true` if the declaration being inline is in a mutually recursive block. -/
  recursive : Bool := false

/-- The arity (aka number of parameters) of the function to be inlined. -/
def InlineCandidateInfo.arity : InlineCandidateInfo → Nat
  | { params, .. } => params.size

/--
Return `some info` if `e` should be inlined.
-/
def inlineCandidate? (e : Expr) : SimpM (Option InlineCandidateInfo) := do
  let mut e := e
  let mut mustInline := false
  if e.isAppOfArity ``inline 2 then
    e ← findExpr e.appArg!
    mustInline := true
  let numArgs := e.getAppNumArgs
  let f := e.getAppFn
  if let .const declName us ← findExpr f then
    if declName == (← read).declName then return none -- TODO: remove after we start storing phase1 code in .olean files
    let inlineIfReduce := hasInlineIfReduceAttribute (← getEnv) declName
    unless mustInline || hasInlineAttribute (← getEnv) declName || inlineIfReduce do return none
    -- TODO: check whether function is recursive or not.
    -- We can skip the test and store function inline so far.
    let some decl ← getDecl? declName | return none
    let arity := decl.getArity
    let inlinePartial := (← read).config.inlinePartial
    if !mustInline && !inlinePartial && numArgs < arity then return none
    if inlineIfReduce then
      let some paramIdx := decl.isCasesOnParam? | return none
      unless paramIdx < numArgs do return none
      let arg ← findExpr (e.getArg! paramIdx)
      unless arg.isConstructorApp (← getEnv) do return none
    let params := decl.instantiateParamsLevelParams us
    let value := decl.instantiateValueLevelParams us
    incInline
    return some {
      isLocal   := false
      f         := e.getAppFn
      args      := e.getAppArgs
      ifReduce  := inlineIfReduce
      recursive := decl.recursive
      params, value
    }
  else if let some decl ← findFunDecl? f then
    unless numArgs > 0 do return none -- It is not worth to inline a local function that does not take any arguments
    unless mustInline || (← shouldInlineLocal decl) do return none
    -- Remark: we inline local function declarations even if they are partial applied
    incInlineLocal
    modify fun s => { s with inlineLocal := s.inlineLocal + 1 }
    return some {
      isLocal  := true
      f        := e.getAppFn
      args     := e.getAppArgs
      params   := decl.params
      value    := decl.value
      ifReduce := false
    }
  else
    return none
