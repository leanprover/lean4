/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Simp.SimpM

set_option warningAsError false
#exit

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
  /-- `ifReduce = true` if the declaration being inlined was tagged with `inline_if_reduce`. -/
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
    unless (← read).config.inlineDefs do
      return none
    let some decl ← getDecl? declName | return none
    let shouldInline : SimpM Bool := do
      if !decl.inlineIfReduceAttr && decl.recursive then return false
      if mustInline then return true
      /-
      We don't inline instances tagged with `[inline]/[always_inline]/[inline_if_reduce]` at the base phase
      We assume that at the base phase these annotations are for the instance methods that have been lambda lifted.
      -/
      if (← inBasePhase <&&> Meta.isInstance decl.name) then
        unless decl.name == ``instDecidableEqBool do
          /-
          TODO: remove this hack after we refactor `Decidable` as suggested by Gabriel.
          Recall that the current `Decidable` class is special case since it is an inductive datatype which is not a
          structure like all other type classes. This is bad since it prevents us from treating all classes in a uniform
          way. After we change `Decidable` to a structure as suggested by Gabriel, we should only accept type classes
          that are structures. Moreover, we should reject instances that have only one exit point producing an explicit structure.
          -/
          return false
      if decl.alwaysInlineAttr then return true
      -- TODO: check inlining quota
      if decl.inlineAttr || decl.inlineIfReduceAttr then return true
      unless decl.noinlineAttr do
        if (← isSmall decl.value) then return true
      return false
    unless (← shouldInline) do return none
    /- check arity -/
    let arity := decl.getArity
    let inlinePartial := (← read).config.inlinePartial
    if !mustInline && !inlinePartial && numArgs < arity then return none
    if decl.inlineIfReduceAttr then
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
      ifReduce  := decl.inlineIfReduceAttr
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

builtin_initialize
  registerTraceClass `Compiler.simp.inline
