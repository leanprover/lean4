/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.ReduceJpArity
import Lean.Compiler.LCNF.Renaming
import Lean.Compiler.LCNF.Simp.Basic
import Lean.Compiler.LCNF.Simp.FunDeclInfo
import Lean.Compiler.LCNF.Simp.JpCases
import Lean.Compiler.LCNF.Simp.Config
import Lean.Compiler.LCNF.Simp.InlineCandidate
import Lean.Compiler.LCNF.Simp.SimpM
import Lean.Compiler.LCNF.Simp.Main
import Lean.Compiler.LCNF.Simp.InlineProj
import Lean.Compiler.LCNF.Simp.DefaultAlt
import Lean.Compiler.LCNF.Simp.SimpValue
import Lean.Compiler.LCNF.Simp.Used

namespace Lean.Compiler.LCNF
open Simp

def Decl.simp? (decl : Decl) : SimpM (Option Decl) := do
  updateFunDeclInfo decl.value
  trace[Compiler.simp.inline.info] "{decl.name}:{Format.nest 2 (← (← get).funDeclInfoMap.format)}"
  traceM `Compiler.simp.step do ppDecl decl
  let value ← simp decl.value
  let s ← get
  let value ← value.applyRenaming s.binderRenaming
  traceM `Compiler.simp.step.new do return m!"{decl.name} :=\n{← ppCode value}"
  trace[Compiler.simp.stat] "{decl.name}, size: {value.size}, # visited: {s.visited}, # inline: {s.inline}, # inline local: {s.inlineLocal}"
  if let some value ← simpJpCases? value then
    let decl := { decl with value }
    decl.reduceJpArity
  else if (← get).simplified then
    return some { decl with value }
  else
    return none

partial def Decl.simp (decl : Decl) (config : Config) : CompilerM Decl := do
  let mut config := config
  if (← isTemplateLike decl) then
    /-
    We do not eta-expand or inline partial applications in template like code.
    Recall we don't want to generate code for them.
    Remark: by eta-expanding partial applications in instances, we also make the simplifier
    work harder when inlining instance projections.
    -/
    config := { config with etaPoly := false, inlinePartial := false }
  go decl config
where
  go (decl : Decl) (config : Config) : CompilerM Decl := do
    if let some decl ← decl.simp? |>.run { config, declName := decl.name } |>.run' {} then
      -- TODO: bound number of steps?
      go decl config
    else
      return decl

def simp (config : Config := {}) (occurrence : Nat := 0) : Pass :=
  .mkPerDeclaration `simp (Decl.simp · config) .base (occurrence := occurrence)

builtin_initialize
  registerTraceClass `Compiler.simp (inherited := true)
  registerTraceClass `Compiler.simp.stat
  registerTraceClass `Compiler.simp.step
  registerTraceClass `Compiler.simp.step.new
