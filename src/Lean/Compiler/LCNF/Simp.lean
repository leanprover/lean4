/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.ReduceJpArity
public import Lean.Compiler.LCNF.Simp.Basic
public import Lean.Compiler.LCNF.Simp.FunDeclInfo
public import Lean.Compiler.LCNF.Simp.JpCases
public import Lean.Compiler.LCNF.Simp.Config
public import Lean.Compiler.LCNF.Simp.InlineCandidate
public import Lean.Compiler.LCNF.Simp.SimpM
public import Lean.Compiler.LCNF.Simp.Main
public import Lean.Compiler.LCNF.Simp.InlineProj
public import Lean.Compiler.LCNF.Simp.DefaultAlt
public import Lean.Compiler.LCNF.Simp.SimpValue
public import Lean.Compiler.LCNF.Simp.Used

public section

namespace Lean.Compiler.LCNF
open Simp

def Decl.simp? (decl : Decl .pure) : SimpM (Option (Decl .pure)) := do
  let .code code := decl.value | return none
  updateFunDeclInfo code
  traceM `Compiler.simp.inline.info do return m!"{decl.name}:{Format.nest 2 (← (← get).funDeclInfoMap.format)}"
  traceM `Compiler.simp.step do ppDecl decl
  let code ← simp code
  let s ← get
  let code ← code.applyRenaming s.binderRenaming
  traceM `Compiler.simp.step.new do return m!"{decl.name} :=\n{← ppCode code}"
  trace[Compiler.simp.stat] "{decl.name}, size: {code.size}, # visited: {s.visited}, # inline: {s.inline}, # inline local: {s.inlineLocal}"
  if let some code ← simpJpCases? code then
    let decl := { decl with value := .code code }
    decl.reduceJpArity
  else if (← get).simplified then
    return some { decl with value := .code code }
  else
    return none

partial def Decl.simp (decl : Decl .pure) (config : Config) : CompilerM (Decl .pure) := do
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
  go (decl : Decl .pure) (config : Config) : CompilerM (Decl .pure) := do
    if let some decl ← decl.simp? |>.run { config, declName := decl.name } |>.run' {} |>.run {} then
      -- TODO: bound number of steps?
      go decl config
    else
      return decl

def simp (config : Config := {}) (occurrence : Nat := 0) (phase := Phase.base) : Pass :=
  phase.withPurityCheck .pure fun h =>
    .mkPerDeclaration `simp phase (h ▸ (Decl.simp · config)) (occurrence := occurrence)

builtin_initialize
  registerTraceClass `Compiler.simp (inherited := true)
  registerTraceClass `Compiler.simp.stat
  registerTraceClass `Compiler.simp.step
  registerTraceClass `Compiler.simp.step.new
