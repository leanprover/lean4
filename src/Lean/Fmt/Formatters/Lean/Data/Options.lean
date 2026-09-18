/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Data.Options
meta import Lean.Parser.Command
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

/-- Formats `<keyword> <name> : <type> := <decl>`, the shared shape of the option registrations. -/
public def fmtOptionRegistration
    (registerTk : Syntax) (name : TSyntax `ident) (colonTk : Syntax) (type : TSyntax `term)
    (colonEqTk : Syntax) (decl : TSyntax `term)
    : FmtM TaggedDoc := do
  let registerTk ← fmt registerTk
  let name ← fmt name
  let colonTk ← fmt colonTk
  let type ← fmt type
  let colonEqTk ← fmt colonEqTk
  let decl ← fmt decl
  let signature := Layouts.globalSignature #[registerTk, name] #[] colonTk type
  return Layouts.assignmentDeclaration signature colonEqTk decl

@[builtin_fmt Lean.Option.registerBuiltinOption]
public def fmtRegisterBuiltinOption : Fmt := fun
  | `(Lean.Option.registerBuiltinOption|
      $[$docComment?:docComment]? $[$visibility?:visibility]?
      register_builtin_option%$registerTk $name:ident :%$colonTk $type:term :=%$colonEqTk
        $decl:term) => do
    let option ← fmtOptionRegistration registerTk name colonTk type colonEqTk decl
    fmtDeclWithModifiers docComment? none #[visibility?] option
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Option.registerOption]
public def fmtRegisterOption : Fmt := fun
  | `(Lean.Option.registerOption|
      $declModifiers:declModifiers
      register_option%$registerTk $name:ident :%$colonTk $type:term :=%$colonEqTk
        $decl:term) => do
    let option ← fmtOptionRegistration registerTk name colonTk type colonEqTk decl
    fmtDeclWithDeclModifiers declModifiers option
  | _ =>
    throw .partialFormatter
