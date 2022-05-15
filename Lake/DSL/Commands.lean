/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Command
import Lake.Config.Package
import Lake.DSL.Attributes

open Lean Parser Command
namespace Lake.DSL

syntax structVal :=
  "{" manyIndent(group(Term.structInstField ", "?)) "}"

syntax declValDo :=
  ppSpace Term.do (Term.whereDecls)?

syntax declValStruct :=
  ppSpace structVal (Term.whereDecls)?

-- # Packages

syntax packageDeclWithBinders :=
  (ppSpace "(" Term.simpleBinder ")")? -- dir
  (ppSpace "(" Term.simpleBinder ")")? -- args
  (declValSimple <|> declValStruct <|> declValDo)

syntax packageDeclTyped :=
  Term.typeSpec declValSimple

syntax packageDeclSpec :=
  ident (Command.whereStructInst <|> packageDeclTyped <|> packageDeclWithBinders)?

scoped syntax (name := packageDecl)
(docComment)? "package " packageDeclSpec : command

def expandPackageBinders
: (dir? : Option Syntax) → (args? : Option Syntax) → MacroM (Bool × Syntax × Syntax)
| none,     none      => do let hole ← `(_); return (false, hole, hole)
| some dir, none      => return (true, dir, ← `(_))
| none,     some args => return (true, ← `(_), args)
| some dir, some args => return (true, dir, args)

def mkPackageDef (id : Syntax) (defn : Syntax) (doc? : Option Syntax)
(dir? : Option Syntax) (args? : Option Syntax) (wds? : Option Syntax) : MacroM Syntax := do
  let (hasBinders, dir, args) ← expandPackageBinders dir? args?
  if hasBinders then
    `($[$doc?:docComment]? @[«package»] def $id : Packager :=
        (fun $dir $args => $defn) $[$wds?]?)
  else
    `($[$doc?:docComment]? @[«package»] def $id : PackageConfig := $defn $[$wds?]?)

@[macro packageDecl]
def expandPackageDecl : Macro
| `($[$doc?:docComment]? package $id:ident) =>
  `($[$doc?:docComment]? @[«package»] def $id : PackageConfig := {name := $(quote id.getId)})
| `($[$doc?:docComment]? package $id:ident where $[$ds]*) =>
  `($[$doc?:docComment]? @[«package»] def $id : PackageConfig where
      name := $(quote id.getId) $[$ds]*)
| `($[$doc?:docComment]? package $id:ident : $ty := $defn $[$wds?]?) =>
  `($[$doc?:docComment]? @[«package»] def $id : $ty := $defn $[$wds?]?)
| `($[$doc?:docComment]? package $id:ident $[($dir?)]? $[($args?)]? := $defn $[$wds?]?) =>
  mkPackageDef id defn doc? dir? args? wds?
| `($[$doc?:docComment]? package $id:ident $[($dir?)]? $[($args?)]? { $[$fs $[,]?]* } $[$wds?]?) => do
  mkPackageDef id (← `({ name := $(quote id.getId), $[$fs]* })) doc? dir? args? wds?
| `($[$doc?:docComment]? package $id:ident $[($dir?)]? $[($args?)]? do $seq $[$wds?]?) => do
  let (_, dir, args) ← expandPackageBinders dir? args?
  `($[$doc?:docComment]? @[«package»] def $id : IOPackager :=
      (fun $dir $args => do $seq) $[$wds?]?)
| stx => Macro.throwErrorAt stx "ill-formed package declaration"

-- # Scripts

syntax scriptDeclSpec :=
  ident (ppSpace "(" Term.simpleBinder ")")? (declValSimple <|> declValDo)

scoped syntax (name := scriptDecl)
(docComment)? "script " scriptDeclSpec : command

@[macro scriptDecl]
def expandScriptDecl : Macro
| `($[$doc?:docComment]? script $id:ident $[($args?)]? do $seq $[$wds?]?) => do
  let args := args?.getD (← `(_))
  `($[$doc?:docComment]? @[«script»] def $id : ScriptFn := fun $args => do $seq $[$wds?]?)
| `($[$doc?:docComment]? script $id:ident $[($args?)]? := $defn $[$wds?]?) => do
  let args := args?.getD (← `(_))
  `($[$doc?:docComment]? @[«script»] def $id : ScriptFn := fun $args => $defn $[$wds?]?)
| stx => Macro.throwErrorAt stx "ill-formed script declaration"
