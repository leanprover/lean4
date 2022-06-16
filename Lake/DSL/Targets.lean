/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.DeclUtil
import Lake.DSL.Attributes
import Lake.Config.Targets

namespace Lake.DSL
open Lean Parser Command

--------------------------------------------------------------------------------
-- # Lean Library & Executable Targets
--------------------------------------------------------------------------------

syntax targetDeclSpec :=
  ident (Command.whereStructInst <|> declValOptTyped <|> declValStruct)?

def mkTargetDecl
(doc? : Option Syntax) (attrs : Array Syntax) (ty : Syntax)
: (spec : Syntax) → MacroM Syntax
| `(targetDeclSpec| $id:ident) =>
  `($[$doc?:docComment]? @[$attrs,*] def $id : $ty :=
    {name := $(quote id.getId)})
| `(targetDeclSpec| $id:ident where $ds;* $[$wds?]?) =>
  `($[$doc?:docComment]? @[$attrs,*] def $id : $ty where
      name := $(quote id.getId); $ds;* $[$wds?]?)
| `(targetDeclSpec| $id:ident $[: $ty?]? := $defn $[$wds?]?) =>
  `($[$doc?:docComment]? @[$attrs,*] def $id : $(ty?.getD ty) := $defn $[$wds?]?)
| `(targetDeclSpec| $id:ident { $[$fs $[,]?]* } $[$wds?]?) => do
  let defn ← `({ name := $(quote id.getId), $fs,* })
  `($[$doc?:docComment]? @[$attrs,*] def $id : $ty := $defn $[$wds?]?)
| stx => Macro.throwErrorAt stx "ill-formed target declaration"

/--
Define a new Lean library target for the package.
Can optionally be provided with a configuration of type `LeanLibConfig`.
Has many forms:

```lean
lean_lib «target-name»
lean_lib «target-name» { /- config opts -/ }
lean_lib «target-name» where /- config opts -/
lean_lib «target-name» := /- config -/
```
-/
scoped macro (name := leanLibDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"lean_lib " spec:targetDeclSpec : command => do
  let attr ← `(Term.attrInstance| leanLib)
  let ty := mkCIdentFrom (← getRef) ``LeanLibConfig
  let attrs := #[attr] ++ expandAttrs attrs?
  mkTargetDecl doc? attrs ty spec

/--
Define a new Lean binary executable target for the package.
Can optionally be provided with a configuration of type `LeanExeConfig`.
Has many forms:

```lean
lean_exe «target-name»
lean_exe «target-name» { /- config opts -/ }
lean_exe «target-name» where /- config opts -/
lean_exe «target-name» := /- config -/
```
-/
scoped macro (name := leanExeDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"lean_exe " spec:targetDeclSpec : command => do
  let attr ← `(Term.attrInstance| leanExe)
  let ty := mkCIdentFrom (← getRef) ``LeanExeConfig
  let attrs := #[attr] ++ expandAttrs attrs?
  mkTargetDecl doc? attrs ty spec

--------------------------------------------------------------------------------
-- # External Library Target
--------------------------------------------------------------------------------

syntax externLibDeclSpec :=
  ident optional(Term.typeSpec) declValSimple

/--
Define a new external library target for the package. Has one form:

```lean
extern_lib «target-name» := /- term of type `FileTarget` -/
```
-/
scoped macro (name := externLibDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"extern_lib " spec:externLibDeclSpec : command => do
  match spec with
  | `(externLibDeclSpec| $id:ident $[: $ty?]? := $defn $[$wds?]?) =>
    let attr ← `(Term.attrInstance| externLib)
    let ty := ty?.getD <| mkCIdentFrom (← getRef) ``ExternLibConfig
    let attrs := #[attr] ++ expandAttrs attrs?
    `($[$doc?:docComment]? @[$attrs,*] def $id : $ty :=
      {name := $(quote id.getId), target := $defn} $[$wds?]?)
  | stx => Macro.throwErrorAt stx "ill-formed external library declaration"
