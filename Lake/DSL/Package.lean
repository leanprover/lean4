/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Package
import Lake.DSL.Attributes
import Lake.DSL.DeclUtil

namespace Lake.DSL
open Lean Parser Command

syntax packageDeclWithBinders :=
  (ppSpace "(" Term.simpleBinder ")")? -- dir
  (ppSpace "(" Term.simpleBinder ")")? -- args
  (declValSimple <|> declValStruct <|> declValDo)

syntax packageDeclSpec :=
  ident (Command.whereStructInst <|> declValTyped <|> packageDeclWithBinders)?

def expandPackageBinders
: (dir? : Option Syntax) → (args? : Option Syntax) → MacroM (Bool × Syntax × Syntax)
| none,     none      => do let hole ← `(_); return (false, hole, hole)
| some dir, none      => return (true, dir, ← `(_))
| none,     some args => return (true, ← `(_), args)
| some dir, some args => return (true, dir, args)

def mkSimplePackageDecl
(doc? : Option Syntax) (attrs : Array Syntax) (id : Syntax) (defn : Syntax)
(dir? : Option Syntax) (args? : Option Syntax) (wds? : Option Syntax) : MacroM Syntax := do
  let (hasBinders, dir, args) ← expandPackageBinders dir? args?
  if hasBinders then
    `($[$doc?:docComment]? @[$attrs,*] def $id : Packager :=
        (fun $dir $args => $defn) $[$wds?]?)
  else
    `($[$doc?:docComment]? @[$attrs,*] def $id : PackageConfig := $defn $[$wds?]?)

/-- The name given to the definition created by the `package` syntax. -/
def packageDeclName := `_package

def mkPackageDecl (doc? : Option Syntax) (attrs : Array Syntax) : Macro
| `(packageDeclSpec| $id:ident) =>
  `($[$doc?:docComment]? @[$attrs,*] def $(mkIdentFrom id packageDeclName) : PackageConfig :=
    {name := $(quote id.getId)})
| `(packageDeclSpec| $id:ident where $[$ds]* $[$wds?]?) =>
  `($[$doc?:docComment]? @[$attrs,*] def $(mkIdentFrom id packageDeclName) : PackageConfig where
      name := $(quote id.getId) $[$ds]* $[$wds?]?)
| `(packageDeclSpec| $id:ident : $ty := $defn $[$wds?]?) =>
  `($[$doc?:docComment]? @[$attrs,*] def $(mkIdentFrom id packageDeclName) : $ty := $defn $[$wds?]?)
| `(packageDeclSpec| $id:ident $[($dir?)]? $[($args?)]? := $defn $[$wds?]?) =>
  mkSimplePackageDecl doc? attrs (mkIdentFrom id packageDeclName) defn dir? args? wds?
| `(packageDeclSpec| $id:ident $[($dir?)]? $[($args?)]? { $[$fs $[,]?]* } $[$wds?]?) => do
  let defn ← `({ name := $(quote id.getId), $[$fs]* })
  mkSimplePackageDecl doc? attrs (mkIdentFrom id packageDeclName) defn dir? args? wds?
| `(packageDeclSpec| $id:ident $[($dir?)]? $[($args?)]? do $seq $[$wds?]?) => do
  let (_, dir, args) ← expandPackageBinders dir? args?
  `($[$doc?:docComment]? @[$attrs,*] def $(mkIdentFrom id packageDeclName) : IOPackager :=
      (fun $dir $args => do $seq) $[$wds?]?)
| stx => Macro.throwErrorAt stx "ill-formed package declaration"

/--
Command that declares the configuration of a Lake package.  Has many forms:

```lean
package «pkg-name»
package «pkg-name» { /- config opts -/ }
package «pkg-name» where /- config opts -/
package «pkg-name» : PackageConfig := /- config -/
```

There can only be one package configuration per lakefile.
The defined package configuration will be available for reference as `_package`.
-/
scoped macro (name := packageDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"package " spec:packageDeclSpec : command => do
  let attr ← `(Term.attrInstance| «package»)
  let attrs := #[attr] ++ expandAttrs attrs?
  mkPackageDecl doc? attrs spec
