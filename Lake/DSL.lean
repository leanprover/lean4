import Lean.Parser
import Lake.Package

open Lean Parser
namespace Lake.DSL

syntax packageStruct :=
  "{" manyIndent(group(Term.structInstField optional(", "))) "}"

syntax packageDeclValSpecial :=
  (packageStruct <|> (ppSpace Term.do)) (Term.whereDecls)?

syntax packageDeclWithBinders :=
  (ppSpace "(" Term.simpleBinder ")")? -- dir
  (ppSpace "(" Term.simpleBinder ")")? -- args
  ppSpace (Command.declValSimple <|> packageDeclValSpecial)

syntax packageDeclTyped :=
  Term.typeSpec Command.declValSimple

scoped syntax (name := packageDecl) declModifiers
"package" (Term.whereDecls <|> packageDeclTyped <|> packageDeclWithBinders) : command

def expandPackageBinders
: (dir? : Option Syntax) → (args? : Option Syntax) → MacroM (Bool × Syntax × Syntax)
| none,     none      => do let hole ← `(_); (false, hole, hole)
| some dir, none      => do (true, dir, ← `(_))
| none,     some args => do (true, ← `(_), args)
| some dir, some args => do (true, dir, args)

def mkPackageDef (defn : Syntax) (mods : Syntax)
(dir? : Option Syntax) (args? : Option Syntax) (wds? : Option Syntax) : MacroM Syntax := do
  let (hasBinders, dir, args) ← expandPackageBinders dir? args?
  if hasBinders then
    `($mods:declModifiers def $(mkIdent `package) : Packager :=
        (fun $dir $args => $defn) $[$wds?]?)
  else
    `($mods:declModifiers def $(mkIdent `package) : PackageConfig := $defn $[$wds?]?)

@[macro packageDecl]
def expandPackageDecl : Macro
| `($mods:declModifiers package where $[$ds]*) =>
  `($mods:declModifiers def $(mkIdent `package) : PackageConfig where $[$ds]*)
| `($mods:declModifiers package : $ty := $defn $[$wds?]?) =>
  `($mods:declModifiers def $(mkIdent `package) : $ty := $defn $[$wds?]?)
| `($mods:declModifiers package $[($dir?)]? $[($args?)]? := $defn $[$wds?]?) =>
  mkPackageDef defn mods dir? args? wds?
| `($mods:declModifiers package $[($dir?)]? $[($args?)]? { $[$fs $[,]?]* } $[$wds?]?) => do
  mkPackageDef (← `({ $[$fs]* })) mods dir? args? wds?
| `($mods:declModifiers package $[($dir?)]? $[($args?)]? do $seq $[$wds?]?) => do
  let (_, dir, args) ← expandPackageBinders dir? args?
  `($mods:declModifiers def $(mkIdent `package) : IOPackager :=
      (fun $dir $args => do $seq) $[$wds?]?)
| stx => Macro.throwErrorAt stx "ill-formed package declaration"
