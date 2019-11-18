/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Option.Basic
import Init.Lean.Expr
import Init.Lean.Environment
import Init.Lean.Attributes
import Init.Lean.ProjFns

namespace Lean

inductive ExternEntry
| adhoc    (backend : Name)
| inline   (backend : Name) (pattern : String)
| standard (backend : Name) (fn : String)
| foreign  (backend : Name) (fn : String)

/-
- `@[extern]`
   encoding: ```.entries = [adhoc `all]```
- `@[extern "level_hash"]`
   encoding: ```.entries = [standard `all "levelHash"]```
- `@[extern cpp "lean::string_size" llvm "lean_str_size"]`
   encoding: ```.entries = [standard `cpp "lean::string_size", standard `llvm "leanStrSize"]```
- `@[extern cpp inline "#1 + #2"]`
   encoding: ```.entries = [inline `cpp "#1 + #2"]```
- `@[extern cpp "foo" llvm adhoc]`
   encoding: ```.entries = [standard `cpp "foo", adhoc `llvm]```
- `@[extern 2 cpp "io_prim_println"]`
   encoding: ```.arity = 2, .entries = [standard `cpp "ioPrimPrintln"]```
-/
structure ExternAttrData :=
(arity    : Option Nat := none)
(entries  : List ExternEntry)

instance ExternAttrData.inhabited : Inhabited ExternAttrData := ⟨{ entries := [] }⟩

private partial def syntaxToExternEntries (a : Array Syntax) : Nat → List ExternEntry → Except String (List ExternEntry)
| i, entries =>
  if i == a.size then Except.ok entries
  else match a.get! i with
    | Syntax.ident _ _ backend _ =>
      let i := i + 1;
      if i == a.size then Except.error "string or identifier expected"
      else match (a.get! i).isIdOrAtom with
        | some "adhoc"  => syntaxToExternEntries (i+1) (ExternEntry.adhoc backend :: entries)
        | some "inline" =>
          let i := i + 1;
          match (a.get! i).isStrLit with
          | some pattern => syntaxToExternEntries (i+1) (ExternEntry.inline backend pattern :: entries)
          | none => Except.error "string literal expected"
        | _ => match (a.get! i).isStrLit with
          | some fn => syntaxToExternEntries (i+1) (ExternEntry.standard backend fn :: entries)
          | none => Except.error "string literal expected"
    | _ => Except.error "identifier expected"

private def syntaxToExternAttrData (s : Syntax) : ExceptT String Id ExternAttrData :=
match s with
| Syntax.missing => Except.ok { entries := [ ExternEntry.adhoc `all ] }
| Syntax.node _ args =>
  if args.size == 0 then Except.error "unexpected kind of argument"
  else
    let (arity, i) : Option Nat × Nat := match (args.get! 0).isNatLit with
      | some arity => (some arity, 1)
      | none       => (none, 0);
    match (args.get! i).isStrLit with
    | some str =>
      if args.size == i+1 then
        Except.ok { arity := arity, entries := [ ExternEntry.standard `all str ] }
      else
        Except.error "invalid extern attribute"
    | none => match syntaxToExternEntries args i [] with
      | Except.ok entries => Except.ok { arity := arity, entries := entries }
      | Except.error msg  => Except.error msg
| _ => Except.error "unexpected kind of argument"

@[extern "lean_add_extern"]
constant addExtern (env : Environment) (n : Name) : ExceptT String Id Environment := arbitrary _

def mkExternAttr : IO (ParametricAttribute ExternAttrData) :=
registerParametricAttribute `extern "builtin and foreign functions"
  (fun _ _ => syntaxToExternAttrData)
  (fun env declName _ =>
    if env.isProjectionFn declName || env.isConstructor declName then
      addExtern env declName
    else
      pure env)

@[init mkExternAttr]
constant externAttr : ParametricAttribute ExternAttrData := arbitrary _

@[export lean_get_extern_attr_data]
def getExternAttrData (env : Environment) (n : Name) : Option ExternAttrData :=
externAttr.getParam env n

private def parseOptNum : Nat → String.Iterator → Nat → String.Iterator × Nat
| 0,   it, r => (it, r)
| n+1, it, r =>
  if !it.hasNext then (it, r)
  else
    let c := it.curr;
    if '0' <= c && c <= '9'
    then parseOptNum n it.next (r*10 + (c.toNat - '0'.toNat))
    else (it, r)

def expandExternPatternAux (args : List String) : Nat → String.Iterator → String → String
| 0,   it, r => r
| i+1, it, r =>
  if ¬ it.hasNext then r
  else let c := it.curr;
    if c ≠ '#' then expandExternPatternAux i it.next (r.push c)
    else
      let it      := it.next;
      let (it, j) := parseOptNum it.remainingBytes it 0;
      let j       := j-1;
      expandExternPatternAux i it (r ++ args.getD j "")

def expandExternPattern (pattern : String) (args : List String) : String :=
expandExternPatternAux args pattern.length pattern.mkIterator ""

def mkSimpleFnCall (fn : String) (args : List String) : String :=
fn ++ "(" ++ ((args.intersperse ", ").foldl HasAppend.append "") ++ ")"

def ExternEntry.backend : ExternEntry → Name
| ExternEntry.adhoc n      => n
| ExternEntry.inline n _   => n
| ExternEntry.standard n _ => n
| ExternEntry.foreign n _  => n

def getExternEntryForAux (backend : Name) : List ExternEntry → Option ExternEntry
| []    => none
| e::es =>
  if e.backend == `all then some e
  else if e.backend == backend then some e
  else getExternEntryForAux es

def getExternEntryFor (d : ExternAttrData) (backend : Name) : Option ExternEntry :=
getExternEntryForAux backend d.entries

def isExtern (env : Environment) (fn : Name) : Bool :=
(getExternAttrData env fn).isSome

/- We say a Lean function marked as `[extern "<c_fn_nane>"]` is for all backends, and it is implemented using `extern "C"`.
   Thus, there is no name mangling. -/
def isExternC (env : Environment) (fn : Name) : Bool :=
match getExternAttrData env fn with
| some { entries := [ ExternEntry.standard `all _ ], .. } => true
| _ => false

def getExternNameFor (env : Environment) (backend : Name) (fn : Name) : Option String :=
do data ← getExternAttrData env fn;
   entry ← getExternEntryFor data backend;
   match entry with
   | ExternEntry.standard _ n => pure n
   | ExternEntry.foreign _ n  => pure n
   | _ => failure

end Lean
