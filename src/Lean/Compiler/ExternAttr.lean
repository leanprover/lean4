/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Environment
import Lean.Attributes
import Lean.ProjFns
import Lean.Meta.Basic

namespace Lean

inductive ExternEntry where
  | adhoc    (backend : Name)
  | inline   (backend : Name) (pattern : String)
  | standard (backend : Name) (fn : String)
  | foreign  (backend : Name) (fn : String)

/--
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
   encoding: ```.arity? = 2, .entries = [standard `cpp "ioPrimPrintln"]```
-/
structure ExternAttrData where
  arity?   : Option Nat := none
  entries  : List ExternEntry
  deriving Inhabited

-- def externEntry := leading_parser optional ident >> optional (nonReservedSymbol "inline ") >> strLit
-- @[builtin_attr_parser] def extern     := leading_parser nonReservedSymbol "extern " >> optional numLit >> many externEntry
private def syntaxToExternAttrData (stx : Syntax) : AttrM ExternAttrData := do
  let arity?  := if stx[1].isNone then none else some <| stx[1][0].isNatLit?.getD 0
  let entriesStx := stx[2].getArgs
  if entriesStx.size == 0 && arity? == none then
    return { entries := [ ExternEntry.adhoc `all ] }
  let mut entries := #[]
  for entryStx in entriesStx do
    let backend := if entryStx[0].isNone then `all else entryStx[0][0].getId
    let str ← match entryStx[2].isStrLit? with
      | none     => throwErrorAt entryStx[2] "string literal expected"
      | some str => pure str
    if entryStx[1].isNone then
      entries := entries.push <| ExternEntry.standard backend str
    else
      entries := entries.push <| ExternEntry.inline backend str
  return { arity? := arity?, entries := entries.toList }

@[extern "lean_add_extern"]
opaque addExtern (env : Environment) (n : Name) : ExceptT String Id Environment

builtin_initialize externAttr : ParametricAttribute ExternAttrData ←
  registerParametricAttribute {
    name := `extern
    descr := "builtin and foreign functions"
    getParam := fun _ stx => syntaxToExternAttrData stx
    afterSet := fun declName _ => do
      let mut env ← getEnv
      if env.isProjectionFn declName || env.isConstructor declName then do
        env ← ofExcept <| addExtern env declName
        setEnv env
      else
        pure ()
  }

@[export lean_get_extern_attr_data]
def getExternAttrData? (env : Environment) (n : Name) : Option ExternAttrData :=
  externAttr.getParam? env n

private def parseOptNum : Nat → String.Iterator → Nat → String.Iterator × Nat
  | 0,   it, r => (it, r)
  | n+1, it, r =>
    if !it.hasNext then (it, r)
    else
      let c := it.curr
      if '0' <= c && c <= '9'
      then parseOptNum n it.next (r*10 + (c.toNat - '0'.toNat))
      else (it, r)

def expandExternPatternAux (args : List String) : Nat → String.Iterator → String → String
  | 0,   _,  r => r
  | i+1, it, r =>
    if ¬ it.hasNext then r
    else let c := it.curr
      if c ≠ '#' then expandExternPatternAux args i it.next (r.push c)
      else
        let it      := it.next
        let (it, j) := parseOptNum it.remainingBytes it 0
        let j       := j-1
        expandExternPatternAux args i it (r ++ args.getD j "")

def expandExternPattern (pattern : String) (args : List String) : String :=
  expandExternPatternAux args pattern.length pattern.mkIterator ""

def mkSimpleFnCall (fn : String) (args : List String) : String :=
  fn ++ "(" ++ ((args.intersperse ", ").foldl (·++·) "") ++ ")"

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
    else getExternEntryForAux backend es

def getExternEntryFor (d : ExternAttrData) (backend : Name) : Option ExternEntry :=
  getExternEntryForAux backend d.entries

def isExtern (env : Environment) (fn : Name) : Bool :=
  getExternAttrData? env fn |>.isSome

/-- We say a Lean function marked as `[extern "<c_fn_nane>"]` is for all backends, and it is implemented using `extern "C"`.
   Thus, there is no name mangling. -/
def isExternC (env : Environment) (fn : Name) : Bool :=
  match getExternAttrData? env fn with
  | some { entries := [ ExternEntry.standard `all _ ], .. } => true
  | _ => false

def getExternNameFor (env : Environment) (backend : Name) (fn : Name) : Option String := do
  let data? ← getExternAttrData? env fn
  let entry ← getExternEntryFor data? backend
  match entry with
  | ExternEntry.standard _ n => pure n
  | ExternEntry.foreign _ n  => pure n
  | _ => failure

private def getExternConstArity (declName : Name) : CoreM Nat := do
  let fromSignature : Unit → CoreM Nat := fun _ => do
    let cinfo ← getConstInfo declName
    let (arity, _) ← (Meta.forallTelescopeReducing cinfo.type fun xs _ => pure xs.size : MetaM Nat).run
    return arity
  let env ← getEnv
  match getExternAttrData? env declName with
  | none      => fromSignature ()
  | some data => match data.arity? with
    | some arity => return arity
    | none       => fromSignature ()

@[export lean_get_extern_const_arity]
def getExternConstArityExport (env : Environment) (declName : Name) : IO (Option Nat) := do
  try
    let (arity, _) ← (getExternConstArity declName).toIO { fileName := "<compiler>", fileMap := default } { env := env }
    return some arity
  catch
   | IO.Error.userError _   => return none
   | _  => return none

end Lean
