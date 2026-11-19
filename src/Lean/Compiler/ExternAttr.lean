/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.ProjFns
public import Lean.Attributes
import Init.Data.String.Lemmas.Order
import Init.Data.String.OrderInstances
import Init.Data.Order.Lemmas

public section

namespace Lean

inductive ExternEntry where
  | adhoc    (backend : Name)
  | inline   (backend : Name) (pattern : String)
  | standard (backend : Name) (fn : String)
  /-- Call to a Lean function without exported IR. -/
  | opaque
  deriving BEq, Hashable

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
-/
structure ExternAttrData where
  entries  : List ExternEntry
  deriving Inhabited, BEq, Hashable

-- def externEntry := leading_parser optional ident >> optional (nonReservedSymbol "inline ") >> strLit
-- @[builtin_attr_parser] def extern     := leading_parser nonReservedSymbol "extern " >> optional numLit >> many externEntry
private def syntaxToExternAttrData (stx : Syntax) : AttrM ExternAttrData := do
  let entriesStx := stx[1].getArgs
  if entriesStx.size == 0 then
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
  return { entries := entries.toList }

builtin_initialize externAttr : ParametricAttribute ExternAttrData ←
  registerParametricAttribute {
    name := `extern
    descr := "builtin and foreign functions"
    getParam := fun _ stx => syntaxToExternAttrData stx
    afterSet := fun declName externAttrData => do
      let env ← getEnv
      if env.isProjectionFn declName || env.isConstructor declName then
        if let some (.thmInfo ..) := env.find? declName then
          -- We should not mark theorems as extern
          return ()
        compileDecls #[declName]
  }

def getExternAttrData? (env : Environment) (n : Name) : Option ExternAttrData :=
  externAttr.getParam? env n

private def parseOptNum (pattern : String.Slice) (it : pattern.Pos) (r : Nat) : pattern.Pos × Nat :=
  if h : it.IsAtEnd then (it, r)
  else
    let c := it.get h
    if '0' <= c && c <= '9'
    then
      parseOptNum pattern (it.next h) (r*10 + (c.toNat - '0'.toNat))
    else (it, r)
termination_by it

def expandExternPatternAux (args : List String) (pattern : String) (it : pattern.Pos) (r : String) : String :=
  if h : it.IsAtEnd then r
  else let c := it.get h
    if c ≠ '#' then expandExternPatternAux args pattern (it.next h) (r.push c)
    else
      let it₁      := it.next h
      let (it₂, j) := parseOptNum (pattern.sliceFrom it₁) (String.Slice.startPos _) 0
      let j       := j-1
      have : it < String.Pos.ofSliceFrom it₂ := Std.lt_of_lt_of_le String.Pos.lt_next String.Pos.le_ofSliceFrom
      expandExternPatternAux args pattern (String.Pos.ofSliceFrom it₂) (r ++ args.getD j "")
termination_by it

def expandExternPattern (pattern : String) (args : List String) : String :=
  expandExternPatternAux args pattern pattern.startPos ""

def mkSimpleFnCall (fn : String) (args : List String) : String :=
  fn ++ "(" ++ ((args.intersperse ", ").foldl (·++·) "") ++ ")"

def ExternEntry.backend : ExternEntry → Name
  | ExternEntry.adhoc n      => n
  | ExternEntry.inline n _   => n
  | ExternEntry.standard n _ => n
  | ExternEntry.opaque ..    => `all

def getExternEntryForAux (backend : Name) (entries : List ExternEntry) : Option ExternEntry :=
  entries.find? fun e =>
    e.backend == `all || e.backend == backend

def getExternEntryFor (d : ExternAttrData) (backend : Name) : Option ExternEntry :=
  getExternEntryForAux backend d.entries

def isExtern (env : Environment) (fn : Name) : Bool :=
  getExternAttrData? env fn |>.isSome

/-- We say a Lean function marked as `[extern "<c_fn_name>"]` is for all backends, and it is implemented using `extern "C"`.
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
  | _ => failure

end Lean
