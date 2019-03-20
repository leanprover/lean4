/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.expr init.data.option.basic

namespace lean

inductive externEntry
| adhoc    (backend : name)
| inline   (backend : name) (pattern : string)
| standard (backend : name) (fn : string)
| foreign  (backend : name) (fn : string)

@[export lean.mkAdhocExtEntryCore]   def mkAdhocExtEntry   := externEntry.adhoc
@[export lean.mkInlineExtEntryCore]  def mkInlineExtEntry  := externEntry.inline
@[export lean.mkStdExtEntryCore]     def mkStdExtEntry     := externEntry.standard
@[export lean.mkForeignExtEntryCore] def mkForeignExtEntry := externEntry.foreign

/-
- `@[extern]`
   encoding: ```.entries = [adhoc `all]```
- `@[extern "levelHash"]`
   encoding: ```.entries = [standard `all "levelHash"]```
- `@[extern cpp "lean::stringSize" llvm "leanStrSize"]`
   encoding: ```.entries = [standard `cpp "lean::stringSize", standard `llvm "leanStrSize"]```
- `@[extern cpp inline "#1 + #2"]`
   encoding: ```.entries = [inline `cpp "#1 + #2"]```
- `@[extern cpp "foo" llvm adhoc]`
   encoding: ```.entries = [standard `cpp "foo", adhoc `llvm]```
- `@[extern 2 cpp "ioPrimPrintln"]`
   encoding: ```.arity = 2, .entries = [standard `cpp "ioPrimPrintln"]```
-/
structure externAttrData :=
(arity    : option nat := none)
(entries  : list externEntry)

@[export lean.mkExternAttrDataCore] def mkExternAttrData := externAttrData.mk

private def parseOptNum : nat → string.iterator → nat → string.iterator × nat
| 0     it r := (it, r)
| (n+1) it r :=
  if !it.hasNext then (it, r)
  else
    let c := it.curr in
    if '0' <= c && c <= '9'
    then parseOptNum n it.next (r*10 + (c.toNat - '0'.toNat))
    else (it, r)

def expandExternPatternAux (args : list string) : nat → string.iterator → string → string
| 0     it r := r
| (i+1) it r :=
  if ¬ it.hasNext then r
  else let c := it.curr in
    if c ≠ '#' then expandExternPatternAux i it.next (r.push c)
    else
      let it      := it.next in
      let (it, j) := parseOptNum it.remaining it 0 in
      let j       := j-1 in
      expandExternPatternAux i it (r ++ (args.nth j).getOrElse "")

@[export lean.expandExternPatternCore]
def expandExternPattern (pattern : string) (args : list string) : string :=
expandExternPatternAux args pattern.length pattern.mkIterator ""

def mkSimpleFnCall (fn : string) (args : list string) : string :=
fn ++ "(" ++ ((args.intersperse ", ").foldl (++) "") ++ ")"

def expandExternEntry : externEntry → list string → option string
| (externEntry.adhoc _) args        := none -- backend must expand it
| (externEntry.standard _ fn) args  := some (mkSimpleFnCall fn args)
| (externEntry.inline _ pat) args   := some (expandExternPattern pat args)
| (externEntry.foreign _ fn) args   := some (mkSimpleFnCall fn args)

def externEntry.backend : externEntry → name
| (externEntry.adhoc n)      := n
| (externEntry.inline n _)   := n
| (externEntry.standard n _) := n
| (externEntry.foreign n _)  := n

def getExternEntryForAux (backend : name) : list externEntry → option externEntry
| []      := none
| (e::es) :=
  if e.backend = `all then some e
  else if e.backend = backend then some e
  else getExternEntryForAux es

@[export lean.getExternEntryForCore]
def getExternEntryFor (d : externAttrData) (backend : name) : option externEntry :=
getExternEntryForAux backend d.entries

@[export lean.mkExternCallCore]
def mkExternCall (d : externAttrData) (backend : name) (args : list string) : option string :=
do e ← getExternEntryFor d backend,
   expandExternEntry e args

end lean
