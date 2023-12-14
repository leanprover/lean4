/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Command

set_option autoImplicit false

namespace Lean.Elab.WF

/-! # Support for `decreasing_by` -/

structure DecreasingByTactic where
  ref   : Syntax
  value : Lean.TSyntax `Lean.Parser.Tactic.tacticSeq
  deriving Inhabited

inductive DecreasingBy where
  | none
  | one (val : DecreasingByTactic)
  | many (map : NameMap DecreasingByTactic)
  deriving Inhabited

open Parser.Command in
/--
This function takes a user-specified `decreasing_by` clause (as `Sytnax`).
If it is a `decreasingByMany` (a set of clauses guarded by the function name) then
* checks that all mentioned names exist in the current declaration
* check that at most one function from each clique is mentioned
and sort the entries by function name.
-/
def expandDecreasingBy? (decreasingBy? : Option Syntax) (cliques : Array (Array Name)) : MacroM DecreasingBy := do
  let some decreasingBy := decreasingBy? | return DecreasingBy.none
  let ref := decreasingBy
  match decreasingBy with
  | `(decreasingBy|decreasing_by $hint1:tacticSeq) =>
    return DecreasingBy.one { ref, value := hint1 }
  | `(decreasingBy|decreasing_by $hints:decreasingByMany) => do
    let m ← hints.raw[0].getArgs.foldlM (init := {}) fun m arg => do
      let arg : TSyntax `decreasingByElement := ⟨arg⟩ -- cannot use syntax pattern match with lookahead
      let `(decreasingByElement| $declId:ident => $tac:tacticSeq) := arg | Macro.throwUnsupported
      let declName? := cliques.findSome? fun clique => clique.findSome? fun declName =>
        if declId.getId.isSuffixOf declName then some declName else none
      match declName? with
      | none => Macro.throwErrorAt declId s!"function '{declId.getId}' not found in current declaration"
      | some declName => return m.insert declName { ref := arg, value := tac }
    for clique in cliques do
      let mut found? := Option.none
      for declName in clique do
        if let some { ref, .. } := m.find? declName then
          if let some found := found? then
            Macro.throwErrorAt ref s!"invalid termination hint element, '{declName}' and '{found}' are in the same clique"
          found? := some declName
    return DecreasingBy.many m
  | _ => Macro.throwUnsupported

def DecreasingBy.markAsUsed (t : DecreasingBy) (clique : Array Name) : DecreasingBy :=
  match t with
  | DecreasingBy.none   => DecreasingBy.none
  | DecreasingBy.one .. => DecreasingBy.none
  | DecreasingBy.many m => Id.run do
    for declName in clique do
      if m.contains declName then
        let m := m.erase declName
        if m.isEmpty then
          return DecreasingBy.none
        else
          return DecreasingBy.many m
    return t

def DecreasingBy.find? (t : DecreasingBy) (clique : Array Name) : Option DecreasingByTactic :=
  match t with
  | DecreasingBy.none   => Option.none
  | DecreasingBy.one v  => some v
  | DecreasingBy.many m => clique.findSome? m.find?

def DecreasingBy.ensureAllUsed (t : DecreasingBy) : MacroM Unit := do
  match t with
  | DecreasingBy.one v   => Macro.throwErrorAt v.ref "unused termination hint element"
  | DecreasingBy.many m  => m.forM fun _ v => Macro.throwErrorAt v.ref "unused termination hint element"
  | _ => pure ()

/-! # Support for `termination_by` notation -/

/-- A single `termination_by` clause -/
structure TerminationByElement where
  ref       : Syntax
  declName  : Name
  vars      : TSyntaxArray [`ident, ``Lean.Parser.Term.hole]
  body      : Term
  implicit  : Bool
  deriving Inhabited

/-- `termination_by` clauses, grouped by clique -/
structure TerminationByClique where
  elements : Array TerminationByElement
  used     : Bool := false

/--
A `termination_by` hint, as specified by the user
-/
structure TerminationBy where
  cliques : Array TerminationByClique
  deriving Inhabited

/--
A `termination_by` hint, as applicable to a single clique
-/
abbrev TerminationWF := Array TerminationByElement

open Parser.Command in
/--
Expands the syntax for a `termination_by` clause, checking that
* each function is mentioned once
* each function mentioned actually occurs in the current declaration
* if anything is specified, then all functions have a clause
* the else-case (`_`) occurs only once, and only when needed

NB:
```
def terminationByElement   := leading_parser ppLine >> (ident <|> hole) >> many (ident <|> hole) >> " => " >> termParser >> optional ";"
def terminationBy          := leading_parser ppLine >> "termination_by " >> many1chIndent terminationByElement
```
-/
def expandTerminationBy? (hint? : Option Syntax) (cliques : Array (Array Name)) :
    MacroM TerminationBy := do
  let some hint := hint?  | return { cliques := #[] }
  let `(terminationBy|termination_by $elementStxs*) := hint | Macro.throwUnsupported
  let mut alreadyFound : NameSet := {}
  let mut elseElemStx? := none
  for elementStx in elementStxs do
    match elementStx with
    | `(terminationByElement|$ident:ident $_* => $_) =>
      let declSuffix := ident.getId
      if alreadyFound.contains declSuffix then
        withRef elementStx <| Macro.throwError s!"invalid `termination_by` syntax, `{declSuffix}` case has already been provided"
      alreadyFound := alreadyFound.insert declSuffix
      if cliques.all fun clique => clique.all fun declName => !declSuffix.isSuffixOf declName then
        withRef elementStx <| Macro.throwError s!"function '{declSuffix}' not found in current declaration"
    | `(terminationByElement|_ $_vars* => $_term) =>
      if elseElemStx?.isSome then
        withRef elementStx <| Macro.throwError "invalid `termination_by` syntax, the else-case (i.e., `_ ... => ...`) has already been specified"
      else
        elseElemStx? := some elementStx
    | _ => Macro.throwUnsupported
  let toElement (declName : Name) (elementStx : TSyntax ``terminationByElement) : TerminationByElement :=
    match elementStx with
    | `(terminationByElement|$ioh $vars* => $body:term) =>
    let implicit := !ioh.raw.isIdent
    { ref := elementStx, declName, vars, implicit, body }
    | _ => unreachable!
  let elementAppliesTo (declName : Name) : TSyntax ``terminationByElement → Bool
    | `(terminationByElement|$ident:ident $_* => $_) => ident.getId.isSuffixOf declName
    | _ => false
  let mut result := #[]
  let mut usedElse := false
  for clique in cliques do
    let mut elements := #[]
    for declName in clique do
      if let some elementStx := elementStxs.find? (elementAppliesTo declName) then
        elements := elements.push (toElement declName elementStx)
      else if let some elseElemStx := elseElemStx? then
        elements := elements.push (toElement declName elseElemStx)
        usedElse := true
    unless elements.isEmpty do
      if let some missing := clique.find? fun declName => elements.find? (·.declName == declName) |>.isNone then
        withRef elements[0]!.ref <| Macro.throwError s!"invalid `termination_by` syntax, missing case for function '{missing}'"
      result := result.push { elements }
  if !usedElse && elseElemStx?.isSome then
    withRef elseElemStx?.get! <| Macro.throwError s!"invalid `termination_by` syntax, unnecessary else-case"
  return ⟨result⟩

open Parser.Command in
def TerminationWF.unexpand (elements : TerminationWF) : MetaM Syntax := do
  let elementStxs ← elements.mapM fun element => do
    let fn : Ident := mkIdent (← unresolveNameGlobal element.declName)
    `(terminationByElement|$fn $element.vars* => $element.body)
  `(terminationBy|termination_by $elementStxs*)

def TerminationBy.markAsUsed (t : TerminationBy) (cliqueNames : Array Name) : TerminationBy :=
  .mk <| t.cliques.map fun clique =>
    if cliqueNames.any fun name => clique.elements.any fun elem => elem.declName == name then
      { clique with used := true }
    else
      clique

def TerminationBy.find? (t : TerminationBy) (cliqueNames : Array Name) : Option TerminationWF :=
  t.cliques.findSome? fun clique =>
    if cliqueNames.any fun name => clique.elements.any fun elem => elem.declName == name then
      some <| clique.elements
    else
      none

def TerminationByClique.allImplicit (c : TerminationByClique) : Bool :=
  c.elements.all fun elem => elem.implicit

def TerminationByClique.getExplicitElement? (c : TerminationByClique) : Option TerminationByElement :=
  c.elements.find? (!·.implicit)

def TerminationBy.ensureAllUsed (t : TerminationBy) : MacroM Unit := do
  let hasUsedAllImplicit := t.cliques.any fun c => c.allImplicit && c.used
  let mut reportedAllImplicit := true
  for clique in t.cliques do
    unless clique.used do
      if let some explicitElem := clique.getExplicitElement? then
        Macro.throwErrorAt explicitElem.ref "unused termination hint element"
      else if !hasUsedAllImplicit then
        unless reportedAllImplicit do
          reportedAllImplicit := true
          Macro.throwErrorAt clique.elements[0]!.ref "unused termination hint element"

end Lean.Elab.WF
