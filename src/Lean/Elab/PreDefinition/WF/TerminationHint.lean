/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Command

namespace Lean.Elab.WF

/-! # Support for `decreasing_by` and `termination_by'` notations -/

structure TerminationHintValue where
  ref   : Syntax
  value : Syntax
  deriving Inhabited

inductive TerminationHint where
  | none
  | one (val : TerminationHintValue)
  | many (map : NameMap TerminationHintValue)
  deriving Inhabited

open Parser.Command in
/--
This function takes a user-specified `decreasing_by` or `termination_by'` clause (as `Sytnax`).
If it is a `terminathionHintMany` (a set of clauses guarded by the function name) then
* checks that all mentioned names exist in the current declaration
* check that at most one function from each clique is mentioned
and sort the entries by function name.
-/
def expandTerminationHint (terminationHint? : Option Syntax) (cliques : Array (Array Name)) : MacroM TerminationHint := do
  let some terminationHint := terminationHint? | return TerminationHint.none
  let ref := terminationHint
  match terminationHint with
  | `(terminationByCore|termination_by' $hint1:terminationHint1)
  | `(decreasingBy|decreasing_by $hint1:terminationHint1) =>
    return TerminationHint.one { ref, value := hint1.raw[0] }
  | `(terminationByCore|termination_by' $hints:terminationHintMany)
  | `(decreasingBy|decreasing_by $hints:terminationHintMany) => do
    let m ← hints.raw[0].getArgs.foldlM (init := {}) fun m arg =>
      let declName? := cliques.findSome? fun clique => clique.findSome? fun declName =>
        if arg[0].getId.isSuffixOf declName then some declName else none
      match declName? with
      | none => Macro.throwErrorAt arg[0] s!"function '{arg[0].getId}' not found in current declaration"
      | some declName => return m.insert declName { ref := arg, value := arg[2] }
    for clique in cliques do
      let mut found? := Option.none
      for declName in clique do
        if let some { ref, .. } := m.find? declName then
          if let some found := found? then
            Macro.throwErrorAt ref s!"invalid termination hint element, '{declName}' and '{found}' are in the same clique"
          found? := some declName
    return TerminationHint.many m
  | _ => Macro.throwUnsupported

def TerminationHint.markAsUsed (t : TerminationHint) (clique : Array Name) : TerminationHint :=
  match t with
  | TerminationHint.none   => TerminationHint.none
  | TerminationHint.one .. => TerminationHint.none
  | TerminationHint.many m => Id.run do
    for declName in clique do
      if m.contains declName then
        let m := m.erase declName
        if m.isEmpty then
          return TerminationHint.none
        else
          return TerminationHint.many m
    return t

def TerminationHint.find? (t : TerminationHint) (clique : Array Name) : Option TerminationHintValue :=
  match t with
  | TerminationHint.none   => Option.none
  | TerminationHint.one v  => some v
  | TerminationHint.many m => clique.findSome? m.find?

def TerminationHint.ensureAllUsed (t : TerminationHint) : MacroM Unit := do
  match t with
  | TerminationHint.one v   => Macro.throwErrorAt v.ref "unused termination hint element"
  | TerminationHint.many m  => m.forM fun _ v => Macro.throwErrorAt v.ref "unused termination hint element"
  | _ => pure ()

/-! # Support for `termination_by` and `termination_by'` notation -/

/-- A single `termination_by` clause -/
structure TerminationByElement where
  ref       : Syntax
  declName  : Name
  vars      : Array Syntax
  body      : Syntax
  implicit  : Bool
  deriving Inhabited

/-- `terminatoin_by` clauses, grouped by clique -/
structure TerminationByClique where
  elements : Array TerminationByElement
  used     : Bool := false

/--
A `termination_by'` or `termination_by` hint, as specified by the user
-/
inductive TerminationBy where
  /-- `termination_by'` -/
  | core (hint : TerminationHint)
  /-- `termination_by` -/
  | ext  (cliques : Array TerminationByClique)
  deriving Inhabited

/--
A `termination_by'` or `termination_by` hint, as applicable to a single clique
-/
inductive TerminationWF where
  | core (stx : Syntax)
  | ext  (clique : Array TerminationByElement)

/-
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
open Parser.Command in
private def expandTerminationByNonCore (hint : Syntax) (cliques : Array (Array Name)) : MacroM TerminationBy := do
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
  return TerminationBy.ext result

/--
Expands the syntax for a `termination_by` or `termination_by'` clause, using the appropriate function
-/
def expandTerminationBy (hint? : Option Syntax) (cliques : Array (Array Name)) : MacroM TerminationBy :=
  if let some hint := hint? then
    if hint.isOfKind ``Parser.Command.terminationByCore then
      return TerminationBy.core (← expandTerminationHint hint? cliques)
    else if hint.isOfKind ``Parser.Command.terminationBy then
      expandTerminationByNonCore hint cliques
    else
      Macro.throwUnsupported
  else
      return TerminationBy.core TerminationHint.none

open Parser.Command in
def TerminationWF.unexpand : TerminationWF → MetaM Syntax
  | .ext elements => do
    let elementStxs ← elements.mapM fun element => do
      let fn : Ident := mkIdent (← unresolveNameGlobal element.declName)
      let body : Term := ⟨element.body⟩
      let vars : Array Ident := element.vars.map TSyntax.mk
      `(terminationByElement|$fn $vars* => $body)
    `(terminationBy|termination_by $elementStxs*)
  | .core _ => unreachable! -- we don't synthetize termination_by' syntax

def TerminationBy.markAsUsed (t : TerminationBy) (cliqueNames : Array Name) : TerminationBy :=
  match t with
  | core hint   => core (hint.markAsUsed cliqueNames)
  | ext cliques => ext <| cliques.map fun clique =>
    if cliqueNames.any fun name => clique.elements.any fun elem => elem.declName == name then
      { clique with used := true }
    else
      clique

def TerminationBy.find? (t : TerminationBy) (cliqueNames : Array Name) : Option TerminationWF :=
  match t with
  | core hint => hint.find? cliqueNames |>.map fun v => TerminationWF.core v.value
  | ext cliques =>
    cliques.findSome? fun clique =>
      if cliqueNames.any fun name => clique.elements.any fun elem => elem.declName == name then
        some <| TerminationWF.ext clique.elements
      else
        none

def TerminationByClique.allImplicit (c : TerminationByClique) : Bool :=
  c.elements.all fun elem => elem.implicit

def TerminationByClique.getExplicitElement? (c : TerminationByClique) : Option TerminationByElement :=
  c.elements.find? (!·.implicit)

def TerminationBy.ensureAllUsed (t : TerminationBy) : MacroM Unit :=
  match t with
  | core hint => hint.ensureAllUsed
  | ext cliques => do
    let hasUsedAllImplicit := cliques.any fun c => c.allImplicit && c.used
    let mut reportedAllImplicit := true
    for clique in cliques do
      unless clique.used do
        if let some explicitElem := clique.getExplicitElement? then
          Macro.throwErrorAt explicitElem.ref "unused termination hint element"
        else if !hasUsedAllImplicit then
          unless reportedAllImplicit do
            reportedAllImplicit := true
            Macro.throwErrorAt clique.elements[0]!.ref "unused termination hint element"

end Lean.Elab.WF
