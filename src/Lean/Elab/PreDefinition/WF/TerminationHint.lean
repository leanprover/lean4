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

def expandTerminationHint (terminationHint? : Option Syntax) (cliques : Array (Array Name)) : MacroM TerminationHint := do
  if let some terminationHint := terminationHint? then
    let ref := terminationHint
    let terminationHint := terminationHint[1]
    if terminationHint.getKind == ``Parser.Command.terminationHint1 then
      return TerminationHint.one { ref, value := terminationHint[0] }
    else if terminationHint.getKind == ``Parser.Command.terminationHintMany then
      let m ← terminationHint[0].getArgs.foldlM (init := {}) fun m arg =>
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
    else
      Macro.throwUnsupported
  else
    return TerminationHint.none

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

/-! # Support for `termination_by` notation -/

structure TerminationByElement where
  ref       : Syntax
  declName  : Name
  vars      : Array Syntax
  body      : Syntax
  implicit  : Bool
  deriving Inhabited

structure TerminationByClique where
  elements : Array TerminationByElement
  used     : Bool := false

inductive TerminationBy where
  | core (hint : TerminationHint)
  | ext  (cliques : Array TerminationByClique)
  deriving Inhabited

inductive TerminationWF where
  | core (stx : Syntax)
  | ext  (clique : Array TerminationByElement)

/-
```
def terminationByElement   := leading_parser ppLine >> (ident <|> hole) >> many (ident <|> hole) >> " => " >> termParser >> optional ";"
def terminationBy          := leading_parser ppLine >> "termination_by " >> many1chIndent terminationByElement
```
-/
private def expandTerminationByNonCore (hint : Syntax) (cliques : Array (Array Name)) : MacroM TerminationBy := do
  let elementStxs := hint[1].getArgs
  let mut alreadyFound : NameSet := {}
  let mut elseElemStx? := none
  for elementStx in elementStxs do
    let declStx := elementStx[0]
    if declStx.isIdent then
      let declSuffix := declStx.getId
      if alreadyFound.contains declSuffix then
        withRef elementStx <| Macro.throwError s!"invalid `termination_by` syntax, `{declSuffix}` case has already been provided"
      alreadyFound := alreadyFound.insert declSuffix
      if cliques.all fun clique => clique.all fun declName => !declSuffix.isSuffixOf declName then
        withRef elementStx <| Macro.throwError s!"function '{declSuffix}' not found in current declaration"
    else if elseElemStx?.isSome then
      withRef elementStx <| Macro.throwError "invalid `termination_by` syntax, the else-case (i.e., `_ ... => ...`) has already been specified"
    else
      elseElemStx? := some elementStx
  let toElement (declName : Name) (elementStx : Syntax) : TerminationByElement :=
    let vars     := elementStx[1].getArgs
    let implicit := !elementStx[0].isIdent
    let body     := elementStx[3]
    { ref := elementStx, declName, vars, implicit, body }
  let mut result := #[]
  let mut usedElse := false
  for clique in cliques do
    let mut elements := #[]
    for declName in clique do
      if let some elementStx := elementStxs.find? fun elementStx => elementStx[0].isIdent && elementStx[0].getId.isSuffixOf declName then
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
