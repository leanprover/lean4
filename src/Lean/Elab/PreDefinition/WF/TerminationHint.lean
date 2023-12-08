/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term

set_option autoImplicit false

namespace Lean.Elab.WF

/-
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
-/

/-! # Support for `termination_by` notation -/

/-- A single `termination_by` clause -/
structure TerminationBy where
  ref       : Syntax
  vars      : TSyntaxArray [`ident, ``Lean.Parser.Term.hole]
  body      : Term
  deriving Inhabited

/-- A complete set of `termination_by` hints, as applicable to a single clique.  -/
abbrev TerminationWF := Array TerminationBy


/-- The termination annotations for a single function -/
structure TerminationHints where
  ref : Syntax
  termination_by? : Option TerminationBy
  decreasing_by?  : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)
  deriving Inhabited


def TerminationHints.none : TerminationHints := ⟨.missing, .none, .none⟩

open Parser.Termination

def elabTerminationHints (stx : TSyntax ``suffix) : TerminationHints :=
  -- TODO: Better understand if this is needed
  if let ⟨.missing⟩ := stx then
    { ref := stx, termination_by? := none, decreasing_by? := none }
  else
    match stx with
  | `(suffix| $[$t?:terminationBy]? $[$d?:decreasingBy]? ) =>
    { ref := stx
      termination_by? := t?.map fun t => match t with
        | `(terminationBy|termination_by $vars* => $body) => {ref := t, vars, body}
        | _ => unreachable!
      decreasing_by? := d?.map fun
        | `(decreasingBy|decreasing_by $ts) => ts
        | _ => unreachable!  }
  | _ => panic! s!"Unexpected Termination.suffix syntax: {stx}"

/-

open Parser.Command in
/--
Expands the syntax for a `termination_by` clause
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
-/

/-
open Parser.Termination in
def TerminationWF.unexpand (elements : TerminationWF) : MetaM Syntax := do
  let vars ← elements.map (·.vars)
  let bodies ← elements.map (·.body)
  `(terminationBy|termination_by $[$vars* => $bodies*]*)
-/

/-

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
-/

end Lean.Elab.WF
