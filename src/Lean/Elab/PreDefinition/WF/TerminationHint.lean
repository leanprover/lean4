/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Command

namespace Lean.Elab.WF

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

def TerminationHint.erase (t : TerminationHint) (clique : Array Name) : TerminationHint :=
  match t with
  | TerminationHint.none   => TerminationHint.none
  | TerminationHint.one .. => TerminationHint.none
  | TerminationHint.many m => Id.run <| do
    for declName in clique do
      if m.contains declName then
        let m := m.erase declName
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

def TerminationHint.ensureIsEmpty (t : TerminationHint) : MacroM Unit := do
  match t with
  | TerminationHint.one v   => Macro.throwErrorAt v.ref "unused termination hint element"
  | TerminationHint.many m  => m.forM fun _ v => Macro.throwErrorAt v.ref "unused termination hint element"
  | _ => pure ()

inductive TerminationBy where
  | core (hint : TerminationHint)

inductive TerminationWF where
  | core (stx : Syntax)

def expandTerminationBy (hint? : Option Syntax) (cliques : Array (Array Name)) : MacroM TerminationBy :=
  if let some hint := hint? then
    if hint.isOfKind ``Parser.Command.terminationByCore then
      return TerminationBy.core (← expandTerminationHint hint? cliques)
    else
      withRef hint <| Macro.throwError "`termination_by` syntax is being modified/simplified. To use the old syntax, please use `termination_by'` instead"
  else
      return TerminationBy.core TerminationHint.none

def TerminationBy.erase (t : TerminationBy) (clique : Array Name) : TerminationBy :=
  match t with
  | core hint => core (hint.erase clique)

def TerminationBy.find? (t : TerminationBy) (clique : Array Name) : Option TerminationWF :=
  match t with
  | core hint => hint.find? clique |>.map fun v => TerminationWF.core v.value

def TerminationBy.ensureIsEmpty (t : TerminationBy) : MacroM Unit :=
  match t with
  | core hint => hint.ensureIsEmpty

end Lean.Elab.WF
