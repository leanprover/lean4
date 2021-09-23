/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Command

namespace Lean.Elab.WF

inductive TerminationBy where
  | none
  | one (stx : Syntax)
  | many (map : NameMap Syntax)

def expandTerminationBy (terminationBy? : Option Syntax) (cliques : Array (Array Name)) : MacroM TerminationBy := do
  if let some terminationBy := terminationBy? then
    let terminationBy := terminationBy[1]
    if terminationBy.getKind == ``Parser.Command.terminationBy1 then
      return TerminationBy.one terminationBy[0]
    else if terminationBy.getKind == ``Parser.Command.terminationByMany then
      let m ← terminationBy[0].getArgs.foldlM (init := {}) fun m arg =>
        let declName? := cliques.findSome? fun clique => clique.findSome? fun declName =>
          if arg[0].getId.isSuffixOf declName then some declName else none
        match declName? with
        | none => Macro.throwErrorAt arg[0] s!"function '{arg[0].getId}' not found in current declaration"
        | some declName => return m.insert declName arg[2]
      for clique in cliques do
        let mut found? := Option.none
        for declName in clique do
          if let some stx := m.find? declName then
            if let some found := found? then
              Macro.throwErrorAt stx s!"invalid 'termination_by' element, '{declName}' and '{found}' are in the same clique"
            found? := some declName
      return TerminationBy.many m
    else
      Macro.throwUnsupported
  else
    return TerminationBy.none

def TerminatioBy.erase (t : TerminationBy) (clique : Array Name) : TerminationBy :=
  match t with
  | TerminationBy.none   => TerminationBy.none
  | TerminationBy.one .. => TerminationBy.none
  | TerminationBy.many m => do
    for declName in clique do
      if m.contains declName then
        let m := m.erase declName
        let m := m.erase declName
        if m.isEmpty then
          return TerminationBy.none
        else
          return TerminationBy.many m
    return t

def TerminationBy.find? (t : TerminationBy) (clique : Array Name) : Option Syntax := do
  match t with
  | TerminationBy.none    => Option.none
  | TerminationBy.one stx => some stx
  | TerminationBy.many m  => clique.findSome? m.find?

def TerminationBy.ensureIsEmpty (t : TerminationBy) : MacroM Unit := do
  match t with
  | TerminationBy.one stx => Macro.throwErrorAt stx "unused 'termination_by' element"
  | TerminationBy.many m => m.forM fun _ stx => Macro.throwErrorAt stx "unused 'termination_by' element"
  | _ => pure ()

end Lean.Elab.WF
