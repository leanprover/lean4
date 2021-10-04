/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Command

namespace Lean.Elab.WF

inductive TerminationHint where
  | none
  | one (stx : Syntax)
  | many (map : NameMap Syntax)
  deriving Inhabited

def expandTerminationHint (terminationHint? : Option Syntax) (cliques : Array (Array Name)) : MacroM TerminationHint := do
  if let some terminationHint := terminationHint? then
    let terminationHint := terminationHint[1]
    if terminationHint.getKind == ``Parser.Command.terminationHint1 then
      return TerminationHint.one terminationHint[0]
    else if terminationHint.getKind == ``Parser.Command.terminationHintMany then
      let m ← terminationHint[0].getArgs.foldlM (init := {}) fun m arg =>
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
              Macro.throwErrorAt stx s!"invalid termination hint element, '{declName}' and '{found}' are in the same clique"
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
  | TerminationHint.many m => do
    for declName in clique do
      if m.contains declName then
        let m := m.erase declName
        let m := m.erase declName
        if m.isEmpty then
          return TerminationHint.none
        else
          return TerminationHint.many m
    return t

def TerminationHint.find? (t : TerminationHint) (clique : Array Name) : Option Syntax := do
  match t with
  | TerminationHint.none    => Option.none
  | TerminationHint.one stx => some stx
  | TerminationHint.many m  => clique.findSome? m.find?

def TerminationHint.ensureIsEmpty (t : TerminationHint) : MacroM Unit := do
  match t with
  | TerminationHint.one stx => Macro.throwErrorAt stx "unused termination hint element"
  | TerminationHint.many m => m.forM fun _ stx => Macro.throwErrorAt stx "unused termination hint element"
  | _ => pure ()

structure TerminationStrategy where
  terminationBy    : TerminationHint := TerminationHint.none
  decreasingTactic : TerminationHint := TerminationHint.none
  deriving Inhabited

end Lean.Elab.WF
