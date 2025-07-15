import Lean.Meta.Basic
import Lean.Elab.Deriving.Basic

/-!
# `deriving` handlers for structures matching names in open namespaces

This test ensures that `deriving` handlers do not fail when added to a declaration whose name
matches one from an open namespace.

Note that the general strategy to resolve this error is to use `mkCIdent` rather than `mkIdent` when
referring to the declaration in deriving handlers.
-/

structure A.B where
structure A.C where
structure A.D where

open A

open Lean Meta Elab Command in
set_option hygiene false in
#eval show CommandElabM Unit from do
  let go : StateRefT (Array (Name × PersistentArray Message)) CommandElabM Unit := do
    let derivingHandlers ← derivingHandlersRef.get
    -- `SizeOf` panics if you try to re-derive it
    let derivingHandlers := derivingHandlers.filter (fun nm _ => nm != ``SizeOf)
    for (cls, _) in derivingHandlers do
      withoutModifyingEnv do
        let s ← getThe Command.State
        -- Many handlers have different logic for enums, singletons, and/or sums
        Command.elabCommand (← `(structure B where deriving $(mkIdent cls):ident))
        Command.elabCommand (← `(structure C where x : Nat deriving $(mkIdent cls):ident))
        Command.elabCommand (← `(inductive D where | mk₁ : Bool → D | mk₂ : Bool → D deriving $(mkIdent cls):ident))
        let msgs := (← getThe Command.State).messages.unreported
        set s
        if msgs.any (·.severity == .error) then
          modify fun s => s.push (cls, msgs)
  let (_, failures) ← go.run #[]
  for (cls, msgs) in failures do
    let msgs := MessageData.joinSep (msgs.map (·.data)).toList "\n\n"
    logError m!"Handler for class `{cls}` failed with errors:\n{msgs}"
