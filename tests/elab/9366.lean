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

/-
The following tests simulate, for each class `Cls` with a registered deriving handler, the three
following declarations:

```
structure B where
  deriving Cls

structure C where
  x : Nat
  deriving Cls

inductive D where
  | mk₁ : Bool → D
  | mk₂ : Bool → D
  deriving Cls
```

The purpose of the three distinct declarations is to account for the fact that many deriving
handlers have different logic for structures, singletons, and/or sums. If a class cannot be derived
for one or more of these declarations, add it to the `exclusions` map below, indicating the tests
from which it should be excluded.
-/

inductive ExclusionKind
  | singleton | struct | sum
  deriving BEq, Hashable

def exclusions : Std.HashMap Lean.Name (Std.HashSet ExclusionKind) := .ofList [
  (``SizeOf, { .singleton, .struct, .sum })
]

def dependencies : Std.HashMap Lean.Name (Array Lean.Name) := .ofList [
  (``ReflBEq, #[``BEq]),
  (``LawfulBEq, #[``BEq, ``ReflBEq])
]

open Lean Meta Elab Command in
set_option hygiene false in
#eval show CommandElabM Unit from do
  let go : StateRefT (Array (Name × PersistentArray Message)) CommandElabM Unit := do
    let derivingHandlers ← derivingHandlersRef.get
    let derivingHandlers := derivingHandlers.filter (fun nm _ => nm != ``SizeOf)
    for (cls, _) in derivingHandlers do
      withoutModifyingEnv do
        let hasExcl (kind : ExclusionKind) := (·.contains kind) <$> exclusions[cls]? |>.getD false
        let s ← getThe Command.State
        let classes := ((dependencies[cls]? |>.getD #[]).push cls).map mkIdent
        unless hasExcl .singleton do
          Command.elabCommand (← `(structure B where deriving $[$classes:ident],*))
        unless hasExcl .struct do
          Command.elabCommand (← `(structure C where x : Nat deriving $[$classes:ident],*))
        unless hasExcl .sum do
          Command.elabCommand (← `(inductive D where | mk₁ : Bool → D | mk₂ : Bool → D deriving $[$classes:ident],*))
        let msgs := (← getThe Command.State).messages.unreported
        set s
        if msgs.any (·.severity == .error) then
          modify fun s => s.push (cls, msgs)
  let (_, failures) ← go.run #[]
  for (cls, msgs) in failures do
    let msgs := MessageData.joinSep (msgs.map (·.data)).toList "\n\n"
    logError m!"Handler for class `{cls}` failed with errors:\n{msgs}"
