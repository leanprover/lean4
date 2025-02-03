/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Meta.Basic

namespace Lean.Elab

open Lean

structure InlayHintLinkLocation where
  module : Name
  range  : String.Range

structure InlayHintLabelPart where
  value     : String
  tooltip?  : Option String := none
  location? : Option InlayHintLinkLocation := none

inductive InlayHintLabel
  | name (n : String)
  | parts (p : Array InlayHintLabelPart)

inductive InlayHintKind where
  | type
  | parameter

structure InlayHintTextEdit where
  range   : String.Range
  newText : String

structure InlayHintInfo where
  position     : String.Pos
  label        : InlayHintLabel
  kind?        : Option InlayHintKind := none
  textEdits    : Array InlayHintTextEdit := #[]
  tooltip?     : Option String := none
  paddingLeft  : Bool := false
  paddingRight : Bool := false

structure InlayHint extends InlayHintInfo where
  lctx               : LocalContext
  deferredResolution : InlayHintInfo → MetaM InlayHintInfo := fun i => .pure i
  deriving TypeName

namespace InlayHint

def toCustomInfo (i : InlayHint) : CustomInfo := {
  stx := .missing
  value := .mk i
}

def ofCustomInfo? (c : CustomInfo) : Option InlayHint :=
  c.value.get? InlayHint

def resolveDeferred (i : InlayHint) : MetaM InlayHint := do
  let info := i.toInlayHintInfo
  let info ← i.deferredResolution info
  return { i with toInlayHintInfo := info }

end InlayHint
