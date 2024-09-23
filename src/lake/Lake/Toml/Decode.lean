/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Toml.Data

/-!
# TOML Decoders

This module contains definitions to assist in decoding TOML data values
into concrete user types.
-/

namespace Lake
open Lean Toml

/-!
## Generic Decode Helpers
-/

instance : MonadLift (Except ε) (Except (Array ε)) where
  monadLift x := x.mapError Array.singleton

/-- Run the decode action. If there were errors, throw. Otherwise, return the result. -/
@[inline] def ensureDecode (x : StateM (Array ε) α) : Except (Array ε) α :=
  let (a, es) := x.run Array.empty; if es.isEmpty then pure a else throw es

/-- Run the decode action. If it fails, add the errors to the state and return `default`. -/
@[inline] def tryDecodeD (default : α) (x : Except (Array ε) α) : StateM (Array ε) α :=
  match x with
  | .ok a => pure a
  | .error es => modify (· ++ es) *> pure default

/-- Run the decode action. If it fails, add the errors to the state and return `Inhabited.default`. -/
@[inline] def tryDecode [Inhabited α] (x : Except (Array ε) α) : StateM (Array ε) α :=
  tryDecodeD default x

/--
If the value is not `none`, run the decode action.
If it fails, add the errors to the state and return `default`.
-/
@[inline] def optDecodeD (default : β)  (a? : Option α) (f : α → Except (Array ε) β) : StateM (Array ε) β :=
  match a? with
  | some a => tryDecodeD default (f a)
  | none => pure default

/--
If the value is not `none`, run the decode action.
If it fails, add the errors to the state and return `Inhabited.default`.
-/
@[inline] def optDecode [Inhabited β] (a? : Option α) (f : α → Except (Array ε) β) : StateM (Array ε) β :=
  optDecodeD default a? f


/--
If the value is not `none`, run the decode action.
If it fails, add the errors to the state and return `none`.
Otherwise, return the result in `some`.
-/
@[inline] def optDecode? (a? : Option α)  (f : α → Except (Array ε) β) : StateM (Array ε) (Option β) :=
  optDecodeD none a? fun a  => some <$> f a

/--
If either action errors, throw the concatenated errors.
Otherwise, if no errors, combine the results with `f`.
-/
def mergeErrors (x₁ : Except (Array ε) α) (x₂ : Except (Array ε) β) (f : α → β → γ) : Except (Array ε) γ :=
  match x₁, x₂ with
  | .ok a, .ok b => .ok (f a b)
  | .ok _, .error es => .error es
  | .error es, .ok _ => .error es
  | .error es', .error es => .error (es ++ es')

structure Toml.DecodeError where
  ref : Syntax
  msg : String

class DecodeToml (α : Type u) where
  decode (v : Value) : Except (Array DecodeError) α

abbrev decodeToml [DecodeToml α] (v : Value) : Except (Array DecodeError) α :=
  DecodeToml.decode v

namespace Toml

/-- Decode an array of TOML values, merging any errors from the elements into a single array. -/
def decodeArray [dec : DecodeToml α] (vs : Array Value) : Except (Array DecodeError) (Array α) :=
  vs.foldl (init := Except.ok (.mkEmpty vs.size)) fun vs v =>
    mergeErrors vs (dec.decode v) Array.push

instance : DecodeToml Value := ⟨pure⟩

namespace Value

@[inline] def decodeString : Value → Except DecodeError String
| .string _ v => .ok v
| x => .error (.mk x.ref "expected string")

instance : DecodeToml String := ⟨(·.decodeString)⟩
instance : DecodeToml System.FilePath := ⟨(.mk <$> decodeToml ·)⟩

@[inline] def decodeName (v : Value) : Except DecodeError Name := do
  match (← v.decodeString).toName with
  | .anonymous => throw (.mk v.ref "expected name")
  | n => pure n

instance : DecodeToml Lean.Name := ⟨(·.decodeName)⟩

@[inline] def decodeInt : Value → Except DecodeError Int
| .integer _ v => .ok v
| x => .error (.mk x.ref "expected integer")

instance : DecodeToml Int := ⟨(·.decodeInt)⟩

@[inline] def decodeNat : Value → Except DecodeError Nat
| .integer _ (.ofNat v) => .ok v
| x => .error (.mk x.ref "expected nonnegative integer")

instance : DecodeToml Nat := ⟨(·.decodeNat)⟩

@[inline] def decodeFloat : Value → Except DecodeError Float
| .float _ v => .ok v
| x => .error (.mk x.ref "expected float")

instance : DecodeToml Float := ⟨(·.decodeFloat)⟩

@[inline] def decodeBool : Value → Except DecodeError Bool
| .boolean _ v => .ok v
| x => .error (.mk x.ref "expected boolean")

instance : DecodeToml Bool := ⟨(·.decodeBool)⟩

@[inline] def decodeDateTime : Value → Except DecodeError DateTime
| .dateTime _ v => .ok v
| x => .error (.mk x.ref "expected date-time")

instance : DecodeToml DateTime := ⟨(·.decodeDateTime)⟩

@[inline] def decodeValueArray : Value → Except DecodeError (Array Value)
| .array _ vs => .ok vs
| x => .error (.mk x.ref "expected array")

@[inline] protected def decodeArray [dec : DecodeToml α] (v : Value) : Except (Array DecodeError) (Array α) := do
  decodeArray (dec := dec) (← v.decodeValueArray)

instance [DecodeToml α] : DecodeToml (Array α) := ⟨Value.decodeArray⟩

@[inline] def decodeArrayOrSingleton [dec : DecodeToml α] : Value → Except (Array DecodeError) (Array α)
| .array _ vs => decodeArray (dec := dec) vs
| v => Array.singleton <$> dec.decode v

@[inline] def decodeTable : Value → Except DecodeError Table
| .table _ t => .ok t
| x => .error (.mk x.ref "expected table")

instance : DecodeToml Table := ⟨(·.decodeTable)⟩

end Value

def decodeKeyval [dec : DecodeToml α] (k : Name) (v : Value) : Except (Array DecodeError) α := do
  dec.decode v |>.mapError fun xs => xs.map fun x =>
    {x with msg := s!"key {ppKey k}: " ++ x.msg}

namespace Table

@[inline] def decodeValue (t : Table) (k : Name) (ref := Syntax.missing) : Except DecodeError Value := do
  let some a := t.find? k
    | throw (.mk ref s!"missing required key: {ppKey k}")
  return a

def decode [dec : DecodeToml α] (t : Table) (k : Name) (ref := Syntax.missing) : Except (Array DecodeError) α := do
  let a ← t.decodeValue k ref
  decodeKeyval (dec := dec) k a

def decode? [dec : DecodeToml α] (t : Table) (k : Name) : Except (Array DecodeError) (Option α) := do
  t.find? k |>.mapM fun v => decodeKeyval (dec := dec) k v

def decodeNameMap [dec : DecodeToml α] (t : Toml.Table) : Except (Array DecodeError) (NameMap α) := do
  t.items.foldl (init := Except.ok {}) fun m (k,v) =>
    mergeErrors m (dec.decode v) fun m v => m.insert k v

instance [DecodeToml α] : DecodeToml (NameMap α) := ⟨(do decodeNameMap <| ← ·.decodeTable)⟩

@[inline] protected def tryDecode [Inhabited α] [dec : DecodeToml α] (t : Table) (k : Name) (ref := Syntax.missing) : StateM (Array DecodeError) α := do
  tryDecode <| t.decode (dec := dec) k ref

@[inline] protected def tryDecode? [dec : DecodeToml α] (t : Table) (k : Name) : StateM (Array DecodeError) (Option α) :=
  optDecode? (t.find? k) dec.decode

@[inline] protected def tryDecodeD [dec : DecodeToml α] (k : Name) (default : α) (t : Table) : StateM (Array DecodeError) α :=
  optDecodeD default (t.find? k) dec.decode

end Table
