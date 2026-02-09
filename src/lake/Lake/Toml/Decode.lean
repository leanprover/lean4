/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.FilePath
public import Lake.Toml.Data
import Init.Data.ToString.Macro

open Lean

/-!
# TOML Decoders

This module contains definitions to assist in decoding TOML data values
into concrete user types.
-/

namespace Lake

public structure Toml.DecodeError where
  ref : Syntax
  msg : String

public abbrev Toml.DecodeM := EStateM Empty (Array DecodeError)

public abbrev Toml.EDecodeM := EStateM Unit (Array DecodeError)

public class DecodeToml (α : Type) where
  decode (v : Toml.Value) : Toml.EDecodeM α

public abbrev decodeToml [DecodeToml α] (v : Toml.Value) : Toml.EDecodeM α :=
  DecodeToml.decode v

namespace Toml

/-- Run the decode action. If there were errors, throw. Otherwise, return the result. -/
@[inline] public  def ensureDecode (x : DecodeM α) : EDecodeM α := fun es =>
  match x es with
  | .ok a es => if es.isEmpty then .ok a es else .error () es

/-- Run the decode action. If it fails, keep the errors but return `default`. -/
@[inline] public  def tryDecodeD (default : α) (x : EDecodeM α) : DecodeM α := fun es =>
  match x es with
  | .ok a es => .ok a es
  | .error _ es => .ok default es

/-- Run the decode action. If it fails, keep the errors but  return `none`. -/
@[inline] public def tryDecode? (x : EDecodeM α) : DecodeM (Option α) := fun es =>
   match x es with
  | .ok a es => .ok (some a) es
  | .error _ es => .ok none es

/-- Run the decode action. If it fails, keep the errors but  return `Inhabited.default`. -/
@[inline] public  def tryDecode [Inhabited α] (x : EDecodeM α) : DecodeM α :=
  tryDecodeD default x

/--
If the value is not `none`, run the decode action.
If it fails, add the errors to the state and return `default`.
-/
@[inline] public def optDecodeD (default : β)  (a? : Option α) (f : α → EDecodeM β) : DecodeM β :=
  match a? with
  | some a => tryDecodeD default (f a)
  | none => pure default

/--
If the value is not `none`, run the decode action.
If it fails, add the errors to the state and return `Inhabited.default`.
-/
@[inline] public def optDecode [Inhabited β] (a? : Option α) (f : α → EDecodeM β) : DecodeM β :=
  optDecodeD default a? f

/--
If the value is not `none`, run the decode action.
If it fails, add the errors to the state and return `none`.
Otherwise, return the result in `some`.
-/
@[inline] public def optDecode? (a? : Option α)  (f : α → EDecodeM β) : DecodeM (Option β) :=
  optDecodeD none a? fun a  => some <$> f a

/--
If either action errors, throw the concatenated errors.
Otherwise, if no errors, combine the results with `f`.
-/
public def mergeErrors (x₁ : EDecodeM α) (x₂ : EDecodeM β) (f : α → β → γ) : EDecodeM γ := fun es =>
  match x₁ es with
  | .ok a es =>
    match x₂ es with
    | .ok b es => .ok (f a b) es
    | .error _ es => .error () es
  | .error _ es => .error () es

@[inline] public def throwDecodeErrorAt (ref : Syntax) (msg : String) : EDecodeM α :=
  fun es => .error () (es.push {ref, msg})

/-- Decode an array of TOML values, merging any errors from the elements into a single array. -/
public def decodeArray [dec : DecodeToml α] (vs : Array Value) : EDecodeM (Array α) :=
  vs.foldl (init := pure (.mkEmpty vs.size)) fun vs v =>
    mergeErrors vs (dec.decode v) Array.push

instance : DecodeToml Value := ⟨pure⟩

namespace Value

public def decodeString (v : Value) : EDecodeM String :=
  match v with
  | .string _ v => .ok v
  | x => throwDecodeErrorAt x.ref "expected string"

public instance : DecodeToml String := ⟨decodeString⟩
public instance : DecodeToml System.FilePath := ⟨(.mk <$> decodeToml ·)⟩

public def decodeName (v : Value) : EDecodeM Name := do
  match (← v.decodeString).toName with
  | .anonymous => throwDecodeErrorAt v.ref "expected name"
  | n => pure n

public instance : DecodeToml Lean.Name := ⟨decodeName⟩

public def decodeInt (v : Value) : EDecodeM Int :=
  match v with
  | .integer _ v => .ok v
  | x => throwDecodeErrorAt x.ref "expected integer"

public instance : DecodeToml Int := ⟨decodeInt⟩

public def decodeNat : Value → EDecodeM Nat
  | .integer _ (.ofNat v) => .ok v
  | x => throwDecodeErrorAt x.ref "expected nonnegative integer"

public instance : DecodeToml Nat := ⟨decodeNat⟩

public def decodeFloat (v : Value) : EDecodeM Float :=
  match v with
  | .float _ v => .ok v
  | x => throwDecodeErrorAt x.ref "expected float"

public instance : DecodeToml Float := ⟨decodeFloat⟩

public def decodeBool (v : Value) : EDecodeM Bool :=
  match v with
  | .boolean _ v => .ok v
  | x => throwDecodeErrorAt x.ref "expected boolean"

public instance : DecodeToml Bool := ⟨decodeBool⟩

public def decodeDateTime (v : Value) : EDecodeM DateTime :=
  match v with
  | .dateTime _ v => .ok v
  | x => throwDecodeErrorAt x.ref "expected date-time"

public instance : DecodeToml DateTime := ⟨decodeDateTime⟩

public def decodeValueArray (v : Value) : EDecodeM (Array Value) :=
  match v with
  | .array _ vs => .ok vs
  | x => throwDecodeErrorAt x.ref "expected array"

@[inline] public protected def decodeArray [dec : DecodeToml α] (v : Value) : EDecodeM (Array α) := do
  decodeArray (dec := dec) (← v.decodeValueArray)

public instance [DecodeToml α] : DecodeToml (Array α) := ⟨Value.decodeArray⟩

@[inline] public def decodeArrayOrSingleton [dec : DecodeToml α] (v : Value) : EDecodeM (Array α) :=
  match v with
  | .array _ vs => decodeArray (dec := dec) vs
  | v => Array.singleton <$> dec.decode v

public def decodeTable (v : Value) : EDecodeM Table :=
  match v with
  | .table _ t => .ok t
  | x => throwDecodeErrorAt x.ref "expected table"

instance : DecodeToml Table := ⟨(·.decodeTable)⟩

end Value

public def decodeKeyval [dec : DecodeToml α] (k : Name) (v : Value) : EDecodeM α := fun es =>
  let iniPos := es.size
  let f es := es.mapIdx fun i e =>
    if iniPos ≤ i then {e with msg := s!"key {ppKey k}: {e.msg}"} else e
  match dec.decode v es with
  | .ok a es => .ok a (f es)
  | .error e es => .error e (f es)

namespace Table

public def decodeValue (t : Table) (k : Name) (ref := Syntax.missing) : EDecodeM Value := do
  let some a := t.find? k
    | throwDecodeErrorAt ref s!"missing required key: {ppKey k}"
  return a

@[inline] public def decode
  [dec : DecodeToml α] (t : Table) (k : Name) (ref := Syntax.missing)
: EDecodeM α := do
  let a ← t.decodeValue k ref
  decodeKeyval (dec := dec) k a

@[inline] public def decode?
  [dec : DecodeToml α] (t : Table) (k : Name)
: EDecodeM (Option α) := t.find? k |>.mapM fun v => decodeKeyval (dec := dec) k v

public def decodeNameMap [dec : DecodeToml α] (t : Toml.Table) : EDecodeM (NameMap α) := do
  t.items.foldl (init := pure {}) fun m (k,v) =>
    mergeErrors m (dec.decode v) fun m v => m.insert k v

public instance [DecodeToml α] : DecodeToml (NameMap α) := ⟨(do decodeNameMap <| ← ·.decodeTable)⟩

@[inline] public protected def tryDecode
  [Inhabited α] [dec : DecodeToml α] (t : Table) (k : Name) (ref := Syntax.missing)
: DecodeM α := tryDecode <| t.decode (dec := dec) k ref

@[inline] public protected def tryDecode?
  [dec : DecodeToml α] (t : Table) (k : Name)
: DecodeM (Option α) := optDecode? (t.find? k) dec.decode

@[inline] public protected def tryDecodeD
  [dec : DecodeToml α] (k : Name) (default : α) (t : Table)
: DecodeM α := optDecodeD default (t.find? k) dec.decode

end Table
