/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
-/
module

prelude
public import Lean.Compiler.IR.Basic

public section

namespace Lean.Compiler.Backend.Wasm.Types

open Lean.IR

/-- WebAssembly value types (binary encoding). -/
inductive ValType where
  | i32  -- 0x7f
  | i64  -- 0x7e
  | f32  -- 0x7d
  | f64  -- 0x7c
  deriving BEq, Inhabited

def ValType.toByte : ValType → UInt8
  | .i32 => 0x7f
  | .i64 => 0x7e
  | .f32 => 0x7d
  | .f64 => 0x7c

/-- Map a single non-aggregate IR type to a WASM valtype. -/
def scalarValType? : IRType → Option ValType
  | .uint8 | .uint16 | .uint32 | .usize | .object | .tobject | .tagged => some .i32
  | .uint64 => some .i64
  | .float => some .f64
  | .float32 => some .f32
  | .void | .erased => none
  | .struct .. | .union .. => none

/-- Flatten an IR type to zero or more WASM result/parameter valtypes.

`struct` becomes the concatenation of its fields (multi-value).
`union` is represented as a tag (`i32`) followed by the widest variant's
flattened payload. -/
partial def flattenValTypes : IRType → Array ValType
  | .void | .erased => #[]
  | .struct _ fields => fields.foldl (init := #[]) fun acc ty => acc ++ flattenValTypes ty
  | .union _ variants =>
    let payloads := variants.map fun ty => flattenValTypes ty
    let maxLen := payloads.foldl (init := 0) fun m a => max m a.size
    let pad : Array ValType := Array.replicate maxLen .i32
    #[.i32] ++ pad
  | ty =>
    match scalarValType? ty with
    | some v => #[v]
    | none => #[]

partial def isSupportedType : IRType → Bool
  | .void | .erased => true
  | .struct _ fields => fields.all isSupportedType
  | .union _ variants => variants.all isSupportedType
  | ty => (scalarValType? ty).isSome

def isSupportedSignature (decl : Decl) : Bool :=
  let params := decl.params.filter fun p => !p.ty.isVoid && p.ty != .erased
  params.all (fun p => isSupportedType p.ty) && isSupportedType decl.resultType

/-- Number of WASM locals/slots needed to hold an IR value (1 for scalars/objects). -/
partial def numSlots : IRType → Nat
  | .void | .erased => 0
  | .struct _ fields => fields.foldl (init := 0) fun n t => n + numSlots t
  | .union _ variants =>
    let maxPayload := variants.foldl (init := 0) fun m t => max m (numSlots t)
    1 + maxPayload  -- tag + widest payload
  | _ => 1

def unsupportedReason (ty : IRType) : String :=
  match ty with
  | .struct .. => "struct type cannot be fully lowered"
  | .union .. => "union type cannot be fully lowered"
  | .void | .erased => "unexpected void/erased in value position"
  | _ => "unsupported IR type"

end Lean.Compiler.Backend.Wasm.Types
