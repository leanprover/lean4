/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
-/
module

prelude
public import Init.Prelude
public import Init.Data.Nat.Basic

public section

namespace Lean.Compiler.Backend.Wasm.Layout

/-- Target pointer width for the WebAssembly object layout.

`wasm32` matches the current WASI language-core runtime (`libleanrt.a`).
Offsets below are ABI-compatible with `lean_object` on that target.
`wasm64` is reserved for a future parametric backend. -/
inductive PtrWidth where
  | wasm32
  | wasm64
  deriving BEq, Inhabited

/-- Default target for the WebAssembly backend. -/
def defaultPtrWidth : PtrWidth := .wasm32

structure ObjectLayout where
  /-- Pointer / `usize` size in bytes. -/
  ptrSize : Nat
  /-- Size of the `lean_object` header in bytes. -/
  headerSize : Nat
  /-- Byte offset of `m_tag` within the header. -/
  tagOffset : Nat
  /-- Byte offset of the reference-count field (`m_rc`). -/
  rcOffset : Nat
  /-- First object field offset (start of `m_objs[]`). -/
  fieldBase : Nat
  deriving Inhabited

def ObjectLayout.forWidth : PtrWidth → ObjectLayout
  | .wasm32 =>
    { ptrSize := 4, headerSize := 8, tagOffset := 7, rcOffset := 0, fieldBase := 8 }
  | .wasm64 =>
    { ptrSize := 8, headerSize := 16, tagOffset := 15, rcOffset := 0, fieldBase := 16 }

def default : ObjectLayout := ObjectLayout.forWidth defaultPtrWidth

/-- Offset of object field `index` (pointer-sized slots after the header). -/
def ObjectLayout.objField (layout : ObjectLayout) (index : Nat) : Nat :=
  layout.fieldBase + index * layout.ptrSize

/-- Offset of `usize` field after `numObjs` object slots. -/
def ObjectLayout.usizeField (layout : ObjectLayout) (numObjs index : Nat) : Nat :=
  layout.fieldBase + numObjs * layout.ptrSize + index * layout.ptrSize

/-- Offset of a scalar field after object and usize slots. -/
def ObjectLayout.scalarField (layout : ObjectLayout) (numObjs numUSize offset : Nat) : Nat :=
  layout.fieldBase + numObjs * layout.ptrSize + numUSize * layout.ptrSize + offset

/-- Closure fixed-arg base: header + arity/num_fixed words. -/
def ObjectLayout.closureFixedBase (layout : ObjectLayout) : Nat :=
  layout.fieldBase + 2 * layout.ptrSize

end Lean.Compiler.Backend.Wasm.Layout
