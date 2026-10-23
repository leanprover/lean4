/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Data.Hashable
public section
namespace Lean.Meta.Sym

/--
Key for maps and sets that compares objects by address, a safe counterpart of `Lean.Ptr`.
The key holds the object, so it stays alive and its address is not reused while the key exists.
Equal values that are different objects are different keys.
-/
structure ObjectPtr where
  value : NonScalar

/--
Returns the key of `a`. The values of `α` must not be represented as scalars at runtime
(e.g., `UInt64`, `Bool`, or enumeration types).
-/
@[inline] def ObjectPtr.of (a : α) : ObjectPtr :=
  { value := unsafe unsafeCast a }

instance : Hashable ObjectPtr where
  hash k := unsafe (ptrAddrUnsafe k.value >>> 3).toUInt64

instance : BEq ObjectPtr where
  beq k₁ k₂ := unsafe ptrEq k₁.value k₂.value

end Lean.Meta.Sym
