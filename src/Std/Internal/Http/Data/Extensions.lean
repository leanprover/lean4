/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Core
public import Init.Dynamic
public import Std.Data.TreeMap

open Lean

public section

/-!
# Extensions

This module provides the `Extensions` type, a dynamically-typed map for storing optional metadata
on HTTP requests and responses. It can be used by parsers, middleware, or other processing stages
to attach arbitrary typed data.
-/

namespace Std.Http

set_option linter.all true

/--
A dynamic typed map for optional metadata that can be attached to HTTP requests and responses.
Extensions allow storing arbitrary typed data keyed by type name, useful for middleware-style
metadata such as parsed socket information or custom processing data.
-/
structure Extensions where
  private mk ::
  /--
  The underlying tree map storing dynamic values keyed by their type name.

  Note: We cannot use `Name.quickCmp` here.
  -/
  private data : TreeMap Name Dynamic (compare ·.hash.toNat ·.hash.toNat) := .empty
deriving Inhabited

namespace Extensions

/--
An empty extensions map with no data.
-/
def empty : Extensions :=
  ⟨.empty⟩

/--
Retrieves a value of type `α` from the extensions, if present.
-/
@[inline]
def get (x : Extensions) (α : Type) [TypeName α] : Option α := do
  let dyn ← x.data.get? (TypeName.typeName α)
  dyn.get? α

/--
Inserts a value into the extensions, keyed by its type name.
If a value of the same type already exists, it is replaced.
-/
@[inline]
def insert (x : Extensions) [TypeName α] (data : α) : Extensions :=
  let dyn := Dynamic.mk data
  ⟨x.data.insert dyn.typeName dyn⟩

/--
Removes the value of type `α` from the extensions.
-/
@[inline]
def remove (x : Extensions) (α : Type) [TypeName α] : Extensions :=
  ⟨x.data.erase (TypeName.typeName α)⟩

/--
Checks whether the extensions contain a value of type `α`.
-/
@[inline]
def contains (x : Extensions) (α : Type) [TypeName α] : Bool :=
  x.data.contains (TypeName.typeName α)

end Std.Http.Extensions
