/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner
-/
prelude
import Init.Core

open Lean

-- Implementation detail of TypeName, since classes cannot be opaque
private opaque TypeNameData (α : Type u) : NonemptyType.{0} :=
  ⟨Name, inferInstance⟩

/--
Dynamic type name information.
Types with an instance of `TypeName` can be stored in an `Dynamic`.
The type class contains the declaration name of the type,
which must not have any universe parameters
and be of type `Sort ..` (i.e., monomorphic).

The preferred way to declare instances of this type is using the derive
handler, which will internally use the unsafe `TypeName.mk` function.

Morally, this is the same as:
```lean
class TypeName (α : Type) where unsafe mk ::
  typeName : Name
```
-/
@[nospecialize]
class TypeName (α : Type u) where private mk' ::
  private data : (TypeNameData α).type

instance : Nonempty (TypeName α) := (TypeNameData α).property.elim (⟨⟨·⟩⟩)

/--
Creates a `TypeName` instance.

For safety, it is required that the constant `typeName` is definitionally equal
to `α`.
-/
unsafe def TypeName.mk (α : Type u) (typeName : Name) : TypeName α :=
  ⟨unsafeCast typeName⟩

private unsafe def TypeName.typeNameImpl (α) [TypeName α] : Name :=
  unsafeCast (@TypeName.data α _)

/--
Returns a declaration name of the type.
-/
@[implemented_by TypeName.typeNameImpl]
opaque TypeName.typeName (α) [TypeName α] : Name

private opaque DynamicPointed : NonemptyType.{0} :=
  ⟨Name × NonScalar, inferInstance⟩

/--
A type-tagged union that can store any type with a `TypeName` instance.

This is roughly equivalent to `(α : Type) × TypeName α × α`, but without the universe bump. Use
`Dynamic.mk` to inject a value into `Dynamic` from another type, and `Dynamic.get?` to extract a
value from `Dynamic` if it has some expected type.
-/
def Dynamic : Type := DynamicPointed.type

instance : Nonempty Dynamic := DynamicPointed.property

private unsafe def Dynamic.typeNameImpl (any : Dynamic) : Name :=
  (unsafeCast any : Name × NonScalar).1

/--
The name of the type of the value stored in the `Dynamic`.
-/
@[implemented_by Dynamic.typeNameImpl]
opaque Dynamic.typeName (any : Dynamic) : Name

private unsafe def Dynamic.get?Impl (α) (any : Dynamic) [TypeName α] : Option α :=
  let ((typeName, obj) : Name × NonScalar) := unsafeCast any
  if typeName == TypeName.typeName α then
    some (unsafeCast obj)
  else
    none

/--
Retrieves the value stored in the `Dynamic`.
Returns `some a` if the value has the right type, and `none` otherwise.
-/
@[implemented_by Dynamic.get?Impl]
opaque Dynamic.get? (α) (any : Dynamic) [TypeName α] : Option α

private unsafe def Dynamic.mkImpl [TypeName α] (obj : α) : Dynamic :=
  unsafeCast (TypeName.typeName α, (unsafeCast obj : NonScalar))

/--
Stores the provided value in a `Dynamic`.

Use `Dynamic.get? α` to retrieve it.
-/
@[implemented_by Dynamic.mkImpl]
opaque Dynamic.mk [TypeName α] (obj : α) : Dynamic
