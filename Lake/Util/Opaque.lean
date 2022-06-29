/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Command

/-!
This module provides utilities for defining simple opaque types
for forward declarations. Types are first declared with `declare_opaque_type`
and then later filled in with `hydrate_opaque_type` once the corresponding
non-opaque type has been defined.
-/

namespace Lake
open Lean Parser Command

macro (name := declareOpaqueType)
doc?:optional(docComment)  "declare_opaque_type " id:ident : command =>
  let nonemptyTypeId := id.getId.modifyBase (· ++ `nonemptyType)
  let type := mkIdentFrom id <| nonemptyTypeId.modifyBase (· ++ `type)
  let prop := mkIdentFrom id <| nonemptyTypeId.modifyBase (· ++ `property)
  let nonemptyType := mkIdentFrom id nonemptyTypeId
  `(
  opaque $nonemptyType : NonemptyType.{0}
  $[$doc?:docComment]? def $id : Type := $type
  instance : Nonempty $id := $prop
  )

macro (name := hydrateOpaqueType)
"hydrate_opaque_type " oty:ident ty:ident : command =>
  let mk := mkIdent `mk
  let unsafeMk := mkIdent `unsafeMk
  let get := mkIdent `get
  let unsafeGet := mkIdent `unsafeGet
  let get_mk := mkIdent `get_mk
  `(
  namespace $oty
  unsafe def $unsafeMk : $ty → $oty := unsafeCast
  @[implementedBy $unsafeMk] opaque $mk : $ty → $oty

  unsafe def $unsafeGet : $oty → $ty := unsafeCast
  @[implementedBy $unsafeGet] opaque $get : $oty → $ty

  instance : Coe $ty $oty := ⟨$mk⟩
  instance : Inhabited $oty := ⟨$mk default⟩
  instance : Coe $oty $ty := ⟨$get⟩

  @[simp] axiom $get_mk {x : $ty} : $get ($mk x) = x
  end $oty
  )
