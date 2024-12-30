/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Binder
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
doc?:optional(docComment)  "declare_opaque_type " id:ident bs:binder* : command => do
  let (bs, args) ← expandBinders bs
  let nonemptyTypeId := id.getId.modifyBase (· ++ `nonemptyType)
  let nonemptyType := mkIdentFrom id nonemptyTypeId
  let nonemptyTypeApp := Syntax.mkApp nonemptyType args
  `(
  opaque $nonemptyType $[$bs]* : NonemptyType.{0}
  $[$doc?:docComment]? def $id $[$bs]* : Type := $nonemptyTypeApp |>.type
  instance : Nonempty $(Syntax.mkApp id args) :=  $nonemptyTypeApp |>.property
  )

macro (name := hydrateOpaqueType)
"hydrate_opaque_type " oty:ident ty:ident args:ident* : command =>
  let mk := mkIdent `mk
  let unsafeMk := mkIdent `unsafeMk
  let get := mkIdent `get
  let unsafeGet := mkIdent `unsafeGet
  `(
  namespace $oty
  unsafe def $unsafeMk : $ty $args* → $oty $args* := unsafeCast
  @[implemented_by $unsafeMk] opaque $mk : $ty $args* → $oty $args*
  instance : Coe ($ty $args*) ($oty $args*) := ⟨$mk⟩

  unsafe def $unsafeGet : $oty $args* → $ty $args* := unsafeCast
  @[implemented_by $unsafeGet] opaque $get $[{$args}]* : $oty $args* → $ty $args*
  instance : Coe ($oty $args*) ($ty $args*) := ⟨$get⟩

  instance [Inhabited ($ty $args*)] : Inhabited ($oty $args*) := ⟨$mk default⟩
  end $oty
  )
