/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Prelude
meta import Lake.Util.Binder
meta import Lean.Parser.Command

/-!
This module provides utilities for defining simple opaque types
for forward declarations. Types are first declared with `declare_opaque_type`
and then later filled in with `hydrate_opaque_type` once the corresponding
non-opaque type has been defined.
-/

namespace Lake
open Lean Parser Command

public section

macro (name := declareOpaqueType)
  doc?:optional(docComment) vis?:optional(visibility) "declare_opaque_type " id:ident bs:binder*
: command => do
  let bvs ← expandBinders bs
  let (bs, args) := Array.unzip <| bvs.map fun view =>
    (view.mkBinder, ⟨view.mkArgument.raw⟩)
  let nonemptyTypeId := id.getId.modifyBase (· ++ `nonemptyType)
  let nonemptyType := mkIdentFrom id nonemptyTypeId
  let nonemptyTypeApp := Syntax.mkApp nonemptyType args
  `(
  opaque $nonemptyType $[$bs]* : NonemptyType.{0}
  $[$doc?:docComment]? $[$vis?:visibility]? def $id $[$bs]* : Type := $nonemptyTypeApp |>.type
  $[$vis?:visibility]? instance : Nonempty $(Syntax.mkApp id args) :=  by
    exact $nonemptyTypeApp |>.property
  )

macro (name := hydrateOpaqueType)
  vis?:optional(visibility) "hydrate_opaque_type " oty:ident ty:ident args:ident*
: command =>
  let mk := mkIdent `mk
  let unsafeMk := mkIdent `unsafeMk
  let get := mkIdent `get
  let unsafeGet := mkIdent `unsafeGet
  `(
  namespace $oty
  @[inline] private unsafe def $unsafeMk : $ty $args* → $oty $args* := unsafeCast
  @[implemented_by $unsafeMk] $[$vis?:visibility]? opaque $mk : $ty $args* → $oty $args*
  $[$vis?:visibility]? instance : Coe ($ty $args*) ($oty $args*) := ⟨$mk⟩

  @[inline] private unsafe def $unsafeGet : $oty $args* → $ty $args* := unsafeCast
  @[implemented_by $unsafeGet] $[$vis?:visibility]? opaque $get $[{$args}]* : $oty $args* → $ty $args*
  $[$vis?:visibility]? instance : Coe ($oty $args*) ($ty $args*) := ⟨$get⟩

  $[$vis?:visibility]? instance [Inhabited ($ty $args*)] : Inhabited ($oty $args*) := ⟨$mk default⟩
  end $oty
  )
