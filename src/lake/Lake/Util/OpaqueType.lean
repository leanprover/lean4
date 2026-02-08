/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public meta import Lake.Util.Binder
public import Init.Notation
import Lake.Util.Binder

/-!
This module provides utilities for defining simple opaque types
for forward declarations. Types are first declared with `nonempty_type`
and then later filled in with `hydrate_opaque_type` once the corresponding
non-opaque type has been defined.
-/

open Lean

namespace Lake

macro (name := nonemptyTypeCmd)
  doc?:optional(docComment) vis?:optional(visibility)
  "nonempty_type " id:ident bs:binder*
: command => do
  let bvs ← expandBinders bs
  let (bs, args) := Array.unzip <| bvs.map fun view =>
    (view.mkBinder, ⟨view.mkArgument.raw⟩)
  let nonemptyType := mkIdentFrom id <| id.getId.modifyBase (·.str "nonemptyType")
  let nonemptyInst := mkIdentFrom id <| id.getId.modifyBase (·.str "instNonempty")
  let nonemptyTypeApp := Syntax.mkApp nonemptyType args
  `(
  private opaque $nonemptyType $[$bs]* : NonemptyType.{0}
  $[$doc?:docComment]? $[$vis?:visibility]? def $id $[$bs]* : Type := $nonemptyTypeApp |>.type
  $[$vis?:visibility]? instance $nonemptyInst:ident : Nonempty $(Syntax.mkApp id args) := by
    exact $nonemptyTypeApp |>.property
  )

macro (name := hydrateOpaqueTypeCmd)
  vis?:optional(visibility) "hydrate_opaque_type " oty:ident ty:ident args:ident*
: command =>
  let mk := mkIdent `mk
  let unsafeMk := mkIdent `unsafeMk
  let instCoeMk := mkIdent `instCoeMk
  let get := mkIdent `get
  let unsafeGet := mkIdent `unsafeGet
  let instCoeGet := mkIdent `instCoeGet
  `(
  namespace $oty
  @[inline] private unsafe def $unsafeMk : $ty $args* → $oty $args* := unsafeCast
  @[implemented_by $unsafeMk] $[$vis?:visibility]? opaque $mk : $ty $args* → $oty $args*
  $[$vis?:visibility]? instance $instCoeMk:ident : Coe ($ty $args*) ($oty $args*) := ⟨$mk⟩

  @[inline] private unsafe def $unsafeGet : $oty $args* → $ty $args* := unsafeCast
  @[implemented_by $unsafeGet] $[$vis?:visibility]? opaque $get $[{$args}]* : $oty $args* → $ty $args*
  $[$vis?:visibility]? instance $instCoeGet:ident : Coe ($oty $args*) ($ty $args*) := ⟨$get⟩

  $[$vis?:visibility]? instance [Inhabited ($ty $args*)] : Inhabited ($oty $args*) := ⟨$mk default⟩
  end $oty
  )
