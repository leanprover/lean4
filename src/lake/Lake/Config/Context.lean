/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Control.Id
public import Lake.Config.Opaque

open System
namespace Lake

/-- A Lake configuration. -/
public structure Context where
  opaqueWs : OpaqueWorkspace

/-- A transformer to equip a monad with a `Lake.Context`. -/
public abbrev LakeT := ReaderT Context

@[inline] public def LakeT.run (ctx : Context) (self : LakeT m α) : m α :=
  ReaderT.run self ctx

/-- A monad equipped with a `Lake.Context`. -/
public abbrev LakeM := LakeT Id

@[inline] public def LakeM.run (ctx : Context) (self : LakeM α) : α :=
  ReaderT.run self ctx |>.run
