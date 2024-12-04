/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Opaque
import Lake.Config.InstallPath

open System
namespace Lake

/-- A Lake configuration. -/
structure Context where
  opaqueWs : OpaqueWorkspace

/-- A transformer to equip a monad with a `Lake.Context`. -/
abbrev LakeT := ReaderT Context

@[inline] def LakeT.run (ctx : Context) (self : LakeT m α) : m α :=
  ReaderT.run self ctx

/-- A monad equipped with a `Lake.Context`. -/
abbrev LakeM := LakeT Id

@[inline] def LakeM.run (ctx : Context) (self : LakeM α) : α :=
  ReaderT.run self ctx |>.run
