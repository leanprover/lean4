/-
Copyright (c) 2026 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Cache
public import Lake.Config.MetaClasses
meta import Lake.Config.Meta

open System Lean

namespace Lake

public configuration CacheConfig where
  defaultService : Name := .anonymous
  services : Array CacheService := #[]
  deriving Inhabited

public configuration LakeConfig where
  cache : CacheConfig := ∅
  deriving Inhabited
