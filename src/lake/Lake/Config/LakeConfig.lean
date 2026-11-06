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

set_option linter.unusedVariables false in
public configuration CacheServiceConfig (name : String) where
  kind, type : CacheServiceKind := .undef
  apiEndpoint : String := ""
  artifactEndpoint : String := ""
  revisionEndpoint : String := ""
  deriving Inhabited

public abbrev CacheServiceMap :=  NameMap CacheService

public configuration CacheConfig where
  defaultService : String := ""
  defaultUploadService : String := ""
  services @ service : CacheServiceMap := {}
  deriving Inhabited

public configuration LakeConfig where
  cache : CacheConfig := ∅
  deriving Inhabited

public structure LoadedLakeConfig where
  config : LakeConfig := ∅
  defaultCacheService : CacheService
  defaultCacheUploadService? : Option CacheService := none
  cacheServices : CacheServiceMap
  deriving Nonempty
