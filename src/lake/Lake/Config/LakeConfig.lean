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
public configuration CacheServiceS3Config (name : String) where
  /-- Base URL for an S3-style service's artifacts. -/
  artifactEndpoint : String := ""
  /-- Base URL for an S3-style service's revisions. -/
  revisionEndpoint : String := ""
  /-- Whether the service scopes artifacts and revisions under different per-package scopes. -/
  hasPackageScopes : Bool := true
  deriving Inhabited

set_option linter.unusedVariables false in
public configuration CacheServiceReservoirConfig (name : String) where
  /-- Base URL for a Reservoir-style service's API. -/
  apiEndpoint : String := ""
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
