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

public inductive CacheServiceKind
| undef
| reservoir
| s3
deriving Inhabited

@[inline]
public def CacheServiceKind.ofString? (s : String) : Option CacheServiceKind :=
  match s with
  | "reservoir" => some .reservoir
  | "s3" => some .s3
  | _ => none

public configuration CacheServiceConfig where
  name : String := ""
  kind, type : CacheServiceKind := .undef
  apiEndpoint : String := ""
  artifactEndpoint : String := ""
  revisionEndpoint : String := ""
  deriving Inhabited

public configuration CacheConfig where
  defaultService : String := ""
  defaultUploadService : String := ""
  services @ service : Array CacheServiceConfig := #[]
  deriving Inhabited

public configuration LakeConfig where
  cache : CacheConfig := ∅
  deriving Inhabited

public structure LoadedLakeConfig where
  config : LakeConfig
  defaultCacheService : CacheService
  defaultUploadCacheService? : Option CacheService
  cacheServices : NameMap CacheService
  deriving Nonempty
