/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
import Init.Control.Do
public import Lake.Util.JsonObject
public import Lake.Util.Version
public import Lake.Config.Env
public import Lake.Util.Reservoir
import Lake.Util.Proc
import Lake.Util.Url

/-! # Package Registries

This module contains definitions for fetching Lake package information from
a online registry (e.g., Reservoir).
-/

open System Lean

namespace Lake

/--
Package source information from a Lake registry (e.g., Reservoir).
Only contains the subset of fields useful to Lake.
-/
public inductive RegistrySrc
| git (data : JsonObject) (url : String)
  (githubUrl? defaultBranch? : Option String) (subDir? : Option FilePath)
| other (data : JsonObject)
deriving Inhabited

namespace RegistrySrc

public def isGit (src : RegistrySrc) : Bool :=
  match src with
  | .git  .. => true
  | .other .. => false

public def data (src : RegistrySrc) : JsonObject :=
  match src with
  | .git (data := data) .. => data
  | .other data => data

public protected def toJson (src : RegistrySrc) : Json :=
  src.data

public instance : ToJson RegistrySrc := ⟨RegistrySrc.toJson⟩

public protected def fromJson? (val : Json) : Except String RegistrySrc := do
  try
    let obj ← JsonObject.fromJson? val
    if let some url ← obj.get? "gitUrl" then
      let githubUrl? ← (← obj.get? "host").bindM fun host =>
        if host == "github" then obj.get? "repoUrl" else pure none
      let defaultBranch? ← obj.get? "defaultBranch"
      let subDir? ← obj.get? "subDir"
      return .git obj url githubUrl? defaultBranch? subDir?
    else
      return .other obj
  catch e =>
    throw s!"invalid registry source: {e}"

public instance : FromJson RegistrySrc := ⟨RegistrySrc.fromJson?⟩

end RegistrySrc

/--
Package metadata from a Lake registry (e.g., Reservoir).
Only contains the subset of fields useful to Lake.
-/
public structure RegistryPkg where
  name : String
  fullName : String
  sources : Array RegistrySrc
  data : Json
  deriving Inhabited

namespace RegistryPkg

public def gitSrc? (pkg : RegistryPkg) : Option RegistrySrc :=
  pkg.sources.find? (·.isGit)

public protected def toJson (src : RegistryPkg) : Json :=
  src.data

instance : ToJson RegistryPkg := ⟨RegistryPkg.toJson⟩

public protected def fromJson? (val : Json) : Except String RegistryPkg := do
  try
    let obj ← JsonObject.fromJson? val
    let name ← obj.get "name"
    let fullName ← obj.get "fullName"
    let sources ← (← obj.getD "sources" #[]).mapM fromJson?
    return {data := obj, name, fullName, sources}
  catch e =>
    throw s!"invalid registry package: {e}"

public instance : FromJson RegistryPkg := ⟨RegistryPkg.fromJson?⟩

end RegistryPkg

/-- A Reservoir API response object. -/
public inductive ReservoirResp (α : Type u)
| data (a : α)
| error (status : Nat) (message : String)

public protected def ReservoirResp.fromJson? [FromJson α] (val : Json) : Except String (ReservoirResp α) := do
  let obj ← JsonObject.fromJson? val
  if let some (err : JsonObject) ← obj.get? "error" then
    let status ← err.get "status"
    let message ← err.get "message"
    return .error status message
  else if let some (val : Json) ← obj.get? "data" then
    .data <$> fromJson? val
  else
    .data <$> fromJson? val

public instance [FromJson α] : FromJson (ReservoirResp α) := ⟨ReservoirResp.fromJson?⟩

public def Reservoir.pkgApiUrl (lakeEnv : Lake.Env) (owner pkg : String) :=
   s!"{lakeEnv.reservoirApiUrl}/packages/{uriEncode owner}/{uriEncode pkg}"

public def Reservoir.fetchPkg? (lakeEnv : Lake.Env) (owner pkg : String) : LogIO (Option RegistryPkg) := do
  let url := Reservoir.pkgApiUrl lakeEnv owner pkg
  let out ←
    try
      getUrl url Reservoir.lakeHeaders
    catch e =>
      logError s!"{owner}/{pkg}: Reservoir lookup failed"
      throw e
  match Json.parse out with
  | .ok json =>
    match fromJson? json with
    | .ok (resp : ReservoirResp RegistryPkg) =>
      match resp with
      | .data pkg =>
        return pkg
      | .error status msg =>
        if status == 404 then
          return none
        else
          error s!"{owner}/{pkg}: Reservoir lookup failed: {msg}"
    | .error e =>
      errorWithLog do
      logError s!"{owner}/{pkg}: Reservoir lookup failed; server returned unsupported JSON: {e}"
      logVerbose s!"{owner}/{pkg}: Reservoir responded with:\n{out.trimAscii}"
      failure
  | .error e =>
    errorWithLog do
    logError s!"{owner}/{pkg}: Reservoir lookup failed; server returned invalid JSON: {e}"
    logVerbose s!"{owner}/{pkg}: Reservoir responded with:\n{out.trimAscii}"
    failure

/--
Version metadata from a Lake registry (e.g., Reservoir).
Only contains the subset of fields useful to Lake.
-/
public structure RegistryVer where
  version : StdVer
  revision : String

public protected def RegistryVer.fromJson? (val : Json) : Except String RegistryVer := do
  try
    let obj ← JsonObject.fromJson? val
    let version ← obj.get "version"
    let revision ← obj.get "revision"
    return {version, revision}
  catch e =>
    throw s!"invalid registry version: {e}"

public instance : FromJson RegistryVer := ⟨RegistryVer.fromJson?⟩

public def Reservoir.pkgVersionsApiUrl (lakeEnv : Lake.Env) (owner pkg : String) :=
   s!"{lakeEnv.reservoirApiUrl}/packages/{uriEncode owner}/{uriEncode pkg}/versions"

public def Reservoir.fetchPkgVersions
  (lakeEnv : Lake.Env) (owner pkg : String)
: LogIO (Array RegistryVer) := do
  let url := Reservoir.pkgVersionsApiUrl lakeEnv owner pkg
  let out ←
    try
      getUrl url Reservoir.lakeHeaders
    catch e =>
      logError s!"{owner}/{pkg}: Reservoir lookup failed"
      throw e
  match Json.parse out with
  | .ok json =>
    match fromJson? json with
    | .ok (resp : ReservoirResp (Array RegistryVer)) =>
      match resp with
      | .data vers =>
        return vers
      | .error status msg =>
        error s!"{owner}/{pkg}: Reservoir lookup failed (code: {status}): {msg}"
    | .error e =>
      errorWithLog do
      logError s!"{owner}/{pkg}: Reservoir lookup failed; server returned unsupported JSON: {e}"
      logVerbose s!"{owner}/{pkg}: Reservoir responded with:\n{out.trimAscii}"
      failure
  | .error e =>
    errorWithLog do
    logError s!"{owner}/{pkg}: Reservoir lookup failed; server returned invalid JSON: {e}"
    logVerbose s!"{owner}/{pkg}: Reservoir responded with:\n{out.trimAscii}"
    failure
