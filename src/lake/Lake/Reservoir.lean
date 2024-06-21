/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Log
import Lake.Util.Proc
import Lake.Util.JsonObject
import Lake.Config.Env

/-! # Package Registries

This module contains definitions for fetching Lake package information from
a online registry (e.g., Reservoir).
-/

open System Lean

namespace Lake

/--
Package Git source information from a Lake registry (e.g., Reservoir).
Only contains the subset of fields useful to Lake.
-/
structure RegistryGitSrc where
  gitUrl : String
  repoUrl? : Option String
  defaultBranch? : Option String
  subDir? : Option FilePath
  deriving Inhabited

/--
Package source information from a Lake registry (e.g., Reservoir).
Only contains the subset of fields useful to Lake.
-/
inductive RegistrySrc
| git (data : JsonObject) (url : String)
  (repoUrl? defaultBranch? : Option String) (subDir? : Option FilePath)
| other (data : JsonObject)
deriving Inhabited

namespace RegistrySrc

def isGit (src : RegistrySrc) : Bool :=
  match src with
  | .git  .. => true
  | .other .. => false

def data (src : RegistrySrc) : JsonObject :=
  match src with
  | .git (data := data) .. => data
  | .other data => data

protected def toJson (src : RegistrySrc) : Json :=
  src.data

instance : ToJson RegistrySrc := ⟨RegistrySrc.toJson⟩

protected def fromJson? (val : Json) : Except String RegistrySrc := do
  try
    let obj ← JsonObject.fromJson? val
    if let some url ← obj.get? "gitUrl" then
      let repoUrl? ← obj.get? "repoUrl"
      let defaultBranch? ← obj.get? "defaultBranch"
      let subDir? ← obj.get? "subDir"
      return .git obj url repoUrl? defaultBranch? subDir?
    else
      return .other obj
  catch e =>
    throw s!"invalid registry source: {e}"

instance : FromJson RegistrySrc := ⟨RegistrySrc.fromJson?⟩

end RegistrySrc

/--
Package metadata from a Lake registry (e.g., Reservoir).
Only contains the subset of fields useful to Lake.
-/
structure RegistryPkg where
  name : String
  fullName : String
  sources : Array RegistrySrc
  data : Json
  deriving Inhabited

namespace RegistryPkg

def gitSrc? (pkg : RegistryPkg) : Option RegistrySrc :=
  pkg.sources.find? (·.isGit)

protected def toJson (src : RegistryPkg) : Json :=
  src.data

instance : ToJson RegistryPkg := ⟨RegistryPkg.toJson⟩

protected def fromJson? (val : Json) : Except String RegistryPkg := do
  try
    let obj ← JsonObject.fromJson? val
    let name ← obj.get "name"
    let fullName ← obj.get "fullName"
    let sources ← (← obj.getD "sources" #[]).mapM fromJson?
    return {data := obj, name, fullName, sources}
  catch e =>
    throw s!"invalid registry package: {e}"

instance : FromJson RegistryPkg := ⟨RegistryPkg.fromJson?⟩

end RegistryPkg

def getUrl (url : String) (headers : Array String := #[]) : LogIO String := do
  let args := #["-s", "-f", "-L"]
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  captureProc {cmd := "curl", args := args.push url}

def hexEncodeByte (b : UInt8) : Char :=
  if b = 0 then '0' else
  if b = 1 then '1' else
  if b = 2 then '2' else
  if b = 3 then '3' else
  if b = 4 then '4' else
  if b = 5 then '5' else
  if b = 6 then '6' else
  if b = 7 then '7' else
  if b = 8 then '8' else
  if b = 9 then '9' else
  if b = 0xa then 'A' else
  if b = 0xb then 'B' else
  if b = 0xc then 'C' else
  if b = 0xd then 'D' else
  if b = 0xe then 'E' else
  if b = 0xf then 'F' else
  '*'

/-- Encode a byte as a URI escape code (e.g., `%20`). -/
def uriEscapeByte (b : UInt8) (s := "") : String :=
  s.push '%' |>.push (hexEncodeByte <| b >>> 4) |>.push (hexEncodeByte <| b &&& 0xF)

@[specialize] def utf8EncodeCharM [Monad m] (c : Char) (f : σ → UInt8 → m σ) (init : σ) : m σ := do
  let v := c.val
  let s ← f init <| v.toUInt8 &&& 0x3f ||| 0x80
  if v ≤ 0x7f then return s
  let s ← f s <| (v >>>  6).toUInt8 &&& 0x1f ||| 0xc0
  if v ≤ 0x7ff then return s
  let s ← f s <| (v >>> 12).toUInt8 &&& 0x0f ||| 0xe0
  if v ≤ 0xffff then return s
  f s <| (v >>> 18).toUInt8 &&& 0x07 ||| 0xf0

/-- Encode a character as a sequence of URI escape codes representing its UTF8 encoding. -/
def uriEscapeChar (c : Char) (s := "") : String :=
  Id.run <| utf8EncodeCharM c (init := s) fun s b => uriEscapeByte b s

/-- A URI unreserved mark as specified in [RFC2396](https://datatracker.ietf.org/doc/html/rfc2396#section-2.3). -/
def isUriUnreservedMark (c : Char)  : Bool :=
  c matches '-' | '_' | '.' | '!' | '~' | '*' | '\'' | '(' | ')'

/-- Encodes anything but a URI unreserved character as a URI escape sequences. -/
def uriEncodeChar (c : Char) (s := "") : String :=
  if c.isAlphanum || isUriUnreservedMark c then
    s.push c
  else
    uriEscapeChar c s

/-- Encodes a string as an ASCII URI component, escaping special characters (and unicode). -/
def uriEncode (s : String) : String :=
  s.foldl (init := "") fun s c => uriEncodeChar c s

def fetchReservoirPkg (lakeEnv : Lake.Env) (owner pkg : String) : LogIO RegistryPkg := do
  let url := s!"{lakeEnv.reservoirApiUrl}/packages/{uriEncode owner}/{uriEncode pkg}"
  let out ←
    try
      getUrl url #["X-Lake-Registry-Api-Version:0.1.0"]
    catch errPos =>
      logError s!"{pkg}: Reservoir lookup failed"
      throw errPos
  match Json.parse out >>= fromJson? with
  | .ok json =>
    match fromJson? json with
    | .ok pkg => pure pkg
    | .error e => error s!"{pkg}: Reservoir lookup failed: server returned unsupported JSON: {e}"
  | .error e => error s!"{pkg}: Reservoir lookup failed: server returned invalid JSON: {e}"
