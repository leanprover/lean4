/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
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
Package source information from a Lake registry (e.g., Reservoir).
Only contains the subset of fields useful to Lake.
-/
inductive RegistrySrc
| git (data : JsonObject) (url : String)
  (githubUrl? defaultBranch? : Option String) (subDir? : Option FilePath)
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
      let githubUrl? ← (← obj.get? "host").bindM fun host =>
        if host == "github" then obj.get? "repoUrl" else pure none
      let defaultBranch? ← obj.get? "defaultBranch"
      let subDir? ← obj.get? "subDir"
      return .git obj url githubUrl? defaultBranch? subDir?
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

/-- Folds a monadic function over the UTF-8 bytes of `Char` from most significant to least significant. -/
@[specialize] def foldlUtf8M [Monad m] (c : Char) (f : σ → UInt8 → m σ) (init : σ) : m σ := do
  let s := init
  let v := c.val
  if v ≤ 0x7f then
    f s v.toUInt8
  else if v ≤ 0x7ff then
    let s ← f s <| (v >>>  6).toUInt8 &&& 0x1f ||| 0xc0
    let s ← f s <| v.toUInt8 &&& 0x3f ||| 0x80
    return s
  else if v ≤ 0xffff then
    let s ← f s <| (v >>> 12).toUInt8 &&& 0x0f ||| 0xe0
    let s ← f s <| (v >>>  6).toUInt8 &&& 0x3f ||| 0x80
    let s ← f s <| v.toUInt8 &&& 0x3f ||| 0x80
    return s
  else
    let s ← f s <| (v >>> 18).toUInt8 &&& 0x07 ||| 0xf0
    let s ← f s <| (v >>> 12).toUInt8 &&& 0x3f ||| 0x80
    let s ← f s <| (v >>>  6).toUInt8 &&& 0x3f ||| 0x80
    let s ← f s <| v.toUInt8 &&& 0x3f ||| 0x80
    return s

abbrev foldlUtf8 (c : Char) (f : σ → UInt8 → σ) (init : σ) : σ :=
  Id.run <| foldlUtf8M c f init

example : foldlUtf8 c (fun l b => b::l) List.nil = (String.utf8EncodeChar c).reverse := by
  simp only [foldlUtf8M, String.utf8EncodeChar, Id.run]
  if h1 : c.val ≤ 0x7f then simp [h1]
  else if h2 : c.val ≤ 0x7ff then simp [h1, h2]
  else if h3 : c.val ≤ 0xffff then simp [h1, h2, h3]
  else simp [h1, h2, h3]

/-- Encode a character as a sequence of URI escape codes representing its UTF8 encoding. -/
def uriEscapeChar (c : Char) (s := "") : String :=
  foldlUtf8 c (init := s) fun s b => uriEscapeByte b s

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

/-- Perform a HTTP `GET` request of a URL (using `curl`) and return the body. -/
def getUrl (url : String) (headers : Array String := #[]) : LogIO String := do
  let args := #["-s", "-L", "--retry", "3"] -- intermittent network errors can occur
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  captureProc {cmd := "curl", args := args.push url}

/-- A Reservoir API response object. -/
inductive ReservoirResp (α : Type u)
| data (a : α)
| error (status : Nat) (message : String)

protected def ReservoirResp.fromJson? [FromJson α] (val : Json) : Except String (ReservoirResp α) := do
  let obj ← JsonObject.fromJson? val
  if let some (err : JsonObject) ← obj.get? "error" then
    let status ← err.get "status"
    let message ← err.get "message"
    return .error status message
  else
    .data <$> fromJson? val

instance [FromJson α] : FromJson (ReservoirResp α) := ⟨ReservoirResp.fromJson?⟩

def Reservoir.pkgApiUrl (lakeEnv : Lake.Env) (owner pkg : String) :=
   s!"{lakeEnv.reservoirApiUrl}/packages/{uriEncode owner}/{uriEncode pkg}"

def Reservoir.lakeHeaders := #[
  "X-Reservoir-Api-Version:1.0.0",
  "X-Lake-Registry-Api-Version:0.1.0"
]

def Reservoir.fetchPkg? (lakeEnv : Lake.Env) (owner pkg : String) : LogIO (Option RegistryPkg) := do
  let url := Reservoir.pkgApiUrl lakeEnv owner pkg
  let out ←
    try
      getUrl url Reservoir.lakeHeaders
    catch e =>
      logError s!"{owner}/{pkg}: Reservoir lookup failed"
      throw e
  match Json.parse out >>= fromJson? with
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
      logVerbose s!"{owner}/{pkg}: Reservoir responded with:\n{out.trim}"
      failure
  | .error e =>
    errorWithLog do
    logError s!"{owner}/{pkg}: Reservoir lookup failed; server returned invalid JSON: {e}"
    logVerbose s!"{owner}/{pkg}: Reservoir responded with:\n{out.trim}"
    failure
