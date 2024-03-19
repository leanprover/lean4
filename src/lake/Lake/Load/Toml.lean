/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner
-/
import Lake.Toml
import Lake.Config.Package
import Lake.Util.Log

open Lean Parser

namespace Lake

def mkParserErrorMessage (ictx : InputContext) (s : ParserState) (e : Parser.Error) : Message where
  fileName := ictx.fileName
  pos := ictx.fileMap.toPosition s.pos
  endPos := none
  keepFullRange := true
  data := toString e

def mkExceptionMessage (ictx : InputContext) (e : Exception) : Message where
  fileName := ictx.fileName
  pos := ictx.fileMap.toPosition <| e.getRef.getPos?.getD 0
  endPos := ictx.fileMap.toPosition <$> e.getRef.getTailPos?
  data := e.toMessageData

def mkMessage (ictx : InputContext) (data : MessageData) (severity := MessageSeverity.error) : Message where
  fileName := ictx.fileName
  pos := ictx.fileMap.toPosition 0
  endPos := none
  severity := severity
  data := data

def parseToml (ictx : InputContext) : EIO MessageLog Toml.Table := do
  let env ←
    match (← mkEmptyEnvironment.toBaseIO) with
    | .ok env => pure env
    | .error e => throw <| MessageLog.empty.add <| mkMessage ictx (toString e)
  let s := Toml.toml.fn.run ictx { env, options := {} } (getTokenTable env) (mkParserState ictx.input)
  if let some errorMsg := s.errorMsg then
    throw <|  MessageLog.empty.add <| mkParserErrorMessage ictx s errorMsg
  else if ictx.input.atEnd s.pos then
    let act := Toml.elabToml ⟨s.stxStack.back⟩
    match (← act.run {fileName := ictx.fileName, fileMap := ictx.fileMap} {env} |>.toBaseIO) with
    | .ok (t, s) =>
      if s.messages.hasErrors then
        throw s.messages
      else
        return t
    | .error e =>
      throw <| MessageLog.empty.add <| mkExceptionMessage ictx e
  else
    throw <| MessageLog.empty.add <| mkParserErrorMessage ictx s {expected := ["end of input"]}

structure Toml.DecodeError where
  ref : Syntax
  msg : String

class OfToml (α : Type u) where
  ofToml : Toml.Value → Except (Array Toml.DecodeError) α

export OfToml (ofToml)

namespace Toml

instance : MonadLift (Except ε) (Except (Array ε)) where
  monadLift x := x.mapError Array.singleton

def tryDecode (x : StateM (Array ε) α) : Except (Array ε) α :=
  let (a, es) := x.run #[]; if es.isEmpty then pure a else throw es

@[inline] def partialDecodeD (default : α) (x : Except (Array ε) α) : StateM (Array ε) α :=
  match x with
  | .ok a => pure a
  | .error es => modify (· ++ es) *> pure default

@[inline] def partialDecode [Inhabited α] (x : Except (Array ε) α) : StateM (Array ε) α :=
  partialDecodeD default x

@[inline] def optDecodeD (default : β)  (a? : Option α)  (f : α → Except (Array ε) β) : StateM (Array ε) β :=
  match a? with
  | some a => partialDecodeD default (f a)
  | none => pure default

@[inline] def optDecode [Inhabited β] (a? : Option α)  (f : α → Except (Array ε) β) : StateM (Array ε) β :=
  optDecodeD default a? f

@[inline] def optDecode? (a? : Option α)  (f : α → Except (Array ε) β) : StateM (Array ε) (Option β) :=
  optDecodeD none a? fun a  => some <$> f a

def mergeErrors (x₁ : Except (Array ε) α) (x₂ : Except (Array ε) β) (f : α → β → γ) : Except (Array ε) γ :=
  match x₁, x₂ with
  | .ok a, .ok b => .ok (f a b)
  | .ok _, .error es => .error es
  | .error es, .ok _ => .error es
  | .error es', .error es => .error (es ++ es')

def decodeArray [OfToml α] (vs : Array Value) : Except (Array DecodeError) (Array α) :=
  vs.foldl (init := Except.ok (.mkEmpty vs.size)) fun vs v =>
    mergeErrors vs (ofToml v) Array.push

instance : OfToml Value := ⟨pure⟩

namespace Value

@[inline] def getString : Value → Except DecodeError String
| .string _ v => .ok v
| x => .error (.mk x.ref "expected string")

instance : OfToml String := ⟨(·.getString)⟩
instance : OfToml System.FilePath := ⟨(.mk <$> ofToml ·)⟩

@[inline] def getName (v : Value) : Except DecodeError Name := do
  match (← v.getString).toName with
  | .anonymous => throw (.mk v.ref "expected name")
  | n => pure n

instance : OfToml Lean.Name := ⟨(·.getName)⟩

@[inline] def getInt : Value → Except DecodeError Int
| .integer _ v => .ok v
| x => .error (.mk x.ref "expected integer")

instance : OfToml Int := ⟨(·.getInt)⟩

@[inline] def getNat : Value → Except DecodeError Nat
| .integer _ (.ofNat v) => .ok v
| x => .error (.mk x.ref "expected nonnegative integer")

instance : OfToml Nat := ⟨(·.getNat)⟩

@[inline] def getFloat : Value → Except DecodeError Float
| .float _ v => .ok v
| x => .error (.mk x.ref "expected float")

instance : OfToml Float := ⟨(·.getFloat)⟩

@[inline] def getBool : Value → Except DecodeError Bool
| .boolean _ v => .ok v
| x => .error (.mk x.ref "expected boolean")

instance : OfToml Bool := ⟨(·.getBool)⟩

@[inline] def getDateTime : Value → Except DecodeError DateTime
| .dateTime _ v => .ok v
| x => .error (.mk x.ref "expected date-time")

instance : OfToml DateTime := ⟨(·.getDateTime)⟩

@[inline] def getValueArray : Value → Except DecodeError (Array Value)
| .array _ vs => .ok vs
| x => .error (.mk x.ref "expected array")

def getArray [OfToml α] (v : Value) : Except (Array DecodeError) (Array α) := do
  decodeArray (← v.getValueArray)

instance [OfToml α] : OfToml (Array α) := ⟨getArray⟩

def getArrayOrSingleton [OfToml α] : Value → Except (Array DecodeError) (Array α)
| .array _ vs => decodeArray vs
| v => Array.singleton <$> ofToml v

def getTable : Value → Except DecodeError Table
| .table _ t => .ok t
| x => .error (.mk x.ref "expected table")

instance : OfToml Table := ⟨(·.getTable)⟩

end Value

namespace Table

@[inline] def get? [OfToml α] (t : Table) (k : Name) : StateM (Array DecodeError) (Option α) :=
  optDecode? (t.find? k) ofToml

@[inline] def getD [OfToml α] (k : Name) (default : α) (t : Table) : StateM (Array DecodeError) α :=
  optDecodeD default (t.find? k) ofToml

@[inline] def getValue (t : Table) (k : Name) (ref := Syntax.missing) : Except DecodeError Value := do
  let some a := t.find? k
    | throw (.mk ref s!"missing required key: {ppKey k}")
  return a

def get [OfToml α] (t : Table) (k : Name) (ref := Syntax.missing) : Except (Array DecodeError) α := do
  let a ← t.getValue k ref
  ofToml a |>.mapError fun xs => xs.map fun x =>
    {x with msg := s!"key {ppKey k}: " ++ x.msg}

@[inline] def getI [Inhabited α] [OfToml α] (t : Table) (k : Name) (ref := Syntax.missing) : StateM (Array DecodeError) α := do
  partialDecode <| t.get k ref

def getNameMap [OfToml α] (t : Toml.Table) : Except (Array DecodeError) (NameMap α) := do
  t.items.foldl (init := Except.ok {}) fun m (k,v) =>
    mergeErrors m (ofToml v) fun m v => m.insert k v

instance [OfToml α] : OfToml (NameMap α) := ⟨(do getNameMap <| ← ·.getTable)⟩

end Table

end Toml

open Toml

protected def WorkspaceConfig.ofToml (t : Table) : Except (Array DecodeError) WorkspaceConfig := tryDecode do
  let packagesDir ← t.getD `packagesDir (defaultLakeDir / defaultPackagesDir)
  return {packagesDir}

instance : OfToml WorkspaceConfig := ⟨fun v => do WorkspaceConfig.ofToml (← v.getTable)⟩

protected def LeanOptionValue.ofToml : Value → Except DecodeError LeanOptionValue
| .string _ v => return .ofString v
| .boolean _ v => return .ofBool v
| .integer _ (.ofNat v) => return .ofNat v
| x => throw (.mk x.ref "expected string, boolean, or nonnegative integer")

instance : OfToml LeanOptionValue := ⟨(LeanOptionValue.ofToml ·)⟩

protected def LeanOption.ofToml (v : Value) : Except (Array DecodeError) LeanOption := do
  match v with
  | .array ref vs =>
    if h : vs.size = 2 then tryDecode do
      let name : Name ← partialDecode <| ofToml vs[0]
      let value ← partialDecode <| ofToml vs[1]
      return {name, value}
    else
      throw #[.mk ref "expected array of size 2"]
  | .table ref t => tryDecode do
    let name ← t.getI `name ref
    let value ← t.getI `value ref
    return {name, value}
  | v =>
    throw #[.mk v.ref "expected array or table"]

instance : OfToml LeanOption := ⟨LeanOption.ofToml⟩

def BuildType.ofString? (s : String) : Option BuildType :=
  match s with
  | "debug" => some .debug
  | "relWithDebInfo" => some .relWithDebInfo
  | "minSizeRel" => some .minSizeRel
  | "release" => some .release
  | _ => none

protected def BuildType.ofToml (v : Value) : Except DecodeError BuildType := do
  match inline <| BuildType.ofString? (← v.getString) with
  | some v => return v
  | none => throw <| .mk v.ref "expected one of 'debug' 'relWithDebInfo', 'minSizeRel', 'release'"

instance : OfToml BuildType := ⟨(BuildType.ofToml ·)⟩

partial def decodeLeanOptionsAux
  (v : Value) (k : Name) (vs : Except (Array DecodeError) (Array LeanOption))
: Except (Array DecodeError) (Array LeanOption) :=
  match v with
  | .table _ t => t.items.foldl (init := vs) fun vs (k',v) =>
    decodeLeanOptionsAux v (k ++ k') vs
  | v => mergeErrors vs (ofToml v) fun vs v => vs.push ⟨k,v⟩

def decodeLeanOptions (v : Value) : Except (Array DecodeError) (Array LeanOption) :=
  match v with
  | .array _ vs => decodeArray vs
  | .table _ t => t.items.foldl (init := .ok #[]) fun vs (k,v) => decodeLeanOptionsAux v k vs
  | v =>
    throw #[.mk v.ref "expected array or table"]

protected def LeanConfig.ofToml (t : Table) : Except (Array DecodeError) LeanConfig := tryDecode do
  let buildType ← t.getD `buildType .release
  let platformIndependent ← t.get? `platformIndependent
  let leanOptions ← optDecodeD #[] (t.find? `leanOptions) decodeLeanOptions
  let moreServerOptions ← t.getD `moreServerOptions #[]
  let moreLeanArgs ← t.getD `moreLeanArgs #[]
  let weakLeanArgs ← t.getD `weakLeanArgs #[]
  let moreLeancArgs ← t.getD `moreLeancArgs #[]
  let weakLeancArgs ← t.getD `weakLeancArgs #[]
  let moreLinkArgs ← t.getD `moreLinkArgs #[]
  let weakLinkArgs ← t.getD `weakLinkArgs #[]
  return {
    buildType, platformIndependent, leanOptions, moreServerOptions,
    moreLeanArgs, weakLeanArgs, moreLeancArgs, weakLeancArgs, moreLinkArgs, weakLinkArgs
  }

instance : OfToml LeanConfig := ⟨fun v => do LeanConfig.ofToml (← v.getTable)⟩

protected def PackageConfig.ofToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) PackageConfig := tryDecode do
  let name ← stringToLegalOrSimpleName <$> t.getI `name ref
  let precompileModules ← t.getD `precompileModules false
  let moreGlobalServerArgs ← t.getD `moreGlobalServerArgs #[]
  let srcDir ← t.getD `srcDir "."
  let buildDir ← t.getD `buildDir defaultBuildDir
  let leanLibDir ← t.getD `buildDir defaultLeanLibDir
  let nativeLibDir ← t.getD `nativeLibDir defaultNativeLibDir
  let binDir ← t.getD `binDir defaultBinDir
  let irDir ← t.getD `irDir defaultIrDir
  let releaseRepo ← t.get? `releaseRepo
  let buildArchive? ← t.get? `buildArchive
  let preferReleaseBuild ← t.getD `preferReleaseBuild false
  let toLeanConfig ← partialDecode <| LeanConfig.ofToml t
  let toWorkspaceConfig ← partialDecode <| WorkspaceConfig.ofToml t
  return {
    name, precompileModules, moreGlobalServerArgs,
    srcDir, buildDir, leanLibDir, nativeLibDir, binDir, irDir,
    releaseRepo, buildArchive?, preferReleaseBuild
    toLeanConfig, toWorkspaceConfig
  }

instance : OfToml PackageConfig := ⟨fun v => do PackageConfig.ofToml (← v.getTable) v.ref⟩

def takeNamePart (ss : Substring) (pre : Name) : (Substring × Name) :=
  if ss.isEmpty then
    (ss, .anonymous)
  else
    let curr := ss.front
    if isIdBeginEscape curr then
      let ss := ss.drop 1
      let startPos := ss.startPos
      let ss := ss.dropWhile (!isIdEndEscape ·)
      if isIdEndEscape ss.front then
        let id := ss.str.extract startPos ss.startPos
        (ss, Name.str pre id)
      else
        (ss, .anonymous)
    else if isIdFirst curr then
      let startPos := ss.startPos
      let ss := ss.drop 1 |>.dropWhile isIdRest
      let id := ss.str.extract startPos ss.startPos
      (ss, Name.str pre id)
    else if curr.isDigit then
      let startPos := ss.startPos
      let ss := ss.drop 1 |>.dropWhile Char.isDigit
      let digits := ss.str.extract startPos ss.startPos
      let n := (Syntax.decodeNatLitVal? digits).get!
      (ss, Name.num pre n)
    else
      (ss, .anonymous)

partial def takeName (ss : Substring) : (Substring × Name) :=
  let rec takeRest ss pre :=
    if ss.front == '.' then
      let startPos := ss.startPos
      let (ss, n) := takeNamePart (ss.drop 1) pre
      if n.isAnonymous then ({ss with startPos}, pre) else takeRest ss n
    else
      (ss, pre)
  let (ss, n) := takeNamePart ss .anonymous
  if n.isAnonymous then (ss, .anonymous) else takeRest ss n

def Glob.ofString? (v : String) : Option Glob := do
  let (ss, n) := takeName v.toSubstring
  if n.isAnonymous then failure
  if h : ss.str.atEnd ss.startPos then
    return .one n
  else if ss.str.get' ss.startPos h == '.' then
    match (ss.drop 1).front with
    | '+' => return .submodules n
    | '*' => return .andSubmodules n
    | _ => failure
  else
    failure

protected def Glob.ofToml (v : Value) : Except DecodeError Glob := do
  match inline <| Glob.ofString? (← v.getString) with
  | some v => return v
  | none => throw <| .mk v.ref "expected glob"

instance : OfToml Glob := ⟨(Glob.ofToml ·)⟩

protected def LeanLibConfig.ofToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) LeanLibConfig := tryDecode do
  let name : Name ← t.getI `name ref
  let srcDir ← t.getD `srcDir "."
  let roots ← t.getD `roots #[name]
  let globs ← optDecodeD (roots.map Glob.one) (t.find? `globs) (·.getArrayOrSingleton)
  let libName ← t.getD `libName (name.toString (escape := false))
  let precompileModules ← t.getD `precompileModules false
  let defaultFacets ← t.getD `defaultFacets #[LeanLib.leanArtsFacet]
  let toLeanConfig ← partialDecode <| LeanConfig.ofToml t
  return {
    name, srcDir, roots, globs, libName,
    precompileModules, defaultFacets, toLeanConfig
  }

instance : OfToml LeanLibConfig := ⟨fun v => do LeanLibConfig.ofToml (← v.getTable) v.ref⟩

protected def LeanExeConfig.ofToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) LeanExeConfig := tryDecode do
  let name ← stringToLegalOrSimpleName <$> t.getI `name ref
  let srcDir ← t.getD `srcDir "."
  let root ← t.getD `root name
  let exeName ← t.getD `exeName (name.toStringWithSep "-" (escape := false))
  let supportInterpreter ← t.getD `supportInterpreter false
  let toLeanConfig ← partialDecode <| LeanConfig.ofToml t
  return {name, srcDir, root, exeName, supportInterpreter, toLeanConfig}

instance : OfToml LeanExeConfig := ⟨fun v => do LeanExeConfig.ofToml (← v.getTable) v.ref⟩

protected def Source.ofToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) Source := do
  let typeVal ← t.getValue `type
  match (← typeVal.getString) with
  | "path" =>
    return Source.path (← t.get `dir)
  | "git" => tryDecode do
    return Source.git (← t.getI `url ref) (← t.get? `rev) (← t.get? `subDir)
  | _ =>
    throw #[DecodeError.mk typeVal.ref "expected one of 'path' or 'git'"]

instance : OfToml Source := ⟨fun v => do Source.ofToml (← v.getTable) v.ref⟩

protected def Dependency.ofToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) Dependency := tryDecode do
  let name ← t.getI `name ref
  let src ← id do
    if let some dir ← t.get? `path then
      return Source.path dir
    else if let some g := t.find? `git then
      match g with
      | .string _ url =>
        return Source.git url (← t.get? `rev) (← t.get? `subDir)
      | .table ref t =>
        return Source.git (← t.getI `url ref) (← t.get? `rev) (← t.get? `subDir)
      | _ =>
        modify (·.push <| .mk g.ref "expected string or table")
        return default
    else
      t.getI `source ref
  let opts ← t.getD `options {}
  return {name, src, opts}

instance : OfToml Dependency := ⟨fun v => do Dependency.ofToml (← v.getTable) v.ref⟩

@[inline] def mkRBArray  (f : β → α) (vs : Array β) : RBArray α β cmp :=
  vs.foldl (init := RBArray.mkEmpty vs.size) fun m v => m.insert (f v) v

def loadTomlConfig (dir relDir relConfigFile : FilePath) : LogIO Package := do
  let configFile := dir / relConfigFile
  let input ← IO.FS.readFile configFile
  let ictx := mkInputContext input relConfigFile.toString
  match (← parseToml ictx |>.toBaseIO) with
  | .ok table =>
    let r := tryDecode do
      let config ← partialDecode <| PackageConfig.ofToml table
      let leanLibConfigs ← mkRBArray (·.name) <$> table.getD `lean_lib #[]
      let leanExeConfigs ← mkRBArray (·.name) <$> table.getD `lean_exe #[]
      let defaultTargets ← table.getD `defaultTargets #[]
      let depConfigs ← table.getD `require #[]
      return {
        dir, relDir, relConfigFile,
        config, depConfigs, leanLibConfigs, leanExeConfigs, defaultTargets
      }
    match r with
    | .ok pkg => return pkg
    | .error es =>
      es.forM fun {ref, msg} =>
        let pos := ictx.fileMap.toPosition <| ref.getPos?.getD 0
        logError <| mkErrorStringWithPos ictx.fileName pos msg
      failure
  | .error log =>
    log.forM fun msg => do logError (← msg.toString)
    failure
