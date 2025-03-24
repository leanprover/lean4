/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Toml.Load
import Lake.Toml.Decode
import Lake.Config.Package
import Lake.Util.Log

open Lean Parser
open System (FilePath)

/-! # TOML Loader

This module contains the main definitions to load a package from a
Lake configuration file written in TOML.
-/

namespace Lake

open Toml

/-! ## General Helpers -/

@[specialize] def decodeFieldCore
  (name : Name) (decode : Toml.Value → EDecodeM α) [field : ConfigField σ name α]
  (val : Toml.Value) (cfg : σ)
: DecodeM σ := fun es =>
  match decode val es with
  | .ok a es => .ok (field.set a cfg) es
  | .error _ es => .ok cfg es

class DecodeField (σ : Type) (name : Name) where
  decodeField (val : Toml.Value) (cfg : σ) : DecodeM σ

export DecodeField (decodeField)

instance [DecodeToml α] [ConfigField σ name α] : DecodeField σ name where
  decodeField := decodeFieldCore name decodeToml

structure TomlFieldInfo (σ : Type) where
  decodeAndSet : Toml.Value → σ → Toml.DecodeM σ

abbrev TomlFieldInfos (σ : Type) :=
  NameMap (TomlFieldInfo σ)

def TomlFieldInfos.empty : TomlFieldInfos σ := {}

@[inline] def TomlFieldInfos.insert
  (name : Name) [DecodeField σ name] (infos : TomlFieldInfos σ)
: TomlFieldInfos σ :=
  NameMap.insert infos name ⟨decodeField name⟩

class ConfigTomlInfo (α : Type) where
  fieldInfos : TomlFieldInfos α

def Toml.Table.decodeConfig
  [EmptyCollection α] [ConfigTomlInfo α] (t : Table)
: Toml.DecodeM α :=
  t.foldM (init := {}) fun cfg key val => do
    if let some info := ConfigTomlInfo.fieldInfos.find? key then
      info.decodeAndSet val cfg
    else
      return cfg

@[inline] def decodeTableValue (decode : Table → DecodeM α) (v : Value) : EDecodeM α := do
  ensureDecode <| decode (← v.decodeTable)

/-! ## Value Decoders -/

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

protected def Glob.decodeToml (v : Value) : EDecodeM Glob := do
  match inline <| Glob.ofString? (← v.decodeString) with
  | some v => return v
  | none => throwDecodeErrorAt v.ref "expected glob"

instance : DecodeToml Glob := ⟨Glob.decodeToml⟩
instance : DecodeToml (Array Glob) := ⟨Value.decodeArrayOrSingleton⟩

protected def LeanOptionValue.decodeToml : Value → EDecodeM LeanOptionValue
| .string _ v => return .ofString v
| .boolean _ v => return .ofBool v
| .integer _ (.ofNat v) => return .ofNat v
| x => throwDecodeErrorAt x.ref "expected string, boolean, or nonnegative integer"

instance : DecodeToml LeanOptionValue := ⟨LeanOptionValue.decodeToml⟩

protected def LeanOption.decodeToml (v : Value) : EDecodeM LeanOption := do
  match v with
  | .array ref vs =>
    if h : vs.size = 2 then ensureDecode do
      let name : Name ← tryDecode <| decodeToml vs[0]
      let value ← tryDecode <| decodeToml vs[1]
      return {name, value}
    else
      throwDecodeErrorAt ref "expected array of size 2"
  | .table ref t => ensureDecode do
    let name ← t.tryDecode `name ref
    let value ← t.tryDecode `value ref
    return {name, value}
  | v =>
    throwDecodeErrorAt v.ref "expected array or table"

instance : DecodeToml LeanOption := ⟨LeanOption.decodeToml⟩

protected def BuildType.decodeToml (v : Value) : EDecodeM BuildType := do
  match inline <| BuildType.ofString? (← v.decodeString) with
  | some v => return v
  | none => throwDecodeErrorAt v.ref "expected one of 'debug', 'relWithDebInfo', 'minSizeRel', 'release'"

instance : DecodeToml BuildType := ⟨(BuildType.decodeToml ·)⟩

protected def Backend.decodeToml (v : Value) : EDecodeM Backend := do
  match inline <| Backend.ofString? (← v.decodeString) with
  | some v => return v
  | none => throwDecodeErrorAt v.ref "expected one of 'c', 'llvm', or 'default'"

instance : DecodeToml Backend := ⟨Backend.decodeToml⟩

partial def decodeLeanOptionsAux
  (v : Value) (k : Name) (vs : EDecodeM (Array LeanOption))
: EDecodeM (Array LeanOption) :=
  match v with
  | .table _ t => t.items.foldl (init := vs) fun vs (k',v) =>
    decodeLeanOptionsAux v (k ++ k') vs
  | v => mergeErrors vs (decodeToml v) fun vs v => vs.push ⟨k,v⟩

def decodeLeanOptions (v : Value) : EDecodeM (Array LeanOption) :=
  match v with
  | .array _ vs => decodeArray vs
  | .table _ t => t.items.foldl (init := .ok #[]) fun vs (k,v) => decodeLeanOptionsAux v k vs
  | v => throwDecodeErrorAt v.ref "expected array or table"

instance : DecodeToml (Array LeanOption) := ⟨decodeLeanOptions⟩

protected def StdVer.decodeToml (v : Value) : EDecodeM LeanVer := do
  match StdVer.parse (← v.decodeString) with
  | .ok v => return v
  | .error e => throwDecodeErrorAt v.ref e

instance : DecodeToml StdVer := ⟨StdVer.decodeToml⟩

protected def StrPat.decodeToml (v : Value) (presets : NameMap StrPat := {}) : EDecodeM StrPat :=
  match v with
  | .array _ vs => .mem <$> decodeArray vs
  | .table r t => do
    if let some pre ← t.decode? `startsWith then
      return .startsWith pre
    else if let some name ← t.decode? `preset then
      if let some preset := presets.find? name then
        return preset
      else
        throwDecodeErrorAt r s!"unknown preset '{name}'"
    else
      throwDecodeErrorAt r "expected 'startsWith' or 'preset'"
  | v => throwDecodeErrorAt v.ref "expected array or table"

instance : DecodeToml StrPat := ⟨StrPat.decodeToml⟩

def decodeVersionTags (v : Value) : EDecodeM StrPat :=
  StrPat.decodeToml (presets := versionTagPresets) v

instance : DecodeField (PackageConfig n) `versionTags where
  decodeField := decodeFieldCore `versionTags decodeVersionTags

-- for `platformIndependent`, `releaseRepo`, `buildArchive`, etc.
instance [DecodeToml α] : DecodeToml (Option α) := ⟨(some <$> decodeToml ·)⟩

/-! ## Dependency Configuration Decoders -/

protected def DependencySrc.decodeToml (t : Table) (ref := Syntax.missing) : EDecodeM DependencySrc := do
  let typeVal ← t.decodeValue `type
  match (← typeVal.decodeString) with
  | "path" =>
    return .path (← t.decode `dir)
  | "git" => ensureDecode do
    return .git (← t.tryDecode `url ref) (← t.tryDecode? `rev) (← t.tryDecode? `subDir)
  | _ =>
    throwDecodeErrorAt typeVal.ref "expected one of 'path' or 'git'"

instance : DecodeToml DependencySrc := ⟨fun v => do DependencySrc.decodeToml (← v.decodeTable) v.ref⟩

protected def Dependency.decodeToml (t : Table) (ref := Syntax.missing) : EDecodeM Dependency := ensureDecode do
  let name ← stringToLegalOrSimpleName <$> t.tryDecode `name ref
  let rev? ← t.tryDecode? `rev
  let src? : Option DependencySrc ← id do
    if let some dir ← t.tryDecode? `path then
      return some <| .path dir
    else if let some g := t.find? `git then
      match g with
      | .string _ url =>
        return some <| .git url rev? (← t.tryDecode? `subDir)
      | .table ref t =>
        return some <| .git (← t.tryDecode `url ref) rev? (← t.tryDecode? `subDir)
      | _ =>
        modify (·.push <| .mk g.ref "expected string or table")
        return default
    else
      t.tryDecode? `source
  let scope ← t.tryDecodeD `scope ""
  let version? ← id do
    if let some ver ← t.tryDecode? `version then
      return some ver
    else if let some rev := rev? then
      return if src?.isSome then none else some s!"git#{rev}"
    else
      return none
  let opts ← t.tryDecodeD `options {}
  return {name, scope, version?, src?, opts}

instance : DecodeToml Dependency := ⟨fun v => do Dependency.decodeToml (← v.decodeTable) v.ref⟩

/-! ## Package & Target Configuration Decoders -/

private def genDecodeToml
  (cmds : Array Command)
  (tyName : Name) [info : ConfigInfo tyName]  (takesName : Bool)
  (exclude : Array Name := {})
: MacroM (Array Command) := do
  let init ← `(TomlFieldInfos.empty)
  let ty := if takesName then Syntax.mkCApp tyName #[mkIdent `n] else mkCIdent tyName
  let infos ← info.fields.foldlM (init := init) fun infos {name, parent, ..} =>
    if parent || exclude.contains name then
      return infos
    else
      `($infos |>.insert $(quote name))
  let instId ← mkIdentFromRef <| `_root_ ++ tyName.str "instConfigTomlInfo"
  let cmds ← cmds.push <$> `(instance $instId:ident : ConfigTomlInfo $ty := ⟨$infos⟩)
  let decId ← mkIdentFromRef <| `_root_ ++ tyName.str "decodeToml"
  let cmds ← cmds.push <$> `(protected def $decId (t : Table) : DecodeM $ty := t.decodeConfig)
  let instId ← mkIdentFromRef <| `_root_ ++ tyName.str "instDecodeToml"
  let cmds ← cmds.push <$> `(instance $instId:ident : DecodeToml $ty := ⟨decodeTableValue $decId⟩)
  return cmds

local macro "gen_toml_decoders%" : command => do
  let cmds := #[]
  -- Targets
  let cmds ← genDecodeToml cmds ``LeanConfig false
    (exclude := #[`dynlibs, `plugins])
  let cmds ← genDecodeToml cmds ``LeanLibConfig true
    (exclude := #[`nativeFacets, `dynlibs, `plugins])
  let cmds ← genDecodeToml cmds ``LeanExeConfig true
    (exclude := #[`nativeFacets, `dynlibs, `plugins])
  -- Package
  let cmds ← genDecodeToml cmds ``WorkspaceConfig false
  let cmds ← genDecodeToml cmds ``PackageConfig true
    (exclude := #[`dynlibs, `plugins])
  return ⟨mkNullNode cmds⟩

gen_toml_decoders%

def decodeTargetDecls
  (p : Name) (t : Table)
: DecodeM (Array (PConfigDecl p) × DNameMap (NConfigDecl p)) := do
  let r := (#[], {})
  let r ← go r `lean_lib LeanLibConfig.decodeToml
  let r ← go r `lean_exe LeanExeConfig.decodeToml
  return r
where
  go r k (decode : {n : Name} → Table → DecodeM (ConfigType k p n)) := do
    let some tableArrayVal := t.find? k | return r
    let some vals ← tryDecode? tableArrayVal.decodeValueArray | return r
    vals.foldlM (init := r) fun r val => do
      let some t ← tryDecode? val.decodeTable | return r
      let some name ← tryDecode? <| stringToLegalOrSimpleName <$> t.decode `name
        | return r
      let (decls, map) := r
      if let some orig := map.find? name then
        modify fun es => es.push <| .mk val.ref s!"\
          {p}: target '{name}' was already defined as a '{orig.kind}', \
          but then redefined as a '{k}'"
        return (decls, map)
      else
        let cfg ← @decode name t
        let decl := .mk (.mk p name k cfg) rfl
        return (decls.push decl, map.insert name (.mk decl rfl))

/-! ## Root Loader -/

/-- Load a `Package` from a Lake configuration file written in TOML. -/
def loadTomlConfig (cfg: LoadConfig) : LogIO Package := do
  let input ← IO.FS.readFile cfg.configFile
  let ictx := mkInputContext input cfg.relConfigFile.toString
  match (← loadToml ictx |>.toBaseIO) with
  | .ok table =>
    let .ok pkg errs := EStateM.run (s := #[]) do
      let name ← stringToLegalOrSimpleName <$> table.tryDecode `name
      let config ← @PackageConfig.decodeToml name table
      let (targetDecls, targetDeclMap) ← decodeTargetDecls name table
      let defaultTargets ← table.tryDecodeD `defaultTargets #[]
      let defaultTargets := defaultTargets.map stringToLegalOrSimpleName
      let depConfigs ← table.tryDecodeD `require #[]
      return {
        dir := cfg.pkgDir
        relDir := cfg.relPkgDir
        relConfigFile := cfg.relConfigFile
        scope := cfg.scope
        remoteUrl := cfg.remoteUrl
        config, depConfigs, targetDecls, targetDeclMap
        defaultTargets
      }
    if errs.isEmpty then
      return pkg
    else
      errorWithLog <| errs.forM fun {ref, msg} =>
        let pos := ictx.fileMap.toPosition <| ref.getPos?.getD 0
        logError <| mkErrorStringWithPos ictx.fileName pos msg
  | .error log =>
    errorWithLog <| log.forM fun msg => do logError (← msg.toString)
