/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Factory
-/
module

prelude
import Lean.CoreM
import Lean.Compiler.LCNF.EmitZig.InlineHelpers
import Lean.Compiler.LCNF.EmitZig.RuntimeExterns
public import Lean.Expr
public import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.EmitUtil
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.ClosedTermCache
import Lean.Compiler.LCNF.SimpleGroundExpr
import Lean.Compiler.NameMangling
import Lean.Compiler.ModPkgExt
import Lean.Runtime
import Init.Data.String.Legacy

open Lean Compiler LCNF RuntimeExterns
namespace Lean.Compiler.LCNF
def leanMainFn := "_lean_main"
namespace ImpureType

def Lean.Expr.toZigType : Expr → String
  | ImpureType.uint8 => "u8"
  | ImpureType.uint16 => "u16"
  | ImpureType.uint32 => "u32"
  | ImpureType.uint64 => "u64"
  | ImpureType.usize => "usize"
  | ImpureType.float => "f64"
  | ImpureType.float32 => "f32"
  | _ => "LeanObj"

def Lean.Expr.unboxOpName : Expr → String
  | ImpureType.usize => "lean_unbox_usize"
  | ImpureType.uint32 => "lean_unbox_uint32"
  | ImpureType.uint64 => "lean_unbox_uint64"
  | ImpureType.float => "lean_unbox_float"
  | ImpureType.float32 => "lean_unbox_float32"
  | _ => "lean_unbox"

def Lean.Expr.boxOpName : Expr → String
  | ImpureType.usize => "lean_box_usize"
  | ImpureType.uint32 => "lean_box_uint32"
  | ImpureType.uint64 => "lean_box_uint64"
  | ImpureType.float => "lean_box_float"
  | ImpureType.float32 => "lean_box_float32"
  | _ => "lean_box"

def Lean.Expr.sprojOpName : Expr → String
  | ImpureType.float => "lean_ctor_get_float"
  | ImpureType.float32 => "lean_ctor_get_float32"
  | ImpureType.uint8 => "lean_ctor_get_uint8"
  | ImpureType.uint16 => "lean_ctor_get_uint16"
  | ImpureType.uint32 => "lean_ctor_get_uint32"
  | ImpureType.uint64 => "lean_ctor_get_uint64"
  | _ => unreachable!

def Lean.Expr.ssetOpName : Expr → String
  | ImpureType.float => "lean_ctor_set_float"
  | ImpureType.float32 => "lean_ctor_set_float32"
  | ImpureType.uint8 => "lean_ctor_set_uint8"
  | ImpureType.uint16 => "lean_ctor_set_uint16"
  | ImpureType.uint32 => "lean_ctor_set_uint32"
  | ImpureType.uint64 => "lean_ctor_set_uint64"
  | _ => unreachable!

end ImpureType

open ImpureType

structure Context where
  localDecls : Array (Decl .impure)
  otherModuleDecls : Array (Signature .impure)
  modName : Name
  currFn : Name := .anonymous
  currParams : Array (Param .impure) := #[]
  fvarTypes : NameMap Expr := {}
  joinDecls : NameMap (FunDecl .impure) := {}
  joinStates : NameMap Nat := {}
  hoistLocals : Bool := false

structure State where
  buf : ByteArray := ByteArray.empty
abbrev EmitM := ReaderT Context <| StateRefT State CoreM

def externFnName? (decl : String) : Option String :=
  if decl.startsWith "extern fn " then
    match (decl.drop 10).toString.splitOn "(" with
    | name :: _ => some name
    | [] => none
  else
    none

def runtimeExternDecls : List String :=
  runtimeExternDeclsGenerated.filter fun decl =>
    match externFnName? decl with
    | some name => !InlineHelpers.isInlineHelperName name
    | none => true

def runtimeExternNames : List String :=
  runtimeExternDecls.filterMap externFnName?

def runtimeExternDeclsForModule (localNames : Array String) : List String :=
  runtimeExternDecls.filter fun decl =>
    match externFnName? decl with
    | some name => !localNames.contains name
    | none => true

@[inline] def emit (text : String) : EmitM Unit :=
  modify fun s => { s with buf := s.buf ++ text.toUTF8 }

@[inline] def emitLn (text : String) : EmitM Unit := do
  emit text
  emit "\n"

@[inline] def emitLns (lines : List String) : EmitM Unit :=
  lines.forM emitLn

def captureOutput (act : EmitM Unit) : EmitM String := do
  let saved ← get
  set { saved with buf := ByteArray.empty }
  act
  let out := String.fromUTF8! (← get).buf
  set saved
  pure out

def bodyUsesIdent (body ident : String) : Bool :=
  if !body.contains ident then
    false
  else
    body.splitOn "\n" |>.any fun line =>
      let trimmed := line.trimAsciiStart.toString
      !(trimmed.startsWith s!"const {ident}:" || trimmed.startsWith s!"var {ident}:") &&
        line.contains ident

@[inline] def getModName : EmitM Name :=
  return (← read).modName

@[inline] def getLocalDecls : EmitM (Array (Decl .impure)) :=
  return (← read).localDecls

@[inline] def getOtherModuleDecls : EmitM (Array (Signature .impure)) :=
  return (← read).otherModuleDecls

@[inline] def getCurrFn : EmitM Name := return (← read).currFn

@[inline] def getCurrParams : EmitM (Array (Param .impure)) := return (← read).currParams

def getStoredType (fvarId : FVarId) : EmitM Expr := do
  let some type := (← read).fvarTypes.find? fvarId.name | throwError "unknown EmitZig local type {fvarId.name}"
  return type

def findStoredJoinDecl? (fvarId : FVarId) : EmitM (Option (FunDecl .impure)) := return (← read).joinDecls.find? fvarId.name
def findStoredJoinState? (fvarId : FVarId) : EmitM (Option Nat) := return (← read).joinStates.find? fvarId.name

def runtimeParams (ps : Array (Param .impure)) : Array (Param .impure) :=
  ps.filter (fun p => !(p.type.isVoid || p.type.isErased))

def runtimeArgs (ps : Array (Param .impure)) (args : Array (Arg .impure)) : Array (Arg .impure) :=
  Id.run do
    let mut filtered := #[]
    for h : i in [0:args.size] do
      let arg := args[i]
      let p := ps[i]!
      if !(p.type.isVoid || p.type.isErased) then
        filtered := filtered.push arg
    filtered
def argMatchesParam (p : Param .impure) : Arg .impure → Bool
  | .fvar fvarId => p.fvarId == fvarId
  | .erased => false

def argUsesFVar (target : FVarId) : Arg .impure → Bool
  | .fvar fvarId => fvarId == target
  | .erased => false

def argsUseFVar (target : FVarId) (args : Array (Arg .impure)) : Bool :=
  args.any (argUsesFVar target)

def letValueUsesFVar (target : FVarId) : LetValue .impure → Bool
  | .ctor _ args => argsUseFVar target args
  | .reset _ fvarId | .oproj _ fvarId | .uproj _ fvarId | .sproj _ _ fvarId
  | .box _ fvarId | .unbox fvarId | .isShared fvarId => fvarId == target
  | .reuse fvarId _ _ args | .fvar fvarId args => fvarId == target || argsUseFVar target args
  | .fap _ args | .pap _ args => argsUseFVar target args
  | .lit .. | .erased => false

partial def codeUsesFVar (target : FVarId) : Code .impure → Bool
  | .let decl k => letValueUsesFVar target decl.value || codeUsesFVar target k
  | .jp decl k => codeUsesFVar target decl.value || codeUsesFVar target k
  | .inc fvarId _ _ _ k
  | .dec fvarId _ _ _ _ k
  | .del fvarId k | .setTag fvarId _ k =>
      fvarId == target || codeUsesFVar target k
  | .oset fvarId _ arg k =>
      fvarId == target || argUsesFVar target arg || codeUsesFVar target k
  | .uset fvarId _ y k | .sset fvarId _ _ y _ k =>
      fvarId == target || y == target || codeUsesFVar target k
  | .cases cs =>
      cs.discr == target || cs.alts.any (fun alt => codeUsesFVar target alt.getCode)
  | .jmp _ args => argsUseFVar target args
  | .return fvarId => fvarId == target
  | .unreach .. => false

partial def letValueUsesFVarRuntime (target : FVarId) : LetValue .impure → EmitM Bool
  | .ctor _ args => pure <| argsUseFVar target args
  | .reset _ fvarId | .oproj _ fvarId | .uproj _ fvarId | .sproj _ _ fvarId
  | .box _ fvarId | .unbox fvarId | .isShared fvarId =>
      pure <| fvarId == target
  | .reuse fvarId _ _ args | .fvar fvarId args =>
      pure <| fvarId == target || argsUseFVar target args
  | .fap fn args | .pap fn args => do
      match ← getImpureSignature? fn with
      | some sig => pure <| argsUseFVar target (runtimeArgs sig.params args)
      | none => pure <| argsUseFVar target args
  | .lit .. | .erased => pure false

partial def codeUsesFVarRuntime (target : FVarId) : Code .impure → EmitM Bool
  | .let decl k => do
      let lhs ← letValueUsesFVarRuntime target decl.value
      let rhs ← codeUsesFVarRuntime target k
      pure (lhs || rhs)
  | .jp decl k => do
      let lhs ← codeUsesFVarRuntime target decl.value
      let rhs ← codeUsesFVarRuntime target k
      pure (lhs || rhs)
  | .inc fvarId _ _ _ k
  | .dec fvarId _ _ _ _ k
  | .del fvarId k | .setTag fvarId _ k => do
      if fvarId == target then pure true else codeUsesFVarRuntime target k
  | .oset fvarId _ arg k => do
      if fvarId == target || argUsesFVar target arg then pure true else codeUsesFVarRuntime target k
  | .uset fvarId _ y k | .sset fvarId _ _ y _ k => do
      if fvarId == target || y == target then pure true else codeUsesFVarRuntime target k
  | .cases cs => do
      if cs.discr == target then
        pure true
      else
        cs.alts.anyM fun alt => codeUsesFVarRuntime target alt.getCode
  | .jmp fvarId args => do
      let some jpDecl ← findStoredJoinDecl? fvarId | unreachable!
      pure <| argsUseFVar target (runtimeArgs jpDecl.params args)
  | .return fvarId => pure <| fvarId == target
  | .unreach .. => pure false

partial def tailCallMutatesParam (fnName : Name) (ps : Array (Param .impure)) (target : FVarId) :
    Code .impure → Bool
  | .let decl (.return fvarId) =>
      match decl.value with
      | .fap callee args =>
          if decl.fvarId == fvarId && callee == fnName then
            let runtimePs := runtimeParams ps
            let runtimeArgs := runtimeArgs ps args
            Id.run do
              for h : i in [0:runtimePs.size] do
                let p := runtimePs[i]
                if p.fvarId == target then
                  return !(argMatchesParam p runtimeArgs[i]!)
              false
          else
            false
      | _ => false
  | .let _ k => tailCallMutatesParam fnName ps target k
  | .jp decl k => tailCallMutatesParam fnName ps target decl.value || tailCallMutatesParam fnName ps target k
  | .inc _ _ _ _ k
  | .dec _ _ _ _ _ k
  | .del _ k | .setTag _ _ k | .oset _ _ _ k | .uset _ _ _ k
  | .sset _ _ _ _ _ k => tailCallMutatesParam fnName ps target k
  | .cases cs => cs.alts.any (fun alt => tailCallMutatesParam fnName ps target alt.getCode)
  | .jmp .. | .return .. | .unreach .. => false

@[inline] def zigParamIdent (name : Name) : String := name.mangle (pre := "arg_v_")

def toZigSymbolName (n : Name) : EmitM String := do
  let env ← getEnv
  match getExportNameFor? env n with
  | some (.str .anonymous s) => pure s
  | some _ => throwError s!"invalid export name '{n}'"
  | none => pure <| if n == `main then leanMainFn else getSymbolStem env n

def toZigDefName (n : Name) : EmitM String :=
  return s!"{← toZigSymbolName n}__def"

def getLocalRuntimeSymbolNames : EmitM (Array String) := do
  let env ← getEnv
  let mut names : Array String := #[]
  for decl in (← getLocalDecls) do
    match decl.value with
    | .code _ =>
      let sym ← toZigSymbolName decl.name
      names := names.push sym
      if let some extName := getExternNameFor env `c decl.name then
        names := names.push extName
    | _ => pure ()
  return names

def getModInitFn : EmitM String := do
  let env ← getEnv
  let pkg? := env.getModulePackage?
  return mkModuleInitializationFunctionName (← getModName) pkg? .all

def importedInitFnNames : EmitM (Array String) := do
  let env ← getEnv
  let names ← env.imports.filterMapM fun imp => do
    let some idx := env.getModuleIdx? imp.module | return none
    let pkg? := env.getModulePackageByIdx? idx
    return some <| mkModuleInitializationFunctionName imp.module pkg? .all
  return names.foldl (init := #[]) fun acc name =>
    if acc.contains name then acc else acc.push name

def emitParamList (ps : Array (Param .impure)) : EmitM Unit := do
  let ps := runtimeParams ps
  for h : i in [0:ps.size] do
    if i > 0 then
      emit ", "
    let p := ps[i]
    emit s!"{zigParamIdent p.fvarId.name}: {p.type.toZigType}"

def emitSignature (name : String) (sig : Signature .impure) : EmitM Unit := do
  emit s!"extern fn {name}("
  emitParamList sig.params
  emitLn s!") callconv(.c) {sig.type.toZigType};"

def emitClosedTermDecl (name : String) (type : Expr) : EmitM Unit :=
  emitLn s!"extern var {name}: {type.toZigType};"

def closedTermReadOpName (t : Expr) : String :=
  match t with
  | ImpureType.float => "lean_float_once_cold"
  | ImpureType.float32 => "lean_float32_once_cold"
  | ImpureType.uint8 => "lean_uint8_once_cold"
  | ImpureType.uint16 => "lean_uint16_once_cold"
  | ImpureType.uint32 => "lean_uint32_once_cold"
  | ImpureType.uint64 => "lean_uint64_once_cold"
  | ImpureType.usize => "lean_usize_once_cold"
  | ImpureType.object | ImpureType.tobject | ImpureType.tagged | ImpureType.void => "lean_obj_once_cold"
  | _ => "lean_obj_once_cold"

def toOnceTokenName (sym : String) : String :=
  sym ++ "_once"

def toZigInitName (n : Name) : EmitM String := do
  return s!"_init_{← toZigSymbolName n}"

def isStandardExternC? (env : Environment) (name : Name) : Option String :=
  getExternAttrData? env name |>.bind fun data =>
    match getExternEntryFor data `c with
    | some (.standard _ externName) => some externName
    | _ => none

def isGlobalVarSignature (env : Environment) (sig : Signature .impure) : Bool :=
  (runtimeParams sig.params).isEmpty && (isStandardExternC? env sig.name).isNone

@[inline] def zigIdent (name : Name) : String :=
  name.mangle (pre := "v_")

@[inline] def tailStateIdent (name : Name) : String :=
  name.mangle (pre := "tail_v_")

@[inline] def usizeLit (n : Nat) : String :=
  s!"@as(usize, {n})"

@[inline] def cUIntLit (n : Nat) : String :=
  s!"@as(c_uint, {n})"

def quoteZigString (s : String) : String :=
  let escaped := s.replace "\\" "\\\\"
  let escaped := escaped.replace "\"" "\\\""
  let escaped := escaped.replace "\n" "\\n"
  let escaped := escaped.replace "\t" "\\t"
  let escaped := escaped.replace "\r" "\\r"
  "\"" ++ escaped ++ "\""

def renderImpureArg : Arg .impure → String
  | .fvar fvarId => zigIdent fvarId.name
  | .erased => s!"lean_box({usizeLit 0})"

def renderImpureArgs (args : Array (Arg .impure)) : List String :=
  args.toList.map renderImpureArg

def renderArgList (args : Array (Arg .impure)) : String :=
  String.intercalate ", " (renderImpureArgs args)

def ctorScalarSizeExpressionZig (usize : Nat) (ssize : Nat) : String :=
  if usize == 0 then
    usizeLit ssize
  else if ssize == 0 then
    s!"@as(usize, @sizeOf(usize) * {usize})"
  else
    s!"@as(usize, @sizeOf(usize) * {usize} + {ssize})"

def offsetExpressionZig (i : Nat) (offset : Nat) : String :=
  if i > 0 then
    if offset > 0 then
      s!"@as(c_uint, @sizeOf(usize) * {i} + {offset})"
    else
      s!"@as(c_uint, @sizeOf(usize) * {i})"
  else
    cUIntLit offset

def renderBoxExpr (type : Expr) (value : String) : String :=
  match type with
  | ImpureType.uint8 | ImpureType.uint16 =>
      s!"lean_box(@as(usize, @intCast({value})))"
  | _ =>
      s!"{type.boxOpName}({value})"

def renderUnboxExpr (type : Expr) (value : String) : String :=
  match type with
  | ImpureType.uint8 =>
      s!"@as(u8, @truncate(lean_unbox({value})))"
  | ImpureType.uint16 =>
      s!"@as(u16, @truncate(lean_unbox({value})))"
  | _ =>
      s!"{type.unboxOpName}({value})"

def renderResetLines (binder : Name) (n : Nat) (fvarId : FVarId) : List String :=
  let lhs := zigIdent binder
  let target := zigIdent fvarId.name
  ["if (lean_is_exclusive(" ++ target ++ ")) {"] ++
    (List.range n).map (fun i => s!"  lean_ctor_release({target}, {cUIntLit i});") ++
    [s!"  {lhs} = {target};", "} else {", s!"  lean_dec_ref({target});",
      s!"  {lhs} = lean_box({usizeLit 0});", "}"]

def renderReuseLines (binder : Name) (fvarId : FVarId) (info : CtorInfo) (update : Bool)
    (args : Array (Arg .impure)) : List String :=
  let lhs := zigIdent binder
  let target := zigIdent fvarId.name
  let head :=
    ["if (lean_is_scalar(" ++ target ++ ") != 0) {",
      s!"  {lhs} = lean_alloc_ctor({cUIntLit info.cidx}, {cUIntLit info.size}, {ctorScalarSizeExpressionZig info.usize info.ssize});",
      "} else {", s!"  {lhs} = {target};"] ++
    (if update then [s!"  lean_ctor_set_tag({lhs}, @as(u8, {info.cidx}));"] else []) ++
    ["}"]
  head ++ (List.range args.size).map (fun i =>
    s!"lean_ctor_set({lhs}, {cUIntLit i}, {renderImpureArg args[i]!});")

def renderSsetLine (fvarId : FVarId) (i offset : Nat) (y : FVarId) (type : Expr) : String :=
  s!"{type.ssetOpName}({zigIdent fvarId.name}, {offsetExpressionZig i offset}, {zigIdent y.name});"

def renderCoreLetValueLines? (binder : Name) (type : Expr) (value : LetValue .impure) :
    Option (List String) :=
  let lhs := zigIdent binder
  let assign (rhs : String) := s!"{lhs} = {rhs};"
  match value with
  | .ctor info args =>
      if info.size == 0 && info.usize == 0 && info.ssize == 0 then
        some [assign s!"lean_box({usizeLit info.cidx})"]
      else
        some <|
          [assign s!"lean_alloc_ctor({cUIntLit info.cidx}, {cUIntLit info.size}, {ctorScalarSizeExpressionZig info.usize info.ssize})"] ++
          ((List.range args.size).map fun i =>
            let arg := args[i]!
            s!"lean_ctor_set({lhs}, {cUIntLit i}, {renderImpureArg arg});")
  | .reset n fvarId =>
      some <| renderResetLines binder n fvarId
  | .reuse fvarId info update args =>
      some <| renderReuseLines binder fvarId info update args
  | .oproj i fvarId =>
      some [assign s!"lean_ctor_get({zigIdent fvarId.name}, {cUIntLit i})"]
  | .uproj i fvarId =>
      some [assign s!"lean_ctor_get_usize({zigIdent fvarId.name}, {cUIntLit i})"]
  | .sproj n offset fvarId =>
      some [assign s!"{type.sprojOpName}({zigIdent fvarId.name}, {offsetExpressionZig n offset})"]
  | .box boxType fvarId =>
      some [assign <| renderBoxExpr boxType (zigIdent fvarId.name)]
  | .unbox fvarId =>
      some [assign <| renderUnboxExpr type (zigIdent fvarId.name)]
  | .isShared fvarId =>
      some [assign s!"@as(u8, @intFromBool(!lean_is_exclusive({zigIdent fvarId.name})))"]
  | .lit lit =>
      let rhs :=
        match lit with
        | .uint8 v => s!"@as(u8, {v})"
        | .uint16 v => s!"@as(u16, {v})"
        | .uint32 v => s!"@as(u32, {v})"
        | .uint64 v => s!"@as(u64, {v})"
        | .usize v => s!"@as(usize, {v})"
        | .nat v =>
            if v < UInt32.size then
              s!"lean_unsigned_to_nat(@as(c_uint, {v}))"
            else
              s!"lean_cstr_to_nat({quoteZigString (toString v)})"
        | .str v =>
            s!"lean_mk_string_unchecked({quoteZigString v}, {usizeLit v.utf8ByteSize}, {usizeLit v.length})"
      some [assign rhs]
  | .erased =>
      some [assign s!"lean_box({usizeLit 0})"]
  | _ => none

def toCallableZigName (fn : Name) : EmitM String := do
  let env ← getEnv
  return (getExternNameFor env `c fn).getD (← toZigSymbolName fn)

def renderGlobalRefRhs (type : Expr) (fn : Name) : EmitM String := do
  let env ← getEnv
  let callable ← toCallableZigName fn
  if isSimpleGroundDecl env fn then
    return callable
  else if isClosedTermName env fn then
    let initName ← toZigInitName fn
    let token := toOnceTokenName callable
    return s!"{closedTermReadOpName type}(&{callable}, &{token}, {initName})"
  else
    return callable

abbrev GroundEmitM := StateT Nat EmitM

partial def emitGroundDecl (decl : Decl .impure) : EmitM Unit := do
  let env ← getEnv
  let some ground := getSimpleGroundExpr env decl.name | unreachable!
  let baseName ← toZigSymbolName decl.name
  let valueName := (← compileGroundToValueNamed baseName (groundValueName baseName) ground |>.run 0).1
  emitLn s!"const {baseName}: LeanObj = {groundLeanObjLitOfValueName valueName};"
  unless isClosedTermName env decl.name do
    emitLn <| "comptime { @export(&" ++ baseName ++ ", .{ .name = \"" ++ baseName ++ "\" }); }"
  emitLn ""
where

  groundValueName (name : String) : String :=
    name ++ "_value"

  groundAuxValueName (rootName : String) (idx : Nat) : String :=
    groundValueName rootName ++ s!"_aux_{idx}"

  renderGroundArrayLit (xs : List String) : String :=
    if xs.isEmpty then ".{}" else ".{ " ++ String.intercalate ", " xs ++ " }"

  groundPtrExprOfValueName (name : String) : String :=
    s!"@as(*align(1) lean_object, @ptrCast(@constCast(&{name})))"

  groundLeanObjLitOfTagged (n : Nat) : String :=
    s!"@as(LeanObj, @ptrFromInt((@as(usize, {n}) << 1) | 1))"

  groundLeanObjLitOfValueName (name : String) : String :=
    s!"@as(LeanObj, {groundPtrExprOfValueName name})"

  groundSlotLitOfTagged (n : Nat) : String :=
    s!"((@as(usize, {n}) << 1) | 1)"

  groundSlotLitOfValueName (name : String) : String :=
    s!"@intFromPtr(@as(*const lean_object, @ptrCast(&{name})))"

  groundHeaderLit (csSz other tag : String) : String :=
    ".{ .m_rc = 0, .m_cs_sz = @as(u16, @intCast(" ++ csSz ++ ")), " ++
      ".m_other = @as(u8, @intCast(" ++ other ++ ")), " ++
      ".m_tag = @as(u8, @intCast(" ++ tag ++ ")) }"

  emitGroundConst (name type value : String) : GroundEmitM Unit := do
    emitLn s!"const {name}: {type} = {value};"

  findValueDecl (decl : Name) : GroundEmitM String := do
    let mut decl := decl
    while true do
      if let some (.reference ref) := getSimpleGroundExpr (← getEnv) decl then
        decl := ref
      else
        break
    return groundValueName (← toZigSymbolName decl)

  groundArgToLeanObjLit : SimpleGroundArg → GroundEmitM String
    | .tagged val => pure <| groundLeanObjLitOfTagged val
    | .reference decl => return groundLeanObjLitOfValueName (← findValueDecl decl)
    | .rawReference decl => pure <| groundLeanObjLitOfValueName decl

  groundArgToSlotLit : SimpleGroundArg → GroundEmitM String
    | .tagged val => pure <| groundSlotLitOfTagged val
    | .reference decl => return groundSlotLitOfValueName (← findValueDecl decl)
    | .rawReference decl => pure <| groundSlotLitOfValueName decl

  packGroundScalarBytes (scalarArgs : Array UInt8) : List String := Id.run do
    assert! scalarArgs.size % 8 == 0
    let chunks := scalarArgs.size / 8
    let mut packed := []
    for idx in [0:chunks] do
      let mut value : Nat := 0
      for off in [0:8] do
        let b := scalarArgs[idx * 8 + off]!.toNat
        value := value + b * (2 ^ (8 * off))
      packed := packed.concat s!"@as(usize, {value})"
    packed

  emitCtorValue (name : String) (cidx : Nat) (objArgs : Array SimpleGroundArg)
      (usizeArgs : Array UInt64) (scalarArgs : Array UInt8) : GroundEmitM Unit := do
    let objLits ← objArgs.toList.mapM groundArgToLeanObjLit
    let usizeLits := usizeArgs.toList.map (fun u => s!"@as(usize, {u.toNat})")
    let scalarLits := packGroundScalarBytes scalarArgs
    let type := "extern struct { m_header: lean_object, m_objs: [" ++ toString objArgs.size ++ "]LeanObj, m_usize: [" ++ toString usizeArgs.size ++ "]usize, m_scalars: [" ++ toString scalarLits.length ++ "]usize }"
    let header := groundHeaderLit
      ("@sizeOf(lean_ctor_object) + @sizeOf(usize) * " ++ toString objArgs.size ++
        " + " ++ ctorScalarSizeExpressionZig usizeArgs.size scalarArgs.size)
      (toString objArgs.size) (toString cidx)
    let value := ".{ .m_header = " ++ header ++
      ", .m_objs = " ++ renderGroundArrayLit objLits ++
      ", .m_usize = " ++ renderGroundArrayLit usizeLits ++
      ", .m_scalars = " ++ renderGroundArrayLit scalarLits ++ " }"
    emitGroundConst name type value

  emitStringValue (name : String) (data : String) : GroundEmitM Unit := do
    let bytes := data.toUTF8.data.push 0
    let byteLits := bytes.toList.map (fun b => s!"@as(u8, {b.toNat})")
    let type := "extern struct { m_header: lean_object, m_size: usize, m_capacity: usize, m_length: usize, m_data: [" ++ toString bytes.size ++ "]u8 }"
    let value := ".{ .m_header = " ++ groundHeaderLit "0" "0" "249" ++
      ", .m_size = " ++ usizeLit bytes.size ++
      ", .m_capacity = " ++ usizeLit bytes.size ++
      ", .m_length = " ++ usizeLit data.length ++
      ", .m_data = " ++ renderGroundArrayLit byteLits ++ " }"
    emitGroundConst name type value

  emitPapValue (name : String) (func : Name) (args : Array SimpleGroundArg) : GroundEmitM Unit := do
    let some sig ← getImpureSignature? func | unreachable!
    let objLits ← args.toList.mapM groundArgToLeanObjLit
    let callable ← toCallableZigName func
    let type := "extern struct { m_header: lean_object, m_fun: ?*anyopaque, m_arity: u16, m_num_fixed: u16, m_objs: [" ++ toString args.size ++ "]LeanObj }"
    let value := ".{ .m_header = " ++
      groundHeaderLit ("@sizeOf(lean_closure_object) + @sizeOf(LeanObj) * " ++ toString args.size) "0" "245" ++
      ", .m_fun = @as(?*anyopaque, @ptrCast(@constCast(&" ++ callable ++ ")))" ++
      ", .m_arity = @as(u16, @intCast(" ++ toString (runtimeParams sig.params).size ++ "))" ++
      ", .m_num_fixed = @as(u16, @intCast(" ++ toString args.size ++ "))" ++
      ", .m_objs = " ++ renderGroundArrayLit objLits ++ " }"
    emitGroundConst name type value

  emitArrayValue (name : String) (elems : Array SimpleGroundArg) : GroundEmitM Unit := do
    let elemLits ← elems.toList.mapM groundArgToLeanObjLit
    let type := "extern struct { m_header: lean_object, m_size: usize, m_capacity: usize, m_data: [" ++ toString elems.size ++ "]LeanObj }"
    let value := ".{ .m_header = " ++
      groundHeaderLit ("@sizeOf(lean_array_object) + @sizeOf(LeanObj) * " ++ toString elems.size) "0" "246" ++
      ", .m_size = " ++ usizeLit elems.size ++
      ", .m_capacity = " ++ usizeLit elems.size ++
      ", .m_data = " ++ renderGroundArrayLit elemLits ++ " }"
    emitGroundConst name type value

  emitByteArrayValue (name : String) (data : Array UInt8) : GroundEmitM Unit := do
    let byteLits := data.toList.map (fun b => s!"@as(u8, {b.toNat})")
    let type := "extern struct { m_header: lean_object, m_size: usize, m_capacity: usize, m_data: [" ++ toString data.size ++ "]u8 }"
    let value := ".{ .m_header = " ++
      groundHeaderLit ("@sizeOf(lean_sarray_object) + " ++ toString data.size) "1" "248" ++
      ", .m_size = " ++ usizeLit data.size ++
      ", .m_capacity = " ++ usizeLit data.size ++
      ", .m_data = " ++ renderGroundArrayLit byteLits ++ " }"
    emitGroundConst name type value

  compileGroundToValueNamed (rootName name : String) (e : SimpleGroundExpr) : GroundEmitM String := do
    match e with
    | .ctor cidx objArgs usizeArgs scalarArgs =>
        emitCtorValue name cidx objArgs usizeArgs scalarArgs
        return name
    | .string data =>
        emitStringValue name data
        return name
    | .pap func args =>
        emitPapValue name func args
        return name
    | .nameMkStr args =>
        assert! args.size > 0
        if args.size == 1 then
          let (ref, hash) := args[0]!
          emitCtorValue name 1 #[.tagged 0, .reference ref] #[] (uint64ToByteArrayLE hash)
          return name
        else
          let (ref, hash) := args.back!
          let idx ← modifyGet fun idx => (idx, idx + 1)
          let auxName := groundAuxValueName rootName idx
          discard <| compileGroundToValueNamed rootName auxName (.nameMkStr args.pop)
          emitCtorValue name 1 #[.rawReference auxName, .reference ref] #[] (uint64ToByteArrayLE hash)
          return name
    | .reference refDecl =>
        findValueDecl refDecl
    | .array elems =>
        emitArrayValue name elems
        return name
    | .byteArray data =>
        emitByteArrayValue name data
        return name

def renderFapLines (binder : Name) (type : Expr) (fn : Name) (args : Array (Arg .impure)) :
    EmitM (List String) := do
  let lhs := zigIdent binder
  let assign (rhs : String) := s!"{lhs} = {rhs};"
  let some sig ← getImpureSignature? fn
    | pure [s!"@panic(\"missing EmitZig signature for {fn}\");"]
  let args := runtimeArgs sig.params args
  match getExternAttrData? (← getEnv) fn |>.bind (getExternEntryFor · `c) with
  | some (.standard _ externName) =>
      pure [assign s!"{externName}({renderArgList args})"]
  | some (.inline _ pat) =>
      pure [assign (expandExternPattern pat (renderImpureArgs args))]
  | some .opaque | none =>
      if args.isEmpty then
        let env ← getEnv
        let callable ← toCallableZigName fn
        if let some localDecl := (← getLocalDecls).find? (·.name == fn) then
          if isSimpleGroundDecl env fn then
            pure [assign (← renderGlobalRefRhs type fn)]
          else if (runtimeParams localDecl.params).isEmpty then
            pure [assign s!"{callable}()"]
          else
            pure [assign s!"{callable}()"]
        else if (isStandardExternC? env fn).isSome then
          pure [assign s!"{callable}()"]
        else
          pure [assign (← renderGlobalRefRhs type fn)]
      else if args.size ≤ closureMaxArgs then
        let callable ← toCallableZigName fn
        pure [assign s!"{callable}({renderArgList args})"]
      else
        let callable ← toCallableZigName fn
        let fnVar := s!"{lhs}__fn"
        let argsVar := s!"{lhs}__args"
        pure [
          "var " ++ argsVar ++ " = [_]LeanObj{ " ++ renderArgList args ++ " };",
          s!"const {fnVar} = lean_alloc_closure(@ptrCast(&{callable}), {cUIntLit (runtimeParams sig.params).size}, {cUIntLit 0});",
          assign s!"lean_apply_n({fnVar}, {cUIntLit args.size}, &{argsVar})"
        ]
  | _ =>
      pure [s!"@panic(\"failed to emit extern application {fn}\");"]

def renderPapLines (binder : Name) (fn : Name) (args : Array (Arg .impure)) :
    EmitM (List String) := do
  let lhs := zigIdent binder
  let assign (rhs : String) := s!"{lhs} = {rhs};"
  let some sig ← getImpureSignature? fn
    | pure [s!"@panic(\"missing EmitZig signature for {fn}\");"]
  let callable ← toCallableZigName fn
  let args := runtimeArgs sig.params args
  pure <|
    [assign s!"lean_alloc_closure(@ptrCast(&{callable}), {cUIntLit (runtimeParams sig.params).size}, {cUIntLit args.size})"] ++
    ((List.range args.size).map fun i =>
      s!"lean_closure_set({lhs}, {cUIntLit i}, {renderImpureArg args[i]!});")

def renderFVarAppLines (binder : Name) (fvarId : FVarId) (args : Array (Arg .impure)) :
    List String :=
  let lhs := zigIdent binder
  let assign (rhs : String) := s!"{lhs} = {rhs};"
  if args.isEmpty then
    [assign <| zigIdent fvarId.name]
  else if args.size ≤ 4 then
    [assign s!"lean_apply_{args.size}({zigIdent fvarId.name}, {renderArgList args})"]
  else
    let argsVar := s!"{lhs}__args"
    ["var " ++ argsVar ++ " = [_]LeanObj{ " ++ renderArgList args ++ " };",
      assign s!"lean_apply_n({zigIdent fvarId.name}, {cUIntLit args.size}, &{argsVar})"]

def renderLetValueLines? (binder : Name) (type : Expr) (value : LetValue .impure) :
    EmitM (Option (List String)) := do
  match renderCoreLetValueLines? binder type value with
  | some lines => pure (some lines)
  | none =>
    match value with
    | .fap fn args => return some (← renderFapLines binder type fn args)
    | .pap fn args => return some (← renderPapLines binder fn args)
    | .fvar fvarId args => return some (renderFVarAppLines binder fvarId args)
    | _ => pure none

def isTailCall (code : Code .impure) : EmitM Bool :=
  match code with
  | .let { fvarId := fvarId, value := .fap declName _, .. } (.return fvarId') =>
      return fvarId == fvarId' && (← getCurrFn) == declName
  | _ => pure false

partial def containsTailCall : Code .impure → EmitM Bool
  | code@(.let _ k) => do
      if ← isTailCall code then pure true else containsTailCall k
  | .jp decl k => do
      let bodyHas ← containsTailCall decl.value
      let restHas ← containsTailCall k
      pure (bodyHas || restHas)
  | .inc _ _ _ _ k
  | .dec _ _ _ _ _ k
  | .del _ k | .setTag _ _ k | .oset _ _ _ k | .uset _ _ _ k
  | .sset _ _ _ _ _ k =>
      containsTailCall k
  | .cases cs => do
      let mut hasTail := false
      for alt in cs.alts do
        hasTail := hasTail || (← containsTailCall alt.getCode)
      pure hasTail
  | .jmp .. | .return .. | .unreach .. => pure false

partial def containsJmp : Code .impure → EmitM Bool
  | .let _ k => containsJmp k
  | .jp decl k => do
      let bodyHas ← containsJmp decl.value
      let restHas ← containsJmp k
      pure (bodyHas || restHas)
  | .inc _ _ _ _ k
  | .dec _ _ _ _ _ k
  | .del _ k | .setTag _ _ k | .oset _ _ _ k | .uset _ _ _ k
  | .sset _ _ _ _ _ k => containsJmp k
  | .cases cs => do
      let mut hasJmp := false
      for alt in cs.alts do
        hasJmp := hasJmp || (← containsJmp alt.getCode)
      pure hasJmp
  | .jmp .. => pure true
  | .return .. | .unreach .. => pure false

/-- Return true if `code` contains a jump to the join point `target`. -/
partial def codeContainsJmpTo (target : FVarId) : Code .impure → Bool
  | .let _ k => codeContainsJmpTo target k
  | .jp decl k => codeContainsJmpTo target decl.value || codeContainsJmpTo target k
  | .inc _ _ _ _ k
  | .dec _ _ _ _ _ k
  | .del _ k | .setTag _ _ k | .oset _ _ _ k | .uset _ _ _ k
  | .sset _ _ _ _ _ k => codeContainsJmpTo target k
  | .cases cs => cs.alts.any (codeContainsJmpTo target ·.getCode)
  | .jmp fvarId _ => fvarId == target
  | .return .. | .unreach .. => false

partial def collectCodeTypes (code : Code .impure) (acc : NameMap Expr := {}) : NameMap Expr :=
  match code with
  | .let decl k =>
      collectCodeTypes k (acc.insert decl.fvarId.name decl.type)
  | .jp decl k =>
      let acc := decl.params.foldl (init := acc) fun acc p => acc.insert p.fvarId.name p.type
      let acc := collectCodeTypes decl.value acc
      collectCodeTypes k acc
  | .inc _ _ _ _ k
  | .dec _ _ _ _ _ k
  | .del _ k | .setTag _ _ k | .oset _ _ _ k | .uset _ _ _ k
  | .sset _ _ _ _ _ k =>
      collectCodeTypes k acc
  | .cases cs =>
      cs.alts.foldl (init := acc) fun acc alt => collectCodeTypes alt.getCode acc
  | .jmp .. | .return .. | .unreach .. =>
      acc

partial def collectJoinDecls (code : Code .impure) (acc : NameMap (FunDecl .impure) := {}) :
    NameMap (FunDecl .impure) :=
  match code with
  | .jp decl k =>
      let acc := acc.insert decl.fvarId.name decl
      let acc := collectJoinDecls decl.value acc
      collectJoinDecls k acc
  | .inc _ _ _ _ k
  | .dec _ _ _ _ _ k
  | .del _ k | .setTag _ _ k | .oset _ _ _ k | .uset _ _ _ k
  | .sset _ _ _ _ _ k | .let _ k =>
      collectJoinDecls k acc
  | .cases cs =>
      cs.alts.foldl (init := acc) fun acc alt => collectJoinDecls alt.getCode acc
  | .jmp .. | .return .. | .unreach .. => acc

partial def collectJoinDeclOrder (code : Code .impure) (acc : Array (FunDecl .impure) := #[]) :
    Array (FunDecl .impure) :=
  match code with
  | .jp decl k =>
      let acc := acc.push decl
      let acc := collectJoinDeclOrder decl.value acc
      collectJoinDeclOrder k acc
  | .inc _ _ _ _ k
  | .dec _ _ _ _ _ k
  | .del _ k | .setTag _ _ k | .oset _ _ _ k | .uset _ _ _ k
  | .sset _ _ _ _ _ k | .let _ k =>
      collectJoinDeclOrder k acc
  | .cases cs =>
      cs.alts.foldl (init := acc) fun acc alt => collectJoinDeclOrder alt.getCode acc
  | .jmp .. | .return .. | .unreach .. => acc

def ensureHasDefault (alts : Array (Alt .impure)) : Array (Alt .impure) :=
  if alts.any (· matches .default ..) then
    alts
  else
    if alts.size < 2 then alts else alts.pop.push (.default alts.back!.getCode)

partial def emitVarDecls : Code .impure → EmitM Unit
  | .let decl k => do
      if ← isTailCall (.let decl k) then
        emitVarDecls k
      else
        emitLn s!"  var {zigIdent decl.fvarId.name}: {decl.type.toZigType} = undefined;"
        emitLn s!"  _ = &{zigIdent decl.fvarId.name};"
        emitVarDecls k
  | .jp decl k => do
      for p in runtimeParams decl.params do
        if ← codeUsesFVarRuntime p.fvarId decl.value then
          emitLn s!"  var {zigIdent p.fvarId.name}: {p.type.toZigType} = undefined;"
          emitLn s!"  _ = &{zigIdent p.fvarId.name};"
      emitVarDecls decl.value
      emitVarDecls k
  | .inc _ _ _ _ k
  | .dec _ _ _ _ _ k
  | .del _ k | .setTag _ _ k | .oset _ _ _ k | .uset _ _ _ k
  | .sset _ _ _ _ _ k => emitVarDecls k
  | .cases cs =>
      for alt in cs.alts do
        emitVarDecls alt.getCode
  | .jmp .. | .return .. | .unreach .. => pure ()

partial def supportsCodeSubset : Code .impure → EmitM Bool
  | .let decl k => do
      if ← isTailCall (.let decl k) then
        supportsCodeSubset k
      else
        match ← renderLetValueLines? decl.fvarId.name decl.type decl.value with
        | some _ => supportsCodeSubset k
        | none => pure false
  | .jp decl k => do
      let bodyOk ← supportsCodeSubset decl.value
      let restOk ← supportsCodeSubset k
      pure (bodyOk && restOk)
  | .inc _ _ _ _ k => supportsCodeSubset k
  | .dec _ _ _ _ _ k => supportsCodeSubset k
  | .del _ k | .setTag _ _ k | .oset _ _ _ k | .uset _ _ _ k | .sset _ _ _ _ _ k =>
      supportsCodeSubset k
  | .cases cs => do
      let mut ok := true
      for alt in cs.alts do
        ok := ok && (← supportsCodeSubset alt.getCode)
      pure ok
  | .jmp .. | .return .. | .unreach .. => pure true

def emitRenderedLet (binder : Name) (type : Expr) (lines : List String) (forceVar := false)
    (declare := true) : EmitM Unit := do
  let lhs := zigIdent binder
  let assignPrefix := s!"{lhs} = "
  match lines with
  | first :: rest =>
      if first.startsWith assignPrefix then
        if declare then
          let kw := if forceVar then "var" else "const"
          emitLn s!"  {kw} {lhs}: {type.toZigType} = {first.drop assignPrefix.length}"
        else
          emitLn s!"  {first}"
        for line in rest do
          emitLn s!"  {line}"
      else
        if declare then
          emitLn s!"  var {lhs}: {type.toZigType} = undefined;"
        for line in lines do
          emitLn s!"  {line}"
  | [] => pure ()

def emitTailCall (decl : LetDecl .impure) : EmitM Unit := do
  let .fap _ args := decl.value | unreachable!
  let ps ← getCurrParams
  let ps := runtimeParams ps
  let args := runtimeArgs (← getCurrParams) args
  let overwriteParam : Bool := Id.run do
    for h1 : i in [0:ps.size] do
      let p := ps[i]
      for h2 : j in [i+1:args.size] do
        match args[j] with
        | .fvar fvarId =>
            if p.fvarId == fvarId then
              return true
        | .erased => ()
    return false
  if overwriteParam then
    for h : i in [0:ps.size] do
      let p := ps[i]
      let arg := args[i]!
      let same :=
        match arg with
        | .fvar fvarId => p.fvarId == fvarId
        | .erased => false
      unless same do
        emitLn s!"  const _tmp_{i}: {p.type.toZigType} = {renderImpureArg arg};"
    for h : i in [0:ps.size] do
      let p := ps[i]
      let arg := args[i]!
      let same :=
        match arg with
        | .fvar fvarId => p.fvarId == fvarId
        | .erased => false
      unless same do
        emitLn s!"  {zigIdent p.fvarId.name} = _tmp_{i};"
  else
    for h : i in [0:ps.size] do
      let p := ps[i]
      let arg := args[i]!
      let same :=
        match arg with
        | .fvar fvarId => p.fvarId == fvarId
        | .erased => false
      unless same do
        emitLn s!"  {zigIdent p.fvarId.name} = {renderImpureArg arg};"
  for h : i in [0:ps.size] do
    let p := ps[i]
    let arg := args[i]!
    let same :=
      match arg with
      | .fvar fvarId => p.fvarId == fvarId
      | .erased => false
    unless same do
      emitLn s!"  {tailStateIdent p.fvarId.name} = {zigIdent p.fvarId.name};"
  if !(← read).joinStates.isEmpty then
    emitLn s!"  jp_state = {cUIntLit 0};"
  emitLn "  continue;"

partial def emitBasicBlock (code0 : Code .impure) : EmitM Unit := do
  let mut code := code0
  while true do
    match code with
    | .jp _decl k =>
        -- Join points are inlined at each `jmp` site; their declarations do not
        -- produce code on their own. Just emit the continuation.
        code := k
    | .let decl k =>
        if ← isTailCall (.let decl k) then
          emitTailCall decl
          break
        else
          match ← renderLetValueLines? decl.fvarId.name decl.type decl.value with
          | some lines =>
              emitRenderedLet decl.fvarId.name decl.type lines
                (forceVar := match decl.value with | .reset .. | .reuse .. => true | _ => false)
                (declare := !(← read).hoistLocals)
              if !codeUsesFVar decl.fvarId k then
                if (← read).hoistLocals then
                  emitLn s!"  _ = &{zigIdent decl.fvarId.name};"
                else
                  emitLn s!"  _ = {zigIdent decl.fvarId.name};"
              code := k
          | none =>
              emitLn "  @panic(\"EmitZig let-value emission not implemented yet\");"
              break
    | .inc fvarId n check persistent k =>
        unless persistent do
          let target := zigIdent fvarId.name
          if n == 1 then
            let incFn := if check then "lean_inc" else "lean_inc_ref"
            emitLn s!"  {incFn}({target});"
          else
            let incFn := if check then "lean_inc_n" else "lean_inc_ref_n"
            emitLn s!"  {incFn}({target}, {usizeLit n});"
        code := k
    | .dec fvarId n check persistent objs? k =>
        unless persistent do
          let target := zigIdent fvarId.name
          match objs? with
          | some objs =>
              if n != 1 then
                throwError "EmitZig does not support known-object dec with n != 1"
              emitLn s!"  lean_dec_ref_known({target}, {cUIntLit objs});"
          | none =>
              if n == 1 then
                let decFn := if check then "lean_dec" else "lean_dec_ref"
                emitLn s!"  {decFn}({target});"
              else
                let decFn := if check then "lean_dec_n" else "lean_dec_ref_n"
                emitLn s!"  {decFn}({target}, {usizeLit n});"
        code := k
    | .del fvarId k =>
        emitLn s!"  lean_del_object({zigIdent fvarId.name});"
        code := k
    | .setTag fvarId cidx k =>
        emitLn s!"  lean_ctor_set_tag({zigIdent fvarId.name}, @as(u8, {cidx}));"
        code := k
    | .oset fvarId i y k =>
        emitLn s!"  lean_ctor_set({zigIdent fvarId.name}, {cUIntLit i}, {renderImpureArg y});"
        code := k
    | .uset fvarId i y k =>
        emitLn s!"  lean_ctor_set_usize({zigIdent fvarId.name}, {cUIntLit i}, {zigIdent y.name});"
        code := k
    | .sset fvarId i offset y type k =>
        emitLn s!"  {renderSsetLine fvarId i offset y type}"
        code := k
    | .cases cs =>
        let shortIf? :=
          if h : cs.alts.size = 2 then
            have : 0 < cs.alts.size := by rw [h]; decide
            have : 1 < cs.alts.size := by rw [h]; decide
            match cs.alts[0] with
            | .ctorAlt info k => some (info.cidx, k, cs.alts[1].getCode)
            | _ => none
          else
            none
        let discrType ← getStoredType cs.discr
        let discrExpr :=
          if discrType.isObj then s!"lean_obj_tag({zigIdent cs.discr.name})" else zigIdent cs.discr.name
        match shortIf? with
        | some (tag, t, e) =>
            emitLn <| "  if (" ++ discrExpr ++ " == " ++ cUIntLit tag ++ ") {"
            emitBasicBlock t
            emitLn "  } else {"
            emitBasicBlock e
            emitLn "  }"
        | none =>
            emitLn <| "  switch (" ++ discrExpr ++ ") {"
            for alt in ensureHasDefault cs.alts do
              match alt with
              | .ctorAlt info k =>
                  emitLn <| "    " ++ cUIntLit info.cidx ++ " => {"
                  emitBasicBlock k
                  emitLn "    },"
              | .default k =>
                  emitLn "    else => {"
                  emitBasicBlock k
                  emitLn "    },"
              | .alt .. =>
                  emitLn "    else => {"
                  emitLn "      @panic(\"EmitZig pure cases not implemented yet\");"
                  emitLn "    },"
            emitLn "  }"
        break
    | .return fvarId =>
        emitLn s!"  return {zigIdent fvarId.name};"
        break
    | .jmp fvarId args =>
        let some jpDecl ← findStoredJoinDecl? fvarId | unreachable!
        if args.size != jpDecl.params.size then
          throwError "invalid jump"
        if let some jpState ← findStoredJoinState? fvarId then
          for h : i in [0:jpDecl.params.size] do
            let p := jpDecl.params[i]
            if p.type.isVoid || p.type.isErased then
              continue
            let arg := args[i]!
            emitLn s!"  {zigIdent p.fvarId.name} = {renderImpureArg arg};"
          emitLn s!"  jp_state = {cUIntLit jpState};"
          emitLn "  continue;"
        else if codeContainsJmpTo fvarId jpDecl.value then
          emitLn "  @panic(\"EmitZig recursive join point not implemented yet\");"
        else
          for h : i in [0:jpDecl.params.size] do
            let p := jpDecl.params[i]
            if p.type.isVoid || p.type.isErased then
              continue
            let arg := args[i]!
            emitLn s!"  {zigIdent p.fvarId.name} = {renderImpureArg arg};"
          emitBasicBlock jpDecl.value
        break
    | .unreach _ =>
        emitLn "  unreachable;"
        break

partial def emitJoinPointCases : Code .impure → EmitM Unit
  | .jp decl k => do
      let some jpState ← findStoredJoinState? decl.fvarId | unreachable!
      emitLn s!"      {cUIntLit jpState} => \{"
      emitBasicBlock decl.value
      emitLn "      },"
      emitJoinPointCases decl.value
      emitJoinPointCases k
  | .let _ k
  | .inc _ _ _ _ k
  | .dec _ _ _ _ _ k
  | .del _ k
  | .setTag _ _ k
  | .oset _ _ _ k
  | .uset _ _ _ k
  | .sset _ _ _ _ _ k =>
      emitJoinPointCases k
  | .cases cs =>
      for alt in cs.alts do
        emitJoinPointCases alt.getCode
  | .jmp .. | .return .. | .unreach .. => pure ()


def emitFileHeader : EmitM Unit := do
  let modName ← getModName
  emitLns [
    "// generated by emitzig",
    s!"// module: {modName}",
    "const std = @import(\"std\");",
    "const lean_object = extern struct {",
    "  m_rc: i32,",
    "  m_cs_sz: u16,",
    "  m_other: u8,",
    "  m_tag: u8,",
    "};",
    "const LeanObj = ?*align(1) lean_object;",
    "const lean_ctor_object = extern struct {",
    "  m_header: lean_object,",
    "  m_objs: [0]usize,",
    "};",
    "const lean_array_object = extern struct {",
    "  m_header: lean_object,",
    "  m_size: usize,",
    "  m_capacity: usize,",
    "  m_data: [0]LeanObj,",
    "};",
    "const lean_sarray_object = extern struct {",
    "  m_header: lean_object,",
    "  m_size: usize,",
    "  m_capacity: usize,",
    "  m_data: [0]u8,",
    "};",
    "const lean_string_object = extern struct {",
    "  m_header: lean_object,",
    "  m_size: usize,",
    "  m_capacity: usize,",
    "  m_length: usize,",
    "  m_data: [0]u8,",
    "};",
    "const lean_closure_object = extern struct {",
    "  m_header: lean_object,",
    "  m_fun: ?*anyopaque,",
    "  m_arity: u16,",
    "  m_num_fixed: u16,",
    "  m_objs: [0]LeanObj,",
    "};",
    "const MainFn = *const fn (c_int, [*c][*c]u8) callconv(.c) LeanObj;",
    ""
  ]
  let localNames ← getLocalRuntimeSymbolNames
  runtimeExternDeclsForModule localNames |>.forM emitLn
  emitLn ""
  InlineHelpers.inlineHelperDecls.forM emitLn
  emitLns [
    "",
    "fn lean_io_result_is_ok(r: LeanObj) bool {",
    "  return lean_obj_tag(r) == @as(c_uint, 0);",
    "}",
    "fn lean_io_result_get_value(r: LeanObj) LeanObj {",
    "  return lean_ctor_get(r, @as(c_uint, 0));",
    "}"
  ]
  emitLn ""

def emitFnDecls : EmitM Unit := do
  emitLn "// forward declarations"
  for sig in (← getOtherModuleDecls) do
    let env ← getEnv
    let name := (getExternNameFor env `c sig.name).getD (← toZigSymbolName sig.name)
    if InlineHelpers.isInlineHelperName name then
      continue
    if runtimeExternNames.contains name then
      continue
    if isGlobalVarSignature env sig then
      emitClosedTermDecl name sig.type
    else
      emitSignature name sig
  for decl in (← getLocalDecls) do
    let env ← getEnv
    if hasInitAttr env decl.name then
      continue
    if isSimpleGroundDecl env decl.name then
      continue
    match decl.value with
    | .extern .. => pure ()
    | _ => emitSignature (← toZigSymbolName decl.name) decl.toSignature
  emitLn ""

def emitDecl (decl : Decl .impure) : EmitM Unit := do
  let env ← getEnv
  if hasInitAttr env decl.name then
    return ()
  if isSimpleGroundDecl env decl.name then
    emitGroundDecl decl
    return ()
  match decl.value with
  | .extern .. => return ()
  | .code code =>
    let defName ← toZigDefName decl.name
    let exportName ← toZigSymbolName decl.name
    let fvarTypes :=
      collectCodeTypes code <|
        decl.params.foldl (init := ({} : NameMap Expr)) fun acc p => acc.insert p.fvarId.name p.type
    let joinDecls := collectJoinDecls code
    let joinOrder := collectJoinDeclOrder code
    let joinStates : NameMap Nat := Id.run do
      let mut states := ({} : NameMap Nat)
      for h : i in [0:joinOrder.size] do
        let jp := joinOrder[i]
        states := states.insert jp.fvarId.name (i + 1)
      return states
    emit s!"fn {defName}("
    emitParamList decl.params
    emitLn (s!") callconv(.c) {decl.type.toZigType} " ++ "{")
    let baseReaderCtx := fun ctx =>
      { ctx with currFn := decl.name, currParams := decl.params, fvarTypes, joinDecls, joinStates }
    let supported ← withReader baseReaderCtx do
      supportsCodeSubset code
    let tailRec ← withReader baseReaderCtx do containsTailCall code
    let hasJmp ← withReader baseReaderCtx do containsJmp code
    let readerCtx := fun ctx => { (baseReaderCtx ctx) with hoistLocals := hasJmp }
    let params := runtimeParams decl.params
    if supported then
      withReader readerCtx do
        for p in params do
          let mutated := tailRec && tailCallMutatesParam decl.name decl.params p.fvarId code
          let used := (← codeUsesFVarRuntime p.fvarId code) || mutated
          if used then
            let name := if tailRec then tailStateIdent p.fvarId.name else zigIdent p.fvarId.name
            let bindingKw := if tailRec && mutated then "var" else "const"
            emitLn s!"  {bindingKw} {name}: {p.type.toZigType} = {zigParamIdent p.fvarId.name};"
          else
            emitLn s!"  _ = {zigParamIdent p.fvarId.name};"
        if hasJmp then
          emitVarDecls code
        if hasJmp then
          emitLn s!"  var jp_state: c_uint = {cUIntLit 0};"
        if !params.isEmpty || hasJmp then
          emitLn ""
        if hasJmp then
          emitLn "  while (true) {"
          if tailRec then
            let usedParams ← params.filterM fun p => do
              let mutated := tailCallMutatesParam decl.name decl.params p.fvarId code
              let used ← codeUsesFVarRuntime p.fvarId code
              pure (used || mutated)
            for p in usedParams do
              let mutated := tailCallMutatesParam decl.name decl.params p.fvarId code
              let bindingKw := if mutated then "var" else "const"
              emitLn s!"  {bindingKw} {zigIdent p.fvarId.name}: {p.type.toZigType} = {tailStateIdent p.fvarId.name};"
            if !usedParams.isEmpty then
              emitLn ""
          emitLn "    switch (jp_state) {"
          emitLn s!"      {cUIntLit 0} => \{"
          emitBasicBlock code
          emitLn "      },"
          emitJoinPointCases code
          emitLn "      else => unreachable,"
          emitLn "    }"
          emitLn "  }"
        else if tailRec then
          emitLn "  while (true) {"
          let usedParams ← params.filterM fun p => do
            let mutated := tailCallMutatesParam decl.name decl.params p.fvarId code
            let used ← codeUsesFVarRuntime p.fvarId code
            pure (used || mutated)
          for p in usedParams do
            let mutated := tailCallMutatesParam decl.name decl.params p.fvarId code
            let bindingKw := if mutated then "var" else "const"
            emitLn s!"  {bindingKw} {zigIdent p.fvarId.name}: {p.type.toZigType} = {tailStateIdent p.fvarId.name};"
          if !usedParams.isEmpty then
            emitLn ""
          emitBasicBlock code
          emitLn "  }"
        else
          emitBasicBlock code
    else
      for p in runtimeParams decl.params do
        emitLn s!"  _ = {zigParamIdent p.fvarId.name};"
      emitLn "  @panic(\"EmitZig body emission not implemented yet\");"
    emitLn "}"
    emitLn <| "comptime { @export(&" ++ defName ++ ", .{ .name = \"" ++ exportName ++ "\" }); }"
    emitLn ""

def emitFns : EmitM Unit := do
  for decl in (← getLocalDecls) do
    emitDecl decl

def emitInitFn : EmitM Unit := do
  let imported ← importedInitFnNames
  imported.forM fun fn => emitLn s!"extern fn {fn}(builtin: u8) callconv(.c) LeanObj;"
  if !imported.isEmpty then
    emitLn ""
  let initName ← getModInitFn
  let defName := s!"{initName}__def"
  let initialized := s!"_G_{initName}_initialized"
  emitLn s!"var {initialized}: bool = false;"
  let builtinParam := if imported.isEmpty then "_: u8" else "builtin: u8"
  emitLn (s!"fn {defName}({builtinParam}) callconv(.c) LeanObj " ++ "{")
  emitLn s!"  if ({initialized}) return lean_io_result_mk_ok(lean_box(0));"
  emitLn s!"  {initialized} = true;"
  emitLn "  lean_initialize_runtime_module();"
  emitLn "  lean_initialize_thread();"
  for fn in imported do
    emitLn s!"  lean_dec_ref({fn}(builtin));"
  emitLn "  return lean_io_result_mk_ok(lean_box(0));"
  emitLn "}"
  emitLn <| "comptime { @export(&" ++ defName ++ ", .{ .name = \"" ++ initName ++ "\" }); }"
  emitLn ""

def emitMainFnIfNeeded : EmitM Unit := do
  let some decl ← findMainDecl? | return ()
  let mainFn ← toZigSymbolName decl.name
  let initFn ← getModInitFn
  let initDefFn := s!"{initFn}__def"
  let env ← getEnv
  if decl.params.size != 1 && decl.params.size != 2 then
    throwError "invalid main function, incorrect arity when generating code"
  let usesLeanAPI := usesModuleFrom env `Lean
  let retTy := env.find? decl.name |>.get!.type |>.getForallBody |>.appArg!
  let hasExitCode := retTy.isConstOf ``UInt32
  emitLns ["fn emitzig_run_main(argc: c_int, argv: [*c][*c]u8) callconv(.c) LeanObj {"]
  if decl.params.size == 2 then
    emitLns [
      "  var in = lean_box(@as(usize, 0));",
      "  var i = argc;",
      "  while (i > 1) {",
      "    i -= 1;",
      "    var n = lean_alloc_ctor(@as(c_uint, 1), @as(c_uint, 2), @as(usize, 0));",
      "    lean_ctor_set(n, @as(c_uint, 0), lean_mk_string(argv[i]));",
      "    lean_ctor_set(n, @as(c_uint, 1), in);",
      "    in = n;",
      "  }",
      s!"  return {mainFn}(in);"
    ]
  else
    emitLns ["  _ = argc;", "  _ = argv;", s!"  return {mainFn}();"]
  emitLns [
    "}",
    "pub fn main(argc: c_int, argv0: [*c][*c]u8) callconv(.c) c_int {",
    "  const argv = lean_setup_args(argc, argv0);",
    if usesLeanAPI then "  lean_initialize();" else "  lean_initialize_runtime_module();",
    "  var res: LeanObj = " ++ initDefFn ++ "(@as(u8, 1));",
    "  lean_io_mark_end_initialization();",
    "  if (lean_io_result_is_ok(res)) {",
    "    lean_dec_ref(res);",
    "    lean_init_task_manager();",
    "    res = lean_run_main(emitzig_run_main, argc, argv);",
    "  }",
    "  lean_finalize_task_manager();",
    "  if (lean_io_result_is_ok(res)) {",
    "    const ret: c_int = " ++ if hasExitCode then "@as(c_int, @intCast(lean_unbox_uint32(lean_io_result_get_value(res))));" else "0;",
    "    lean_dec_ref(res);",
    "    return ret;",
    "  }",
    "  lean_io_result_show_error(res);",
    "  lean_dec_ref(res);",
    "  return 1;",
    "}",
    "comptime {",
    "  @export(\u0026main, .{ .name = \"main\" });",
    "}"
  ]
  emitLn ""
where
  findMainDecl? : EmitM (Option (Decl .impure)) := do
    if let some decl := (← getLocalDecls).find? (·.name == `main) then
      return some decl
    for decl in ← getLocalDecls do
      let symbol ← toZigSymbolName decl.name
      if symbol == leanMainFn || symbol.endsWith "__main" then
        return some decl
    return none

def emitFile : EmitM Unit := do
  emitFileHeader
  emitFnDecls
  emitFns
  emitInitFn
  emitMainFnIfNeeded

def emitZigForDecls (modName : Name) (decls : Array Name) : CoreM String := do
  let (localDecls, otherModuleDecls) ← collectUsedDecls decls
  let indexMap := getImpureDeclIndices (← getEnv) decls
  let localDecls := localDecls.qsort fun l r => indexMap[l.name]! < indexMap[r.name]!
  let (_, state) ← emitFile.run { localDecls, otherModuleDecls, modName } |>.run {}
  return String.fromUTF8! state.buf

public def emitZig (modName : Name) : CoreM String := do
  emitZigForDecls modName (← getLocalImpureDecls)

end Lean.Compiler.LCNF

namespace EmitZig

public def renderCoreLetValueLines? (binder : Name) (type : Expr) (value : LetValue .impure) : Option (List String) := Lean.Compiler.LCNF.renderCoreLetValueLines? binder type value
public def renderSsetLine (fvarId : FVarId) (i offset : Nat) (y : FVarId) (type : Expr) : String := Lean.Compiler.LCNF.renderSsetLine fvarId i offset y type
public def emitZig (modName : Name) : CoreM String := Lean.Compiler.LCNF.emitZig modName

end EmitZig
