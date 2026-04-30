/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.EmitUtil
import Lean.Compiler.NameMangling
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.ExportAttr
import Lean.Compiler.ModPkgExt
import Lean.Compiler.LCNF.SimpleGroundExpr
import Lean.Compiler.ClosedTermCache
import Lean.Runtime
import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.InitAttr
import Init.Omega
import Init.While
import Lean.Compiler.LCNF.SimpCase
import Lean.Compiler.LCNF.PrettyPrinter

namespace Lean.Compiler.LCNF

def leanMainFn := "_lean_main"

namespace ImpureType

def Lean.Expr.toCType : Expr → String
  | float => "double"
  | float32 => "float"
  | uint8 => "uint8_t"
  | uint16 => "uint16_t"
  | uint32 => "uint32_t"
  | uint64 => "uint64_t"
  | usize => "size_t"
  | object => "lean_object*"
  | tagged => "lean_object*"
  | tobject => "lean_object*"
  | erased => "lean_object*"
  | void => "lean_object*"
  | _ => unreachable!

def Lean.Expr.unboxOpName (t : Expr) : String :=
  match t with
  | usize => "lean_unbox_usize"
  | uint32 => "lean_unbox_uint32"
  | uint64 => "lean_unbox_uint64"
  | float => "lean_unbox_float"
  | float32 => "lean_unbox_float32"
  | _ => "lean_unbox"

def Lean.Expr.boxOpName (t : Expr) : String :=
  match t with
  | usize => "lean_box_usize"
  | uint32 => "lean_box_uint32"
  | uint64 => "lean_box_uint64"
  | float => "lean_box_float"
  | float32 => "lean_box_float32"
  | _ => "lean_box"

def Lean.Expr.sprojOpName (t : Expr) : String :=
  match t with
  | float => "lean_ctor_get_float"
  | float32 => "lean_ctor_get_float32"
  | uint8 => "lean_ctor_get_uint8"
  | uint16 => "lean_ctor_get_uint16"
  | uint32 => "lean_ctor_get_uint32"
  | uint64 => "lean_ctor_get_uint64"
  | _ => unreachable!

def Lean.Expr.ssetOpName (t : Expr) : String :=
  match t with
  | float => "lean_ctor_set_float"
  | float32 => "lean_ctor_set_float32"
  | uint8 => "lean_ctor_set_uint8"
  | uint16 => "lean_ctor_set_uint16"
  | uint32 => "lean_ctor_set_uint32"
  | uint64 => "lean_ctor_set_uint64"
  | _ => unreachable!

def Lean.Expr.closedTermReadOpName (t : Expr) : String :=
  match t with
  | float => "lean_float_once"
  | float32 => "lean_float32_once"
  | uint8 => "lean_uint8_once"
  | uint16 => "lean_uint16_once"
  | uint32 => "lean_uint32_once"
  | uint64 => "lean_uint64_once"
  | usize => "lean_usize_once"
  | object | tobject | tagged | void => "lean_obj_once"
  | _ => unreachable!

end ImpureType

open ImpureType

structure Context where
  /--
  Declarations from the current module in topologically sorted order.
  -/
  localDecls : Array (Decl .impure)
  /--
  Signatures of declarations from other modules.
  -/
  otherModuleDecls : Array (Signature .impure)
  /--
  The name of the current module
  -/
  modName : Name
  /--
  The function that is currently being emitted.
  -/
  currFn : Name := default
  /--
  The parameters of the function that is currently being emitted.
  -/
  currParams : Array (Param .impure) := #[]

structure State where
  buf : String := ""
  varMangleCache : Std.HashMap Name String := {}
  funMangleCache : Std.HashMap Name String := {}
  funInitMangleCache : Std.HashMap Name String := {}

abbrev EmitM := ReaderT Context StateRefT State CompilerM

@[inline] def getModName : EmitM Name := return (← read).modName

@[inline] def getModInitFn (phases : IRPhases) : EmitM String := do
  let pkg? := (← getEnv).getModulePackage?
  return mkModuleInitializationFunctionName (phases := phases) (← getModName) pkg?

@[inline] def getCurrFn : EmitM Name := return (← read).currFn

@[inline] def getCurrParams : EmitM (Array (Param .impure)) := return (← read).currParams

@[inline] def getLocalDecls : EmitM (Array (Decl .impure)) := return (← read).localDecls

@[inline] def getOtherModuleDecls : EmitM (Array (Signature .impure)) :=
  return (← read).otherModuleDecls

class EmitToString (α : Type) where
  toEmitString : α → EmitM String

instance (priority := low) [ToString α] : EmitToString α where
  toEmitString x := return toString x

instance : EmitToString Name where
  toEmitString v := do
    modifyGet fun s =>
      if let some mangled := s.varMangleCache[v]? then
        (mangled, s)
      else
        let mangled := v.mangle (pre := "v_")
        (mangled, { s with varMangleCache := s.varMangleCache.insert v mangled })

instance : EmitToString FVarId where
  toEmitString fvarId := do EmitToString.toEmitString (← getBinderName fvarId)

def Arg.toCString (a : Arg .impure) : EmitM String := do
  match a with
  | .fvar fvarId => EmitToString.toEmitString fvarId
  | .erased => return "lean_box(0)"

instance : EmitToString (Arg .impure) where
  toEmitString a := a.toCString


@[inline] def emit [EmitToString α] (a : α) : EmitM Unit := do
  let str ← EmitToString.toEmitString a
  modify fun out => { out with buf := out.buf ++ str }

@[inline] def emitLn [EmitToString α] (a : α) : EmitM Unit := do
  emit a; emit "\n"

@[inline]
def emitCApp1 {α : Type} [EmitToString α] (fn : String) (arg : α) : EmitM Unit := do
  emit fn; emit "("; emit arg; emit ")"

@[inline]
def emitCApp2 {α β : Type} [EmitToString α] [EmitToString β] (fn : String) (arg1 : α) (arg2 : β) :
    EmitM Unit := do
  emit fn; emit "("; emit arg1; emit ", "; emit arg2; emit ")"

@[inline]
def emitCApp3 {α β γ : Type} [EmitToString α] [EmitToString β] [EmitToString γ] (fn : String)
    (arg1 : α) (arg2 : β) (arg3 : γ) : EmitM Unit := do
  emit fn; emit "("; emit arg1; emit ", "; emit arg2; emit ", "; emit arg3; emit ")"

def toStringArgs (ys : Array (Arg .impure)) : EmitM (List String) :=
  ys.toList.mapM (·.toCString)

def emitArgs (args : Array (Arg .impure)) : EmitM Unit := do
  for h : i in 0...args.size do
    if i > 0 then emit ", "
    emit args[i]

def emitLns [EmitToString α] (as : List α) : EmitM Unit :=
  as.forM fun a => emitLn a

@[inline] def withEmitBlock (x : EmitM α) : EmitM α := do
  emitLn "{"
  let ret ← x
  emitLn "}"
  return ret

def toDigit (c : Nat) : String :=
  String.singleton c.digitChar

def quoteString (s : String) : String :=
  let q := "\"";
  let q := s.foldl
    (fun q c => q ++
      if c == '\n' then "\\n"
      else if c == '\r' then "\\r"
      else if c == '\t' then "\\t"
      else if c == '\\' then "\\\\"
      else if c == '\"' then "\\\""
      else if c == '?' then "\\?" -- avoid trigraphs
      else if c.toNat <= 31 then
        -- Use octal escapes instead of hex escapes because C hex escapes are
        -- greedy: "\x01abc" would be parsed as the single escape \x01abc rather
        -- than \x01 followed by "abc".  Octal escapes consume at most 3 digits.
        let n := c.toNat
        "\\" ++ toDigit (n / 64) ++ toDigit ((n / 8) % 8) ++ toDigit (n % 8)
      -- TODO(Leo): we should use `\unnnn` for escaping unicode characters.
      else String.singleton c)
    q;
  q ++ "\""

def throwInvalidExportName (n : Name) : EmitM α :=
  throwError s!"invalid export name '{n}'"

def toCName (n : Name) : EmitM String := do
  if let some cached := (← get).funMangleCache[n]? then
    return cached
  let mangled ← go
  modify fun s => { s with funMangleCache := s.funMangleCache.insert n mangled }
  return mangled
where
  go : EmitM String := do
    let env ← getEnv
    -- TODO: we should support simple export names only
    match getExportNameFor? env n with
    | some (.str .anonymous s) => return s
    | some _                   => throwInvalidExportName n
    | none                     => return if n == `main then leanMainFn else getSymbolStem env n

def emitCName (n : Name) : EmitM Unit :=
  toCName n >>= emit

def toCInitName (n : Name) : EmitM String := do
  if let some cached := (← get).funInitMangleCache[n]? then
    return cached
  let mangled ← go
  modify fun s => { s with funInitMangleCache := s.funInitMangleCache.insert n mangled }
  return mangled
where
  go : EmitM String := do
    let env ← getEnv;
    -- TODO: we should support simple export names only
    match getExportNameFor? env n with
    | some (.str .anonymous s) => return "_init_" ++ s
    | some _                   => throwInvalidExportName n
    | none                     => return "_init_" ++ getSymbolStem env n

def emitCInitName (n : Name) : EmitM Unit :=
  toCInitName n >>= emit

def emitFileHeader : EmitM Unit := do
  let env ← getEnv
  let modName ← getModName
  emitLn "// Lean compiler output"
  emitLn s!"// Module: {modName}"
  emit "// Imports:"
  env.imports.forM fun m => emit (" " ++ toString m)
  emitLn ""
  emitLn "#include <lean/lean.h>"
  emitLns [
    "#if defined(__clang__)",
    "#pragma clang diagnostic ignored \"-Wunused-parameter\"",
    "#pragma clang diagnostic ignored \"-Wunused-label\"",
    "#elif defined(__GNUC__) && !defined(__CLANG__)",
    "#pragma GCC diagnostic ignored \"-Wunused-parameter\"",
    "#pragma GCC diagnostic ignored \"-Wunused-label\"",
    "#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"",
    "#endif",
    "#ifdef __cplusplus",
    "extern \"C\" {",
    "#endif"
  ]

def ctorScalarSizeExpression (usize : Nat) (ssize : Nat) : String :=
  if usize == 0 then
    s!"{ssize}"
  else if ssize == 0 then
    s!"sizeof(size_t)*{usize}"
  else
    s!"sizeof(size_t)*{usize} + {ssize}"

structure GroundState where
  auxCounter : Nat := 0

abbrev GroundM := StateRefT GroundState EmitM

partial def emitGroundDecl (decl : Decl .impure) (cppBaseName : String) : EmitM Unit := do
  let some ground := getSimpleGroundExpr (← getEnv) decl.name | unreachable!
  discard <| compileGround ground |>.run {}
where
  compileGround (e : SimpleGroundExpr) : GroundM Unit := do
    let valueName ← compileGroundToValue e
    let declPrefix := if isClosedTermName (← getEnv) decl.name then "static" else "LEAN_EXPORT"
    emitLn <| s!"{declPrefix} const lean_object* {cppBaseName} = (const lean_object*)&{valueName};"

  compileGroundToValue (e : SimpleGroundExpr) : GroundM String := do
    match e with
    | .ctor cidx objArgs usizeArgs scalarArgs =>
      let val ← compileCtor cidx objArgs usizeArgs scalarArgs
      mkValueCLit "lean_ctor_object" val
    | .string data =>
      let leanStringTag := 249
      let header := mkHeader 0 0 leanStringTag
      let size := data.utf8ByteSize + 1 -- null byte
      let length := data.length
      let data : String := quoteString data
      mkValueCLit
        "lean_string_object"
        s!"\{.m_header = {header}, .m_size = {size}, .m_capacity = {size}, .m_length = {length}, .m_data = {data}}"
    | .pap func args =>
      let numFixed := args.size
      let leanClosureTag := 245
      let header := mkHeader s!"sizeof(lean_closure_object) + sizeof(void*)*{numFixed}" 0 leanClosureTag
      let funPtr := s!"(void*){← toCName func}"
      let arity := (← getImpureSignature? func).get!.params.size
      let args ← args.mapM groundArgToCLit
      let argArray := String.intercalate "," args.toList
      mkValueCLit
        "lean_closure_object"
        s!"\{.m_header = {header}, .m_fun = {funPtr}, .m_arity = {arity}, .m_num_fixed = {numFixed}, .m_objs = \{{argArray}} }"
    | .nameMkStr args =>
      let obj ← groundNameMkStrToCLit args
      mkValueCLit "lean_ctor_object" obj
    | .array elems =>
      let leanArrayTag := 246
      let header := mkHeader s!"sizeof(lean_array_object) + sizeof(void*)*{elems.size}" 0 leanArrayTag
      let elemLits ← elems.mapM groundArgToCLit
      let dataArray := String.intercalate "," elemLits.toList
      mkValueCLit
        "lean_array_object"
        s!"\{.m_header = {header}, .m_size = {elems.size}, .m_capacity = {elems.size}, .m_data = \{{dataArray}}}"
    | .byteArray data =>
      let leanScalarArrayTag := 248
      let elemSize : Nat := 1
      let header := mkHeader s!"sizeof(lean_sarray_object) + {data.size}" elemSize leanScalarArrayTag
      let dataLits := data.map toString
      let dataArray := String.intercalate "," dataLits.toList
      mkValueCLit
        "lean_sarray_object"
        s!"\{.m_header = {header}, .m_size = {data.size}, .m_capacity = {data.size}, .m_data = \{{dataArray}}}"
    | .reference refDecl => findValueDecl refDecl

  mkValueName (name : String) : String :=
    name ++ "_value"

  mkAuxValueName (name : String) (idx : Nat) : String :=
    mkValueName name ++ s!"_aux_{idx}"

  mkAuxDecl (type value : String) : GroundM String := do
    let idx ← modifyGet fun s => (s.auxCounter, { s with auxCounter := s.auxCounter + 1 })
    let name := mkAuxValueName cppBaseName idx
    emitLn <| s!"static const {type} {name} = {value};"
    return name

  mkValueCLit (type value : String) : GroundM String := do
    let valueName := mkValueName cppBaseName
    emitLn <| s!"static const {type} {valueName} = {value};"
    return valueName

  groundNameMkStrToCLit (args : Array (Name × UInt64)) : GroundM String := do
    assert! args.size > 0
    if h : args.size = 1 then
      let (ref, hash) := args[0]
      let hash := uint64ToByteArrayLE hash
      compileCtor 1 #[.tagged 0, .reference ref] #[] hash
    else
      let (ref, hash) := args.back!
      let args := args.pop
      let lit ← groundNameMkStrToCLit args
      let auxName ← mkAuxDecl "lean_ctor_object" lit
      let hash := uint64ToByteArrayLE hash
      compileCtor 1 #[.rawReference auxName, .reference ref] #[] hash

  groundArgToCLit (a : SimpleGroundArg) : GroundM String := do
    match a with
    | .tagged val => return s!"((lean_object*)(((size_t)({val}) << 1) | 1))"
    | .reference decl =>  return s!"((lean_object*)&{← findValueDecl decl})"
    | .rawReference decl => return s!"((lean_object*)&{decl})"

  findValueDecl (decl : Name) : GroundM String := do
    let mut decl := decl
    while true do
      if let some (.reference ref) := getSimpleGroundExpr (← getEnv) decl then
        decl := ref
      else
        break
    return mkValueName (← toCName decl)

  compileCtor (cidx : Nat) (objArgs : Array SimpleGroundArg) (usizeArgs : Array UInt64)
      (scalarArgs : Array UInt8) : GroundM String := do
    let header := mkCtorHeader objArgs.size usizeArgs.size scalarArgs.size cidx
    let objArgs ← objArgs.mapM groundArgToCLit
    let usizeArgs : Array String := usizeArgs.map fun val => s!"(lean_object*)(size_t)({val}ULL)"
    assert! scalarArgs.size % 8 == 0
    let scalarArgs : Array String := Id.run do
      let chunks := scalarArgs.size / 8
      let mut packed := Array.emptyWithCapacity chunks
      for h : idx in 0...chunks do
        have : idx * 8 + 7 < scalarArgs.size := by
          have : idx < scalarArgs.size / 8 := Std.Rco.lt_upper_of_mem h
          omega
        let b1 := scalarArgs[idx * 8]
        let b2 := scalarArgs[idx * 8 + 1]
        let b3 := scalarArgs[idx * 8 + 2]
        let b4 := scalarArgs[idx * 8 + 3]
        let b5 := scalarArgs[idx * 8 + 4]
        let b6 := scalarArgs[idx * 8 + 5]
        let b7 := scalarArgs[idx * 8 + 6]
        let b8 := scalarArgs[idx * 8 + 7]
        let lit := s!"LEAN_SCALAR_PTR_LITERAL({b1}, {b2}, {b3}, {b4}, {b5}, {b6}, {b7}, {b8})"
        packed := packed.push lit
      return packed
    let argArray := String.intercalate "," (objArgs ++ usizeArgs ++ scalarArgs).toList
    return s!"\{.m_header = {header}, .m_objs = \{{argArray}}}"

  mkCtorHeader (numObjs : Nat) (usize : Nat) (ssize : Nat) (tag : Nat) : String :=
    let size := s!"sizeof(lean_ctor_object) + sizeof(void*)*{numObjs} + {ctorScalarSizeExpression usize ssize}"
    mkHeader size numObjs tag

  mkHeader {α : Type} [ToString α] (csSz : α) (other : Nat) (tag : Nat) : String :=
    s!"\{.m_rc = 0, .m_cs_sz = {csSz}, .m_other = {other}, .m_tag = {tag}}"

def toOnceTokenName (cppBaseName : String) : String :=
  s!"{cppBaseName}_once"

@[inline]
def paramsWithoutVoid (ps : Array (Param .impure)) :=
  ps.filter (!·.type.isVoid)

@[inline]
def paramsWithoutErased (ps : Array (Param .impure)) :=
  ps.filter (!·.type.isErased)

def emitFnDecls : EmitM Unit := do
  (← getOtherModuleDecls).forM fun sig => do
    match getExternNameFor (← getEnv) `c sig.name with
    | some externName => emitExternDecl sig externName
    | none => emitFnDeclStandard sig true
  (← getLocalDecls).forM fun decl => do
    match getExternNameFor (← getEnv) `c decl.name with
    | some externName => emitExternDecl decl.toSignature externName
    | none => emitFnDecl decl false
where
  emitExternDecl (sig : Signature .impure) (externName : String) : EmitM Unit := do
    let env ← getEnv
    let extC := isExternC env sig.name
    emitFnDeclAux sig externName extC

  emitFnDecl (decl : Decl .impure) (isExternal : Bool) : EmitM Unit := do
    let env ← getEnv
    let cppBaseName ← toCName decl.name
    if isSimpleGroundDecl env decl.name then
      emitGroundDecl decl cppBaseName
    else if isClosedTermName env decl.name then
      emitFnDeclClosed decl cppBaseName
    else
      emitFnDeclStandard decl.toSignature isExternal

  emitFnDeclClosed (decl : Decl .impure) (cppBaseName : String) : EmitM Unit := do
    emitLn s!"static lean_once_cell_t {toOnceTokenName cppBaseName} = LEAN_ONCE_CELL_INITIALIZER;"
    emitLn s!"static {decl.type.toCType} {cppBaseName};"

  emitFnDeclStandard (sig : Signature .impure) (isExternal : Bool) : EmitM Unit := do
    let env ← getEnv
    let cppBaseName ← toCName sig.name
    emitFnDeclAux sig cppBaseName isExternal

  emitFnDeclAux (sig : Signature .impure) (cppBaseName : String) (isExternal : Bool) :
      EmitM Unit := do
    let ps := sig.params
    let env ← getEnv

    if ps.isEmpty then
      if isExternal then
        emit "extern "
      else
        emit "LEAN_EXPORT "
    else if !isExternal then
      emit "LEAN_EXPORT "
    emit <| sig.type.toCType ++ " " ++ cppBaseName
    unless ps.isEmpty do
      emit "("
      -- We omit void parameters, note that they are guaranteed not to occur in boxed functions
      let ps := paramsWithoutVoid ps
      -- We omit erased parameters for extern constants
      let ps := if isExternC env sig.name then paramsWithoutErased ps else ps
      if ps.size > closureMaxArgs && isBoxedName sig.name then
        emit "lean_object**"
      else
        ps.size.forM fun i _ => do
          if i > 0 then emit ", "
          emit ps[i].type.toCType
      emit ")"
    emitLn ";"

def offsetExpression (i : Nat) (offset : Nat) : String :=
  if i > 0 then
    if offset > 0 then
      s!"sizeof(void*)*{i} + {offset}"
    else
      s!"sizeof(void*)*{i}"
  else
    s!"{offset}"

def isTailCall (code : Code .impure) : EmitM Bool  :=
  match code with
  | .let { fvarId := fvarId, value := .fap declName _, .. } (.return fvarId') =>
    return fvarId == fvarId' && (← getCurrFn) == declName
  | _ => return false

def declareVars (code : Code .impure) : EmitM Bool :=
  go code false
where
  go (code : Code .impure) (didChange : Bool) : EmitM Bool := do
    match code with
    | .let decl k =>
      if ← isTailCall code then
        return didChange
      else
        declareVar decl.binderName decl.type
        go k true
    | .jp decl k =>
      declareParams decl.params
      go k (didChange || !decl.params.isEmpty)
    | .del (k := k) .. | .dec (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
    | .sset (k := k) .. | .uset (k := k) .. | .oset (k := k) .. => go k didChange
    | .cases .. | .return .. | .jmp .. | .unreach .. => return didChange


  declareVar (binderName : Name) (type : Expr) : EmitM Unit := do
    emit type.toCType; emit " "; emit binderName; emit "; "

  declareParams (ps : Array (Param .impure)) : EmitM Unit := do
    ps.forM fun p => declareVar p.binderName p.type

def emitLetDecl (decl : LetDecl .impure) : EmitM Unit := do
  match decl.value with
  | .ctor info args => emitCtor info args
  | .reset n fvarId => emitReset n fvarId
  | .reuse fvarId info update args => emitReuse fvarId info update args
  | .oproj i fvarId => emitOproj i fvarId
  | .uproj i fvarId => emitUproj i fvarId
  | .sproj n offset fvarId => emitSproj n offset fvarId
  | .fap fn args => emitFap fn args
  | .pap fn args => emitPap fn args
  | .fvar fvarId args => emitAp fvarId args
  | .box ty fvarId => emitBox ty fvarId
  | .unbox fvarId => emitUnbox fvarId
  | .isShared fvarId => emitIsShared fvarId
  | .lit v => emitLit v
  | .erased => emitErased
where
  emitAllocCtor (info : CtorInfo) : EmitM Unit :=
    emitCApp3 "lean_alloc_ctor" info.cidx info.size (ctorScalarSizeExpression info.usize info.ssize)

  emitCtorSetArgs (targetId : FVarId) (args : Array (Arg .impure)) : EmitM Unit := do
    for h : i in 0...args.size do
      let arg := args[i]
      emitCApp3 "lean_ctor_set" targetId i arg; emitLn ";"

  emitCtor (info : CtorInfo) (args : Array (Arg .impure)) : EmitM Unit := do
    if info.size == 0 && info.usize == 0 && info.ssize == 0 then do
      withEmitAssignment do emitCApp1 "lean_box" info.cidx
    else do
      withEmitAssignment do emitAllocCtor info
      emitCtorSetArgs decl.fvarId args

  emitReset (n : Nat) (fvarId : FVarId) : EmitM Unit := do
    emit "if("; emitCApp1 "lean_is_exclusive" fvarId; emit ")"
    withEmitBlock do
      for i in 0...n do
        emitCApp2 "lean_ctor_release" fvarId i; emitLn ";"
      withEmitAssignment do emit fvarId
    emit "else"
    withEmitBlock do
      emitCApp1 "lean_dec_ref" fvarId; emitLn ";"
      withEmitAssignment do emit "lean_box(0)"

  emitReuse (fvarId : FVarId) (info : CtorInfo) (update : Bool) (args : Array (Arg .impure)) :
      EmitM Unit := do
    emit "if("; emitCApp1 "lean_is_scalar" fvarId; emit ")"
    withEmitBlock do
      withEmitAssignment do emitAllocCtor info
    emit "else"
    withEmitBlock do
      withEmitAssignment do emit fvarId
      if update then
        emitCApp2 "lean_ctor_set_tag" decl.fvarId info.cidx; emitLn ";"
    emitCtorSetArgs decl.fvarId args

  emitOproj (i : Nat) (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emitCApp2 "lean_ctor_get" fvarId i

  emitUproj (i : Nat) (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emitCApp2 "lean_ctor_get_usize" fvarId i

  emitSproj (n : Nat) (offset : Nat) (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emitCApp2 decl.type.sprojOpName fvarId (offsetExpression n offset)

  emitLeanFunReference (ty : Expr) (f : Name) : EmitM Unit := do
    let env ← getEnv
    if isSimpleGroundDecl env f then
      emit s!"((lean_object*)({← toCName f}))"
    else if isClosedTermName env f then
      let cname ← toCName f
      let cnameRef := s!"&{cname}"
      let tokenRef := s!"&{toOnceTokenName cname}"
      let initName ← toCInitName f
      emitCApp3 ty.closedTermReadOpName cnameRef tokenRef initName
    else
      emitCName f

  emitFap (fn : Name) (args : Array (Arg .impure)) : EmitM Unit := do
    let some sig ← getImpureSignature? fn | unreachable!
    let ps := sig.params
    withEmitAssignment do
      match getExternAttrData? (← getEnv) fn |>.bind (getExternEntryFor · `c) with
      | some (.standard _ fn) =>
        let (_, args) :=
          ps.zip args
            |>.filter (fun (p, _) => !(p.type.isVoid || p.type.isErased))
            |>.unzip
        emit fn; emit "("
        for h : i in 0...args.size do
          if i > 0 then emit ", "
          emit args[i]
        emit ")"
      | some (.inline _ pat) =>
        emit (expandExternPattern pat (← toStringArgs args))
      | some .opaque | none =>
        emitLeanFunReference decl.type fn
        if args.size > 0 then
          let (_, args) :=
            ps.zip args
              |>.filter (fun (p, _) => !p.type.isVoid)
              |>.unzip
          emit "("; emitArgs args; emit ")"
      | _ => throwError s!"failed to emit extern application '{fn}'"

  emitPap (fn : Name) (args : Array (Arg .impure)) : EmitM Unit := do
    let some sig ← getImpureSignature? fn | unreachable!
    let arity := sig.params.size
    withEmitAssignment do
      emitCApp3 "lean_alloc_closure" s!"(void*)({← toCName fn})" arity args.size
    for h : i in 0...args.size do
      let arg := args[i]
      emitCApp3 "lean_closure_set" decl.fvarId i arg; emitLn ";"

  emitAp (fvarId : FVarId) (args : Array (Arg .impure)) : EmitM Unit := do
    assert! !args.isEmpty
    if args.size > closureMaxArgs then
      withEmitBlock do
        emit "lean_object* _aargs[] = {"; emitArgs args; emitLn "};"
        withEmitAssignment do
          emitCApp3 "lean_apply_m" fvarId args.size "_aargs"
    else
      withEmitAssignment do
        emit s!"lean_apply_{args.size}("; emit fvarId; emit ", "; emitArgs args; emit ")"

  emitBox (ty : Expr) (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emitCApp1 ty.boxOpName fvarId

  emitUnbox (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emitCApp1 decl.type.unboxOpName fvarId

  emitIsShared (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emit "!"; emitCApp1 "lean_is_exclusive" fvarId

  emitLit (v : LitValue) : EmitM Unit := do
    withEmitAssignment do
      match v with
      | .uint8 v | .uint16 v | .uint32 v => emit v
      | .uint64 v => emit v; emit "ULL"
      | .usize v => emit "((size_t)"; emit v; emit "ULL)"
      | .nat v =>
        if v < UInt32.size then
          emit "lean_unsigned_to_nat("; emit v; emit "u)"
        else
          emit "lean_cstr_to_nat(\""; emit v; emit "\")"
      | .str v =>
        emitCApp3 "lean_mk_string_unchecked" (quoteString v) v.utf8ByteSize v.length

  emitErased : EmitM Unit := do
    withEmitAssignment do
      emit "lean_box(0)"

  emitLhs (binderName : Name) : EmitM Unit := do
    emit binderName; emit " = "

  @[inline]
  withEmitAssignment {α : Type} (x : EmitM α) : EmitM α := do
    emitLhs decl.binderName
    let ret ← x
    emitLn ";"
    return ret

def emitTailCall (decl : LetDecl .impure) : EmitM Unit := do
  let .fap _ args := decl.value | unreachable!
  let ps ← getCurrParams
  assert! ps.size == args.size
  let (ps, args) := ps.zip args |>.filter (fun (p, _) => !p.type.isVoid) |>.unzip
  if overwriteParam ps args then
    withEmitBlock do
      for h : i in 0...ps.size do
        let p := ps[i]
        let arg := args[i]!
        unless paramEqArg p arg do
          emit p.type.toCType; emit " _tmp_"; emit i; emit " = "; emit arg; emitLn ";"

      for h : i in 0...ps.size do
        let p := ps[i]
        let arg := args[i]!
        unless paramEqArg p arg do
          emit p.binderName; emit " = _tmp_"; emit i; emitLn ";"
  else
    for p in ps, arg in args do
      unless paramEqArg p arg do
        emit p.binderName; emit " = "; emit arg; emitLn ";"
  emitLn "goto _start;"
where
  /--
  Given `[p_0, ..., p_{n-1}]`, `[arg_0, ..., arg_{n-1}]`, representing the assignments
  ```
  p_0 := arg_0,
  ...
  p_{n-1} := arg_{n-1}
  ```
  Return true iff we have `(i, j)` where `j > i`, and `arg_j == p_i`.
  That is, we have
  ```
  p_i := arg_i,
  ...
  p_j := p_i, -- p_i was overwritten above
  ```
  -/
  overwriteParam (ps : Array (Param .impure)) (args : Array (Arg .impure)) : Bool := Id.run do
    for h1 : i in 0...ps.size do
      let p := ps[i]
      for h2 : j in (i+1)...args.size do
        if paramEqArg p args[j] then
          return true
    return false

  paramEqArg (p : Param .impure) (arg : Arg .impure) : Bool :=
    match arg with
    | .fvar fvarId => p.fvarId == fvarId
    | .erased => false


mutual

partial def emitBasicBlock (code : Code .impure) : EmitM Unit := do
  match code with
  | .jp (k := k) .. => emitBasicBlock k
  | .let decl k =>
    if ← isTailCall code then
      emitTailCall decl
    else
      emitLetDecl decl
      emitBasicBlock k
  | .inc fvarId n check persistent k =>
    unless persistent do emitInc fvarId n check
    emitBasicBlock k
  | .dec fvarId n check persistent k =>
    unless persistent do emitDec fvarId n check
    emitBasicBlock k
  | .del fvarId k =>
    emitDel fvarId
    emitBasicBlock k
  | .setTag fvarId cidx k =>
    emitSetTag fvarId cidx
    emitBasicBlock k
  | .oset fvarId i y k =>
    emitOset fvarId i y
    emitBasicBlock k
  | .uset fvarId i y k =>
    emitUset fvarId i y
    emitBasicBlock k
  | .sset fvarId i offset y ty k =>
    emitSset fvarId i offset y ty
    emitBasicBlock k
  | .cases cs => emitCases cs
  | .return fvarId => emitReturn fvarId
  | .jmp fvarId args => emitJmp fvarId args
  | .unreach .. => emitUnreach
where
  emitInc (fvarId : FVarId) (n : Nat) (check : Bool) : EmitM Unit := do
    if n == 1 then
      let incFn := if check then "lean_inc" else "lean_inc_ref"
      emitCApp1 incFn fvarId
    else
      let incFn := if check then "lean_inc_n" else "lean_inc_ref_n"
      emitCApp2 incFn fvarId n
    emitLn ";"

  emitDec (fvarId : FVarId) (n : Nat) (check : Bool) : EmitM Unit := do
    -- Anything else is unsupported at the moment
    assert! n == 1
    let decFn := if check then "lean_dec" else "lean_dec_ref"
    emitCApp1 decFn fvarId
    emitLn ";"

  emitDel (fvarId : FVarId) : EmitM Unit := do
    emitCApp1 "lean_del_object" fvarId
    emitLn ";"

  emitSetTag (fvarId : FVarId) (cidx : Nat) : EmitM Unit := do
    emitCApp2 "lean_ctor_set_tag" fvarId cidx
    emitLn ";"

  emitOset (fvarId : FVarId) (i : Nat) (y : Arg .impure) : EmitM Unit := do
    emitCApp3 "lean_ctor_set" fvarId i y
    emitLn ";"

  emitUset (fvarId : FVarId) (i : Nat) (y : FVarId) : EmitM Unit := do
    emitCApp3 "lean_ctor_set_usize" fvarId i y
    emitLn ";"

  emitSset (fvarId : FVarId) (i : Nat) (offset : Nat) (y : FVarId) (ty : Expr) : EmitM Unit := do
    emitCApp3 ty.ssetOpName fvarId (offsetExpression i offset) y
    emitLn ";"

  isIf (cs : Cases .impure) : EmitM (Option (Nat × Code .impure × Code .impure)) := do
    if h : cs.alts.size = 2 then
      match cs.alts[0] with
      | .ctorAlt info k => return some (info.cidx, k, cs.alts[1].getCode)
      | _ => return none
    else
      return none

  emitTag (fvarId : FVarId) : EmitM Unit := do
    let type ← getType fvarId
    if type.isObj then do
      emitCApp1 "lean_obj_tag" fvarId
    else
      emit fvarId

  emitCases (cs : Cases .impure) : EmitM Unit := do
    match ← isIf cs with
    | some (tag, t, e) =>
      emit "if ("; emitTag cs.discr; emit " == "; emit tag; emitLn ")";
      emitCode t
      emitLn "else"
      emitCode e
    | none =>
      emit "switch("; emitTag cs.discr; emitLn ")"
      withEmitBlock do
        let alts := ensureHasDefault cs.alts
        -- TODO: consider UB if no default?
        alts.forM fun alt => do
          match alt with
          | .ctorAlt info k =>
            emit "case "; emit info.cidx; emitLn ":"
            emitCode k
          | .default k =>
            emitLn "default: ";
            emitCode k

  emitReturn (fvarId : FVarId) : EmitM Unit := do
    emit "return "; emit fvarId; emitLn ";"

  emitJmp (fvarId : FVarId) (args : Array (Arg .impure)) : EmitM Unit := do
    let some jpDecl ← findFunDecl? (pu := .impure) fvarId | unreachable!
    let ps := jpDecl.params
    if args.size != ps.size then
      throwError "invalid jump"
    for arg in args, p in ps do
      emit p.binderName; emit " = "; emit arg; emitLn ";"
    emit "goto "; emit fvarId; emitLn ";"

  emitUnreach : EmitM Unit := do
    emitLn "lean_internal_panic_unreachable();"

partial def emitJoinPoints (code : Code .impure) : EmitM Unit := do
  match code with
  | .jp decl k =>
    emit decl.binderName; emitLn ":"
    emitCode decl.value
    emitJoinPoints k
  | .let (k := k) .. | .del (k := k) .. | .dec (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
  | .sset (k := k) .. | .uset (k := k) .. | .oset (k := k) .. => emitJoinPoints k
  | .cases .. | .return .. | .jmp .. | .unreach .. => return ()

partial def emitCode (code : Code .impure) : EmitM Unit := do
  withEmitBlock do
    let declared ← declareVars code
    if declared then emitLn ""
    emitBasicBlock code
    emitJoinPoints code

end

def emitDecl (decl : Decl .impure) : EmitM Unit := do
  let env ← getEnv
  if hasInitAttr env decl.name || isSimpleGroundDecl env decl.name then
    return ()
  match decl.value with
  | .extern .. => return ()
  | .code code =>
    let baseName ← toCName decl.name
    let ps := decl.params
    if ps.isEmpty then
      emit "static "
    else
      -- make the symbol visible to the interpreter for native execution
      emit "LEAN_EXPORT "

    emit decl.type.toCType; emit " "

    if ps.isEmpty then
      emitCInitName decl.name
      emit "(void)"
    else
      emit baseName
      emit "("
      let ps := paramsWithoutVoid ps
      if ps.size > closureMaxArgs && isBoxedName decl.name then
        emit "lean_object** _args"
      else
        ps.size.forM fun i _ => do
          if i > 0 then emit ", "
          let p := ps[i]
          emit p.type.toCType; emit " "; emit p.binderName
      emit ")"

    withEmitBlock do
      if ps.size > closureMaxArgs && isBoxedName decl.name then
        ps.size.forM fun i _ => do
          let p := ps[i]
          emit "lean_object* "; emit p.binderName; emit " = _args["; emit i; emitLn "];"
      -- goto marker for tail recursion
      emitLn "_start:"
      withReader (fun ctx => { ctx with currFn := decl.name, currParams := ps }) do
        emitCode code

def emitFns : EmitM Unit := do
  (← getLocalDecls).forM go
where
  go (decl : Decl .impure) : EmitM Unit := do
    let decl ← decl.internalize (uniqueIdents := true)
    try
      emitDecl decl
    catch err =>
      throwError m!"{err.toMessageData}\ncompiling:\n{decl.name}"

def withErrRet (emitIORes : EmitM Unit) : EmitM Unit := do
  emit "res = "; emitIORes; emitLn ";"
  emitLn "if (lean_io_result_is_error(res)) return res;"

def emitMarkPersistent (decl : Decl .impure) : EmitM Unit := do
  if decl.type.isObj then
    emitCApp1 "lean_mark_persistent" (← toCName decl.name); emitLn ";"

def emitDeclInit (decl : Decl .impure) (isBuiltin : Bool) : EmitM Unit := do
  let env ← getEnv
  if (isBuiltin && isIOUnitBuiltinInitFn env decl.name) || isIOUnitInitFn env decl.name then
    withErrRet do
      emitCName decl.name; emit "()"
    emitLn "lean_dec_ref(res);"
  else if decl.params.isEmpty then
    if let some initFn := (guard isBuiltin *> getBuiltinInitFnNameFor? env decl.name) <|> getInitFnNameFor? env decl.name then
      withErrRet do
        emitCName initFn; emit "()"
      emitCName decl.name
      if decl.type.isScalar then
        emitLn <| " = " ++ decl.type.unboxOpName ++ "(lean_io_result_get_value(res));"
      else
        emitLn " = lean_io_result_get_value(res);"
        emitMarkPersistent decl
      emitLn "lean_dec_ref(res);"
    else if !(isClosedTermName env decl.name || isSimpleGroundDecl env decl.name) then
      emitCName decl.name; emit " = "; emitCInitName decl.name; emitLn "();"
      emitMarkPersistent decl

def emitInitFn (phases : IRPhases) : EmitM Unit := do
  let env ← getEnv
  let impInitFns ← env.imports.filterMapM fun imp => do
    if phases != .all && imp.isMeta != (phases == .comptime) then
      return none
    let some idx := env.getModuleIdx? imp.module
      | throwError "(internal) import without module index" -- should be unreachable
    let pkg? := env.getModulePackageByIdx? idx
    let fn := mkModuleInitializationFunctionName (phases := if phases == .all then .all else if imp.isMeta then .runtime else phases) imp.module pkg?
    emitLn s!"lean_object* {fn}(uint8_t builtin);"
    return some fn
  let initialized := s!"_G_{mkModuleInitializationPrefix phases}initialized"
  emitLns [
    s!"static bool {initialized} = false;",
    s!"LEAN_EXPORT lean_object* {← getModInitFn (phases := phases)}(uint8_t builtin) \{",
    "lean_object * res;",
    s!"if ({initialized}) return lean_io_result_mk_ok(lean_box(0));",
    s!"{initialized} = true;"
  ]
  impInitFns.forM fun fn => do
    withErrRet do
      emit s!"{fn}(builtin)"
    emitLn "lean_dec_ref(res);"
  for decl in (← getLocalDecls) do
    if phases == .all || (phases == .comptime) == isMarkedMeta env decl.name then
      emitDeclInit decl (isBuiltin := phases != .comptime)
  emitLn "return lean_io_result_mk_ok(lean_box(0));"
  emitLn "}"

/-- Init function used before phase split under module system, keep for compatibility. -/
def emitLegacyInitFn : EmitM Unit := do
  let env ← getEnv
  let impInitFns ← env.imports.filterMapM fun imp => do
    let some idx := env.getModuleIdx? imp.module
      | throwError "(internal) import without module index" -- should be unreachable
    let pkg? := env.getModulePackageByIdx? idx
    let fn := mkModuleInitializationFunctionName imp.module pkg?
    emitLn s!"lean_object* {fn}(uint8_t builtin);"
    return some fn
  let initialized := s!"_G_initialized"
  emitLns [
    s!"static bool {initialized} = false;",
    s!"LEAN_EXPORT lean_object* {← getModInitFn (phases := .all)}(uint8_t builtin) \{",
    "lean_object * res;",
    s!"if ({initialized}) return lean_io_result_mk_ok(lean_box(0));",
    s!"{initialized} = true;"
  ]
  impInitFns.forM fun fn => do
    withErrRet do
      emit s!"{fn}(builtin)"
    emitLn "lean_dec_ref(res);"
  withErrRet do
    emit s!"{← getModInitFn (phases := .runtime)}(builtin)"
  emitLn "lean_dec_ref(res);"
  withErrRet do
    emit s!"{← getModInitFn (phases := .comptime)}(builtin)"
  emitLn "lean_dec_ref(res);"
  emitLn s!"return {← getModInitFn (phases := .all)}(builtin);"
  emitLn "}"

def emitMainFnIfNeeded : EmitM Unit := do
  if let some mainFn ← hasMainFn then
    emitMainFn mainFn
where
  hasMainFn : EmitM (Option (Decl .impure)) := do
    return (← getLocalDecls).find? (·.name == `main)

  emitMainFn (decl : Decl .impure) : EmitM Unit := do
    let .code .. := decl.value | throwError "Expected Lean function declaration as `main`"
    let ps := decl.params
    if ps.size != 1 && ps.size != 2 then
      throwError "invalid main function, incorrect arity when generating code"
    let env ← getEnv
    let usesLeanAPI := usesModuleFrom env `Lean
    emitLns [
      "char ** lean_setup_args(int argc, char ** argv);",
      if usesLeanAPI then "void lean_initialize();" else "void lean_initialize_runtime_module();",
      "#if defined(WIN32) || defined(_WIN32)",
      "#include <windows.h>",
      "#endif",
      "lean_object* run_main(int argc, char ** argv) {"
    ]
    if ps.size == 2 then
      emitLns [
        "    lean_object* in = lean_box(0);",
        "    int i = argc;",
        "    while (i > 1) {",
        "      lean_object* n;",
        "      i--;",
        "      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);",
        "      in = n;",
        "    }"
      ]
      emitLn <| "    return " ++ leanMainFn ++ "(in);"
    else
      emitLn <| "    return " ++ leanMainFn ++ "();"
    emitLns [
      "}",
      "int main(int argc, char ** argv) {",
      "#if defined(WIN32) || defined(_WIN32)",
      "  SetErrorMode(SEM_FAILCRITICALERRORS);",
      "  SetConsoleOutputCP(CP_UTF8);",
      "#endif",
      "  lean_object* res;",
      "  argv = lean_setup_args(argc, argv);",
      if usesLeanAPI then "  lean_initialize();" else "  lean_initialize_runtime_module();",
      s!"  res = {← getModInitFn (phases := if env.header.isModule then .runtime else .all)}(1 /* builtin */);",
      "  lean_io_mark_end_initialization();",
      "  if (lean_io_result_is_ok(res)) {",
      "    lean_dec_ref(res);",
      "    lean_init_task_manager();",
      "    res = lean_run_main(&run_main, argc, argv);",
      "  }"
    ]
    -- `IO _`
    let retTy := env.find? `main |>.get! |>.type |>.getForallBody
    -- either `UInt32` or `(P)Unit`
    let retTy := retTy.appArg!
    let hasExitCode := retTy.isConstOf ``UInt32
    -- finalize at least the task manager to avoid leak sanitizer false positives from tasks outliving the main thread
    emitLns [
      "  lean_finalize_task_manager();",
      "  if (lean_io_result_is_ok(res)) {",
      "    int ret = " ++ if hasExitCode then "lean_unbox_uint32(lean_io_result_get_value(res));" else "0;",
      "    lean_dec_ref(res);",
      "    return ret;",
      "  } else {",
      "    lean_io_result_show_error(res);",
      "    lean_dec_ref(res);",
      "    return 1;",
      "  }"]
    emitLn "}"

def emitFileFooter : EmitM Unit :=
  emitLns [
   "#ifdef __cplusplus",
   "}",
   "#endif"
  ]

def main : EmitM Unit := do
  emitFileHeader
  emitFnDecls
  emitFns
  if (← getEnv).header.isModule then
    emitInitFn (phases := .runtime)
    emitInitFn (phases := .comptime)
    emitLegacyInitFn
  else
    emitInitFn (phases := .all)
  emitMainFnIfNeeded
  emitFileFooter

public def emitCForDecls (modName : Name) (decls : Array Name) : CoreM String := do
  let (localDecls, otherModuleDecls) ← collectUsedDecls decls
  let env ← getEnv
  let indexMap := getImpureDeclIndices env decls
  let localDecls := localDecls.qsort fun l r => indexMap[l.name]! < indexMap[r.name]!
  let (_, { buf, .. }) ←
    main
      |>.run { localDecls, otherModuleDecls, modName }
      |>.run {}
      |>.run (phase := .impure)
  return buf

public def emitC (modName : Name) : CoreM String := do
  emitCForDecls modName (← getLocalImpureDecls)

end Lean.Compiler.LCNF
