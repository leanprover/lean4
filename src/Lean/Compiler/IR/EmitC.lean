/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.NameMangling
public import Lean.Compiler.IR.EmitUtil
public import Lean.Compiler.IR.NormIds
public import Lean.Compiler.IR.SimpCase
public import Lean.Compiler.IR.Boxing
public import Lean.Compiler.IR.StructRC
public import Lean.Compiler.ModPkgExt

public section

namespace Lean.IR.EmitC
open ExplicitBoxing (isBoxedName)

def leanMainFn := "_lean_main"

structure Context where
  env        : Environment
  modName    : Name
  jpMap      : JPParamsMap := {}
  mainFn     : FunId := default
  mainParams : Array Param := #[]
  varTypes   : VarTypeMap := {}
  structs    : StructTypeLookup := {}

abbrev M := ReaderT Context (EStateM String String)

@[inline] def getEnv : M Environment := Context.env <$> read

@[inline] def getModName : M Name := Context.modName <$> read

@[inline] def getModInitFn : M String := do
  let pkg? := (← getEnv).getModulePackage?
  return mkModuleInitializationFunctionName (← getModName) pkg?

def getDecl (n : Name) : M Decl := do
  let env ← getEnv
  match findEnvDecl env n with
  | some d => pure d
  | none   => throw s!"unknown declaration '{n}'"

@[inline] def emit {α : Type} [ToString α] (a : α) : M Unit :=
  modify fun out => out ++ toString a

@[inline] def emitLn {α : Type} [ToString α] (a : α) : M Unit := do
  emit a; emit "\n"

def emitLns {α : Type} [ToString α] (as : List α) : M Unit :=
  as.forM fun a => emitLn a

def argToCString (x : Arg) : String :=
  match x with
  | .var x => toString x
  | .erased => "lean_box(0)"

def emitArg (x : Arg) : M Unit :=
  emit (argToCString x)

@[inline]
def lookupStruct (ty : IRType) : M Nat := do
  return (← read).structs[IRTypeApprox.mk ty]!

def structType (id : Nat) : String :=
  "struct l_s" ++ id.repr

def toCType : IRType → M String
  | .float      => return "double"
  | .float32    => return "float"
  | .uint8      => return "uint8_t"
  | .uint16     => return "uint16_t"
  | .uint32     => return "uint32_t"
  | .uint64     => return "uint64_t"
  | .usize      => return "size_t"
  | .object     => return "lean_object*"
  | .tagged     => return "lean_object*"
  | .tobject    => return "lean_object*"
  | .erased     => return "lean_object*"
  | .void       => return "lean_object*"
  | ty@(.struct ..) | ty@(.union ..) =>
    return structType (← lookupStruct ty)

def throwInvalidExportName {α : Type} (n : Name) : M α :=
  throw s!"invalid export name '{n}'"

def toCName (n : Name) : M String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => return s
  | some _                   => throwInvalidExportName n
  | none                     => return if n == `main then leanMainFn else getSymbolStem env n

def emitCName (n : Name) : M Unit :=
  toCName n >>= emit

def toCInitName (n : Name) : M String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => return "_init_" ++ s
  | some _                   => throwInvalidExportName n
  | none                     => return "_init_" ++ getSymbolStem env n

def emitCInitName (n : Name) : M Unit :=
  toCInitName n >>= emit

def emitSpreadArg (ty : IRType) (name : Option String) (first : Bool) : M Bool := do
  if let .struct _ tys 0 0 := ty then
    let mut first := first
    for h : i in *...tys.size do
      let ty := tys[i]
      if ty matches .erased then
        continue
      first ← emitSpreadArg ty (name.map fun nm => nm ++ "_" ++ i.repr) first
    return first
  if ty matches .void then
    return first
  unless first do
    emit ", "
  emit (← toCType ty)
  if let some nm := name then
    emit " "; emit nm
  return false

def emitSpreadArgs (ps : Array Param) (emitNames : Bool) : M Unit := do
  let mut first := true
  for p in ps do
    first ← emitSpreadArg p.ty (if emitNames then some (toString p.x) else none) first

def emitSpreadValue (ty : IRType) (name : String) : M Unit := do
  if let .struct _ tys 0 0 := ty then
    emit "{"
    let mut first := true
    for h : i in *...tys.size do
      let ty := tys[i]
      if ty matches .erased | .void then
        continue
      unless first do
        emit ", "
      emit ".i"; emit i; emit " = "
      emitSpreadValue ty (name ++ "_" ++ i.repr)
      first := false
    emit "}"
    return
  emit name

def emitSpreads (ps : Array Param) : M Unit := do
  for p in ps do
    if let .struct _ _ 0 0 := p.ty then
      emit (← toCType p.ty); emit " "; emit p.x; emit " = ("; emit (← toCType p.ty); emit ")"
      emitSpreadValue p.ty (toString p.x)
      emitLn ";"

def emitFullAppArg (ty : IRType) (nm : String) (first : Bool) : M Bool := do
  if let .struct _ tys 0 0 := ty then
    let mut first := first
    for h : i in *...tys.size do
      let ty := tys[i]
      if ty matches .erased | .void then
        continue
      first ← emitFullAppArg ty (nm ++ ".i" ++ i.repr) first
    return first
  if ty matches .void then
    return first
  unless first do emit ", "
  emit nm
  return false

def emitFullAppArgs (ps : Array Param) (args : Array Arg) : M Unit := do
  let mut first := true
  for h : i in *...args.size do
    let ty := ps[i]!.ty
    let arg := args[i]
    if ty matches .void then
      continue
    match arg with
    | .erased =>
      unless first do emit ", "
      emit "lean_box(0)"
      first := false
    | .var v =>
      first ← emitFullAppArg ty (toString v) first

def emitFnDeclAux (decl : Decl) (cppBaseName : String) (isExternal : Bool) : M Unit := do
  let ps := decl.params
  let env ← getEnv
  if ps.isEmpty then
    if isExternal then emit "extern "
    else if isClosedTermName env decl.name then emit "static "
    else emit "LEAN_EXPORT "
  else
    if !isExternal then emit "LEAN_EXPORT "
  emit ((← toCType decl.resultType) ++ " " ++ cppBaseName)
  unless ps.isEmpty do
    emit "("
    -- We omit void parameters, note that they are guaranteed not to occur in boxed functions
    let ps := ps.filter (fun p => !p.ty.isVoid)
    -- We omit erased parameters for extern constants
    let ps := if isExternC env decl.name then ps.filter (fun p => !p.ty.isErased) else ps
    if ps.size > closureMaxArgs && isBoxedName decl.name then
      emit "lean_object**"
    else
      emitSpreadArgs ps false
    emit ")"
  emitLn ";"

def emitFnDecl (decl : Decl) (isExternal : Bool) : M Unit := do
  let cppBaseName ← toCName decl.name
  emitFnDeclAux decl cppBaseName isExternal

def emitExternDeclAux (decl : Decl) (cNameStr : String) : M Unit := do
  let env ← getEnv
  let extC := isExternC env decl.name
  emitFnDeclAux decl cNameStr extC

def emitFnDecls : M Unit := do
  let env ← getEnv
  let decls := getDecls env
  let modDecls  : NameSet := decls.foldl (fun s d => s.insert d.name) {}
  let usedDecls : NameSet := decls.foldl (fun s d => collectUsedDecls env d (s.insert d.name)) {}
  let usedDecls := usedDecls.toList
  usedDecls.forM fun n => do
    let decl ← getDecl n;
    match getExternNameFor env `c decl.name with
    | some cName => emitExternDeclAux decl cName
    | none       => emitFnDecl decl (!modDecls.contains n)

def emitMainFn : M Unit := do
  let d ← getDecl `main
  match d with
  | .fdecl (xs := xs) .. => do
    unless xs.size == 2 || xs.size == 1 do throw "invalid main function, incorrect arity when generating code"
    let env ← getEnv
    let usesLeanAPI := usesModuleFrom env `Lean
    emitLn "char ** lean_setup_args(int argc, char ** argv);";
    if usesLeanAPI then
       emitLn "void lean_initialize();"
    else
       emitLn "void lean_initialize_runtime_module();";
    emitLn "
  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
  #endif
  lean_object* in; lean_object* res;";
    emitLn "argv = lean_setup_args(argc, argv);";
    if usesLeanAPI then
      emitLn "lean_initialize();"
    else
      emitLn "lean_initialize_runtime_module();"
    /- We disable panic messages because they do not mesh well with extracted closed terms.
       See issue #534. We can remove this workaround after we implement issue #467. -/
    emitLn "lean_set_panic_messages(false);"
    emitLn s!"res = {← getModInitFn}(1 /* builtin */);"
    emitLn "lean_set_panic_messages(true);"
    emitLns ["lean_io_mark_end_initialization();",
             "if (lean_io_result_is_ok(res)) {",
             "lean_dec_ref(res);",
             "lean_init_task_manager();"];
    if xs.size == 2 then
      emitLns ["in = lean_box(0);",
               "int i = argc;",
               "while (i > 1) {",
               " lean_object* n;",
               " i--;",
               " n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);",
               " in = n;",
              "}"]
      emitLn ("res = " ++ leanMainFn ++ "(in);")
    else
      emitLn ("res = " ++ leanMainFn ++ "();")
    emitLn "}"
    -- `IO _`
    let retTy := env.find? `main |>.get! |>.type |>.getForallBody
    -- either `UInt32` or `(P)Unit`
    let retTy := retTy.appArg!
    -- finalize at least the task manager to avoid leak sanitizer false positives from tasks outliving the main thread
    emitLns ["lean_finalize_task_manager();",
             "if (lean_io_result_is_ok(res)) {",
             "  int ret = " ++ if retTy.constName? == some ``UInt32 then "lean_unbox_uint32(lean_io_result_get_value(res));" else "0;",
             "  lean_dec_ref(res);",
             "  return ret;",
             "} else {",
             "  lean_io_result_show_error(res);",
             "  lean_dec_ref(res);",
             "  return 1;",
             "}"]
    emitLn "}"
  | _     => throw "function declaration expected"

def hasMainFn : M Bool := do
  let env ← getEnv
  let decls := getDecls env
  return decls.any (fun d => d.name == `main)

def emitMainFnIfNeeded : M Unit := do
  if (← hasMainFn) then emitMainFn

def emitFileHeader : M Unit := do
  let env ← getEnv
  let modName ← getModName
  emitLn "// Lean compiler output"
  emitLn ("// Module: " ++ toString modName)
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

def emitFileFooter : M Unit :=
  emitLns [
   "#ifdef __cplusplus",
   "}",
   "#endif"
  ]

def throwUnknownVar {α : Type} (x : VarId) : M α :=
  throw s!"unknown variable '{x}'"

def getJPParams (j : JoinPointId) : M (Array Param) := do
  let ctx ← read;
  match ctx.jpMap[j]? with
  | some ps => pure ps
  | none    => throw "unknown join point"

def declareVar (x : VarId) (t : IRType) : M Unit := do
  emit (← toCType t); emit " "; emit x; emit "; "

def declareParams (ps : Array Param) : M Unit :=
  ps.forM fun p => declareVar p.x p.ty

partial def declareVars : FnBody → Bool → M Bool
  | e@(FnBody.vdecl x t _ b), d => do
    let ctx ← read
    if isTailCallTo ctx.mainFn e then
      pure d
    else
      declareVar x t; declareVars b true
  | FnBody.jdecl _ xs _ b,    d => do declareParams xs; declareVars b (d || xs.size > 0)
  | e,                        d => if e.isTerminal then pure d else declareVars e.body d

partial def optionLikePath (ty : IRType) : Option (List Nat) := Id.run do
  match ty with
  | .struct _ tys _ _ =>
    for h : i in *...tys.size do
      if let some l := optionLikePath tys[i] then
        return i :: l
    return none
  | .tagged | .object | .tobject => return some []
  | _ => return none

def optionLike? (ty : IRType) : Option (List Nat) :=
  match ty with
  | .union _ #[.struct _ #[] 0 0, ty] => optionLikePath ty
  | _ => none

def emitPath (path : List Nat) : M Unit := do
  emit ".cs.c1"; path.forM (emit s!".i{·}")

def emitTag (x : VarId) (xType : IRType) : M Unit := do
  if xType.isObj then do
    emit "lean_obj_tag("; emit x; emit ")"
  else if xType.isStruct then
    if let some a := optionLike? xType then
      emit x; emitPath a; emit " != 0"
    else
      emit x; emit ".tag"
  else
    emit x

def isIf (alts : Array Alt) : Option (Nat × FnBody × FnBody) :=
  if h : alts.size ≠ 2 then none
  else match alts[0] with
    | Alt.ctor c b => some (c.cidx, b, alts[1].body)
    | _            => none

partial def needsRC (ty : IRType) : Bool :=
  match ty with
  | .object | .tobject => true
  | .union _ tys => tys.any needsRC
  | .struct _ tys _ _ => tys.any needsRC
  | _ => false

def structIncFnPrefix := "_l_struct_inc_"
def structDecFnPrefix := "_l_struct_dec_"
def structReshapeFnPrefix := "_l_struct_reshape_"
def structBoxFnPrefix := "_l_struct_box_"
def structUnboxFnPrefix := "_l_struct_unbox_"

def emitIncOfType (x : String) (ty : IRType) (n : Nat) (checkRef : Bool) (nstr : String) :
    M Unit := do
  if ty.isStruct then
    unless needsRC ty do
      return
    let id ← lookupStruct ty
    emit structIncFnPrefix; emit id; emit "("
    emit x; emit ", "; emit nstr
    emitLn ");"
  else
    emit $
      if checkRef then (if n == 1 then "lean_inc" else "lean_inc_n")
      else (if n == 1 then "lean_inc_ref" else "lean_inc_ref_n")
    emit "("; emit x
    if n != 1 then emit ", "; emit nstr
    emitLn ");"

def emitInc (x : VarId) (n : Nat) (checkRef : Bool)  : M Unit := do
  let ty := (← read).varTypes[x]!
  emitIncOfType (toString x) ty n checkRef n.repr

def emitDecOfType (x : String) (ty : IRType) (n : Nat) (checkRef : Bool) : M Unit := do
  if ty.isStruct then
    unless needsRC ty do
      return
    let id ← lookupStruct ty
    emit structDecFnPrefix; emit id; emit "("; emit x; emitLn ");"
  else
    n.forM fun _ _ => do
      emit (if checkRef then "lean_dec" else "lean_dec_ref");
      emit "("; emit x; emitLn ");"

def emitDec (x : VarId) (n : Nat) (checkRef : Bool) : M Unit := do
  let ty := (← read).varTypes[x]!
  emitDecOfType (toString x) ty n checkRef

def emitDel (x : VarId) : M Unit := do
  emit "lean_free_object("; emit x; emitLn ");"

def emitSetTag (x : VarId) (i : Nat) : M Unit := do
  emit "lean_ctor_set_tag("; emit x; emit ", "; emit i; emitLn ");"

def emitSet (x : VarId) (i : Nat) (y : Arg) : M Unit := do
  emit "lean_ctor_set("; emit x; emit ", "; emit i; emit ", "; emitArg y; emitLn ");"

def emitOffset (n : Nat) (offset : Nat) : M Unit := do
  if n > 0 then
    emit "sizeof(void*)*"; emit n;
    if offset > 0 then emit " + "; emit offset
  else
    emit offset


def emitUSet (x : VarId) (cidx : Nat) (n : Nat) (y : VarId) : M Unit := do
  let ty := (← read).varTypes[x]!
  if let .union _ tys := ty then
    let .struct _ tys _ _ := tys[cidx]! | unreachable!
    emit x; emit ".cs.c"; emit cidx; emit ".u["; emit (n - tys.size); emit "] = "; emit y; emitLn ";"
  else if let .struct _ tys _ _ := ty then
    emit x; emit ".u["; emit (n - tys.size); emit "] = "; emit y; emitLn ";"
  else
    emit "lean_ctor_set_usize("; emit x; emit ", "; emit n; emit ", "; emit y; emitLn ");"

def emitSSet (x : VarId) (cidx : Nat) (n : Nat) (offset : Nat) (y : VarId) (t : IRType) : M Unit := do
  let ty := (← read).varTypes[x]!
  if ty matches .union .. then
    emit "*(("; emit (← toCType t); emit "*)("
    emit x; emit ".cs.c"; emit cidx; emit ".s+"; emit offset; emit ")) = "; emit y; emitLn ";"
    return
  else if ty matches .struct .. then
    emit "*(("; emit (← toCType t); emit "*)("
    emit x; emit ".s+"; emit offset; emit ")) = "; emit y; emitLn ";"
    return
  match t with
  | IRType.float   => emit "lean_ctor_set_float"
  | IRType.float32 => emit "lean_ctor_set_float32"
  | IRType.uint8   => emit "lean_ctor_set_uint8"
  | IRType.uint16  => emit "lean_ctor_set_uint16"
  | IRType.uint32  => emit "lean_ctor_set_uint32"
  | IRType.uint64  => emit "lean_ctor_set_uint64"
  | _              => throw "invalid instruction";
  emit "("; emit x; emit ", "; emitOffset n offset; emit ", "; emit y; emitLn ");"

def emitJmp (j : JoinPointId) (xs : Array Arg) : M Unit := do
  let ps ← getJPParams j
  if h : xs.size = ps.size then
    xs.size.forM fun i _ => do
      let p := ps[i]
      let x := xs[i]
      emit p.x; emit " = "; emitArg x; emitLn ";"
    emit "goto "; emit j; emitLn ";"
  else
    do throw "invalid goto"

def emitLhs (z : VarId) : M Unit := do
  emit z; emit " = "

def emitArgs (ys : Array Arg) : M Unit :=
  ys.size.forM fun i _ => do
    if i > 0 then emit ", "
    emitArg ys[i]

def emitCtorScalarSize (usize : Nat) (ssize : Nat) : M Unit := do
  if usize == 0 then emit ssize
  else if ssize == 0 then emit "sizeof(size_t)*"; emit usize
  else emit "sizeof(size_t)*"; emit usize; emit " + "; emit ssize

def emitAllocCtor (c : CtorInfo) : M Unit := do
  emit "lean_alloc_ctor("; emit c.cidx; emit ", "; emit c.size; emit ", "
  emitCtorScalarSize c.usize c.ssize; emitLn ");"

def emitCtorSetArgs (z : VarId) (ys : Array Arg) : M Unit :=
  ys.size.forM fun i _ => do
    emit "lean_ctor_set("; emit z; emit ", "; emit i; emit ", "; emitArg ys[i]; emitLn ");"

def emitCtor (z : VarId) (t : IRType) (c : CtorInfo) (ys : Array Arg) : M Unit := do
  if let .union _ tys := t then
    if let some path := optionLike? t then
      if c.cidx = 0 then
        emit z; emitPath path; emitLn " = 0;"
        return
    else
      emit z; emit ".tag = "; emit c.cidx; emitLn ";"
    let .struct _ tys _ _ := tys[c.cidx]! | unreachable!
    for h : i in *...ys.size do
      if tys[i]! matches .erased | .void then
        continue
      emit z; emit ".cs.c"; emit c.cidx; emit ".i"; emit i
      emit " = "; emitArg ys[i]; emitLn ";"
    return
  else if let .struct _ tys _ _ := t then
    for h : i in *...ys.size do
      if tys[i]! matches .erased | .void then
        continue
      emit z; emit ".i"; emit i; emit " = "; emitArg ys[i]; emitLn ";"
    return
  emitLhs z
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    emit "lean_box("; emit c.cidx; emitLn ");"
  else do
    emitAllocCtor c; emitCtorSetArgs z ys

def emitReset (z : VarId) (n : Nat) (x : VarId) : M Unit := do
  emit "if (lean_is_exclusive("; emit x; emitLn ")) {";
  n.forM fun i _ => do
    emit " lean_ctor_release("; emit x; emit ", "; emit i; emitLn ");"
  emit " "; emitLhs z; emit x; emitLn ";";
  emitLn "} else {";
  emit " lean_dec_ref("; emit x; emitLn ");";
  emit " "; emitLhs z; emitLn "lean_box(0);";
  emitLn "}"

def emitReuse (z : VarId) (x : VarId) (c : CtorInfo) (updtHeader : Bool) (ys : Array Arg) : M Unit := do
  emit "if (lean_is_scalar("; emit x; emitLn ")) {";
  emit " "; emitLhs z; emitAllocCtor c;
  emitLn "} else {";
  emit " "; emitLhs z; emit x; emitLn ";";
  if updtHeader then emit " lean_ctor_set_tag("; emit z; emit ", "; emit c.cidx; emitLn ");"
  emitLn "}";
  emitCtorSetArgs z ys

def emitProj (z : VarId) (c : Nat) (i : Nat) (x : VarId) : M Unit := do
  emitLhs z
  let ty := (← read).varTypes[x]!
  if ty matches .struct .. then
    emit x; emit ".i"; emit i; emitLn ";"
  else if ty matches .union .. then
    emit x; emit ".cs.c"; emit c; emit ".i"; emit i; emitLn ";"
  else
    emit "lean_ctor_get("; emit x; emit ", "; emit i; emitLn ");"

def emitUProj (z : VarId) (cidx : Nat) (i : Nat) (x : VarId) : M Unit := do
  emitLhs z
  let ty := (← read).varTypes[x]!
  if let .union _ tys := ty then
    let .struct _ tys _ _ := tys[cidx]! | unreachable!
    emit x; emit ".cs.c"; emit cidx; emit ".u["; emit (i - tys.size); emitLn "];"
  else if let .struct _ tys _ _ := ty then
    emit x; emit ".u["; emit (i - tys.size); emitLn "];"
  else
    emit "lean_ctor_get_usize("; emit x; emit ", "; emit i; emitLn ");"

def emitSProj (z : VarId) (t : IRType) (cidx : Nat) (n offset : Nat) (x : VarId) : M Unit := do
  emitLhs z
  let ty := (← read).varTypes[x]!
  if ty matches .union .. then
    emit "*(("; emit (← toCType t); emit "*)("
    emit x; emit ".cs.c"; emit cidx; emit ".s+"; emit offset; emitLn "));"
    return
  else if ty matches .struct .. then
    emit "*(("; emit (← toCType t); emit "*)("
    emit x; emit ".s+"; emit offset; emitLn "));"
    return
  match t with
  | IRType.float   => emit "lean_ctor_get_float"
  | IRType.float32 => emit "lean_ctor_get_float32"
  | IRType.uint8   => emit "lean_ctor_get_uint8"
  | IRType.uint16  => emit "lean_ctor_get_uint16"
  | IRType.uint32  => emit "lean_ctor_get_uint32"
  | IRType.uint64  => emit "lean_ctor_get_uint64"
  | _              => throw "invalid instruction"
  emit "("; emit x; emit ", "; emitOffset n offset; emitLn ");"

def toStringArgs (ys : Array Arg) : List String :=
  ys.toList.map argToCString

def emitSimpleExternalCall (f : String) (ps : Array Param) (ys : Array Arg) : M Unit := do
  emit f; emit "("
  -- We must remove erased arguments to extern calls.
  discard <| ys.size.foldM
    (fun i _ (first : Bool) =>
      let ty := ps[i]!.ty
      if ty.isErased || ty.isVoid then
        pure first
      else do
        unless first do emit ", "
        emitArg ys[i]
        pure false)
    true
  emitLn ");"
  pure ()

def emitExternCall (f : FunId) (ps : Array Param) (extData : ExternAttrData) (ys : Array Arg) : M Unit :=
  match getExternEntryFor extData `c with
  | some (ExternEntry.standard _ extFn) => emitSimpleExternalCall extFn ps ys
  | some (ExternEntry.inline _ pat)     => do emit (expandExternPattern pat (toStringArgs ys)); emitLn ";"
  | _ => throw s!"failed to emit extern application '{f}'"

def emitFullApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
  emitLhs z
  let decl ← getDecl f
  match decl with
  | .fdecl (xs := ps) .. | .extern (xs := ps) (ext := { entries := [.opaque], .. }) .. =>
    emitCName f
    if ys.size > 0 then
      emit "("; emitFullAppArgs ps ys; emit ")"
    emitLn ";"
  | Decl.extern _ ps _ extData => emitExternCall f ps extData ys

def emitPartialApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
  let decl ← getDecl f
  let arity := decl.params.size;
  emitLhs z; emit "lean_alloc_closure((void*)("; emitCName f; emit "), "; emit arity; emit ", "; emit ys.size; emitLn ");";
  ys.size.forM fun i _ => do
    let y := ys[i]
    emit "lean_closure_set("; emit z; emit ", "; emit i; emit ", "; emitArg y; emitLn ");"

def emitApp (z : VarId) (f : VarId) (ys : Array Arg) : M Unit :=
  if ys.size > closureMaxArgs then do
    emit "{ lean_object* _aargs[] = {"; emitArgs ys; emitLn "};";
    emitLhs z; emit "lean_apply_m("; emit f; emit ", "; emit ys.size; emitLn ", _aargs); }"
  else do
    emitLhs z; emit "lean_apply_"; emit ys.size; emit "("; emit f; emit ", "; emitArgs ys; emitLn ");"

def emitBoxFn (xType tgt : IRType) : M Unit := do
  match xType with
  | .usize   => emit "lean_box_usize"
  | .uint32  => emit "lean_box_uint32"
  | .uint64  => emit "lean_box_uint64"
  | .float   => emit "lean_box_float"
  | .float32 => emit "lean_box_float32"
  | ty@(.struct ..) | ty@(.union ..) =>
    let id ← lookupStruct ty
    if tgt.isStruct then
      emit structReshapeFnPrefix
      emit id
      emit "_"
      emit (← lookupStruct tgt)
    else
      emit structBoxFnPrefix
      emit id
  | _        => emit "lean_box"

def emitBox (z : VarId) (x : VarId) (xType tgt : IRType) : M Unit := do
  emitLhs z; emitBoxFn xType tgt; emit "("; emit x; emitLn ");"

def emitUnboxFn (t : IRType) : M Unit := do
  if t.isStruct then
    emit structUnboxFnPrefix
    emit (← lookupStruct t)
  else
    emit (getUnboxOpName t)

def emitUnbox (z : VarId) (t : IRType) (x : VarId) : M Unit := do
  emitLhs z; emitUnboxFn t; emit "("; emit x; emitLn ");"

def emitIsShared (z : VarId) (x : VarId) : M Unit := do
  emitLhs z; emit "!lean_is_exclusive("; emit x; emitLn ");"

def toHexDigit (c : Nat) : String :=
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
        "\\x" ++ toHexDigit (c.toNat / 16) ++ toHexDigit (c.toNat % 16)
      -- TODO(Leo): we should use `\unnnn` for escaping unicode characters.
      else String.singleton c)
    q;
  q ++ "\""

def emitNumLit (t : IRType) (v : Nat) : M Unit := do
  if t.isObj then
    if v < UInt32.size then
      emit "lean_unsigned_to_nat("; emit v; emit "u)"
    else
      emit "lean_cstr_to_nat(\""; emit v; emit "\")"
  else
    if v < UInt32.size then
      emit v
    else if t == .usize then
      emit "((size_t)"
      emit v
      emit "ULL)"
    else
      emit v
      emit "ULL"

def emitLit (z : VarId) (t : IRType) (v : LitVal) : M Unit := do
  emitLhs z;
  match v with
  | LitVal.num v => emitNumLit t v; emitLn ";"
  | LitVal.str v =>
    emit "lean_mk_string_unchecked(";
    emit (quoteString v); emit ", ";
    emit v.utf8ByteSize; emit ", ";
    emit v.length; emitLn ");"

def emitVDecl (z : VarId) (t : IRType) (v : Expr) : M Unit :=
  match v with
  | Expr.ctor c ys      => emitCtor z t c ys
  | Expr.reset n x      => emitReset z n x
  | Expr.reuse x c u ys => emitReuse z x c u ys
  | Expr.proj c i x     => emitProj z c i x
  | Expr.uproj c i x    => emitUProj z c i x
  | Expr.sproj c n o x  => emitSProj z t c n o x
  | Expr.fap c ys       => emitFullApp z c ys
  | Expr.pap c ys       => emitPartialApp z c ys
  | Expr.ap x ys        => emitApp z x ys
  | Expr.box t' x       => emitBox z x t' t
  | Expr.unbox x        => emitUnbox z t x
  | Expr.isShared x     => emitIsShared z x
  | Expr.lit v          => emitLit z t v

def isTailCall (x : VarId) (v : Expr) (b : FnBody) : M Bool := do
  let ctx ← read;
  match v, b with
  | Expr.fap f _, FnBody.ret (.var y) => return f == ctx.mainFn && x == y
  | _, _ => pure false

def paramEqArg (p : Param) (x : Arg) : Bool :=
  match x with
  | .var x => p.x == x
  | .erased => false

/--
Given `[p_0, ..., p_{n-1}]`, `[y_0, ..., y_{n-1}]`, representing the assignments
```
p_0 := y_0,
...
p_{n-1} := y_{n-1}
```
Return true iff we have `(i, j)` where `j > i`, and `y_j == p_i`.
That is, we have
```
      p_i := y_i,
      ...
      p_j := p_i, -- p_i was overwritten above
```
-/
def overwriteParam (ps : Array Param) (ys : Array Arg) : Bool :=
  let n := ps.size;
  n.any fun i _ =>
    let p := ps[i]
    (i+1, n).anyI fun j _ _ => paramEqArg p ys[j]!

def emitTailCall (v : Expr) : M Unit :=
  match v with
  | Expr.fap _ ys => do
    let ctx ← read
    let ps := ctx.mainParams
    if h : ps.size = ys.size then
      let (ps, ys) := ps.zip ys |>.filter (fun (p, _) => !p.ty.isVoid) |>.unzip
      if overwriteParam ps ys then
        emitLn "{"
        ps.size.forM fun i _ => do
          let p := ps[i]
          let y := ys[i]!
          unless paramEqArg p y do
            emit (← toCType p.ty); emit " _tmp_"; emit i; emit " = "; emitArg y; emitLn ";"
        ps.size.forM fun i _ => do
          let p := ps[i]
          let y := ys[i]!
          unless paramEqArg p y do emit p.x; emit " = _tmp_"; emit i; emitLn ";"
        emitLn "}"
      else
        ps.size.forM fun i _ => do
          let p := ps[i]
          let y := ys[i]!
          unless paramEqArg p y do emit p.x; emit " = "; emitArg y; emitLn ";"
      emitLn "goto _start;"
    else
      throw "invalid tail call"
  | _ => throw "bug at emitTailCall"

mutual

partial def emitIf (x : VarId) (xType : IRType) (tag : Nat) (t : FnBody) (e : FnBody) : M Unit := do
  emit "if ("; emitTag x xType; emit " == "; emit tag; emitLn ")";
  emitFnBody t;
  emitLn "else";
  emitFnBody e

partial def emitCase (x : VarId) (xType : IRType) (alts : Array Alt) : M Unit :=
  match isIf alts with
  | some (tag, t, e) => emitIf x xType tag t e
  | _ => do
    emit "switch ("; emitTag x xType; emitLn ") {";
    let alts := ensureHasDefault alts;
    alts.forM fun alt => do
      match alt with
      | Alt.ctor c b  => emit "case "; emit c.cidx; emitLn ":"; emitFnBody b
      | Alt.default b => emitLn "default: "; emitFnBody b
    emitLn "}"

partial def emitBlock (b : FnBody) : M Unit := do
  match b with
  | FnBody.jdecl _ _  _ b      => emitBlock b
  | d@(FnBody.vdecl x t v b)   =>
    let ctx ← read
    if isTailCallTo ctx.mainFn d then
      emitTailCall v
    else
      emitVDecl x t v
      emitBlock b
  | FnBody.inc x n c p b       =>
    unless p do emitInc x n c
    emitBlock b
  | FnBody.dec x n c p b       =>
    unless p do emitDec x n c
    emitBlock b
  | FnBody.del x b             => emitDel x; emitBlock b
  | FnBody.setTag x i b        => emitSetTag x i; emitBlock b
  | FnBody.set x i y b         => emitSet x i y; emitBlock b
  | FnBody.uset x c i y b      => emitUSet x c i y; emitBlock b
  | FnBody.sset x c i o y t b  => emitSSet x c i o y t; emitBlock b
  | FnBody.ret x               => emit "return "; emitArg x; emitLn ";"
  | FnBody.case _ x xType alts => emitCase x xType alts
  | FnBody.jmp j xs            => emitJmp j xs
  | FnBody.unreachable         => emitLn "lean_internal_panic_unreachable();"

partial def emitJPs : FnBody → M Unit
  | FnBody.jdecl j _  v b => do emit j; emitLn ":"; emitFnBody v; emitJPs b
  | e                     => do unless e.isTerminal do emitJPs e.body

partial def emitFnBody (b : FnBody) : M Unit := do
  emitLn "{"
  let declared ← declareVars b false
  if declared then emitLn ""
  emitBlock b
  emitJPs b
  emitLn "}"

end

partial def emitStructDefn (ty : IRType) (nm : String) : M Unit := do
  emitLn (nm ++ " {")
  match ty with
  | .union _ tys =>
    emitLn "union {"
    for h : i in *...tys.size do
      emit (← toCType tys[i]); emit " c"; emit i; emitLn ";"
    assert! tys.size ≤ 256
    emitLn "} cs;"
    if (optionLike? ty).isNone then
      emitLn "uint8_t tag;"
  | .struct _ tys us ss =>
    for h : i in *...tys.size do
      if tys[i] matches .erased | .void then
        continue
      emit (← toCType tys[i]); emit " i"; emit i; emitLn ";"
    if us ≠ 0 ∨ ss ≠ 0 then
      -- Note: we keep a `size_t[0]` to ensure alignment of the scalars
      emitLn s!"size_t u[{us}];"
      emitLn s!"uint8_t s[{ss}];"
  | _ => unreachable!
  emitLn "};"

def emitUnionSwitch (n : Nat) (x : String) (branch : (i : Nat) → i < n → M Unit) : M Unit := do
  if h : n = 1 then
    branch 0 (by simp_all)
  else if h : n = 2 then
    emit "if ("; emit x; emitLn " == 0) {"
    branch 0 (by simp_all)
    emitLn "} else {"
    branch 1 (by simp_all)
    emitLn "}"
  else
    emit "switch ("; emit x; emitLn ") {"
    for h : i in *...n do
      emit "case "; emit i; emitLn ":"
      branch i (by get_elem_tactic)
      emitLn "break;"
    emitLn "}"

def emitUnionSwitchWithImpossible (n : Nat) (x : String)
    (possible : Nat → Bool)
    (branch : (i : Nat) → i < n → M Unit) : M Unit := do
  let branches : Array (Fin n) := (Array.ofFn id).filter fun i => possible i
  if h : branches.size = 1 then
    branch branches[0].1 branches[0].2
  else if h : branches.size = 2 then
    emit "if ("; emit x; emitLn " == 0) {"
    branch branches[0].1 branches[0].2
    emitLn "} else {"
    branch branches[1].1 branches[1].2
    emitLn "}"
  else
    emit "switch ("; emit x; emitLn ") {"
    for i in branches do
      emit "case "; emit i; emitLn ":"
      branch i.1 i.2
      emitLn "break;"
    emitLn "}"

def emitStructIncDecFn (ty : IRType) (id : Nat) (isInc : Bool) : M Unit := do
  let prfx := if isInc then structIncFnPrefix else structDecFnPrefix
  let call (tgt : String) (ty : IRType) := do
    if ty matches .void | .erased || ty.isScalar then
      return
    if isInc then
      emitIncOfType tgt ty 0 true "n"
    else
      emitDecOfType tgt ty 1 true
  emit "static void "; emit prfx; emit id
  emit "("; emit (structType id);
  if isInc then emitLn " x, size_t n) {" else emitLn " x) {"

  if let .union _ tys := ty then
    if let some path := optionLike? ty then
      emit "if (x"; emitPath path; emitLn " != 0) {"
      call s!"x.cs.c1" tys[1]!
      emitLn "}"
    else
      emitUnionSwitch tys.size "x.tag" fun i _ => call s!"x.cs.c{i}" tys[i]
  else if let .struct _ tys _ _ := ty then
    for h : i in *...tys.size do
      call s!"x.i{i}" tys[i]
  emitLn "}"

def emitReshapeFn (origin target : IRType) : M Unit := do
  if origin.isObj then
    emitUnboxFn target
  else
    emitBoxFn origin target

partial def compatibleReshape (origin target : IRType) : Bool :=
  match origin, target with
  | .struct _ tys _ _, .struct _ tys' _ _ =>
    tys.isEqv tys' compatibleReshape
  | .union .., .struct .. => false
  | .struct .., .union .. => false
  | _, _ => (!origin.isScalar || !target.isStruct) && (!origin.isStruct || !target.isScalar)

def emitStructReshapeFn (origin target : IRType) (id1 id2 : Nat) : M Unit := do
  if id1 == id2 then
    return
  unless compatibleReshape origin target do
    return
  emit "static "; emit (structType id2); emit " "
  emit structReshapeFnPrefix; emit id1; emit "_"; emit id2
  emit "("; emit (structType id1); emitLn " x) {"
  emit (structType id2); emitLn " y;"

  match origin, target with
  | .union _ tys, .union _ tys' =>
    let reshapeUnion (i : Nat) : M Unit := do
      emit "y.cs.c"; emit i; emit " = "
      if tys[i]!.compatibleWith tys'[i]! then
        emit "x.cs.c"; emit i; emitLn ";"
      else
        emitReshapeFn tys[i]! tys'[i]!
        emit "(x.cs.c"; emit i; emitLn ");"
    if let some path := optionLike? origin then
      let compatible := compatibleReshape tys[1]! tys'[1]!
      if !compatible then
        if let some path2 := optionLike? target then
          emit "y"; emitPath path2; emitLn " = 0;"
        else
          emitLn "y.tag = 0;"
      else
        emit "if (x"; emitPath path; emitLn "== 0) {"
        if let some path2 := optionLike? target then
          emit "y"; emitPath path2; emitLn " = 0;"
        else
          emitLn "y.tag = 0;"
        emitLn "} else {"
        if (optionLike? target).isNone then
          emitLn "y.tag = 1;"
        reshapeUnion 1
        emitLn "}"
    else if let some path := optionLike? target then
      let compatible := compatibleReshape tys[1]! tys'[1]!
      if !compatible then emit "y"; emitPath path; emitLn " = 0;" else
      emitLn "if (x.tag == 0) {"
      emit "y"; emitPath path; emitLn " = 0;"
      emitLn "} else {"
      reshapeUnion 1
      emitLn "}"
    else
      emitLn "y.tag = x.tag;"
      -- Note: through cse in the mono stage we can get "bad" reshapes
      -- where e.g. `let a : Option UInt8 := none` and `let a : Option (Option UInt8) := none`
      -- merged into one variable. In that case, ignore branches with incompatibilities.
      emitUnionSwitchWithImpossible tys.size "x.tag"
          (fun i => compatibleReshape tys[i]! tys'[i]!)
          fun i _ => reshapeUnion i
  | .struct _ tys us ss, .struct _ tys' _ _ =>
    if us ≠ 0 ∨ ss ≠ 0 then
      emit "memcpy(y.u, x.u, sizeof(size_t)*"; emit us; emit "+"; emit ss; emitLn ");"
    for h : i in *...tys.size do
      if tys'[i]! matches .erased | .void then
        continue
      if tys[i] matches .erased | .void then
        emit "y.i"; emit i; emitLn " = lean_box(0);"
      else if tys[i].compatibleWith tys'[i]! then
        emit "y.i"; emit i; emit " = x.i"; emit i; emitLn ";"
      else
        emit "y.i"; emit i; emit " = "
        emitReshapeFn tys[i] tys'[i]!
        emit "(x.i"; emit i; emitLn ");"
        if tys[i].isObj then
          -- note: for unboxing functions the calling conventions don't match up
          -- (has @& -> @&, expected owned -> owned) so we need to compensate
          -- TODO: avoid these reference counting instructions when possible
          if needsRC tys'[i]! then
            emitIncOfType s!"y.i{i}" tys'[i]! 1 true "1"
          emit "lean_dec(x.i"; emit i; emitLn ");"
  | _, _ => pure ()
  emitLn "return y;"
  emitLn "}"

def emitStructBox (ty : IRType) (cidx : Nat) (x : String) : M Unit := do
  let .struct _ tys us ss := ty | unreachable!
  if tys.isEmpty && us == 0 && ss == 0 then
    emit "y = lean_box("; emit cidx; emitLn ");"
    return
  emit "y = lean_alloc_ctor(";
  emit cidx; emit ", "; emit tys.size;
  emit ", sizeof(size_t)*"; emit us; emit "+"; emit ss
  emitLn ");"
  if us ≠ 0 ∨ ss ≠ 0 then
    emit "memcpy(lean_ctor_scalar_cptr(y), "; emit x; emit ".u, sizeof(size_t)*"
    emit us; emit "+"; emit ss; emitLn ");"
  for h : i in *...tys.size do
    emit "lean_ctor_set(y, "; emit i; emit ", "
    if tys[i] matches .erased | .void then
      emitLn "lean_box(0));"
    else if tys[i] matches .object | .tobject | .tagged then
      emit x; emit ".i"; emit i; emitLn ");"
    else
      emitBoxFn tys[i] .tobject
      emit "("; emit x; emit ".i"; emit i; emitLn "));"

def emitStructBoxFn (ty : IRType) (id : Nat) : M Unit := do
  emit "static lean_object* "
  emit structBoxFnPrefix; emit id
  emit "("; emit (structType id); emitLn " x) {"
  emitLn "lean_object* y;"
  if let .union _ tys := ty then
    if let some path := optionLike? ty then
      emitLn "if (x"; emitPath path; emit " == 0) {"
      emitLn "y = lean_box(0);"
      emitLn "} else {"
      emitStructBox tys[1]! 1 s!"x.cs.c1"
      emitLn "}"
    else
      emitUnionSwitch tys.size "x.tag" fun i _ => do
        emitStructBox tys[i] i s!"x.cs.c{i}"
  else
    emitStructBox ty 0 "x"
  emitLn "return y;"
  emitLn "}"

def emitStructUnboxFn (ty : IRType) (id : Nat) : M Unit := do
  emit "static "; emit (structType id); emit " "
  emit structUnboxFnPrefix; emit id
  emitLn "(lean_object* x) {"
  emit (structType id); emitLn " y;"

  if let .union _ tys := ty then
    if let some path := optionLike? ty then
      emitLn "if (lean_is_scalar(x)) {"
      emit "y"; emitPath path; emitLn " = 0;"
      emitLn "} else {"
      emit "y.cs.c1 = "
      emitUnboxFn tys[1]!
      emitLn "(x);"
      emitLn "}"
    else
      emitLn "y.tag = lean_obj_tag(x);"
      emitUnionSwitch tys.size "y.tag" fun i _ => do
        emit "y.cs.c"; emit i; emit " = "
        emitUnboxFn tys[i]
        emitLn "(x);"
  else
    let .struct _ tys us ss := ty | unreachable!
    if us ≠ 0 ∨ ss ≠ 0 then
      emit "memcpy(y.u, lean_ctor_scalar_cptr(x), sizeof(size_t)*"
      emit us; emit "+"; emit ss; emitLn ");"
    for h : i in *...tys.size do
      if tys[i] matches .erased | .void then
        continue
      else if tys[i] matches .object | .tobject | .tagged then
        emit "y.i"; emit i; emit " = lean_ctor_get(x, "; emit i; emitLn ");"
      else
        emit "y.i"; emit i; emit " = "
        emitUnboxFn tys[i]
        emit "(lean_ctor_get(x, "; emit i; emitLn "));"
  emitLn "return y;"
  emitLn "}"

def emitStructDeclsFor (id : Nat) (info : StructTypeInfo) : M Unit := do
  let ty := info.type
  emitStructDefn ty (structType id)
  if needsRC ty then
    emitStructIncDecFn ty id true
    emitStructIncDecFn ty id false
  emitStructBoxFn ty id
  emitStructUnboxFn ty id

def emitStructDecls (cont : M α) : M α := do
  let env ← getEnv
  let decls := getDecls env
  let (data, lookup) := collectStructTypes decls
  withReader (fun ctx => { ctx with structs := lookup }) do
    let mut emitted : Std.HashSet Nat := {}
    for h : i in *...data.size do
      emitStructDeclsFor i data[i]
    for h : i in *...data.size do
      let info := data[i]
      for reshape in info.reshapes do
        emitStructReshapeFn info.type data[reshape]!.type i reshape
    cont

def emitDeclAux (d : Decl) : M Unit := do
  let env ← getEnv
  let (varTypes, jpMap) := mkVarJPMaps d
  withReader (fun ctx => { ctx with jpMap, varTypes }) do
  unless hasInitAttr env d.name do
    match d with
    | .fdecl (f := f) (xs := xs) (type := t) (body := b) .. =>
      let baseName ← toCName f;
      if xs.size == 0 then
        emit "static "
      else
        emit "LEAN_EXPORT "  -- make symbol visible to the interpreter
      emit (← toCType t); emit " ";
      if xs.size > 0 then
        let xs := xs.filter (fun p => !p.ty.isVoid)
        emit baseName;
        emit "(";
        if xs.size > closureMaxArgs && isBoxedName d.name then
          emit "lean_object** _args"
        else
          emitSpreadArgs xs true
        emit ")"
      else
        emit ("_init_" ++ baseName ++ "()")
      emitLn " {";
      if xs.size > closureMaxArgs && isBoxedName d.name then
        xs.size.forM fun i _ => do
          let x := xs[i]!
          emit "lean_object* "; emit x.x; emit " = _args["; emit i; emitLn "];"
      emitSpreads xs
      emitLn "_start:";
      withReader (fun ctx => { ctx with mainFn := f, mainParams := xs }) (emitFnBody b);
      emitLn "}"
    | _ => pure ()

def emitDecl (d : Decl) : M Unit := do
  -- this is a bit of weird optimization step since we are not allowed to run it for
  -- interpreted code, so we run it here instead
  let d := d.normalizeIds -- ensure we don't have gaps in the variable indices
  let d := StructRC.visitDecl d
  try
    emitDeclAux d
  catch err =>
    throw s!"{err}\ncompiling:\n{d}"

def emitFns : M Unit := do
  let env ← getEnv;
  let decls := getDecls env;
  decls.reverse.forM emitDecl

def emitMarkPersistent (d : Decl) (n : Name) : M Unit := do
  if d.resultType.isObj then
    emit "lean_mark_persistent("
    emitCName n
    emitLn ");"

open ExplicitBoxing in
def emitDeclInit (d : Decl) : M Unit := do
  let env ← getEnv
  let n := d.name
  if isIOUnitInitFn env n then
    if isIOUnitBuiltinInitFn env n then
      emit "if (builtin) {"
    emit "res = "; emitCName (mkBoxedName n); emitLn "(lean_box(0));"
    emitLn "if (lean_io_result_is_error(res)) return res;"
    emitLn "lean_dec_ref(res);"
    if isIOUnitBuiltinInitFn env n then
      emit "}"
  else if d.params.size == 0 then
    match getInitFnNameFor? env d.name with
    | some initFn =>
      if getBuiltinInitFnNameFor? env d.name |>.isSome then
        emit "if (builtin) {"
      emit "res = "; emitCName (mkBoxedName initFn); emitLn "(lean_box(0));"
      emitLn "if (lean_io_result_is_error(res)) return res;"
      emitCName n
      if d.resultType.isScalarOrStruct then
        emit " = "
        emitUnboxFn d.resultType
        emitLn "(lean_io_result_get_value(res));"
      else
        emitLn " = lean_io_result_get_value(res);"
        emitMarkPersistent d n
      emitLn "lean_dec_ref(res);"
      if getBuiltinInitFnNameFor? env d.name |>.isSome then
        emit "}"
    | _ =>
      emitCName n; emit " = "; emitCInitName n; emitLn "();"; emitMarkPersistent d n

def emitInitFn : M Unit := do
  let env ← getEnv
  let impInitFns ← env.imports.mapM fun imp => do
    let some idx := env.getModuleIdx? imp.module
      | throw "(internal) import without module index" -- should be unreachable
    let pkg? := env.getModulePackageByIdx? idx
    let fn := mkModuleInitializationFunctionName imp.module pkg?
    emitLn s!"lean_object* {fn}(uint8_t builtin);"
    return fn
  emitLns [
    "static bool _G_initialized = false;",
    s!"LEAN_EXPORT lean_object* {← getModInitFn}(uint8_t builtin) \{",
    "lean_object * res;",
    "if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));",
    "_G_initialized = true;"
  ]
  impInitFns.forM fun fn => emitLns [
    s!"res = {fn}(builtin);",
    "if (lean_io_result_is_error(res)) return res;",
    "lean_dec_ref(res);"]
  let decls := getDecls env
  decls.reverse.forM emitDeclInit
  emitLns ["return lean_io_result_mk_ok(lean_box(0));", "}"]

def main : M Unit := do
  emitFileHeader
  emitLn "void* memcpy(void* restrict, const void* restrict, size_t);"
  emitStructDecls do
  emitFnDecls
  emitFns
  emitInitFn
  emitMainFnIfNeeded
  emitFileFooter

end EmitC

def emitC (env : Environment) (modName : Name) : Except String String :=
  match EmitC.main { env, modName } |>.run "" with
  | EStateM.Result.ok    _   s => Except.ok s
  | EStateM.Result.error err _ => Except.error err

end Lean.IR
