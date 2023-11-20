/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Runtime
import Lean.Compiler.NameMangling
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.SimpCase
import Lean.Compiler.IR.Boxing

namespace Lean.IR.EmitC
open ExplicitBoxing (requiresBoxedVersion mkBoxedName isBoxedName)

def leanMainFn := "_lean_main"

structure Context where
  env        : Environment
  modName    : Name
  jpMap      : JPParamsMap := {}
  mainFn     : FunId := default
  mainParams : Array Param := #[]

abbrev M := ReaderT Context (EStateM String String)

def getEnv : M Environment := Context.env <$> read
def getModName : M Name := Context.modName <$> read
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
  | Arg.var x => toString x
  | _         => "lean_box(0)"

def emitArg (x : Arg) : M Unit :=
  emit (argToCString x)

def toCType : IRType → String
  | IRType.float      => "double"
  | IRType.uint8      => "uint8_t"
  | IRType.uint16     => "uint16_t"
  | IRType.uint32     => "uint32_t"
  | IRType.uint64     => "uint64_t"
  | IRType.usize      => "size_t"
  | IRType.object     => "lean_object*"
  | IRType.tobject    => "lean_object*"
  | IRType.irrelevant => "lean_object*"
  | IRType.struct _ _ => panic! "not implemented yet"
  | IRType.union _ _  => panic! "not implemented yet"

def throwInvalidExportName {α : Type} (n : Name) : M α :=
  throw s!"invalid export name '{n}'"

def toCName (n : Name) : M String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => pure s
  | some _                   => throwInvalidExportName n
  | none                     => if n == `main then pure leanMainFn else pure n.mangle

def emitCName (n : Name) : M Unit :=
  toCName n >>= emit

def toCInitName (n : Name) : M String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => return "_init_" ++ s
  | some _                   => throwInvalidExportName n
  | none                     => pure ("_init_" ++ n.mangle)

def emitCInitName (n : Name) : M Unit :=
  toCInitName n >>= emit

def emitFnDeclAux (decl : Decl) (cppBaseName : String) (isExternal : Bool) : M Unit := do
  let ps := decl.params
  let env ← getEnv
  if ps.isEmpty then
    if isClosedTermName env decl.name then emit "static "
    else if isExternal then emit "extern "
    else emit "LEAN_EXPORT "
  else
    if !isExternal then emit "LEAN_EXPORT "
  emit (toCType decl.resultType ++ " " ++ cppBaseName)
  unless ps.isEmpty do
    emit "("
    -- We omit irrelevant parameters for extern constants
    let ps := if isExternC env decl.name then ps.filter (fun p => !p.ty.isIrrelevant) else ps
    if ps.size > closureMaxArgs && isBoxedName decl.name then
      emit "lean_object**"
    else
      ps.size.forM fun i => do
        if i > 0 then emit ", "
        emit (toCType ps[i]!.ty)
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
  #endif
  lean_object* in; lean_object* res;";
    if usesLeanAPI then
      emitLn "lean_initialize();"
    else
      emitLn "lean_initialize_runtime_module();"
    let modName ← getModName
    /- We disable panic messages because they do not mesh well with extracted closed terms.
       See issue #534. We can remove this workaround after we implement issue #467. -/
    emitLn "lean_set_panic_messages(false);"
    emitLn ("res = " ++ mkModuleInitializationFunctionName modName ++ "(1 /* builtin */, lean_io_mk_world());")
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
      emitLn ("res = " ++ leanMainFn ++ "(in, lean_io_mk_world());")
    else
      emitLn ("res = " ++ leanMainFn ++ "(lean_io_mk_world());")
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
  match ctx.jpMap.find? j with
  | some ps => pure ps
  | none    => throw "unknown join point"

def declareVar (x : VarId) (t : IRType) : M Unit := do
  emit (toCType t); emit " "; emit x; emit "; "

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

def emitTag (x : VarId) (xType : IRType) : M Unit := do
  if xType.isObj then do
    emit "lean_obj_tag("; emit x; emit ")"
  else
    emit x

def isIf (alts : Array Alt) : Option (Nat × FnBody × FnBody) :=
  if alts.size != 2 then none
  else match alts[0]! with
    | Alt.ctor c b => some (c.cidx, b, alts[1]!.body)
    | _            => none

def emitInc (x : VarId) (n : Nat) (checkRef : Bool) : M Unit := do
  emit $
    if checkRef then (if n == 1 then "lean_inc" else "lean_inc_n")
    else (if n == 1 then "lean_inc_ref" else "lean_inc_ref_n")
  emit "("; emit x
  if n != 1 then emit ", "; emit n
  emitLn ");"

def emitDec (x : VarId) (n : Nat) (checkRef : Bool) : M Unit := do
  emit (if checkRef then "lean_dec" else "lean_dec_ref");
  emit "("; emit x;
  if n != 1 then emit ", "; emit n
  emitLn ");"

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

def emitUSet (x : VarId) (n : Nat) (y : VarId) : M Unit := do
  emit "lean_ctor_set_usize("; emit x; emit ", "; emit n; emit ", "; emit y; emitLn ");"

def emitSSet (x : VarId) (n : Nat) (offset : Nat) (y : VarId) (t : IRType) : M Unit := do
  match t with
  | IRType.float  => emit "lean_ctor_set_float"
  | IRType.uint8  => emit "lean_ctor_set_uint8"
  | IRType.uint16 => emit "lean_ctor_set_uint16"
  | IRType.uint32 => emit "lean_ctor_set_uint32"
  | IRType.uint64 => emit "lean_ctor_set_uint64"
  | _             => throw "invalid instruction";
  emit "("; emit x; emit ", "; emitOffset n offset; emit ", "; emit y; emitLn ");"

def emitJmp (j : JoinPointId) (xs : Array Arg) : M Unit := do
  let ps ← getJPParams j
  unless xs.size == ps.size do throw "invalid goto"
  xs.size.forM fun i => do
    let p := ps[i]!
    let x := xs[i]!
    emit p.x; emit " = "; emitArg x; emitLn ";"
  emit "goto "; emit j; emitLn ";"

def emitLhs (z : VarId) : M Unit := do
  emit z; emit " = "

def emitArgs (ys : Array Arg) : M Unit :=
  ys.size.forM fun i => do
    if i > 0 then emit ", "
    emitArg ys[i]!

def emitCtorScalarSize (usize : Nat) (ssize : Nat) : M Unit := do
  if usize == 0 then emit ssize
  else if ssize == 0 then emit "sizeof(size_t)*"; emit usize
  else emit "sizeof(size_t)*"; emit usize; emit " + "; emit ssize

def emitAllocCtor (c : CtorInfo) : M Unit := do
  emit "lean_alloc_ctor("; emit c.cidx; emit ", "; emit c.size; emit ", "
  emitCtorScalarSize c.usize c.ssize; emitLn ");"

def emitCtorSetArgs (z : VarId) (ys : Array Arg) : M Unit :=
  ys.size.forM fun i => do
    emit "lean_ctor_set("; emit z; emit ", "; emit i; emit ", "; emitArg ys[i]!; emitLn ");"

def emitCtor (z : VarId) (c : CtorInfo) (ys : Array Arg) : M Unit := do
  emitLhs z;
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    emit "lean_box("; emit c.cidx; emitLn ");"
  else do
    emitAllocCtor c; emitCtorSetArgs z ys

def emitReset (z : VarId) (n : Nat) (x : VarId) : M Unit := do
  emit "if (lean_is_exclusive("; emit x; emitLn ")) {";
  n.forM fun i => do
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

def emitProj (z : VarId) (i : Nat) (x : VarId) : M Unit := do
  emitLhs z; emit "lean_ctor_get("; emit x; emit ", "; emit i; emitLn ");"

def emitUProj (z : VarId) (i : Nat) (x : VarId) : M Unit := do
  emitLhs z; emit "lean_ctor_get_usize("; emit x; emit ", "; emit i; emitLn ");"

def emitSProj (z : VarId) (t : IRType) (n offset : Nat) (x : VarId) : M Unit := do
  emitLhs z;
  match t with
  | IRType.float  => emit "lean_ctor_get_float"
  | IRType.uint8  => emit "lean_ctor_get_uint8"
  | IRType.uint16 => emit "lean_ctor_get_uint16"
  | IRType.uint32 => emit "lean_ctor_get_uint32"
  | IRType.uint64 => emit "lean_ctor_get_uint64"
  | _             => throw "invalid instruction"
  emit "("; emit x; emit ", "; emitOffset n offset; emitLn ");"

def toStringArgs (ys : Array Arg) : List String :=
  ys.toList.map argToCString

def emitSimpleExternalCall (f : String) (ps : Array Param) (ys : Array Arg) : M Unit := do
  emit f; emit "("
  -- We must remove irrelevant arguments to extern calls.
  discard <| ys.size.foldM
    (fun i (first : Bool) =>
      if ps[i]!.ty.isIrrelevant then
        pure first
      else do
        unless first do emit ", "
        emitArg ys[i]!
        pure false)
    true
  emitLn ");"
  pure ()

def emitExternCall (f : FunId) (ps : Array Param) (extData : ExternAttrData) (ys : Array Arg) : M Unit :=
  match getExternEntryFor extData `c with
  | some (ExternEntry.standard _ extFn) => emitSimpleExternalCall extFn ps ys
  | some (ExternEntry.inline _ pat)     => do emit (expandExternPattern pat (toStringArgs ys)); emitLn ";"
  | some (ExternEntry.foreign _ extFn)  => emitSimpleExternalCall extFn ps ys
  | _ => throw s!"failed to emit extern application '{f}'"

def emitFullApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
  emitLhs z
  let decl ← getDecl f
  match decl with
  | Decl.extern _ ps _ extData => emitExternCall f ps extData ys
  | _ =>
    emitCName f
    if ys.size > 0 then emit "("; emitArgs ys; emit ")"
    emitLn ";"

def emitPartialApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
  let decl ← getDecl f
  let arity := decl.params.size;
  emitLhs z; emit "lean_alloc_closure((void*)("; emitCName f; emit "), "; emit arity; emit ", "; emit ys.size; emitLn ");";
  ys.size.forM fun i => do
    let y := ys[i]!
    emit "lean_closure_set("; emit z; emit ", "; emit i; emit ", "; emitArg y; emitLn ");"

def emitApp (z : VarId) (f : VarId) (ys : Array Arg) : M Unit :=
  if ys.size > closureMaxArgs then do
    emit "{ lean_object* _aargs[] = {"; emitArgs ys; emitLn "};";
    emitLhs z; emit "lean_apply_m("; emit f; emit ", "; emit ys.size; emitLn ", _aargs); }"
  else do
    emitLhs z; emit "lean_apply_"; emit ys.size; emit "("; emit f; emit ", "; emitArgs ys; emitLn ");"

def emitBoxFn (xType : IRType) : M Unit :=
  match xType with
  | IRType.usize  => emit "lean_box_usize"
  | IRType.uint32 => emit "lean_box_uint32"
  | IRType.uint64 => emit "lean_box_uint64"
  | IRType.float  => emit "lean_box_float"
  | _             => emit "lean_box"

def emitBox (z : VarId) (x : VarId) (xType : IRType) : M Unit := do
  emitLhs z; emitBoxFn xType; emit "("; emit x; emitLn ");"

def emitUnbox (z : VarId) (t : IRType) (x : VarId) : M Unit := do
  emitLhs z
  emit (getUnboxOpName t)
  emit "("; emit x; emitLn ");"

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
    emit v

def emitLit (z : VarId) (t : IRType) (v : LitVal) : M Unit := do
  emitLhs z;
  match v with
  | LitVal.num v => emitNumLit t v; emitLn ";"
  | LitVal.str v => emit "lean_mk_string_from_bytes("; emit (quoteString v); emit ", "; emit v.utf8ByteSize; emitLn ");"

def emitVDecl (z : VarId) (t : IRType) (v : Expr) : M Unit :=
  match v with
  | Expr.ctor c ys      => emitCtor z c ys
  | Expr.reset n x      => emitReset z n x
  | Expr.reuse x c u ys => emitReuse z x c u ys
  | Expr.proj i x       => emitProj z i x
  | Expr.uproj i x      => emitUProj z i x
  | Expr.sproj n o x    => emitSProj z t n o x
  | Expr.fap c ys       => emitFullApp z c ys
  | Expr.pap c ys       => emitPartialApp z c ys
  | Expr.ap x ys        => emitApp z x ys
  | Expr.box t x        => emitBox z x t
  | Expr.unbox x        => emitUnbox z t x
  | Expr.isShared x     => emitIsShared z x
  | Expr.lit v          => emitLit z t v

def isTailCall (x : VarId) (v : Expr) (b : FnBody) : M Bool := do
  let ctx ← read;
  match v, b with
  | Expr.fap f _, FnBody.ret (Arg.var y) => return f == ctx.mainFn && x == y
  | _, _ => pure false

def paramEqArg (p : Param) (x : Arg) : Bool :=
  match x with
  | Arg.var x => p.x == x
  | _ => false

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
  n.any fun i =>
    let p := ps[i]!
    (i+1, n).anyI fun j => paramEqArg p ys[j]!

def emitTailCall (v : Expr) : M Unit :=
  match v with
  | Expr.fap _ ys => do
    let ctx ← read
    let ps := ctx.mainParams
    unless ps.size == ys.size do throw "invalid tail call"
    if overwriteParam ps ys then
      emitLn "{"
      ps.size.forM fun i => do
        let p := ps[i]!
        let y := ys[i]!
        unless paramEqArg p y do
          emit (toCType p.ty); emit " _tmp_"; emit i; emit " = "; emitArg y; emitLn ";"
      ps.size.forM fun i => do
        let p := ps[i]!
        let y := ys[i]!
        unless paramEqArg p y do emit p.x; emit " = _tmp_"; emit i; emitLn ";"
      emitLn "}"
    else
      ys.size.forM fun i => do
        let p := ps[i]!
        let y := ys[i]!
        unless paramEqArg p y do emit p.x; emit " = "; emitArg y; emitLn ";"
    emitLn "goto _start;"
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
  | FnBody.uset x i y b        => emitUSet x i y; emitBlock b
  | FnBody.sset x i o y t b    => emitSSet x i o y t; emitBlock b
  | FnBody.mdata _ b           => emitBlock b
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

def emitDeclAux (d : Decl) : M Unit := do
  let env ← getEnv
  let (_, jpMap) := mkVarJPMaps d
  withReader (fun ctx => { ctx with jpMap := jpMap }) do
  unless hasInitAttr env d.name do
    match d with
    | .fdecl (f := f) (xs := xs) (type := t) (body := b) .. =>
      let baseName ← toCName f;
      if xs.size == 0 then
        emit "static "
      else
        emit "LEAN_EXPORT "  -- make symbol visible to the interpreter
      emit (toCType t); emit " ";
      if xs.size > 0 then
        emit baseName;
        emit "(";
        if xs.size > closureMaxArgs && isBoxedName d.name then
          emit "lean_object** _args"
        else
          xs.size.forM fun i => do
            if i > 0 then emit ", "
            let x := xs[i]!
            emit (toCType x.ty); emit " "; emit x.x
        emit ")"
      else
        emit ("_init_" ++ baseName ++ "()")
      emitLn " {";
      if xs.size > closureMaxArgs && isBoxedName d.name then
        xs.size.forM fun i => do
          let x := xs[i]!
          emit "lean_object* "; emit x.x; emit " = _args["; emit i; emitLn "];"
      emitLn "_start:";
      withReader (fun ctx => { ctx with mainFn := f, mainParams := xs }) (emitFnBody b);
      emitLn "}"
    | _ => pure ()

def emitDecl (d : Decl) : M Unit := do
  let d := d.normalizeIds; -- ensure we don't have gaps in the variable indices
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

def emitDeclInit (d : Decl) : M Unit := do
  let env ← getEnv
  let n := d.name
  if isIOUnitInitFn env n then
    if isIOUnitBuiltinInitFn env n then
      emit "if (builtin) {"
    emit "res = "; emitCName n; emitLn "(lean_io_mk_world());"
    emitLn "if (lean_io_result_is_error(res)) return res;"
    emitLn "lean_dec_ref(res);"
    if isIOUnitBuiltinInitFn env n then
      emit "}"
  else if d.params.size == 0 then
    match getInitFnNameFor? env d.name with
    | some initFn =>
      if getBuiltinInitFnNameFor? env d.name |>.isSome then
        emit "if (builtin) {"
      emit "res = "; emitCName initFn; emitLn "(lean_io_mk_world());"
      emitLn "if (lean_io_result_is_error(res)) return res;"
      emitCName n
      if d.resultType.isScalar then
        emitLn (" = " ++ getUnboxOpName d.resultType ++ "(lean_io_result_get_value(res));")
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
  let modName ← getModName
  env.imports.forM fun imp => emitLn ("lean_object* " ++ mkModuleInitializationFunctionName imp.module ++ "(uint8_t builtin, lean_object*);")
  emitLns [
    "static bool _G_initialized = false;",
    "LEAN_EXPORT lean_object* " ++ mkModuleInitializationFunctionName modName ++ "(uint8_t builtin, lean_object* w) {",
    "lean_object * res;",
    "if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));",
    "_G_initialized = true;"
  ]
  env.imports.forM fun imp => emitLns [
    "res = " ++ mkModuleInitializationFunctionName imp.module ++ "(builtin, lean_io_mk_world());",
    "if (lean_io_result_is_error(res)) return res;",
    "lean_dec_ref(res);"]
  let decls := getDecls env
  decls.reverse.forM emitDeclInit
  emitLns ["return lean_io_result_mk_ok(lean_box(0));", "}"]

def main : M Unit := do
  emitFileHeader
  emitFnDecls
  emitFns
  emitInitFn
  emitMainFnIfNeeded
  emitFileFooter

end EmitC

@[export lean_ir_emit_c]
def emitC (env : Environment) (modName : Name) : Except String String :=
  match (EmitC.main { env := env, modName := modName }).run "" with
  | EStateM.Result.ok    _   s => Except.ok s
  | EStateM.Result.error err _ => Except.error err

end Lean.IR
