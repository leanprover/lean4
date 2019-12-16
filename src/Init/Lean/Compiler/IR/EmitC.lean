/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Conditional
import Init.Lean.Runtime
import Init.Lean.Compiler.NameMangling
import Init.Lean.Compiler.ExportAttr
import Init.Lean.Compiler.InitAttr
import Init.Lean.Compiler.IR.CompilerM
import Init.Lean.Compiler.IR.EmitUtil
import Init.Lean.Compiler.IR.NormIds
import Init.Lean.Compiler.IR.SimpCase
import Init.Lean.Compiler.IR.Boxing

namespace Lean
namespace IR
open ExplicitBoxing (requiresBoxedVersion mkBoxedName isBoxedName)
namespace EmitC

def leanMainFn := "_lean_main"

structure Context :=
(env        : Environment)
(modName    : Name)
(jpMap      : JPParamsMap := {})
(mainFn     : FunId := arbitrary _)
(mainParams : Array Param := #[])

abbrev M := ReaderT Context (EStateM String String)

def getEnv : M Environment := Context.env <$> read
def getModName : M Name := Context.modName <$> read
def getDecl (n : Name) : M Decl := do
env ← getEnv;
match findEnvDecl env n with
| some d => pure d
| none   => throw ("unknown declaration '" ++ toString n ++ "'")

@[inline] def emit {α : Type} [HasToString α] (a : α) : M Unit :=
modify (fun out => out ++ toString a)

@[inline] def emitLn {α : Type} [HasToString α] (a : α) : M Unit :=
emit a *> emit "\n"

def emitLns {α : Type} [HasToString α] (as : List α) : M Unit :=
as.forM $ fun a => emitLn a

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
throw ("invalid export name '" ++ toString n ++ "'")

def toCName (n : Name) : M String := do
env ← getEnv;
-- TODO: we should support simple export names only
match getExportNameFor env n with
| some (Name.str Name.anonymous s _) => pure s
| some _                             => throwInvalidExportName n
| none                               => if n == `main then pure leanMainFn else pure n.mangle

def emitCName (n : Name) : M Unit :=
toCName n >>= emit

def toCInitName (n : Name) : M String := do
env ← getEnv;
-- TODO: we should support simple export names only
match getExportNameFor env n with
| some (Name.str Name.anonymous s _) => pure $ "_init_" ++ s
| some _                             => throwInvalidExportName n
| none                               => pure ("_init_" ++ n.mangle)

def emitCInitName (n : Name) : M Unit :=
toCInitName n >>= emit

def emitFnDeclAux (decl : Decl) (cppBaseName : String) (addExternForConsts : Bool) : M Unit := do
let ps := decl.params;
env ← getEnv;
when (ps.isEmpty && addExternForConsts) (emit "extern ");
emit (toCType decl.resultType ++ " " ++ cppBaseName);
unless (ps.isEmpty) $ do {
  emit "(";
  -- We omit irrelevant parameters for extern constants
  let ps := if isExternC env decl.name then ps.filter (fun p => !p.ty.isIrrelevant) else ps;
  if ps.size > closureMaxArgs && isBoxedName decl.name then
    emit "lean_object**"
  else
    ps.size.forM $ fun i => do {
      when (i > 0) (emit ", ");
      emit (toCType (ps.get! i).ty)
    };
  emit ")"
};
emitLn ";"

def emitFnDecl (decl : Decl) (addExternForConsts : Bool) : M Unit := do
cppBaseName ← toCName decl.name;
emitFnDeclAux decl cppBaseName addExternForConsts

def emitExternDeclAux (decl : Decl) (cNameStr : String) : M Unit := do
let cName := mkNameSimple cNameStr;
env ← getEnv;
let extC := isExternC env decl.name;
emitFnDeclAux decl cNameStr (!extC)

def emitFnDecls : M Unit := do
env ← getEnv;
let decls := getDecls env;
let modDecls  : NameSet := decls.foldl (fun s d => s.insert d.name) {};
let usedDecls : NameSet := decls.foldl (fun s d => collectUsedDecls env d (s.insert d.name)) {};
let usedDecls := usedDecls.toList;
usedDecls.forM $ fun n => do
  decl ← getDecl n;
  match getExternNameFor env `c decl.name with
  | some cName => emitExternDeclAux decl cName
  | none       => emitFnDecl decl (!modDecls.contains n)

def emitMainFn : M Unit := do
d ← getDecl `main;
match d with
| Decl.fdecl f xs t b => do
  unless (xs.size == 2 || xs.size == 1) (throw "invalid main function, incorrect arity when generating code");
  env ← getEnv;
  let usesLeanAPI := usesLeanNamespace env d;
  if usesLeanAPI then
     emitLn "void lean_initialize();"
  else
     emitLn "void lean_initialize_runtime_module();";
  emitLn "int main(int argc, char ** argv) {\nlean_object* in; lean_object* res;";
  if usesLeanAPI then
    emitLn "lean_initialize();"
  else
    emitLn "lean_initialize_runtime_module();";
  modName ← getModName;
  emitLn ("res = initialize_" ++ (modName.mangle "") ++ "(lean_io_mk_world());");
  emitLns ["lean_io_mark_end_initialization();",
           "if (lean_io_result_is_ok(res)) {",
           "lean_dec_ref(res);",
           "lean_init_task_manager();"];
  if xs.size == 2 then do {
    emitLns ["in = lean_box(0);",
             "int i = argc;",
             "while (i > 1) {",
             " lean_object* n;",
             " i--;",
             " n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);",
             " in = n;",
            "}"];
    emitLn ("res = " ++ leanMainFn ++ "(in, lean_io_mk_world());")
  } else do {
    emitLn ("res = " ++ leanMainFn ++ "(lean_io_mk_world());")
  };
  emitLn "}";
  emitLns ["if (lean_io_result_is_ok(res)) {",
           "  int ret = lean_unbox(lean_io_result_get_value(res));",
           "  lean_dec_ref(res);",
           "  return ret;",
           "} else {",
           "  lean_io_result_show_error(res);",
           "  lean_dec_ref(res);",
           "  return 1;",
           "}"];
  emitLn "}"
| other => throw "function declaration expected"

def hasMainFn : M Bool := do
env ← getEnv;
let decls := getDecls env;
pure $ decls.any (fun d => d.name == `main)

def emitMainFnIfNeeded : M Unit :=
whenM hasMainFn emitMainFn

def emitFileHeader : M Unit := do
env ← getEnv;
modName ← getModName;
emitLn "// Lean compiler output";
emitLn ("// Module: " ++ toString modName);
emit "// Imports:";
env.imports.forM $ fun m => emit (" " ++ toString m);
emitLn "";
emitLn "#include \"runtime/lean.h\"";
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
throw ("unknown variable '" ++ toString x ++ "'")

def getJPParams (j : JoinPointId) : M (Array Param) := do
ctx ← read;
match ctx.jpMap.find? j with
| some ps => pure ps
| none    => throw "unknown join point"

def declareVar (x : VarId) (t : IRType) : M Unit := do
emit (toCType t); emit " "; emit x; emit "; "

def declareParams (ps : Array Param) : M Unit :=
ps.forM $ fun p => declareVar p.x p.ty

partial def declareVars : FnBody → Bool → M Bool
| e@(FnBody.vdecl x t _ b), d => do
  ctx ← read;
  if isTailCallTo ctx.mainFn e then
    pure d
  else
    declareVar x t *> declareVars b true
| FnBody.jdecl j xs _ b,    d => declareParams xs *> declareVars b (d || xs.size > 0)
| e,                        d => if e.isTerminal then pure d else declareVars e.body d

def emitTag (x : VarId) (xType : IRType) : M Unit := do
if xType.isObj then do
  emit "lean_obj_tag("; emit x; emit ")"
else
  emit x

def isIf (alts : Array Alt) : Option (Nat × FnBody × FnBody) :=
if alts.size != 2 then none
else match alts.get! 0 with
  | Alt.ctor c b => some (c.cidx, b, (alts.get! 1).body)
  | _            => none

def emitIf (emitBody : FnBody → M Unit) (x : VarId) (xType : IRType) (tag : Nat) (t : FnBody) (e : FnBody) : M Unit := do
emit "if ("; emitTag x xType; emit " == "; emit tag; emitLn ")";
emitBody t;
emitLn "else";
emitBody e

def emitCase (emitBody : FnBody → M Unit) (x : VarId) (xType : IRType) (alts : Array Alt) : M Unit :=
match isIf alts with
| some (tag, t, e) => emitIf emitBody x xType tag t e
| _ => do
  emit "switch ("; emitTag x xType; emitLn ") {";
  let alts := ensureHasDefault alts;
  alts.forM $ fun alt => match alt with
    | Alt.ctor c b  => emit "case " *> emit c.cidx *> emitLn ":" *> emitBody b
    | Alt.default b => emitLn "default: " *> emitBody b;
  emitLn "}"

def emitInc (x : VarId) (n : Nat) (checkRef : Bool) : M Unit := do
emit $
  if checkRef then (if n == 1 then "lean_inc" else "lean_inc_n")
  else (if n == 1 then "lean_inc_ref" else "lean_inc_ref_n");
emit "(" *> emit x;
when (n != 1) (emit ", " *> emit n);
emitLn ");"

def emitDec (x : VarId) (n : Nat) (checkRef : Bool) : M Unit := do
emit (if checkRef then "lean_dec" else "lean_dec_ref");
emit "("; emit x;
when (n != 1) (do emit ", "; emit n);
emitLn ");"

def emitDel (x : VarId) : M Unit := do
emit "lean_free_object("; emit x; emitLn ");"

def emitSetTag (x : VarId) (i : Nat) : M Unit := do
emit "lean_ctor_set_tag("; emit x; emit ", "; emit i; emitLn ");"

def emitSet (x : VarId) (i : Nat) (y : Arg) : M Unit := do
emit "lean_ctor_set("; emit x; emit ", "; emit i; emit ", "; emitArg y; emitLn ");"

def emitOffset (n : Nat) (offset : Nat) : M Unit :=
if n > 0 then do
  emit "sizeof(void*)*"; emit n;
  when (offset > 0) (emit " + " *> emit offset)
else
  emit offset

def emitUSet (x : VarId) (n : Nat) (y : VarId) : M Unit := do
emit "lean_ctor_set_usize("; emit x; emit ", "; emit n; emit ", "; emit y; emitLn ");"

def emitSSet (x : VarId) (n : Nat) (offset : Nat) (y : VarId) (t : IRType) : M Unit := do
match t with
| IRType.float  => throw "floats are not supported yet"
| IRType.uint8  => emit "lean_ctor_set_uint8"
| IRType.uint16 => emit "lean_ctor_set_uint16"
| IRType.uint32 => emit "lean_ctor_set_uint32"
| IRType.uint64 => emit "lean_ctor_set_uint64"
| _             => throw "invalid instruction";
emit "("; emit x; emit ", "; emitOffset n offset; emit ", "; emit y; emitLn ");"

def emitJmp (j : JoinPointId) (xs : Array Arg) : M Unit := do
ps ← getJPParams j;
unless (xs.size == ps.size) (throw "invalid goto");
xs.size.forM $ fun i => do {
  let p := ps.get! i;
  let x := xs.get! i;
  emit p.x; emit " = "; emitArg x; emitLn ";"
};
emit "goto "; emit j; emitLn ";"

def emitLhs (z : VarId) : M Unit := do
emit z; emit " = "

def emitArgs (ys : Array Arg) : M Unit :=
ys.size.forM $ fun i => do
  when (i > 0) (emit ", ");
  emitArg (ys.get! i)

def emitCtorScalarSize (usize : Nat) (ssize : Nat) : M Unit :=
if usize == 0 then emit ssize
else if ssize == 0 then emit "sizeof(size_t)*" *> emit usize
else emit "sizeof(size_t)*" *> emit usize *> emit " + " *> emit ssize

def emitAllocCtor (c : CtorInfo) : M Unit := do
emit "lean_alloc_ctor("; emit c.cidx; emit ", "; emit c.size; emit ", ";
emitCtorScalarSize c.usize c.ssize; emitLn ");"

def emitCtorSetArgs (z : VarId) (ys : Array Arg) : M Unit :=
ys.size.forM $ fun i => do
  emit "lean_ctor_set("; emit z; emit ", "; emit i; emit ", "; emitArg (ys.get! i); emitLn ");"

def emitCtor (z : VarId) (c : CtorInfo) (ys : Array Arg) : M Unit := do
emitLhs z;
if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
  emit "lean_box("; emit c.cidx; emitLn ");"
else do
  emitAllocCtor c; emitCtorSetArgs z ys

def emitReset (z : VarId) (n : Nat) (x : VarId) : M Unit := do
emit "if (lean_is_exclusive("; emit x; emitLn ")) {";
n.forM $ fun i => do {
  emit " lean_ctor_release("; emit x; emit ", "; emit i; emitLn ");"
};
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
when updtHeader (do emit " lean_ctor_set_tag("; emit z; emit ", "; emit c.cidx; emitLn ");");
emitLn "}";
emitCtorSetArgs z ys

def emitProj (z : VarId) (i : Nat) (x : VarId) : M Unit := do
emitLhs z; emit "lean_ctor_get("; emit x; emit ", "; emit i; emitLn ");"

def emitUProj (z : VarId) (i : Nat) (x : VarId) : M Unit := do
emitLhs z; emit "lean_ctor_get_usize("; emit x; emit ", "; emit i; emitLn ");"

def emitSProj (z : VarId) (t : IRType) (n offset : Nat) (x : VarId) : M Unit := do
emitLhs z;
match t with
| IRType.float  => throw "floats are not supported yet"
| IRType.uint8  => emit "lean_ctor_get_uint8"
| IRType.uint16 => emit "lean_ctor_get_uint16"
| IRType.uint32 => emit "lean_ctor_get_uint32"
| IRType.uint64 => emit "lean_ctor_get_uint64"
| _             => throw "invalid instruction";
emit "("; emit x; emit ", "; emitOffset n offset; emitLn ");"

def toStringArgs (ys : Array Arg) : List String :=
ys.toList.map argToCString

def emitSimpleExternalCall (f : String) (ps : Array Param) (ys : Array Arg) : M Unit := do
emit f; emit "(";
-- We must remove irrelevant arguments to extern calls.
ys.size.foldM
  (fun i (first : Bool) =>
    if (ps.get! i).ty.isIrrelevant then
      pure first
    else do
      unless first (emit ", ");
      emitArg (ys.get! i);
      pure false)
  true;
emitLn ");";
pure ()

def emitExternCall (f : FunId) (ps : Array Param) (extData : ExternAttrData) (ys : Array Arg) : M Unit :=
match getExternEntryFor extData `c with
| some (ExternEntry.standard _ extFn) => emitSimpleExternalCall extFn ps ys
| some (ExternEntry.inline _ pat)     => do emit (expandExternPattern pat (toStringArgs ys)); emitLn ";"
| some (ExternEntry.foreign _ extFn)  => emitSimpleExternalCall extFn ps ys
| _ => throw ("failed to emit extern application '" ++ toString f ++ "'")

def emitFullApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
emitLhs z;
decl ← getDecl f;
match decl with
| Decl.extern _ ps _ extData => emitExternCall f ps extData ys
| _ => do emitCName f; when (ys.size > 0) (do emit "("; emitArgs ys; emit ")"); emitLn ";"

def emitPartialApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
decl ← getDecl f;
let arity := decl.params.size;
emitLhs z; emit "lean_alloc_closure((void*)("; emitCName f; emit "), "; emit arity; emit ", "; emit ys.size; emitLn ");";
ys.size.forM $ fun i => do {
  let y := ys.get! i;
  emit "lean_closure_set("; emit z; emit ", "; emit i; emit ", "; emitArg y; emitLn ");"
}

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
| IRType.float  => throw "floats are not supported yet"
| other         => emit "lean_box"

def emitBox (z : VarId) (x : VarId) (xType : IRType) : M Unit := do
emitLhs z; emitBoxFn xType; emit "("; emit x; emitLn ");"

def emitUnbox (z : VarId) (t : IRType) (x : VarId) : M Unit := do
emitLhs z;
match t with
| IRType.usize  => emit "lean_unbox_usize"
| IRType.uint32 => emit "lean_unbox_uint32"
| IRType.uint64 => emit "lean_unbox_uint64"
| IRType.float  => throw "floats are not supported yet"
| other         => emit "lean_unbox";
emit "("; emit x; emitLn ");"

def emitIsShared (z : VarId) (x : VarId) : M Unit := do
emitLhs z; emit "!lean_is_exclusive("; emit x; emitLn ");"

def emitIsTaggedPtr (z : VarId) (x : VarId) : M Unit := do
emitLhs z; emit "!lean_is_scalar("; emit x; emitLn ");"

def toHexDigit (c : Nat) : String :=
String.singleton c.digitChar

def quoteString (s : String) : String :=
let q := "\"";
let q := s.foldl
  (fun q c => q ++
    if c == '\n' then "\\n"
    else if c == '\n' then "\\t"
    else if c == '\\' then "\\\\"
    else if c == '\"' then "\\\""
    else if c.toNat <= 31 then
      "\\x" ++ toHexDigit (c.toNat / 16) ++ toHexDigit (c.toNat % 16)
    -- TODO(Leo): we should use `\unnnn` for escaping unicode characters.
    else String.singleton c)
  q;
q ++ "\""

def emitNumLit (t : IRType) (v : Nat) : M Unit :=
if t.isObj then do
  if v < uint32Sz then
    emit "lean_unsigned_to_nat(" *> emit v *> emit "u)"
  else
    emit "lean_cstr_to_nat(\"" *> emit v *> emit "\")"
else
  emit v

def emitLit (z : VarId) (t : IRType) (v : LitVal) : M Unit :=
emitLhs z *>
match v with
| LitVal.num v => emitNumLit t v *> emitLn ";"
| LitVal.str v => do emit "lean_mk_string("; emit (quoteString v); emitLn ");"

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
| Expr.isTaggedPtr x  => emitIsTaggedPtr z x
| Expr.lit v          => emitLit z t v

def isTailCall (x : VarId) (v : Expr) (b : FnBody) : M Bool := do
ctx ← read;
match v, b with
| Expr.fap f _, FnBody.ret (Arg.var y) => pure $ f == ctx.mainFn && x == y
| _, _ => pure false

def paramEqArg (p : Param) (x : Arg) : Bool :=
match x with
| Arg.var x => p.x == x
| _ => false

/-
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
n.any $ fun i =>
  let p := ps.get! i;
  (i+1, n).anyI $ fun j => paramEqArg p (ys.get! j)

def emitTailCall (v : Expr) : M Unit :=
match v with
| Expr.fap _ ys => do
  ctx ← read;
  let ps := ctx.mainParams;
  unless (ps.size == ys.size) (throw "invalid tail call");
  if overwriteParam ps ys then do {
    emitLn "{";
    ps.size.forM $ fun i => do {
      let p := ps.get! i;
      let y := ys.get! i;
      unless (paramEqArg p y) $ do {
        emit (toCType p.ty); emit " _tmp_"; emit i; emit " = "; emitArg y; emitLn ";"
      }
    };
    ps.size.forM $ fun i => do {
      let p := ps.get! i;
      let y := ys.get! i;
      unless (paramEqArg p y) (do emit p.x; emit " = _tmp_"; emit i; emitLn ";")
    };
    emitLn "}"
  } else do {
    ys.size.forM $ fun i => do {
      let p := ps.get! i;
      let y := ys.get! i;
      unless (paramEqArg p y) (do emit p.x; emit " = "; emitArg y; emitLn ";")
    }
  };
  emitLn "goto _start;"
| _ => throw "bug at emitTailCall"

partial def emitBlock (emitBody : FnBody → M Unit) : FnBody → M Unit
| FnBody.jdecl j xs v b      => emitBlock b
| d@(FnBody.vdecl x t v b)   =>
  do ctx ← read; if isTailCallTo ctx.mainFn d then emitTailCall v else emitVDecl x t v *> emitBlock b
| FnBody.inc x n c p b       => unless p (emitInc x n c) *> emitBlock b
| FnBody.dec x n c p b       => unless p (emitDec x n c) *> emitBlock b
| FnBody.del x b             => emitDel x *> emitBlock b
| FnBody.setTag x i b        => emitSetTag x i *> emitBlock b
| FnBody.set x i y b         => emitSet x i y *> emitBlock b
| FnBody.uset x i y b        => emitUSet x i y *> emitBlock b
| FnBody.sset x i o y t b    => emitSSet x i o y t *> emitBlock b
| FnBody.mdata _ b           => emitBlock b
| FnBody.ret x               => emit "return " *> emitArg x *> emitLn ";"
| FnBody.case _ x xType alts => emitCase emitBody x xType alts
| FnBody.jmp j xs            => emitJmp j xs
| FnBody.unreachable         => emitLn "lean_panic_unreachable();"

partial def emitJPs (emitBody : FnBody → M Unit) : FnBody → M Unit
| FnBody.jdecl j xs v b => do emit j; emitLn ":"; emitBody v; emitJPs b
| e                     => unless e.isTerminal (emitJPs e.body)

partial def emitFnBody : FnBody → M Unit
| b => do
emitLn "{";
declared ← declareVars b false;
when declared (emitLn "");
emitBlock emitFnBody b;
emitJPs emitFnBody b;
emitLn "}"

def emitDeclAux (d : Decl) : M Unit := do
env ← getEnv;
let (vMap, jpMap) := mkVarJPMaps d;
adaptReader (fun (ctx : Context) => { jpMap := jpMap, .. ctx }) $ do
unless (hasInitAttr env d.name) $
  match d with
  | Decl.fdecl f xs t b => do
    baseName ← toCName f;
    emit (toCType t); emit " ";
    if xs.size > 0 then do {
      emit baseName;
      emit "(";
      if xs.size > closureMaxArgs && isBoxedName d.name then
        emit "lean_object** _args"
      else
        xs.size.forM $ fun i => do {
          when (i > 0) (emit ", ");
          let x := xs.get! i;
          emit (toCType x.ty); emit " "; emit x.x
        };
      emit ")"
    } else do {
      emit ("_init_" ++ baseName ++ "()")
    };
    emitLn " {";
    when (xs.size > closureMaxArgs && isBoxedName d.name) $
      xs.size.forM $ fun i => do {
        let x := xs.get! i;
        emit "lean_object* "; emit x.x; emit " = _args["; emit i; emitLn "];"
      };
    emitLn "_start:";
    adaptReader (fun (ctx : Context) => { mainFn := f, mainParams := xs, .. ctx }) (emitFnBody b);
    emitLn "}"
  | _ => pure ()

def emitDecl (d : Decl) : M Unit :=
let d := d.normalizeIds; -- ensure we don't have gaps in the variable indices
catch
  (emitDeclAux d)
  (fun err => throw (err ++ "\ncompiling:\n" ++ toString d))

def emitFns : M Unit := do
env ← getEnv;
let decls := getDecls env;
decls.reverse.forM emitDecl

def emitMarkPersistent (d : Decl) (n : Name) : M Unit :=
when d.resultType.isObj $ do {
  emit "lean_mark_persistent("; emitCName n; emitLn ");"
}

def emitDeclInit (d : Decl) : M Unit := do
env ← getEnv;
let n := d.name;
if isIOUnitInitFn env n then do {
  emit "res = "; emitCName n; emitLn "(lean_io_mk_world());";
  emitLn "if (lean_io_result_is_error(res)) return res;";
  emitLn "lean_dec_ref(res);"
} else when (d.params.size == 0) $
  match getInitFnNameFor env d.name with
  | some initFn => do {
    emit "res = "; emitCName initFn; emitLn "(lean_io_mk_world());";
    emitLn "if (lean_io_result_is_error(res)) return res;";
    emitCName n; emitLn " = lean_io_result_get_value(res);";
    emitMarkPersistent d n;
    emitLn "lean_dec_ref(res);"
    }
  | _ => do { emitCName n; emit " = "; emitCInitName n; emitLn "();"; emitMarkPersistent d n }

def emitInitFn : M Unit := do
env ← getEnv;
modName ← getModName;
env.imports.forM $ fun imp => emitLn ("lean_object* initialize_" ++ imp.module.mangle "" ++ "(lean_object*);");
emitLns [
  "static bool _G_initialized = false;",
  "lean_object* initialize_" ++ modName.mangle "" ++ "(lean_object* w) {",
  "lean_object * res;",
  "if (_G_initialized) return lean_mk_io_result(lean_box(0));",
  "_G_initialized = true;"
];
env.imports.forM $ fun imp => emitLns [
  "res = initialize_" ++ imp.module.mangle "" ++ "(lean_io_mk_world());",
  "if (lean_io_result_is_error(res)) return res;",
  "lean_dec_ref(res);"];
let decls := getDecls env;
decls.reverse.forM emitDeclInit;
emitLns ["return lean_mk_io_result(lean_box(0));", "}"]

def main : M Unit := do
emitFileHeader;
emitFnDecls;
emitFns;
emitInitFn;
emitMainFnIfNeeded;
emitFileFooter

end EmitC

@[export lean_ir_emit_c]
def emitC (env : Environment) (modName : Name) : Except String String :=
match (EmitC.main { env := env, modName := modName }).run "" with
| EStateM.Result.ok    _   s => Except.ok s
| EStateM.Result.error err _ => Except.error err

end IR
end Lean
