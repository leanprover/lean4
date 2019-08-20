/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.conditional
import init.lean.runtime
import init.lean.compiler.namemangling
import init.lean.compiler.exportattr
import init.lean.compiler.initattr
import init.lean.compiler.ir.compilerm
import init.lean.compiler.ir.emitutil
import init.lean.compiler.ir.normids
import init.lean.compiler.ir.simpcase
import init.lean.compiler.ir.boxing

namespace Lean
namespace IR
open ExplicitBoxing (requiresBoxedVersion mkBoxedName isBoxedName)
namespace EmitCpp

def leanMainFn := "_lean_main"

structure Context :=
(env        : Environment)
(modName    : Name)
(varMap     : VarTypeMap := {})
(jpMap      : JPParamsMap := {})
(mainFn     : FunId := default _)
(mainParams : Array Param := Array.empty)

abbrev M := ReaderT Context (EState String String)

def getEnv : M Environment := Context.env <$> read
def getModName : M Name := Context.modName <$> read
def getDecl (n : Name) : M Decl :=
do env ← getEnv;
   match findEnvDecl env n with
   | some d => pure d
   | none   => throw ("unknown declaration '" ++ toString n ++ "'")

@[inline] def emit {α : Type} [HasToString α] (a : α) : M Unit :=
modify (fun out => out ++ toString a)

@[inline] def emitLn {α : Type} [HasToString α] (a : α) : M Unit :=
emit a *> emit "\n"

def emitLns {α : Type} [HasToString α] (as : List α) : M Unit :=
as.mfor $ fun a => emitLn a

def argToCppString (x : Arg) : String :=
match x with
| Arg.var x => toString x
| _         => "lean::box(0)"

def emitArg (x : Arg) : M Unit :=
emit (argToCppString x)

def toCppType : IRType → String
| IRType.float      => "double"
| IRType.uint8      => "uint8"
| IRType.uint16     => "uint16"
| IRType.uint32     => "uint32"
| IRType.uint64     => "uint64"
| IRType.usize      => "usize"
| IRType.object     => "obj*"
| IRType.tobject    => "obj*"
| IRType.irrelevant => "obj*"

def openNamespacesAux : Name → M Unit
| Name.anonymous    => pure ()
| Name.mkString p s => openNamespacesAux p *> emitLn ("namespace " ++ s ++ " {")
| n                 => throw ("invalid namespace '" ++ toString n ++ "'")

def openNamespaces (n : Name) : M Unit :=
openNamespacesAux n.getPrefix

def openNamespacesFor (n : Name) : M Unit :=
do env ← getEnv;
   match getExportNameFor env n with
   | none   => pure ()
   | some n => openNamespaces n

def closeNamespacesAux : Name → M Unit
| Name.anonymous    => pure ()
| Name.mkString p _ => emitLn "}" *> closeNamespacesAux p
| n                 => throw ("invalid namespace '" ++ toString n ++ "'")

def closeNamespaces (n : Name) : M Unit :=
closeNamespacesAux n.getPrefix

def closeNamespacesFor (n : Name) : M Unit :=
do env ← getEnv;
   match getExportNameFor env n with
   | none   => pure ()
   | some n => closeNamespaces n

def throwInvalidExportName {α : Type} (n : Name) : M α :=
throw ("invalid export name '" ++ toString n ++ "'")

def toBaseCppName (n : Name) : M String :=
do env ← getEnv;
   match getExportNameFor env n with
   | some (Name.mkString _ s) => pure s
   | some _                   => throwInvalidExportName n
   | none                     => if n == `main then pure leanMainFn else pure n.mangle

def toCppName (n : Name) : M String :=
do env ← getEnv;
   match getExportNameFor env n with
   | some s => pure (s.toStringWithSep "::")
   | none   => if n == `main then pure leanMainFn else pure n.mangle

def emitCppName (n : Name) : M Unit :=
toCppName n >>= emit

def toCppInitName (n : Name) : M String :=
do env ← getEnv;
   match getExportNameFor env n with
   | some (Name.mkString p s) => pure $ (Name.mkString p ("_init_" ++ s)).toStringWithSep "::"
   | some _                   => throwInvalidExportName n
   | none                     => pure ("_init_" ++ n.mangle)

def emitCppInitName (n : Name) : M Unit :=
toCppInitName n >>= emit

def isSimpleExportName (n : Name) : M Bool :=
do env ← getEnv;
   match getExportNameFor env n with
   | some (Name.mkString Name.anonymous s) => pure true
   | _ => pure false

def emitFnDeclAux (decl : Decl) (cppBaseName : String) (addExternForConsts : Bool) : M Unit :=
do
let ps := decl.params;
if ps.isEmpty && addExternForConsts then
  emit "extern "
else
  -- Temporary hack for transitioning to C
  mwhen (isSimpleExportName decl.name) (emit "extern \"C\" ");
emit (toCppType decl.resultType ++ " " ++ cppBaseName);
unless (ps.isEmpty) $ do {
  emit "(";
  if ps.size > closureMaxArgs && isBoxedName decl.name then
    emit "obj**"
  else
    ps.size.mfor $ fun i => do {
      when (i > 0) (emit ", ");
      emit (toCppType (ps.get i).ty)
    };
  emit ")"
};
emitLn ";"

def emitFnDecl (decl : Decl) (addExternForConsts : Bool) : M Unit :=
do
openNamespacesFor decl.name;
cppBaseName ← toBaseCppName decl.name;
emitFnDeclAux decl cppBaseName addExternForConsts;
closeNamespacesFor decl.name

def cppQualifiedNameToName (s : String) : Name :=
(s.split "::").foldl Name.mkString Name.anonymous

def emitExternDeclAux (decl : Decl) (cppName : String) : M Unit :=
do
let qCppName := cppQualifiedNameToName cppName;
openNamespaces qCppName;
env ← getEnv;
let extC := isExternC env decl.name;
when extC (emit "extern \"C\" ");
(Name.mkString _ qCppBaseName) ← pure qCppName | throw "invalid name";
emitFnDeclAux decl qCppBaseName (!extC);
closeNamespaces qCppName

def emitFnDecls : M Unit :=
do
env ← getEnv;
let decls := getDecls env;
let modDecls  : NameSet := decls.foldl (fun s d => s.insert d.name) {};
let usedDecls : NameSet := decls.foldl (fun s d => collectUsedDecls env d (s.insert d.name)) {};
let usedDecls := usedDecls.toList;
usedDecls.mfor $ fun n => do
  decl ← getDecl n;
  match getExternNameFor env `cpp decl.name with
  | some cppName => emitExternDeclAux decl cppName
  | none         => emitFnDecl decl (!modDecls.contains n)

def emitMainFn : M Unit :=
do
d ← getDecl `main;
match d with
| Decl.fdecl f xs t b => do
  unless (xs.size == 2 || xs.size == 1) (throw "invalid main function, incorrect arity when generating code");
  env ← getEnv;
  let usesLeanAPI := usesLeanNamespace env d;
  when usesLeanAPI (emitLn "namespace lean { void initialize(); }");
  emitLn "int main(int argc, char ** argv) {";
  if usesLeanAPI then
    emitLn "lean::initialize();"
  else
    emitLn "lean::initialize_runtime_module();";
  emitLn "obj * w = lean::io_mk_world();";
  modName ← getModName;
  emitLn ("w = initialize_" ++ (modName.mangle "") ++ "(w);");
  emitLns ["lean::io_mark_end_initialization();",
           "if (io_result_is_ok(w)) {",
           "lean::scoped_task_manager tmanager(lean::hardware_concurrency());"];
  if xs.size == 2 then do {
    emitLns ["obj* in = lean::box(0);",
             "int i = argc;",
             "while (i > 1) {",
             " i--;",
             " obj* n = lean::alloc_cnstr(1,2,0); lean::cnstr_set(n, 0, lean::mk_string(argv[i])); lean::cnstr_set(n, 1, in);",
             " in = n;",
             "}"];
    emitLn ("w = " ++ leanMainFn ++ "(in, w);")
  } else do {
    emitLn ("w = " ++ leanMainFn ++ "(w);")
  };
  emitLn "}";
  emitLns ["if (io_result_is_ok(w)) {",
           "  int ret = lean::unbox(io_result_get_value(w));",
           "  lean::dec_ref(w);",
           "  return ret;",
           "} else {",
           "  lean::io_result_show_error(w);",
           "  lean::dec_ref(w);",
           "  return 1;",
           "}"];
  emitLn "}"
| other => throw "function declaration expected"

def hasMainFn : M Bool :=
do env ← getEnv;
   let decls := getDecls env;
   pure $ decls.any (fun d => d.name == `main)

def emitMainFnIfNeeded : M Unit :=
mwhen hasMainFn emitMainFn

def emitFileHeader : M Unit :=
do
env ← getEnv;
modName ← getModName;
emitLn "// Lean compiler output";
emitLn ("// Module: " ++ toString modName);
emit "// Imports:";
env.imports.mfor $ fun m => emit (" " ++ toString m);
emitLn "";
emitLn "#include \"runtime/object.h\"";
emitLn "#include \"runtime/apply.h\"";
mwhen hasMainFn $ emitLn "#include \"runtime/init_module.h\"";
emitLns [
 "typedef lean::object obj;    typedef lean::usize  usize;",
 "typedef lean::uint8  uint8;  typedef lean::uint16 uint16;",
 "typedef lean::uint32 uint32; typedef lean::uint64 uint64;",
 "#if defined(__clang__)",
 "#pragma clang diagnostic ignored \"-Wunused-parameter\"",
 "#pragma clang diagnostic ignored \"-Wunused-label\"",
 "#elif defined(__GNUC__) && !defined(__CLANG__)",
 "#pragma GCC diagnostic ignored \"-Wunused-parameter\"",
 "#pragma GCC diagnostic ignored \"-Wunused-label\"",
 "#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"",
 "#endif"]

def throwUnknownVar {α : Type} (x : VarId) : M α :=
throw ("unknown variable '" ++ toString x ++ "'")

def isObj (x : VarId) : M Bool :=
do ctx ← read;
   match ctx.varMap.find x with
   | some t => pure t.isObj
   | none   => throwUnknownVar x

def getJPParams (j : JoinPointId) : M (Array Param) :=
do ctx ← read;
   match ctx.jpMap.find j with
   | some ps => pure ps
   | none    => throw "unknown join point"

def declareVar (x : VarId) (t : IRType) : M Unit :=
do emit (toCppType t); emit " "; emit x; emit "; "

def declareParams (ps : Array Param) : M Unit :=
ps.mfor $ fun p => declareVar p.x p.ty

partial def declareVars : FnBody → Bool → M Bool
| e@(FnBody.vdecl x t _ b), d => do
  ctx ← read;
  if isTailCallTo ctx.mainFn e then
    pure d
  else
    declareVar x t *> declareVars b true
| FnBody.jdecl j xs _ b,    d => declareParams xs *> declareVars b (d || xs.size > 0)
| e,                        d => if e.isTerminal then pure d else declareVars e.body d

def emitTag (x : VarId) : M Unit :=
do
xIsObj ← isObj x;
if xIsObj then do
  emit "lean::obj_tag("; emit x; emit ")"
else
  emit x

def isIf (alts : Array Alt) : Option (Nat × FnBody × FnBody) :=
if alts.size != 2 then none
else match alts.get 0 with
  | Alt.ctor c b => some (c.cidx, b, (alts.get 1).body)
  | _            => none

def emitIf (emitBody : FnBody → M Unit) (x : VarId) (tag : Nat) (t : FnBody) (e : FnBody) : M Unit :=
do
emit "if ("; emitTag x; emit " == "; emit tag; emitLn ")";
emitBody t;
emitLn "else";
emitBody e

def emitCase (emitBody : FnBody → M Unit) (x : VarId) (alts : Array Alt) : M Unit :=
match isIf alts with
| some (tag, t, e) => emitIf emitBody x tag t e
| _ => do
  emit "switch ("; emitTag x; emitLn ") {";
  let alts := ensureHasDefault alts;
  alts.mfor $ fun alt => match alt with
    | Alt.ctor c b  => emit "case " *> emit c.cidx *> emitLn ":" *> emitBody b
    | Alt.default b => emitLn "default: " *> emitBody b;
  emitLn "}"

def emitInc (x : VarId) (n : Nat) (checkRef : Bool) : M Unit :=
do
emit (if checkRef then "lean::inc" else "lean::inc_ref");
emit "(" *> emit x;
when (n != 1) (emit ", " *> emit n);
emitLn ");"

def emitDec (x : VarId) (n : Nat) (checkRef : Bool) : M Unit :=
do
emit (if checkRef then "lean::dec" else "lean::dec_ref");
emit "("; emit x;
when (n != 1) (do emit ", "; emit n);
emitLn ");"

def emitDel (x : VarId) : M Unit :=
do emit "lean::free_heap_obj("; emit x; emitLn ");"

def emitSetTag (x : VarId) (i : Nat) : M Unit :=
do emit "lean::cnstr_set_tag("; emit x; emit ", "; emit i; emitLn ");"

def emitSet (x : VarId) (i : Nat) (y : Arg) : M Unit :=
do emit "lean::cnstr_set("; emit x; emit ", "; emit i; emit ", "; emitArg y; emitLn ");"

def emitOffset (n : Nat) (offset : Nat) : M Unit :=
if n > 0 then do
  emit "sizeof(void*)*"; emit n;
  when (offset > 0) (emit " + " *> emit offset)
else
  emit offset

def emitUSet (x : VarId) (n : Nat) (y : VarId) : M Unit :=
do emit "lean::cnstr_set_usize("; emit x; emit ", "; emit n; emit ", "; emit y; emitLn ");"

def emitSSet (x : VarId) (n : Nat) (offset : Nat) (y : VarId) (t : IRType) : M Unit :=
do
match t with
| IRType.float  => throw "floats are not supported yet"
| IRType.uint8  => emit "lean::cnstr_set_uint8"
| IRType.uint16 => emit "lean::cnstr_set_uint16"
| IRType.uint32 => emit "lean::cnstr_set_uint32"
| IRType.uint64 => emit "lean::cnstr_set_uint64"
| _             => throw "invalid instruction";
emit "("; emit x; emit ", "; emitOffset n offset; emit ", "; emit y; emitLn ");"

def emitJmp (j : JoinPointId) (xs : Array Arg) : M Unit :=
do
  ps ← getJPParams j;
  unless (xs.size == ps.size) (throw "invalid goto");
  xs.size.mfor $ fun i => do {
    let p := ps.get i;
    let x := xs.get i;
    emit p.x; emit " = "; emitArg x; emitLn ";"
  };
  emit "goto "; emit j; emitLn ";"

def emitLhs (z : VarId) : M Unit :=
do emit z; emit " = "

def emitArgs (ys : Array Arg) : M Unit :=
ys.size.mfor $ fun i => do
  when (i > 0) (emit ", ");
  emitArg (ys.get i)

def emitCtorScalarSize (usize : Nat) (ssize : Nat) : M Unit :=
if usize == 0 then emit ssize
else if ssize == 0 then emit "sizeof(size_t)*" *> emit usize
else emit "sizeof(size_t)*" *> emit usize *> emit " + " *> emit ssize

def emitAllocCtor (c : CtorInfo) : M Unit :=
do
emit "lean::alloc_cnstr("; emit c.cidx; emit ", "; emit c.size; emit ", ";
emitCtorScalarSize c.usize c.ssize; emitLn ");"

def emitCtorSetArgs (z : VarId) (ys : Array Arg) : M Unit :=
ys.size.mfor $ fun i => do
  emit "lean::cnstr_set("; emit z; emit ", "; emit i; emit ", "; emitArg (ys.get i); emitLn ");"

def emitCtor (z : VarId) (c : CtorInfo) (ys : Array Arg) : M Unit :=
do
emitLhs z;
if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
  emit "lean::box("; emit c.cidx; emitLn ");"
else do
  emitAllocCtor c; emitCtorSetArgs z ys

def emitReset (z : VarId) (n : Nat) (x : VarId) : M Unit :=
do
emit "if (lean::is_exclusive("; emit x; emitLn ")) {";
n.mfor $ fun i => do {
  emit " lean::cnstr_release("; emit x; emit ", "; emit i; emitLn ");"
};
emit " "; emitLhs z; emit x; emitLn ";";
emitLn "} else {";
emit " lean::dec_ref("; emit x; emitLn ");";
emit " "; emitLhs z; emitLn "lean::box(0);";
emitLn "}"

def emitReuse (z : VarId) (x : VarId) (c : CtorInfo) (updtHeader : Bool) (ys : Array Arg) : M Unit :=
do
emit "if (lean::is_scalar("; emit x; emitLn ")) {";
emit " "; emitLhs z; emitAllocCtor c;
emitLn "} else {";
emit " "; emitLhs z; emit x; emitLn ";";
when updtHeader (do emit " lean::cnstr_set_tag("; emit z; emit ", "; emit c.cidx; emitLn ");");
emitLn "}";
emitCtorSetArgs z ys

def emitProj (z : VarId) (i : Nat) (x : VarId) : M Unit :=
do emitLhs z; emit "lean::cnstr_get("; emit x; emit ", "; emit i; emitLn ");"

def emitUProj (z : VarId) (i : Nat) (x : VarId) : M Unit :=
do emitLhs z; emit "lean::cnstr_get_usize("; emit x; emit ", "; emit i; emitLn ");"

def emitSProj (z : VarId) (t : IRType) (n offset : Nat) (x : VarId) : M Unit :=
do emitLhs z;
match t with
| IRType.float  => throw "floats are not supported yet"
| IRType.uint8  => emit "lean::cnstr_get_uint8"
| IRType.uint16 => emit "lean::cnstr_get_uint16"
| IRType.uint32 => emit "lean::cnstr_get_uint32"
| IRType.uint64 => emit "lean::cnstr_get_uint64"
| _             => throw "invalid instruction";
emit "("; emit x; emit ", "; emitOffset n offset; emitLn ");"

def toStringArgs (ys : Array Arg) : List String :=
ys.toList.map argToCppString

def emitFullApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit :=
do
emitLhs z;
decl ← getDecl f;
match decl with
| Decl.extern _ _ _ extData =>
  match mkExternCall extData `cpp (toStringArgs ys) with
  | some c => emit c *> emitLn ";"
  | none   => throw "failed to emit extern application"
| _ => do emitCppName f; when (ys.size > 0) (do emit "("; emitArgs ys; emit ")"); emitLn ";"

def emitPartialApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit :=
do
decl ← getDecl f;
let arity := decl.params.size;
emitLhs z; emit "lean::alloc_closure(reinterpret_cast<void*>("; emitCppName f; emit "), "; emit arity; emit ", "; emit ys.size; emitLn ");";
ys.size.mfor $ fun i => do {
   let y := ys.get i;
   emit "lean::closure_set("; emit z; emit ", "; emit i; emit ", "; emitArg y; emitLn ");"
}

def emitApp (z : VarId) (f : VarId) (ys : Array Arg) : M Unit :=
if ys.size > closureMaxArgs then do
  emit "{ obj* _aargs[] = {"; emitArgs ys; emitLn "};";
  emitLhs z; emit "lean::apply_m("; emit f; emit ", "; emit ys.size; emitLn ", _aargs); }"
else do
  emitLhs z; emit "lean::apply_"; emit ys.size; emit "("; emit f; emit ", "; emitArgs ys; emitLn ");"

def emitBoxFn (xType : IRType) : M Unit :=
match xType with
| IRType.usize  => emit "lean::box_size_t"
| IRType.uint32 => emit "lean::box_uint32"
| IRType.uint64 => emit "lean::box_uint64"
| IRType.float  => throw "floats are not supported yet"
| other         => emit "lean::box"

def emitBox (z : VarId) (x : VarId) (xType : IRType) : M Unit :=
do emitLhs z; emitBoxFn xType; emit "("; emit x; emitLn ");"

def emitUnbox (z : VarId) (t : IRType) (x : VarId) : M Unit :=
do
emitLhs z;
match t with
| IRType.usize  => emit "lean::unbox_size_t"
| IRType.uint32 => emit "lean::unbox_uint32"
| IRType.uint64 => emit "lean::unbox_uint64"
| IRType.float  => throw "floats are not supported yet"
| other         => emit "lean::unbox";
emit "("; emit x; emitLn ");"

def emitIsShared (z : VarId) (x : VarId) : M Unit :=
do emitLhs z; emit "!lean::is_exclusive("; emit x; emitLn ");"

def emitIsTaggedPtr (z : VarId) (x : VarId) : M Unit :=
do emitLhs z; emit "!lean::is_scalar("; emit x; emitLn ");"

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
  emit "lean::mk_nat_obj(";
  if v < uint32Sz then emit v *> emit "u"
  else emit "lean::mpz(\"" *> emit v *> emit "\")";
  emit ")"
else
  emit v

def emitLit (z : VarId) (t : IRType) (v : LitVal) : M Unit :=
emitLhs z *>
match v with
| LitVal.num v => emitNumLit t v *> emitLn ";"
| LitVal.str v => do emit "lean::mk_string("; emit (quoteString v); emitLn ");"

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

def isTailCall (x : VarId) (v : Expr) (b : FnBody) : M Bool :=
do
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
  let p := ps.get i;
  (i+1, n).anyI $ fun j => paramEqArg p (ys.get j)

def emitTailCall (v : Expr) : M Unit :=
match v with
| Expr.fap _ ys => do
  ctx ← read;
  let ps := ctx.mainParams;
  unless (ps.size == ys.size) (throw "invalid tail call");
  if overwriteParam ps ys then do {
    emitLn "{";
    ps.size.mfor $ fun i => do {
      let p := ps.get i;
      let y := ys.get i;
      unless (paramEqArg p y) $ do {
        emit (toCppType p.ty); emit " _tmp_"; emit i; emit " = "; emitArg y; emitLn ";"
      }
    };
    ps.size.mfor $ fun i => do {
      let p := ps.get i;
      let y := ys.get i;
      unless (paramEqArg p y) (do emit p.x; emit " = _tmp_"; emit i; emitLn ";")
    };
    emitLn "}"
  } else do {
    ys.size.mfor $ fun i => do {
      let p := ps.get i;
      let y := ys.get i;
      unless (paramEqArg p y) (do emit p.x; emit " = "; emitArg y; emitLn ";")
    }
  };
  emitLn "goto _start;"
| _ => throw "bug at emitTailCall"

partial def emitBlock (emitBody : FnBody → M Unit) : FnBody → M Unit
| FnBody.jdecl j xs v b    => emitBlock b
| d@(FnBody.vdecl x t v b) =>
  do ctx ← read; if isTailCallTo ctx.mainFn d then emitTailCall v else emitVDecl x t v *> emitBlock b
| FnBody.inc x n c b       => emitInc x n c *> emitBlock b
| FnBody.dec x n c b       => emitDec x n c *> emitBlock b
| FnBody.del x b           => emitDel x *> emitBlock b
| FnBody.setTag x i b      => emitSetTag x i *> emitBlock b
| FnBody.set x i y b       => emitSet x i y *> emitBlock b
| FnBody.uset x i y b      => emitUSet x i y *> emitBlock b
| FnBody.sset x i o y t b  => emitSSet x i o y t *> emitBlock b
| FnBody.mdata _ b         => emitBlock b
| FnBody.ret x             => emit "return " *> emitArg x *> emitLn ";"
| FnBody.case _ x alts     => emitCase emitBody x alts
| FnBody.jmp j xs          => emitJmp j xs
| FnBody.unreachable       => emitLn "lean_unreachable();"

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

def emitDeclAux (d : Decl) : M Unit :=
do
env ← getEnv;
let (vMap, jpMap) := mkVarJPMaps d;
adaptReader (fun (ctx : Context) => { varMap := vMap, jpMap := jpMap, .. ctx }) $ do
unless (hasInitAttr env d.name) $
  match d with
  | Decl.fdecl f xs t b => do
    openNamespacesFor f;
    baseName ← toBaseCppName f;
    emit (toCppType t); emit " ";
    if xs.size > 0 then do {
      emit baseName;
      emit "(";
      if xs.size > closureMaxArgs && isBoxedName d.name then
        emit "obj** _args"
      else
        xs.size.mfor $ fun i => do {
          when (i > 0) (emit ", ");
          let x := xs.get i;
          emit (toCppType x.ty); emit " "; emit x.x
        };
      emit ")"
    } else do {
      emit ("_init_" ++ baseName ++ "()")
    };
    emitLn " {";
    when (xs.size > closureMaxArgs && isBoxedName d.name) $
      xs.size.mfor $ fun i => do {
        let x := xs.get i;
        emit "obj * "; emit x.x; emit " = _args["; emit i; emitLn "];"
      };
    emitLn "_start:";
    adaptReader (fun (ctx : Context) => { mainFn := f, mainParams := xs, .. ctx }) (emitFnBody b);
    emitLn "}";
    closeNamespacesFor f
  | _ => pure ()

def emitDecl (d : Decl) : M Unit :=
let d := d.normalizeIds;
catch
  (emitDeclAux d)
  (fun err => throw (err ++ "\ncompiling:\n" ++ toString d))

def emitFns : M Unit :=
do
env ← getEnv;
let decls := getDecls env;
decls.reverse.mfor emitDecl

def emitDeclInit (d : Decl) : M Unit :=
do
env ← getEnv;
let n := d.name;
if isIOUnitInitFn env n then do {
  emit "w = "; emitCppName n; emitLn "(w);";
  emitLn "if (io_result_is_error(w)) return w;"
} else when (d.params.size == 0) $ do {
  match getInitFnNameFor env d.name with
  | some initFn => do {
    emit "w = "; emitCppName initFn; emitLn "(w);";
    emitLn "if (io_result_is_error(w)) return w;";
    emitCppName n; emitLn " = io_result_get_value(w);"
  }
  | _ => do {
    emitCppName n; emit " = "; emitCppInitName n; emitLn "();"
  };
  when d.resultType.isObj $ do {
    emit "lean::mark_persistent("; emitCppName n; emitLn ");"
  }
}

def emitInitFn : M Unit :=
do
env ← getEnv;
modName ← getModName;
env.imports.mfor $ fun m => emitLn ("obj* initialize_" ++ m.mangle "" ++ "(obj*);");
emitLns [
    "static bool _G_initialized = false;",
    "obj* initialize_" ++ modName.mangle "" ++ "(obj* w) {",
    "if (_G_initialized) return w;",
    "_G_initialized = true;",
    "if (io_result_is_error(w)) return w;"
];
env.imports.mfor $ fun m => emitLns [
  "w = initialize_" ++ m.mangle "" ++ "(w);",
  "if (io_result_is_error(w)) return w;"
];
let decls := getDecls env;
decls.reverse.mfor emitDeclInit;
emitLns [
  "return w;",
  "}"]

def main : M Unit :=
do
emitFileHeader;
emitFnDecls;
emitFns;
emitInitFn;
emitMainFnIfNeeded

end EmitCpp

@[export lean_ir_emit_cpp]
def emitCpp (env : Environment) (modName : Name) : Except String String :=
match (EmitCpp.main { env := env, modName := modName }).run "" with
| EState.Result.ok    _   s => Except.ok s
| EState.Result.error err _ => Except.error err

end IR
end Lean
