/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.conditional
import init.lean.name_mangling
import init.lean.compiler.ir.compilerm
import init.lean.compiler.ir.emitutil

namespace Lean
namespace IR
-- TODO: @[export]
constant getExportNameFor (env : Environment) (n : Name) : Option Name := default _

namespace EmitCpp

def leanMainFn := "_lean_main"

structure Context :=
(env        : Environment)
(localCtx   : LocalContext := {})
(modName    : Name)
(mainFn     : FunId := default _)
(mainParams : Array Param := Array.empty)

abbrev M := ReaderT Context (EState String String)

def getEnv : M Environment := Context.env <$> read
def getModName : M Name := Context.modName <$> read
def getDecl (n : Name) : M Decl :=
do env ← getEnv,
   match findEnvDecl env n with
   | some d := pure d
   | none   := throw ("unknown declaration '" ++ toString n ++ "'")

@[inline] def emit {α : Type} [HasToString α] (a : α) : M Unit :=
modify (λ out, out ++ toString a)

@[inline] def emitLn {α : Type} [HasToString α] (a : α) : M Unit :=
emit a *> emit "\n"

def toCppType : IRType → String
| IRType.float      := "double"
| IRType.uint8      := "uint8"
| IRType.uint16     := "uint16"
| IRType.uint32     := "uint32"
| IRType.uint64     := "uint64"
| IRType.usize      := "usize"
| IRType.object     := "obj*"
| IRType.tobject    := "obj*"
| IRType.irrelevant := "obj*"

def openNamespacesAux : Name → M Unit
| Name.anonymous      := pure ()
| (Name.mkString p s) := openNamespacesAux p *> emitLn ("namespace " ++ s ++ "{")
| n                   := throw ("invalid namespace '" ++ toString n ++ "'")

def openNamespaces (n : Name) : M Unit :=
openNamespacesAux n.getPrefix

def openNamespacesFor (n : Name) : M Unit :=
do env ← getEnv,
   match getExportNameFor env n with
   | none   := pure ()
   | some n := openNamespaces n

def closeNamespacesAux : Name → M Unit
| Name.anonymous      := pure ()
| (Name.mkString p _) := emitLn "}" *> closeNamespacesAux p
| n                   := throw ("invalid namespace '" ++ toString n ++ "'")

def closeNamespaces (n : Name) : M Unit :=
closeNamespacesAux n.getPrefix

def closeNamespacesFor (n : Name) : M Unit :=
do env ← getEnv,
   match getExportNameFor env n with
   | none   := pure ()
   | some n := closeNamespaces n

def toBaseCppName (n : Name) : M String :=
do env ← getEnv,
   match getExportNameFor env n with
   | some (Name.mkString _ s) := pure s
   | some _                   := throw "invalid export name"
   | none                     := if n == `main then pure leanMainFn else pure n.mangle

def toCppName (n : Name) : M String :=
do env ← getEnv,
   match getExportNameFor env n with
   | some s := pure (s.toStringWithSep "::")
   | none   := if n == `main then pure leanMainFn else pure n.mangle

def toCppInitName (n : Name) : M String :=
do env ← getEnv,
   match getExportNameFor env n with
   | some (Name.mkString p s) := pure $ (Name.mkString p ("_init_" ++ s)).toStringWithSep "::"
   | some _                   := throw "invalid export name"
   | none                     := pure ("_init_" ++ n.mangle)

def emitFnDeclAux (decl : Decl) (extern : Bool) : M Unit :=
do
cppBaseName ← toBaseCppName decl.name,
let ps := decl.params,
when (ps.isEmpty && extern) (emit "extern "),
emit (toCppType decl.resultType ++ " " ++ cppBaseName),
unless (ps.isEmpty) $ do {
  emit "(",
  ps.size.mfor $ λ i, do {
    when (i > 0) (emit ", "),
    emit (toCppType (ps.get i).ty)
  },
  emit ")"
},
emitLn ";"

def emitFnDecl (decl : Decl) (extern : Bool) : M Unit :=
do
openNamespacesFor decl.name,
emitFnDeclAux decl extern,
closeNamespacesFor decl.name

def emitFnDecls : M Unit :=
do env ← getEnv,
   let decls := getDecls env,
   let modDecls  : NameSet := decls.foldl (λ s d, s.insert d.name) {},
   let usedDecls : NameSet := decls.foldl (λ s d, collectUsedDecls d (s.insert d.name)) {},
   let usedDecls := usedDecls.toList,
   usedDecls.mfor $ λ n, do {
     decl ← getDecl n,
     -- TODO: check extern
     emitFnDecl decl (!modDecls.contains n)
   }

def emitMainFn : M Unit :=
do
d ← getDecl `main,
match d with
| Decl.fdecl f xs t b := do
  unless (xs.size == 2 || xs.size == 1) (throw "invalid main function, incorrect arity when generating code"),
  env ← getEnv,
  let usesLeanAPI := usesLeanNamespace env d,
  when usesLeanAPI (emitLn "namespace lean { void initialize(); }"),
  emitLn "int main(int argc, char ** argv) {",
  if usesLeanAPI then
    emitLn "lean::initialize();"
  else
    emitLn "lean::initialize_runtime_module();",
  emitLn "obj * w = lean::io_mk_world();",
  modName ← getModName,
  emitLn ("w = initialize_" ++ (modName.mangle "") ++ "(w);"),
  emitLn "lean::io_mark_end_initialization();",
  emitLn "if (io_result_is_ok(w)) {",
  emitLn "lean::scoped_task_manager tmanager(lean::hardware_concurrency());",
  if xs.size == 2 then do {
    emitLn "obj* in = lean::box(0);",
    emitLn "int i = argc;",
    emitLn "while (i > 1) {",
    emitLn " i--;",
    emitLn " obj* n = lean::alloc_cnstr(1,2,0); lean::cnstr_set(n, 0, lean::mk_string(argv[i])); lean::cnstr_set(n, 1, in);",
    emitLn " in = n;",
    emitLn "}",
    emitLn ("w = " ++ leanMainFn ++ "(in, w);")
  } else do {
    emitLn ("w = " ++ leanMainFn ++ "(w);")
  },
  emitLn "}",
  emitLn "if (io_result_is_ok(w)) {",
  emitLn "  int ret = lean::unbox(io_result_get_value(w));",
  emitLn "  lean::dec_ref(w);",
  emitLn "  return ret;",
  emitLn "} else {",
  emitLn "  lean::io_result_show_error(w);",
  emitLn "  lean::dec_ref(w);",
  emitLn "  return 1;",
  emitLn "}",
  emitLn "}"
| other := throw "function declaration expected"

def hasMainFn : M Bool :=
do env ← getEnv,
   let decls := getDecls env,
   pure $ decls.any (λ d, d.name == `main)

def emitMainFnIfNeeded : M Unit :=
mwhen hasMainFn emitMainFn

def emitFileHeader : M Unit :=
do
env ← getEnv,
modName ← getModName,
emitLn "// Lean compiler output",
emitLn ("// Module: " ++ toString modName),
emit "// Imports:",
env.imports.mfor $ λ m, emit (" " ++ toString m),
emitLn "",
emitLn "#include \"runtime/object.h\"",
emitLn "#include \"runtime/apply.h\"",
mwhen hasMainFn $ emitLn "#include \"runtime/init_module.h\"",
emitLn "typedef lean::object obj;    typedef lean::usize  usize;",
emitLn "typedef lean::uint8  uint8;  typedef lean::uint16 uint16;",
emitLn "typedef lean::uint32 uint32; typedef lean::uint64 uint64;",
emitLn "#if defined(__clang__)",
emitLn "#pragma clang diagnostic ignored \"-Wunused-parameter\"",
emitLn "#pragma clang diagnostic ignored \"-Wunused-label\"",
emitLn "#elif defined(__GNUC__) && !defined(__CLANG__)",
emitLn "#pragma GCC diagnostic ignored \"-Wunused-parameter\"",
emitLn "#pragma GCC diagnostic ignored \"-Wunused-label\"",
emitLn "#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"",
emitLn "#endif"

def main : M Unit :=
do
emitFileHeader,
emitFnDecls,
emitMainFnIfNeeded

end EmitCpp

@[export lean.ir.emit_cpp_core]
def emitCpp (env : Environment) (modName : Name) : Except String String :=
match (EmitCpp.main { env := env, modName := modName }).run "" with
| EState.Result.ok    _   s := Except.ok s
| EState.Result.error err _ := Except.error err

end IR
end Lean
