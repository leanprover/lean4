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
namespace EmitCpp

def leanMainFn := "_lean_main"

structure Context :=
(env        : Environment)
(localCtx   : LocalContext := {})
(modName    : Name)
(modDeps    : Array Name)
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
  emitLn "if (io_result_is_ok(w)) {\n",
  emitLn "lean::scoped_task_manager tmanager(lean::hardware_concurrency());",
  if xs.size == 2 then do {
    emitLn "obj* in = lean::box(0);",
    emitLn "int i = argc;\n",
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

def main : M Unit :=
do env ← getEnv,
   let decls := getDecls env,
   when (decls.any (λ d, d.name == `main)) emitMainFn,
   pure ()

end EmitCpp

@[export lean.ir.emit_cpp_core]
def emitCpp (env : Environment) (modName : Name) (modDeps : Array Name) : Except String String :=
match (EmitCpp.main { env := env, modName := modName, modDeps := modDeps }).run "" with
| EState.Result.ok    _   s := Except.ok s
| EState.Result.error err _ := Except.error err

end IR
end Lean
