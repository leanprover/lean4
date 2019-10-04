/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Compiler.Ir.Basic
import Init.Lean.Compiler.Ir.Format
import Init.Lean.Compiler.Ir.Compilerm
import Init.Lean.Compiler.Ir.Pushproj
import Init.Lean.Compiler.Ir.Elimdead
import Init.Lean.Compiler.Ir.Simpcase
import Init.Lean.Compiler.Ir.Resetreuse
import Init.Lean.Compiler.Ir.Normids
import Init.Lean.Compiler.Ir.Checker
import Init.Lean.Compiler.Ir.Borrow
import Init.Lean.Compiler.Ir.Boxing
import Init.Lean.Compiler.Ir.Rc
import Init.Lean.Compiler.Ir.Expandresetreuse
import Init.Lean.Compiler.Ir.Unboxresult
import Init.Lean.Compiler.Ir.Emitc

namespace Lean
namespace IR

private def compileAux (decls : Array Decl) : CompilerM Unit :=
do
logDecls `init decls;
checkDecls decls;
let decls := decls.map Decl.pushProj;
logDecls `push_proj decls;
let decls := decls.map Decl.insertResetReuse;
logDecls `reset_reuse decls;
let decls := decls.map Decl.elimDead;
logDecls `elim_dead decls;
let decls := decls.map Decl.simpCase;
logDecls `simp_case decls;
let decls := decls.map Decl.normalizeIds;
decls ← inferBorrow decls;
logDecls `borrow decls;
decls ← explicitBoxing decls;
logDecls `boxing decls;
decls ← explicitRC decls;
logDecls `rc decls;
let decls := decls.map Decl.expandResetReuse;
logDecls `expand_reset_reuse decls;
let decls := decls.map Decl.pushProj;
logDecls `push_proj decls;
logDecls `result decls;
checkDecls decls;
addDecls decls;
pure ()

@[export lean_ir_compile]
def compile (env : Environment) (opts : Options) (decls : Array Decl) : Log × (Except String Environment) :=
match (compileAux decls opts).run { env := env } with
| EState.Result.ok     _  s => (s.log, Except.ok s.env)
| EState.Result.error msg s => (s.log, Except.error msg)

def addBoxedVersionAux (decl : Decl) : CompilerM Unit :=
do
env ← getEnv;
if !ExplicitBoxing.requiresBoxedVersion env decl then pure ()
else do
  let decl := ExplicitBoxing.mkBoxedVersion decl;
  let decls : Array Decl := Array.singleton decl;
  decls ← explicitRC decls;
  decls.mfor $ fun decl => modifyEnv $ fun env => addDeclAux env decl;
  pure ()

-- Remark: we are ignoring the `Log` here. This should be fine.
@[export lean_ir_add_boxed_version]
def addBoxedVersion (env : Environment) (decl : Decl) : Except String Environment :=
match (addBoxedVersionAux decl Options.empty).run { env := env } with
| EState.Result.ok     _  s => Except.ok s.env
| EState.Result.error msg s => Except.error msg

end IR
end Lean
