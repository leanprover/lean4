/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.basic
import init.lean.compiler.ir.format
import init.lean.compiler.ir.compilerm
import init.lean.compiler.ir.pushproj
import init.lean.compiler.ir.elimdead
import init.lean.compiler.ir.simpcase
import init.lean.compiler.ir.resetreuse
import init.lean.compiler.ir.normids
import init.lean.compiler.ir.checker
import init.lean.compiler.ir.borrow
import init.lean.compiler.ir.boxing
import init.lean.compiler.ir.rc
import init.lean.compiler.ir.expandresetreuse
import init.lean.compiler.ir.emitc

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

end IR
end Lean
