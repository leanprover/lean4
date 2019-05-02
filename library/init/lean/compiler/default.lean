/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.constfolding
import init.lean.compiler.ir
import init.lean.compiler.pushproj
import init.lean.compiler.elimdead
import init.lean.compiler.simpcase

namespace Lean
namespace IR

@[export lean.ir.test_core]
def test (d : Decl) : IO Unit :=
do IO.println d,
   IO.println $ ("Max variable " ++ toString d.maxVar),
   let d := d.pushProj,
   IO.println "=== After push projections ===",
   IO.println d,
   let d := d.elimDead,
   IO.println "=== After elim dead locals ===",
   IO.println d,
   let d := d.simpCase,
   IO.println "=== After simplify case ===",
   IO.println d

end IR
end Lean
