/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.basic
import init.lean.compiler.ir.format
import init.lean.compiler.ir.pushproj
import init.lean.compiler.ir.elimdead
import init.lean.compiler.ir.simpcase
import init.lean.compiler.ir.resetreuse
import init.lean.compiler.ir.normids
import init.lean.compiler.ir.checker
import init.lean.compiler.ir.boxing

namespace Lean
namespace IR

@[export lean.ir.test_core]
def test (d : Decl) : IO Unit :=
do
   d.check,
   IO.println d,
   IO.println $ ("Max index " ++ toString d.maxIndex),
   let d := d.pushProj,
   IO.println "=== After push projections ===",
   IO.println d,
   let d := d.insertResetReuse,
   IO.println "=== After insert reset reuse ===",
   IO.println d,
   let d := d.elimDead,
   IO.println "=== After elim dead locals ===",
   IO.println d,
   let d := d.simpCase,
   IO.println "=== After simplify case ===",
   IO.println d,
   let d := d.normalizeIds,
   IO.println "=== After normalize Ids ===",
   IO.println d,
   d.check,
   pure ()

end IR
end Lean
