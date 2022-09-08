import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do
#exit
open Lean
open Lean.Compiler.LCNF

-- Run compilation twice to avoid the output caused by the inliner
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]

@[cpass]
def findJoinPointFixTest : PassInstaller := Testing.assertIsAtFixPoint `findJoinPoints

@[cpass]
def cseSizeTest : PassInstaller :=
  Testing.assertReducesOrPreservesSize `findJoinPoints `findJoinPointsSizeLeq "findJoinPoints increased size of declaration"

set_option trace.Compiler.test true in
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
