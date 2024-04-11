import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do
open Lean
open Lean.Compiler.LCNF

-- Run compilation twice to avoid the output caused by the inliner
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo, ``Lean.MetavarContext.MkBinding.collectForwardDeps]

@[cpass]
def findJoinPointFixTest : PassInstaller := Testing.assertIsAtFixPoint |>.install `findJoinPoints `findJoinPointsFix

@[cpass]
def cseSizeTest : PassInstaller :=
  Testing.assertReducesOrPreservesSize "findJoinPoints increased size of declaration" |>.install `findJoinPoints `findJoinPointsSizeLeq

set_option trace.compiler.test true in
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo, ``Lean.MetavarContext.MkBinding.collectForwardDeps]
