import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do

open Lean
open Lean.Compiler.LCNF

-- Run compilation twice to avoid the output caused by the inliner
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]

@[cpass]
def cseFixTest : PassInstaller := Testing.assertIsAtFixPoint `cse

@[cpass]
def cseSizeTest : PassInstaller :=
  Testing.assertReducesOrPreservesSize `cse `cseSizeLeq "CSE increased size of declaration"

set_option trace.Compiler.test true in
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
