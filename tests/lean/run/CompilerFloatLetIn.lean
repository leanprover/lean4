import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do

open Lean
open Lean.Compiler.LCNF

-- Run compilation twice to avoid the output caused by the inliner
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]

-- #eval fails if we uncomment this pass after I added a `floatLetIn` pass at the mono phase
-- @[cpass]
-- def floatLetInFixTest : PassInstaller := Testing.assertIsAtFixPoint |>.install `floatLetIn `floatLetInFix

@[cpass]
def floatLetInSizeTest : PassInstaller :=
  Testing.assertReducesOrPreservesSize "FloatLetIn increased size of declaration" |>.install `floatLetIn `floatLetInSizeEq

set_option trace.Compiler.test true in
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
