import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do
import Lean.Elab.Command

open Lean
open Lean.Compiler.LCNF

-- #eval fails if we uncomment this pass after I added a `floatLetIn` pass at the mono phase
-- @[cpass]
-- def floatLetInFixTest : PassInstaller := Testing.assertIsAtFixPoint |>.install `floatLetIn `floatLetInFix

@[cpass]
def floatLetInSizeTest : PassInstaller :=
  Testing.assertReducesOrPreservesSize "FloatLetIn increased size of declaration" |>.install `floatLetIn `floatLetInSizeEq

set_option trace.Compiler.test true in
/--
trace: [Compiler.test] Starting wrapper test floatLetInSizeEq for floatLetIn occurrence 0
[Compiler.test] Wrapper test floatLetInSizeEq for floatLetIn occurrence 0 successful
[Compiler.test] Starting wrapper test floatLetInSizeEq for floatLetIn occurrence 1
[Compiler.test] Wrapper test floatLetInSizeEq for floatLetIn occurrence 1 successful
[Compiler.test] Starting wrapper test floatLetInSizeEq for floatLetIn occurrence 2
[Compiler.test] Wrapper test floatLetInSizeEq for floatLetIn occurrence 2 successful
---
info: [Compiler.test] Starting wrapper test floatLetInSizeEq for floatLetIn occurrence 0
[Compiler.test] Wrapper test floatLetInSizeEq for floatLetIn occurrence 0 successful
[Compiler.test] Starting wrapper test floatLetInSizeEq for floatLetIn occurrence 1
[Compiler.test] Wrapper test floatLetInSizeEq for floatLetIn occurrence 1 successful
[Compiler.test] Starting wrapper test floatLetInSizeEq for floatLetIn occurrence 2
[Compiler.test] Wrapper test floatLetInSizeEq for floatLetIn occurrence 2 successful
-/
#guard_msgs in
run_meta Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
