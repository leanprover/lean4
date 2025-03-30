import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do
import Lean.Elab.Command

open Lean
open Lean.Compiler.LCNF

@[cpass]
def findJoinPointFixTest : PassInstaller := Testing.assertIsAtFixPoint |>.install `findJoinPoints `findJoinPointsFix

@[cpass]
def cseSizeTest : PassInstaller :=
  Testing.assertReducesOrPreservesSize "findJoinPoints increased size of declaration" |>.install `findJoinPoints `findJoinPointsSizeLeq

set_option trace.Compiler.test true in
/--
info: [Compiler.test] Starting wrapper test findJoinPointsSizeLeq for findJoinPoints occurrence 0
[Compiler.test] Wrapper test findJoinPointsSizeLeq for findJoinPoints occurrence 0 successful
[Compiler.test] Starting post condition test findJoinPointsFix for findJoinPoints occurrence 0
[Compiler.test] Post condition test findJoinPointsFix for findJoinPoints occurrence 0 successful
-/
#guard_msgs in
run_meta Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo, ``Lean.MetavarContext.MkBinding.collectForwardDeps]
