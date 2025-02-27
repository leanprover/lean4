import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do
import Lean.Elab.Command

open Lean
open Lean.Compiler.LCNF

@[cpass]
def pullInstancesFixTest : PassInstaller := Testing.assertIsAtFixPoint |>.install `pullInstances `pullInstancesFix

@[cpass]
def pullInstancesSizeTest : PassInstaller :=
  Testing.assertPreservesSize "Pulling instances changed size" |>.install `pullInstances `pullInstancesSizeEq

set_option trace.Compiler.test true in
/--
trace: [Compiler.test] Starting wrapper test pullInstancesSizeEq for pullInstances occurrence 0
[Compiler.test] Wrapper test pullInstancesSizeEq for pullInstances occurrence 0 successful
[Compiler.test] Starting post condition test pullInstancesFix for pullInstances occurrence 0
[Compiler.test] Post condition test pullInstancesFix for pullInstances occurrence 0 successful
---
info: [Compiler.test] Starting wrapper test pullInstancesSizeEq for pullInstances occurrence 0
[Compiler.test] Wrapper test pullInstancesSizeEq for pullInstances occurrence 0 successful
[Compiler.test] Starting post condition test pullInstancesFix for pullInstances occurrence 0
[Compiler.test] Post condition test pullInstancesFix for pullInstances occurrence 0 successful
-/
#guard_msgs in
run_meta Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
