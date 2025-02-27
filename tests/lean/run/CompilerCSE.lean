import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do
import Lean.Elab.Command

open Lean
open Lean.Compiler.LCNF

@[cpass]
def cseFixTest : PassInstaller := Testing.assertIsAtFixPoint |>.install `cse `cseFix

@[cpass]
def cseSizeTest : PassInstaller :=
  Testing.assertReducesOrPreservesSize "CSE increased size of declaration" |>.install `cse `cseSizeLeq

set_option trace.Compiler.test true in
/--
trace: [Compiler.test] Starting wrapper test cseSizeLeq for cse occurrence 0
[Compiler.test] Wrapper test cseSizeLeq for cse occurrence 0 successful
[Compiler.test] Starting post condition test cseFix for cse occurrence 0
[Compiler.test] Post condition test cseFix for cse occurrence 0 successful
[Compiler.test] Starting wrapper test cseSizeLeq for cse occurrence 1
[Compiler.test] Wrapper test cseSizeLeq for cse occurrence 1 successful
[Compiler.test] Starting post condition test cseFix for cse occurrence 1
[Compiler.test] Post condition test cseFix for cse occurrence 1 successful
[Compiler.test] Starting wrapper test cseSizeLeq for cse occurrence 2
[Compiler.test] Wrapper test cseSizeLeq for cse occurrence 2 successful
[Compiler.test] Starting post condition test cseFix for cse occurrence 2
[Compiler.test] Post condition test cseFix for cse occurrence 2 successful
---
info: [Compiler.test] Starting wrapper test cseSizeLeq for cse occurrence 0
[Compiler.test] Wrapper test cseSizeLeq for cse occurrence 0 successful
[Compiler.test] Starting post condition test cseFix for cse occurrence 0
[Compiler.test] Post condition test cseFix for cse occurrence 0 successful
[Compiler.test] Starting wrapper test cseSizeLeq for cse occurrence 1
[Compiler.test] Wrapper test cseSizeLeq for cse occurrence 1 successful
[Compiler.test] Starting post condition test cseFix for cse occurrence 1
[Compiler.test] Post condition test cseFix for cse occurrence 1 successful
[Compiler.test] Starting wrapper test cseSizeLeq for cse occurrence 2
[Compiler.test] Wrapper test cseSizeLeq for cse occurrence 2 successful
[Compiler.test] Starting post condition test cseFix for cse occurrence 2
[Compiler.test] Post condition test cseFix for cse occurrence 2 successful
-/
#guard_msgs in
run_meta Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
