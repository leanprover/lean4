import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do
import Lean.Elab.Command

open Lean
open Lean.Compiler.LCNF

@[cpass]
def simpFixTest : PassInstaller := Testing.assertIsAtFixPoint |>.install `simp `simpFix

@[cpass]
def simpReaderTest : PassInstaller :=
  Testing.assertDoesNotContainConstAfter `ReaderT.bind "simp did not inline ReaderT.bind" |>.install `simp `simpInlinesBinds

set_option trace.Compiler.test true in
/--
info: [Compiler.test] Starting post condition test simpInlinesBinds for simp occurrence 0
[Compiler.test] Post condition test simpInlinesBinds for simp occurrence 0 successful
[Compiler.test] Starting post condition test simpFix for simp occurrence 0
[Compiler.test] Post condition test simpFix for simp occurrence 0 successful
[Compiler.test] Starting post condition test simpInlinesBinds for simp occurrence 1
[Compiler.test] Post condition test simpInlinesBinds for simp occurrence 1 successful
[Compiler.test] Starting post condition test simpFix for simp occurrence 1
[Compiler.test] Post condition test simpFix for simp occurrence 1 successful
[Compiler.test] Starting post condition test simpInlinesBinds for simp occurrence 2
[Compiler.test] Post condition test simpInlinesBinds for simp occurrence 2 successful
[Compiler.test] Starting post condition test simpFix for simp occurrence 2
[Compiler.test] Post condition test simpFix for simp occurrence 2 successful
[Compiler.test] Starting post condition test simpInlinesBinds for simp occurrence 3
[Compiler.test] Post condition test simpInlinesBinds for simp occurrence 3 successful
[Compiler.test] Starting post condition test simpFix for simp occurrence 3
[Compiler.test] Post condition test simpFix for simp occurrence 3 successful
[Compiler.test] Starting post condition test simpInlinesBinds for simp occurrence 4
[Compiler.test] Post condition test simpInlinesBinds for simp occurrence 4 successful
[Compiler.test] Starting post condition test simpFix for simp occurrence 4
[Compiler.test] Post condition test simpFix for simp occurrence 4 successful
[Compiler.test] Starting post condition test simpInlinesBinds for simp occurrence 5
[Compiler.test] Post condition test simpInlinesBinds for simp occurrence 5 successful
[Compiler.test] Starting post condition test simpFix for simp occurrence 5
[Compiler.test] Post condition test simpFix for simp occurrence 5 successful
-/
#guard_msgs in
run_meta Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
