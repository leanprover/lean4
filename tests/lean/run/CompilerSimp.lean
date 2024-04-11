import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do

open Lean
open Lean.Compiler.LCNF

-- Run compilation twice to avoid the output caused by the inliner
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]

@[cpass]
def simpFixTest : PassInstaller := Testing.assertIsAtFixPoint |>.install `simp `simpFix

@[cpass]
def simpReaderTest : PassInstaller :=
  Testing.assertDoesNotContainConstAfter `ReaderT.bind "simp did not inline ReaderT.bind" |>.install `simp `simpInlinesBinds

set_option trace.compiler.test true in
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
