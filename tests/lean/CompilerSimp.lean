import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do

open Lean
open Lean.Compiler.LCNF

-- Run compilation twice to avoid the output caused by the inliner
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]

@[cpass]
def simpFixTest : PassInstaller := Testing.assertIsAtFixPoint `simp

@[cpass]
def simpReaderTest : PassInstaller :=
  Testing.assertDoesNotContainConstAfter `simp `simpInlinesBinds `ReaderT.bind "simp did not inline ReaderT.bind"

set_option trace.Compiler.test true in
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
