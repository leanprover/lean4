import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do

open Lean
open Lean.Compiler.LCNF

-- Run compilation twice to avoid the output caused by the inliner
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]

@[cpass]
def pullInstancesFixTest : PassInstaller := Testing.assertIsAtFixPoint `pullInstances

@[cpass]
def pullInstancesSizeTest : PassInstaller :=
  Testing.assertPreservesSize `pullInstances `pullInstancesSizeEq "Pulling instances changed size"

set_option trace.Compiler.test true in
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
