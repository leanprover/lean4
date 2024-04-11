import Lean.Compiler.Main
import Lean.Compiler.LCNF.Testing
import Lean.Elab.Do

open Lean
open Lean.Compiler.LCNF

-- Run compilation twice to avoid the output caused by the inliner
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]

@[cpass]
def pullInstancesFixTest : PassInstaller := Testing.assertIsAtFixPoint |>.install `pullInstances `pullInstancesFix

@[cpass]
def pullInstancesSizeTest : PassInstaller :=
  Testing.assertPreservesSize "Pulling instances changed size" |>.install `pullInstances `pullInstancesSizeEq

set_option trace.compiler.test true in
#eval Compiler.compile #[``Lean.Meta.synthInstance, ``Lean.Elab.Term.Do.elabDo]
