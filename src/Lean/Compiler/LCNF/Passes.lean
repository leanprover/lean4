/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PullLetDecls
import Lean.Compiler.LCNF.CSE
import Lean.Compiler.LCNF.Simp
import Lean.Compiler.LCNF.PullFunDecls
import Lean.Compiler.LCNF.ReduceJpArity

namespace Lean.Compiler.LCNF

@[cpass] def builtin : PassInstaller :=
  .append #[pullInstances, cse, simp, pullFunDecls, reduceJpArity, simp { etaPoly := true }]

end Lean.Compiler.LCNF
