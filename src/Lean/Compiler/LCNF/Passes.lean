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

@[cpass]
def pullInstancesInstaller : PassInstaller :=
  .installAfter `init (.mkPerDeclaration `pullInstances Decl.pullInstances)

@[cpass]
def cseInstaller : PassInstaller :=
  .installAfter `pullInstances (.mkPerDeclaration `cse Decl.cse)

@[cpass]
def simpInstaller : PassInstaller :=
  .installAfter `cse (.mkPerDeclaration `simp Decl.simp)

@[cpass]
def toJoinPointInstaller : PassInstaller :=
  .installAfter `simp (.mkPerDeclaration `pullFunDecls Decl.pullFunDecls)

@[cpass]
def reduceJpArityInstaller : PassInstaller :=
  .installAfter `pullFunDecls (.mkPerDeclaration `reduceJpArity Decl.reduceJpArity)

end Lean.Compiler.LCNF
