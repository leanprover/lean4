/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF

namespace Lean.Compiler
/--
Run the code generation pipeline for all declarations in `declNames`
that fulfill the requirements of `shouldGenerateCode`.
-/
def compile (declNames : Array Name) : CoreM Unit := do profileitM Exception "compiler new" (← getOptions) do
  withTraceNode `Compiler (fun _ => return m!"compiling: {declNames}") do
    discard <| LCNF.compile declNames

builtin_initialize
  registerTraceClass `Compiler
  registerTraceClass `Compiler.stat

end Lean.Compiler
