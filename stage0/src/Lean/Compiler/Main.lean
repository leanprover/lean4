/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.Decl
import Lean.Compiler.TerminalCases
import Lean.Compiler.CSE

namespace Lean.Compiler

/--
We do not generate code for `declName` if
- Its type is a proposition.
- Its type is a type former.
- It is tagged as `[macroInline]`.
- It is a type class instance.

Remark: we still generate code for declarations tagged as `[inline]`
and `[specialize]` since they can be partially applied.
-/
def shouldGenerateCode (declName : Name) : CoreM Bool := do
  if (← isCompIrrelevant |>.run') then return false
  if hasMacroInlineAttribute (← getEnv) declName then return false
  -- TODO: check if type class instance
  return true
where
  isCompIrrelevant : MetaM Bool := do
    let info ← getConstInfo declName
    Meta.isProp info.type <||> Meta.isTypeFormerType info.type

def checkpoint (step : Name) (decls : Array Decl) (cfg : Check.Config := {}): CoreM Unit := do
  trace[Compiler.step] "{step}"
  for decl in decls do
    withOptions (fun opts => opts.setBool `pp.motives.pi false) do
      trace[Compiler.step] "{decl.name} := {decl.value}"
      decl.check cfg

def compile (declNames : Array Name) : CoreM Unit := do profileitM Exception "compiler new" (← getOptions) do
  let declNames ← declNames.filterM shouldGenerateCode
  let decls ← declNames.mapM toDecl
  checkpoint `init decls { terminalCasesOnly := false }
  let decls ← decls.mapM (·.terminalCases)
  checkpoint `terminalCases decls
  -- Remark: add simplification step here, `cse` is useful after simplification
  let decls ← decls.mapM (·.cse)
  checkpoint `cse decls

builtin_initialize
  registerTraceClass `Compiler
  registerTraceClass `Compiler.step

end Lean.Compiler
