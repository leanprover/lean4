prelude

import Lean.Attributes
import Lean.Meta.Basic
import Lean.Util.Recognizers

namespace Lean.Meta

def validateRflAttr (declName : Name) : AttrM Unit := do
  let { kind := .thm, constInfo, .. } ← getAsyncConstInfo declName |
    throwError "Could not find {declName}"
  let .thmInfo _info ← traceBlock "isRflTheorem theorem body" constInfo |
    throwError "{declName} is not a theorem"
  -- TODO: Do the actual check

builtin_initialize rflAttr : TagAttribute ←
  registerTagAttribute `rfl "mark theorem as a `rfl`-theorem, to be used by `dsimp`"
    (validate := validateRflAttr) (applicationTime := .afterTypeChecking)
    (asyncMode := .async)


def inferRflAttr (declName : Name) : MetaM Unit := do
  let info ← getConstVal declName
  let isRfl ← forallTelescopeReducing info.type fun _ type => do
    let some (_, lhs, rhs) := type.eq? | return false
    try
      isDefEq lhs rhs
    catch _ =>
      pure false
  if isRfl then
    modifyEnv fun env => rflAttr.ext.addEntry env declName
