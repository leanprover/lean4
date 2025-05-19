prelude

import Lean.Attributes

open Lean

namespace Lean

def validateRflAttr (declName : Name) : AttrM Unit := do
  let { kind := .thm, constInfo, .. } ← getAsyncConstInfo declName |
    throwError "Could not find {declName}"
  let .thmInfo _info ← traceBlock "isRflTheorem theorem body" constInfo |
    throwError "{declName} is not a theorem"
  -- TODO: Do the actual check

builtin_initialize rflAttr : TagAttribute ←
  -- TODO: We could validate even after after header elaboration, but thats not an `applicationTime`
  -- we have yet
  registerTagAttribute `rfl "mark theorem as a `rfl`-theorem, to be used by `dsimp`"
    (validate := validateRflAttr) (applicationTime := .afterTypeChecking)
