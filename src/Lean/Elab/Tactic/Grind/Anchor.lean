/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
namespace Lean.Elab.Tactic.Grind
open Meta Grind

public def elabAnchorRef (anchor : TSyntax `hexnum) : CoreM AnchorRef := do
  let numDigits := anchor.getHexNumSize
  let val := anchor.getHexNumVal
  if val >= UInt64.size then
    throwError "invalid anchor, value is too big"
  let anchorPrefix := val.toUInt64
  return { numDigits, anchorPrefix }

end Lean.Elab.Tactic.Grind
