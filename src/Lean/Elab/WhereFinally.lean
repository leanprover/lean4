/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Lean.Parser.Term

namespace Lean.Elab

structure WhereFinallyView where
  ref       : Syntax
  tactic    : TSyntax ``Lean.Parser.Tactic.tacticSeq
  deriving Inhabited

def WhereFinallyView.none : WhereFinallyView := { ref := .missing, tactic := ⟨.missing⟩ }

def WhereFinallyView.isNone (o : WhereFinallyView) : Bool := o.ref.isMissing && o.tactic.raw.isMissing

/-- Creates a view of the `finally` section of a `whereDecls` syntax object -/
def mkWhereFinallyView {m} [Monad m] [MonadError m] (stx : TSyntax ``Parser.Term.whereDecls) : m WhereFinallyView := do
  -- Fail gracefully upon partial parses/missing where or finally sections
  let whereFinally := stx.raw[2][0]
  if whereFinally.isMissing then
    return { ref := stx, tactic := ⟨.missing⟩ }
  if !whereFinally[2][0].isMissing then
    throwErrorAt stx "`where ... finally` does not currently support any named sub-sections `| sectionName => ...`"
  let tactic := ⟨whereFinally[1]⟩
  return { ref := whereFinally, tactic }
