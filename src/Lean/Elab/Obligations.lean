/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Lean.Parser.Term

namespace Lean.Elab

structure Obligations where
  ref       : Syntax
  tactic    : TSyntax ``Lean.Parser.Tactic.tacticSeq
  deriving Inhabited

def Obligations.none : Obligations := { ref := .missing, tactic := ⟨.missing⟩ }

def Obligations.isNone (o : Obligations) : Bool := o.ref.isMissing && o.tactic.raw.isMissing

/-- Takes apart a `obligationsBy` syntax object -/
def mkObligations {m} [Monad m] [MonadError m] (stx : TSyntax ``Parser.Term.obligationsBy) : m Obligations := do
  -- Fail gracefully upon partial parses
  if let .missing := stx.raw then
    return { ref := stx, tactic := ⟨.missing⟩ }
  if let some ob := stx.raw.getOptional? then
    match ob with
    | `(Parser.Term.obligationsBy| obligations_by $tactic) =>
      return { ref := stx, tactic }
    | `(Parser.Term.obligationsBy| obligations_by) =>
      return { ref := stx, tactic := ⟨.missing⟩ }
    | `(Parser.Term.obligationsBy| $_) =>
      throwErrorAt stx "`obligations_by` does not currently support any named sub-sections `| sectionName => ...`"
  else return .none
