/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term
import Lean.Elab.Match
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Induction

namespace Lean.Elab.Tactic
open Meta

open TSyntax.Compat in
open Parser.Tactic in
private def mkAuxiliaryMatchTerm (parentTag : Name) (matchTac : Syntax) : MacroM (Term × Array Syntax) := do
  let matchAlts := matchTac[5]
  let alts      := matchAlts[0].getArgs
  let mut newAlts := #[]
  let mut nextIdx := 1
  let mut newCases := #[]
  for alt in alts do
    let alt := alt.setKind ``Parser.Term.matchAlt
    let holeOrTacticSeq := alt[3]
    -- must generate a separate mvar for each `| $patGroup | ... => ...` as they can have different local contexts
    for patGroup in alt[1].getSepArgs do
      let mut alt := alt.setArg 1 (mkNullNode #[patGroup])
      if holeOrTacticSeq.isOfKind ``Parser.Term.syntheticHole then
        pure ()
      else if holeOrTacticSeq.isOfKind ``Parser.Term.hole then
        let tag := if alts.size > 1 then parentTag ++ (`match).appendIndexAfter nextIdx else parentTag
        let holeName := mkIdentFrom holeOrTacticSeq tag
        let newHole ← `(?$holeName:ident)
        nextIdx := nextIdx + 1
        alt := alt.setArg 3 newHole
      else
        let newHole ← withFreshMacroScope `(?rhs)
        let newHoleId := newHole.raw[1]
        let newCase ← `(tactic|
          case $newHoleId:ident =>%$(alt[2])
            -- annotate `| ... =>` with state after `case`
            with_annotate_state $(mkNullNode #[alt[0], alt[2]]) skip
            $holeOrTacticSeq)
        newCases := newCases.push newCase
        alt := alt.setArg 3 newHole
      newAlts := newAlts.push alt
  let result  := matchTac.setKind ``Parser.Term.«match»
  let result  := result.setArg 5 (mkNode ``Parser.Term.matchAlts #[mkNullNode newAlts])
  return (result, newCases)

@[builtin_tactic Lean.Parser.Tactic.match]
def evalMatch : Tactic := fun stx => do
  let tag ← getMainTag
  let (matchTerm, casesStx) ← liftMacroM <| mkAuxiliaryMatchTerm tag stx
  let refineMatchTerm ← `(tactic| refine no_implicit_lambda% $matchTerm)
  let stxNew := mkNullNode (#[refineMatchTerm] ++ casesStx)
  withMacroExpansion stx stxNew <| evalTactic stxNew

end Lean.Elab.Tactic
