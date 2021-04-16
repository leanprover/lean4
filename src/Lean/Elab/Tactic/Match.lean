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

/- Erase auxiliary `_discr` variables introduced by `match`-expression elaborator -/
@[builtinTactic Lean.Parser.Tactic.eraseAuxDiscrs]
def evalEraseAuxDiscrs : Tactic := fun _ => do
  withMainContext do
    let lctx ← getLCtx
    let auxDecls := lctx.foldl (init := []) fun auxDecls localDecl =>
      if Term.isAuxDiscrName localDecl.userName then
        localDecl.fvarId :: auxDecls
      else
        auxDecls
    let mut mvarId ← getMainGoal
    for auxDecl in auxDecls do
      mvarId ← tryClear mvarId auxDecl
    replaceMainGoal [mvarId]

structure AuxMatchTermState where
  nextIdx : Nat := 1
  «cases» : Array Syntax := #[]

private def mkAuxiliaryMatchTermAux (parentTag : Name) (matchTac : Syntax) : StateT AuxMatchTermState MacroM Syntax := do
  let matchAlts := matchTac[5]
  let alts      := matchAlts[0].getArgs
  let newAlts ← alts.mapM fun alt => do
    let alt    := alt.setKind ``Parser.Term.matchAlt
    let holeOrTacticSeq := alt[3]
    if holeOrTacticSeq.isOfKind ``Parser.Term.syntheticHole then
      pure alt
    else if holeOrTacticSeq.isOfKind ``Parser.Term.hole then
      let s ← get
      let tag := if alts.size > 1 then parentTag ++ (`match).appendIndexAfter s.nextIdx else parentTag
      let holeName := mkIdentFrom holeOrTacticSeq tag
      let newHole ← `(?$holeName:ident)
      modify fun s => { s with nextIdx := s.nextIdx + 1}
      pure <| alt.setArg 3 newHole
    else withFreshMacroScope do
      let newHole ← `(?rhs)
      let newHoleId := newHole[1]
      let newCase ← `(tactic| case $newHoleId =>%$(alt[2]) eraseAuxDiscrs!; ($holeOrTacticSeq:tacticSeq) )
      modify fun s => { s with cases := s.cases.push newCase }
      pure <| alt.setArg 3 newHole
  let result  := matchTac.setKind ``Parser.Term.«match»
  let result  := result.setArg 5 (mkNode ``Parser.Term.matchAlts #[mkNullNode newAlts])
  pure result

private def mkAuxiliaryMatchTerm (parentTag : Name) (matchTac : Syntax) : MacroM (Syntax × Array Syntax) := do
  let (matchTerm, s) ← mkAuxiliaryMatchTermAux parentTag matchTac |>.run {}
  pure (matchTerm, s.cases)

@[builtinTactic Lean.Parser.Tactic.match]
def evalMatch : Tactic := fun stx => do
  let tag ← getMainTag
  let (matchTerm, cases) ← liftMacroM <| mkAuxiliaryMatchTerm tag stx
  let refineMatchTerm ← `(tactic| refine $matchTerm)
  let stxNew := mkNullNode (#[refineMatchTerm] ++ cases)
  withMacroExpansion stx stxNew <| evalTactic stxNew

end Lean.Elab.Tactic
