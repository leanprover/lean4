/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Match
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Induction

namespace Lean
namespace Elab
namespace Tactic

structure AuxMatchTermState :=
(nextIdx : Nat := 1)
(cases   : Array Syntax := #[])

private def mkAuxiliaryMatchTermAux (parentTag : Name) (matchTac : Syntax) : StateT AuxMatchTermState MacroM Syntax := do
let alts := (matchTac.getArg 5).getArgs;
newAlts ← alts.mapSepElemsM fun alt => do {
  let alt    := alt.updateKind `Lean.Parser.Term.matchAlt;
  let holeOrTactic := alt.getArg 2;
  if holeOrTactic.isOfKind `Lean.Parser.Term.namedHole then
    pure alt
  else if holeOrTactic.isOfKind `Lean.Parser.Term.hole then do
    s ← get;
    let holeName := mkIdentFrom holeOrTactic (parentTag ++ (`match).appendIndexAfter s.nextIdx);
    newHole ← `(?$holeName:ident);
    modify fun s => { s with nextIdx := s.nextIdx + 1};
    pure $ alt.setArg 2 newHole
  else withFreshMacroScope do
    newHole ← `(?rhs);
    let newHoleId := newHole.getArg 1;
    newCase ← `(tactic| case $newHoleId $holeOrTactic);
    modify fun s => { s with cases := s.cases.push newCase };
    pure $ alt.setArg 2 newHole
};
let result  := matchTac.updateKind `Lean.Parser.Term.match;
let result  := result.setArg 5 (mkNullNode newAlts);
pure result

private def mkAuxiliaryMatchTerm (parentTag : Name) (matchTac : Syntax) : MacroM (Syntax × Array Syntax) := do
(matchTerm, s) ← (mkAuxiliaryMatchTermAux parentTag matchTac).run {};
pure (matchTerm, s.cases)

def mkTacticSeq (ref : Syntax) (tacs : Array Syntax) : Syntax :=
mkSepStx tacs (mkAtomFrom ref "; ")

@[builtinTactic Lean.Parser.Tactic.match] def evalMatch : Tactic :=
fun stx => do
  tag ← getMainTag;
  (matchTerm, cases) ← liftMacroM $ mkAuxiliaryMatchTerm tag stx;
  refineMatchTerm ← `(tactic| refine $matchTerm);
  let stxNew := mkTacticSeq stx (#[refineMatchTerm] ++ cases);
  withMacroExpansion stx stxNew $ evalTactic stxNew

end Tactic
end Elab
end Lean
