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

private def mkAuxiliaryMatchTermAux (matchTac : Syntax) : StateT (Array Syntax) MacroM Syntax := do
let alts := (matchTac.getArg 5).getArgs;
newAlts ← alts.mapSepElemsM fun alt => do {
  let alt    := alt.updateKind `Lean.Parser.Term.matchAlt;
  let holeOrTactic := alt.getArg 2;
  if isHoleRHS holeOrTactic then
    pure alt
  else withFreshMacroScope do
    newHole ← `(?rhs);
    let newHoleId := newHole.getArg 1;
    newCase ← `(tactic| case $newHoleId $holeOrTactic);
    modify fun cases => cases.push newCase;
    pure $ alt.setArg 2 newHole
};
let result  := matchTac.updateKind `Lean.Parser.Term.match;
let result  := result.setArg 5 (mkNullNode newAlts);
pure result

private def mkAuxiliaryMatchTerm (matchTac : Syntax) : MacroM (Syntax × Array Syntax) :=
(mkAuxiliaryMatchTermAux matchTac).run #[]

def mkTacticSeq (ref : Syntax) (tacs : Array Syntax) : Syntax :=
let seq := mkSepStx tacs (mkAtomFrom ref "; ");
Syntax.node `Lean.Parser.Tactic.seq #[seq]

@[builtinTactic Lean.Parser.Tactic.match] def evalMatch : Tactic :=
fun stx => do
  (matchTerm, cases) ← liftMacroM $ mkAuxiliaryMatchTerm stx;
  refineMatchTerm ← `(tactic| refine $matchTerm);
  let stxNew := mkTacticSeq stx (#[refineMatchTerm] ++ cases);
  withMacroExpansion stx stxNew $ evalTactic stxNew

end Tactic
end Elab
end Lean
