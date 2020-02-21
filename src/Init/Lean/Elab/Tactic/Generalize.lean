/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Meta.Tactic.Generalize
import Init.Lean.Elab.Tactic.ElabTerm

namespace Lean
namespace Elab
namespace Tactic

private def getAuxHypothesisName (stx : Syntax) : Option Name :=
if (stx.getArg 1).isNone then none
else some ((stx.getArg 1).getIdAt 0).eraseMacroScopes

private def getVarName (stx : Syntax) : Name :=
(stx.getIdAt 4).eraseMacroScopes

def evalGeneralizeWithEq (ref : Syntax) (h : Name) (e : Expr) (x : Name) : TacticM Unit :=
liftMetaTactic ref $ fun mvarId => do
  eType    ← Meta.inferType e;
  mvarId   ← Meta.generalize mvarId e x;
  mvarDecl ← Meta.getMVarDecl mvarId;
  -- let target := Lean.mkForall
  pure [] -- TODO

def evalGeneralizeAux (ref : Syntax) (h? : Option Name) (e : Expr) (x : Name) : TacticM Unit :=
match h? with
| none   => liftMetaTactic ref $ fun mvarId => do
  mvarId ← Meta.generalize mvarId e x;
  (_, mvarId) ← Meta.intro1 mvarId false;
  pure [mvarId]
| some h =>
  throwError ref ("WIP " ++ toString h? ++ " : " ++ e ++ " = " ++ x)

@[builtinTactic «generalize»] def evalGeneralize : Tactic :=
fun stx => do
  let h? := getAuxHypothesisName stx;
  let x  := getVarName stx;
  e ← elabTerm (stx.getArg 2) none;
  evalGeneralizeAux stx h? e x

end Tactic
end Elab
end Lean
