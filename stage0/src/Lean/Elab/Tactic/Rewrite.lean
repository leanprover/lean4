/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm

namespace Lean
namespace Elab
namespace Tactic

@[builtinMacro Lean.Parser.Tactic.rewriteSeq] def expandRewriteTactic : Macro :=
fun stx =>
  let seq := ((stx.getArg 1).getArg 1).getArgs.getSepElems;
  let loc := stx.getArg 2;
  pure $ mkNullNode $ seq.map fun rwRule => Syntax.node `Lean.Parser.Tactic.rewrite #[stx.getArg 0, rwRule, loc]

@[builtinTactic «rewrite»] def evalRewrite : Tactic :=
fun stx =>  do
  logInfo $ "WIP " ++ stx;
  pure ()

end Tactic
end Elab
end Lean
