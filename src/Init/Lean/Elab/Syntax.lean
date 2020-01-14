/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Command

namespace Lean
namespace Elab
namespace Command

@[builtinCommandElab syntaxCat] def elabDeclareSyntaxCat : CommandElab :=
fun stx => do
  let catName  := stx.getIdAt 1;
  let attrName := catName.appendAfter "Parser";
  env ← getEnv;
  env ← liftIO stx $ Parser.registerParserCategory env attrName catName;
  setEnv env


@[builtinCommandElab syntax] def elabSyntax : CommandElab :=
fun stx =>
  throwError stx ("not implemented yet " ++ toString stx)

end Command
end Elab
end Lean
