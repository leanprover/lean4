/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/

namespace Lean
namespace Elab

def expandOptDeclSig (stx : Syntax) : Syntax × Option Syntax :=
-- many Term.bracketedBinder >> Term.optType
let binders := stx.getArg 0;
let optType := stx.getArg 1; -- optional (parser! " : " >> termParser)
if optType.isNone then
  (binders, none)
else
  let typeSpec := optType.getArg 0;
  (binders, some $ typeSpec.getArg 1)

def expandDeclSig (stx : Syntax) : Syntax × Syntax :=
-- many Term.bracketedBinder >> Term.typeSpec
let binders := stx.getArg 0;
let typeSpec := stx.getArg 1;
(binders, typeSpec.getArg 1)

end Elab
end Lean
