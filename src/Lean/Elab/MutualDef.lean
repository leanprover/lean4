/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command

namespace Lean
namespace Elab
namespace Term

def elabMutualDef (vars : Array Expr) (ds : Array Syntax) : TermElabM Unit := do
throwError "WIP mutual def"

end Term

namespace Command

def elabMutualDef (ds : Array Syntax) : CommandElabM Unit :=
runTermElabM none fun vars => Term.elabMutualDef vars ds

end Command
end Elab
end Lean
