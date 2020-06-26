/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Elab.Definition

namespace Lean
namespace Elab
namespace Command

structure InductiveView :=
(ref           : Syntax)
(modifiers     : Modifiers)
(declId        : Syntax)
(binders       : Syntax)
(type?         : Option Syntax)
(introRules    : Array Syntax)

instance InductiveView.inhabited : Inhabited InductiveView :=
⟨{ ref := arbitrary _, modifiers := {}, declId := arbitrary _, binders := arbitrary _, type? := none, introRules := #[] }⟩

def mkInductive (ref : Syntax) (declName : Name) (explictLevelNames : List Name) (vars : Array Expr) (xs : Array Expr) (type : Expr) (intros : Array Syntax)
    : TermElabM Declaration := do
Term.throwError ref ref

def elabInductiveCore (views : Array InductiveView) : CommandElabM Unit := do
let ref := (views.get! 0).ref;
throwError ref ("WIP\n" ++ toString (views.map (fun (v : InductiveView) => v.ref)))
-- pure ()
/-
withDeclId declId $ fun name => do
  declName          ← mkDeclName modifiers name;
  checkNotAlreadyDeclared ref declName;
  applyAttributes ref declName modifiers.attrs AttributeApplicationTime.beforeElaboration;
  explictLevelNames ← getLevelNames;
  decl ← runTermElabM declName $ fun vars => Term.elabBinders binders.getArgs $ fun xs => do {
    -- TODO
    pure ()
  };

  throwError ref (ref ++ "\n" ++ toString explictLevelNames)
-/

end Command
end Elab
end Lean
