/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Elab.Definition

namespace Lean
namespace Elab

/- DefView after elaborating the header. -/
structure DefViewElabHeader :=
(ref           : Syntax)
(modifiers     : Modifiers)
(kind          : DefKind)
(shortDeclName : Name)
(declName      : Name)
(levelNames    : List Name)
(numParams     : Nat)
(type          : Expr) -- including the parameters
(val           : Syntax)

namespace Term

open Meta

private def checkModifiers (m₁ m₂ : Modifiers) : TermElabM Unit := do
unless (m₁.isUnsafe == m₂.isUnsafe) $
  throwError "cannot mix unsafe and safe definitions";
unless (m₁.isNoncomputable == m₂.isNoncomputable) $
  throwError "cannot mix computable and non-computable definitions";
unless (m₁.isPartial == m₂.isPartial) $
  throwError "cannot mix partial and non-partial definitions";
pure ()

private def checkKinds (k₁ k₂ : DefKind) : TermElabM Unit := do
unless (k₁.isExample == k₂.isExample) $
  throwError "cannot mix examples and definitions"; -- Reason: we should discard examples
unless (k₁.isTheorem == k₂.isTheorem) $
  throwError "cannot mix theorems and definitions"; -- Reason: we will eventually elaborate theorems in `Task`s.
pure ()

private def check (prevHeaders : Array DefViewElabHeader) (newHeader : DefViewElabHeader) : TermElabM Unit :=
if h : 0 < prevHeaders.size then
  let firstHeader := prevHeaders.get ⟨0, h⟩;
  catch
   (do
     checkModifiers newHeader.modifiers firstHeader.modifiers;
     checkKinds newHeader.kind firstHeader.kind)
   (fun ex => match ex with
     | Exception.error ref msg => throw (Exception.error ref ("invalid mutually recursive definitions, " ++ msg))
     | _ => throw ex)
else
  pure ()

private def elabFunType (xs : Array Expr) (view : DefView) : TermElabM Expr :=
match view.type? with
| some typeStx => do
  type ← elabType typeStx;
  synthesizeSyntheticMVarsNoPostponing;
  type ← instantiateMVars type;
  mkForallFVars xs type
| none => do
  type ← withRef view.binders $ mkFreshTypeMVar;
  mkForallFVars xs type

def elabHeaders (views : Array DefView) : TermElabM (Array DefViewElabHeader) :=
views.foldlM
  (fun (headers : Array DefViewElabHeader) (view : DefView) => withRef view.ref do
    currNamespace ← getCurrNamespace;
    currLevelNames ← getLevelNames;
    ⟨shortDeclName, declName, levelNames⟩ ← expandDeclId currNamespace currLevelNames view.declId view.modifiers;
    withLevelNames levelNames $ elabBinders view.binders.getArgs fun xs => do
      type ← elabFunType xs view;
      let newHeader : DefViewElabHeader := {
        ref           := view.ref,
        modifiers     := view.modifiers,
        kind          := view.kind,
        shortDeclName := shortDeclName,
        declName      := declName,
        levelNames    := levelNames,
        numParams     := xs.size,
        type          := type,
        val           := view.val
      };
      check headers newHeader;
      pure $ headers.push newHeader)
  #[]

def elabMutualDef (vars : Array Expr) (views : Array DefView) : TermElabM Unit := do
views ← elabHeaders views;
throwError "WIP mutual def"

end Term

namespace Command

def elabMutualDef (ds : Array Syntax) : CommandElabM Unit := do
views ← ds.mapM fun d => do {
  modifiers ← elabModifiers (d.getArg 0);
  mkDefView modifiers (d.getArg 1)
};
runTermElabM none fun vars => Term.elabMutualDef vars views

end Command
end Elab
end Lean
