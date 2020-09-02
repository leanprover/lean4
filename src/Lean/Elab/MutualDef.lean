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

def checkModifiers (m₁ m₂ : Modifiers) : TermElabM Unit := do
unless (m₁.isUnsafe == m₂.isUnsafe) $
  throwError "cannot mix unsafe and safe definitions";
unless (m₁.isNoncomputable == m₂.isNoncomputable) $
  throwError "cannot mix computable and non-computable definitions";
unless (m₁.isPartial == m₂.isPartial) $
  throwError "cannot mix partial and non-partial definitions";
pure ()

def elabHeaders (views : Array DefView) : TermElabM (Array DefViewElabHeader) :=
views.foldlM
  (fun (headers : Array DefViewElabHeader) (view : DefView) => withRef view.ref do
    currNamespace ← getCurrNamespace;
    currLevelNames ← getLevelNames;
    ⟨shortDeclName, declName, levelNames⟩ ← expandDeclId currNamespace currLevelNames view.declId view.modifiers;
    withLevelNames levelNames $ elabBinders view.binders.getArgs fun xs => do
      type ← match view.type? with
        | some typeStx => do
          type ← elabType typeStx;
          synthesizeSyntheticMVarsNoPostponing;
          type ← instantiateMVars type;
          mkForallFVars xs type
        | none => do {
          type ← withRef view.binders $ mkFreshTypeMVar;
          mkForallFVars xs type
        };
      if h : 0 < headers.size then
        let firstHeader := headers.get ⟨0, h⟩;
        catch
          (do
            unless (xs.size == firstHeader.numParams) $
              throwError "number of parameters mismatch";
            unless (levelNames == firstHeader.levelNames) $
              throwError "universe parameters mismatch in mutual definition";
            checkModifiers view.modifiers firstHeader.modifiers;
            forallTelescopeCompatible type firstHeader.type xs.size fun _ _ _ => pure ())
          (fun ex => match ex with
            | Exception.error ref msg => throw (Exception.error ref ("invalid mutually recursive definitions, " ++ msg))
            | _ => throw ex)
      else
        pure ();
      pure $ headers.push {
        ref           := view.ref,
        modifiers     := view.modifiers,
        kind          := view.kind,
        shortDeclName := shortDeclName,
        declName      := declName,
        levelNames    := levelNames,
        numParams     := xs.size,
        type          := type,
        val           := view.val
      })
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
