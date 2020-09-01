/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Elab.Definition

namespace Lean
namespace Elab

structure MutualDefView :=
(ref           : Syntax)
(modifiers     : Modifiers)
(kind          : Command.DefKind)
(shortDeclName : Name)
(declName      : Name)
(levelNames    : List Name)
(numParams     : Nat)
(type          : Expr) -- including the parameters
(val           : Syntax)

namespace Term

open Meta
open Command (DefView mkDefViewOfAbbrev mkDefViewOfDef mkDefViewOfTheorem)

private def mkDefView {m} [Monad m] [MonadError m] (modifiers : Modifiers) (decl : Syntax) : m DefView :=
let k := decl.getKind;
if k == `Lean.Parser.Command.«abbrev» then
  pure (mkDefViewOfAbbrev modifiers decl)
else if k == `Lean.Parser.Command.«def» then
  pure (mkDefViewOfDef modifiers decl)
else
  throwError "unexpected kind of definition"

def checkModifiers (m₁ m₂ : Modifiers) : TermElabM Unit := do
unless (m₁.isUnsafe == m₂.isUnsafe) $
  throwError "cannot mix unsafe and safe definitions";
unless (m₁.isNoncomputable == m₂.isNoncomputable) $
  throwError "cannot mix computable and non-computable definitions";
unless (m₁.isPartial == m₂.isPartial) $
  throwError "cannot mix partial and non-partial definitions";
pure ()

def elabHeaders (ds : Array Syntax) : TermElabM (Array MutualDefView) :=
ds.foldlM
  (fun (headers : Array MutualDefView) (d : Syntax) => withRef d do
    modifiers ← elabModifiers (d.getArg 0);
    view ← mkDefView modifiers (d.getArg 1);
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
            checkModifiers modifiers firstHeader.modifiers;
            forallTelescopeCompatible type firstHeader.type xs.size fun _ _ _ => pure ())
          (fun ex => match ex with
            | Exception.error ref msg => throw (Exception.error ref ("invalid mutually recursive definitions, " ++ msg))
            | _ => throw ex)
      else
        pure ();
      pure $ headers.push {
        ref           := d,
        modifiers     := modifiers,
        kind          := view.kind,
        shortDeclName := shortDeclName,
        declName      := declName,
        levelNames    := levelNames,
        numParams     := xs.size,
        type          := type,
        val           := view.val
      })
  #[]

def elabMutualDef (vars : Array Expr) (ds : Array Syntax) : TermElabM Unit := do
views ← elabHeaders ds;
throwError "WIP mutual def"

end Term

namespace Command

def elabMutualDef (ds : Array Syntax) : CommandElabM Unit :=
runTermElabM none fun vars => Term.elabMutualDef vars ds

end Command
end Elab
end Lean
