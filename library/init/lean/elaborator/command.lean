/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.elaborator.alias
import init.lean.elaborator.basic

namespace Lean
namespace Elab

private def addScopes (cmd : String) (updateNamespace : Bool) : Name → List ElabScope → List ElabScope
| Name.anonymous      scopes := scopes
| (Name.mkString p h) scopes :=
  let scopes := addScopes p scopes;
  let ns     := scopes.head.ns;
  let ns     := if updateNamespace then Name.mkString ns h else ns;
  { cmd := cmd, header := h, ns := ns } :: scopes
| _ _ := [] -- unreachable

@[builtinCommandElab «namespace»] def elabNamespace : CommandElab :=
fun n => do
  let header := (n.getArg 1).getIdentVal;
  modify $ fun s => { scopes := addScopes "namespace" true header s.scopes, .. s };
  ns     ← getNamespace;
  modify $ fun s => { env := registerNamespace s.env ns, .. s }

@[builtinCommandElab «section»] def elabSection : CommandElab :=
fun n => do
  let header := (n.getArg 1).getOptionalIdent;
  ns ← getNamespace;
  modify $ fun s =>
    match header with
    | some header => { scopes := addScopes "section" false header s.scopes, .. s }
    | none        => { scopes := { cmd := "section", header := Name.anonymous, ns := ns } :: s.scopes, .. s }

private def getNumEndScopes : Option Name → Nat
| none     := 1
| (some n) := n.getNumParts

private def checkAnonymousScope : List ElabScope → Bool
| ({ header := Name.anonymous, .. } :: _) := true
| _ := false

private def checkEndHeader : Name → List ElabScope → Bool
| Name.anonymous _ := true
| (Name.mkString p s) ({ header := h, .. } :: scopes) := h.eqStr s && checkEndHeader p scopes
| _ _ := false

@[builtinCommandElab «end»] def elabEnd : CommandElab :=
fun n => do
  s      ← get;
  let header := (n.getArg 1).getOptionalIdent;
  let num    := getNumEndScopes header;
  let scopes := s.scopes;
  if num < scopes.length then
    modify $ fun s => { scopes := s.scopes.drop num, .. s }
  else do {
    -- we keep "root" scope
    modify $ fun s => { scopes := s.scopes.drop (s.scopes.length - 1), .. s };
    throw "invalid 'end', insufficient scopes"
  };
  match header with
  | none => unless (checkAnonymousScope scopes) $ throw "invalid 'end', name is missing"
  | some header => unless (checkEndHeader header scopes) $ throw "invalid 'end', name mismatch"

@[builtinCommandElab «export»] def elabExport : CommandElab :=
fun n => do
  -- `n` is of the form (Command.export "export" <namespace> "(" (null <ids>*) ")")
  let ns  := (n.getArg 1).getIdentVal;
  let ids := (n.getArg 3).getArgs;
  ns ← resolveNamespace ns;
  currNs ← getNamespace;
  when (ns == currNs) $ throw "invalid 'export', self export";
  s ← get;
  let env := s.env;
  aliases ← ids.mfoldl (fun (aliases : List (Name × Name)) (idStx : Syntax) => do {
    let id := idStx.getIdentVal;
    let declName := ns ++ id;
    if env.contains declName then
      pure $ (currNs ++ id, declName) :: aliases
    else do
      logError idStx ("unknown declaration '" ++ toString declName ++ "'");
      pure aliases
    })
    [];
  modify $ fun s => { env := aliases.foldl (fun env p => addAlias env p.1 p.2) s.env, .. s }

/- We just ignore Lean3 notation declaration commands. -/
@[builtinCommandElab «mixfix»] def elabMixfix : CommandElab := fun _ => pure ()
@[builtinCommandElab «reserve»] def elabReserve : CommandElab := fun _ => pure ()
@[builtinCommandElab «notation»] def elabNotation : CommandElab := fun _ => pure ()

end Elab
end Lean
