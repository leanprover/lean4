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

private def addScopes (cmd : String) : Name → Name → List ElabScope → List ElabScope
| Name.anonymous ns scopes := scopes
| (Name.mkString p h) ns scopes :=
  let ns := Name.mkString ns h;
  { cmd := cmd, header := h, ns := ns.mkString h } :: addScopes p ns scopes
| _ _ _ := [] -- unreachable

@[builtinCommandElab «namespace»] def elabNamespace : CommandElab :=
fun n => do
  ns     ← getNamespace;
  header ← (n.getArg 1).getIdentVal;
  modify $ fun s => { scopes := addScopes "namespace" header ns s.scopes, .. s };
  ns     ← getNamespace;
  modify $ fun s => { env := registerNamespace s.env ns }

@[builtinCommandElab «section»] def elabSection : CommandElab :=
fun n => do
  ns     ← getNamespace;
  header ← (n.getArg 1).getOptionalIdent;
  modify $ fun s =>
    match header with
    | some header => { scopes := addScopes "section" header ns s.scopes, .. s }
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
  header ← (n.getArg 1).getOptionalIdent;
  let num    := getNumEndScopes header;
  let scopes := s.scopes;
  modify $ fun s => { scopes := s.scopes.drop num, .. s };
  when (num > scopes.length) $ throw "invalid 'end', insufficient scopes";
  match header with
  | none => unless (checkAnonymousScope scopes) $ throw "invalid 'end', name is missing"
  | some header => unless (checkEndHeader header scopes) $ throw "invalid 'end', name mismatch"

/- We just ignore Lean3 notation declaration commands. -/
@[builtinCommandElab «mixfix»] def elabMixfix : CommandElab := fun _ => pure ()
@[builtinCommandElab «reserve»] def elabReserve : CommandElab := fun _ => pure ()
@[builtinCommandElab «notation»] def elabNotation : CommandElab := fun _ => pure ()

end Elab
end Lean
