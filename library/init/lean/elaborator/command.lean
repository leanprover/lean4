/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.elaborator.basic

namespace Lean
namespace Elab

@[builtinCommandElab «namespace»] def elabNamespace : CommandElab :=
fun n => do
  header ← (n.getArg 1).getIdentVal;
  modify $ fun s =>
    let scope : ElabScope := { cmd := "namespace", header := header };
    { scopes := scope :: s.scopes, .. s }

@[builtinCommandElab «section»] def elabSection : CommandElab :=
fun n => do
  header ← (n.getArg 1).getOptionalIdent;
  let header := header.getOrElse Name.anonymous;
  modify $ fun s =>
    let scope : ElabScope := { cmd := "section", header := header };
    { scopes := scope :: s.scopes, .. s }

@[builtinCommandElab «end»] def elabEnd : CommandElab :=
fun n => do
  s ← get;
  match s.scopes with
  | [] => throw "invalid 'end', there is no open scope"
  | (scope::scopes) => do
    modify $ fun s => { scopes := scopes, .. s };
    header ← (n.getArg 1).getOptionalIdent;
    let header := header.getOrElse Name.anonymous;
    unless (scope.header == header) $ throw "invalid 'end', name mismatch"

end Elab
end Lean
