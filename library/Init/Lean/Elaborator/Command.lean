/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elaborator.Alias
import Init.Lean.Elaborator.Basic
import Init.Lean.Elaborator.ResolveName
import Init.Lean.Elaborator.Term

namespace Lean
namespace Elab

private def addScopes (cmd : String) (updateNamespace : Bool) : Name → List ElabScope → List ElabScope
| Name.anonymous,      scopes => scopes
| Name.mkString p h,   scopes =>
  let scopes := addScopes p scopes;
  let ns     := scopes.head!.ns;
  let ns     := if updateNamespace then Name.mkString ns h else ns;
  { cmd := cmd, header := h, ns := ns } :: scopes
| _, _ => [] -- unreachable

@[builtinCommandElab «namespace»] def elabNamespace : CommandElab :=
fun n => do
  let header := n.getIdAt 1;
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
| none   => 1
| some n => n.getNumParts

private def checkAnonymousScope : List ElabScope → Bool
| { header := Name.anonymous, .. } :: _   => true
| _ => false

private def checkEndHeader : Name → List ElabScope → Bool
| Name.anonymous, _ => true
| Name.mkString p s,   { header := h, .. } :: scopes   => h.eqStr s && checkEndHeader p scopes
| _, _ => false

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
  let ns  := n.getIdAt 1;
  ns ← resolveNamespace ns;
  currNs ← getNamespace;
  when (ns == currNs) $ throw "invalid 'export', self export";
  env ← getEnv;
  let ids := (n.getArg 3).getArgs;
  aliases ← ids.mfoldl (fun (aliases : List (Name × Name)) (idStx : Syntax) => do {
    let id := idStx.getId;
    let declName := ns ++ id;
    if env.contains declName then
      pure $ (currNs ++ id, declName) :: aliases
    else do
      logUnknownDecl idStx declName;
      pure aliases
    })
    [];
  modify $ fun s => { env := aliases.foldl (fun env p => addAlias env p.1 p.2) s.env, .. s }

def addOpenDecl (d : OpenDecl) : Elab Unit :=
modifyScope $ fun scope => { openDecls := d :: scope.openDecls, .. scope }

def elabOpenSimple (n : SyntaxNode) : Elab Unit :=
let nss := n.getArg 0;
nss.mforArgs $ fun ns => do
  ns ← resolveNamespace ns.getId;
  addOpenDecl (OpenDecl.simple ns [])

def elabOpenOnly (n : SyntaxNode) : Elab Unit :=
do
let ns  := n.getIdAt 0;
ns ← resolveNamespace ns;
let ids := n.getArg 2;
ids.mforArgs $ fun idStx => do
  let id := idStx.getId;
  let declName := ns ++ id;
  env ← getEnv;
  if env.contains declName then
    addOpenDecl (OpenDecl.explicit id declName)
  else
    logUnknownDecl idStx declName

def elabOpenHiding (n : SyntaxNode) : Elab Unit :=
do
let ns := n.getIdAt 0;
ns ← resolveNamespace ns;
let idsStx := n.getArg 2;
env ← getEnv;
ids : List Name ← idsStx.mfoldArgs (fun idStx ids => do
  let id := idStx.getId;
  let declName := ns ++ id;
  if env.contains declName then
    pure (id::ids)
  else do
    logUnknownDecl idStx declName;
    pure ids)
  [];
addOpenDecl (OpenDecl.simple ns ids)

def elabOpenRenaming (n : SyntaxNode) : Elab Unit :=
do
let ns := n.getIdAt 0;
ns ← resolveNamespace ns;
let rs := (n.getArg 2);
rs.mforSepArgs $ fun stx => do
  let fromId   := stx.getIdAt 0;
  let toId     := stx.getIdAt 2;
  let declName := ns ++ fromId;
  env ← getEnv;
  if env.contains declName then
    addOpenDecl (OpenDecl.explicit toId declName)
  else
    logUnknownDecl stx declName

@[builtinCommandElab «open»] def elabOpen : CommandElab :=
fun n => do
  let body := (n.getArg 1).asNode;
  let k    := body.getKind;
  if k == `Lean.Parser.Command.openSimple then
    elabOpenSimple body
  else if k == `Lean.Parser.Command.openOnly then
    elabOpenOnly body
  else if k == `Lean.Parser.Command.openHiding then
    elabOpenHiding body
  else
    elabOpenRenaming body

def addUniverse (idStx : Syntax) : Elab Unit :=
do
let id := idStx.getId;
univs ← getUniverses;
if univs.elem id then
  logError idStx ("a universe named '" ++ toString id ++ "' has already been declared in this Scope")
else
  modifyScope $ fun scope => { univs := id :: scope.univs, .. scope }

@[builtinCommandElab «universe»] def elabUniverse : CommandElab :=
fun n => do
  addUniverse (n.getArg 1)

@[builtinCommandElab «universes»] def elabUniverses : CommandElab :=
fun n => do
  let idsStx := n.getArg 1;
  idsStx.mforArgs addUniverse

@[builtinCommandElab «init_quot»] def elabInitQuot : CommandElab :=
fun _ => do
  env ← getEnv;
  match env.addDecl Declaration.quotDecl with
  | Except.ok env   => setEnv env
  | Except.error ex => logElabException (ElabException.kernel ex)

@[builtinCommandElab «variable»] def elabVariable : CommandElab :=
fun n => do
  runIO (IO.println n.val);
  pure ()

@[builtinCommandElab «resolve_name»] def elabResolveName : CommandElab :=
fun n => do
  let id := n.getIdAt 1;
  resolvedIds ← resolveName id;
  pos ← getPosition;
  runIO (IO.println (toString pos ++ " " ++ toString resolvedIds));
  pure ()

@[builtinCommandElab «preterm»] def elabPreTerm : CommandElab :=
fun n => do
  let s := n.getArg 1;
  runIO (IO.println s);
  pre ← toPreTerm (s.lift Expr);
  runIO (IO.println pre.dbgToString);
  pure ()

@[builtinCommandElab «elab»] def elabElab : CommandElab :=
fun n => do
  let s := n.getArg 1;
  r ← elabTerm (s.lift Expr);
  match r with
  | Syntax.other e => runIO (IO.println e.dbgToString)
  | other          => do
    runIO (IO.println other);
    throw "failed to elaborate syntax"

/- We just ignore Lean3 notation declaration commands. -/
@[builtinCommandElab «mixfix»] def elabMixfix : CommandElab := fun _ => pure ()
@[builtinCommandElab «reserve»] def elabReserve : CommandElab := fun _ => pure ()
@[builtinCommandElab «notation»] def elabNotation : CommandElab := fun _ => pure ()

end Elab
end Lean
