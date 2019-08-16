/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.modifiers
import init.lean.elaborator.alias
import init.lean.elaborator.basic

namespace Lean
namespace Elab

/- Check whether `ns ++ id` is a valid namepace name and/or there are aliases names `ns ++ id`. -/
private def resolveQualifiedName (env : Environment) (ns : Name) (id : Name) : List Name :=
let resolvedId  := ns ++ id;
let resolvedIds := getAliases env resolvedId;
if env.contains resolvedId && (!id.isAtomic || !isProtected env resolvedId) then resolvedId :: resolvedIds
else resolvedIds

/- Check surrounding namespaces -/
private def resolveUsingNamespace (env : Environment) (id : Name) : Name → List Name
| ns@(Name.mkString p _) =>
  match resolveQualifiedName env ns id with
  | [] => resolveUsingNamespace p
  | resolvedIds => resolvedIds
| _ => []

/- Check exact name -/
private def resolveExact (env : Environment) (id : Name) : Option Name :=
if id.isAtomic then none
else
  let resolvedId := id.replacePrefix rootNamespace Name.anonymous;
  if env.contains resolvedId then some resolvedId else none

/- Check open namespaces -/
private def resolveOpenDecls (env : Environment) (id : Name) : List OpenDecl → List Name → List Name
| [], resolvedIds => resolvedIds
| OpenDecl.simple ns exs :: openDecls, resolvedIds =>
  if exs.elem id then resolveOpenDecls openDecls resolvedIds
  else
    let newResolvedIds := resolveQualifiedName env ns id;
    resolveOpenDecls openDecls (newResolvedIds ++ resolvedIds)
| OpenDecl.explicit openedId resolvedId :: openDecls, resolvedIds =>
  let resolvedIds := if id == openedId then resolvedId :: resolvedIds else resolvedIds;
  resolveOpenDecls openDecls resolvedIds

private def resolveNameAux (env : Environment) (ns : Name) (openDecls : List OpenDecl) : Name → Nat → List (Nat × Name)
| id@(Name.mkString p _), projSize =>
  match resolveUsingNamespace env id ns with
  | resolvedIds@(_ :: _) => resolvedIds.eraseDups.map $ fun id => (projSize, id)
  | [] =>
  match resolveExact env id with
  | some newId => [(projSize, newId)]
  | none =>
  let resolvedIds := if env.contains id then [id] else [];
  let resolvedIds := resolveOpenDecls env id openDecls resolvedIds;
  let resolvedIds := getAliases env id ++ resolvedIds;
  match resolvedIds with
  | resolvedIds@(_ :: _) => resolvedIds.eraseDups.map $ fun id => (projSize, id)
  | [] => resolveNameAux p (projSize + 1)
| _, _ => []

def resolveName (id : Name) : Elab (List (Nat × Name)) :=
do env ← getEnv;
   ns  ← getNamespace;
   openDecls ← getOpenDecls;
   pure $ resolveNameAux env ns openDecls id 0

private partial def preresolveNamesAux {α} (env : Environment) (ns : Name) (openDecls : List OpenDecl) : Syntax α → Syntax α
| Syntax.node k args             => Syntax.node k (args.map preresolveNamesAux)
| Syntax.ident info rawVal val _ => Syntax.ident info rawVal val (resolveNameAux env ns openDecls val 0)
| stx                            => stx

def preresolveNames {α} (stx : Syntax α) : Elab (Syntax α) :=
do env ← getEnv;
   ns  ← getNamespace;
   openDecls ← getOpenDecls;
   pure $ preresolveNamesAux env ns openDecls stx

end Elab
end Lean
