/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Hygiene
import Init.Lean.Modifiers
import Init.Lean.Elab.Alias

namespace Lean
namespace Elab

inductive OpenDecl
| simple   (ns : Name) (except : List Name)
| explicit (id : Name) (declName : Name)

namespace OpenDecl
instance : Inhabited OpenDecl := ⟨simple Name.anonymous []⟩

instance : HasToString OpenDecl :=
⟨fun decl => match decl with
 | explicit id decl => toString id ++ " → " ++ toString decl
 | simple ns ex     => toString ns ++ (if ex == [] then "" else " hiding " ++ toString ex)⟩

end OpenDecl

def rootNamespace := `_root_

def removeRoot (n : Name) : Name :=
n.replacePrefix rootNamespace Name.anonymous

/- Global name resolution -/

/- Check whether `ns ++ id` is a valid namepace name and/or there are aliases names `ns ++ id`. -/
private def resolveQualifiedName (env : Environment) (ns : Name) (id : Name) : List Name :=
let resolvedId  := ns ++ id;
let resolvedIds := getAliases env resolvedId;
if env.contains resolvedId && (!id.isAtomic || !isProtected env resolvedId) then resolvedId :: resolvedIds
else resolvedIds

/- Check surrounding namespaces -/
private def resolveUsingNamespace (env : Environment) (id : Name) : Name → List Name
| ns@(Name.str p _ _) =>
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

private def resolveGlobalNameAux (env : Environment) (ns : Name) (openDecls : List OpenDecl)
    (extractionResult : ExtractMacroScopesResult) : Name → List String → List (Name × List String)
| id@(Name.str p s _), projs =>
  -- NOTE: we assume that macro scopes always belong to the projected constant, not the projections
  let id := addMacroScopes extractionResult.mainModule id extractionResult.scopes;
  match resolveUsingNamespace env id ns with
  | resolvedIds@(_ :: _) => resolvedIds.eraseDups.map $ fun id => (id, projs)
  | [] =>
  match resolveExact env id with
  | some newId => [(newId, projs)]
  | none =>
  let resolvedIds := if env.contains id then [id] else [];
  let resolvedIds := resolveOpenDecls env id openDecls resolvedIds;
  let resolvedIds := getAliases env id ++ resolvedIds;
  match resolvedIds with
  | resolvedIds@(_ :: _) => resolvedIds.eraseDups.map $ fun id => (id, projs)
  | [] => resolveGlobalNameAux p (s::projs)
| _, _ => []

def resolveGlobalName (env : Environment) (ns : Name) (openDecls : List OpenDecl) (id : Name) : List (Name × List String) :=
-- decode macro scopes from name before recursion
let extractionResult := extractMacroScopes id;
resolveGlobalNameAux env ns openDecls extractionResult extractionResult.name []

/- Namespace resolution -/

def resolveNamespaceUsingScope (env : Environment) (n : Name) : Name → Option Name
| Name.anonymous      => none
| ns@(Name.str p _ _) => if isNamespace env (ns ++ n) then some (ns ++ n) else resolveNamespaceUsingScope p
| _                   => unreachable!

def resolveNamespaceUsingOpenDecls (env : Environment) (n : Name) : List OpenDecl → Option Name
| []                          => none
| OpenDecl.simple ns [] :: ds =>  if isNamespace env (ns ++ n) then some (ns ++ n) else resolveNamespaceUsingOpenDecls ds
| _ :: ds                     => resolveNamespaceUsingOpenDecls ds

/-
Given a name `id` try to find namespace it refers to. The resolution procedure works as follows
1- If `id` is the extact name of an existing namespace, then return `id`
2- If `id` is in the scope of `namespace` commands the namespace `s_1. ... . s_n`,
   then return `s_1 . ... . s_i ++ n` if it is the name of an existing namespace. We search "backwards".
3- Finally, for each command `open N`, return `N ++ n` if it is the name of an existing namespace.
   We search "backwards" again. That is, we try the most recent `open` command first.
   We only consider simple `open` commands.
-/
def resolveNamespace (env : Environment) (ns : Name) (openDecls : List OpenDecl) (id : Name) : Option Name :=
if isNamespace env id then some id
else match resolveNamespaceUsingScope env id ns with
  | some n => some n
  | none   =>
    match resolveNamespaceUsingOpenDecls env id openDecls with
    | some n => some n
    | none   => none

end Elab
end Lean
