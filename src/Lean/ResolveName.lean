/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Data.OpenDecl
import Lean.Hygiene
import Lean.Modifiers
import Lean.Exception

namespace Lean
/-!
  We use aliases to implement the `export <id> (<id>+)` command.
  An `export A (x)` in the namespace `B` produces an alias `B.x ~> A.x`. -/

abbrev AliasState := SMap Name (List Name)
abbrev AliasEntry := Name × Name

def addAliasEntry (s : AliasState) (e : AliasEntry) : AliasState :=
  match s.find? e.1 with
  | none    => s.insert e.1 [e.2]
  | some es => if es.elem e.2 then s else s.insert e.1 (e.2 :: es)

builtin_initialize aliasExtension : SimplePersistentEnvExtension AliasEntry AliasState ←
  registerSimplePersistentEnvExtension {
    name          := `aliasesExt,
    addEntryFn    := addAliasEntry,
    addImportedFn := fun es => mkStateFromImportedEntries addAliasEntry {} es |>.switch
  }

/- Add alias `a` for `e` -/
@[export lean_add_alias] def addAlias (env : Environment) (a : Name) (e : Name) : Environment :=
  aliasExtension.addEntry env (a, e)

def getAliasState (env : Environment) : AliasState :=
  aliasExtension.getState env

def getAliases (env : Environment) (a : Name) : List Name :=
  match aliasExtension.getState env |>.find? a with
  | none    => []
  | some es => es

-- slower, but only used in the pretty printer
def getRevAliases (env : Environment) (e : Name) : List Name :=
  (aliasExtension.getState env).fold (fun as a es => if List.contains es e then a :: as else as) []

/- Global name resolution -/
namespace ResolveName

/- Check whether `ns ++ id` is a valid namepace name and/or there are aliases names `ns ++ id`. -/
private def resolveQualifiedName (env : Environment) (ns : Name) (id : Name) : List Name :=
  let resolvedId    := ns ++ id
  let resolvedIds   := getAliases env resolvedId
  if env.contains resolvedId && (!id.isAtomic || !isProtected env resolvedId) then
    resolvedId :: resolvedIds
  else
    -- Check whether environment contains the private version. That is, `_private.<module_name>.ns.id`.
    let resolvedIdPrv := mkPrivateName env resolvedId
    if env.contains resolvedIdPrv then resolvedIdPrv :: resolvedIds
    else resolvedIds

/- Check surrounding namespaces -/
private def resolveUsingNamespace (env : Environment) (id : Name) : Name → List Name
  | ns@(Name.str p _ _) =>
    match resolveQualifiedName env ns id with
    | []          => resolveUsingNamespace env id p
    | resolvedIds => resolvedIds
  | _ => []

/- Check exact name -/
private def resolveExact (env : Environment) (id : Name) : Option Name :=
  if id.isAtomic then none
  else
    let resolvedId := id.replacePrefix rootNamespace Name.anonymous
    if env.contains resolvedId then some resolvedId
    else
      -- We also allow `_root` when accessing private declarations.
      -- If we change our minds, we should just replace `resolvedId` with `id`
      let resolvedIdPrv := mkPrivateName env resolvedId
      if env.contains resolvedIdPrv then some resolvedIdPrv
      else none

/- Check `OpenDecl`s -/
private def resolveOpenDecls (env : Environment) (id : Name) : List OpenDecl → List Name → List Name
  | [], resolvedIds => resolvedIds
  | OpenDecl.simple ns exs :: openDecls, resolvedIds =>
    if exs.elem id then
      resolveOpenDecls env id openDecls resolvedIds
    else
      let newResolvedIds := resolveQualifiedName env ns id
      resolveOpenDecls env id openDecls (newResolvedIds ++ resolvedIds)
  | OpenDecl.explicit openedId resolvedId :: openDecls, resolvedIds =>
    let resolvedIds :=
      if openedId == id then
        resolvedId :: resolvedIds
      else if openedId.isPrefixOf id then
        let candidate := id.replacePrefix openedId resolvedId
        if env.contains candidate then
          candidate :: resolvedIds
        else
          resolvedIds
      else
        resolvedIds
    resolveOpenDecls env id openDecls resolvedIds

def resolveGlobalName (env : Environment) (ns : Name) (openDecls : List OpenDecl) (id : Name) : List (Name × List String) :=
  -- decode macro scopes from name before recursion
  let extractionResult := extractMacroScopes id
  let rec loop (id : Name) (projs : List String) : List (Name × List String) :=
    match id with
    | Name.str p s _ =>
      -- NOTE: we assume that macro scopes always belong to the projected constant, not the projections
      let id := { extractionResult with name := id }.review
      match resolveUsingNamespace env id ns with
      | resolvedIds@(_ :: _) => resolvedIds.eraseDups.map fun id => (id, projs)
      | [] =>
        match resolveExact env id with
        | some newId => [(newId, projs)]
        | none =>
          let resolvedIds := if env.contains id then [id] else []
          let idPrv       := mkPrivateName env id
          let resolvedIds := if env.contains idPrv then [idPrv] ++ resolvedIds else resolvedIds
          let resolvedIds := resolveOpenDecls env id openDecls resolvedIds
          let resolvedIds := getAliases env id ++ resolvedIds
          match resolvedIds with
          | _ :: _ => resolvedIds.eraseDups.map fun id => (id, projs)
          | []     => loop p (s::projs)
    | _ => []
  loop extractionResult.name []

/- Namespace resolution -/

def resolveNamespaceUsingScope (env : Environment) (n : Name) : Name → Option Name
  | Name.anonymous      => if env.isNamespace n then some n else none
  | ns@(Name.str p _ _) => if env.isNamespace (ns ++ n) then some (ns ++ n) else resolveNamespaceUsingScope env n p
  | _                   => unreachable!

def resolveNamespaceUsingOpenDecls (env : Environment) (n : Name) : List OpenDecl → Option Name
  | []                          => none
  | OpenDecl.simple ns [] :: ds =>  if env.isNamespace (ns ++ n) then some (ns ++ n) else resolveNamespaceUsingOpenDecls env n ds
  | _ :: ds                     => resolveNamespaceUsingOpenDecls env n ds

/-
Given a name `id` try to find namespace it refers to. The resolution procedure works as follows
1- If `id` is in the scope of `namespace` commands the namespace `s_1. ... . s_n`,
   then return `s_1 . ... . s_i ++ n` if it is the name of an existing namespace. We search "backwards".
2- If `id` is the extact name of an existing namespace, then return `id`

3- Finally, for each command `open N`, return `N ++ n` if it is the name of an existing namespace.
   We search "backwards" again. That is, we try the most recent `open` command first.
   We only consider simple `open` commands. -/
def resolveNamespace? (env : Environment) (ns : Name) (openDecls : List OpenDecl) (id : Name) : Option Name :=
  match resolveNamespaceUsingScope env id ns with
  | some n => some n
  | none   =>
    match resolveNamespaceUsingOpenDecls env id openDecls with
    | some n => some n
    | none   => none

end ResolveName

class MonadResolveName (m : Type → Type) where
  getCurrNamespace   : m Name
  getOpenDecls       : m (List OpenDecl)

export MonadResolveName (getCurrNamespace getOpenDecls)

instance (m n) [MonadLift m n] [MonadResolveName m] : MonadResolveName n where
  getCurrNamespace := liftM (m:=m) getCurrNamespace
  getOpenDecls     := liftM (m:=m) getOpenDecls

/-
  Given a name `n`, return a list of possible interpretations.
  Each interpretation is a pair `(declName, fieldList)`, where `declName`
  is the name of a declaration in the current environment, and `fieldList` are
  (potential) field names.
  The pair is needed because in Lean `.` may be part of a qualified name or
  a field (aka dot-notation).
  As an example, consider the following definitions
  ```
  def Boo.x   := 1
  def Foo.x   := 2
  def Foo.x.y := 3
  ```
  After `open Foo`, we have
  - `resolveGlobalName x`     => `[(Foo.x, [])]`
  - `resolveGlobalName x.y`   => `[(Foo.x.y, [])]`
  - `resolveGlobalName x.z.w` => `[(Foo.x, [z, w])]`
  After `open Foo open Boo`, we have
  - `resolveGlobalName x`     => `[(Foo.x, []), (Boo.x, [])]`
  - `resolveGlobalName x.y`   => `[(Foo.x.y, [])]`
  - `resolveGlobalName x.z.w` => `[(Foo.x, [z, w]), (Boo.x, [z, w])]`
-/
def resolveGlobalName [Monad m] [MonadResolveName m] [MonadEnv m] (id : Name) : m (List (Name × List String)) := do
  return ResolveName.resolveGlobalName (← getEnv) (← getCurrNamespace) (← getOpenDecls) id

def resolveNamespace [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (id : Name) : m Name := do
  match ResolveName.resolveNamespace? (← getEnv) (← getCurrNamespace) (← getOpenDecls) id with
  | some ns => return ns
  | none    => throwError s!"unknown namespace '{id}'"

/--
Similar to `resolveGlobalName`, but discard any candidate whose `fieldList` is not empty.
For identifiers taken from syntax, use `resolveGlobalConst` instead, which respects preresolved names. -/
def resolveGlobalConstCore [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (n : Name) : m (List Name) := do
  let cs ← resolveGlobalName n
  let cs := cs.filter fun (_, fieldList) => fieldList.isEmpty
  if cs.isEmpty then throwUnknownConstant n
  return cs.map (·.1)

/-- For identifiers taken from syntax, use `resolveGlobalConstNoOverload` instead, which respects preresolved names. -/
def resolveGlobalConstNoOverloadCore [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (n : Name) : m Name := do
  let cs ← resolveGlobalConstCore n
  match cs with
  | [c] => pure c
  | _   => throwError s!"ambiguous identifier '{mkConst n}', possible interpretations: {cs.map mkConst}"

def resolveGlobalConst [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] : Syntax → m (List Name)
  | stx@(Syntax.ident _ _ n pre) => do
    let pre := pre.filterMap fun (n, fields) => if fields.isEmpty then some n else none
    if pre.isEmpty then
      withRef stx <| resolveGlobalConstCore n
    else
      return pre
  | stx => throwErrorAt stx s!"expected identifier"

def resolveGlobalConstNoOverload [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (id : Syntax) : m Name := do
  let cs ← resolveGlobalConst id
  match cs with
  | [c] => pure c
  | _   => throwErrorAt id s!"ambiguous identifier '{id}', possible interpretations: {cs.map mkConst}"

end Lean
