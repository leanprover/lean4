/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Data.OpenDecl
import Lean.Hygiene
import Lean.Modifiers
import Lean.Exception

namespace Lean
/-!
Reserved names.

We use reserved names for automatically generated theorems (e.g., equational theorems).
Automation may register new reserved name predicates.
In this module, we just check the registered predicates, but do not trigger actions associated with them.
For example, give a definition `foo`, we flag `foo.def` as reserved symbol.
-/

def throwReservedNameNotAvailable [Monad m] [MonadError m] (declName : Name) (reservedName : Name) : m Unit := do
  throwError "failed to declare `{declName}` because `{.ofConstName reservedName true}` has already been declared"

def ensureReservedNameAvailable [Monad m] [MonadEnv m] [MonadError m] (declName : Name) (suffix : String) : m Unit := do
  let reservedName := .str declName suffix
  if (← getEnv).contains reservedName then
    throwReservedNameNotAvailable declName reservedName

/-- Global reference containing all reserved name predicates. -/
builtin_initialize reservedNamePredicatesRef : IO.Ref (Array (Environment → Name → Bool)) ← IO.mkRef #[]

/--
Registers a new reserved name predicate.
-/
def registerReservedNamePredicate (p : Environment → Name → Bool) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register reserved name suffix predicate, this operation can only be performed during initialization")
  reservedNamePredicatesRef.modify fun ps => ps.push p

builtin_initialize reservedNamePredicatesExt : EnvExtension (Array (Environment → Name → Bool)) ←
  registerEnvExtension reservedNamePredicatesRef.get

/--
Returns `true` if `name` is a reserved name.
-/
def isReservedName (env : Environment) (name : Name) : Bool :=
  reservedNamePredicatesExt.getState env |>.any (· env name)

/-!
  We use aliases to implement the `export <id> (<id>+)` command.
  An `export A (x)` in the namespace `B` produces an alias `B.x ~> A.x`.
-/

abbrev AliasState := SMap Name (List Name)
abbrev AliasEntry := Name × Name

def addAliasEntry (s : AliasState) (e : AliasEntry) : AliasState :=
  match s.find? e.1 with
  | none    => s.insert e.1 [e.2]
  | some es => if es.contains e.2 then s else s.insert e.1 (e.2 :: es)

builtin_initialize aliasExtension : SimplePersistentEnvExtension AliasEntry AliasState ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := addAliasEntry,
    addImportedFn := fun es => mkStateFromImportedEntries addAliasEntry {} es |>.switch
  }

/-- Add alias `a` for `e` -/
@[export lean_add_alias] def addAlias (env : Environment) (a : Name) (e : Name) : Environment :=
  aliasExtension.addEntry env (a, e)

def getAliasState (env : Environment) : AliasState :=
  aliasExtension.getState env

/--
  Retrieve aliases for `a`. If `skipProtected` is `true`, then the resulting list only includes
  declarations that are not marked as `protected`.
-/
def getAliases (env : Environment) (a : Name) (skipProtected : Bool) : List Name :=
  match aliasExtension.getState env |>.find? a with
  | none    => []
  | some es =>
    if skipProtected then
      es.filter (!isProtected env ·)
    else
      es

-- slower, but only used in the pretty printer
def getRevAliases (env : Environment) (e : Name) : List Name :=
  (aliasExtension.getState env).fold (fun as a es => if List.contains es e then a :: as else as) []

/-! # Global name resolution -/
namespace ResolveName

private def containsDeclOrReserved (env : Environment) (declName : Name) : Bool :=
  env.contains declName || isReservedName env declName

/-- Check whether `ns ++ id` is a valid namespace name and/or there are aliases names `ns ++ id`. -/
private def resolveQualifiedName (env : Environment) (ns : Name) (id : Name) : List Name :=
  let resolvedId    := ns ++ id
  -- We ignore protected aliases if `id` is atomic.
  let resolvedIds   := getAliases env resolvedId (skipProtected := id.isAtomic)
  if (containsDeclOrReserved env resolvedId && (!id.isAtomic || !isProtected env resolvedId)) then
    resolvedId :: resolvedIds
  else
    -- Check whether environment contains the private version. That is, `_private.<module_name>.ns.id`.
    let resolvedIdPrv := mkPrivateName env resolvedId
    if containsDeclOrReserved env resolvedIdPrv then resolvedIdPrv :: resolvedIds
    else resolvedIds

/-- Check surrounding namespaces -/
private def resolveUsingNamespace (env : Environment) (id : Name) : Name → List Name
  | ns@(.str p _) =>
    match resolveQualifiedName env ns id with
    | []          => resolveUsingNamespace env id p
    | resolvedIds => resolvedIds
  | _ => []

/-- Check exact name -/
private def resolveExact (env : Environment) (id : Name) : Option Name :=
  if id.isAtomic then none
  else
    let resolvedId := id.replacePrefix rootNamespace Name.anonymous
    if containsDeclOrReserved env resolvedId then some resolvedId
    else
      -- We also allow `_root` when accessing private declarations.
      -- If we change our minds, we should just replace `resolvedId` with `id`
      let resolvedIdPrv := mkPrivateName env resolvedId
      if containsDeclOrReserved env resolvedIdPrv then some resolvedIdPrv
      else none

/-- Check `OpenDecl`s -/
private def resolveOpenDecls (env : Environment) (id : Name) : List OpenDecl → List Name → List Name
  | [], resolvedIds => resolvedIds
  | OpenDecl.simple ns exs :: openDecls, resolvedIds =>
    if exs.contains id then
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

/--
Primitive global name resolution procedure. It does not trigger actions associated with reserved names.
Recall that Lean has reserved names. For example, a definition `foo` has a reserved name `foo.def` for theorem
containing stating that `foo` is equal to its definition. The action associated with `foo.def`
automatically proves the theorem. At the macro level, the name is resolved, but the action is not
executed.
-/
def resolveGlobalName (env : Environment) (ns : Name) (openDecls : List OpenDecl) (id : Name) : List (Name × List String) :=
  -- decode macro scopes from name before recursion
  let extractionResult := extractMacroScopes id
  let rec loop (id : Name) (projs : List String) : List (Name × List String) :=
    match id with
    | .str p s =>
      -- NOTE: we assume that macro scopes always belong to the projected constant, not the projections
      let id := { extractionResult with name := id }.review
      match resolveUsingNamespace env id ns with
      | resolvedIds@(_ :: _) => resolvedIds.eraseDups.map fun id => (id, projs)
      | [] =>
        match resolveExact env id with
        | some newId => [(newId, projs)]
        | none =>
          let resolvedIds := if containsDeclOrReserved env id then [id] else []
          let idPrv       := mkPrivateName env id
          let resolvedIds := if containsDeclOrReserved env idPrv then [idPrv] ++ resolvedIds else resolvedIds
          let resolvedIds := resolveOpenDecls env id openDecls resolvedIds
          let resolvedIds := getAliases env id (skipProtected := id.isAtomic) ++ resolvedIds
          match resolvedIds with
          | _ :: _ => resolvedIds.eraseDups.map fun id => (id, projs)
          | []     => loop p (s::projs)
    | _ => []
  loop extractionResult.name []

/-! # Namespace resolution -/

def resolveNamespaceUsingScope? (env : Environment) (n : Name) (ns : Name) : Option Name :=
  match ns with
  | .str p _ =>
    if env.isNamespace (ns ++ n) then
      some (ns ++ n)
    else
      resolveNamespaceUsingScope? env n p
  | .anonymous =>
    let n := n.replacePrefix rootNamespace .anonymous
    if env.isNamespace n then some n else none
  | _ => unreachable!

def resolveNamespaceUsingOpenDecls (env : Environment) (n : Name) : List OpenDecl → List Name
  | [] => []
  | OpenDecl.simple ns exs :: ds =>
    if env.isNamespace (ns ++ n) && !exs.contains n then
      (ns ++ n) :: resolveNamespaceUsingOpenDecls env n ds
    else
      resolveNamespaceUsingOpenDecls env n ds
  | _ :: ds => resolveNamespaceUsingOpenDecls env n ds

/--
Given a name `id` try to find namespaces it may refer to. The resolution procedure works as follows

1- If `id` is in the scope of `namespace` commands the namespace `s_1. ... . s_n`,
   then we include `s_1 . ... . s_i ++ n` in the result if it is the name of an existing namespace.
   We search "backwards", and include at most one of the in the list of resulting namespaces.

2- If `id` is the exact name of an existing namespace, then include `id`

3- Finally, for each command `open N`, include in the result `N ++ n` if it is the name of an existing namespace.
   We only consider simple `open` commands. -/
def resolveNamespace (env : Environment) (ns : Name) (openDecls : List OpenDecl) (id : Name) : List Name :=
  match resolveNamespaceUsingScope? env id ns with
  | some ns => ns :: resolveNamespaceUsingOpenDecls env id openDecls
  | none => resolveNamespaceUsingOpenDecls env id openDecls

end ResolveName

class MonadResolveName (m : Type → Type) where
  getCurrNamespace   : m Name
  getOpenDecls       : m (List OpenDecl)

export MonadResolveName (getCurrNamespace getOpenDecls)

instance (m n) [MonadLift m n] [MonadResolveName m] : MonadResolveName n where
  getCurrNamespace := liftM (m:=m) getCurrNamespace
  getOpenDecls     := liftM (m:=m) getOpenDecls

/--
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

/--
Given a namespace name, return a list of possible interpretations.
Names extracted from syntax should be passed to `resolveNamespace` instead.
-/
def resolveNamespaceCore [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (id : Name) (allowEmpty := false) : m (List Name) := do
  let nss := ResolveName.resolveNamespace (← getEnv) (← getCurrNamespace) (← getOpenDecls) id
  if !allowEmpty && nss.isEmpty then
    throwError s!"unknown namespace '{id}'"
  return nss

/-- Given a namespace identifier, return a list of possible interpretations. -/
def resolveNamespace [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] : Ident → m (List Name)
  | stx@⟨Syntax.ident _ _ n pre⟩ => do
    let pre := pre.filterMap fun
      | .namespace ns => some ns
      | _             => none
    if pre.isEmpty then
      withRef stx <| resolveNamespaceCore n
    else
      return pre
  | stx => throwErrorAt stx s!"expected identifier"

/-- Given a namespace identifier, return the unique interpretation or else fail. -/
def resolveUniqueNamespace [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (id : Ident) : m Name := do
  match (← resolveNamespace id) with
  | [ns] => return ns
  | nss => throwError s!"ambiguous namespace '{id.getId}', possible interpretations: '{nss}'"

/-- Helper function for `resolveGlobalConstCore`. -/
def filterFieldList [Monad m] [MonadError m] (n : Name) (cs : List (Name × List String)) : m (List Name) := do
  let cs := cs.filter fun (_, fieldList) => fieldList.isEmpty
  if cs.isEmpty then throwUnknownConstant n
  return cs.map (·.1)

/-- Given a name `n`, returns a list of possible interpretations for global constants.

Similar to `resolveGlobalName`, but discard any candidate whose `fieldList` is not empty.
For identifiers taken from syntax, use `resolveGlobalConst` instead, which respects preresolved names. -/
private def resolveGlobalConstCore [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (n : Name) : m (List Name) := do
  let cs ← resolveGlobalName n
  filterFieldList n cs

/-- Helper function for `resolveGlobalConstNoOverloadCore` -/
def ensureNoOverload [Monad m] [MonadError m] (n : Name) (cs : List Name) : m Name := do
  match cs with
  | [c] => pure c
  | _   => throwError s!"ambiguous identifier '{mkConst n}', possible interpretations: {cs.map mkConst}"

/-- For identifiers taken from syntax, use `resolveGlobalConstNoOverload` instead, which respects preresolved names. -/
def resolveGlobalConstNoOverloadCore [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (n : Name) : m Name := do
  ensureNoOverload n (← resolveGlobalConstCore n)

def preprocessSyntaxAndResolve [Monad m] [MonadError m] (stx : Syntax) (k : Name → m (List Name)) : m (List Name) := do
  match stx with
  | .ident _ _ n pre => do
    let pre := pre.filterMap fun
      | .decl n [] => some n
      | _          => none
    if pre.isEmpty then
      withRef stx <| k n
    else
      return pre
  | _ => throwErrorAt stx s!"expected identifier"

/--
Interprets the syntax `n` as an identifier for a global constant, and returns a list of resolved
constant names that it could be referring to based on the currently open namespaces.
This should be used instead of `resolveGlobalConstCore` for identifiers taken from syntax
because `Syntax` objects may have names that have already been resolved.

Consider using `realizeGlobalConst` if you need to handle reserved names, and
`realizeGlobalConstWithInfo` if you want the syntax to show the resulting name's info on hover.

## Example:
```
def Boo.x   := 1
def Foo.x   := 2
def Foo.x.y := 3
```
After `open Foo`, we have
- `resolveGlobalConst x`     => `[Foo.x]`
- `resolveGlobalConst x.y`   => `[Foo.x.y]`
- `resolveGlobalConst x.z.w` => error: unknown constant

After `open Foo open Boo`, we have
- `resolveGlobalConst x`     => `[Foo.x, Boo.x]`
- `resolveGlobalConst x.y`   => `[Foo.x.y]`
- `resolveGlobalConst x.z.w` => error: unknown constant
-/
def resolveGlobalConst [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (stx : Syntax) : m (List Name) :=
  preprocessSyntaxAndResolve stx resolveGlobalConstCore

/--
Given a list of names produced by `resolveGlobalConst`, throws an error if the list does not contain
exactly one element.
Recall that `resolveGlobalConst` does not return empty lists.
-/
def ensureNonAmbiguous [Monad m] [MonadError m] (id : Syntax) (cs : List Name) : m Name := do
  match cs with
  | []  => unreachable!
  | [c] => pure c
  | _   => throwErrorAt id s!"ambiguous identifier '{id}', possible interpretations: {cs.map mkConst}"

/-- Interprets the syntax `n` as an identifier for a global constant, and return a resolved
constant name. If there are multiple possible interpretations it will throw.

Consider using `realizeGlobalConstNoOverload` if you need to handle reserved names, and
`realizeGlobalConstNoOverloadWithInfo` if you
want the syntax to show the resulting name's info on hover.

## Example:
```
def Boo.x   := 1
def Foo.x   := 2
def Foo.x.y := 3
```
After `open Foo`, we have
- `resolveGlobalConstNoOverload x`     => `Foo.x`
- `resolveGlobalConstNoOverload x.y`   => `Foo.x.y`
- `resolveGlobalConstNoOverload x.z.w` => error: unknown constant

After `open Foo open Boo`, we have
- `resolveGlobalConstNoOverload x`     => error: ambiguous identifier
- `resolveGlobalConstNoOverload x.y`   => `Foo.x.y`
- `resolveGlobalConstNoOverload x.z.w` => error: unknown constant
-/
def resolveGlobalConstNoOverload [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (id : Syntax) : m Name := do
  ensureNonAmbiguous id (← resolveGlobalConst id)

/--
Finds a name that unambiguously resolves to the given name `n₀`.
Considers suffixes of `n₀` and suffixes of aliases of `n₀` when "unresolving".
Aliases are considered first.

When `fullNames` is true, returns either `n₀` or `_root_.n₀`.

This function is meant to be used for pretty printing.
If `n₀` is an accessible name, then the result will be an accessible name.
-/
def unresolveNameGlobal [Monad m] [MonadResolveName m] [MonadEnv m] (n₀ : Name) (fullNames := false) : m Name := do
  if n₀.hasMacroScopes then return n₀
  if fullNames then
    match (← resolveGlobalName n₀) with
      | [(potentialMatch, _)] => if (privateToUserName? potentialMatch).getD potentialMatch == n₀ then return n₀ else return rootNamespace ++ n₀
      | _ => return n₀ -- if can't resolve, return the original
  let mut initialNames := (getRevAliases (← getEnv) n₀).toArray
  initialNames := initialNames.push (rootNamespace ++ n₀)
  for initialName in initialNames do
    if let some n ← unresolveNameCore initialName then
      return n
  return n₀ -- if can't resolve, return the original
where
  unresolveNameCore (n : Name) : m (Option Name) := do
    if n.hasMacroScopes then return none
    let mut revComponents := n.componentsRev
    let mut candidate := Name.anonymous
    for cmpt in revComponents do
      candidate := Name.appendCore cmpt candidate
      if let [(potentialMatch, _)] ← resolveGlobalName candidate then
        if potentialMatch == n₀ then
          return some candidate
    return none

def unresolveNameGlobalAvoidingLocals [Monad m] [MonadResolveName m] [MonadEnv m] [MonadLCtx m]
    (n₀ : Name) (fullNames := false) : m Name := do
  let mut n ← unresolveNameGlobal n₀ fullNames
  unless (← getLCtx).usesUserName n do return n
  -- `n` is also a local declaration
  if n == n₀ then
    -- `n` is the fully qualified name. So, we append the `_root_` prefix
    return `_root_ ++ n
  else
    return n₀

end Lean
