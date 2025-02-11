/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Data.OpenDecl
import Lean.Data.ExportDecl
import Lean.Hygiene
import Lean.Modifiers
import Lean.Exception

/-!
# Name resolution
-/

namespace Lean
/-!
### Reserved names.

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
### Aliases

The `export` command creates *aliases*, which are like "symbolic links" in the name hierarchy.
An `export A (x)` from within the namespace `B` produces an alias `B.x ~> y`, where `y` is what the name `A.x` resolves to.
An `export A` from within the namespace `B` produces a family of aliases `B.* ~> A.*`.
Alias resolution is recursive.

Abstract description: "`m` is an alias for `n`" is a relation on names.
1. If `n₁` is an alias for `n₂` and `n₂` is an alias for `n₃` then `n₁` is an alias for `n₃`.
2. Given `ExportDecl.explicit aDecl dDecl`, then `aDecl` is an alias for `dDecl`.
   Futhermore, if `dDecl` is a namepace then the rule for `ExportDecl.namespace aDecl dDecl []` also applies.
3. Given `ExportDecl.namespace ans ns except`, then for all names `m` not in `except`,
   if `m = Name.str m' id`, `ns ++ m'` is a namespace, and `ans ++ m` is not a private name,
   then `ans ++ m` is an alias for `ns ++ m`.

For a name `m`, we say "alias `m` resolves to `n`" if `m` maps to `n` and `n` is a declaration or a reserved name.
**The result of `resolveAlias m`** is a list containing every `n` such that alias `m` resolves to `n`.
The condition that `ExportDecl.namespace` only resolves names whose prefix is a namespace ensures that we can implement
this with a (terminating!) efficient algorithm, since this ensures the problem is equivalent to a graph search on a finite graph.

The difference between the behavior of `ExportDecl.explict ans ns` and `ExportDecl.namespace ans ns []` is that the
first one additionally makes `ans` an alias for `ns` if `ns` is a declaration. The second does not — it only causes names
appearing inside `ns` to be aliased inside `ans`.
-/

/--
Data for exporting a namespace into another namespace. Represents a single `ExportDecl.namespace` entry.
The `fwd` parameter represents whether this is for the forward map or the reverse map in `AliasState`.
-/
structure NamespaceAlias (fwd : Bool) where
  /-- If `fwd`, then the namespace that's been exported. Otherwise, the destination namespace for the export. -/
  ns : Name
  /-- The names that are not exported. For each `e` in `except`, `ns ++ e` is not exported. -/
  except : List Name
  deriving BEq, Inhabited

/--
The main state for aliases. `AliasStateMaps true` is the forward direction, and `AliasStateMaps false` is the reverse direction.
Each determines the other, but in `AliasState` we have both for efficient lookups.
-/
structure AliasStateMaps (fwd : Bool) where
  /-- Map from aliases to the declarations they could refer to.
  An `ExportDecl.explicit a b` entry is represented as `b ∈ aliases[a]` (if forward mode) or `a ∈ aliases[b]` (if backward mode). -/
  aliases : SMap Name (List Name) := {}
  /-- Map from namespaces to the namespaces exported to it.
  An `ExportDecl.namespace a b except` entry is represented as `{ns := b, except} ∈ namespaceAliases[a]` (if forward mode)
  or `{ns := a, except} ∈ namespaceAliases[b]` (if backward mode). -/
  namespaceAliases : SMap Name (List (NamespaceAlias fwd)) := {}
  deriving Inhabited

def AliasStateMaps.addExplicit (s : AliasStateMaps fwd) (aDeclName declName : Name) : AliasStateMaps fwd :=
  let (key, value) := if fwd then (aDeclName, declName) else (declName, aDeclName)
  let { aliases, namespaceAliases } := s
  let aliases :=
    if let some decls := aliases.find? key then
      if decls.contains declName then aliases else aliases.insert key (value :: decls)
    else
      aliases.insert key [value]
  { aliases, namespaceAliases }

def AliasStateMaps.addNamespace (s : AliasStateMaps fwd) (ans ns : Name) (except : List Name) : AliasStateMaps fwd :=
  let (key, value) := if fwd then (ans, ns) else (ns, ans)
  let { aliases, namespaceAliases } := s
  let nsAlias : NamespaceAlias fwd := { ns := value, except }
  let namespaceAliases :=
    if let some decls := namespaceAliases.find? key then
      if decls.contains nsAlias then namespaceAliases else namespaceAliases.insert key (nsAlias :: decls)
    else
      namespaceAliases.insert key [nsAlias]
  { aliases, namespaceAliases }

def AliasStateMaps.switch : AliasStateMaps fwd → AliasStateMaps fwd
  | { aliases, namespaceAliases } => { aliases := aliases.switch, namespaceAliases := namespaceAliases.switch }

/--
Applies `f` to all relevant alias entries for the name `a`.
In `fwd` mode, this means finding all `.explicit a' _` entries with `a'` a prefix of `a` (or equal to `a`)
and all `.namespace ns _ _` entries with `ns` a prefix of `a`.
Otherwise, in reverse mode, this means doing it with `.explicit _ a'` and `.namespace _ ns _` instead.
Does not do any processing of `.namespace` exceptions, and does not do any checking of the namespace rules.
-/
def AliasStateMaps.forMatchingM [Monad m] (s : AliasStateMaps fwd) (a : Name) (f : ExportDecl → m Unit) : m Unit := do
  if let some decls := s.aliases.find? a then
    decls.forM (fun val => f (mkExplicit a val))
  if let .str ns _ := a then
    visitNS ns
where
  mkExplicit (key val : Name) : ExportDecl :=
    if fwd then .explicit key val else .explicit val key
  mkNamespace (key val : Name) (except : List Name) : ExportDecl :=
    if fwd then .namespace key val except else .namespace val key except
  visitNS (ns : Name) : m Unit := do
    match ns with
    | .str ns' _ | .num ns' _ => visitNS ns'
    | .anonymous => pure ()
    if let some decls := s.aliases.find? ns then
      decls.forM fun val => f (mkExplicit ns val)
    if let some decls := s.namespaceAliases.find? ns then
      decls.forM fun decl => f (mkNamespace ns decl.ns decl.except)

structure AliasState where
  /-- Alias maps, forward direction. Maps aliases to what they are aliases to. For resolving aliases. -/
  fwd : AliasStateMaps true := {}
  /-- Alias maps, reverse direction. Maps names to their aliases. For 'unresolving'. -/
  rev : AliasStateMaps false := {}
  deriving Inhabited

def AliasState.switch : AliasState → AliasState
  | { fwd, rev } => { fwd := fwd.switch, rev := rev.switch }

private def addExportDecl (s : AliasState) (e : ExportDecl) : AliasState :=
  let { fwd, rev } := s
  match e with
  | .explicit aDecl dDecl =>
    { fwd := fwd.addExplicit aDecl dDecl
      rev := rev.addExplicit aDecl dDecl }
  | .namespace ans ns except =>
    { fwd := fwd.addNamespace ans ns except
      rev := rev.addNamespace ans ns except }

builtin_initialize aliasExtension : SimplePersistentEnvExtension ExportDecl AliasState ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := addExportDecl,
    addImportedFn := fun es => mkStateFromImportedEntries addExportDecl {} es |>.switch
  }

/--
Adds an alias `aDeclName` that refers to `declName`. (Creates an `ExportDecl.explicit` entry).
-/
@[export lean_add_alias] def addAlias (env : Environment) (aDeclName : Name) (declName : Name) : Environment :=
  aliasExtension.addEntry env (.explicit aDeclName declName)

/--
Makes `ans.f` resolve to `ns.f` if `ns.f` exists as either a declaration or an alias
and `f` is not in the `except` list. (Creates an `ExportDecl.namespace` entry).
-/
def addNamespaceAlias (env : Environment) (ans : Name) (ns : Name) (except : List Name) : Environment :=
  aliasExtension.addEntry env (.namespace ans ns except)

def getAliasState (env : Environment) : AliasState :=
  aliasExtension.getState env

/--
Implementation of procedure to resolve the alias `a`.
The `List Name` state for aliases visited is used to prevent infinite loops,
which can be caused by `.namespace` exports re-exporting aliases.
-/
private partial def resolveAliasAux (env : Environment) (a : Name) (skipProtected : Bool) :
    StateM (List Name × List Name) Unit := do
  unless (← get).1.contains a do
    modify fun (aliases, declNames) => (a :: aliases, declNames)
    let visitDecl (dDecl : Name) : StateM (List Name × List Name) Unit := do
      if (env.contains dDecl && (!skipProtected || !isProtected env dDecl))
          || (isReservedName env dDecl && !skipProtected) then
        modify fun (aliases, declNames) => (aliases, dDecl :: declNames)
      resolveAliasAux env dDecl skipProtected
    let visitIfNamespace (decl : Name) : StateM (List Name × List Name) Unit := do
      if decl.isStr && env.isNamespace decl.getPrefix then
        visitDecl decl
    let isPriv := isPrivateName a
    getAliasState env |>.fwd.forMatchingM a fun edecl => do
      match edecl with
      | .explicit aDecl dDecl =>
        if aDecl == a then
          visitDecl dDecl
        else if !isPriv then
          visitIfNamespace (a.replacePrefix aDecl dDecl)
      | .namespace ans ns except =>
        if !isPriv then
          let m := a.replacePrefix ans .anonymous
          unless except.contains m do
            visitIfNamespace (Name.appendCore ns m)

/--
Retrieve declarations that `a` is an alias for.
If `skipProtected` is `true`, then the resulting list only includes declarations that are not marked as `protected`.
-/
def resolveAlias (env : Environment) (a : Name) (skipProtected : Bool) : List Name :=
  resolveAliasAux env a skipProtected |>.run ([], []) |>.2.2

/--
Implementation of procedure to find all aliases of the declaration `d`.
The `List Name` state for declarations is to prevent infinite loops.
-/
private partial def unresolveAliasesAux (env : Environment) (d : Name) (skipAtomic : Bool) (allowHorizAliases : Bool) :
    StateM (List Name × List Name) Unit :=
  unless (← get).2.contains d do
    modify fun (aliases, declNames) => (aliases, d :: declNames)
    let visitDecl (aDecl : Name) : StateM (List Name × List Name) Unit := do
      if (!skipAtomic || !aDecl.isAtomic) && (allowHorizAliases || aDecl.getPrefix.isPrefixOf d) then
        modify fun (aliases, declNames) => (aDecl :: aliases, declNames)
        unresolveAliasesAux env aDecl skipAtomic allowHorizAliases
    let visitNamespace (aDecl : Name) : StateM (List Name × List Name) Unit := do
      if d.isStr && env.isNamespace d.getPrefix && !isPrivateName aDecl then
        visitDecl aDecl
    getAliasState env |>.rev.forMatchingM d fun edecl => do
      match edecl with
      | .explicit aDecl dDecl =>
        if dDecl == d then
          visitDecl aDecl
        else
          visitNamespace (d.replacePrefix dDecl aDecl)
      | .namespace ans ns except =>
        let m := d.replacePrefix ns .anonymous
        unless except.contains m do
          visitNamespace (Name.appendCore ans m)

/--
Retrieve all aliases of the declaration `declName`.

If `skipAtomic` is true, then aliases that are atomic names are not returned.
This option is parallel to `Lean.getAliases`'s `skipProtected`, which is used in `Lean.ResolveName.resolveQualifiedName`.

For `allowHorizAliases`, see the docstring for `Lean.unresolveNameGlobal`.
-/
def unresolveAliases (env : Environment) (declName : Name) (skipAtomic := false) (allowHorizAliases := true) : List Name :=
  unresolveAliasesAux env declName (skipAtomic := skipAtomic) (allowHorizAliases := allowHorizAliases) |>.run ([], []) |>.2.1

/-! ### Global name resolution -/
namespace ResolveName

private def containsDeclOrReserved (env : Environment) (declName : Name) : Bool :=
  env.contains declName || isReservedName env declName

/-- Check whether `ns ++ id` is a valid namespace name and/or there are aliases names `ns ++ id`. -/
private def resolveQualifiedName (env : Environment) (ns : Name) (id : Name) : List Name :=
  let resolvedId    := ns ++ id
  -- We ignore protected aliases if `id` is atomic.
  let resolvedIds   := resolveAlias env resolvedId (skipProtected := id.isAtomic)
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
          let resolvedIds := resolveAlias env id (skipProtected := id.isAtomic) ++ resolvedIds
          match resolvedIds with
          | _ :: _ => resolvedIds.eraseDups.map fun id => (id, projs)
          | []     => loop p (s::projs)
    | _ => []
  loop extractionResult.name []

/-! ### Namespace resolution -/

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

When `allowHorizAliases` is false, then "horizontal aliases" (ones that are not put into a parent namespace) are filtered out.
The assumption is that non-horizontal aliases are "API exports" (i.e., intentional exports that should be considered to be the new canonical name).
"Non-API exports" arise from (1) using `export` to add names to a namespace for dot notation or (2) projects that want names to be conveniently and permanently accessible in their own namespaces.

This function is meant to be used for pretty printing.
If `n₀` is an accessible name, then the result will be an accessible name.
-/
def unresolveNameGlobal [Monad m] [MonadResolveName m] [MonadEnv m] (n₀ : Name) (fullNames := false) (allowHorizAliases := false) : m Name := do
  if n₀.hasMacroScopes then return n₀
  if fullNames then
    match (← resolveGlobalName n₀) with
      | [(potentialMatch, _)] => if (privateToUserName? potentialMatch).getD potentialMatch == n₀ then return n₀ else return rootNamespace ++ n₀
      | _ => return n₀ -- if can't resolve, return the original
  let env ← getEnv
  -- In `Lean.ResolveName.resolveQualifiedName`, if a name is atomic it's not allowed to refer to a protected declaration,
  -- so here we conversely omit atomic aliases if the declaration is protected.
  let mut initialNames := (unresolveAliases env n₀ (allowHorizAliases := allowHorizAliases) (skipAtomic := isProtected env n₀)).toArray
  unless allowHorizAliases do
    initialNames := initialNames.filter fun n => n.getPrefix.isPrefixOf n₀.getPrefix
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
