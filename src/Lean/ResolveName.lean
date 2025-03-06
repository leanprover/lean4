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
import Lean.Namespace

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

/-- Resolves the name `n` in the local context. -/
def resolveLocalName [Monad m] [MonadResolveName m] [MonadEnv m] [MonadLCtx m] (n : Name) : m (Option (Expr × List String)) := do
  let lctx ← getLCtx
  let auxDeclToFullName := (← getLCtx).auxDeclToFullName
  let currNamespace ← getCurrNamespace
  let view := extractMacroScopes n
  /- Simple case. "Match" function for regular local declarations. -/
  let matchLocalDecl? (localDecl : LocalDecl) (givenName : Name) : Option LocalDecl := do
    guard (localDecl.userName == givenName)
    return localDecl
  /-
  "Match" function for auxiliary declarations that correspond to recursive definitions being defined.
  This function is used in the first-pass.
  Note that we do not check for `localDecl.userName == givenName` in this pass as we do for regular local declarations.
  Reason: consider the following example
  ```
    mutual
      inductive Foo
      | somefoo : Foo | bar : Bar → Foo → Foo
      inductive Bar
      | somebar : Bar| foobar : Foo → Bar → Bar
    end

    mutual
      private def Foo.toString : Foo → String
        | Foo.somefoo => go 2 ++ toString.go 2 ++ Foo.toString.go 2
        | Foo.bar b f => toString f ++ Bar.toString b
      where
        go (x : Nat) := s!"foo {x}"

      private def _root_.Ex2.Bar.toString : Bar → String
        | Bar.somebar => "bar"
        | Bar.foobar f b => Foo.toString f ++ Bar.toString b
    end
  ```
  In the example above, we have two local declarations named `toString` in the local context, and
  we want the `toString f` to be resolved to `Foo.toString f`.
  -/
  let matchAuxRecDecl? (localDecl : LocalDecl) (fullDeclName : Name) (givenNameView : MacroScopesView) : Option LocalDecl := do
    let fullDeclView := extractMacroScopes fullDeclName
    /- First cleanup private name annotations -/
    let fullDeclView := { fullDeclView with name := (privateToUserName? fullDeclView.name).getD fullDeclView.name }
    let fullDeclName := fullDeclView.review
    let localDeclNameView := extractMacroScopes localDecl.userName
    /- If the current namespace is a prefix of the full declaration name,
       we use a relaxed matching test where we must satisfy the following conditions
       - The local declaration is a suffix of the given name.
       - The given name is a suffix of the full declaration.

       Recall the `let rec`/`where` declaration naming convention. For example, suppose we have
       ```
       def Foo.Bla.f ... :=
         ... go ...
       where
          go ... := ...
       ```
       The current namespace is `Foo.Bla`, and the full name for `go` is `Foo.Bla.f.g`, but we want to
       refer to it using just `go`. It is also accepted to refer to it using `f.go`, `Bla.f.go`, etc.

    -/
    if currNamespace.isPrefixOf fullDeclName then
      /- Relaxed mode that allows us to access `let rec` declarations using shorter names -/
      guard (localDeclNameView.isSuffixOf givenNameView)
      guard (givenNameView.isSuffixOf fullDeclView)
      return localDecl
    else
      /-
         It is the standard algorithm we are using at `resolveGlobalName` for processing namespaces.

         The current solution also has a limitation when using `def _root_` in a mutual block.
         The non `def _root_` declarations may update the namespace. See the following example:
         ```
         mutual
           def Foo.f ... := ...
           def _root_.g ... := ...
             let rec h := ...
             ...
         end
         ```
         `def Foo.f` updates the namespace. Then, even when processing `def _root_.g ...`
         the condition `currNamespace.isPrefixOf fullDeclName` does not hold.
         This is not a big problem because we are planning to modify how we handle the mutual block in the future.

         Note that we don't check for `localDecl.userName == givenName` here.
      -/
      let rec go (ns : Name) : Option LocalDecl := do
        if { givenNameView with name := ns ++ givenNameView.name }.review == fullDeclName then
          return localDecl
        match ns with
        | .str pre .. => go pre
        | _ => failure
      return (← go currNamespace)
  /- Traverse the local context backwards looking for match `givenNameView`.
     If `skipAuxDecl` we ignore `auxDecl` local declarations. -/
  let findLocalDecl? (givenNameView : MacroScopesView) (skipAuxDecl : Bool) : Option LocalDecl :=
    let givenName := givenNameView.review
    let localDecl? := lctx.decls.findSomeRev? fun localDecl? => do
      let localDecl ← localDecl?
      if localDecl.isAuxDecl then
        guard (!skipAuxDecl)
        if let some fullDeclName := auxDeclToFullName.find? localDecl.fvarId then
          matchAuxRecDecl? localDecl fullDeclName givenNameView
        else
          matchLocalDecl? localDecl givenName
      else
        matchLocalDecl? localDecl givenName
    if localDecl?.isSome || skipAuxDecl then
      localDecl?
    else
      -- Search auxDecls again trying an exact match of the given name
      lctx.decls.findSomeRev? fun localDecl? => do
        let localDecl ← localDecl?
        guard localDecl.isAuxDecl
        matchLocalDecl? localDecl givenName
  /-
  We use the parameter `globalDeclFound` to decide whether we should skip auxiliary declarations or not.
  We set it to true if we found a global declaration `n` as we iterate over the `loop`.
  Without this workaround, we would not be able to elaborate an example such as
  ```
  def foo.aux := 1
  def foo : Nat → Nat
    | n => foo.aux -- should not be interpreted as `(foo).aux`
  ```
  See test `aStructPerfIssue.lean` for another example.
  We skip auxiliary declarations when `projs` is not empty and `globalDeclFound` is true.
  Remark: we did not use to have the `globalDeclFound` parameter. Without this extra check we failed
  to elaborate
  ```
  example : Nat :=
    let n := 0
    n.succ + (m |>.succ) + m.succ
  where
    m := 1
  ```
  See issue #1850.
  -/
  let rec loop (n : Name) (projs : List String) (globalDeclFound : Bool) := do
    let givenNameView := { view with name := n }
    let mut globalDeclFoundNext := globalDeclFound
    unless globalDeclFound do
      let r ← resolveGlobalName givenNameView.review
      let r := r.filter fun (_, fieldList) => fieldList.isEmpty
      unless r.isEmpty do
        globalDeclFoundNext := true
    /-
    Note that we use `globalDeclFound` instead of `globalDeclFoundNext` in the following test.
    Reason: a local should shadow a global with the same name.
    Consider the following example. See issue #3079
    ```
    def foo : Nat := 1

    def bar : Nat :=
      foo.add 1 -- should be 11
    where
      foo := 10
    ```
    -/
    match findLocalDecl? givenNameView (skipAuxDecl := globalDeclFound && !projs.isEmpty) with
    | some decl => return some (decl.toExpr, projs)
    | none => match n with
      | .str pre s => loop pre (s::projs) globalDeclFoundNext
      | _ => return none
  loop view.name [] (globalDeclFound := false)

/--
Finds a name that unambiguously resolves to the given name `n₀`.
Considers suffixes of `n₀` and suffixes of aliases of `n₀` when "unresolving".
Aliases are considered first.

When `fullNames` is true, returns either `n₀` or `_root_.n₀`.

When `allowHorizAliases` is false, then "horizontal aliases" (ones that are not put into a parent namespace) are filtered out.
The assumption is that non-horizontal aliases are "API exports" (i.e., intentional exports that should be considered to be the new canonical name).
"Non-API exports" arise from (1) using `export` to add names to a namespace for dot notation or (2) projects that want names to be conveniently and permanently accessible in their own namespaces.

`filter` specifies a predicate that the unresolved name must additionally satisfy.

This function is meant to be used for pretty printing.
If `n₀` is an accessible name, then the result will be an accessible name.
-/
def unresolveNameGlobal [Monad m] [MonadResolveName m] [MonadEnv m]
    (n₀ : Name) (fullNames := false) (allowHorizAliases := false)
    (filter : Name → m Bool := fun _ => pure true) : m Name := do
  if n₀.hasMacroScopes then return n₀
  if fullNames then
    match (← resolveGlobalName n₀) with
      | [(potentialMatch, _)] => if (privateToUserName? potentialMatch).getD potentialMatch == n₀ then return n₀ else return rootNamespace ++ n₀
      | _ => return n₀ -- if can't resolve, return the original
  let mut initialNames := (getRevAliases (← getEnv) n₀).toArray
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
          if (← filter candidate) then
            return some candidate
    return none

/-- Like `Lean.unresolveNameGlobal`, but also ensures that the unresolved name does not conflict
with the names of any local declarations. -/
def unresolveNameGlobalAvoidingLocals [Monad m] [MonadResolveName m] [MonadEnv m] [MonadLCtx m] (n₀ : Name) (fullNames := false) : m Name :=
  unresolveNameGlobal n₀ (fullNames := fullNames) (filter := fun n => Option.isNone <$> resolveLocalName n)

end Lean
