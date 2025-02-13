/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Meta.Basic

namespace Lean.Meta

/-- Resolves the name `n` in the local context. -/
def resolveLocalName (n : Name) : MetaM (Option (Expr × List String)) := do
  let lctx ← getLCtx
  let auxDeclToFullName := (← read).auxDeclToFullName
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

/-- Like `Lean.unresolveNameGlobal`, but also ensures that the unresolved name does not conflict
with the names of any local declarations. -/
def unresolveNameGlobalAvoidingLocals (n₀ : Name) (fullNames := false) : MetaM Name :=
  unresolveNameGlobal n₀ (fullNames := fullNames) (filter := fun n => Option.isNone <$> resolveLocalName n)
