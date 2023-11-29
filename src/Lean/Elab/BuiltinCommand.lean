/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectLevelParams
import Lean.Meta.Reduce
import Lean.Elab.DeclarationRange
import Lean.Elab.Eval
import Lean.Elab.Command
import Lean.Elab.Open
import Lean.Elab.SetOption
import Lean.PrettyPrinter

namespace Lean.Elab.Command

@[builtin_command_elab moduleDoc] def elabModuleDoc : CommandElab := fun stx => do
   match stx[1] with
   | Syntax.atom _ val =>
     let doc := val.extract 0 (val.endPos - ⟨2⟩)
     let range ← Elab.getDeclarationRange stx
     modifyEnv fun env => addMainModuleDoc env ⟨doc, range⟩
   | _ => throwErrorAt stx "unexpected module doc string{indentD stx[1]}"

private def addScope (isNewNamespace : Bool) (isNoncomputable : Bool) (header : String) (newNamespace : Name) : CommandElabM Unit := do
  modify fun s => { s with
    env    := s.env.registerNamespace newNamespace,
    scopes := { s.scopes.head! with header := header, currNamespace := newNamespace, isNoncomputable := s.scopes.head!.isNoncomputable || isNoncomputable } :: s.scopes
  }
  pushScope
  if isNewNamespace then
    activateScoped newNamespace

private def addScopes (isNewNamespace : Bool) (isNoncomputable : Bool) : Name → CommandElabM Unit
  | .anonymous => pure ()
  | .str p header => do
    addScopes isNewNamespace isNoncomputable p
    let currNamespace ← getCurrNamespace
    addScope isNewNamespace isNoncomputable header (if isNewNamespace then Name.mkStr currNamespace header else currNamespace)
  | _ => throwError "invalid scope"

private def addNamespace (header : Name) : CommandElabM Unit :=
  addScopes (isNewNamespace := true) (isNoncomputable := false) header

def withNamespace {α} (ns : Name) (elabFn : CommandElabM α) : CommandElabM α := do
  addNamespace ns
  let a ← elabFn
  modify fun s => { s with scopes := s.scopes.drop ns.getNumParts }
  pure a

private def popScopes (numScopes : Nat) : CommandElabM Unit :=
  for _ in [0:numScopes] do
    popScope

private def checkAnonymousScope : List Scope → Option Name
  | { header := "", .. } :: _ => none
  | { header := h, .. }  :: _ => some h
  | _                         => some .anonymous -- should not happen

private def checkEndHeader : Name → List Scope → Option Name
  | .anonymous, _ => none
  | .str p s, { header := h, .. } :: scopes =>
    if h == s then
      (.str · s) <$> checkEndHeader p scopes
    else
      some h
  | _, _ => some .anonymous -- should not happen

@[builtin_command_elab «namespace»] def elabNamespace : CommandElab := fun stx =>
  match stx with
  | `(namespace $n) => addNamespace n.getId
  | _               => throwUnsupportedSyntax

@[builtin_command_elab «section»] def elabSection : CommandElab := fun stx => do
  match stx with
  | `(section $header:ident) => addScopes (isNewNamespace := false) (isNoncomputable := false) header.getId
  | `(section)               => addScope (isNewNamespace := false) (isNoncomputable := false) "" (← getCurrNamespace)
  | _                        => throwUnsupportedSyntax

@[builtin_command_elab noncomputableSection] def elabNonComputableSection : CommandElab := fun stx => do
  match stx with
  | `(noncomputable section $header:ident) => addScopes (isNewNamespace := false) (isNoncomputable := true) header.getId
  | `(noncomputable section)               => addScope (isNewNamespace := false) (isNoncomputable := true) "" (← getCurrNamespace)
  | _                        => throwUnsupportedSyntax

@[builtin_command_elab «end»] def elabEnd : CommandElab := fun stx => do
  let header? := (stx.getArg 1).getOptionalIdent?;
  let endSize := match header? with
    | none   => 1
    | some n => n.getNumParts
  let scopes ← getScopes
  if endSize < scopes.length then
    modify fun s => { s with scopes := s.scopes.drop endSize }
    popScopes endSize
  else -- we keep "root" scope
    let n := (← get).scopes.length - 1
    modify fun s => { s with scopes := s.scopes.drop n }
    popScopes n
    throwError "invalid 'end', insufficient scopes"
  match header? with
  | none        =>
    if let some name := checkAnonymousScope scopes then
      throwError "invalid 'end', name is missing (expected {name})"
  | some header =>
    if let some name := checkEndHeader header scopes then
      addCompletionInfo <| CompletionInfo.endSection stx (scopes.map fun scope => scope.header)
      throwError "invalid 'end', name mismatch (expected {if name == `«» then `nothing else name})"

private partial def elabChoiceAux (cmds : Array Syntax) (i : Nat) : CommandElabM Unit :=
  if h : i < cmds.size then
    let cmd := cmds.get ⟨i, h⟩;
    catchInternalId unsupportedSyntaxExceptionId
      (elabCommand cmd)
      (fun _ => elabChoiceAux cmds (i+1))
  else
    throwUnsupportedSyntax

@[builtin_command_elab choice] def elabChoice : CommandElab := fun stx =>
  elabChoiceAux stx.getArgs 0

/-- Declares one or more universe variables.

`universe u v`

`Prop`, `Type`, `Type u` and `Sort u` are types that classify other types, also known as
*universes*. In `Type u` and `Sort u`, the variable `u` stands for the universe's *level*, and a
universe at level `u` can only classify universes that are at levels lower than `u`. For more
details on type universes, please refer to [the relevant chapter of Theorem Proving in Lean][tpil
universes].

Just as type arguments allow polymorphic definitions to be used at many different types, universe
parameters, represented by universe variables, allow a definition to be used at any required level.
While Lean mostly handles universe levels automatically, declaring them explicitly can provide more
control when writing signatures. The `universe` keyword allows the declared universe variables to be
used in a collection of definitions, and Lean will ensure that these definitions use them
consistently.

[tpil universes]: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#types-as-objects
(Type universes on Theorem Proving in Lean)

```lean
/- Explicit type-universe parameter. -/
def id₁.{u} (α : Type u) (a : α) := a

/- Implicit type-universe parameter, equivalent to `id₁`.
  Requires option `autoImplicit true`, which is the default. -/
def id₂ (α : Type u) (a : α) := a

/- Explicit standalone universe variable declaration, equivalent to `id₁` and `id₂`. -/
universe u
def id₃ (α : Type u) (a : α) := a
```

On a more technical note, using a universe variable only in the right-hand side of a definition
causes an error if the universe has not been declared previously.

```lean
def L₁.{u} := List (Type u)

-- def L₂ := List (Type u) -- error: `unknown universe level 'u'`

universe u
def L₃ := List (Type u)
```

## Examples

```lean
universe u v w

structure Pair (α : Type u) (β : Type v) : Type (max u v) where
  a : α
  b : β

#check Pair.{v, w}
-- Pair : Type v → Type w → Type (max v w)
```
-/
@[builtin_command_elab «universe»] def elabUniverse : CommandElab := fun n => do
  n[1].forArgsM addUnivLevel

@[builtin_command_elab «init_quot»] def elabInitQuot : CommandElab := fun _ => do
  match (← getEnv).addDecl Declaration.quotDecl with
  | Except.ok env   => setEnv env
  | Except.error ex => throwError (ex.toMessageData (← getOptions))

/-- Adds names from other namespaces to the current namespace.

The command `export Some.Namespace (name₁ name₂)` makes `name₁` and `name₂`:

- visible in the current namespace without prefix `Some.Namespace`, like `open`, and
- visible from outside the current namespace `N` as `N.name₁` and `N.name₂`.

## Examples

```lean
namespace Morning.Sky
  def star := "venus"
end Morning.Sky

namespace Evening.Sky
  export Morning.Sky (star)
  -- `star` is now in scope
  #check star
end Evening.Sky

-- `star` is visible in `Evening.Sky`
#check Evening.Sky.star
```
-/
@[builtin_command_elab «export»] def elabExport : CommandElab := fun stx => do
  let `(export $ns ($ids*)) := stx | throwUnsupportedSyntax
  let nss ← resolveNamespace ns
  let currNamespace ← getCurrNamespace
  if nss == [currNamespace] then throwError "invalid 'export', self export"
  let mut aliases := #[]
  for idStx in ids do
    let id := idStx.getId
    let declName ← resolveNameUsingNamespaces nss idStx
    if (← getInfoState).enabled then
      addConstInfo idStx declName
    aliases := aliases.push (currNamespace ++ id, declName)
  modify fun s => { s with env := aliases.foldl (init := s.env) fun env p => addAlias env p.1 p.2 }

/-- Makes names from other namespaces visible without writing the namespace prefix.

Names that are made available with `open` are visible within the current `section` or `namespace`
block. This makes referring to (type) definitions and theorems easier, but note that it can also
make [scoped instances], notations, and attributes from a different namespace available.

The `open` command can be used in a few different ways:

* `open Some.Namespace.Path1 Some.Namespace.Path2` makes all non-protected names in
  `Some.Namespace.Path1` and `Some.Namespace.Path2` available without the prefix, so that
  `Some.Namespace.Path1.x` and `Some.Namespace.Path2.y` can be referred to by writing only `x` and
  `y`.

* `open Some.Namespace.Path hiding def1 def2` opens all non-protected names in `Some.Namespace.Path`
  except `def1` and `def2`.

* `open Some.Namespace.Path (def1 def2)` only makes `Some.Namespace.Path.def1` and
  `Some.Namespace.Path.def2` available without the full prefix, so `Some.Namespace.Path.def3` would
  be unaffected.

  This works even if `def1` and `def2` are `protected`.

* `open Some.Namespace.Path renaming def1 → def1', def2 → def2'` same as `open Some.Namespace.Path
  (def1 def2)` but `def1`/`def2`'s names are changed to `def1'`/`def2'`.

  This works even if `def1` and `def2` are `protected`.

* `open scoped Some.Namespace.Path1 Some.Namespace.Path2` **only** opens [scoped instances],
  notations, and attributes from `Namespace1` and `Namespace2`; it does **not** make any other name
  available.

* `open <any of the open shapes above> in` makes the names `open`-ed visible only in the next
  command or expression.

[scoped instance]: https://lean-lang.org/theorem_proving_in_lean4/type_classes.html#scoped-instances
(Scoped instances in Theorem Proving in Lean)


## Examples

```lean
/-- SKI combinators https://en.wikipedia.org/wiki/SKI_combinator_calculus -/
namespace Combinator.Calculus
  def I (a : α) : α := a
  def K (a : α) : β → α := fun _ => a
  def S (x : α → β → γ) (y : α → β) (z : α) : γ := x z (y z)
end Combinator.Calculus

section
  -- open everything under `Combinator.Calculus`, *i.e.* `I`, `K` and `S`,
  -- until the section ends
  open Combinator.Calculus

  theorem SKx_eq_K : S K x = I := rfl
end

-- open everything under `Combinator.Calculus` only for the next command (the next `theorem`, here)
open Combinator.Calculus in
theorem SKx_eq_K' : S K x = I := rfl

section
  -- open only `S` and `K` under `Combinator.Calculus`
  open Combinator.Calculus (S K)

  theorem SKxy_eq_y : S K x y = y := rfl

  -- `I` is not in scope, we have to use its full path
  theorem SKxy_eq_Iy : S K x y = Combinator.Calculus.I y := rfl
end

section
  open Combinator.Calculus
    renaming
      I → identity,
      K → konstant

  #check identity
  #check konstant
end

section
  open Combinator.Calculus
    hiding S

  #check I
  #check K
end

section
  namespace Demo
    inductive MyType
    | val

    namespace N1
      scoped infix:68 " ≋ " => BEq.beq

      scoped instance : BEq MyType where
        beq _ _ := true

      def Alias := MyType
    end N1
  end Demo

  -- bring `≋` and the instance in scope, but not `Alias`
  open scoped Demo.N1

  #check Demo.MyType.val == Demo.MyType.val
  #check Demo.MyType.val ≋ Demo.MyType.val
  -- #check Alias -- unknown identifier 'Alias'
end
```
-/
@[builtin_command_elab «open»] def elabOpen : CommandElab
  | `(open $decl:openDecl) => do
    let openDecls ← elabOpenDecl decl
    modifyScope fun scope => { scope with openDecls := openDecls }
  | _ => throwUnsupportedSyntax

open Lean.Parser.Term

private def typelessBinder? : Syntax → Option (Array (TSyntax [`ident, `Lean.Parser.Term.hole]) × Bool)
  | `(bracketedBinderF|($ids*)) => some (ids, true)
  | `(bracketedBinderF|{$ids*}) => some (ids, false)
  | _                          => none

/--  If `id` is an identifier, return true if `ids` contains `id`. -/
private def containsId (ids : Array (TSyntax [`ident, ``Parser.Term.hole])) (id : TSyntax [`ident, ``Parser.Term.hole]) : Bool :=
  id.raw.isIdent && ids.any fun id' => id'.raw.getId == id.raw.getId

/--
  Auxiliary method for processing binder annotation update commands: `variable (α)` and `variable {α}`.
  The argument `binder` is the binder of the `variable` command.
  The method returns an array containing the "residue", that is, variables that do not correspond to updates.
  Recall that a `bracketedBinder` can be of the form `(x y)`.
  ```
  variable {α β : Type}
  variable (α γ)
  ```
  The second `variable` command updates the binder annotation for `α`, and returns "residue" `γ`.
-/
private def replaceBinderAnnotation (binder : TSyntax ``Parser.Term.bracketedBinder) : CommandElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) := do
  let some (binderIds, explicit) := typelessBinder? binder | return #[binder]
  let varDecls := (← getScope).varDecls
  let mut varDeclsNew := #[]
  let mut binderIds := binderIds
  let mut binderIdsIniSize := binderIds.size
  let mut modifiedVarDecls := false
  for varDecl in varDecls do
    let (ids, ty?, explicit') ← match varDecl with
      | `(bracketedBinderF|($ids* $[: $ty?]? $(annot?)?)) =>
        if annot?.isSome then
          for binderId in binderIds do
            if containsId ids binderId then
              throwErrorAt binderId "cannot update binder annotation of variables with default values/tactics"
        pure (ids, ty?, true)
      | `(bracketedBinderF|{$ids* $[: $ty?]?}) =>
        pure (ids, ty?, false)
      | `(bracketedBinderF|[$id : $_]) =>
        for binderId in binderIds do
          if binderId.raw.isIdent && binderId.raw.getId == id.getId then
            throwErrorAt binderId "cannot change the binder annotation of the previously declared local instance `{id.getId}`"
        varDeclsNew := varDeclsNew.push varDecl; continue
      | _ =>
        varDeclsNew := varDeclsNew.push varDecl; continue
    if explicit == explicit' then
      -- no update, ensure we don't have redundant annotations.
      for binderId in binderIds do
        if containsId ids binderId then
          throwErrorAt binderId "redundant binder annotation update"
      varDeclsNew := varDeclsNew.push varDecl
    else if binderIds.all fun binderId => !containsId ids binderId then
      -- `binderIds` and `ids` are disjoint
      varDeclsNew := varDeclsNew.push varDecl
    else
      let mkBinder (id : TSyntax [`ident, ``Parser.Term.hole]) (explicit : Bool) : CommandElabM (TSyntax ``Parser.Term.bracketedBinder) :=
        if explicit then
          `(bracketedBinderF| ($id $[: $ty?]?))
        else
          `(bracketedBinderF| {$id $[: $ty?]?})
      for id in ids do
        if let some idx := binderIds.findIdx? fun binderId => binderId.raw.isIdent && binderId.raw.getId == id.raw.getId then
          binderIds := binderIds.eraseIdx idx
          modifiedVarDecls := true
          varDeclsNew := varDeclsNew.push (← mkBinder id explicit)
        else
          varDeclsNew := varDeclsNew.push (← mkBinder id explicit')
  if modifiedVarDecls then
    modifyScope fun scope => { scope with varDecls := varDeclsNew }
  if binderIds.size != binderIdsIniSize then
    binderIds.mapM fun binderId =>
      if explicit then
        `(bracketedBinderF| ($binderId))
      else
        `(bracketedBinderF| {$binderId})
  else
    return #[binder]

/-- Declares one or more typed variables, or modifies whether already-declared variables are
implicit.

Introduces variables that can be used in definitions within the same `namespace` or `section` block.
When a definition mentions a variable, Lean will add it as an argument of the definition. The
`variable` command is also able to add typeclass parameters. This is useful in particular when
writing many definitions that have parameters in common (see below for an example).

Variable declarations have the same flexibility as regular function paramaters. In particular they
can be [explicit, implicit][binder docs], or [instance implicit][tpil classes] (in which case they
can be anonymous). This can be changed, for instance one can turn explicit variable `x` into an
implicit one with `variable {x}`. Note that currently, you should avoid changing how variables are
bound and declare new variables at the same time; see [issue 2789] for more on this topic.

See [*Variables and Sections* from Theorem Proving in Lean][tpil vars] for a more detailed
discussion.

[tpil vars]: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#variables-and-sections
(Variables and Sections on Theorem Proving in Lean)
[tpil classes]: https://lean-lang.org/theorem_proving_in_lean4/type_classes.html
(Type classes on Theorem Proving in Lean)
[binder docs]: https://leanprover-community.github.io/mathlib4_docs/Lean/Expr.html#Lean.BinderInfo
(Documentation for the BinderInfo type)
[issue 2789]: https://github.com/leanprover/lean4/issues/2789
(Issue 2789 on github)

## Examples

```lean
section
  variable
    {α : Type u}      -- implicit
    (a : α)           -- explicit
    [instBEq : BEq α] -- instance implicit, named
    [Hashable α]      -- instance implicit, anonymous

  def isEqual (b : α) : Bool :=
    a == b

  #check isEqual
  -- isEqual.{u} {α : Type u} (a : α) [instBEq : BEq α] (b : α) : Bool

  variable
    {a} -- `a` is implicit now

  def eqComm {b : α} := a == b ↔ b == a

  #check eqComm
  -- eqComm.{u} {α : Type u} {a : α} [instBEq : BEq α] {b : α} : Prop
end
```

The following shows a typical use of `variable` to factor out definition arguments:

```lean
variable (Src : Type)

structure Logger where
  trace : List (Src × String)
#check Logger
-- Logger (Src : Type) : Type

namespace Logger
  -- switch `Src : Type` to be implicit until the `end Logger`
  variable {Src}

  def empty : Logger Src where
    trace := []
  #check empty
  -- Logger.empty {Src : Type} : Logger Src

  variable (log : Logger Src)

  def len :=
    log.trace.length
  #check len
  -- Logger.len {Src : Type} (log : Logger Src) : Nat

  variable (src : Src) [BEq Src]

  -- at this point all of `log`, `src`, `Src` and the `BEq` instance can all become arguments

  def filterSrc :=
    log.trace.filterMap
      fun (src', str') => if src' == src then some str' else none
  #check filterSrc
  -- Logger.filterSrc {Src : Type} (log : Logger Src) (src : Src) [inst✝ : BEq Src] : List String

  def lenSrc :=
    log.filterSrc src |>.length
  #check lenSrc
  -- Logger.lenSrc {Src : Type} (log : Logger Src) (src : Src) [inst✝ : BEq Src] : Nat
end Logger
```

-/
@[builtin_command_elab «variable»] def elabVariable : CommandElab
  | `(variable $binders*) => do
    -- Try to elaborate `binders` for sanity checking
    runTermElabM fun _ => Term.withAutoBoundImplicit <|
      Term.elabBinders binders fun _ => pure ()
    for binder in binders do
      let binders ← replaceBinderAnnotation binder
      -- Remark: if we want to produce error messages when variables shadow existing ones, here is the place to do it.
      for binder in binders do
        let varUIds ← getBracketedBinderIds binder |>.mapM (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
        modifyScope fun scope => { scope with varDecls := scope.varDecls.push binder, varUIds := scope.varUIds ++ varUIds }
  | _ => throwUnsupportedSyntax

open Meta

def elabCheckCore (ignoreStuckTC : Bool) : CommandElab
  | `(#check%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_check do
    -- show signature for `#check id`/`#check @id`
    if let `($_:ident) := term then
      try
        for c in (← resolveGlobalConstWithInfos term) do
          addCompletionInfo <| .id term c (danglingDot := false) {} none
          logInfoAt tk <| .ofPPFormat { pp := fun
            | some ctx => ctx.runMetaM <| PrettyPrinter.ppSignature c
            | none     => return f!"{c}"  -- should never happen
          }
          return
      catch _ => pure ()  -- identifier might not be a constant but constant + projection
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := ignoreStuckTC)
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let type ← inferType e
    if e.isSyntheticSorry then
      return
    logInfoAt tk m!"{e} : {type}"
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Lean.Parser.Command.check] def elabCheck : CommandElab := elabCheckCore (ignoreStuckTC := true)

@[builtin_command_elab Lean.Parser.Command.reduce] def elabReduce : CommandElab
  | `(#reduce%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    -- TODO: add options or notation for setting the following parameters
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      let e ← withTransparency (mode := TransparencyMode.all) <| reduce e (skipProofs := false) (skipTypes := false)
      logInfoAt tk e
  | _ => throwUnsupportedSyntax

def hasNoErrorMessages : CommandElabM Bool := do
  return !(← get).messages.hasErrors

def failIfSucceeds (x : CommandElabM Unit) : CommandElabM Unit := do
  let resetMessages : CommandElabM MessageLog := do
    let s ← get
    let messages := s.messages;
    modify fun s => { s with messages := {} };
    pure messages
  let restoreMessages (prevMessages : MessageLog) : CommandElabM Unit := do
    modify fun s => { s with messages := prevMessages ++ s.messages.errorsToWarnings }
  let prevMessages ← resetMessages
  let succeeded ← try
    x
    hasNoErrorMessages
  catch
    | ex@(Exception.error _ _) => do logException ex; pure false
    | Exception.internal id _  => do logError (← id.getName); pure false
  finally
    restoreMessages prevMessages
  if succeeded then
    throwError "unexpected success"

@[builtin_command_elab «check_failure»] def elabCheckFailure : CommandElab
  | `(#check_failure $term) => do
    failIfSucceeds <| elabCheckCore (ignoreStuckTC := false) (← `(#check $term))
  | _ => throwUnsupportedSyntax

private def mkEvalInstCore (evalClassName : Name) (e : Expr) : MetaM Expr := do
  let α    ← inferType e
  let u    ← getDecLevel α
  let inst := mkApp (Lean.mkConst evalClassName [u]) α
  try
    synthInstance inst
  catch _ =>
    -- Put `α` in WHNF and try again
    try
      let α ← whnf α
      synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
    catch _ =>
      -- Fully reduce `α` and try again
      try
        let α ← reduce (skipTypes := false) α
        synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
      catch _ =>
        throwError "expression{indentExpr e}\nhas type{indentExpr α}\nbut instance{indentExpr inst}\nfailed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `{evalClassName}` class"

private def mkRunMetaEval (e : Expr) : MetaM Expr :=
  withLocalDeclD `env (mkConst ``Lean.Environment) fun env =>
  withLocalDeclD `opts (mkConst ``Lean.Options) fun opts => do
    let α ← inferType e
    let u ← getDecLevel α
    let instVal ← mkEvalInstCore ``Lean.MetaEval e
    let e := mkAppN (mkConst ``Lean.runMetaEval [u]) #[α, instVal, env, opts, e]
    instantiateMVars (← mkLambdaFVars #[env, opts] e)

private def mkRunEval (e : Expr) : MetaM Expr := do
  let α ← inferType e
  let u ← getDecLevel α
  let instVal ← mkEvalInstCore ``Lean.Eval e
  instantiateMVars (mkAppN (mkConst ``Lean.runEval [u]) #[α, instVal, mkSimpleThunk e])

unsafe def elabEvalUnsafe : CommandElab
  | `(#eval%$tk $term) => do
    let declName := `_eval
    let addAndCompile (value : Expr) : TermElabM Unit := do
      let value ← Term.levelMVarToParam (← instantiateMVars value)
      let type ← inferType value
      let us := collectLevelParams {} value |>.params
      let value ← instantiateMVars value
      let decl := Declaration.defnDecl {
        name        := declName
        levelParams := us.toList
        type        := type
        value       := value
        hints       := ReducibilityHints.opaque
        safety      := DefinitionSafety.unsafe
      }
      Term.ensureNoUnassignedMVars decl
      addAndCompile decl
    -- Elaborate `term`
    let elabEvalTerm : TermElabM Expr := do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
      if (← Term.logUnassignedUsingErrorInfos (← getMVars e)) then throwAbortTerm
      if (← isProp e) then
        mkDecide e
      else
        return e
    -- Evaluate using term using `MetaEval` class.
    let elabMetaEval : CommandElabM Unit := do
      -- act? is `some act` if elaborated `term` has type `CommandElabM α`
      let act? ← runTermElabM fun _ => Term.withDeclName declName do
        let e ← elabEvalTerm
        let eType ← instantiateMVars (← inferType e)
        if eType.isAppOfArity ``CommandElabM 1 then
          let mut stx ← Term.exprToSyntax e
          unless (← isDefEq eType.appArg! (mkConst ``Unit)) do
            stx ← `($stx >>= fun v => IO.println (repr v))
          let act ← Lean.Elab.Term.evalTerm (CommandElabM Unit) (mkApp (mkConst ``CommandElabM) (mkConst ``Unit)) stx
          pure <| some act
        else
          let e ← mkRunMetaEval e
          let env ← getEnv
          let opts ← getOptions
          let act ← try addAndCompile e; evalConst (Environment → Options → IO (String × Except IO.Error Environment)) declName finally setEnv env
          let (out, res) ← act env opts -- we execute `act` using the environment
          logInfoAt tk out
          match res with
          | Except.error e => throwError e.toString
          | Except.ok env  => do setEnv env; pure none
      let some act := act? | return ()
      act
    -- Evaluate using term using `Eval` class.
    let elabEval : CommandElabM Unit := runTermElabM fun _ => Term.withDeclName declName do
      -- fall back to non-meta eval if MetaEval hasn't been defined yet
      -- modify e to `runEval e`
      let e ← mkRunEval (← elabEvalTerm)
      let env ← getEnv
      let act ← try addAndCompile e; evalConst (IO (String × Except IO.Error Unit)) declName finally setEnv env
      let (out, res) ← liftM (m := IO) act
      logInfoAt tk out
      match res with
      | Except.error e => throwError e.toString
      | Except.ok _    => pure ()
    if (← getEnv).contains ``Lean.MetaEval then do
      elabMetaEval
    else
      elabEval
  | _ => throwUnsupportedSyntax

@[builtin_command_elab «eval», implemented_by elabEvalUnsafe]
opaque elabEval : CommandElab

@[builtin_command_elab «synth»] def elabSynth : CommandElab := fun stx => do
  let term := stx[1]
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_synth_cmd do
    let inst ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let inst ← instantiateMVars inst
    let val  ← synthInstance inst
    logInfo val
    pure ()

@[builtin_command_elab «set_option»] def elabSetOption : CommandElab := fun stx => do
  let options ← Elab.elabSetOption stx[1] stx[2]
  modify fun s => { s with maxRecDepth := maxRecDepth.get options }
  modifyScope fun scope => { scope with opts := options }

@[builtin_macro Lean.Parser.Command.«in»] def expandInCmd : Macro
  | `($cmd₁ in $cmd₂) => `(section $cmd₁:command $cmd₂ end)
  | _                 => Macro.throwUnsupported

@[builtin_command_elab Parser.Command.addDocString] def elabAddDeclDoc : CommandElab := fun stx => do
  match stx with
  | `($doc:docComment add_decl_doc $id) =>
    let declName ← resolveGlobalConstNoOverloadWithInfo id
    if let .none ← findDeclarationRangesCore? declName then
      -- this is only relevant for declarations added without a declaration range
      -- in particular `Quot.mk` et al which are added by `init_quot`
      addAuxDeclarationRanges declName stx id
    addDocString declName (← getDocStringText doc)
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Parser.Command.exit] def elabExit : CommandElab := fun _ =>
  logWarning "using 'exit' to interrupt Lean"

@[builtin_command_elab Parser.Command.import] def elabImport : CommandElab := fun _ =>
  throwError "invalid 'import' command, it must be used in the beginning of the file"

@[builtin_command_elab Parser.Command.eoi] def elabEoi : CommandElab := fun _ =>
  return

end Lean.Elab.Command
