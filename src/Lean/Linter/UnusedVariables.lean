/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mario Carneiro
-/
prelude
import Lean.Elab.Command
import Lean.Linter.Util
set_option linter.missingDocs true -- keep it documented

/-! # Unused variable Linter

This file implements the unused variable linter, which runs automatically on all
commands and reports any local variables that are never referred to, using
information from the info tree.

It is not immediately obvious but this is a surprisingly expensive check without
some optimizations.  The main complication is that it can be difficult to
determine what constitutes a "use" apart from direct references to a variable
that we can easily find in the info tree.  For example, we would like this to be
considered a use of `x`:
```
def foo (x : Nat) : Nat := by assumption
```

The final proof term is `fun x => x` so clearly `x` was used, but we can't make
use of this because the final proof term is after we have abstracted over the
original `fvar` for `x`. Instead, we make sure to store the proof term before
abstraction but after instantiation of mvars in the info tree and retrieve it in
the linter. Using the instantiated term is very important as redoing that step
in the linter can be prohibitively expensive. The downside of special-casing the
definition body in this way is that while it works for parameters, it does not
work for local variables in the body, so we ignore them by default if any tactic
infos are present (`linter.unusedVariables.analyzeTactics`).

If we do turn on this option and look further into the tactic state, we can see
the `fvar` show up in the instantiation to the original goal metavariable
`?m : Nat := x`, but it is not always the case that we can follow metavariable
instantiations to determine what happened after the fact, because tactics might
skip the goal metavariable and instantiate some other metavariable created prior
to it instead.  Instead, we use a (much more expensive) overapproximation, which
is just to look through the entire metavariable context looking for occurrences
of `x`. We use caching to ensure that this is still linear in the size of the
info tree, even though there are many metavariable contexts in all the
intermediate stages of elaboration; these are highly similar and make use of
`PersistentHashMap` so there is a lot of subterm sharing we can take advantage
of.

## The `@[unused_variables_ignore_fn]` attribute

Some occurrences of variables are deliberately unused, or at least we don't want
to lint on unused variables in these positions. For example:

```
def foo (x : Nat) : (y : Nat) → Nat := fun _ => x
                  -- ^ don't lint this unused variable because it is public API
```

They are generally a syntactic criterion, so we allow adding custom
`IgnoreFunction`s so that external syntax can also opt in to lint suppression,
like so:

```
macro (name := foobarKind) "foobar " name:ident : command => `(def foo ($name : Nat) := 0)

foobar n -- linted because n is unused in the macro expansion

@[unused_variables_ignore_fn]
def ignoreFoobar : Lean.Linter.IgnoreFunction := fun _ stack _ => stack.matches [``foobarKind]

foobar n -- not linted
```

-/

namespace Lean.Linter
open Lean.Elab.Command Lean.Server Std

/-- Enables or disables all unused variable linter warnings -/
register_builtin_option linter.unusedVariables : Bool := {
  defValue := true,
  descr := "enable the 'unused variables' linter"
}
/-- Enables or disables unused variable linter warnings in function arguments -/
register_builtin_option linter.unusedVariables.funArgs : Bool := {
  defValue := true,
  descr := "enable the 'unused variables' linter to mark unused function arguments"
}
/-- Enables or disables unused variable linter warnings in patterns -/
register_builtin_option linter.unusedVariables.patternVars : Bool := {
  defValue := true,
  descr := "enable the 'unused variables' linter to mark unused pattern variables"
}
/-- Enables linting variables defined in tactic blocks, may be expensive for complex proofs -/
register_builtin_option linter.unusedVariables.analyzeTactics : Bool := {
  defValue := false
  descr := "enable analysis of local variables in presence of tactic proofs\
          \n\
          \nBy default, the linter will limit itself to linting a declaration's parameters \
            whenever tactic proofs are present as these can be expensive to analyze. Enabling this \
            option extends linting to local variables both inside and outside tactic proofs, \
            though it can also lead to some false negatives as intermediate tactic states may \
            reference some variables without the declaration ultimately depending on them."
}

/-- Gets the status of `linter.unusedVariables` -/
def getLinterUnusedVariables (o : Options) : Bool :=
  getLinterValue linter.unusedVariables o

/-- Gets the status of `linter.unusedVariables.funArgs` -/
def getLinterUnusedVariablesFunArgs (o : Options) : Bool :=
  o.get linter.unusedVariables.funArgs.name (getLinterUnusedVariables o)

/-- Gets the status of `linter.unusedVariables.patternVars` -/
def getLinterUnusedVariablesPatternVars (o : Options) : Bool :=
  o.get linter.unusedVariables.patternVars.name (getLinterUnusedVariables o)

/-- An `IgnoreFunction` receives:

* a `Syntax.ident` for the unused variable
* a `Syntax.Stack` with the location of this piece of syntax in the command
* The `Options` set locally to this syntax

and should return `true` to indicate that the lint should be suppressed,
or `false` to proceed with linting as usual (other `IgnoreFunction`s may still
say it is ignored). A variable is only linted if it is unused and no
`IgnoreFunction` returns `true` on this syntax.
-/
abbrev IgnoreFunction := Syntax → Syntax.Stack → Options → Bool

/-- Interpret an `IgnoreFunction` from the environment. -/
unsafe def mkIgnoreFnImpl (constName : Name) : ImportM IgnoreFunction := do
  let { env, opts, .. } ← read
  match env.find? constName with
  | none      => throw ↑s!"unknown constant '{constName}'"
  | some info =>
    unless info.type.isConstOf ``IgnoreFunction do
      throw ↑s!"unexpected unused_variables_ignore_fn at '{constName}', must be of type `Lean.Linter.IgnoreFunction`"
    IO.ofExcept <| env.evalConst IgnoreFunction opts constName

@[inherit_doc mkIgnoreFnImpl, implemented_by mkIgnoreFnImpl]
opaque mkIgnoreFn (constName : Name) : ImportM IgnoreFunction

/-- The list of builtin `IgnoreFunction`s. -/
builtin_initialize builtinUnusedVariablesIgnoreFnsRef : IO.Ref <| Array IgnoreFunction ← IO.mkRef #[]

/-- Adds a new builtin `IgnoreFunction`.
This function should only be used from within the `Lean` package. -/
def addBuiltinUnusedVariablesIgnoreFn (h : IgnoreFunction) : IO Unit :=
  builtinUnusedVariablesIgnoreFnsRef.modify (·.push h)

/-- An extension which keeps track of registered `IgnoreFunction`s. -/
builtin_initialize unusedVariablesIgnoreFnsExt :
  PersistentEnvExtension Name (Name × IgnoreFunction) (List Name × Array IgnoreFunction) ←
  registerPersistentEnvExtension {
    mkInitial       := return ([], ← builtinUnusedVariablesIgnoreFnsRef.get)
    addImportedFn   := fun as => do
      ([], ·) <$> as.foldlM (init := ← builtinUnusedVariablesIgnoreFnsRef.get) fun s as =>
        as.foldlM (init := s) fun s n => s.push <$> mkIgnoreFn n
    addEntryFn      := fun (entries, s) (n, h) => (n::entries, s.push h)
    exportEntriesFn := fun s => s.1.reverse.toArray
    statsFn := fun s => format "number of local entries: " ++ format s.1.length
  }

/-- Adds the `@[{builtin_}unused_variables_ignore_fn]` attribute, which is applied
to declarations of type `IgnoreFunction` for use by the unused variables linter. -/
builtin_initialize
  let mkAttr (builtin : Bool) (name : Name) := registerBuiltinAttribute {
    name
    descr           := (if builtin then "(builtin) " else "") ++
      "Marks a function of type `Lean.Linter.IgnoreFunction` for suppressing unused variable warnings"
    applicationTime := .afterCompilation
    add             := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
      unless (← getConstInfo decl).type.isConstOf ``IgnoreFunction do
        throwError "invalid attribute '{name}', must be of type `Lean.Linter.IgnoreFunction`"
      let env ← getEnv
      if builtin then
        let h := mkConst decl
        declareBuiltin decl <| mkApp (mkConst ``addBuiltinUnusedVariablesIgnoreFn) h
      else
        setEnv <| unusedVariablesIgnoreFnsExt.addEntry env (decl, ← mkIgnoreFn decl)
  }
  mkAttr true `builtin_unused_variables_ignore_fn
  mkAttr false `unused_variables_ignore_fn

/-- `variable (unused : Nat)` -/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
    stack.matches [`null, none, `null, ``Lean.Parser.Command.variable])

/-- `structure Foo where unused : Nat` -/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, ``Lean.Parser.Command.structure])

/-- `inductive Foo where | unused : Foo` -/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, none, ``Lean.Parser.Command.inductive] &&
  (stack.get? 3 |>.any fun (stx, pos) =>
    pos == 0 &&
    [``Lean.Parser.Command.optDeclSig, ``Lean.Parser.Command.declSig].any (stx.isOfKind ·)))

/--
* `structure Foo where foo (unused : Nat) : Nat`
* `inductive Foo where | mk (unused : Nat) : Foo`
-/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, ``Lean.Parser.Command.optDeclSig, none] &&
  (stack.get? 4 |>.any fun (stx, _) =>
    [``Lean.Parser.Command.ctor, ``Lean.Parser.Command.structSimpleBinder].any (stx.isOfKind ·)))

/--
* `opaque foo (unused : Nat) : Nat`
* `axiom foo (unused : Nat) : Nat`
-/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, ``Lean.Parser.Command.declSig, none] &&
  (stack.get? 4 |>.any fun (stx, _) =>
    [``Lean.Parser.Command.opaque, ``Lean.Parser.Command.axiom].any (stx.isOfKind ·)))

/--
Definition with foreign definition
* `@[extern "bla"] def foo (unused : Nat) : Nat := ...`
* `@[implemented_by bla] def foo (unused : Nat) : Nat := ...`
-/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, none, none, ``Lean.Parser.Command.declaration] &&
  (stack.get? 3 |>.any fun (stx, _) =>
    stx.isOfKind ``Lean.Parser.Command.optDeclSig ||
    stx.isOfKind ``Lean.Parser.Command.declSig) &&
  (stack.get? 5 |>.any fun (stx, _) => match stx[0] with
    | `(Lean.Parser.Command.declModifiersT| $[$_:docComment]? @[$[$attrs:attr],*] $[$vis]? $[noncomputable]?) =>
      attrs.any (fun attr => attr.raw.isOfKind ``Parser.Attr.extern || attr matches `(attr| implemented_by $_))
    | _ => false))

/--
Dependent arrow
* `def foo : (unused : Nat) → Nat := id`
-/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, ``Lean.Parser.Term.explicitBinder, ``Lean.Parser.Term.depArrow])

/--
Function argument in let declaration (when `linter.unusedVariables.funArgs` is false)
* `def foo := let x (unused : Nat) := 1; x`
-/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesFunArgs opts &&
  stack.matches [`null, none, `null, ``Lean.Parser.Term.letIdDecl, none] &&
  (stack.get? 3 |>.any fun (_, pos) => pos == 1) &&
  (stack.get? 5 |>.any fun (stx, _) => !stx.isOfKind ``Lean.Parser.Command.whereStructField))

/--
Function argument in declaration signature (when `linter.unusedVariables.funArgs` is false)
* `def foo (unused : Nat) := 1`
-/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesFunArgs opts &&
  stack.matches [`null, none, `null, none] &&
  (stack.get? 3 |>.any fun (stx, pos) =>
    pos == 0 &&
    [``Lean.Parser.Command.optDeclSig, ``Lean.Parser.Command.declSig].any (stx.isOfKind ·)))

/--
Function argument in function definition (when `linter.unusedVariables.funArgs` is false)
* `def foo := fun (unused : Nat) => 1`
-/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesFunArgs opts &&
  (stack.matches [`null, ``Lean.Parser.Term.basicFun] ||
  stack.matches [``Lean.Parser.Term.typeAscription, `null, ``Lean.Parser.Term.basicFun]))

/--
In pattern (when `linter.unusedVariables.patternVars` is false)
* `def foo := match 0 with | unused => 1`
-/
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesPatternVars opts &&
  stack.any fun (stx, pos) =>
    (stx.isOfKind ``Lean.Parser.Term.matchAlt && pos == 1) ||
    (stx.isOfKind ``Lean.Parser.Tactic.inductionAltLHS && pos == 2))

/-- Get the current list of `IgnoreFunction`s. -/
def getUnusedVariablesIgnoreFns : CommandElabM (Array IgnoreFunction) := do
  return (unusedVariablesIgnoreFnsExt.getState (← getEnv)).2

namespace UnusedVariables

/-- Collect into a heterogeneous collection of objects with external storage. This uses
pointer identity and does not store the objects, so it is important not to store the last
pointer to an object in the map, or it can be freed and reused, resulting in incorrect behavior.

Returns `true` if the object was not already in the set. -/
unsafe def insertObjImpl {α : Type} (set : IO.Ref (Std.HashSet USize)) (a : α) : IO Bool := do
  if (← set.get).contains (ptrAddrUnsafe a) then
    return false
  set.modify (·.insert (ptrAddrUnsafe a))
  return true

@[inherit_doc insertObjImpl, implemented_by insertObjImpl]
opaque insertObj {α : Type} (set : IO.Ref (Std.HashSet USize)) (a : α) : IO Bool

/--
Collects into `fvarUses` all `fvar`s occurring in the `Expr`s in `assignments`.
This implementation respects subterm sharing in both the `PersistentHashMap` and the `Expr`
to ensure that pointer-equal subobjects are not visited multiple times, which is important
in practice because these expressions are very frequently highly shared.
-/
partial def visitAssignments (set : IO.Ref (Std.HashSet USize))
    (fvarUses : IO.Ref (Std.HashSet FVarId))
    (assignments : Array (PersistentHashMap MVarId Expr)) : IO Unit := do
  MonadCacheT.run do
    for assignment in assignments do
      visitNode assignment.root
where
  /-- Visit a `PersistentHashMap.Node`, collecting all fvars in it into `fvarUses` -/
  visitNode node : MonadCacheT Expr Unit IO Unit := do
    if ← insertObj set node then
      match node with
      | .entries entries => for e in entries do visitEntry e
      | .collision _ vs _ => for e in vs do visitExpr e
  /-- Visit a `PersistentHashMap.Entry`, collecting all fvars in it into `fvarUses` -/
  visitEntry e : MonadCacheT Expr Unit IO Unit := do
    if ← insertObj set e then
      match e with
      | .entry _ e => visitExpr e
      | .ref node => visitNode node
      | .null => pure ()
  /-- Visit an `Expr`, collecting all fvars in it into `fvarUses` -/
  visitExpr e : MonadCacheT Expr Unit IO Unit := do
    if ← insertObj set e then
      ForEachExpr.visit (e := e) fun e => do
        match e with
        | .fvar id => fvarUses.modify (·.insert id); return false
        | _ => return e.hasFVar

/-- Given `aliases` as a map from an alias to what it aliases, we get the original
term by recursion. This has no cycle detection, so if `aliases` contains a loop
then this function will recurse infinitely. -/
partial def followAliases (aliases : Std.HashMap FVarId FVarId) (x : FVarId) : FVarId :=
  match aliases[x]? with
  | none => x
  | some y => followAliases aliases y

/-- Information regarding an `FVarId` definition. -/
structure FVarDefinition where
  /-- The user-provided name of the `FVarId` -/
  userName : Name
  /-- A (usually `.ident`) syntax for the defined variable -/
  stx : Syntax
  /-- The options set locally to this part of the syntax (used by `IgnoreFn`) -/
  opts : Options
  /-- The list of all `FVarId`s that are considered as being defined at this position.
  This can have more than one element if multiple variables are declared by the same
  syntax, such as the `h` in `if h : c then ... else ...`. We only report an unused variable
  at this span if all variables in `aliases` are unused. -/
  aliases : Array FVarId

/-- The main data structure used to collect information from the info tree regarding unused
variables. -/
structure References where
  /-- The set of all (ranges corresponding to) global definitions that are made in the syntax.
  For example in `mutual def foo := ...  def bar := ... where baz := ... end` this would be
  the spans for `foo`, `bar`, and `baz`. Global definitions are always treated as used.
  (It would be nice to be able to detect unused global definitions but this requires more
  information than the linter framework can provide.) -/
  constDecls : Std.HashSet String.Range := .empty
  /-- The collection of all local declarations, organized by the span of the declaration.
  We collapse all declarations declared at the same position into a single record using
  `FVarDefinition.aliases`. -/
  fvarDefs : Std.HashMap String.Range FVarDefinition := .empty
  /-- The set of `FVarId`s that are used directly. These may or may not be aliases. -/
  fvarUses : Std.HashSet FVarId := .empty
  /-- A mapping from alias to original FVarId. We don't guarantee that the value is not itself
  an alias, but we use `followAliases` when adding new elements to try to avoid long chains. -/
  -- TODO: use a `UnionFind` data structure here
  fvarAliases : Std.HashMap FVarId FVarId := .empty
  /-- Collection of all `MetavarContext`s following the execution of a tactic. We trawl these
  if needed to find additional `fvarUses`. -/
  assignments : Array (PersistentHashMap MVarId Expr) := #[]

/-- Collect information from the `infoTrees` into `References`.
See `References` for more information about the return value. -/
partial def collectReferences (infoTrees : Array Elab.InfoTree) (cmdStxRange : String.Range) :
    StateRefT References IO Unit := ReaderT.run (r := false) <| go infoTrees none
where
  go infoTrees ctx? := do
    for tree in infoTrees do
      tree.visitM' (ctx? := ctx?) (preNode := fun ci info children => do
        -- set if `analyzeTactics` is unset, tactic infos are present, and we're inside the body
        let ignored ← read
        match info with
        | .ofCustomInfo ti =>
          if !linter.unusedVariables.analyzeTactics.get ci.options then
            if let some bodyInfo := ti.value.get? Elab.Term.BodyInfo then
              if let some value := bodyInfo.value? then
                -- the body is the only `Expr` we will analyze in this case
                -- NOTE: we include it even if no tactics are present as at least for parameters we want
                -- to lint only truly unused binders
                let (e, _) := instantiateMVarsCore ci.mctx value
                modify fun s => { s with
                  assignments := s.assignments.push (.insert {} ⟨.anonymous⟩ e) }
                let tacticsPresent := children.any (·.findInfo? (· matches .ofTacticInfo ..) |>.isSome)
                withReader (· || tacticsPresent) do
                  go children.toArray ci
                return false
        | .ofTermInfo ti =>
          if ignored then return true
          match ti.expr with
          | .const .. =>
            if ti.isBinder then
              let some range := info.range? | return true
              let .original .. := info.stx.getHeadInfo | return true -- we are not interested in canonical syntax here
              modify fun s => { s with constDecls := s.constDecls.insert range }
          | .fvar id .. =>
            let some range := info.range? | return true
            let .original .. := info.stx.getHeadInfo | return true -- we are not interested in canonical syntax here
            if ti.isBinder then
              -- This is a local variable declaration.
              if ignored then return true
              let some ldecl := ti.lctx.find? id | return true
              -- Skip declarations which are outside the command syntax range, like `variable`s
              -- (it would be confusing to lint these), or those which are macro-generated
              if !cmdStxRange.contains range.start || ldecl.userName.hasMacroScopes then return true
              let opts := ci.options
              -- we have to check for the option again here because it can be set locally
              if !getLinterUnusedVariables opts then return true
              let stx := skipDeclIdIfPresent info.stx
              if let .str _ s := stx.getId then
                -- If the variable name is `_foo` then it is intentionally (possibly) unused, so skip.
                -- This is the suggested way to silence the warning
                if s.startsWith "_" then return true
              -- Record this either as a new `fvarDefs`, or an alias of an existing one
              modify fun s =>
                if let some ref := s.fvarDefs[range]? then
                  { s with fvarDefs := s.fvarDefs.insert range { ref with aliases := ref.aliases.push id } }
                else
                  { s with fvarDefs := s.fvarDefs.insert range { userName := ldecl.userName, stx, opts, aliases := #[id] } }
            else
              -- Found a direct use, keep track of it
              modify fun s => { s with fvarUses := s.fvarUses.insert id }
          | _ => pure ()
        | .ofTacticInfo ti =>
          -- When ignoring new binders, no need to look at intermediate tactic states either as
          -- references to binders outside the body will be covered by the body `Expr`
          if ignored then return true
          -- Keep track of the `MetavarContext` after a tactic for later
          modify fun s => { s with assignments := s.assignments.push ti.mctxAfter.eAssignment }
        | .ofFVarAliasInfo i =>
          if ignored then return true
          -- record any aliases we find
          modify fun s =>
            let id := followAliases s.fvarAliases i.baseId
            { s with fvarAliases := s.fvarAliases.insert i.id id }
        | _ => pure ()
        return true)
  /-- Since declarations attach the declaration info to the `declId`,
  we skip that to get to the `.ident` if possible. -/
  skipDeclIdIfPresent (stx : Syntax) : Syntax :=
    if stx.isOfKind ``Lean.Parser.Command.declId then
      stx[0]
    else
      stx

/-- Reports unused variable warnings on each command. Use `linter.unusedVariables` to disable. -/
def unusedVariables : Linter where
  run cmdStx := do
    unless getLinterUnusedVariables (← getOptions) do
      return

    -- NOTE: `messages` is local to the current command
    if (← get).messages.hasErrors then
      return

    let some cmdStxRange := cmdStx.getRange?
      | return

    let infoTrees := (← get).infoState.trees.toArray

    if (← infoTrees.anyM (·.hasSorry)) then
      return

    -- Run the main collection pass, resulting in `s : References`.
    let (_, s) ← (collectReferences infoTrees cmdStxRange).run {}

    -- If there are no local defs then there is nothing to do
    if s.fvarDefs.isEmpty then return

    -- Resolve all recursive references in `fvarAliases`.
    -- At this point everything in `fvarAliases` is guaranteed not to be itself an alias,
    -- and should point to some element of `FVarDefinition.aliases` in `s.fvarDefs`
    let fvarAliases : Std.HashMap FVarId FVarId := s.fvarAliases.fold (init := {}) fun m id baseId =>
      m.insert id (followAliases s.fvarAliases baseId)

    let getCanonVar (id : FVarId) : FVarId := fvarAliases.getD id id

    -- Collect all non-alias fvars corresponding to `fvarUses` by resolving aliases in the list.
    -- Unlike `s.fvarUses`, `fvarUsesRef` is guaranteed to contain no aliases.
    let fvarUsesRef ← IO.mkRef <| fvarAliases.fold (init := s.fvarUses) fun fvarUses id baseId =>
      if fvarUses.contains id then fvarUses.insert baseId else fvarUses

    -- Collect ignore functions
    let ignoreFns ← getUnusedVariablesIgnoreFns

    let mut initializedMVars := false
    let mut unused := #[]
    -- For each variable definition, check to see if it is used
    for (range, { userName, stx := declStx, opts, aliases }) in s.fvarDefs.toArray do
      let fvarUses ← fvarUsesRef.get
      -- If any of the `fvar`s corresponding to this declaration is (an alias of) a variable in
      -- `fvarUses`, then it is used
      if aliases.any fun id => fvarUses.contains (getCanonVar id) then continue
      -- If this is a global declaration then it is (potentially) used after the command
      if s.constDecls.contains range then continue

      -- Get the syntax stack for this variable declaration
      let some ((id', _) :: stack) := cmdStx.findStack? (·.getRange?.any (·.includes range))
        | continue

      -- If it is blacklisted by an `ignoreFn` then skip it
      if id'.isIdent && ignoreFns.any (· declStx stack opts) then continue

      -- Evaluate ignore functions again on macro expansion outputs
      if ← infoTrees.anyM fun tree => do
        let some macroExpansions ← collectMacroExpansions? range tree | return false
        return macroExpansions.any fun expansion =>
          -- in a macro expansion, there may be multiple leafs whose (synthetic) range
          -- includes `range`, so accept strict matches only
          if let some (_ :: stack) :=
            expansion.output.findStack?
              (·.getRange?.any (·.includes range))
              (fun stx => stx.isIdent && stx.getRange?.any (· == range))
          then
            ignoreFns.any (· declStx stack opts)
          else
            false
      then
        continue

      -- Visiting the metavariable assignments is expensive so we delay initialization
      if !initializedMVars then
        -- collect additional `fvarUses` from tactic assignments
        visitAssignments (← IO.mkRef {}) fvarUsesRef s.assignments
        -- Resolve potential aliases again to preserve `fvarUsesRef` invariant
        fvarUsesRef.modify fun fvarUses => fvarUses.toArray.map getCanonVar |> .insertMany {}
        initializedMVars := true
        let fvarUses ← fvarUsesRef.get
        -- Redo the initial check because `fvarUses` could be bigger now
        if aliases.any fun id => fvarUses.contains (getCanonVar id) then continue

      -- If we made it this far then the variable is unused and not ignored
      unused := unused.push (declStx, userName)

    -- Sort the outputs by position
    for (declStx, userName) in unused.qsort (·.1.getPos?.get! < ·.1.getPos?.get!) do
      logLint linter.unusedVariables declStx m!"unused variable `{userName}`"

builtin_initialize addLinter unusedVariables

end UnusedVariables
end Linter

/-- Returns true if this is a message produced by the unused variable linter.
This is used to give these messages an additional "faded" style in the editor. -/
def MessageData.isUnusedVariableWarning (msg : MessageData) : Bool :=
  msg.hasTag (· == Linter.linter.unusedVariables.name)
