/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.ReservedNameAction
public import Lean.AddDecl
public import Lean.Meta.Basic
public import Lean.Meta.Match.MatcherInfo
public import Lean.DefEqAttrib
public import Lean.Meta.LetToHave
import Lean.Meta.AppBuilder

public section

namespace Lean.Meta

register_builtin_option backward.eqns.nonrecursive : Bool := {
    defValue := true
    descr    := "Create fine-grained equational lemmas even for non-recursive definitions."
  }

register_builtin_option backward.eqns.deepRecursiveSplit : Bool := {
    defValue := true
    descr    := "Create equational lemmas for recursive functions like for non-recursive \
                functions. If disabled, match statements in recursive function definitions \
                that do not contain recursive calls do not cause further splits in the \
                equational lemmas. This was the behavior before Lean 4.12, and the purpose of \
                this option is to help migrating old code."
  }


/--
These options affect the generation of equational theorems in a significant way. For these, their
value at definition time, not realization time, should matter.

This is implemented by
 * eagerly realizing the equations when they are set to a non-default value
 * when realizing them lazily, reset the options to their default
-/
def eqnAffectingOptions : Array (Lean.Option Bool) := #[backward.eqns.nonrecursive, backward.eqns.deepRecursiveSplit]

/--
Environment extension for storing which declarations are recursive.
This information is populated by the `PreDefinition` module, but the simplifier
uses when unfolding declarations.
-/
builtin_initialize recExt : TagDeclarationExtension ←
  mkTagDeclarationExtension `recExt (asyncMode := .async .asyncEnv)

/--
Marks the given declaration as recursive.
-/
def markAsRecursive (declName : Name) : CoreM Unit :=
  modifyEnv (recExt.tag · declName)

/--
Returns `true` if `declName` was defined using well-founded recursion, or structural recursion.
-/
def isRecursiveDefinition (declName : Name) : CoreM Bool :=
  return recExt.isTagged (← getEnv) declName

def eqnThmSuffixBase := "eq"
def eqnThmSuffixBasePrefix := eqnThmSuffixBase ++ "_"
def eqn1ThmSuffix := eqnThmSuffixBasePrefix ++ "1"
example : eqn1ThmSuffix = "eq_1" := rfl

/-- Returns `true` if `s` is of the form `eq_<idx>` -/
def isEqnReservedNameSuffix (s : String) : Bool :=
  eqnThmSuffixBasePrefix.isPrefixOf s && (s.drop 3).isNat

def unfoldThmSuffix := "eq_def"
def eqUnfoldThmSuffix := "eq_unfold"

def isEqnLikeSuffix (s : String) : Bool :=
  s == unfoldThmSuffix || s == eqUnfoldThmSuffix || isEqnReservedNameSuffix s

/--
The equational theorem for a definition can be private even if the definition itself is not.
So un-private the name here when looking for a declaration
-/
def declFromEqLikeName (env : Environment) (name : Name) : Option (Name × String) := Id.run do
  if let .str p s := name then
    if isEqnLikeSuffix s then
      for p in [p, privateToUserName p] do
        -- Remark: `f.match_<idx>.eq_<idx>` are handled separately in `Lean.Meta.Match.MatchEqs`.
        if (env.setExporting false).isSafeDefinition p && !isMatcherCore env p then
          return some (p, s)
  return none

def mkEqLikeNameFor (env : Environment) (declName : Name) (suffix : String) : Name :=
  let isExposed := !env.header.isModule || ((env.setExporting true).find? declName).elim false (·.hasValue)
  let name := .str declName suffix
  let name := if isExposed then name else mkPrivateName env name
  name

/--
Throw an error if names for equation theorems for `declName` are not available.
-/
def ensureEqnReservedNamesAvailable (declName : Name) : CoreM Unit := do
  ensureReservedNameAvailable declName eqUnfoldThmSuffix
  ensureReservedNameAvailable declName unfoldThmSuffix
  ensureReservedNameAvailable declName eqn1ThmSuffix
  -- TODO: `declName` may need to reserve multiple `eq_<idx>` names, but we check only the first one.
  -- Possible improvement: try to efficiently compute the number of equation theorems at declaration time, and check all of them.

/--
Ensures that `f.eq_def`, `f.unfold` and `f.eq_<idx>` are reserved names if `f` is a safe definition.
-/
builtin_initialize registerReservedNamePredicate fun env n => Id.run do
  if let some (declName, suffix) := declFromEqLikeName env n then
    -- The reserved name predicate has to be precise, as `resolveExact`
    -- will believe it. So make sure that `n` is exactly the name we expect,
    -- including the privat prefix.
    n == mkEqLikeNameFor env declName suffix
  else
    false

@[expose] def GetEqnsFn := Name → MetaM (Option (Array Name))

private builtin_initialize getEqnsFnsRef : IO.Ref (List GetEqnsFn) ← IO.mkRef []

/--
Registers a new function for retrieving equation theorems.
We generate equations theorems on demand, and they are generated by more than one module.
For example, the structural and well-founded recursion modules generate them.
Most recent getters are tried first.

A getter returns an `Option (Array Name)`. The result is `none` if the getter failed.
Otherwise, it is a sequence of theorem names where each one of them corresponds to
an alternative. Example: the definition

```
def f (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x::xs => (x+1)::f xs
```
should have two equational theorems associated with it
```
f [] = []
```
and
```
(x : Nat) → (xs : List Nat) → f (x :: xs) = (x+1) :: f xs
```
-/
def registerGetEqnsFn (f : GetEqnsFn) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register equation getter, this kind of extension can only be registered during initialization")
  getEqnsFnsRef.modify (f :: ·)

/-- Returns `true` iff `declName` is a definition and its type is not a proposition. -/
private def shouldGenerateEqnThms (declName : Name) : MetaM Bool := do
  if let some { kind := .defn, sig, .. } := (← getEnv).findAsync? declName then
    return !(← isProp sig.get.type)
  else
    return false

/-- A mapping from equational theorem to the declaration it was derived from.  -/
structure EqnsExtState where
  mapInv : PHashMap Name Name := {}
  deriving Inhabited

/-- A mapping from equational theorem to the declaration it was derived from.  -/
builtin_initialize eqnsExt : EnvExtension EqnsExtState ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/--
Simple equation theorem for nonrecursive definitions.
-/
private def mkSimpleEqThm (declName : Name) : MetaM (Option Name) := do
  if let some (.defnInfo info) := (← getEnv).find? declName then
    let name := mkEqLikeNameFor (← getEnv) declName unfoldThmSuffix
    realizeConst declName name (doRealize name info)
    return some name
  else
    return none
where doRealize name info := do
  lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
    let lhs := mkAppN (mkConst info.name <| info.levelParams.map mkLevelParam) xs
    let type  ← mkForallFVars xs (← mkEq lhs body)
    -- Note: if this definition was added using `def`, then `letToHave` has already been applied to the body.
    let type  ← letToHave type
    let value ← mkLambdaFVars xs (← mkEqRefl lhs)
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
    inferDefEqAttr name -- should always succeed

/--
Returns `some declName` if `thmName` is an equational theorem for `declName`.
-/
def isEqnThm? (thmName : Name) : CoreM (Option Name) := do
  return eqnsExt.getState (← getEnv) |>.mapInv.find? thmName

/--
Returns `true` if `thmName` is an equational theorem.
-/
def isEqnThm (thmName : Name) : CoreM Bool := do
  return eqnsExt.getState (← getEnv) |>.mapInv.contains thmName

/--
Stores in the `eqnsExt` environment extension that `eqThms` are the equational theorems for `declName`
-/
private def registerEqnThms (declName : Name) (eqThms : Array Name) : CoreM Unit := do
  modifyEnv fun env => eqnsExt.modifyState env fun s => { s with
    mapInv := eqThms.foldl (init := s.mapInv) fun mapInv eqThm => mapInv.insert eqThm declName
  }

/--
Equation theorems are generated on demand, check whether they were generated in an imported file.
-/
private partial def alreadyGenerated? (declName : Name) : MetaM (Option (Array Name)) := do
  let env ← getEnv
  let eq1 := mkEqLikeNameFor env declName eqn1ThmSuffix
  if env.contains eq1 then
    let rec loop (idx : Nat) (eqs : Array Name) : MetaM (Array Name) := do
      let nextEq := mkEqLikeNameFor env declName s!"{eqnThmSuffixBasePrefix}{idx+1}"
      if env.containsOnBranch nextEq then
        loop (idx+1) (eqs.push nextEq)
      else
        return eqs
    let eqs ← loop 1 #[eq1]
    registerEqnThms declName eqs
    return some eqs
  else
    return none

private def getEqnsFor?Core (declName : Name) : MetaM (Option (Array Name)) := withLCtx {} {} do
  if !(← shouldGenerateEqnThms declName) then
    return none
  if let some eqs ← alreadyGenerated? declName then
    return some eqs
  for f in (← getEqnsFnsRef.get) do
    if let some r ← f declName then
      registerEqnThms declName r
      return some r
  return none

/--
Returns equation theorems for the given declaration.
-/
def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := withLCtx {} {} do
  -- This is the entry point for lazy equation generation. Ignore the current value
  -- of the options, and revert to the default.
  withOptions (eqnAffectingOptions.foldl fun os o => o.set os o.defValue) do
    getEqnsFor?Core declName

/--
If any equation theorem affecting option is not the default value, create the equations now.
-/
def generateEagerEqns (declName : Name) : MetaM Unit := do
  let opts ← getOptions
  if eqnAffectingOptions.any fun o => o.get opts != o.defValue then
    trace[Elab.definition.eqns] "generating eager equations for {declName}"
    let _ ← getEqnsFor?Core declName

@[expose] def GetUnfoldEqnFn := Name → MetaM (Option Name)

private builtin_initialize getUnfoldEqnFnsRef : IO.Ref (List GetUnfoldEqnFn) ← IO.mkRef []

/--
Registers a new function for retrieving a "unfold" equation theorem.

We generate this kind of equation theorem on demand, and it is generated by more than one module.
For example, the structural and well-founded recursion modules generate it.
Most recent getters are tried first.

A getter returns an `Option Name`. The result is `none` if the getter failed.
Otherwise, it is a theorem name. Example: the definition

```
def f (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x::xs => (x+1)::f xs
```
should have the theorem
```
(xs : Nat) →
  f xs =
    match xs with
    | [] => []
    | x::xs => (x+1)::f xs
```
-/
def registerGetUnfoldEqnFn (f : GetUnfoldEqnFn) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register equation getter, this kind of extension can only be registered during initialization")
  getUnfoldEqnFnsRef.modify (f :: ·)

/--
Returns an "unfold" theorem (`f.eq_def`) for the given declaration.
By default, we do not create unfold theorems for nonrecursive definitions.
You can use `nonRec := true` to override this behavior.
-/
def getUnfoldEqnFor? (declName : Name) (nonRec := false) : MetaM (Option Name) := withLCtx {} {} do
  let unfoldName := mkEqLikeNameFor (← getEnv) declName unfoldThmSuffix
  let r? ← withoutExporting do
    let env := (← getEnv)

    if env.contains unfoldName then
      return some unfoldName
    if (← shouldGenerateEqnThms declName) then
      if (← isRecursiveDefinition declName) then
        for f in (← getUnfoldEqnFnsRef.get) do
          if let some r ← f declName then
            return some r
      else
        if nonRec then
          return (← mkSimpleEqThm declName)
    return none
  if let some r := r? then
    unless r == unfoldName do
      throwError "invalid unfold theorem name `{r}` has been generated expected `{unfoldName}`"
  return r?

builtin_initialize
  registerReservedNameAction fun name => do
    withTraceNode `ReservedNameAction (pure m!"{exceptBoolEmoji ·} Lean.Meta.Eqns reserved name action for {name}") do
      if let some (declName, suffix) := declFromEqLikeName (← getEnv) name then
        if name == mkEqLikeNameFor (← getEnv) declName suffix then
          if isEqnReservedNameSuffix suffix then
            return (← MetaM.run' <| getEqnsFor? declName).isSome
          if suffix == unfoldThmSuffix then
            return (← MetaM.run' <| getUnfoldEqnFor? declName (nonRec := true)).isSome
      return false

end Lean.Meta
