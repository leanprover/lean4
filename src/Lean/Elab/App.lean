/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.FindMVar
import Lean.Util.CollectFVars
import Lean.Parser.Term
import Lean.Meta.KAbstract
import Lean.Meta.Tactic.ElimInfo
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Lean.Elab.Arg
import Lean.Elab.RecAppSyntax

namespace Lean.Elab.Term
open Meta

builtin_initialize elabWithoutExpectedTypeAttr : TagAttribute ←
  registerTagAttribute `elab_without_expected_type "mark that applications of the given declaration should be elaborated without the expected type"

def hasElabWithoutExpectedType (env : Environment) (declName : Name) : Bool :=
  elabWithoutExpectedTypeAttr.hasTag env declName

instance : ToString Arg where
  toString
    | .stx  val => toString val
    | .expr val => toString val

instance : ToString NamedArg where
  toString s := "(" ++ toString s.name ++ " := " ++ toString s.val ++ ")"

def throwInvalidNamedArg (namedArg : NamedArg) (fn? : Option Name) : TermElabM α :=
  withRef namedArg.ref <| match fn? with
    | some fn => throwError "invalid argument name '{namedArg.name}' for function '{fn}'"
    | none    => throwError "invalid argument name '{namedArg.name}' for function"

private def ensureArgType (f : Expr) (arg : Expr) (expectedType : Expr) : TermElabM Expr := do
  try
    ensureHasType expectedType arg none f
  catch
    | ex@(.error ..) =>
      if (← read).errToSorry then
        exceptionToSorry ex expectedType
      else
        throw ex
    | ex => throw ex

private def mkProjAndCheck (structName : Name) (idx : Nat) (e : Expr) : MetaM Expr := do
  let r := mkProj structName idx e
  let eType ← inferType e
  if (← isProp eType) then
    let rType ← inferType r
    if !(← isProp rType) then
      throwError "invalid projection, the expression{indentExpr e}\nis a proposition and has type{indentExpr eType}\nbut the projected value is not, it has type{indentExpr rType}"
  return r

def synthesizeAppInstMVars (instMVars : Array MVarId) (app : Expr) : TermElabM Unit :=
  for mvarId in instMVars do
    unless (← synthesizeInstMVarCore mvarId) do
      registerSyntheticMVarWithCurrRef mvarId (.typeClass none)
      registerMVarErrorImplicitArgInfo mvarId (← getRef) app

/-- Return `some namedArg` if `namedArgs` contains an entry for `binderName`. -/
private def findBinderName? (namedArgs : List NamedArg) (binderName : Name) : Option NamedArg :=
  namedArgs.find? fun namedArg => namedArg.name == binderName

/-- Erase entry for `binderName` from `namedArgs`. -/
def eraseNamedArg (namedArgs : List NamedArg) (binderName : Name) : List NamedArg :=
  namedArgs.filter (·.name != binderName)

/-- Return true if the given type contains `OptParam` or `AutoParams` -/
private def hasOptAutoParams (type : Expr) : MetaM Bool := do
  forallTelescopeReducing type fun xs _ =>
    xs.anyM fun x => do
      let xType ← inferType x
      return xType.getOptParamDefault?.isSome || xType.getAutoParamTactic?.isSome


/-! # Default application elaborator -/
namespace ElabAppArgs

structure Context where
  /--
   `true` if `..` was used
  -/
  ellipsis      : Bool  --
  /--
   `true` if `@` modifier was used
  -/
  explicit      : Bool
  /--
    If the result type of an application is the `outParam` of some local instance, then special support may be needed
    because type class resolution interacts poorly with coercions in this kind of situation.
    This flag enables the special support.

    The idea is quite simple, if the result type is the `outParam` of some local instance, we simply
    execute `synthesizeSyntheticMVarsUsingDefault`. We added this feature to make sure examples as follows
    are correctly elaborated.
    ```lean
    class GetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
      getElem (xs : Cont) (i : Idx) : Elem

    export GetElem (getElem)

    instance : GetElem (Array α) Nat α where
      getElem xs i := xs.get ⟨i, sorry⟩

    opaque f : Option Bool → Bool
    opaque g : Bool → Bool

    def bad (xs : Array Bool) : Bool :=
      let x := getElem xs 0
      f x && g x
    ```
    Without the special support, Lean fails at `g x` saying `x` has type `Option Bool` but is expected to have type `Bool`.
    From the user's point of view this is a bug, since `let x := getElem xs 0` clearly constrains `x` to be `Bool`, but
    we only obtain this information after we apply the `OfNat` default instance for `0`.

    Before converging to this solution, we have tried to create a "coercion placeholder" when `resultIsOutParamSupport = true`,
    but it did not work well in practice. For example, it failed in the example above.
  -/
  resultIsOutParamSupport : Bool

/-- Auxiliary structure for elaborating the application `f args namedArgs`. -/
structure State where
  f                    : Expr
  fType                : Expr
  /-- Remaining regular arguments. -/
  args                 : List Arg
  /-- remaining named arguments to be processed. -/
  namedArgs            : List NamedArg
  expectedType?        : Option Expr
  /--
    When named arguments are provided and explicit arguments occurring before them are missing,
    the elaborator eta-expands the declaration. For example,
    ```
    def f (x y : Nat) := x + y
    #check f (y := 5)
    -- fun x => f x 5
    ```
    `etaArgs` stores the fresh free variables for implementing the eta-expansion.
    When `..` is used, eta-expansion is disabled, and missing arguments are treated as `_`.
  -/
  etaArgs              : Array Expr   := #[]
  /-- Metavariables that we need to set the error context using the application being built. -/
  toSetErrorCtx        : Array MVarId := #[]
  /-- Metavariables for the instance implicit arguments that have already been processed. -/
  instMVars            : Array MVarId := #[]
  /--
    The following field is used to implement the `propagateExpectedType` heuristic.
    It is set to `true` true when `expectedType` still has to be propagated.
  -/
  propagateExpected    : Bool
  /--
    If the result type may be the `outParam` of some local instance.
    See comment at `Context.resultIsOutParamSupport`
   -/
  resultTypeOutParam?  : Option MVarId := none

abbrev M := ReaderT Context (StateRefT State TermElabM)

/-- Add the given metavariable to the collection of metavariables associated with instance-implicit arguments. -/
private def addInstMVar (mvarId : MVarId) : M Unit :=
  modify fun s => { s with instMVars := s.instMVars.push mvarId }

/--
  Try to synthesize metavariables are `instMVars` using type class resolution.
  The ones that cannot be synthesized yet stay in the `instMVars` list.
  Remark: we use this method
    - before trying to apply coercions to function,
    - before unifying the expected type.
-/
def trySynthesizeAppInstMVars : M Unit := do
  let instMVars ← (← get).instMVars.filterM fun instMVar => do
    unless (← instantiateMVars (← inferType (.mvar instMVar))).isMVar do try
      if (← synthesizeInstMVarCore instMVar) then
        return false
      catch _ => pure ()
    return true
  modify ({ · with instMVars })

/--
  Try to synthesize metavariables are `instMVars` using type class resolution.
  The ones that cannot be synthesized yet are registered.
-/
def synthesizeAppInstMVars : M Unit := do
  Term.synthesizeAppInstMVars (← get).instMVars (← get).f
  modify ({ · with instMVars := #[] })

/-- fType may become a forallE after we synthesize pending metavariables. -/
private def synthesizePendingAndNormalizeFunType : M Unit := do
  trySynthesizeAppInstMVars
  synthesizeSyntheticMVars
  let s ← get
  let fType ← whnfForall s.fType
  if fType.isForall then
    modify fun s => { s with fType }
  else
    if let some f ← coerceToFunction? s.f then
      let fType ← inferType f
      modify fun s => { s with f, fType }
    else
      for namedArg in s.namedArgs do
        let f := s.f.getAppFn
        if f.isConst then
          throwInvalidNamedArg namedArg f.constName!
        else
          throwInvalidNamedArg namedArg none
      throwError "function expected at{indentExpr s.f}\nterm has type{indentExpr fType}"

/-- Normalize and return the function type. -/
private def normalizeFunType : M Expr := do
  let s ← get
  let fType ← whnfForall s.fType
  modify fun s => { s with fType }
  return fType

/-- Return the binder name at `fType`. This method assumes `fType` is a function type. -/
private def getBindingName : M Name := return (← get).fType.bindingName!

/-- Return the next argument expected type. This method assumes `fType` is a function type. -/
private def getArgExpectedType : M Expr := return (← get).fType.bindingDomain!

/-- Remove named argument with name `binderName` from `namedArgs`. -/
def eraseNamedArg (binderName : Name) : M Unit :=
  modify fun s => { s with namedArgs := Term.eraseNamedArg s.namedArgs binderName }

/--
  Add a new argument to the result. That is, `f := f arg`, update `fType`.
  This method assumes `fType` is a function type. -/
private def addNewArg (argName : Name) (arg : Expr) : M Unit := do
  modify fun s => { s with f := mkApp s.f arg, fType := s.fType.bindingBody!.instantiate1 arg }
  if arg.isMVar then
    registerMVarArgName arg.mvarId! argName

/--
  Elaborate the given `Arg` and add it to the result. See `addNewArg`.
  Recall that, `Arg` may be wrapping an already elaborated `Expr`. -/
private def elabAndAddNewArg (argName : Name) (arg : Arg) : M Unit := do
  let s ← get
  let expectedType := (← getArgExpectedType).consumeTypeAnnotations
  match arg with
  | Arg.expr val =>
    let arg ← ensureArgType s.f val expectedType
    addNewArg argName arg
  | Arg.stx stx  =>
    let val ← elabTerm stx expectedType
    let arg ← withRef stx <| ensureArgType s.f val expectedType
    addNewArg argName arg

/-- Return true if `fType` contains `OptParam` or `AutoParams` -/
private def fTypeHasOptAutoParams : M Bool := do
  hasOptAutoParams (← get).fType

/--
   Auxiliary function for retrieving the resulting type of a function application.
   See `propagateExpectedType`.
   Remark: `(explicit : Bool) == true` when `@` modifier is used. -/
private partial def getForallBody (explicit : Bool) : Nat → List NamedArg → Expr → Option Expr
  | i, namedArgs, type@(.forallE n d b bi) =>
    match findBinderName? namedArgs n with
    | some _ => getForallBody explicit i (Term.eraseNamedArg namedArgs n) b
    | none =>
      if !explicit && !bi.isExplicit then
        getForallBody explicit i namedArgs b
      else if i > 0 then
        getForallBody explicit (i-1) namedArgs b
      else if d.isAutoParam || d.isOptParam then
        getForallBody explicit i namedArgs b
      else
        some type
  | 0, [], type => some type
  | _, _,  _    => none

private def shouldPropagateExpectedTypeFor (nextArg : Arg) : Bool :=
  match nextArg with
  | .expr _  => false -- it has already been elaborated
  | .stx stx =>
    -- TODO: make this configurable?
    stx.getKind != ``Lean.Parser.Term.hole &&
    stx.getKind != ``Lean.Parser.Term.syntheticHole &&
    stx.getKind != ``Lean.Parser.Term.byTactic

/--
  Auxiliary method for propagating the expected type. We call it as soon as we find the first explicit
  argument. The goal is to propagate the expected type in applications of functions such as
  ```lean
  Add.add {α : Type u} : α → α → α
  List.cons {α : Type u} : α → List α → List α
  ```
  This is particularly useful when there applicable coercions. For example,
  assume we have a coercion from `Nat` to `Int`, and we have
  `(x : Nat)` and the expected type is `List Int`. Then, if we don't use this function,
  the elaborator will fail to elaborate
  ```
  List.cons x []
  ```
  First, the elaborator creates a new metavariable `?α` for the implicit argument `{α : Type u}`.
  Then, when it processes `x`, it assigns `?α := Nat`, and then obtains the
  resultant type `List Nat` which is **not** definitionally equal to `List Int`.
  We solve the problem by executing this method before we elaborate the first explicit argument (`x` in this example).
  This method infers that the resultant type is `List ?α` and unifies it with `List Int`.
  Then, when we elaborate `x`, the elaborate realizes the coercion from `Nat` to `Int` must be used, and the
  term
  ```
  @List.cons Int (coe x) (@List.nil Int)
  ```
  is produced.

  The method will do nothing if
  1- The resultant type depends on the remaining arguments (i.e., `!eTypeBody.hasLooseBVars`).
  2- The resultant type contains optional/auto params.

  We have considered adding the following extra conditions
    a) The resultant type does not contain any type metavariable.
    b) The resultant type contains a nontype metavariable.

  These two conditions would restrict the method to simple functions that are "morally" in
  the Hindley&Milner fragment.
  If users need to disable expected type propagation, we can add an attribute `[elab_without_expected_type]`.
-/
private def propagateExpectedType (arg : Arg) : M Unit := do
  if shouldPropagateExpectedTypeFor arg then
    let s ← get
    -- TODO: handle s.etaArgs.size > 0
    unless !s.etaArgs.isEmpty || !s.propagateExpected do
      match s.expectedType? with
      | none              => pure ()
      | some expectedType =>
        /- We don't propagate `Prop` because we often use `Prop` as a more general "Bool" (e.g., `if-then-else`).
           If we propagate `expectedType == Prop` in the following examples, the elaborator would fail
           ```
           def f1 (s : Nat × Bool) : Bool := if s.2 then false else true

           def f2 (s : List Bool) : Bool := if s.head! then false else true

           def f3 (s : List Bool) : Bool := if List.head! (s.map not) then false else true
           ```
           They would all fail for the same reason. So, let's focus on the first one.
           We would elaborate `s.2` with `expectedType == Prop`.
           Before we elaborate `s`, this method would be invoked, and `s.fType` is `?α × ?β → ?β` and after
           propagation we would have `?α × Prop → Prop`. Then, when we would try to elaborate `s`, and
           get a type error because `?α × Prop` cannot be unified with `Nat × Bool`.
           Most users would have a hard time trying to understand why these examples failed.

           Here is a possible alternative workaround. We give up the idea of using `Prop` at `if-then-else`.
           Drawback: users use `if-then-else` with conditions that are not Decidable.
           So, users would have to embrace `propDecidable` and `choice`.
           This may not be that bad since the developers and users don't seem to care about constructivism.

           We currently use a different workaround, we just don't propagate the expected type when it is `Prop`. -/
        if expectedType.isProp then
          modify fun s => { s with propagateExpected := false }
        else
          let numRemainingArgs := s.args.length
          trace[Elab.app.propagateExpectedType] "etaArgs.size: {s.etaArgs.size}, numRemainingArgs: {numRemainingArgs}, fType: {s.fType}"
          match getForallBody (← read).explicit numRemainingArgs s.namedArgs s.fType with
          | none           => pure ()
          | some fTypeBody =>
            unless fTypeBody.hasLooseBVars do
              unless (← hasOptAutoParams fTypeBody) do
                trySynthesizeAppInstMVars
                trace[Elab.app.propagateExpectedType] "{expectedType} =?= {fTypeBody}"
                if (← isDefEq expectedType fTypeBody) then
                  /- Note that we only set `propagateExpected := false` when propagation has succeeded. -/
                  modify fun s => { s with propagateExpected := false }

/-- This method executes after all application arguments have been processed. -/
private def finalize : M Expr := do
  let s ← get
  let mut e := s.f
  -- all user explicit arguments have been consumed
  trace[Elab.app.finalize] e
  let ref ← getRef
  -- Register the error context of implicits
  for mvarId in s.toSetErrorCtx do
    registerMVarErrorImplicitArgInfo mvarId ref e
  if !s.etaArgs.isEmpty then
    e ← mkLambdaFVars s.etaArgs e
  /-
    Remark: we should not use `s.fType` as `eType` even when
    `s.etaArgs.isEmpty`. Reason: it may have been unfolded.
  -/
  let eType ← inferType e
  trace[Elab.app.finalize] "after etaArgs, {e} : {eType}"
  /- Recall that `resultTypeOutParam? = some mvarId` if the function result type is the output parameter
     of a local instance. The value of this parameter may be inferable using other arguments. For example,
     suppose we have
     ```lean
     def add_one {X} [Trait X] [One (Trait.R X)] [HAdd X (Trait.R X) X] (x : X) : X := x + (One.one : (Trait.R X))
     ```
     from test `948.lean`. There are multiple ways to infer `X`, and we don't want to mark it as `syntheticOpaque`.
  -/
  if let some outParamMVarId := s.resultTypeOutParam? then
    synthesizeAppInstMVars
    /- If `eType != mkMVar outParamMVarId`, then the
       function is partially applied, and we do not apply default instances. -/
    if !(← outParamMVarId.isAssigned) && eType.isMVar && eType.mvarId! == outParamMVarId then
      synthesizeSyntheticMVarsUsingDefault
      return e
    else
      return e
  if let some expectedType := s.expectedType? then
    trySynthesizeAppInstMVars
    -- Try to propagate expected type. Ignore if types are not definitionally equal, caller must handle it.
    trace[Elab.app.finalize] "expected type: {expectedType}"
    discard <| isDefEq expectedType eType
  synthesizeAppInstMVars
  return e

/--
Returns a named argument that depends on the next argument, otherwise `none`.
-/
private def findNamedArgDependsOnCurrent? : M (Option NamedArg) := do
  let s ← get
  if s.namedArgs.isEmpty then
    return none
  else
    forallTelescopeReducing s.fType fun xs _ => do
      let curr := xs[0]!
      for h : i in [1:xs.size] do
        let xDecl ← xs[i].fvarId!.getDecl
        if let some arg := s.namedArgs.find? fun arg => arg.name == xDecl.userName then
          /- Remark: a default value at `optParam` does not count as a dependency -/
          if (← exprDependsOn xDecl.type.cleanupAnnotations curr.fvarId!) then
            return arg
      return none


/-- Return `true` if there are regular or named arguments to be processed. -/
private def hasArgsToProcess : M Bool := do
  let s ← get
  return !s.args.isEmpty || !s.namedArgs.isEmpty

/--
Returns the argument syntax if the next argument at `args` is of the form `_`.
-/
private def nextArgHole? : M (Option Syntax) := do
  match (← get).args with
  | Arg.stx stx@(Syntax.node _ ``Lean.Parser.Term.hole _) :: _ => pure stx
  | _ => pure none

/--
  Return `true` if the next argument to be processed is the outparam of a local instance, and it the result type
  of the function.

  For example, suppose we have the class
  ```lean
  class Get (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
    get (xs : Cont) (i : Idx) : Elem
  ```
  And the current value of `fType` is
  ```
  {Cont : Type u_1} → {Idx : Type u_2} → {Elem : Type u_3} → [self : Get Cont Idx Elem] → Cont → Idx → Elem
  ```
  then the result returned by this method is `false` since `Cont` is not the output param of any local instance.
  Now assume `fType` is
  ```
  {Elem : Type u_3} → [self : Get Cont Idx Elem] → Cont → Idx → Elem
  ```
  then, the method returns `true` because `Elem` is an output parameter for the local instance `[self : Get Cont Idx Elem]`.

  Remark: if `resultIsOutParamSupport` is `false`, this method returns `false`.
-/
private partial def isNextOutParamOfLocalInstanceAndResult : M Bool := do
  if !(← read).resultIsOutParamSupport then
    return false
  let type := (← get).fType.bindingBody!
  unless isResultType type 0 do
    return false
  if (← hasLocalInstaceWithOutParams type) then
    let x := mkFVar (← mkFreshFVarId)
    isOutParamOfLocalInstance x (type.instantiate1 x)
  else
    return false
where
  isResultType (type : Expr) (i : Nat) : Bool :=
    match type with
    | .forallE _ _ b _ => isResultType b (i + 1)
    | .bvar idx        => idx == i
    | _                => false

  /-- (quick filter) Return true if `type` contains a binder `[C ...]` where `C` is a class containing outparams. -/
  hasLocalInstaceWithOutParams (type : Expr) : CoreM Bool := do
    let .forallE _ d b bi := type | return false
    if bi.isInstImplicit then
      if let .const declName .. := d.getAppFn then
        if hasOutParams (← getEnv) declName then
          return true
    hasLocalInstaceWithOutParams b

  isOutParamOfLocalInstance (x : Expr) (type : Expr) : MetaM Bool := do
    let .forallE _ d b bi := type | return false
    if bi.isInstImplicit then
      if let .const declName .. := d.getAppFn then
        if hasOutParams (← getEnv) declName then
          let cType ← inferType d.getAppFn
          if (← isOutParamOf x 0 d.getAppArgs cType) then
            return true
    isOutParamOfLocalInstance x b

  isOutParamOf (x : Expr) (i : Nat) (args : Array Expr) (cType : Expr) : MetaM Bool := do
    if h : i < args.size then
      match (← whnf cType) with
      | .forallE _ d b _ =>
        if args[i] == x && d.isOutParam then
          return true
        isOutParamOf x (i+1) args b
      | _ => return false
    else
      return false

mutual
  /--
  Create a fresh local variable with the current binder name and argument type, add it to `etaArgs` and `f`,
  and then execute the main loop.
  -/
  private partial def addEtaArg (argName : Name) : M Expr := do
    let n    ← getBindingName
    let type ← getArgExpectedType
    withLocalDeclD n type fun x => do
      modify fun s => { s with etaArgs := s.etaArgs.push x }
      addNewArg argName x
      main

  /--
  Create a fresh metavariable for the implicit argument, add it to `f`, and then execute the main loop.
  -/
  private partial def addImplicitArg (argName : Name) : M Expr := do
    let argType ← getArgExpectedType
    let arg ← if (← isNextOutParamOfLocalInstanceAndResult) then
      let arg ← mkFreshExprMVar argType
      /- When the result type is an output parameter, we don't want to propagate the expected type.
         So, we just mark `propagateExpected := false` to disable it.
         At `finalize`, we check whether `arg` is still unassigned, if it is, we apply default instances,
         and try to synthesize pending mvars. -/
      modify fun s => { s with resultTypeOutParam? := some arg.mvarId!, propagateExpected := false }
      pure arg
    else
      mkFreshExprMVar argType
    modify fun s => { s with toSetErrorCtx := s.toSetErrorCtx.push arg.mvarId! }
    addNewArg argName arg
    main

  /--
  Process a `fType` of the form `(x : A) → B x`.
  This method assume `fType` is a function type.
  -/
  private partial def processExplicitArg (argName : Name) : M Expr := do
    match (← get).args with
    | arg::args =>
      -- Note: currently the following test never succeeds in explicit mode since `@x.f` notation does not exist.
      if let some true := NamedArg.suppressDeps <$> (← findNamedArgDependsOnCurrent?) then
        /-
        We treat the explicit argument `argName` as implicit
        if we have a named arguments that depends on it whose `suppressDeps` flag set to `true`.
        The motivation for this is class projections (issue #1851).
        In some cases, class projections can have explicit parameters. For example, in
        ```
        class Approx {α : Type} (a : α) (X : Type) : Type where
          val : X
        ```
        the type of `Approx.val` is `{α : Type} → (a : α) → {X : Type} → [self : Approx a X] → X`.
        Note that the parameter `a` is explicit since there is no way to infer it from the expected
        type or from the types of other explicit parameters.
        Being a parameter of the class, `a` is determined by the type of `self`.

        Consider
        ```
        variable {α β X Y : Type} {f' : α → β} {x' : α} [f : Approx f' (X → Y)]
        ```
        Recall that `f.val` is, to first approximation, sugar for `Approx.val (self := f)`.
        Without further refinement, this would expand to `fun f'' : α → β => Approx.val f'' f`,
        which is a type error, since `f''` must be defeq to `f'`.
        Furthermore, with projection notation, users expect all structure parameters
        to be uniformly implicit; after all, they are determined by `self`.
        To handle this, the `(self := f)` named argument is annotated with the `suppressDeps` flag.
        This causes the `a` parameter to become implicit, and `f.val` instead expands to `Approx.val f' f`.

        This feature previously was enabled for *all* explicit arguments, which confused users
        and was frequently reported as a bug (issue #1867).
        Now it is only enabled for the `self` argument in structure projections.

        We used to do this only when `(← get).args` was empty,
        but it created an asymmetry because `f.val` worked as expected,
        yet one would have to write `f.val _ x` when there are further arguments.
        -/
        return (← addImplicitArg argName)
      propagateExpectedType arg
      modify fun s => { s with args }
      elabAndAddNewArg argName arg
      main
    | _ =>
      if (← read).ellipsis && (← readThe Term.Context).inPattern then
        /-
        In patterns, ellipsis should always be an implicit argument, even if it is an optparam or autoparam.
        This prevents examples such as the one in #4555 from failing:
        ```lean
        match e with
        | .internal .. => sorry
        | .error .. => sorry
        ```
        The `internal` has an optparam (`| internal (id : InternalExceptionId) (extra : KVMap := {})`).

        We may consider having ellipsis suppress optparams and autoparams in general.
        We avoid doing so for now since it's possible to opt-out of them (for example with `.internal (extra := _) ..`)
        but it's not possible to opt-in.
        -/
        return ← addImplicitArg argName
      let argType ← getArgExpectedType
      match (← read).explicit, argType.getOptParamDefault?, argType.getAutoParamTactic? with
      | false, some defVal, _  => addNewArg argName defVal; main
      | false, _, some (.const tacticDecl _) =>
        let env ← getEnv
        let opts ← getOptions
        match evalSyntaxConstant env opts tacticDecl with
        | Except.error err       => throwError err
        | Except.ok tacticSyntax =>
          let tacticBlock ← `(by $(⟨tacticSyntax⟩))
          /-
          We insert position information from the current ref into `stx` everywhere, simulating this being
          a tactic script inserted by the user, which ensures error messages and logging will always be attributed
          to this application rather than sometimes being placed at position (1,0) in the file.
          Placing position information on `by` syntax alone is not sufficient since incrementality
          (in particular, `Lean.Elab.Term.withReuseContext`) controls the ref to avoid leakage of outside data.
          Note that `tacticSyntax` contains no position information itself, since it is erased by `Lean.Elab.Term.quoteAutoTactic`.
          -/
          let info := (← getRef).getHeadInfo
          let tacticBlock := tacticBlock.raw.rewriteBottomUp (·.setInfo info)
          let mvar ← mkTacticMVar argType.consumeTypeAnnotations tacticBlock (.autoParam argName)
          -- Note(kmill): We are adding terminfo to simulate a previous implementation that elaborated `tacticBlock`.
          -- We should look into removing this since terminfo for synthetic syntax is suspect,
          -- but we noted it was necessary to preserve the behavior of the unused variable linter.
          addTermInfo' tacticBlock mvar
          let argNew := Arg.expr mvar
          propagateExpectedType argNew
          elabAndAddNewArg argName argNew
          main
      | false, _, some _ =>
        throwError "invalid autoParam, argument must be a constant"
      | _, _, _ =>
        if (← read).ellipsis then
          addImplicitArg argName
        else if !(← get).namedArgs.isEmpty then
          if let some _ ← findNamedArgDependsOnCurrent? then
            /-
            Dependencies of named arguments cannot be turned into eta arguments
            since they are determined by the named arguments.
            Instead we can turn them into implicit arguments.
            -/
            addImplicitArg argName
          else
            addEtaArg argName
        else if !(← read).explicit then
          if (← fTypeHasOptAutoParams) then
            addEtaArg argName
          else
            finalize
        else
          finalize

  /--
    Process a `fType` of the form `{x : A} → B x`.
    This method assume `fType` is a function type -/
  private partial def processImplicitArg (argName : Name) : M Expr := do
    if (← read).explicit then
      processExplicitArg argName
    else
      addImplicitArg argName

  /--
    Process a `fType` of the form `{{x : A}} → B x`.
    This method assume `fType` is a function type -/
  private partial def processStrictImplicitArg (argName : Name) : M Expr := do
    if (← read).explicit then
      processExplicitArg argName
    else if (← hasArgsToProcess) then
      addImplicitArg argName
    else
      finalize

  /--
  Process a `fType` of the form `[x : A] → B x`.
  This method assume `fType` is a function type.
  -/
  private partial def processInstImplicitArg (argName : Name) : M Expr := do
    if (← read).explicit then
      if let some stx ← nextArgHole? then
        -- We still use typeclass resolution for `_` arguments.
        -- This behavior can be suppressed with `(_)`.
        let ty ← getArgExpectedType
        let arg ← mkInstMVar ty
        addTermInfo' stx arg ty
        modify fun s => { s with args := s.args.tail! }
        main
      else
        processExplicitArg argName
    else
      discard <| mkInstMVar (← getArgExpectedType)
      main
  where
    mkInstMVar (ty : Expr) : M Expr := do
      let arg ← mkFreshExprMVar ty MetavarKind.synthetic
      addInstMVar arg.mvarId!
      addNewArg argName arg
      return arg

  /-- Elaborate function application arguments. -/
  partial def main : M Expr := do
    let fType ← normalizeFunType
    if fType.isForall then
      let binderName := fType.bindingName!
      let binfo := fType.bindingInfo!
      let s ← get
      match findBinderName? s.namedArgs binderName with
      | some namedArg =>
        propagateExpectedType namedArg.val
        eraseNamedArg binderName
        elabAndAddNewArg binderName namedArg.val
        main
      | none          =>
        match binfo with
        | .implicit       => processImplicitArg binderName
        | .instImplicit   => processInstImplicitArg binderName
        | .strictImplicit => processStrictImplicitArg binderName
        | _               => processExplicitArg binderName
    else if (← hasArgsToProcess) then
      synthesizePendingAndNormalizeFunType
      main
    else
      finalize

end

end ElabAppArgs


/-! # Eliminator-like function application elaborator -/

/--
Information about an eliminator used by the elab-as-elim elaborator.
This is not to be confused with `Lean.Meta.ElimInfo`, which is for `induction` and `cases`.
The elab-as-elim routine is less restrictive in what counts as an eliminator, and it doesn't need
to have a strict notion of what is a "target" — all it cares about are
1. that the return type of a function is of the form `m ...` where `m` is a parameter
   (unlike `induction` and `cases` eliminators, the arguments to `m`, known as "discriminants",
   can be any expressions, not just parameters), and
2. which arguments should be eagerly elaborated, to make discriminants be as elaborated as
   possible for the expected type generalization procedure,
   and which should be postponed (since they are the "minor premises").

Note that the routine isn't doing induction/cases *on* particular expressions.
The purpose of elab-as-elim is to successfully solve the higher-order unification problem
between the return type of the function and the expected type.
-/
structure ElabElimInfo where
  /-- The eliminator. -/
  elimExpr   : Expr
  /-- The type of the eliminator. -/
  elimType   : Expr
  /-- The position of the motive parameter. -/
  motivePos  : Nat
  /--
  Positions of "major" parameters (those that should be eagerly elaborated
  because they can contribute to the motive inference procedure).
  All parameters that are neither the motive nor a major parameter are "minor" parameters.
  The major parameters include all of the parameters that transitively appear in the motive's arguments,
  as well as "first-order" arguments that include such parameters,
  since they too can help with elaborating discriminants.

  For example, in the following theorem the argument `h : a = b`
  should be elaborated eagerly because it contains `b`, which occurs in `motive b`.
  ```
  theorem Eq.subst' {α} {motive : α → Prop} {a b : α} (h : a = b) : motive a → motive b
  ```
  For another example, the term `isEmptyElim (α := α)` is an underapplied eliminator, and it needs
  argument `α` to be elaborated eagerly to create a type-correct motive.
  ```
  def isEmptyElim [IsEmpty α] {p : α → Sort _} (a : α) : p a := ...
  example {α : Type _} [IsEmpty α] : id (α → False) := isEmptyElim (α := α)
  ```
  -/
  majorsPos : Array Nat := #[]
  deriving Repr, Inhabited

def getElabElimExprInfo (elimExpr : Expr) : MetaM ElabElimInfo := do
  let elimType ← inferType elimExpr
  trace[Elab.app.elab_as_elim] "eliminator {indentExpr elimExpr}\nhas type{indentExpr elimType}"
  forallTelescopeReducing elimType fun xs type => do
    let motive  := type.getAppFn
    let motiveArgs := type.getAppArgs
    unless motive.isFVar && motiveArgs.size > 0 do
      throwError "unexpected eliminator resulting type{indentExpr type}"
    let motiveType ← inferType motive
    forallTelescopeReducing motiveType fun motiveParams motiveResultType => do
      unless motiveParams.size == motiveArgs.size do
        throwError "unexpected number of arguments at motive type{indentExpr motiveType}"
      unless motiveResultType.isSort do
        throwError "motive result type must be a sort{indentExpr motiveType}"
    let some motivePos ← pure (xs.indexOf? motive) |
      throwError "unexpected eliminator type{indentExpr elimType}"
    /-
    Compute transitive closure of fvars appearing in arguments to the motive.
    These are the primary set of major parameters.
    -/
    let initMotiveFVars : CollectFVars.State := motiveArgs.foldl (init := {}) collectFVars
    let motiveFVars ← xs.size.foldRevM (init := initMotiveFVars) fun i s => do
      let x := xs[i]!
      if s.fvarSet.contains x.fvarId! then
        return collectFVars s (← inferType x)
      else
        return s
    /- Collect the major parameter positions -/
    let mut majorsPos := #[]
    for h : i in [:xs.size] do
      let x := xs[i]
      unless motivePos == i do
        let xType ← x.fvarId!.getType
        /-
        We also consider "first-order" types because we can reliably "extract" information from them.
        We say a term is "first-order" if all applications are of the form `f ...` where `f` is a constant.
        -/
        let isFirstOrder (e : Expr) : Bool := Option.isNone <| e.find? fun e => e.isApp && !e.getAppFn.isConst
        if motiveFVars.fvarSet.contains x.fvarId!
            || (isFirstOrder xType
                && Option.isSome (xType.find? fun e => e.isFVar && motiveFVars.fvarSet.contains e.fvarId!)) then
          majorsPos := majorsPos.push i
    trace[Elab.app.elab_as_elim] "motivePos: {motivePos}"
    trace[Elab.app.elab_as_elim] "majorsPos: {majorsPos}"
    return { elimExpr, elimType,  motivePos, majorsPos }

def getElabElimInfo (elimName : Name) : MetaM ElabElimInfo := do
  getElabElimExprInfo (← mkConstWithFreshMVarLevels elimName)

builtin_initialize elabAsElim : TagAttribute ←
  registerTagAttribute `elab_as_elim
    "instructs elaborator that the arguments of the function application should be elaborated as were an eliminator"
    /-
    We apply `elab_as_elim` after compilation because this kind of attribute is not applied to auxiliary declarations
    created by the `WF` and `Structural` modules. This is an "indirect" fix for issue #1900. We should consider
    having an explicit flag in attributes to indicate whether they should be copied to auxiliary declarations or not.
    -/
    (applicationTime := .afterCompilation)
    fun declName => do
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        if (← hasOptAutoParams info.type) then
          throwError "[elab_as_elim] attribute cannot be used in declarations containing optional and auto parameters"
        discard <| getElabElimInfo declName
      go.run' {} {}

namespace ElabElim

/-- Context of the `elab_as_elim` elaboration procedure. -/
structure Context where
  elimInfo : ElabElimInfo
  expectedType : Expr

/-- State of the `elab_as_elim` elaboration procedure. -/
structure State where
  /-- The resultant expression being built. -/
  f            : Expr
  /-- `f : fType -/
  fType        : Expr
  /-- User-provided named arguments that still have to be processed. -/
  namedArgs    : List NamedArg
  /-- User-provided arguments that still have to be processed. -/
  args         : List Arg
  /-- Instance implicit arguments collected so far. -/
  instMVars    : Array MVarId := #[]
  /-- Position of the next argument to be processed. We use it to decide whether the argument is the motive or a discriminant. -/
  idx          : Nat := 0
  /-- Store the metavariable used to represent the motive that will be computed at `finalize`. -/
  motive?      : Option Expr := none

abbrev M := ReaderT Context $ StateRefT State TermElabM

/-- Infer the `motive` using the expected type by `kabstract`ing the discriminants. -/
def mkMotive (discrs : Array Expr) (expectedType : Expr) : MetaM Expr := do
  discrs.foldrM (init := expectedType) fun discr motive => do
    let discr ← instantiateMVars discr
    let motiveBody ← kabstract motive discr
    /- We use `transform (usedLetOnly := true)` to eliminate unnecessary let-expressions. -/
    let discrType ← transform (usedLetOnly := true) (← instantiateMVars (← inferType discr))
    return Lean.mkLambda (← mkFreshBinderName) BinderInfo.default discrType motiveBody

/--
If the eliminator is over-applied, we "revert" the extra arguments.
Returns the function with the reverted arguments applied and the new generalized expected type.
-/
def revertArgs (args : List Arg) (f : Expr) (expectedType : Expr) : TermElabM (Expr × Expr) := do
  let (xs, expectedType) ← args.foldrM (init := ([], expectedType)) fun arg (xs, expectedType) => do
    let val ←
      match arg with
      | .expr val => pure val
      | .stx stx => elabTerm stx none
    let val ← instantiateMVars val
    let expectedTypeBody ← kabstract expectedType val
    /- We use `transform (usedLetOnly := true)` to eliminate unnecessary let-expressions. -/
    let valType ← transform (usedLetOnly := true) (← instantiateMVars (← inferType val))
    return (val :: xs, mkForall (← mkFreshBinderName) BinderInfo.default valType expectedTypeBody)
  return (xs.foldl .app f, expectedType)

/--
Construct the resulting application after all discriminants have been elaborated, and we have
consumed as many given arguments as possible.
-/
def finalize : M Expr := do
  unless (← get).namedArgs.isEmpty do
    throwError "failed to elaborate eliminator, unused named arguments: {(← get).namedArgs.map (·.name)}"
  let some motive := (← get).motive?
    | throwError "failed to elaborate eliminator, insufficient number of arguments"
  trace[Elab.app.elab_as_elim] "motive: {motive}"
  forallTelescope (← get).fType fun xs fType => do
    trace[Elab.app.elab_as_elim] "xs: {xs}"
    let mut expectedType := (← read).expectedType
    trace[Elab.app.elab_as_elim] "expectedType:{indentD expectedType}"
    let throwInsufficient := do
      throwError "failed to elaborate eliminator, insufficient number of arguments, expected type:{indentExpr expectedType}"
    let mut f := (← get).f
    if xs.size > 0 then
      -- under-application, specialize the expected type using `xs`
      -- Note: if we ever wanted to support optParams and autoParams, this is where it could be.
      assert! (← get).args.isEmpty
      for x in xs do
        let .forallE _ t b _ ← whnf expectedType | throwInsufficient
        unless ← fullApproxDefEq <| isDefEq t (← inferType x) do
          -- We can't assume that these binding domains were supposed to line up, so report insufficient arguments
          throwInsufficient
        expectedType := b.instantiate1 x
      trace[Elab.app.elab_as_elim] "xs after specialization of expected type: {xs}"
    else
      -- over-application, simulate `revert` while generalizing the values of these arguments in the expected type
      (f, expectedType) ← revertArgs (← get).args f expectedType
      unless ← isTypeCorrect expectedType do
        throwError "failed to elaborate eliminator, after generalizing over-applied arguments, expected type is type incorrect:{indentExpr expectedType}"
    trace[Elab.app.elab_as_elim] "expectedType after processing:{indentD expectedType}"
    let result := mkAppN f xs
    trace[Elab.app.elab_as_elim] "result:{indentD result}"
    unless fType.getAppFn == (← get).motive? do
      throwError "Internal error, eliminator target type isn't an application of the motive"
    let discrs := fType.getAppArgs
    trace[Elab.app.elab_as_elim] "discrs: {discrs}"
    let motiveVal ← mkMotive discrs expectedType
    unless (← isTypeCorrect motiveVal) do
      throwError "failed to elaborate eliminator, motive is not type correct:{indentD motiveVal}"
    unless (← isDefEq motive motiveVal) do
      throwError "failed to elaborate eliminator, invalid motive{indentExpr motiveVal}"
    synthesizeAppInstMVars (← get).instMVars result
    trace[Elab.app.elab_as_elim] "completed motive:{indentD motive}"
    let result ← mkLambdaFVars xs (← instantiateMVars result)
    return result

/--
Return the next argument to be processed.
The result is `.none` if it is an implicit argument which was not provided using a named argument.
The result is `.undef` if `args` is empty and `namedArgs` does contain an entry for `binderName`.
-/
def getNextArg? (binderName : Name) (binderInfo : BinderInfo) : M (LOption Arg) := do
  match findBinderName? (← get).namedArgs binderName with
  | some namedArg =>
    modify fun s => { s with namedArgs := eraseNamedArg s.namedArgs binderName }
    return .some namedArg.val
  | none =>
    if binderInfo.isExplicit then
      match (← get).args with
      | [] => return .undef
      | arg :: args =>
        modify fun s => { s with args }
        return .some arg
    else
      return .none

/-- Set the `motive` field in the state. -/
def setMotive (motive : Expr) : M Unit :=
  modify fun s => { s with motive? := motive }

/-- Elaborate the given argument with the given expected type. -/
private def elabArg (arg : Arg) (argExpectedType : Expr) : M Expr := do
  match arg with
  | Arg.expr val => ensureArgType (← get).f val argExpectedType
  | Arg.stx stx  =>
    let val ← elabTerm stx argExpectedType
    withRef stx <| ensureArgType (← get).f val argExpectedType

/-- Save information for producing error messages. -/
def saveArgInfo (arg : Expr) (binderName : Name) : M Unit := do
  if arg.isMVar then
    registerMVarArgName arg.mvarId! binderName

/-- Create an implicit argument using the given `BinderInfo`. -/
def mkImplicitArg (argExpectedType : Expr) (bi : BinderInfo) : M Expr := do
  let arg ← mkFreshExprMVar argExpectedType (if bi.isInstImplicit then .synthetic else .natural)
  if bi.isInstImplicit then
    modify fun s => { s with instMVars := s.instMVars.push arg.mvarId! }
  return arg

/-- Main loop of the `elimAsElab` procedure. -/
partial def main : M Expr := do
  let .forallE binderName binderType body binderInfo ← whnfForall (← get).fType |
    finalize
  let addArgAndContinue (arg : Expr) : M Expr := do
    modify fun s => { s with idx := s.idx + 1, f := mkApp s.f arg, fType := body.instantiate1 arg }
    saveArgInfo arg binderName
    main
  let idx := (← get).idx
  if (← read).elimInfo.motivePos == idx then
    let motive ←
      match (← getNextArg? binderName binderInfo) with
      | .some arg =>
        /- Due to `Lean.Elab.Term.elabAppArgs.elabAsElim?`, this must be a positional argument that is the syntax `_`. -/
        elabArg arg binderType
      | .none | .undef =>
        /- Note: undef occurs when the motive is explicit but missing.
           In this case, we treat it as if it were an implicit argument
           to support writing `h.rec` when `h : False`, rather than requiring `h.rec _`. -/
        mkImplicitArg binderType binderInfo
    setMotive motive
    addArgAndContinue motive
  else if (← read).elimInfo.majorsPos.contains idx then
    match (← getNextArg? binderName binderInfo) with
    | .some arg => let discr ← elabArg arg binderType; addArgAndContinue discr
    | .undef => finalize
    | .none => let discr ← mkImplicitArg binderType binderInfo; addArgAndContinue discr
  else match (← getNextArg? binderName binderInfo) with
    | .some (.stx stx) => addArgAndContinue (← postponeElabTerm stx binderType)
    | .some (.expr val) => addArgAndContinue (← ensureArgType (← get).f val binderType)
    | .undef => finalize
    | .none => addArgAndContinue (← mkImplicitArg binderType binderInfo)

end ElabElim

/-- Return `true` if `declName` is a candidate for `ElabElim.main` elaboration. -/
private def shouldElabAsElim (declName : Name) : CoreM Bool := do
  if (← isRec declName) then return true
  let env ← getEnv
  if isCasesOnRecursor env declName then return true
  if isBRecOnRecursor env declName then return true
  if isRecOnRecursor env declName then return true
  return elabAsElim.hasTag env declName

private def propagateExpectedTypeFor (f : Expr) : TermElabM Bool :=
  match f.getAppFn.constName? with
  | some declName => return !hasElabWithoutExpectedType (← getEnv) declName
  | _ => return true

/-! # Function application elaboration -/

/--
Elaborate a `f`-application using `namedArgs` and `args` as the arguments.
- `expectedType?` the expected type if available. It is used to propagate typing information only. This method does **not** ensure the result has this type.
- `explicit = true` when notation `@` is used, and implicit arguments are assumed to be provided at `namedArgs` and `args`.
- `ellipsis = true` when notation `..` is used. That is, we add `_` for missing arguments.
- `resultIsOutParamSupport` is used to control whether special support is used when processing applications of functions that return
   output parameter of some local instance. Example:
   ```
   GetElem.getElem : {Cont : Type u_1} → {Idx : Type u_2} → {elem : Type u_3} → {dom : cont → idx → Prop} → [self : GetElem cont idx elem dom] → (xs : cont) → (i : idx) → dom xs i → elem
   ```
   The result type `elem` is the output parameter of the local instance `self`.
   When this parameter is set to `true`, we execute `synthesizeSyntheticMVarsUsingDefault`. For additional details, see comment at
   `ElabAppArgs.resultIsOutParam`.
-/
def elabAppArgs (f : Expr) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit ellipsis : Bool) (resultIsOutParamSupport := true) : TermElabM Expr := do
  -- Coercions must be available to use this flag.
  -- If `@` is used (i.e., `explicit = true`), we disable `resultIsOutParamSupport`.
  let resultIsOutParamSupport := ((← getEnv).contains ``Lean.Internal.coeM) && resultIsOutParamSupport && !explicit
  let fType ← inferType f
  let fType ← instantiateMVars fType
  unless namedArgs.isEmpty && args.isEmpty do
    tryPostponeIfMVar fType
  trace[Elab.app.args] "explicit: {explicit}, ellipsis: {ellipsis}, {f} : {fType}"
  trace[Elab.app.args] "namedArgs: {namedArgs}"
  trace[Elab.app.args] "args: {args}"
  if let some elimInfo ← elabAsElim? then
    tryPostponeIfNoneOrMVar expectedType?
    let some expectedType := expectedType? | throwError "failed to elaborate eliminator, expected type is not available"
    let expectedType ← instantiateMVars expectedType
    if expectedType.getAppFn.isMVar then throwError "failed to elaborate eliminator, expected type is not available"
    ElabElim.main.run { elimInfo, expectedType } |>.run' {
      f, fType
      args := args.toList
      namedArgs := namedArgs.toList
    }
  else
    ElabAppArgs.main.run { explicit, ellipsis, resultIsOutParamSupport } |>.run' {
      args := args.toList
      expectedType?, f, fType
      namedArgs := namedArgs.toList
      propagateExpected := (← propagateExpectedTypeFor f)
    }
where
  /-- Return `some info` if we should elaborate as an eliminator. -/
  elabAsElim? : TermElabM (Option ElabElimInfo) := do
    unless (← read).heedElabAsElim do return none
    if explicit || ellipsis then return none
    let .const declName _ := f | return none
    unless (← shouldElabAsElim declName) do return none
    let elimInfo ← getElabElimInfo declName
    forallTelescopeReducing (← inferType f) fun xs _ => do
      /- Process arguments similar to `Lean.Elab.Term.ElabElim.main` to see if the motive has been
         provided, in which case we use the standard app elaborator.
         If the motive is explicit (like for `False.rec`), then a positional `_` counts as "not provided". -/
      let mut args := args.toList
      let mut namedArgs := namedArgs.toList
      for x in xs[0:elimInfo.motivePos] do
        let localDecl ← x.fvarId!.getDecl
        match findBinderName? namedArgs localDecl.userName with
        | some _ => namedArgs := eraseNamedArg namedArgs localDecl.userName
        | none   => if localDecl.binderInfo.isExplicit then args := args.tailD []
      -- Invariant: `elimInfo.motivePos < xs.size` due to construction of `elimInfo`.
      let some x := xs[elimInfo.motivePos]? | unreachable!
      let localDecl ← x.fvarId!.getDecl
      if findBinderName? namedArgs localDecl.userName matches some _ then
        -- motive has been explicitly provided, so we should use standard app elaborator
        return none
      else
        match localDecl.binderInfo.isExplicit, args with
        | true, .expr _ :: _  =>
          -- motive has been explicitly provided, so we should use standard app elaborator
          return none
        | true, .stx arg :: _ =>
          if arg.isOfKind ``Lean.Parser.Term.hole then
            return some elimInfo
          else
            -- positional motive is not `_`, so we should use standard app elaborator
            return none
        | _, _ => return some elimInfo


/-- Auxiliary inductive datatype that represents the resolution of an `LVal`. -/
inductive LValResolution where
  /-- When applied to `f`, effectively expands to `BaseStruct.fieldName (self := Struct.toBase f)`.
  This is a special named argument where it suppresses any explicit arguments depending on it so that type parameters don't need to be supplied. -/
  | projFn   (baseStructName : Name) (structName : Name) (fieldName : Name)
  /-- Similar to `projFn`, but for extracting field indexed by `idx`. Works for structure-like inductive types in general. -/
  | projIdx  (structName : Name) (idx : Nat)
  /-- When applied to `f`, effectively expands to `constName ... (Struct.toBase f)`, with the argument placed in the correct
  positional argument if possible, or otherwise as a named argument. The `Struct.toBase` is not present if `baseStructName == structName`,
  in which case these do not need to be structures. Supports generalized field notation. -/
  | const    (baseStructName : Name) (structName : Name) (constName : Name)
  /-- Like `const`, but with `fvar` instead of `constName`.
  The `fullName` is the name of the recursive function, and `baseName` is the base name of the type to search for in the parameter list. -/
  | localRec (baseName : Name) (fullName : Name) (fvar : Expr)

private def throwLValError (e : Expr) (eType : Expr) (msg : MessageData) : TermElabM α :=
  throwError "{msg}{indentExpr e}\nhas type{indentExpr eType}"

/--
`findMethod? S fName` tries the following for each namespace `S'` in the resolution order for `S`:
- If `env` contains `S' ++ fName`, returns `(S', S' ++ fName)`
- Otherwise if `env` contains private name `prv` for `S' ++ fName`, returns `(S', prv)`
-/
private partial def findMethod? (structName fieldName : Name) : MetaM (Option (Name × Name)) := do
  let env ← getEnv
  let find? structName' : MetaM (Option (Name × Name)) := do
    let fullName := structName' ++ fieldName
    if env.contains fullName then
      return some (structName', fullName)
    let fullNamePrv := mkPrivateName env fullName
    if env.contains fullNamePrv then
      return some (structName', fullNamePrv)
    return none
  -- Optimization: the first element of the resolution order is `structName`,
  -- so we can skip computing the resolution order in the common case
  -- of the name resolving in the `structName` namespace.
  find? structName <||> do
    let resolutionOrder ← if isStructure env structName then getStructureResolutionOrder structName else pure #[structName]
    for h : i in [1:resolutionOrder.size] do
      if let some res ← find? resolutionOrder[i] then
        return res
    return none

/--
  Return `some (structName', fullName)` if `structName ++ fieldName` is an alias for `fullName`, and
  `fullName` is of the form `structName' ++ fieldName`.

  TODO: if there is more than one applicable alias, it returns `none`. We should consider throwing an error or
  warning.
-/
private def findMethodAlias? (env : Environment) (structName fieldName : Name) : Option (Name × Name) :=
  let fullName := structName ++ fieldName
  -- We never skip `protected` aliases when resolving dot-notation.
  let aliasesCandidates := getAliases env fullName (skipProtected := false) |>.filterMap fun alias =>
    match alias.eraseSuffix? fieldName with
    | none => none
    | some structName' => some (structName', alias)
  match aliasesCandidates with
  | [r] => some r
  | _   => none

private def throwInvalidFieldNotation (e eType : Expr) : TermElabM α :=
  throwLValError e eType "invalid field notation, type is not of the form (C ...) where C is a constant"

private def resolveLValAux (e : Expr) (eType : Expr) (lval : LVal) : TermElabM LValResolution := do
  if eType.isForall then
    match lval with
    | LVal.fieldName _ fieldName _ _ =>
      let fullName := Name.str `Function fieldName
      if (← getEnv).contains fullName then
        return LValResolution.const `Function `Function fullName
    | _ => pure ()
  match eType.getAppFn.constName?, lval with
  | some structName, LVal.fieldIdx _ idx =>
    if idx == 0 then
      throwError "invalid projection, index must be greater than 0"
    let env ← getEnv
    let failK _ := throwLValError e eType "invalid projection, structure expected"
    matchConstStructure eType.getAppFn failK fun _ _ ctorVal => do
      let numFields := ctorVal.numFields
      if idx - 1 < numFields then
        if isStructure env structName then
          let fieldNames := getStructureFields env structName
          return LValResolution.projFn structName structName fieldNames[idx - 1]!
        else
          /- `structName` was declared using `inductive` command.
            So, we don't projection functions for it. Thus, we use `Expr.proj` -/
          return LValResolution.projIdx structName (idx - 1)
      else
        throwLValError e eType m!"invalid projection, structure has only {numFields} field(s)"
  | some structName, LVal.fieldName _ fieldName _ _ =>
    let env ← getEnv
    let searchEnv : Unit → TermElabM LValResolution := fun _ => do
      if let some (baseStructName, fullName) ← findMethod? structName (.mkSimple fieldName) then
        return LValResolution.const baseStructName structName fullName
      else if let some (structName', fullName) := findMethodAlias? env structName (.mkSimple fieldName) then
        return LValResolution.const structName' structName' fullName
      else
        throwLValError e eType
          m!"invalid field '{fieldName}', the environment does not contain '{Name.mkStr structName fieldName}'"
    -- search local context first, then environment
    let searchCtx : Unit → TermElabM LValResolution := fun _ => do
      let fullName := Name.mkStr structName fieldName
      for localDecl in (← getLCtx) do
        if localDecl.isAuxDecl then
          if let some localDeclFullName := (← read).auxDeclToFullName.find? localDecl.fvarId then
            if fullName == (privateToUserName? localDeclFullName).getD localDeclFullName then
              /- LVal notation is being used to make a "local" recursive call. -/
              return LValResolution.localRec structName fullName localDecl.toExpr
      searchEnv ()
    if isStructure env structName then
      match findField? env structName (Name.mkSimple fieldName) with
      | some baseStructName => return LValResolution.projFn baseStructName structName (Name.mkSimple fieldName)
      | none                => searchCtx ()
    else
      searchCtx ()
  | none, LVal.fieldName _ _ (some suffix) _ =>
    if e.isConst then
      throwUnknownConstant (e.constName! ++ suffix)
    else
      throwInvalidFieldNotation e eType
  | _, _ => throwInvalidFieldNotation e eType

/-- whnfCore + implicit consumption.
   Example: given `e` with `eType := {α : Type} → (fun β => List β) α `, it produces `(e ?m, List ?m)` where `?m` is fresh metavariable. -/
private partial def consumeImplicits (stx : Syntax) (e eType : Expr) (hasArgs : Bool) : TermElabM (Expr × Expr) := do
  let eType ← whnfCore eType
  match eType with
  | .forallE _ d b bi =>
    if bi.isImplicit || (hasArgs && bi.isStrictImplicit) then
      let mvar ← mkFreshExprMVar d
      registerMVarErrorHoleInfo mvar.mvarId! stx
      consumeImplicits stx (mkApp e mvar) (b.instantiate1 mvar) hasArgs
    else if bi.isInstImplicit then
      let mvar ← mkInstMVar d
      let r := mkApp e mvar
      registerMVarErrorImplicitArgInfo mvar.mvarId! stx r
      consumeImplicits stx r (b.instantiate1 mvar) hasArgs
    else match d.getOptParamDefault? with
      | some defVal => consumeImplicits stx (mkApp e defVal) (b.instantiate1 defVal) hasArgs
      -- TODO: we do not handle autoParams here.
      | _ => return (e, eType)
  | _ => return (e, eType)

private partial def resolveLValLoop (lval : LVal) (e eType : Expr) (previousExceptions : Array Exception) (hasArgs : Bool) : TermElabM (Expr × LValResolution) := do
  let (e, eType) ← consumeImplicits lval.getRef e eType hasArgs
  tryPostponeIfMVar eType
  /- If `eType` is still a metavariable application, we try to apply default instances to "unblock" it. -/
  if (← isMVarApp eType) then
    synthesizeSyntheticMVarsUsingDefault
  let eType ← instantiateMVars eType
  try
    let lvalRes ← resolveLValAux e eType lval
    return (e, lvalRes)
  catch
    | ex@(Exception.error _ _) =>
      let eType? ← unfoldDefinition? eType
      match eType? with
      | some eType => resolveLValLoop lval e eType (previousExceptions.push ex) hasArgs
      | none       =>
        previousExceptions.forM fun ex => logException ex
        throw ex
    | ex@(Exception.internal _ _) => throw ex

private def resolveLVal (e : Expr) (lval : LVal) (hasArgs : Bool) : TermElabM (Expr × LValResolution) := do
  let eType ← inferType e
  resolveLValLoop lval e eType #[] hasArgs

private partial def mkBaseProjections (baseStructName : Name) (structName : Name) (e : Expr) : TermElabM Expr := do
  let env ← getEnv
  match getPathToBaseStructure? env baseStructName structName with
  | none => throwError "failed to access field in parent structure"
  | some path =>
    let mut e := e
    for projFunName in path do
      let projFn ← mkConst projFunName
      e ← elabAppArgs projFn #[{ name := `self, val := Arg.expr e, suppressDeps := true }] (args := #[]) (expectedType? := none) (explicit := false) (ellipsis := false)
    return e

private def typeMatchesBaseName (type : Expr) (baseName : Name) : MetaM Bool := do
  if baseName == `Function then
    return (← whnfR type).isForall
  else if type.cleanupAnnotations.isAppOf baseName then
    return true
  else
    return (← whnfR type).isAppOf baseName

/--
Auxiliary method for field notation. Tries to add `e` as a new argument to `args` or `namedArgs`.
This method first finds the parameter with a type of the form `(baseName ...)`.
When the parameter is found, if it an explicit one and `args` is big enough, we add `e` to `args`.
Otherwise, if there isn't another parameter with the same name, we add `e` to `namedArgs`.

Remark: `fullName` is the name of the resolved "field" access function. It is used for reporting errors
-/
private partial def addLValArg (baseName : Name) (fullName : Name) (e : Expr) (args : Array Arg) (namedArgs : Array NamedArg) (f : Expr) :
    MetaM (Array Arg × Array NamedArg) := do
  withoutModifyingState <| go f (← inferType f) 0 namedArgs (namedArgs.map (·.name)) true
where
  /--
  * `argIdx` is the position into `args` for the next place an explicit argument can be inserted.
  * `remainingNamedArgs` keeps track of named arguments that haven't been visited yet,
    for handling the case where multiple parameters have the same name.
  * `unusableNamedArgs` keeps track of names that can't be used as named arguments. This is initialized with user-provided named arguments.
  * `allowNamed` is whether or not to allow using named arguments.
    Disabled after using `CoeFun` since those parameter names unlikely to be meaningful,
    and otherwise whether dot notation works or not could feel random.
  -/
  go (f fType : Expr) (argIdx : Nat) (remainingNamedArgs : Array NamedArg) (unusableNamedArgs : Array Name) (allowNamed : Bool) := withIncRecDepth do
    /- Use metavariables (rather than `forallTelescope`) to prevent `coerceToFunction?` from succeeding when multiple instances could apply -/
    let (xs, bInfos, fType') ← forallMetaTelescope fType
    let mut argIdx := argIdx
    let mut remainingNamedArgs := remainingNamedArgs
    let mut unusableNamedArgs := unusableNamedArgs
    for x in xs, bInfo in bInfos do
      let xDecl ← x.mvarId!.getDecl
      if let some idx := remainingNamedArgs.findIdx? (·.name == xDecl.userName) then
        /- If there is named argument with name `xDecl.userName`, then it is accounted for and we can't make use of it. -/
        remainingNamedArgs := remainingNamedArgs.eraseIdx idx
      else
        if (← typeMatchesBaseName xDecl.type baseName) then
          /- We found a type of the form (baseName ...).
             First, we check if the current argument is an explicit one,
             and if the current explicit position "fits" at `args` (i.e., it must be ≤ arg.size) -/
          if argIdx ≤ args.size && bInfo.isExplicit then
            /- We can insert `e` as an explicit argument -/
            return (args.insertAt! argIdx (Arg.expr e), namedArgs)
          else
            /- If we can't add `e` to `args`, we try to add it using a named argument, but this is only possible
               if there isn't an argument with the same name occurring before it. -/
            if !allowNamed || unusableNamedArgs.contains xDecl.userName then
              throwError "\
                invalid field notation, function '{fullName}' has argument with the expected type\
                {indentExpr xDecl.type}\n\
                but it cannot be used"
            else
              return (args, namedArgs.push { name := xDecl.userName, val := Arg.expr e })
        /- Advance `argIdx` and update seen named arguments. -/
        if bInfo.isExplicit then
          argIdx := argIdx + 1
        unusableNamedArgs := unusableNamedArgs.push xDecl.userName
    /- If named arguments aren't allowed, then it must still be possible to pass the value as an explicit argument.
       Otherwise, we can abort now. -/
    if allowNamed || argIdx ≤ args.size then
      if let fType'@(.forallE ..) ← whnf fType' then
        return ← go (mkAppN f xs) fType' argIdx remainingNamedArgs unusableNamedArgs allowNamed
      if let some f' ← coerceToFunction? (mkAppN f xs) then
        return ← go f' (← inferType f') argIdx remainingNamedArgs unusableNamedArgs false
    throwError "\
      invalid field notation, function '{fullName}' does not have argument with type ({baseName} ...) that can be used, \
      it must be explicit or implicit with a unique name"

/-- Adds the `TermInfo` for the field of a projection. See `Lean.Parser.Term.identProjKind`. -/
private def addProjTermInfo
    (stx            : Syntax)
    (e              : Expr)
    (expectedType?  : Option Expr := none)
    (lctx?          : Option LocalContext := none)
    (elaborator     : Name := Name.anonymous)
    (isBinder force : Bool := false)
    : TermElabM Expr :=
  addTermInfo (Syntax.node .none Parser.Term.identProjKind #[stx]) e expectedType? lctx? elaborator isBinder force

private def elabAppLValsAux (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) (explicit ellipsis : Bool)
    (f : Expr) (lvals : List LVal) : TermElabM Expr :=
  let rec loop : Expr → List LVal → TermElabM Expr
  | f, []          => elabAppArgs f namedArgs args expectedType? explicit ellipsis
  | f, lval::lvals => do
    if let LVal.fieldName (fullRef := fullRef) .. := lval then
      addDotCompletionInfo fullRef f expectedType?
    let hasArgs := !namedArgs.isEmpty || !args.isEmpty
    let (f, lvalRes) ← resolveLVal f lval hasArgs
    match lvalRes with
    | LValResolution.projIdx structName idx =>
      let f ← mkProjAndCheck structName idx f
      let f ← addTermInfo lval.getRef f
      loop f lvals
    | LValResolution.projFn baseStructName structName fieldName =>
      let f ← mkBaseProjections baseStructName structName f
      let some info := getFieldInfo? (← getEnv) baseStructName fieldName | unreachable!
      if isPrivateNameFromImportedModule (← getEnv) info.projFn then
        throwError "field '{fieldName}' from structure '{structName}' is private"
      let projFn ← mkConst info.projFn
      let projFn ← addProjTermInfo lval.getRef projFn
      if lvals.isEmpty then
        let namedArgs ← addNamedArg namedArgs { name := `self, val := Arg.expr f, suppressDeps := true }
        elabAppArgs projFn namedArgs args expectedType? explicit ellipsis
      else
        let f ← elabAppArgs projFn #[{ name := `self, val := Arg.expr f, suppressDeps := true }] #[] (expectedType? := none) (explicit := false) (ellipsis := false)
        loop f lvals
    | LValResolution.const baseStructName structName constName =>
      let f ← if baseStructName != structName then mkBaseProjections baseStructName structName f else pure f
      let projFn ← mkConst constName
      let projFn ← addProjTermInfo lval.getRef projFn
      if lvals.isEmpty then
        let (args, namedArgs) ← addLValArg baseStructName constName f args namedArgs projFn
        elabAppArgs projFn namedArgs args expectedType? explicit ellipsis
      else
        let f ← elabAppArgs projFn #[] #[Arg.expr f] (expectedType? := none) (explicit := false) (ellipsis := false)
        loop f lvals
    | LValResolution.localRec baseName fullName fvar =>
      let fvar ← addProjTermInfo lval.getRef fvar
      if lvals.isEmpty then
        let (args, namedArgs) ← addLValArg baseName fullName f args namedArgs fvar
        elabAppArgs fvar namedArgs args expectedType? explicit ellipsis
      else
        let f ← elabAppArgs fvar #[] #[Arg.expr f] (expectedType? := none) (explicit := false) (ellipsis := false)
        loop f lvals
  loop f lvals

private def elabAppLVals (f : Expr) (lvals : List LVal) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit ellipsis : Bool) : TermElabM Expr := do
  elabAppLValsAux namedArgs args expectedType? explicit ellipsis f lvals

def elabExplicitUnivs (lvls : Array Syntax) : TermElabM (List Level) := do
  lvls.foldrM (init := []) fun stx lvls => return (← elabLevel stx)::lvls

/-!
# Interaction between `errToSorry` and `observing`.

- The method `elabTerm` catches exceptions, logs them, and returns a synthetic sorry (IF `ctx.errToSorry` == true).

- When we elaborate choice nodes (and overloaded identifiers), we track multiple results using the `observing x` combinator.
  The `observing x` executes `x` and returns a `TermElabResult`.

`observing x` does not check for synthetic sorry's, just an exception. Thus, it may think `x` worked when it didn't
if a synthetic sorry was introduced. We decided that checking for synthetic sorrys at `observing` is not a good solution
because it would not be clear to decide what the "main" error message for the alternative is. When the result contains
a synthetic `sorry`, it is not clear which error message corresponds to the `sorry`. Moreover, while executing `x`, many
error messages may have been logged. Recall that we need an error per alternative at `mergeFailures`.

Thus, we decided to set `errToSorry` to `false` whenever processing choice nodes and overloaded symbols.

Important: we rely on the property that after `errToSorry` is set to
false, no elaboration function executed by `x` will reset it to
`true`.
-/

private partial def elabAppFnId (fIdent : Syntax) (fExplicitUnivs : List Level) (lvals : List LVal)
    (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) (explicit ellipsis overloaded : Bool) (acc : Array (TermElabResult Expr))
    : TermElabM (Array (TermElabResult Expr)) := do
  let funLVals ← withRef fIdent <| resolveName' fIdent fExplicitUnivs expectedType?
  let overloaded := overloaded || funLVals.length > 1
  -- Set `errToSorry` to `false` if `funLVals` > 1. See comment above about the interaction between `errToSorry` and `observing`.
  withReader (fun ctx => { ctx with errToSorry := funLVals.length == 1 && ctx.errToSorry }) do
    funLVals.foldlM (init := acc) fun acc (f, fIdent, fields) => do
      let lvals' := toLVals fields (first := true)
      let s ← observing do
        checkDeprecated fIdent f
        let f ← addTermInfo fIdent f expectedType?
        let e ← elabAppLVals f (lvals' ++ lvals) namedArgs args expectedType? explicit ellipsis
        if overloaded then ensureHasType expectedType? e else return e
      return acc.push s
where
  toName (fields : List Syntax) : Name :=
    let rec go
      | []              => .anonymous
      | field :: fields => .mkStr (go fields) field.getId.toString
    go fields.reverse

  toLVals : List Syntax → (first : Bool) → List LVal
    | [],            _     => []
    | field::fields, true  => .fieldName field field.getId.getString! (toName (field::fields)) fIdent :: toLVals fields false
    | field::fields, false => .fieldName field field.getId.getString! none fIdent :: toLVals fields false

/-- Resolve `(.$id:ident)` using the expected type to infer namespace. -/
private partial def resolveDotName (id : Syntax) (expectedType? : Option Expr) : TermElabM Name := do
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType := expectedType?
    | throwError "invalid dotted identifier notation, expected type must be known"
  withForallBody expectedType fun resultType => do
    go resultType expectedType #[]
where
  /-- A weak version of forallTelescopeReducing that only uses whnfCore, to avoid unfolding definitions except by `unfoldDefinition?` below. -/
  withForallBody {α} (type : Expr) (k : Expr → TermElabM α) : TermElabM α :=
    forallTelescope type fun _ body => do
      let body ← whnfCore body
      if body.isForall then
        withForallBody body k
      else
        k body
  go (resultType : Expr) (expectedType : Expr) (previousExceptions : Array Exception) : TermElabM Name := do
    let resultType ← instantiateMVars resultType
    let resultTypeFn := resultType.cleanupAnnotations.getAppFn
    try
      tryPostponeIfMVar resultTypeFn
      let .const declName .. := resultTypeFn.cleanupAnnotations
        | throwError "invalid dotted identifier notation, expected type is not of the form (... → C ...) where C is a constant{indentExpr expectedType}"
      let idNew := declName ++ id.getId.eraseMacroScopes
      unless (← getEnv).contains idNew do
        throwError "invalid dotted identifier notation, unknown identifier `{idNew}` from expected type{indentExpr expectedType}"
      return idNew
    catch
      | ex@(.error ..) =>
        match (← unfoldDefinition? resultType) with
        | some resultType =>
          withForallBody resultType fun resultType => do
            go resultType expectedType (previousExceptions.push ex)
        | none =>
          previousExceptions.forM fun ex => logException ex
          throw ex
      | ex@(.internal _ _) => throw ex

private partial def elabAppFn (f : Syntax) (lvals : List LVal) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit ellipsis overloaded : Bool) (acc : Array (TermElabResult Expr)) : TermElabM (Array (TermElabResult Expr)) := do
  if f.getKind == choiceKind then
    -- Set `errToSorry` to `false` when processing choice nodes. See comment above about the interaction between `errToSorry` and `observing`.
    withReader (fun ctx => { ctx with errToSorry := false }) do
      f.getArgs.foldlM (init := acc) fun acc f => elabAppFn f lvals namedArgs args expectedType? explicit ellipsis true acc
  else
    let elabFieldName (e field : Syntax) (explicit : Bool) := do
      let newLVals := field.identComponents.map fun comp =>
        -- We use `none` in `suffix?` since `field` can't be part of a composite name
        LVal.fieldName comp comp.getId.getString! none f
      elabAppFn e (newLVals ++ lvals) namedArgs args expectedType? explicit ellipsis overloaded acc
    let elabFieldIdx (e idxStx : Syntax) (explicit : Bool) := do
      let some idx := idxStx.isFieldIdx? | throwError "invalid field index"
      elabAppFn e (LVal.fieldIdx idxStx idx :: lvals) namedArgs args expectedType? explicit ellipsis overloaded acc
    match f with
    | `($(e).$idx:fieldIdx) => elabFieldIdx e idx explicit
    | `($e |>.$idx:fieldIdx) => elabFieldIdx e idx explicit
    | `($(e).$field:ident) => elabFieldName e field explicit
    | `($e |>.$field:ident) => elabFieldName e field explicit
    | `(@$(e).$idx:fieldIdx) => elabFieldIdx e idx (explicit := true)
    | `(@$(e).$field:ident) => elabFieldName e field (explicit := true)
    | `($_:ident@$_:term) =>
      throwError "unexpected occurrence of named pattern"
    | `($id:ident) => do
      elabAppFnId id [] lvals namedArgs args expectedType? explicit ellipsis overloaded acc
    | `($id:ident.{$us,*}) => do
      let us ← elabExplicitUnivs us
      elabAppFnId id us lvals namedArgs args expectedType? explicit ellipsis overloaded acc
    | `(@$id:ident) =>
      elabAppFn id lvals namedArgs args expectedType? (explicit := true) ellipsis overloaded acc
    | `(@$_:ident.{$_us,*}) =>
      elabAppFn (f.getArg 1) lvals namedArgs args expectedType? (explicit := true) ellipsis overloaded acc
    | `(@$_)     => throwUnsupportedSyntax -- invalid occurrence of `@`
    | `(_)       => throwError "placeholders '_' cannot be used where a function is expected"
    | `(.$id:ident) =>
        addCompletionInfo <| CompletionInfo.dotId f id.getId (← getLCtx) expectedType?
        let fConst ← mkConst (← resolveDotName id expectedType?)
        let s ← observing do
          -- Use (force := true) because we want to record the result of .ident resolution even in patterns
          let fConst ← addTermInfo f fConst expectedType? (force := true)
          let e ← elabAppLVals fConst lvals namedArgs args expectedType? explicit ellipsis
          if overloaded then ensureHasType expectedType? e else return e
        return acc.push s
    | _ => do
      let catchPostpone := !overloaded
      /- If we are processing a choice node, then we should use `catchPostpone == false` when elaborating terms.
        Recall that `observing` does not catch `postponeExceptionId`. -/
      if lvals.isEmpty && namedArgs.isEmpty && args.isEmpty then
        /- Recall that elabAppFn is used for elaborating atomics terms **and** choice nodes that may contain
          arbitrary terms. If they are not being used as a function, we should elaborate using the expectedType. -/
        let s ← observing do
          if overloaded then
            elabTermEnsuringType f expectedType? catchPostpone
          else
            elabTerm f expectedType?
        return acc.push s
      else
        let s ← observing do
          let f ← elabTerm f none catchPostpone
          let e ← elabAppLVals f lvals namedArgs args expectedType? explicit ellipsis
          if overloaded then ensureHasType expectedType? e else return e
        return acc.push s

/-- Return the successful candidates. Recall we have Syntax `choice` nodes and overloaded symbols when we open multiple namespaces. -/
private def getSuccesses (candidates : Array (TermElabResult Expr)) : TermElabM (Array (TermElabResult Expr)) := do
  let r₁ := candidates.filter fun | EStateM.Result.ok .. => true | _ => false
  if r₁.size ≤ 1 then return r₁
  let r₂ ← candidates.filterM fun
    | .ok e s => do
      if e.isMVar then
        /- Make sure `e` is not a delayed coercion.
           Recall that coercion insertion may be delayed when the type and expected type contains
           metavariables that block TC resolution.
           When processing overloaded notation, we disallow delayed coercions at `e`. -/
        try
          s.restore
          synthesizeSyntheticMVars -- Tries to process pending coercions (and elaboration tasks)
          let e ← instantiateMVars e
          if e.isMVar then
          /- If `e` is still a metavariable, and its `SyntheticMVarDecl` is a coercion, we discard this solution -/
            if let some synDecl ← getSyntheticMVarDecl? e.mvarId! then
              if synDecl.kind matches SyntheticMVarKind.coe .. then
                return false
        catch _ =>
          -- If `synthesizeSyntheticMVars` failed, we just eliminate the candidate.
          return false
      return true
    | _ => return false
  if r₂.size == 0 then
    return r₁
  if r₂.size == 1 then
    return r₂
  /-
  If there are still more than one solution, discard solutions that have pending metavariables.
  We added this extra filter to address regressions introduced after fixing
  `isDefEqStuckEx` behavior at `ExprDefEq.lean`.
  -/
  let r₂ ← candidates.filterM fun
    | .ok _ s => do
      try
        s.restore
        synthesizeSyntheticMVars (postpone := .no)
        return true
      catch _ =>
        return false
    | _ => return false
  if r₂.size == 0 then
    return r₁
  return r₂
/--
  Throw an error message that describes why each possible interpretation for the overloaded notation and symbols did not work.
  We use a nested error message to aggregate the exceptions produced by each failure.
-/
private def mergeFailures (failures : Array (TermElabResult Expr)) : TermElabM α := do
  let exs := failures.map fun | .error ex _ => ex | _ => unreachable!
  throwErrorWithNestedErrors "overloaded" exs

private def elabAppAux (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (ellipsis : Bool) (expectedType? : Option Expr) : TermElabM Expr := do
  let candidates ← elabAppFn f [] namedArgs args expectedType? (explicit := false) (ellipsis := ellipsis) (overloaded := false) #[]
  if h : candidates.size = 1 then
    have : 0 < candidates.size := by rw [h]; decide
    applyResult candidates[0]
  else
    let successes ← getSuccesses candidates
    if h : successes.size = 1 then
      have : 0 < successes.size := by rw [h]; decide
      applyResult successes[0]
    else if successes.size > 1 then
      let msgs : Array MessageData ← successes.mapM fun success => do
        match success with
        | .ok e s => withMCtx s.meta.meta.mctx <| withEnv s.meta.core.env do addMessageContext m!"{e} : {← inferType e}"
        | _       => unreachable!
      throwErrorAt f "ambiguous, possible interpretations {toMessageList msgs}"
    else
      withRef f <| mergeFailures candidates

/--
  We annotate recursive applications with their `Syntax` node to make sure we can produce error messages with
  correct position information at `WF` and `Structural`.
-/
-- TODO: It is overkill to store the whole `Syntax` object, and we have to make sure we erase it later.
-- We should store only the position information in the future.
-- Recall that we will need to have a compact way of storing position information in the future anyway, if we
-- want to support debugging information
private def annotateIfRec (stx : Syntax) (e : Expr) : TermElabM Expr := do
  if (← read).saveRecAppSyntax then
    let resultFn := e.getAppFn
    if resultFn.isFVar then
      let localDecl ← resultFn.fvarId!.getDecl
      if localDecl.isAuxDecl then
        return mkRecAppWithSyntax e stx
  return e

@[builtin_term_elab app] def elabApp : TermElab := fun stx expectedType? =>
  universeConstraintsCheckpoint do
    let (f, namedArgs, args, ellipsis) ← expandApp stx
    annotateIfRec stx (← elabAppAux f namedArgs args (ellipsis := ellipsis) expectedType?)

private def elabAtom : TermElab := fun stx expectedType? => do
  annotateIfRec stx (← elabAppAux stx #[] #[] (ellipsis := false) expectedType?)

@[builtin_term_elab ident] def elabIdent : TermElab := elabAtom
@[builtin_term_elab namedPattern] def elabNamedPattern : TermElab := elabAtom
@[builtin_term_elab dotIdent] def elabDotIdent : TermElab := elabAtom
@[builtin_term_elab explicitUniv] def elabExplicitUniv : TermElab := elabAtom
@[builtin_term_elab pipeProj] def elabPipeProj : TermElab
  | `($e |>.%$tk$f $args*), expectedType? =>
    universeConstraintsCheckpoint do
      let (namedArgs, args, ellipsis) ← expandArgs args
      let mut stx ← `($e |>.%$tk$f)
      if let (some startPos, some stopPos) := (e.raw.getPos?, f.raw.getTailPos?) then
        stx := ⟨stx.raw.setInfo <| .synthetic (canonical := true) startPos stopPos⟩
      elabAppAux stx namedArgs args (ellipsis := ellipsis) expectedType?
  | _, _ => throwUnsupportedSyntax

@[builtin_term_elab explicit] def elabExplicit : TermElab := fun stx expectedType? =>
  match stx with
  | `(@$_:ident)          => elabAtom stx expectedType?  -- Recall that `elabApp` also has support for `@`
  | `(@$_:ident.{$_us,*}) => elabAtom stx expectedType?
  | `(@$(_).$_:fieldIdx)  => elabAtom stx expectedType?
  | `(@$(_).$_:ident)     => elabAtom stx expectedType?
  | `(@($t))             => elabTerm t expectedType? (implicitLambda := false)    -- `@` is being used just to disable implicit lambdas
  | `(@$t)               => elabTerm t expectedType? (implicitLambda := false)   -- `@` is being used just to disable implicit lambdas
  | _                    => throwUnsupportedSyntax

@[builtin_term_elab choice] def elabChoice : TermElab := elabAtom
@[builtin_term_elab proj] def elabProj : TermElab := elabAtom

builtin_initialize
  registerTraceClass `Elab.app
  registerTraceClass `Elab.app.args (inherited := true)
  registerTraceClass `Elab.app.propagateExpectedType (inherited := true)
  registerTraceClass `Elab.app.finalize (inherited := true)
  registerTraceClass `Elab.app.elab_as_elim (inherited := true)

end Lean.Elab.Term
