/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.FindMVar
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
  registerTagAttribute `elabWithoutExpectedType "mark that applications of the given declaration should be elaborated without the expected type"

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
    ensureHasTypeAux expectedType (← inferType arg) arg f
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

/--
  Relevant definitions:
  ```
  class CoeFun (α : Sort u) (γ : α → outParam (Sort v))
  ```
-/
private def tryCoeFun? (α : Expr) (a : Expr) : TermElabM (Option Expr) := do
  let v ← mkFreshLevelMVar
  let type ← mkArrow α (mkSort v)
  let γ ← mkFreshExprMVar type
  let u ← getLevel α
  let coeFunInstType := mkAppN (Lean.mkConst ``CoeFun [u, v]) #[α, γ]
  let mvar ← mkFreshExprMVar coeFunInstType MetavarKind.synthetic
  let mvarId := mvar.mvarId!
  try
    if (← synthesizeCoeInstMVarCore mvarId) then
      expandCoe <| mkAppN (Lean.mkConst ``CoeFun.coe [u, v]) #[α, γ, mvar, a]
    else
      return none
  catch _ =>
    return none

def synthesizeAppInstMVars (instMVars : Array MVarId) (app : Expr) : TermElabM Unit :=
  for mvarId in instMVars do
    unless (← synthesizeInstMVarCore mvarId) do
      registerSyntheticMVarWithCurrRef mvarId SyntheticMVarKind.typeClass
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
    From the users point of view this is a bug, since `let x := getElem xs 0` clearly constraints `x` to be `Bool`, but
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
  /-- Metavariables that we need the set the error context using the application being built. -/
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
  The ones that cannot be synthesized yet are registered.
  Remark: we use this method before trying to apply coercions to function. -/
def synthesizeAppInstMVars : M Unit := do
  let s ← get
  let instMVars := s.instMVars
  modify fun s => { s with instMVars := #[] }
  Term.synthesizeAppInstMVars instMVars s.f

/-- fType may become a forallE after we synthesize pending metavariables. -/
private def synthesizePendingAndNormalizeFunType : M Unit := do
  synthesizeAppInstMVars
  synthesizeSyntheticMVars
  let s ← get
  let fType ← whnfForall s.fType
  if fType.isForall then
    modify fun s => { s with fType }
  else
    match (← tryCoeFun? fType s.f) with
    | some f =>
      let fType ← inferType f
      modify fun s => { s with f, fType }
    | none =>
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
    let mvarId := arg.mvarId!
    if let some mvarErrorInfo ← getMVarErrorInfo? mvarId then
      registerMVarErrorInfo { mvarErrorInfo with argName? := argName }

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
  Auxiliary method for propagating the expected type. We call it as soon as we find the first explict
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
  Then, when it processes `x`, it assigns `?α := Nat`, and then obtain the
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
  If users need to disable expected type propagation, we can add an attribute `[elabWithoutExpectedType]`.
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
           get a type error because `?α × Prop` cannot be unified with `Nat × Bool`
           Most users would have a hard time trying to understand why these examples failed.

           Here is a possible alternative workarounds. We give up the idea of using `Prop` at `if-then-else`.
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
    -- Try to propagate expected type. Ignore if types are not definitionally equal, caller must handle it.
    trace[Elab.app.finalize] "expected type: {expectedType}"
    discard <| isDefEq expectedType eType
  synthesizeAppInstMVars
  return e

/-- Return `true` if there is a named argument that depends on the next argument. -/
private def anyNamedArgDependsOnCurrent : M Bool := do
  let s ← get
  if s.namedArgs.isEmpty then
    return false
  else
    forallTelescopeReducing s.fType fun xs _ => do
      let curr := xs[0]!
      for i in [1:xs.size] do
        let xDecl ← xs[i]!.fvarId!.getDecl
        if s.namedArgs.any fun arg => arg.name == xDecl.userName then
          if (← localDeclDependsOn xDecl curr.fvarId!) then
            return true
      return false


/-- Return `true` if there are regular or named arguments to be processed. -/
private def hasArgsToProcess : M Bool := do
  let s ← get
  return !s.args.isEmpty || !s.namedArgs.isEmpty

/-- Return `true` if the next argument at `args` is of the form `_` -/
private def isNextArgHole : M Bool := do
  match (← get).args with
  | Arg.stx (Syntax.node _ ``Lean.Parser.Term.hole _) :: _ => pure true
  | _ => pure false

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

  /-- (quick filter) Return true if `type` constains a binder `[C ...]` where `C` is a class containing outparams. -/
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
        let arg := args.get ⟨i, h⟩
        if arg == x && d.isOutParam then
          return true
        isOutParamOf x (i+1) args b
      | _ => return false
    else
      return false

mutual
  /--
    Create a fresh local variable with the current binder name and argument type, add it to `etaArgs` and `f`,
    and then execute the main loop.-/
  private partial def addEtaArg (argName : Name) : M Expr := do
    let n    ← getBindingName
    let type ← getArgExpectedType
    withLocalDeclD n type fun x => do
      modify fun s => { s with etaArgs := s.etaArgs.push x }
      addNewArg argName x
      main

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
    This method assume `fType` is a function type -/
  private partial def processExplictArg (argName : Name) : M Expr := do
    match (← get).args with
    | arg::args =>
      propagateExpectedType arg
      modify fun s => { s with args }
      elabAndAddNewArg argName arg
      main
    | _ =>
      let argType ← getArgExpectedType
      match (← read).explicit, argType.getOptParamDefault?, argType.getAutoParamTactic? with
      | false, some defVal, _  => addNewArg argName defVal; main
      | false, _, some (.const tacticDecl _) =>
        let env ← getEnv
        let opts ← getOptions
        match evalSyntaxConstant env opts tacticDecl with
        | Except.error err       => throwError err
        | Except.ok tacticSyntax =>
          -- TODO(Leo): does this work correctly for tactic sequences?
          let tacticBlock ← `(by $(⟨tacticSyntax⟩))
          let argNew := Arg.stx tacticBlock
          propagateExpectedType argNew
          elabAndAddNewArg argName argNew
          main
      | false, _, some _ =>
        throwError "invalid autoParam, argument must be a constant"
      | _, _, _ =>
        if !(← get).namedArgs.isEmpty then
          if (← anyNamedArgDependsOnCurrent) then
            addImplicitArg argName
          else if (← read).ellipsis then
            addImplicitArg argName
          else
            addEtaArg argName
        else if !(← read).explicit then
          if (← read).ellipsis then
            addImplicitArg argName
          else if (← fTypeHasOptAutoParams) then
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
      processExplictArg argName
    else
      addImplicitArg argName

  /--
    Process a `fType` of the form `{{x : A}} → B x`.
    This method assume `fType` is a function type -/
  private partial def processStrictImplicitArg (argName : Name) : M Expr := do
    if (← read).explicit then
      processExplictArg argName
    else if (← hasArgsToProcess) then
      addImplicitArg argName
    else
      finalize

  /--
    Process a `fType` of the form `[x : A] → B x`.
    This method assume `fType` is a function type -/
  private partial def processInstImplicitArg (argName : Name) : M Expr := do
    if (← read).explicit then
      if (← isNextArgHole) then
        /- Recall that if '@' has been used, and the argument is '_', then we still use type class resolution -/
        let arg ← mkFreshExprMVar (← getArgExpectedType) MetavarKind.synthetic
        modify fun s => { s with args := s.args.tail! }
        addInstMVar arg.mvarId!
        addNewArg argName arg
        main
      else
        processExplictArg argName
    else
      let arg ← mkFreshExprMVar (← getArgExpectedType) MetavarKind.synthetic
      addInstMVar arg.mvarId!
      addNewArg argName arg
      main

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
        | _               => processExplictArg binderName
    else if (← hasArgsToProcess) then
      synthesizePendingAndNormalizeFunType
      main
    else
      finalize

end

end ElabAppArgs

builtin_initialize elabAsElim : TagAttribute ←
  registerTagAttribute `elabAsElim
    "instructs elaborator that the arguments of the function application should be elaborated as were an eliminator"
    fun declName => do
      let go : MetaM Unit := do
        discard <| getElimInfo declName
        let info ← getConstInfo declName
        if (← hasOptAutoParams info.type) then
          throwError "[elabAsElim] attribute cannot be used in declarations containing optional and auto parameters"
      go.run' {} {}

/-! # Eliminator-like function application elaborator -/
namespace ElabElim

/-- Context of the `elabAsElim` elaboration procedure. -/
structure Context where
  elimInfo : ElimInfo
  expectedType : Expr

/-- State of the `elabAsElim` elaboration procedure. -/
structure State where
  /-- The resultant expression being built. -/
  f            : Expr
  /-- `f : fType -/
  fType        : Expr
  /-- User-provided named arguments that still have to be processed. -/
  namedArgs    : List NamedArg
  /-- User-providedarguments that still have to be processed. -/
  args         : List Arg
  /-- Discriminants processed so far. -/
  discrs       : Array Expr := #[]
  /-- Instance implicit arguments collected so far. -/
  instMVars    : Array MVarId := #[]
  /-- Position of the next argument to be processed. We use it to decide whether the argument is the motive or a discriminant. -/
  idx          : Nat := 0
  /-- Store the metavariable used to represent the motive that will be computed at `finalize`. -/
  motive?      : Option Expr := none

abbrev M := ReaderT Context $ StateRefT State TermElabM

/-- Infer the `motive` using the expected type by `kabstract`ing the discriminants. -/
def mkMotive (discrs : Array Expr) (expectedType : Expr): MetaM Expr := do
  discrs.foldrM (init := expectedType) fun discr motive => do
    let discr ← instantiateMVars discr
    let motiveBody ← kabstract motive discr
    /- We use `transform (usedLetOnly := true)` to eliminate unnecessary let-expressions. -/
    let discrType ← transform (usedLetOnly := true) (← instantiateMVars (← inferType discr))
    return Lean.mkLambda (← mkFreshBinderName) BinderInfo.default discrType motiveBody

/-- If the eliminator is over-applied, we "revert" the extra arguments. -/
def revertArgs (args : List Arg) (f : Expr) (expectedType : Expr) : TermElabM (Expr × Expr) :=
  args.foldrM (init := (f, expectedType)) fun arg (f, expectedType) => do
    let val ←
      match arg with
      | .expr val => pure val
      | .stx stx => elabTerm stx none
    let val ← instantiateMVars val
    let expectedTypeBody ← kabstract expectedType val
    /- We use `transform (usedLetOnly := true)` to eliminate unnecessary let-expressions. -/
    let valType ← transform (usedLetOnly := true) (← instantiateMVars (← inferType val))
    return (mkApp f val, mkForall (← mkFreshBinderName) BinderInfo.default valType expectedTypeBody)

/--
Contruct the resulting application after all discriminants have bee elaborated, and we have
consumed as many given arguments as possible.
-/
def finalize : M Expr := do
  unless (← get).namedArgs.isEmpty do
    throwError "failed to elaborate eliminator, unused named arguments: {(← get).namedArgs.map (·.name)}"
  let some motive := (← get).motive?
    | throwError "failed to elaborate eliminator, insufficient number of arguments"
  forallTelescope (← get).fType fun xs _ => do
    let mut expectedType := (← read).expectedType
    let mut f := (← get).f
    if xs.size > 0 then
      assert! (← get).args.isEmpty
      try
        expectedType ← instantiateForall expectedType xs
      catch _ =>
        throwError "failed to elaborate eliminator, insufficient number of arguments, expected type:{indentExpr expectedType}"
    else
      -- over-application, simulate `revert`
      (f, expectedType) ← revertArgs (← get).args f expectedType
    let result := mkAppN f xs
    let mut discrs := (← get).discrs
    let idx := (← get).idx
    if (← get).discrs.size < (← read).elimInfo.targetsPos.size then
      for i in [idx:idx + xs.size], x in xs do
        if (← read).elimInfo.targetsPos.contains i then
          discrs := discrs.push x
    let motiveVal ← mkMotive discrs expectedType
    unless (← isDefEq motive motiveVal) do
      throwError "failed to elaborate eliminator, invalid motive{indentExpr motiveVal}"
    synthesizeAppInstMVars (← get).instMVars result
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

/-- Push the given expression into the `discrs` field in the state. -/
def addDiscr (discr : Expr) : M Unit :=
  modify fun s => { s with discrs := s.discrs.push discr }

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
    let mvarId := arg.mvarId!
    if let some mvarErrorInfo ← getMVarErrorInfo? mvarId then
      registerMVarErrorInfo { mvarErrorInfo with argName? := binderName }

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
    let motive ← mkImplicitArg binderType binderInfo
    setMotive motive
    addArgAndContinue motive
  else if (← read).elimInfo.targetsPos.contains idx then
    match (← getNextArg? binderName binderInfo) with
    | .some arg => let discr ← elabArg arg binderType; addDiscr discr; addArgAndContinue discr
    | .undef => finalize
    | .none => let discr ← mkImplicitArg binderType binderInfo; addDiscr discr; addArgAndContinue discr
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
  elabAsElim? : TermElabM (Option ElimInfo) := do
    if explicit || ellipsis then return none
    let .const declName _ := f | return none
    unless (← shouldElabAsElim declName) do return none
    let elimInfo ← getElimInfo declName
    forallTelescopeReducing (← inferType f) fun xs _ => do
      if h : elimInfo.motivePos < xs.size then
        let x := xs[elimInfo.motivePos]
        let localDecl ← x.fvarId!.getDecl
        if findBinderName? namedArgs.toList localDecl.userName matches some _ then
          -- motive has been explicitly provided, so we should use standard app elaborator
          return none
        return some elimInfo
      else
        return none

/-- Auxiliary inductive datatype that represents the resolution of an `LVal`. -/
inductive LValResolution where
  | projFn   (baseStructName : Name) (structName : Name) (fieldName : Name)
  | projIdx  (structName : Name) (idx : Nat)
  | const    (baseStructName : Name) (structName : Name) (constName : Name)
  | localRec (baseName : Name) (fullName : Name) (fvar : Expr)

private def throwLValError (e : Expr) (eType : Expr) (msg : MessageData) : TermElabM α :=
  throwError "{msg}{indentExpr e}\nhas type{indentExpr eType}"

/--
`findMethod? env S fName`.
- If `env` contains `S ++ fName`, return `(S, S++fName)`
- Otherwise if `env` contains private name `prv` for `S ++ fName`, return `(S, prv)`, o
- Otherwise for each parent structure `S'` of  `S`, we try `findMethod? env S' fname`
-/
private partial def findMethod? (env : Environment) (structName fieldName : Name) : Option (Name × Name) :=
  let fullName := structName ++ fieldName
  match env.find? fullName with
  | some _ => some (structName, fullName)
  | none   =>
    let fullNamePrv := mkPrivateName env fullName
    match env.find? fullNamePrv with
    | some _ => some (structName, fullNamePrv)
    | none   =>
      if isStructure env structName then
        (getParentStructures env structName).findSome? fun parentStructName => findMethod? env parentStructName fieldName
      else
        none

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
      let fullName := `Function ++ fieldName
      if (← getEnv).contains fullName then
        return LValResolution.const `Function `Function fullName
    | _ => pure ()
  match eType.getAppFn.constName?, lval with
  | some structName, LVal.fieldIdx _ idx =>
    if idx == 0 then
      throwError "invalid projection, index must be greater than 0"
    let env ← getEnv
    unless isStructureLike env structName do
      throwLValError e eType "invalid projection, structure expected"
    let numFields := getStructureLikeNumFields env structName
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
      if let some (baseStructName, fullName) := findMethod? env structName fieldName then
        return LValResolution.const baseStructName structName fullName
      else if let some (structName', fullName) := findMethodAlias? env structName fieldName then
        return LValResolution.const structName' structName' fullName
      else
        throwLValError e eType
          m!"invalid field '{fieldName}', the environment does not contain '{Name.mkStr structName fieldName}'"
    -- search local context first, then environment
    let searchCtx : Unit → TermElabM LValResolution := fun _ => do
      let fullName := Name.mkStr structName fieldName
      for localDecl in (← getLCtx) do
        if localDecl.binderInfo == BinderInfo.auxDecl then
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
      e ← elabAppArgs projFn #[{ name := `self, val := Arg.expr e }] (args := #[]) (expectedType? := none) (explicit := false) (ellipsis := false)
    return e

private def typeMatchesBaseName (type : Expr) (baseName : Name) : MetaM Bool := do
  if baseName == `Function then
    return (← whnfR type).isForall
  else if type.consumeMData.isAppOf baseName then
    return true
  else
    return (← whnfR type).isAppOf baseName

/-- Auxiliary method for field notation. It tries to add `e` as a new argument to `args` or `namedArgs`.
   This method first finds the parameter with a type of the form `(baseName ...)`.
   When the parameter is found, if it an explicit one and `args` is big enough, we add `e` to `args`.
   Otherwise, if there isn't another parameter with the same name, we add `e` to `namedArgs`.

   Remark: `fullName` is the name of the resolved "field" access function. It is used for reporting errors -/
private def addLValArg (baseName : Name) (fullName : Name) (e : Expr) (args : Array Arg) (namedArgs : Array NamedArg) (fType : Expr)
    : TermElabM (Array Arg × Array NamedArg) :=
  forallTelescopeReducing fType fun xs _ => do
    let mut argIdx := 0 -- position of the next explicit argument
    let mut remainingNamedArgs := namedArgs
    for i in [:xs.size] do
      let x := xs[i]!
      let xDecl ← x.fvarId!.getDecl
      /- If there is named argument with name `xDecl.userName`, then we skip it. -/
      match remainingNamedArgs.findIdx? (fun namedArg => namedArg.name == xDecl.userName) with
      | some idx =>
        remainingNamedArgs := remainingNamedArgs.eraseIdx idx
      | none =>
        let type := xDecl.type
        if (← typeMatchesBaseName type baseName) then
          /- We found a type of the form (baseName ...).
             First, we check if the current argument is an explicit one,
             and the current explicit position "fits" at `args` (i.e., it must be ≤ arg.size) -/
          if argIdx ≤ args.size && xDecl.binderInfo.isExplicit then
            /- We insert `e` as an explicit argument -/
            return (args.insertAt argIdx (Arg.expr e), namedArgs)
          /- If we can't add `e` to `args`, we try to add it using a named argument, but this is only possible
             if there isn't an argument with the same name occurring before it. -/
          for j in [:i] do
            let prev := xs[j]!
            let prevDecl ← prev.fvarId!.getDecl
            if prevDecl.userName == xDecl.userName then
              throwError "invalid field notation, function '{fullName}' has argument with the expected type{indentExpr type}\nbut it cannot be used"
          return (args, namedArgs.push { name := xDecl.userName, val := Arg.expr e })
        if xDecl.binderInfo.isExplicit then
          -- advance explicit argument position
          argIdx := argIdx + 1
    throwError "invalid field notation, function '{fullName}' does not have argument with type ({baseName} ...) that can be used, it must be explicit or implicit with an unique name"

private def elabAppLValsAux (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) (explicit ellipsis : Bool)
    (f : Expr) (lvals : List LVal) : TermElabM Expr :=
  let rec loop : Expr → List LVal → TermElabM Expr
  | f, []          => elabAppArgs f namedArgs args expectedType? explicit ellipsis
  | f, lval::lvals => do
    if let LVal.fieldName (ref := fieldStx) (targetStx := targetStx) .. := lval then
      addDotCompletionInfo targetStx f expectedType? fieldStx
    let hasArgs := !namedArgs.isEmpty || !args.isEmpty
    let (f, lvalRes) ← resolveLVal f lval hasArgs
    match lvalRes with
    | LValResolution.projIdx structName idx =>
      let f ← mkProjAndCheck structName idx f
      let f ← addTermInfo lval.getRef f
      loop f lvals
    | LValResolution.projFn baseStructName structName fieldName =>
      let f ← mkBaseProjections baseStructName structName f
      if let some info := getFieldInfo? (← getEnv) baseStructName fieldName then
        if isPrivateNameFromImportedModule (← getEnv) info.projFn then
          throwError "field '{fieldName}' from structure '{structName}' is private"
        let projFn ← mkConst info.projFn
        let projFn ← addTermInfo lval.getRef projFn
        if lvals.isEmpty then
          let namedArgs ← addNamedArg namedArgs { name := `self, val := Arg.expr f }
          elabAppArgs projFn namedArgs args expectedType? explicit ellipsis
        else
          let f ← elabAppArgs projFn #[{ name := `self, val := Arg.expr f }] #[] (expectedType? := none) (explicit := false) (ellipsis := false)
          loop f lvals
      else
        unreachable!
    | LValResolution.const baseStructName structName constName =>
      let f ← if baseStructName != structName then mkBaseProjections baseStructName structName f else pure f
      let projFn ← mkConst constName
      let projFn ← addTermInfo lval.getRef projFn
      if lvals.isEmpty then
        let projFnType ← inferType projFn
        let (args, namedArgs) ← addLValArg baseStructName constName f args namedArgs projFnType
        elabAppArgs projFn namedArgs args expectedType? explicit ellipsis
      else
        let f ← elabAppArgs projFn #[] #[Arg.expr f] (expectedType? := none) (explicit := false) (ellipsis := false)
        loop f lvals
    | LValResolution.localRec baseName fullName fvar =>
      let fvar ← addTermInfo lval.getRef fvar
      if lvals.isEmpty then
        let fvarType ← inferType fvar
        let (args, namedArgs) ← addLValArg baseName fullName f args namedArgs fvarType
        elabAppArgs fvar namedArgs args expectedType? explicit ellipsis
      else
        let f ← elabAppArgs fvar #[] #[Arg.expr f] (expectedType? := none) (explicit := false) (ellipsis := false)
        loop f lvals
  loop f lvals

private def elabAppLVals (f : Expr) (lvals : List LVal) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit ellipsis : Bool) : TermElabM Expr := do
  if !lvals.isEmpty && explicit then
    throwError "invalid use of field notation with `@` modifier"
  elabAppLValsAux namedArgs args expectedType? explicit ellipsis f lvals

def elabExplicitUnivs (lvls : Array Syntax) : TermElabM (List Level) := do
  lvls.foldrM (init := []) fun stx lvls => return (← elabLevel stx)::lvls

/-!
# Interaction between `errToSorry` and `observing`.

- The method `elabTerm` catches exceptions, log them, and returns a synthetic sorry (IF `ctx.errToSorry` == true).

- When we elaborate choice nodes (and overloaded identifiers), we track multiple results using the `observing x` combinator.
  The `observing x` executes `x` and returns a `TermElabResult`.

`observing `x does not check for synthetic sorry's, just an exception. Thus, it may think `x` worked when it didn't
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
    | field::fields, true  => .fieldName field field.getId.toString (toName (field::fields)) fIdent :: toLVals fields false
    | field::fields, false => .fieldName field field.getId.toString none fIdent :: toLVals fields false

/-- Resolve `(.$id:ident)` using the expected type to infer namespace. -/
private partial def resolveDotName (id : Syntax) (expectedType? : Option Expr) : TermElabM Name := do
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType := expectedType?
    | throwError "invalid dotted identifier notation, expected type must be known"
  forallTelescopeReducing expectedType fun _ resultType => do
    go resultType expectedType #[]
where
  go (resultType : Expr) (expectedType : Expr) (previousExceptions : Array Exception) : TermElabM Name := do
    let resultTypeFn := (← instantiateMVars resultType).cleanupAnnotations.getAppFn
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
        | some resultType => go (← whnfCore resultType) expectedType (previousExceptions.push ex)
        | none       =>
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
    let elabFieldName (e field : Syntax) := do
      let newLVals := field.identComponents.map fun comp =>
        -- We use `none` in `suffix?` since `field` can't be part of a composite name
        LVal.fieldName comp (toString comp.getId) none e
      elabAppFn e (newLVals ++ lvals) namedArgs args expectedType? explicit ellipsis overloaded acc
    let elabFieldIdx (e idxStx : Syntax) := do
      let idx := idxStx.isFieldIdx?.get!
      elabAppFn e (LVal.fieldIdx idxStx idx :: lvals) namedArgs args expectedType? explicit ellipsis overloaded acc
    match f with
    | `($(e).$idx:fieldIdx) => elabFieldIdx e idx
    | `($e |>.$idx:fieldIdx) => elabFieldIdx e idx
    | `($(e).$field:ident) => elabFieldName e field
    | `($e |>.$field:ident) => elabFieldName e field
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
        let fConst ← addTermInfo f fConst
        let s ← observing do
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
  if r₂.size == 0 then return r₁ else return r₂

/--
  Throw an error message that describes why each possible interpretation for the overloaded notation and symbols did not work.
  We use a nested error message to aggregate the exceptions produced by each failure.
-/
private def mergeFailures (failures : Array (TermElabResult Expr)) : TermElabM α := do
  let exs := failures.map fun | .error ex _ => ex | _ => unreachable!
  throwErrorWithNestedErrors "overloaded" exs

private def elabAppAux (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (ellipsis : Bool) (expectedType? : Option Expr) : TermElabM Expr := do
  let candidates ← elabAppFn f [] namedArgs args expectedType? (explicit := false) (ellipsis := ellipsis) (overloaded := false) #[]
  if candidates.size == 1 then
    applyResult candidates[0]!
  else
    let successes ← getSuccesses candidates
    if successes.size == 1 then
      applyResult successes[0]!
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

@[builtinTermElab app] def elabApp : TermElab := fun stx expectedType? =>
  universeConstraintsCheckpoint do
    let (f, namedArgs, args, ellipsis) ← expandApp stx
    annotateIfRec stx (← elabAppAux f namedArgs args (ellipsis := ellipsis) expectedType?)

private def elabAtom : TermElab := fun stx expectedType? => do
  annotateIfRec stx (← elabAppAux stx #[] #[] (ellipsis := false) expectedType?)

@[builtinTermElab ident] def elabIdent : TermElab := elabAtom
/-- `x@e` matches the pattern `e` and binds its value to the identifier `x`. -/
@[builtinTermElab namedPattern] def elabNamedPattern : TermElab := elabAtom
@[builtinTermElab dotIdent] def elabDotIdent : TermElab := elabAtom
/-- `x.{u, ...}` explicitly specifies the universes `u, ...` of the constant `x`. -/
@[builtinTermElab explicitUniv] def elabExplicitUniv : TermElab := elabAtom
/-- `e |>.x` is a shorthand for `(e).x`. It is especially useful for avoiding parentheses with repeated applications. -/
@[builtinTermElab pipeProj] def elabPipeProj : TermElab
  | `($e |>.$f $args*), expectedType? =>
    universeConstraintsCheckpoint do
      let (namedArgs, args, ellipsis) ← expandArgs args
      elabAppAux (← `($e |>.$f)) namedArgs args (ellipsis := ellipsis) expectedType?
  | _, _ => throwUnsupportedSyntax

/--
`@x` disables automatic insertion of implicit parameters of the constant `x`.
`@e` for any term `e` also disables the insertion of implicit lambdas at this position. -/
@[builtinTermElab explicit] def elabExplicit : TermElab := fun stx expectedType? =>
  match stx with
  | `(@$_:ident)         => elabAtom stx expectedType?  -- Recall that `elabApp` also has support for `@`
  | `(@$_:ident.{$_us,*}) => elabAtom stx expectedType?
  | `(@($t))             => elabTerm t expectedType? (implicitLambda := false)    -- `@` is being used just to disable implicit lambdas
  | `(@$t)               => elabTerm t expectedType? (implicitLambda := false)   -- `@` is being used just to disable implicit lambdas
  | _                    => throwUnsupportedSyntax

@[builtinTermElab choice] def elabChoice : TermElab := elabAtom
@[builtinTermElab proj] def elabProj : TermElab := elabAtom

builtin_initialize
  registerTraceClass `Elab.app

end Lean.Elab.Term
