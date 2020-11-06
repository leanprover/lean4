/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.FindMVar
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Term
open Meta

/--
  Auxiliary inductive datatype for combining unelaborated syntax
  and already elaborated expressions. It is used to elaborate applications. -/
inductive Arg
  | stx  (val : Syntax)
  | expr (val : Expr)

instance : Inhabited Arg := ⟨Arg.stx (arbitrary _)⟩

instance : ToString Arg := ⟨fun
  | Arg.stx  val => toString val
  | Arg.expr val => toString val⟩

/-- Named arguments created using the notation `(x := val)` -/
structure NamedArg :=
  (ref  : Syntax := Syntax.missing)
  (name : Name)
  (val  : Arg)

instance : ToString NamedArg :=
  ⟨fun s => "(" ++ toString s.name ++ " := " ++ toString s.val ++ ")"⟩

instance : Inhabited NamedArg := ⟨{ name := arbitrary _, val := arbitrary _ }⟩

def throwInvalidNamedArg {α} (namedArg : NamedArg) (fn? : Option Name) : TermElabM α :=
  withRef namedArg.ref $ match fn? with
    | some fn => throwError! "invalid argument name '{namedArg.name}' for function '{fn}'"
    | none    => throwError! "invalid argument name '{namedArg.name}' for function"

/--
  Add a new named argument to `namedArgs`, and throw an error if it already contains a named argument
  with the same name. -/
def addNamedArg (namedArgs : Array NamedArg) (namedArg : NamedArg) : TermElabM (Array NamedArg) := do
  if namedArgs.any (namedArg.name == ·.name) then
    throwError! "argument '{namedArg.name}' was already set"
  pure $ namedArgs.push namedArg

private def ensureArgType (f : Expr) (arg : Expr) (expectedType : Expr) : TermElabM Expr := do
  let argType ← inferType arg
  ensureHasTypeAux expectedType argType arg f

/-
  Relevant definitions:
  ```
  class CoeFun (α : Sort u) (γ : α → outParam (Sort v))
  abbrev coeFun {α : Sort u} {γ : α → Sort v} (a : α) [CoeFun α γ] : γ a
  ``` -/
private def tryCoeFun? (α : Expr) (a : Expr) : TermElabM (Option Expr) := do
  let v ← mkFreshLevelMVar
  let type ← mkArrow α (mkSort v)
  let γ ← mkFreshExprMVar type
  let u ← getLevel α
  let coeFunInstType := mkAppN (Lean.mkConst `CoeFun [u, v]) #[α, γ]
  let mvar ← mkFreshExprMVar coeFunInstType MetavarKind.synthetic
  let mvarId := mvar.mvarId!
  try
    if (← synthesizeInstMVarCore mvarId) then
      pure $ some $ mkAppN (Lean.mkConst `coeFun [u, v]) #[α, γ, a, mvar]
    else
      pure none
  catch _ =>
    pure none

def synthesizeAppInstMVars (instMVars : Array MVarId) : TermElabM Unit :=
  for mvarId in instMVars do
    unless (← synthesizeInstMVarCore mvarId) do
      registerSyntheticMVarWithCurrRef mvarId SyntheticMVarKind.typeClass

namespace ElabAppArgs

/- Auxiliary structure for elaborating the application `f args namedArgs`. -/
structure State :=
  (explicit          : Bool) -- true if `@` modifier was used
  (f                 : Expr)
  (fType             : Expr)
  (args              : List Arg)            -- remaining regular arguments
  (namedArgs         : List NamedArg)       -- remaining named arguments to be processed
  (ellipsis          : Bool := false)
  (expectedType?     : Option Expr)
  (etaArgs           : Array Expr   := #[])
  (toSetErrorCtx     : Array MVarId := #[]) -- metavariables that we need the set the error context using the application being built
  (instMVars         : Array MVarId := #[]) -- metavariables for the instance implicit arguments that have already been processed
  -- The following two fields are used to implement the `propagateExpectedType` heuristic.
  (typeMVars         : Array MVarId := #[]) -- metavariables for implicit arguments of the form `{α : Sort u}` that have already been processed
  (alreadyPropagated : Bool := false)       -- true when expectedType has already been propagated

abbrev M := StateRefT State TermElabM

/- Add the given metavariable to the collection of metavariables associated with instance-implicit arguments. -/
private def addInstMVar (mvarId : MVarId) : M Unit :=
  modify fun s => { s with instMVars := s.instMVars.push mvarId }

/-
  Try to synthesize metavariables are `instMVars` using type class resolution.
  The ones that cannot be synthesized yet are registered.
  Remark: we use this method before trying to apply coercions to function. -/
def synthesizeAppInstMVars : M Unit := do
  let s ← get
  let instMVars := s.instMVars
  modify fun s => { s with instMVars := #[] }
  Lean.Elab.Term.synthesizeAppInstMVars instMVars

/- fType may become a forallE after we synthesize pending metavariables. -/
private def synthesizePendingAndNormalizeFunType : M Unit := do
  synthesizeAppInstMVars
  synthesizeSyntheticMVars
  let s ← get
  let fType ← whnfForall s.fType
  match fType with
  | Expr.forallE _ _ _ _ => modify fun s => { s with fType := fType }
  | _ =>
    match (← tryCoeFun? fType s.f) with
    | some f =>
      let fType ← inferType f
      modify fun s => { s with f := f, fType := fType }
    | none =>
      for namedArg in s.namedArgs do
        match s.f.getAppFn with
        | Expr.const fn .. => throwInvalidNamedArg namedArg fn
        | _                => throwInvalidNamedArg namedArg none
      throwError! "function expected at{indentExpr s.f}\nterm has type{indentExpr fType}"

/- Normalize and return the function type. -/
private def normalizeFunType : M Expr := do
  let s ← get
  let fType ← whnfForall s.fType
  modify fun s => { s with fType := fType }
  pure fType

/- Return the binder name at `fType`. This method assumes `fType` is a function type. -/
private def getBindingName : M Name := return (← get).fType.bindingName!

/- Return the next argument expected type. This method assumes `fType` is a function type. -/
private def getArgExpectedType : M Expr := return (← get).fType.bindingDomain!

def eraseNamedArgCore (namedArgs : List NamedArg) (binderName : Name) : List NamedArg :=
  namedArgs.filter (·.name != binderName)

/- Remove named argument with name `binderName` from `namedArgs`. -/
def eraseNamedArg (binderName : Name) : M Unit :=
  modify fun s => { s with namedArgs := eraseNamedArgCore s.namedArgs binderName }

/- Return true if the next argument at `args` is of the form `_` -/
private def isNextArgHole : M Bool := do
  match (← get).args with
  | Arg.stx (Syntax.node `Lean.Parser.Term.hole _) :: _ => pure true
  | _ => pure false

/-
  Add a new argument to the result. That is, `f := f arg`, update `fType`.
  This method assumes `fType` is a function type. -/
private def addNewArg (arg : Expr) : M Unit :=
  modify fun s => { s with f := mkApp s.f arg, fType := s.fType.bindingBody!.instantiate1 arg }

/-
  Elaborate the given `Arg` and add it to the result. See `addNewArg`.
  Recall that, `Arg` may be wrapping an already elaborated `Expr`. -/
private def elabAndAddNewArg (arg : Arg) : M Unit := do
  let s ← get
  let expectedType ← getArgExpectedType
  match arg with
  | Arg.expr val =>
    let arg ← ensureArgType s.f val expectedType
    addNewArg arg
  | Arg.stx val  =>
    let val ← elabTerm val expectedType
    let arg ← ensureArgType s.f val expectedType
    addNewArg arg

/- Return true if the given type contains `OptParam` or `AutoParams` -/
private def hasOptAutoParams (type : Expr) : M Bool := do
  forallTelescopeReducing type fun xs type =>
    xs.anyM fun x => do
      let xType ← inferType x
      pure $ xType.getOptParamDefault?.isSome || xType.getAutoParamTactic?.isSome

/- Return true if `fType` contains `OptParam` or `AutoParams` -/
private def fTypeHasOptAutoParams : M Bool := do
  hasOptAutoParams (← get).fType

/- Auxiliary function for retrieving the resulting type of a function application.
   See `propagateExpectedType`. -/
private partial def getForallBody : Nat → List NamedArg → Expr → Option Expr
  | i, namedArgs, type@(Expr.forallE n d b c) =>
    match namedArgs.find? fun (namedArg : NamedArg) => namedArg.name == n with
    | some _ => getForallBody i (eraseNamedArgCore namedArgs n) b
    | none =>
      if !c.binderInfo.isExplicit then
        getForallBody i namedArgs b
      else if i > 0 then
        getForallBody (i-1) namedArgs b
      else if d.isAutoParam || d.isOptParam then
        getForallBody i namedArgs b
      else
        some type
  | 0, [], type => some type
  | _, _,  _    => none

/-
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
  1- The resultant type depends on the remaining arguments (i.e., `!eTypeBody.hasLooseBVars`)
  2- The resultant type does not contain any type metavariable.
  3- The resultant type contains a nontype metavariable.

  We added conditions 2&3 to be able to restrict this method to simple functions that are "morally" in
  the Hindley&Milner fragment.
  For example, consider the following definitions
  ```
  def foo {n m : Nat} (a : bv n) (b : bv m) : bv (n - m)
  ```
  Now, consider
  ```
  def test (x1 : bv 32) (x2 : bv 31) (y1 : bv 64) (y2 : bv 63) : bv 1 :=
  foo x1 x2 = foo y1 y2
  ```
  When the elaborator reaches the term `foo y1 y2`, the expected type is `bv (32-31)`.
  If we apply this method, we would solve the unification problem `bv (?n - ?m) =?= bv (32 - 31)`,
  by assigning `?n := 32` and `?m := 31`. Then, the elaborator fails elaborating `y1` since
  `bv 64` is **not** definitionally equal to `bv 32`.
-/
private def propagateExpectedType : M Unit := do
  let s ← get
  -- TODO: handle s.etaArgs.size > 0
  unless s.explicit || !s.etaArgs.isEmpty || s.alreadyPropagated || s.typeMVars.isEmpty do
    modify fun s => { s with alreadyPropagated := true }
    match s.expectedType? with
    | none              => pure ()
    | some expectedType =>
      let numRemainingArgs := s.args.length
      trace[Elab.app.propagateExpectedType]! "etaArgs.size: {s.etaArgs.size}, numRemainingArgs: {numRemainingArgs}, fType: {s.fType}"
      match getForallBody numRemainingArgs s.namedArgs s.fType with
      | none           => pure ()
      | some fTypeBody =>
        unless fTypeBody.hasLooseBVars do
          let hasTypeMVar     := (fTypeBody.findMVar? fun mvarId => s.typeMVars.contains mvarId).isSome
          let hasOnlyTypeMVar := (fTypeBody.findMVar? fun mvarId => !s.typeMVars.contains mvarId).isNone
          if hasTypeMVar && hasOnlyTypeMVar then
            unless (← hasOptAutoParams fTypeBody) do
              trace[Elab.app.propagateExpectedType]! "{expectedType} =?= {fTypeBody}"
              isDefEq expectedType fTypeBody
              pure ()

/-
  Create a fresh local variable with the current binder name and argument type, add it to `etaArgs` and `f`,
  and then execute the continuation `k`.-/
private def addEtaArg (k : M Expr) : M Expr := do
  let n    ← getBindingName
  let type ← getArgExpectedType
  withLocalDeclD n type fun x => do
    modify fun s => { s with etaArgs := s.etaArgs.push x }
    addNewArg x
    k

/- This method execute after all application arguments have been processed. -/
private def finalize : M Expr := do
  let s ← get
  let e     := s.f
  let eType := s.fType
  -- all user explicit arguments have been consumed
  trace[Elab.app.finalize]! e
  let ref ← getRef
  -- Register the error context of implicits
  for mvarId in s.toSetErrorCtx do
    registerMVarErrorImplicitArgInfo mvarId ref e
  if !s.etaArgs.isEmpty then
    e ← mkLambdaFVars s.etaArgs e
    eType ← inferType e
  trace[Elab.app.finalize]! "after etaArgs, {e} : {eType}"
  match s.expectedType? with
  | none              => pure ()
  | some expectedType =>
     trace[Elab.app.finalize]! "expected type: {expectedType}"
     -- Try to propagate expected type. Ignore if types are not definitionally equal, caller must handle it.
     isDefEq expectedType eType
     pure ()
  synthesizeAppInstMVars
  pure e

private def addImplicitArg (k : M Expr) : M Expr := do
  let argType ← getArgExpectedType
  let arg ← mkFreshExprMVar argType
  if (← isTypeFormer arg) then
    modify fun s => { s with typeMVars := s.typeMVars.push arg.mvarId!, toSetErrorCtx := s.toSetErrorCtx.push arg.mvarId! }
  addNewArg arg
  k

/-
  Process a `fType` of the form `(x : A) → B x`.
  This method assume `fType` is a function type -/
private def processExplictArg (k : M Expr) : M Expr := do
  let s ← get
  match s.args with
  | arg::args =>
    propagateExpectedType
    modify fun s => { s with args := args }
    elabAndAddNewArg arg
    k
  | _ =>
    let argType ← getArgExpectedType
    match s.explicit, argType.getOptParamDefault?, argType.getAutoParamTactic? with
    | false, some defVal, _  => addNewArg defVal; k
    | false, _, some (Expr.const tacticDecl _ _) =>
      let env ← getEnv
      let opts ← getOptions
      match evalSyntaxConstant env opts tacticDecl with
      | Except.error err       => throwError err
      | Except.ok tacticSyntax =>
        let tacticBlock ← `(by { $(tacticSyntax.getArgs)* })
        -- tacticBlock does not have any position information.
        -- So, we use the current ref
        let ref ← getRef
        let tacticBlock := tacticBlock.copyInfo ref
        let argType     := argType.getArg! 0 -- `autoParam type := by tactic` ==> `type`
        propagateExpectedType
        elabAndAddNewArg (Arg.stx tacticBlock)
        k
    | false, _, some _ =>
      throwError "invalid autoParam, argument must be a constant"
    | _, _, _ =>
      if !s.namedArgs.isEmpty then
        addEtaArg k
      else if !s.explicit then
        if (← fTypeHasOptAutoParams) then
          addEtaArg k
        else if (← get).ellipsis then
          addImplicitArg k
        else
          finalize
      else
        finalize

/-
  Process a `fType` of the form `{x : A} → B x`.
  This method assume `fType` is a function type -/
private def processImplicitArg (k : M Expr) : M Expr := do
  if (← get).explicit then
    processExplictArg k
  else
    addImplicitArg k

/-
  Process a `fType` of the form `[x : A] → B x`.
  This method assume `fType` is a function type -/
private def processInstImplicitArg (k : M Expr) : M Expr := do
  if (← get).explicit then
    let isHole ← isNextArgHole
    if isHole then
      /- Recall that if '@' has been used, and the argument is '_', then we still use type class resolution -/
      let arg ← mkFreshExprMVar (← getArgExpectedType) MetavarKind.synthetic
      modify fun s => { s with args := s.args.tail! }
      addInstMVar arg.mvarId!
      addNewArg arg
      k
    else
      processExplictArg k
  else
    let arg ← mkFreshExprMVar (← getArgExpectedType) MetavarKind.synthetic
    addInstMVar arg.mvarId!
    addNewArg arg
    k

/- Return true if there are regular or named arguments to be processed. -/
private def hasArgsToProcess : M Bool := do
  let s ← get
  pure $ !s.args.isEmpty || !s.namedArgs.isEmpty

/- Elaborate function application arguments. -/
partial def main : M Expr := do
  let s ← get
  let fType ← normalizeFunType
  match fType with
  | Expr.forallE binderName _ _ c =>
    let s ← get
    match s.namedArgs.find? fun (namedArg : NamedArg) => namedArg.name == binderName with
    | some namedArg =>
      propagateExpectedType
      eraseNamedArg binderName
      elabAndAddNewArg namedArg.val
      main
    | none          =>
      match c.binderInfo with
      | BinderInfo.implicit     => processImplicitArg main
      | BinderInfo.instImplicit => processInstImplicitArg main
      | _                       => processExplictArg main
  | _ =>
    if (← hasArgsToProcess) then
      synthesizePendingAndNormalizeFunType
      main
    else
      finalize

end ElabAppArgs

private def elabAppArgs (f : Expr) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit ellipsis : Bool) : TermElabM Expr := do
  let fType ← inferType f
  let fType ← instantiateMVars fType
  trace[Elab.app.args]! "explicit: {explicit}, {f} : {fType}"
  unless namedArgs.isEmpty && args.isEmpty do
    tryPostponeIfMVar fType
  ElabAppArgs.main.run' {
    args := args.toList,
    expectedType? := expectedType?,
    explicit := explicit,
    ellipsis := ellipsis,
    namedArgs := namedArgs.toList,
    f := f,
    fType := fType
  }

/-- Auxiliary inductive datatype that represents the resolution of an `LVal`. -/
inductive LValResolution
  | projFn   (baseStructName : Name) (structName : Name) (fieldName : Name)
  | projIdx  (structName : Name) (idx : Nat)
  | const    (baseStructName : Name) (structName : Name) (constName : Name)
  | localRec (baseName : Name) (fullName : Name) (fvar : Expr)
  | getOp    (fullName : Name) (idx : Syntax)

private def throwLValError {α} (e : Expr) (eType : Expr) (msg : MessageData) : TermElabM α :=
  throwError! "{msg}{indentExpr e}\nhas type{indentExpr eType}"

/-- `findMethod? env S fName`.
    1- If `env` contains `S ++ fName`, return `(S, S++fName)`
    2- Otherwise if `env` contains private name `prv` for `S ++ fName`, return `(S, prv)`, o
    3- Otherwise for each parent structure `S'` of  `S`, we try `findMethod? env S' fname` -/
private partial def findMethod? (env : Environment) (structName fieldName : Name) : Option (Name × Name) :=
  let fullName := structName ++ fieldName
  match env.find? fullName with
  | some _ => some (structName, fullName)
  | none   =>
    let fullNamePrv := mkPrivateName env fullName
    match env.find? fullNamePrv with
    | some _ => some (structName, fullNamePrv)
    | none   =>
      if isStructureLike env structName then
        (getParentStructures env structName).findSome? fun parentStructName => findMethod? env parentStructName fieldName
      else
        none

private def resolveLValAux (e : Expr) (eType : Expr) (lval : LVal) : TermElabM LValResolution := do
  match eType.getAppFn, lval with
  | Expr.const structName _ _, LVal.fieldIdx idx =>
    if idx == 0 then
      throwError "invalid projection, index must be greater than 0"
    let env ← getEnv
    unless isStructureLike env structName do
      throwLValError e eType "invalid projection, structure expected"
    let fieldNames := getStructureFields env structName
    if h : idx - 1 < fieldNames.size then
      if isStructure env structName then
        pure $ LValResolution.projFn structName structName (fieldNames.get ⟨idx - 1, h⟩)
      else
        /- `structName` was declared using `inductive` command.
           So, we don't projection functions for it. Thus, we use `Expr.proj` -/
        pure $ LValResolution.projIdx structName (idx - 1)
    else
      throwLValError e eType msg!"invalid projection, structure has only {fieldNames.size} field(s)"
  | Expr.const structName _ _, LVal.fieldName fieldName =>
    let env ← getEnv
    let searchEnv : Unit → TermElabM LValResolution := fun _ => do
      match findMethod? env structName (mkNameSimple fieldName) with
      | some (baseStructName, fullName) => pure $ LValResolution.const baseStructName structName fullName
      | none   =>
        throwLValError e eType
          msg!"invalid field notation, '{fieldName}' is not a valid \"field\" because environment does not contain '{mkNameStr structName fieldName}'"
    -- search local context first, then environment
    let searchCtx : Unit → TermElabM LValResolution := fun _ => do
      let fullName := mkNameStr structName fieldName
      let currNamespace ← getCurrNamespace
      let localName := fullName.replacePrefix currNamespace Name.anonymous
      let lctx ← getLCtx
      match lctx.findFromUserName? localName with
      | some localDecl =>
        if localDecl.binderInfo == BinderInfo.auxDecl then
          /- LVal notation is being used to make a "local" recursive call. -/
          pure $ LValResolution.localRec structName fullName localDecl.toExpr
        else
          searchEnv ()
      | none => searchEnv ()
    if isStructure env structName then
      match findField? env structName (mkNameSimple fieldName) with
      | some baseStructName => pure $ LValResolution.projFn baseStructName structName (mkNameSimple fieldName)
      | none                => searchCtx ()
    else
      searchCtx ()
  | Expr.const structName _ _, LVal.getOp idx =>
    let env ← getEnv
    let fullName := mkNameStr structName "getOp"
    match env.find? fullName with
    | some _ => pure $ LValResolution.getOp fullName idx
    | none   => throwLValError e eType msg!"invalid [..] notation because environment does not contain '{fullName}'"
  | _, LVal.getOp idx =>
    throwLValError e eType "invalid [..] notation, type is not of the form (C ...) where C is a constant"
  | _, _ =>
    throwLValError e eType "invalid field notation, type is not of the form (C ...) where C is a constant"

/- whnfCore + implicit consumption.
   Example: given `e` with `eType := {α : Type} → (fun β => List β) α `, it produces `(e ?m, List ?m)` where `?m` is fresh metavariable. -/
private partial def consumeImplicits (e eType : Expr) : TermElabM (Expr × Expr) := do
  let eType ← whnfCore eType
  match eType with
  | Expr.forallE n d b c =>
    if !c.binderInfo.isExplicit then
      let mvar ← mkFreshExprMVar d
      consumeImplicits (mkApp e mvar) (b.instantiate1 mvar)
    else match d.getOptParamDefault? with
      | some defVal => consumeImplicits (mkApp e defVal) (b.instantiate1 defVal)
      -- TODO: we do not handle autoParams here.
      | _ => pure (e, eType)
  | _ => pure (e, eType)

private partial def resolveLValLoop (lval : LVal) (e eType : Expr) (previousExceptions : Array Exception) : TermElabM (Expr × LValResolution) := do
  let (e, eType) ← consumeImplicits e eType
  tryPostponeIfMVar eType
  try
    let lvalRes ← resolveLValAux e eType lval
    pure (e, lvalRes)
  catch
    | ex@(Exception.error _ _) =>
      let eType? ← unfoldDefinition? eType
      match eType? with
      | some eType => resolveLValLoop lval e eType (previousExceptions.push ex)
      | none       =>
        previousExceptions.forM fun ex => logException ex
        throw ex
    | ex@(Exception.internal _) => throw ex

private def resolveLVal (e : Expr) (lval : LVal) : TermElabM (Expr × LValResolution) := do
  let eType ← inferType e
  resolveLValLoop lval e eType #[]

private partial def mkBaseProjections (baseStructName : Name) (structName : Name) (e : Expr) : TermElabM Expr := do
  let env ← getEnv
  match getPathToBaseStructure? env baseStructName structName with
  | none => throwError "failed to access field in parent structure"
  | some path =>
    let e := e
    for projFunName in path do
      let projFn ← mkConst projFunName
      e ← elabAppArgs projFn #[{ name := `self, val := Arg.expr e }] (args := #[]) (expectedType? := none) (explicit := false) (ellipsis := false)
    return e

/- Auxiliary method for field notation. It tries to add `e` to `args` as the first explicit parameter
   which takes an element of type `(C ...)` where `C` is `baseName`.
   `fullName` is the name of the resolved "field" access function. It is used for reporting errors -/
private def addLValArg (baseName : Name) (fullName : Name) (e : Expr) (args : Array Arg) (namedArgs : Array NamedArg) (fType : Expr)
    : TermElabM (Array Arg) :=
  forallTelescopeReducing fType fun xs _ => do
    let i         := 0
    let namedArgs := namedArgs
    for x in xs do
      let xDecl ← getLocalDecl x.fvarId!
      if xDecl.binderInfo.isExplicit then
        /- If there is named argument with name `xDecl.userName`, then we skip it. -/
        match namedArgs.findIdx? (fun namedArg => namedArg.name == xDecl.userName) with
        | some idx =>
          namedArgs := namedArgs.eraseIdx idx
        | none =>
          let type := xDecl.type
          if type.consumeMData.isAppOf baseName then
            -- found it
            return args.insertAt i (Arg.expr e)
          -- normalize type and try again
          let type ← withReducible $ whnf type
          if type.consumeMData.isAppOf baseName then
            -- found it
            return args.insertAt i (Arg.expr e)
          if i < args.size then
            i := i + 1
          else
            for namedArg in namedArgs do
              throwInvalidNamedArg namedArg fullName
            throwError! "invalid field notation, function '{fullName}' does not have explicit argument with type ({baseName} ...)"
    return args

private def elabAppLValsAux (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) (explicit ellipsis : Bool)
    (f : Expr) (lvals : List LVal) : TermElabM Expr :=
  let rec loop : Expr → List LVal → TermElabM Expr
  | f, []          => elabAppArgs f namedArgs args expectedType? explicit ellipsis
  | f, lval::lvals => do
    let (f, lvalRes) ← resolveLVal f lval
    match lvalRes with
    | LValResolution.projIdx structName idx =>
      let f := mkProj structName idx f
      loop f lvals
    | LValResolution.projFn baseStructName structName fieldName =>
      let f ← mkBaseProjections baseStructName structName f
      let projFn ← mkConst (baseStructName ++ fieldName)
      if lvals.isEmpty then
        let namedArgs ← addNamedArg namedArgs { name := `self, val := Arg.expr f }
        elabAppArgs projFn namedArgs args expectedType? explicit ellipsis
      else
        let f ← elabAppArgs projFn #[{ name := `self, val := Arg.expr f }] #[] (expectedType? := none) (explicit := false) (ellipsis := false)
        loop f lvals
    | LValResolution.const baseStructName structName constName =>
      let f ← if baseStructName != structName then mkBaseProjections baseStructName structName f else pure f
      let projFn ← mkConst constName
      if lvals.isEmpty then
        let projFnType ← inferType projFn
        let args ← addLValArg baseStructName constName f args namedArgs projFnType
        elabAppArgs projFn namedArgs args expectedType? explicit ellipsis
      else
        let f ← elabAppArgs projFn #[] #[Arg.expr f] (expectedType? := none) (explicit := false) (ellipsis := false)
        loop f lvals
    | LValResolution.localRec baseName fullName fvar =>
      if lvals.isEmpty then
        let fvarType ← inferType fvar
        let args ← addLValArg baseName fullName f args namedArgs fvarType
        elabAppArgs fvar namedArgs args expectedType? explicit ellipsis
      else
        let f ← elabAppArgs fvar #[] #[Arg.expr f] (expectedType? := none) (explicit := false) (ellipsis := false)
        loop f lvals
    | LValResolution.getOp fullName idx =>
      let getOpFn ← mkConst fullName
      if lvals.isEmpty then
        let namedArgs ← addNamedArg namedArgs { name := `self, val := Arg.expr f }
        let namedArgs ← addNamedArg namedArgs { name := `idx,  val := Arg.stx idx }
        elabAppArgs getOpFn namedArgs args expectedType? explicit ellipsis
      else
        let f ← elabAppArgs getOpFn #[{ name := `self, val := Arg.expr f }, { name := `idx, val := Arg.stx idx }]
                            #[] (expectedType? := none) (explicit := false) (ellipsis := false)
        loop f lvals
  loop f lvals

private def elabAppLVals (f : Expr) (lvals : List LVal) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit ellipsis : Bool) : TermElabM Expr := do
  if !lvals.isEmpty && explicit then
    throwError "invalid use of field notation with `@` modifier"
  elabAppLValsAux namedArgs args expectedType? explicit ellipsis f lvals

def elabExplicitUnivs (lvls : Array Syntax) : TermElabM (List Level) := do
  lvls.foldrM (fun stx lvls => do pure ((← elabLevel stx)::lvls)) []

/-
Interaction between `errToSorry` and `observing`.

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
    (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) (explicit ellipsis overloaded : Bool) (acc : Array TermElabResult)
    : TermElabM (Array TermElabResult) := do
  match fIdent with
  | Syntax.ident _ _ n preresolved =>
    let funLVals ← withRef fIdent $ resolveName n preresolved fExplicitUnivs
    let overloaded := overloaded || funLVals.length > 1
    -- Set `errToSorry` to `false` if `funLVals` > 1. See comment above about the interaction between `errToSorry` and `observing`.
    withReader (fun ctx => { ctx with errToSorry := funLVals.length == 1 && ctx.errToSorry }) do
      funLVals.foldlM (init := acc) fun acc ⟨f, fields⟩ => do
        let lvals' := fields.map LVal.fieldName
        let s ← observing do
          let e ← elabAppLVals f (lvals' ++ lvals) namedArgs args expectedType? explicit ellipsis
          if overloaded then ensureHasType expectedType? e else pure e
        pure $ acc.push s
  | _ => throwUnsupportedSyntax

private partial def elabAppFn (f : Syntax) (lvals : List LVal) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit ellipsis overloaded : Bool) (acc : Array TermElabResult) : TermElabM (Array TermElabResult) :=
  if f.getKind == choiceKind then
    -- Set `errToSorry` to `false` when processing choice nodes. See comment above about the interaction between `errToSorry` and `observing`.
    withReader (fun ctx => { ctx with errToSorry := false }) do
      f.getArgs.foldlM (fun acc f => elabAppFn f lvals namedArgs args expectedType? explicit ellipsis true acc) acc
  else match_syntax f with
  | `($(e).$idx:fieldIdx) =>
    let idx := idx.isFieldIdx?.get!
    elabAppFn e (LVal.fieldIdx idx :: lvals) namedArgs args expectedType? explicit ellipsis overloaded acc
  | `($e $.$field) => do
     let f ← `($(e).$field)
     elabAppFn f lvals namedArgs args expectedType? explicit ellipsis overloaded acc
  | `($(e).$field:ident) =>
    let newLVals := field.getId.eraseMacroScopes.components.map (fun n => LVal.fieldName (toString n))
    elabAppFn e (newLVals ++ lvals) namedArgs args expectedType? explicit ellipsis overloaded acc
  | `($e[$idx]) =>
    elabAppFn e (LVal.getOp idx :: lvals) namedArgs args expectedType? explicit ellipsis overloaded acc
  | `($id:ident@$t:term) =>
    throwError "unexpected occurrence of named pattern"
  | `($id:ident) => do
    elabAppFnId id [] lvals namedArgs args expectedType? explicit ellipsis overloaded acc
  | `($id:ident.{$us*}) => do
    let us ← elabExplicitUnivs us.getSepElems
    elabAppFnId id us lvals namedArgs args expectedType? explicit ellipsis overloaded acc
  | `(@$id:ident) =>
    elabAppFn id lvals namedArgs args expectedType? (explicit := true) ellipsis overloaded acc
  | `(@$id:ident.{$us*}) =>
    elabAppFn (f.getArg 1) lvals namedArgs args expectedType? (explicit := true) ellipsis overloaded acc
  | `(@$t)     => throwUnsupportedSyntax -- invalid occurrence of `@`
  | `(_)       => throwError "placeholders '_' cannot be used where a function is expected"
  | _ => do
    let catchPostpone := !overloaded
    /- If we are processing a choice node, then we should use `catchPostpone == false` when elaborating terms.
       Recall that `observing` does not catch `postponeExceptionId`. -/
    if lvals.isEmpty && namedArgs.isEmpty && args.isEmpty then
      /- Recall that elabAppFn is used for elaborating atomics terms **and** choice nodes that may contain
         arbitrary terms. If they are not being used as a function, we should elaborate using the expectedType. -/
      let s ←
        if overloaded then
          observing $ elabTermEnsuringType f expectedType? catchPostpone
        else
          observing $ elabTerm f expectedType?
      pure $ acc.push s
    else
      let s ← observing do
        let f ← elabTerm f none catchPostpone
        let e ← elabAppLVals f lvals namedArgs args expectedType? explicit ellipsis
        if overloaded then ensureHasType expectedType? e else pure e
      pure $ acc.push s

private def isSuccess (candidate : TermElabResult) : Bool :=
  match candidate with
  | EStateM.Result.ok _ _ => true
  | _ => false

private def getSuccess (candidates : Array TermElabResult) : Array TermElabResult :=
  candidates.filter isSuccess

private def toMessageData (ex : Exception) : TermElabM MessageData := do
  let pos ← getRefPos
  match ex.getRef.getPos with
  | none       => pure ex.toMessageData
  | some exPos =>
    if pos == exPos then
      pure ex.toMessageData
    else
      let fileMap ← MonadLog.getFileMap -- Remove `MonadLog.` it is a workaround for old frontend
      let exPosition := fileMap.toPosition exPos
      pure msg!"{exPosition.line}:{exPosition.column} {ex.toMessageData}"

private def toMessageList (msgs : Array MessageData) : MessageData :=
  indentD (MessageData.joinSep msgs.toList (Format.line ++ Format.line))

private def mergeFailures {α} (failures : Array TermElabResult) : TermElabM α := do
  let msgs ← failures.mapM fun failure =>
    match failure with
    | EStateM.Result.ok _ _     => unreachable!
    | EStateM.Result.error ex _ => toMessageData ex
  throwError! "overloaded, errors {toMessageList msgs}"

private def elabAppAux (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (ellipsis : Bool) (expectedType? : Option Expr) : TermElabM Expr := do
  let candidates ← elabAppFn f [] namedArgs args expectedType? (explicit := false) (ellipsis := ellipsis) (overloaded := false) #[]
  if candidates.size == 1 then
    applyResult candidates[0]
  else
    let successes := getSuccess candidates
    if successes.size == 1 then
      let e ← applyResult successes[0]
      pure e
    else if successes.size > 1 then
      let lctx ← getLCtx
      let opts ← getOptions
      let msgs : Array MessageData := successes.map fun success => match success with
        | EStateM.Result.ok e s => MessageData.withContext { env := s.core.env, mctx := s.meta.mctx, lctx := lctx, opts := opts } e
        | _                     => unreachable!
      throwErrorAt! f "ambiguous, possible interpretations {toMessageList msgs}"
    else
      withRef f $ mergeFailures candidates

partial def expandApp (stx : Syntax) (pattern := false) : TermElabM (Syntax × Array NamedArg × Array Arg × Bool) := do
  let f    := stx[0]
  let args := stx[1].getArgs
  let (args, ellipsis) :=
    if args.back.isOfKind `Lean.Parser.Term.ellipsis then
      (args.pop, true)
    else
      (args, false)
  let (namedArgs, args) ← args.foldlM (init := (#[], #[])) fun (namedArgs, args) stx => do
    if stx.getKind == `Lean.Parser.Term.namedArgument then
      -- tparser! try ("(" >> ident >> " := ") >> termParser >> ")"
      let name := stx[1].getId.eraseMacroScopes
      let val  := stx[3]
      let namedArgs ← addNamedArg namedArgs { ref := stx, name := name, val := Arg.stx val }
      pure (namedArgs, args)
    else if stx.getKind == `Lean.Parser.Term.ellipsis then
      throwErrorAt stx "unexpected '..'"
    else
      pure (namedArgs, args.push $ Arg.stx stx)
  pure (f, namedArgs, args, ellipsis)

@[builtinTermElab app] def elabApp : TermElab := fun stx expectedType? =>
  withoutPostponingUniverseConstraints do
    let (f, namedArgs, args, ellipsis) ← expandApp stx
    elabAppAux f namedArgs args (ellipsis := ellipsis) expectedType?

private def elabAtom : TermElab := fun stx expectedType? =>
  elabAppAux stx #[] #[] (ellipsis := false) expectedType?

@[builtinTermElab ident] def elabIdent : TermElab := elabAtom
@[builtinTermElab namedPattern] def elabNamedPattern : TermElab := elabAtom
@[builtinTermElab explicitUniv] def elabExplicitUniv : TermElab := elabAtom
@[builtinTermElab dollarProj] def expandDollarProj : TermElab := elabAtom

@[builtinTermElab explicit] def elabExplicit : TermElab := fun stx expectedType? =>
  match_syntax stx with
  | `(@$id:ident)        => elabAtom stx expectedType?  -- Recall that `elabApp` also has support for `@`
  | `(@$id:ident.{$us*}) => elabAtom stx expectedType?
  | `(@($t))             => elabTermWithoutImplicitLambdas t expectedType?    -- `@` is being used just to disable implicit lambdas
  | `(@$t)               => elabTermWithoutImplicitLambdas t expectedType?    -- `@` is being used just to disable implicit lambdas
  | _                    => throwUnsupportedSyntax

@[builtinTermElab choice] def elabChoice : TermElab := elabAtom
@[builtinTermElab proj] def elabProj : TermElab := elabAtom
@[builtinTermElab arrayRef] def elabArrayRef : TermElab := elabAtom

builtin_initialize
  registerTraceClass `Elab.app

end Lean.Elab.Term
