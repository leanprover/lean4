/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Term

namespace Lean
namespace Elab
namespace Term
/--
  Auxiliary inductive datatype for combining unelaborated syntax
  and already elaborated expressions. It is used to elaborate applications. -/
inductive Arg
| stx  (val : Syntax)
| expr (val : Expr)

instance Arg.inhabited : Inhabited Arg := ⟨Arg.stx (arbitrary _)⟩

instance Arg.hasToString : HasToString Arg :=
⟨fun arg => match arg with
  | Arg.stx  val => toString val
  | Arg.expr val => toString val⟩

/-- Named arguments created using the notation `(x := val)` -/
structure NamedArg :=
(name : Name) (val : Arg)

instance NamedArg.hasToString : HasToString NamedArg :=
⟨fun s => "(" ++ toString s.name ++ " := " ++ toString s.val ++ ")"⟩

instance NamedArg.inhabited : Inhabited NamedArg := ⟨{ name := arbitrary _, val := arbitrary _ }⟩

/--
  Add a new named argument to `namedArgs`, and throw an error if it already contains a named argument
  with the same name. -/
def addNamedArg (ref : Syntax) (namedArgs : Array NamedArg) (namedArg : NamedArg) : TermElabM (Array NamedArg) := do
when (namedArgs.any $ fun namedArg' => namedArg.name == namedArg'.name) $
  throwError ref ("argument '" ++ toString namedArg.name ++ "' was already set");
pure $ namedArgs.push namedArg

def synthesizeAppInstMVars (ref : Syntax) (instMVars : Array MVarId) : TermElabM Unit :=
instMVars.forM $ fun mvarId =>
  unlessM (synthesizeInstMVarCore ref mvarId) $
    registerSyntheticMVar ref mvarId SyntheticMVarKind.typeClass

private def ensureArgType (ref : Syntax) (f : Expr) (arg : Expr) (expectedType : Expr) : TermElabM Expr := do
argType ← inferType ref arg;
ensureHasTypeAux ref expectedType argType arg f

private def elabArg (ref : Syntax) (f : Expr) (arg : Arg) (expectedType : Expr) : TermElabM Expr :=
match arg with
| Arg.expr val => ensureArgType ref f val expectedType
| Arg.stx val  => do
  val ← elabTerm val expectedType;
  ensureArgType ref f val expectedType

private def mkArrow (d b : Expr) : TermElabM Expr := do
n ← mkFreshAnonymousName;
pure $ Lean.mkForall n BinderInfo.default d b

/-
  Relevant definitions:
  ```
  class CoeFun (α : Sort u) (γ : α → outParam (Sort v))
  abbrev coeFun {α : Sort u} {γ : α → Sort v} (a : α) [CoeFun α γ] : γ a
  ``` -/
private def tryCoeFun (ref : Syntax) (α : Expr) (a : Expr) : TermElabM Expr := do
v ← mkFreshLevelMVar ref;
type ← mkArrow α (mkSort v);
γ ← mkFreshExprMVar ref type;
u ← getLevel ref α;
let coeFunInstType := mkAppN (Lean.mkConst `CoeFun [u, v]) #[α, γ];
mvar ← mkFreshExprMVar ref coeFunInstType MetavarKind.synthetic;
let mvarId := mvar.mvarId!;
synthesized ←
  catch (withoutMacroStackAtErr $ synthesizeInstMVarCore ref mvarId)
  (fun ex =>
    match ex with
    | Exception.ex (Elab.Exception.error errMsg) => throwError ref ("function expected" ++ Format.line ++ errMsg.data)
    | _ => throwError ref "function expected");
if synthesized then
  pure $ mkAppN (Lean.mkConst `coeFun [u, v]) #[α, γ, a, mvar]
else
  throwError ref "function expected"

/-- Auxiliary structure used to elaborate function application arguments. -/
structure ElabAppArgsCtx :=
(ref           : Syntax)
(args          : Array Arg)
(expectedType? : Option Expr)
(explicit      : Bool)                -- if true, all arguments are treated as explicit
(argIdx        : Nat := 0)            -- position of next explicit argument to be processed
(namedArgs     : Array NamedArg)      -- remaining named arguments to be processed
(instMVars     : Array MVarId := #[]) -- metavariables for the instance implicit arguments that have already been processed
(typeMVars     : Array MVarId := #[]) -- metavariables for implicit arguments of the form `{α : Sort u}` that have already been processed
(foundExplicit : Bool := false)       -- true if an explicit argument has already been processed

private def isAutoOrOptParam (type : Expr) : Bool :=
-- TODO: add auto param
type.getOptParamDefault?.isSome

/- Auxiliary function for retrieving the resulting type of a function application.
   See `propagateExpectedType`. -/
private partial def getForallBody : Nat → Array NamedArg → Expr → Option Expr
| i, namedArgs, type@(Expr.forallE n d b c) =>
  match namedArgs.findIdx? (fun namedArg => namedArg.name == n) with
  | some idx => getForallBody i (namedArgs.eraseIdx idx) b
  | none     =>
    if !c.binderInfo.isExplicit then
      getForallBody i namedArgs b
    else if i > 0 then
      getForallBody (i-1) namedArgs b
    else if isAutoOrOptParam d then
      getForallBody i namedArgs b
    else
      some type
| i, namedArgs, type => if i == 0 && namedArgs.isEmpty then some type else none

private def hasTypeMVar (ctx : ElabAppArgsCtx) (type : Expr) : Bool :=
(type.findMVar? (fun mvarId => ctx.typeMVars.contains mvarId)).isSome

private def hasOnlyTypeMVar (ctx : ElabAppArgsCtx) (type : Expr) : Bool :=
(type.findMVar? (fun mvarId => !ctx.typeMVars.contains mvarId)).isNone

/-
  Auxiliary method for propagating the expected type. We call it as soon as we find the first explict
  argument. The goal is to propagate the expected type in applications of functions such as
  ```lean
  HasAdd.add {α : Type u} : α → α → α
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
private def propagateExpectedType (ctx : ElabAppArgsCtx) (eType : Expr) : TermElabM Unit :=
unless (ctx.explicit || ctx.foundExplicit || ctx.typeMVars.isEmpty)  $ do
  match ctx.expectedType? with
  | none              => pure ()
  | some expectedType =>
    let numRemainingArgs := ctx.args.size - ctx.argIdx;
    match getForallBody numRemainingArgs ctx.namedArgs eType with
    | none           => pure ()
    | some eTypeBody =>
      unless eTypeBody.hasLooseBVars $
      when (hasTypeMVar ctx eTypeBody && hasOnlyTypeMVar ctx eTypeBody) $ do
        isDefEq ctx.ref expectedType eTypeBody;
        pure ()

/- Elaborate function application arguments. -/
private partial def elabAppArgsAux : ElabAppArgsCtx → Expr → Expr → TermElabM Expr
| ctx, e, eType => do
  let finalize : Unit → TermElabM Expr := fun _ => do {
    -- all user explicit arguments have been consumed
    match ctx.expectedType? with
    | none              => pure ()
    | some expectedType => do {
      -- Try to propagate expected type. Ignore if types are not definitionally equal, caller must handle it.
      isDefEq ctx.ref expectedType eType;
      pure ()
    };
    synthesizeAppInstMVars ctx.ref ctx.instMVars;
    pure e
  };
  eType ← whnfForall ctx.ref eType;
  match eType with
  | Expr.forallE n d b c =>
    match ctx.namedArgs.findIdx? (fun namedArg => namedArg.name == n) with
    | some idx => do
      let arg := ctx.namedArgs.get! idx;
      let namedArgs := ctx.namedArgs.eraseIdx idx;
      argElab ← elabArg ctx.ref e arg.val d;
      propagateExpectedType ctx eType;
      elabAppArgsAux { foundExplicit := true, namedArgs := namedArgs, .. ctx } (mkApp e argElab) (b.instantiate1 argElab)
    | none =>
      let processExplictArg : Unit → TermElabM Expr := fun _ => do {
        propagateExpectedType ctx eType;
        let ctx := { foundExplicit := true, .. ctx };
        if h : ctx.argIdx < ctx.args.size then do
          argElab ← elabArg ctx.ref e (ctx.args.get ⟨ctx.argIdx, h⟩) d;
          elabAppArgsAux { argIdx := ctx.argIdx + 1, .. ctx } (mkApp e argElab) (b.instantiate1 argElab)
        else match ctx.explicit, d.getOptParamDefault? with
          | false, some defVal => elabAppArgsAux ctx (mkApp e defVal) (b.instantiate1 defVal)
          | _, _               =>
            -- TODO: tactic auto param
            if ctx.namedArgs.isEmpty then
              finalize ()
            else
              throwError ctx.ref ("explicit parameter '" ++ n ++ "' is missing, unused named arguments " ++ toString (ctx.namedArgs.map $ fun narg => narg.name))
      };
      if ctx.explicit then
        processExplictArg ()
      else match c.binderInfo with
        | BinderInfo.implicit => do
          a ← mkFreshExprMVar ctx.ref d;
          typeMVars ← condM (isType ctx.ref a) (pure $ ctx.typeMVars.push a.mvarId!) (pure ctx.typeMVars);
          elabAppArgsAux { typeMVars := typeMVars, .. ctx } (mkApp e a) (b.instantiate1 a)
        | BinderInfo.instImplicit => do
          a ← mkFreshExprMVar ctx.ref d MetavarKind.synthetic;
          elabAppArgsAux { instMVars := ctx.instMVars.push a.mvarId!, .. ctx } (mkApp e a) (b.instantiate1 a)
        | _ =>
          processExplictArg ()
  | _ =>
    if ctx.namedArgs.isEmpty && ctx.argIdx == ctx.args.size then
      finalize ()
    else do
      e ← tryCoeFun ctx.ref eType e;
      eType ← inferType ctx.ref e;
      elabAppArgsAux ctx e eType

private def elabAppArgs (ref : Syntax) (f : Expr) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit : Bool) : TermElabM Expr := do
fType ← inferType ref f;
fType ← instantiateMVars ref fType;
tryPostponeIfMVar fType;
elabAppArgsAux {ref := ref, args := args, expectedType? := expectedType?, explicit := explicit, namedArgs := namedArgs } f fType

/-- Auxiliary inductive datatype that represents the resolution of an `LVal`. -/
inductive LValResolution
| projFn   (baseStructName : Name) (structName : Name) (fieldName : Name)
| projIdx  (structName : Name) (idx : Nat)
| const    (baseName : Name) (constName : Name)
| localRec (baseName : Name) (fullName : Name) (fvar : Expr)
| getOp    (fullName : Name) (idx : Syntax)

private def throwLValError {α} (ref : Syntax) (e : Expr) (eType : Expr) (msg : MessageData) : TermElabM α :=
throwError ref $ msg ++ indentExpr e ++ Format.line ++ "has type" ++ indentExpr eType

private def resolveLValAux (ref : Syntax) (e : Expr) (eType : Expr) (lval : LVal) : TermElabM LValResolution :=
match eType.getAppFn, lval with
| Expr.const structName _ _, LVal.fieldIdx idx => do
  when (idx == 0) $
    throwError ref "invalid projection, index must be greater than 0";
  env ← getEnv;
  unless (isStructureLike env structName) $
    throwLValError ref e eType "invalid projection, structure expected";
  let fieldNames := getStructureFields env structName;
  if h : idx - 1 < fieldNames.size then
    if isStructure env structName then
      pure $ LValResolution.projFn structName structName (fieldNames.get ⟨idx - 1, h⟩)
    else
      /- `structName` was declared using `inductive` command.
         So, we don't projection functions for it. Thus, we use `Expr.proj` -/
      pure $ LValResolution.projIdx structName (idx - 1)
  else
    throwLValError ref e eType ("invalid projection, structure has only " ++ toString fieldNames.size ++ " field(s)")
| Expr.const structName _ _, LVal.fieldName fieldName => do
  env ← getEnv;
  let searchEnv (fullName : Name) : TermElabM LValResolution := do {
    match env.find? fullName with
    | some _ => pure $ LValResolution.const structName fullName
    | none   => throwLValError ref e eType $
      "invalid field notation, '" ++ fieldName ++ "' is not a valid \"field\" because environment does not contain '" ++ fullName ++ "'"
  };
  -- search local context first, then environment
  let searchCtx : Unit → TermElabM LValResolution := fun _ => do {
    let fullName := structName ++ fieldName;
    currNamespace ← getCurrNamespace;
    let localName := fullName.replacePrefix currNamespace Name.anonymous;
    lctx ← getLCtx;
    match lctx.findFromUserName? localName with
    | some localDecl =>
      if localDecl.binderInfo == BinderInfo.auxDecl then
        /- LVal notation is being used to make a "local" recursive call. -/
        pure $ LValResolution.localRec structName fullName localDecl.toExpr
      else
        searchEnv fullName
    | none => searchEnv fullName
  };
  if isStructure env structName then
    match findField? env structName fieldName with
    | some baseStructName => pure $ LValResolution.projFn baseStructName structName fieldName
    | none                => searchCtx ()
  else
    searchCtx ()
| Expr.const structName _ _, LVal.getOp idx => do
  env ← getEnv;
  let fullName := mkNameStr structName "getOp";
  match env.find? fullName with
  | some _ => pure $ LValResolution.getOp fullName idx
  | none   => throwLValError ref e eType $ "invalid [..] notation because environment does not contain '" ++ fullName ++ "'"
| _, LVal.getOp idx =>
  throwLValError ref e eType "invalid [..] notation, type is not of the form (C ...) where C is a constant"
| _, _ =>
  throwLValError ref e eType "invalid field notation, type is not of the form (C ...) where C is a constant"

private partial def resolveLValLoop (ref : Syntax) (e : Expr) (lval : LVal) : Expr → Array Message → TermElabM LValResolution
| eType, previousExceptions => do
  eType ← whnfCore ref eType;
  tryPostponeIfMVar eType;
  catch (resolveLValAux ref e eType lval)
    (fun ex =>
      match ex with
      | Exception.postpone                            => throw ex
      | Exception.ex Elab.Exception.unsupportedSyntax => throw ex
      | Exception.ex (Elab.Exception.error errMsg)    => do
        eType? ← unfoldDefinition? ref eType;
        match eType? with
        | some eType => resolveLValLoop eType (previousExceptions.push errMsg)
        | none       => do
          previousExceptions.forM $ fun ex =>
            logMessage errMsg;
          throw (Exception.ex (Elab.Exception.error errMsg)))

private def resolveLVal (ref : Syntax) (e : Expr) (lval : LVal) : TermElabM LValResolution := do
eType ← inferType ref e;
resolveLValLoop ref e lval eType #[]

private partial def mkBaseProjections (ref : Syntax) (baseStructName : Name) (structName : Name) (e : Expr) : TermElabM Expr := do
env ← getEnv;
match getPathToBaseStructure? env baseStructName structName with
| none => throwError ref "failed to access field in parent structure"
| some path =>
  path.foldlM
    (fun e projFunName => do
      projFn ← mkConst ref projFunName;
      elabAppArgs ref projFn #[{ name := `self, val := Arg.expr e }] #[] none false)
    e

/- Auxiliary method for field notation. It tries to add `e` to `args` as the first explicit parameter
   which takes an element of type `(C ...)` where `C` is `baseName`.
   `fullName` is the name of the resolved "field" access function. It is used for reporting errors -/
private def addLValArg (ref : Syntax) (baseName : Name) (fullName : Name) (e : Expr) (args : Array Arg) : Nat → Array NamedArg → Expr → TermElabM (Array Arg)
| i, namedArgs, Expr.forallE n d b c =>
  if !c.binderInfo.isExplicit then
    addLValArg i namedArgs b
  else
    /- If there is named argument with name `n`, then we should skip. -/
    match namedArgs.findIdx? (fun namedArg => namedArg.name == n) with
    | some idx => do
      let namedArgs := namedArgs.eraseIdx idx;
      addLValArg i namedArgs b
    | none => do
      if d.consumeMData.isAppOf baseName then
        pure $ args.insertAt i (Arg.expr e)
      else if i < args.size then
        addLValArg (i+1) namedArgs b
      else
        throwError ref $ "invalid field notation, insufficient number of arguments for '" ++ fullName ++ "'"
| _, _, fType =>
  throwError ref $
    "invalid field notation, function '" ++ fullName ++ "' does not have explicit argument with type (" ++ baseName ++ " ...)"

private def elabAppLValsAux (ref : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) (explicit : Bool)
    : Expr → List LVal → TermElabM Expr
| f, []          => elabAppArgs ref f namedArgs args expectedType? explicit
| f, lval::lvals => do
  lvalRes ← resolveLVal ref f lval;
  match lvalRes with
  | LValResolution.projIdx structName idx =>
    let f := mkProj structName idx f;
    elabAppLValsAux f lvals
  | LValResolution.projFn baseStructName structName fieldName => do
    f ← mkBaseProjections ref baseStructName structName f;
    projFn ← mkConst ref (baseStructName ++ fieldName);
    if lvals.isEmpty then do
      namedArgs ← addNamedArg ref namedArgs { name := `self, val := Arg.expr f };
      elabAppArgs ref projFn namedArgs args expectedType? explicit
    else do
      f ← elabAppArgs ref projFn #[{ name := `self, val := Arg.expr f }] #[] none false;
      elabAppLValsAux f lvals
  | LValResolution.const baseName constName => do
    projFn ← mkConst ref constName;
    if lvals.isEmpty then do
      projFnType ← inferType ref projFn;
      args ← addLValArg ref baseName constName f args 0 namedArgs projFnType;
      elabAppArgs ref projFn namedArgs args expectedType? explicit
    else do
      f ← elabAppArgs ref projFn #[] #[Arg.expr f] none false;
      elabAppLValsAux f lvals
  | LValResolution.localRec baseName fullName fvar =>
    if lvals.isEmpty then do
      fvarType ← inferType ref fvar;
      args ← addLValArg ref baseName fullName f args 0 namedArgs fvarType;
      elabAppArgs ref fvar namedArgs args expectedType? explicit
    else do
      f ← elabAppArgs ref fvar #[] #[Arg.expr f] none false;
      elabAppLValsAux f lvals
  | LValResolution.getOp fullName idx => do
    getOpFn ← mkConst ref fullName;
    if lvals.isEmpty then do
      namedArgs ← addNamedArg ref namedArgs { name := `self, val := Arg.expr f };
      namedArgs ← addNamedArg ref namedArgs { name := `idx, val := Arg.stx idx };
      elabAppArgs ref getOpFn namedArgs args expectedType? explicit
    else do
      f ← elabAppArgs ref getOpFn #[{ name := `self, val := Arg.expr f }, { name := `idx, val := Arg.stx idx }] #[] none false;
      elabAppLValsAux f lvals

private def elabAppLVals (ref : Syntax) (f : Expr) (lvals : List LVal) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit : Bool) : TermElabM Expr := do
when (!lvals.isEmpty && explicit) $ throwError ref "invalid use of field notation with `@` modifier";
elabAppLValsAux ref namedArgs args expectedType? explicit f lvals

def elabExplicitUniv (stx : Syntax) : TermElabM (List Level) := do
let lvls := stx.getArg 1;
lvls.foldSepRevArgsM
  (fun stx lvls => do
    lvl ← elabLevel stx;
    pure (lvl::lvls))
  []

private partial def elabAppFnId (ref : Syntax) (fIdent : Syntax) (fExplicitUnivs : List Level) (lvals : List LVal)
    (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) (explicit : Bool) (acc : Array TermElabResult)
    : TermElabM (Array TermElabResult) :=
match fIdent with
| Syntax.ident _ _ n preresolved => do
  funLVals ← resolveName fIdent n preresolved fExplicitUnivs;
  funLVals.foldlM
    (fun acc ⟨f, fields⟩ => do
      let lvals' := fields.map LVal.fieldName;
      s ← observing $ elabAppLVals ref f (lvals' ++ lvals) namedArgs args expectedType? explicit;
      pure $ acc.push s)
    acc
| _ => throwUnsupportedSyntax

private partial def elabAppFn (ref : Syntax) : Syntax → List LVal → Array NamedArg → Array Arg → Option Expr → Bool → Array TermElabResult → TermElabM (Array TermElabResult)
| f, lvals, namedArgs, args, expectedType?, explicit, acc =>
  if f.isIdent then
    -- A raw identifier is not a valid Term. Recall that `Term.id` is defined as `parser! ident >> optional (explicitUniv <|> namedPattern)`
    -- We handle it here to make macro development more comfortable.
    elabAppFnId ref f [] lvals namedArgs args expectedType? explicit acc
  else if f.getKind == choiceKind then
    f.getArgs.foldlM (fun acc f => elabAppFn f lvals namedArgs args expectedType? explicit acc) acc
  else match_syntax f with
  | `($(e).$idx:fieldIdx) =>
    let idx := idx.isFieldIdx?.get!;
    elabAppFn (f.getArg 0) (LVal.fieldIdx idx :: lvals) namedArgs args expectedType? explicit acc
  | `($(e).$field:ident) =>
    let newLVals := field.getId.components.map (fun n => LVal.fieldName (toString n));
    elabAppFn (f.getArg 0) (newLVals ++ lvals) namedArgs args expectedType? explicit acc
  | `($e[$idx]) =>
    elabAppFn e (LVal.getOp idx :: lvals) namedArgs args expectedType? explicit acc
  | `($id:ident$us:explicitUniv*) => do
    -- Remark: `id.<namedPattern>` should already have been expanded
    us ← if us.isEmpty then pure [] else elabExplicitUniv (us.get! 0);
    elabAppFnId ref id us lvals namedArgs args expectedType? explicit acc
  | `(@$f) =>
    elabAppFn f lvals namedArgs args expectedType? true acc
  | _ => do
    s ← observing $ do {
      f ← elabTerm f none;
      elabAppLVals ref f lvals namedArgs args expectedType? explicit
    };
    pure $ acc.push s

private def getSuccess (candidates : Array TermElabResult) : Array TermElabResult :=
candidates.filter $ fun c => match c with
  | EStateM.Result.ok _ _ => true
  | _ => false

private def toMessageData (msg : Message) (stx : Syntax) : TermElabM MessageData := do
strPos ← getPos stx;
pos ← getPosition strPos;
if pos == msg.pos then
  pure msg.data
else
  pure $ toString msg.pos.line ++ ":" ++ toString msg.pos.column ++ " " ++ msg.data

private def mergeFailures {α} (failures : Array TermElabResult) (stx : Syntax) : TermElabM α := do
msgs ← failures.mapM $ fun failure =>
  match failure with
  | EStateM.Result.ok _ _         => unreachable!
  | EStateM.Result.error errMsg s => toMessageData errMsg stx;
throwError stx ("overloaded, errors " ++ MessageData.ofArray msgs)

private def elabAppAux (ref : Syntax) (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) : TermElabM Expr := do
/- TODO: if `f` contains `choice` or overloaded symbols, `mayPostpone == true`, and `expectedType? == some ?m` where `?m` is not assigned,
   then we should postpone until `?m` is assigned.
   Another (more expensive) option is: execute, and if successes > 1, `mayPostpone == true`, and `expectedType? == some ?m` where `?m` is not assigned,
   then we postpone `elabAppAux`. It is more expensive because we would have to re-elaborate the whole thing after we assign `?m`.
   We **can't** continue from `TermElabResult` since they contain a snapshot of the state, and state has changed. -/
candidates ← elabAppFn ref f [] namedArgs args expectedType? false #[];
if candidates.size == 1 then
  applyResult $ candidates.get! 0
else
  let successes := getSuccess candidates;
  if successes.size == 1 then
    applyResult $ successes.get! 0
  else if successes.size > 1 then do
    lctx ← getLCtx;
    opts ← getOptions;
    let msgs : Array MessageData := successes.map $ fun success => match success with
      | EStateM.Result.ok e s => MessageData.withContext { env := s.env, mctx := s.mctx, lctx := lctx, opts := opts } e
      | _                     => unreachable!;
    throwError f ("ambiguous, possible interpretations " ++ MessageData.ofArray msgs)
  else
    mergeFailures candidates f

private partial def expandApp (stx : Syntax) : TermElabM (Syntax × Array NamedArg × Array Arg) := do
let f    := stx.getArg 0;
(namedArgs, args) ← (stx.getArg 1).getArgs.foldlM
  (fun (acc : Array NamedArg × Array Arg) (stx : Syntax) => do
    let (namedArgs, args) := acc;
    if stx.getKind == `Lean.Parser.Term.namedArgument then do
      -- tparser! try ("(" >> ident >> " := ") >> termParser >> ")"
      let name := (stx.getArg 1).getId;
      let val  := stx.getArg 3;
      namedArgs ← addNamedArg stx namedArgs { name := name, val := Arg.stx val };
      pure (namedArgs, args)
    else
      pure (namedArgs, args.push $ Arg.stx stx))
  (#[], #[]);
pure (f, namedArgs, args)

@[builtinTermElab app] def elabApp : TermElab :=
fun stx expectedType? => do
  (f, namedArgs, args) ← expandApp stx;
  elabAppAux stx f namedArgs args expectedType?

def elabAtom : TermElab :=
fun stx expectedType? => elabAppAux stx stx #[] #[] expectedType?

@[builtinTermElab «id»] def elabId : TermElab := elabAtom
@[builtinTermElab explicit] def elabExplicit : TermElab := elabAtom
@[builtinTermElab choice] def elabChoice : TermElab := elabAtom
@[builtinTermElab proj] def elabProj : TermElab := elabAtom
@[builtinTermElab arrayRef] def elabArrayRef : TermElab := elabAtom
/- A raw identiier is not a valid term,
   but it is nice to have a handler for them because it allows `macros` to insert them into terms. -/
@[builtinTermElab ident] def elabRawIdent : TermElab := elabAtom

@[builtinTermElab sortApp] def elabSortApp : TermElab :=
fun stx _ => do
  u ← elabLevel (stx.getArg 1);
  if (stx.getArg 0).getKind == `Lean.Parser.Term.sort then do
    pure $ mkSort u
  else
    pure $ mkSort (mkLevelSucc u)

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.app;
pure ()

end Term
end Elab
end Lean
