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

/-- Consume parameters of the form `(x : A := val)` and `(x : A . tactic)` -/
private def consumeDefaultParams (ref : Syntax) : Expr → Expr → TermElabM Expr
| eType, e =>
  -- TODO
  pure e

private def synthesizeAppInstMVars (ref : Syntax) (instMVars : Array MVarId) : TermElabM Unit :=
instMVars.forM $ fun mvarId =>
  unlessM (synthesizeInstMVarCore ref mvarId) $
    registerSyntheticMVar ref mvarId SyntheticMVarKind.typeClass

private def elabArg (ref : Syntax) (arg : Arg) (expectedType : Expr) : TermElabM Expr :=
match arg with
| Arg.expr val => do
  valType ← inferType ref val;
  ensureHasType ref expectedType valType val
| Arg.stx val  => do
  val ← elabTerm val expectedType;
  valType ← inferType ref val;
  ensureHasType ref expectedType valType val

private partial def elabAppArgsAux (ref : Syntax) (args : Array Arg) (expectedType? : Option Expr) (explicit : Bool)
    : Nat → Array NamedArg → Array MVarId → Expr → Expr → TermElabM Expr
| argIdx, namedArgs, instMVars, eType, e => do
  let finalize : Unit → TermElabM Expr := fun _ => do {
    -- all user explicit arguments have been consumed
    e ← if explicit then pure e else consumeDefaultParams ref eType e;
    e ← ensureHasType ref expectedType? eType e;
    synthesizeAppInstMVars ref instMVars;
    pure e
  };
  eType ← whnfForall ref eType;
  match eType with
  | Expr.forallE n d b c =>
    match namedArgs.findIdx? (fun namedArg => namedArg.name == n) with
    | some idx => do
      let arg := namedArgs.get! idx;
      let namedArgs := namedArgs.eraseIdx idx;
      argElab ← elabArg ref arg.val d;
      elabAppArgsAux argIdx namedArgs instMVars (b.instantiate1 argElab) (mkApp e argElab)
    | none =>
      let processExplictArg : Unit → TermElabM Expr := fun _ => do {
        if h : argIdx < args.size then do
          argElab ← elabArg ref (args.get ⟨argIdx, h⟩) d;
          elabAppArgsAux (argIdx + 1) namedArgs instMVars (b.instantiate1 argElab) (mkApp e argElab)
        else if namedArgs.isEmpty then
          finalize ()
        else
          throwError ref ("explicit parameter '" ++ n ++ "' is missing, unused named arguments " ++ toString (namedArgs.map $ fun narg => narg.name))
      };
      if explicit then
        processExplictArg ()
      else match c.binderInfo with
        | BinderInfo.implicit => do
          a ← mkFreshExprMVar ref d;
          elabAppArgsAux argIdx namedArgs instMVars (b.instantiate1 a) (mkApp e a)
        | BinderInfo.instImplicit => do
          a ← mkFreshExprMVar ref d MetavarKind.synthetic;
          elabAppArgsAux argIdx namedArgs (instMVars.push a.mvarId!) (b.instantiate1 a) (mkApp e a)
        | _ =>
          processExplictArg ()
  | _ =>
    if namedArgs.isEmpty && argIdx == args.size then
      finalize ()
    else
      -- TODO: try `HasCoeToFun`
      throwError ref "too many arguments"

private def elabAppArgs (ref : Syntax) (f : Expr) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit : Bool) : TermElabM Expr := do
fType ← inferType ref f;
fType ← instantiateMVars ref fType;
tryPostponeIfMVar fType;
let argIdx    := 0;
let instMVars := #[];
elabAppArgsAux ref args expectedType? explicit argIdx namedArgs instMVars fType f

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

private partial def resolveLValLoop (ref : Syntax) (e : Expr) (lval : LVal) : Expr → Array Elab.Exception → TermElabM LValResolution
| eType, previousExceptions => do
  eType ← whnfCore ref eType;
  tryPostponeIfMVar eType;
  catch (resolveLValAux ref e eType lval)
    (fun ex =>
      match ex with
      | Exception.postpone => throw ex
      | Exception.error ex => do
        eType? ← unfoldDefinition? ref eType;
        match eType? with
        | some eType => resolveLValLoop eType (previousExceptions.push ex)
        | none       => do
          previousExceptions.forM $ fun ex =>
            logMessage ex;
          throw (Exception.error ex))

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
    | none =>
      if d.isAppOf baseName then
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

private partial def elabAppFn (ref : Syntax) : Syntax → List LVal → Array NamedArg → Array Arg → Option Expr → Bool → Array TermElabResult → TermElabM (Array TermElabResult)
| f, lvals, namedArgs, args, expectedType?, explicit, acc =>
  let k := f.getKind;
  if k == `Lean.Parser.Term.explicit then
    -- `f` is of the form `@ id`
    elabAppFn (f.getArg 1) lvals namedArgs args expectedType? true acc
  else if k == choiceKind then
    f.getArgs.foldlM (fun acc f => elabAppFn f lvals namedArgs args expectedType? explicit acc) acc
  else if k == `Lean.Parser.Term.proj then
    -- term `.` (fieldIdx <|> ident)
    let field := f.getArg 2;
    match field.isFieldIdx?, field with
    | some idx, _                      => elabAppFn (f.getArg 0) (LVal.fieldIdx idx :: lvals) namedArgs args expectedType? explicit acc
    | _,        Syntax.ident _ _ val _ =>
      let newLVals := val.components.map (fun n => LVal.fieldName (toString n));
      elabAppFn (f.getArg 0) (newLVals ++ lvals) namedArgs args expectedType? explicit acc
    | _,        _                      => throwError field "unexpected kind of field access"
  else if k == `Lean.Parser.Term.arrayRef then do
    -- term `[` term `]`
    let idx := f.getArg 2;
    elabAppFn (f.getArg 0) (LVal.getOp idx :: lvals) namedArgs args expectedType? explicit acc
  else if k == `Lean.Parser.Term.id then
    -- ident (explicitUniv | namedPattern)?
    -- Remark: `namedPattern` should already have been expanded
    match f.getArg 0 with
    | Syntax.ident _ _ n preresolved => do
      us        ← elabExplicitUniv (f.getArg 1);
      funLVals ← resolveName f n preresolved us;
      funLVals.foldlM
        (fun acc ⟨f, fields⟩ => do
          let lvals' := fields.map LVal.fieldName;
          s ← observing $ elabAppLVals ref f (lvals' ++ lvals) namedArgs args expectedType? explicit;
          pure $ acc.push s)
        acc
    | _ => unreachable!
  else do
    f ← elabTerm f none;
    s ← observing $ elabAppLVals ref f lvals namedArgs args expectedType? explicit;
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
  | EStateM.Result.ok _ _     => unreachable!
  | EStateM.Result.error ex s => toMessageData ex stx;
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
    let msgs : Array MessageData := successes.map $ fun success => match success with
      | EStateM.Result.ok e s => MessageData.context s.env s.mctx lctx e
      | _                     => unreachable!;
    throwError f ("ambiguous, possible interpretations " ++ MessageData.ofArray msgs)
  else
    mergeFailures candidates f

private partial def expandAppAux : Syntax → Array Syntax → Syntax × Array Syntax
| stx, args => stx.ifNodeKind `Lean.Parser.Term.app
  (fun node =>
    let fn  := node.getArg 0;
    let arg := node.getArg 1;
    expandAppAux fn (args.push arg))
  (fun _ => (stx, args.reverse))

private def expandApp (stx : Syntax) : TermElabM (Syntax × Array NamedArg × Array Arg) := do
let (f, args) := expandAppAux stx #[];
(namedArgs, args) ← args.foldlM
  (fun (acc : Array NamedArg × Array Arg) arg =>
    let (namedArgs, args) := acc;
    arg.ifNodeKind `Lean.Parser.Term.namedArgument
      (fun argNode => do
        -- `(` ident `:=` term `)`
        namedArgs ← addNamedArg arg acc.1 { name := argNode.getIdAt 1, val := Arg.stx $ argNode.getArg 3 };
        pure (namedArgs, args))
      (fun _ =>
        pure (namedArgs, args.push $ Arg.stx arg)))
  (#[], #[]);
pure (f, namedArgs, args)

@[builtinTermElab app] def elabApp : TermElab :=
fun stx expectedType? => do
  (f, namedArgs, args) ← expandApp stx.val;
  elabAppAux stx.val f namedArgs args expectedType?

@[builtinTermElab «id»] def elabId : TermElab := elabApp
@[builtinTermElab explicit] def elabExplicit : TermElab := elabApp
@[builtinTermElab choice] def elabChoice : TermElab := elabApp
@[builtinTermElab proj] def elabProj : TermElab := elabApp
@[builtinTermElab arrayRef] def elabArrayRef : TermElab := elabApp

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.app;
pure ()

end Term
end Elab
end Lean
