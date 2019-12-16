/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic

namespace Lean

def indentExpr (msg : MessageData) : MessageData :=
MessageData.nest 2 (Format.line ++ msg)

namespace Meta
namespace Exception

private def run? {α} (ctx : ExceptionContext) (x : MetaM α) : Option α :=
match x { lctx := ctx.lctx } { env := ctx.env, mctx := ctx.mctx, ngen := { namePrefix := `_meta_exception } } with
| EStateM.Result.ok a _ => some a
| EStateM.Result.error _ _ => none

private def inferType? (ctx : ExceptionContext) (e : Expr) : Option Expr :=
run? ctx (inferType e)

private def inferDomain? (ctx : ExceptionContext) (f : Expr) : Option Expr :=
run? ctx $ do
  fType ← inferType f;
  fType ← whnf fType;
  match fType with
  | Expr.forallE _ d _ _ => pure d
  | _                    => throw $ Exception.other "unexpected"

private def whnf? (ctx : ExceptionContext) (e : Expr) : Option Expr :=
run? ctx (whnf e)

def mkAppTypeMismatchMessage (f a : Expr) (ctx : ExceptionContext) : MessageData :=
mkCtx ctx $
  let e      := mkApp f a;
  match inferType? ctx a, inferDomain? ctx f with
  | some aType, some expectedType =>
    "application type mismatch" ++ indentExpr e
    ++ Format.line ++ "argument" ++ indentExpr a
    ++ Format.line ++ "has type" ++ indentExpr aType
    ++ Format.line ++ "but is expected to have type" ++ indentExpr expectedType
  | _, _ =>
    "application type mismatch" ++ indentExpr e

def mkLetTypeMismatchMessage (fvarId : FVarId) (ctx : ExceptionContext) : MessageData :=
mkCtx ctx $
  match ctx.lctx.find? fvarId with
  | some (LocalDecl.ldecl _ n t v b) =>
    match inferType? ctx v with
    | some vType =>
      "invalid let declaration, term" ++ indentExpr v
      ++ Format.line ++ "has type " ++ indentExpr vType
      ++ Format.line ++ "but is expected to have type" ++ indentExpr t
    | none => "type mismatch at let declaration for " ++ n
  | _ => unreachable!

/--
  Convert to `MessageData` that is supposed to be displayed in user-friendly error messages. -/
def toMessageData : Exception → MessageData
| unknownConst c ctx              => mkCtx ctx $ "unknown constant " ++ c
| unknownFVar fvarId ctx          => mkCtx ctx $ "unknown free variable " ++ fvarId
| unknownExprMVar mvarId ctx      => mkCtx ctx $ "unknown metavariable " ++ mvarId
| unknownLevelMVar mvarId ctx     => mkCtx ctx $ "unknown universe level metavariable " ++ mvarId
| unexpectedBVar bvarIdx          => "unexpected bound variable " ++ mkBVar bvarIdx
| functionExpected f a ctx        => mkCtx ctx $ "function expected " ++ mkApp f a
| typeExpected t ctx              => mkCtx ctx $ "type expected " ++ t
| incorrectNumOfLevels c lvls ctx => mkCtx ctx $ "incorrect number of universe levels " ++ mkConst c lvls
| invalidProjection s i e ctx     => mkCtx ctx $ "invalid projection" ++ indentExpr (mkProj s i e)
| revertFailure xs decl ctx       => mkCtx ctx $ "revert failure"
| readOnlyMVar mvarId ctx         => mkCtx ctx $ "tried to update read only metavariable " ++ mkMVar mvarId
| isLevelDefEqStuck u v ctx       => mkCtx ctx $ "stuck at " ++ u ++ " =?= " ++ v
| isExprDefEqStuck t s ctx        => mkCtx ctx $ "stuck at " ++ t ++ " =?= " ++ s
| letTypeMismatch fvarId ctx      => mkLetTypeMismatchMessage fvarId ctx
| appTypeMismatch f a ctx         => mkAppTypeMismatchMessage f a ctx
| notInstance i ctx               => mkCtx ctx $ "not a type class instance " ++ i
| appBuilder op msg args ctx      => mkCtx ctx $ "application builder failure " ++ op ++ " " ++ args ++ " " ++ msg
| synthInstance inst ctx          => mkCtx ctx $ "failed to synthesize" ++ indentExpr inst
| bug _ _                         => "internal bug" -- TODO improve
| other s                         => s

end Exception

end Meta

namespace KernelException

private def mkCtx (env : Environment) (lctx : LocalContext) (msg : MessageData) : MessageData :=
MessageData.context env {} lctx msg

def toMessageData (e : KernelException) : MessageData :=
match e with
| unknownConstant env constName       => mkCtx env {} $ "(kernel) unknown constant " ++ constName
| alreadyDeclared env constName       => mkCtx env {} $ "(kernel) constant has already been declared " ++ constName
| declTypeMismatch env decl givenType =>
  let process (n : Name) (expectedType : Expr) : MessageData :=
    "(kernel) declaration type mismatch " ++ n
    ++ Format.line ++ "has type" ++ indentExpr givenType
    ++ Format.line ++ "but it is expected to have type" ++ indentExpr expectedType;
  match decl with
  | Declaration.defnDecl { name := n, type := type, .. } => process n type
  | Declaration.thmDecl { name := n, type := type, .. }  => process n type
  | _ => "(kernel) declaration type mismatch" -- TODO fix type checker, type mismatch for mutual decls does not have enough information
| declHasMVars env constName _        => mkCtx env {} $ "(kernel) declaration has metavariables " ++ constName
| declHasFVars env constName _        => mkCtx env {} $ "(kernel) declaration has free variables " ++ constName
| funExpected env lctx e              => mkCtx env lctx $ "(kernel) function expected" ++ indentExpr e
| typeExpected env lctx e             => mkCtx env lctx $ "(kernel) type expected" ++ indentExpr e
| letTypeMismatch  env lctx n _ _     => mkCtx env lctx $ "(kernel) let-declaration type mismatch " ++ n
| exprTypeMismatch env lctx e _       => mkCtx env lctx $ "(kernel) type mismatch at " ++ indentExpr e
| appTypeMismatch  env lctx e _ _     =>
  match e with
  | Expr.app f a _ => "(kernel) " ++ Meta.Exception.mkAppTypeMismatchMessage f a { env := env, lctx := lctx, mctx := {} }
  | _              => "(kernel) application type mismatch at" ++ indentExpr e
| invalidProj env lctx e              => mkCtx env lctx $ "(kernel) invalid projection" ++ indentExpr e
| other msg                           => "(kernel) " ++ msg

end KernelException

end Lean
