/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic

namespace Lean
namespace Meta
namespace Exception

private def run? {α} (ctx : ExceptionContext) (x : MetaM α) : Option α :=
match x { lctx := ctx.lctx, currRecDepth := 0, maxRecDepth := getMaxRecDepth ctx.opts } { env := ctx.env, mctx := ctx.mctx, ngen := { namePrefix := `_meta_exception } } with
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
| isLevelDefEqStuck u v ctx       => mkCtx ctx $ "stuck at universe level constraint " ++ u ++ " =?= " ++ v
| isExprDefEqStuck t s ctx        => mkCtx ctx $ "stuck at constraint " ++ t ++ " =?= " ++ s
| letTypeMismatch fvarId ctx      => mkLetTypeMismatchMessage fvarId ctx
| appTypeMismatch f a ctx         => mkAppTypeMismatchMessage f a ctx
| notInstance i ctx               => mkCtx ctx $ "not a type class instance " ++ i
| appBuilder op msg args ctx      => mkCtx ctx $ "application builder failure " ++ op ++ " " ++ args ++ " " ++ msg
| synthInstance inst ctx          => mkCtx ctx $ "failed to synthesize" ++ indentExpr inst
| tactic tacName mvarId msg ctx   => mkCtx ctx $ "tactic '" ++ tacName ++ "' failed, " ++ msg ++ Format.line ++ MessageData.ofGoal mvarId
| kernel ex opts                  => ex.toMessageData opts
| bug _ _                         => "internal bug" -- TODO improve
| other s                         => s

end Exception

instance MetaHasEval {α} [MetaHasEval α] : MetaHasEval (MetaM α) :=
⟨fun env opts x _ => do
   match x { config := { opts := opts }, currRecDepth := 0, maxRecDepth := getMaxRecDepth opts } { env := env } with
   | EStateM.Result.ok a s    => do
     s.traceState.traces.forM $ fun m => IO.println $ format m;
     MetaHasEval.eval s.env opts a
   | EStateM.Result.error err s => do
     s.traceState.traces.forM $ fun m => IO.println $ format m;
     throw (IO.userError (toString (format err.toMessageData)))⟩

end Meta
end Lean
