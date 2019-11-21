/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment
import Init.Lean.Message
import Init.Lean.MetavarContext

namespace Lean
namespace Meta

structure ExceptionContext :=
(env : Environment) (mctx : MetavarContext) (lctx : LocalContext)

inductive Bug
| overwritingExprMVar (mvarId : Name)

inductive Exception
| unknownConst         (constName : Name) (ctx : ExceptionContext)
| unknownFVar          (fvarId : Name) (ctx : ExceptionContext)
| unknownExprMVar      (mvarId : Name) (ctx : ExceptionContext)
| unknownLevelMVar     (mvarId : Name) (ctx : ExceptionContext)
| unexpectedBVar       (bvarIdx : Nat)
| functionExpected     (f a : Expr) (ctx : ExceptionContext)
| typeExpected         (type : Expr) (ctx : ExceptionContext)
| incorrectNumOfLevels (constName : Name) (constLvls : List Level) (ctx : ExceptionContext)
| invalidProjection    (structName : Name) (idx : Nat) (s : Expr) (ctx : ExceptionContext)
| revertFailure        (toRevert : Array Expr) (decl : LocalDecl) (ctx : ExceptionContext)
| readOnlyMVar         (mvarId : Name) (ctx : ExceptionContext)
| isDefEqStuck         (t s : Expr) (ctx : ExceptionContext)
| letTypeMismatch      (fvarId : Name) (ctx : ExceptionContext)
| appTypeMismatch      (f a : Expr) (ctx : ExceptionContext)
| bug                  (b : Bug) (ctx : ExceptionContext)
| other                (msg : String)

namespace Exception
instance : Inhabited Exception := ⟨other ""⟩

-- TODO: improve, use (to be implemented) pretty printer
def toStr : Exception → String
| unknownConst c _              => "unknown constant '" ++ toString c ++ "'"
| unknownFVar fvarId _          => "unknown free variable '" ++ toString fvarId ++ "'"
| unknownExprMVar mvarId _      => "unknown metavariable '" ++ toString mvarId ++ "'"
| unknownLevelMVar mvarId _     => "unknown universe level metavariable '" ++ toString mvarId ++ "'"
| unexpectedBVar bvarIdx        => "unexpected loose bound variable #" ++ toString bvarIdx
| functionExpected fType args _ => "function expected"
| typeExpected _ _              => "type expected"
| incorrectNumOfLevels c lvls _ => "incorrect number of universe levels for '" ++ toString c ++ "' " ++ toString lvls
| invalidProjection _ _ _ _     => "invalid projection"
| revertFailure _ _ _           => "revert failure"
| readOnlyMVar _ _              => "try to assign read only metavariable"
| isDefEqStuck _ _ _            => "isDefEq is stuck"
| letTypeMismatch _ _           => "type mismatch at let-expression"
| appTypeMismatch _ _ _         => "application type mismatch"
| bug _ _                       => "bug"
| other s                       => s

instance : HasToString Exception := ⟨toStr⟩

private def mkCtx (c : ExceptionContext) (m : MessageData) : MessageData :=
MessageData.context c.env c.mctx c.lctx m

def toMessageData : Exception → MessageData
| unknownConst c ctx              => mkCtx ctx $ `unknownConst ++ " " ++ c
| unknownFVar fvarId ctx          => mkCtx ctx $ `unknownFVar ++ " " ++ fvarId
| unknownExprMVar mvarId ctx      => mkCtx ctx $ `unknownExprMVar ++ " " ++ mkMVar mvarId
| unknownLevelMVar mvarId ctx     => mkCtx ctx $ `unknownLevelMVar ++ " " ++ mkLevelMVar mvarId
| unexpectedBVar bvarIdx          => `unexpectedBVar ++ " " ++ mkBVar bvarIdx
| functionExpected f a ctx        => mkCtx ctx $ `functionExpected ++ " " ++ mkApp f a
| typeExpected t ctx              => mkCtx ctx $ `typeExpected ++ " " ++ t
| incorrectNumOfLevels c lvls ctx => mkCtx ctx $ `incorrectNumOfLevels ++ " " ++ mkConst c lvls
| invalidProjection s i e ctx     => mkCtx ctx $ `invalidProjection ++ " " ++ mkProj s i e
| revertFailure xs decl ctx       => mkCtx ctx $ `revertFailure -- TODO improve
| readOnlyMVar mvarId ctx         => mkCtx ctx $ `readOnlyMVar ++ " " ++ mkMVar mvarId
| isDefEqStuck t s ctx            => mkCtx ctx $ `isDefEqStuck ++ " " ++ t ++ " =?= " ++ s
| letTypeMismatch fvarId ctx      => mkCtx ctx $ `letTypeMismatch ++ " " ++ mkFVar fvarId
| appTypeMismatch f a ctx         => mkCtx ctx $ `appTypeMismatch ++ " " ++ mkApp f a
| bug _ _                         => "internal bug" -- TODO improve
| other s                         => s

end Exception

end Meta
end Lean
