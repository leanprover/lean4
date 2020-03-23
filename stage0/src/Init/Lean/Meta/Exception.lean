/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment
import Init.Lean.MetavarContext
import Init.Lean.Message
import Init.Lean.Util.PPGoal

namespace Lean
namespace Meta

abbrev ExceptionContext := MessageDataContext

inductive Bug
| overwritingExprMVar (mvarId : Name)

inductive Exception
| unknownConst         (constName : Name) (ctx : ExceptionContext)
| unknownFVar          (fvarId : FVarId) (ctx : ExceptionContext)
| unknownExprMVar      (mvarId : MVarId) (ctx : ExceptionContext)
| unknownLevelMVar     (mvarId : MVarId) (ctx : ExceptionContext)
| unexpectedBVar       (bvarIdx : Nat)
| functionExpected     (f a : Expr) (ctx : ExceptionContext)
| typeExpected         (type : Expr) (ctx : ExceptionContext)
| incorrectNumOfLevels (constName : Name) (constLvls : List Level) (ctx : ExceptionContext)
| invalidProjection    (structName : Name) (idx : Nat) (s : Expr) (ctx : ExceptionContext)
| revertFailure        (toRevert : Array Expr) (decl : LocalDecl) (ctx : ExceptionContext)
| readOnlyMVar         (mvarId : MVarId) (ctx : ExceptionContext)
| isLevelDefEqStuck    (u v : Level) (ctx : ExceptionContext)
| isExprDefEqStuck     (t s : Expr) (ctx : ExceptionContext)
| letTypeMismatch      (fvarId : FVarId) (ctx : ExceptionContext)
| appTypeMismatch      (f a : Expr) (ctx : ExceptionContext)
| notInstance          (e : Expr) (ctx : ExceptionContext)
| appBuilder           (op : Name) (msg : String) (args : Array Expr) (ctx : ExceptionContext)
| synthInstance        (inst : Expr) (ctx : ExceptionContext)
| tactic               (tacticName : Name) (mvarId : MVarId) (msg : MessageData) (ctx : ExceptionContext)
| kernel               (ex : KernelException) (opts : Options)
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
| isLevelDefEqStuck _ _ _       => "isDefEq is stuck"
| isExprDefEqStuck _ _ _        => "isDefEq is stuck"
| letTypeMismatch _ _           => "type mismatch at let-expression"
| appTypeMismatch _ _ _         => "application type mismatch"
| notInstance _ _               => "type class instance expected"
| appBuilder _ _ _ _            => "application builder failure"
| synthInstance _ _             => "type class instance synthesis failed"
| tactic tacName _ _ _          => "tactic '" ++ toString tacName ++ "' failed"
| kernel _ _                    => "kernel exception"
| bug _ _                       => "bug"
| other s                       => s

instance : HasToString Exception := ⟨toStr⟩

def mkCtx (ctx : ExceptionContext) (m : MessageData) : MessageData :=
MessageData.withContext ctx m

/-- Generate trace message that is suitable for tracing crawlers -/
def toTraceMessageData : Exception → MessageData
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
| isLevelDefEqStuck u v ctx       => mkCtx ctx $ `isLevelDefEqStuck ++ " " ++ u ++ " =?= " ++ v
| isExprDefEqStuck t s ctx        => mkCtx ctx $ `isExprDefEqStuck ++ " " ++ t ++ " =?= " ++ s
| letTypeMismatch fvarId ctx      => mkCtx ctx $ `letTypeMismatch ++ " " ++ mkFVar fvarId
| appTypeMismatch f a ctx         => mkCtx ctx $ `appTypeMismatch ++ " " ++ mkApp f a
| notInstance i ctx               => mkCtx ctx $ `notInstance ++ " " ++ i
| appBuilder op msg args ctx      => mkCtx ctx $ `appBuilder ++ " " ++ op ++ " " ++ args ++ " " ++ msg
| synthInstance inst ctx          => mkCtx ctx $ `synthInstance ++ " " ++ inst
| tactic tacName mvarId msg ctx   => mkCtx ctx $ `tacticFailure ++ " " ++ tacName ++ " " ++ msg
| kernel ex opts                  => ex.toMessageData opts
| bug _ _                         => "internal bug" -- TODO improve
| other s                         => s

end Exception

end Meta
end Lean
