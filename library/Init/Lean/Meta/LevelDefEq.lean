/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic

namespace Lean
namespace Meta

private def strictOccursMaxAux (lvl : Level) : Level → Bool
| Level.max u v _ => strictOccursMaxAux u || strictOccursMaxAux v
| u               => u != lvl && lvl.occurs u

/--
  Return true iff `lvl` occurs in `max u_1 ... u_n` and `lvl != u_i` for all `i in [1, n]`.
  That is, `lvl` is a proper level subterm of some `u_i`. -/
private def strictOccursMax (lvl : Level) : Level → Bool
| Level.max u v _ => strictOccursMaxAux lvl u || strictOccursMaxAux lvl v
| _               => false

/-- `mkMaxArgsDiff mvarId (max u_1 ... (mvar mvarId) ... u_n) v` => `max v u_1 ... u_n` -/
private def mkMaxArgsDiff (mvarId : Name) : Level → Level → Level
| Level.max u v _,     acc => mkMaxArgsDiff v $ mkMaxArgsDiff u acc
| l@(Level.mvar id _), acc => if id != mvarId then mkLevelMax acc l else acc
| l,                   acc => mkLevelMax acc l

/--
  Solve `?m =?= max ?m v` by creating a fresh metavariable `?n`
  and assigning `?m := max ?n v` -/
private def solveSelfMax (mvarId : Name) (v : Level) : MetaM Unit :=
do mvarId ← mkFreshLevelMVarId;
   let lhs := mkMaxArgsDiff mvarId v (mkLevelMVar mvarId);
   assignLevelMVar mvarId lhs

private def postponeIsLevelDefEq (lhs : Level) (rhs : Level) : MetaM Unit :=
modify $ fun s => { postponed := s.postponed.push { lhs := lhs, rhs := rhs }, .. s }

inductive LevelConstraintKind
| mvarEq         -- ?m =?= l         where ?m does not occur in l
| mvarEqSelfMax  -- ?m =?= max ?m l  where ?m does not occur in l
| other

private def getLevelConstraintKind (u v : Level) : MetaM LevelConstraintKind :=
match u with
| Level.mvar mvarId _ =>
  condM (isReadOnlyLevelMVar mvarId)
    (pure LevelConstraintKind.other)
    (if !u.occurs v then pure LevelConstraintKind.mvarEq
     else if !strictOccursMax u v then pure LevelConstraintKind.mvarEqSelfMax
     else pure LevelConstraintKind.other)
| _ =>
  pure LevelConstraintKind.other

private partial def isLevelDefEqAux : Level → Level → MetaM Bool
| Level.succ lhs _, Level.succ rhs _ => isLevelDefEqAux lhs rhs
| lhs, rhs =>
  if lhs == rhs then
    pure true
  else do
    trace! `type_context.level_is_def_eq (lhs ++ " =?= " ++ rhs);
    lhs' ← instantiateLevelMVars lhs;
    let lhs' := lhs'.normalize;
    rhs' ← instantiateLevelMVars rhs;
    let rhs' := rhs'.normalize;
    if lhs != lhs' || rhs != rhs' then
      isLevelDefEqAux lhs' rhs'
    else do
      mctx ← getMCtx;
      if !mctx.hasAssignableLevelMVar lhs && !mctx.hasAssignableLevelMVar rhs then
        pure false
      else do
        k ← getLevelConstraintKind lhs rhs;
        match k with
        | LevelConstraintKind.mvarEq        => do assignLevelMVar lhs.mvarId! rhs; pure true
        | LevelConstraintKind.mvarEqSelfMax => do solveSelfMax lhs.mvarId! rhs; pure true
        | _ => do
          k ← getLevelConstraintKind rhs lhs;
          match k with
          | LevelConstraintKind.mvarEq        => do assignLevelMVar rhs.mvarId! lhs; pure true
          | LevelConstraintKind.mvarEqSelfMax => do solveSelfMax rhs.mvarId! lhs; pure true
          | _ =>
            if lhs.isMVar || rhs.isMVar then
              pure false
            else if lhs.isSucc || rhs.isSucc then
              match lhs.dec, rhs.dec with
              | some lhs', some rhs' => isLevelDefEqAux lhs' rhs'
              | _,         _         => do postponeIsLevelDefEq lhs rhs; pure true
            else do postponeIsLevelDefEq lhs rhs; pure true

private def getNumPostponed : MetaM Nat :=
do s ← get;
   pure s.postponed.size

private def getResetPostponed : MetaM (PersistentArray PostponedEntry) :=
do s ← get;
   let ps := s.postponed;
   modify $ fun s => { postponed := {}, .. s };
   pure ps

private def processPostponedStep : MetaM Bool :=
traceCtx `type_context.level_is_def_eq.postponed_step $ do
  ps ← getResetPostponed;
  ps.foldlM
    (fun (r : Bool) (p : PostponedEntry) =>
      if r then
        isLevelDefEqAux p.lhs p.rhs
      else
        pure false)
    true

private partial def processPostponedAux : Bool → MetaM Bool
| mayPostpone => do
  numPostponed ← getNumPostponed;
  if numPostponed == 0 then
    pure true
  else do
    trace! `type_context.level_is_def_eq ("processing #" ++ toString numPostponed ++ " postponed is-def-eq level constraints");
    r ← processPostponedStep;
    if !r then
      pure r
    else do
      numPostponed' ← getNumPostponed;
      if numPostponed' == 0 then
        pure true
      else if numPostponed' < numPostponed then
        processPostponedAux mayPostpone
      else do
        trace! `type_context.level_is_def_eq ("no progress solving pending is-def-eq level constraints");
        pure mayPostpone

private def processPostponed (mayPostpone : Bool) : MetaM Bool :=
do numPostponed ← getNumPostponed;
   if numPostponed == 0 then pure true
   else traceCtx `type_context.level_is_def_eq.postponed $ processPostponedAux mayPostpone


private def restore (env : Environment) (mctx : MetavarContext) (postponed : PersistentArray PostponedEntry) : MetaM Unit :=
modify $ fun s => { env := env, mctx := mctx, postponed := postponed, .. s }

/--
  `try x` executes `x` and process all postponed universe level constraints produced by `x`.
  We keep the modifications only if both return `true`.

  Remark: postponed universe level constraints must be solved before returning. Otherwise,
  we don't know whether `x` really succeeded. -/
@[specialize] def try (x : MetaM Bool) : MetaM Bool :=
do s ← get;
   let env       := s.env;
   let mctx      := s.mctx;
   let postponed := s.postponed;
   modify $ fun s => { postponed := {}, .. s };
   catch
     (condM x
       (condM (processPostponed false)
         (pure true)
         (do restore env mctx postponed; pure false))
       (do restore env mctx postponed; pure false))
     (fun ex => do restore env mctx postponed; throw ex)

/- Public interface -/

def isLevelDefEq (u v : Level) : MetaM Bool :=
try $ do
  r ← isLevelDefEqAux u v;
  if !r then pure false
  else processPostponed false

def isListLevelDefEq : List Level → List Level → MetaM Bool
| [],    []    => pure true
| u::us, v::vs => isLevelDefEq u v <&&> isListLevelDefEq us vs
| _,     _     => pure false

end Meta
end Lean
