/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment

namespace Lean

private def getFirstCtor (env : Environment) (d : Name) : Option Name :=
match env.find d with
| some (ConstantInfo.inductInfo { ctors := ctor::_, ..}) => some ctor
| _ => none

private def mkNullaryCtor (env : Environment) (type : Expr) (nparams : Nat) : Option Expr :=
match type.getAppFn with
| Expr.const d lvls =>
  match getFirstCtor env d with
  | some ctor => mkApp (Expr.const ctor lvls) (type.getAppArgs.shrink nparams)
  | none      => none
| _ => none

private def toCtorIfLit : Expr → Expr
| Expr.lit (Literal.natVal v) =>
  if v == 0 then Expr.const `Nat.zero []
  else Expr.app (Expr.const `Nat.succ []) (Expr.lit (Literal.natVal (v-1)))
| e => e

private def getRecRuleFor (rec : RecursorVal) (major : Expr) : Option RecursorRule :=
match major.getAppFn with
| Expr.const fn _ => rec.rules.find $ fun r => r.ctor == fn
| _ => none

@[specialize] private def toCtorWhenK {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    (env : Environment) (rec : RecursorVal) (major : Expr) : m (Option Expr) :=
do majorType ← inferType major;
   majorType ← whnf majorType;
   let majorTypeI := majorType.getAppFn;
   if !majorTypeI.isConstOf rec.getInduct then
     pure none
   else if majorType.hasExprMVar && majorType.getAppArgs.anyFrom Expr.hasExprMVar rec.nparams then
     pure none
   else
     match mkNullaryCtor env majorType rec.nparams with
     | none => pure none
     | some newCtorApp => do
       newType ← inferType newCtorApp;
       defeq ← isDefEq majorType newType;
       pure $ if defeq then newCtorApp else none

/-- Auxiliary function for reducing recursor applications. -/
@[specialize] def reduceRecAux {α} {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    (env : Environment)
    (rec : RecursorVal) (recLvls : List Level) (recArgs : Array Expr)
    (failK : Unit → m α)
    (successK : Expr → m α) : m α :=
let majorIdx := rec.getMajorIdx;
if h : majorIdx < recArgs.size then do
  let major := recArgs.get ⟨majorIdx, h⟩;
  major ← whnf major;
  major ←
    if !rec.k then
      pure major
    else do {
      newMajor ← toCtorWhenK whnf inferType isDefEq env rec major;
      pure (newMajor.getD major)
    };
  let major := toCtorIfLit major;
  match getRecRuleFor rec major with
  | some rule =>
    let majorArgs := major.getAppArgs;
    if recLvls.length != rec.lparams.length then
      failK ()
    else
      let rhs := rule.rhs.instantiateLevelParams rec.lparams recLvls;
      -- Apply parameters, motives and minor premises from recursor application.
      let rhs := mkAppRange rhs 0 (rec.nparams+rec.nmotives+rec.nminors) recArgs;
      /- The number of parameters in the constructor is not necessarily
         equal to the number of parameters in the recursor when we have
         nested inductive types. -/
      let nparams := majorArgs.size - rule.nfields;
      let rhs := mkAppRange rhs nparams majorArgs.size majorArgs;
      let rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs;
      successK rhs
  | none => failK ()
else
  failK ()

@[inline] private def matchRecApp {α} {m : Type → Type} [Monad m] (env : Environment)
   (e : Expr) (failK : Unit → m α) (k : RecursorVal → List Level → Array Expr → m α) : m α :=
matchConst env e.getAppFn failK $ fun cinfo recLvls =>
  match cinfo with
  | ConstantInfo.recInfo rec => k rec recLvls e.getAppArgs
  | _ => failK ()

/-- Reduce recursor applications. -/
@[specialize] def reduceRec {α} {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    (env : Environment) (e : Expr)
    (failK : Unit → m α)
    (successK : Expr → m α) : m α :=
matchRecApp env e failK $ fun rec recLvls recArgs => reduceRecAux whnf inferType isDefEq env rec recLvls recArgs failK successK

@[specialize] def isRecStuck {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (isStuck : Expr → m (Option Expr))
    (env : Environment) (e : Expr) : m (Option Expr) :=
matchRecApp env e (fun _ => pure none) $ fun rec recLvls recArgs =>
  if rec.k then
    -- TODO: improve this case
    pure none
  else do
    let majorIdx := rec.getMajorIdx;
    if h : majorIdx < recArgs.size then do
      let major := recArgs.get ⟨majorIdx, h⟩;
      major ← whnf major;
      isStuck major
    else
      pure none

end Lean
