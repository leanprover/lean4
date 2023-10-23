import Lean

open Lean
open Meta

def execShow (x : MetaM Expr) : MetaM Unit := do
  let e ← x
  IO.println (← ppExpr e)

/-
The `MetaM` has an ambient local context.
The local context contains the types of the free variables.
-/

def mkLam1 : MetaM Expr :=
  /- The following `withLocalDecl` extends the local context with `(x : Nat)`, and executes the lambda
     with an expression `x`. -/
  withLocalDecl `x BinderInfo.default (mkConst `Nat) fun x =>
  /- Similar to the method above, but sets `BinderInfo.default`. -/
  withLocalDeclD `y (mkConst `Nat) fun y => do
    -- Double backticks instruct Lean to resolve the names at compilation time
    let b ← mkAppM ``HAdd.hAdd #[x, y] -- `x + y`
    let b ← mkAppM ``HAdd.hAdd #[b, x] -- `x + y + x`
    /- `mkLambdaFVars` converts the free variables into de-Bruijn bound variables, and construct the lambda for us. -/
    mkLambdaFVars #[x, y] b

#eval execShow mkLam1

#eval execShow do let e ← mkLam1; inferType e

def mkForall1 : MetaM Expr :=
  withLocalDeclD `x (mkConst `Nat) fun x =>
  withLocalDeclD `y (mkConst `Nat) fun y => do
    let b ← mkEq x y
    mkForallFVars #[x, y] b

#eval execShow mkForall1

def mkForall2Lambda : MetaM Expr := do
  let e ← mkForall1
  /- The following method `opens` a `forall` term, and expands the local context with
     new free variables corresponding to the forall binders.
     We also have a telescope function for `lambda` terms. -/
  forallTelescopeReducing e fun xs b => do
    IO.println s!">> {← xs.mapM Meta.ppExpr}"
    IO.println s!">> {← ppExpr b}"
    -- xs is an array of `Expr`
    let b ← mkAppM ``HMul.hMul xs
    mkLambdaFVars xs b

#eval execShow mkForall2Lambda

def mkGoal : MetaM Expr :=
  withLocalDeclD `x (mkConst `Nat) fun x =>
  withLocalDeclD `y (mkConst `Nat) fun y => do
  withLocalDeclD `h (← mkEq x y) fun h => do
    let b ← mkEq y x
    mkForallFVars #[x, y, h] b

#eval execShow mkGoal

def proveGoal : MetaM Unit := do
  let g ← mkGoal
  -- `main` is a metavariable representing the term we want to construct
  let main ← mkFreshExprSyntheticOpaqueMVar g
  let m := main.mvarId!
  IO.println (← ppGoal m)
  IO.println "-----"
  let (xs, m) ← introNP m 3 -- `intro` 3 variables using the binder names to name the new locals
  IO.println (← ppGoal m)
  IO.println "-----"
  -- The `apply` tactic generates 0 or more subgoals
  let [m] ← apply m (mkConst ``Eq.symm [levelOne]) | throwError "unexpected number of subgoals"
  IO.println (← ppGoal m)
  IO.println "-----"
  assumption m
  -- `main` contains the whole proof now
  IO.println (← ppExpr main)
  check main -- type check the proof. This is not the kernel type checker.
  IO.println (← ppExpr (← inferType main))

#eval proveGoal
