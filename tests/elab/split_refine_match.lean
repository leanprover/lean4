module
import Lean
public meta import Lean.Meta.Tactic.Split

/-!
Tests matcher-based case refinement of a target containing no matcher application, including
overlapping patterns, computed discriminants, and discriminants closed over shared bindings.
-/

open Lean Meta Elab

private def matcherTemplate (x y : Nat) : Nat :=
  match x, y with
  | 0, _ => 1
  | _, 0 => 2
  | n + 1, m + 1 => n + m

private meta def hasHypothesis (type : Expr) : MetaM Bool := do
  for decl in ← getLCtx do
    if ← isDefEq decl.type type then return true
  return false

private meta def checkRefinement (app : MatcherApp) (x p : Expr)
    (discr : Expr → MetaM Expr) (shared : Bool) : MetaM Unit := do
  let goal ← mkFreshExprSyntheticOpaqueMVar (mkApp p x)
  let branches ← Split.refineMatch goal.mvarId! app.matcherName app.matcherLevels app.params
    #[x, ← discr x]
  unless branches.length == 3 do throwError "expected three branches"
  for i in *...3 do
    let branch := branches[i]!
    branch.withContext do
      let target ← branch.getType'
      unless target.isApp && target.appFn! == p do
        throwError "refinement changed the target predicate"
      let arg := target.appArg!
      match i with
      | 0 =>
        unless ← isDefEq arg (mkNatLit 0) do throwError "first branch did not specialize x to zero"
      | 1 =>
        unless arg.isFVar do throwError "overlapping branch specialized x"
        unless ← hasHypothesis (mkNot (← mkEq arg (mkNatLit 0))) do
          throwError "missing overlap hypothesis"
        unless ← hasHypothesis (← mkEq (← discr arg) (mkNatLit 0)) do
          throwError "missing computed-discriminant hypothesis"
      | _ =>
        unless arg.isAppOfArity ``Nat.succ 1 && arg.appArg!.isFVar do
          throwError "last branch did not specialize x to a successor"
        let expected ← discr arg
        let mut found := false
        for decl in ← getLCtx do
          if let some (_, lhs, rhs) := decl.type.eq? then
            if rhs.isAppOfArity ``Nat.succ 1 && rhs.appArg!.isFVar then
              if ← isDefEq lhs expected then
                if shared && !lhs.isLet then throwError "discriminant sharing was lost"
                found := true
        unless found do throwError "missing successor discriminant hypothesis"

run_meta do
  let info ← getConstInfoDefn ``matcherTemplate
  lambdaTelescope info.value fun xs rhs => do
    let some app ← matchMatcherApp? rhs | throwError "expected matcher"
    let nat := mkConst ``Nat
    withLocalDeclD `f (← mkArrow nat nat) fun f => do
      withLocalDeclD `p (← mkArrow nat (mkSort 0)) fun p => do
        checkRefinement app xs[0]! p (fun x => pure (mkApp f x)) false
        checkRefinement app xs[0]! p (fun x =>
          withLetDecl `a nat (mkApp f x) (nondep := true) fun a =>
            withLetDecl `b nat (mkNatAdd a a) (nondep := true) fun b =>
              mkLetFVars #[a, b] (mkNatAdd b b) (generalizeNondepLet := false)) true
