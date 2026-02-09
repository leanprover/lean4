import Lean
open Lean Meta

def test1 (e : Expr) : Option Expr :=
  match_expr e with
  | c@Eq α a b => some (mkApp3 c α b a)
  | Eq.refl _ a => some a
  | _ => none

/--
info: 3 = 1
---
info: 3
---
info: 4 = 2
-/
#guard_msgs in
run_meta do
  let eq ← mkEq (toExpr 1) (toExpr 3)
  let eq := mkAnnotation `foo eq
  let some eq := test1 eq | throwError "unexpected"
  logInfo eq
  let rfl ← mkEqRefl (toExpr 3)
  let some n := test1 rfl | throwError "unexpected"
  logInfo n
  let eq := mkAnnotation `boo <| mkApp (mkAnnotation `bla (mkApp (mkAnnotation `foo eq.appFn!.appFn!) (toExpr 2))) (toExpr 4)
  let some eq := test1 eq | throwError "unexpected"
  logInfo eq

def test2 (e : Expr) : MetaM Expr := do
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => mkSub a b
  | HMul.hMul _ _ _ _ a b => mkAdd b a
  | _ => return e

/--
info: 2 - 5
---
info: 5 + 2
---
info: 5 - 2
-/
#guard_msgs in
run_meta do
  let e ← mkAdd (toExpr 2) (toExpr 5)
  let e ← test2 e
  logInfo e
  let e ← mkMul (toExpr 2) (toExpr 5)
  let e ← test2 e
  logInfo e
  let m ← mkFreshExprMVar none
  let m ← test2 m
  assert! m.isMVar
  discard <| isDefEq m e
  let m ← test2 m
  logInfo m

def test3 (e : Expr) : Option Expr :=
  let_expr c@Eq α a b := e | none
  some (mkApp3 c α b a)

def test4 (e : Expr) : Option Expr :=
  let_expr Eq.refl _ a := e | none
  some a

/--
info: 3 = 1
---
info: 3
---
info: 4 = 2
-/
#guard_msgs in
run_meta do
  let eq ← mkEq (toExpr 1) (toExpr 3)
  let eq := mkAnnotation `foo eq
  let some eq := test3 eq | throwError "unexpected"
  logInfo eq
  let rfl ← mkEqRefl (toExpr 3)
  let some n := test4 rfl | throwError "unexpected"
  logInfo n
  let eq := mkAnnotation `boo <| mkApp (mkAnnotation `bla (mkApp (mkAnnotation `foo eq.appFn!.appFn!) (toExpr 2))) (toExpr 4)
  let some eq := test3 eq | throwError "unexpected"
  logInfo eq

def test5 (e : Expr) : MetaM Expr := do
  let_expr HAdd.hAdd _ _ _ _ a b ← e
    | return e
  mkSub a b

def test6 (e : Expr) : MetaM Expr := do
  let_expr HAdd.hAdd _ _ _ _ a b := e
    | return e
  mkSub a b

/--
info: 2 - 5
---
info: 2 - 5
---
info: 2 - 5
-/
#guard_msgs in
run_meta do
  let e ← mkAdd (toExpr 2) (toExpr 5)
  let e' ← test5 e
  logInfo e'
  let e' ← test6 e
  logInfo e'
  let m ← mkFreshExprMVar none
  let m ← test5 m
  assert! m.isMVar
  discard <| isDefEq m e
  let m' ← test5 m
  logInfo m'
  assert! m.isMVar
  let m' ← test6 m -- does not instantiate mvars
  assert! m'.isMVar
