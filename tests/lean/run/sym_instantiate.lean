import Lean.Meta.Sym
set_option sym.debug true
open Lean Meta Sym
open Internal
def tst1 : SymM Unit := do
  let f ← mkConstS `f
  let e ← mkAppS (← mkAppS (← mkAppS f (← mkBVarS 0)) (← mkBVarS 1)) (← shareCommon (mkNatLit 1))
  let a ← mkConstS `a
  let b ← mkConstS `b
  let r ← instantiateRevS e #[a, b]
  assert! r == e.instantiateRev #[a, b]
  logInfo r
  let r ← instantiateS e #[a, b]
  assert! r == e.instantiate #[a, b]
  logInfo r
  let e ← mkLambdaS `x .default (← mkConstS ``Nat) e
  let r ← instantiateRevS e #[a, b]
  assert! r == e.instantiateRev #[a, b]
  logInfo r
  let r ← instantiateS e #[a, b]
  assert! r == e.instantiate #[a, b]
  logInfo r

/--
info: f b a 1
---
info: f a b 1
---
info: fun x => f x b 1
---
info: fun x => f x a 1
-/
#guard_msgs in
#eval SymM.run tst1

def tst2 : SymM Unit := do
  let f ← mkConstS `f
  withLocalDeclD `w (← mkConstS ``Nat) fun w => do
  let w ← shareCommon w
  let e ← mkAppS (← mkAppS (← mkAppS f (← mkBVarS 0)) (← mkBVarS 1)) w
  withLocalDeclD `x (← mkConstS ``Nat) fun x => do
  withLocalDeclD `y (← mkConstS ``Nat) fun y => do
  let x ← shareCommon x
  let y ← shareCommon y
  logInfo e
  let r ← instantiateRevS e #[x, y]
  logInfo r
  assert! isSameExpr (← abstractFVars r #[x, y]) e
  logInfo (← abstractFVars r #[x, y])
  logInfo (← abstractFVarsRange r 1 #[x, y])
  logInfo (← mkLambdaFVarsS #[x, y] e)


set_option pp.funBinderTypes true in
/--
info: f #0 #1 w
---
info: f y x w
---
info: f #0 #1 w
---
info: f #0 x w
---
info: fun (x y : Nat) => f y x w
-/
#guard_msgs in
#eval SymM.run tst2
