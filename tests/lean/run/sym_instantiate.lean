import Lean.Meta.Sym

open Lean Meta Grind Sym

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
#eval SymM.run' tst1

def tst2 : SymM Unit := do
  let f ← mkConstS `f
  let e ← mkAppS (← mkAppS (← mkAppS f (← mkBVarS 0)) (← mkBVarS 1)) (← shareCommon (mkNatLit 1))
  withLocalDeclD `x (← mkConstS ``Nat) fun x => do
  withLocalDeclD `y (← mkConstS ``Nat) fun y => do
  logInfo e
  let r ← instantiateRevS e #[x, y]
  logInfo r
  assert! isSameExpr (← abstractFVars r #[x, y]) e
  logInfo (← abstractFVars r #[x, y])
  logInfo (← abstractFVarsRange r 1 #[x, y])


/--
info: f #0 #1 1
---
info: f y x 1
---
info: f #0 #1 1
---
info: f #0 x 1
-/
#guard_msgs in
#eval SymM.run' tst2
