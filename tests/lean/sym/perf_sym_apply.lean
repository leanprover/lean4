import Lean.Meta.Tactic
import Lean.Meta.Sym

open Lean Meta Sym
def profileM {α : Type} (k : MetaM α) (msg : String := "experiment") : MetaM α :=
  profileitM Exception msg ({ : Options }.set `profiler true |>.setNat `profiler.threshold 0)  k

def genTerm (n : Nat) : Expr := Id.run do
  let mut e := mkConst ``True
  let nat := mkConst ``Nat
  for _ in 0...n do
    let eq := mkApp3 (mkConst ``Eq [1]) nat (mkBVar 0) (mkNatAdd (mkBVar 2) (mkBVar 1))
    e := mkApp2 (mkConst ``And) eq e
    e := mkApp2 (mkConst ``Exists [1]) nat (mkLambda `y .default nat e)
    e := mkForall `x .default nat e
    e := mkLet `z nat (mkNatAdd (mkBVar 1) (mkBVar 0)) e
  let eq := mkApp3 (mkConst ``Eq [1]) nat (mkBVar 0) (mkNatAdd (mkBVar 2) (mkBVar 1))
  e := mkApp2 (mkConst ``And) eq e
  e := mkApp2 (mkConst ``Exists [1]) nat (mkLambda `y .default nat e)
  e := mkForall `x .default nat e
  e := mkLet `z nat (mkNatLit 0) e
  return e

set_option maxRecDepth 10000000

def tryIntros? (goals : List MVarId) : SymM (Option (List MVarId)) := do
  try
    let goal :: goals := goals | return none
    let (_, goal') ← intros goal
    return some (goal' :: goals)
  catch _ =>
    return none

def tryApply? (rule : BackwardRule) (goals : List MVarId) : SymM (Option (List MVarId)) := do
  let goal :: goals := goals | return none
  try
    let goals' ← rule.apply goal
    return some (goals' ++ goals)
  catch _ =>
    return none

def tryApplyAny? (rules : List BackwardRule) (goals : List MVarId) : SymM (Option (List MVarId)) := do
  match rules with
  | [] => return none
  | rule :: rules =>
    if let some goals' ← tryApply? rule goals then
      return some goals'
    else
      tryApplyAny? rules goals

def solve (n : Nat) (type : Expr) : MetaM Unit := profileM (msg := s!"size {n}") <| SymM.run do
  let mvarId := (← mkFreshExprMVar type).mvarId!
  let rules ← [``Exists.intro, ``And.intro, ``Eq.refl, ``True.intro].mapM fun declName => mkBackwardRuleFromDecl declName
  let goal ← preprocessMVar mvarId
  discard <| go 10000000 rules [goal]
  return ()
where
  go (fuel : Nat) (rules : List BackwardRule) (goals : List MVarId) : SymM Bool := do
    let fuel + 1 := fuel | throwError "out of fuel"
    let goal :: goals' := goals | return true
    if (← goal.isAssigned) then
      go fuel rules goals'
    else
      if let some goals' ← tryIntros? goals then
        go fuel rules goals'
      else if let some goals' ← tryApplyAny? rules goals then
        go fuel rules goals'
      else
        throwError "Stuck at {goal}"

def test (n : Nat) : MetaM Unit := do
  let e := genTerm n
  solve n e

-- We are solving problems of the following form
#eval logInfo (genTerm 2)

#eval test 1000
#eval test 2000
#eval test 3000
#eval test 4000
#eval test 5000
#eval test 6000
