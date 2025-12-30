import Lean.Meta.Tactic
import Lean.Meta.Sym

open Lean Meta Sym
def profileM {α : Type} (k : MetaM α) (msg : String := "experiment") : MetaM α :=
  profileitM Exception msg ({ : Options }.setBool `profiler true |>.setNat `profiler.threshold 0)  k

macro "gen_term" n:num : term => do
  let mut stx ← `(True)
  for _ in 0...n.getNat do
    stx := ← `(let z : Nat := x + y; forall x : Nat, exists y : Nat, y = z+x /\ $stx)
  `(let z : Nat := 0 ; forall x : Nat, exists y : Nat, y = z+x ∧ $stx)

set_option maxRecDepth 10000000
axiom ex1000 : gen_term 1000
axiom ex2000 : gen_term 2000
axiom ex3000 : gen_term 3000
axiom ex4000 : gen_term 4000
axiom ex5000 : gen_term 5000

def tryIntros? (goals : List Goal) : SymM (Option (List Goal)) := do
  try
    let goal :: goals := goals | return none
    let (_, goal') ← intros goal
    return some (goal' :: goals)
  catch _ =>
    return none

def tryApply? (rule : BackwardRule) (goals : List Goal) : SymM (Option (List Goal)) := do
  let goal :: goals := goals | return none
  try
    let goals' ← rule.apply goal
    return some (goals' ++ goals)
  catch _ =>
    return none

def tryApplyAny? (rules : List BackwardRule) (goals : List Goal) : SymM (Option (List Goal)) := do
  match rules with
  | [] => return none
  | rule :: rules =>
    if let some goals' ← tryApply? rule goals then
      return some goals'
    else
      tryApplyAny? rules goals

def solve (declName : Name) : MetaM Unit := profileM (msg := declName.toString) <| SymM.run' do
  let type := (← getConstInfo declName).type
  let mvarId := (← mkFreshExprMVar type).mvarId!
  let rules ← [``Exists.intro, ``And.intro, ``Eq.refl, ``True.intro].mapM fun declName => mkBackwardRuleFromDecl declName
  let goal ← mkGoal mvarId
  discard <| go 10000000 rules [goal]
  return ()
where
  go (fuel : Nat) (rules : List BackwardRule) (goals : List Goal) : SymM Bool := do
    let fuel + 1 := fuel | throwError "out of fuel"
    let goal :: goals' := goals | return true
    if (← goal.mvarId.isAssigned) then
      go fuel rules goals'
    else
      if let some goals' ← tryIntros? goals then
        go fuel rules goals'
      else if let some goals' ← tryApplyAny? rules goals then
        go fuel rules goals'
      else
        throwError "Stuck at {goal.mvarId}"

#eval solve ``ex1000
#eval solve ``ex2000
#eval solve ``ex3000
#eval solve ``ex4000
#eval solve ``ex5000
