import Lean.Meta.Tactic

open Lean Meta
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

def tryIntros? (goals : List MVarId) : MetaM (Option (List MVarId)) := do
  let goal :: goals := goals | return none
  let (fvars, goal') ← goal.intros
  if fvars.isEmpty then return none
  return some (goal' :: goals)

def tryApply? (declName : Name) (goals : List MVarId) : MetaM (Option (List MVarId)) := do
  let goal :: goals := goals | return none
  try
    let goals' ← goal.applyConst declName
    return some (goals' ++ goals)
  catch _ =>
    return none

def tryApplyAny? (declNames : List Name) (goals : List MVarId) : MetaM (Option (List MVarId)) := do
  match declNames with
  | [] => return none
  | declName :: declNames =>
    if let some goals' ← tryApply? declName goals then
      return some goals'
    else
      tryApplyAny? declNames goals

def solve (declName : Name) : MetaM Unit := profileM (msg := declName.toString) do
  let type := (← getConstInfo declName).type
  let mvarId := (← mkFreshExprMVar type).mvarId!
  discard <| go 10000000 [mvarId]
  return ()
where
  go (fuel : Nat) (goals : List MVarId) : MetaM Bool := do
    let fuel + 1 := fuel | throwError "out of fuel"
    let goal :: goals' := goals | return true
    if (← goal.isAssigned) then
      go fuel goals'
    else
      if let some goals' ← tryIntros? goals then
        go fuel goals'
      else if let some goals' ← tryApplyAny? [``Exists.intro, ``And.intro, ``Eq.refl, ``True.intro] goals then
        go fuel goals'
      else
        throwError "Stuck at {goal}"

#eval solve ``ex1000
#eval solve ``ex2000
#eval solve ``ex3000
#eval solve ``ex4000
#eval solve ``ex5000
