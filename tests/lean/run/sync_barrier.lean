import Std.Sync.Barrier

def consBarrier (b : Std.Barrier) (list : IO.Ref (List Nat)) : IO Bool := do
  for _ in [0:1000] do
    list.modify fun l => 1 :: l
  let isLeader ← b.wait
  for _ in [0:1000] do
    list.modify fun l => 2 :: l
  return isLeader

def barrier : IO Unit := do
  let b ← Std.Barrier.new 2
  let ref ← IO.mkRef []
  go b ref
  -- reuse barrier
  go b ref
where
  go (b : Std.Barrier) (ref : IO.Ref (List Nat)) : IO Unit := do
    let t1 ← IO.asTask (prio := .dedicated) (consBarrier b ref)
    let t2 ← IO.asTask (prio := .dedicated) (consBarrier b ref)
    let leaderT1 ← IO.ofExcept t1.get
    let leaderT2 ← IO.ofExcept t2.get
    if leaderT1 == leaderT2 then
      let err := s!"Exactly one should be leader but t1 leader? {leaderT1} t2 leader? {leaderT2}"
      throw <| .userError err
    let list ← ref.get
    if list.take 2000 |>.any (· != 2) then
      throw <| .userError "List head should have only 2's but doesn't"
    if list.drop 2000 |>.take 2000 |>.any (· != 1) then
      throw <| .userError "List tail should have only 1's but doesn't"

#eval barrier
