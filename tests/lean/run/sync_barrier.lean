import Std.Sync.Barrier

def consBarrier (b : Std.Barrier) (list : IO.Ref (List Nat)) : IO Unit := do
  for _ in [0:1000] do
    list.modify fun l => 1 :: l
  b.wait
  for _ in [0:1000] do
    list.modify fun l => 2 :: l

def barrier : IO Unit := do
  let b ← Std.Barrier.new 2
  let ref ← IO.mkRef []
  let t1 ← IO.asTask (prio := .dedicated) (consBarrier b ref)
  let t2 ← IO.asTask (prio := .dedicated) (consBarrier b ref)
  IO.ofExcept t1.get
  IO.ofExcept t2.get
  let list ← ref.get
  if list.take 2000 |>.any (· != 2) then
    throw <| .userError "List head should have only 2's but doesn't"
  if list.drop 2000 |>.any (· != 1) then
    throw <| .userError "List tail should have only 1's but doesn't"

#eval barrier
