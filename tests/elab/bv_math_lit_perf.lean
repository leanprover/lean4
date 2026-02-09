open BitVec

def f (x : BitVec 32) : Nat :=
  match x with
  | 10#32  => 0
  | 100#32 => 2
  | 200#32 => 3
  | 300#32 => 4
  | 400#32 => 5
  | 500#32 => 6
  | 600#32 => 7
  | 700#32 => 8
  | 800#32 => 9
  | 900#32 => 10
  | 910#32 => 11
  | 920#32 => 12
  | _      => 1000

-- Generate the equational lemmas ahead of time, to avoid going
-- over the heartbeat limit below
#guard_msgs(drop all) in
#print equations f

set_option maxHeartbeats 800
example : f 500#32 = x := by
  simp [f]
  sorry
