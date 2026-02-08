import Lean.ObjectGraph
import Lean

open Lean

-- Arrays
#eval IO.println <| objectGraphToDot  <| #[(1 : UInt8), 2, 3, 4]
#eval IO.println <| objectGraphToDot  <| #[(1 : UInt64), 2, 3, 4]
#eval IO.println <| objectGraphToDot  <| #[(1 : Nat), 2, 3, 4, 2^64 + 1]

-- Maps
#eval IO.println <| objectGraphToDot <| Std.TreeMap.ofList [(128, "128"), (64, "64"), (32, "32"), (16, "16"), (8, "8"), (4, "4")]
#eval IO.println <| objectGraphToDot <| Std.HashMap.ofList [(128, "128"), (64, "64"), (32, "32"), (16, "16"), (8, "8"), (4, "4")]

-- Channel
#eval show IO _ from do
  let chan ← Std.Channel.new (α := String) (capacity := some 8)
  discard <| IO.ofExcept <| (← IO.asTask (chan.sync.send "1")).get
  discard <| IO.ofExcept <| (← IO.asTask (chan.sync.send "2")).get
  discard <| IO.ofExcept <| (← IO.asTask (chan.sync.recv)).get
  discard <| IO.ofExcept <| (← IO.asTask (chan.sync.send "3")).get
  discard <| IO.ofExcept <| (← IO.asTask (chan.sync.send "4")).get
  IO.println <| objectGraphToDot <| chan

def A : Nat := 0

def mkAddTree (n : Nat) : CoreM Expr := do
  go n |>.run' {} {}
where
  go (n : Nat) : MetaM Expr := do
  match n with
  | 0 => return mkConst `A
  | n + 1 => Meta.mkAppM (``Add.add) #[← go n, ← go n]

#eval show CoreM _ from do
  IO.println <| objectGraphToDot <| (← mkAddTree 4)

#eval show CoreM _ from do
  IO.println <| objectGraphToDot <| ShareCommon.shareCommon (← mkAddTree 4)
