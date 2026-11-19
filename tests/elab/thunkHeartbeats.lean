/-!
Evaluating a thunk shared between threads does not count toward the heartbeats of the thread that
happens to force it first, while evaluating a thread-local thunk still does.
-/

@[noinline] def mkThunk (k : Nat) : Thunk Nat :=
  .mk fun _ => (List.range k).length

@[noinline] def force (t : Thunk Nat) : Nat :=
  t.get

/-- Heartbeats spent on forcing `t`, which must evaluate to `k`. -/
def forceHeartbeats (t : Thunk Nat) (k : Nat) : IO Nat := do
  let h₀ ← IO.getNumHeartbeats
  let n := force t
  -- checks the value before reading the heartbeats again, so that forcing is not moved past it
  unless n == k do throw <| IO.userError "unexpected value"
  let h₁ ← IO.getNumHeartbeats
  return h₁ - h₀

/-- info: (true, true, true) -/
#guard_msgs in
#eval show IO _ from do
  -- not literals, and distinct, so that the thunks below are not merged into one
  let k := (← IO.getRandomBytes 0).size + 10000
  let forced := mkThunk k
  discard <| forceHeartbeats forced k
  let base ← forceHeartbeats forced k
  let threadLocal ← forceHeartbeats (mkThunk (k + 1)) (k + 1)
  let shared := mkThunk (k + 2)
  -- the task's closure captures the thunk, marking it as shared
  discard <| IO.wait (Task.spawn fun _ => shared)
  let mt ← forceHeartbeats shared (k + 2)
  let persistent ← unsafe Runtime.markPersistent (mkThunk (k + 3))
  let pers ← forceHeartbeats persistent (k + 3)
  return (decide (threadLocal > base + k), mt == base, pers == base)
