def Nat.isZero (x : Nat) : Bool :=
  match x with
  | 0 => true
  | x+1 => false

example (x : Nat) : (1 + id x.succ.pred).isZero = false := by
  dsimp
  trace_state
  simp [Nat.succ_add]
  dsimp [Nat.isZero]

#check Nat.pred_succ

example (x : Nat) : (id x.succ.succ).isZero = false := by
  dsimp [Nat.isZero]

example (x : Nat) : (id x.succ.succ).isZero = false := by
  dsimp!

@[simp] theorem isZero_succ (x : Nat) : (x + 1).isZero = false :=
  rfl

theorem ex1 (x : Nat) : (id x.succ.succ.pred).isZero = false := by
  dsimp
