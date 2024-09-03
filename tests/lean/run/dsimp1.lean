def Nat.isZero (x : Nat) : Bool :=
  match x with
  | 0 => true
  | _+1 => false

axiom P : Bool → Prop
axiom P_false : P false

/--
info: x : Nat
⊢ P (1 + x).isZero
-/
#guard_msgs in
example (x : Nat) : P (1 + id x.succ.pred).isZero := by
  dsimp
  trace_state
  simp [Nat.succ_add]
  dsimp [Nat.isZero]
  apply P_false

example (x : Nat) : P (id x.succ.succ).isZero := by
  dsimp [Nat.isZero]
  apply P_false

example (x : Nat) : P (id x.succ.succ).isZero := by
  dsimp [Nat.isZero.eq_2]
  apply P_false

example (x : Nat) : P (id x.succ.succ).isZero := by
  dsimp!
  apply P_false

@[simp] theorem isZero_succ (x : Nat) : (x + 1).isZero = false :=
  rfl

theorem ex1 (x : Nat) : P (id x.succ.succ.pred).isZero  := by
  dsimp
  apply P_false
