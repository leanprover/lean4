/--
info: equations:
theorem List.append.eq_1.{u} : ∀ {α : Type u} (x : List α), List.append [] x = x
theorem List.append.eq_2.{u} : ∀ {α : Type u} (x : List α) (a : α) (l : List α),
  List.append (a :: l) x = a :: List.append l x
-/
#guard_msgs in
#print eqns List.append

/--
info: equations:
theorem List.append.eq_1.{u} : ∀ {α : Type u} (x : List α), List.append [] x = x
theorem List.append.eq_2.{u} : ∀ {α : Type u} (x : List α) (a : α) (l : List α),
  List.append (a :: l) x = a :: List.append l x
-/
#guard_msgs in
#print equations List.append

@[simp] def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

/--
info: equations:
theorem ack.eq_1 : ∀ (x : Nat), ack 0 x = x + 1
theorem ack.eq_2 : ∀ (x_2 : Nat), ack (Nat.succ x_2) 0 = ack x_2 1
theorem ack.eq_3 : ∀ (x_2 y : Nat), ack (Nat.succ x_2) (Nat.succ y) = ack x_2 (ack (x_2 + 1) y)
-/
#guard_msgs in
#print eqns ack
