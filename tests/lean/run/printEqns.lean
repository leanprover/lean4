/--
info: equations:
@[defeq] theorem List.append.eq_1.{u} : ∀ {α : Type u} (x : List α), [].append x = x
@[defeq] theorem List.append.eq_2.{u} : ∀ {α : Type u} (x : List α) (a : α) (l : List α),
  (a :: l).append x = a :: l.append x
-/
#guard_msgs in
#print eqns List.append

/--
info: equations:
@[defeq] theorem List.append.eq_1.{u} : ∀ {α : Type u} (x : List α), [].append x = x
@[defeq] theorem List.append.eq_2.{u} : ∀ {α : Type u} (x : List α) (a : α) (l : List α),
  (a :: l).append x = a :: l.append x
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
theorem ack.eq_2 : ∀ (x_2 : Nat), ack x_2.succ 0 = ack x_2 1
theorem ack.eq_3 : ∀ (x_2 y : Nat), ack x_2.succ y.succ = ack x_2 (ack (x_2 + 1) y)
-/
#guard_msgs in
#print eqns ack
