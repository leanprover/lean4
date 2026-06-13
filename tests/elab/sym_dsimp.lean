

example (h : a = c) : ((fun x => x) a, b).1 = c := by
  sym =>
    dsimp
    exact h

example (h : 10 + a = b) : let x := 10; x + a = b := by
  sym =>
    intro x
    dsimp [x]
    exact h

/--
trace: case grind
a b : Nat
h : 10 + a = b
x : Nat := 10
y : Nat := a
⊢ 10 + a = b
-/
#guard_msgs in
example (h : 10 + a = b) : let x := 10; let y := a; x + y = b := by
  sym =>
    intro x y
    dsimp [*]
    show_goals
    exact h

register_sym_dsimp myDSimp where
  pre  := beta >> match >> zeta >> zeta_delta
  post := none

/--
trace: case grind
a b : Nat
h : 10 + a = b
⊢ 10 + a = b
-/
#guard_msgs in
example (h : 10 + a = b) : let x := 10; let y := a; x + y = b := by
  sym =>
    fail_if_success dsimp
    dsimp myDSimp
    show_goals
    exact h

/--
trace: case grind
a b : Nat
β✝ : Type u_1
c : β✝
h : 10 + a = b
⊢ 10 + a = (b, c).fst
-/
#guard_msgs in
example (h : 10 + a = b) : let x := 10; let y := a; x + y = (b, c).1 := by
  sym =>
    dsimp myDSimp -- projections are not reduced
    show_goals
    exact h
