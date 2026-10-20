

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

/-!
`zeta_delta` must also unfold a let-bound variable in the head position of an application,
since `dsimp` does not visit application heads. See Zulip discussion on
`Sym.DSimp.zetaDelta` leaving `foo a b` untouched.
-/

/--
trace: case grind
a b : Nat
foo : Nat → Nat → Nat := fun x y => x + y
⊢ a + b = b + a
-/
#guard_msgs in
example (a b : Nat) : let foo := fun (x y : Nat) => x + y; foo a b = foo b a := by
  sym =>
    intro foo
    dsimp [*]
    show_goals
    exact Nat.add_comm a b

/--
trace: case grind
a b : Nat
foo : Nat → Nat → Nat := fun x y => x + y
⊢ a + b = b + a
-/
#guard_msgs in
example (a b : Nat) : let foo := fun (x y : Nat) => x + y; foo a b = foo b a := by
  sym =>
    intro foo
    dsimp [foo]
    show_goals
    exact Nat.add_comm a b

/--
trace: case grind
a b : Nat
h : ∀ (bar : Nat → Nat → Nat), a + b = bar b a
foo : Nat → Nat → Nat := fun x y => x + y
bar : Nat → Nat → Nat := fun x y => x * y
⊢ a + b = bar b a
-/
#guard_msgs in
example (a b : Nat) (h : ∀ bar : Nat → Nat → Nat, a + b = bar b a) :
    let foo := fun (x y : Nat) => x + y; let bar := fun (x y : Nat) => x * y; foo a b = bar b a := by
  sym =>
    intro foo bar
    dsimp [foo]
    show_goals
    exact h bar

-- Partial application: the exposed lambda is beta-reduced as far as the arguments allow.
/--
trace: case grind
a : Nat
foo : Nat → Nat → Nat := fun x y => x + y
⊢ (fun y => a + y) = fun y => a + y
-/
#guard_msgs in
example (a : Nat) : let foo := fun (x y : Nat) => x + y; foo a = fun y => a + y := by
  sym =>
    intro foo
    dsimp [*]
    show_goals
    exact rfl
