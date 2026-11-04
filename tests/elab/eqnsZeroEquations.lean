/-!
Tests that a definition whose body eliminates an empty type, where splitting leaves no goals, gets
a single equation lemma that states the unfolded definition, and that tactics can use it.
-/

def f (x : Empty) : Nat := nomatch x

def h : Fin 0 → Nat := fun i => nomatch i

def g : Empty → Nat → Nat
  | x, _ => nomatch x

/--
info: equations:
@[backward_defeq] theorem f.eq_1 : ∀ (x : Empty), f x = nomatch x
-/
#guard_msgs in
#print equations f

/--
info: equations:
@[backward_defeq] theorem h.eq_1 : ∀ (i : Fin 0), h i = nomatch i
-/
#guard_msgs in
#print equations h

/--
info: equations:
@[backward_defeq] theorem g.eq_1 : ∀ (x : Empty) (x_1 : Nat),
  g x x_1 =
    match x, x_1 with
    | x, x_2 => nomatch x
-/
#guard_msgs in
#print equations g

example (x : Empty) : f x = 0 := by
  simp only [f]
  exact nomatch x

example (x : Empty) : f x = 0 := by
  rw [f]
  exact nomatch x

example (x : Empty) : f x = 0 := by
  unfold f
  exact nomatch x

example (x : Empty) : f x = 0 := by grind [f]

example (x : Empty) : f x = 0 := by grind [f.eq_def]

/-! `grind` on a matcher without alternatives -/

example (x : Empty) : (nomatch x : Nat) = 0 := by grind
