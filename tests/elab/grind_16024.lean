/-!
Regression test for #16024: `grind?` keeps `[grind inj]` theorems from the environment
that the proof uses.
-/

def f (n : Nat) : Nat := n + 1

@[grind inj]
theorem f_injective : Function.Injective f := fun _ _ h => Nat.add_right_cancel h

/--
info: Try this:
  [apply] grind only [inj f_injective]
-/
#guard_msgs in
example (a b : Nat) (h : f a = f b) : a = b := by grind?

example (a b : Nat) (h : f a = f b) : a = b := by grind only [inj f_injective]

-- An explicit `inj` parameter is not duplicated.
/--
info: Try this:
  [apply] grind only [inj f_injective]
-/
#guard_msgs in
example (a b : Nat) (h : f a = f b) : a = b := by grind? [inj f_injective]

-- Unused injectivity theorems are not included.
def g (n : Nat) : Nat := n + 2

@[grind inj]
theorem g_injective : Function.Injective g := fun _ _ h => Nat.add_right_cancel h

/--
info: Try this:
  [apply] grind only
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (_ : g a = g b) : a = b := by grind?
