module

/-!
Regression test for #14573: `grind?` and `finish?` suggestions used to omit parameters whose
effect is not representable in the generated script (e.g., `inj f_inj`, `funCC q`), so the
suggestions failed when pasted.
-/

def f (n : Nat) := n + 3

theorem f_inj : Function.Injective f := by
  intro a b h
  simp [f] at h
  omega

/--
info: Try this:
  [apply] grind only [inj f_inj]
-/
#guard_msgs in
example (a b : Nat) (h : f a = f b) : a = b := by grind? [inj f_inj]

example (a b : Nat) (h : f a = f b) : a = b := by grind only [inj f_inj]

/-! `inj` must also be carried by the script form, when the proof needs further steps. -/

/--
info: Try these:
  [apply] grind only [#3e09, inj f_inj]
  [apply] grind only [inj f_inj]
  [apply] grind [inj f_inj] => cases #3e09
-/
#guard_msgs in
example (a b : Nat) (h : f a = f b) (c : Bool) (y : Nat) (h' : y = if c then a else b) : y = a := by
  grind? [inj f_inj]

example (a b : Nat) (h : f a = f b) (c : Bool) (y : Nat) (h' : y = if c then a else b) : y = a := by
  grind only [#3e09, inj f_inj]

example (a b : Nat) (h : f a = f b) (c : Bool) (y : Nat) (h' : y = if c then a else b) : y = a := by
  grind [inj f_inj] => cases #3e09

opaque q : Nat → Nat → Nat

/--
info: Try this:
  [apply] grind only [funCC q]
-/
#guard_msgs in
example (a b : Nat) (g : Nat → Nat) (h : q a = g) : q a b = g b := by grind? [funCC q]

example (a b : Nat) (g : Nat → Nat) (h : q a = g) : q a b = g b := by grind only [funCC q]

/-!
`finish?` has the same problem. The script suggestion (`cases #3e09` here) cannot carry the
parameter, so it must not be offered; the `finish only` suggestion must keep it.
-/

/--
info: Try this:
  [apply] finish only [#3e09, inj f_inj]
-/
#guard_msgs in
example (a b : Nat) (h : f a = f b) (c : Bool) (y : Nat) (h' : y = if c then a else b) : y = a := by
  grind => finish? [inj f_inj]

example (a b : Nat) (h : f a = f b) (c : Bool) (y : Nat) (h' : y = if c then a else b) : y = a := by
  grind => finish only [#3e09, inj f_inj]
