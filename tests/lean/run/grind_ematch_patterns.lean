def replicate : (n : Nat) → (a : α) → List α
  | 0,   _ => []
  | n+1, a => a :: replicate n a

/--
info: [grind.ematch.pattern] replicate.eq_1: [@replicate #1 `[0] #0]
[grind.ematch.pattern] replicate.eq_2: [@replicate #2 (#0 + 1) #1]
-/
#guard_msgs (info) in
set_option trace.grind.ematch.pattern true in
attribute [grind] replicate

example : ys = [] → replicate 0 [] = ys := by
  grind only [replicate]

/--
error: invalid `grind` parameter, `replicate` is a definition, the only acceptable (and redundant) modifier is '='
-/
#guard_msgs (error) in
example : ys = [] → replicate 0 [] = ys := by
  grind only [←replicate]

example : ys = [] → replicate 0 [] = ys := by
  fail_if_success grind only
  sorry

example (ys : List α) : n = 0 → replicate n ys = [] := by
  grind only [replicate]

example (ys : List α) : n = 0 → List.replicate n ys = [] := by
  grind only [List.replicate]

opaque foo : Nat → Nat
opaque bla : Nat → Nat

theorem foo_bla : foo x = bla x := sorry

example : foo x = bla x := by
  grind only [_=_ foo_bla]

@[reducible] def inc (_ : Nat) := 1

/--
error: `inc` is a reducible definition, `grind` automatically unfolds them
-/
#guard_msgs (error) in
example : a = 1 → inc x = a := by
  grind [inc]
