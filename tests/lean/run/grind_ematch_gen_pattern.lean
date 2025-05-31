set_option grind.warning false

@[grind] theorem pbind_some' {α β} {x : Option α} {a : α} {f : (a : α) → x = some a → Option β}
     (h : x = some a) : Option.pbind x f = f a h := by
  subst h; rfl

def f (x : Option Nat) (h : x ≠ none) : Nat :=
  match x with
  | none => by contradiction
  | some a => a

example (h : b = some a) : (b.pbind fun a h => some <| a + f b (by grind)) = some (a + a) := by
  grind only [pbind_some', f]
