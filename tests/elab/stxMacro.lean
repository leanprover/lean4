-- Macro for the `syntax` category
macro "many " x:stx : stx => `(stx| ($x)*)

syntax "sum! " (many term:max) : term

macro_rules
| `(sum! $xs*) => do
  let mut r ← `(0)
  for x in xs do
    r ← `($r + $x)
  return r

#check sum! 1 2 3
#guard sum! 1 2 3 == 6
#check sum!

theorem ex : sum! 1 2 3 = 6 :=
rfl
