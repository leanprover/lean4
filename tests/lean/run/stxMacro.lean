new_frontend

-- Macro for the `syntax` category
macro "many " x:stx : stx => `(stx| ($x)*)

syntax "sum! " (many term:max) : term

macro_rules
| `(sum! $x*) => do
  let r ← `(0);
  x.foldlM (fun r elem => `($r + $elem)) r

#check sum! 1 2 3
#eval sum! 1 2 3
#check sum!

theorem ex : sum! 1 2 3 = 6 :=
rfl
