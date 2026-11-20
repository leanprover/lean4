/-!
Tests that `cbv` maximally shares the result of reducing a `match` via `reduceRecMatcher?`.

The return type of `g` depends on `o`, so `cbv` cannot rewrite the argument `o` to a constructor
and the match equations do not apply; the match is then reduced by `reduceRecMatcher?`. The
resulting inner `match` used to be unshared, which tripped the `sym.debug` sharing assertion
when its discriminant was simplified.
-/

set_option sym.debug true

def ok (_ : Option Nat) : Prop := True

def g (o : Option Nat) (h : ok o) : { _x : Nat // ok o } :=
  match o, h with
  | none, h => ⟨0, h⟩
  | some k, h => match compare 3 k with | .lt => ⟨0, h⟩ | _ => ⟨k, h⟩

def o : Option Nat := some 1

example : (g o trivial).val = 1 := by cbv
