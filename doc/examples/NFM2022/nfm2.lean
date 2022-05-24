/- First-class functions -/

def twice (f : Nat → Nat) (a : Nat) :=
  f (f a)

#check twice
-- (Nat → Nat) → Nat → Nat

#eval twice (fun x => x + 2) 10

theorem twice_add_2 (a : Nat) : twice (fun x => x + 2) a = a + 4 := rfl

-- `(· + 2)` is syntax sugar for `(fun x => x + 2)`.
#eval twice (· + 2) 10
