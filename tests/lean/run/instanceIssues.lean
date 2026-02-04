inductive Vector' (α : Type u) : Nat → Type u
  | nil  : Vector' α 0
  | cons : α → Vector' α n → Vector' α (n + 1)

def test [Monad m] (xs : Vector' α a) : m Unit :=
  match xs with
  | Vector'.nil => return ()
  | Vector'.cons _ xs => test xs
termination_by sizeOf xs

/--
error: cannot use `instance` in `mutual` block; consider splitting into separate `mutual` `def`s
-/
#guard_msgs in
mutual
instance i1 : Repr Nat := i2
instance i2 : Repr Nat := i1
end
