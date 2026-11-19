namespace Bla

inductive Nat where
  | z : Nat
  | s : Nat → Nat

def add : Nat → Nat → Nat
  | a, Nat.z => a
  | a, Nat.s b => Nat.s (add a b)

theorem ex (x : Nat) : add Nat.z x = x := by
  induction x
  done

end Bla
