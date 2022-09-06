import Lean

def test (a : Nat) :=
  let foo := match a with
  | .zero => a
  | .succ b => b
  Nat.add foo .zero

#eval Lean.Compiler.compile #[``test]
