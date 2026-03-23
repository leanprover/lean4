module

public import DiamondExampleA.Ring.Defs
import DiamondExampleA.Ring.Lemmas

open Ring

public theorem bar [Ring α] (a b c : α) : a + b + c = b + a + c := by
  rw [add_assoc]
  rw [add_left_comm]
  rw [← add_assoc]
