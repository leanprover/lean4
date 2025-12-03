module

public import DiamondExampleA.Ring.Defs
import DiamondExampleA.Ring.Lemmas

open Ring

public theorem foo [Ring α] (a b c d : α) : a + (b + (c + d)) = b + c + a + d := by
  rw [poorly_named_lemma]
  rw [poorly_named_lemma a c d]
  rw [← add_assoc, ← add_assoc]
